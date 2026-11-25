import A377090.Basic
import A377090.AnalyticInputs

/-!
# Theorem 3: Prime-Gap Lower Bound and Unbounded Logarithmic Ratio

This file formalizes Section 4 of the paper:

* **Lemma 4.1** (`prime_gap_twoDeviation_lower_bound`, `prime_gap_deviation_lower_bound`):
  For *any* injective integer sequence `a : ℕ → ℤ` with prime step sizes and any consecutive
  primes `p < q`,
  `max_{p ≤ n ≤ q} | |a(n)| - n / 2 | ≥ (q - p) / 8`.
  This proof is **100% unconditional**, requiring no external analytic hypotheses.
* **Corollary 4.2** (`deviation_div_log_unbounded`):
  Using Mathlib's Bertrand postulate (`bertrand_consecutive_primes_lt`) together with
  `WestzynthiusInput`, `limsup_{n → ∞} δ(n) / log(n + 2) = ∞`.
-/

namespace A377090

open Finset

/-- Integerized doubled deviation `2 * δ(n) = |2 * |a(n)| - n|`. -/
def twoDeviation (a : ℕ → ℤ) (n : ℕ) : ℕ :=
  Int.natAbs (2 * ((a n).natAbs : ℤ) - (n : ℤ))

/-- Deviation `δ(n) = ||a(n)| - n / 2|`. -/
noncomputable def deviation (a : ℕ → ℤ) (n : ℕ) : ℝ :=
  |((a n).natAbs : ℝ) - (n : ℝ) / 2|

theorem deviation_eq_twoDeviation_div_two (a : ℕ → ℤ) (n : ℕ) :
    deviation a n = (twoDeviation a n : ℝ) / 2 := by
  unfold deviation twoDeviation
  have hcast : ((Int.natAbs (2 * ((a n).natAbs : ℤ) - (n : ℤ)) : ℕ) : ℝ) =
      |(2 * ((a n).natAbs : ℝ) - (n : ℝ))| := by
    have h1 : (((Int.natAbs (2 * ((a n).natAbs : ℤ) - (n : ℤ)) : ℕ) : ℤ) : ℝ) =
        ((|(2 * ((a n).natAbs : ℤ) - (n : ℤ))| : ℤ) : ℝ) := by
      rw [Int.natCast_natAbs]
    rw [Int.cast_natCast] at h1
    rw [h1, Int.cast_abs, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
      Int.cast_natCast]
  rw [hcast]
  have hdiv : |(2 * ((a n).natAbs : ℝ) - (n : ℝ))| / 2 =
      |((a n).natAbs : ℝ) - (n : ℝ) / 2| := by
    have h2 : (0 : ℝ) < 2 := by norm_num
    calc
      |(2 * ((a n).natAbs : ℝ) - (n : ℝ))| / 2
          = |2 * (((a n).natAbs : ℝ) - (n : ℝ) / 2)| / |2| := by
              rw [abs_of_pos h2]
              ring_nf
      _ = (|2| * |((a n).natAbs : ℝ) - (n : ℝ) / 2|) / |2| := by rw [abs_mul]
      _ = |((a n).natAbs : ℝ) - (n : ℝ) / 2| := by
              rw [abs_of_pos h2]
              field_simp
  exact hdiv.symm

/-- **Lemma 4.1 (Pure integer version, zero external assumptions)**:
For any injective `a : ℕ → ℤ` with prime adjacent steps and any consecutive primes `p < q`,
`q - p ≤ 4 * max_{p ≤ n ≤ q} (2 * δ(n))`. -/
theorem prime_gap_twoDeviation_lower_bound (a : ℕ → ℤ)
    (hinj : Function.Injective a)
    (hstep : ∀ n : ℕ, Nat.Prime (a (n + 1) - a n).natAbs)
    {p q : ℕ} (hpq : p < q)
    (hconsec : ∀ r : ℕ, p < r → r < q → ¬Nat.Prime r) :
    q - p ≤ 4 * (Finset.Icc p q).sup (twoDeviation a) := by
  let d2 : ℕ := (Finset.Icc p q).sup (twoDeviation a)
  let L : ℕ := p + d2
  let U : ℕ := q - d2
  by_cases hLU : U ≤ L
  · dsimp only [L, U] at hLU
    omega
  have hL_lt_U : L < U := lt_of_not_ge hLU
  have htwoDev_le : ∀ k : ℕ, p ≤ k → k ≤ q → twoDeviation a k ≤ d2 := fun k hpk hkq =>
    Finset.le_sup (f := twoDeviation a) (Finset.mem_Icc.mpr ⟨hpk, hkq⟩)
  have hbetween : ∀ i : ℕ, L ≤ i → i < U →
      p < (a i).natAbs + (a (i + 1)).natAbs ∧ (a i).natAbs + (a (i + 1)).natAbs < q := by
    intro i hiL hiU
    have hi_bounds : p ≤ i ∧ i ≤ q := ⟨by omega, by omega⟩
    have hi1_bounds : p ≤ i + 1 ∧ i + 1 ≤ q := ⟨by omega, by omega⟩
    have hdev_i : twoDeviation a i ≤ d2 := htwoDev_le i hi_bounds.1 hi_bounds.2
    have hdev_i1 : twoDeviation a (i + 1) ≤ d2 := htwoDev_le (i + 1) hi1_bounds.1 hi1_bounds.2
    unfold twoDeviation at hdev_i hdev_i1
    omega
  have hsame_adj : ∀ i : ℕ, L ≤ i → i < U →
      (0 < a i ∧ 0 < a (i + 1)) ∨ (a i < 0 ∧ a (i + 1) < 0) := by
    intro i hiL hiU
    obtain ⟨hp_lt, hlt_q⟩ := hbetween i hiL hiU
    by_contra hnot
    have hstep_eq : (a (i + 1) - a i).natAbs = (a i).natAbs + (a (i + 1)).natAbs := by
      omega
    have hpr : Nat.Prime ((a i).natAbs + (a (i + 1)).natAbs) := by
      rw [← hstep_eq]
      exact hstep i
    exact hconsec _ hp_lt hlt_q hpr
  have hsame_all : (∀ k ∈ Finset.Icc L U, 0 < a k) ∨ (∀ k ∈ Finset.Icc L U, a k < 0) := by
    have hL_step := hsame_adj L le_rfl hL_lt_U
    rcases hL_step with ⟨hL_pos, _⟩ | ⟨hL_neg, _⟩
    · left
      have hind : ∀ t : ℕ, L + t ≤ U → 0 < a (L + t) := by
        intro t
        induction t with
        | zero => intro _; simpa using hL_pos
        | succ t ih =>
            intro ht
            have ht0 : 0 < a (L + t) := ih (by omega)
            have hstep_t := hsame_adj (L + t) (by omega) (by omega)
            rcases hstep_t with ⟨_, hnext⟩ | ⟨hneg, _⟩
            · simpa [Nat.add_assoc] using hnext
            · omega
      intro k hk
      rcases Finset.mem_Icc.mp hk with ⟨hkL, hkU⟩
      have hkt := hind (k - L) (by omega)
      rwa [show L + (k - L) = k by omega] at hkt
    · right
      have hind : ∀ t : ℕ, L + t ≤ U → a (L + t) < 0 := by
        intro t
        induction t with
        | zero => intro _; simpa using hL_neg
        | succ t ih =>
            intro ht
            have ht0 : a (L + t) < 0 := ih (by omega)
            have hstep_t := hsame_adj (L + t) (by omega) (by omega)
            rcases hstep_t with ⟨hpos, _⟩ | ⟨_, hnext⟩
            · omega
            · simpa [Nat.add_assoc] using hnext
      intro k hk
      rcases Finset.mem_Icc.mp hk with ⟨hkL, hkU⟩
      have hkt := hind (k - L) (by omega)
      rwa [show L + (k - L) = k by omega] at hkt
  let S : Finset ℕ := (Finset.Icc L U).image (fun k => (a k).natAbs)
  have hS_card : S.card = U - L + 1 := by
    rw [Finset.card_image_of_injOn]
    · rw [Nat.card_Icc]
      omega
    · intro x hx y hy hxy
      dsimp only at hxy
      rcases hsame_all with hpos | hneg
      · have hx' := hpos x hx
        have hy' := hpos y hy
        exact hinj (by omega)
      · have hx' := hneg x hx
        have hy' := hneg y hy
        exact hinj (by omega)
  have hS_ne : S.Nonempty := by
    refine ⟨(a L).natAbs, Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨le_rfl, hL_lt_U.le⟩)⟩
  let mMin : ℕ := S.min' hS_ne
  let mMax : ℕ := S.max' hS_ne
  have hS_sub : S ⊆ Finset.Icc mMin mMax := fun m hm =>
    Finset.mem_Icc.mpr ⟨Finset.min'_le S m hm, Finset.le_max' S m hm⟩
  have hmMinMax : mMin ≤ mMax := Finset.min'_le S _ (Finset.max'_mem S hS_ne)
  have hcard_le : S.card ≤ mMax - mMin + 1 := by
    have hle := Finset.card_le_card hS_sub
    rw [Nat.card_Icc] at hle
    omega
  obtain ⟨kMin, hkMin_Icc, hkMin_eq⟩ := Finset.mem_image.mp (Finset.min'_mem S hS_ne)
  obtain ⟨kMax, hkMax_Icc, hkMax_eq⟩ := Finset.mem_image.mp (Finset.max'_mem S hS_ne)
  have hkMin_bounds := Finset.mem_Icc.mp hkMin_Icc
  have hkMax_bounds := Finset.mem_Icc.mp hkMax_Icc
  have hdevMin : twoDeviation a kMin ≤ d2 := htwoDev_le kMin (by omega) (by omega)
  have hdevMax : twoDeviation a kMax ≤ d2 := htwoDev_le kMax (by omega) (by omega)
  unfold twoDeviation at hdevMin hdevMax
  dsimp only [mMin, mMax] at hcard_le hkMin_eq hkMax_eq hmMinMax
  rw [← hkMin_eq, ← hkMax_eq] at hcard_le hmMinMax
  rw [hS_card] at hcard_le
  omega

/-- **Lemma 4.1 (Real-valued version, zero external assumptions)**:
There exists `n ∈ [p, q]` with `deviation a n ≥ (q - p) / 8`. -/
theorem prime_gap_deviation_lower_bound (a : ℕ → ℤ)
    (hinj : Function.Injective a)
    (hstep : ∀ n : ℕ, Nat.Prime (a (n + 1) - a n).natAbs)
    {p q : ℕ} (hpq : p < q)
    (hconsec : ∀ r : ℕ, p < r → r < q → ¬Nat.Prime r) :
    ∃ n ∈ Finset.Icc p q, ((q - p : ℕ) : ℝ) / 8 ≤ deviation a n := by
  have hne : (Finset.Icc p q).Nonempty := ⟨p, Finset.mem_Icc.mpr ⟨le_rfl, hpq.le⟩⟩
  obtain ⟨n, hn_mem, hn_sup⟩ := Finset.exists_mem_eq_sup (Finset.Icc p q) hne (twoDeviation a)
  refine ⟨n, hn_mem, ?_⟩
  have hgap := prime_gap_twoDeviation_lower_bound a hinj hstep hpq hconsec
  rw [hn_sup] at hgap
  have hgapR : ((q - p : ℕ) : ℝ) ≤ 4 * (twoDeviation a n : ℝ) := by exact_mod_cast hgap
  rw [deviation_eq_twoDeviation_div_two]
  linarith

/-- **Corollary 4.2 (Unbounded Logarithmic Ratio)**:
Under `WestzynthiusInput` (together with Bertrand's postulate from Mathlib),
`δ(n) / log(n + 2)` is unbounded above along OEIS A377090. -/
theorem deviation_div_log_unbounded (hW : WestzynthiusInput) :
    ∀ R : ℝ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ R < deviation a377090 n / Real.log ((n : ℝ) + 2) := by
  intro R N
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let R' : ℝ := 8 * (max R 1) * (1 + 2 / Real.log 2) + 1
  obtain ⟨p, q, hNp, hp, hq, hpq, hconsec, hgap⟩ := hW.large_gap R' (max N 2)
  have hN_le_p : N ≤ p := le_trans (le_max_left _ _) hNp
  have h2_le_p : 2 ≤ p := le_trans (le_max_right _ _) hNp
  have hbertrand : q < 2 * p := bertrand_consecutive_primes_lt hp hq hpq hconsec
  obtain ⟨n, hn_mem, hn_dev⟩ :=
    prime_gap_deviation_lower_bound a377090 a377090_injective a377090_step_prime hpq hconsec
  rcases Finset.mem_Icc.mp hn_mem with ⟨hpn, hnq⟩
  refine ⟨n, hN_le_p.trans hpn, ?_⟩
  have hp_real : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h2_le_p
  have hq_real : (q : ℝ) ≤ 2 * (p : ℝ) := by exact_mod_cast hbertrand.le
  have hn_real : (n : ℝ) ≤ (q : ℝ) := by exact_mod_cast hnq
  have hlog_p_pos : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith)
  have hlog_n2_pos : 0 < Real.log ((n : ℝ) + 2) := Real.log_pos (by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith)
  have hlog_n2_le : Real.log ((n : ℝ) + 2) ≤ Real.log (4 * (p : ℝ)) := by
    apply Real.log_le_log (by positivity)
    linarith
  have hlog4p : Real.log (4 * (p : ℝ)) = 2 * Real.log 2 + Real.log (p : ℝ) := by
    have h4 : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
    rw [Real.log_mul (by norm_num) (by linarith), h4, Real.log_pow]
    ring
  have hlog_ratio : Real.log ((n : ℝ) + 2) ≤ (1 + 2 / Real.log 2) * Real.log (p : ℝ) := by
    have hlog2_le_one : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hlog2_le_p : Real.log 2 ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by norm_num) hp_real
    have h2div : 0 ≤ 2 / Real.log 2 := by positivity
    have h2 : 2 * Real.log 2 ≤ (2 / Real.log 2) * Real.log (p : ℝ) := by
      calc
        2 * Real.log 2 ≤ 2 := by linarith
        _ = (2 / Real.log 2) * Real.log 2 := by
            have hne : Real.log 2 ≠ 0 := hlog2_pos.ne'
            field_simp [hne]
        _ ≤ (2 / Real.log 2) * Real.log (p : ℝ) :=
            mul_le_mul_of_nonneg_left hlog2_le_p h2div
    calc
      Real.log ((n : ℝ) + 2) ≤ Real.log (4 * (p : ℝ)) := hlog_n2_le
      _ = 2 * Real.log 2 + Real.log (p : ℝ) := hlog4p
      _ ≤ (2 / Real.log 2) * Real.log (p : ℝ) + Real.log (p : ℝ) := by linarith [h2]
      _ = (1 + 2 / Real.log 2) * Real.log (p : ℝ) := by ring
  have hRmax : R ≤ max R 1 := le_max_left _ _
  have h1max : 1 ≤ max R 1 := le_max_right _ _
  have hnum_gt : R * Real.log ((n : ℝ) + 2) < ((q - p : ℕ) : ℝ) / 8 := by
    have hmul : (max R 1) * Real.log ((n : ℝ) + 2) ≤
        (max R 1) * (1 + 2 / Real.log 2) * Real.log (p : ℝ) := by
      calc
        (max R 1) * Real.log ((n : ℝ) + 2)
            ≤ (max R 1) * ((1 + 2 / Real.log 2) * Real.log (p : ℝ)) :=
                mul_le_mul_of_nonneg_left hlog_ratio (by linarith)
        _ = (max R 1) * (1 + 2 / Real.log 2) * Real.log (p : ℝ) := by ring
    have hR1 : R * Real.log ((n : ℝ) + 2) ≤ (max R 1) * Real.log ((n : ℝ) + 2) :=
      mul_le_mul_of_nonneg_right hRmax hlog_n2_pos.le
    have hR'_gt : 8 * (max R 1) * (1 + 2 / Real.log 2) < R' := by
      dsimp only [R']
      linarith
    have hgap' : 8 * (max R 1) * (1 + 2 / Real.log 2) * Real.log (p : ℝ) < ((q - p : ℕ) : ℝ) := by
      calc
        8 * (max R 1) * (1 + 2 / Real.log 2) * Real.log (p : ℝ)
            < R' * Real.log (p : ℝ) := mul_lt_mul_of_pos_right hR'_gt hlog_p_pos
        _ < ((q - p : ℕ) : ℝ) := hgap
    linarith
  exact (lt_div_iff₀ hlog_n2_pos).mpr (lt_of_lt_of_le hnum_gt hn_dev)

end A377090
