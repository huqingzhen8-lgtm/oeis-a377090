import A377090.Basic
import A377090.AnalyticInputs

/-!
# Theorem 2: Independent Quantitative Prefix Coverage Proof

This file formalizes Section 3 of the paper independently of `A377090.Surjectivity`, working
strictly inside finite prefixes `S_n = {a(0), …, a(n)}`. It proves:

* **Lemma 3.1** (`maxPrefixRadius_bounds`): `n / 2 ≤ M_n ≤ C_M * n * log (2 * n)` for `n ≥ 2`.
* **Theorem 2** (`prefix_coverage_lower_bound`): under `GoldbachMeanSquareInput`, the coverage
  radius `k_n = prefixCoverage n` satisfies `c₁ * n / (log n)^4 ≤ k_n` for all sufficiently
  large `n`.
* **Corollary (`a377090_surjective_of_prefix_coverage`)**: independent surjectivity of `a377090`
  from quantitative prefix coverage.
-/

namespace A377090

open Finset Filter

section BasicPrefixDefinitions

open Classical in
/-- Maximum prefix radius `M_n = max_{0 ≤ j ≤ n} |a(j)|`. -/
def maxPrefixRadius (n : ℕ) : ℕ :=
  (prefixSet n).sup Int.natAbs

theorem le_maxPrefixRadius_of_mem {n : ℕ} {x : ℤ} (hx : x ∈ prefixSet n) :
    x.natAbs ≤ maxPrefixRadius n :=
  Finset.le_sup (f := Int.natAbs) hx

theorem natAbs_le_maxPrefixRadius {n j : ℕ} (hj : j ≤ n) :
    (a377090 j).natAbs ≤ maxPrefixRadius n :=
  le_maxPrefixRadius_of_mem (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega)))

theorem exists_omitted_natAbs (n : ℕ) :
    ∃ k : ℕ, ∃ h : ℤ, h.natAbs = k ∧ h ∉ prefixSet n := by
  refine ⟨maxPrefixRadius n + 1, ((maxPrefixRadius n + 1 : ℕ) : ℤ), Int.natAbs_natCast _, ?_⟩
  intro hmem
  have hle := le_maxPrefixRadius_of_mem hmem
  rw [Int.natAbs_natCast] at hle
  omega

/-- Smallest absolute value omitted from `{a(0), …, a(n)}`:
`k_n = min { |h| : h ∈ ℤ \ prefixSet n }`. -/
noncomputable def prefixCoverage (n : ℕ) : ℕ :=
  by classical exact Nat.find (exists_omitted_natAbs n)

theorem prefixCoverage_exists_omitted (n : ℕ) :
    ∃ h : ℤ, h.natAbs = prefixCoverage n ∧ h ∉ prefixSet n := by
  classical
  exact Nat.find_spec (exists_omitted_natAbs n)

theorem prefixCoverage_mem_prefixSet {n : ℕ} {z : ℤ} (hz : z.natAbs < prefixCoverage n) :
    z ∈ prefixSet n := by
  classical
  by_contra hnot
  unfold prefixCoverage at hz
  exact Nat.find_min (exists_omitted_natAbs n) hz ⟨z, rfl, hnot⟩

theorem prefixCoverage_pos (n : ℕ) : 1 ≤ prefixCoverage n := by
  by_contra hzero
  have h0 : prefixCoverage n = 0 := by omega
  obtain ⟨h, hh_abs, hh_not⟩ := prefixCoverage_exists_omitted n
  have hz : h = 0 := by omega
  subst hz
  exact hh_not (Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n), a377090_zero⟩)

theorem prefixCoverage_le_half_add_one (n : ℕ) : 2 * prefixCoverage n ≤ n + 2 := by
  have hk_pos : 1 ≤ prefixCoverage n := prefixCoverage_pos n
  let k1 : ℕ := prefixCoverage n - 1
  let box : Finset ℤ := Finset.Icc (-(k1 : ℤ)) (k1 : ℤ)
  have hsub : box ⊆ prefixSet n := by
    intro z hz
    rcases Finset.mem_Icc.mp hz with ⟨hz1, hz2⟩
    exact prefixCoverage_mem_prefixSet (by dsimp only [k1] at hz1 hz2; omega)
  have hbox_card : box.card = 2 * k1 + 1 := by
    rw [Int.card_Icc]
    omega
  have hpref_card : (prefixSet n).card ≤ n + 1 :=
    Finset.card_image_le.trans_eq (Finset.card_range (n + 1))
  have hle := Finset.card_le_card hsub
  omega

end BasicPrefixDefinitions

section RadiusBounds

/-- **Lemma 3.1 (Control of the Maximum Prefix Radius)**:
For `n ≥ 2`, `n / 2 ≤ M_n ≤ C_M * n * log (2 * n)` for a universal constant `C_M > 0`,
using only Chebyshev's bound proved in `AnalyticInputs`. -/
theorem maxPrefixRadius_bounds :
    ∃ C_M : ℝ, 0 < C_M ∧ ∀ n : ℕ, 2 ≤ n →
      (n : ℝ) / 2 ≤ (maxPrefixRadius n : ℝ) ∧
      (maxPrefixRadius n : ℝ) ≤ C_M * (n : ℝ) * Real.log (2 * (n : ℝ)) := by
  obtain ⟨C, hC_pos, hcheb⟩ := chebyshev_le_mul_log_of_primeCounting_le
  have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  let C_M : ℝ := C + 1 / (2 * Real.log 4)
  have hCM_pos : 0 < C_M := by positivity
  refine ⟨C_M, hCM_pos, fun n hn => ?_⟩
  let M : ℕ := maxPrefixRadius n
  have hlower_nat : n ≤ 2 * M := by
    have hsub : prefixSet n ⊆ Finset.Icc (-(M : ℤ)) (M : ℤ) := by
      intro x hx
      have hle := le_maxPrefixRadius_of_mem hx
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hpref_card : (prefixSet n).card = n + 1 := by
      rw [prefixSet, Finset.card_image_of_injOn]
      · exact Finset.card_range (n + 1)
      · intro x _ y _ hxy
        exact a377090_injective hxy
    have hbox_card : (Finset.Icc (-(M : ℤ)) (M : ℤ)).card = 2 * M + 1 := by
      rw [Int.card_Icc]
      omega
    have hle := Finset.card_le_card hsub
    omega
  have hlower_real : (n : ℝ) / 2 ≤ (M : ℝ) := by
    have : (n : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast hlower_nat
    linarith
  refine ⟨hlower_real, ?_⟩
  have hM_pos : 1 ≤ M := by omega
  have hex : ∃ j : ℕ, j ≤ n ∧ (a377090 j).natAbs = M := by
    have hne : (prefixSet n).Nonempty :=
      ⟨a377090 0, Finset.mem_image_of_mem _ (Finset.mem_range.mpr (Nat.zero_lt_succ n))⟩
    obtain ⟨x, hx_mem, hx_sup⟩ := Finset.exists_mem_eq_sup (prefixSet n) hne Int.natAbs
    rcases Finset.mem_image.mp hx_mem with ⟨j, hj_rng, rfl⟩
    have hj_le : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj_rng)
    exact ⟨j, hj_le, hx_sup.symm⟩
  classical
  let j₀ : ℕ := Nat.find hex
  have hj₀_spec : j₀ ≤ n ∧ (a377090 j₀).natAbs = M := Nat.find_spec hex
  have hj₀_ne : j₀ ≠ 0 := by
    intro hj₀_zero
    have ha0 : (a377090 0).natAbs = M := by simpa [hj₀_zero] using hj₀_spec.2
    rw [a377090_zero, Int.natAbs_zero] at ha0
    omega
  let j₁ : ℕ := j₀ - 1
  have hj₁_succ : j₁ + 1 = j₀ := Nat.sub_add_cancel (Nat.pos_of_ne_zero hj₀_ne)
  have hj₁_lt : j₁ < j₀ := by omega
  have hj₁_le_n : j₁ ≤ n := by omega
  let y : ℤ := a377090 j₁
  have hy_lt_M : y.natAbs < M := by
    have hle : y.natAbs ≤ M := natAbs_le_maxPrefixRadius hj₁_le_n
    have hne : y.natAbs ≠ M := by
      intro heq
      exact Nat.find_min hex hj₁_lt ⟨hj₁_le_n, heq⟩
    omega
  let s : ℤ := if 0 ≤ y then 1 else -1
  let w : ℕ → ℤ := fun p => y - s * (p : ℤ)
  let P_rng : Finset ℕ := (Finset.range M).filter Nat.Prime
  have hPrng_le : P_rng.card ≤ (prefixSet j₁).card := by
    refine Finset.card_le_card_of_injOn w ?_ ?_
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp_rng, hp_prime⟩
      have hp_lt : p < M := Finset.mem_range.mp hp_rng
      have hp_two : 2 ≤ p := hp_prime.two_le
      have hw_lt_M : (w p).natAbs < M := by
        dsimp only [w, s]
        split_ifs <;> omega
      by_contra hw_not
      have hw_prime : Nat.Prime (w p - y).natAbs := by
        have hsub : w p - y = -(s * (p : ℤ)) := by
          dsimp only [w]
          ring
        rw [hsub, Int.natAbs_neg, Int.natAbs_mul]
        have hs_abs : s.natAbs = 1 := by dsimp only [s]; split_ifs <;> decide
        rw [hs_abs, one_mul, Int.natAbs_natCast]
        exact hp_prime
      have hgreedy : (a377090 (j₁ + 1)).natAbs ≤ (w p).natAbs :=
        a377090_greedy_abs hw_not hw_prime
      rw [hj₁_succ, hj₀_spec.2] at hgreedy
      omega
    · intro p₁ _ p₂ _ heq
      dsimp only [w, s] at heq
      split_ifs at heq <;> omega
  have hpi_le_n : Nat.primeCounting (M - 1) ≤ n := by
    have hpi_eq : Nat.primeCounting (M - 1) = P_rng.card := by
      rw [primeCounting_eq_card_filter, Nat.sub_add_cancel hM_pos]
    have hpref1_card : (prefixSet j₁).card ≤ j₁ + 1 :=
      Finset.card_image_le.trans_eq (Finset.card_range (j₁ + 1))
    omega
  have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hpiR : (Nat.primeCounting (M - 1) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpi_le_n
  have hcheb_M : ((M - 1 : ℕ) : ℝ) ≤ C * (n : ℝ) * Real.log (2 * (n : ℝ)) :=
    hcheb (M - 1) (n : ℝ) hn_ge1 hpiR
  have hM_real : (M : ℝ) ≤ ((M - 1 : ℕ) : ℝ) + 1 := by
    have : M ≤ (M - 1) + 1 := by omega
    exact_mod_cast this
  have hn_real : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog_ge : Real.log 4 ≤ Real.log (2 * (n : ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith)
  have h1_le : (1 : ℝ) ≤ (1 / (2 * Real.log 4)) * (n : ℝ) * Real.log (2 * (n : ℝ)) := by
    have hmul : 2 * Real.log 4 ≤ (n : ℝ) * Real.log (2 * (n : ℝ)) := by nlinarith
    calc
      (1 : ℝ) = (1 / (2 * Real.log 4)) * (2 * Real.log 4) := by field_simp
      _ ≤ (1 / (2 * Real.log 4)) * ((n : ℝ) * Real.log (2 * (n : ℝ))) := by gcongr
      _ = (1 / (2 * Real.log 4)) * (n : ℝ) * Real.log (2 * (n : ℝ)) := by ring
  calc
    (M : ℝ) ≤ ((M - 1 : ℕ) : ℝ) + 1 := hM_real
    _ ≤ C * (n : ℝ) * Real.log (2 * (n : ℝ)) +
        (1 / (2 * Real.log 4)) * (n : ℝ) * Real.log (2 * (n : ℝ)) := by linarith
    _ = C_M * (n : ℝ) * Real.log (2 * (n : ℝ)) := by dsimp only [C_M]; ring

end RadiusBounds

section Step1OppositeParity

/-- **Step 1 of Theorem 2**: For every `n`, there exist `h₀, h₁ ∉ prefixSet n` of opposite parity
with `max (1, |h₀|, |h₁|) ≤ C_K * (k_n + 1) * log (2 * (k_n + 1))`. -/
theorem exists_opposite_parity_prefix_omitted :
    ∃ C_K : ℝ, 0 < C_K ∧ ∀ n : ℕ, ∃ h₀ h₁ : ℤ,
      h₀ ∉ prefixSet n ∧ h₁ ∉ prefixSet n ∧ h₀ % 2 = 0 ∧ h₁ % 2 = 1 ∧
      (max 1 (max h₀.natAbs h₁.natAbs) : ℝ) ≤
        C_K * ((prefixCoverage n : ℝ) + 1) * Real.log (2 * ((prefixCoverage n : ℝ) + 1)) := by
  obtain ⟨C_p, hC_p_pos, hnth⟩ := chebyshev_nth_prime_le
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C_K : ℝ := 6 * C_p + 1 / Real.log 2
  have hCK_pos : 0 < C_K := by positivity
  refine ⟨C_K, hCK_pos, fun n => ?_⟩
  let k : ℕ := prefixCoverage n
  have hk_pos : 1 ≤ k := prefixCoverage_pos n
  obtain ⟨h, hh_abs, hh_not⟩ := prefixCoverage_exists_omitted n
  classical
  let Q : Finset ℕ := (Finset.range (2 * k + 2)).image (fun j => Nat.nth Nat.Prime (j + 1))
  have hQ_card : Q.card = 2 * k + 2 := by
    rw [Finset.card_image_of_injOn]
    · exact Finset.card_range (2 * k + 2)
    · intro j₁ _ j₂ _ heq
      have hinj := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective
      have := hinj heq
      omega
  let Qbad : Finset ℕ := Q.filter (fun q : ℕ => h + (q : ℤ) ∈ prefixSet n)
  have hQbad_le : Qbad.card ≤ 2 * k + 1 := by
    let idxOf : ℕ → ℕ := fun q =>
      if hq : h + (q : ℤ) ∈ prefixSet n then
        Nat.find (Finset.mem_image.mp hq)
      else 0
    have hcard_eq : Qbad.card = (Qbad.image idxOf).card := by
      symm
      apply Finset.card_image_of_injOn
      intro q₁ hq₁ q₂ hq₂ heq
      dsimp only [idxOf] at heq
      have h1 : h + (q₁ : ℤ) ∈ prefixSet n := (Finset.mem_filter.mp hq₁).2
      have h2 : h + (q₂ : ℤ) ∈ prefixSet n := (Finset.mem_filter.mp hq₂).2
      simp only [h1, h2, ↓reduceDIte] at heq
      have hs1 := Nat.find_spec (Finset.mem_image.mp h1)
      have hs2 := Nat.find_spec (Finset.mem_image.mp h2)
      rw [heq, hs2.2] at hs1
      omega
    have hsub : Qbad.image idxOf ⊆
        (Finset.range (n + 1)).filter (fun idx => Nat.Prime (a377090 idx - h).natAbs) := by
      intro idx hidx
      rcases Finset.mem_image.mp hidx with ⟨q, hq, rfl⟩
      have hqQ : q ∈ Q := (Finset.mem_filter.mp hq).1
      rcases Finset.mem_image.mp hqQ with ⟨j, _, rfl⟩
      have hq_prime : Nat.Prime (Nat.nth Nat.Prime (j + 1)) :=
        Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (j + 1)
      have hmem : h + (Nat.nth Nat.Prime (j + 1) : ℤ) ∈ prefixSet n :=
        (Finset.mem_filter.mp hq).2
      dsimp only [idxOf]
      simp only [hmem, ↓reduceDIte]
      have hs := Nat.find_spec (Finset.mem_image.mp hmem)
      refine Finset.mem_filter.mpr ⟨hs.1, ?_⟩
      rw [hs.2]
      have hsub : (h + (Nat.nth Nat.Prime (j + 1) : ℤ) - h).natAbs = Nat.nth Nat.Prime (j + 1) := by
        rw [add_sub_cancel_left, Int.natAbs_natCast]
      rwa [hsub]
    have hle_neigh := prefix_omitted_neighbors_card_le n hh_not
    rw [hcard_eq]
    exact (Finset.card_le_card hsub).trans hle_neigh |>.trans (by omega)
  have hdiff_ne : (Q \ Qbad).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    have hle := Finset.card_le_card hsub
    omega
  obtain ⟨q, hq_diff⟩ := hdiff_ne
  rcases Finset.mem_sdiff.mp hq_diff with ⟨hq_Q, hq_not_bad⟩
  rcases Finset.mem_image.mp hq_Q with ⟨j, hj_rng, rfl⟩
  have hj_lt : j < 2 * k + 2 := Finset.mem_range.mp hj_rng
  have hq_prime : Nat.Prime (Nat.nth Nat.Prime (j + 1)) :=
    Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (j + 1)
  have hq_gt2 : 2 < Nat.nth Nat.Prime (j + 1) := by
    have h02 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
    rw [← h02]
    exact Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.zero_lt_succ j)
  have hq_odd : Nat.nth Nat.Prime (j + 1) % 2 = 1 := by
    rcases hq_prime.eq_two_or_odd with heq | hodd
    · omega
    · exact hodd
  let h' : ℤ := h + (Nat.nth Nat.Prime (j + 1) : ℤ)
  have hh'_not : h' ∉ prefixSet n := fun hmem =>
    hq_not_bad (Finset.mem_filter.mpr ⟨hq_Q, hmem⟩)
  have hq_bound : (Nat.nth Nat.Prime (j + 1) : ℝ) ≤
      6 * C_p * ((k : ℝ) + 1) * Real.log (2 * ((k : ℝ) + 1)) := by
    have hj_bound := hnth (j + 1)
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
    have hj_le_k : ((j + 1 : ℕ) : ℝ) + 1 ≤ 3 * ((k : ℝ) + 1) := by
      have : j + 2 ≤ 3 * (k + 1) := by omega
      exact_mod_cast this
    have hlog2k_pos : 0 < Real.log (2 * ((k : ℝ) + 1)) := Real.log_pos (by linarith)
    have hj_pos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) + 1 := by positivity
    have hlog_le : Real.log (2 * (((j + 1 : ℕ) : ℝ) + 1)) ≤ 2 * Real.log (2 * ((k : ℝ) + 1)) := by
      have hmul_le : 2 * (((j + 1 : ℕ) : ℝ) + 1) ≤ 3 * (2 * ((k : ℝ) + 1)) := by linarith
      have hlog1 : Real.log (2 * (((j + 1 : ℕ) : ℝ) + 1)) ≤
          Real.log (3 * (2 * ((k : ℝ) + 1))) := Real.log_le_log (by positivity) hmul_le
      have hlog3 : Real.log (3 * (2 * ((k : ℝ) + 1))) =
          Real.log 3 + Real.log (2 * ((k : ℝ) + 1)) :=
        Real.log_mul (by norm_num) (by linarith)
      have hlog3_le : Real.log 3 ≤ Real.log (2 * ((k : ℝ) + 1)) :=
        Real.log_le_log (by norm_num) (by linarith)
      linarith
    have hlog_j_nonneg : 0 ≤ Real.log (2 * (((j + 1 : ℕ) : ℝ) + 1)) :=
      Real.log_nonneg (by linarith)
    calc
      (Nat.nth Nat.Prime (j + 1) : ℝ)
          ≤ C_p * (((j + 1 : ℕ) : ℝ) + 1) * Real.log (2 * (((j + 1 : ℕ) : ℝ) + 1)) := hj_bound
      _ ≤ C_p * (3 * ((k : ℝ) + 1)) * (2 * Real.log (2 * ((k : ℝ) + 1))) := by
          gcongr
      _ = 6 * C_p * ((k : ℝ) + 1) * Real.log (2 * ((k : ℝ) + 1)) := by ring
  have hmax_bound : (max 1 (max h.natAbs h'.natAbs) : ℝ) ≤
      C_K * ((k : ℝ) + 1) * Real.log (2 * ((k : ℝ) + 1)) := by
    have hmax_nat : max 1 (max h.natAbs h'.natAbs) ≤ k + Nat.nth Nat.Prime (j + 1) := by
      have hh'_abs : h'.natAbs ≤ k + Nat.nth Nat.Prime (j + 1) := by
        dsimp only [h']
        omega
      omega
    have hk_le_real : (max 1 (max h.natAbs h'.natAbs) : ℝ) ≤
        (k : ℝ) + (Nat.nth Nat.Prime (j + 1) : ℝ) := by exact_mod_cast hmax_nat
    have hk1_pos : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
    have hk_le_mul : (k : ℝ) ≤ (1 / Real.log 2) * ((k : ℝ) + 1) * Real.log (2 * ((k : ℝ) + 1)) := by
      have hlog_ge : Real.log 2 ≤ Real.log (2 * ((k : ℝ) + 1)) :=
        Real.log_le_log (by norm_num) (by
          have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
          linarith)
      have hmul : (k : ℝ) * Real.log 2 ≤ ((k : ℝ) + 1) * Real.log (2 * ((k : ℝ) + 1)) := by
        nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
      calc
        (k : ℝ) = (1 / Real.log 2) * ((k : ℝ) * Real.log 2) := by field_simp
        _ ≤ (1 / Real.log 2) * (((k : ℝ) + 1) * Real.log (2 * ((k : ℝ) + 1))) := by gcongr
        _ = (1 / Real.log 2) * ((k : ℝ) + 1) * Real.log (2 * ((k : ℝ) + 1)) := by ring
    calc
      (max 1 (max h.natAbs h'.natAbs) : ℝ)
          ≤ (k : ℝ) + (Nat.nth Nat.Prime (j + 1) : ℝ) := hk_le_real
      _ ≤ (1 / Real.log 2) * ((k : ℝ) + 1) * Real.log (2 * ((k : ℝ) + 1)) +
          6 * C_p * ((k : ℝ) + 1) * Real.log (2 * ((k : ℝ) + 1)) := by linarith
      _ = C_K * ((k : ℝ) + 1) * Real.log (2 * ((k : ℝ) + 1)) := by dsimp only [C_K]; ring
  by_cases hmod : h % 2 = 0
  · refine ⟨h, h', hh_not, hh'_not, hmod, ?_, ?_⟩
    · dsimp only [h']; omega
    · exact hmax_bound
  · refine ⟨h', h, hh'_not, hh_not, ?_, ?_, ?_⟩
    · dsimp only [h']; omega
    · omega
    · exact (le_of_eq (by rw [max_comm (h'.natAbs : ℝ) (h.natAbs : ℝ)])).trans hmax_bound

end Step1OppositeParity

section Step2DyadicAndContraction

private theorem eventually_pow_log_lt_const_mul_self_pc (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, Real.log X ^ k < ε * X := by
  have ht : Tendsto (fun X : ℝ => Real.log X ^ k / (1 * X + 0)) atTop (nhds 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 k one_ne_zero
  have hev := ht.eventually (eventually_lt_nhds hε)
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with X hX hX0
  simp only [one_mul, add_zero] at hX
  exact (div_lt_iff₀ hX0).mp hX

/-- **Step 2a**: Dyadic Goldbach exceptional set bound across `[1, 2M]`. -/
private theorem dyadic_goldbach_exceptional_card (hG : GoldbachMeanSquareInput) :
    ∃ c C_exc : ℝ, 0 < c ∧ 0 < C_exc ∧ ∃ M₀ : ℕ, 16 ≤ M₀ ∧
      ∀ M : ℕ, M₀ ≤ M →
        let L : ℝ := Real.log (2 * (M : ℝ))
        let E_even : Finset ℕ := (Finset.Icc 1 (2 * M)).filter
          (fun m : ℕ => Even m ∧ (goldbachCount m : ℝ) < c * (m : ℝ) / L ^ 2)
        (E_even.card : ℝ) ≤ C_exc * (M : ℝ) / L ^ 4 := by
  obtain ⟨c, hc_pos, hgold⟩ := goldbach_uniform_lower_bound hG
  obtain ⟨C₄, hC₄_pos, hbad4⟩ := hgold 4 (by norm_num)
  let C_exc : ℝ := 1 + 1024 * C₄
  have hCexc_pos : 0 < C_exc := by positivity
  have hev : ∀ᶠ y : ℝ in atTop,
      2 * hG.X₀ ^ 2 ≤ y ∧ (32 : ℝ) ≤ y ∧ Real.log y ^ 8 < (1 / 2 : ℝ) * y :=
    (eventually_ge_atTop (2 * hG.X₀ ^ 2)).and <|
      (eventually_ge_atTop (32 : ℝ)).and <|
      eventually_pow_log_lt_const_mul_self_pc 8 (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.mp hev
  let M₀ : ℕ := Nat.ceil (Y₀ / 2) + 16
  refine ⟨c, C_exc, hc_pos, hCexc_pos, M₀, by omega, fun M hM => ?_⟩
  intro L E_even
  have hy_ge : Y₀ ≤ 2 * (M : ℝ) := by
    have hceil : Y₀ / 2 ≤ (Nat.ceil (Y₀ / 2) : ℝ) := Nat.le_ceil _
    have hm : (Nat.ceil (Y₀ / 2) : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : Nat.ceil (Y₀ / 2) ≤ M)
    linarith
  obtain ⟨hX₀_sq, h32, hlog8⟩ := hY₀ (2 * (M : ℝ)) hy_ge
  have hM16 : (16 : ℝ) ≤ (M : ℝ) := by linarith
  have hM_pos : 0 < (M : ℝ) := by linarith
  have hM_nat16 : 16 ≤ M := by exact_mod_cast hM16
  have hL_gt1 : 1 < L := by
    have h4 : (4 : ℝ) < 2 * (M : ℝ) := by linarith
    have hexp1 : Real.exp 1 < 2 * (M : ℝ) := by
      have := Real.exp_one_lt_d9
      linarith
    simpa [L] using Real.log_lt_log (Real.exp_pos 1) hexp1 |>.trans_eq' (Real.log_exp 1)
  have hL_pos : 0 < L := by linarith
  have hsqrt_ge_X₀ : hG.X₀ ≤ Real.sqrt (M : ℝ) := by
    have hX₀_nonneg : 0 ≤ hG.X₀ := by linarith [hG.hX₀]
    have hsq : hG.X₀ ^ 2 ≤ (M : ℝ) := by linarith
    calc
      hG.X₀ = Real.sqrt (hG.X₀ ^ 2) := (Real.sqrt_sq hX₀_nonneg).symm
      _ ≤ Real.sqrt (M : ℝ) := Real.sqrt_le_sqrt hsq
  have hL4_le_sqrt : L ^ 4 ≤ Real.sqrt (M : ℝ) := by
    have h8_le : (L ^ 4) ^ 2 ≤ (M : ℝ) := by
      have heq : (L ^ 4) ^ 2 = Real.log (2 * (M : ℝ)) ^ 8 := by dsimp only [L]; ring
      linarith
    calc
      L ^ 4 = Real.sqrt ((L ^ 4) ^ 2) := (Real.sqrt_sq (pow_nonneg hL_pos.le 4)).symm
      _ ≤ Real.sqrt (M : ℝ) := Real.sqrt_le_sqrt h8_le
  let E_small : Finset ℕ := E_even.filter (fun m : ℕ => (m : ℝ) ≤ Real.sqrt (M : ℝ))
  let E_large : Finset ℕ := E_even.filter (fun m : ℕ => Real.sqrt (M : ℝ) < (m : ℝ))
  have hsplit : E_even.card ≤ E_small.card + E_large.card := by
    have hsub : E_even ⊆ E_small ∪ E_large := by
      intro m hm
      rcases le_or_gt (m : ℝ) (Real.sqrt (M : ℝ)) with hm_le | hm_gt
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hm, hm_le⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hm, hm_gt⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hEsmall_card : (E_small.card : ℝ) ≤ (M : ℝ) / L ^ 4 := by
    have hsub : E_small ⊆ Finset.Icc 1 (Nat.floor (Real.sqrt (M : ℝ))) := by
      intro m hm
      rcases Finset.mem_filter.mp hm with ⟨hm_ev, hm_le⟩
      have hm_rng := (Finset.mem_filter.mp hm_ev).1
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm_rng).1
      exact Finset.mem_Icc.mpr ⟨hm1, Nat.le_floor hm_le⟩
    have hle_nat : E_small.card ≤ Nat.floor (Real.sqrt (M : ℝ)) := by
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc] at this
      omega
    have hle_sqrt : (E_small.card : ℝ) ≤ Real.sqrt (M : ℝ) :=
      (Nat.cast_le.mpr hle_nat).trans (Nat.floor_le (Real.sqrt_nonneg _))
    have hsqrt_div : Real.sqrt (M : ℝ) ≤ (M : ℝ) / L ^ 4 := by
      rw [le_div_iff₀ (pow_pos hL_pos 4)]
      calc
        Real.sqrt (M : ℝ) * L ^ 4
            ≤ Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) :=
                mul_le_mul_of_nonneg_left hL4_le_sqrt (Real.sqrt_nonneg _)
        _ = (M : ℝ) := Real.mul_self_sqrt hM_pos.le
    exact hle_sqrt.trans hsqrt_div
  let K_dy : ℕ := Nat.log 2 (2 * M) + 1
  let X : ℕ → ℝ := fun i => (2 * (M : ℝ)) / (2 : ℝ) ^ i
  let I_idx : Finset ℕ := (Finset.range K_dy).filter (fun i : ℕ => Real.sqrt (M : ℝ) < X i)
  let BadBlock : ℕ → Finset ℕ := fun i =>
    (Finset.range (Nat.floor (X i) + 1)).filter
      (fun m : ℕ => Even m ∧ X i / 2 ≤ (m : ℝ) ∧
        (goldbachCount m : ℝ) < c * X i / (Real.log (X i)) ^ 2)
  have hElarge_sub : E_large ⊆ I_idx.biUnion BadBlock := by
    intro m hm
    rcases Finset.mem_filter.mp hm with ⟨hm_even, hm_gt_sqrt⟩
    rcases Finset.mem_filter.mp hm_even with ⟨hm_Icc, hm_ev, hm_gb⟩
    rcases Finset.mem_Icc.mp hm_Icc with ⟨hm1, hm2M⟩
    let q : ℕ := (2 * M) / m
    have hq_pos : 0 < q := Nat.div_pos hm2M hm1
    let i : ℕ := Nat.log 2 q
    have hi_rng : i < K_dy := by
      have hq_le : q ≤ 2 * M := Nat.div_le_self _ _
      have hlog_le : Nat.log 2 q ≤ Nat.log 2 (2 * M) := Nat.log_mono_right hq_le
      omega
    have hpow_le : 2 ^ i ≤ q := Nat.pow_log_le_self 2 hq_pos.ne'
    have hpow_gt : q < 2 ^ (i + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
    have hmul_le : 2 ^ i * m ≤ 2 * M := (Nat.div_mul_le_self (2 * M) m).trans'
      (Nat.mul_le_mul_right m hpow_le)
    have hmul_gt : 2 * M < 2 ^ (i + 1) * m := by
      have hq1 : q + 1 ≤ 2 ^ (i + 1) := hpow_gt
      have hdiv : q * m + (2 * M) % m = 2 * M := by
        rw [mul_comm]
        exact Nat.div_add_mod (2 * M) m
      have hmod : (2 * M) % m < m := Nat.mod_lt _ hm1
      have h1 : 2 * M < (q + 1) * m := by
        calc
          2 * M = q * m + (2 * M) % m := hdiv.symm
          _ < q * m + m := by omega
          _ = (q + 1) * m := by ring
      exact h1.trans_le (Nat.mul_le_mul_right m hq1)
    have h2pow_pos : (0 : ℝ) < (2 : ℝ) ^ i := by positivity
    have hm_le_Xi : (m : ℝ) ≤ X i := by
      dsimp only [X]
      rw [le_div_iff₀ h2pow_pos]
      have hleR : ((2 ^ i * m : ℕ) : ℝ) ≤ ((2 * M : ℕ) : ℝ) := by exact_mod_cast hmul_le
      push_cast at hleR
      linarith
    have hXi_half_lt : X i / 2 < (m : ℝ) := by
      dsimp only [X]
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2)]
      rw [div_lt_iff₀ h2pow_pos]
      have hgtR : ((2 * M : ℕ) : ℝ) < ((2 ^ (i + 1) * m : ℕ) : ℝ) := by exact_mod_cast hmul_gt
      push_cast at hgtR
      rw [pow_succ'] at hgtR
      linarith
    have hi_mem : i ∈ I_idx :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi_rng, hm_gt_sqrt.trans_le hm_le_Xi⟩
    have hm_rng : m ∈ Finset.range (Nat.floor (X i) + 1) := by
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (Nat.le_floor hm_le_Xi)
    have hXi_ge_X₀ : hG.X₀ ≤ X i := hsqrt_ge_X₀.trans (hm_gt_sqrt.trans_le hm_le_Xi).le
    have hXi_ge4 : 4 ≤ X i := hG.hX₀.trans hXi_ge_X₀
    have hlogXi_pos : 0 < Real.log (X i) := Real.log_pos (by linarith)
    have hXi_le_2M : X i ≤ 2 * (M : ℝ) := by
      dsimp only [X]
      exact div_le_self (by positivity) (by
        have : (1 : ℝ) ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
        exact this)
    have hlogXi_le_L : Real.log (X i) ≤ L :=
      Real.log_le_log (by linarith) hXi_le_2M
    have hgb_Xi : (goldbachCount m : ℝ) < c * X i / (Real.log (X i)) ^ 2 := by
      have hle1 : c * (m : ℝ) / L ^ 2 ≤ c * X i / L ^ 2 := by
        gcongr
      have hle2 : c * X i / L ^ 2 ≤ c * X i / (Real.log (X i)) ^ 2 := by
        gcongr
      exact hm_gb.trans_le (hle1.trans hle2)
    refine Finset.mem_biUnion.mpr ⟨i, hi_mem, ?_⟩
    exact Finset.mem_filter.mpr ⟨hm_rng, hm_ev, hXi_half_lt.le, hgb_Xi⟩
  have hElarge_card : (E_large.card : ℝ) ≤ 1024 * C₄ * (M : ℝ) / L ^ 4 := by
    have hle_bi : E_large.card ≤ (I_idx.biUnion BadBlock).card := Finset.card_le_card hElarge_sub
    have hbi_le_sum : (I_idx.biUnion BadBlock).card ≤ ∑ i ∈ I_idx, (BadBlock i).card :=
      Finset.card_biUnion_le
    have hsumR : (E_large.card : ℝ) ≤ ∑ i ∈ I_idx, ((BadBlock i).card : ℝ) := by
      have h1 : (E_large.card : ℝ) ≤ ((∑ i ∈ I_idx, (BadBlock i).card : ℕ) : ℝ) := by
        exact_mod_cast hle_bi.trans hbi_le_sum
      simpa using h1
    have hterm_le : ∀ i ∈ I_idx,
        ((BadBlock i).card : ℝ) ≤ (512 * C₄ * (M : ℝ) / L ^ 4) * (1 / 2 : ℝ) ^ i := by
      intro i hi
      have hi_gt : Real.sqrt (M : ℝ) < X i := (Finset.mem_filter.mp hi).2
      have hXi_ge : hG.X₀ ≤ X i := hsqrt_ge_X₀.trans hi_gt.le
      have hblock_le : ((BadBlock i).card : ℝ) ≤ C₄ * X i / (Real.log (X i)) ^ 4 := by
        have hraw := hbad4 (X i) hXi_ge
        rw [← Real.rpow_natCast]
        exact hraw.trans_eq (by norm_num)
      have hL_le_4log : L ≤ 4 * Real.log (X i) := by
        have h2M_lt_sq : 2 * (M : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
        have hsq_eq : (M : ℝ) ^ 2 = (Real.sqrt (M : ℝ)) ^ 4 := by
          have : (Real.sqrt (M : ℝ)) ^ 2 = (M : ℝ) := Real.sq_sqrt hM_pos.le
          calc
            (M : ℝ) ^ 2 = ((Real.sqrt (M : ℝ)) ^ 2) ^ 2 := by rw [this]
            _ = (Real.sqrt (M : ℝ)) ^ 4 := by ring
        have h2M_lt_Xi4 : 2 * (M : ℝ) < (X i) ^ 4 := by
          have hpow : (Real.sqrt (M : ℝ)) ^ 4 < (X i) ^ 4 :=
            pow_lt_pow_left₀ hi_gt (Real.sqrt_nonneg _) (by norm_num)
          linarith
        have hlog_eq : Real.log ((X i) ^ 4) = 4 * Real.log (X i) := by
          rw [Real.log_pow]
          norm_num
        calc
          L = Real.log (2 * (M : ℝ)) := rfl
          _ ≤ Real.log ((X i) ^ 4) := Real.log_le_log (by positivity) h2M_lt_Xi4.le
          _ = 4 * Real.log (X i) := hlog_eq
      have hXi_ge4 : 4 ≤ X i := hG.hX₀.trans hXi_ge
      have hlogXi_pos : 0 < Real.log (X i) := Real.log_pos (by linarith)
      have hpow4_le : L ^ 4 ≤ 256 * (Real.log (X i)) ^ 4 := by
        have hpow := pow_le_pow_left₀ hL_pos.le hL_le_4log 4
        linarith [show (4 * Real.log (X i)) ^ 4 = 256 * (Real.log (X i)) ^ 4 by ring]
      have hfrac_le : 1 / (Real.log (X i)) ^ 4 ≤ 256 / L ^ 4 := by
        rw [div_le_div_iff₀ (pow_pos hlogXi_pos 4) (pow_pos hL_pos 4)]
        linarith
      calc
        ((BadBlock i).card : ℝ)
            ≤ C₄ * X i / (Real.log (X i)) ^ 4 := hblock_le
        _ = (C₄ * X i) * (1 / (Real.log (X i)) ^ 4) := by ring
        _ ≤ (C₄ * X i) * (256 / L ^ 4) := by gcongr
        _ = (512 * C₄ * (M : ℝ) / L ^ 4) * (1 / 2 : ℝ) ^ i := by
            dsimp only [X]
            rw [one_div, inv_pow]
            ring
    have hsum_le_sub : ∑ i ∈ I_idx, ((BadBlock i).card : ℝ) ≤
        ∑ i ∈ Finset.range K_dy, (512 * C₄ * (M : ℝ) / L ^ 4) * (1 / 2 : ℝ) ^ i := by
      calc
        ∑ i ∈ I_idx, ((BadBlock i).card : ℝ)
            ≤ ∑ i ∈ I_idx, (512 * C₄ * (M : ℝ) / L ^ 4) * (1 / 2 : ℝ) ^ i :=
                Finset.sum_le_sum hterm_le
        _ ≤ ∑ i ∈ Finset.range K_dy, (512 * C₄ * (M : ℝ) / L ^ 4) * (1 / 2 : ℝ) ^ i :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                  (fun _ _ _ => by positivity)
    have hgeom : ∑ i ∈ Finset.range K_dy, (1 / 2 : ℝ) ^ i ≤ 2 := by
      rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
      have hpos_pow : 0 ≤ (1 / 2 : ℝ) ^ K_dy := by positivity
      calc
        ((1 / 2 : ℝ) ^ K_dy - 1) / (1 / 2 - 1) = 2 - 2 * (1 / 2 : ℝ) ^ K_dy := by ring
        _ ≤ 2 := by linarith
    have hsum_geom :
        ∑ i ∈ Finset.range K_dy, (512 * C₄ * (M : ℝ) / L ^ 4) * (1 / 2 : ℝ) ^ i ≤
          1024 * C₄ * (M : ℝ) / L ^ 4 := by
      rw [← Finset.mul_sum]
      calc
        (512 * C₄ * (M : ℝ) / L ^ 4) * ∑ i ∈ Finset.range K_dy, (1 / 2 : ℝ) ^ i
            ≤ (512 * C₄ * (M : ℝ) / L ^ 4) * 2 :=
                mul_le_mul_of_nonneg_left hgeom (by positivity)
        _ = 1024 * C₄ * (M : ℝ) / L ^ 4 := by ring
    exact hsumR.trans (hsum_le_sub.trans hsum_geom)
  have hEevenR : (E_even.card : ℝ) ≤ (E_small.card : ℝ) + (E_large.card : ℝ) := by
    exact_mod_cast hsplit
  calc
    (E_even.card : ℝ) ≤ (M : ℝ) / L ^ 4 + 1024 * C₄ * (M : ℝ) / L ^ 4 := by linarith
    _ = C_exc * (M : ℝ) / L ^ 4 := by dsimp only [C_exc]; ring

/-- Ordered-to-unordered Goldbach bound: `r(m) ≤ 2 * U(m)`. -/
private theorem goldbachCount_le_two_mul_half (m : ℕ) :
    goldbachCount m ≤
      2 * ((Finset.range (m / 2 + 1)).filter
        (fun u : ℕ => Nat.Prime u ∧ Nat.Prime (m - u))).card := by
  let S := (Finset.range (m + 1)).filter (fun u : ℕ => Nat.Prime u ∧ Nat.Prime (m - u))
  let Uhalf := (Finset.range (m / 2 + 1)).filter (fun u : ℕ => Nat.Prime u ∧ Nat.Prime (m - u))
  let S_hi := S.filter (fun u : ℕ => m / 2 < u)
  have hS_split : S.card ≤ Uhalf.card + S_hi.card := by
    have hsub : S ⊆ Uhalf ∪ S_hi := by
      intro u hu
      rcases Finset.mem_filter.mp hu with ⟨_, hu_p, hv_p⟩
      rcases le_or_gt u (m / 2) with hle | hgt
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hu_p, hv_p⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hu, hgt⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hShi_le : S_hi.card ≤ Uhalf.card := by
    refine Finset.card_le_card_of_injOn (fun u => m - u) ?_ ?_
    · intro u hu
      have huS := (Finset.mem_filter.mp hu).1
      have hu_gt := (Finset.mem_filter.mp hu).2
      rcases Finset.mem_filter.mp huS with ⟨hu_rng, hu_p, hv_p⟩
      have hu_le : u ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu_rng)
      have hm_sub_lt : m - u < m / 2 + 1 := by omega
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm_sub_lt, hv_p, ?_⟩
      rwa [Nat.sub_sub_self hu_le]
    · intro u₁ hu₁ u₂ hu₂ heq
      have hu₁_le : u₁ ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp
        (Finset.mem_filter.mp (Finset.mem_filter.mp hu₁).1).1)
      have hu₂_le : u₂ ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp
        (Finset.mem_filter.mp (Finset.mem_filter.mp hu₂).1).1)
      dsimp only at heq
      omega
  change S.card ≤ 2 * Uhalf.card
  omega

private theorem natAbs_sub_mod_two_eq_zero {x b : ℤ} (h : (x - b) % 2 = 0) :
    (x - b).natAbs % 2 = 0 := by
  omega

/-- **Step 2b**: A non-exceptional term with `|a(j)| ≥ 6 * K` and `r(m) > 4 * K + 2`
contracts by at least `3 / 4`. -/
private theorem contraction_step {n j K : ℕ} {h₀ h₁ : ℤ}
    (hjn : j < n)
    (hh₀ : h₀ ∉ prefixSet n) (hh₁ : h₁ ∉ prefixSet n)
    (hh₀_even : h₀ % 2 = 0) (hh₁_odd : h₁ % 2 = 1)
    (hK_ge : max 1 (max h₀.natAbs h₁.natAbs) ≤ K)
    (hj_ge : 6 * K ≤ (a377090 j).natAbs)
    (hgb : 4 * K + 2 <
      goldbachCount (a377090 j - (if a377090 j % 2 = 0 then h₀ else h₁)).natAbs) :
    4 * (a377090 (j + 1)).natAbs ≤ 3 * (a377090 j).natAbs := by
  let x : ℤ := a377090 j
  let b : ℤ := if x % 2 = 0 then h₀ else h₁
  have hb_not : b ∉ prefixSet n := by
    dsimp only [b]; split_ifs <;> assumption
  have hb_abs : b.natAbs ≤ K := by
    dsimp only [b]; split_ifs <;> omega
  let m : ℕ := (x - b).natAbs
  let s : ℤ := if b ≤ x then 1 else -1
  have hx_eq : x = b + s * (m : ℤ) := by
    dsimp only [s, m]; split_ifs <;> omega
  let Uhalf : Finset ℕ :=
    (Finset.range (m / 2 + 1)).filter (fun u : ℕ => Nat.Prime u ∧ Nat.Prime (m - u))
  have hU_gt : 2 * K + 1 < Uhalf.card := by
    have hgb' : 4 * K + 2 < goldbachCount m := hgb
    have hle := goldbachCount_le_two_mul_half m
    change goldbachCount m ≤ 2 * Uhalf.card at hle
    omega
  let Ubad : Finset ℕ := Uhalf.filter (fun u : ℕ => b + s * (u : ℤ) ∈ prefixSet n)
  have hUbad_le : Ubad.card ≤ 2 * K + 1 := by
    classical
    let idxOf : ℕ → ℕ := fun u =>
      if hu : b + s * (u : ℤ) ∈ prefixSet n then
        Nat.find (Finset.mem_image.mp hu)
      else 0
    have hcard_eq : Ubad.card = (Ubad.image idxOf).card := by
      symm
      apply Finset.card_image_of_injOn
      intro u₁ hu₁ u₂ hu₂ heq
      dsimp only [idxOf] at heq
      have h1 : b + s * (u₁ : ℤ) ∈ prefixSet n := (Finset.mem_filter.mp hu₁).2
      have h2 : b + s * (u₂ : ℤ) ∈ prefixSet n := (Finset.mem_filter.mp hu₂).2
      simp only [h1, h2, ↓reduceDIte] at heq
      have hs1 := Nat.find_spec (Finset.mem_image.mp h1)
      have hs2 := Nat.find_spec (Finset.mem_image.mp h2)
      rw [heq, hs2.2] at hs1
      have hsu : s * (u₁ : ℤ) = s * (u₂ : ℤ) := by omega
      dsimp only [s] at hsu
      split_ifs at hsu <;> omega
    have hsub : Ubad.image idxOf ⊆
        (Finset.range (n + 1)).filter (fun idx => Nat.Prime (a377090 idx - b).natAbs) := by
      intro idx hidx
      rcases Finset.mem_image.mp hidx with ⟨u, hu, rfl⟩
      have huU : u ∈ Uhalf := (Finset.mem_filter.mp hu).1
      have hu_prime : Nat.Prime u := (Finset.mem_filter.mp huU).2.1
      have hmem : b + s * (u : ℤ) ∈ prefixSet n := (Finset.mem_filter.mp hu).2
      dsimp only [idxOf]
      simp only [hmem, ↓reduceDIte]
      have hs := Nat.find_spec (Finset.mem_image.mp hmem)
      refine Finset.mem_filter.mpr ⟨hs.1, ?_⟩
      rw [hs.2]
      have hsub : (b + s * (u : ℤ) - b).natAbs = u := by
        have : b + s * (u : ℤ) - b = s * (u : ℤ) := by ring
        rw [this, Int.natAbs_mul]
        have hs_abs : s.natAbs = 1 := by dsimp only [s]; split_ifs <;> decide
        rw [hs_abs, one_mul, Int.natAbs_natCast]
      rwa [hsub]
    have hle_neigh := prefix_omitted_neighbors_card_le n hb_not
    rw [hcard_eq]
    exact ((Finset.card_le_card hsub).trans hle_neigh).trans (by omega)
  have hdiff_ne : (Uhalf \ Ubad).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    have hle := Finset.card_le_card hsub
    omega
  obtain ⟨u, hu_diff⟩ := hdiff_ne
  rcases Finset.mem_sdiff.mp hu_diff with ⟨hu_U, hu_not_bad⟩
  rcases Finset.mem_filter.mp hu_U with ⟨hu_rng, _hu_prime, hv_prime⟩
  have hu_le_half : u ≤ m / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu_rng)
  let z : ℤ := b + s * (u : ℤ)
  have hz_not_n : z ∉ prefixSet n := fun hmem =>
    hu_not_bad (Finset.mem_filter.mpr ⟨hu_U, hmem⟩)
  have hz_not_j : z ∉ prefixSet j := by
    intro hmem
    apply hz_not_n
    rcases Finset.mem_image.mp hmem with ⟨t, ht, htz⟩
    have ht_lt : t < j + 1 := Finset.mem_range.mp ht
    rw [← htz]
    exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))
  have hzx_prime : Nat.Prime (z - x).natAbs := by
    have hu_le_m : u ≤ m := by omega
    have hsub : z - x = -(s * ((m - u : ℕ) : ℤ)) := by
      dsimp only [z]
      rw [hx_eq]
      dsimp only [s]
      split_ifs <;> omega
    rw [hsub, Int.natAbs_neg, Int.natAbs_mul]
    have hs_abs : s.natAbs = 1 := by dsimp only [s]; split_ifs <;> decide
    rw [hs_abs, one_mul, Int.natAbs_natCast]
    exact hv_prime
  have hgreedy : (a377090 (j + 1)).natAbs ≤ z.natAbs :=
    a377090_greedy_abs hz_not_j hzx_prime
  have hz_bound : z.natAbs ≤ K + m / 2 := by
    dsimp only [z, s]
    split_ifs <;> omega
  have hm_bound : m ≤ x.natAbs + K := by
    dsimp only [m]
    omega
  omega

end Step2DyadicAndContraction

section Step3SegmentCounting

private theorem pow_four_mul_le_pow_three_mul {f : ℕ → ℕ} {a : ℕ} (r : ℕ)
    (hstep : ∀ k < r, 4 * f (a + k + 1) ≤ 3 * f (a + k)) :
    4 ^ r * f (a + r) ≤ 3 ^ r * f a := by
  induction r with
  | zero => simp
  | succ r ih =>
      have ih' := ih (fun k hk => hstep k (by omega))
      have hlast := hstep r (Nat.lt_succ_self r)
      calc
        4 ^ (r + 1) * f (a + (r + 1))
            = 4 ^ r * (4 * f (a + r + 1)) := by rw [pow_succ, ← Nat.add_assoc]; ring
        _ ≤ 4 ^ r * (3 * f (a + r)) := Nat.mul_le_mul_left _ hlast
        _ = 3 * (4 ^ r * f (a + r)) := by ring
        _ ≤ 3 * (3 ^ r * f a) := Nat.mul_le_mul_left _ ih'
        _ = 3 ^ (r + 1) * f a := by rw [pow_succ]; ring

/-- Segment-counting bound by strong induction along `3 / 4`-contracting runs. -/
private theorem contracting_run_bound (n M R : ℕ) (f : ℕ → ℕ) (E : Finset ℕ)
    (hfM : ∀ j < n, f j ≤ M)
    (hstep : ∀ j < n, j ∉ E → 1 ≤ f j ∧ 4 * f (j + 1) ≤ 3 * f j)
    (hMR : 3 ^ R * M < 4 ^ R) :
    n ≤ (E.card + 1) * (R + 1) := by
  classical
  let q := n / (R + 1)
  have hblk : ∀ b < q, ∃ r : ℕ, r < R + 1 ∧ b * (R + 1) + r ∈ E := by
    intro b hb
    by_contra hnone
    push Not at hnone
    have hb_lt : b * (R + 1) + R < n := by
      have hmul : (b + 1) * (R + 1) ≤ q * (R + 1) :=
        Nat.mul_le_mul_right (R + 1) hb
      have hqn : q * (R + 1) ≤ n := Nat.div_mul_le_self n (R + 1)
      have : b * (R + 1) + (R + 1) = (b + 1) * (R + 1) := by ring
      omega
    have hstep_b : ∀ k < R, 4 * f (b * (R + 1) + k + 1) ≤ 3 * f (b * (R + 1) + k) := by
      intro k hk
      exact (hstep (b * (R + 1) + k) (by omega) (hnone k (by omega))).2
    have hcontract := pow_four_mul_le_pow_three_mul R hstep_b
    have hposR : 1 ≤ f (b * (R + 1) + R) :=
      (hstep (b * (R + 1) + R) hb_lt (hnone R (Nat.lt_succ_self R))).1
    have hfa_le : f (b * (R + 1)) ≤ M := hfM (b * (R + 1)) (by omega)
    have h4 : 4 ^ R ≤ 4 ^ R * f (b * (R + 1) + R) := Nat.le_mul_of_pos_right _ hposR
    have h3 : 3 ^ R * f (b * (R + 1)) ≤ 3 ^ R * M := Nat.mul_le_mul_left _ hfa_le
    omega
  let pick : ℕ → ℕ := fun b =>
    if hb : b < q then b * (R + 1) + Nat.find (hblk b hb) else 0
  have hq_le_E : q ≤ E.card := by
    have hcard_q : q = (Finset.range q).card := (Finset.card_range q).symm
    rw [hcard_q]
    refine Finset.card_le_card_of_injOn pick ?_ ?_
    · intro b hb
      have hbq : b < q := Finset.mem_range.mp hb
      dsimp only [pick]
      simp only [hbq, ↓reduceDIte]
      exact (Nat.find_spec (hblk b hbq)).2
    · intro b₁ hb₁ b₂ hb₂ heq
      have hb₁q : b₁ < q := Finset.mem_range.mp hb₁
      have hb₂q : b₂ < q := Finset.mem_range.mp hb₂
      dsimp only [pick] at heq
      simp only [hb₁q, hb₂q, ↓reduceDIte] at heq
      have hr₁ := (Nat.find_spec (hblk b₁ hb₁q)).1
      have hr₂ := (Nat.find_spec (hblk b₂ hb₂q)).1
      by_cases hlt : b₁ < b₂
      · have hle : b₁ + 1 ≤ b₂ := hlt
        nlinarith
      · by_cases hgt : b₂ < b₁
        · have hle : b₂ + 1 ≤ b₁ := hgt
          nlinarith
        · omega
  have hdiv : n < (q + 1) * (R + 1) := by
    have hdm := Nat.div_add_mod n (R + 1)
    have hml := Nat.mod_lt n (by omega : 0 < R + 1)
    have hmul : (R + 1) * q + n % (R + 1) = n := hdm
    calc
      n = (R + 1) * q + n % (R + 1) := hmul.symm
      _ = q * (R + 1) + n % (R + 1) := by ring
      _ < q * (R + 1) + (R + 1) := by omega
      _ = (q + 1) * (R + 1) := by ring
  have hmul_le : (q + 1) * (R + 1) ≤ (E.card + 1) * (R + 1) :=
    Nat.mul_le_mul_right (R + 1) (Nat.add_le_add_right hq_le_E 1)
  omega

/-- **Theorem 2 (Quantitative Prefix Coverage Rate)**:
Under `GoldbachMeanSquareInput` (and proved completely independently of `A377090.Surjectivity`),
there exist `c₁ > 0` and `N₁` such that for all `n ≥ N₁`,
`c₁ * n / (log n)^4 ≤ k_n`. -/
theorem prefix_coverage_lower_bound (hG : GoldbachMeanSquareInput) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ N₁ : ℕ, 2 ≤ N₁ ∧ ∀ n : ℕ, N₁ ≤ n →
      c₁ * (n : ℝ) / Real.log (n : ℝ) ^ 4 ≤ (prefixCoverage n : ℝ) := by
  obtain ⟨C_M, hCM_pos, hM_bounds⟩ := maxPrefixRadius_bounds
  obtain ⟨C_K, hCK_pos, hK_opp⟩ := exists_opposite_parity_prefix_omitted
  obtain ⟨c, C_exc, hc_pos, hCexc_pos, M₀, hM₀16, hdyadic⟩ :=
    dyadic_goldbach_exceptional_card hG
  have hlog43_pos : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  let C_R : ℝ := 1 / Real.log (4 / 3 : ℝ) + 2
  let C_T : ℝ := max 6 (9 / c)
  have hCR_pos : 0 < C_R := by positivity
  have hCT_pos : 0 < C_T := by positivity
  -- Threshold for L = log (2 * M_n) and n
  let A_abs : ℝ := 4 * C_exc * C_R * C_M
  let N₁ : ℕ :=
    max (2 * M₀) <|
    max (Nat.ceil (4 * C_M) + 4) <|
    Nat.ceil (Real.exp (Real.sqrt (8 * A_abs))) + 16
  have hN₁_ge4 : 4 ≤ N₁ := by
    have : Nat.ceil (4 * C_M) + 4 ≤ N₁ := le_trans (le_max_left _ _) (le_max_right _ _)
    omega
  have hN₁_ge16 : 16 ≤ N₁ := by
    have : Nat.ceil (Real.exp (Real.sqrt (8 * A_abs))) + 16 ≤ N₁ :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    omega
  let c₁ : ℝ := 1 / (1728 * C_T * C_R * C_K)
  have hc₁_pos : 0 < c₁ := by positivity
  refine ⟨c₁, hc₁_pos, N₁, by omega, fun n hn => ?_⟩
  let M : ℕ := maxPrefixRadius n
  have hM_ge_M₀ : M₀ ≤ M := by
    have hn_M₀ : 2 * M₀ ≤ n := hn.trans' (le_max_left _ _)
    have hM_lo := (hM_bounds n (by omega)).1
    have hM_nat : (M₀ : ℝ) ≤ (M : ℝ) := by
      have : (2 * M₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_M₀
      linarith
    exact_mod_cast hM_nat
  obtain ⟨hM_lo, hM_hi⟩ := hM_bounds n (by omega)
  let L : ℝ := Real.log (2 * (M : ℝ))
  have hM16 : 16 ≤ M := hM₀16.trans hM_ge_M₀
  have hM_pos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hL_ge_logn : Real.log (n : ℝ) ≤ L := by
    have hn_le_2M : (n : ℝ) ≤ 2 * (M : ℝ) := by linarith
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    exact Real.log_le_log hn_pos hn_le_2M
  have hlogn_gt1 : 1 < Real.log (n : ℝ) := by
    have hn16 : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hN₁_ge16.trans hn
    have hexp1 : Real.exp 1 < (n : ℝ) := by
      have := Real.exp_one_lt_d9
      linarith
    simpa using Real.log_lt_log (Real.exp_pos 1) hexp1 |>.trans_eq' (Real.log_exp 1)
  have hlogn_pos : 0 < Real.log (n : ℝ) := by linarith
  have hL_pos : 0 < L := by linarith
  have hL_gt1 : 1 < L := by linarith
  have hL_le_3logn : L ≤ 3 * Real.log (n : ℝ) := by
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have h4CM_le_n : 4 * C_M ≤ (n : ℝ) := by
      have hceil_le : Nat.ceil (4 * C_M) ≤ n := by
        have : Nat.ceil (4 * C_M) + 4 ≤ N₁ := le_trans (le_max_left _ _) (le_max_right _ _)
        omega
      exact (Nat.le_ceil _).trans (by exact_mod_cast hceil_le)
    have hlog2n_le : Real.log (2 * (n : ℝ)) ≤ 2 * (n : ℝ) := by
      linarith [Real.log_le_sub_one_of_pos (show 0 < 2 * (n : ℝ) by linarith)]
    have h2M_le_n3 : 2 * (M : ℝ) ≤ (n : ℝ) ^ 3 := by
      calc
        2 * (M : ℝ) ≤ 2 * (C_M * (n : ℝ) * Real.log (2 * (n : ℝ))) := by linarith
        _ ≤ 2 * (C_M * (n : ℝ) * (2 * (n : ℝ))) := by gcongr
        _ = (4 * C_M) * (n : ℝ) ^ 2 := by ring
        _ ≤ (n : ℝ) * (n : ℝ) ^ 2 := by gcongr
        _ = (n : ℝ) ^ 3 := by ring
    have hlog_pow3 : Real.log ((n : ℝ) ^ 3) = 3 * Real.log (n : ℝ) := by
      rw [Real.log_pow]
      norm_num
    calc
      L = Real.log (2 * (M : ℝ)) := rfl
      _ ≤ Real.log ((n : ℝ) ^ 3) := Real.log_le_log (by positivity) h2M_le_n3
      _ = 3 * Real.log (n : ℝ) := hlog_pow3
  let k : ℕ := prefixCoverage n
  have hk_pos : 1 ≤ k := prefixCoverage_pos n
  obtain ⟨h₀, h₁, hh₀, hh₁, hh₀_even, hh₁_odd, hopp_bound⟩ := hK_opp n
  let K : ℕ := max 1 (max h₀.natAbs h₁.natAbs)
  have hK_pos : 1 ≤ K := le_max_left _ _
  have hK_bound : (K : ℝ) ≤ C_K * ((k : ℝ) + 1) * Real.log (2 * ((k : ℝ) + 1)) := by
    dsimp only [K]
    push_cast
    exact hopp_bound
  let R : ℕ := Nat.floor (L / Real.log (4 / 3 : ℝ)) + 1
  have hR1_le : (R : ℝ) + 1 ≤ C_R * L := by
    have hfl : (Nat.floor (L / Real.log (4 / 3 : ℝ)) : ℝ) ≤ L / Real.log (4 / 3 : ℝ) :=
      Nat.floor_le (div_nonneg hL_pos.le hlog43_pos.le)
    calc
      (R : ℝ) + 1 = (Nat.floor (L / Real.log (4 / 3 : ℝ)) : ℝ) + 2 := by
          dsimp only [R]; push_cast; ring
      _ ≤ L / Real.log (4 / 3 : ℝ) + 2 := by linarith
      _ ≤ L / Real.log (4 / 3 : ℝ) + 2 * L := by nlinarith
      _ = C_R * L := by dsimp only [C_R]; ring
  have hMR : 3 ^ R * M < 4 ^ R := by
    have hlogM_le_L : Real.log (M : ℝ) < L :=
      Real.log_lt_log hM_pos (by linarith)
    have hgt_div : L / Real.log (4 / 3 : ℝ) < (R : ℝ) := by
      have := Nat.lt_floor_add_one (L / Real.log (4 / 3 : ℝ))
      dsimp only [R]
      push_cast
      linarith
    have hlogM_lt : Real.log (M : ℝ) < (R : ℝ) * Real.log (4 / 3 : ℝ) := by
      have h1 : Real.log (M : ℝ) / Real.log (4 / 3 : ℝ) < (R : ℝ) :=
        (div_lt_div_of_pos_right hlogM_le_L hlog43_pos).trans hgt_div
      exact (div_lt_iff₀ hlog43_pos).mp h1
    have hlog_eq : (R : ℝ) * Real.log (4 / 3 : ℝ) = Real.log ((4 / 3 : ℝ) ^ R) := by
      rw [Real.log_pow]
    have hM_lt_pow : (M : ℝ) < (4 / 3 : ℝ) ^ R := by
      have hpow_pos : 0 < (4 / 3 : ℝ) ^ R := by positivity
      rw [← Real.exp_log hM_pos, ← Real.exp_log hpow_pos]
      exact Real.exp_lt_exp.mpr (hlogM_lt.trans_eq hlog_eq)
    have h3R_pos : (0 : ℝ) < (3 : ℝ) ^ R := by positivity
    have hreal_ineq : (3 : ℝ) ^ R * (M : ℝ) < (4 : ℝ) ^ R := by
      calc
        (3 : ℝ) ^ R * (M : ℝ) < (3 : ℝ) ^ R * ((4 / 3 : ℝ) ^ R) :=
            mul_lt_mul_of_pos_left hM_lt_pow h3R_pos
        _ = (3 * (4 / 3 : ℝ)) ^ R := by rw [mul_pow]
        _ = (4 : ℝ) ^ R := by ring_nf
    exact_mod_cast hreal_ineq
  let T : ℕ := Nat.ceil (C_T * ((K : ℝ) + 1) * L ^ 2)
  have hT_ge_real : C_T * ((K : ℝ) + 1) * L ^ 2 ≤ (T : ℝ) := Nat.le_ceil _
  have hT_le_real : (T : ℝ) ≤ C_T * ((K : ℝ) + 1) * L ^ 2 + 1 := by
    have hceil_lt : (T : ℝ) < C_T * ((K : ℝ) + 1) * L ^ 2 + 1 := by
      exact Nat.ceil_lt_add_one (by positivity)
    exact hceil_lt.le
  have h6K_le_T : 6 * K ≤ T := by
    have h6_le_CT : (6 : ℝ) ≤ C_T := le_max_left _ _
    have hL2_ge1 : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ hL_gt1.le
    have h1 : (6 * K : ℝ) ≤ C_T * ((K : ℝ) + 1) * L ^ 2 := by
      calc
        (6 * K : ℝ) = 6 * (K : ℝ) * 1 := by ring
        _ ≤ C_T * ((K : ℝ) + 1) * L ^ 2 := by
            gcongr
            linarith
    exact_mod_cast h1.trans hT_ge_real
  let E_even : Finset ℕ := (Finset.Icc 1 (2 * M)).filter
    (fun m : ℕ => Even m ∧ (goldbachCount m : ℝ) < c * (m : ℝ) / L ^ 2)
  have hEeven_le : (E_even.card : ℝ) ≤ C_exc * (M : ℝ) / L ^ 4 := hdyadic M hM_ge_M₀
  let bFn : ℕ → ℤ := fun j => if a377090 j % 2 = 0 then h₀ else h₁
  let E₁ : Finset ℕ := (Finset.range n).filter (fun j : ℕ => (a377090 j).natAbs < T)
  let E₂ : Finset ℕ := (Finset.range n).filter
    (fun j : ℕ => T ≤ (a377090 j).natAbs ∧ (a377090 j - bFn j).natAbs ∈ E_even)
  have hE₁_le : E₁.card ≤ 2 * T + 1 := by
    let box : Finset ℤ := Finset.Icc (-(T : ℤ)) (T : ℤ)
    have hbox_card : box.card = 2 * T + 1 := by
      rw [Int.card_Icc]
      omega
    rw [← hbox_card]
    refine Finset.card_le_card_of_injOn a377090 ?_ ?_
    · intro j hj
      have hj_lt := (Finset.mem_filter.mp hj).2
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro x _ y _ hxy
      exact a377090_injective hxy
  have hE₂_le : E₂.card ≤ 4 * E_even.card := by
    let shifts : ℕ → Finset ℤ := fun m =>
      {h₀ + (m : ℤ), h₀ - (m : ℤ), h₁ + (m : ℤ), h₁ - (m : ℤ)}
    have hsub : E₂.image a377090 ⊆ E_even.biUnion shifts := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
      have hm_mem : (a377090 j - bFn j).natAbs ∈ E_even := (Finset.mem_filter.mp hj).2.2
      refine Finset.mem_biUnion.mpr ⟨(a377090 j - bFn j).natAbs, hm_mem, ?_⟩
      dsimp only [shifts, bFn]
      split_ifs
      · rcases Int.natAbs_eq (a377090 j - h₀) with hpos | hneg <;>
          simp only [Finset.mem_insert, Finset.mem_singleton] <;> omega
      · rcases Int.natAbs_eq (a377090 j - h₁) with hpos | hneg <;>
          simp only [Finset.mem_insert, Finset.mem_singleton] <;> omega
    have hE₂_eq : E₂.card = (E₂.image a377090).card := by
      symm
      exact Finset.card_image_of_injOn (fun x _ y _ hxy => a377090_injective hxy)
    have hbi_le : (E_even.biUnion shifts).card ≤ ∑ _m ∈ E_even, 4 := by
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun m _ => ?_)
      dsimp only [shifts]
      have h1 := Finset.card_insert_le (h₀ + (m : ℤ)) {h₀ - (m : ℤ), h₁ + (m : ℤ), h₁ - (m : ℤ)}
      have h2 := Finset.card_insert_le (h₀ - (m : ℤ)) {h₁ + (m : ℤ), h₁ - (m : ℤ)}
      have h3 := Finset.card_insert_le (h₁ + (m : ℤ)) {h₁ - (m : ℤ)}
      have h4 : ({h₁ - (m : ℤ)} : Finset ℤ).card = 1 := Finset.card_singleton _
      omega
    have hsum4 : ∑ _m ∈ E_even, 4 = 4 * E_even.card := by
      simp [Finset.sum_const, Nat.mul_comm]
    rw [hE₂_eq]
    exact (Finset.card_le_card hsub).trans (hbi_le.trans_eq hsum4)
  let E : Finset ℕ := E₁ ∪ E₂
  have hstep_good : ∀ j < n, j ∉ E →
      1 ≤ (a377090 j).natAbs ∧ 4 * (a377090 (j + 1)).natAbs ≤ 3 * (a377090 j).natAbs := by
    intro j hjn hj_not_E
    have hj_not_E₁ : j ∉ E₁ := fun hmem => hj_not_E (Finset.mem_union_left _ hmem)
    have hj_not_E₂ : j ∉ E₂ := fun hmem => hj_not_E (Finset.mem_union_right _ hmem)
    have hj_rng : j ∈ Finset.range n := Finset.mem_range.mpr hjn
    have hT_le_j : T ≤ (a377090 j).natAbs := by
      by_contra hlt
      push Not at hlt
      exact hj_not_E₁ (Finset.mem_filter.mpr ⟨hj_rng, hlt⟩)
    have hj_ge6K : 6 * K ≤ (a377090 j).natAbs := h6K_le_T.trans hT_le_j
    have hj_ge1 : 1 ≤ (a377090 j).natAbs := by omega
    let b := bFn j
    let m := (a377090 j - b).natAbs
    have hb_not : b ∉ prefixSet n := by
      dsimp only [b, bFn]
      split_ifs <;> assumption
    have hxb_ne : a377090 j ≠ b := fun heq =>
      hb_not (heq ▸ Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega)))
    have hb_abs : b.natAbs ≤ K := by
      dsimp only [b, bFn]
      split_ifs <;> omega
    have hj_le_M : (a377090 j).natAbs ≤ M := natAbs_le_maxPrefixRadius hjn.le
    have hm_not_Eeven : m ∉ E_even := fun hm =>
      hj_not_E₂ (Finset.mem_filter.mpr ⟨hj_rng, hT_le_j, hm⟩)
    have hm_pos : 1 ≤ m := by
      dsimp only [m]
      omega
    have hm_le_2M : m ≤ 2 * M := by
      have hm_le_abs : m ≤ (a377090 j).natAbs + b.natAbs := by
        dsimp only [m]; omega
      omega
    have hm_even : Even m := by
      rw [Nat.even_iff]
      apply natAbs_sub_mod_two_eq_zero
      dsimp only [b, bFn]
      split_ifs with hmod
      · omega
      · have hmod1 : a377090 j % 2 = 1 := by omega
        omega
    have hgb_real : c * (m : ℝ) / L ^ 2 ≤ (goldbachCount m : ℝ) := by
      by_contra hlt
      push Not at hlt
      exact hm_not_Eeven (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm_pos, hm_le_2M⟩, hm_even, hlt⟩)
    have hm_ge_T2 : (T : ℝ) / 2 ≤ (m : ℝ) := by
      have hm_ge_sub : (a377090 j).natAbs - b.natAbs ≤ m := by
        dsimp only [m]; omega
      have hmnat : T ≤ 2 * m := by omega
      have : (T : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hmnat
      linarith
    have hgb_gt : 4 * K + 2 < goldbachCount m := by
      have h9c_le_CT : 9 / c ≤ C_T := le_max_right _ _
      have hlow : 9 / c * ((K : ℝ) + 1) * L ^ 2 ≤ (T : ℝ) := by
        have h1 : 9 / c * ((K : ℝ) + 1) * L ^ 2 ≤ C_T * ((K : ℝ) + 1) * L ^ 2 := by gcongr
        exact h1.trans hT_ge_real
      have hfrac : (4 * (K : ℝ) + 2) < c * ((T : ℝ) / 2) / L ^ 2 := by
        have hL2_pos : 0 < L ^ 2 := pow_pos hL_pos 2
        have hcalc : (9 / 2 : ℝ) * ((K : ℝ) + 1) ≤ c * ((T : ℝ) / 2) / L ^ 2 := by
          have hc_ne : c ≠ 0 := hc_pos.ne'
          have hL_ne : L ≠ 0 := hL_pos.ne'
          calc
            (9 / 2 : ℝ) * ((K : ℝ) + 1)
                = c * ((9 / c * ((K : ℝ) + 1) * L ^ 2) / 2) / L ^ 2 := by
                    field_simp
            _ ≤ c * ((T : ℝ) / 2) / L ^ 2 := by gcongr
        linarith
      have hlt_real : ((4 * K + 2 : ℕ) : ℝ) < (goldbachCount m : ℝ) := by
        have hm_ineq : c * ((T : ℝ) / 2) / L ^ 2 ≤ c * (m : ℝ) / L ^ 2 := by gcongr
        push_cast
        linarith
      exact_mod_cast hlt_real
    refine ⟨hj_ge1, contraction_step hjn hh₀ hh₁ hh₀_even hh₁_odd le_rfl hj_ge6K ?_⟩
    simpa [bFn, b, m] using hgb_gt
  have hcount : n ≤ (E.card + 1) * (R + 1) :=
    contracting_run_bound n M R (fun j => (a377090 j).natAbs) E
      (fun j hj => natAbs_le_maxPrefixRadius hj.le) hstep_good hMR
  have hE_card : E.card ≤ 2 * T + 1 + 4 * E_even.card :=
    (Finset.card_union_le E₁ E₂).trans (Nat.add_le_add hE₁_le hE₂_le)
  have hmain_real : (n : ℝ) ≤
      (2 * (T : ℝ) + 2) * ((R : ℝ) + 1) + 4 * (E_even.card : ℝ) * ((R : ℝ) + 1) := by
    have hnat_ineq : n ≤ (2 * T + 2) * (R + 1) + 4 * E_even.card * (R + 1) := by
      have : E.card + 1 ≤ (2 * T + 2) + 4 * E_even.card := by omega
      calc
        n ≤ (E.card + 1) * (R + 1) := hcount
        _ ≤ (2 * T + 2 + 4 * E_even.card) * (R + 1) := Nat.mul_le_mul_right _ this
        _ = (2 * T + 2) * (R + 1) + 4 * E_even.card * (R + 1) := by ring
    exact_mod_cast hnat_ineq
  -- Bound the second term 4 * E_even.card * (R + 1) ≤ n / 2
  have hsecond_le : 4 * (E_even.card : ℝ) * ((R : ℝ) + 1) ≤ (n : ℝ) / 2 := by
    have hL2_ge : 8 * A_abs ≤ L ^ 2 := by
      have hceil_le : Nat.ceil (Real.exp (Real.sqrt (8 * A_abs))) ≤ n := by
        have : Nat.ceil (Real.exp (Real.sqrt (8 * A_abs))) + 16 ≤ N₁ :=
          le_trans (le_max_right _ _) (le_max_right _ _)
        omega
      have hexp_le_n : Real.exp (Real.sqrt (8 * A_abs)) ≤ (n : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast hceil_le)
      have hsqrt_le_log : Real.sqrt (8 * A_abs) ≤ Real.log (n : ℝ) := by
        calc
          Real.sqrt (8 * A_abs) = Real.log (Real.exp (Real.sqrt (8 * A_abs))) :=
              (Real.log_exp _).symm
          _ ≤ Real.log (n : ℝ) := Real.log_le_log (Real.exp_pos _) hexp_le_n
      have hsqrt_le_L : Real.sqrt (8 * A_abs) ≤ L := hsqrt_le_log.trans hL_ge_logn
      have hsq : Real.sqrt (8 * A_abs) ^ 2 ≤ L ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt_le_L 2
      have hnonneg : 0 ≤ 8 * A_abs := by positivity
      rwa [Real.sq_sqrt hnonneg] at hsq
    have hL3_pos : 0 < L ^ 3 := pow_pos hL_pos 3
    have hL2_pos : 0 < L ^ 2 := pow_pos hL_pos 2
    have hlog2n_2L : Real.log (2 * (n : ℝ)) ≤ 2 * L := by
      have h2n_le_4M : 2 * (n : ℝ) ≤ 4 * (M : ℝ) := by linarith
      have hn_pos : (0 : ℝ) < 2 * (n : ℝ) := by
        have : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hN₁_ge16.trans hn
        linarith
      have hlog_2n_le : Real.log (2 * (n : ℝ)) ≤ Real.log (4 * (M : ℝ)) :=
        Real.log_le_log hn_pos h2n_le_4M
      have hlog_4M : Real.log (4 * (M : ℝ)) = Real.log 2 + L := by
        have hmul : 4 * (M : ℝ) = 2 * (2 * (M : ℝ)) := by ring
        rw [hmul, Real.log_mul (by norm_num) (by positivity)]
      have hlog2_le_L : Real.log 2 ≤ L := by
        have : (2 : ℝ) ≤ 2 * (M : ℝ) := by
          have : (16 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM16
          linarith
        exact Real.log_le_log (by norm_num) this
      linarith
    calc
      4 * (E_even.card : ℝ) * ((R : ℝ) + 1)
          ≤ 4 * (C_exc * (M : ℝ) / L ^ 4) * (C_R * L) := by gcongr
      _ = 4 * C_exc * C_R * ((M : ℝ) / L ^ 3) := by
          have hL_ne : L ≠ 0 := hL_pos.ne'
          field_simp
      _ ≤ 4 * C_exc * C_R * (C_M * (n : ℝ) * Real.log (2 * (n : ℝ)) / L ^ 3) := by gcongr
      _ ≤ 4 * C_exc * C_R * (C_M * (n : ℝ) * (2 * L) / L ^ 3) := by gcongr
      _ = (2 * A_abs / L ^ 2) * (n : ℝ) := by
          dsimp only [A_abs]
          have hL_ne : L ≠ 0 := hL_pos.ne'
          field_simp
      _ ≤ (1 / 4 : ℝ) * (n : ℝ) := by
          have hfrac : 2 * A_abs / L ^ 2 ≤ 1 / 4 := by
            rw [div_le_div_iff₀ hL2_pos (by norm_num)]
            linarith
          have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          exact mul_le_mul_of_nonneg_right hfrac hn_nonneg
      _ ≤ (n : ℝ) / 2 := by
          have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
  have hfirst_ge : (n : ℝ) / 2 ≤ (2 * (T : ℝ) + 2) * ((R : ℝ) + 1) := by linarith
  have hT2_le : 2 * (T : ℝ) + 2 ≤ 4 * C_T * ((K : ℝ) + 1) * L ^ 2 := by
    have h6_le_CT : (6 : ℝ) ≤ C_T := le_max_left _ _
    have hK_ge1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK_pos
    have hL2_ge1 : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ hL_gt1.le
    have h4_le : (4 : ℝ) ≤ 2 * C_T * ((K : ℝ) + 1) * L ^ 2 := by
      have h12 : (2 : ℝ) ≤ C_T * ((K : ℝ) + 1) * L ^ 2 := by
        calc
          (2 : ℝ) ≤ 6 * 1 * 1 := by norm_num
          _ ≤ C_T * ((K : ℝ) + 1) * L ^ 2 := by gcongr; linarith
      linarith
    linarith
  have hK1_le_2K : (K : ℝ) + 1 ≤ 2 * (K : ℝ) := by
    have : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK_pos
    linarith
  have hk1_le_2k : (k : ℝ) + 1 ≤ 2 * (k : ℝ) := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
    linarith
  have hlog2k_le : Real.log (2 * ((k : ℝ) + 1)) ≤ 2 * Real.log (n : ℝ) := by
    have hcov_le := prefixCoverage_le_half_add_one n
    have h2k_le_n2 : 2 * (k + 1) ≤ n * n := by
      have hn4 : 4 ≤ n := hN₁_ge4.trans hn
      have h2n_le_nn : 2 * n ≤ n * n := by
        calc
          2 * n ≤ 4 * n := by omega
          _ ≤ n * n := Nat.mul_le_mul_right n hn4
      omega
    have h2k_le_R : 2 * ((k : ℝ) + 1) ≤ (n : ℝ) ^ 2 := by
      have hcast : ((2 * (k + 1) : ℕ) : ℝ) ≤ ((n * n : ℕ) : ℝ) := by exact_mod_cast h2k_le_n2
      simpa [pow_two] using hcast
    have h2k_pos : 0 < 2 * ((k : ℝ) + 1) := by positivity
    have hlog_pow2 : Real.log ((n : ℝ) ^ 2) = 2 * Real.log (n : ℝ) := by
      rw [Real.log_pow]
      norm_num
    exact (Real.log_le_log h2k_pos h2k_le_R).trans_eq hlog_pow2
  have hK_real_le : (K : ℝ) ≤ 4 * C_K * (k : ℝ) * Real.log (n : ℝ) := by
    have hlogk_nonneg : 0 ≤ Real.log (2 * ((k : ℝ) + 1)) := by
      have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      exact Real.log_nonneg (by linarith)
    calc
      (K : ℝ) ≤ C_K * ((k : ℝ) + 1) * Real.log (2 * ((k : ℝ) + 1)) := hK_bound
      _ ≤ C_K * (2 * (k : ℝ)) * (2 * Real.log (n : ℝ)) := by gcongr
      _ = 4 * C_K * (k : ℝ) * Real.log (n : ℝ) := by ring
  have hL3_le : L ^ 3 ≤ 27 * Real.log (n : ℝ) ^ 3 := by
    have hpow := pow_le_pow_left₀ hL_pos.le hL_le_3logn 3
    linarith [show (3 * Real.log (n : ℝ)) ^ 3 = 27 * Real.log (n : ℝ) ^ 3 by ring]
  have hbound_prod : (n : ℝ) / 2 ≤ 864 * C_T * C_R * C_K * (k : ℝ) * Real.log (n : ℝ) ^ 4 := by
    have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    calc
      (n : ℝ) / 2 ≤ (2 * (T : ℝ) + 2) * ((R : ℝ) + 1) := hfirst_ge
      _ ≤ (4 * C_T * ((K : ℝ) + 1) * L ^ 2) * (C_R * L) := by gcongr
      _ = 4 * C_T * C_R * ((K : ℝ) + 1) * L ^ 3 := by ring
      _ ≤ 4 * C_T * C_R * (2 * (K : ℝ)) * (27 * Real.log (n : ℝ) ^ 3) := by gcongr
      _ = 216 * C_T * C_R * (K : ℝ) * Real.log (n : ℝ) ^ 3 := by ring
      _ ≤ 216 * C_T * C_R * (4 * C_K * (k : ℝ) * Real.log (n : ℝ)) * Real.log (n : ℝ) ^ 3 := by
          gcongr
      _ = 864 * C_T * C_R * C_K * (k : ℝ) * Real.log (n : ℝ) ^ 4 := by ring
  have hlog4_pos : 0 < Real.log (n : ℝ) ^ 4 := pow_pos hlogn_pos 4
  rw [div_le_iff₀ hlog4_pos]
  have hden_pos : 0 < 864 * C_T * C_R * C_K := by positivity
  calc
    c₁ * (n : ℝ)
        = (1 / (864 * C_T * C_R * C_K)) * ((n : ℝ) / 2) := by
            dsimp only [c₁]
            field_simp
            ring
    _ ≤ (1 / (864 * C_T * C_R * C_K)) *
          (864 * C_T * C_R * C_K * (k : ℝ) * Real.log (n : ℝ) ^ 4) := by gcongr
    _ = (k : ℝ) * Real.log (n : ℝ) ^ 4 := by
        field_simp

end Step3SegmentCounting

/-- Independent proof of surjectivity of `a377090` directly from Theorem 2
(`prefix_coverage_lower_bound`), without appealing to `A377090.Surjectivity`. -/
theorem a377090_surjective_of_prefix_coverage (hG : GoldbachMeanSquareInput) :
    Function.Surjective a377090 := by
  obtain ⟨c₁, hc₁_pos, N₁, hN₁, hcov⟩ := prefix_coverage_lower_bound hG
  intro z
  have hlim : ∀ᶠ n : ℝ in atTop, Real.log n ^ 4 < (c₁ / ((z.natAbs : ℝ) + 1)) * n :=
    eventually_pow_log_lt_const_mul_self_pc 4 (by positivity)
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp hlim
  let n : ℕ := max N₁ (max (Nat.ceil X₀) 2)
  have hn_N₁ : N₁ ≤ n := le_max_left _ _
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast le_trans (le_max_right _ _) (le_max_right _ _)
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hn_X₀ : X₀ ≤ (n : ℝ) := (Nat.le_ceil X₀).trans (by
    exact_mod_cast le_trans (le_max_left _ _) (le_max_right _ _))
  have hlog4_lt := hX₀ (n : ℝ) hn_X₀
  have hlt_kR : (z.natAbs : ℝ) < (prefixCoverage n : ℝ) := by
    have hz_pos : (0 : ℝ) < (z.natAbs : ℝ) + 1 := by positivity
    have h1 : ((z.natAbs : ℝ) + 1) * Real.log (n : ℝ) ^ 4 < c₁ * (n : ℝ) := by
      have hmul := mul_lt_mul_of_pos_left hlog4_lt hz_pos
      have heq : ((z.natAbs : ℝ) + 1) * (c₁ / ((z.natAbs : ℝ) + 1) * (n : ℝ)) = c₁ * (n : ℝ) := by
        field_simp
      linarith
    have h2 : (z.natAbs : ℝ) + 1 < c₁ * (n : ℝ) / Real.log (n : ℝ) ^ 4 :=
      (lt_div_iff₀ (pow_pos hlog_pos 4)).mpr h1
    linarith [hcov n hn_N₁]
  have hlt_k : z.natAbs < prefixCoverage n := by exact_mod_cast hlt_kR
  have hz_mem := prefixCoverage_mem_prefixSet hlt_k
  rcases Finset.mem_image.mp hz_mem with ⟨idx, _, hidx⟩
  exact ⟨idx, hidx⟩

end A377090