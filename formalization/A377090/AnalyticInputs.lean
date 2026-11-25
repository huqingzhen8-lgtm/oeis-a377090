import Mathlib

/-!
# Analytic Number Theory Inputs, Chebyshev Bounds, and Binary Goldbach Lemma

This file collects:

1. **Bertrand's Postulate** (`bertrand_consecutive_primes_lt`): consecutive primes `p < q`
   satisfy `q < 2 * p`, proved directly from Mathlib's `Nat.exists_prime_lt_and_le_two_mul`.
2. **Chebyshev Prime-Counting Bounds** (`chebyshev_primeCounting_lower`,
   `chebyshev_le_mul_log_of_primeCounting_le`, `chebyshev_nth_prime_le`): proved directly from
   Mathlib's `Chebyshev.pi_ge`, with **zero external hypotheses**.
3. **Explicit External Inputs** (typed `structure` records, no custom `axiom`s):
   * `GoldbachMeanSquareInput`: the Chudakov–van der Corput–Estermann mean-square estimate
     for binary Goldbach representations (Vaughan 1972, p. 22);
   * `WestzynthiusInput`: arbitrarily large prime gaps `(q - p) / log p → ∞`.
4. **Lemma 1.2** (`goldbach_uniform_lower_bound`): derived inside Lean from
   `GoldbachMeanSquareInput` by Chebyshev/Markov counting.
-/

namespace A377090

open Finset Filter

section Bertrand

/-- By Bertrand's postulate, consecutive primes `p < q` satisfy `q < 2 * p`. -/
theorem bertrand_consecutive_primes_lt {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (_hpq : p < q) (hconsec : ∀ r : ℕ, p < r → r < q → ¬Nat.Prime r) : q < 2 * p := by
  obtain ⟨r, hr_prime, hpr, hr2p⟩ := Nat.exists_prime_lt_and_le_two_mul p hp.ne_zero
  have hqr : q ≤ r := by
    by_contra hlt
    exact hconsec r hpr (lt_of_not_ge hlt) hr_prime
  have hq_le : q ≤ 2 * p := hqr.trans hr2p
  have h2p_not_prime : ¬Nat.Prime (2 * p) := by
    intro hprime
    rcases hprime.eq_one_or_self_of_dvd 2 ⟨p, rfl⟩ with h | h
    · omega
    · have := hp.two_le
      omega
  exact lt_of_le_of_ne hq_le (fun heq => h2p_not_prime (heq ▸ hq))

end Bertrand

section Chebyshev

theorem primeCounting_eq_card_filter (n : ℕ) :
    Nat.primeCounting n = ((Finset.range (n + 1)).filter Nat.Prime).card := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

theorem primeCounting_nth_prime (j : ℕ) :
    Nat.primeCounting (Nat.nth Nat.Prime j) = j + 1 := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_succ]
  simp [Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime j]
  exact Nat.primeCounting'_nth_eq j

private theorem log_two_lt_one : Real.log 2 < 1 := by
  rw [← Real.log_exp 1]
  apply Real.log_lt_log (by norm_num)
  linarith [Real.exp_one_gt_d9]

/-- Explicit Chebyshev lower bound on `π(n)` proved directly from Mathlib (`Chebyshev.pi_ge`). -/
theorem chebyshev_primeCounting_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 16 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n →
      c * (n : ℝ) / Real.log n ≤ (Nat.primeCounting n : ℝ) := by
  refine ⟨1 / 4, by norm_num, 16, le_rfl, fun n hn => ?_⟩
  have hnR : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hpi := Chebyshev.pi_ge n
  have hlog8 : Real.log 8 < 3 := by
    have h8 : (8 : ℝ) = 2 ^ (3 : ℕ) := by norm_num
    rw [h8, Real.log_pow]
    push_cast
    linarith [log_two_lt_one]
  have hlog_n1 : Real.log ((n : ℝ) + 1) ≤ (n : ℝ) / 8 + 17 / 8 := by
    have hmul : ((n : ℝ) + 1) = 8 * (((n : ℝ) + 1) / 8) := by ring
    rw [hmul, Real.log_mul (by norm_num) (by linarith)]
    have hle := Real.log_le_sub_one_of_pos (show 0 < ((n : ℝ) + 1) / 8 by linarith)
    linarith
  have hlog2 : (69 / 100 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hnum : (1 / 4 : ℝ) * (n : ℝ) ≤ (n : ℝ) * Real.log 2 - Real.log ((n : ℝ) + 1) := by
    nlinarith
  exact (div_le_div_of_nonneg_right hnum hlog_pos.le).trans hpi

/-- Elementary inversion: if `c * x / log x ≤ y` (`4 ≤ x`, `1 ≤ y`), then `x ≤ C * y * log (2 * y)`. -/
theorem div_log_le_imp_le_mul_log {c x y : ℝ} (hc : 0 < c) (hx : 4 ≤ x) (hy : 1 ≤ y)
    (h : c * x / Real.log x ≤ y) :
    x ≤ ((4 / (c ^ 2 * Real.log 2) + 2) / c) * y * Real.log (2 * y) := by
  have hx_pos : 0 < x := by linarith
  have hy_pos : 0 < y := by linarith
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2y_pos : 0 < Real.log (2 * y) := Real.log_pos (by linarith)
  have hcx : c * x ≤ y * Real.log x := (div_le_iff₀ hlogx_pos).mp h
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
  have hlogx_le_sqrt : Real.log x ≤ 2 * Real.sqrt x := by
    have h1 : Real.log x = 2 * Real.log (Real.sqrt x) := by
      have hsq : Real.sqrt x ^ (2 : ℕ) = x := Real.sq_sqrt hx_pos.le
      conv_lhs => rw [← hsq, Real.log_pow]
      norm_num
    have h2 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
      Real.log_le_sub_one_of_pos hsqrt_pos
    linarith
  have hsqrt_le : Real.sqrt x ≤ (2 / c) * y := by
    have hmul : c * (Real.sqrt x * Real.sqrt x) ≤ 2 * y * Real.sqrt x := by
      rw [Real.mul_self_sqrt hx_pos.le]
      calc
        c * x ≤ y * Real.log x := hcx
        _ ≤ y * (2 * Real.sqrt x) := mul_le_mul_of_nonneg_left hlogx_le_sqrt hy_pos.le
        _ = 2 * y * Real.sqrt x := by ring
    have hle1 : c * Real.sqrt x ≤ 2 * y := by
      nlinarith
    calc
      Real.sqrt x = (c * Real.sqrt x) / c := by field_simp
      _ ≤ (2 * y) / c := div_le_div_of_nonneg_right hle1 hc.le
      _ = (2 / c) * y := by ring
  have hx_le_sq : x ≤ (4 / c ^ 2) * y ^ 2 := by
    have h0 : 0 ≤ Real.sqrt x := hsqrt_pos.le
    have hsq := pow_le_pow_left₀ h0 hsqrt_le 2
    rw [Real.sq_sqrt hx_pos.le] at hsq
    calc
      x ≤ ((2 / c) * y) ^ 2 := hsq
      _ = (4 / c ^ 2) * y ^ 2 := by ring
  have hconst_pos : 0 < 4 / c ^ 2 := by positivity
  have hlogx_le : Real.log x ≤ (4 / (c ^ 2 * Real.log 2) + 2) * Real.log (2 * y) := by
    have h1 : Real.log x ≤ Real.log ((4 / c ^ 2) * y ^ 2) :=
      Real.log_le_log hx_pos hx_le_sq
    have h2 : Real.log ((4 / c ^ 2) * y ^ 2) = Real.log (4 / c ^ 2) + 2 * Real.log y := by
      rw [Real.log_mul hconst_pos.ne' (pow_ne_zero 2 hy_pos.ne'), Real.log_pow]
      ring
    have h3 : Real.log (4 / c ^ 2) ≤ 4 / c ^ 2 := by
      linarith [Real.log_le_sub_one_of_pos hconst_pos]
    have h4 : 1 ≤ Real.log (2 * y) / Real.log 2 :=
      (one_le_div hlog2_pos).mpr (Real.log_le_log (by norm_num) (by linarith))
    have h5 : Real.log y ≤ Real.log (2 * y) :=
      Real.log_le_log hy_pos (by linarith)
    calc
      Real.log x ≤ Real.log (4 / c ^ 2) + 2 * Real.log y := by linarith
      _ ≤ (4 / c ^ 2) * (Real.log (2 * y) / Real.log 2) + 2 * Real.log (2 * y) := by
          nlinarith
      _ = (4 / (c ^ 2 * Real.log 2) + 2) * Real.log (2 * y) := by
          field_simp
  calc
    x = (c * x) / c := by field_simp
    _ ≤ (y * Real.log x) / c := div_le_div_of_nonneg_right hcx hc.le
    _ ≤ (y * ((4 / (c ^ 2 * Real.log 2) + 2) * Real.log (2 * y))) / c := by
        refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlogx_le hy_pos.le) hc.le
    _ = ((4 / (c ^ 2 * Real.log 2) + 2) / c) * y * Real.log (2 * y) := by ring

/-- If `π(m) ≤ y` with `1 ≤ y`, then `m ≤ C * y * log (2 * y)` for a universal constant `C`. -/
theorem chebyshev_le_mul_log_of_primeCounting_le :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, ∀ y : ℝ, 1 ≤ y → (Nat.primeCounting m : ℝ) ≤ y →
      (m : ℝ) ≤ C * y * Real.log (2 * y) := by
  obtain ⟨c, hc, N₀, hN₀_ge, hpi⟩ := chebyshev_primeCounting_lower
  let C₁ : ℝ := (4 / (c ^ 2 * Real.log 2) + 2) / c
  let C : ℝ := max C₁ ((N₀ : ℝ) / Real.log 2)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC₁_pos : 0 < C₁ := by positivity
  have hC_pos : 0 < C := lt_of_lt_of_le hC₁_pos (le_max_left _ _)
  refine ⟨C, hC_pos, fun m y hy hmy => ?_⟩
  have hlog2y_ge : Real.log 2 ≤ Real.log (2 * y) := Real.log_le_log (by norm_num) (by linarith)
  have hlog2y_pos : 0 < Real.log (2 * y) := lt_of_lt_of_le hlog2_pos hlog2y_ge
  by_cases hm : N₀ ≤ m
  · have hm4 : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 4 ≤ m)
    have hdiv : c * (m : ℝ) / Real.log (m : ℝ) ≤ y := (hpi m hm).trans hmy
    have hle := div_log_le_imp_le_mul_log hc hm4 hy hdiv
    have hC₁_le : C₁ ≤ C := le_max_left _ _
    calc
      (m : ℝ) ≤ C₁ * y * Real.log (2 * y) := hle
      _ ≤ C * y * Real.log (2 * y) := by gcongr
  · have hm_lt : (m : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast (Nat.lt_of_not_ge hm).le
    have hN₀_le : (N₀ : ℝ) / Real.log 2 ≤ C := le_max_right _ _
    calc
      (m : ℝ) ≤ (N₀ : ℝ) := hm_lt
      _ = ((N₀ : ℝ) / Real.log 2) * 1 * Real.log 2 := by field_simp
      _ ≤ C * y * Real.log (2 * y) := by
          gcongr

/-- Chebyshev upper bound on the `j`-th prime: `p_j ≤ C * (j + 1) * log (2 * (j + 1))`. -/
theorem chebyshev_nth_prime_le :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ,
      (Nat.nth Nat.Prime j : ℝ) ≤ C * ((j : ℝ) + 1) * Real.log (2 * ((j : ℝ) + 1)) := by
  obtain ⟨C, hC, hbound⟩ := chebyshev_le_mul_log_of_primeCounting_le
  refine ⟨C, hC, fun j => ?_⟩
  refine hbound (Nat.nth Nat.Prime j) ((j : ℝ) + 1) (by linarith) ?_
  rw [primeCounting_nth_prime]
  norm_num

end Chebyshev

section GoldbachAndPrimeGaps

/-- Ordered binary Goldbach representation count `r(m) = #{(u, v) ∈ ℙ² : u + v = m}`. -/
def goldbachCount (m : ℕ) : ℕ :=
  ((Finset.range (m + 1)).filter (fun u => Nat.Prime u ∧ Nat.Prime (m - u))).card

/-- Chudakov–van der Corput–Estermann mean-square estimate for binary Goldbach representations
(Vaughan 1972, *On Goldbach's problem*, Acta Arith. 22, p. 22). -/
structure GoldbachMeanSquareInput where
  main : ℕ → ℝ
  c₀ : ℝ
  hc₀ : 0 < c₀
  X₀ : ℝ
  hX₀ : 4 ≤ X₀
  main_lower : ∀ X : ℝ, X₀ ≤ X → ∀ m : ℕ, Even m →
    X / 2 ≤ (m : ℝ) → (m : ℝ) ≤ X →
    2 * c₀ * X / (Real.log X) ^ 2 ≤ main m
  mean_square : ∀ B : ℝ, 0 < B → ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
    ∑ m ∈ (Finset.range (Nat.floor X + 1)).filter Even,
      ((goldbachCount m : ℝ) - main m) ^ 2 ≤ C * X ^ 3 / (Real.log X) ^ B

/-- **Lemma 1.2 (Uniform Binary Goldbach Lower Bound)**:
Derived from `GoldbachMeanSquareInput` via Markov/Chebyshev counting with `B = A + 4`.
Crucially, `c > 0` does not depend on `A`. -/
theorem goldbach_uniform_lower_bound (hG : GoldbachMeanSquareInput) :
    ∃ c : ℝ, 0 < c ∧ ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, hG.X₀ ≤ X →
      (((Finset.range (Nat.floor X + 1)).filter
        (fun m : ℕ => Even m ∧ X / 2 ≤ (m : ℝ) ∧
          (goldbachCount m : ℝ) < c * X / (Real.log X) ^ 2)).card : ℝ) ≤
        C * X / (Real.log X) ^ A := by
  refine ⟨hG.c₀, hG.hc₀, fun A hA => ?_⟩
  obtain ⟨CB, hCB, hms⟩ := hG.mean_square (A + 4) (by linarith)
  refine ⟨CB / hG.c₀ ^ 2, div_pos hCB (sq_pos_of_pos hG.hc₀), fun X hX => ?_⟩
  have hX4 : 4 ≤ X := hG.hX₀.trans hX
  have hXpos : 0 < X := by linarith
  have hlogX_pos : 0 < Real.log X := Real.log_pos (by linarith)
  let Ev : Finset ℕ := (Finset.range (Nat.floor X + 1)).filter Even
  let Bad : Finset ℕ := (Finset.range (Nat.floor X + 1)).filter
    (fun m : ℕ => Even m ∧ X / 2 ≤ (m : ℝ) ∧
      (goldbachCount m : ℝ) < hG.c₀ * X / (Real.log X) ^ 2)
  have hBad_sub : Bad ⊆ Ev := by
    intro m hm
    rcases Finset.mem_filter.mp hm with ⟨hm_rng, hm_ev, _⟩
    exact Finset.mem_filter.mpr ⟨hm_rng, hm_ev⟩
  let thresh : ℝ := hG.c₀ * X / (Real.log X) ^ 2
  have hthresh_pos : 0 < thresh := div_pos (mul_pos hG.hc₀ hXpos) (sq_pos_of_pos hlogX_pos)
  have hterm_ge : ∀ m ∈ Bad, thresh ^ 2 ≤ ((goldbachCount m : ℝ) - hG.main m) ^ 2 := by
    intro m hm
    rcases Finset.mem_filter.mp hm with ⟨hm_rng, hm_ev, hm_low, hm_bad⟩
    have hm_le : (m : ℝ) ≤ X := by
      have hm_lt : m < Nat.floor X + 1 := Finset.mem_range.mp hm_rng
      have hm_le_floor : m ≤ Nat.floor X := Nat.lt_succ_iff.mp hm_lt
      exact (Nat.cast_le.mpr hm_le_floor).trans (Nat.floor_le hXpos.le)
    have hmain := hG.main_lower X hX m hm_ev hm_low hm_le
    have h2 : 2 * thresh ≤ hG.main m := by
      calc
        2 * thresh = 2 * hG.c₀ * X / (Real.log X) ^ 2 := by dsimp only [thresh]; ring
        _ ≤ hG.main m := hmain
    have hdiff : thresh ≤ hG.main m - (goldbachCount m : ℝ) := by
      dsimp only [thresh] at *
      linarith
    have hsq : thresh ^ 2 ≤ (hG.main m - (goldbachCount m : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hthresh_pos.le hdiff 2
    have hsq_eq :
        (hG.main m - (goldbachCount m : ℝ)) ^ 2 = ((goldbachCount m : ℝ) - hG.main m) ^ 2 := by
      ring
    exact hsq.trans_eq hsq_eq
  have hsum_bad :
      (Bad.card : ℝ) * thresh ^ 2 ≤
        ∑ m ∈ Bad, ((goldbachCount m : ℝ) - hG.main m) ^ 2 := by
    calc
      (Bad.card : ℝ) * thresh ^ 2 = ∑ _m ∈ Bad, thresh ^ 2 := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ m ∈ Bad, ((goldbachCount m : ℝ) - hG.main m) ^ 2 := Finset.sum_le_sum hterm_ge
  have hsum_le :
      ∑ m ∈ Bad, ((goldbachCount m : ℝ) - hG.main m) ^ 2 ≤
        ∑ m ∈ Ev, ((goldbachCount m : ℝ) - hG.main m) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hBad_sub (fun _ _ _ => sq_nonneg _)
  have htotal : (Bad.card : ℝ) * thresh ^ 2 ≤ CB * X ^ 3 / (Real.log X) ^ (A + 4) :=
    hsum_bad.trans (hsum_le.trans (hms X hX))
  have hpow4 : (Real.log X) ^ (A + 4) = (Real.log X) ^ A * (Real.log X) ^ (4 : ℕ) := by
    rw [Real.rpow_add hlogX_pos, ← Real.rpow_natCast (Real.log X) 4]
    norm_num
  have hrpowA_pos : 0 < (Real.log X) ^ A := Real.rpow_pos_of_pos hlogX_pos A
  have hthresh_sq_pos : 0 < thresh ^ 2 := sq_pos_of_pos hthresh_pos
  have hdiv :
      (Bad.card : ℝ) ≤ (CB * X ^ 3 / (Real.log X) ^ (A + 4)) / thresh ^ 2 :=
    (le_div_iff₀ hthresh_sq_pos).mpr htotal
  refine hdiv.trans_eq ?_
  dsimp only [thresh]
  rw [hpow4]
  field_simp

/-- Westzynthius's large prime-gap theorem (1931; see Ford–Green–Konyagin–Tao 2016, pp. 935–936):
there exist arbitrarily large consecutive primes `p < q` with `(q - p) / log p → ∞`. -/
structure WestzynthiusInput where
  large_gap : ∀ R : ℝ, ∀ N : ℕ, ∃ p q : ℕ,
    N ≤ p ∧ Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧
    (∀ r : ℕ, p < r → r < q → ¬Nat.Prime r) ∧
    R * Real.log (p : ℝ) < ((q - p : ℕ) : ℝ)

end GoldbachAndPrimeGaps

end A377090
