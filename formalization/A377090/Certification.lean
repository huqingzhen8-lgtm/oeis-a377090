import A377090.PrimeGaps

/-!
# Computational Certification Methodology and Earliest Counterexample `n = 370313`

This file formalizes (with **zero external assumptions**) the rational-arithmetic
certification method of `verify_a377090.py` and the concrete numerical facts for the
earliest logarithmic violation `n = 370313`, `a(n) = -185183`:

* Exact Taylor rational bounds `taylorLo < exp 1 < taylorHi`;
* Equivalence `deviation < 2 * log (n + 2) ↔ exp d < (n + 2)^4` and rational certificates;
* Monotonicity reduction (`earliest_index_monotonicity`): checking the first index of each
  distinct integer `d = |2 * |a(n)| - n|` suffices;
* Rigorous proof of `2 * log (370315) < |185183 - 370313 / 2| = 26.5`;
* Rigorous proof that `[370261, 370373]` is a prime gap of width `112`.
-/

namespace A377090

open Finset

/-- Rational lower Taylor bound for `e`: `∑_{k=0}^{10} 1 / k!`. -/
def taylorLo : ℚ :=
  ∑ k ∈ Finset.range 11, (1 : ℚ) / (Nat.factorial k : ℚ)

/-- Rational upper Taylor bound for `e`: `taylorLo + 1 / (10 * 10!)`. -/
def taylorHi : ℚ :=
  taylorLo + (1 : ℚ) / (10 * (Nat.factorial 10 : ℚ))

theorem taylorLo_pos : (0 : ℚ) < taylorLo := by
  norm_num [taylorLo, Finset.sum_range_succ, Nat.factorial]

theorem taylorLo_lt_exp_one : (taylorLo : ℝ) < Real.exp 1 := by
  have hsum : ∑ i ∈ Finset.range 12, (1 : ℝ) ^ i / (Nat.factorial i : ℝ) ≤ Real.exp 1 :=
    Real.sum_le_exp_of_nonneg (by norm_num) 12
  have hsplit : ∑ i ∈ Finset.range 12, (1 : ℝ) ^ i / (Nat.factorial i : ℝ) =
      (taylorLo : ℝ) + 1 / (Nat.factorial 11 : ℝ) := by
    rw [Finset.sum_range_succ]
    simp [taylorLo]
  have hpos : (0 : ℝ) < 1 / (Nat.factorial 11 : ℝ) := by positivity
  linarith

theorem exp_one_lt_taylorHi : Real.exp 1 < (taylorHi : ℝ) := by
  have hbound := Real.exp_bound' (x := (1 : ℝ)) (by norm_num) (by norm_num) (n := 11) (by omega)
  have htail : (1 : ℝ) ^ 11 * ((11 : ℝ) + 1) / ((Nat.factorial 11 : ℝ) * 11) <
      1 / (10 * (Nat.factorial 10 : ℝ)) := by
    have h11 : Nat.factorial 11 = 11 * Nat.factorial 10 := Nat.factorial_succ 10
    rw [h11]
    have hfac_pos : (0 : ℝ) < (Nat.factorial 10 : ℝ) := by positivity
    push_cast
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hsum_cast : ∑ m ∈ Finset.range 11, (1 : ℝ) ^ m / (Nat.factorial m : ℝ) = (taylorLo : ℝ) := by
    simp [taylorLo]
  have hhi_cast : (taylorHi : ℝ) = (taylorLo : ℝ) + 1 / (10 * (Nat.factorial 10 : ℝ)) := by
    simp [taylorHi]
  linarith

/-- Equivalence `| |a| - n/2 | < 2 * log (n + 2) ↔ exp d < (n + 2)^4` where `d = 2 * δ`. -/
theorem deviation_lt_two_log_iff (a : ℤ) (n : ℕ) :
    |((a.natAbs : ℝ) - (n : ℝ) / 2)| < 2 * Real.log ((n : ℝ) + 2) ↔
      Real.exp (Int.natAbs (2 * (a.natAbs : ℤ) - (n : ℤ)) : ℝ) < ((n : ℝ) + 2) ^ 4 := by
  let d : ℕ := Int.natAbs (2 * (a.natAbs : ℤ) - (n : ℤ))
  have hdev : |((a.natAbs : ℝ) - (n : ℝ) / 2)| = (d : ℝ) / 2 := by
    have h := deviation_eq_twoDeviation_div_two (fun _ => a) n
    simpa [deviation, twoDeviation, d] using h
  have hn2_pos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hn2_pow_pos : (0 : ℝ) < ((n : ℝ) + 2) ^ 4 := by positivity
  rw [hdev]
  constructor
  · intro h
    have h4 : (d : ℝ) < 4 * Real.log ((n : ℝ) + 2) := by linarith
    have hlog : (d : ℝ) < Real.log (((n : ℝ) + 2) ^ 4) := by
      rwa [Real.log_pow, Nat.cast_ofNat]
    calc
      Real.exp (d : ℝ) < Real.exp (Real.log (((n : ℝ) + 2) ^ 4)) := Real.exp_lt_exp.mpr hlog
      _ = ((n : ℝ) + 2) ^ 4 := Real.exp_log hn2_pow_pos
  · intro h
    have hlog : (d : ℝ) < Real.log (((n : ℝ) + 2) ^ 4) := by
      rw [← Real.exp_lt_exp, Real.exp_log hn2_pow_pos]
      exact h
    rw [Real.log_pow, Nat.cast_ofNat] at hlog
    linarith

/-- Same equivalence with opposite strict inequality `2 * log (n + 2) < deviation`. -/
theorem two_log_lt_deviation_iff (a : ℤ) (n : ℕ) :
    2 * Real.log ((n : ℝ) + 2) < |((a.natAbs : ℝ) - (n : ℝ) / 2)| ↔
      ((n : ℝ) + 2) ^ 4 < Real.exp (Int.natAbs (2 * (a.natAbs : ℤ) - (n : ℤ)) : ℝ) := by
  let d : ℕ := Int.natAbs (2 * (a.natAbs : ℤ) - (n : ℤ))
  have hdev : |((a.natAbs : ℝ) - (n : ℝ) / 2)| = (d : ℝ) / 2 := by
    have h := deviation_eq_twoDeviation_div_two (fun _ => a) n
    simpa [deviation, twoDeviation, d] using h
  have hn2_pos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hn2_pow_pos : (0 : ℝ) < ((n : ℝ) + 2) ^ 4 := by positivity
  rw [hdev]
  constructor
  · intro h
    have hlog : Real.log (((n : ℝ) + 2) ^ 4) < (d : ℝ) := by
      rw [Real.log_pow, Nat.cast_ofNat]
      linarith
    calc
      ((n : ℝ) + 2) ^ 4 = Real.exp (Real.log (((n : ℝ) + 2) ^ 4)) := (Real.exp_log hn2_pow_pos).symm
      _ < Real.exp (d : ℝ) := Real.exp_lt_exp.mpr hlog
  · intro h
    have hlog : Real.log (((n : ℝ) + 2) ^ 4) < (d : ℝ) := by
      rw [← Real.exp_lt_exp, Real.exp_log hn2_pow_pos]
      exact h
    rw [Real.log_pow, Nat.cast_ofNat] at hlog
    linarith

/-- Soundness of the upper-bound rational check `taylorHi ^ d < (n + 2)^4` in `verify_a377090.py`. -/
theorem taylorHi_certifies_bound (a : ℤ) (n : ℕ)
    (hcert : taylorHi ^ Int.natAbs (2 * (a.natAbs : ℤ) - (n : ℤ)) < (((n : ℚ) + 2) ^ 4)) :
    |((a.natAbs : ℝ) - (n : ℝ) / 2)| < 2 * Real.log ((n : ℝ) + 2) := by
  rw [deviation_lt_two_log_iff]
  let d : ℕ := Int.natAbs (2 * (a.natAbs : ℤ) - (n : ℤ))
  have hexp_d : Real.exp (d : ℝ) = (Real.exp 1) ^ d := by
    rw [← Real.exp_nat_mul]
    simp
  have hpow : (Real.exp 1) ^ d ≤ (taylorHi : ℝ) ^ d :=
    pow_le_pow_left₀ (Real.exp_pos 1).le exp_one_lt_taylorHi.le d
  have hcertR : ((taylorHi : ℝ) ^ d) < ((n : ℝ) + 2) ^ 4 := by
    dsimp only [d]
    exact_mod_cast hcert
  linarith [hexp_d, hpow, hcertR]

/-- Soundness of the lower-bound rational violation check `((n + 2)^4 ≤ taylorLo ^ d)` for `d ≥ 1`. -/
theorem taylorLo_certifies_violation (a : ℤ) (n : ℕ)
    (hd : 1 ≤ Int.natAbs (2 * (a.natAbs : ℤ) - (n : ℤ)))
    (hcert : (((n : ℚ) + 2) ^ 4) ≤ taylorLo ^ Int.natAbs (2 * (a.natAbs : ℤ) - (n : ℤ))) :
    2 * Real.log ((n : ℝ) + 2) < |((a.natAbs : ℝ) - (n : ℝ) / 2)| := by
  rw [two_log_lt_deviation_iff]
  let d : ℕ := Int.natAbs (2 * (a.natAbs : ℤ) - (n : ℤ))
  have hexp_d : Real.exp (d : ℝ) = (Real.exp 1) ^ d := by
    rw [← Real.exp_nat_mul]
    simp
  have hloR : (0 : ℝ) ≤ (taylorLo : ℝ) := by exact_mod_cast taylorLo_pos.le
  have hpow : (taylorLo : ℝ) ^ d < (Real.exp 1) ^ d :=
    pow_lt_pow_left₀ taylorLo_lt_exp_one hloR (by omega)
  have hcertR : ((n : ℝ) + 2) ^ 4 ≤ (taylorLo : ℝ) ^ d := by
    dsimp only [d]
    exact_mod_cast hcert
  linarith [hexp_d, hpow, hcertR]

/-- Monotonicity reduction used by `verify_a377090.py`: once a value `d = 2 * δ(n₁)` satisfies
`δ(n₁) < 2 * log (n₁ + 2)`, any later index `n₂ ≥ n₁` with the same `d` also satisfies it. -/
theorem earliest_index_monotonicity (a : ℕ → ℤ) {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂)
    (hd : twoDeviation a n₁ = twoDeviation a n₂)
    (h1 : deviation a n₁ < 2 * Real.log ((n₁ : ℝ) + 2)) :
    deviation a n₂ < 2 * Real.log ((n₂ : ℝ) + 2) := by
  rw [deviation_eq_twoDeviation_div_two] at h1 ⊢
  rw [← hd]
  have hlog : Real.log ((n₁ : ℝ) + 2) ≤ Real.log ((n₂ : ℝ) + 2) := by
    apply Real.log_le_log (by positivity)
    have : (n₁ : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast hn
    linarith
  linarith

/-- Certified strict logarithmic violation at `n = 370313`, `a(n) = -185183` (purely rational). -/
theorem counterexample_inequality_370313 :
    2 * Real.log ((370313 : ℝ) + 2) < |(((-185183 : ℤ).natAbs : ℝ) - (370313 : ℝ) / 2)| := by
  apply taylorLo_certifies_violation (-185183) 370313 (by decide)
  have h27 : (27 / 10 : ℚ) < taylorLo := by
    norm_num [taylorLo, Finset.sum_range_succ, Nat.factorial]
  have hpow53 : ((370313 : ℚ) + 2) ^ 4 ≤ (27 / 10 : ℚ) ^ 53 := by
    norm_num
  have hmono : (27 / 10 : ℚ) ^ 53 ≤ taylorLo ^ 53 :=
    pow_le_pow_left₀ (by norm_num) h27.le 53
  refine (hpow53.trans hmono).trans_eq ?_
  congr 1

private theorem not_prime_of_dvd_witness {r d : ℕ} (hd1 : 1 < d) (hdr : d < r) (hdvd : d ∣ r) :
    ¬Nat.Prime r := by
  intro hprime
  rcases hprime.eq_one_or_self_of_dvd d hdvd with h1 | hself <;> omega

private def existsDivIn (r lo len : ℕ) : ℕ → Bool
  | 0 => false
  | fuel + 1 =>
    if len ≤ 1 then
      if len = 1 then decide (1 < lo) && decide (lo < r) && (r % lo == 0) else false
    else
      let h := len / 2
      existsDivIn r lo h fuel || existsDivIn r (lo + h) (len - h) fuel

private theorem existsDivIn_sound (r lo len fuel : ℕ) (h : existsDivIn r lo len fuel = true) :
    ∃ d : ℕ, 1 < d ∧ d < r ∧ d ∣ r := by
  induction fuel generalizing lo len with
  | zero => simp [existsDivIn] at h
  | succ fuel ih =>
    dsimp [existsDivIn] at h
    split_ifs at h with hlen h1
    · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      exact ⟨lo, h.1.1, h.1.2, Nat.dvd_of_mod_eq_zero h.2⟩
    · simp only [Bool.or_eq_true] at h
      rcases h with hL | hR
      · exact ih lo (len / 2) hL
      · exact ih (lo + len / 2) (len - len / 2) hR

private def allCompositeFrom (lo len dMax dfuel : ℕ) : ℕ → Bool
  | 0 => false
  | fuel + 1 =>
    if len ≤ 1 then
      if len = 1 then existsDivIn lo 2 dMax dfuel else true
    else
      let h := len / 2
      allCompositeFrom lo h dMax dfuel fuel &&
        allCompositeFrom (lo + h) (len - h) dMax dfuel fuel

private theorem allCompositeFrom_sound (lo len dMax dfuel fuel : ℕ)
    (h : allCompositeFrom lo len dMax dfuel fuel = true) :
    ∀ r : ℕ, lo ≤ r → r < lo + len → ¬Nat.Prime r := by
  induction fuel generalizing lo len with
  | zero => simp [allCompositeFrom] at h
  | succ fuel ih =>
    intro r hr1 hr2
    dsimp [allCompositeFrom] at h
    split_ifs at h with hlen h1
    · have hr : r = lo := by omega
      subst hr
      obtain ⟨d, hd1, hdr, hdvd⟩ := existsDivIn_sound r 2 dMax dfuel h
      exact not_prime_of_dvd_witness hd1 hdr hdvd
    · omega
    · simp only [Bool.and_eq_true] at h
      by_cases hrmid : r < lo + len / 2
      · exact ih lo (len / 2) h.1 r hr1 hrmid
      · exact ih (lo + len / 2) (len - len / 2) h.2 r (by omega) (by omega)

/-- `[370261, 370373]` is a gap of width `112` between consecutive primes. -/
theorem prime_gap_370261_370373 :
    Nat.Prime 370261 ∧ Nat.Prime 370373 ∧ 370373 - 370261 = 112 ∧
    ∀ r : ℕ, 370261 < r → r < 370373 → ¬Nat.Prime r := by
  refine ⟨by norm_num, by norm_num, rfl, ?_⟩
  have hcomp : allCompositeFrom 370262 111 610 12 10 = true := by decide
  intro r hr1 hr2
  exact allCompositeFrom_sound 370262 111 610 12 10 hcomp r (by omega) (by omega)

end A377090
