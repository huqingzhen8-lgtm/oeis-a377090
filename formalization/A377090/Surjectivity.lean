import A377090.Basic
import A377090.AnalyticInputs

/-!
# Theorem 1: Unconditional Surjectivity of OEIS A377090

This file formalizes Section 2 of the paper, proving:

* `a377090_surjective`: assuming `GoldbachMeanSquareInput`, every integer appears in `a377090`.
* `a377090_bijective`: `a377090` is a bijection `ℕ → ℤ`.

Chebyshev's prime-counting lower bound is imported directly from `AnalyticInputs`
(proved inside Lean from Mathlib's `Chebyshev.pi_ge`).
-/

namespace A377090

open Finset Filter

section AsymptoticHelpers

private theorem eventually_pow_log_lt_const_mul_self (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, Real.log X ^ k < ε * X := by
  have ht : Tendsto (fun X : ℝ => Real.log X ^ k / (1 * X + 0)) atTop (nhds 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 k one_ne_zero
  have hev := ht.eventually (eventually_lt_nhds hε)
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with X hX hX0
  simp only [one_mul, add_zero] at hX
  exact (div_lt_iff₀ hX0).mp hX

private theorem eventually_const_lt_log_pow (k : ℕ) (hk : 1 ≤ k) (M : ℝ) :
    ∀ᶠ X : ℝ in atTop, M < Real.log X ^ k := by
  have ht : Tendsto (fun X : ℝ => Real.log X ^ k) atTop atTop :=
    (tendsto_pow_atTop (by omega : k ≠ 0)).comp Real.tendsto_log_atTop
  exact ht.eventually_gt_atTop M

end AsymptoticHelpers

section SurjectivityProof

private theorem exists_odd_and_even_omitted {b₀ : ℤ} (hb₀ : b₀ ∉ Set.range a377090) :
    ∃ h₀ h₁ : ℤ, h₀ ∉ Set.range a377090 ∧ h₁ ∉ Set.range a377090 ∧ h₀ % 2 = 0 ∧ h₁ % 2 = 1 := by
  obtain ⟨P₀, hP₀⟩ := exists_large_prime_add_sub_omitted hb₀
  obtain ⟨p₀, hp₀_ge, hp₀⟩ := Nat.exists_infinite_primes (max P₀ 3)
  have hp₀_P₀ : P₀ ≤ p₀ := le_trans (le_max_left _ _) hp₀_ge
  have hp₀_3 : 3 ≤ p₀ := le_trans (le_max_right _ _) hp₀_ge
  have hb₁ : b₀ + (p₀ : ℤ) ∉ Set.range a377090 := (hP₀ p₀ hp₀ hp₀_P₀).1
  have hp₀_odd : p₀ % 2 = 1 := by
    rcases hp₀.eq_two_or_odd with rfl | hodd
    · omega
    · exact hodd
  by_cases hmod : b₀ % 2 = 0
  · refine ⟨b₀, b₀ + (p₀ : ℤ), hb₀, hb₁, hmod, ?_⟩
    omega
  · refine ⟨b₀ + (p₀ : ℤ), b₀, hb₁, hb₀, ?_, ?_⟩ <;> omega

private theorem between_natAbs_lt {h t z : ℤ} {K X_nat d : ℕ}
    (ht : t = h + (if h < t then (1 : ℤ) else -1) * (X_nat : ℤ))
    (hz : z = h + (if h < t then (1 : ℤ) else -1) * (d : ℤ))
    (hhK : h.natAbs ≤ K) (hKt : K < t.natAbs)
    (hd0 : 0 < d) (hdX : d < X_nat) : z.natAbs < t.natAbs := by
  split_ifs at ht hz <;> omega

private theorem exists_smaller_omitted_neighbor (hG : GoldbachMeanSquareInput)
    {h₀ h₁ : ℤ} (hh₀ : h₀ ∉ Set.range a377090) (hh₁ : h₁ ∉ Set.range a377090)
    (hh₀_even : h₀ % 2 = 0) (hh₁_odd : h₁ % 2 = 1) :
    ∃ T₀ : ℕ, ∀ t : ℤ, T₀ ≤ t.natAbs →
      ∃ z : ℤ, z ∉ Set.range a377090 ∧ z.natAbs < t.natAbs ∧ Nat.Prime (t - z).natAbs := by
  classical
  let K : ℕ := max h₀.natAbs h₁.natAbs
  obtain ⟨c, hc_pos, hgold⟩ := goldbach_uniform_lower_bound hG
  obtain ⟨C₆, _hC₆_pos, hbad6⟩ := hgold 6 (by norm_num)
  obtain ⟨cπ, hcπ_pos, Nπ, hNπ16, hpi_ge⟩ := chebyshev_primeCounting_lower
  have hcπ2_pos : 0 < cπ / 2 := by linarith
  have hc2_pos : 0 < c / 2 := by linarith
  have hε1_pos : 0 < cπ / (2 * (2 + 2 * (K : ℝ))) := by positivity
  have hε2_pos : 0 < (c / 2) / (2 * (K : ℝ) + 2) := by positivity
  have hev : ∀ᶠ X : ℝ in atTop,
      hG.X₀ ≤ X ∧ (16 : ℝ) ≤ X ∧ max 2 cπ < Real.log X ∧
      2 * Real.log X ^ 3 ≤ X ∧
      (Nπ : ℝ) + 1 ≤ X / Real.log X ^ 3 ∧
      C₆ < (cπ / 2) * Real.log X ^ 2 ∧
      Real.log X ^ 4 < (cπ / (2 * (2 + 2 * (K : ℝ)))) * X ∧
      2 < (c / 2) * Real.log X ∧
      Real.log X ^ 2 < ((c / 2) / (2 * (K : ℝ) + 2)) * X := by
    have hεNπ_pos : 0 < (1 : ℝ) / ((Nπ : ℝ) + 1) := by positivity
    filter_upwards
      [eventually_ge_atTop hG.X₀,
       eventually_ge_atTop (16 : ℝ),
       eventually_const_lt_log_pow 1 le_rfl (max 2 cπ),
       eventually_pow_log_lt_const_mul_self 3 (by norm_num : (0 : ℝ) < 1 / 2),
       eventually_pow_log_lt_const_mul_self 3 hεNπ_pos,
       eventually_const_lt_log_pow 2 (by omega) (2 * C₆ / cπ),
       eventually_pow_log_lt_const_mul_self 4 hε1_pos,
       eventually_const_lt_log_pow 1 le_rfl (4 / c),
       eventually_pow_log_lt_const_mul_self 2 hε2_pos]
      with X hX₀ h16 hlog_max hlog3_half hlog3_Nπ hlog2_C₆ hlog4 hlog1_raw hlog2
    rw [pow_one] at hlog_max hlog1_raw
    have hlog1 : 1 < Real.log X := lt_of_le_of_lt (by norm_num : (1 : ℝ) ≤ max 2 cπ) hlog_max
    have hlog3_pos : 0 < Real.log X ^ 3 := pow_pos (by linarith) 3
    refine ⟨hX₀, h16, hlog_max, by linarith, ?_, ?_, hlog4, ?_, hlog2⟩
    · rw [le_div_iff₀ hlog3_pos]
      have hNπ1_pos : (0 : ℝ) < (Nπ : ℝ) + 1 := by positivity
      calc
        ((Nπ : ℝ) + 1) * Real.log X ^ 3
            ≤ ((Nπ : ℝ) + 1) * ((1 / ((Nπ : ℝ) + 1)) * X) :=
                mul_le_mul_of_nonneg_left hlog3_Nπ.le hNπ1_pos.le
        _ = X := by field_simp
    · calc
        C₆ = (2 * C₆ / cπ) * (cπ / 2) := by field_simp
        _ < Real.log X ^ 2 * (cπ / 2) := mul_lt_mul_of_pos_right hlog2_C₆ hcπ2_pos
        _ = (cπ / 2) * Real.log X ^ 2 := by ring
    · calc
        (2 : ℝ) = (4 / c) * (c / 2) := by field_simp; norm_num
        _ < Real.log X * (c / 2) := mul_lt_mul_of_pos_right hlog1_raw hc2_pos
        _ = (c / 2) * Real.log X := by ring
  obtain ⟨X_thresh, hX_thresh⟩ := Filter.eventually_atTop.mp hev
  let T₀ : ℕ := Nat.ceil (max X_thresh 4) + K + 1
  refine ⟨T₀, fun t ht => ?_⟩
  let h : ℤ := if t % 2 = 0 then h₁ else h₀
  have hh_not : h ∉ Set.range a377090 := by
    dsimp only [h]; split_ifs <;> assumption
  have hh_abs : h.natAbs ≤ K := by
    dsimp only [h, K]; split_ifs <;> [exact le_max_right _ _; exact le_max_left _ _]
  have ht_sub_h_odd : (t - h).natAbs % 2 = 1 := by
    dsimp only [h]; split_ifs <;> omega
  let s : ℤ := if h < t then 1 else -1
  let X_nat : ℕ := (t - h).natAbs
  have hX_nat_ge_abs : t.natAbs - K ≤ X_nat := by
    dsimp only [X_nat]; omega
  have ht_eq : t = h + s * (X_nat : ℤ) := by
    dsimp only [s, X_nat]; split_ifs <;> omega
  have hs_sq : s * s = 1 := by
    dsimp only [s]; split_ifs <;> decide
  have hX_nat_ge_ceil : Nat.ceil (max X_thresh 4) ≤ X_nat := by omega
  have hX_ge_thresh : X_thresh ≤ (X_nat : ℝ) := by
    have h1 : max X_thresh 4 ≤ (Nat.ceil (max X_thresh 4) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (max X_thresh 4) : ℝ) ≤ (X_nat : ℝ) := by exact_mod_cast hX_nat_ge_ceil
    exact (le_max_left _ _).trans (h1.trans h2)
  let X : ℝ := (X_nat : ℝ)
  obtain ⟨hX_X₀, hX_16, hlogX_max, hlog3_half, hNπ_le_div, hC₆_bound, hlog4_bound, hlog1_bound,
    hlog2_bound⟩ := hX_thresh X hX_ge_thresh
  have hlogX_gt1 : 1 < Real.log X := lt_of_le_of_lt (by norm_num : (1 : ℝ) ≤ max 2 cπ) hlogX_max
  have hlogX_gt2 : 2 < Real.log X := lt_of_le_of_lt (le_max_left 2 cπ) hlogX_max
  have hX_pos : 0 < X := by linarith
  have hlogX_pos : 0 < Real.log X := by linarith
  have hlogX3_pos : 0 < Real.log X ^ 3 := pow_pos hlogX_pos 3
  let H : ℕ := Nat.floor (X / Real.log X ^ 3)
  have hH_le_div : (H : ℝ) ≤ X / Real.log X ^ 3 := Nat.floor_le (div_nonneg hX_pos.le hlogX3_pos.le)
  have hdiv_sub_lt_H : X / Real.log X ^ 3 - 1 < (H : ℝ) := by
    have := Nat.lt_floor_add_one (X / Real.log X ^ 3)
    linarith
  have hNπ_le_H : Nπ ≤ H := by
    have hlt : (Nπ : ℝ) < (H : ℝ) := by linarith
    exact_mod_cast hlt.le
  have hH_ge_16 : 16 ≤ H := hNπ16.trans hNπ_le_H
  have hH_le_half : (H : ℝ) ≤ X / 2 := by
    have hlog3_ge2 : (2 : ℝ) ≤ Real.log X ^ 3 := by
      have : (8 : ℝ) < Real.log X ^ 3 := by nlinarith
      linarith
    have hdiv : X / Real.log X ^ 3 ≤ X / 2 :=
      div_le_div_of_nonneg_left hX_pos.le (by norm_num) hlog3_ge2
    exact hH_le_div.trans hdiv
  have hH_le_Xnat : H ≤ X_nat := by
    have hle : (H : ℝ) ≤ (X_nat : ℝ) := hH_le_half.trans (by dsimp only [X]; linarith)
    exact_mod_cast hle
  have hH_le_X_half_nat : 2 * H ≤ X_nat := by
    have hle : ((2 * H : ℕ) : ℝ) ≤ (X_nat : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hle
  -- Count candidate odd primes p ≤ H
  let Pcand : Finset ℕ := (Finset.range (H + 1)).filter (fun p : ℕ => Nat.Prime p ∧ 3 ≤ p)
  have hpi_le_Pcand : Nat.primeCounting H ≤ Pcand.card + 1 := by
    rw [primeCounting_eq_card_filter]
    have hsub : (Finset.range (H + 1)).filter Nat.Prime ⊆ insert 2 Pcand := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp_rng, hp_prime⟩
      rcases lt_or_ge p 3 with hp3 | hp3
      · have hp2 : p = 2 := by
          have := hp_prime.two_le
          omega
        rw [hp2]
        exact Finset.mem_insert_self 2 Pcand
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hp_rng, hp_prime, hp3⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_insert_le 2 Pcand)
  -- Excluded class (1): primes p with h + s * p ∈ range a377090
  let Pbad1 : Finset ℕ := Pcand.filter (fun p : ℕ => h + s * (p : ℤ) ∈ Set.range a377090)
  have hPbad1_le : Pbad1.card ≤ 2 * K := by
    let idxOf : ℕ → ℕ := fun p =>
      if hp : h + s * (p : ℤ) ∈ Set.range a377090 then Nat.find hp else 0
    have hcard_eq : Pbad1.card = (Pbad1.image idxOf).card := by
      symm
      apply Finset.card_image_of_injOn
      intro p₁ hp₁ p₂ hp₂ heq
      dsimp only [idxOf] at heq
      have h1 : h + s * (p₁ : ℤ) ∈ Set.range a377090 := (Finset.mem_filter.mp hp₁).2
      have h2 : h + s * (p₂ : ℤ) ∈ Set.range a377090 := (Finset.mem_filter.mp hp₂).2
      simp only [h1, h2, ↓reduceDIte] at heq
      have hs1 := Nat.find_spec h1
      have hs2 := Nat.find_spec h2
      rw [heq, hs2] at hs1
      have hsp : s * (p₁ : ℤ) = s * (p₂ : ℤ) := by omega
      have hpz : (p₁ : ℤ) = (p₂ : ℤ) := by
        dsimp only [s] at hsp; split_ifs at hsp <;> omega
      exact_mod_cast hpz
    have hle_h : (Pbad1.image idxOf).card ≤ 2 * h.natAbs := by
      apply omitted_neighbors_card_le hh_not
      intro j hj
      rcases Finset.mem_image.mp hj with ⟨p, hp, rfl⟩
      have hp_cand : p ∈ Pcand := (Finset.mem_filter.mp hp).1
      have hp_prime : Nat.Prime p := (Finset.mem_filter.mp hp_cand).2.1
      have hp_mem : h + s * (p : ℤ) ∈ Set.range a377090 := (Finset.mem_filter.mp hp).2
      dsimp only [idxOf]
      simp only [hp_mem, ↓reduceDIte]
      rw [Nat.find_spec hp_mem]
      have hnat : (h + s * (p : ℤ) - h).natAbs = p := by
        have h1 : h + s * (p : ℤ) - h = s * (p : ℤ) := by ring
        rw [h1, Int.natAbs_mul]
        have hs_abs : s.natAbs = 1 := by dsimp only [s]; split_ifs <;> decide
        rw [hs_abs, one_mul, Int.natAbs_natCast]
      rwa [hnat]
    omega
  -- Excluded class (2): primes p with goldbachCount (X_nat - p) < c * X / (log X)^2
  let Bad := (Finset.range (Nat.floor X + 1)).filter
    (fun m : ℕ => Even m ∧ X / 2 ≤ (m : ℝ) ∧ (goldbachCount m : ℝ) < c * X / (Real.log X) ^ 2)
  let Pbad2 : Finset ℕ := Pcand.filter
    (fun p : ℕ => (goldbachCount (X_nat - p) : ℝ) < c * X / (Real.log X) ^ 2)
  have hPbad2_le : Pbad2.card ≤ Bad.card := by
    refine Finset.card_le_card_of_injOn (fun p => X_nat - p) ?_ ?_
    · intro p hp
      have hp_cand : p ∈ Pcand := (Finset.mem_filter.mp hp).1
      have hp_rng := (Finset.mem_filter.mp hp_cand).1
      have hp_prime : Nat.Prime p := (Finset.mem_filter.mp hp_cand).2.1
      have hp3 : 3 ≤ p := (Finset.mem_filter.mp hp_cand).2.2
      have hpH : p ≤ H := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp_rng)
      have hpX : p ≤ X_nat := hpH.trans hH_le_Xnat
      have hp_odd : p % 2 = 1 := by
        rcases hp_prime.eq_two_or_odd with rfl | hodd
        · omega
        · exact hodd
      have hm_even : Even (X_nat - p) := by
        rw [Nat.even_iff]
        omega
      have hm_rng : X_nat - p ∈ Finset.range (Nat.floor X + 1) := by
        rw [Finset.mem_range, Nat.floor_natCast]
        omega
      have hm_low : X / 2 ≤ ((X_nat - p : ℕ) : ℝ) := by
        have hpR : (p : ℝ) ≤ (H : ℝ) := by exact_mod_cast hpH
        have hcast : ((X_nat - p : ℕ) : ℝ) = X - (p : ℝ) := by
          rw [Nat.cast_sub hpX]
        linarith
      exact Finset.mem_filter.mpr ⟨hm_rng, hm_even, hm_low, (Finset.mem_filter.mp hp).2⟩
    · intro p₁ hp₁ p₂ hp₂ heq
      have hp1H : p₁ ≤ H := Nat.lt_succ_iff.mp
        (Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp₁).1).1)
      have hp2H : p₂ ≤ H := Nat.lt_succ_iff.mp
        (Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp₂).1).1)
      have hp1X : p₁ ≤ X_nat := hp1H.trans hH_le_Xnat
      have hp2X : p₂ ≤ X_nat := hp2H.trans hH_le_Xnat
      dsimp only at heq
      omega
  have hBad_card_le : (Bad.card : ℝ) ≤ C₆ * X / Real.log X ^ 6 := by
    have hraw := hbad6 X hX_X₀
    rw [← Real.rpow_natCast]
    exact hraw.trans_eq (by norm_num)
  -- Show Pbad1 ∪ Pbad2 has strictly fewer elements than Pcand
  have hpi_H_lower : cπ * (H : ℝ) / Real.log (H : ℝ) ≤ (Nat.primeCounting H : ℝ) :=
    hpi_ge H hNπ_le_H
  have hH_posR : (0 : ℝ) < (H : ℝ) := by
    have : (16 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH_ge_16
    linarith
  have hlogH_pos : 0 < Real.log (H : ℝ) := by
    have : (16 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH_ge_16
    exact Real.log_pos (by linarith)
  have hlogH_le_logX : Real.log (H : ℝ) ≤ Real.log X := by
    dsimp only [X]
    exact Real.log_le_log hH_posR (by exact_mod_cast hH_le_Xnat)
  have hpi_X_lower : cπ * (X / Real.log X ^ 3 - 1) / Real.log X ≤ (Nat.primeCounting H : ℝ) := by
    have h1 : cπ * (X / Real.log X ^ 3 - 1) / Real.log X ≤ cπ * (H : ℝ) / Real.log X := by
      gcongr
    have h2 : cπ * (H : ℝ) / Real.log X ≤ cπ * (H : ℝ) / Real.log (H : ℝ) := by
      gcongr
    exact h1.trans (h2.trans hpi_H_lower)
  have hbad_lt_cand : (Pbad1 ∪ Pbad2).card < Pcand.card := by
    suffices hR : ((Pbad1.card : ℝ) + (Pbad2.card : ℝ) + 1) < (Nat.primeCounting H : ℝ) by
      have hcard_un : ((Pbad1 ∪ Pbad2).card : ℝ) ≤ (Pbad1.card : ℝ) + (Pbad2.card : ℝ) := by
        exact_mod_cast Finset.card_union_le Pbad1 Pbad2
      have hpiR : (Nat.primeCounting H : ℝ) ≤ (Pcand.card : ℝ) + 1 := by exact_mod_cast hpi_le_Pcand
      have hltR : ((Pbad1 ∪ Pbad2).card : ℝ) < (Pcand.card : ℝ) := by linarith
      exact_mod_cast hltR
    have hPbad1R : (Pbad1.card : ℝ) ≤ 2 * (K : ℝ) := by exact_mod_cast hPbad1_le
    have hPbad2R : (Pbad2.card : ℝ) ≤ C₆ * X / Real.log X ^ 6 :=
      (by exact_mod_cast hPbad2_le : (Pbad2.card : ℝ) ≤ (Bad.card : ℝ)).trans hBad_card_le
    have hstepA : (2 + 2 * (K : ℝ)) * Real.log X ^ 4 < (cπ / 2) * X := by
      have h2K_pos : 0 < 2 + 2 * (K : ℝ) := by positivity
      have := mul_lt_mul_of_pos_left hlog4_bound h2K_pos
      have heq : (2 + 2 * (K : ℝ)) * (cπ / (2 * (2 + 2 * (K : ℝ))) * X) = (cπ / 2) * X := by
        field_simp
      linarith
    have hstepA_div : 2 + 2 * (K : ℝ) < (cπ / 2) * X / Real.log X ^ 4 := by
      rw [lt_div_iff₀ (pow_pos hlogX_pos 4)]
      exact hstepA
    have hstepB_div : C₆ * X / Real.log X ^ 6 < (cπ / 2) * X / Real.log X ^ 4 := by
      have hlog6 : Real.log X ^ 6 = Real.log X ^ 4 * Real.log X ^ 2 := by ring
      rw [hlog6]
      have hmul : C₆ * X < ((cπ / 2) * Real.log X ^ 2) * X :=
        mul_lt_mul_of_pos_right hC₆_bound hX_pos
      have hden_pos : 0 < Real.log X ^ 4 * Real.log X ^ 2 := by positivity
      calc
        C₆ * X / (Real.log X ^ 4 * Real.log X ^ 2)
            < ((cπ / 2) * Real.log X ^ 2 * X) / (Real.log X ^ 4 * Real.log X ^ 2) :=
                div_lt_div_of_pos_right hmul hden_pos
        _ = (cπ / 2) * X / Real.log X ^ 4 := by
            have hne : Real.log X ^ 2 ≠ 0 := (pow_pos hlogX_pos 2).ne'
            field_simp
    have hlog4_rhs : (cπ / 2) * X / Real.log X ^ 4 + (cπ / 2) * X / Real.log X ^ 4 - 1 ≤
        cπ * (X / Real.log X ^ 3 - 1) / Real.log X := by
      have hsub1 : cπ / Real.log X ≤ 1 :=
        (div_le_one hlogX_pos).mpr (lt_of_le_of_lt (le_max_right 2 cπ) hlogX_max).le
      have hlog_ne : Real.log X ≠ 0 := hlogX_pos.ne'
      have heq : cπ * (X / Real.log X ^ 3 - 1) / Real.log X =
          (cπ / 2) * X / Real.log X ^ 4 + (cπ / 2) * X / Real.log X ^ 4 - cπ / Real.log X := by
        field_simp
        ring
      linarith
    linarith [hPbad1R, hPbad2R, hstepA_div, hstepB_div, hlog4_rhs, hpi_X_lower]
  have hdiff_ne : (Pcand \ (Pbad1 ∪ Pbad2)).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    have hle := Finset.card_le_card hsub
    omega
  obtain ⟨p, hp_diff⟩ := hdiff_ne
  rcases Finset.mem_sdiff.mp hp_diff with ⟨hp_cand, hp_not_bad⟩
  have hp_not1 : p ∉ Pbad1 := fun hmem => hp_not_bad (Finset.mem_union_left _ hmem)
  have hp_not2 : p ∉ Pbad2 := fun hmem => hp_not_bad (Finset.mem_union_right _ hmem)
  rcases Finset.mem_filter.mp hp_cand with ⟨hp_rng, hp_prime, _hp3⟩
  have hpH : p ≤ H := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp_rng)
  have hpX : p ≤ X_nat := hpH.trans hH_le_Xnat
  let b : ℤ := h + s * (p : ℤ)
  have hb_not : b ∉ Set.range a377090 := fun hb_mem =>
    hp_not1 (Finset.mem_filter.mpr ⟨hp_cand, hb_mem⟩)
  have hgold_p : c * X / Real.log X ^ 2 ≤ (goldbachCount (X_nat - p) : ℝ) := by
    by_contra hlt
    push Not at hlt
    exact hp_not2 (Finset.mem_filter.mpr ⟨hp_cand, hlt⟩)
  have hb_abs_le : b.natAbs ≤ K + H := by
    dsimp only [b, s]
    split_ifs <;> omega
  have h2b_lt_gold : 2 * (b.natAbs : ℝ) < (goldbachCount (X_nat - p) : ℝ) := by
    have hlog2_pos : 0 < Real.log X ^ 2 := pow_pos hlogX_pos 2
    have h2K_lt : 2 * (K : ℝ) < (c / 2) * X / Real.log X ^ 2 := by
      have h2K_pos : 0 < 2 * (K : ℝ) + 2 := by positivity
      have hmul := mul_lt_mul_of_pos_left hlog2_bound h2K_pos
      have heq : (2 * (K : ℝ) + 2) * (((c / 2) / (2 * (K : ℝ) + 2)) * X) = (c / 2) * X := by
        field_simp
      have h1 : (2 * (K : ℝ) + 2) * Real.log X ^ 2 < (c / 2) * X := by linarith
      have h3 : 2 * (K : ℝ) * Real.log X ^ 2 < (c / 2) * X := by nlinarith
      exact (lt_div_iff₀ hlog2_pos).mpr h3
    have h2H_lt : 2 * (H : ℝ) < (c / 2) * X / Real.log X ^ 2 := by
      have h2H_le : 2 * (H : ℝ) ≤ 2 * X / Real.log X ^ 3 := by
        calc
          2 * (H : ℝ) ≤ 2 * (X / Real.log X ^ 3) := by linarith
          _ = 2 * X / Real.log X ^ 3 := by ring
      have hdiv_lt : 2 * X / Real.log X ^ 3 < ((c / 2) * Real.log X) * X / Real.log X ^ 3 :=
        div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hlog1_bound hX_pos) hlogX3_pos
      have heq : ((c / 2) * Real.log X) * X / Real.log X ^ 3 = (c / 2) * X / Real.log X ^ 2 := by
        have hne : Real.log X ≠ 0 := hlogX_pos.ne'
        field_simp
      linarith
    have hb_real : 2 * (b.natAbs : ℝ) ≤ 2 * (K : ℝ) + 2 * (H : ℝ) := by
      have : (b.natAbs : ℝ) ≤ (K : ℝ) + (H : ℝ) := by exact_mod_cast hb_abs_le
      linarith
    have hsum_eq : (c / 2) * X / Real.log X ^ 2 + (c / 2) * X / Real.log X ^ 2 = c * X / Real.log X ^ 2 := by
      ring
    linarith
  have h2b_lt_nat : 2 * b.natAbs < goldbachCount (X_nat - p) := by
    exact_mod_cast h2b_lt_gold
  let U : Finset ℕ := (Finset.range (X_nat - p + 1)).filter
    (fun u : ℕ => Nat.Prime u ∧ Nat.Prime (X_nat - p - u))
  have hU_card : U.card = goldbachCount (X_nat - p) := rfl
  let Ubad : Finset ℕ := U.filter (fun u : ℕ => b + s * (u : ℤ) ∈ Set.range a377090)
  have hUbad_le : Ubad.card ≤ 2 * b.natAbs := by
    let idxU : ℕ → ℕ := fun u =>
      if hu : b + s * (u : ℤ) ∈ Set.range a377090 then Nat.find hu else 0
    have hcard_eq : Ubad.card = (Ubad.image idxU).card := by
      symm
      apply Finset.card_image_of_injOn
      intro u₁ hu₁ u₂ hu₂ heq
      dsimp only [idxU] at heq
      have h1 : b + s * (u₁ : ℤ) ∈ Set.range a377090 := (Finset.mem_filter.mp hu₁).2
      have h2 : b + s * (u₂ : ℤ) ∈ Set.range a377090 := (Finset.mem_filter.mp hu₂).2
      simp only [h1, h2, ↓reduceDIte] at heq
      have hs1 := Nat.find_spec h1
      have hs2 := Nat.find_spec h2
      rw [heq, hs2] at hs1
      have hsu : s * (u₁ : ℤ) = s * (u₂ : ℤ) := by omega
      have huz : (u₁ : ℤ) = (u₂ : ℤ) := by
        dsimp only [s] at hsu; split_ifs at hsu <;> omega
      exact_mod_cast huz
    rw [hcard_eq]
    apply omitted_neighbors_card_le hb_not
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨u, hu, rfl⟩
    have hu_U : u ∈ U := (Finset.mem_filter.mp hu).1
    have hu_prime : Nat.Prime u := (Finset.mem_filter.mp hu_U).2.1
    have hu_mem : b + s * (u : ℤ) ∈ Set.range a377090 := (Finset.mem_filter.mp hu).2
    dsimp only [idxU]
    simp only [hu_mem, ↓reduceDIte]
    rw [Nat.find_spec hu_mem]
    have hnat : (b + s * (u : ℤ) - b).natAbs = u := by
      have h1 : b + s * (u : ℤ) - b = s * (u : ℤ) := by ring
      rw [h1, Int.natAbs_mul]
      have hs_abs : s.natAbs = 1 := by dsimp only [s]; split_ifs <;> decide
      rw [hs_abs, one_mul, Int.natAbs_natCast]
    rwa [hnat]
  have hUdiff_ne : (U \ Ubad).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    have hle := Finset.card_le_card hsub
    omega
  obtain ⟨u, hu_diff⟩ := hUdiff_ne
  rcases Finset.mem_sdiff.mp hu_diff with ⟨hu_U, hu_not_bad⟩
  have hz_not : b + s * (u : ℤ) ∉ Set.range a377090 :=
    fun hmem => hu_not_bad (Finset.mem_filter.mpr ⟨hu_U, hmem⟩)
  rcases Finset.mem_filter.mp hu_U with ⟨hu_rng, hu_prime, hv_prime⟩
  have hu_le : u ≤ X_nat - p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu_rng)
  have hp_pos : 0 < p := hp_prime.pos
  have hu_pos : 0 < u := hu_prime.pos
  have hv_pos : 0 < X_nat - p - u := hv_prime.pos
  let z : ℤ := b + s * (u : ℤ)
  refine ⟨z, hz_not, ?_, ?_⟩
  · have ht_gt_K : K < t.natAbs := by omega
    have hz_eq : z = h + s * ((p + u : ℕ) : ℤ) := by
      dsimp only [z, b]
      push_cast
      ring
    exact between_natAbs_lt ht_eq hz_eq hh_abs ht_gt_K (by omega) (by omega)
  · have hsub : t - z = s * ((X_nat - p - u : ℕ) : ℤ) := by
      dsimp only [z, b]
      rw [ht_eq]
      dsimp only [s]
      split_ifs <;> omega
    rw [hsub, Int.natAbs_mul]
    have hs_abs : s.natAbs = 1 := by dsimp only [s]; split_ifs <;> decide
    rwa [hs_abs, one_mul, Int.natAbs_natCast]

end SurjectivityProof

/-- **Theorem 1 (Unconditional Surjectivity of OEIS A377090)**:
Under `GoldbachMeanSquareInput` alone (with Chebyshev prime-counting bounds proved inside Lean
from Mathlib), every integer appears in the sequence `a377090`. -/
theorem a377090_surjective (hG : GoldbachMeanSquareInput) : Function.Surjective a377090 := by
  by_contra hnot
  dsimp only [Function.Surjective] at hnot
  push Not at hnot
  obtain ⟨b₀, hb₀_mem⟩ := hnot
  have hb₀ : b₀ ∉ Set.range a377090 := fun ⟨n, hn⟩ => hb₀_mem n hn
  obtain ⟨h₀, h₁, hh₀, hh₁, hh₀_even, hh₁_odd⟩ := exists_odd_and_even_omitted hb₀
  obtain ⟨T₀, hdesc⟩ := exists_smaller_omitted_neighbor hG hh₀ hh₁ hh₀_even hh₁_odd
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (a377090_abs_tendsto.eventually_ge_atTop T₀)
  have hchain : ∀ m : ℕ, (a377090 (N₀ + m)).natAbs + m ≤ (a377090 N₀).natAbs := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        have hstep_ge : T₀ ≤ (a377090 (N₀ + m)).natAbs := hN₀ (N₀ + m) (by omega)
        obtain ⟨z, hz_not, hz_abs, hz_prime⟩ := hdesc (a377090 (N₀ + m)) hstep_ge
        have hz_not_vis : z ∉ prefixSet (N₀ + m) := by
          intro hmem
          rcases Finset.mem_image.mp hmem with ⟨k, _, hk⟩
          exact hz_not ⟨k, hk⟩
        have hz_prime' : Nat.Prime (z - a377090 (N₀ + m)).natAbs := by
          rwa [show (z - a377090 (N₀ + m)).natAbs = (a377090 (N₀ + m) - z).natAbs by
            rw [← Int.natAbs_neg, neg_sub]]
        have hgreedy : (a377090 (N₀ + m + 1)).natAbs ≤ z.natAbs :=
          a377090_greedy_abs hz_not_vis hz_prime'
        have hgreedy' : (a377090 (N₀ + (m + 1))).natAbs ≤ z.natAbs := by
          simpa [Nat.add_assoc] using hgreedy
        omega
  have hcontra := hchain ((a377090 N₀).natAbs + 1)
  omega

/-- OEIS A377090 is a bijection `ℕ → ℤ` under `GoldbachMeanSquareInput`. -/
theorem a377090_bijective (hG : GoldbachMeanSquareInput) : Function.Bijective a377090 :=
  ⟨a377090_injective, a377090_surjective hG⟩

end A377090
