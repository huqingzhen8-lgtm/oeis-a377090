import Mathlib

/-!
# OEIS A377090: Definition, Basic Properties, and Omitted-Point Lemma

This file formalizes the sequence OEIS A377090 (`a377090 : ℕ → ℤ`) without any
additional hypotheses beyond Lean's standard axioms, and proves:

* well-definedness, injectivity, prime step differences, and the greedy rule;
* divergence `|a(n)| → ∞`;
* **Lemma 1.1** (`omitted_neighbors_card_le`): if `b ∉ Set.range a377090`, then at most
  `2 * |b|` (in fact `2 * |b| - 1`) visited terms lie at prime distance from `b`;
* the finite-prefix variant (`prefix_omitted_neighbors_card_le`): at most `2 * |h| + 1`
  terms in `{a(0), …, a(n)}` lie at prime distance from an omitted `h`.
-/

namespace A377090

open Finset Filter

/-- Canonical enumeration of `ℤ`: `0, +1, -1, +2, -2, …`. -/
def ofRank (r : ℕ) : ℤ :=
  if r % 2 = 1 then ((r + 1) / 2 : ℕ) else -((r / 2 : ℕ) : ℤ)

/-- Inverse of `ofRank`: maps each integer to its position in `0, +1, -1, +2, -2, …`. -/
def toRank (z : ℤ) : ℕ :=
  if 0 < z then 2 * z.natAbs - 1 else 2 * z.natAbs

@[simp]
theorem toRank_zero : toRank 0 = 0 := by
  simp [toRank]

@[simp]
theorem ofRank_zero : ofRank 0 = 0 := by
  simp [ofRank]

theorem toRank_ofRank (r : ℕ) : toRank (ofRank r) = r := by
  unfold ofRank toRank
  by_cases hr : r % 2 = 1
  · simp only [hr, ↓reduceIte]
    have hpos : (0 : ℤ) < (((r + 1) / 2 : ℕ) : ℤ) := by omega
    simp only [hpos, ↓reduceIte, Int.natAbs_natCast]
    omega
  · simp only [hr, ↓reduceIte]
    have hnpos : ¬((0 : ℤ) < -((r / 2 : ℕ) : ℤ)) := by omega
    simp only [hnpos, ↓reduceIte, Int.natAbs_neg, Int.natAbs_natCast]
    omega

theorem ofRank_toRank (z : ℤ) : ofRank (toRank z) = z := by
  unfold ofRank toRank
  by_cases hz : 0 < z
  · simp only [hz, ↓reduceIte]
    have hmod : (2 * z.natAbs - 1) % 2 = 1 := by omega
    simp only [hmod, ↓reduceIte]
    omega
  · simp only [hz, ↓reduceIte]
    have hmod : (2 * z.natAbs) % 2 ≠ 1 := by omega
    simp only [hmod, ↓reduceIte]
    omega

theorem ofRank_injective : Function.Injective ofRank :=
  Function.LeftInverse.injective toRank_ofRank

theorem natAbs_le_of_toRank_le {x y : ℤ} (h : toRank x ≤ toRank y) : x.natAbs ≤ y.natAbs := by
  unfold toRank at h
  split_ifs at h <;> omega

theorem toRank_lt_of_natAbs_lt {x y : ℤ} (h : x.natAbs < y.natAbs) : toRank x < toRank y := by
  unfold toRank
  split_ifs <;> omega

theorem toRank_pos_lt_neg {k : ℕ} (hk : 0 < k) : toRank (k : ℤ) < toRank (-(k : ℤ)) := by
  unfold toRank
  have h1 : (0 : ℤ) < (k : ℤ) := Int.natCast_pos.mpr hk
  have h2 : ¬((0 : ℤ) < -(k : ℤ)) := by omega
  simp only [h1, ↓reduceIte, h2, Int.natAbs_natCast, Int.natAbs_neg]
  omega

/-- Every integer `prev` and finite visited set `visited` admits an unvisited prime neighbor. -/
theorem exists_valid_next (prev : ℤ) (visited : Finset ℤ) :
    ∃ r : ℕ, ofRank r ∉ visited ∧ Nat.Prime (ofRank r - prev).natAbs := by
  let M : ℕ := visited.sup Int.natAbs + prev.natAbs + 1
  obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (M + 1)
  refine ⟨toRank (prev + (p : ℤ)), ?_, ?_⟩
  · rw [ofRank_toRank]
    intro hmem
    have hle : (prev + (p : ℤ)).natAbs ≤ visited.sup Int.natAbs :=
      Finset.le_sup (f := Int.natAbs) hmem
    omega
  · rw [ofRank_toRank]
    have hsub : (prev + (p : ℤ) - prev).natAbs = p := by
      rw [add_sub_cancel_left, Int.natAbs_natCast]
    rwa [hsub]

noncomputable section

/-- Step-by-step state `(a(n), {a(0), …, a(n)})` defining OEIS A377090. -/
def a377090State : ℕ → ℤ × Finset ℤ
  | 0 => (0, {0})
  | n + 1 =>
      let prev := (a377090State n).1
      let vis := (a377090State n).2
      let h := exists_valid_next prev vis
      let nxt := ofRank (Nat.find h)
      (nxt, insert nxt vis)

/-- **OEIS A377090**: `a(0) = 0`, greedily minimizing `|a(n)|` (positive on ties) with
`|a(n) - a(n-1)|` prime and no repeated terms. -/
def a377090 (n : ℕ) : ℤ :=
  (a377090State n).1

/-- The finite set `{a(0), …, a(n)}`. -/
def prefixSet (n : ℕ) : Finset ℤ :=
  (Finset.range (n + 1)).image a377090

@[simp]
theorem a377090_zero : a377090 0 = 0 := rfl

theorem a377090State_snd_eq_prefixSet : ∀ n : ℕ, (a377090State n).2 = prefixSet n
  | 0 => by
      simp [a377090State, prefixSet]
  | n + 1 => by
      have ih := a377090State_snd_eq_prefixSet n
      have hstate : (a377090State (n + 1)).2 = insert (a377090 (n + 1)) (a377090State n).2 := rfl
      rw [hstate, ih]
      simp only [prefixSet, Finset.range_add_one, Finset.image_insert]

theorem a377090_not_mem_prefixSet (n : ℕ) : a377090 (n + 1) ∉ prefixSet n := by
  rw [← a377090State_snd_eq_prefixSet n]
  exact (Nat.find_spec (exists_valid_next (a377090State n).1 (a377090State n).2)).1

theorem a377090_step_prime (n : ℕ) : Nat.Prime (a377090 (n + 1) - a377090 n).natAbs :=
  (Nat.find_spec (exists_valid_next (a377090State n).1 (a377090State n).2)).2

theorem a377090_greedy_rank {n : ℕ} {z : ℤ}
    (hz_vis : z ∉ prefixSet n) (hz_prime : Nat.Prime (z - a377090 n).natAbs) :
    toRank (a377090 (n + 1)) ≤ toRank z := by
  have hspec := Nat.find_min' (exists_valid_next (a377090State n).1 (a377090State n).2)
    (m := toRank z) ⟨by simpa [ofRank_toRank, a377090State_snd_eq_prefixSet] using hz_vis,
      by simpa [ofRank_toRank, a377090] using hz_prime⟩
  simpa [a377090, a377090State, toRank_ofRank] using hspec

theorem a377090_greedy_abs {n : ℕ} {z : ℤ}
    (hz_vis : z ∉ prefixSet n) (hz_prime : Nat.Prime (z - a377090 n).natAbs) :
    (a377090 (n + 1)).natAbs ≤ z.natAbs :=
  natAbs_le_of_toRank_le (a377090_greedy_rank hz_vis hz_prime)

theorem a377090_mem_prefixSet_self (n : ℕ) : a377090 n ∈ prefixSet n :=
  Finset.mem_image_of_mem _ (Finset.mem_range.mpr (Nat.lt_succ_self n))

theorem a377090_lt_ne {i j : ℕ} (hij : i < j) : a377090 i ≠ a377090 j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  intro heq
  have hmem : a377090 i ∈ prefixSet k :=
    Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))
  rw [heq] at hmem
  exact a377090_not_mem_prefixSet k hmem

theorem a377090_injective : Function.Injective a377090 := by
  intro i j hij
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · exact absurd hij (a377090_lt_ne hlt)
  · rfl
  · exact absurd hij.symm (a377090_lt_ne hgt)

theorem a377090_succ_ne_zero (j : ℕ) : a377090 (j + 1) ≠ 0 := by
  rw [← a377090_zero]
  exact (a377090_lt_ne (Nat.zero_lt_succ j)).symm

/-- Every bounded interval of integers is visited finitely many times, so `|a(n)| → ∞`. -/
theorem a377090_abs_tendsto :
    Tendsto (fun n => (a377090 n).natAbs) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro B
  let S : Finset ℤ := Finset.Icc (-(B : ℤ)) (B : ℤ)
  let T : Finset ℕ := S.preimage a377090 (fun x _ y _ hxy => a377090_injective hxy)
  refine ⟨T.sup id + 1, fun n hn => ?_⟩
  by_contra hlt
  push Not at hlt
  have haS : a377090 n ∈ S := by
    simp only [S, Finset.mem_Icc]
    omega
  have hnT : n ∈ T := Finset.mem_preimage.mpr haS
  have hle : n ≤ T.sup id := Finset.le_sup (f := id) hnT
  omega

/-- Finite-prefix version of the omitted-point lemma: if `h ∉ prefixSet n`, then at most
`2 * |h| + 1` indices `j ≤ n` satisfy `|a(j) - h| ∈ ℙ`. -/
theorem prefix_omitted_neighbors_card_le (n : ℕ) {h : ℤ} (hh : h ∉ prefixSet n) :
    ((Finset.range (n + 1)).filter (fun j => Nat.Prime (a377090 j - h).natAbs)).card ≤
      2 * h.natAbs + 1 := by
  let F := (Finset.range (n + 1)).filter (fun j => Nat.Prime (a377090 j - h).natAbs)
  let Flt := F.filter (fun j => j < n)
  let Feq := F.filter (fun j => j = n)
  have hF_split : F.card ≤ Flt.card + Feq.card := by
    have hsub : F ⊆ Flt ∪ Feq := by
      intro j hj
      have hj_rng : j < n + 1 := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj_rng) with hlt | heq
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hj, hlt⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hj, heq⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hFeq : Feq.card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro x hx y hy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    omega
  let box : Finset ℤ := (Finset.Icc (-(h.natAbs : ℤ)) (h.natAbs : ℤ)).erase h
  have hbox_card : box.card ≤ 2 * h.natAbs := by
    have hIcc : (Finset.Icc (-(h.natAbs : ℤ)) (h.natAbs : ℤ)).card = 2 * h.natAbs + 1 := by
      rw [Int.card_Icc]
      omega
    by_cases hh_in : h ∈ Finset.Icc (-(h.natAbs : ℤ)) (h.natAbs : ℤ)
    · rw [Finset.card_erase_of_mem hh_in, hIcc]
      omega
    · exfalso
      exact hh_in (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hFlt_le : Flt.card ≤ box.card := by
    refine Finset.card_le_card_of_injOn (fun j => a377090 (j + 1)) ?_ ?_
    · intro j hj
      have hjF := (Finset.mem_filter.mp hj).1
      have hjn : j < n := (Finset.mem_filter.mp hj).2
      have hprime_jh : Nat.Prime (a377090 j - h).natAbs := (Finset.mem_filter.mp hjF).2
      have hprime_hj : Nat.Prime (h - a377090 j).natAbs := by
        rwa [show (h - a377090 j).natAbs = (a377090 j - h).natAbs by rw [← Int.natAbs_neg, neg_sub]]
      have hh_not_j : h ∉ prefixSet j := by
        intro hmem
        apply hh
        rcases Finset.mem_image.mp hmem with ⟨m, hm, rfl⟩
        have hm' : m < j + 1 := Finset.mem_range.mp hm
        exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))
      have habs : (a377090 (j + 1)).natAbs ≤ h.natAbs := a377090_greedy_abs hh_not_j hprime_hj
      have hne : a377090 (j + 1) ≠ h := by
        intro heq
        apply hh
        rw [← heq]
        exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))
      dsimp only
      refine Finset.mem_erase.mpr ⟨hne, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩ <;> omega
    · intro x _ y _ hxy
      have := a377090_injective hxy
      omega
  change F.card ≤ 2 * h.natAbs + 1
  omega

/-- **Lemma 1.1 (Omitted-Point Neighborhood Bound)**:
If `b ∉ Set.range a377090`, then any finite set `I` of indices `j` such that `|a(j) - b|`
is prime satisfies `I.card ≤ 2 * |b|` (and in fact `≤ 2 * |b| - 1` when `b ≠ 0`). -/
theorem omitted_neighbors_card_le {b : ℤ} (hb : b ∉ Set.range a377090) (I : Finset ℕ)
    (hI : ∀ j ∈ I, Nat.Prime (a377090 j - b).natAbs) : I.card ≤ 2 * b.natAbs := by
  let box : Finset ℤ := (Finset.Icc (-(b.natAbs : ℤ)) (b.natAbs : ℤ)).erase b
  have hbox_card : box.card ≤ 2 * b.natAbs := by
    have hIcc : (Finset.Icc (-(b.natAbs : ℤ)) (b.natAbs : ℤ)).card = 2 * b.natAbs + 1 := by
      rw [Int.card_Icc]
      omega
    by_cases hb_in : b ∈ Finset.Icc (-(b.natAbs : ℤ)) (b.natAbs : ℤ)
    · rw [Finset.card_erase_of_mem hb_in, hIcc]
      omega
    · simp only [Finset.mem_Icc] at hb_in
      omega
  refine (Finset.card_le_card_of_injOn (fun j => a377090 (j + 1)) ?_ ?_).trans hbox_card
  · intro j hj
    have hprime : Nat.Prime (b - a377090 j).natAbs := by
      have hj' := hI j hj
      rwa [show (b - a377090 j).natAbs = (a377090 j - b).natAbs by rw [← Int.natAbs_neg, neg_sub]]
    have hb_not_j : b ∉ prefixSet j := fun hmem =>
      let ⟨m, _, hm⟩ := Finset.mem_image.mp hmem
      hb ⟨m, hm⟩
    have habs : (a377090 (j + 1)).natAbs ≤ b.natAbs := a377090_greedy_abs hb_not_j hprime
    have hne : a377090 (j + 1) ≠ b := fun heq => hb ⟨j + 1, heq⟩
    dsimp only
    refine Finset.mem_erase.mpr ⟨hne, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩ <;> omega
  · intro x _ y _ hxy
    have := a377090_injective hxy
    omega

/-- Sharpened omitted-point bound `2 * |b| - 1` (since `a(0) = 0` cannot be a successor). -/
theorem omitted_neighbors_card_le_sub_one {b : ℤ} (hb : b ∉ Set.range a377090) (I : Finset ℕ)
    (hI : ∀ j ∈ I, Nat.Prime (a377090 j - b).natAbs) : I.card ≤ 2 * b.natAbs - 1 := by
  have hb_ne : b ≠ 0 := by
    rintro rfl
    exact hb ⟨0, a377090_zero⟩
  let box : Finset ℤ := ((Finset.Icc (-(b.natAbs : ℤ)) (b.natAbs : ℤ)).erase b).erase 0
  have hb_in : b ∈ Finset.Icc (-(b.natAbs : ℤ)) (b.natAbs : ℤ) := by
    simp only [Finset.mem_Icc]
    omega
  have h0_in : (0 : ℤ) ∈ (Finset.Icc (-(b.natAbs : ℤ)) (b.natAbs : ℤ)).erase b := by
    refine Finset.mem_erase.mpr ⟨hb_ne.symm, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩ <;> omega
  have hbox_card : box.card = 2 * b.natAbs - 1 := by
    have hIcc : (Finset.Icc (-(b.natAbs : ℤ)) (b.natAbs : ℤ)).card = 2 * b.natAbs + 1 := by
      rw [Int.card_Icc]
      omega
    rw [Finset.card_erase_of_mem h0_in, Finset.card_erase_of_mem hb_in, hIcc]
    omega
  rw [← hbox_card]
  refine Finset.card_le_card_of_injOn (fun j => a377090 (j + 1)) ?_ ?_
  · intro j hj
    have hprime : Nat.Prime (b - a377090 j).natAbs := by
      have hj' := hI j hj
      rwa [show (b - a377090 j).natAbs = (a377090 j - b).natAbs by rw [← Int.natAbs_neg, neg_sub]]
    have hb_not_j : b ∉ prefixSet j := fun hmem =>
      let ⟨m, _, hm⟩ := Finset.mem_image.mp hmem
      hb ⟨m, hm⟩
    have habs : (a377090 (j + 1)).natAbs ≤ b.natAbs := a377090_greedy_abs hb_not_j hprime
    have hne : a377090 (j + 1) ≠ b := fun heq => hb ⟨j + 1, heq⟩
    dsimp only
    refine Finset.mem_erase.mpr ⟨a377090_succ_ne_zero j,
      Finset.mem_erase.mpr ⟨hne, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩⟩ <;> omega
  · intro x _ y _ hxy
    have := a377090_injective hxy
    omega

/-- Only finitely many primes `p` can satisfy `b + p ∈ range a377090` or `b - p ∈ range a377090`
when `b ∉ range a377090`. -/
theorem exists_large_prime_add_sub_omitted {b : ℤ} (hb : b ∉ Set.range a377090) :
    ∃ P₀ : ℕ, ∀ p : ℕ, Nat.Prime p → P₀ ≤ p →
      b + (p : ℤ) ∉ Set.range a377090 ∧ b - (p : ℤ) ∉ Set.range a377090 := by
  classical
  have hfin : {j : ℕ | Nat.Prime (a377090 j - b).natAbs}.Finite := by
    by_contra hinf
    obtain ⟨I, hI_sub, hI_card⟩ := Set.Infinite.exists_subset_card_eq hinf (2 * b.natAbs + 1)
    have hle := omitted_neighbors_card_le hb I (fun j hj => hI_sub hj)
    omega
  let F : Finset ℕ := hfin.toFinset
  refine ⟨F.sup (fun j => (a377090 j - b).natAbs) + 1, fun p hp hpP₀ => ⟨?_, ?_⟩⟩
  · rintro ⟨j, hj⟩
    have hmem : j ∈ F := by
      rw [Set.Finite.mem_toFinset]
      change Nat.Prime (a377090 j - b).natAbs
      rw [hj]
      simpa using hp
    have hle : (a377090 j - b).natAbs ≤ F.sup (fun j => (a377090 j - b).natAbs) :=
      Finset.le_sup (f := fun j => (a377090 j - b).natAbs) hmem
    rw [hj] at hle
    simp only [add_sub_cancel_left, Int.natAbs_natCast] at hle
    omega
  · rintro ⟨j, hj⟩
    have hmem : j ∈ F := by
      rw [Set.Finite.mem_toFinset]
      change Nat.Prime (a377090 j - b).natAbs
      rw [hj]
      have hsub : (b - (p : ℤ) - b).natAbs = p := by
        have : b - (p : ℤ) - b = -(p : ℤ) := by ring
        rw [this, Int.natAbs_neg, Int.natAbs_natCast]
      rwa [hsub]
    have hle : (a377090 j - b).natAbs ≤ F.sup (fun j => (a377090 j - b).natAbs) :=
      Finset.le_sup (f := fun j => (a377090 j - b).natAbs) hmem
    rw [hj] at hle
    have hsub : (b - (p : ℤ) - b).natAbs = p := by
      have : b - (p : ℤ) - b = -(p : ℤ) := by ring
      rw [this, Int.natAbs_neg, Int.natAbs_natCast]
    rw [hsub] at hle
    omega

end

end A377090
