import Mathlib
import Submission.Work.GM.Energy.Defs

/-!
# Vocabulary for GM Lemma 11.6 (discrete fourth moment)

GM Lemma 11.6 bounds `Σ_{n₁,n₂∼M} |R(n₁/n₂)|⁴`.  The proof splits the pairs
`(t₁,t₂) ∈ W²` according to the number of representations of the integer
`u = ⌊t₁-t₂⌋`, applies the locality lemma (GM Lemma 11.3) to replace the
supremum over a unit window by an integral, and then applies Heath-Brown's theorem
to the `1`-separated set of integers `u₁-u₂`.

This file contains the vocabulary: the pair set `W²`, the key `⌊t₁-t₂⌋`, the
representation count `c u`, the dyadic classes `clsSet W j`, the Dirichlet sum
`Gsum M τ = Σ_{n∈[M,2M]} n^{iτ}` and the partial `R`-sum `Zclass`.

Everything here is sorry-free.
-/

namespace Work.GM.Energy.EnergyCore

open Complex Finset
open scoped BigOperators
set_option autoImplicit false

/-- The set of pairs from `W`: `W²`. -/
noncomputable def pairSet (W : Finset ℝ) : Finset (ℝ × ℝ) := W ×ˢ W

/-- The integer `⌊t₁-t₂⌋` attached to a pair `(t₁,t₂)`. -/
noncomputable def pkey (p : ℝ × ℝ) : ℤ := ⌊p.1 - p.2⌋

/-- The set of keys `⌊t₁-t₂⌋` occurring among the pairs. -/
noncomputable def keySet (W : Finset ℝ) : Finset ℤ := (pairSet W).image pkey

/-- The pairs with a prescribed key. -/
noncomputable def repPairs (W : Finset ℝ) (u : ℤ) : Finset (ℝ × ℝ) :=
  (pairSet W).filter (fun p => pkey p = u)

/-- `c u = #{(t₁,t₂) ∈ W² : ⌊t₁-t₂⌋ = u}`, the number of representations of `u`. -/
noncomputable def repCount (W : Finset ℝ) (u : ℤ) : ℕ := (repPairs W u).card

/-- The dyadic class of a key: `⌊log₂ c(u)⌋` (`Nat.log 2`). -/
noncomputable def clsIdx (W : Finset ℝ) (u : ℤ) : ℕ := Nat.log 2 (repCount W u)

/-- Number of dyadic classes needed: `⌊log₂ |W|²⌋ + 1`. -/
noncomputable def clsNum (W : Finset ℝ) : ℕ := Nat.log 2 (W.card * W.card) + 1

/-- The keys in dyadic class `j` (GM's `U_B` with `B = 2^j`). -/
noncomputable def clsSet (W : Finset ℝ) (j : ℕ) : Finset ℤ :=
  (keySet W).filter (fun u => clsIdx W u = j)

/-- The quadruple set whose cardinality is GM's additive energy `E(W)`. -/
noncomputable def quadSet (W : Finset ℝ) : Finset (ℝ × ℝ × ℝ × ℝ) :=
  (W ×ˢ W ×ˢ W ×ˢ W).filter (fun q : ℝ × ℝ × ℝ × ℝ => |q.1 + q.2.1 - q.2.2.1 - q.2.2.2| ≤ 1)

lemma quadSet_card (W : Finset ℝ) : (quadSet W).card = Submission.GM.energy W := rfl

/-- The Dirichlet sum `G(τ) = Σ_{n ∈ [M,2M]} n^{iτ}`. -/
noncomputable def Gsum (M : ℕ) (τ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc M (2 * M), (n : ℂ) ^ (Complex.I * (τ : ℂ))

/-- The partial `R`-sum over a set `U` of keys:
`Σ_{u∈U} Σ_{p ∈ W², ⌊p.1-p.2⌋ = u} x^{i(p.1-p.2)}`. -/
noncomputable def Zclass (W : Finset ℝ) (U : Finset ℤ) (x : ℝ) : ℂ :=
  ∑ u ∈ U, ∑ p ∈ repPairs W u, (x : ℂ) ^ (Complex.I * (((p.1 - p.2 : ℝ)) : ℂ))

section Basic

variable {W : Finset ℝ}

lemma pairSet_card : (pairSet W).card = W.card * W.card := Finset.card_product W W

lemma mem_pairSet {p : ℝ × ℝ} : p ∈ pairSet W ↔ p.1 ∈ W ∧ p.2 ∈ W := Finset.mem_product

lemma pkey_mem_keySet {p : ℝ × ℝ} (hp : p ∈ pairSet W) : pkey p ∈ keySet W :=
  Finset.mem_image_of_mem _ hp

lemma mem_keySet {u : ℤ} : u ∈ keySet W ↔ ∃ p ∈ pairSet W, pkey p = u := Finset.mem_image

lemma mem_repPairs {u : ℤ} {p : ℝ × ℝ} : p ∈ repPairs W u ↔ p ∈ pairSet W ∧ pkey p = u := by
  simp only [repPairs, Finset.mem_filter]

lemma repPairs_subset (u : ℤ) : repPairs W u ⊆ pairSet W := Finset.filter_subset _ _

lemma repCount_le (u : ℤ) : repCount W u ≤ W.card * W.card := by
  rw [repCount, ← pairSet_card]
  exact Finset.card_le_card (repPairs_subset u)

lemma repCount_pos_of_mem {u : ℤ} (hu : u ∈ keySet W) : 0 < repCount W u := by
  rw [mem_keySet] at hu
  obtain ⟨p, hp, hpu⟩ := hu
  rw [repCount]
  exact Finset.card_pos.mpr ⟨p, by rw [mem_repPairs]; exact ⟨hp, hpu⟩⟩

/-- The pairs of `W²` are partitioned by the value of `⌊t₁-t₂⌋`. -/
lemma sum_keySet {α : Type*} [AddCommMonoid α] (F : ℝ × ℝ → α) :
    (∑ u ∈ keySet W, ∑ p ∈ repPairs W u, F p) = ∑ p ∈ pairSet W, F p := by
  have h := Finset.sum_fiberwise_of_maps_to (s := pairSet W) (t := (pairSet W).image pkey)
    (g := pkey) (fun p hp => Finset.mem_image_of_mem _ hp) F
  simpa [keySet, repPairs] using h

lemma clsIdx_lt_of_mem {u : ℤ} (hu : u ∈ keySet W) : clsIdx W u < clsNum W := by
  have h : Nat.log 2 (repCount W u) ≤ Nat.log 2 (W.card * W.card) :=
    Nat.log_mono_right (repCount_le u)
  rw [clsIdx, clsNum]
  omega

/-- The keys are partitioned by their dyadic class. -/
lemma sum_clsSet {α : Type*} [AddCommMonoid α] (F : ℤ → α) :
    (∑ j ∈ Finset.range (clsNum W), ∑ u ∈ clsSet W j, F u) = ∑ u ∈ keySet W, F u := by
  have h := Finset.sum_fiberwise_of_maps_to (s := keySet W) (t := Finset.range (clsNum W))
    (g := clsIdx W) (fun u hu => Finset.mem_range.mpr (clsIdx_lt_of_mem hu)) F
  simpa [clsSet] using h

lemma clsSet_subset (j : ℕ) : clsSet W j ⊆ keySet W := Finset.filter_subset _ _

lemma mem_clsSet {j : ℕ} {u : ℤ} : u ∈ clsSet W j ↔ u ∈ keySet W ∧ clsIdx W u = j := by
  simp only [clsSet, Finset.mem_filter]

lemma clsSet_pow_le {j : ℕ} {u : ℤ} (hu : u ∈ clsSet W j) : 2 ^ j ≤ repCount W u := by
  rw [mem_clsSet] at hu
  have hpos : repCount W u ≠ 0 := (repCount_pos_of_mem hu.1).ne'
  have h : j ≤ Nat.log 2 (repCount W u) := by rw [← hu.2]; exact le_rfl
  exact Nat.pow_le_of_le_log hpos h

lemma clsSet_lt_pow {j : ℕ} {u : ℤ} (hu : u ∈ clsSet W j) : repCount W u < 2 ^ (j + 1) := by
  rw [mem_clsSet] at hu
  have hpos : repCount W u ≠ 0 := (repCount_pos_of_mem hu.1).ne'
  have h2 : Nat.log 2 (repCount W u) = j := hu.2
  have h : Nat.log 2 (repCount W u) < j + 1 := by omega
  exact (Nat.log_lt_iff_lt_pow (by norm_num) hpos).mp h

/-- Each pair is counted once by the representation counts. -/
lemma sum_repCount : (∑ u ∈ keySet W, repCount W u) = W.card * W.card := by
  have h : (∑ u ∈ keySet W, repCount W u) = ∑ _p ∈ pairSet W, (1 : ℕ) := by
    rw [← sum_keySet (W := W) (fun _ => (1 : ℕ))]
    exact Finset.sum_congr rfl fun u _ => by
      rw [repCount, Finset.card_eq_sum_ones]
  rw [h, Finset.sum_const, smul_eq_mul, mul_one, pairSet_card]

/-- The dyadic classes have total "mass" `|W|²`. -/
lemma sum_clsSet_pow_mul_card :
    (∑ j ∈ Finset.range (clsNum W), 2 ^ j * (clsSet W j).card) ≤ W.card * W.card := by
  have h1 : ∀ j ∈ Finset.range (clsNum W),
      2 ^ j * (clsSet W j).card ≤ ∑ u ∈ clsSet W j, repCount W u := by
    intro j _
    rw [Finset.card_eq_sum_ones, Finset.mul_sum]
    exact Finset.sum_le_sum fun u hu => by
      simpa using clsSet_pow_le hu
  calc (∑ j ∈ Finset.range (clsNum W), 2 ^ j * (clsSet W j).card)
      ≤ ∑ j ∈ Finset.range (clsNum W), ∑ u ∈ clsSet W j, repCount W u :=
        Finset.sum_le_sum h1
    _ = ∑ u ∈ keySet W, repCount W u := sum_clsSet _
    _ = W.card * W.card := sum_repCount

/-- Within one dyadic class, `(2^j)²·#U_j` is at most `Σ_{u∈U_j} c(u)²`. -/
lemma clsSet_sq_mul_card_le (j : ℕ) :
    (2 ^ j) ^ 2 * (clsSet W j).card ≤ ∑ u ∈ clsSet W j, (repCount W u) ^ 2 := by
  have h : (2 ^ j) ^ 2 * (clsSet W j).card = ∑ _u ∈ clsSet W j, (2 ^ j) ^ 2 := by
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  rw [h]
  exact Finset.sum_le_sum fun u hu => Nat.pow_le_pow_left (clsSet_pow_le hu) 2

lemma keySet_card_le : (keySet W).card ≤ W.card * W.card := by
  rw [keySet, ← pairSet_card]; exact Finset.card_image_le

lemma clsSet_card_le (j : ℕ) : (clsSet W j).card ≤ W.card * W.card :=
  (Finset.card_le_card (clsSet_subset j)).trans keySet_card_le

/-- If `⌊a⌋ = u` then the residual `a - u` lies in `[0,1)`. -/
lemma floor_residual_bounds {a : ℝ} {u : ℤ} (h : ⌊a⌋ = u) :
    0 ≤ a - (u : ℝ) ∧ a - (u : ℝ) < 1 := by
  have h1 : ((u : ℤ) : ℝ) ≤ a := by rw [← h]; exact Int.floor_le a
  have h2 : a < ((u : ℤ) : ℝ) + 1 := by rw [← h]; exact Int.lt_floor_add_one a
  constructor <;> linarith

private lemma abs_sub_lt_one_of_floor_eq {x y : ℝ} (h : ⌊x⌋ = ⌊y⌋) : |x - y| < 1 := by
  rw [abs_lt]
  constructor
  · have hle : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
    have hlt : y < (⌊y⌋ : ℝ) + 1 := Int.lt_floor_add_one y
    rw [← h] at hlt
    linarith
  · have hle : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
    have hlt : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
    rw [h] at hlt
    linarith

/-- The number of pairs of pairs of `W²` with equal key is at most the additive energy `E(W)`. -/
lemma sum_repCount_sq_le_energy (W : Finset ℝ) :
    (∑ u ∈ keySet W, (repCount W u) ^ 2) ≤ Submission.GM.energy W := by
  classical
  set T : Finset ((ℝ × ℝ) × (ℝ × ℝ)) :=
    ((pairSet W) ×ˢ (pairSet W)).filter (fun z => pkey z.1 = pkey z.2) with hT
  have hcard : (∑ u ∈ keySet W, (repCount W u) ^ 2) = T.card := by
    have step1 : (∑ u ∈ keySet W, (repCount W u) ^ 2)
        = ∑ u ∈ keySet W, ∑ p ∈ repPairs W u, repCount W u := by
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.sum_const, smul_eq_mul]
      simp [repCount, sq, mul_comm]
    have step2a : (∑ u ∈ keySet W, ∑ p ∈ repPairs W u, repCount W u)
        = ∑ u ∈ keySet W, ∑ p ∈ repPairs W u, repCount W (pkey p) := by
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun p hp => ?_
      rw [(mem_repPairs.mp hp).2]
    have step2b : (∑ u ∈ keySet W, ∑ p ∈ repPairs W u, repCount W (pkey p))
        = ∑ p ∈ pairSet W, repCount W (pkey p) := sum_keySet _
    have step3 : (∑ p ∈ pairSet W, repCount W (pkey p)) = T.card := by
      rw [hT, Finset.card_filter, Finset.sum_product]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← Finset.card_filter]
      simp only [repCount, repPairs]
      congr 1
      ext q
      simp only [Finset.mem_filter]
      constructor <;> (intro h; exact ⟨h.1, h.2.symm⟩)
    rw [step1, step2a, step2b, step3]
  rw [hcard, ← quadSet_card W]
  refine Finset.card_le_card_of_injOn (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
    (z.1.1, z.2.2, z.2.1, z.1.2)) ?_ ?_
  · intro z hz
    have hzT : z ∈ T := by simpa using hz
    rw [hT, Finset.mem_filter, Finset.mem_product] at hzT
    obtain ⟨⟨hp, hq⟩, hkeq⟩ := hzT
    rw [mem_pairSet] at hp hq
    show (z.1.1, z.2.2, z.2.1, z.1.2) ∈ quadSet W
    simp only [quadSet, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hp.1, hq.2, hq.1, hp.2⟩, ?_⟩
    have hlt := abs_sub_lt_one_of_floor_eq hkeq
    rw [show (z.1.1 - z.1.2) - (z.2.1 - z.2.2)
        = z.1.1 + z.2.2 - z.2.1 - z.1.2 by ring] at hlt
    linarith
  · intro z hz z' hz' h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    obtain ⟨p, q⟩ := z
    obtain ⟨p', q'⟩ := z'
    obtain ⟨p1, p2⟩ := p
    obtain ⟨q1, q2⟩ := q
    obtain ⟨p1', p2'⟩ := p'
    obtain ⟨q1', q2'⟩ := q'
    simp only [Prod.mk.injEq] at h1 h2 h3 h4 ⊢
    exact ⟨by simp_all, by simp_all⟩

end Basic

end Work.GM.Energy.EnergyCore
