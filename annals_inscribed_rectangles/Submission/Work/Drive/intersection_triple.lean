import Mathlib
import Submission.Work.Drive.boxParity
import Submission.Work.Drive.intersection_bordism
import Submission.Work.Drive.cofactor_restrict_surjective

/-!
# The triple-intersection Leibniz rule in `ℝ⁴`

`Submission/Work/Drive/intersection_parity.lean` proves the Leibniz rule for the mod-2 pairing of a
2-chain with a 3-chain in `ℝ⁴` — the parity bookkeeping of Hugelmeyer's Lemma 2 (the two-plane
comparison, whose class is `ω_P ∪ α`).  This file proves the corresponding rule for **three**
3-chains, which is the parity bookkeeping of Hugelmeyer's Lemmas 3 and 4 (the class
`ω_P ∪ ω_Q ∪ ω_R`):

> the intersection of three 3-chains `V₀, V₁, V₂ : ℝ³ → ℝ⁴` is (generically) a compact 1-manifold
> whose boundary is the disjoint union of the three "one chain's boundary against the other two"
> intersections; hence the sum of the three corresponding counts is even.

Concretely, `tripleDiff V : ℝ⁹ → ℝ⁸` sends `x = (x₀, x₁, x₂) ∈ [0,1]³ × [0,1]³ × [0,1]³` to
`(V₀x₀ − V₁x₁, V₀x₀ − V₂x₂)`, whose zeros are the points where all three chains meet; the zeros on
the boundary of the nine-box split, according to which of the three blocks of coordinates is on a
face, into the three counts

* `blockMeet V 0` = `#(∂V₀ ⋔ V₁ ⋔ V₂)`,
* `blockMeet V 1` = `#(V₀ ⋔ ∂V₁ ⋔ V₂)`,
* `blockMeet V 2` = `#(V₀ ⋔ V₁ ⋔ ∂V₂)`,

whose sum is even.  This is exactly the "`n_P + n_Q + n_R` even at the tube boundaries" bookkeeping of
Hugelmeyer's Lemma 3 (the remaining two counts `n_λ`, `n_{−λ}` being attached to the ends of the
capped manifold, where the same argument applies with `∂V_i` replaced by its end part).

The engine is again `Work.Drive.boxParity` (`Submission.Drive.ParityProp`), this time for `m = 8`.
-/

namespace Work.Drive

open Submission.Drive
open scoped Manifold ContDiff Topology

noncomputable section

/-! ## The nine-box as three cubes -/

/-- The `j`-th coordinate of the `k`-th block of the nine-box: the coordinates `0,1,2` for `k = 0`,
`3,4,5` for `k = 1` and `6,7,8` for `k = 2`. -/
def bIdx (k : Fin 3) (j : Fin 3) : Fin 9 := ⟨j.val + 3 * k.val, by omega⟩

lemma bIdx_val (k : Fin 3) (j : Fin 3) : (bIdx k j).val = j.val + 3 * k.val := rfl

@[simp] lemma bIdx_zero_val (j : Fin 3) : (bIdx 0 j).val = j.val := rfl

@[simp] lemma bIdx_one_val (j : Fin 3) : (bIdx 1 j).val = j.val + 3 := rfl

@[simp] lemma bIdx_two_val (j : Fin 3) : (bIdx 2 j).val = j.val + 6 := rfl

lemma bIdx_injective (k : Fin 3) : Function.Injective (bIdx k) := by
  intro j j' h
  have h' := congrArg Fin.val h
  rw [bIdx_val, bIdx_val] at h'
  exact Fin.ext (by omega)

lemma bIdx_disjoint {k k' : Fin 3} (h : k ≠ k') (j j' : Fin 3) :
    bIdx k j ≠ bIdx k' j' := by
  intro hh
  have h' := congrArg Fin.val hh
  rw [bIdx_val, bIdx_val] at h'
  exact h (Fin.ext (by omega))

lemma bIdx_eq_of_val_eq {k k' : Fin 3} (h : k.val = k'.val) (j : Fin 3) :
    bIdx k j = bIdx k' j := by
  ext
  rw [bIdx_val, bIdx_val, h]

/-- **Splitting the nine-box into three blocks.**  Every coordinate lies in one of the three cubes. -/
lemma exists_fin_nine_iff (P : Fin 9 → Prop) :
    (∃ i, P i) ↔ (∃ j : Fin 3, P (bIdx 0 j)) ∨ (∃ j : Fin 3, P (bIdx 1 j))
      ∨ (∃ j : Fin 3, P (bIdx 2 j)) := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨k, j, hk⟩ : ∃ (k : Fin 3) (j : Fin 3), bIdx k j = i :=
      ⟨⟨i.val / 3, by omega⟩, ⟨i.val % 3, by omega⟩,
        by ext; rw [bIdx_val, Nat.mod_add_div]⟩
    rcases (show k.val = 0 ∨ k.val = 1 ∨ k.val = 2 by omega) with hk0 | hk1 | hk2
    · refine Or.inl ⟨j, ?_⟩
      rw [← bIdx_eq_of_val_eq (k := k) (k' := 0) hk0 j, hk]
      exact hi
    · refine Or.inr (Or.inl ⟨j, ?_⟩)
      rw [← bIdx_eq_of_val_eq (k := k) (k' := 1) hk1 j, hk]
      exact hi
    · refine Or.inr (Or.inr ⟨j, ?_⟩)
      rw [← bIdx_eq_of_val_eq (k := k) (k' := 2) hk2 j, hk]
      exact hi
  · rintro (⟨j, hj⟩ | ⟨j, hj⟩ | ⟨j, hj⟩)
    · exact ⟨bIdx 0 j, hj⟩
    · exact ⟨bIdx 1 j, hj⟩
    · exact ⟨bIdx 2 j, hj⟩

/-- The projection of the nine-box onto its `k`-th block. -/
def bPart (k : Fin 3) (x : EuclideanSpace ℝ (Fin 9)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 fun j => x (bIdx k j)

@[simp] lemma bPart_apply (k : Fin 3) (x : EuclideanSpace ℝ (Fin 9)) (j : Fin 3) :
    bPart k x j = x (bIdx k j) := rfl

/-- The `k`-th block of coordinates is on a face of the nine-box. -/
def onBlockFace (k : Fin 3) (x : EuclideanSpace ℝ (Fin 9)) : Prop :=
  ∃ j : Fin 3, x (bIdx k j) = 0 ∨ x (bIdx k j) = 1

lemma mem_unitBox_nine_iff (x : EuclideanSpace ℝ (Fin 9)) :
    x ∈ unitBox 8 ↔ bPart 0 x ∈ unitBox 2 ∧ bPart 1 x ∈ unitBox 2 ∧ bPart 2 x ∈ unitBox 2 := by
  constructor
  · intro h
    exact ⟨fun j => h (bIdx 0 j), fun j => h (bIdx 1 j), fun j => h (bIdx 2 j)⟩
  · rintro ⟨h0, h1, h2⟩ i
    obtain ⟨k, j, hk⟩ : ∃ (k : Fin 3) (j : Fin 3), bIdx k j = i :=
      ⟨⟨i.val / 3, by omega⟩, ⟨i.val % 3, by omega⟩,
        by ext; rw [bIdx_val, Nat.mod_add_div]⟩
    rw [← hk]
    rcases (show k.val = 0 ∨ k.val = 1 ∨ k.val = 2 by omega) with hk0 | hk1 | hk2
    · rw [bIdx_eq_of_val_eq (k := k) (k' := 0) hk0 j]; exact h0 j
    · rw [bIdx_eq_of_val_eq (k := k) (k' := 1) hk1 j]; exact h1 j
    · rw [bIdx_eq_of_val_eq (k := k) (k' := 2) hk2 j]; exact h2 j

lemma mem_unitBoxBdry_nine_iff (x : EuclideanSpace ℝ (Fin 9)) :
    x ∈ unitBoxBdry 8 ↔ x ∈ unitBox 8 ∧ (onBlockFace 0 x ∨ onBlockFace 1 x ∨ onBlockFace 2 x) := by
  constructor
  · rintro ⟨hbox, i, hi⟩
    refine ⟨hbox, ?_⟩
    rcases (exists_fin_nine_iff (fun i => x i = 0 ∨ x i = 1)).mp ⟨i, hi⟩ with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro ⟨hbox, h | h | h⟩
    · obtain ⟨j, hj⟩ := h
      exact ⟨hbox, bIdx 0 j, hj⟩
    · obtain ⟨j, hj⟩ := h
      exact ⟨hbox, bIdx 1 j, hj⟩
    · obtain ⟨j, hj⟩ := h
      exact ⟨hbox, bIdx 2 j, hj⟩

/-! ## The difference map of three 3-chains -/

/-- Two vectors of `ℝ⁴` stacked into a vector of `ℝ⁸`. -/
def pairUp (a b : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 8) :=
  WithLp.toLp 2 fun k : Fin 8 =>
    if h : k.val < 4 then a ⟨k.val, h⟩ else b ⟨k.val - 4, by omega⟩

@[simp] lemma pairUp_apply_fst (a b : EuclideanSpace ℝ (Fin 4)) (k : Fin 4) :
    pairUp a b (Fin.castAdd 4 k) = a k := by
  simp only [pairUp, WithLp.ofLp_toLp]
  rw [dif_pos (by simp)]
  exact congrArg a (Fin.ext (by simp))

@[simp] lemma pairUp_apply_snd (a b : EuclideanSpace ℝ (Fin 4)) (k : Fin 4) :
    pairUp a b (Fin.natAdd 4 k) = b k := by
  simp only [pairUp, WithLp.ofLp_toLp]
  rw [dif_neg (by simp)]
  exact congrArg b (Fin.ext (by simp))

/-- **The difference map of three 3-chains.**  Its zeros in `[0,1]³ × [0,1]³ × [0,1]³` are the
common intersection points of the three chains. -/
def tripleDiff (V : Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 8) :=
  fun x => pairUp (V 0 (bPart 0 x) - V 1 (bPart 1 x)) (V 0 (bPart 0 x) - V 2 (bPart 2 x))

/-- The zeros of the triple difference map whose `k`-th block of coordinates is on a face of the
box: the intersection of the boundary 2-chain of `V k` with the other two chains. -/
def blockMeet (V : Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4)) (k : Fin 3) :
    Set (EuclideanSpace ℝ (Fin 9)) :=
  {x | x ∈ unitBox 8 ∧ onBlockFace k x ∧ tripleDiff V x = 0}

/-- **The boundary of the triple intersection.**  The zeros of `tripleDiff V` on the boundary of the
nine-box are exactly the union of the three block intersections. -/
theorem bdyZeros_tripleDiff_eq (V : Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4)) :
    bdyZeros (tripleDiff V) = blockMeet V 0 ∪ blockMeet V 1 ∪ blockMeet V 2 := by
  ext x
  simp only [bdyZeros, blockMeet, Set.mem_ofPred_eq, Set.mem_union]
  rw [mem_unitBoxBdry_nine_iff x]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨hbox, hf⟩ := h1
    rcases hf with h | h | h
    · exact Or.inl (Or.inl ⟨hbox, h, h2⟩)
    · exact Or.inl (Or.inr ⟨hbox, h, h2⟩)
    · exact Or.inr ⟨hbox, h, h2⟩
  · rintro ((⟨hbox, h, h2⟩ | ⟨hbox, h, h2⟩) | ⟨hbox, h, h2⟩)
    · exact ⟨⟨hbox, Or.inl h⟩, h2⟩
    · exact ⟨⟨hbox, Or.inr (Or.inl h)⟩, h2⟩
    · exact ⟨⟨hbox, Or.inr (Or.inr h)⟩, h2⟩

/-! ## The parity of the boundary -/

/-- **The triple-intersection Leibniz rule.**  Let `V₀, V₁, V₂` be 3-chains in `ℝ⁴` (modelled on the
unit cube), meeting transversally in the sense of the three hypotheses of
`Submission.Drive.ParityProp` for `tripleDiff V`.  Then the number of points in which the boundary
2-chain of one chain meets the other two — summed over the three chains — is even: it is the number
of boundary points of the compact 1-manifold `V₀ ⋔ V₁ ⋔ V₂`. -/
theorem even_ncard_blockMeet_sum
    (V : Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (tripleDiff V))
    (hreg : ∀ x ∈ unitBox 8, tripleDiff V x = 0 →
      Function.Surjective (fderiv ℝ (tripleDiff V) x))
    (hface : ∀ x ∈ unitBoxBdry 8, tripleDiff V x = 0 → ∃ i : Fin (8 + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
      Function.Surjective (fun v : {v : Amb 8 // v i = 0} =>
        fderiv ℝ (tripleDiff V) x v.1)) :
    Even ((blockMeet V 0).ncard + (blockMeet V 1).ncard + (blockMeet V 2).ncard) := by
  obtain ⟨hfin, heven⟩ := boxParity 8 (tripleDiff V) hF hreg hface
  have hfin' : (bdyZeros (tripleDiff V)).Finite := hfin
  have heven' : Even (bdyZeros (tripleDiff V)).ncard := heven
  rw [bdyZeros_tripleDiff_eq] at hfin' heven'
  -- the three blocks are pairwise disjoint, by the "exactly one face" hypothesis
  have huniq : ∀ x ∈ unitBoxBdry 8, tripleDiff V x = 0 → ∃ i : Fin (8 + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) :=
    fun x hx h0 => (hface x hx h0).imp fun _ h => ⟨h.1, h.2.1⟩
  have key : ∀ {x : EuclideanSpace ℝ (Fin 9)} {i i' : Fin 9},
      (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) → (x i' = 0 ∨ x i' = 1) → i' = i := by
    intro y i i' hother hi'
    by_contra hne
    have hmem := hother i' hne
    rcases hi' with h | h
    · rw [h] at hmem; exact absurd hmem.1 (by norm_num)
    · rw [h] at hmem; exact absurd hmem.2 (by norm_num)
  have h01 : Disjoint (blockMeet V 0) (blockMeet V 1) := by
    rw [Set.disjoint_left]
    rintro x ⟨hxbox, hx0, hxF⟩ ⟨-, hx1, -⟩
    have hxbdy : x ∈ unitBoxBdry 8 :=
      (mem_unitBoxBdry_nine_iff x).mpr ⟨hxbox, Or.inl hx0⟩
    obtain ⟨i, hi, hother⟩ := huniq x hxbdy hxF
    obtain ⟨j, hj⟩ := hx0
    obtain ⟨j', hj'⟩ := hx1
    have h1 : bIdx 0 j = i := key hother hj
    have h2 : bIdx 1 j' = i := key hother hj'
    refine bIdx_disjoint (k := 0) (k' := 1) (by decide) j j' ?_
    rw [h1, h2]
  have h02 : Disjoint (blockMeet V 0) (blockMeet V 2) := by
    rw [Set.disjoint_left]
    rintro x ⟨hxbox, hx0, hxF⟩ ⟨-, hx2, -⟩
    have hxbdy : x ∈ unitBoxBdry 8 :=
      (mem_unitBoxBdry_nine_iff x).mpr ⟨hxbox, Or.inl hx0⟩
    obtain ⟨i, hi, hother⟩ := huniq x hxbdy hxF
    obtain ⟨j, hj⟩ := hx0
    obtain ⟨j', hj'⟩ := hx2
    have h1 : bIdx 0 j = i := key hother hj
    have h2 : bIdx 2 j' = i := key hother hj'
    refine bIdx_disjoint (k := 0) (k' := 2) (by decide) j j' ?_
    rw [h1, h2]
  have h12 : Disjoint (blockMeet V 1) (blockMeet V 2) := by
    rw [Set.disjoint_left]
    rintro x ⟨hxbox, hx1, hxF⟩ ⟨-, hx2, -⟩
    have hxbdy : x ∈ unitBoxBdry 8 :=
      (mem_unitBoxBdry_nine_iff x).mpr ⟨hxbox, Or.inr (Or.inl hx1)⟩
    obtain ⟨i, hi, hother⟩ := huniq x hxbdy hxF
    obtain ⟨j, hj⟩ := hx1
    obtain ⟨j', hj'⟩ := hx2
    have h1 : bIdx 1 j = i := key hother hj
    have h2 : bIdx 2 j' = i := key hother hj'
    refine bIdx_disjoint (k := 1) (k' := 2) (by decide) j j' ?_
    rw [h1, h2]
  have hf0 : (blockMeet V 0).Finite :=
    hfin'.subset (fun x hx => by simp only [Set.mem_union]; exact Or.inl (Or.inl hx))
  have hf1 : (blockMeet V 1).Finite :=
    hfin'.subset (fun x hx => by simp only [Set.mem_union]; exact Or.inl (Or.inr hx))
  have hf2 : (blockMeet V 2).Finite :=
    hfin'.subset (fun x hx => by simp only [Set.mem_union]; exact Or.inr hx)
  have hdisj : Disjoint (blockMeet V 0 ∪ blockMeet V 1) (blockMeet V 2) := by
    rw [Set.disjoint_left]
    rintro x (hx | hx) hy
    · exact Set.disjoint_left.mp h02 hx hy
    · exact Set.disjoint_left.mp h12 hx hy
  rw [Set.ncard_union_eq hdisj (hf0.union hf1) hf2,
    Set.ncard_union_eq h01 hf0 hf1] at heven'
  exact heven'

/-- **Finiteness of the three block intersections.**  Under the transversality hypotheses of
`Submission.Drive.ParityProp` the sets `blockMeet V k` are finite, so that the parity statement of
`Work.Drive.even_ncard_blockMeet_sum` is not a vacuous one. -/
theorem finite_blockMeet
    (V : Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hF : ContDiff ℝ Ctop (tripleDiff V))
    (hreg : ∀ x ∈ unitBox 8, tripleDiff V x = 0 →
      Function.Surjective (fderiv ℝ (tripleDiff V) x))
    (hface : ∀ x ∈ unitBoxBdry 8, tripleDiff V x = 0 → ∃ i : Fin (8 + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
      Function.Surjective (fun v : {v : Amb 8 // v i = 0} =>
        fderiv ℝ (tripleDiff V) x v.1)) :
    (blockMeet V 0).Finite ∧ (blockMeet V 1).Finite ∧ (blockMeet V 2).Finite := by
  obtain ⟨hfin, -⟩ := boxParity 8 (tripleDiff V) hF hreg hface
  have hfin' : (bdyZeros (tripleDiff V)).Finite := hfin
  rw [bdyZeros_tripleDiff_eq] at hfin'
  refine ⟨hfin'.subset ?_, hfin'.subset ?_, hfin'.subset ?_⟩
  · intro x hx; simp only [Set.mem_union]; exact Or.inl (Or.inl hx)
  · intro x hx; simp only [Set.mem_union]; exact Or.inl (Or.inr hx)
  · intro x hx; simp only [Set.mem_union]; exact Or.inr hx

/-- **The triple-intersection Leibniz rule in the cofactor form of the face hypothesis.**  As in
`Work.Drive.even_ncard_loopMeet_add_solidMeet_cofactor`, the third hypothesis of
`Submission.Drive.ParityProp` is replaced by the scalar condition that the tangential direction of the
triple intersection 1-manifold at each boundary zero is not tangent to the face. -/
theorem even_ncard_blockMeet_sum_cofactor
    (V : Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (tripleDiff V))
    (hreg : ∀ x ∈ unitBox 8, tripleDiff V x = 0 →
      Function.Surjective (fderiv ℝ (tripleDiff V) x))
    (hface : ∀ x ∈ unitBoxBdry 8, tripleDiff V x = 0 → ∃ i : Fin (8 + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
      cofactorVectorF (tripleDiff V) x i ≠ 0) :
    Even ((blockMeet V 0).ncard + (blockMeet V 1).ncard + (blockMeet V 2).ncard) :=
  even_ncard_blockMeet_sum V hF hreg fun x hx h0 =>
    let ⟨i, hi, hoth, hne⟩ := hface x hx h0
    ⟨i, hi, hoth, (surjective_domRestrict_iff_cofactorVec_ne_zero
      (fderiv ℝ (tripleDiff V) x) (hreg x hx.1 h0) i).mpr hne⟩

end

end Work.Drive
