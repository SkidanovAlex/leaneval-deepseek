import Submission.Work.PTGeometric.SourceFamily

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the block decomposition of an iterated concatenation

`GenLoop.transAt i f g` reads the first factor on the half `t i ≤ 1/2` of the cube and the second on
the other half, each with the `i`-th coordinate rescaled (`Work.PTGeometric.genLoop_transAt_apply`).
Iterating this (`Work.PTGeometric.genLoopListConcat`), the cube splits into one block per element of
the list, and on the `k`-th block the concatenation reads the `k`-th element of the list at the block
reparametrisation of the cube point.

This file proves the resulting **block decomposition**: the preimage of a set `A` which does not
contain the base point `x` under the iterated concatenation of a list `l` is the disjoint union of
the preimages under the elements of `l`:

`(genLoopListConcat i l) ⁻¹' A ≃ₜ Σ k : Fin l.length, (l.get k) ⁻¹' A`.

This is the geometric content of the `0`-end of the null-homotopy in the Pontryagin–Thom source
construction: a block is selected by the dyadic subdivision of the `i`-th coordinate, the block
reparametrisation is a homeomorphism of the cube onto the whole cube, and the middle of the cube
(the boundary between two blocks) is never in the preimage because there the concatenation takes the
value `x ∉ A`.

## Main results

* `Work.PTGeometric.halfHomeoL`, `Work.PTGeometric.halfHomeoR` — the two halves of the cube rescaled
  onto the whole cube (resp. the punctured cube);
* `Work.PTGeometric.nonempty_transAt_preimage_split` — the two-block splitting of one `transAt`;
* `Work.PTGeometric.genLoopListConcat_preimage_homeo` — the block decomposition.

## Implementation notes

The generic topological helpers used are `nonempty_homeo_sumCompl` (a space with a clopen set is the
topological sum of that set and its complement), `nonempty_homeo_subtypeInter` (a subtype of a
subtype is the subtype of the conjunction), `nonempty_homeo_sigma_succ` (the `0`-th fibre of a sigma
over `Fin (n+1)` splits off) and `nonempty_homeo_sigma_congr` (reindexing a sigma along an
equivalence with homeomorphic fibres).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped Topology unitInterval
open Function Set

namespace Work.PTGeometric

noncomputable section

variable {N : Type*} [DecidableEq N]

/-! ## The two halves of the cube, rescaled -/

section CubeHalves

/-- The block map of the left half of the cube: rescale the `i`-th coordinate by `2`. -/
def halfMapL (i : N) (t : {t : I^N // ((t : I^N) i : ℝ) ≤ 1/2}) : I^N :=
  Function.update (t : I^N) i (Set.projIcc 0 1 zero_le_one (2 * (((t : I^N) i : I) : ℝ)))

/-- The inverse of the block map of the left half: halve the `i`-th coordinate. -/
def halfMapLInv (i : N) (u : I^N) : {t : I^N // ((t : I^N) i : ℝ) ≤ 1/2} :=
  ⟨Function.update u i (Set.projIcc 0 1 zero_le_one (((u i : I) : ℝ) / 2)), by
    rw [Function.update_self]
    have hu : ((u i : I) : ℝ) ≤ 1 := (u i).2.2
    have hmem : ((u i : I) : ℝ) / 2 ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [(u i).2.1], by linarith⟩
    rw [Set.projIcc_of_mem zero_le_one hmem]
    linarith⟩

lemma coe_halfMapL (i : N) (t : {t : I^N // ((t : I^N) i : ℝ) ≤ 1/2}) :
    (halfMapL i t : I^N) =
      Function.update (t : I^N) i (Set.projIcc 0 1 zero_le_one (2 * (((t : I^N) i : I) : ℝ))) :=
  rfl

lemma coe_halfMapLInv (i : N) (u : I^N) :
    ((halfMapLInv i u : {t : I^N // ((t : I^N) i : ℝ) ≤ 1/2}) : I^N) =
      Function.update u i (Set.projIcc 0 1 zero_le_one (((u i : I) : ℝ) / 2)) :=
  rfl

lemma halfMapL_left_inv (i : N) : LeftInverse (halfMapLInv i) (halfMapL i) := by
  intro t
  apply Subtype.ext
  rw [coe_halfMapLInv, coe_halfMapL]
  have ht : (((t : I^N) i : I) : ℝ) ≤ 1/2 := t.2
  have h2 : 2 * (((t : I^N) i : I) : ℝ) ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by linarith [((t : I^N) i : I).2.1], by linarith [ht]⟩
  simp only [Function.update_self]
  rw [Set.projIcc_of_mem zero_le_one h2]
  have h3 : ((⟨2 * (((t : I^N) i : I) : ℝ), h2⟩ : I) : ℝ) / 2 = (((t : I^N) i : I) : ℝ) := by
    simp
  rw [h3, Set.projIcc_val zero_le_one ((t : I^N) i), Function.update_idem]
  exact Function.update_eq_self i (t : I^N)

lemma halfMapL_right_inv (i : N) : RightInverse (halfMapLInv i) (halfMapL i) := by
  intro u
  rw [coe_halfMapL, coe_halfMapLInv]
  have hmem : ((u i : I) : ℝ) / 2 ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by linarith [(u i).2.1], by linarith [(u i).2.2]⟩
  simp only [Function.update_self]
  rw [Set.projIcc_of_mem zero_le_one hmem]
  have h3 : 2 * (((⟨((u i : I) : ℝ) / 2, hmem⟩ : I)) : ℝ) = ((u i : I) : ℝ) := by ring
  rw [h3, Set.projIcc_val zero_le_one (u i), Function.update_idem]
  exact Function.update_eq_self i u

lemma continuous_halfMapL (i : N) : Continuous (halfMapL i) := by
  rw [show halfMapL i = fun t : {t : I^N // ((t : I^N) i : ℝ) ≤ 1/2} =>
    Function.update (t : I^N) i (Set.projIcc 0 1 zero_le_one (2 * (((t : I^N) i : I) : ℝ))) from rfl]
  apply Continuous.update continuous_subtype_val i
  exact continuous_projIcc.comp (continuous_const.mul
    (continuous_subtype_val.comp ((continuous_apply i).comp continuous_subtype_val)))

lemma continuous_halfMapLInv (i : N) : Continuous (halfMapLInv i) := by
  rw [show halfMapLInv i = fun u : I^N =>
    (⟨Function.update u i (Set.projIcc 0 1 zero_le_one (((u i : I) : ℝ) / 2)), by
      rw [Function.update_self]
      have hu : ((u i : I) : ℝ) ≤ 1 := (u i).2.2
      have hmem : ((u i : I) : ℝ) / 2 ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [(u i).2.1], by linarith⟩
      rw [Set.projIcc_of_mem zero_le_one hmem]
      linarith⟩ : {t : I^N // ((t : I^N) i : ℝ) ≤ 1/2}) from rfl]
  apply Continuous.subtype_mk
  apply Continuous.update continuous_id i
  exact continuous_projIcc.comp ((continuous_subtype_val.comp (continuous_apply i)).div_const 2)

/-- The left half of the cube, rescaled onto the whole cube. -/
def halfHomeoL (i : N) : {t : I^N // ((t : I^N) i : ℝ) ≤ 1/2} ≃ₜ (I^N) :=
  { toFun := halfMapL i
    invFun := halfMapLInv i
    left_inv := halfMapL_left_inv i
    right_inv := halfMapL_right_inv i
    continuous_toFun := continuous_halfMapL i
    continuous_invFun := continuous_halfMapLInv i }

/-- The block map of the right half of the cube: rescale the `i`-th coordinate by `2` and subtract
`1`; the target is the punctured cube `{u | u i ≠ 0}`. -/
def halfMapR (i : N) (t : {t : I^N // ¬ (((t : I^N) i : I) : ℝ) ≤ 1/2}) :
    {u : I^N // ((u i : I) : ℝ) ≠ 0} :=
  ⟨Function.update (t : I^N) i (Set.projIcc 0 1 zero_le_one (2 * (((t : I^N) i : I) : ℝ) - 1)), by
    rw [Function.update_self]
    have hlt : 1/2 < (((t : I^N) i : I) : ℝ) := not_le.mp t.2
    have h2 : 2 * (((t : I^N) i : I) : ℝ) - 1 ∈ Set.Icc (0:ℝ) 1 :=
      ⟨by linarith, by linarith [((t : I^N) i : I).2.2]⟩
    rw [Set.projIcc_of_mem zero_le_one h2]
    simp only [ne_eq, Subtype.coe_mk]
    linarith⟩

/-- The inverse of the block map of the right half. -/
def halfMapRInv (i : N) (u : {u : I^N // ((u i : I) : ℝ) ≠ 0}) :
    {t : I^N // ¬ (((t : I^N) i : I) : ℝ) ≤ 1/2} :=
  ⟨Function.update (u : I^N) i (Set.projIcc 0 1 zero_le_one (((((u : I^N) i : I) : ℝ) + 1) / 2)), by
    rw [Function.update_self]
    have hpos : 0 < (((u : I^N) i : I) : ℝ) := lt_of_le_of_ne ((u : I^N) i).2.1 (Ne.symm u.2)
    have hmem : ((((u : I^N) i : I) : ℝ) + 1) / 2 ∈ Set.Icc (0:ℝ) 1 :=
      ⟨by linarith, by linarith [((u : I^N) i : I).2.2]⟩
    rw [Set.projIcc_of_mem zero_le_one hmem]
    simp only [not_le, Subtype.coe_mk]
    linarith⟩

lemma coe_halfMapR (i : N) (t : {t : I^N // ¬ (((t : I^N) i : I) : ℝ) ≤ 1/2}) :
    ((halfMapR i t : {u : I^N // ((u i : I) : ℝ) ≠ 0}) : I^N) =
      Function.update (t : I^N) i
        (Set.projIcc 0 1 zero_le_one (2 * (((t : I^N) i : I) : ℝ) - 1)) :=
  rfl

lemma coe_halfMapRInv (i : N) (u : {u : I^N // ((u i : I) : ℝ) ≠ 0}) :
    ((halfMapRInv i u : {t : I^N // ¬ (((t : I^N) i : I) : ℝ) ≤ 1/2}) : I^N) =
      Function.update (u : I^N) i
        (Set.projIcc 0 1 zero_le_one (((((u : I^N) i : I) : ℝ) + 1) / 2)) :=
  rfl

lemma halfMapR_left_inv (i : N) : LeftInverse (halfMapRInv i) (halfMapR i) := by
  intro t
  apply Subtype.ext
  rw [coe_halfMapRInv, coe_halfMapR]
  have hlt : 1/2 < (((t : I^N) i : I) : ℝ) := not_le.mp t.2
  have h2 : 2 * (((t : I^N) i : I) : ℝ) - 1 ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by linarith, by linarith [((t : I^N) i : I).2.2]⟩
  simp only [Function.update_self]
  rw [Set.projIcc_of_mem zero_le_one h2]
  have h3 : (((⟨2 * (((t : I^N) i : I) : ℝ) - 1, h2⟩ : I) : ℝ) + 1) / 2
      = (((t : I^N) i : I) : ℝ) := by
    simp only [Subtype.coe_mk]; ring
  rw [h3, Set.projIcc_val zero_le_one ((t : I^N) i), Function.update_idem]
  exact Function.update_eq_self i (t : I^N)

lemma halfMapR_right_inv (i : N) : RightInverse (halfMapRInv i) (halfMapR i) := by
  intro u
  apply Subtype.ext
  rw [coe_halfMapR, coe_halfMapRInv]
  have hpos : 0 < (((u : I^N) i : I) : ℝ) := lt_of_le_of_ne ((u : I^N) i).2.1 (Ne.symm u.2)
  have hmem : ((((u : I^N) i : I) : ℝ) + 1) / 2 ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by linarith, by linarith [((u : I^N) i : I).2.2]⟩
  simp only [Function.update_self]
  rw [Set.projIcc_of_mem zero_le_one hmem]
  have h3 : 2 * (((⟨((((u : I^N) i : I) : ℝ) + 1) / 2, hmem⟩ : I)) : ℝ) - 1
      = (((u : I^N) i : I) : ℝ) := by
    simp only [Subtype.coe_mk]; ring
  rw [h3, Set.projIcc_val zero_le_one ((u : I^N) i), Function.update_idem]
  exact Function.update_eq_self i (u : I^N)

lemma continuous_halfMapR (i : N) : Continuous (halfMapR i) := by
  rw [show halfMapR i = fun t : {t : I^N // ¬ (((t : I^N) i : I) : ℝ) ≤ 1/2} =>
    (⟨Function.update (t : I^N) i
      (Set.projIcc 0 1 zero_le_one (2 * (((t : I^N) i : I) : ℝ) - 1)), by
        rw [Function.update_self]
        have hlt : 1/2 < (((t : I^N) i : I) : ℝ) := not_le.mp t.2
        have h2 : 2 * (((t : I^N) i : I) : ℝ) - 1 ∈ Set.Icc (0:ℝ) 1 :=
          ⟨by linarith, by linarith [((t : I^N) i : I).2.2]⟩
        rw [Set.projIcc_of_mem zero_le_one h2]
        simp only [ne_eq, Subtype.coe_mk]
        linarith⟩ : {u : I^N // ((u i : I) : ℝ) ≠ 0}) from rfl]
  apply Continuous.subtype_mk
  apply Continuous.update continuous_subtype_val i
  exact continuous_projIcc.comp
    ((continuous_const.mul (continuous_subtype_val.comp
      ((continuous_apply i).comp continuous_subtype_val))).sub continuous_const)

lemma continuous_halfMapRInv (i : N) : Continuous (halfMapRInv i) := by
  rw [show halfMapRInv i = fun u : {u : I^N // ((u i : I) : ℝ) ≠ 0} =>
    (⟨Function.update (u : I^N) i
      (Set.projIcc 0 1 zero_le_one (((((u : I^N) i : I) : ℝ) + 1) / 2)), by
        rw [Function.update_self]
        have hpos : 0 < (((u : I^N) i : I) : ℝ) := lt_of_le_of_ne ((u : I^N) i).2.1 (Ne.symm u.2)
        have hmem : ((((u : I^N) i : I) : ℝ) + 1) / 2 ∈ Set.Icc (0:ℝ) 1 :=
          ⟨by linarith, by linarith [((u : I^N) i : I).2.2]⟩
        rw [Set.projIcc_of_mem zero_le_one hmem]
        simp only [not_le, Subtype.coe_mk]
        linarith⟩ : {t : I^N // ¬ (((t : I^N) i : I) : ℝ) ≤ 1/2}) from rfl]
  apply Continuous.subtype_mk
  apply Continuous.update continuous_subtype_val i
  exact continuous_projIcc.comp
    (((continuous_subtype_val.comp ((continuous_apply i).comp continuous_subtype_val)).add
      continuous_const).div_const 2)

/-- The right half of the cube, rescaled onto the punctured cube `{u | u i ≠ 0}`. -/
def halfHomeoR (i : N) :
    {t : I^N // ¬ (((t : I^N) i : I) : ℝ) ≤ 1/2} ≃ₜ {u : I^N // ((u i : I) : ℝ) ≠ 0} :=
  { toFun := halfMapR i
    invFun := halfMapRInv i
    left_inv := halfMapR_left_inv i
    right_inv := halfMapR_right_inv i
    continuous_toFun := continuous_halfMapR i
    continuous_invFun := continuous_halfMapRInv i }

end CubeHalves

/-! ## Generic topological helpers -/

/-- **A subtype of a subtype is the subtype of the conjunction.** -/
theorem nonempty_homeo_subtypeInter {α : Type*} [TopologicalSpace α] {p q : α → Prop} :
    Nonempty ({x : {x // p x} // q x.1} ≃ₜ {x : α // p x ∧ q x}) := by
  refine ⟨{ toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
            invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
            left_inv := fun x => rfl
            right_inv := fun x => rfl
            continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
              (fun x => ⟨x.1.2, x.2⟩)
            continuous_invFun := (Continuous.subtype_mk continuous_subtype_val
              (fun x => x.2.1)).subtype_mk (fun x => x.2.2) }⟩

/-- **A redundant predicate may be dropped.**  If `q` implies `p` then the `q`-elements of `↥p` are
the `q`-elements. -/
theorem nonempty_homeo_subtype_of_imp {α : Type*} [TopologicalSpace α] {p q : α → Prop}
    (h : ∀ x, q x → p x) : Nonempty ({x : {x // p x} // q x.1} ≃ₜ {x : α // q x}) := by
  obtain ⟨e⟩ := nonempty_homeo_subtypeInter (p := p) (q := q)
  refine ⟨e.trans (Homeomorph.setCongr ?_)⟩
  ext x
  exact ⟨fun hx => hx.2, fun hx => ⟨h x hx, hx⟩⟩

/-- **A space is the topological sum of a clopen set and its complement.** -/
theorem nonempty_homeo_sumCompl {Y : Type*} [TopologicalSpace Y] {s : Set Y} (hs : IsClopen s) :
    Nonempty (Y ≃ₜ (s ⊕ (sᶜ : Set Y))) := by
  classical
  refine ⟨((Equiv.Set.sumCompl s).toHomeomorphOfContinuousClosed ?_ ?_).symm⟩
  · rw [continuous_sum_dom]
    exact ⟨continuous_subtype_val, continuous_subtype_val⟩
  · intro C hC
    obtain ⟨h1, h2⟩ := isClosed_sum_iff.mp hC
    have himg : (Equiv.Set.sumCompl s) '' C =
        (Subtype.val '' (Sum.inl ⁻¹' C)) ∪ (Subtype.val '' (Sum.inr ⁻¹' C)) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        rcases z with x | x
        · exact Or.inl ⟨x, hz, Equiv.Set.sumCompl_apply_inl s x⟩
        · exact Or.inr ⟨x, hz, Equiv.Set.sumCompl_apply_inr s x⟩
      · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
        · exact ⟨Sum.inl x, hx, Equiv.Set.sumCompl_apply_inl s x⟩
        · exact ⟨Sum.inr x, hx, Equiv.Set.sumCompl_apply_inr s x⟩
    rw [himg]
    exact ((hs.1.isClosedMap_subtype_val : IsClosedMap (Subtype.val : s → Y))
      (Sum.inl ⁻¹' C) h1).union
      ((hs.2.isClosed_compl.isClosedMap_subtype_val :
          IsClosedMap (Subtype.val : (sᶜ : Set Y) → Y))
        (Sum.inr ⁻¹' C) h2)

/-- **`Fin.cases` of a family of continuous maps is continuous in the last argument.** -/
theorem continuous_finCases {n : ℕ} {Y : Fin (n+1) → Type*} [∀ k, TopologicalSpace (Y k)]
    {Z : Type*} [TopologicalSpace Z] {z : (Y 0) → Z} {s : (k : Fin n) → Y k.succ → Z}
    (hz : Continuous z) (hs : ∀ k, Continuous (s k)) :
    ∀ j : Fin (n+1), Continuous (Fin.cases (motive := fun i => Y i → Z) z s j) := by
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · simpa using hz
  · simpa using hs k

/-- **The `0`-th fibre of a sigma over `Fin (n+1)` splits off.** -/
theorem nonempty_homeo_sigma_succ {n : ℕ} {Y : Fin (n+1) → Type*} [∀ k, TopologicalSpace (Y k)] :
    Nonempty (((Σ k : Fin n, Y k.succ) ⊕ Y 0) ≃ₜ (Σ k : Fin (n+1), Y k)) := by
  refine ⟨{ toFun := Sum.elim (fun p : Σ k : Fin n, Y k.succ => ⟨p.1.succ, p.2⟩) (fun y => ⟨0, y⟩)
            invFun := fun p => Fin.cases (motive := fun j => Y j → ((Σ k : Fin n, Y k.succ) ⊕ Y 0))
              Sum.inr (fun k y => Sum.inl ⟨k, y⟩) p.1 p.2
            left_inv := ?_
            right_inv := ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }⟩
  · rintro (⟨k, y⟩ | y)
    · rfl
    · rfl
  · rintro ⟨j, y⟩
    revert y
    refine Fin.cases ?_ ?_ j
    · intro y; rfl
    · intro k y; rfl
  · rw [continuous_sum_dom]
    refine ⟨?_, continuous_sigmaMk⟩
    apply continuous_sigma
    intro k
    exact continuous_sigmaMk
  · apply continuous_sigma
    intro j
    exact continuous_finCases (z := (Sum.inr : Y 0 → ((Σ k : Fin n, Y k.succ) ⊕ Y 0)))
      (s := fun k y => (Sum.inl ⟨k, y⟩ : ((Σ k : Fin n, Y k.succ) ⊕ Y 0)))
      continuous_inr (fun k => continuous_inl.comp continuous_sigmaMk) j

/-- **Reindexing a sigma type along an equivalence with homeomorphic fibres.** -/
theorem nonempty_homeo_sigma_congr {ι κ : Type*} {P : ι → Type*} {Q : κ → Type*}
    [∀ i, TopologicalSpace (P i)] [∀ j, TopologicalSpace (Q j)]
    (e : ι ≃ κ) (h : ∀ i, Nonempty (P i ≃ₜ Q (e i))) :
    Nonempty ((Σ i, P i) ≃ₜ (Σ j, Q j)) := by
  have G : ∀ i, P i ≃ₜ Q (e i) := fun i => Classical.choice (h i)
  exact ⟨(IsHomeomorph.sigmaMap (f := ⇑e) e.bijective (g := fun i => ⇑(G i))
    (fun i => (G i).isHomeomorph)).homeomorph⟩

/-! ## The two-block splitting of one concatenation -/

/-- **The preimage of `A` under `transAt i F g` splits into the preimages under `F` and `g`.**
The cube is cut at `t i = 1/2`; on each half the concatenation reads one factor at the block
reparametrisation; the cut locus itself is never in the preimage because the reparametrisation sends
it to the boundary of the cube, where the factor takes the value `x ∉ A`. -/
theorem nonempty_transAt_preimage_split {X : Type} [TopologicalSpace X] {x : X}
    (i : N) (F g : GenLoop N X x) (A : Set X) (hx : x ∉ A) :
    Nonempty (((GenLoop.transAt i F g) ⁻¹' A) ≃ₜ ((F ⁻¹' A) ⊕ (g ⁻¹' A))) := by
  classical
  set P := (GenLoop.transAt i F g) ⁻¹' A with hP
  have hcoord : Continuous fun t : P => (((t : I^N) i : I) : ℝ) :=
    continuous_subtype_val.comp ((continuous_apply i).comp continuous_subtype_val)
  set s : Set P := {t | (((t : I^N) i : I) : ℝ) ≤ 1/2} with hs
  -- the cut locus is not in `P`: there the concatenation takes the value `x ∉ A`
  have hne : ∀ t : P, (((t : I^N) i : I) : ℝ) ≠ 1/2 := by
    intro t ht
    have hle : (((t : I^N) i : I) : ℝ) ≤ 1/2 := le_of_eq ht
    have hp : Set.projIcc (0:ℝ) 1 (by norm_num) (2 * (1/2 : ℝ)) = (1 : I) := by
      rw [show 2 * (1/2 : ℝ) = 1 by norm_num, Set.projIcc_right]
      rfl
    have hval : GenLoop.transAt i F g (t : I^N) = F (Function.update (t : I^N) i 1) := by
      rw [genLoop_transAt_apply_of_le i F g hle, show 2 * (((t : I^N) i : I) : ℝ) = 2 * (1/2) by rw [ht]]
      exact congrArg F (congrArg (Function.update (t : I^N) i) hp)
    have hb : Function.update (t : I^N) i (1 : I) ∈ Cube.boundary N :=
      ⟨i, Or.inr (Function.update_self i (1 : I) (t : I^N))⟩
    have hmem : GenLoop.transAt i F g (t : I^N) ∈ A := t.2
    rw [hval, GenLoop.boundary F (Function.update (t : I^N) i (1 : I)) hb] at hmem
    exact hx hmem
  have hscl : IsClopen s := by
    have hsplit : s = {t : P | (((t : I^N) i : I) : ℝ) < 1/2} := by
      ext t
      rw [hs]
      exact ⟨fun h => lt_of_le_of_ne h (hne t),
        fun h => show (((t : I^N) i : I) : ℝ) ≤ 1/2 from le_of_lt h⟩
    refine ⟨IsClosed.preimage hcoord isClosed_Iic, ?_⟩
    rw [hsplit]
    exact IsOpen.preimage hcoord isOpen_Iio
  obtain ⟨hsum⟩ := nonempty_homeo_sumCompl (Y := P) hscl
  -- the left piece
  have hL : Nonempty (s ≃ₜ (F ⁻¹' A)) := by
    obtain ⟨e₁⟩ := nonempty_homeo_subtypeInter (p := fun t : I^N => GenLoop.transAt i F g t ∈ A)
      (q := fun t : I^N => (((t : I^N) i : I) : ℝ) ≤ 1/2)
    obtain ⟨e₂⟩ := nonempty_homeo_subtypeInter (p := fun t : I^N => (((t : I^N) i : I) : ℝ) ≤ 1/2)
      (q := fun t : I^N => GenLoop.transAt i F g t ∈ A)
    refine ⟨e₁.trans ((Homeomorph.setCongr ?_).trans (e₂.symm.trans ?_))⟩
    · ext t
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    · exact (halfHomeoL i).subtype
        (p := fun t : {t : I^N // (((t : I^N) i : I) : ℝ) ≤ 1/2} =>
          GenLoop.transAt i F g (t : I^N) ∈ A)
        (q := fun u : I^N => F u ∈ A)
        (fun t => by
          rw [genLoop_transAt_apply_of_le i F g t.2]
          rfl)
  -- the right piece
  have hR : Nonempty ((sᶜ : Set P) ≃ₜ (g ⁻¹' A)) := by
    obtain ⟨e₁⟩ := nonempty_homeo_subtypeInter (p := fun t : I^N => GenLoop.transAt i F g t ∈ A)
      (q := fun t : I^N => ¬ (((t : I^N) i : I) : ℝ) ≤ 1/2)
    obtain ⟨e₂⟩ := nonempty_homeo_subtypeInter
      (p := fun t : I^N => ¬ (((t : I^N) i : I) : ℝ) ≤ 1/2)
      (q := fun t : I^N => GenLoop.transAt i F g t ∈ A)
    have e₃ : {t : {t : I^N // ¬ (((t : I^N) i : I) : ℝ) ≤ 1/2} //
          GenLoop.transAt i F g (t : I^N) ∈ A} ≃ₜ
        {u : {u : I^N // ((u i : I) : ℝ) ≠ 0} // g (u : I^N) ∈ A} :=
      (halfHomeoR i).subtype
        (p := fun t : {t : I^N // ¬ (((t : I^N) i : I) : ℝ) ≤ 1/2} =>
          GenLoop.transAt i F g (t : I^N) ∈ A)
        (q := fun u : {u : I^N // ((u i : I) : ℝ) ≠ 0} => g (u : I^N) ∈ A)
        (fun t => by
          rw [genLoop_transAt_apply_of_gt i F g t.2]
          rfl)
    obtain ⟨e₄⟩ := nonempty_homeo_subtype_of_imp
      (p := fun u : I^N => ((u i : I) : ℝ) ≠ 0) (q := fun u : I^N => g u ∈ A)
      (fun u hu h0 => by
        have hb : u ∈ Cube.boundary N := ⟨i, Or.inl (Subtype.ext h0)⟩
        rw [GenLoop.boundary g u hb] at hu
        exact hx hu)
    refine ⟨e₁.trans ((Homeomorph.setCongr ?_).trans (e₂.symm.trans (e₃.trans e₄)))⟩
    ext t
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  exact ⟨hsum.trans (Homeomorph.sumCongr (Classical.choice hL) (Classical.choice hR))⟩

/-! ## The block decomposition -/

theorem genLoopListConcat_preimage_homeo {N : Type*} [DecidableEq N] {X : Type} [TopologicalSpace X]
    {x : X} (i : N) (l : List (GenLoop N X x)) {A : Set X} (hA : IsClosed A) (hx : x ∉ A) :
    Nonempty (((Work.PTGeometric.genLoopListConcat i l) ⁻¹' A) ≃ₜ
      (Σ k : Fin l.length, ((l.get k) ⁻¹' A))) := by
  classical
  induction l with
  | nil =>
    rw [genLoopListConcat_nil]
    haveI h1 : IsEmpty (((GenLoop.const : GenLoop N X x) ⁻¹' A)) :=
      ⟨fun t => hx (by
        have h2 : (GenLoop.const : GenLoop N X x) (t : I^N) ∈ A := t.2
        rwa [GenLoop.const_apply] at h2)⟩
    haveI h2 : IsEmpty ((Σ k : Fin ([] : List (GenLoop N X x)).length,
        ((([] : List (GenLoop N X x)).get k) ⁻¹' A))) :=
      ⟨fun p => Fin.elim0 p.1⟩
    exact ⟨Homeomorph.empty⟩
  | cons g l' ih =>
    obtain ⟨e⟩ := ih
    obtain ⟨h1⟩ := nonempty_transAt_preimage_split (i := i)
      (F := genLoopListConcat i l') (g := g) (A := A) hx
    have hset : ∀ k : Fin l'.length,
        (l'.get k) ⁻¹' A = ((g :: l').get (Fin.succ k)) ⁻¹' A := by
      intro k
      have hk : (g :: l').get (Fin.succ k) = l'.get k := List.get_cons_succ
      rw [hk]
    obtain ⟨h2⟩ := nonempty_homeo_sigma_congr (ι := Fin l'.length) (κ := Fin l'.length)
      (P := fun k => (l'.get k) ⁻¹' A)
      (Q := fun k => ((g :: l').get (Fin.succ k)) ⁻¹' A)
      (Equiv.refl _) (fun k => ⟨Homeomorph.setCongr (hset k)⟩)
    obtain ⟨h3⟩ := nonempty_homeo_sigma_succ (n := l'.length)
      (Y := fun j => ((g :: l').get j) ⁻¹' A)
    exact ⟨h1.trans <| (Homeomorph.sumCongr e (Homeomorph.refl (g ⁻¹' A))).trans <|
      (Homeomorph.sumCongr h2 (Homeomorph.refl (g ⁻¹' A))).trans <|
      (Homeomorph.sumCongr
        (Homeomorph.refl (Σ k : Fin l'.length, ((g :: l').get (Fin.succ k)) ⁻¹' A))
        (Homeomorph.setCongr (by rw [List.get_cons_zero]))).trans h3⟩

end

end Work.PTGeometric
