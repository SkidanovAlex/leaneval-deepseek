/-
# The local Möbius model of a fold transition (pointwise form)

`Work.RTOwed.FoldTransLocal` is the named hypothesis of the area `Work.RTOwed`: at every point of
the source of the transition of two fold charts, the transition is the Möbius transformation of a
*single* Lorentz matrix on some open neighbourhood.  This file proves it, i.e. fills the one hole
of the fold block of the atlas, in the pointwise form

  `Work.RTOwed.foldTrans_local (i j) (hz : z ∈ Trans i j) : ∃ V B, IsOpen V ∧ z ∈ V ∧
   IsLorentzMat B ∧ ∀ z' ∈ V ∩ Trans i j, transMap i j z' = mobius B z'`.

The mathematics: a point `z` of the transition source has a *common lift* `x` in a cell
`Dvor i r ∩ Dvor j s` of the Voronoi decompositions of the two classes; the transition at the class
of `x` is then `mobius (transMat i j r s)` (`Work.RTOwed.foldTrans_piece`).  The Voronoi cells with
the *same* matrix are closed under the identification relation `rel` of `M̄`: crossing a wall of the
source class multiplies `D_r` on the right by `psi` of the *set of sides* of the crossed walls
(`Work.RTOwed.foldDr_flipSet_eq_psi`), and the crossed walls of the two classes have the same sides,
so the ratio `D_{r'} D_r⁻¹` — and hence `transMat` — is unchanged.  Their union `R` is therefore a
saturated open subset of `X̄`, `mk '' R` is an open neighbourhood of the class in `M̄`, and its image
under the chart `i` is the required `V`.
-/
import Mathlib
import Submission.Work.RTOwed.Defs
import Submission.Work.RTOwed.FoldTransLocal
import Submission.Work.RTOwed.transPieceLift
import Submission.Work.RTOwed.foldTrans_piece
import Submission.Work.RTOwed.coordPerm_eq_mobius
import Submission.Work.RTOwed.mobiusKlein_eq_mobius
import Submission.Work.RTOwed.foldDr_ratio_flip
import Submission.Work.FoldInst.Basic
import Submission.Work.FoldInst.Data
import Submission.Work.FoldInst.Cert
import Submission.Work.FoldInst.CertFold
import Submission.Work.FoldInst.Polytope
import Submission.Work.FoldInst.Qbar_geometry
import Submission.Work.FoldInst.Action
import Submission.Work.FoldInst.Continuous
import Submission.Work.FoldInst.Atlas
import Submission.Work.FoldInst.Quotient
import Submission.Work.FoldInst.Connected
import Submission.Work.FoldInst.FoldPiece
import Submission.Work.FoldInst.copies_meet
import Submission.Work.FoldInst.fold_theta_coord
import Submission.Work.FoldInst.fold_theta_orthant
import Submission.Work.FoldInst.fold_cover_sides
import Submission.Work.FoldInst.Voronoi
import Submission.Work.FoldInst.CertFlip
import Submission.Work.FoldInst.fold_state_flipSet
import Submission.Work.FoldInst.Dvor_disjoint
import Submission.Work.FoldInst.Ksub_eq_wallSum
import Submission.Work.FoldInst.actX_image_Dvor
import Submission.Work.FoldInst.foldTheta_flip
import Submission.Work.FoldInst.foldTheta_injOn
import Submission.Work.FoldInst.fold_chart_of_glued
import Submission.Work.FoldInst.foldPsi_eq
import Submission.Work.FoldInst.foldPsi_hagree
import Submission.Work.FoldInst.foldPsi_hcross
import Submission.Work.FoldInst.foldPsi_continuousOn
import Submission.Work.FoldInst.isOpen_foldTheta_image
import Submission.Work.FoldInst.htarget_open
import Submission.Work.FoldInst.foldPhi_mk
import Submission.Work.FoldInst.foldPhi_continuousOn
import Submission.Work.FoldInst.exists_foldChart
import Submission.Work.FoldInst.CoverData
import Submission.Work.FoldInst.Cover
import Submission.Work.FoldInst.Qbar_of_mem_VoronoiOpen_root
import Submission.Work.FoldInst.foldPsi_image_reflVec
import Submission.Work.FoldInst.FoldInvDefs
import Submission.Work.FoldInst.foldInv_foldTheta
import Submission.Work.FoldInst.continuousOn_foldInv
import Submission.Work.FoldInst.exists_pos_le_foldTheta_height
import Submission.Work.FoldInst.FoldChart
import Submission.Work.HypModel.Basic
import Submission.Work.HypModel.Lorentz
import Submission.Work.HypModel.lorentz_dHypOfUHS
import Submission.Work.HypModel.hypOfUHS_four_pos
import Submission.Work.HypModel.lorentz_hypOfUHS_self
import Submission.Work.HypModel.four_pos_of_lorentz_pair_neg
import Submission.Work.HypModel.hasFDerivAt_hypOfUHS
import Submission.Work.HypModel.hasFDerivAt_uhsOfHyp
import Submission.Work.HypModel.hypOfKlein_mem_upperSheet
import Submission.Work.HypModel.hypOfKlein_injOn
import Submission.Work.HypModel.hypOfKlein_kleinOfHyp
import Submission.Work.HypModel.hypOfKlein_diagonal
import Submission.Work.HypModel.hypOfKlein_segment_pos_combo
import Submission.Work.HypModel.hypOfUHS_injOn
import Submission.Work.HypModel.hypOfUHS_uhsOfHyp
import Submission.Work.HypModel.uhsOfHyp_three_pos
import Submission.Work.HypModel.isLorentzMat_uhsTranslation
import Submission.Work.HypModel.kleinOfHyp_hypOfKlein
import Submission.Work.HypModel.kleinOfHyp_mem_ball
import Submission.Work.HypModel.mobiusKlein_isometry
import Submission.Work.HypModel.mobiusKlein_mem
import Submission.Work.HypModel.mobiusKlein_mul
import Submission.Work.HypModel.mobius_contDiffOn
import Submission.Work.HypModel.uhsOfHyp_hypOfUHS
import Submission.Work.HypModel.mobius_isometry
import Submission.Work.HypModel.mobius_mul
import Submission.Work.HypModel.mobius_one
import Submission.Work.HypModel.mobius_uhsTranslation
import Submission.Work.HypModel.polarToUHS_isometry
import Submission.Work.HypModel.tangent_hypOfUHS

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Filter Matrix
open scoped Manifold ContDiff Topology Bundle RealInnerProductSpace Matrix
open Bundle

namespace Work.RTOwed

open Work.FoldInst

/-! ### Elementary facts about the wall generators

The generator `foldGen i t` of the `t`-th wall of a fold class does not depend on the sign index
(`Work.RTOwed.sideType_foldWalls`).  We need two consequences: the generators of the walls of a
*nonempty* Voronoi piece are pairwise distinct, and the generators of the five side types are
linearly independent over `ZMod 2`. -/

/-- **The five wall generators are independent.**  The subset sums of the five side types
`Work.FoldInst.typeGen` are injective: a subset of `Fin 5` is recovered from the sum of the
generators of its elements. -/
theorem typeGen_sum_injective :
    Function.Injective fun a : Finset (Fin 5) => ∑ i ∈ a, Work.FoldInst.typeGen i := by
  decide

/-- The sum of the five generators over a subset vanishes only for the empty subset. -/
theorem typeGen_sum_eq_zero {a : Finset (Fin 5)}
    (h : ∑ i ∈ a, Work.FoldInst.typeGen i = 0) : a = ∅ := by
  have h0 : (∑ i ∈ (∅ : Finset (Fin 5)), Work.FoldInst.typeGen i) = 0 := by simp
  refine typeGen_sum_injective ?_
  change (∑ i ∈ a, Work.FoldInst.typeGen i) = ∑ i ∈ (∅ : Finset (Fin 5)), Work.FoldInst.typeGen i
  rw [h, h0]

/-- **The walls of a nonempty Voronoi piece have distinct generators.**  If two walls of the sign
index `r` of the class `i` have the same generator, and some point `x` lies in `Dvor i r`, then the
two walls coincide: the two single flips of `r` at those walls are `actX`-translates of `Dvor i r`
by the same group element, so the two (distinct, hence disjoint) pieces are equal, and `x` gives one
of them a point. -/
theorem foldGen_inj_of_mem {i : Fin 98} {r : Fin (foldCodim i) → Bool} {x : Xbar}
    (hx : x ∈ Dvor i r) {t₁ t₂ : Fin (foldCodim i)}
    (h : foldGen i t₁ = foldGen i t₂) : t₁ = t₂ := by
  by_contra ht
  have hW : wallSum i {t₁} = wallSum i {t₂} := by
    rw [wallSum, wallSum]; simp [h]
  have h1 : actX (wallSum i {t₁}) '' Dvor i r = Dvor i (flipSet r {t₁}) :=
    actX_image_Dvor i r {t₁}
  have h2 : actX (wallSum i {t₂}) '' Dvor i r = Dvor i (flipSet r {t₂}) :=
    actX_image_Dvor i r {t₂}
  have hne : flipSet r {t₁} ≠ flipSet r {t₂} := by
    intro heq
    have h1 : flipSet r {t₁} t₁ ≠ flipSet r {t₂} t₁ := by
      have hmem1 : t₁ ∈ ({t₁} : Finset (Fin (foldCodim i))) := Finset.mem_singleton_self t₁
      have hmem2 : t₁ ∉ ({t₂} : Finset (Fin (foldCodim i))) := by
        simp [Finset.mem_singleton, ht]
      rw [flipSet_apply, flipSet_apply,
        decide_eq_true_iff.mpr hmem1, decide_eq_false_iff_not.mpr hmem2]
      cases r t₁ <;> simp
    exact h1 (congrFun heq t₁)
  have heq : Dvor i (flipSet r {t₁}) = Dvor i (flipSet r {t₂}) := by
    rw [← h1, hW, h2]
  have hdisj : Disjoint (Dvor i (flipSet r {t₁})) (Dvor i (flipSet r {t₂})) :=
    Dvor_disjoint i hne
  have hmem : actX (wallSum i {t₁}) x ∈ Dvor i (flipSet r {t₁}) := by
    rw [← h1]; exact ⟨x, hx, rfl⟩
  have hmem2 : actX (wallSum i {t₁}) x ∈ Dvor i (flipSet r {t₂}) := heq ▸ hmem
  exact (Set.disjoint_left.mp hdisj hmem) hmem2

/-- The generator of a wall is the type of that wall. -/
theorem foldGen_eq_sideType (i : Fin 98) (r : Fin (foldCodim i) → Bool)
    (t : Fin (foldCodim i)) :
    foldGen i t = sideType (foldWalls i r t) := by
  rw [foldGen]
  exact (sideType_foldWalls i r t).symm

/-- **Two distinct tight sides of a point of a Voronoi piece have different types.**  Both are walls
of any piece containing the point (`Work.FoldInst.Dvor_tight`), and the generators of the walls of a
nonempty piece are pairwise distinct (`foldGen_inj_of_mem`). -/
theorem sideType_inj_of_tight {i : Fin 98} {r : Fin (foldCodim i) → Bool} {x : Xbar}
    (hx : x ∈ Dvor i r) {S₁ S₂ : Fin 24} (h₁ : sideSlack S₁ ↑x.2 = 0)
    (h₂ : sideSlack S₂ ↑x.2 = 0) (h : sideType S₁ = sideType S₂) : S₁ = S₂ := by
  obtain ⟨t₁, ht₁⟩ := Dvor_tight i r hx h₁
  obtain ⟨t₂, ht₂⟩ := Dvor_tight i r hx h₂
  have hgen : foldGen i t₁ = foldGen i t₂ := by
    rw [foldGen_eq_sideType i r t₁, foldGen_eq_sideType i r t₂, ht₁, ht₂, h]
  have htt : t₁ = t₂ := foldGen_inj_of_mem hx hgen
  rw [← ht₁, ← ht₂, htt]

/-- **The sum of the types of a set of tight sides vanishes only for the empty set.** -/
theorem sum_sideType_eq_zero_of_tight {i : Fin 98} {r : Fin (foldCodim i) → Bool} {x : Xbar}
    (hx : x ∈ Dvor i r) {D : Finset (Fin 24)} (hD : ∀ S ∈ D, sideSlack S ↑x.2 = 0)
    (h : ∑ S ∈ D, sideType S = 0) : D = ∅ := by
  have hinj : Set.InjOn sideTypeIdx (↑D : Set (Fin 24)) := by
    intro S₁ hS₁ S₂ hS₂ hss
    exact sideType_inj_of_tight hx (hD S₁ hS₁) (hD S₂ hS₂) (by rw [sideType, sideType, hss])
  have hsum : ∑ i ∈ D.image sideTypeIdx, Work.FoldInst.typeGen i = 0 := by
    rw [Finset.sum_image (f := Work.FoldInst.typeGen) (g := sideTypeIdx) hinj]
    simpa only [sideType, typeGen] using h
  have hempty : D.image sideTypeIdx = ∅ := typeGen_sum_eq_zero hsum
  by_contra hne
  obtain ⟨S, hS⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have : sideTypeIdx S ∈ D.image sideTypeIdx := Finset.mem_image_of_mem _ hS
  rw [hempty] at this
  exact Finset.notMem_empty _ this


/-! ### The wall sets of the two classes agree

Crossing a wall of the source class at `x` is given by a group element `wallSum i Δi`; the same
group element is a sum of wall generators of the target class, `wallSum j Δj`.  The *sets of sides*
of the two families of crossed walls agree: they are both computed from the sum of the types, which
determines the set of sides because the side types of the tight sides are distinct and the five type
generators are independent. -/

/-- The type of a side is the generator of its type index. -/
theorem sideType_eq_typeGen_sideTypeIdx (S : Fin 24) :
    sideType S = Work.FoldInst.typeGen (sideTypeIdx S) := rfl

/-- The sum of the types of a set of sides, as the sum of the generators of the image of the set
under the type index. -/
theorem sum_sideType_eq_sum_typeGen (D : Finset (Fin 24))
    (hinj : Set.InjOn sideTypeIdx (↑D : Set (Fin 24))) :
    ∑ S ∈ D, sideType S = ∑ i ∈ D.image sideTypeIdx, Work.FoldInst.typeGen i := by
  rw [Finset.sum_image (f := Work.FoldInst.typeGen) (g := sideTypeIdx) hinj]
  exact Finset.sum_congr rfl fun S _ => (sideType_eq_typeGen_sideTypeIdx S).symm

set_option linter.unusedVariables false in
/-- **The sets of sides of the crossed walls of the two classes agree.** -/
theorem image_foldWalls_eq_of_wallSum_eq {i j : Fin 98}
    {r : Fin (foldCodim i) → Bool} {s : Fin (foldCodim j) → Bool} {x : Xbar}
    (hxr : x ∈ Dvor i r) (hxs : x ∈ Dvor j s)
    {Δi : Finset (Fin (foldCodim i))} {Δj : Finset (Fin (foldCodim j))}
    (hi : ∀ t ∈ Δi, sideSlack (foldWalls i r t) ↑x.2 = 0)
    (hj : ∀ t ∈ Δj, sideSlack (foldWalls j s t) ↑x.2 = 0)
    (h : wallSum i Δi = wallSum j Δj) :
    Δi.image (foldWalls i r) = Δj.image (foldWalls j s) := by
  set A := Δi.image (foldWalls i r) with hAdef
  set B := Δj.image (foldWalls j s) with hBdef
  have hA : ∀ S ∈ A, sideSlack S ↑x.2 = 0 := by
    intro S hS
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hS
    exact hi t ht
  have hB : ∀ S ∈ B, sideSlack S ↑x.2 = 0 := by
    intro S hS
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hS
    exact hj t ht
  -- the two sums of types agree
  have hsumA : ∑ S ∈ A, sideType S = wallSum i Δi := by
    rw [hAdef, Finset.sum_image (f := sideType)
      (g := foldWalls i r) (foldWalls_apply_injective i r).injOn]
    simp only [wallSum]
    exact Finset.sum_congr rfl fun t _ => (foldGen_eq_sideType i r t).symm
  have hsumB : ∑ S ∈ B, sideType S = wallSum j Δj := by
    rw [hBdef, Finset.sum_image (f := sideType)
      (g := foldWalls j s) (foldWalls_apply_injective j s).injOn]
    simp only [wallSum]
    exact Finset.sum_congr rfl fun t _ => (foldGen_eq_sideType j s t).symm
  have hsum : ∑ S ∈ A, sideType S = ∑ S ∈ B, sideType S := by
    rw [hsumA, hsumB, h]
  -- the type images agree
  have hinjA : Set.InjOn sideTypeIdx (↑A : Set (Fin 24)) := by
    intro S₁ hS₁ S₂ hS₂ hss
    exact sideType_inj_of_tight hxr (hA S₁ hS₁) (hA S₂ hS₂) (by rw [sideType, sideType, hss])
  have hinjB : Set.InjOn sideTypeIdx (↑B : Set (Fin 24)) := by
    intro S₁ hS₁ S₂ hS₂ hss
    exact sideType_inj_of_tight hxr (hB S₁ hS₁) (hB S₂ hS₂) (by rw [sideType, sideType, hss])
  have himg : A.image sideTypeIdx = B.image sideTypeIdx := by
    refine typeGen_sum_injective ?_
    change (∑ i ∈ A.image sideTypeIdx, Work.FoldInst.typeGen i) =
      ∑ i ∈ B.image sideTypeIdx, Work.FoldInst.typeGen i
    rw [← sum_sideType_eq_sum_typeGen A hinjA, ← sum_sideType_eq_sum_typeGen B hinjB]
    exact hsum
  -- conclude `A = B`: both consist of the tight sides of a given type
  refine Finset.Subset.antisymm ?_ ?_
  · intro S hS
    have hmem : sideTypeIdx S ∈ B.image sideTypeIdx := by rw [← himg]; exact Finset.mem_image_of_mem _ hS
    obtain ⟨S', hS', hSS'⟩ := Finset.mem_image.mp hmem
    have : S' = S := sideType_inj_of_tight hxr (hB S' hS') (hA S hS)
      (by rw [sideType, sideType, hSS'])
    rwa [← this]
  · intro S hS
    have hmem : sideTypeIdx S ∈ A.image sideTypeIdx := by rw [himg]; exact Finset.mem_image_of_mem _ hS
    obtain ⟨S', hS', hSS'⟩ := Finset.mem_image.mp hmem
    have : S' = S := sideType_inj_of_tight hxr (hA S' hS') (hB S hS)
      (by rw [sideType, sideType, hSS'])
    rwa [← this]

/-! ### The matrix of a cell depends only on the class

The telescoped flip identity `Work.RTOwed.foldDr_flipSet_eq_psi` multiplies the developing matrix on
the right by `psi` of the *set of sides* of the flipped walls.  Two cells of the decompositions of
two fold classes that share a point of `X̄` are related by such flips with the same set of sides
(`image_foldWalls_eq_of_wallSum_eq`), so the `transMat` of the two cells agree. -/

/-- The correction matrix `Work.RTOwed.psi` over `ℝ`. -/
def psiR (S : Finset (Fin 24)) : Matrix (Fin 5) (Fin 5) ℝ :=
  (psi S).map (Int.castRingHom ℝ)

/-- The determinant of `psiR` is a unit (it is a `±1` matrix). -/
theorem isUnit_det_psiR (S : Finset (Fin 24)) : IsUnit (psiR S).det := by
  have h : psiR S = (Int.castRingHom ℝ).mapMatrix (psi S) := rfl
  rw [h, ← RingHom.map_det]
  exact (isUnit_det_psi S).map (Int.castRingHom ℝ)

/-- The telescoped flip identity over `ℝ`. -/
theorem foldDrR_flipSet_eq_psiR (i : Fin 98) (r : Fin (foldCodim i) → Bool)
    (Δ : Finset (Fin (foldCodim i))) :
    foldDrR i (flipSet r Δ) = foldDrR i r * psiR (Δ.image (foldWalls i r)) := by
  rw [foldDrR, foldDrR, foldDr_flipSet_eq_psi, Matrix.map_mul]
  rfl

/-- Cancelling a common invertible factor on the right of a product of two matrices. -/
theorem mul_mul_inv_mul (P Q U : Matrix (Fin 5) (Fin 5) ℝ) (hU : IsUnit U.det) :
    (P * U) * (Q * U)⁻¹ = P * Q⁻¹ := by
  rw [Matrix.mul_inv_rev]
  rw [← Matrix.mul_assoc (P * U) U⁻¹ Q⁻¹]
  rw [Matrix.mul_assoc P U U⁻¹, mul_nonsing_inv U hU, Matrix.mul_one]

/-- **The `transMat` of the cells of two classes through a common point agree.**  If `x` and `x'`
have the same class, `x` lies in the cell `Dvor i r ∩ Dvor j s` and `x'` in the cell
`Dvor i r' ∩ Dvor j s'`, then the two cells carry the same transition matrix. -/
theorem transMat_eq_of_rel {i j : Fin 98} {r r' : Fin (foldCodim i) → Bool}
    {s s' : Fin (foldCodim j) → Bool} {x x' : Xbar}
    (hx : x ∈ Dvor i r) (hxs : x ∈ Dvor j s) (hx' : x' ∈ Dvor i r') (hxs' : x' ∈ Dvor j s')
    (hrel : rel x x') : transMat i j r' s' = transMat i j r s := by
  obtain ⟨θ, hθK, hθ⟩ := hrel
  obtain ⟨Δi, hΔi, hΔiθ⟩ := (Ksub_eq_wallSum i hx θ).mp hθK
  obtain ⟨Δj, hΔj, hΔjθ⟩ := (Ksub_eq_wallSum j hxs θ).mp hθK
  have hwall : Δi.image (foldWalls i r) = Δj.image (foldWalls j s) :=
    image_foldWalls_eq_of_wallSum_eq hx hxs hΔi hΔj (by rw [← hΔiθ, ← hΔjθ])
  have hr' : r' = flipSet r Δi := by
    have hmem : x' ∈ Dvor i (flipSet r Δi) := by
      rw [← hθ, hΔiθ, ← actX_image_Dvor i r Δi]
      exact ⟨x, hx, rfl⟩
    exact (Dvor_eq_of_mem hmem hx').symm
  have hs' : s' = flipSet s Δj := by
    have hmem : x' ∈ Dvor j (flipSet s Δj) := by
      rw [← hθ, hΔjθ, ← actX_image_Dvor j s Δj]
      exact ⟨x, hxs, rfl⟩
    exact (Dvor_eq_of_mem hmem hxs').symm
  rw [hr', hs']
  unfold transMat
  rw [foldDrR_flipSet_eq_psiR i r Δi, foldDrR_flipSet_eq_psiR j s Δj, hwall]
  set U := psiR (Δj.image (foldWalls j s)) with hUdef
  have hU : IsUnit U.det := isUnit_det_psiR _
  rw [Matrix.mul_assoc (coordPermMat j) (foldNr j * (foldDrR j s * U))
    ((foldNr i * (foldDrR i r * U))⁻¹)]
  rw [← Matrix.mul_assoc (foldNr j) (foldDrR j s) U,
    ← Matrix.mul_assoc (foldNr i) (foldDrR i r) U]
  rw [mul_mul_inv_mul (foldNr j * foldDrR j s) (foldNr i * foldDrR i r) U hU]
  simp only [Matrix.mul_assoc]

/-! ### A common lift of a transition point

Every point of the transition source is the value of the chart `i` at a class whose lift lies in
**both** the Voronoi piece of the source class and that of the target class. -/

theorem transPieceLift_common (i j : Fin 98) {z : Work.FoldInst.E4}
    (hz : z ∈ Work.RTOwed.Trans i j) :
    ∃ (r : Fin (foldCodim i) → Bool) (s : Fin (foldCodim j) → Bool) (x : Xbar),
      x ∈ Dvor i r ∧ x ∈ Dvor j s ∧ z = foldTheta i r ↑x.2 := by
  rw [Trans, OpenPartialHomeomorph.trans_source] at hz
  obtain ⟨hzT, hzS⟩ := hz
  rw [OpenPartialHomeomorph.symm_source] at hzT
  have hps : (foldChart i).symm z ∈ (foldChart i).source := by
    have hmem : (foldChart i).symm z ∈ (foldChart i).symm '' (foldChart i).symm.source :=
      ⟨z, hzT, rfl⟩
    rwa [OpenPartialHomeomorph.image_source_eq_target, OpenPartialHomeomorph.symm_target] at hmem
  rw [foldChart_source] at hps hzS
  obtain ⟨r, hp⟩ := Set.mem_iUnion.mp hps
  obtain ⟨x, hxr, hx⟩ := Set.mem_image _ _ _ |>.mp hp
  obtain ⟨s, hq⟩ := Set.mem_iUnion.mp hzS
  obtain ⟨y, hys, hy⟩ := Set.mem_image _ _ _ |>.mp hq
  have hrel : rel x y := Quotient.eq.mp (hx.trans hy.symm)
  have hyD : y ∈ ⋃ r : Fin (foldCodim i) → Bool, Dvor i r :=
    mem_foldC_of_rel_dvor i (Set.mem_iUnion.mpr ⟨r, hxr⟩) hrel
  obtain ⟨r', hx'r'⟩ := Set.mem_iUnion.mp hyD
  refine ⟨r', s, y, hx'r', hys, ?_⟩
  have hval : (foldChart i) (mk x) = z := by
    rw [hx]
    exact OpenPartialHomeomorph.right_inv (foldChart i) hzT
  rw [← hval, show mk x = mk y from hx.trans hy.symm]
  exact foldChart_apply i r' y hx'r'

/-! ### The cells carrying a fixed transition matrix -/

/-- The union of the cells `Dvor i r ∩ Dvor j s` of the two fold decompositions whose transition
matrix is `B`. -/
def CellMatSet (i j : Fin 98) (B : Matrix (Fin 5) (Fin 5) ℝ) : Set Xbar :=
  {n | ∃ (r : Fin (foldCodim i) → Bool) (s : Fin (foldCodim j) → Bool),
        n ∈ Dvor i r ∧ n ∈ Dvor j s ∧ transMat i j r s = B}

/-- `CellMatSet` is a union of finitely many cells, hence open. -/
theorem isOpen_cellMatSet (i j : Fin 98) (B : Matrix (Fin 5) (Fin 5) ℝ) :
    IsOpen (CellMatSet i j B) := by
  have hset : CellMatSet i j B =
      ⋃ (p : (Fin (foldCodim i) → Bool) × (Fin (foldCodim j) → Bool)),
        if transMat i j p.1 p.2 = B then Dvor i p.1 ∩ Dvor j p.2 else ∅ := by
    ext n
    constructor
    · rintro ⟨r, s, hr, hs, hB⟩
      exact Set.mem_iUnion.mpr ⟨(r, s), by rw [ite_eq_left hB]; exact ⟨hr, hs⟩⟩
    · intro h
      obtain ⟨p, hp⟩ := Set.mem_iUnion.mp h
      by_cases hB : transMat i j p.1 p.2 = B
      · rw [ite_eq_left hB] at hp
        exact ⟨p.1, p.2, hp.1, hp.2, hB⟩
      · rw [ite_eq_right hB] at hp
        exact absurd hp (Set.notMem_empty p)
  rw [hset]
  refine isOpen_iUnion fun p => ?_
  by_cases hB : transMat i j p.1 p.2 = B
  · rw [ite_eq_left hB]
    exact (isOpen_Dvor i p.1).inter (isOpen_Dvor j p.2)
  · rw [ite_eq_right hB]
    exact isOpen_empty

/-- **`CellMatSet` is saturated for the identification relation**: cells of one class that share a
point carry the same matrix (`transMat_eq_of_rel`). -/
theorem rel_mem_cellMatSet {i j : Fin 98} {B : Matrix (Fin 5) (Fin 5) ℝ} {n n' : Xbar}
    (hn : n ∈ CellMatSet i j B) (h : rel n n') : n' ∈ CellMatSet i j B := by
  obtain ⟨r, s, hr, hs, hB⟩ := hn
  have hn'i : n' ∈ ⋃ r : Fin (foldCodim i) → Bool, Dvor i r :=
    mem_foldC_of_rel_dvor i (Set.mem_iUnion.mpr ⟨r, hr⟩) h
  have hn'j : n' ∈ ⋃ s : Fin (foldCodim j) → Bool, Dvor j s :=
    mem_foldC_of_rel_dvor j (Set.mem_iUnion.mpr ⟨s, hs⟩) h
  obtain ⟨r', hr'⟩ := Set.mem_iUnion.mp hn'i
  obtain ⟨s', hs'⟩ := Set.mem_iUnion.mp hn'j
  exact ⟨r', s', hr', hs', by rw [transMat_eq_of_rel hr hs hr' hs' h, hB]⟩

/-- The image in `M̄` of the union of the cells with a fixed matrix is open. -/
theorem isOpen_image_cellMatSet (i j : Fin 98) (B : Matrix (Fin 5) (Fin 5) ℝ) :
    IsOpen (mk '' CellMatSet i j B) := by
  rw [isOpen_quotient_iff_preimage]
  have hpre : mk ⁻¹' (mk '' CellMatSet i j B) = CellMatSet i j B := by
    ext n
    constructor
    · intro hn
      obtain ⟨n₀, hn₀, heq⟩ := hn
      exact rel_mem_cellMatSet hn₀ (Quotient.eq.mp heq)
    · intro hn
      exact ⟨n, hn, rfl⟩
  rw [hpre]
  exact isOpen_cellMatSet i j B

/-! ### The local Möbius model -/

theorem foldTrans_local (i j : Fin 98) {z : Work.FoldInst.E4}
    (hz : z ∈ Work.RTOwed.Trans i j) :
    ∃ (V : Set Work.FoldInst.E4) (B : Matrix (Fin 5) (Fin 5) ℝ), IsOpen V ∧ z ∈ V ∧
      Work.HypModel.IsLorentzMat B ∧
      ∀ z' ∈ V ∩ Work.RTOwed.Trans i j,
        Work.RTOwed.transMap i j z' = Work.HypModel.mobius B z' := by
  obtain ⟨r, s, x, hxr, hxs, hzval⟩ := transPieceLift_common i j hz
  refine ⟨(foldChart i) '' (mk '' CellMatSet i j (transMat i j r s) ∩ (foldChart i).source),
    transMat i j r s, ?_, ?_, transMat_isLorentz i j r s, ?_⟩
  · exact (foldChart i).isOpen_image_of_subset_source
      ((isOpen_image_cellMatSet i j _).inter (foldChart i).open_source) Set.inter_subset_right
  · refine ⟨mk x, ⟨?_, ?_⟩, ?_⟩
    · exact ⟨x, ⟨r, s, hxr, hxs, rfl⟩, rfl⟩
    · rw [foldChart_source]
      exact Set.mem_iUnion.mpr ⟨r, ⟨x, hxr, rfl⟩⟩
    · rw [foldChart_apply i r x hxr]
      exact hzval.symm
  · intro z' hz'
    obtain ⟨p, hp, hpz⟩ := hz'.1
    obtain ⟨hpmem, hpsrc⟩ := hp
    obtain ⟨n, hn, hnmk⟩ := hpmem
    obtain ⟨r', s', hr', hs', hB⟩ := hn
    have hsymm : (foldChart i).symm z' = p := by
      rw [← hpz]
      exact OpenPartialHomeomorph.left_inv (foldChart i) hpsrc
    have hzi : (foldChart i) (mk n) = z' := by rw [hnmk]; exact hpz
    have hzj : (foldChart j) (mk n) = foldTheta j s' ↑n.2 := foldChart_apply j s' n hs'
    calc Work.RTOwed.transMap i j z'
        = (foldChart j) ((foldChart i).symm z') := rfl
      _ = (foldChart j) (mk n) := by rw [hsymm, hnmk]
      _ = Work.HypModel.mobius (Work.RTOwed.transMat i j r' s') ((foldChart i) (mk n)) :=
            foldTrans_piece i j r' s' hr' hs'
      _ = Work.HypModel.mobius (Work.RTOwed.transMat i j r' s') z' := by rw [hzi]
      _ = Work.HypModel.mobius (Work.RTOwed.transMat i j r s) z' := by rw [hB]

/-! ### The named hypothesis of the area is inhabited

`Work.RTOwed.FoldTransLocal` is the area's name for the pointwise statement proved above; its single
field `localModel` is exactly `foldTrans_local` (with the two fold classes and the point as
arguments).  A colleague plugging the hole of `Submission.Work.RTOwed.foldTransLocal` should note
that the present module declares `Work.RTOwed.foldTrans_local` with the same statement as
`Submission.Work.RTOwed.FoldTransLocalApply` but *without* the extra hypothesis argument, so the two
modules cannot be imported together as they stand. -/
set_option linter.unusedVariables false in
theorem foldTransLocal_inhabited : Work.RTOwed.FoldTransLocal :=
  ⟨fun i j z hz => foldTrans_local i j hz⟩

end Work.RTOwed
