import Mathlib
import Submission.Work.Thom.ATools
import Submission.Work.Thom.Glue
import Submission.Work.Thom.Relocate.TrivProductHomeo
import Submission.Work.Thom.LineThomClass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

/-!
# Local Thom data over a chart, from the Thom class of the trivial bundle

The **producer of `Work.Thom.LocalThom` data** for this chapter.  Let `Z → B` be a real bundle with
model fibre `F`, let `U ⊆ B` be contained in a chart `Z.baseSet i`, and let `X = Z.TotalSpace` with
`X|_U = Z.proj ⁻¹' U` the part of the total space over `U`.  Then the restricted Thom pair
`(X|_U, X|_U∖0)` carries a class `τ` for which the *local Thom map*

  `H^k(U;ℤ) → H^{k+n}(X|_U, X|_U∖0)`,   `x ↦ π^*(x) ⌣ τ`

is bijective in every degree — a **local Thom class** of `Z` over `U`.

The construction transports the Thom class of the **trivial** bundle `U × F → U` along the chart
homeomorphism of the piece, in two steps:

  `E₀.TotalSpace --Work.Thom.trivProductHomeo--> ↥U × F --(chart of Z)⁻¹--> ↥(Z.proj ⁻¹' U)`,

both steps being homeomorphisms of pairs (carrying `E₀∖0` onto `U × (F∖0)`, respectively onto
`X|_U∖0`) that commute with the projections to `↥U`.  The transport of the bijectivity of the cup
map along such a homeomorphism of pairs is `Work.Thom.cupMap_transfer_fwdA`
(`Submission/Work/Thom/ATools.lean`, the copy of `Work.Thom.cupMap_transfer_fwd` that lives in the
same island of the workspace as `Submission/Work/TangentClasses/` and
`Submission/Work/Thom/Interface.lean`).

Main results:

* `Work.Thom.nonempty_localThom_of_subset_baseSet_of_trivial` — **the producer**, conditional only
  on a Thom class of the *trivial* bundle `U × F → U` of the same rank: the exact shape in which
  the classical proof supplies the local step of the Mayer–Vietoris induction;
* `Work.Thom.nonempty_localThom_of_line` — the **line-bundle case made unconditional**
  (`F = ℝ`, `n = 1`), from `Work.Thom.nonempty_thomClass_trivial_line`;
* `Work.Thom.pieceChartA`, `pieceChartA_apply`, `pieceChartA_symm_apply`,
  `projFstA'_comp_pieceChartA` — the chart homeomorphism of a piece of the total space over a base
  set lying in a chart, and its formulas;
* `Work.Thom.coordChange_indexAt_eq_zero_iffA`,
  `Work.Thom.coordChange_indexAt_comp_eq_zero_iffA` — clean copies of the two coordinate-change
  kernel computations.
-/

open Work.TangentClasses

namespace Work.Thom

open CategoryTheory

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-! ## Two coordinate-change computations -/

/-- `x ↦ Z.coordChange (Z.indexAt x) i x` is injective (it is inverted by the transition back). -/
theorem coordChange_indexAt_eq_zero_iffA (Z : RealBundle B F ι) (i : ι)
    (x : B) (hx : x ∈ Z.baseSet i) (v : F) :
    Z.coordChange (Z.indexAt x) i x v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have h1 : Z.coordChange (Z.indexAt x) (Z.indexAt x) x v = v :=
      Z.coordChange_self (Z.indexAt x) x (Z.mem_baseSet_at x) v
    have h2 := Z.coordChange_comp (Z.indexAt x) i (Z.indexAt x) x
      ⟨⟨Z.mem_baseSet_at x, hx⟩, Z.mem_baseSet_at x⟩ v
    rw [h1] at h2
    rw [h, map_zero] at h2
    exact h2.symm
  · intro h; rw [h, map_zero]

/-! ## The chart homeomorphism of a piece -/

/-- The projection `B × F → B` of a product. -/
def projFstA' (B : Type) [TopologicalSpace B] {F : Type} [TopologicalSpace F] : C(B × F, B) :=
  ⟨Prod.fst, continuous_fst⟩

/-- **The chart homeomorphism of the piece over `U ⊆ Z.baseSet i` with `U × F`.** -/
def pieceChartA (Z : RealBundle B F ι) (i : ι) (U : Set B) (hU : U ⊆ Z.baseSet i) :
    ↥(Z.proj ⁻¹' U) ≃ₜ (↥U × F) :=
  (Z.localTriv i).preimageHomeomorph hU

/-- The chart homeomorphism, on points. -/
theorem pieceChartA_apply (Z : RealBundle B F ι) (i : ι) (U : Set B) (hU : U ⊆ Z.baseSet i)
    (p : ↥(Z.proj ⁻¹' U)) :
    pieceChartA Z i U hU p =
      (⟨Z.proj p.1, p.2⟩, Z.coordChange (Z.indexAt p.1.1) i p.1.1 p.1.2) := by
  rw [pieceChartA, Bundle.Trivialization.preimageHomeomorph_apply]
  rw [VectorBundleCore.localTriv_apply]

/-- The projection of the piece, read through the chart, is the projection of the product. -/
theorem projFstA'_comp_pieceChartA (Z : RealBundle B F ι) (i : ι) (U : Set B)
    (hU : U ⊆ Z.baseSet i) :
    (projFstA' ↥U (F := F)).comp (pieceChartA Z i U hU : C(↥(Z.proj ⁻¹' U), ↥U × F))
      = pieceProj Z U := by
  apply ContinuousMap.ext
  intro p
  exact congrArg Prod.fst (pieceChartA_apply Z i U hU p)

/-! ## The producer -/

/-- **The local Thom class of a bundle over a chart of a trivialisable piece, from the Thom class
of the trivial bundle.** -/
theorem nonempty_localThom_of_subset_baseSet_of_trivial {n : ℕ}
    (Z : RealBundle B F ι) (i : ι) (U : Set B) (hU : U ⊆ Z.baseSet i)
    (hT : Nonempty (ThomClass (RealBundle.trivial ↥U F PUnit) n)) :
    Nonempty (LocalThom Z n U) := by
  obtain ⟨T⟩ := hT
  -- Step 1: from the trivial bundle over `↥U` to the product `↥U × F`
  have hf₁ : ∀ p ∈ zeroComplement (RealBundle.trivial ↥U F PUnit),
      trivProductHomeo ↥U F PUnit p ∈ {q : ↥U × F | q.2 ≠ 0} :=
    fun p hp => (trivProductHomeo_zeroComplement ↥U F PUnit p).mp hp
  have hπ₁ : (projFstA' ↥U (F := F)).comp
        (trivProductHomeo ↥U F PUnit :
          C((RealBundle.trivial ↥U F PUnit).TotalSpace, ↥U × F))
      = bundleProj (RealBundle.trivial ↥U F PUnit) := by
    apply ContinuousMap.ext
    intro p
    exact congrArg Prod.fst (trivProductHomeo_apply ↥U F PUnit p)
  obtain ⟨σ, -, hσ⟩ := cupMap_transfer_bwdA
    (trivProductHomeo ↥U F PUnit :
      C((RealBundle.trivial ↥U F PUnit).TotalSpace, ↥U × F))
    {q : ↥U × F | q.2 ≠ 0} (zeroComplement (RealBundle.trivial ↥U F PUnit)) hf₁
    (fun m => bijective_relCohMap_of_homeomorphA
      (zeroComplement (RealBundle.trivial ↥U F PUnit)) {q : ↥U × F | q.2 ≠ 0}
      (trivProductHomeo ↥U F PUnit)
      (fun p => trivProductHomeo_zeroComplement ↥U F PUnit p) ℤ m)
    (projFstA' ↥U (F := F)) (bundleProj (RealBundle.trivial ↥U F PUnit)) hπ₁ n T.τ T.isThom
  -- Step 2: from the product to the piece of `Z`, along the chart of `Z`
  have he₂ : ∀ p : ↥(Z.proj ⁻¹' U), p ∈ (Subtype.val : ↥(Z.proj ⁻¹' U) → Z.TotalSpace) ⁻¹'
        zeroComplement Z ↔ pieceChartA Z i U hU p ∈ {q : ↥U × F | q.2 ≠ 0} := by
    intro p
    rw [Set.mem_preimage, mem_zeroComplement]
    show (show F from p.1.2) ≠ 0 ↔ (pieceChartA Z i U hU p).2 ≠ 0
    rw [pieceChartA_apply]
    exact (coordChange_indexAt_eq_zero_iffA Z i p.1.1 (hU p.2) p.1.2).not.symm
  exact ⟨⟨(relCohMap (pieceChartA Z i U hU : C(↥(Z.proj ⁻¹' U), ↥U × F))
      ((Subtype.val : ↥(Z.proj ⁻¹' U) → Z.TotalSpace) ⁻¹' zeroComplement Z)
      {q : ↥U × F | q.2 ≠ 0} (fun p hp => (he₂ p).mp hp) ℤ n).hom σ,
    cupMap_transfer_fwdA (pieceChartA Z i U hU : C(↥(Z.proj ⁻¹' U), ↥U × F))
      {q : ↥U × F | q.2 ≠ 0}
      ((Subtype.val : ↥(Z.proj ⁻¹' U) → Z.TotalSpace) ⁻¹' zeroComplement Z)
      (fun p hp => (he₂ p).mp hp)
      (fun m => bijective_relCohMap_of_homeomorphA
        ((Subtype.val : ↥(Z.proj ⁻¹' U) → Z.TotalSpace) ⁻¹' zeroComplement Z)
        {q : ↥U × F | q.2 ≠ 0} (pieceChartA Z i U hU) he₂ ℤ m)
      (projFstA' ↥U (F := F)) (pieceProj Z U)
      (projFstA'_comp_pieceChartA Z i U hU) n σ hσ⟩⟩

/-- **Local Thom data over a chart of a real line bundle** (the unconditional rank-one case). -/
theorem nonempty_localThom_of_line {ι : Type} (Z : RealBundle B ℝ ι) (i : ι)
    (U : Set B) (hU : U ⊆ Z.baseSet i) :
    Nonempty (LocalThom Z 1 U) :=
  nonempty_localThom_of_subset_baseSet_of_trivial Z i U hU
    (nonempty_thomClass_trivial_line (B := ↥U) (ι₀ := PUnit))

end

end Work.Thom
