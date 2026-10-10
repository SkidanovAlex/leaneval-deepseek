import Mathlib
import Submission.Work.Twist.Defs
import Submission.Work.Twist.away_chart_mvPolynomial
import Submission.Work.Twist.away_chart_mvPolynomial_X

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Twist

open CategoryTheory AlgebraicGeometry
open Work.Twist
open MvPolynomial HomogeneousLocalization

set_option linter.style.haveILetI false

noncomputable section

/-! ## Auxiliary lemmas for the dimension of `ℙⁿ`

Everything here is stated for the standard graded polynomial ring `𝕜[X₀,…,Xₙ]`, i.e. for
`𝒜 = MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜 = Work.Twist.stdGrading 𝕜 n`. -/

/-- **`ringKrullDim` is invariant under ring isomorphisms.**  Both directions are
`ringKrullDim_le_iff_height_le` together with the invariance of the height of a prime ideal under a
ring isomorphism (`RingEquiv.height_map`, `RingEquiv.height_comap`). -/
lemma ringKrullDim_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    ringKrullDim R = ringKrullDim S := by
  refine le_antisymm ?_ ?_
  · rw [ringKrullDim_le_iff_height_le]
    intro p hp
    haveI := hp
    rw [← RingEquiv.height_map e p]
    exact Ideal.height_le_ringKrullDim_of_isPrime
  · rw [ringKrullDim_le_iff_height_le]
    intro p hp
    haveI := hp
    rw [← RingEquiv.height_comap e p]
    exact Ideal.height_le_ringKrullDim_of_isPrime

/-- **A chart meeting an irreducible closed set bounds its coheight.**  If `f : U → X` is an open
embedding and the irreducible closed set `Z ⊆ X` meets the image of `f`, then the coheight of `Z`
in `X` is at most the topological Krull dimension of `U`.

This is the locality ingredient of the dimension computation: `Topology.IsOpenEmbedding.coheight_map`
computes the coheight of `Z` as the coheight of the corresponding irreducible closed subset of `U`
(`TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding`), and the coheight of an element of
a preorder is at most its Krull dimension (`Order.coheight_le_krullDim`). -/
theorem coheight_le_topologicalKrullDim_of_isOpenEmbedding {U X : Type*} [TopologicalSpace U]
    [TopologicalSpace X] {f : U → X} (hf : Topology.IsOpenEmbedding f)
    {Z : TopologicalSpace.IrreducibleCloseds X} (hZ : (f ⁻¹' (Z : Set X)).Nonempty) :
    (Order.coheight Z : WithBot ℕ∞) ≤ topologicalKrullDim U := by
  have hmap : TopologicalSpace.IrreducibleCloseds.map f hf.continuous
      ((TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding f hf).symm ⟨Z, hZ⟩) = Z :=
    congrArg Subtype.val ((TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding f hf)
      |>.apply_symm_apply ⟨Z, hZ⟩)
  calc (Order.coheight Z : WithBot ℕ∞)
      = (Order.coheight (TopologicalSpace.IrreducibleCloseds.map f hf.continuous
          ((TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding f hf).symm
            ⟨Z, hZ⟩)) : WithBot ℕ∞) := by rw [hmap]
    _ = (Order.coheight ((TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding f hf).symm
          ⟨Z, hZ⟩) : WithBot ℕ∞) := by rw [Topology.IsOpenEmbedding.coheight_map hf]
    _ ≤ Order.krullDim (TopologicalSpace.IrreducibleCloseds U) := Order.coheight_le_krullDim _
    _ = topologicalKrullDim U := rfl

/-- **The charts `D₊(X_i)` cover `ℙⁿ`.**  The variables `X_i` generate `𝕜[X₀,…,Xₙ]` as an algebra
over the constants `𝒜 0`, so `Proj.iSup_basicOpen_eq_top'` applies to them. -/
lemma iSup_basicOpen_X_eq_top (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    (⨆ i : Fin (n + 1), Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)
      (MvPolynomial.X i)) = ⊤ := by
  refine Proj.iSup_basicOpen_eq_top' _ _
    (fun i => ⟨1, MvPolynomial.isHomogeneous_X _ i⟩) ?_
  let S := Algebra.adjoin (↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜 0))
    (Set.range (MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) 𝕜))
  have hX : ∀ i : Fin (n + 1), MvPolynomial.X i ∈ S :=
    fun i => Algebra.subset_adjoin (Set.mem_range_self i)
  have hC : ∀ a : 𝕜, MvPolynomial.C a ∈ S := by
    intro a
    have hmem : MvPolynomial.C a ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜 0 :=
      (MvPolynomial.mem_homogeneousSubmodule 0 _).mpr (MvPolynomial.isHomogeneous_C _ a)
    simpa using Subalgebra.algebraMap_mem S ⟨MvPolynomial.C a, hmem⟩
  show S = ⊤
  refine le_antisymm le_top ?_
  rintro p -
  induction p using MvPolynomial.induction_on with
  | C a => exact hC a
  | add p q hp hq => exact Subalgebra.add_mem S hp hq
  | mul_X p i hp => exact Subalgebra.mul_mem S hp (hX i)

/-- **The dimension of the standard chart `D₊(X_i)` of `ℙⁿ`.**  `D₊(X_i) ≅ Spec (A⁰_{X_i})` with
`A⁰_{X_i} ≅ 𝕜[y₁,…,yₙ]` (`Work.Twist.away_chart_mvPolynomial_X`), and
`topologicalKrullDim (Spec R) = ringKrullDim R`. -/
lemma topologicalKrullDim_basicOpen_X (𝕜 : Type) [Field 𝕜] (n : ℕ) (i : Fin (n + 1)) :
    topologicalKrullDim (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)
      (MvPolynomial.X i)) = (n : WithBot ℕ∞) := by
  have hiso := Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)
    (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i) (by norm_num : (0 : ℕ) < 1)
  rw [IsHomeomorph.topologicalKrullDim_eq ⇑(hiso.hom.homeomorph) hiso.hom.homeomorph.isHomeomorph]
  have e : Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜) (MvPolynomial.X i) ≃+*
      MvPolynomial (Fin n) 𝕜 := (away_chart_mvPolynomial_X 𝕜 n i).some
  rw [show topologicalKrullDim (Spec ↧(Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)
        (MvPolynomial.X i)))
      = ringKrullDim (Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)
        (MvPolynomial.X i)) from PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _,
    ringKrullDim_eq_of_ringEquiv e,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
  simp

/-- **The dimension of `ℙⁿ_𝕜`.**  `ℙⁿ_𝕜 = Proj 𝕜[X₀,…,Xₙ]` has topological Krull dimension `n`.
This is one of the three conjuncts of `ProjectiveModelGap 𝕜 n`
(`Submission/Work/PointlessIndexFive/Model.lean`), and `curveModel_projectiveSpace_one` shows that
the three conjuncts at `n = 1` are exactly what is missing for a `CurveModel 𝕜`.

Ingredients, all available: `Proj.iSup_basicOpen_eq_top` (the open cover by the charts
`D₊(X_i)`), `Proj.basicOpenIsoSpec` (`D₊(X_i) ≅ Spec (Away 𝒜 X_i)`),
`Twist.away_chart_mvPolynomial` (`Away 𝒜 X_i ≅ 𝕜[y₁,…,yₙ]`, hence
`ringKrullDim = ringKrullDim (MvPolynomial (Fin n) 𝕜)`),
`MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite`,
`ringKrullDim_eq_zero_of_field`, `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`, and the
locality of `topologicalKrullDim` for an open cover, which follows from
`Topology.IsOpenEmbedding.coheight_map` (`Topology/KrullDimension.lean`), `krullDim_eq_iSup_coheight`
and the fact that the closure in `X` of an irreducible closed subset of a chart it meets is computed
in the chart's generic point.  Note `topologicalKrullDim` lands in `WithBot ℕ∞`, so the statement is
`= (n : WithBot ℕ∞)`. -/
theorem topologicalKrullDim_projectiveSpace (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    topologicalKrullDim (Work.PointlessIndexFive.projectiveSpace 𝕜 n) = n := by
  classical
  have hcover : (⨆ i : Fin (n + 1),
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)
        (MvPolynomial.X i)) = ⊤ := iSup_basicOpen_X_eq_top 𝕜 n
  have hchart := topologicalKrullDim_basicOpen_X 𝕜 n
  refine le_antisymm ?_ ?_
  · -- Upper bound: every irreducible closed subset of `ℙⁿ` meets a chart of dimension `n`.
    change Order.krullDim (TopologicalSpace.IrreducibleCloseds
      ↥(Work.PointlessIndexFive.projectiveSpace 𝕜 n)) ≤ (n : WithBot ℕ∞)
    rw [Order.krullDim_eq_iSup_coheight]
    refine iSup_le fun Z => ?_
    obtain ⟨z, hz⟩ := Z.2.nonempty
    have hzmem : z ∈ (⨆ i : Fin (n + 1),
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)
          (MvPolynomial.X i)) := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hzmem
    have hZne : ((Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝕜)
        (MvPolynomial.X i)).ι ⁻¹'
          (Z : Set ↥(Work.PointlessIndexFive.projectiveSpace 𝕜 n))).Nonempty :=
      ⟨⟨z, hi⟩, hz⟩
    refine (coheight_le_topologicalKrullDim_of_isOpenEmbedding
      (Scheme.Hom.isOpenEmbedding (Proj.basicOpen (MvPolynomial.homogeneousSubmodule
        (Fin (n + 1)) 𝕜) (MvPolynomial.X i)).ι) hZne).trans ?_
    exact le_of_eq (hchart i)
  · -- Lower bound: one chart already has dimension `n`.
    rw [← hchart 0]
    exact (Scheme.Hom.isOpenEmbedding (Proj.basicOpen (MvPolynomial.homogeneousSubmodule
      (Fin (n + 1)) 𝕜) (MvPolynomial.X 0)).ι).isInducing.topologicalKrullDim_le

end

end Work.Twist
