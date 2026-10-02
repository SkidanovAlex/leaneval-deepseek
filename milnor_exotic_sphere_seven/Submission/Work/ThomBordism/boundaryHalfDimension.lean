import Mathlib
import Submission.Work.ThomBordism.boundaryDualityExplicit
import Submission.Work.ThomBordism.boundaryAssembly
import Submission.Work.ThomBordism.bdryRatCohFinite
import Submission.Work.ThomBordism.bdryMidFormNondegenerate
import Submission.Work.ThomBordism.boundaryMaximalIsotropic
import Submission.Work.Bordism.Middle
import Submission.Work.Bordism.LesImage
import Submission.Work.Cohomology.PairSequence
import Submission.Work.ThomBordism.nondegenerate_midForm_of_good

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Middle-degree Lefschetz duality for the pair `(W, ∂W)`: the algebraic reduction

`Work.ThomBordism.boundaryHalfDimension` (at the bottom of this file) is `Work.Bordism.HalfDimension 4`
for the explicit boundary bordism `(∂W, ∂w) ⟶ (∅, 0)` of a `NullBordismFamily` — the crux of
`Work.ThomBordism.BoundarySigma`.

This file contains the **algebraic reduction** of that statement to the two inputs that are *not*
linear algebra:

*(both are now proved: the non-degeneracy is `Work.ThomBordism.bdryMidFormNondegenerate`,
`Submission/Work/ThomBordism/bdryMidFormNondegenerate.lean`, and the crux is
`Work.ThomBordism.boundaryMaximalIsotropic`,
`Submission/Work/ThomBordism/boundaryMaximalIsotropic.lean` — which reduces the crux to middle
Lefschetz duality for the pair `(W, ∂W)`, `Work.ThomBordism.lefschetzDualityBdry`.  So
`boundaryHalfDimension` below is unconditional.)*


* `Work.ThomBordism.bdryMidFormNondegenerate` (`Submission/Work/ThomBordism/bdryMidFormNondegenerate.lean`)
  — middle-degree Poincaré duality for the closed oriented `8`-manifold `∂W`, i.e. non-degeneracy of
  its middle intersection form;
* `Work.ThomBordism.BoundaryMaximalIsotropic` (`Submission/Work/ThomBordism/boundaryMaximalIsotropic.lean`)
  — the *maximality* half of middle-degree Lefschetz duality for the pair `(W, ∂W)`: every class
  orthogonal to `K = image(H⁴(W;ℚ) → H⁴(∂W;ℚ))` lies in `K` (the *isotropy* half `K ⊆ Kᗮ` is the
  theorem `Work.ThomBordism.bdryK_isotropic`), together with
* `Work.ThomBordism.bdryRatCohFinite` (proved, `Submission/Work/ThomBordism/bdryRatCohFinite.lean`)
  — finite dimensionality of `H⁴(∂W;ℚ)`.

The reduction is the classical "half lives on each side" dimension count, in the following form.
Write `V = H⁴(∂W;ℚ)`, `B = Work.ThomBordism.bdryFormBilin W` (the middle intersection form of
`∂W`, whose quadratic form is `Work.Bordism.midForm (bdryClosed W)`) and `K = Work.ThomBordism.bdryK W`
(the image of the restriction). Then

* `B` is symmetric (`bdryFormBilin_symm`, degree `4` of an `8`-manifold);
* `B` is non-degenerate (`bdryFormBilin_nondegenerate`, from `bdryMidFormNondegenerate`);
* `K` is isotropic for `B` (`bdryK_isotropic`, already in the workspace);
* `K` is maximal isotropic for `B` (the crux `BoundaryMaximalIsotropic`).

The abstract lemma `two_mul_finrank_of_isLagrangian` (no topology: a non-degenerate symmetric form
on a finite dimensional space) then gives `2 · dim K = dim V`, and the bookkeeping
(`middleMap = (iM*, iN*)` with `iN` the empty map, whose target `H⁴(∅;ℚ)` is a subsingleton) turns
this into `Work.Bordism.HalfDimension 4`.

## Contents (all complete)

* `two_mul_finrank_of_isLagrangian`, `submoduleProdLinearEquiv`, `finrank_submodule_prod`,
  `finrank_submodule_prod_bot`, `finrank_range_prod_eq_of_eq_zero`, `finrank_prod_of_subsingleton`
  — the linear algebra;
* `bdryFormBilin_symm`, `bdryFormBilin_nondegenerate` — the two facts about the middle form of
  `∂W` used by the count;
* `boundaryHalfDimension_of_maximalIsotropic` — the reduction proper;
* `boundaryHalfDimension` — the requested statement (assembled from the two named inputs).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology
open scoped TensorProduct

namespace Work.ThomBordism

noncomputable section

/-! ## The abstract Lagrangian dimension count -/

/-- **A nondegenerate symmetric bilinear form on a finite dimensional space has no Lagrangian of
half dimension other than the orthogonal self-complementary ones**: if `K` is totally isotropic
(`hiso`) and maximal isotropic (`hmax`), then `2 dim K = dim V`. -/
theorem two_mul_finrank_of_isLagrangian {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [FiniteDimensional 𝕜 V] (B : V →ₗ[𝕜] V →ₗ[𝕜] 𝕜) (hsym : ∀ x y, B x y = B y x)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (K : Submodule 𝕜 V)
    (hiso : ∀ x ∈ K, ∀ y ∈ K, B x y = 0)
    (hmax : ∀ y, (∀ x ∈ K, B x y = 0) → y ∈ K) :
    2 * Module.finrank 𝕜 K = Module.finrank 𝕜 V := by
  let φ : V →ₗ[𝕜] (K →ₗ[𝕜] 𝕜) := (Submodule.dualRestrict K).comp B.flip
  have hφ : ∀ y (x : K), φ y x = B x.1 y := by
    intro y x
    simp only [φ, LinearMap.comp_apply, Submodule.dualRestrict_apply, LinearMap.flip_apply]
  have hker : LinearMap.ker φ = K := by
    ext y
    rw [LinearMap.mem_ker]
    constructor
    · intro h
      refine hmax y (fun x hx => ?_)
      have h1 := congrArg (fun (g : K →ₗ[𝕜] 𝕜) => g ⟨x, hx⟩) h
      simpa only [hφ, LinearMap.zero_apply] using h1
    · intro hy
      ext x
      rw [hφ, LinearMap.zero_apply]
      exact hiso x x.2 y hy
  have hBsurj : Function.Surjective B.flip := by
    have hinj : Function.Injective B.flip := by
      intro y y' h
      have hsub : B.flip (y - y') = 0 := by rw [map_sub, h, sub_self]
      have hz : y - y' = 0 := hnd (y - y') (fun z => by
        have h1 := congrArg (fun (g : V →ₗ[𝕜] 𝕜) => g z) hsub
        simp only [LinearMap.zero_apply, LinearMap.flip_apply] at h1
        rw [← hsym z (y - y')]
        exact h1)
      exact sub_eq_zero.mp hz
    have hfin : Module.finrank 𝕜 V = Module.finrank 𝕜 (V →ₗ[𝕜] 𝕜) :=
      (Subspace.dual_finrank_eq).symm
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinj
  have hφsurj : Function.Surjective φ :=
    (Subspace.dualRestrict_surjective (W := K)).comp hBsurj
  have h1 : Module.finrank 𝕜 (LinearMap.range φ) + Module.finrank 𝕜 (LinearMap.ker φ)
      = Module.finrank 𝕜 V := LinearMap.finrank_range_add_finrank_ker φ
  rw [LinearMap.range_eq_top.mpr hφsurj, hker, finrank_top,
    Subspace.dual_finrank_eq] at h1
  omega

/-! ## `finrank` of `Submodule.prod` -/

/-- `p.prod q` is linearly equivalent to `p × q`. -/
def submoduleProdLinearEquiv {R M M' : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid M']
    [Module R M] [Module R M'] (p : Submodule R M) (q : Submodule R M') :
    ↥(p.prod q) ≃ₗ[R] ↥p × ↥q where
  toFun z := (⟨z.1.1, (Submodule.mem_prod.mp z.2).1⟩, ⟨z.1.2, (Submodule.mem_prod.mp z.2).2⟩)
  invFun w := ⟨(w.1.1, w.2.1), Submodule.mem_prod.mpr ⟨w.1.2, w.2.2⟩⟩
  left_inv z := by ext <;> rfl
  right_inv w := by ext <;> rfl
  map_add' z z' := by ext <;> rfl
  map_smul' c z := by ext <;> rfl

/-- `finrank` of a product of submodules is the sum. -/
theorem finrank_submodule_prod {R M M' : Type*} [Field R] [AddCommGroup M] [AddCommGroup M']
    [Module R M] [Module R M'] [FiniteDimensional R M] [FiniteDimensional R M']
    (p : Submodule R M) (q : Submodule R M') :
    Module.finrank R ↥(p.prod q) = Module.finrank R ↥p + Module.finrank R ↥q := by
  rw [LinearEquiv.finrank_eq (submoduleProdLinearEquiv p q), Module.finrank_prod]

/-- `finrank` of `p.prod ⊥` is the `finrank` of `p`. -/
theorem finrank_submodule_prod_bot {R M M' : Type*} [Field R] [AddCommGroup M] [AddCommGroup M']
    [Module R M] [Module R M'] [FiniteDimensional R M] [FiniteDimensional R M']
    (p : Submodule R M) :
    Module.finrank R ↥(p.prod (⊥ : Submodule R M')) = Module.finrank R ↥p := by
  rw [finrank_submodule_prod (q := (⊥ : Submodule R M')), finrank_bot R M', add_zero]

/-- **The `finrank` of the range of `f.prod g` with `g = 0`**: the second component contributes
nothing. -/
theorem finrank_range_prod_eq_of_eq_zero {R M M₂ M₃ : Type*} [Field R] [AddCommGroup M]
    [AddCommGroup M₂] [AddCommGroup M₃] [Module R M] [Module R M₂] [Module R M₃]
    [FiniteDimensional R M₂] [FiniteDimensional R M₃]
    (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) (hg : g = 0) :
    Module.finrank R ↥(f.prod g).range = Module.finrank R ↥f.range := by
  have hgoal : (f.prod g).range = f.range.prod (⊥ : Submodule R M₃) := by
    have h1 : LinearMap.ker g = ⊤ := LinearMap.ker_eq_top.mpr hg
    have h2 : LinearMap.range g = ⊥ := LinearMap.range_eq_bot.mpr hg
    rw [LinearMap.range_prod_eq (f := f) (g := g) (by rw [h1, sup_top_eq]), h2]
  rw [hgoal, finrank_submodule_prod_bot (M' := M₃)]

/-- **`finrank` of a product with a subsingleton factor**: the second factor contributes nothing. -/
theorem finrank_prod_of_subsingleton {R M M' : Type*} [Field R] [AddCommGroup M] [AddCommGroup M']
    [Module R M] [Module R M'] [Subsingleton M'] :
    Module.finrank R (M × M') = Module.finrank R M := by
  have hbij : Function.Bijective (LinearMap.fst R M M') :=
    ⟨fun a b h => by
      have h1 : a.1 = b.1 := h
      have h2 : a.2 = b.2 := Subsingleton.elim _ _
      exact Prod.ext h1 h2, fun y => ⟨(y, 0), rfl⟩⟩
  exact LinearEquiv.finrank_eq (LinearEquiv.ofBijective _ hbij)
/-! ## The middle intersection form of the boundary -/

/-- **The middle intersection form of `∂W` is symmetric**: degree `4` of the closed `8`-manifold
`∂W` is even, so the graded commutativity of the cup product has sign `+1`
(`Work.ThomBordism.interForm_symm_of_even`), and the rationalisation preserves symmetry. -/
theorem bdryFormBilin_symm {ι : Type} [Fintype ι] {F : ι → Man8} (W : NullBordismFamily ι F) :
    ∀ x y, bdryFormBilin W x y = bdryFormBilin W y x := by
  intro x y
  have hflip : bdryFormBilin W = (bdryFormBilin W).flip := by
    refine Work.SignatureBordism.tensor_bilin_ext (fun a b m n => ?_)
    rw [LinearMap.flip_apply]
    simp only [bdryFormBilin, Work.SignatureBordism.ratInterForm_tmul]
    rw [Work.ThomBordism.interForm_symm_of_even (TopCat.toSSet.obj (TopCat.of (bdrySet W.W))) 4
      (by norm_num) _ m n]
    ring
  conv_lhs => rw [hflip]
  rw [LinearMap.flip_apply]

/-- **Non-degeneracy of the middle form of `∂W`, in bilinear form**: the radical of the associated
bilinear form of `midForm (bdryClosed W)` is trivial. -/
theorem bdryFormBilin_nondegenerate {ι : Type} [Fintype ι] {F : ι → Man8}
    (W : NullBordismFamily ι F)
    (hnd : Work.Bordism.Nondegenerate (Work.Bordism.midForm (k := 4) (bdryClosed W))) :
    ∀ x, (∀ y, bdryFormBilin W x y = 0) → x = 0 := by
  intro x hx
  refine hnd x (fun y => ?_)
  show QuadraticMap.associated (Work.SignatureBordism.quadOfBilin (bdryFormBilin W)) x y = 0
  have h2 : Work.SignatureBordism.quadOfBilin (bdryFormBilin W) (x + y)
      - Work.SignatureBordism.quadOfBilin (bdryFormBilin W) x
      - Work.SignatureBordism.quadOfBilin (bdryFormBilin W) y = 0 := by
    simp only [Work.SignatureBordism.quadOfBilin_apply, map_add, LinearMap.add_apply]
    rw [bdryFormBilin_symm W y x, hx y, hx x]
    ring
  rw [QuadraticMap.associated_apply (S := ℚ), h2, smul_zero]
/-! ## The reduction of `HalfDimension` to the Lagrangian property -/

/-- **`HalfDimension 4` for the explicit boundary bordism, from the Lagrangian property of the
image of the restriction and the two Poincaré-duality inputs for `∂W`.**

The isotropy `K ⊆ Kᗮ` is *proved* in the workspace (`Work.ThomBordism.bdryK_isotropic`); the
maximality `Kᗮ ⊆ K` is the hypothesis `hmax` (the crux, `Work.ThomBordism.BoundaryMaximalIsotropic`).
Together with non-degeneracy of the middle form of `∂W` (`hnd`) and its finite dimensionality
(`Work.ThomBordism.bdryRatCohFinite`), the abstract count `two_mul_finrank_of_isLagrangian` gives
`2 dim K = dim H⁴(∂W;ℚ)`, which is exactly `Work.Bordism.HalfDimension 4` (the second end is empty,
so its factor contributes nothing). -/
theorem boundaryHalfDimension_of_maximalIsotropic (hmax : BoundaryMaximalIsotropic) :
    ∀ (ι : Type) [Fintype ι] (F : ι → Man8) (W : NullBordismFamily ι F),
      Work.Bordism.HalfDimension 4 (boundaryBordismExplicit W) := by
  intro ι _ F W
  haveI hfin : FiniteDimensional ℚ (Work.SignatureBordism.ratCohomology 4
      (TopCat.toSSet.obj (TopCat.of (bdrySet W.W)))) := bdryRatCohFinite F W
  haveI hfin0 : FiniteDimensional ℚ (Work.SignatureBordism.ratCohomology 4
      (TopCat.toSSet.obj (TopCat.of PEmpty))) := finite_empty
  have hndB : ∀ x, (∀ y, bdryFormBilin W x y = 0) → x = 0 :=
    bdryFormBilin_nondegenerate W (bdryMidFormNondegenerate F W)
  have hiso : ∀ x ∈ bdryK W, ∀ y ∈ bdryK W, bdryFormBilin W x y = 0 := bdryK_isotropic W
  have hmaxB : ∀ y, (∀ x ∈ bdryK W, bdryFormBilin W x y = 0) → y ∈ bdryK W := by
    intro y hy
    refine hmax ι F W y (fun x hx => ?_)
    show QuadraticMap.associated (Work.SignatureBordism.quadOfBilin (bdryFormBilin W)) x y = 0
    have h2 : Work.SignatureBordism.quadOfBilin (bdryFormBilin W) (x + y)
        - Work.SignatureBordism.quadOfBilin (bdryFormBilin W) x
        - Work.SignatureBordism.quadOfBilin (bdryFormBilin W) y = 0 := by
      simp only [Work.SignatureBordism.quadOfBilin_apply, map_add, LinearMap.add_apply]
      rw [bdryFormBilin_symm W y x, hy x hx]
      ring
    rw [QuadraticMap.associated_apply (S := ℚ), h2, smul_zero]
  have hkey : 2 * Module.finrank ℚ (bdryK W) = Module.finrank ℚ
      (Work.SignatureBordism.ratCohomology 4
        (TopCat.toSSet.obj (TopCat.of (bdrySet W.W)))) :=
    two_mul_finrank_of_isLagrangian (bdryFormBilin W) (bdryFormBilin_symm W) hndB
      (bdryK W) hiso hmaxB
  have hmm : Work.Bordism.middleMap 4 (boundaryBordismExplicit W)
      = (Work.Bordism.pullbackRat 4 (bdryIncl W)).prod
          (Work.Bordism.pullbackRat 4 (boundaryBordismExplicit W).iN) := rfl
  haveI hsub0 : Subsingleton (Work.SignatureBordism.ratCohomology 4
      (TopCat.toSSet.obj (TopCat.of PEmpty))) := subsingleton_ratCohomology_pempty 4
  have hgm : Work.Bordism.pullbackRat 4 (boundaryBordismExplicit W).iN = 0 :=
    LinearMap.ext (fun z => Subsingleton.elim _ _)
  have hrange : LinearMap.range (Work.Bordism.middleMap 4 (boundaryBordismExplicit W))
      = (bdryK W).prod (⊥ : Submodule ℚ (Work.SignatureBordism.ratCohomology 4
          (TopCat.toSSet.obj (TopCat.of PEmpty)))) := by
    rw [hmm, LinearMap.range_prod_eq (f := Work.Bordism.pullbackRat 4 (bdryIncl W))
        (g := Work.Bordism.pullbackRat 4 (boundaryBordismExplicit W).iN)
        (by rw [LinearMap.ker_eq_top.mpr hgm, sup_top_eq]),
      LinearMap.range_eq_bot.mpr hgm]
  rw [Work.Bordism.HalfDimension, hrange,
    finrank_submodule_prod_bot (M' := Work.SignatureBordism.ratCohomology 4
      (TopCat.toSSet.obj (TopCat.of PEmpty))),
    finrank_prod_of_subsingleton]
  exact hkey

/-- **Middle-degree Lefschetz duality for the pair `(W, ∂W)`** — the crux of `Work.ThomBordism.BoundarySigma`. `Work.ThomBordism.boundaryBordismExplicit W` is the explicit bordism `(∂W, ∂w) ⟶ (∅, 0)` (bordism manifold `W` itself, the inclusion of the boundary, the empty second end; `Submission/Work/ThomBordism/boundaryDualityExplicit.lean`), and `Work.Bordism.HalfDimension 4` of it says that the image of the restriction `H⁴(W;ℚ) → H⁴(∂W;ℚ)` has half the dimension of `H⁴(∂W;ℚ)`, i.e. is a Lagrangian of the middle intersection form of `∂W` — the isotropy half already being the theorem `Work.Bordism.boundaryForm_middleMap_eq_zero`. The classical proof, the reduction already in place, the exact available machinery of the workspace (long exact sequences of a pair, `Work.Cohomology.kronH_natural`, the relative cap product `Work.Cohomology.relCapPair` and `Work.Surgery.LefschetzDuality`, absolute Poincaré duality in the `Good` form) and the two viable routes (collar/compactly-supported, and double + Mayer–Vietoris with `Work.ThomBordism.goodUniv_of_localGen` on the double) are written out in `Submission/Work/ThomBordism/HALFDIM_PLAN.md`. -/
theorem boundaryHalfDimension : ∀ (ι : Type) [Fintype ι] (F : ι → Work.ThomBordism.Man8)
    (W : Work.ThomBordism.NullBordismFamily ι F),
    Work.Bordism.HalfDimension 4 (Work.ThomBordism.boundaryBordismExplicit W) := by
  -- The crux `Work.ThomBordism.BoundaryMaximalIsotropic` is
  -- `Submission/Work/ThomBordism/boundaryMaximalIsotropic.lean` (middle Lefschetz duality for the
  -- pair `(W, ∂W)`), and the non-degeneracy of the middle form of `∂W` is the proved
  -- `Work.ThomBordism.bdryMidFormNondegenerate`; everything else is
  -- `boundaryHalfDimension_of_maximalIsotropic`.
  exact boundaryHalfDimension_of_maximalIsotropic boundaryMaximalIsotropic

end

end Work.ThomBordism
