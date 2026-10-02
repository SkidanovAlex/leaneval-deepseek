import Mathlib
import Submission.Work.Tubular.NormalFrame
import Submission.Work.Tubular.LocalIFT
import Submission.Work.Tubular.TubeLocal

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000

/-!
# The normal foot of a point, and the foot equation

For an embedding `E : V ↪ ℝ^{8+k}` and a chart `i` of `V`, the **foot equation** of a point
`y : ℝ^{8+k}` near the image of `V` is

  `A_τ† (y - f τ) = 0`,     `A_τ = fderiv ℝ (chartRep E.e i) τ`,  `f = chartRep E.e i`,

to be solved for the chart coordinate `τ` of the foot.  Since `A_τ†` is a *smooth* family of
surjective maps `ℝ^{8+k} → ℝ^8` (the family `tauAdj`), the map

  `footMap p = (A_{p.1}† (p.2 - f p.1), p.2)`

is a local diffeomorphism at each point `(τ, f τ)` of the zero section: its derivative there is

  `footDeriv₀ A (δτ, δy) = (A† (δy - A δτ), δy)`,   `A = A_τ`,

which is invertible because `A` is injective (`footDeriv₀_bijective`).  The inverse function theorem
(`Work.Tubular.exists_localInverse_of_contDiffOn`) applied to `footMap` therefore gives the *normal
foot* `τ(y)` as a smooth function of `y` on a neighbourhood of the image point (`FootData`).

This is the analytic heart of the tubular neighbourhood theorem; the assembly of the foot data into
the local tube charts is in `LocalTube.lean`.
-/

open scoped Manifold ContDiff Topology InnerProduct
open Function Filter

namespace Work.Tubular

open Work.ThomBordism.PontryaginThom

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-! ## The adjoint, as a continuous linear map -/

/-- **The adjoint of a continuous linear map, as a continuous linear map** (the adjoint of the
continuous linear maps between Euclidean spaces is itself continuous linear, indeed an isometry). -/
def adjointClm (m n : ℕ) : (Euc m →L[ℝ] Euc n) →L[ℝ] (Euc n →L[ℝ] Euc m) where
  toLinearMap :=
    { toFun := fun A => A.adjoint
      map_add' := by
        intro A B
        refine ContinuousLinearMap.ext fun x => ?_
        apply ext_inner_left ℝ
        intro v
        rw [ContinuousLinearMap.adjoint_inner_right, add_apply, inner_add_left,
          ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.adjoint_inner_right,
          ← inner_add_right, add_apply]
      map_smul' := by
        intro c A
        refine ContinuousLinearMap.ext fun x => ?_
        apply ext_inner_left ℝ
        intro v
        rw [ContinuousLinearMap.adjoint_inner_right, smul_apply, inner_smul_left,
          ← ContinuousLinearMap.adjoint_inner_right, smul_apply, inner_smul_right]
        simp }
  cont := by fun_prop

theorem adjointClm_apply (m n : ℕ) (A : Euc m →L[ℝ] Euc n) :
    adjointClm m n A = A.adjoint := rfl

/-- An element of an endomorphism ring that is a unit is bijective. -/
theorem bijective_of_isUnit {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {f : P →L[ℝ] P} (hf : IsUnit f) : Function.Bijective f := by
  obtain ⟨u, rfl⟩ := hf
  have hright : ∀ x, (↑u : P →L[ℝ] P) ((↑u⁻¹ : P →L[ℝ] P) x) = x := by
    intro x
    have h1 : (↑u : P →L[ℝ] P) ((↑u⁻¹ : P →L[ℝ] P) x)
        = ((↑u : P →L[ℝ] P) * (↑u⁻¹ : P →L[ℝ] P)) x := rfl
    rw [h1, u.mul_inv]
    rfl
  have hleft : ∀ x, (↑u⁻¹ : P →L[ℝ] P) ((↑u : P →L[ℝ] P) x) = x := by
    intro x
    have h1 : (↑u⁻¹ : P →L[ℝ] P) ((↑u : P →L[ℝ] P) x)
        = ((↑u⁻¹ : P →L[ℝ] P) * (↑u : P →L[ℝ] P)) x := rfl
    rw [h1, u.inv_mul]
    rfl
  exact ⟨fun x y hxy => by rw [← hleft x, ← hleft y, hxy],
    fun y => ⟨((↑u⁻¹ : P →L[ℝ] P) y), hright y⟩⟩

/-! ## The family of tangent frames and of their adjoints, in chart coordinates -/

/-- The tangent frame in chart coordinates, as a function of `τ ∈ ℝ^8`. -/
def tauFrame (E : EmbeddingData V (8 + k)) (i : atlas (Euc 8) V.pt) (τ : Euc 8) :
    Euc 8 →L[ℝ] Euc (8 + k) :=
  fderiv ℝ (chartRep E.e i) τ

theorem tauFrame_eq_fderiv (E : EmbeddingData V (8 + k)) (i : atlas (Euc 8) V.pt) (τ : Euc 8) :
    tauFrame E i τ = fderiv ℝ (chartRep E.e i) τ := rfl

/-- **The adjoint of the tangent frame**, as a function of the chart coordinate: the smooth family
of surjective maps `ℝ^{8+k} → ℝ^8` whose kernels are the normal spaces. -/
def tauAdj (E : EmbeddingData V (8 + k)) (i : atlas (Euc 8) V.pt) (τ : Euc 8) :
    Euc (8 + k) →L[ℝ] Euc 8 :=
  (tauFrame E i τ).adjoint

theorem tauAdj_eq (E : EmbeddingData V (8 + k)) (i : atlas (Euc 8) V.pt) (τ : Euc 8) :
    tauAdj E i τ = adjointClm 8 (8 + k) (tauFrame E i τ) := rfl

/-- The chart representative is `C^∞` on the chart's target. -/
theorem contDiffOn_chartRep_infty (E : EmbeddingData V (8 + k)) (i : atlas (Euc 8) V.pt) :
    ContDiffOn ℝ ∞ (chartRep E.e i) i.1.target := by
  have hmem : i.1 ∈ IsManifold.maximalAtlas (𝓡 8) ∞ V.pt :=
    IsManifold.subset_maximalAtlas (I := 𝓡 8) (n := ∞) i.2
  have hsymm : ContMDiffOn 𝓘(ℝ, Euc 8) (𝓡 8) ∞ (fun y => i.1.symm y) i.1.target :=
    contMDiffOn_symm_of_mem_maximalAtlas hmem
  have hcomp : ContMDiffOn 𝓘(ℝ, Euc 8) (𝓡 (8 + k)) ∞ (fun y => E.e (i.1.symm y)) i.1.target :=
    (E.smooth.contMDiffOn).comp hsymm (t := Set.univ) (fun y _ => Set.mem_univ (i.1.symm y))
  exact hcomp.contDiffOn

theorem contDiffOn_tauFrame (E : EmbeddingData V (8 + k)) (i : atlas (Euc 8) V.pt) :
    ContDiffOn ℝ ∞ (tauFrame E i) i.1.target :=
  contDiffOn_tangentFrame_coord E i

/-- **The family of adjoints of the tangent frames is `C^∞`** on the chart's target. -/
theorem contDiffOn_tauAdj (E : EmbeddingData V (8 + k)) (i : atlas (Euc 8) V.pt) :
    ContDiffOn ℝ ∞ (tauAdj E i) i.1.target :=
  (adjointClm 8 (8 + k)).contDiff.comp_contDiffOn (contDiffOn_tauFrame E i)

/-! ## The foot map -/

/-- The **foot map**: `p ↦ (A_{p.1}† (p.2 - f p.1), p.2)`.  Its `0`-fibre in the first coordinate is
exactly the set of pairs `(τ, y)` for which `τ` is the chart coordinate of the foot of `y`. -/
def footMap (E : EmbeddingData V (8 + k)) (i : atlas (Euc 8) V.pt)
    (p : Euc 8 × Euc (8 + k)) : Euc 8 × Euc (8 + k) :=
  (tauAdj E i p.1 (p.2 - chartRep E.e i p.1), p.2)

theorem footMap_apply (E : EmbeddingData V (8 + k)) (i : atlas (Euc 8) V.pt)
    (p : Euc 8 × Euc (8 + k)) :
    footMap E i p = (tauAdj E i p.1 (p.2 - chartRep E.e i p.1), p.2) := rfl

/-- The foot map is `C^∞` on the product of the chart's target with everything. -/
theorem contDiffOn_footMap (E : EmbeddingData V (8 + k)) (i : atlas (Euc 8) V.pt) :
    ContDiffOn ℝ ∞ (footMap E i) (i.1.target ×ˢ Set.univ) := by
  have hτ : ContDiffOn ℝ ∞ (fun p : Euc 8 × Euc (8 + k) => tauAdj E i p.1)
      (i.1.target ×ˢ Set.univ) :=
    (contDiffOn_tauAdj E i).comp contDiffOn_fst (fun p hp => hp.1)
  have harg : ContDiffOn ℝ ∞ (fun p : Euc 8 × Euc (8 + k) => p.2 - chartRep E.e i p.1)
      (i.1.target ×ˢ Set.univ) :=
    contDiffOn_snd.sub ((contDiffOn_chartRep_infty E i).comp contDiffOn_fst (fun p hp => hp.1))
  exact (hτ.clm_apply harg).prodMk contDiffOn_snd

/-- The first component of the foot map vanishes at a point of the zero section. -/
theorem footMap_zero (E : EmbeddingData V (8 + k)) (i : atlas (Euc 8) V.pt) (τ : Euc 8) :
    footMap E i (τ, chartRep E.e i τ) = ((0 : Euc 8), chartRep E.e i τ) := by
  simp [footMap]

/-! ## The derivative of the foot map at a point of the zero section -/

/-- **The derivative of the foot map at a point of the zero section**, for a frame `A`: the linear
map `(δτ, δy) ↦ (A† (δy - A δτ), δy)`. -/
def footDeriv₀ (A : Euc 8 →L[ℝ] Euc (8 + k)) :
    (Euc 8 × Euc (8 + k)) →L[ℝ] (Euc 8 × Euc (8 + k)) :=
  ((A.adjoint.comp (ContinuousLinearMap.snd ℝ (Euc 8) (Euc (8 + k))))
    - ((A.adjoint.comp A).comp (ContinuousLinearMap.fst ℝ (Euc 8) (Euc (8 + k))))).prod
    (ContinuousLinearMap.snd ℝ (Euc 8) (Euc (8 + k)))

@[simp] theorem clm_fst_apply (u : Euc 8 × Euc (8 + k)) :
    (ContinuousLinearMap.fst ℝ (Euc 8) (Euc (8 + k))) u = u.1 := rfl

@[simp] theorem clm_snd_apply (u : Euc 8 × Euc (8 + k)) :
    (ContinuousLinearMap.snd ℝ (Euc 8) (Euc (8 + k))) u = u.2 := rfl

theorem footDeriv₀_apply (A : Euc 8 →L[ℝ] Euc (8 + k))
    (u : Euc 8 × Euc (8 + k)) :
    footDeriv₀ A u = (A.adjoint (u.2 - A u.1), u.2) := by
  simp only [footDeriv₀, ContinuousLinearMap.prod_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, clm_fst_apply, clm_snd_apply]
  rw [map_sub]

/-- A vector that is both in the range of an injective map and orthogonal to it is zero. -/
theorem eq_zero_of_mem_range_and_orthogonal {A : Euc 8 →L[ℝ] Euc (8 + k)}
    (hA : Function.Injective A) {z : Euc 8} (hz : A z ∈ (LinearMap.range A.toLinearMap)ᗮ) :
    z = 0 := by
  have h1 : inner ℝ (A z) (A z) = 0 :=
    (Submodule.mem_orthogonal _ _).mp hz _ (LinearMap.mem_range.mpr ⟨z, rfl⟩)
  have h2 : A z = 0 := inner_self_eq_zero.mp h1
  exact hA (h2.trans (map_zero A).symm)

/-- `A† ∘ A` is injective when `A` is. -/
theorem injective_adjoint_comp (A : Euc 8 →L[ℝ] Euc (8 + k)) (hA : Function.Injective A) :
    Function.Injective (A.adjoint.comp A).toLinearMap := by
  intro u v huv
  have h1 : (A.adjoint.comp A) (u - v) = 0 := by
    have h0 : (A.adjoint.comp A) u = (A.adjoint.comp A) v := huv
    calc (A.adjoint.comp A) (u - v)
        = (A.adjoint.comp A) u - (A.adjoint.comp A) v := map_sub _ _ _
      _ = 0 := by rw [h0, sub_self]
  have h3 : A.adjoint (A (u - v)) = 0 := by
    simpa only [ContinuousLinearMap.comp_apply] using h1
  exact sub_eq_zero.mp (eq_zero_of_mem_range_and_orthogonal hA
    ((adjoint_eq_zero_iff_mem_orthogonal A (A (u - v))).mp h3))

/-- **The derivative of the foot map at a point of the zero section is bijective**, because the
tangent frame is injective. -/
theorem footDeriv₀_bijective (A : Euc 8 →L[ℝ] Euc (8 + k)) (hA : Function.Injective A) :
    Function.Bijective (footDeriv₀ A) := by
  refine ⟨?_, ?_⟩
  · intro u v huv
    have h2 : u.2 = v.2 := by
      simpa [footDeriv₀_apply] using congrArg Prod.snd huv
    have h1 : A.adjoint (u.2 - A u.1) = A.adjoint (v.2 - A v.1) := by
      simpa [footDeriv₀_apply] using congrArg Prod.fst huv
    have h3 : A.adjoint (A (v.1 - u.1)) = 0 := by
      have h1' : A.adjoint (u.2 - A u.1) = A.adjoint (u.2 - A v.1) :=
        h1.trans (congrArg (fun w => A.adjoint (w - A v.1)) h2).symm
      have key : A.adjoint ((u.2 - A u.1) - (u.2 - A v.1)) = 0 := by
        rw [map_sub, h1', sub_self]
      have hvec : (u.2 - A u.1) - (u.2 - A v.1) = A (v.1 - u.1) := by
        rw [map_sub]; abel
      rwa [hvec] at key
    have h4 : v.1 - u.1 = 0 :=
      eq_zero_of_mem_range_and_orthogonal hA
        ((adjoint_eq_zero_iff_mem_orthogonal A (A (v.1 - u.1))).mp h3)
    have h5 : v.1 = u.1 := sub_eq_zero.mp h4
    exact Prod.ext h5.symm h2
  · intro w
    have hsurj : Function.Surjective (A.adjoint.comp A).toLinearMap :=
      (LinearMap.injective_iff_surjective).mp (injective_adjoint_comp A hA)
    obtain ⟨δτ, hδτ⟩ := hsurj (A.adjoint w.2 - w.1)
    have hgoal : A.adjoint (w.2 - A δτ) = w.1 := by
      have hδτ' : A.adjoint (A δτ) = A.adjoint w.2 - w.1 :=
        Eq.trans (ContinuousLinearMap.comp_apply A.adjoint A δτ).symm hδτ
      rw [map_sub, hδτ', sub_sub_cancel]
    refine ⟨(δτ, w.2), ?_⟩
    rw [footDeriv₀_apply, Prod.mk.injEq]
    exact ⟨hgoal, rfl⟩

/-- The derivative of `footMap` at the zero section, written in the form produced by the product
rule (the second term of `HasFDerivAt.clm_apply` applied to `0`). -/
def rawDeriv (E : EmbeddingData V (8 + k)) (i : atlas (Euc 8) V.pt) (τ₀ : Euc 8) :
    (Euc 8 × Euc (8 + k)) →L[ℝ] (Euc 8 × Euc (8 + k)) :=
  ContinuousLinearMap.prod
    ((tauAdj E i (τ₀, chartRep E.e i τ₀).1).comp
        ((ContinuousLinearMap.snd ℝ (Euc 8) (Euc (8 + k)))
          - ((fderiv ℝ (chartRep E.e i) τ₀).comp
              (ContinuousLinearMap.fst ℝ (Euc 8) (Euc (8 + k)))))
      + (((fderiv ℝ (tauAdj E i) τ₀).comp
            (ContinuousLinearMap.fst ℝ (Euc 8) (Euc (8 + k)))).flip
          ((τ₀, chartRep E.e i τ₀).2 - chartRep E.e i (τ₀, chartRep E.e i τ₀).1)))
    (ContinuousLinearMap.snd ℝ (Euc 8) (Euc (8 + k)))

/-- The "raw" derivative of the foot map at the zero section is the explicit one. -/
theorem rawDeriv_eq_footDeriv₀ (E : EmbeddingData V (8 + k)) (i : atlas (Euc 8) V.pt)
    (τ₀ : Euc 8) :
    rawDeriv E i τ₀ = footDeriv₀ (tauFrame E i τ₀) := by
  have hflip : (((fderiv ℝ (tauAdj E i) τ₀).comp
        (ContinuousLinearMap.fst ℝ (Euc 8) (Euc (8 + k)))).flip (0 : Euc (8 + k))) = 0 := by
    refine ContinuousLinearMap.ext fun v => ?_
    rw [ContinuousLinearMap.flip_apply, map_zero, ContinuousLinearMap.zero_apply]
  have hcomp : ((tauFrame E i τ₀).adjoint).comp
        (ContinuousLinearMap.snd ℝ (Euc 8) (Euc (8 + k))
          - ((fderiv ℝ (chartRep E.e i) τ₀).comp
              (ContinuousLinearMap.fst ℝ (Euc 8) (Euc (8 + k)))))
      = ((tauFrame E i τ₀).adjoint).comp (ContinuousLinearMap.snd ℝ (Euc 8) (Euc (8 + k)))
        - (((tauFrame E i τ₀).adjoint).comp (tauFrame E i τ₀)).comp
            (ContinuousLinearMap.fst ℝ (Euc 8) (Euc (8 + k))) := by
    rw [ContinuousLinearMap.comp_sub]
    congr 1
  rw [rawDeriv, footDeriv₀]
  rw [show (tauAdj E i (τ₀, chartRep E.e i τ₀).1) = ((tauFrame E i τ₀).adjoint) from rfl]
  rw [show ((τ₀, chartRep E.e i τ₀).2 - chartRep E.e i (τ₀, chartRep E.e i τ₀).1)
      = (0 : Euc (8 + k)) from sub_self _]
  rw [hflip, add_zero, hcomp]

/-- **The foot map is differentiable at the zero section, with the explicit derivative
`footDeriv₀`.** -/
theorem hasFDerivAt_footMap_zero (E : EmbeddingData V (8 + k)) (i : atlas (Euc 8) V.pt)
    {τ₀ : Euc 8} (hτ₀ : τ₀ ∈ i.1.target) :
    HasFDerivAt (footMap E i) (footDeriv₀ (tauFrame E i τ₀))
      (τ₀, chartRep E.e i τ₀) := by
  have hAt : ContDiffAt ℝ ∞ (tauAdj E i) τ₀ :=
    (contDiffOn_tauAdj E i).contDiffAt (i.1.open_target.mem_nhds hτ₀)
  have hd : DifferentiableAt ℝ (tauAdj E i) τ₀ := hAt.differentiableAt (by simp)
  have hfAt : ContDiffAt ℝ ∞ (chartRep E.e i) τ₀ :=
    (contDiffOn_chartRep_infty E i).contDiffAt (i.1.open_target.mem_nhds hτ₀)
  have hd2 : DifferentiableAt ℝ (chartRep E.e i) τ₀ := hfAt.differentiableAt (by simp)
  have hc : HasFDerivAt (fun p : Euc 8 × Euc (8 + k) => tauAdj E i p.1)
      ((fderiv ℝ (tauAdj E i) τ₀).comp (ContinuousLinearMap.fst ℝ (Euc 8) (Euc (8 + k))))
      (τ₀, chartRep E.e i τ₀) := by
    have h1 := (hd.hasFDerivAt).comp (τ₀, chartRep E.e i τ₀)
      (ContinuousLinearMap.fst ℝ (Euc 8) (Euc (8 + k))).hasFDerivAt
    exact h1.congr_of_eventuallyEq (EventuallyEq.of_eq (by
      ext p
      rfl))
  have hu : HasFDerivAt (fun p : Euc 8 × Euc (8 + k) => p.2 - chartRep E.e i p.1)
      ((ContinuousLinearMap.snd ℝ (Euc 8) (Euc (8 + k)))
        - ((fderiv ℝ (chartRep E.e i) τ₀).comp
            (ContinuousLinearMap.fst ℝ (Euc 8) (Euc (8 + k)))))
      (τ₀, chartRep E.e i τ₀) :=
    hasFDerivAt_snd.sub (by
      have h1 := (hd2.hasFDerivAt).comp (τ₀, chartRep E.e i τ₀)
        (ContinuousLinearMap.fst ℝ (Euc 8) (Euc (8 + k))).hasFDerivAt
      exact h1.congr_of_eventuallyEq (EventuallyEq.of_eq (by
        ext p
        rfl)))
  have hH := hc.clm_apply hu
  have hG := hH.prodMk (hasFDerivAt_snd :
    HasFDerivAt (fun p : Euc 8 × Euc (8 + k) => p.2)
      (ContinuousLinearMap.snd ℝ (Euc 8) (Euc (8 + k))) (τ₀, chartRep E.e i τ₀))
  have hG' : HasFDerivAt (footMap E i) (rawDeriv E i τ₀) (τ₀, chartRep E.e i τ₀) :=
    hG.congr_of_eventuallyEq (EventuallyEq.of_eq (by
      funext p
      rfl))
  rw [rawDeriv_eq_footDeriv₀] at hG'
  exact hG'

/-! ## The inverse function theorem data for the foot map -/

/-- **The data produced by the inverse function theorem for the foot map**: a local inverse of the
foot map at a point of the zero section.  The first component of `g` is the *normal foot*: for `y`
in `U`, `(g y).1` is the chart coordinate of the foot of `y`, and `y - E.e (i.symm (g y).1)` is the
normal vector of `y`. -/
structure FootData (E : EmbeddingData V (8 + k)) (i : atlas (Euc 8) V.pt) (x₀ : V.pt) where
  mem_source : x₀ ∈ i.1.source
  W : Set (Euc 8 × Euc (8 + k))
  hW : IsOpen W
  mem_W : (i.1 x₀, chartRep E.e i (i.1 x₀)) ∈ W
  U : Set (Euc 8 × Euc (8 + k))
  hU : IsOpen U
  mem_U : ((0 : Euc 8), chartRep E.e i (i.1 x₀)) ∈ U
  image_eq : footMap E i '' W = U
  injOn : Set.InjOn (footMap E i) W
  g : Euc 8 × Euc (8 + k) → Euc 8 × Euc (8 + k)
  g_mem : ∀ y ∈ U, g y ∈ W
  g_spec : ∀ y ∈ U, footMap E i (g y) = y
  g_spec' : ∀ p ∈ W, g (footMap E i p) = p
  continuousOn_g : ContinuousOn g U
  contDiffOn_g : ContDiffOn ℝ ∞ g U

/-- **The inverse function theorem for the foot map**: at every point of the zero section the foot
map has a smooth local inverse. -/
theorem nonempty_footData (E : EmbeddingData V (8 + k)) (x₀ : V.pt) :
    Nonempty (FootData E (chartAtIdx x₀) x₀) := by
  have hx₀ : x₀ ∈ (chartAtIdx x₀).1.source := mem_chart_source (Euc 8) x₀
  have hτ₀ : (chartAtIdx x₀).1 x₀ ∈ (chartAtIdx x₀).1.target := (chartAtIdx x₀).1.map_source hx₀
  have hinj : Function.Injective
      (tauFrame E (chartAtIdx x₀) ((chartAtIdx x₀).1 x₀)) := by
    have h := mfderiv_eq_fderiv_chartAt E.e (E.smooth.of_le (by simp)) x₀
    show Function.Injective (fderiv ℝ (fun y => E.e ((chartAt (Euc 8) x₀).symm y))
      ((chartAt (Euc 8) x₀) x₀))
    rw [← h]
    exact E.injective_mfderiv x₀
  have hbase := hasFDerivAt_footMap_zero E (chartAtIdx x₀) hτ₀
  obtain ⟨φ, hφ⟩ := exists_continuousLinearEquiv_of_bijective
    (footDeriv₀ (tauFrame E (chartAtIdx x₀) ((chartAtIdx x₀).1 x₀)))
    (footDeriv₀_bijective _ hinj)
  -- the derivative of the foot map is a unit at the base point, and stays one nearby
  have hder := (contDiffOn_footMap E (chartAtIdx x₀)).fderiv_of_isOpen
    ((chartAtIdx x₀).1.open_target.prod isOpen_univ) (m := 0) (by simp)
  have hcont : ContinuousAt
      (fun p : Euc 8 × Euc (8 + k) => fderiv ℝ (footMap E (chartAtIdx x₀)) p)
      ((chartAtIdx x₀).1 x₀, chartRep E.e (chartAtIdx x₀) ((chartAtIdx x₀).1 x₀)) :=
    hder.continuousOn.continuousAt
      (((chartAtIdx x₀).1.open_target.prod isOpen_univ).mem_nhds ⟨hτ₀, Set.mem_univ _⟩)
  have hunit : IsUnit (fderiv ℝ (footMap E (chartAtIdx x₀))
      ((chartAtIdx x₀).1 x₀, chartRep E.e (chartAtIdx x₀) ((chartAtIdx x₀).1 x₀))) := by
    rw [hbase.fderiv, ← hφ]
    exact ⟨⟨φ.toContinuousLinearMap, φ.symm.toContinuousLinearMap,
      (by apply ContinuousLinearMap.ext; intro z; simpa using φ.apply_symm_apply z),
      (by apply ContinuousLinearMap.ext; intro z; simpa using φ.symm_apply_apply z)⟩, rfl⟩
  obtain ⟨r, hrpos, hrsub⟩ := Metric.mem_nhds_iff.mp
    (hcont.eventually (Units.isOpen.mem_nhds hunit))
  -- the open set on which the inverse function theorem is applied
  have hW₀open : IsOpen (Metric.ball
      ((chartAtIdx x₀).1 x₀, chartRep E.e (chartAtIdx x₀) ((chartAtIdx x₀).1 x₀)) r
        ∩ ((chartAtIdx x₀).1.target ×ˢ (Set.univ : Set (Euc (8 + k))))) :=
    Metric.isOpen_ball.inter ((chartAtIdx x₀).1.open_target.prod isOpen_univ)
  have hmem₀ : ((chartAtIdx x₀).1 x₀, chartRep E.e (chartAtIdx x₀) ((chartAtIdx x₀).1 x₀))
      ∈ Metric.ball ((chartAtIdx x₀).1 x₀, chartRep E.e (chartAtIdx x₀) ((chartAtIdx x₀).1 x₀)) r
        ∩ ((chartAtIdx x₀).1.target ×ˢ (Set.univ : Set (Euc (8 + k)))) :=
    ⟨Metric.mem_ball_self hrpos, hτ₀, Set.mem_univ _⟩
  have hcd : ContDiffOn ℝ ∞ (footMap E (chartAtIdx x₀))
      (Metric.ball ((chartAtIdx x₀).1 x₀, chartRep E.e (chartAtIdx x₀) ((chartAtIdx x₀).1 x₀)) r
        ∩ ((chartAtIdx x₀).1.target ×ˢ (Set.univ : Set (Euc (8 + k))))) :=
    (contDiffOn_footMap E (chartAtIdx x₀)).mono Set.inter_subset_right
  have hφ' : HasFDerivAt (footMap E (chartAtIdx x₀))
      (φ : (Euc 8 × Euc (8 + k)) →L[ℝ] (Euc 8 × Euc (8 + k)))
      ((chartAtIdx x₀).1 x₀, chartRep E.e (chartAtIdx x₀) ((chartAtIdx x₀).1 x₀)) := by
    rw [show (φ : (Euc 8 × Euc (8 + k)) →L[ℝ] (Euc 8 × Euc (8 + k)))
        = footDeriv₀ (tauFrame E (chartAtIdx x₀) ((chartAtIdx x₀).1 x₀)) from hφ]
    exact hbase
  have hInv : ∀ p ∈ Metric.ball
        ((chartAtIdx x₀).1 x₀, chartRep E.e (chartAtIdx x₀) ((chartAtIdx x₀).1 x₀)) r
        ∩ ((chartAtIdx x₀).1.target ×ˢ (Set.univ : Set (Euc (8 + k)))),
      ∃ ψ : (Euc 8 × Euc (8 + k)) ≃L[ℝ] (Euc 8 × Euc (8 + k)),
        HasFDerivAt (footMap E (chartAtIdx x₀))
          (ψ : (Euc 8 × Euc (8 + k)) →L[ℝ] (Euc 8 × Euc (8 + k))) p := by
    rintro p ⟨hpball, hp⟩
    have hdiff : HasFDerivAt (footMap E (chartAtIdx x₀))
        (fderiv ℝ (footMap E (chartAtIdx x₀)) p) p :=
      ((hcd.contDiffAt (hW₀open.mem_nhds ⟨hpball, hp⟩)).differentiableAt (by simp)).hasFDerivAt
    have hunitp : IsUnit (fderiv ℝ (footMap E (chartAtIdx x₀)) p) := hrsub hpball
    obtain ⟨ψ, hψ⟩ := exists_continuousLinearEquiv_of_bijective _ (bijective_of_isUnit hunitp)
    exact ⟨ψ, by rw [hψ]; exact hdiff⟩
  obtain ⟨W, U, g, hW, hmemW, -, hU, himg, hinj', hgmem, hgright, hgleft, hgcont, hgsmooth⟩ :=
    exists_localInverse_of_contDiffOn (footMap E (chartAtIdx x₀)) φ hW₀open hmem₀ hcd hφ' hInv
  refine ⟨hx₀, W, hW, hmemW, U, hU, ?_, himg, hinj', g, hgmem, hgright, hgleft, hgcont,
    hgsmooth⟩
  rw [← himg]
  exact ⟨((chartAtIdx x₀).1 x₀, chartRep E.e (chartAtIdx x₀) ((chartAtIdx x₀).1 x₀)), hmemW,
    footMap_zero E (chartAtIdx x₀) ((chartAtIdx x₀).1 x₀)⟩

end

end Work.Tubular
