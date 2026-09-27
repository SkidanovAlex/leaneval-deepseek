import Mathlib
import Submission.Work.Drive.N2.ChartSplit
import Submission.Work.Drive.N2.HeightBasics

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# The critical-point parametrisation of a chart representation

Let `F : ℝ² → ℝ⁵` be a chart representation of an immersed surface, smooth on an open set `T`,
and fix distinct indices `a b : Fin 5` such that the `(a,b)`-minor `depProj a b ∘ DF(y)` is
invertible for every `y ∈ T`.

This file sets up the *parametrisation of the critical directions of the height functions*
`y ↦ ⟪v, F y⟫`.  Since `v` is a critical direction at `y` iff `(DF y)† v = 0`, and since

  `(DF y)† (w + depIns s) = (DF y)† w + critMinor y s`,

where `critMinor y = (depProj a b ∘ DF y)†` is invertible on `T`, the critical directions at `y`
are exactly the vectors `critPhi y w = w + depIns (critS y w)` with

  `critS y w = -(critMinor y)⁻¹ ((DF y)† w)`.

This makes the family of critical directions a graph over `y ∈ T` and `w ∈ ℝ⁵`; the corresponding
smooth map `critPhiT : ℝ⁵ → ℝ⁵` (splitting the input into `(depProj z, freePart z)`) is the map to
which Sard's lemma is applied in `Work.Drive.N2.volume_badSet_eq_zero`: its Jacobian is singular
exactly at the parameters whose direction has a degenerate Hessian.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff RealInnerProductSpace
open MeasureTheory Filter Topology

/-- The adjoint of the derivative of the chart representation: `v ↦ (DF(y))† v`.
`v` is a *critical direction* of the height function `y ↦ ⟪v, F y⟫` exactly when `critAdj F y v = 0`. -/
noncomputable def critAdj (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 5))
    (y : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 5) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (fderiv ℝ F y).adjoint

/-- The `(a,b)`-minor of the derivative, transposed (an endomorphism of `ℝ²`). -/
noncomputable def critMinor (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 5))
    (a b : Fin 5) (y : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (minor F a b y).adjoint

/-- The second derivative `D²F(y)` of the chart representation. -/
noncomputable def critD2 (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 5))
    (y : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 5) :=
  fderiv ℝ (fun y' => fderiv ℝ F y') y

/-- The operation `A ↦ A†` as a continuous linear map. -/
noncomputable def critAdjCLM :
    (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 5)) →L[ℝ]
      (EuclideanSpace ℝ (Fin 5) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :=
  ContinuousLinearMap.adjoint.toContinuousLinearMap

/-- The operation `A ↦ A†` on endomorphisms of `ℝ²`, as a continuous linear map. -/
noncomputable def critAdjEndCLM :
    (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) →L[ℝ]
      (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :=
  ContinuousLinearMap.adjoint.toContinuousLinearMap

/-- The derivative of `y ↦ (DF y)†`, i.e. the adjoint of `D²F(y)`, as a continuous linear map in
the first variable. -/
noncomputable def critD2Adj (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 5))
    (y : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] (EuclideanSpace ℝ (Fin 5) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :=
  critAdjCLM.comp (critD2 F y)

/-- The Hessian of the height function `y ↦ ⟪v, F y⟫` at `y`, as an endomorphism of `ℝ²`,
i.e. the Riesz vector of the second derivative.  Its defining property is
`⟪critHess F v y u, x⟫ = fderiv ℝ (fderiv ℝ (chartHeight F v)) y u x`. -/
noncomputable def critHess (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 5))
    (v : EuclideanSpace ℝ (Fin 5)) (y : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm.toContinuousLinearMap).comp
    (fderiv ℝ (fderiv ℝ (chartHeight F v)) y)

/-- The `(a,b)`-datum `s` of the critical direction with free part `w`: the unique solution of
`critMinor y s = -critAdj y w`. -/
noncomputable def critS (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 5))
    (a b : Fin 5) (y : EuclideanSpace ℝ (Fin 2)) (w : EuclideanSpace ℝ (Fin 5)) :
    EuclideanSpace ℝ (Fin 2) :=
  - (critMinor F a b y).inverse (critAdj F y w)

/-- The critical direction at `y` with datum `w`. -/
noncomputable def critPhi (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 5))
    (a b : Fin 5) (y : EuclideanSpace ℝ (Fin 2)) (w : EuclideanSpace ℝ (Fin 5)) :
    EuclideanSpace ℝ (Fin 5) :=
  w + depIns a b (critS F a b y w)

/-- The parametrisation of the critical directions as a self-map of `ℝ⁵`, using
`z ↦ (depProj a b z, freePart a b z)` as coordinates on the source. -/
noncomputable def critPhiT (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 5))
    (a b : Fin 5) (z : EuclideanSpace ℝ (Fin 5)) : EuclideanSpace ℝ (Fin 5) :=
  critPhi F a b (depProj a b z) (freePart a b z)

/-- The set of parameters `z` whose direction `critPhiT F a b z` is a *degenerate* critical
direction at `depProj a b z`. -/
def critSigma (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 5))
    (T : Set (EuclideanSpace ℝ (Fin 2))) (a b : Fin 5) : Set (EuclideanSpace ℝ (Fin 5)) :=
  {z | depProj a b z ∈ T ∧
    ¬ Function.Injective
      (fderiv ℝ (fderiv ℝ (chartHeight F (critPhiT F a b z))) (depProj a b z))}

section Basic

variable {F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 5)}
  {a b : Fin 5} {y : EuclideanSpace ℝ (Fin 2)} {w v : EuclideanSpace ℝ (Fin 5)}
  {T : Set (EuclideanSpace ℝ (Fin 2))}

/-- The defining property of `critAdj`. -/
lemma critAdj_inner (y : EuclideanSpace ℝ (Fin 2)) (v : EuclideanSpace ℝ (Fin 5))
    (x : EuclideanSpace ℝ (Fin 2)) :
    ⟪critAdj F y v, x⟫ = ⟪v, fderiv ℝ F y x⟫ :=
  ContinuousLinearMap.adjoint_inner_left _ _ _

/-- The adjoint of the insertion `depIns a b` is the projection `depProj a b`. -/
lemma adjoint_depProj (a b : Fin 5) : (depProj a b).adjoint = depIns a b := by
  refine ContinuousLinearMap.ext (fun u => ?_)
  refine ext_inner_left ℝ (fun v => ?_)
  rw [ContinuousLinearMap.adjoint_inner_right]
  rw [← real_inner_comm v (depIns a b u), inner_depIns, PiLp.inner_apply]
  simp only [Fin.sum_univ_two, depProj_apply_zero, depProj_apply_one]
  simp

/-- `critMinor` is the adjoint of the `(a,b)`-minor. -/
lemma critMinor_eq_minor_adjoint (a b : Fin 5) (y : EuclideanSpace ℝ (Fin 2)) :
    critMinor F a b y = (minor F a b y).adjoint := rfl

/-- The key computation: `critAdj` applied to an inserted pair is `critMinor`. -/
lemma critAdj_depIns (a b : Fin 5) (y : EuclideanSpace ℝ (Fin 2))
    (x : EuclideanSpace ℝ (Fin 2)) :
    critAdj F y (depIns a b x) = critMinor F a b y x := by
  show (fderiv ℝ F y).adjoint (depIns a b x) = (minor F a b y).adjoint x
  rw [minor, ContinuousLinearMap.adjoint_comp, adjoint_depProj,
    ContinuousLinearMap.comp_apply]

/-- `critMinor y` is the composition of `critAdj y` with the insertion `depIns a b`. -/
lemma critMinor_eq_comp (a b : Fin 5) (y : EuclideanSpace ℝ (Fin 2)) :
    critMinor F a b y = (critAdj F y).comp (depIns a b) := by
  ext x
  rw [ContinuousLinearMap.comp_apply, critAdj_depIns]

/-- The defining property of `critHess`: it is the Riesz vector of the second derivative of the
height function. -/
lemma critHess_inner (v : EuclideanSpace ℝ (Fin 5)) (y u x : EuclideanSpace ℝ (Fin 2)) :
    ⟪critHess F v y u, x⟫ = fderiv ℝ (fderiv ℝ (chartHeight F v)) y u x := by
  simp [critHess]

/-- The defining property of `critD2Adj`. -/
lemma critD2Adj_apply (y δ : EuclideanSpace ℝ (Fin 2)) (v : EuclideanSpace ℝ (Fin 5)) :
    critD2Adj F y δ v = (critD2 F y δ).adjoint v := rfl

/-- A bijective endomorphism of a complete space is invertible. -/
lemma isInvertible_of_bijective (f : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (h : Function.Bijective f) : f.IsInvertible := by
  obtain ⟨u, hu⟩ := ContinuousLinearMap.isUnit_iff_bijective.mpr h
  exact ⟨ContinuousLinearEquiv.ofUnit u, hu⟩

/-- The adjoint of an operator on `ℝ²` is injective iff the operator is surjective. -/
lemma injective_adjoint_iff (f : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
    Function.Injective f.adjoint ↔ Function.Surjective f := by
  constructor
  · intro h
    have hker : f.adjoint.ker = ⊥ := LinearMap.ker_eq_bot.mpr h
    have h1 : f.rangeᗮ = ⊥ := by
      rw [← ContinuousLinearMap.orthogonal_range] at hker
      exact hker
    have h2 : f.range = ⊤ := by
      rwa [Submodule.orthogonal_eq_bot_iff] at h1
    exact LinearMap.range_eq_top.mp h2
  · intro h x z hxz
    have hall : ∀ q, ⟪x - z, f q⟫ = 0 := by
      intro q
      have hx : f.adjoint (x - z) = 0 := by rw [map_sub, hxz, sub_self]
      rw [← ContinuousLinearMap.adjoint_inner_left f q (x - z), hx]
      simp
    obtain ⟨q, hq⟩ := h (x - z)
    specialize hall q
    rw [hq] at hall
    have h2 : x - z = 0 := inner_self_eq_zero.mp hall
    exact sub_eq_zero.mp h2

/-- The adjoint of an operator on `ℝ²` is surjective iff the operator is injective. -/
lemma surjective_adjoint_iff (f : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
    Function.Surjective f.adjoint ↔ Function.Injective f := by
  rw [← injective_adjoint_iff f.adjoint, ContinuousLinearMap.adjoint_adjoint]

/-- The adjoint of an operator on `ℝ²` is bijective iff the operator is. -/
lemma bijective_adjoint_iff (f : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
    Function.Bijective f.adjoint ↔ Function.Bijective f := by
  rw [Function.Bijective, Function.Bijective, injective_adjoint_iff, surjective_adjoint_iff,
    and_comm]

/-- On `T` the `(a,b)`-minor is invertible. -/
lemma critMinor_isInvertible (hmin : Function.Bijective (minor F a b y)) :
    (critMinor F a b y).IsInvertible := by
  refine isInvertible_of_bijective _ ?_
  rw [critMinor_eq_minor_adjoint]
  exact (bijective_adjoint_iff _).mpr hmin

/-- The defining equation of `critS`: `critMinor y (critS y w) = -critAdj y w`. -/
lemma critS_spec (hmin : Function.Bijective (minor F a b y)) (w : EuclideanSpace ℝ (Fin 5)) :
    critMinor F a b y (critS F a b y w) = -critAdj F y w := by
  have hI := critMinor_isInvertible (F := F) (a := a) (b := b) (y := y) hmin
  rw [critS, map_neg, hI.self_apply_inverse]

/-- `critS y w` is the unique solution of the criticality equation. -/
lemma critS_unique (hmin : Function.Bijective (minor F a b y)) (w : EuclideanSpace ℝ (Fin 5))
    (x : EuclideanSpace ℝ (Fin 2)) (hx : critMinor F a b y x = -critAdj F y w) :
    x = critS F a b y w := by
  have hI := critMinor_isInvertible (F := F) (a := a) (b := b) (y := y) hmin
  have h2 : critMinor F a b y x = critMinor F a b y (critS F a b y w) := by
    rw [hx, critS_spec hmin]
  exact hI.injective h2

/-- The parametrised direction is critical. -/
lemma critAdj_critPhi (hmin : Function.Bijective (minor F a b y))
    (w : EuclideanSpace ℝ (Fin 5)) :
    critAdj F y (critPhi F a b y w) = 0 := by
  rw [critPhi, map_add, critAdj_depIns, critS_spec hmin, add_neg_cancel]

/-- Conversely, every critical direction is parametrised by its free part. -/
lemma critPhi_eq_of_critAdj_eq_zero (hmin : Function.Bijective (minor F a b y))
    (h : critAdj F y v = 0) :
    critPhi F a b y (freePart a b v) = v := by
  have hI := critMinor_isInvertible (F := F) (a := a) (b := b) (y := y) hmin
  have hsplit : freePart a b v + depIns a b (depProj a b v) = v := freePart_add_depIns a b v
  have h2 : critAdj F y (freePart a b v) + critMinor F a b y (depProj a b v) = 0 := by
    rw [← critAdj_depIns (F := F) (a := a) (b := b) y (depProj a b v), ← map_add, hsplit, h]
  have h3 : critMinor F a b y (depProj a b v) = -critAdj F y (freePart a b v) :=
    eq_neg_of_add_eq_zero_right h2
  have h4 : depProj a b v = critS F a b y (freePart a b v) :=
    critS_unique hmin _ _ h3
  rw [critPhi, ← h4, hsplit]

/-- `freePart` in coordinates. -/
lemma freePart_apply (a b : Fin 5) (v : EuclideanSpace ℝ (Fin 5)) :
    freePart a b v = v - depIns a b (depProj a b v) := by
  rw [freePart, sub_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply]

/-- The free part is idempotent. -/
lemma freePart_freePart {a b : Fin 5} (hab : a ≠ b) (v : EuclideanSpace ℝ (Fin 5)) :
    freePart a b (freePart a b v) = freePart a b v := by
  have h1 : depProj a b (freePart a b v) = 0 := depProj_freePart hab v
  rw [freePart_apply a b (freePart a b v), h1, map_zero, sub_zero]

/-- The free part of a parametrised direction is the free part of its datum. -/
lemma freePart_critPhi {a b : Fin 5} (hab : a ≠ b) (y : EuclideanSpace ℝ (Fin 2))
    (w : EuclideanSpace ℝ (Fin 5)) :
    freePart a b (critPhi F a b y w) = freePart a b w := by
  rw [critPhi, map_add, freePart_depIns hab, add_zero]

/-- The free part of `critPhiT`. -/
lemma freePart_critPhiT {a b : Fin 5} (hab : a ≠ b) (z : EuclideanSpace ℝ (Fin 5)) :
    freePart a b (critPhiT F a b z) = freePart a b z := by
  rw [critPhiT, freePart_critPhi hab, freePart_freePart hab]

/-- `critPhiT` unrolled. -/
lemma critPhiT_eq (a b : Fin 5) (z : EuclideanSpace ℝ (Fin 5)) :
    critPhiT F a b z = critPhi F a b (depProj a b z) (freePart a b z) := rfl

/-- Criticality of the height function in terms of `critAdj`. -/
lemma critAdj_eq_zero_iff (y : EuclideanSpace ℝ (Fin 2)) (v : EuclideanSpace ℝ (Fin 5))
    (hd : DifferentiableAt ℝ F y) :
    critAdj F y v = 0 ↔ fderiv ℝ (chartHeight F v) y = 0 := by
  constructor
  · intro h
    rw [fderiv_chartHeight F v y hd]
    refine ContinuousLinearMap.ext (fun x => ?_)
    rw [ContinuousLinearMap.comp_apply, zero_apply, innerCLM_apply,
      ← critAdj_inner, h]
    simp
  · intro h
    have h3 : ⟪critAdj F y v, critAdj F y v⟫ = 0 := by
      rw [critAdj_inner, ← innerCLM_apply, ← ContinuousLinearMap.comp_apply,
        ← fderiv_chartHeight F v y hd, h]
      rfl
    exact inner_self_eq_zero.mp h3

/-- The derivative of `y ↦ fderiv ℝ F y` is the second derivative `critD2`. -/
lemma hasFDerivAt_critD2 (hT : IsOpen T) (hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F T)
    (hy : y ∈ T) :
    HasFDerivAt (fun y' => fderiv ℝ F y') (critD2 F y) y := by
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F y := hF.contDiffAt (hT.mem_nhds hy)
  have h2 : ContDiffAt ℝ (1 : WithTop ℕ∞) (fderiv ℝ F) y :=
    h1.fderiv_right (by rw [← WithTop.coe_one, ← WithTop.coe_add, WithTop.coe_le_coe]; exact le_top)
  exact (h2.differentiableAt one_ne_zero).hasFDerivAt

/-- The derivative of `y ↦ (DF y)†` is `critD2Adj`. -/
lemma hasFDerivAt_critAdj (hT : IsOpen T) (hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F T)
    (hy : y ∈ T) :
    HasFDerivAt (fun y' => critAdj F y') (critD2Adj F y) y :=
  (ContinuousLinearMap.hasFDerivAt critAdjCLM (x := fderiv ℝ F y)).comp y
    (hasFDerivAt_critD2 hT hF hy)

lemma critAdjCLM_apply (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 5)) :
    critAdjCLM A = A.adjoint := rfl

lemma critAdjEndCLM_apply (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
    critAdjEndCLM A = A.adjoint := rfl

/-- The index inequality `⊤ + 1 ≤ ⊤` for the `C^∞` index. -/
private lemma crit_top_add_one_le :
    ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  rw [← WithTop.coe_one, ← WithTop.coe_add, WithTop.coe_le_coe]
  exact le_top

/-- **The chain rule for the second derivative.** The second derivative of the height function
`y ↦ ⟪v, F y⟫` is the second derivative of `F` paired with `v`. -/
theorem fderiv_fderiv_chartHeight_apply (hT : IsOpen T)
    (hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F T)
    (hy : y ∈ T) (v : EuclideanSpace ℝ (Fin 5)) (u x : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (fderiv ℝ (chartHeight F v)) y u x = ⟪v, critD2 F y u x⟫ := by
  have hD : HasFDerivAt (fun y' => fderiv ℝ F y') (critD2 F y) y := hasFDerivAt_critD2 hT hF hy
  have h1 : HasFDerivAt (fun y' => (innerCLM v).comp (fderiv ℝ F y'))
      (((ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 5)) ℝ)
        (innerCLM v)) ∘L (critD2 F y)) y :=
    (ContinuousLinearMap.hasFDerivAt ((ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin 2))
      (EuclideanSpace ℝ (Fin 5)) ℝ) (innerCLM v)) (x := fderiv ℝ F y)).comp y hD
  have hev : (fun y' => fderiv ℝ (chartHeight F v) y') =ᶠ[𝓝 y]
      (fun y' => (innerCLM v).comp (fderiv ℝ F y')) := by
    filter_upwards [hT.mem_nhds hy] with y' hy'
    exact fderiv_chartHeight F v y'
      ((hF.contDiffAt (hT.mem_nhds hy')).differentiableAt (by simp))
  have h2 : fderiv ℝ (fun y' => fderiv ℝ (chartHeight F v) y') y
      = fderiv ℝ (fun y' => (innerCLM v).comp (fderiv ℝ F y')) y := hev.fderiv_eq
  change ((fderiv ℝ (fun y' => fderiv ℝ (chartHeight F v) y') y) u) x = ⟪v, critD2 F y u x⟫
  rw [h2, h1.fderiv]
  simp [ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply, innerCLM_apply]

/-- **The Hessian as the adjoint of the second derivative.** -/
theorem critHess_eq_adjoint (hT : IsOpen T)
    (hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F T)
    (hy : y ∈ T) (v : EuclideanSpace ℝ (Fin 5)) (u : EuclideanSpace ℝ (Fin 2)) :
    critHess F v y u = (critD2 F y u).adjoint v := by
  refine ext_inner_left ℝ (fun x => ?_)
  rw [← real_inner_comm x (critHess F v y u), critHess_inner,
    fderiv_fderiv_chartHeight_apply hT hF hy v u x,
    ContinuousLinearMap.adjoint_inner_right, real_inner_comm]

/-- **Smoothness of the criticality datum.** The map `(y, w) ↦ critS F a b y w` is smooth on
`T × ℝ⁵`. -/
theorem contDiffAt_critS (hT : IsOpen T)
    (hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F T)
    (hmin : ∀ y ∈ T, Function.Bijective (minor F a b y))
    (hy : y ∈ T) (w : EuclideanSpace ℝ (Fin 5)) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 5) =>
        critS F a b p.1 p.2) (y, w) := by
  have hFy : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F y := hF.contDiffAt (hT.mem_nhds hy)
  have hfw : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y' => fderiv ℝ F y') y :=
    hFy.fderiv_right crit_top_add_one_le
  have hminAt : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y' => minor F a b y') y :=
    (ContinuousLinearMap.contDiff (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin 2))
      (EuclideanSpace ℝ (Fin 5)) (EuclideanSpace ℝ (Fin 2)) (depProj a b))).contDiffAt.comp
        (x := y) hfw
  have hcritMinor : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y' => critMinor F a b y') y := by
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y' => critAdjEndCLM (minor F a b y')) y :=
      (ContinuousLinearMap.contDiff critAdjEndCLM).contDiffAt.comp (x := y) hminAt
    simpa only [critMinor, critAdjEndCLM_apply] using h1
  have hcritAdj : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y' => critAdj F y') y := by
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y' => critAdjCLM (fderiv ℝ F y')) y :=
      (ContinuousLinearMap.contDiff critAdjCLM).contDiffAt.comp (x := y) hfw
    simpa only [critAdj, critAdjCLM_apply] using h1
  have hInv : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y' => (critMinor F a b y').inverse) y :=
    ((critMinor_isInvertible (hmin y hy)).contDiffAt_map_inverse).comp y hcritMinor
  have hA : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 5) =>
        (critMinor F a b p.1).inverse) (y, w) :=
    hInv.comp (y, w) contDiffAt_fst
  have hB : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 5) =>
        (critAdj F p.1) p.2) (y, w) :=
    (hcritAdj.comp (y, w) contDiffAt_fst).clm_apply contDiffAt_snd
  exact (hA.clm_apply hB).neg

/-- The one-variable smoothness of `y ↦ critS F a b y w`. -/
theorem contDiffAt_critS_right (hT : IsOpen T)
    (hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F T)
    (hmin : ∀ y ∈ T, Function.Bijective (minor F a b y))
    (hy : y ∈ T) (w : EuclideanSpace ℝ (Fin 5)) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y' => critS F a b y' w) y := by
  have h : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y' : EuclideanSpace ℝ (Fin 2) => (y', w)) y :=
    contDiffAt_id.prodMk (contDiffAt_const (c := w))
  have h' : (fun y' => critS F a b y' w)
      = ((fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 5) => critS F a b p.1 p.2)
          ∘ fun y' => (y', w)) := rfl
  rw [h']
  exact (contDiffAt_critS hT hF hmin hy w).comp y h

/-- **The derivative of the criticality datum.** Differentiating the relation
`critMinor y (critS y w) = -critAdj y w` with respect to `y` gives
`critMinor y (∂_y critS) = -critHess`, the Hessian of the height function in direction
`critPhi y w`. -/
theorem fderiv_critS (hT : IsOpen T) (hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F T)
    (hmin : ∀ y ∈ T, Function.Bijective (minor F a b y)) (hy : y ∈ T)
    (w : EuclideanSpace ℝ (Fin 5)) (u : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (fun y' => critS F a b y' w) y u
      = - (critMinor F a b y).inverse (critHess F (critPhi F a b y w) y u) := by
  have hSdiff : DifferentiableAt ℝ (fun y' => critS F a b y' w) y :=
    (contDiffAt_critS_right hT hF hmin hy w).differentiableAt (by simp)
  have hS : HasFDerivAt (fun y' => critS F a b y' w)
      (fderiv ℝ (fun y' => critS F a b y' w) y) y := hSdiff.hasFDerivAt
  have hV : HasFDerivAt (fun y' => (w : EuclideanSpace ℝ (Fin 5)) + depIns a b (critS F a b y' w))
      ((depIns a b) ∘L (fderiv ℝ (fun y' => critS F a b y' w) y)) y := by
    have hdep : HasFDerivAt (fun y' => depIns a b (critS F a b y' w))
        ((depIns a b) ∘L (fderiv ℝ (fun y' => critS F a b y' w) y)) y :=
      (ContinuousLinearMap.hasFDerivAt (depIns a b)
        (x := critS F a b y w)).comp y hS
    have hsum := (hasFDerivAt_const (w : EuclideanSpace ℝ (Fin 5)) y).add hdep
    have heq : ((fun _ : EuclideanSpace ℝ (Fin 2) => (w : EuclideanSpace ℝ (Fin 5))) +
        fun y' => depIns a b (critS F a b y' w))
        = fun y' => (w : EuclideanSpace ℝ (Fin 5)) + depIns a b (critS F a b y' w) := by
      funext y'; rw [Pi.add_apply]
    rw [heq, zero_add] at hsum
    exact hsum
  have hAdj := hasFDerivAt_critAdj (F := F) (T := T) (y := y) hT hF hy
  set Ψ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun y' => critAdj F y' ((w : EuclideanSpace ℝ (Fin 5)) + depIns a b (critS F a b y' w))
    with hΨdef
  have hPsi : HasFDerivAt Ψ
      (critAdj F y ∘L ((depIns a b) ∘L (fderiv ℝ (fun y' => critS F a b y' w) y))
        + (critD2Adj F y).flip ((w : EuclideanSpace ℝ (Fin 5)) + depIns a b (critS F a b y w)))
      y :=
    hAdj.clm_apply hV
  have hzero : (fun _ : EuclideanSpace ℝ (Fin 2) => (0 : EuclideanSpace ℝ (Fin 2)))
      =ᶠ[𝓝 y] Ψ := by
    filter_upwards [hT.mem_nhds hy] with y' hy'
    rw [hΨdef]
    exact (critAdj_critPhi (hmin y' hy') w).symm
  have hPsi0 : HasFDerivAt Ψ (0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) y :=
    (hasFDerivAt_const (0 : EuclideanSpace ℝ (Fin 2)) y).congr_of_eventuallyEq hzero.symm
  have hL : (critAdj F y ∘L ((depIns a b) ∘L (fderiv ℝ (fun y' => critS F a b y' w) y))
        + (critD2Adj F y).flip ((w : EuclideanSpace ℝ (Fin 5)) + depIns a b (critS F a b y w)))
      = 0 :=
    hPsi.unique hPsi0
  have hu := congrArg (fun L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) => L u) hL
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    zero_apply] at hu
  rw [critAdj_depIns, critD2Adj_apply,
    ← critHess_eq_adjoint (F := F) (T := T) (y := y) hT hF hy
      ((w : EuclideanSpace ℝ (Fin 5)) + depIns a b (critS F a b y w)) u] at hu
  have h4 : critMinor F a b y (fderiv ℝ (fun y' => critS F a b y' w) y u)
      = -critHess F ((w : EuclideanSpace ℝ (Fin 5)) + depIns a b (critS F a b y w)) y u :=
    eq_neg_of_add_eq_zero_left hu
  have hI := critMinor_isInvertible (F := F) (a := a) (b := b) (y := y) (hmin y hy)
  have h5 : fderiv ℝ (fun y' => critS F a b y' w) y u
      = (critMinor F a b y).inverse
          (-critHess F ((w : EuclideanSpace ℝ (Fin 5)) + depIns a b (critS F a b y w)) y u) :=
    hI.injective (by rw [h4, hI.self_apply_inverse])
  rw [h5, map_neg]
  rfl

/-- **Differentiability of the parametrisation `critPhiT`.** -/
theorem differentiableAt_critPhiT (hT : IsOpen T)
    (hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F T) (a b : Fin 5)
    (hmin : ∀ y ∈ T, Function.Bijective (minor F a b y))
    {z : EuclideanSpace ℝ (Fin 5)} (hz : depProj a b z ∈ T) :
    DifferentiableAt ℝ (critPhiT F a b) z := by
  have h1 : DifferentiableAt ℝ
      (fun z' : EuclideanSpace ℝ (Fin 5) => (depProj a b z', freePart a b z')) z :=
    DifferentiableAt.prodMk (depProj a b).differentiableAt (freePart a b).differentiableAt
  have h2 : DifferentiableAt ℝ
      (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 5) => critS F a b p.1 p.2)
      (depProj a b z, freePart a b z) :=
    (contDiffAt_critS hT hF hmin hz (freePart a b z)).differentiableAt (by simp)
  have h3 := h2.comp z h1
  have h4 : DifferentiableAt ℝ
      (fun z' : EuclideanSpace ℝ (Fin 5) =>
        depIns a b (critS F a b (depProj a b z') (freePart a b z'))) z :=
    ((ContinuousLinearMap.differentiableAt (depIns a b)
      (x := critS F a b (depProj a b z) (freePart a b z))).comp z h3)
  have h5 : DifferentiableAt ℝ
      (fun z' : EuclideanSpace ℝ (Fin 5) =>
        freePart a b z' + depIns a b (critS F a b (depProj a b z') (freePart a b z'))) z :=
    (freePart a b).differentiableAt.add h4
  have heq : (fun z' : EuclideanSpace ℝ (Fin 5) =>
        freePart a b z' + depIns a b (critS F a b (depProj a b z') (freePart a b z')))
      = critPhiT F a b := by
    funext z'
    rw [critPhiT, critPhi]
  rw [heq] at h5
  exact h5

/-- The partial derivative of the two-variable datum in the `y`-direction. -/
theorem fderiv_critS_pair_inl (hT : IsOpen T) (hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F T)
    (hmin : ∀ y ∈ T, Function.Bijective (minor F a b y)) (hy : y ∈ T)
    (w : EuclideanSpace ℝ (Fin 5)) (u : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 5) =>
        critS F a b p.1 p.2) (y, w) (u, 0)
      = fderiv ℝ (fun y' => critS F a b y' w) y u := by
  have h1 : HasFDerivAt (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 5) =>
        critS F a b p.1 p.2)
      (fderiv ℝ (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 5) =>
        critS F a b p.1 p.2) (y, w)) (y, w) :=
    ((contDiffAt_critS hT hF hmin hy w).differentiableAt (by simp)).hasFDerivAt
  have hu : HasDerivAt (fun t : ℝ => t • u) u 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const u
  have hu' : HasDerivAt (fun t : ℝ => y + t • u) u 0 := hu.const_add y
  have hcurve : HasDerivAt (fun t : ℝ => (y + t • u, w)) (u, (0 : EuclideanSpace ℝ (Fin 5))) 0 :=
    hu'.prodMk (hasDerivAt_const (0 : ℝ) w)
  have h1' : HasFDerivAt (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 5) =>
        critS F a b p.1 p.2)
      (fderiv ℝ (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 5) =>
        critS F a b p.1 p.2) (y, w))
      ((fun t : ℝ => (y + t • u, w)) 0) := by
    simpa using h1
  have hG := h1'.comp_hasDerivAt (f := fun t : ℝ => (y + t • u, w)) 0 hcurve
  have hSd := ((contDiffAt_critS_right hT hF hmin hy w).differentiableAt (by simp)).hasFDerivAt
  have hSd' : HasFDerivAt (fun y' => critS F a b y' w)
      (fderiv ℝ (fun y' => critS F a b y' w) y) ((fun t : ℝ => y + t • u) 0) := by
    simpa using hSd
  have hG' : HasDerivAt (fun t : ℝ => critS F a b (y + t • u) w)
      (fderiv ℝ (fun y' => critS F a b y' w) y u) 0 :=
    hSd'.comp_hasDerivAt (f := fun t : ℝ => y + t • u) 0 hu'
  exact hG.unique hG'

/-- **The chain rule for `critPhiT` in the direction of the `(a,b)`-plane.** Moving `z` in the
direction `depIns a b u` keeps the free part fixed and moves `depProj` by `u`. -/
theorem fderiv_critPhiT_apply_depIns (hT : IsOpen T)
    (hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F T) (a b : Fin 5) (hab : a ≠ b)
    (hmin : ∀ y ∈ T, Function.Bijective (minor F a b y))
    {z : EuclideanSpace ℝ (Fin 5)} (hz : depProj a b z ∈ T)
    (u : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (critPhiT F a b) z (depIns a b u)
      = depIns a b (fderiv ℝ (fun y' => critS F a b y' (freePart a b z)) (depProj a b z) u) := by
  have hu : HasDerivAt (fun t : ℝ => t • depIns a b u) (depIns a b u) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (depIns a b u)
  have hcurve : HasDerivAt (fun t : ℝ => z + t • depIns a b u) (depIns a b u) 0 := hu.const_add z
  have hfd := (differentiableAt_critPhiT (F := F) (T := T) (a := a) (b := b) hT hF hmin hz).hasFDerivAt
  have hfd' : HasFDerivAt (critPhiT F a b) (fderiv ℝ (critPhiT F a b) z)
      ((fun t : ℝ => z + t • depIns a b u) 0) := by simpa using hfd
  have hG := hfd'.comp_hasDerivAt (f := fun t : ℝ => z + t • depIns a b u) 0 hcurve
  have hy : HasDerivAt (fun t : ℝ => t • u) u 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const u
  have hy' : HasDerivAt (fun t : ℝ => depProj a b z + t • u) u 0 := hy.const_add _
  have hSd := ((contDiffAt_critS_right hT hF hmin hz (freePart a b z)).differentiableAt
    (by simp)).hasFDerivAt
  have hSd' : HasFDerivAt (fun y' => critS F a b y' (freePart a b z))
      (fderiv ℝ (fun y' => critS F a b y' (freePart a b z)) (depProj a b z))
      ((fun t : ℝ => depProj a b z + t • u) 0) := by simpa using hSd
  have hScurve : HasDerivAt (fun t : ℝ => critS F a b (depProj a b z + t • u) (freePart a b z))
      ((fderiv ℝ (fun y' => critS F a b y' (freePart a b z)) (depProj a b z)) u) 0 :=
    hSd'.comp_hasDerivAt (f := fun t : ℝ => depProj a b z + t • u) 0 hy'
  have hdepcurve : HasDerivAt
      (fun t : ℝ => depIns a b (critS F a b (depProj a b z + t • u) (freePart a b z)))
      (depIns a b ((fderiv ℝ (fun y' => critS F a b y' (freePart a b z)) (depProj a b z)) u)) 0 :=
    (ContinuousLinearMap.hasFDerivAt (depIns a b)
      (x := (fun t : ℝ => critS F a b (depProj a b z + t • u) (freePart a b z)) 0)).comp_hasDerivAt
        (f := fun t : ℝ => critS F a b (depProj a b z + t • u) (freePart a b z)) 0 hScurve
  have hG' : HasDerivAt
      (fun t : ℝ => freePart a b z + depIns a b (critS F a b (depProj a b z + t • u)
        (freePart a b z)))
      (depIns a b ((fderiv ℝ (fun y' => critS F a b y' (freePart a b z))
        (depProj a b z)) u)) 0 :=
    hdepcurve.const_add _
  have heq : (fun t : ℝ => critPhiT F a b (z + t • depIns a b u))
      = fun t : ℝ => freePart a b z + depIns a b (critS F a b (depProj a b z + t • u)
          (freePart a b z)) := by
    funext t
    rw [critPhiT, critPhi, map_add, map_add, map_smul, map_smul, depProj_depIns hab,
      freePart_depIns hab]
    simp
  rw [Function.comp_def] at hG
  rw [heq] at hG
  exact hG.unique hG'

/-- **The bad directions are parametrised.** Every direction `v` for which the height function
`y ↦ ⟪v, F y⟫` has a degenerate critical point in `T` is the value of `critPhiT` at some parameter
in `critSigma`. -/
theorem badSet_subset_critPhiT_image (hT : IsOpen T)
    (hdiff : ∀ y ∈ T, DifferentiableAt ℝ F y) (a b : Fin 5) (hab : a ≠ b)
    (hmin : ∀ y ∈ T, Function.Bijective (minor F a b y)) :
    badSet F T ⊆ critPhiT F a b '' critSigma F T a b := by
  rintro v ⟨y, hy, hcrit, hdeg⟩
  have hadj : critAdj F y v = 0 := (critAdj_eq_zero_iff y v (hdiff y hy)).mpr hcrit
  have hv : critPhi F a b y (freePart a b v) = v :=
    critPhi_eq_of_critAdj_eq_zero (hmin y hy) hadj
  set z : EuclideanSpace ℝ (Fin 5) := v + depIns a b (y - depProj a b v) with hz
  have hdepz : depProj a b z = y := by
    rw [hz, map_add, depProj_depIns hab]
    abel
  have hfreez : freePart a b z = freePart a b v := by
    rw [hz, map_add, freePart_depIns hab, add_zero]
  have hcritT : critPhiT F a b z = v := by
    rw [critPhiT, hdepz, hfreez, hv]
  exact ⟨z, ⟨by rw [hdepz]; exact hy, by rw [hcritT, hdepz]; exact hdeg⟩, hcritT⟩

/-- **The Jacobian of `critPhiT` is singular at `critSigma`.** This is the core of the Sard
argument: at a parameter whose direction has a degenerate Hessian, the derivative of `critPhiT`
kills the (nonzero) direction `depIns a b u` coming from a kernel vector `u` of the Hessian. -/
theorem det_fderiv_critPhiT_eq_zero (hT : IsOpen T)
    (hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F T) (a b : Fin 5) (hab : a ≠ b)
    (hmin : ∀ y ∈ T, Function.Bijective (minor F a b y))
    {z : EuclideanSpace ℝ (Fin 5)} (hz : z ∈ critSigma F T a b) :
    (fderiv ℝ (critPhiT F a b) z).det = 0 := by
  obtain ⟨u, hu_ne, hu0⟩ : ∃ u : EuclideanSpace ℝ (Fin 2), u ≠ 0 ∧
      (fderiv ℝ (fderiv ℝ (chartHeight F (critPhiT F a b z))) (depProj a b z)) u = 0 := by
    obtain ⟨x, y, hxy, hne⟩ : ∃ x y, (fderiv ℝ (fderiv ℝ (chartHeight F (critPhiT F a b z)))
        (depProj a b z)) x = (fderiv ℝ (fderiv ℝ (chartHeight F (critPhiT F a b z)))
        (depProj a b z)) y ∧ x ≠ y := by
      by_contra h
      exact hz.2 (fun x y hxy => by by_contra hne; exact h ⟨x, y, hxy, hne⟩)
    exact ⟨x - y, sub_ne_zero.mpr hne, by rw [map_sub, hxy, sub_self]⟩
  have hHu : critHess F (critPhiT F a b z) (depProj a b z) u = 0 := by
    have h1 : ⟪critHess F (critPhiT F a b z) (depProj a b z) u,
        critHess F (critPhiT F a b z) (depProj a b z) u⟫ = 0 := by
      rw [critHess_inner, hu0]
      rfl
    exact inner_self_eq_zero.mp h1
  have hker : fderiv ℝ (critPhiT F a b) z (depIns a b u) = 0 := by
    have hH : critHess F (critPhi F a b (depProj a b z) (freePart a b z)) (depProj a b z) u = 0 :=
      hHu
    rw [fderiv_critPhiT_apply_depIns (F := F) (T := T) (a := a) (b := b) hT hF hab hmin hz.1 u,
      fderiv_critS (F := F) (T := T) (a := a) (b := b) hT hF hmin hz.1 (freePart a b z) u, hH]
    simp
  have hninj : ¬ Function.Injective (fderiv ℝ (critPhiT F a b) z) := by
    intro hinj
    have hdep : depIns a b u = 0 := hinj (by rw [hker, map_zero])
    have huzero : u = 0 := by
      have := congrArg (depProj a b) hdep
      simpa [depProj_depIns hab] using this
    exact hu_ne huzero
  rw [ContinuousLinearMap.det, LinearMap.det_eq_zero_iff_ker_ne_bot]
  intro hbot
  exact hninj (LinearMap.ker_eq_bot.mp hbot)

end Basic

end Work.Drive.N2
