/-
  Work.WilE2.Ebc — `component_locally_level`.

  Let `F : ℝᵏ → ℝ` be `C¹` and regular on its zero set `N = {F = 0}` (i.e. `fderiv ℝ F z ≠ 0`
  whenever `F z = 0`).  Then every point `z'` of `N` has a neighbourhood in `N` contained in the
  connected component of `z'`: a regular level set of a `C¹` function is locally connected, so
  its connected components are open (equivalently: `N` is locally a graph of a continuous
  function, and a graph over a ball is preconnected).

  The proof is organised as

  * `local_component_of_regular_zero` — the pointwise, local statement: every zero of `F`
    sufficiently close to a regular zero `z` lies in the connected component of `z` inside
    `{F = 0}`.  This is the analytic content; it is reduced to the (Banach-space) implicit
    function theorem `zero_set_component_locality_general` applied to
    `G (x, t) = F (x + t • w)`, where `w` is a direction with `fderiv ℝ F z w = 1`
    (`G`'s zero set is locally a graph of the implicit function over its first argument, and a
    graph over a convex ball is preconnected).
  * `component_locally_level` — the requested statement, obtained from the pointwise form by
    `Metric.eventually_nhds_iff` and the fact that `connectedComponentIn {F = 0} z'` agrees with
    `connectedComponentIn {F = 0} z` whenever `z'` lies in the latter.
-/
import Mathlib
import Submission.Work.WilE2.Ebc.Defs
import Submission.Work.WilE2.Ebc.zero_set_component_locality_general

set_option autoImplicit false

namespace Work.WilE2.Ebc

open scoped Topology
open Filter

/-- **Local connectedness of a regular level set (pointwise form).**

If `F : ℝᵏ → ℝ` is `C¹` at a zero `z` with `fderiv ℝ F z ≠ 0`, then every zero of `F`
sufficiently close to `z` lies in the connected component of `z` inside the zero set `{F = 0}`.

Choose a direction `w` with `fderiv ℝ F z w = 1` and apply the implicit function theorem to
`G (x, t) = F (x + t • w)`: the differential of `G` in its second argument at `(z, 0)` is the
identity, so the zeros of `G` near `(z, 0)` are the graph of a continuous function of the first
variable, and a graph over a ball is preconnected, hence contained in the connected component of
`(z, 0)` in `{G = 0}`.  Mapping this back along the continuous linear map
`(x, t) ↦ x + t • w` (which sends `(z, 0)` to `z` and `{G = 0}` into `{F = 0}`) transports the
conclusion to `{F = 0}`. -/
theorem local_component_of_regular_zero {k : ℕ} (F : (Fin k → ℝ) → ℝ) (z : Fin k → ℝ)
    (hF : ContDiffAt ℝ 1 F z) (hz : F z = 0) (hreg : fderiv ℝ F z ≠ 0) :
    ∀ᶠ y in nhds z, F y = 0 → y ∈ connectedComponentIn {y : Fin k → ℝ | F y = 0} z := by
  classical
  -- a direction `w` with `fderiv ℝ F z w = 1`
  obtain ⟨w, hw⟩ : ∃ w : Fin k → ℝ, fderiv ℝ F z w = 1 := by
    obtain ⟨v, hv⟩ : ∃ v : Fin k → ℝ, fderiv ℝ F z v ≠ 0 := by
      by_contra h
      push_neg at h
      exact hreg (ContinuousLinearMap.ext fun x => by simpa using h x)
    exact ⟨(fderiv ℝ F z v)⁻¹ • v, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv]⟩
  -- the linear change of variables `(x, t) ↦ x + t • w`
  set φ : (Fin k → ℝ) × ℝ →L[ℝ] (Fin k → ℝ) :=
    ContinuousLinearMap.fst ℝ (Fin k → ℝ) ℝ +
      (ContinuousLinearMap.snd ℝ (Fin k → ℝ) ℝ).smulRight w with hφdef
  have hφ_apply : ∀ p : (Fin k → ℝ) × ℝ, φ p = p.1 + p.2 • w := by
    intro p
    rw [hφdef]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply]
    rfl
  have hφz0 : φ (z, 0) = z := by rw [hφ_apply]; simp
  -- `G := F ∘ φ`
  have hFφ : ContDiffAt ℝ 1 F (φ (z, 0)) := by rw [hφz0]; exact hF
  have hφcd : ContDiffAt ℝ 1 (⇑φ : (Fin k → ℝ) × ℝ → (Fin k → ℝ)) (z, 0) :=
    (ContinuousLinearMap.contDiff φ : ContDiff ℝ 1 ⇑φ).contDiffAt
  have hGcdf : ContDiffAt ℝ 1 (fun p : (Fin k → ℝ) × ℝ => F (φ p)) (z, 0) :=
    hFφ.comp (z, 0) hφcd
  have hG0 : (fun p : (Fin k → ℝ) × ℝ => F (φ p)) (z, 0) = 0 := by
    show F (φ (z, 0)) = 0
    rw [hφz0, hz]
  have hFd : HasFDerivAt F (fderiv ℝ F z) (φ (z, 0)) := by
    rw [hφz0]
    exact (hF.differentiableAt (by norm_num)).hasFDerivAt
  have hFG : HasFDerivAt (fun p : (Fin k → ℝ) × ℝ => F (φ p)) ((fderiv ℝ F z).comp φ) (z, 0) :=
    hFd.comp (z, 0) φ.hasFDerivAt
  have hderiv : fderiv ℝ (fun p : (Fin k → ℝ) × ℝ => F (φ p)) (z, 0) =
      (fderiv ℝ F z).comp φ := hFG.fderiv
  -- the differential of `G` in its second variable is the identity
  have hcompSL : ((fderiv ℝ (fun p : (Fin k → ℝ) × ℝ => F (φ p)) (z, 0))
      ∘SL ContinuousLinearMap.inr ℝ (Fin k → ℝ) ℝ) = ContinuousLinearMap.id ℝ ℝ := by
    rw [hderiv]
    ext t
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.id_apply]
    rw [hφ_apply]
    simp [hw]
  have hif : ((fderiv ℝ (fun p : (Fin k → ℝ) × ℝ => F (φ p)) (z, 0))
      ∘SL ContinuousLinearMap.inr ℝ (Fin k → ℝ) ℝ).IsInvertible := by
    rw [hcompSL]
    exact ⟨ContinuousLinearEquiv.refl ℝ ℝ, rfl⟩
  -- the implicit function theorem for `G`, with the (tautological) target `{G = 0}`
  have hcore := zero_set_component_locality_general (fun p : (Fin k → ℝ) × ℝ => F (φ p))
    (z, 0) hGcdf hG0 hif {p : (Fin k → ℝ) × ℝ | F (φ p) = 0}
    (Eventually.of_forall fun _ hv => hv)
  -- the image of the component of `(z,0)` under `φ` lies in the component of `z`
  have hpre : IsPreconnected ((⇑φ : (Fin k → ℝ) × ℝ → (Fin k → ℝ)) ''
      connectedComponentIn {p : (Fin k → ℝ) × ℝ | F (φ p) = 0} (z, 0)) :=
    (isPreconnected_connectedComponentIn (x := (z, 0))
      (F := {p : (Fin k → ℝ) × ℝ | F (φ p) = 0})).image ⇑φ φ.continuous.continuousOn
  have hmem0 : (z, 0) ∈ connectedComponentIn {p : (Fin k → ℝ) × ℝ | F (φ p) = 0} (z, 0) :=
    IsPreconnected.subset_connectedComponentIn (s := {(z, 0)}) (x := (z, 0))
      (F := {p : (Fin k → ℝ) × ℝ | F (φ p) = 0}) isPreconnected_singleton
      (by simp)
      (by rw [Set.singleton_subset_iff]; simpa [hφ_apply] using hz)
      (by simp)
  have hzimg : z ∈ (⇑φ : (Fin k → ℝ) × ℝ → (Fin k → ℝ)) ''
      connectedComponentIn {p : (Fin k → ℝ) × ℝ | F (φ p) = 0} (z, 0) :=
    ⟨(z, 0), hmem0, hφz0⟩
  have hsF : (⇑φ : (Fin k → ℝ) × ℝ → (Fin k → ℝ)) ''
      connectedComponentIn {p : (Fin k → ℝ) × ℝ | F (φ p) = 0} (z, 0) ⊆
      {y : Fin k → ℝ | F y = 0} := by
    rintro y ⟨p, hp, rfl⟩
    exact connectedComponentIn_subset {p : (Fin k → ℝ) × ℝ | F (φ p) = 0} (z, 0) hp
  have hcomp := IsPreconnected.subset_connectedComponentIn hpre hzimg hsF
  -- transport back
  have hι : Tendsto (fun y : Fin k → ℝ => (y, (0 : ℝ))) (nhds z) (nhds (z, 0)) :=
    (continuous_id.prodMk continuous_const).continuousAt
  filter_upwards [hι.eventually hcore] with y hy
  intro hyF
  have hmem : (y, 0) ∈ connectedComponentIn {p : (Fin k → ℝ) × ℝ | F (φ p) = 0} (z, 0) :=
    hy (by show F (φ (y, 0)) = 0; rw [hφ_apply]; simp [hyF])
  have hφy0 : φ (y, 0) = y := by rw [hφ_apply]; simp
  exact hφy0 ▸ hcomp ⟨(y, 0), hmem, rfl⟩

/-- **The components of a regular level set are open.**  If `F : ℝᵏ → ℝ` is `C¹` and its
differential is non-zero at every zero, then every point `z'` of the connected component of `z`
inside `{F = 0}` has a Euclidean ball around it all of whose zeros of `F` lie in that same
component. -/
theorem component_locally_level {k : ℕ} (F : (Fin k → ℝ) → ℝ) (hF : ContDiff ℝ 1 F)
    (hreg : ∀ z, F z = 0 → fderiv ℝ F z ≠ 0) (z : Fin k → ℝ) :
    ∀ z' ∈ connectedComponentIn {y : Fin k → ℝ | F y = 0} z, ∃ ε : ℝ, 0 < ε ∧
      ∀ y : Fin k → ℝ, dist y z' < ε → F y = 0 →
        y ∈ connectedComponentIn {y : Fin k → ℝ | F y = 0} z := by
  intro z' hz'
  have hz'F : F z' = 0 := connectedComponentIn_subset {y : Fin k → ℝ | F y = 0} z hz'
  have hcore : ∀ᶠ y in nhds z', F y = 0 →
      y ∈ connectedComponentIn {y : Fin k → ℝ | F y = 0} z' :=
    local_component_of_regular_zero F z' hF.contDiffAt hz'F (hreg z' hz'F)
  rw [Metric.eventually_nhds_iff] at hcore
  obtain ⟨ε, hε, hε'⟩ := hcore
  refine ⟨ε, hε, fun y hy hyF => ?_⟩
  have hEq : connectedComponentIn {y : Fin k → ℝ | F y = 0} z =
      connectedComponentIn {y : Fin k → ℝ | F y = 0} z' :=
    connectedComponentIn_eq hz'
  rw [hEq]
  exact hε' hy hyF

end Work.WilE2.Ebc
