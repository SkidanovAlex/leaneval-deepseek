import Mathlib
import Submission.Work.Embedding.isInvertible_adjoint_comp
import Submission.Work.Embedding.smooth_implicit_function_nhd
import Submission.Work.Sard.submersion_param

namespace Work.Sard

/-- **Submersion parametrisation, smooth on a neighbourhood.**  Same setting as
`Sard/submersion_param`, but with the stronger (and more useful) conclusion that the parametrising map
`Φ` is smooth on an *open set* `O` containing the base point, and that `u (Φ y) = y.1` holds for *all*
`y ∈ O`.

Proof sketch: put `K := (fderiv ℝ u x₀).ker`, `π := Submodule.projectionOnto K C hC`,
`Θ := fun x => (u x, π x)` and `e := (hΘ).toOpenPartialHomeomorph Θ : OpenPartialHomeomorph E (G × K)`
where `hΘ : HasStrictFDerivAt Θ (fderiv ℝ Θ x₀) x₀` comes from `ContDiff.hasStrictFDerivAt`
(`Θ` is globally `C^∞`).  Then `e.symm = Θ.localInverse` and
`e.right_inv : ∀ y ∈ e.target, Θ (e.symm y) = y`, `e.left_inv : ∀ x ∈ e.source, e.symm (e x) = x`.
For the smoothness: the set `T := {y ∈ e.target | (fderiv ℝ Θ (e.symm y)).IsInvertible}` is open
(preimage of the open set of invertible continuous linear maps under a continuous map; see
`Work.Embedding.isOpen_isInvertible` in `Submission/Work/Embedding/isInvertible_adjoint_comp.lean`,
whose statement is `IsOpen {T : E →L[ℝ] F | T.IsInvertible}`), contains `Θ x₀`, and on `T` the map
`e.symm` is `C^∞` by `OpenPartialHomeomorph.contDiffAt_symm` at each point.  Take `Φ := e.symm` and
`O := T`; the remaining properties follow from `e.right_inv`, `e.left_inv` and `localInverse_apply_image`. -/
theorem submersion_smooth {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (u : E → G) (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) (x₀ : E)
    (hsurj : Function.Surjective (fderiv ℝ u x₀))
    (C : Submodule ℝ E) (hC : IsCompl (fderiv ℝ u x₀).ker C) :
    ∃ (Φ : G × (fderiv ℝ u x₀).ker → E) (O : Set (G × (fderiv ℝ u x₀).ker)),
      IsOpen O ∧ (u x₀, (Submodule.projectionOnto (fderiv ℝ u x₀).ker C hC) x₀) ∈ O ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ O ∧
      (∀ y ∈ O, u (Φ y) = y.1) ∧
      Φ (u x₀, (Submodule.projectionOnto (fderiv ℝ u x₀).ker C hC) x₀) = x₀ ∧
      (∀ᶠ x in nhds x₀,
        Φ (u x, (Submodule.projectionOnto (fderiv ℝ u x₀).ker C hC) x) = x) := by
  classical
  -- ### The projection `π` onto `K = ker (fderiv ℝ u x₀)` along `C`
  have hAu : (fderiv ℝ u x₀).range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hπran : (Submodule.projectionOnto (fderiv ℝ u x₀).ker C hC).range = ⊤ :=
    LinearMap.range_eq_top.mpr (Submodule.projectionOnto_surjective hC)
  let π : E →L[ℝ] (fderiv ℝ u x₀).ker :=
    LinearMap.toContinuousLinearMap (Submodule.projectionOnto (fderiv ℝ u x₀).ker C hC)
  have hπrange : (π : E →ₗ[ℝ] (fderiv ℝ u x₀).ker).range = ⊤ := by
    rw [show (π : E →ₗ[ℝ] (fderiv ℝ u x₀).ker) =
      Submodule.projectionOnto (fderiv ℝ u x₀).ker C hC from
      LinearMap.coe_toContinuousLinearMap _]
    exact hπran
  have hπker : (π : E →ₗ[ℝ] (fderiv ℝ u x₀).ker).ker = C := by
    rw [show (π : E →ₗ[ℝ] (fderiv ℝ u x₀).ker) =
      Submodule.projectionOnto (fderiv ℝ u x₀).ker C hC from
      LinearMap.coe_toContinuousLinearMap _]
    exact Submodule.ker_projectionOnto hC
  have hcompl : IsCompl ((fderiv ℝ u x₀) : E →ₗ[ℝ] G).ker
      (π : E →ₗ[ℝ] (fderiv ℝ u x₀).ker).ker := by
    rw [hπker]
    exact hC
  -- ### The linear isomorphism `x ↦ (fderiv ℝ u x₀ x, π x)`
  let e : E ≃L[ℝ] G × (fderiv ℝ u x₀).ker :=
    (fderiv ℝ u x₀).equivProdOfSurjectiveOfIsCompl π hAu hπrange hcompl
  have hcoe : (e : E →L[ℝ] G × (fderiv ℝ u x₀).ker) = (fderiv ℝ u x₀).prod π := rfl
  -- ### The submersion chart `Θ x = (u x, proj x)`, written as in the statement
  let Θ : E → G × (fderiv ℝ u x₀).ker :=
    fun x => (u x, (Submodule.projectionOnto (fderiv ℝ u x₀).ker C hC) x)
  have hΘeq : ∀ x : E, Θ x =
      (u x, (Submodule.projectionOnto (fderiv ℝ u x₀).ker C hC) x) := fun x => rfl
  have hnz : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hΘc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ := by
    have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (u x, π x)) := hu.prodMk π.contDiff
    exact h
  have hΘd : HasFDerivAt Θ (e : E →L[ℝ] G × (fderiv ℝ u x₀).ker) x₀ := by
    have h1 : HasFDerivAt u (fderiv ℝ u x₀) x₀ :=
      (hu.differentiable hnz).differentiableAt.hasFDerivAt
    have h2 : HasFDerivAt (fun x => π x) π x₀ := π.hasFDerivAt
    have h3 : HasFDerivAt (fun x => (u x, π x)) ((fderiv ℝ u x₀).prod π) x₀ := h1.prodMk h2
    rw [hcoe]
    exact h3
  -- ### The local inverse of `Θ` at `x₀`, and the open set where it is a submersion
  let φ : OpenPartialHomeomorph E (G × (fderiv ℝ u x₀).ker) :=
    hΘc.contDiffAt.toOpenPartialHomeomorph Θ hΘd hnz
  let Φ : G × (fderiv ℝ u x₀).ker → E := ⇑φ.symm
  let O : Set (G × (fderiv ℝ u x₀).ker) :=
    φ.target ∩ (fun y => fderiv ℝ Θ (φ.symm y)) ⁻¹'
      {A : E →L[ℝ] G × (fderiv ℝ u x₀).ker | A.IsInvertible}
  have hφcoe : (⇑φ : E → G × (fderiv ℝ u x₀).ker) = Θ := rfl
  have hx₀src : x₀ ∈ φ.source :=
    hΘc.contDiffAt.mem_toOpenPartialHomeomorph_source hΘd hnz
  have hbase : ⇑φ.symm (Θ x₀) = x₀ := by
    have h := φ.left_inv hx₀src
    rw [hφcoe] at h
    exact h
  have hbase_inv : (fderiv ℝ Θ (⇑φ.symm (Θ x₀))).IsInvertible := by
    rw [hbase, hΘd.fderiv]
    exact ⟨e, rfl⟩
  -- ### `O` is open
  have hO : IsOpen O := by
    have hcontfd : Continuous (fderiv ℝ Θ) := hΘc.continuous_fderiv hnz
    have hg : ContinuousOn (fun y => fderiv ℝ Θ (φ.symm y)) φ.target :=
      hcontfd.comp_continuousOn φ.continuousOn_symm
    exact hg.isOpen_inter_preimage φ.open_target
      (Work.Embedding.isOpen_isInvertible (E := E) (F := G × (fderiv ℝ u x₀).ker))
  -- ### `Φ` is `C^∞` on `O`
  have hΦsmooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ O := by
    rw [hO.contDiffOn_iff]
    intro y hy
    have hy' : (fderiv ℝ Θ (φ.symm y)).IsInvertible := hy.2
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑φ) (φ.symm y) := hΘc.contDiffAt
    have hfd : HasFDerivAt Θ (fderiv ℝ Θ (φ.symm y)) (φ.symm y) :=
      (hΘc.contDiffAt.differentiableAt hnz).hasFDerivAt
    obtain ⟨e', he'⟩ := hy'
    have h2 : HasFDerivAt (⇑φ) (e' : E →L[ℝ] G × (fderiv ℝ u x₀).ker) (φ.symm y) :=
      hfd.congr_fderiv he'.symm
    exact φ.contDiffAt_symm hy.1 h2 h1
  refine ⟨Φ, O, hO, ?_, hΦsmooth, ?_, ?_, ?_⟩
  · rw [← hΘeq x₀]
    exact ⟨φ.map_source hx₀src, hbase_inv⟩
  · intro y hy
    have h := congrArg Prod.fst (φ.right_inv hy.1)
    rw [hφcoe] at h
    simpa only [Θ, Φ] using h
  · rw [← hΘeq x₀]
    exact hbase
  · filter_upwards [φ.open_source.mem_nhds hx₀src] with x hx
    have h := φ.left_inv hx
    rw [hφcoe] at h
    rw [← hΘeq x]
    exact h

end Work.Sard
