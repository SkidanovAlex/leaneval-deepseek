import Mathlib
/-!
# Generic C^1 inverse-function theorem package

Task: prove `c1_local_inverse` below.
-/
open ContinuousLinearMap
open scoped ContDiff Topology
open Set Metric

namespace Submission

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section

/-- At a point `v` of the ball where `exp` is `C^1` with invertible derivative, the local inverse
`P.symm` produced by the inverse function theorem at `0` is `C^1` at `exp v`. -/
private lemma contDiffAt_symm_of_invDeriv {exp : E → E} {ρE : ℝ} {P : OpenPartialHomeomorph E E}
    (hPe : (P : E → E) = exp)
    (hExpC1 : ContDiffOn ℝ 1 exp (ball 0 ρE))
    (hInvDeriv : ∀ v ∈ ball 0 ρE, ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = fderiv ℝ exp v)
    {v : E} (hv : v ∈ ball (0 : E) ρE) (hvs : v ∈ P.source) :
    ContDiffAt ℝ 1 (P.symm) (exp v) := by
  have hcv : ContDiffAt ℝ 1 exp v := hExpC1.contDiffAt (Metric.isOpen_ball.mem_nhds hv)
  rcases hInvDeriv v hv with ⟨e, he⟩
  have hfd : HasFDerivAt exp (fderiv ℝ exp v) v :=
    (hcv.differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)).hasFDerivAt
  have hfv : HasFDerivAt exp ((e : E →L[ℝ] E)) v := by simpa [he] using hfd
  have hstrict : HasStrictFDerivAt exp ((e : E →L[ℝ] E)) v :=
    hcv.hasStrictFDerivAt' hfv (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hns : P.source ∈ 𝓝 v := P.open_source.mem_nhds hvs
  have hp_left : ∀ᶠ x in 𝓝 v, P.symm (exp x) = x := by
    filter_upwards [hns] with x hx
    rw [← hPe]
    exact P.left_inv hx
  have huniq : ∀ᶠ y in 𝓝 (exp v),
      P.symm y = HasStrictFDerivAt.localInverse exp e v hstrict y :=
    HasStrictFDerivAt.localInverse_unique hstrict hp_left
  have hlinv : ContDiffAt ℝ 1 (HasStrictFDerivAt.localInverse exp e v hstrict) (exp v) :=
    ContDiffAt.to_localInverse hcv hfv (by norm_num : (1 : ℕ∞ω) ≠ 0)
  exact hlinv.congr_of_eventuallyEq huniq

theorem c1_local_inverse {x₀ : E} (exp : E → E) {ρE : ℝ} (hρE : 0 < ρE)
    (hExpC1 : ContDiffOn ℝ 1 exp (ball 0 ρE))
    (hExp0 : exp 0 = x₀)
    (hFderiv0 : HasFDerivAt exp (ContinuousLinearMap.id ℝ E) 0)
    (hInvDeriv : ∀ v ∈ ball 0 ρE, ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = fderiv ℝ exp v) :
    ∃ U ∈ 𝓝 (0 : E), ∃ V ∈ 𝓝 x₀, ∃ inv : E → E,
      Set.MapsTo exp U V ∧ Function.Injective (fun v : U => exp v.1) ∧
      Set.SurjOn exp U V ∧ ContinuousOn exp U ∧
      (∀ y ∈ V, inv y ∈ U ∧ exp (inv y) = y) ∧
      (∀ v ∈ U, inv (exp v) = v) ∧
      ContDiffOn ℝ 1 inv V := by
  classical
  -- The inverse function theorem at `0` provides an `OpenPartialHomeomorph` `P`.
  have hc0 : ContDiffAt ℝ 1 exp (0 : E) := hExpC1.contDiffAt (Metric.ball_mem_nhds (0 : E) hρE)
  have hf0 : HasFDerivAt exp ((ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E)) (0 : E) := by
    simpa using hFderiv0
  let hn0 : (1 : ℕ∞ω) ≠ 0 := by norm_num
  let P : OpenPartialHomeomorph E E := hc0.toOpenPartialHomeomorph exp hf0 hn0
  have hP0 : (0 : E) ∈ P.source := by
    have := ContDiffAt.mem_toOpenPartialHomeomorph_source hc0 hf0 hn0
    simpa [P] using this
  have hPx0 : x₀ ∈ P.target := by
    have := ContDiffAt.image_mem_toOpenPartialHomeomorph_target hc0 hf0 hn0
    simpa [P, hExp0] using this
  have hPe : (P : E → E) = exp := by simp [P]
  -- Choose a small radius `ρU` such that `ball 0 ρU ⊆ P.source` and `ball 0 ρU ⊆ ball 0 ρE`.
  have hsrc_nhds : P.source ∩ ball (0 : E) ρE ∈ 𝓝 (0 : E) :=
    Filter.inter_mem (P.open_source.mem_nhds hP0) (Metric.ball_mem_nhds (0 : E) hρE)
  obtain ⟨ρU, hρU_pos, hρU_sub⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ball (0 : E) ρ ⊆ P.source ∩ ball (0 : E) ρE := by
    rcases (Metric.nhds_basis_ball.mem_iff).mp hsrc_nhds with ⟨r, hr0, hsub⟩
    exact ⟨r, hr0, hsub⟩
  let U : Set E := ball (0 : E) ρU
  let V : Set E := exp '' U
  have hU_open : IsOpen U := isOpen_ball
  have hU_nhds : U ∈ 𝓝 (0 : E) := by
    simpa [U] using (Metric.ball_mem_nhds (0 : E) hρU_pos)
  have hU_source : U ⊆ P.source := by
    intro x hx
    exact (hρU_sub hx).1
  have hU_ballE : U ⊆ ball (0 : E) ρE := by
    intro x hx
    exact (hρU_sub hx).2
  have hU0 : (0 : E) ∈ U := by simpa [U] using hρU_pos
  -- `V` is open and is a neighbourhood of `x₀`.
  have hV_open : IsOpen V := by
    -- `exp = P` as global functions, so `V = P '' U`; `P` maps open subsets of its source to open sets.
    have hV_eq : V = P '' U := by
      ext y
      constructor
      · rintro ⟨x, hx, hy⟩
        exact ⟨x, hx, by simpa [P] using hy⟩
      · rintro ⟨x, hx, hy⟩
        exact ⟨x, hx, by simpa [P] using hy⟩
    rw [hV_eq]
    exact P.isOpen_image_of_subset_source hU_open hU_source
  have hV_nhds : V ∈ 𝓝 x₀ := by
    exact hV_open.mem_nhds (by
      refine ⟨(0 : E), hU0, ?_⟩
      exact hExp0)
  -- inverse laws
  have hMapsTo : Set.MapsTo exp U V := by
    intro x hx
    exact mem_image_of_mem exp hx
  have hInj : Function.Injective (fun v : U => exp v.1) := by
    intro a b hab
    apply Subtype.ext
    have ha : a.1 ∈ P.source := hU_source a.2
    have hb : b.1 ∈ P.source := hU_source b.2
    apply P.injOn ha hb
    simpa [P] using hab
  have hSurj : Set.SurjOn exp U V := by
    intro y hy
    simpa [V] using hy
  have hCont : ContinuousOn exp U := hExpC1.continuousOn.mono hU_ballE
  have hInv1 : ∀ y ∈ V, P.symm y ∈ U ∧ exp (P.symm y) = y := by
    intro y hy
    rcases hy with ⟨v, hvU, hyv⟩
    have hvs : v ∈ P.source := hU_source hvU
    have hsy : P.symm y = v := by
      rw [← hyv, ← hPe]
      exact P.left_inv hvs
    constructor
    · rw [hsy]
      exact hvU
    · rw [hsy, hyv]
  have hInv2 : ∀ v ∈ U, P.symm (exp v) = v := by
    intro v hvU
    have hvs : v ∈ P.source := hU_source hvU
    rw [← hPe]
    exact P.left_inv hvs
  have hContDiff : ContDiffOn ℝ 1 (P.symm) V := by
    rw [hV_open.contDiffOn_iff]
    intro y hy
    rcases hy with ⟨v, hvU, hyv⟩
    rw [← hyv]
    exact contDiffAt_symm_of_invDeriv (exp := exp) (P := P) hPe hExpC1 hInvDeriv
      (hU_ballE hvU) (hU_source hvU)
  refine ⟨U, hU_nhds, V, hV_nhds, P.symm, hMapsTo, hInj, hSurj, hCont, hInv1, hInv2, hContDiff⟩

end
end Submission
