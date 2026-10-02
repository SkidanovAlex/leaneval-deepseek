import Mathlib
import Submission.Work.Tubular.TubeTransversalityOfChart

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.PTGeometric

/-- **The derivative of `ℓ ∘ normalCoord ∘ P` is onto at a zero of the normal coordinate.**

`E : EmbeddingData V (8+k)` is an embedding of a closed `8`-manifold, `C` a tube chart of it,
`P : ℝ^{8+k+1} → ℝ^{8+k}` a map which is `C^∞` on the open set `W`, whose derivative at every point
of `W` is surjective, and `y ∈ W` is such that `P y` lies in the open tube and has vanishing normal
coordinate, so `P y = E.e x` is a point of the embedded manifold.  If `ℓ : ℝ^{8+k} → ℝ^k` is
injective on the normal space `ν_x = normalSpace E x` then the derivative of
`z ↦ ℓ (normalCoord E C (P z))` at `y` is surjective. -/
theorem fderiv_tubeCoord_surjective {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (ℓ : Work.Tubular.Euc (8 + k) →L[ℝ] EuclideanSpace ℝ (Fin k))
    {P : EuclideanSpace ℝ (Fin (8 + k + 1)) → Work.Tubular.Euc (8 + k)}
    {W : Set (EuclideanSpace ℝ (Fin (8 + k + 1)))}
    (hW : IsOpen W) (hPsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P W)
    (hPsurj : ∀ y ∈ W, Function.Surjective (fderiv ℝ P y))
    {y : EuclideanSpace ℝ (Fin (8 + k + 1))} (hy : y ∈ W)
    (htube : P y ∈ C.openTube)
    (hnc : Work.Tubular.normalCoord E C (P y) = 0)
    (hinj : ∀ (x : V.pt), E.e x = P y → ∀ z ∈ Work.Tubular.normalSpace E x, ℓ z = 0 → z = 0) :
    Function.Surjective (fderiv ℝ (fun z => ℓ (Work.Tubular.normalCoord E C (P z))) y) := by
  -- `P y` is a point of the embedded manifold: pick its foot `x`.
  obtain ⟨x, hx⟩ := (Work.Tubular.normalCoord_eq_zero_iff E C htube).1 hnc
  -- the derivative of the normal coordinate at `P y` has range exactly the normal space `ν_x`
  have hLrange : (fderiv ℝ (Work.Tubular.normalCoord E C) (P y)).toLinearMap.range
      = Work.Tubular.normalSpace E x := by
    have h := (Work.Tubular.TubeTransversalityOfChart E C).mfderiv_range x
    rw [hx] at h
    rw [mfderiv_eq_fderiv] at h
    exact h
  -- the chain rule
  have hcomp : fderiv ℝ (fun z => ℓ (Work.Tubular.normalCoord E C (P z))) y
      = ℓ.comp ((fderiv ℝ (Work.Tubular.normalCoord E C) (P y)).comp (fderiv ℝ P y)) := by
    have hP_at : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P y := hPsm.contDiffAt (hW.mem_nhds hy)
    have hP_hfd : HasFDerivAt P (fderiv ℝ P y) y :=
      (hP_at.differentiableAt (by simp)).hasFDerivAt
    have hnc_at : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Tubular.normalCoord E C) (P y) :=
      (ContMDiffOn.contDiffOn (Work.Tubular.contMDiffOn_normalCoord E C)).contDiffAt
        (C.openTube_isOpen.mem_nhds htube)
    have hnc_hfd : HasFDerivAt (Work.Tubular.normalCoord E C)
        (fderiv ℝ (Work.Tubular.normalCoord E C) (P y)) (P y) :=
      (hnc_at.differentiableAt (by simp)).hasFDerivAt
    have h1 : HasFDerivAt (fun z => Work.Tubular.normalCoord E C (P z))
        ((fderiv ℝ (Work.Tubular.normalCoord E C) (P y)).comp (fderiv ℝ P y)) y :=
      hnc_hfd.comp y hP_hfd
    have h2 := (ContinuousLinearMap.hasFDerivAt ℓ).comp y h1
    have h3 := h2.fderiv
    rw [show (⇑ℓ ∘ fun z => Work.Tubular.normalCoord E C (P z))
          = (fun z => ℓ (Work.Tubular.normalCoord E C (P z))) from rfl] at h3
    exact h3
  rw [hcomp]
  intro v
  -- `ℓ` is an isomorphism from `ν_x` onto `ℝ^k`, because it is injective and the two spaces have
  -- the same dimension `k`
  have hsurj_ℓ : ∃ w ∈ Work.Tubular.normalSpace E x, ℓ w = v := by
    let φ : (Work.Tubular.normalSpace E x) →ₗ[ℝ] EuclideanSpace ℝ (Fin k) :=
      (ℓ : Work.Tubular.Euc (8 + k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)).comp
        (Work.Tubular.normalSpace E x).subtype
    have hker : LinearMap.ker φ = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro w hw
      rw [LinearMap.mem_ker] at hw
      exact Subtype.ext (hinj x hx w w.2 (by simpa [φ, ContinuousLinearMap.comp_apply,
        LinearMap.comp_apply] using hw))
    have hfr : Module.finrank ℝ (Work.Tubular.normalSpace E x)
        = Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) := by
      rw [Work.Tubular.finrank_normalSpace E x, finrank_euclideanSpace]
      simp
    have hsurjφ : Function.Surjective φ :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1
        (LinearMap.ker_eq_bot.mp hker)
    obtain ⟨w, hw⟩ := hsurjφ v
    exact ⟨w, w.2, by simpa [φ, LinearMap.comp_apply] using hw⟩
  obtain ⟨w, hwS, hwv⟩ := hsurj_ℓ
  -- every vector of the normal space is in the range of the derivative of the normal coordinate
  obtain ⟨u, hu⟩ : ∃ u : Work.Tubular.Euc (8 + k),
      fderiv ℝ (Work.Tubular.normalCoord E C) (P y) u = w := by
    have hw : w ∈ (fderiv ℝ (Work.Tubular.normalCoord E C) (P y)).toLinearMap.range := by
      rw [hLrange]; exact hwS
    exact LinearMap.mem_range.mp hw
  -- `u` is in the range of the derivative of `P` at `y`
  obtain ⟨t, ht⟩ := hPsurj y hy u
  exact ⟨t, by simp only [ContinuousLinearMap.comp_apply]; rw [ht, hu, hwv]⟩

end Work.PTGeometric
