import Mathlib
import Submission.Work.Drive.Push.localInverseContDiffOn

/-!
# The smooth local inverse function theorem, target contained in the source

`Work.Drive.N2.localInverseContDiffOnNhd` is the version of the smooth local inverse function
theorem in which the local inverse `σ` is required not only to invert `g` on its domain `S` but
also to *land in* the neighbourhood `W` of `p` (`∀ u ∈ S, σ u ∈ W`).

The mathematics is the same inverse function theorem argument as in
`Work.Drive.Push.localInverseContDiffOn` (imported here): one takes the local homeomorphism `Φ`
produced by the inverse function theorem at `p` and cuts the target down to the open locus where
the derivative of `g` is invertible.  Writing `S = Φ.target ∩ σ ⁻¹' V` with
`V = {x | Injective (fderiv ℝ g x)} ∩ U` and `W = Φ.source ∩ U`, the extra requirement is
immediate: `σ = Φ.symm` maps `Φ.target` into `Φ.source`, and on `σ ⁻¹' V` its values lie in `U`.
-/

namespace Work.Drive.N2

open scoped ContDiff

/-- **The smooth local inverse function theorem**, with the local inverse mapping the local
codomain `S` into the local domain `W` of `p`. -/
theorem localInverseContDiffOnNhd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (g : E → E) (U : Set E) (hU : IsOpen U)
    (hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g U) (p : E) (hp : p ∈ U)
    (hinj : Function.Injective (fderiv ℝ g p)) :
    ∃ (S W : Set E) (σ : E → E),
      IsOpen S ∧ IsOpen W ∧ W ⊆ U ∧ g p ∈ S ∧ p ∈ W ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ S ∧
      (∀ u ∈ S, σ u ∈ W) ∧
      (∀ u ∈ S, g (σ u) = u) ∧
      (∀ x ∈ W, σ (g x) = x) := by
  have hca : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g p := hg.contDiffAt (hU.mem_nhds hp)
  have hnz : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hderiv : HasFDerivAt g (fderiv ℝ g p) p := (hca.differentiableAt hnz).hasFDerivAt
  -- the derivative at `p`, upgraded to a continuous linear equivalence
  let ep : E ≃L[ℝ] E :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ g p).toLinearMap (by simpa using hinj))
      |>.toContinuousLinearEquiv
  have hep : (ep : E →L[ℝ] E) = fderiv ℝ g p := by ext v; simp [ep]
  have hderiv' : HasFDerivAt g (ep : E →L[ℝ] E) p := by rw [hep]; exact hderiv
  -- the inverse function theorem at `p`
  let Φ : OpenPartialHomeomorph E E := hca.toOpenPartialHomeomorph g hderiv' hnz
  -- the open locus where the derivative of `g` is invertible
  let V : Set E := {x : E | Function.Injective (fderiv ℝ g x)} ∩ U
  have hVopen : IsOpen V := Work.Drive.Push.isOpen_injLocus g U hU hg
  let σ : E → E := Φ.symm
  let S : Set E := Φ.target ∩ σ ⁻¹' V
  let W : Set E := Φ.source ∩ U
  have hp_source : p ∈ Φ.source := hca.mem_toOpenPartialHomeomorph_source hderiv' hnz
  have hgp_target : g p ∈ Φ.target :=
    hca.image_mem_toOpenPartialHomeomorph_target hderiv' hnz
  have hsymm_gp : σ (g p) = p := by
    have h := Φ.left_inv hp_source
    simpa [σ, Φ] using h
  have hSopen : IsOpen S := by
    have hcont : ContinuousOn σ Φ.target := Φ.continuousOn_invFun
    exact hcont.isOpen_inter_preimage Φ.open_target hVopen
  have hWopen : IsOpen W := Φ.open_source.inter hU
  have hWU : W ⊆ U := fun _ hx => hx.2
  have hpS : g p ∈ S := by
    refine ⟨hgp_target, ?_⟩
    simp only [Set.mem_preimage]
    rw [hsymm_gp]
    exact ⟨hinj, hp⟩
  have hpW : p ∈ W := ⟨hp_source, hp⟩
  -- `σ` is `C^∞` at every point of the target at which the derivative of `g` is invertible
  have hσ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ S := by
    rw [hSopen.contDiffOn_iff]
    intro y hy
    have hyt : y ∈ Φ.target := hy.1
    have hyV : σ y ∈ V := hy.2
    have hyU : σ y ∈ U := hyV.2
    have hyinj : Function.Injective (fderiv ℝ g (σ y)) := hyV.1
    let ey : E ≃L[ℝ] E :=
      (LinearEquiv.ofInjectiveEndo (fderiv ℝ g (σ y)).toLinearMap (by simpa using hyinj))
        |>.toContinuousLinearEquiv
    have hey : (ey : E →L[ℝ] E) = fderiv ℝ g (σ y) := by ext v; simp [ey]
    have hF : HasFDerivAt (Φ : E → E) (ey : E →L[ℝ] E) (σ y) := by
      have h := ((hg.contDiffAt (hU.mem_nhds hyU)).differentiableAt hnz).hasFDerivAt
      rw [hey]
      exact h
    have hG : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φ : E → E) (σ y) :=
      hg.contDiffAt (hU.mem_nhds hyU)
    have := Φ.contDiffAt_symm hyt hF hG
    simpa [σ] using this
  -- the extra requirement: `σ` maps `S` into `W = Φ.source ∩ U`
  have hσW : ∀ u ∈ S, σ u ∈ W := by
    intro u hu
    exact ⟨Φ.mapsTo_symm hu.1, hu.2.2⟩
  exact ⟨S, W, σ, hSopen, hWopen, hWU, hpS, hpW, hσ, hσW,
    fun u hu => Φ.right_inv hu.1, fun x hx => Φ.left_inv hx.1⟩

end Work.Drive.N2
