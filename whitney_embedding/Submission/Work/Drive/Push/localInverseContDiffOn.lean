import Mathlib

/-!
# The smooth local inverse function theorem, in the form needed by the drive

`Work.Drive.Push.localInverseContDiffOn`: if `g : E → E` is `C^∞` on an open set `U`, if `p ∈ U`, and
if the derivative `fderiv ℝ g p` is injective (equivalently, invertible, `E` being finite
dimensional), then `g` has a smooth local inverse: there are open sets `S ∋ g p`, `W ∋ p` with
`W ⊆ U` and a function `σ` that is `C^∞` on `S`, with `g ∘ σ = id` on `S` and `σ ∘ g = id` on `W`.

The proof is the inverse function theorem.  Mathlib already provides it in the `C^r` case
(`ContDiffAt.toOpenPartialHomeomorph`, `ContDiffAt.to_localInverse`, and the "easy part"
`OpenPartialHomeomorph.contDiffAt_symm`), but the inverse function theorem at a *single* point only
produces a local homeomorphism `Φ`: the smoothness locus of `Φ.symm` inside `Φ.target` is the set
of points `y` where `fderiv ℝ g (Φ.symm y)` is invertible — which is *not* all of `Φ.target` in
general (e.g. `x ↦ x³` restricted to a neighbourhood of `1` is a local homeomorphism whose inverse
is not differentiable where the function's derivative vanishes).  So the target has to be cut down
to the (open) invertibility locus of the derivative of `g`, and that is the one extra ingredient
proved here: the injective endomorphisms of a finite dimensional space are an open subset of
`E →L[ℝ] E`.
-/

namespace Work.Drive.Push

open scoped ContDiff

/-- For a continuous linear endomorphism of a finite dimensional space, injectivity is equivalent
to being a unit of the ring `E →L[ℝ] E` (nothing else is needed: injective ⟹ bijective). -/
lemma injective_iff_isUnit_clm {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    (f : E →L[ℝ] E) : Function.Injective f ↔ IsUnit f :=
  ⟨fun h => ContinuousLinearMap.isUnit_iff_bijective.mpr
      ⟨h, LinearMap.injective_iff_surjective.mp h⟩,
    fun h => (ContinuousLinearMap.isUnit_iff_bijective.mp h).1⟩

/-- The locus where the derivative of a `C^1` map on an open set is injective is open. -/
lemma isOpen_injLocus {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    (g : E → E) (U : Set E) (hU : IsOpen U)
    (hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g U) :
    IsOpen ({x : E | Function.Injective (fderiv ℝ g x)} ∩ U) := by
  have hcont : ContinuousOn (fun x : E => fderiv ℝ g x) U :=
    hg.continuousOn_fderiv_of_isOpen hU (by simp)
  have h1 : IsOpen (U ∩ (fun x : E => fderiv ℝ g x) ⁻¹' {f : E →L[ℝ] E | IsUnit f}) :=
    hcont.isOpen_inter_preimage hU Units.isOpen
  have hset : {x : E | Function.Injective (fderiv ℝ g x)} ∩ U =
      U ∩ (fun x : E => fderiv ℝ g x) ⁻¹' {f : E →L[ℝ] E | IsUnit f} := by
    ext x
    exact ⟨fun hx => ⟨hx.2, (injective_iff_isUnit_clm _).mp hx.1⟩,
      fun hx => ⟨(injective_iff_isUnit_clm _).mpr hx.2, hx.1⟩⟩
  rw [hset]
  exact h1

/-- **The smooth local inverse function theorem.** -/
theorem localInverseContDiffOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    (g : E → E) (U : Set E) (hU : IsOpen U)
    (hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g U) (p : E) (hp : p ∈ U)
    (hinj : Function.Injective (fderiv ℝ g p)) :
    ∃ (S W : Set E) (σ : E → E),
      IsOpen S ∧ IsOpen W ∧ W ⊆ U ∧ g p ∈ S ∧ p ∈ W ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ S ∧
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
  have hVopen : IsOpen V := isOpen_injLocus g U hU hg
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
  exact ⟨S, W, σ, hSopen, hWopen, hWU, hpS, hpW, hσ,
    fun u hu => Φ.right_inv hu.1, fun x hx => Φ.left_inv hx.1⟩

end Work.Drive.Push
