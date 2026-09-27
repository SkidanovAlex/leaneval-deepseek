import Mathlib

namespace Work.Sard

/-- **Submersion normal form, as a local homeomorphism.**
Let `u : E → G` be `C^∞` between finite-dimensional real normed spaces, `x₀ : E`, and suppose
`fderiv ℝ u x₀` is surjective. Let `lam : E →L[ℝ] (Fin m → ℝ)` be a linear map whose kernel meets
`ker (fderiv ℝ u x₀)` trivially, and assume `finrank ℝ E = finrank ℝ G + m`. Then there is a local
homeomorphism `e : G × (Fin m → ℝ) ⇄ E` around the base point `(u x₀, lam x₀) ⇄ x₀` which is the
inverse of `x ↦ (u x, lam x)`: `e.symm x = (u x, lam x)` on `e.target` and `u (e z) = z.1` on
`e.source`, `e` is smooth on its source, and its derivative within the source is bijective at every
point of the source. (Proof: `x ↦ (u x, lam x)` has bijective derivative at `x₀` by the kernel
condition and the dimension count, so it is a local diffeomorphism; take `e` to be its inverse,
shrinking the source to a neighbourhood of the base point on which the derivative stays bijective. -/
theorem submersion_local_form {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (m : ℕ) (hm : Module.finrank ℝ E = Module.finrank ℝ G + m)
    (u : E → G) (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) (x₀ : E)
    (hsurj : Function.Surjective (fderiv ℝ u x₀))
    (lam : E →L[ℝ] (Fin m → ℝ)) (hlam : Disjoint (fderiv ℝ u x₀).ker lam.ker) :
    ∃ e : OpenPartialHomeomorph (G × (Fin m → ℝ)) E,
      x₀ ∈ e.target ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e : G × (Fin m → ℝ) → E) e.source ∧
      (∀ z ∈ e.source, u (e z) = z.1) ∧
      (∀ x ∈ e.target, e.symm x = (u x, lam x)) ∧
      (∀ z ∈ e.source,
        Function.Bijective (fderivWithin ℝ (e : G × (Fin m → ℝ) → E) e.source z)) := by
  classical
  have hnu : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  -- ### Linear algebra: `x ↦ (fderiv ℝ u x₀ x, lam x)` is a continuous linear equivalence
  set A : E →L[ℝ] G := fderiv ℝ u x₀ with hA
  set L : E →L[ℝ] (Fin m → ℝ) := lam with hL
  have hdisj : Disjoint A.ker L.ker := by rw [hA, hL]; exact hlam
  have hker : ((A.prod L) : E →ₗ[ℝ] G × (Fin m → ℝ)).ker = ⊥ := by
    rw [ContinuousLinearMap.ker_prod]
    rw [show (↑A : E →ₗ[ℝ] G).ker = A.ker from rfl,
      show (↑L : E →ₗ[ℝ] (Fin m → ℝ)).ker = L.ker from rfl]
    exact hdisj.eq_bot
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (G × (Fin m → ℝ)) := by
    rw [Module.finrank_prod, Module.finrank_fin_fun]
    exact hm
  have hrange : ((A.prod L) : E →ₗ[ℝ] G × (Fin m → ℝ)).range = ⊤ :=
    (LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank hdim).mp hker
  let e' : E ≃L[ℝ] G × (Fin m → ℝ) := ContinuousLinearEquiv.ofBijective (A.prod L) hker hrange
  have hcoe' : (e' : E →L[ℝ] G × (Fin m → ℝ)) = A.prod L := rfl
  -- `hsurj` is not needed for the conclusion below; we record its consequence all the same.
  have _hA_top : A.range = ⊤ := LinearMap.range_eq_top.mpr (by rw [hA]; exact hsurj)
  -- ### The map `Θ x = (u x, lam x)`
  set Θ : E → G × (Fin m → ℝ) := fun x => (u x, lam x) with hΘ
  have hΘc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ := by
    rw [hΘ]; exact hu.prodMk lam.contDiff
  have hΘd : HasFDerivAt Θ (e' : E →L[ℝ] G × (Fin m → ℝ)) x₀ := by
    have h1 : HasFDerivAt u (fderiv ℝ u x₀) x₀ :=
      (hu.differentiable hnu).differentiableAt.hasFDerivAt
    have h3 : HasFDerivAt Θ ((fderiv ℝ u x₀).prod lam) x₀ := by
      rw [hΘ]; exact h1.prodMk lam.hasFDerivAt
    exact h3.congr_fderiv (by rw [hcoe', ← hA, ← hL])
  -- ### The local homeomorphism `φ` of `Θ` at `x₀`
  let φ : OpenPartialHomeomorph E (G × (Fin m → ℝ)) :=
    hΘc.contDiffAt.toOpenPartialHomeomorph Θ hΘd hnu
  have hφcoe : (⇑φ : E → G × (Fin m → ℝ)) = Θ := rfl
  have hx₀src : x₀ ∈ φ.source := hΘc.contDiffAt.mem_toOpenPartialHomeomorph_source hΘd hnu
  -- ### The open set of points where `fderiv Θ` is invertible
  let s : Set E := {x | (fderiv ℝ Θ x).IsInvertible}
  have hs : IsOpen s := by
    have hInv : IsOpen {T : E →L[ℝ] G × (Fin m → ℝ) | T.IsInvertible} := by
      have h : {T : E →L[ℝ] G × (Fin m → ℝ) | T.IsInvertible} =
          Set.range ((↑) : (E ≃L[ℝ] G × (Fin m → ℝ)) → (E →L[ℝ] G × (Fin m → ℝ))) := by
        ext t; simp [ContinuousLinearMap.IsInvertible, Set.mem_range]
      rw [h]; exact ContinuousLinearEquiv.isOpen
    exact (hΘc.continuous_fderiv hnu).isOpen_preimage _ hInv
  have hx₀s : x₀ ∈ s := by
    show (fderiv ℝ Θ x₀).IsInvertible
    rw [hΘd.fderiv]; exact ⟨e', rfl⟩
  -- ### `e` is the inverse of `x ↦ (u x, lam x)`, with source cut down to the good set
  let ψ : OpenPartialHomeomorph E (G × (Fin m → ℝ)) := φ.restrOpen s hs
  let e : OpenPartialHomeomorph (G × (Fin m → ℝ)) E := ψ.symm
  have he_coe : (⇑e : (G × (Fin m → ℝ)) → E) = (⇑φ.symm : (G × (Fin m → ℝ)) → E) :=
    OpenPartialHomeomorph.coe_restrOpen_symm (e := φ) hs
  have hψcoe : (⇑ψ : E → G × (Fin m → ℝ)) = Θ := by
    show (⇑(φ.restrOpen s hs) : E → G × (Fin m → ℝ)) = Θ
    rw [OpenPartialHomeomorph.coe_restrOpen (e := φ) hs, hφcoe]
  have hx₀_target : x₀ ∈ e.target := by
    rw [show e.target = ψ.source from rfl,
      OpenPartialHomeomorph.restrOpen_source (e := φ) s hs]
    exact ⟨hx₀src, hx₀s⟩
  have he_source : e.source = (φ.target ∩ (φ.symm : (G × (Fin m → ℝ)) → E) ⁻¹' s) := by
    rw [show e.source = ψ.target from rfl,
      show ψ.target = (φ.restrOpen s hs).target from rfl,
      OpenPartialHomeomorph.restrOpen_toPartialEquiv, PartialEquiv.restr_target]
    rfl
  -- ### smoothness of `e` on its source
  have he_smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e : G × (Fin m → ℝ) → E) e.source := by
    rw [IsOpen.contDiffOn_iff e.open_source]
    intro z hz
    rw [he_coe]
    rw [he_source, Set.mem_inter_iff, Set.mem_preimage] at hz
    obtain ⟨hz1, hz2⟩ := hz
    simp only [s, Set.mem_ofPred_eq] at hz2
    obtain ⟨f'', hf''⟩ := hz2
    have hfd : HasFDerivAt Θ (fderiv ℝ Θ (φ.symm z)) (φ.symm z) :=
      (hΘc.contDiffAt.differentiableAt hnu).hasFDerivAt
    have hfd' : HasFDerivAt (⇑φ) (f'' : E →L[ℝ] G × (Fin m → ℝ)) (φ.symm z) := by
      rw [hφcoe]; exact hfd.congr_fderiv hf''.symm
    have hcont : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑φ) (φ.symm z) := by
      rw [hφcoe]; exact hΘc.contDiffAt
    exact φ.contDiffAt_symm hz1 hfd' hcont
  -- ### `u (e z) = z.1`
  have he_right : ∀ z ∈ e.source, u (e z) = z.1 := by
    intro z hz
    have h2 : (⇑ψ) (e z) = z := by
      have hz' : z ∈ ψ.target := hz
      exact ψ.right_inv hz'
    rw [hψcoe] at h2
    exact congrArg Prod.fst h2
  -- ### `e.symm x = (u x, lam x)`
  have he_symm : ∀ x ∈ e.target, e.symm x = (u x, lam x) := by
    intro x hx
    have h3 : (⇑ψ) x = Θ x := congrFun hψcoe x
    show (⇑ψ) x = (u x, lam x)
    rw [h3]
  -- ### the derivative of `e` within its source is bijective everywhere
  have he_deriv : ∀ z ∈ e.source,
      Function.Bijective (fderivWithin ℝ (e : G × (Fin m → ℝ) → E) e.source z) := by
    intro z hz
    have hze : z ∈ e.source := hz
    rw [he_source, Set.mem_inter_iff, Set.mem_preimage] at hz
    obtain ⟨hz1, hz2⟩ := hz
    simp only [s, Set.mem_ofPred_eq] at hz2
    obtain ⟨f'', hf''⟩ := hz2
    have hfd : HasFDerivAt Θ (fderiv ℝ Θ (φ.symm z)) (φ.symm z) :=
      (hΘc.contDiffAt.differentiableAt hnu).hasFDerivAt
    have hφd : HasFDerivAt (⇑φ) (f'' : E →L[ℝ] G × (Fin m → ℝ)) (φ.symm z) := by
      rw [hφcoe]; exact hfd.congr_fderiv hf''.symm
    have hsymm : HasFDerivAt (⇑φ.symm) ((f'').symm : (G × (Fin m → ℝ)) →L[ℝ] E) z :=
      φ.hasFDerivAt_symm hz1 hφd
    rw [fderivWithin_of_isOpen e.open_source hze, he_coe, hsymm.fderiv]
    exact f''.symm.bijective
  exact ⟨e, hx₀_target, he_smooth, he_right, he_symm, he_deriv⟩

end Work.Sard
