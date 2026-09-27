import Mathlib

/-!
# A family of orthogonal maps acting on `W` by `c g • 1 + s g • J` is a family of complex scalars

(The auxiliary step used by `Work.Mostow.complexBlockStructure`.)
-/

namespace Work.Mostow

set_option maxHeartbeats 800000 in
/-- **A family acting on `W` as `c g • 1 + s g • J` is a family of complex scalars.**

Let `ρ : G →* O(V)` be a family of orthogonal maps of a real inner product space, `W ≠ ⊥` a
`ρ`-invariant subspace, `J : V →ₗ[ℝ] V` an "almost complex structure on `W`" (i.e. `J (J x) = -x`
and `‖J x‖ = ‖x‖` for `x ∈ W`, and `J` maps `W` into itself), and `c s : G → ℝ` real functions with
`(ρ g) x = c g • x + s g • J x` for every `x ∈ W`.  Then the pairs `(c g, s g)` are the real and
imaginary parts of a monoid homomorphism `z : G →* Circle` (the unit circle in `ℂ`), i.e.
`z g = c g + s g * I`, so that `(ρ g) x = re (z g) • x + im (z g) • J x` on `W`, and moreover
`‖(ρ g) x - x‖ ≤ ‖z g - 1‖ * ‖x‖`.

Indeed, on `W` the map `J` is orthogonal (`⟪J x, J y⟫ = ⟪x, y⟫` by polarisation from
`‖J x‖ = ‖x‖`) and hence `⟪x, J x⟫ = 0` because `J (J x) = -x`; `⟪x, J x⟫ = 0` together with
`‖ρ g x‖ = ‖x‖` gives `c g ^ 2 + s g ^ 2 = 1` (evaluate at a nonzero `u ∈ W`), and evaluating
`ρ (g * g') = ρ g ∘ ρ g'` at `u` and comparing the (unique) coordinates in the basis `(u, J u)`
gives the multiplicativity `z (g * g') = z g * z g'`. -/
theorem complexScalarAssembly {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {G : Type*} [Group G] (ρ : G →* (V ≃ₗᵢ[ℝ] V))
    (W : Submodule ℝ V) (hWne : W ≠ ⊥)
    (hW : ∀ g : G, ∀ x ∈ W, ρ g x ∈ W)
    (J : V →ₗ[ℝ] V) (hJ2 : ∀ x ∈ W, J (J x) = -x) (hJnorm : ∀ x ∈ W, ‖J x‖ = ‖x‖)
    (hJmem : ∀ x ∈ W, J x ∈ W)
    (c s : G → ℝ) (hcs : ∀ g x, x ∈ W → (ρ g) x = c g • x + s g • J x) :
    ∃ z : G →* Circle,
      (∀ g x, x ∈ W → (ρ g) x
        = (((z g : Circle) : ℂ).re) • x + (((z g : Circle) : ℂ).im) • (J x)) ∧
      (∀ g x, x ∈ W → ‖(ρ g) x - x‖ ≤ ‖(((z g : Circle) : ℂ) - 1)‖ * ‖x‖) := by
  classical
  obtain ⟨u, huW, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
  have hu_ne : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
  have hu2_ne : ‖u‖ ^ 2 ≠ 0 := pow_ne_zero 2 hu_ne
  -- `J` preserves the inner product of vectors of `W` (polarisation from `‖J x‖ = ‖x‖`).
  have hJinner : ∀ x ∈ W, ∀ y ∈ W, inner ℝ (J x) (J y) = inner ℝ x y := by
    intro x hx y hy
    have h1 : ‖J x + J y‖ = ‖x + y‖ := by
      rw [← map_add, hJnorm (x + y) (W.add_mem hx hy)]
    have h2 : ‖J x + J y‖ ^ 2 = ‖x + y‖ ^ 2 := by rw [h1]
    rw [norm_add_sq_real, norm_add_sq_real, hJnorm x hx, hJnorm y hy] at h2
    linarith
  -- `x ⊥ J x` on `W`.
  have hJorth : ∀ x ∈ W, inner ℝ x (J x) = 0 := by
    intro x hx
    have h1 := hJinner x hx (J x) (hJmem x hx)
    rw [hJ2 x hx, inner_neg_right, real_inner_comm x (J x)] at h1
    linarith
  -- `c g ^ 2 + s g ^ 2 = 1`.
  have hunit : ∀ g : G, c g ^ 2 + s g ^ 2 = 1 := by
    intro g
    have hnorm2 : ‖(ρ g) u‖ ^ 2 = (c g ^ 2 + s g ^ 2) * ‖u‖ ^ 2 := by
      rw [hcs g u huW, norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs,
        Real.norm_eq_abs, hJnorm u huW, real_inner_smul_left, real_inner_smul_right,
        hJorth u huW, mul_zero, mul_pow, mul_pow, sq_abs, sq_abs]
      ring
    have h2 : (c g ^ 2 + s g ^ 2) * ‖u‖ ^ 2 = 1 * ‖u‖ ^ 2 := by
      rw [one_mul, ← hnorm2, LinearIsometryEquiv.norm_map]
    exact mul_right_cancel₀ hu2_ne h2
  -- uniqueness of the coordinates in the basis `(u, J u)`.
  have hcoord : ∀ {α β γ δ : ℝ}, α • u + β • J u = γ • u + δ • J u → α = γ ∧ β = δ := by
    intro α β γ δ h
    have h1 : (α - γ) • u + (β - δ) • J u = 0 := by
      have h0 : (α - γ) • u + (β - δ) • J u = (α • u + β • J u) - (γ • u + δ • J u) := by
        module
      rw [h0, h, sub_self]
    have e1 : (α - γ) * ‖u‖ ^ 2 = 0 := by
      have h' := congrArg (fun v => inner ℝ v u) h1
      rw [inner_zero_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_comm u (J u), hJorth u huW, real_inner_self_eq_norm_sq] at h'
      linarith
    have e2 : (β - δ) * ‖u‖ ^ 2 = 0 := by
      have h' := congrArg (fun v => inner ℝ v (J u)) h1
      rw [inner_zero_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        hJorth u huW, real_inner_self_eq_norm_sq, hJnorm u huW] at h'
      linarith
    have hα : α - γ = 0 := by
      rcases mul_eq_zero.mp e1 with h | h
      · exact h
      · exact absurd h hu2_ne
    have hβ : β - δ = 0 := by
      rcases mul_eq_zero.mp e2 with h | h
      · exact h
      · exact absurd h hu2_ne
    exact ⟨sub_eq_zero.mp hα, sub_eq_zero.mp hβ⟩
  -- multiplicativity of the pairs `(c g, s g)`, from `ρ (g * g') = ρ g ∘ ρ g'`.
  have hmulcoords : ∀ g g' : G,
      c (g * g') = c g * c g' - s g * s g' ∧ s (g * g') = c g * s g' + s g * c g' := by
    intro g g'
    have hgu : (ρ g') u ∈ W := hW g' u huW
    have h1 : (ρ (g * g')) u = c (g * g') • u + s (g * g') • J u := hcs (g * g') u huW
    have h2 : (ρ g) ((ρ g') u) = c g • ((ρ g') u) + s g • J ((ρ g') u) := hcs g _ hgu
    have h3 : (ρ g') u = c g' • u + s g' • J u := hcs g' u huW
    have h4 : J ((ρ g') u) = (c g') • J u - (s g') • u := by
      rw [h3, map_add, map_smul, map_smul, hJ2 u huW]
      module
    have h5 : (ρ (g * g')) u = (ρ g) ((ρ g') u) := by
      have hm := congrFun (congrArg (fun e : V ≃ₗᵢ[ℝ] V => (e : V → V)) (map_mul ρ g g')) u
      rw [hm, congrFun (LinearIsometryEquiv.coe_mul (ρ g) (ρ g')) u]
      rfl
    have h6 : (ρ (g * g')) u
        = (c g * c g' - s g * s g') • u + (c g * s g' + s g * c g') • J u := by
      rw [h5, h2, h4, h3]
      module
    exact hcoord (by rw [← h1, h6])
  let Z : G → ℂ := fun g => Complex.mk (c g) (s g)
  have hZre : ∀ g, (Z g).re = c g := fun g => rfl
  have hZim : ∀ g, (Z g).im = s g := fun g => rfl
  have hZmul : ∀ g g', Z (g * g') = Z g * Z g' := by
    intro g g'
    obtain ⟨hh1, hh2⟩ := hmulcoords g g'
    apply Complex.ext
    · rw [Complex.mul_re, hZre, hZre, hZim, hZim, hZre]
      exact hh1
    · rw [Complex.mul_im, hZre, hZre, hZim, hZim, hZim]
      exact hh2
  have hZnorm : ∀ g, ‖Z g‖ = 1 := by
    intro g
    have h1 : Complex.normSq (Z g) = 1 := by
      rw [Complex.normSq_apply, hZre g, hZim g, ← pow_two, ← pow_two, hunit g]
    have h2 : ‖Z g‖ ^ 2 = 1 ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, h1, one_pow]
    exact (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).mp h2
  let zfun : G → Circle := fun g => ⟨Z g, mem_sphere_zero_iff_norm.mpr (hZnorm g)⟩
  have hzfun_mul : ∀ g g', zfun (g * g') = zfun g * zfun g' := by
    intro g g'
    apply Circle.ext
    show ((zfun (g * g') : Circle) : ℂ) = ((zfun g * zfun g' : Circle) : ℂ)
    rw [Circle.coe_mul]
    show Z (g * g') = Z g * Z g'
    exact hZmul g g'
  refine ⟨MonoidHom.mk' zfun hzfun_mul, ?_, ?_⟩
  · intro g x hx
    show (ρ g) x = (Z g).re • x + (Z g).im • J x
    rw [hZre, hZim]
    exact hcs g x hx
  · intro g x hx
    have hsub : (ρ g) x - x = (c g - 1) • x + s g • J x := by
      rw [hcs g x hx]
      module
    have hsq1 : ‖(ρ g) x - x‖ ^ 2 = ((c g - 1) ^ 2 + s g ^ 2) * ‖x‖ ^ 2 := by
      rw [hsub, norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        hJnorm x hx, real_inner_smul_left, real_inner_smul_right, hJorth x hx, mul_zero,
        mul_pow, mul_pow, sq_abs, sq_abs]
      ring
    have hsq2 : ‖Z g - 1‖ ^ 2 = ((c g - 1) ^ 2 + s g ^ 2) := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, hZre,
        Complex.one_re, Complex.sub_im, hZim, Complex.one_im, sub_zero]
      ring
    have hmain : ‖(ρ g) x - x‖ = ‖Z g - 1‖ * ‖x‖ := by
      refine (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp ?_
      rw [mul_pow, hsq2, hsq1]
    show ‖(ρ g) x - x‖ ≤ ‖Z g - 1‖ * ‖x‖
    rw [hmain]

end Work.Mostow
