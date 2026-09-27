import Mathlib
import Submission.Work.Mostow.abelianBlockDefs
import Submission.Work.Mostow.symPartSmulComplexStructure
import Submission.Work.Mostow.isometryEqOfSymPartEq
import Submission.Work.Mostow.complexScalarAssembly
import Submission.Work.Mostow.oSk_eq_smul_of_comp_scalar

namespace Work.Mostow

/-- **Structure of a "complex" block of a family of orthogonal maps.**

Let `ρ : G →* O(V)` be a family of orthogonal maps of a finite-dimensional real inner product space
`V`, and let `W ≠ ⊥` be a `ρ`-invariant subspace on which every `ρ g` has scalar "symmetric part"
and every product of two "antisymmetric parts" is scalar:

* `∀ g, ∃ a, ∀ x ∈ W, oSym (ρ g) x = a • x`   (`oSym b = b + b⁻¹`),
* `∀ g g', ∃ m, ∀ x ∈ W, (oSk (ρ g) * oSk (ρ g')) x = m • x`   (`oSk b = b - b⁻¹`, `*` = composition),
* some `g₀` has scalar `a₀` with `a₀ ^ 2 < 4`.

Then `W` carries an orthogonal complex structure `J` (`J² = -1`, `‖J x‖ = ‖x‖`, `J` preserves `W`)
and each `ρ g` acts on `W` as the complex scalar `z g`, `z : G →* Circle` (the unit circle in `ℂ`),
i.e. `(ρ g) x = re (z g) • x + im (z g) • (J x)` for `x ∈ W`; moreover
`‖(ρ g) x - x‖ ≤ ‖z g - 1‖ ‖x‖`.

Route.  (1) For `a` the scalar of `g` and `x ∈ W`, `a ‖x‖² = ⟪ρ g x, x⟫ + ⟪(ρ g)⁻¹ x, x⟫` (because
the adjoint of `ρ g` is `(ρ g)⁻¹`), hence `|a| ≤ 2` by Cauchy–Schwarz.  (2) With `c := a₀ / 2`
(so `|c| < 1`) apply `Submission.Work.Mostow.symPartSmulComplexStructure` to `ρ g₀`, `W`, `c`
(its hypothesis is `(2⁻¹) • (T x + T.symm x) = c • x`; use `LinearIsometryEquiv.coe_inv`); it gives
`J := (√(1 - c^2))⁻¹ • ((ρ g₀ : V →ₗ[ℝ] V) - c • 1)` with `J (J x) = -x` and `‖J x‖ = ‖x‖` for
`x ∈ W`; also `J x ∈ W` for `x ∈ W`.  (3) For an arbitrary `g` with scalar `a`: if `a^2 < 4` the
same construction gives `J_g`, and `oSk (ρ g) x = 2 * √(1 - c_g^2) • J_g x` on `W`
(`c_g = a/2`).  Feeding `g` and `g₀` into the second hypothesis gives `(J_g * J) x = m x` on `W`;
from `J_g (J_g J) = -J` one gets `J_g = ε J` with `ε = ±1` (no commutativity of `J_g`, `J` needed).
If `a^2 = 4` (the only other possibility by (1)), then `a/2 = ±1` and
`Submission.Work.Mostow.isometryEqOfSymPartEq` applied to `ρ g`, `W`, `a/2` gives `ρ g x = (a/2) x`.
(4) Put `z g := c_g + (√(1 - c_g^2) * ε_g) * Complex.I ∈ ℂ` (take `ε_g = 1` when `a_g^2 = 4`, where
the second term vanishes).  Then `z g` has norm `1`, and `z` is multiplicative: the formula for
`g`, `g'`, `g * g'` combined with `ρ (g * g') = ρ g * ρ g'` and `J² = -1` gives equal `(1,J)`
coordinates; uniqueness of the coordinates uses `W ≠ ⊥` and `J² = -1` (which excludes `J = t • 1`).
(5) For the norm: `(ρ g) x - x = (c_g - 1) • x + √(1 - c_g^2) * ε_g • (J x)` is an orthogonal sum
(`⟪x, J x⟫ = 0` since `J` is antisymmetric: `⟪J x, J y⟫ = ⟪x, y⟫` on `W` and `J² = -1`), so
`‖(ρ g) x - x‖² = ((c_g - 1)^2 + (1 - c_g^2)) ‖x‖² = ‖z g - 1‖² ‖x‖²`. -/
theorem complexBlockStructure {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {G : Type*} [Group G] (ρ : G →* (V ≃ₗᵢ[ℝ] V))
    (W : Submodule ℝ V) (hWne : W ≠ ⊥)
    (hW : ∀ g : G, ∀ x ∈ W, ρ g x ∈ W)
    (hscal : ∀ g : G, ∃ a : ℝ, ∀ x ∈ W, oSym (ρ g) x = a • x)
    (hmu : ∀ g g' : G, ∃ m : ℝ, ∀ x ∈ W, (oSk (ρ g) * oSk (ρ g')) x = m • x)
    (hcx : ∃ g₀ : G, ∃ a₀ : ℝ, (∀ x ∈ W, oSym (ρ g₀) x = a₀ • x) ∧ a₀ ^ 2 < 4) :
    ∃ (J : V →ₗ[ℝ] V) (z : G →* Circle),
      (∀ x ∈ W, J (J x) = -x) ∧ (∀ x ∈ W, ‖J x‖ = ‖x‖) ∧ (∀ x ∈ W, J x ∈ W) ∧
      (∀ g x, x ∈ W → (ρ g) x
        = (((z g : Circle) : ℂ).re) • x + (((z g : Circle) : ℂ).im) • (J x)) ∧
      (∀ g x, x ∈ W → ‖(ρ g) x - x‖ ≤ ‖(((z g : Circle) : ℂ) - 1)‖ * ‖x‖) := by
  classical
  obtain ⟨g₀, a₀, ha₀, hlt₀⟩ := hcx
  -- (1) choice of the scalar `a g` of `ρ g` on `W` and uniqueness of that scalar.
  choose a ha using hscal
  have ha_eq : a g₀ = a₀ := by
    obtain ⟨u, huW, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
    refine smul_left_injective ℝ hu0 ?_
    show a g₀ • u = a₀ • u
    rw [← ha g₀ u huW, ha₀ u huW]
  -- (2) the complex structure `J` coming from `ρ g₀`.
  set c : G → ℝ := fun g => a g / 2 with hc_def
  have hc_apply : ∀ g, c g = a g / 2 := by intro g; rw [hc_def]
  have hc₀sq : (c g₀)^2 < 1 := by
    have h4 : (a g₀)^2 < 4 := by rw [ha_eq]; exact hlt₀
    rw [hc_apply g₀]; nlinarith
  have hc₀_lt : |c g₀| < 1 := (sq_lt_one_iff_abs_lt_one (c g₀)).mp hc₀sq
  set s₀ : ℝ := Real.sqrt (1 - (c g₀)^2) with hs₀_def
  have hs₀_sq : s₀^2 = 1 - (c g₀)^2 := by
    rw [hs₀_def]; exact Real.sq_sqrt (by nlinarith [sq_nonneg (c g₀)])
  have hs₀_pos : 0 < s₀ := by
    rw [hs₀_def]; exact Real.sqrt_pos.mpr (by nlinarith [sq_nonneg (c g₀)])
  have hs₀_ne : s₀ ≠ 0 := ne_of_gt hs₀_pos
  set J : V →ₗ[ℝ] V := s₀⁻¹ • ((ρ g₀ : V →ₗ[ℝ] V) - (c g₀) • 1) with hJ_def
  have hbase : ∀ x ∈ W, (2⁻¹ : ℝ) • ((ρ g₀) x + (ρ g₀).symm x) = (c g₀) • x := by
    intro x hx
    have h := ha g₀ x hx
    rw [oSym_apply, congrFun (LinearIsometryEquiv.coe_inv (ρ g₀)) x] at h
    have ha2 : a g₀ = 2 * c g₀ := by rw [hc_apply g₀]; ring
    rw [ha2] at h
    rw [h, smul_smul, show (2⁻¹ : ℝ) * (2 * c g₀) = c g₀ by ring]
  have hJraw := symPartSmulComplexStructure (ρ g₀) W (c g₀) hc₀_lt hbase
  have hJ2 : ∀ x ∈ W, J (J x) = -x := by
    intro x hx
    rw [hJ_def, hs₀_def]
    exact hJraw.1 x hx
  have hJnorm : ∀ x ∈ W, ‖J x‖ = ‖x‖ := by
    intro x hx
    rw [hJ_def, hs₀_def]
    exact hJraw.2 x hx
  have hJmem : ∀ x ∈ W, J x ∈ W := by
    intro x hx
    rw [hJ_def, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply]
    exact W.smul_mem _ (W.sub_mem (hW g₀ x hx) (W.smul_mem _ hx))
  -- the antisymmetric part of `ρ g₀` on `W`, in terms of `J`.
  have hT₀ : ∀ x ∈ W, oSk (ρ g₀) x = (2 * s₀) • J x := by
    intro x hx
    have hb := hbase x hx
    have hb2 : (ρ g₀) x + (ρ g₀).symm x = (2 * c g₀) • x := by
      have h' : (2:ℝ) • ((2⁻¹:ℝ) • ((ρ g₀) x + (ρ g₀).symm x)) = (2:ℝ) • (c g₀ • x) := by
        rw [hb]
      rwa [smul_smul, mul_inv_cancel₀ (by norm_num : (2:ℝ) ≠ 0), one_smul, smul_smul] at h'
    have hb3 : (ρ g₀).symm x = (2 * c g₀) • x - (ρ g₀) x := by
      rw [eq_sub_iff_add_eq]; rw [add_comm]; exact hb2
    rw [oSk_apply, congrFun (LinearIsometryEquiv.coe_inv (ρ g₀)) x, hb3]
    rw [hJ_def, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply]
    rw [smul_smul]
    have hc2 : 2 * s₀ * s₀⁻¹ = (2:ℝ) := by rw [mul_assoc, mul_inv_cancel₀ hs₀_ne, mul_one]
    rw [hc2]
    have hgoal : (ρ g₀) x - ((2 * c g₀) • x - (ρ g₀) x) = (2:ℝ) • ((ρ g₀) x - (c g₀) • x) := by
      rw [smul_sub, smul_smul, two_smul]; abel
    exact hgoal
  -- (3) `oSk (ρ g) = 2 s g • J` for every `g`, where `oSk (ρ g) * oSk (ρ g₀) = m g • 1`.
  have hmg : ∀ g : G, ∃ m : ℝ, ∀ x ∈ W, (oSk (ρ g) * oSk (ρ g₀)) x = m • x :=
    fun g => hmu g g₀
  choose m hm using hmg
  set s : G → ℝ := fun g => -(m g) / (4 * s₀) with hs_def
  have hs_apply : ∀ g, s g = -(m g) / (4 * s₀) := by intro g; rw [hs_def]
  have hs_g : ∀ g x, x ∈ W → oSk (ρ g) x = (2 * s g) • J x := by
    intro g x hx
    have h := oSk_eq_smul_of_comp_scalar (ρ g) (ρ g₀) W J s₀ (m g) hs₀_ne
      hJ2 hJmem hT₀ (hm g) x hx
    rw [h]
    congr 1
    rw [hs_apply g]
    field_simp
    ring
  -- (4) `(ρ g) x = c g • x + s g • J x` on `W` (average of the symmetric and antisymmetric parts).
  have hcs : ∀ g x, x ∈ W → (ρ g) x = c g • x + s g • J x := by
    intro g x hx
    have h1 : oSym (ρ g) x = (2 * c g) • x := by
      have h := ha g x hx
      rw [h]
      congr 1
      rw [hc_apply g]; ring
    have h2 : oSk (ρ g) x = (2 * s g) • J x := hs_g g x hx
    have hsum : oSym (ρ g) + oSk (ρ g) = (2:ℝ) • ((ρ g : V ≃ₗᵢ[ℝ] V) : V →ₗ[ℝ] V) := by
      unfold oSym oSk; module
    have h3 := congrArg (fun (L : V →ₗ[ℝ] V) => L x) hsum
    simp only [LinearMap.add_apply, LinearMap.smul_apply] at h3
    rw [h1, h2] at h3
    have h4 : (2 * c g) • x + (2 * s g) • J x = (2:ℝ) • (c g • x + s g • J x) := by
      rw [smul_add, smul_smul, smul_smul]
    rw [h4] at h3
    have h5 := congrArg (fun v => (2⁻¹:ℝ) • v) h3.symm
    simpa [smul_smul, inv_mul_cancel₀ (show (2:ℝ) ≠ 0 by norm_num)] using h5
  -- (5) assemble the complex scalar character.
  obtain ⟨z, hz1, hz2⟩ :=
    complexScalarAssembly ρ W hWne hW J hJ2 hJnorm hJmem c s hcs
  exact ⟨J, z, hJ2, hJnorm, hJmem, hz1, hz2⟩

end Work.Mostow
