import Mathlib
import Submission.Work.MotK.TGen.ZTwistDivGeomDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.ZpgEIrreducible`

`zpgE a b h` is the eliminant of the chart `y₀ = 1` of the twisted Klein curve `C_{h²}`
(`Submission/Work/MotK/TGen/ZTwistDivGeomDefs.lean`), and `ZElim2 a b h` is the eliminant of the
residual plane model.  The two are related by the *invertible diagonal* change of variables
`X₀ ↦ (a/b) X₀`, `X₁ ↦ -(a h/b) X₁` up to the unit `a³/b⁴`: in the division-free form

`σ_a(ZElim2 a b h) · b⁴ = a³ · σ_b(zpgE a b h)`,   `σ_a = diag(a, -a h)`,  `σ_b = diag(b, b)`,

where `σ_c = diag(c₀,c₁)` is the elementary diagonal automorphism `X i ↦ C cᵢ · X i` of
`K[X₀,X₁]` (well defined since `a, b, h ≠ 0`).  Composing the identity with `σ_b⁻¹` exhibits
`zpgE a b h` as `σ_b⁻¹(σ_a(ZElim2 a b h))` times a unit, so irreducibility of `ZElim2 a b h`
implies irreducibility of `zpgE a b h`.
-/

set_option maxHeartbeats 1000000

namespace Work.MotK.TGen

open MvPolynomial

/-- The **diagonal scaling** `X i ↦ C (c i) * X i` is an `R`-algebra automorphism of the
polynomial ring (its inverse is the scaling by the inverse units). -/
noncomputable def scaleAlgEquiv {R : Type*} [CommSemiring R] {σ : Type*} (c : σ → Rˣ) :
    MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval (fun i => MvPolynomial.C ((c i : R)) * MvPolynomial.X i))
    (MvPolynomial.aeval (fun i => MvPolynomial.C (((c i)⁻¹ : Rˣ) : R) * MvPolynomial.X i))
    (by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
        MvPolynomial.algebraMap_eq, map_mul, AlgHom.id_apply]
      rw [← mul_assoc, ← MvPolynomial.C_mul, Units.inv_mul (c i),
        MvPolynomial.C_1, one_mul])
    (by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
        MvPolynomial.algebraMap_eq, map_mul, AlgHom.id_apply]
      rw [← mul_assoc, ← MvPolynomial.C_mul, Units.mul_inv (c i),
        MvPolynomial.C_1, one_mul])

lemma scaleAlgEquiv_apply {R : Type*} [CommSemiring R] {σ : Type*} (c : σ → Rˣ)
    (f : MvPolynomial σ R) :
    scaleAlgEquiv c f
      = MvPolynomial.aeval (fun i => MvPolynomial.C ((c i : R)) * MvPolynomial.X i) f := rfl

/-- **The division-free substitution certificate.**
`σ_a(ZElim2 a b h) · b⁴ = a³ · σ_b(zpgE a b h)` with `σ_a = diag(a, -a h)` and `σ_b = diag(b, b)`
(this is the `zpgE_aeval_eq` identity of `ZTwistDivGeomCerts`). -/
lemma zpgE_scaling_rel (K : Type) [Field K] (a b h : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    scaleAlgEquiv (σ := Fin 2)
        ![Units.mk0 a ha, Units.mk0 (-(a * h)) (neg_ne_zero.mpr (mul_ne_zero ha hh))]
        (Work.MotK.TwCensus.ZElim2 a b h) * MvPolynomial.C (b ^ 4)
      = MvPolynomial.C (a ^ 3)
        * scaleAlgEquiv (σ := Fin 2) (fun _ : Fin 2 => Units.mk0 b hb)
            (Work.MotK.TGen.zpgE a b h) := by
  rw [scaleAlgEquiv_apply, scaleAlgEquiv_apply]
  rw [Work.MotK.TwCensus.ZElim2, Work.MotK.TGen.zpgE]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat,
    MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Units.val_mk0]
  first | refl_ring1 | ring

theorem ZpgEIrreducible (K : Type) [Field K] (a b h : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0)
    (hirr : Irreducible (Work.MotK.TwCensus.ZElim2 a b h)) :
    Irreducible (Work.MotK.TGen.zpgE a b h) := by
  have hrel := zpgE_scaling_rel K a b h ha hb hh
  have hu1 : IsUnit (MvPolynomial.C (b ^ 4) : MvPolynomial (Fin 2) K) :=
    IsUnit.map MvPolynomial.C ((isUnit_iff_ne_zero).mpr (pow_ne_zero 4 hb))
  have hu2 : IsUnit (MvPolynomial.C (a ^ 3) : MvPolynomial (Fin 2) K) :=
    IsUnit.map MvPolynomial.C ((isUnit_iff_ne_zero).mpr (pow_ne_zero 3 ha))
  -- `Irreducible (ZElim2)` transfers to `Irreducible (σ_a(ZElim2))`
  have h1 : Irreducible (scaleAlgEquiv (σ := Fin 2)
      ![Units.mk0 a ha, Units.mk0 (-(a * h)) (neg_ne_zero.mpr (mul_ne_zero ha hh))]
      (Work.MotK.TwCensus.ZElim2 a b h)) :=
    (MulEquiv.irreducible_iff (scaleAlgEquiv (σ := Fin 2)
      ![Units.mk0 a ha, Units.mk0 (-(a * h)) (neg_ne_zero.mpr (mul_ne_zero ha hh))])).mpr hirr
  -- multiplication by the unit `b⁴`
  have h2 : Irreducible (scaleAlgEquiv (σ := Fin 2)
      ![Units.mk0 a ha, Units.mk0 (-(a * h)) (neg_ne_zero.mpr (mul_ne_zero ha hh))]
      (Work.MotK.TwCensus.ZElim2 a b h) * MvPolynomial.C (b ^ 4)) :=
    (irreducible_mul_isUnit hu1).mpr h1
  rw [hrel] at h2
  -- drop the unit `a³` and undo the diagonal scaling `σ_b`
  have h3 : Irreducible (scaleAlgEquiv (σ := Fin 2) (fun _ : Fin 2 => Units.mk0 b hb)
      (Work.MotK.TGen.zpgE a b h)) :=
    (irreducible_isUnit_mul hu2).mp h2
  exact (MulEquiv.irreducible_iff (scaleAlgEquiv (σ := Fin 2)
    (fun _ : Fin 2 => Units.mk0 b hb))).mp h3

end Work.MotK.TGen
