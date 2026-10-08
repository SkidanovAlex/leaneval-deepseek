import Mathlib
import Submission.Work.Grun.Diag

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Classical

namespace Work.Grun

/-- The diagonal contribution is insensitive to conjugation (M. Hall, Lemma 14.4.2): `γ ↦ g⁻¹ • γ`
is a bijection from the cosets of `H` fixed by `u` to those fixed by `g⁻¹ * u * g`, and corresponding
factors are conjugate in `H`, hence have the same image under any homomorphism into a commutative
group. -/
theorem theta_diagFactor_conj {G : Type*} [Group G] [Fintype G] {H : Subgroup G} [Fintype (G ⧸ H)]
    {A : Type*} [CommGroup A] (θ : H →* A) (u g : G) :
    Work.Grun.diagProd θ (g⁻¹ * u * g) = Work.Grun.diagProd θ u := by
  -- `γ ↦ g⁻¹ • γ` maps the cosets fixed by `u` to the cosets fixed by `g⁻¹ * u * g`.
  have hφ : ∀ γ : fixedCosets H u, (g⁻¹ * u * g) • (g⁻¹ • γ.1) = g⁻¹ • γ.1 := by
    intro γ
    rw [mul_assoc, mul_smul, mul_smul, smul_inv_smul, show u • γ.1 = γ.1 from γ.2]
  -- and `δ ↦ g • δ` is its inverse on the other side.
  have hψ : ∀ δ : fixedCosets H (g⁻¹ * u * g), u • (g • δ.1) = g • δ.1 := by
    intro δ
    rw [← mul_smul, show u * g = g * (g⁻¹ * u * g) by group, mul_smul, δ.2]
  let φ : fixedCosets H u ≃ fixedCosets H (g⁻¹ * u * g) :=
    { toFun := fun γ => ⟨g⁻¹ • γ.1, hφ γ⟩
      invFun := fun δ => ⟨g • δ.1, hψ δ⟩
      left_inv := fun γ => Subtype.ext (by simp)
      right_inv := fun δ => Subtype.ext (by simp) }
  -- Corresponding factors are conjugate in `H`, so `θ` takes the same value on them.
  have hconj : ∀ γ : fixedCosets H u,
      θ (diagFactor H u γ) = θ (diagFactor H (g⁻¹ * u * g) (φ γ)) := by
    intro γ
    have hxq : (((γ.1).out : G) : G ⧸ H) = γ.1 := Quotient.out_eq' γ.1
    have hyq : ((((φ γ).1).out : G) : G ⧸ H) = (φ γ).1 := Quotient.out_eq' (φ γ).1
    -- `(φ γ).1.out` is a representative of the coset `g⁻¹ • γ.1 = (g⁻¹ * γ.1.out) H`.
    have hsm : g⁻¹ • γ.1 = (((g⁻¹ * ((γ.1).out : G)) : G) : G ⧸ H) := by
      conv_lhs => rw [show γ.1 = (((γ.1).out : G) : G ⧸ H) from (Quotient.out_eq' γ.1).symm]
      rw [MulAction.Quotient.smul_mk]
      rfl
    have hyx : ((((φ γ).1).out : G) : G ⧸ H) =
        (((g⁻¹ * ((γ.1).out : G)) : G) : G ⧸ H) := by
      rw [hyq]; exact hsm
    -- hence `(φ γ).1.out * hH = g⁻¹ * γ.1.out` for `hH ∈ H`.
    have hHmem : (((φ γ).1).out)⁻¹ * (g⁻¹ * (γ.1).out) ∈ H := QuotientGroup.eq.mp hyx
    let hH : H := ⟨(((φ γ).1).out)⁻¹ * (g⁻¹ * (γ.1).out), hHmem⟩
    have hhH : ((hH : H) : G) = (((φ γ).1).out)⁻¹ * (g⁻¹ * (γ.1).out) := rfl
    have hy_eq : ((φ γ).1).out = (g⁻¹ * (γ.1).out) * ((hH : H) : G)⁻¹ := by
      rw [hhH]; group
    -- conjugating `g⁻¹ * u * g` by `(φ γ).1.out = (g⁻¹ * γ.1.out) * hH⁻¹` gives
    -- the `H`-conjugate of `diagFactor H u γ`.
    have hb : diagFactor H (g⁻¹ * u * g) (φ γ) = hH * diagFactor H u γ * hH⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_diagFactor]
      rw [hy_eq]
      group
    calc θ (diagFactor H u γ) = θ (hH * diagFactor H u γ * hH⁻¹) := by
          rw [map_mul, map_mul, map_inv]
          exact (mul_inv_cancel_comm _ _).symm
      _ = θ (diagFactor H (g⁻¹ * u * g) (φ γ)) := by rw [hb]
  -- Reindex the defining product along the bijection `φ`.
  rw [diagProd_def, diagProd_def]
  exact (Fintype.prod_equiv φ (fun γ => θ (diagFactor H u γ))
      (fun δ => θ (diagFactor H (g⁻¹ * u * g) δ)) (fun γ => hconj γ)).symm

end Work.Grun
