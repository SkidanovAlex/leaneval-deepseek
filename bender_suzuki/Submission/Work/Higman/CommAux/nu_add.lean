import Mathlib
import Submission.Work.Higman.lemma3_core
import Submission.Work.Higman.delta_uv_mem_powSub_four

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.CommAux

open Work.Higman

/-- Abelian algebra: `(a * b⁻¹)² = a² * (b²)⁻¹` for `a, b` in an abelian subgroup. -/
theorem l3_sq_mul_inv {P : Type} [Group P] {A : Subgroup P}
    (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {a b : P} (ha : a ∈ A) (hb : b ∈ A) :
    (a * b⁻¹) * (a * b⁻¹) = (a * a) * ((b * b)⁻¹) := by
  have hc : Commute a b⁻¹ := hAb a ha b⁻¹ (A.inv_mem hb)
  rw [← pow_two, hc.mul_pow, pow_two, pow_two, mul_inv_rev]

theorem nu_add {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A : Subgroup P} (hA : Work.Higman.IsXiAbelNormal h A)
    (hA2 : ∀ x ∈ A, x * x = 1 → x ∈ Work.Higman.powSub A 2)
    (u v : P) (a : ↥A) :
    ((Work.Higman.l3Sqrt h hA (u * v) a : ↥A) : P)
      * (((Work.Higman.l3Sqrt h hA u a : ↥A) : P)
        * ((Work.Higman.l3Sqrt h hA v a : ↥A) : P))⁻¹ ∈ Work.Higman.powSub A 2 := by
  have hpuv : ((Work.Higman.l3Sqrt h hA (u * v) a : ↥A) : P) ∈ A :=
    (Work.Higman.l3Sqrt h hA (u * v) a).2
  have hpu : ((Work.Higman.l3Sqrt h hA u a : ↥A) : P) ∈ A :=
    (Work.Higman.l3Sqrt h hA u a).2
  have hpv : ((Work.Higman.l3Sqrt h hA v a : ↥A) : P) ∈ A :=
    (Work.Higman.l3Sqrt h hA v a).2
  have hpq : ((Work.Higman.l3Sqrt h hA u a : ↥A) : P)
      * ((Work.Higman.l3Sqrt h hA v a : ↥A) : P) ∈ A := A.mul_mem hpu hpv
  -- The square of `ν_u(a) · ν_v(a)` is `Δ_u(a) · Δ_v(a)` (the subgroup is abelian).
  have hsq_prod : (((Work.Higman.l3Sqrt h hA u a : ↥A) : P)
        * ((Work.Higman.l3Sqrt h hA v a : ↥A) : P))
      * (((Work.Higman.l3Sqrt h hA u a : ↥A) : P)
        * ((Work.Higman.l3Sqrt h hA v a : ↥A) : P))
      = (u⁻¹ * (a : P) * u * (a : P)⁻¹) * (v⁻¹ * (a : P) * v * (a : P)⁻¹) := by
    rw [Work.Higman.l3_sq_mul hA.abelian hpu hpv, Work.Higman.l3Sqrt_sq h hA u a,
      Work.Higman.l3Sqrt_sq h hA v a]
  -- The square of `ν_{uv}(a) · (ν_u(a) ν_v(a))⁻¹` is `Δ_{uv}(a) · (Δ_u(a) Δ_v(a))⁻¹`.
  have hx2 : (((Work.Higman.l3Sqrt h hA (u * v) a : ↥A) : P)
        * (((Work.Higman.l3Sqrt h hA u a : ↥A) : P)
          * ((Work.Higman.l3Sqrt h hA v a : ↥A) : P))⁻¹)
      * (((Work.Higman.l3Sqrt h hA (u * v) a : ↥A) : P)
        * (((Work.Higman.l3Sqrt h hA u a : ↥A) : P)
          * ((Work.Higman.l3Sqrt h hA v a : ↥A) : P))⁻¹)
      = ((u * v)⁻¹ * (a : P) * (u * v) * (a : P)⁻¹)
        * ((u⁻¹ * (a : P) * u * (a : P)⁻¹)
          * (v⁻¹ * (a : P) * v * (a : P)⁻¹))⁻¹ := by
    rw [l3_sq_mul_inv hA.abelian hpuv hpq, Work.Higman.l3Sqrt_sq h hA (u * v) a, hsq_prod]
  exact Work.Higman.l3_mem_powSub_two_of_sq_mem_four hA.abelian hA2
    (A.mul_mem hpuv (A.inv_mem hpq))
    (by rw [hx2]; exact Work.Higman.delta_uv_mem_powSub_four h hA u v a)

end Work.Higman.CommAux
