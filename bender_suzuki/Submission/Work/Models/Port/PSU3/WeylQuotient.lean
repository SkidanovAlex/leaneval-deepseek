/-
**The rank-one `(B,N)`-pair of `PSU(3,2^n)`: `N_{PSU(3,2^n)}(T̄) = T̄ ⋊ ⟨w̄⟩`.**

`PSU(3,2^n)` is the image of `SU(3,2^n)` under the canonical surjection
`psu3Hom n : SU(3,2^n) → PSU(3,2^n)` whose kernel is the scalar subgroup (a central subgroup of
odd order contained in the maximal torus `suTS n`).  Consequently the normalizer of the image of
the torus is the image of the normalizer:

  `N_{PSU(3,2^n)}(T̄) = N_{SU(3,2^n)}(T)·psu3Hom`

and the rank-one `(B,N)`-pair relation for `SU(3,2^n)`
(`normalizer_suTS_eq_sup_zpowers_suSgM`) descends to the quotient.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.PSU3.Weyl
import Submission.Work.Models.Port.PSU3.Main
import Submission.Work.Models.Port.PSU3.PSU3Order
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.map_normalizer_eq_normalizer_map_of_ker_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Matrix LeanEval.GroupTheory.Defs
open scoped Pointwise

namespace Submission.PSU3

/-! ## The kernel of `SU(3,2^n) → PSU(3,2^n)` lies in the maximal torus -/

/-- The unit identities satisfied by a scalar matrix of `SU(3,2^n)`: if `λ^(q+1) = λ^3 = 1`
(`q = 2^n`) then `λ^(q-1) = λ` and `λ^q = λ⁻¹`. -/
lemma unit_pow_identities (n : ℕ) (u : (F n)ˣ) (hq1 : u ^ (2 ^ n + 1) = 1) (h3 : u ^ 3 = 1) :
    u ^ (2 ^ n - 1) = u ∧ u ^ (2 ^ n) = u⁻¹ := by
  have hq : u ^ (2 ^ n) = u⁻¹ := by
    have h : u ^ (2 ^ n) * u = 1 := by rw [← pow_succ, hq1]
    calc u ^ (2 ^ n) = u ^ (2 ^ n) * u * u⁻¹ := by group
      _ = 1 * u⁻¹ := by rw [h]
      _ = u⁻¹ := one_mul _
  have hsq : u * u = u⁻¹ := by
    have h : u * u * u = 1 := by
      have e : u * u * u = u ^ 3 := by rw [pow_three]; group
      rw [e, h3]
    calc u * u = u * u * u * u⁻¹ := by group
      _ = 1 * u⁻¹ := by rw [h]
      _ = u⁻¹ := one_mul _
  have hinv2 : u⁻¹ * u⁻¹ = u := by
    rw [← _root_.mul_inv_rev, hsq, _root_.inv_inv]
  have hstep : u ^ (2 ^ n - 1) * u = u ^ (2 ^ n) :=
    pow_sub_one_mul (by positivity : 2 ^ n ≠ 0) u
  refine ⟨?_, hq⟩
  calc u ^ (2 ^ n - 1) = u ^ (2 ^ n - 1) * u * u⁻¹ := by group
    _ = u ^ (2 ^ n) * u⁻¹ := by rw [hstep]
    _ = u⁻¹ * u⁻¹ := by rw [hq]
    _ = u := hinv2

/-- A scalar matrix `λ·1` of `SU(3,2^n)` lies in the maximal torus `suT n`
`= {diag(a, a^(q-1), a^(-q))}`. -/
lemma scalar_mem_suT (n : ℕ) {u : (F n)ˣ} (hq1 : u ^ (2 ^ n + 1) = 1) (h3 : u ^ 3 = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) u ∈ suT n := by
  obtain ⟨hpow, hq⟩ := unit_pow_identities n u hq1 h3
  have hpowF : ((u : F n)) ^ (2 ^ n - 1) = (u : F n) := by
    have := congrArg (fun z : (F n)ˣ => (z : F n)) hpow
    simpa using this
  have hqF : ((u : F n)) ^ (2 ^ n) = ((u : F n))⁻¹ := by
    have := congrArg (fun z : (F n)ˣ => (z : F n)) hq
    simpa using this
  refine ⟨u, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, suTg_coe, suTmat,
    Matrix.diagonal_eq_diagonal_iff]
  intro i
  fin_cases i <;> simp [hpowF, hqF]

/-- **The kernel of `SU(3,2^n) → PSU(3,2^n)` lies in the maximal torus.** -/
lemma psu3Hom_ker_le_suTS (n : ℕ) : (psu3Hom n).ker ≤ suTS n := by
  intro x hx
  have hxc : (x : GL (Fin 3) (F n)) ∈ Subgroup.center (GL (Fin 3) (F n)) := by
    have h := hx
    rw [psu3Hom_ker_eq, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h
    exact h.2
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hxc
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hxc
  have huSU3 : IsSU3 (Matrix.GeneralLinearGroup.scalar (Fin 3) u) := by
    rw [hu]; exact x.2
  obtain ⟨hq1, h3⟩ := (isSU3_scalar_iff n u).mp huSU3
  rw [suTS, Subgroup.mem_subgroupOf]
  rw [show (x : GL (Fin 3) (F n)) = Matrix.GeneralLinearGroup.scalar (Fin 3) u from hu.symm]
  exact scalar_mem_suT n hq1 h3

/-! ## The maximal torus and the Weyl theorem at the level of `PSU(3,2^n)` -/

/-- The maximal torus `T̄` of `PSU(3,2^n)`: the image of the torus of `SU(3,2^n)`. -/
noncomputable def psu3T (n : ℕ) : Subgroup (PSU3Model n) := (suTS n).map (psu3Hom n)

/-- The Weyl element `w̄` of `PSU(3,2^n)`: the image of the Weyl element of `SU(3,2^n)`. -/
noncomputable def psu3Weyl (n : ℕ) : PSU3Model n := psu3Hom n (suSgM n)

/-- **The rank-one `(B,N)`-pair relation `N(T̄) = T̄ ⋊ ⟨w̄⟩` at the level of `PSU(3,2^n)`.** -/
theorem normalizer_psu3T_eq_sup_zpowers_psu3Weyl (n : ℕ) (hn : 2 ≤ n) :
    Subgroup.normalizer (psu3T n : Set (PSU3Model n)) =
      psu3T n ⊔ Subgroup.zpowers (psu3Weyl n) := by
  have h := Commons.GroupTheory.Subgroup.map_normalizer_eq_normalizer_map_of_ker_le
    (psu3Hom n) (psu3Hom_surjective n) (psu3Hom_ker_le_suTS n)
  rw [show psu3T n = (suTS n).map (psu3Hom n) from rfl, h, normalizer_suTS_eq_sup_zpowers_suSgM n hn,
    Subgroup.map_sup, MonoidHom.map_zpowers]
  rfl

end Submission.PSU3
