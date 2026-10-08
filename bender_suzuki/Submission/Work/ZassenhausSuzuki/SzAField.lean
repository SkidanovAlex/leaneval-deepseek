import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausSuzuki.SzA.sq_eq
import Submission.Work.ZassenhausSuzuki.TitsAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Elementary field/group lemmas about `A(K,θ)` used by the reflection computation

These are the "local" inputs of the Baumeister–Grüninger §5.13–5.14 computation of
`Fix θ = 𝔽₂` (`szClassNumber_fixTheta`):

* `szA_comm_iff` — the commutation criterion: `x * y = y * x ↔ x.a * θ y.a = y.a * θ x.a`;
* `szA_comm_iff_of_fix` — its specialisation: an element with first coordinate in
  `Fix θ^#` commutes with `y` iff `y.a ∈ Fix θ`;
* `szA_sq_eq_imp_mul_inv_mem_center` — in `A(K,θ)` with `orderOf θ` odd, `x² = y²` forces
  `x * y⁻¹ ∈ Z(A(K,θ))`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ZassenhausSuzuki

open SzA

/-- **The commutation criterion in `A(K,θ)`.**  For `x = ⟨a,b⟩`, `y = ⟨c,d⟩` the commutator is
`(0, a·θc + c·θa)`, so `x` and `y` commute iff `a·θc = c·θa`. -/
theorem szA_comm_iff {K : Type} [Field K] [CharP K 2] (θ : K ≃+* K) (x y : SzA K θ) :
    x * y = y * x ↔ x.a * θ y.a = y.a * θ x.a := by
  constructor
  · intro h
    have hb := congrArg SzA.b h
    simp only [SzA.mul_b] at hb
    have h2 : (x.b + y.b) + x.a * θ y.a = (x.b + y.b) + y.a * θ x.a := by
      rw [hb]; ring
    exact add_left_cancel h2
  · intro h
    ext
    · simp only [SzA.mul_a]; ring
    · simp only [SzA.mul_b]; rw [h]; ring

/-- **The commutation criterion, `Fix θ`-form.**  If the first coordinate of `x` is a non-zero
fixed point of `θ`, then `x` commutes with `y` iff the first coordinate of `y` is a fixed point
of `θ` (i.e. `Fix θ` is a subfield and `x.a ∈ Fix θ^#`). -/
theorem szA_comm_iff_of_fix {K : Type} [Field K] [CharP K 2] (θ : K ≃+* K) {x y : SzA K θ}
    (hx0 : x.a ≠ 0) (hx : θ x.a = x.a) :
    x * y = y * x ↔ θ y.a = y.a := by
  constructor
  · intro h
    have hcomm := (szA_comm_iff θ x y).mp h
    rw [hx] at hcomm
    exact mul_left_cancel₀ hx0 (by rw [hcomm]; ring)
  · intro h
    rw [szA_comm_iff, h, hx]; ring

/-- The first coordinate of a product of a square root: `(x*y⁻¹).a = x.a + y.a`. -/
theorem szA_mul_inv_a {K : Type} [Field K] [CharP K 2] (θ : K ≃+* K) (x y : SzA K θ) :
    (x * y⁻¹).a = x.a + y.a := by
  simp only [SzA.mul_a, SzA.inv_a, CharTwo.neg_eq]

/-- **`x ↦ x · θ x` is injective on `K`** when `orderOf θ` is odd (`K` of characteristic two).

This is the `Kˣ`-statement `Work.ZassenhausSuzuki.units_mul_map_injective` extended over `0`. -/
theorem mul_theta_injective {K : Type} [Field K] [CharP K 2] (θ : K ≃+* K)
    (hodd : Odd (orderOf θ)) : Function.Injective (fun a : K => a * θ a) := by
  intro a b hab
  change a * θ a = b * θ b at hab
  by_cases ha : a = 0
  · rw [ha] at hab ⊢
    have hb : b * θ b = 0 := by simpa using hab.symm
    rcases mul_eq_zero.mp hb with h | h
    · exact h.symm
    · exact (θ.map_eq_zero_iff.mp h).symm
  · have hb0 : b ≠ 0 := by
      intro hb0
      rw [hb0, zero_mul] at hab
      rcases mul_eq_zero.mp hab with h | h
      · exact ha h
      · exact ha (θ.map_eq_zero_iff.mp h)
    have hunits : (Units.mk0 a ha) * Units.map θ.toMonoidHom (Units.mk0 a ha)
        = (Units.mk0 b hb0) * Units.map θ.toMonoidHom (Units.mk0 b hb0) := by
      ext
      simpa [Units.val_mul] using hab
    have := units_mul_map_injective θ hodd hunits
    simpa using congrArg (fun u : Kˣ => (u : K)) this

/-- **In `A(K,θ)` with `orderOf θ` odd, equal squares force a central quotient.**
If `x * x = y * y` then `x * y⁻¹` lies in the centre `Z(A(K,θ)) = {⟨0,b⟩}`. -/
theorem szA_sq_eq_imp_mul_inv_mem_center {K : Type} [Field K] [CharP K 2] (θ : K ≃+* K)
    (hodd : Odd (orderOf θ)) {x y : SzA K θ} (h : x * x = y * y) :
    x * y⁻¹ ∈ Subgroup.center (SzA K θ) := by
  have hsq := congrArg SzA.b h
  simp only [SzA.mul_b, CharTwo.add_self_eq_zero, zero_add] at hsq
  have hfst : x.a = y.a := mul_theta_injective θ hodd hsq
  rw [Subgroup.mem_center_iff]
  intro z
  have hzero : (x * y⁻¹).a = 0 := by
    rw [szA_mul_inv_a, hfst, CharTwo.add_self_eq_zero]
  have h1 : x * y⁻¹ = (⟨0, (x * y⁻¹).b⟩ : SzA K θ) := by ext <;> simp [hzero]
  rw [h1]
  exact (Subgroup.mem_center_iff.mp (SzA.mk_zero_mem_center θ _)) z

end Work.ZassenhausSuzuki
