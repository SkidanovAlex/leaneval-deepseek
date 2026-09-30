import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The `ℚ`-linear map attached to the family of logs `log (φ (α_i))`:
`w ↦ ∑ᵢ wᵢ · log (φ (αᵢ))`. Its kernel is trivial exactly when the logs are
`ℚ`-linearly independent. This is the map through which `lamP` factors:
`lamP φ α v L a = (2^v)⁻¹ · lamComb φ α (fun i => L a i)`. -/
noncomputable def lamComb {K : Type*} [Field K] {n : ℕ} (φ : K →+* ℂ) (α : Fin n → K) :
    (Fin n → ℚ) →ₗ[ℚ] ℂ where
  toFun w := ∑ i, (w i : ℂ) * Complex.log (φ (α i))
  map_add' x y := by
    simp only [Pi.add_apply, Rat.cast_add, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, Rat.smul_def, Finset.mul_sum, Rat.cast_mul, RingHom.id_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring

/-- If the logs `log (φ (α_i))` are `ℚ`-linearly independent and the rows of `L` are
`ℚ`-linearly independent, then the family `a ↦ lamP φ α v L a` is `ℚ`-linearly independent.

*Proof:* `0 = ∑_a c_a lamP φ α v L a` gives
`0 = ((2:ℂ)^v)⁻¹ ∑_i (∑_a c_a L_a i) log (φ (α_i))`, so `∑_a c_a L_a i = 0` for every `i` by
independence of the logs, hence `c = 0` by independence of the rows. -/
theorem lamP_linearIndependent {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ) (α : Fin n → K)
    (v : ℕ) (L : Fin r → Fin n → ℤ)
    (hlog : LinearIndependent ℚ (fun i => Complex.log (φ (α i))))
    (hL : LinearIndependent ℚ (fun a i => (L a i : ℚ))) :
    LinearIndependent ℚ (fun a => lamP φ α v L a) := by
  -- `lamP` factors as `(2^v)⁻¹ • (lamComb ∘ rows)`; a composition of injective `ℚ`-linear
  -- maps preserves linear independence.
  rw [Fintype.linearIndependent_iff] at hlog
  have hs : ((2 : ℂ) ^ v)⁻¹ ≠ 0 := by simp
  have hker : LinearMap.ker (lamComb φ α) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    funext i
    exact hlog w (by simpa [lamComb, Rat.smul_def] using hw) i
  have h1 : LinearIndependent ℚ (fun a : Fin r => lamComb φ α (fun i => (L a i : ℚ))) :=
    hL.map' (lamComb φ α) hker
  have h2 : LinearIndependent ℚ (fun a : Fin r =>
      (LinearMap.mulLeft ℚ ((2 : ℂ) ^ v)⁻¹) (lamComb φ α (fun i => (L a i : ℚ)))) :=
    h1.map' (LinearMap.mulLeft ℚ ((2 : ℂ) ^ v)⁻¹) (by
      rw [LinearMap.ker_eq_bot']
      intro z hz
      rw [LinearMap.mulLeft_apply] at hz
      exact (mul_eq_zero.mp hz).resolve_left hs)
  have hV : ∀ a, lamP φ α v L a = ((2 : ℂ) ^ v)⁻¹ * lamComb φ α (fun i => (L a i : ℚ)) := by
    intro a
    simp [lamP, lamComb, Rat.cast_intCast]
  simpa only [LinearMap.mulLeft_apply, hV] using h2

end Work.BW
