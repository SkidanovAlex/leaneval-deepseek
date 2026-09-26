import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.Kernels.TildeFacts.KPlus_z_tildeA
import Submission.Work.Kernels.TildeFacts.KMinus_z_tildeA

/-!
# The second difference of the kernel on the imaginary axis, as a `z`-slash

CKMRV Proposition 4.10 in the second variable (the Lean statements
`Work.Kernels.TildeFacts.KPlus_z_tildeA` and `KMinus_z_tildeA`) says

  `K_+^{(d)}(τ, z+1) - 2K_+^{(d)}(τ,z) + K_+^{(d)}(τ, z-1) = 2 (K_+^{(d)} |^z_{2-d/2} S)(τ,z)`,
  `K_-^{(d)}(τ, z+1) - 2K_-^{(d)}(τ,z) + K_-^{(d)}(τ, z-1) = -2 (K_-^{(d)} |^z_{2-d/2} S)(τ,z)`.

On the imaginary axis (`z = i t`, so `S • z = i/t`) this identifies the second difference `Φ` of
the kernel with the `z`-slash of `K_±`, which is exactly the quantity controlled by the CKMRV
quotient bounds (`Work.Asymptotics.KPlus_slash_bound_half`).  This is the bridge that makes the
tail bound on the two lines `Re τ = ±1/2` accessible: at `z = i t` the slash argument `z` has
`Im z = t ≥ 1/3`, so the quotient bounds apply directly, whereas the second difference itself
involves the kernel at the shifted points `i t ± 1`, where they do not.
-/

noncomputable section

open UpperHalfPlane
open scoped Topology Manifold

namespace Work.CKFinal

/-- The point `i/t` of `ℍ`, for `t > 0`, is `S • (i t)`. -/
theorem S_smul_imagAxis (t : ℝ) (ht : 0 < t) :
    ModularGroup.S • Work.Kernels.imagAxis t ht
      = Work.Kernels.imagAxis (1 / t) (by positivity) := by
  ext
  rw [UpperHalfPlane.modular_S_smul]
  simp [Work.Kernels.imagAxis]
  ring

/-- `Kax K τ 0 (1/t) = K (τ, S • (i t))`, the `S`-transformed second argument. -/
theorem Kax_zero_inv (K : ℍ → ℍ → ℂ) (τ : ℍ) {t : ℝ} (ht : 0 < t) :
    Kax K τ 0 (1 / t) = K τ (ModularGroup.S • Work.Kernels.imagAxis t ht) := by
  rw [Kax, dif_pos (by positivity : (0:ℝ) < 1 / t), zero_vadd]
  exact congrArg (K τ) (S_smul_imagAxis t ht).symm

/-- `TildeA` evaluated at the imaginary-axis point: the second difference of the kernel in the
second variable equals `2ε` times the `z`-slash. -/
theorem tildeA_axis (K : ℍ → ℍ → ℂ) (ε : ℤ) (k : ℤ) (τ : ℍ) {t : ℝ} (ht : 0 < t)
    (h : Work.Kernels.TildeA ε k (fun z : UpperHalfPlane => K τ z) = 0) :
    Kax K τ 1 t + Kax K τ (-1) t - 2 * Kax K τ 0 t
      = 2 * (ε : ℂ) * Kax K τ 0 (1 / t) * ((Work.Kernels.imagAxis t ht : ℂ) ^ (-k)) := by
  have hz := congr_fun h (Work.Kernels.imagAxis t ht)
  simp only [Work.Kernels.TildeA, Pi.sub_apply, Pi.add_apply, Pi.zero_apply, Pi.smul_apply,
    smul_eq_mul] at hz
  rw [Work.Kernels.slash_S_apply] at hz
  have h1 : K τ ((1 : ℝ) +ᵥ Work.Kernels.imagAxis t ht) = Kax K τ 1 t := by
    rw [Kax, dif_pos ht]
  have h2 : K τ ((-1 : ℝ) +ᵥ Work.Kernels.imagAxis t ht) = Kax K τ (-1) t := by
    rw [Kax, dif_pos ht]
  have h3 : K τ (Work.Kernels.imagAxis t ht) = Kax K τ 0 t := by
    rw [Kax, dif_pos ht]
    congr 1
    exact (zero_vadd ℝ _).symm
  rw [h1, h2, h3, ← Kax_zero_inv K τ ht] at hz
  have hz' : Kax K τ 1 t + Kax K τ (-1) t - 2 * Kax K τ 0 t
      - 2 * (ε : ℂ) * Kax K τ 0 (1 / t) * ((Work.Kernels.imagAxis t ht : ℂ) ^ (-k)) = 0 := by
    linear_combination hz
  exact sub_eq_zero.mp hz'

/-- **The `K`-second-difference identity on the imaginary axis.**  For `t > 0`,
`2K(τ,i t) - K(τ,i t+1) - K(τ,i t-1) = -(i t)^{d/2-2}·(K₊(τ,i/t) - K₋(τ,i/t))`. -/
theorem Phi_axis_eq (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) {t : ℝ} (ht : 0 < t) :
    Phi (Work.Kernels.Kfun ℓ d) τ t
      = -(((t : ℂ) * Complex.I) ^ ((d : ℤ) / 2 - 2))
        * (Kax (Work.Kernels.KPlus d) τ 0 (1 / t) - Kax (Work.Kernels.KMinus ℓ d) τ 0 (1 / t)) := by
  have hp := tildeA_axis (Work.Kernels.KPlus d) 1 (2 - (d : ℤ) / 2) τ ht
    (Work.Kernels.TildeFacts.KPlus_z_tildeA d hd τ)
  have hm := tildeA_axis (Work.Kernels.KMinus ℓ d) (-1) (2 - (d : ℤ) / 2) τ ht
    (Work.Kernels.TildeFacts.KMinus_z_tildeA ℓ d hd τ)
  have hk : ∀ x : ℂ, (x ^ (-(2 - (d : ℤ) / 2))) = x ^ ((d : ℤ) / 2 - 2) := by
    intro x; congr 1; ring
  rw [hk] at hp hm
  have hsplit : ∀ x : ℝ, Kax (Work.Kernels.Kfun ℓ d) τ x t
      = (Kax (Work.Kernels.KPlus d) τ x t + Kax (Work.Kernels.KMinus ℓ d) τ x t) / 2 := by
    intro x
    rw [Kax, Kax, Kax]
    by_cases h : 0 < t
    · simp only [dif_pos h]
      rfl
    · simp only [dif_neg h]
      ring
  rw [Phi, hsplit 1, hsplit (-1), hsplit 0]
  have hc : ((Work.Kernels.imagAxis t ht : ℂ)) = (t : ℂ) * Complex.I := rfl
  rw [hc] at hp hm
  linear_combination -(hp + hm) / 2

/-- **The `K̂`-second-difference identity on the imaginary axis.**  For `t > 0`,
`2K̂(τ,i t) - K̂(τ,i t+1) - K̂(τ,i t-1) = -(i t)^{d/2-2}·(K₊(τ,i/t) + K₋(τ,i/t))`. -/
theorem PhiHat_axis_eq (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) {t : ℝ} (ht : 0 < t) :
    2 * Kax (Work.Kernels.Khat ℓ d) τ 0 t - Kax (Work.Kernels.Khat ℓ d) τ 1 t
        - Kax (Work.Kernels.Khat ℓ d) τ (-1) t
      = -(((t : ℂ) * Complex.I) ^ ((d : ℤ) / 2 - 2))
        * (Kax (Work.Kernels.KPlus d) τ 0 (1 / t) + Kax (Work.Kernels.KMinus ℓ d) τ 0 (1 / t)) := by
  have hp := tildeA_axis (Work.Kernels.KPlus d) 1 (2 - (d : ℤ) / 2) τ ht
    (Work.Kernels.TildeFacts.KPlus_z_tildeA d hd τ)
  have hm := tildeA_axis (Work.Kernels.KMinus ℓ d) (-1) (2 - (d : ℤ) / 2) τ ht
    (Work.Kernels.TildeFacts.KMinus_z_tildeA ℓ d hd τ)
  have hk : ∀ x : ℂ, (x ^ (-(2 - (d : ℤ) / 2))) = x ^ ((d : ℤ) / 2 - 2) := by
    intro x; congr 1; ring
  rw [hk] at hp hm
  have hsplit : ∀ x : ℝ, Kax (Work.Kernels.Khat ℓ d) τ x t
      = (Kax (Work.Kernels.KPlus d) τ x t - Kax (Work.Kernels.KMinus ℓ d) τ x t) / 2 := by
    intro x
    rw [Kax, Kax, Kax]
    by_cases h : 0 < t
    · simp only [dif_pos h, Work.Kernels.Khat, Work.Kernels.Kfun]
    · simp only [dif_neg h]
      ring
  rw [hsplit 1, hsplit (-1), hsplit 0]
  have hc : ((Work.Kernels.imagAxis t ht : ℂ)) = (t : ℂ) * Complex.I := rfl
  rw [hc] at hp hm
  linear_combination -(hp - hm) / 2

end Work.CKFinal
