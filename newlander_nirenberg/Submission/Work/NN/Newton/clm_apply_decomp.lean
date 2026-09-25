import Mathlib

namespace Work.NN.Newton

/-- Decomposition of a complex number in the real basis `{1, I}`: for complex
`A`, `B` and `z`, the real-linear combination `z.re • A + z.im • B` equals the sum
of a complex-linear part `(1/2)(A - iB) z` and an anti-linear part
`(1/2)(A + iB) conj z`. -/
private lemma clm_apply_decomp_key (A B z : ℂ) :
    (z.re : ℂ) * A + (z.im : ℂ) * B
      = (1/2 : ℂ) * (A - Complex.I * B) * z
        + (1/2 : ℂ) * (A + Complex.I * B) * (starRingEnd ℂ) z := by
  apply Complex.ext <;> simp <;> ring

/-- Writing an `ℝ`-linear map `T` out in the real basis `{1, I}` of `ℂ` on each
coordinate: the tuple `u` decomposes as `∑ p, u p.re • e_p + u p.im • (i e_p)`,
so `T u` is the corresponding real-linear combination of `T e_p` and `T (i e_p)`. -/
theorem clm_apply_decomp {n : ℕ} (T : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)) (u : Fin n → ℂ) (j : Fin n) :
    (T u) j = ∑ p : Fin n,
      ((1 / 2 : ℂ) * ((T (Pi.single p 1)) j - Complex.I * (T (Pi.single p Complex.I)) j) * u p
        + (1 / 2 : ℂ) * ((T (Pi.single p 1)) j + Complex.I * (T (Pi.single p Complex.I)) j)
            * Complex.conjCLE (u p)) := by
  classical
  -- Decomposition of each coordinate `u p` in the real basis `{1, I}`.
  have hsingle : ∀ p : Fin n, Pi.single p (u p)
      = (u p).re • (Pi.single p (1:ℂ) : Fin n → ℂ)
        + (u p).im • (Pi.single p Complex.I : Fin n → ℂ) := by
    intro p
    funext k
    by_cases hk : k = p
    · subst hk
      simp [Complex.real_smul, Complex.re_add_im]
    · simp [Pi.single_eq_of_ne hk]
  -- Decomposition of the whole tuple `u`.
  have hdecomp : u = ∑ p : Fin n,
      ((u p).re • (Pi.single p (1:ℂ) : Fin n → ℂ)
        + (u p).im • (Pi.single p Complex.I : Fin n → ℂ)) := by
    funext k
    rw [show (∑ p : Fin n, ((u p).re • (Pi.single p (1:ℂ) : Fin n → ℂ)
        + (u p).im • (Pi.single p Complex.I : Fin n → ℂ)))
        = ∑ p : Fin n, Pi.single p (u p) from
          Finset.sum_congr rfl (fun p _ => (hsingle p).symm)]
    rw [Finset.sum_apply]
    exact (Fintype.sum_pi_single k u).symm
  -- Apply `T` to the decomposition, using only `ℝ`-linearity of `T`.
  have hTu : T u = ∑ p : Fin n,
      ((u p).re • T (Pi.single p (1:ℂ)) + (u p).im • T (Pi.single p Complex.I)) := by
    conv_lhs => rw [hdecomp]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [map_add, map_smul, map_smul]
  -- Evaluate at `j` and compare term by term with the claimed complex identity.
  rw [hTu, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro p _
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Complex.real_smul, Complex.real_smul,
    Complex.conjCLE_apply]
  exact clm_apply_decomp_key _ _ _

end Work.NN.Newton
