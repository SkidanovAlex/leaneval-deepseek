import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.DbarCnPertAux
import Submission.Work.NN.Core.dbarCn_implicit_form
import Submission.Work.NN.Core.dbarCoord_eq_beltramiCoeff

namespace Work.NN.Core

/-- **Pointwise Beltrami form of the perturbed `∂̄`-equation.**

If `∂̄_{Jstd + A} u` vanishes at `z` in every coordinate direction `e_k` (the pointwise
form of `∂̄_{Jstd + A} u (z) = 0`), and the conjugate Beltrami operator `BopBar A z` is small
(`‖BopBar A z‖ ≤ 1/4`, so that `1 + BopBar A z` is invertible), then at `z` the Wirtinger
derivatives of `u` satisfy the *decoupled* Beltrami system

`∂̄_k u(z) = Σ_j beltramiCoef A k j z · ∂_j u(z)`,

with `beltramiCoef A k j z` the entries of `(1 + BopBar A z)⁻¹ Bop A z`.

This is the hypothesis-free, smoothness-free pointwise companion of
`dbarCoord_eq_beltramiCoeff`: no regularity of `A` and no positivity of `n` is needed. -/
theorem dbarCoord_eq_beltramiCoeff_pointwise {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (u : Work.NN.Core.Cn n → ℂ) (z : Work.NN.Core.Cn n)
    (hquarter : ‖Work.NN.Core.BopBar A z‖ ≤ 1 / 4)
    (hz : ∀ k : Fin n,
      Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z (Pi.single k 1) = 0)
    (k : Fin n) :
    Work.CR.Flat.dbarCoord k u z
      = ∑ j : Fin n, Work.NN.Core.beltramiCoef A k j z * Work.CR.Flat.dCoord j u z := by
  have hInv : (1 + BopBar A z).IsInvertible :=
    (isInvertible_one_add_and_inverse_norm_le hquarter).1
  -- The implicit Beltrami system, with the perturbation term killed by `hz`.
  have hsys : (1 + BopBar A z) (fun j => Work.CR.Flat.dbarCoord j u z)
      = Bop A z (fun j => Work.CR.Flat.dCoord j u z) := by
    have h := dbarCn_implicit_form A u z
    have hzero : (fun j => dbarCn (JstdCn n + A) u z (Pi.single j (1 : ℂ))) = 0 := by
      ext j; exact hz j
    rw [hzero, zero_add] at h
    exact h
  -- Solving the system: `∂̄u(z) = (1 + BopBar A z)⁻¹ Bop A z (∂u(z))`.
  have hfun : ContinuousLinearMap.inverse (1 + BopBar A z)
      (Bop A z (fun j => Work.CR.Flat.dCoord j u z))
      = (fun j => Work.CR.Flat.dbarCoord j u z) := by
    have h0 := ContinuousLinearMap.IsInvertible.inverse_apply_self hInv
      (fun j => Work.CR.Flat.dbarCoord j u z)
    rwa [hsys] at h0
  -- Evaluate the `k`-th coordinate, using complex linearity of `beltramiCoeff A z`.
  have hlast : (beltramiCoeff A z (fun j => Work.CR.Flat.dCoord j u z)) k
      = ∑ j : Fin n, beltramiCoef A k j z * Work.CR.Flat.dCoord j u z := by
    have hlinμ : ∀ (c : ℂ) (v : Cn n), beltramiCoeff A z (c • v) = c • beltramiCoeff A z v := by
      intro c v
      have hlin : ∀ (c : ℂ) (v : Cn n), BopBar A z (c • v) = c • BopBar A z v :=
        fun c v => (Bop_map_smul A z v c).2
      rw [beltramiCoeff, mul_apply_eq_comp, mul_apply_eq_comp, (Bop_map_smul A z v c).1]
      exact inverse_one_add_map_smul hInv hlin c (Bop A z v)
    have hw : (fun j => Work.CR.Flat.dCoord j u z)
        = ∑ j : Fin n, (Work.CR.Flat.dCoord j u z) • (Pi.single j (1 : ℂ) : Cn n) := by
      ext m
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single m]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne (Ne.symm hb)]
      · intro h
        exact absurd (Finset.mem_univ m) h
    rw [hw, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hlinμ, Pi.smul_apply, smul_eq_mul, beltramiCoef]
    ring
  calc Work.CR.Flat.dbarCoord k u z
      = (fun j => Work.CR.Flat.dbarCoord j u z) k := rfl
    _ = (beltramiCoeff A z (fun j => Work.CR.Flat.dCoord j u z)) k := by
          rw [beltramiCoeff, mul_apply_eq_comp]
          exact (congrFun hfun k).symm
    _ = ∑ j : Fin n, beltramiCoef A k j z * Work.CR.Flat.dCoord j u z := hlast

end Work.NN.Core
