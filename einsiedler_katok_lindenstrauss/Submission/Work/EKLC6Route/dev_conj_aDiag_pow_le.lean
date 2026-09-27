import Mathlib
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLC6Core.contraction_rate_uminus

/-!
# `EKLC6Route.dev_conj_aDiag_pow_le` — contraction of the `dev`-norm along `Uminus t`

`dev g = max_{i,j} |gᵢⱼ - δᵢⱼ|` is the sup-norm distance of `g` to the identity.  Conjugation
by the diagonal flow scales entries: `(aDiag t ^ n · g · (aDiag t ^ n)⁻¹)ᵢⱼ =
e^{n (tᵢ - tⱼ)} gᵢⱼ` (`boxi_conj_pow_apply`).  For `u ∈ Uminus t` the entry facts
`uminus_entry_facts` say that `uᵢᵢ = 1` and that `uᵢⱼ = 0` whenever `t j ≤ t i`, so only the
*contracted* pairs `tᵢ < tⱼ` contribute, and there the exponential factor is
`e^{-n (tⱼ - tᵢ)} ≤ e^{-n·lamExp t}` because `lamExp t` is the minimum of the gaps `tⱼ - tᵢ`
(fallback value `1`).  Hence each entry of the conjugate is bounded by
`e^{-n·lamExp t} · dev u`, and the maximum over entries gives the claim.
-/

open Work.EKLContract

namespace Work.EKLC6Route

theorem dev_conj_aDiag_pow_le {t : Fin 3 → ℝ} {u : Work.EKLContract.SL3}
    (hu : u ∈ Work.EKLC6Core.Uminus t) (n : ℕ) :
    Work.EKLC6Route.dev
        (Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹) ≤
      Real.exp (-(Work.EKLC6Route.lamExp t * (n : ℝ))) * Work.EKLC6Route.dev u := by
  obtain ⟨hdiag, hzero⟩ := Work.EKLC6Core.uminus_entry_facts t hu
  -- each entry of `u` is bounded by `dev u`
  have hdev_bd : ∀ i j : Fin 3,
      |(u : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤
        Work.EKLC6Route.dev u := by
    intro i j
    exact Finset.le_sup'
      (s := (Finset.univ : Finset (Fin 3 × Fin 3)))
      (f := fun p : Fin 3 × Fin 3 =>
        |(u : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2 - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|)
      (Finset.mem_univ (i, j))
  have hdevu_nn : 0 ≤ Work.EKLC6Route.dev u := le_trans (abs_nonneg _) (hdev_bd 0 0)
  -- `lamExp t` is at most every contraction gap `t j - t i`
  have hlam : ∀ i j : Fin 3, t i < t j → Work.EKLC6Route.lamExp t ≤ t j - t i := by
    intro i j hij
    have h1 : Work.EKLC6Route.lamExp t ≤
        (if t i < t j then t j - t i else 1) := by
      rw [Work.EKLC6Route.lamExp]
      exact Finset.inf'_le (s := (Finset.univ : Finset (Fin 3 × Fin 3)))
        (f := fun p : Fin 3 × Fin 3 => if t p.1 < t p.2 then t p.2 - t p.1 else 1)
        (Finset.mem_univ (i, j))
    rwa [if_pos hij] at h1
  have hMnn : 0 ≤ Real.exp (-(Work.EKLC6Route.lamExp t * (n : ℝ))) * Work.EKLC6Route.dev u :=
    mul_nonneg (Real.exp_pos _).le hdevu_nn
  -- the entrywise bound
  have hbound : ∀ i j : Fin 3,
      |(↑(Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹) :
          Matrix (Fin 3) (Fin 3) ℝ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤
      Real.exp (-(Work.EKLC6Route.lamExp t * (n : ℝ))) * Work.EKLC6Route.dev u := by
    intro i j
    rw [Work.EKLC6Core.boxi_conj_pow_apply]
    by_cases hij : i = j
    · subst hij
      rw [hdiag i, mul_one, Matrix.one_apply_eq]
      rw [show (n : ℝ) * (t i - t i) = 0 by ring, Real.exp_zero, sub_self, abs_zero]
      exact hMnn
    · rw [Matrix.one_apply_ne hij, sub_zero, abs_mul, abs_of_pos (Real.exp_pos _)]
      by_cases hlt : t i < t j
      · have h2 : Real.exp ((n : ℝ) * (t i - t j)) ≤
            Real.exp (-(Work.EKLC6Route.lamExp t * (n : ℝ))) := by
          rw [Real.exp_le_exp]
          have hα := hlam i j hlt
          have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          nlinarith [mul_nonneg hn (sub_nonneg.mpr hα)]
        have hb : |(u : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ Work.EKLC6Route.dev u := by
          have h := hdev_bd i j
          rwa [Matrix.one_apply_ne hij, sub_zero] at h
        exact mul_le_mul h2 hb (abs_nonneg _) (Real.exp_pos _).le
      · push Not at hlt
        rw [hzero i j hij hlt]
        simp only [mul_zero, abs_zero]
        exact hMnn
  rw [Work.EKLC6Route.dev]
  exact Finset.sup'_le Finset.univ_nonempty _ (fun p _ => hbound p.1 p.2)

end Work.EKLC6Route
