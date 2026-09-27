import Mathlib
import Submission.Work.EKLContract.Lemmas.isHoro_sup_same_source
import Submission.Work.EKLContract.Lemmas.isHoro_Uij
import Submission.Work.EKLContract.Interfaces

namespace Work.EKLC6Core

open Filter Topology

/-- **Contraction of `U_ij ⊔ U_ik` for an arbitrary exponent vector.**

Whenever `t i < t j` and `t i < t k`, the diagonal one-parameter group `aDiag t` contracts
every element of the join `U_ij ⊔ U_ik`:

`aDiag t ^ n * u * (aDiag t ^ n)⁻¹ → 1` as `n → ∞`.

The join is the range of `(s, s') ↦ u_ij(s) · u_ik(s')` (`Lemmas.srcU_sup_eq_sub`), and
conjugation by `aDiag t ^ n` rescales the two parameters by `exp(n (t i - t j))` and
`exp(n (t i - t k))` (`Lemmas.srcU_pow_conj`); both exponents are negative by hypothesis, so
both parameters tend to `0` and the two transvections tend to `1`.

No case distinction `j = k` is needed: the auxiliary lemmas are stated without it. -/
theorem srcU_contraction_of_lt {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (t : Fin 3 → ℝ) (htj : t i < t j) (htk : t i < t k) :
    ∀ u ∈ Work.EKLContract.Uij hij ⊔ Work.EKLContract.Uij hik,
      Filter.Tendsto
        (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
        Filter.atTop (nhds 1) := by
  intro u hu
  -- Write `u` as a shape element `u_ij(s) · u_ik(s')`.
  have hu' : u ∈ Work.EKLContract.Lemmas.srcU_sub hij hik := by
    rwa [Work.EKLContract.Lemmas.srcU_sup_eq_sub hij hik] at hu
  obtain ⟨s, s', hs⟩ := (Work.EKLContract.Lemmas.srcU_mem_sub hij hik u).mp hu'
  rw [← hs]
  -- The two rescaled parameters tend to `0`.
  have hA : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (t i - t j)) * s) atTop (𝓝 0) := by
    have h := Work.EKLContract.Lemmas.srcU_tendsto_exp (show t i - t j < 0 by linarith)
    simpa using h.mul_const s
  have hB : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (t i - t k)) * s') atTop (𝓝 0) := by
    have h := Work.EKLContract.Lemmas.srcU_tendsto_exp (show t i - t k < 0 by linarith)
    simpa using h.mul_const s'
  -- The two transvections tend to `1`.
  have h1 : Tendsto
      (fun n : ℕ => Work.EKLContract.uij hij (Real.exp ((n : ℝ) * (t i - t j)) * s))
      atTop (𝓝 1) := by
    have h := (Work.EKLContract.Lemmas.horoUij_cont hij).tendsto 0 |>.comp hA
    rwa [Work.EKLContract.Lemmas.horoUij_zero hij] at h
  have h2 : Tendsto
      (fun n : ℕ => Work.EKLContract.uij hik (Real.exp ((n : ℝ) * (t i - t k)) * s'))
      atTop (𝓝 1) := by
    have h := (Work.EKLContract.Lemmas.horoUij_cont hik).tendsto 0 |>.comp hB
    rwa [Work.EKLContract.Lemmas.horoUij_zero hik] at h
  have hmul := h1.mul h2
  rw [one_mul] at hmul
  -- Conjugation rewrites the diagonal powers into the rescaled shape element.
  rw [show (fun n : ℕ => Work.EKLContract.aDiag t ^ n *
          Work.EKLContract.Lemmas.srcU_shape hij hik s s' * (Work.EKLContract.aDiag t ^ n)⁻¹)
      = fun n : ℕ => Work.EKLContract.Lemmas.srcU_shape hij hik
          (Real.exp ((n : ℝ) * (t i - t j)) * s)
          (Real.exp ((n : ℝ) * (t i - t k)) * s') from
      funext fun n => Work.EKLContract.Lemmas.srcU_pow_conj hij hik t n s s']
  simpa [Work.EKLContract.Lemmas.srcU_shape] using hmul

end Work.EKLC6Core
