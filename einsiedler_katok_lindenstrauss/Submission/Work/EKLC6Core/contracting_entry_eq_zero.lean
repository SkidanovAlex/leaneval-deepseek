import Mathlib
import Submission.Work.EKLC6Core.box_iInter_conjBox

namespace Work.EKLC6Core

open Filter

/-- If `u ∈ U` is contracted by the diagonal flow `aDiag t` (in the sense that
`(aDiag t)ⁿ u (aDiag t)⁻ⁿ → 1`) and `t j < t i`, then the `(i,j)`-entry of `u` vanishes.

Indeed the entry of the conjugate is `e^{n (t i - t j)} · u i j`, which tends to `0` while the
factor `e^{n (t i - t j)}` is bounded below by `1` (as `t i - t j > 0`). -/
theorem contracting_entry_eq_zero {U : Subgroup Work.EKLContract.SL3} {t : Fin 3 → ℝ}
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
      Filter.atTop (nhds 1))
    {u : Work.EKLContract.SL3} (hu : u ∈ U) {i j : Fin 3} (hij : i ≠ j) (hlt : t j < t i) :
    u i j = 0 := by
  have hcont : Continuous (fun x : Work.EKLContract.SL3 => x i j) := by fun_prop
  have hid : ((1 : Work.EKLContract.SL3) i j) = 0 := Matrix.one_apply_ne hij
  have hlim : Tendsto (fun n : ℕ => (Work.EKLContract.aDiag t ^ n * u *
      (Work.EKLContract.aDiag t ^ n)⁻¹ : Work.EKLContract.SL3) i j) atTop
      (nhds ((1 : Work.EKLContract.SL3) i j)) :=
    (hcont.tendsto 1).comp (hcontr u hu)
  have h1 : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (t i - t j)) * u i j) atTop (nhds 0) := by
    simpa [boxi_conj_pow_apply, hid] using hlim
  exact boxi_eq_zero_of_tendsto_exp_mul (c := t i - t j) (by linarith) h1

end Work.EKLC6Core
