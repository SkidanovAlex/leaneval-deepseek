import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLContract.Lemmas.isHoro_Uij

namespace Work.EKLContract.Lemmas

open Filter Topology
open Work.EKLContract

/-- **Two transvections with the same target.**  If both `t i < t j` and `t k < t j`, the `n`-th
`aDiag t`-conjugate of the product `u_ij(s) u_kj(s')` tends to `1`: the conjugation splits over the
product (`Work.EKLContract.Lemmas.horoUij_aDiag_conj`), each factor tends to `1`
(`Work.EKLContract.Lemmas.horoUij_tendsto_conj`), and multiplication is continuous. -/
theorem uij_same_target_tendsto {i j k : Fin 3} (hij : i ≠ j) (hkj : k ≠ j) (t : Fin 3 → ℝ)
    (hti : t i < t j) (htk : t k < t j) (s s' : ℝ) :
    Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t ^ n *
      (Work.EKLContract.uij hij s * Work.EKLContract.uij hkj s') *
      (Work.EKLContract.aDiag t ^ n)⁻¹) Filter.atTop (nhds 1) := by
  have hprod : Tendsto (fun n : ℕ =>
      (Work.EKLContract.aDiag t ^ n * Work.EKLContract.uij hij s *
        (Work.EKLContract.aDiag t ^ n)⁻¹) *
      (Work.EKLContract.aDiag t ^ n * Work.EKLContract.uij hkj s' *
        (Work.EKLContract.aDiag t ^ n)⁻¹))
      atTop (nhds 1) := by
    have h := (Work.EKLContract.Lemmas.horoUij_tendsto_conj t hij hti s).mul
      (Work.EKLContract.Lemmas.horoUij_tendsto_conj t hkj htk s')
    simpa using h
  refine hprod.congr (fun n => ?_)
  group

end Work.EKLContract.Lemmas
