import Mathlib
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLC7.PerSub
import Submission.Work.EKLRelCross.horoZone

/-!
# `exp t0 i < exp t0 j` when `U_ij` is contracted by `aDiag t0`

`Work.EKLRelCross.horoZone` shows that a subgroup `U` contracted by `aDiag t0` is unipotent
with respect to the weights of `t0`: the `(i,j)`-entry of every `u ∈ U` vanishes whenever
`t0 i ≥ t0 j`.

For `U = U_ij` this is impossible with `u = u_ij(1)`, whose `(i,j)`-entry is `1`.  Hence
`t0 i < t0 j`, i.e. `Real.exp (t0 i - t0 j) < 1`: the root subgroup `U_ij` can only be contracted
when the corresponding diagonal weight `e^{t0 i - t0 j}` is shrinking.
-/

namespace Work.EKLRelCross

open Work.EKLContract Filter

/-- The `(i,j)`-entry of the transvection `u_ij(s)` is `s`. -/
lemma coe_uij_entry {i j : Fin 3} (hij : i ≠ j) (s : ℝ) :
    ((uij hij s : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j = s := by
  rw [← Work.EKLContract.toMat_apply (uij hij s) i j,
    Work.EKLContract.Lemmas.toMat_uij hij s, Matrix.add_apply, Matrix.one_apply_ne hij,
    Matrix.single_apply_same, zero_add]

theorem exp_t0_sub_lt_one {U : Subgroup Work.EKLContract.SL3} {t0 : Fin 3 → ℝ} {i j : Fin 3}
    (hij : i ≠ j) (hUeq : U = Work.EKLContract.Uij hij)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1)) :
    Real.exp (t0 i - t0 j) < 1 := by
  by_contra hcon
  have hle : 1 ≤ Real.exp (t0 i - t0 j) := not_lt.mp hcon
  -- `1 ≤ e^{t0 i - t0 j}` forces `t0 j ≤ t0 i`.
  have hge : t0 i ≥ t0 j := by
    have h0 : (0 : ℝ) ≤ t0 i - t0 j := by
      have h1 : Real.exp (0 : ℝ) ≤ Real.exp (t0 i - t0 j) := by rwa [Real.exp_zero]
      exact Real.exp_le_exp.mp h1
    linarith
  -- the transvection `u_ij(1)` lies in `U = U_ij`
  have hmem : Work.EKLContract.uij hij 1 ∈ U := by
    rw [hUeq]
    exact Subgroup.subset_closure (Set.mem_range_self 1)
  -- but its `(i,j)`-entry is `1`, while `horoZone` says it must vanish
  have hentry := (horoZone hcontr (Work.EKLContract.uij hij 1) hmem).1 i j hij hge
  rw [coe_uij_entry hij 1] at hentry
  exact one_ne_zero hentry

end Work.EKLRelCross
