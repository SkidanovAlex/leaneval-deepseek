import Mathlib
import Submission.Work.WilG1.Basic
import Submission.Work.WilG0.liftMN_mem
import Submission.Work.WilG0.Omega_cast
import Submission.Work.WilG0.API

namespace Work.WilG1.Calc

open WilkiesDesign

/-- The "lift" set `liftNM k m Dset = {z : ℝ^{k+m} | (j ↦ z (k+j)) ∈ Dset}`, i.e. `Dset`
placed in the *last* `m` coordinates of `ℝ^{k+m}`, written with `Nat.add_comm` so that the
`Dset`-block sits in the second summand.  The version `WilG0.liftMN k m Dset` produced by
iterating `SOMin.prod_left` has the two summands in the other order, so the two sets agree
after transporting along `Nat.add_comm m k`; the two index maps `Fin.natAdd k` and
`Fin.addNat · k` have the same underlying value `k + j = j + k`. -/
theorem liftNM_eq_cast (n m : ℕ) (A : Set (Fin m → ℝ)) :
    Work.WilG0.liftNM n m A = (Nat.add_comm m n) ▸ Work.WilG0.liftMN n m A := by
  ext z
  rw [Work.WilG0.cast_mem_iff]
  simp only [Work.WilG0.liftNM, Work.WilG0.liftMN, Set.mem_ofPred_eq]
  have hfun : (fun j : Fin m => z (Fin.natAdd n j)) =
      (fun j : Fin m => z (Fin.cast (Nat.add_comm m n) (j.addNat n))) := by
    funext j
    congr 1
    exact Fin.ext (by simp [Fin.val_natAdd])
  rw [hfun]

theorem liftNM_mem {S : WilkiesDesign.SOMin} {m : ℕ} {F D : ℕ} {Dset : Set (Fin m → ℝ)}
    (hD : Dset ∈ S.Ω F D m) (k : ℕ) :
    {z : Fin (k + m) → ℝ | (fun j : Fin m => z (Fin.natAdd k j)) ∈ Dset} ∈
      S.Ω (F + k) D (k + m) := by
  -- `WilG0.liftMN` prepends `k` free coordinates one at a time via `SOMin.prod_left`.
  have hlift : Work.WilG0.liftMN k m Dset ∈ S.Ω (F + k) D (m + k) :=
    Work.WilG0.liftMN_mem hD k
  show Work.WilG0.liftNM k m Dset ∈ S.Ω (F + k) D (k + m)
  rw [liftNM_eq_cast k m Dset]
  exact Work.WilG0.Omega_cast (Nat.add_comm m k) hlift

end Work.WilG1.Calc
