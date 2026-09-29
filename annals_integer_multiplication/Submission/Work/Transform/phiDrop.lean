import Mathlib
import Submission.Work.Transform.phiAux

/-!
# Erasing the parameter of `T̃`

`Work.Transform.dropParamWord`: the tiny word `v :: int p :: R ↦ v :: R` (`KernelLib.roll 1` then
`KernelLib.drop`), used by `Work.Transform.phiWordNE` to remove the precision parameter left by
`Work.Transform.phiZipWord`.  Its cost is `K * (vsz v + isz p + 1)`.
-/

set_option autoImplicit false

namespace Work.Transform

open HvdH

theorem dropParamWord : HvdH.KernelLib → ∃ (prog : Cmd) (K : ℕ),
    ∀ (main : Cmd) (p : ℕ) (v : Val) (R : List Val),
      WordR main prog (fun vs => vs = v :: Val.int p :: R) (fun vs out => out = v :: R)
        (fun vs => K * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)) := by
  intro Kl
  obtain ⟨roll, Kr, hroll⟩ := Kl.roll
  obtain ⟨drp, Kd, hdrop⟩ := Kl.drop
  refine ⟨Cmd.seq (roll 1) drp, 2 * Kr + Kd, ?_⟩
  intro main p v R
  have hroll' : WordR main (roll 1)
      (fun vs => vs = v :: Val.int (p : ℤ) :: R)
      (fun _ out => out = Val.int (p : ℤ) :: v :: R)
      (fun _ => Kr * 2 * (vsz v + isz (p : ℤ) + 1)) := by
    refine Work.Kernel.WordR_conseq (hroll main 1) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]
      simp only [List.length_cons]
      omega
    · intro vs out hvs hout
      rw [hvs] at hout
      rw [hout]
      simp only [List.getD_cons_succ, List.getD_cons_zero, List.eraseIdx_cons_succ,
        List.eraseIdx_cons_zero]
    · intro vs hvs
      rw [hvs]
      have hsum : (((v :: Val.int (p : ℤ) :: R).take (1 + 1)).map vsz).sum
          ≤ vsz v + isz (p : ℤ) := by
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, vsz_int]
        omega
      calc Kr * (1 + 1) * ((((v :: Val.int (p : ℤ) :: R).take (1 + 1)).map vsz).sum + 1)
          = Kr * 2 * ((((v :: Val.int (p : ℤ) :: R).take (1 + 1)).map vsz).sum + 1) := by norm_num
        _ ≤ Kr * 2 * (vsz v + isz (p : ℤ) + 1) := by
              apply Nat.mul_le_mul_left
              omega
  have hdrop' : WordR main drp
      (fun vs => vs = Val.int (p : ℤ) :: v :: R)
      (fun _ out => out = v :: R)
      (fun _ => Kd * (isz (p : ℤ) + 1)) := by
    refine Work.Kernel.WordR_conseq (hdrop main) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]
      simp
    · intro vs out hvs hout
      rw [hvs] at hout
      obtain ⟨a, rest, ha, hout'⟩ := hout
      injection ha with h1 h2
      rw [hout']
      exact h2.symm
    · intro vs hvs
      rw [hvs]
      show Kd * (vsz (Val.int (p : ℤ)) + 1) ≤ Kd * (isz (p : ℤ) + 1)
      rw [vsz_int]
  refine Work.Kernel.WordR_conseq (p := Cmd.seq (roll 1) drp)
    (Work.Kernel.WordR_seq (B := fun _ => Kd * (isz (p : ℤ) + 1)) hroll' hdrop' ?_) ?_ ?_ ?_
  · intro vs mid hvs hmid
    subst mid
    exact ⟨rfl, le_refl _⟩
  · intro vs hvs
    exact hvs
  · intro vs out hvs hout
    obtain ⟨mid, -, hout'⟩ := hout
    exact hout'
  · intro vs hvs
    show Kr * 2 * (vsz v + isz (p : ℤ) + 1) + Kd * (isz (p : ℤ) + 1)
        ≤ (2 * Kr + Kd) * (vsz (vs.getD 0 Val.nil) + vsz (vs.getD 1 Val.nil) + 1)
    rw [hvs]
    simp only [List.getD_cons_zero, List.getD_cons_succ, vsz_int]
    rw [add_mul]
    have h1 : Kd * (isz (p : ℤ) + 1) ≤ Kd * (vsz v + isz (p : ℤ) + 1) :=
      Nat.mul_le_mul_left Kd (by omega)
    have h2 : Kr * 2 * (vsz v + isz (p : ℤ) + 1) = 2 * Kr * (vsz v + isz (p : ℤ) + 1) := by
      ring
    rw [h2]
    exact Nat.add_le_add_left h1 _

end Work.Transform
