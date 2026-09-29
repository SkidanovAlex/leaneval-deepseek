import Mathlib
import Submission.Work.ConvR.pwdefs
import Submission.Work.ConvR.permTop

namespace Work.ConvR

open HvdH

/-- The index permutation `[p, r, As, Bs] ↦ [As, Bs, p, r]`. -/
theorem perm_rarr : ([2, 3, 0, 1] : List ℕ).Perm (List.range 4) := by decide

theorem reorderArr (hK : HvdH.KernelLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p r : ℕ)
      (As Bs : List (List (ℤ × ℤ))) (rest : List HvdH.Val),
      Work.ConvR.WordC main prog
        (fun vs => vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int (r : ℤ) :: HvdH.rarrVal As :: HvdH.rarrVal Bs :: rest)
        (fun _ out => out = HvdH.rarrVal As :: HvdH.rarrVal Bs :: HvdH.Val.int (p : ℤ) :: HvdH.Val.int (r : ℤ) :: rest)
        (K * (HvdH.vsz (HvdH.rarrVal As) + HvdH.vsz (HvdH.rarrVal Bs) + HvdH.isz (p : ℤ) + HvdH.isz (r : ℤ) + 1)) := by
  obtain ⟨permP, K0, hperm⟩ := permTop hK
  refine ⟨permP [2, 3, 0, 1], K0 * 25, ?_⟩
  intro main p r As Bs rest
  have h := hperm main 4 [2, 3, 0, 1]
    [HvdH.Val.int (p : ℤ), HvdH.Val.int (r : ℤ), HvdH.rarrVal As, HvdH.rarrVal Bs] rest
    (by simp) (by simp) perm_rarr
  refine WordC.ofWordR ?_
  refine hK.conseq (main := main) (p := permP [2, 3, 0, 1])
    (P := fun vs => vs = [HvdH.Val.int (p : ℤ), HvdH.Val.int (r : ℤ), HvdH.rarrVal As,
      HvdH.rarrVal Bs] ++ rest)
    (Q := fun _ out => out = [2, 3, 0, 1].map (fun i =>
      ([HvdH.Val.int (p : ℤ), HvdH.Val.int (r : ℤ), HvdH.rarrVal As, HvdH.rarrVal Bs]).getD i HvdH.Val.nil) ++ rest)
    (C := fun _ => K0 * (4 + 1) * (4 + 1) *
      ((([HvdH.Val.int (p : ℤ), HvdH.Val.int (r : ℤ), HvdH.rarrVal As,
        HvdH.rarrVal Bs]).map HvdH.vsz).sum + 1))
    (P' := fun vs => vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int (r : ℤ) ::
      HvdH.rarrVal As :: HvdH.rarrVal Bs :: rest)
    (Q' := fun _ out => out = HvdH.rarrVal As :: HvdH.rarrVal Bs ::
      HvdH.Val.int (p : ℤ) :: HvdH.Val.int (r : ℤ) :: rest)
    (C' := fun _ => K0 * 25 * (HvdH.vsz (HvdH.rarrVal As) + HvdH.vsz (HvdH.rarrVal Bs) +
      HvdH.isz (p : ℤ) + HvdH.isz (r : ℤ) + 1)) h ?_ ?_ ?_
  · intro vs hv
    rw [hv]
    rfl
  · intro vs out hv hQ
    rw [hQ]
    simp
  · intro vs hv
    have hsum : (([HvdH.Val.int (p : ℤ), HvdH.Val.int (r : ℤ), HvdH.rarrVal As,
        HvdH.rarrVal Bs]).map HvdH.vsz).sum =
        HvdH.isz (p : ℤ) + HvdH.isz (r : ℤ) + HvdH.vsz (HvdH.rarrVal As) +
          HvdH.vsz (HvdH.rarrVal Bs) := by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int]
      ring
    rw [hsum]
    have e : K0 * (4 + 1) * (4 + 1) = K0 * 25 := by ring
    rw [e]
    exact Nat.mul_le_mul_left _ (by omega)

end Work.ConvR
