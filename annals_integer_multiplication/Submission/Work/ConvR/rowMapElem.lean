import Mathlib
import Submission.Work.ConvR.scaleArrDefs
import Submission.Work.ConvR.basic

set_option linter.unusedVariables false

namespace Work.ConvR

open HvdH

theorem rowMapElem (hK : HvdH.KernelLib) (rowProg : HvdH.Cmd) (Krow : ℕ)
    (hrow : Work.ConvR.RowSpec rowProg Krow)
    {main : HvdH.Cmd} {p c r : ℕ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2 ^ p) (rest : List HvdH.Val) :
    ∀ x, Work.ConvR.ArrP p r x →
      HvdH.WordR main rowProg
        (fun vs => vs = x :: HvdH.Val.int (p : ℤ) :: HvdH.Val.int (c : ℤ) :: rest)
        (fun _ out => ∃ y, out = y :: HvdH.Val.int (p : ℤ) :: HvdH.Val.int (c : ℤ) :: rest ∧
          Work.ConvR.ArrQ p r c x y ∧ HvdH.vsz y ≤ Work.ConvR.cvecSz p r)
        (fun _ => Krow * (r + 1) * (p + 1) ^ 2 + Krow) := by
  intro x hx
  obtain ⟨u, rfl, hu⟩ := hx
  intro vs hvs s R hR
  obtain ⟨out, s', n, ⟨v, hout, hv, herr⟩, heval, hcost, hstk, hother⟩ :=
    hrow main p c r hc1 hc2 u rest hu vs hvs s R hR
  exact ⟨out, s', n,
    ⟨cvecVal v, hout, ⟨v, rfl, fun u' hu' => ⟨hv, fun j z hz => by
        have huu : u' = u := cvecVal_inj hu'.symm
        rw [huu]
        exact herr j z hz⟩⟩, vsz_cvecVal_le hv⟩,
    heval, hcost, hstk, hother⟩

end Work.ConvR
