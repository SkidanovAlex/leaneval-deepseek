import Mathlib
import Submission.Work.ConvR.basic
import Submission.Work.ConvR.scaleArrDefs
import Submission.Work.ConvR.flagWord
import Submission.Work.ConvR.scaleRowWord
import Submission.Work.ConvR.scaleArrMap
import Submission.Work.ConvR.scaleAssembly

namespace Work.ConvR

theorem scaleArr (hK : HvdH.KernelLib) (hI : HvdH.IntLib) (hL : HvdH.LayoutLib) (hF : HvdH.FxLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p c M r : ℕ), 1 ≤ c → c ≤ 2 ^ p →
      ∀ (As : List (List (ℤ × ℤ))) (a : Fin M → Fin r → ℂ) (rest : List HvdH.Val),
        HvdH.InDiscArr p M r As → (∀ (i : Fin M) (j : Fin r), (c : ℝ) * ‖a i j‖ ≤ 1) →
        HvdH.WordR main prog
          (fun vs => vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int (c : ℤ) :: HvdH.rarrVal As :: rest)
          (fun _ out => ∃ Bs, out = HvdH.rarrVal Bs :: rest ∧ HvdH.InDiscArr p M r Bs ∧
            ∀ (i : Fin M) (j : Fin r), (2 : ℝ) ^ p *
                ‖HvdH.fxC p ((Bs.getD i []).getD j (0, 0)) - (c : ℂ) * a i j‖ <
              2 * c * ((2 : ℝ) ^ p * ‖HvdH.fxC p ((As.getD i []).getD j (0, 0)) - a i j‖) + 3)
          (fun _ => K * (M * r + 1) * (p + 1) ^ 2 + K) := by
  obtain ⟨flagProg, KF, hflag⟩ := flagWord
  obtain ⟨rowProg, Krow, hrow⟩ := scaleRowWord hK hF
  obtain ⟨mapProg, Kmap, hmap⟩ := scaleArrMap hK rowProg Krow hrow
  obtain ⟨K, hK'⟩ := scaleArrAssembly hK flagProg mapProg KF Kmap Krow hflag hmap
  exact ⟨sProg hK flagProg mapProg, K, hK'⟩


end Work.ConvR
