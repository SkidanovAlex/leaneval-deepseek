import Mathlib
import Submission.Work.ConvR.scaleFacts
import Submission.Work.ConvR.scaleInject
import Submission.Work.ConvR.scaleArrDefs
import Submission.Work.ConvR.arrExtract
import Submission.Work.ConvR.rowMapElem
import Submission.Work.Kernel.Raw

namespace Work.ConvR

open HvdH
open Work.Kernel

theorem scaleArrMap (hK : HvdH.KernelLib) (rowProg : HvdH.Cmd) (Krow : ℕ)
    (hrow : ∀ (main : HvdH.Cmd) (p c r : ℕ), 1 ≤ c → c ≤ 2 ^ p →
      ∀ (u : List (ℤ × ℤ)) (rest : List HvdH.Val), HvdH.InDiscVec p r u →
        HvdH.WordR main rowProg
          (fun vs => vs = HvdH.cvecVal u :: HvdH.Val.int (p : ℤ) :: HvdH.Val.int (c : ℤ) :: rest)
          (fun _ out => ∃ v : List (ℤ × ℤ),
            out = HvdH.cvecVal v :: HvdH.Val.int (p : ℤ) :: HvdH.Val.int (c : ℤ) :: rest ∧
            HvdH.InDiscVec p r v ∧
            ∀ (j : Fin r) (x : ℂ), (c : ℝ) * ‖x‖ ≤ 1 →
              (2 : ℝ) ^ p * ‖HvdH.fxC p (v.getD j (0, 0)) - (c : ℂ) * x‖ <
                2 * c * ((2 : ℝ) ^ p * ‖HvdH.fxC p (u.getD j (0, 0)) - x‖) + 3)
          (fun _ => Krow * (r + 1) * (p + 1) ^ 2 + Krow)) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p c M r : ℕ), 1 ≤ c → c ≤ 2 ^ p →
      ∀ (As : List (List (ℤ × ℤ))) (rest : List HvdH.Val), HvdH.InDiscArr p M r As →
        HvdH.WordR main prog
          (fun vs => vs = HvdH.rarrVal As :: HvdH.Val.int (p : ℤ) :: HvdH.Val.int (c : ℤ) :: rest)
          (fun _ out => ∃ Bs : List (List (ℤ × ℤ)),
            out = HvdH.rarrVal Bs :: HvdH.Val.int (p : ℤ) :: HvdH.Val.int (c : ℤ) :: rest ∧
            Bs.length = M ∧
            (∀ i : ℕ, i < M → HvdH.InDiscVec p r (Bs.getD i []) ∧
              ∀ (j : Fin r) (x : ℂ), (c : ℝ) * ‖x‖ ≤ 1 →
                (2 : ℝ) ^ p * ‖HvdH.fxC p ((Bs.getD i []).getD j (0, 0)) - (c : ℂ) * x‖ <
                  2 * c * ((2 : ℝ) ^ p * ‖HvdH.fxC p ((As.getD i []).getD j (0, 0)) - x‖) + 3))
          (fun _ => K * (M * (Krow * (r + 1) * (p + 1) ^ 2 + Krow) + 1) + K)  := by
  obtain ⟨mapP, Km, hmap⟩ := hK.mapList
  refine ⟨mapP rowProg, 1 + 11 * Km, ?_⟩
  intro main p c M r hc1 hc2 As rest hdisc
  have hKrow1 : 1 ≤ Krow := by
    by_contra hcon
    have h0 : Krow = 0 := by omega
    have hIn : InDiscVec 0 0 ([] : List (ℤ × ℤ)) :=
      ⟨rfl, by intro z hz; exact absurd hz (by simp)⟩
    have hW := hrow main 0 1 0 (by norm_num) (by norm_num) ([] : List (ℤ × ℤ)) rest hIn
    obtain ⟨out, s', n, -, hev, hcost, -, -⟩ :=
      hW (cvecVal ([] : List (ℤ × ℤ)) :: Val.int (0 : ℤ) :: Val.int (1 : ℤ) :: rest) rfl
        ⟨fun _ => Glyph.eos,
          fun k => if k = 0 then
            encs (cvecVal ([] : List (ℤ × ℤ)) :: Val.int (0 : ℤ) :: Val.int (1 : ℤ) :: rest)
            else []⟩ []
        (by simp)
    have hn0 : n ≤ 0 := by simpa [h0] using hcost
    have hp1 : 1 ≤ n := eval_cost_pos hev
    omega
  have hmain := hmap main rowProg (Val.int (p : ℤ) :: Val.int (c : ℤ) :: rest)
    (ArrP p r) (ArrQ p r c) (Krow * (r + 1) * (p + 1) ^ 2 + Krow) (cvecSz p r)
    (fun x hx => rowMapElem hK rowProg Krow hrow hc1 hc2 rest x hx)
    (As.map cvecVal)
    (by
      intro x hx
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
      have hru := hdisc.2 u hu
      exact ⟨⟨u, rfl, hru⟩, vsz_cvecVal_le hru⟩)
  refine WordR_conseq hmain ?_ ?_ ?_
  · intro vs hvs
    exact hvs
  · intro vs out hvs hq
    obtain ⟨ys, hout, hForall⟩ := hq
    obtain ⟨Bs, hys, hlen, hP⟩ := arrExtract hForall
    refine ⟨Bs, ?_, ?_, ?_⟩
    · rw [hout, hys]
      simp only [rarrVal]
    · rw [hlen, hdisc.1]
    · intro i hi
      exact hP i (by rw [hdisc.1]; exact hi)
  · intro vs hvs
    have hKey : cvecSz p r + 1 ≤ 11 * (Krow * (r + 1) * (p + 1) ^ 2 + Krow) := by
      have hcfx : cvecSz p r + 1 = r * (2 * p + 9) + 2 := by
        simp only [cvecSz, cfxSz]
        ring
      rw [hcfx]
      have h2p : 2 * p + 9 ≤ 11 * (p + 1) ^ 2 := by nlinarith
      have hmul := Nat.mul_le_mul_left r h2p
      nlinarith [hmul, hKrow1, Nat.zero_le r, Nat.zero_le p]
    show (As.map cvecVal).length *
        (Krow * (r + 1) * (p + 1) ^ 2 + Krow + Km * (cvecSz p r + 1)) + Km ≤
      (1 + 11 * Km) * (M * (Krow * (r + 1) * (p + 1) ^ 2 + Krow) + 1) + (1 + 11 * Km)
    rw [List.length_map, hdisc.1]
    have h1 : Km * (cvecSz p r + 1) ≤ Km * (11 * (Krow * (r + 1) * (p + 1) ^ 2 + Krow)) :=
      Nat.mul_le_mul_left Km hKey
    have h2 : Krow * (r + 1) * (p + 1) ^ 2 + Krow + Km * (cvecSz p r + 1) ≤
        (Krow * (r + 1) * (p + 1) ^ 2 + Krow) * (1 + 11 * Km) := by
      calc Krow * (r + 1) * (p + 1) ^ 2 + Krow + Km * (cvecSz p r + 1)
          ≤ Krow * (r + 1) * (p + 1) ^ 2 + Krow +
              Km * (11 * (Krow * (r + 1) * (p + 1) ^ 2 + Krow)) :=
            Nat.add_le_add_left h1 _
        _ = (Krow * (r + 1) * (p + 1) ^ 2 + Krow) * (1 + 11 * Km) := by ring
    have h3 : M * (Krow * (r + 1) * (p + 1) ^ 2 + Krow + Km * (cvecSz p r + 1)) ≤
        M * ((Krow * (r + 1) * (p + 1) ^ 2 + Krow) * (1 + 11 * Km)) :=
      Nat.mul_le_mul_left M h2
    nlinarith [h3]


end Work.ConvR
