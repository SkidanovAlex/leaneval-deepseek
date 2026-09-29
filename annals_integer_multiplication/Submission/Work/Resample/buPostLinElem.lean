import Mathlib
import Submission.Work.Resample.buQWpostDefs
import Submission.Work.Resample.buQWelemLin
import Submission.Work.Resample.buQWelemKit

namespace Work.Resample

open HvdH
open Work.Main.word

local infixr:68 " ;;; " => HvdH.Cmd.seq

/-- If two `cons`-chains with the same 3-value prefix are equal, their tails are equal. -/
theorem cons3_tail_eq {A B C : Val} {r r' : List Val}
    (h : A :: B :: C :: r = A :: B :: C :: r') : r = r' := by
  have h1 : B :: C :: r = B :: C :: r' := (List.cons.inj h).2
  have h2 : C :: r = C :: r' := (List.cons.inj h1).2
  exact (List.cons.inj h2).2

/-- The `∃ rest`-form of `Work.Resample.buQWelemLin`, read as a `Pipe` word on the fixed 3-value
window `[cfxVal a, cfxVal b, int σ]` (the tail `rest` is quantified outside). -/
theorem bu_linPipe {linP : Cmd} {KLin P : ℕ} {σ : ℤ} {a b : ℤ × ℤ} (main : Cmd)
    (h : WordR main linP
      (fun vs => ∃ rest, vs = cfxVal a :: cfxVal b :: Val.int σ :: rest)
      (fun vs out => ∃ rest, vs = cfxVal a :: cfxVal b :: Val.int σ :: rest ∧
        out = cfxVal (a.1 + σ * b.1, a.2 + σ * b.2) :: rest)
      (fun _ => KLin * (P + 1))) :
    Pipe main linP [cfxVal a, cfxVal b, Val.int σ]
      [cfxVal (a.1 + σ * b.1, a.2 + σ * b.2)] (KLin * (P + 1)) := by
  intro rest vs hvs s R hR
  have hvs2 : vs = cfxVal a :: cfxVal b :: Val.int σ :: rest := hvs
  obtain ⟨out, s', n, ⟨rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ := h vs ⟨rest, hvs2⟩ s R hR
  have hrest : rest' = rest := (cons3_tail_eq (hvs2.symm.trans hvs')).symm
  refine ⟨out, s', n, ?_, hev, hn, hstk, hoth⟩
  rw [hrest] at hout
  exact hout

/-- **Element word for the signed accumulation inside a `zipWith`.**

Consume the two complex values `cfxVal a` and `cfxVal b` and the sign `Val.int σ` on top of the
stack and produce `cfxVal (a + σ·b)` **followed by the same `Val.int σ`** (so that the fixed tail `T`
below the sign is preserved and the sign is still available for the next element):

  `cfxVal a :: cfxVal b :: int σ :: T  ↦  cfxVal (a₁+σ·b₁, a₂+σ·b₂) :: int σ :: T`.

Suggested program: `KL.pick 2 ;;; KL.roll 3 ;;; KL.roll 3 ;;; KL.roll 3 ;;; <the 17-step program of
`Work.Resample.buQWelemLin>` (`unconsP ;;; rollP 2 ;;; unconsP ;;; pickP 4 ;;; rollP 1 ;;; mulP ;;;
pickP 4 ;;; rollP 2 ;;; mulP ;;; rollP 3 ;;; addP ;;; rollP 2 ;;; rollP 2 ;;; addP ;;; rollP 2 ;;;
dropP ;;; consP`).  On `[int σ, cfxVal a, cfxVal b, int σ]` the three `roll 3` steps rotate the
4-element block into `[cfxVal a, cfxVal b, int σ(o), int σ(c)]`, so the linear-combination program
(which consumes its `int σ`) leaves the copied sign in place; the composed cost is of the form
`Kc·(P+1)`. -/
theorem buPostLinElem (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (q : HvdH.Cmd) (Kc : ℕ),
    ∀ (main : HvdH.Cmd) (P : ℕ) (σ : ℤ) (a b : ℤ × ℤ) (T : List HvdH.Val),
      (σ = 1 ∨ σ = -1) → HvdH.isz a.1 ≤ P → HvdH.isz a.2 ≤ P →
      HvdH.isz b.1 ≤ P → HvdH.isz b.2 ≤ P →
      HvdH.WordR main q
        (fun vs => vs = HvdH.cfxVal a :: HvdH.cfxVal b :: HvdH.Val.int σ :: T)
        (fun vs out => vs = HvdH.cfxVal a :: HvdH.cfxVal b :: HvdH.Val.int σ :: T ∧
          out = HvdH.cfxVal (a.1 + σ * b.1, a.2 + σ * b.2) :: HvdH.Val.int σ :: T)
        (fun _ => Kc * (P + 1)) := by
  obtain ⟨pickP, KP, hpick⟩ := KL.pick
  obtain ⟨rollP, KR, hroll⟩ := KL.roll
  obtain ⟨linP, KLin, hlin⟩ := buQWelemLin KL IL
  refine ⟨pickP 2 ;;; rollP 3 ;;; rollP 3 ;;; rollP 3 ;;; linP,
    105 * KP + (105 * KR + (105 * KR + (105 * KR + KLin))), ?_⟩
  intro main P σ a b T hσ ha1 ha2 hb1 hb2
  have hsig : isz σ ≤ 3 := isz_pm_one hσ
  have hA : vsz (HvdH.cfxVal a) ≤ 4 * P + 4 := good_cfx ha1 ha2
  have hB : vsz (HvdH.cfxVal b) ≤ 4 * P + 4 := good_cfx hb1 hb2
  have hS : vsz (HvdH.Val.int σ) ≤ 4 * P + 4 := good_pm hsig
  -- ### the window of the three consumed values
  have hM3 : ∀ v ∈ ([HvdH.cfxVal a, HvdH.cfxVal b, Val.int σ] : List Val),
      vsz v ≤ 4 * P + 4 := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact hA
    · exact hB
    · exact hS
  -- ### step 1: copy the sign to the top
  have H1 : Pipe main (pickP 2) [HvdH.cfxVal a, HvdH.cfxVal b, Val.int σ]
      [Val.int σ, HvdH.cfxVal a, HvdH.cfxVal b, Val.int σ] (105 * KP * (P + 1)) :=
    Pipe.rw (bu_pickK4 main hpick (A := [HvdH.cfxVal a, HvdH.cfxVal b, Val.int σ])
      (k := 2) (P := P) (by simp) (by norm_num) hM3) (by simp)
  -- ### step 2: rotate the 4-block `[σ, A, B, σ] → [σ, σ, A, B]`
  have hM4a : ∀ v ∈ ([Val.int σ, HvdH.cfxVal a, HvdH.cfxVal b, Val.int σ] : List Val),
      vsz v ≤ 4 * P + 4 := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hS
    · exact hA
    · exact hB
    · exact hS
  have H2 : Pipe main (rollP 3) [Val.int σ, HvdH.cfxVal a, HvdH.cfxVal b, Val.int σ]
      [Val.int σ, Val.int σ, HvdH.cfxVal a, HvdH.cfxVal b] (105 * KR * (P + 1)) :=
    Pipe.rw (bu_rollK4 main hroll
      (A := [Val.int σ, HvdH.cfxVal a, HvdH.cfxVal b, Val.int σ])
      (k := 3) (P := P) (by simp) (by norm_num) hM4a) (by simp)
  -- ### step 3: `[σ, σ, A, B] → [B, σ, σ, A]`
  have hM4b : ∀ v ∈ ([Val.int σ, Val.int σ, HvdH.cfxVal a, HvdH.cfxVal b] : List Val),
      vsz v ≤ 4 * P + 4 := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hS
    · exact hS
    · exact hA
    · exact hB
  have H3 : Pipe main (rollP 3) [Val.int σ, Val.int σ, HvdH.cfxVal a, HvdH.cfxVal b]
      [HvdH.cfxVal b, Val.int σ, Val.int σ, HvdH.cfxVal a] (105 * KR * (P + 1)) :=
    Pipe.rw (bu_rollK4 main hroll
      (A := [Val.int σ, Val.int σ, HvdH.cfxVal a, HvdH.cfxVal b])
      (k := 3) (P := P) (by simp) (by norm_num) hM4b) (by simp)
  -- ### step 4: `[B, σ, σ, A] → [A, B, σ, σ]`
  have hM4c : ∀ v ∈ ([HvdH.cfxVal b, Val.int σ, Val.int σ, HvdH.cfxVal a] : List Val),
      vsz v ≤ 4 * P + 4 := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hB
    · exact hS
    · exact hS
    · exact hA
  have H4 : Pipe main (rollP 3) [HvdH.cfxVal b, Val.int σ, Val.int σ, HvdH.cfxVal a]
      [HvdH.cfxVal a, HvdH.cfxVal b, Val.int σ, Val.int σ] (105 * KR * (P + 1)) :=
    Pipe.rw (bu_rollK4 main hroll
      (A := [HvdH.cfxVal b, Val.int σ, Val.int σ, HvdH.cfxVal a])
      (k := 3) (P := P) (by simp) (by norm_num) hM4c) (by simp)
  -- ### step 5: the linear-combination word on `[A, B, σ]`, keeping the sign below
  have HLin : Pipe main linP [HvdH.cfxVal a, HvdH.cfxVal b, Val.int σ]
      [HvdH.cfxVal (a.1 + σ * b.1, a.2 + σ * b.2)] (KLin * (P + 1)) :=
    bu_linPipe main (hlin main P σ a b hσ ha1 ha2 hb1 hb2)
  have H5 : Pipe main linP [HvdH.cfxVal a, HvdH.cfxVal b, Val.int σ, Val.int σ]
      [HvdH.cfxVal (a.1 + σ * b.1, a.2 + σ * b.2), Val.int σ] (KLin * (P + 1)) :=
    Pipe.appendTail [Val.int σ] HLin
  -- ### assemble the chain
  have hAll : Pipe main (pickP 2 ;;; rollP 3 ;;; rollP 3 ;;; rollP 3 ;;; linP)
      [HvdH.cfxVal a, HvdH.cfxVal b, Val.int σ]
      [HvdH.cfxVal (a.1 + σ * b.1, a.2 + σ * b.2), Val.int σ]
      ((105 * KP + (105 * KR + (105 * KR + (105 * KR + KLin)))) * (P + 1)) :=
    Pipe.comp' H1 (Pipe.comp' H2 (Pipe.comp' H3 (Pipe.comp' H4 H5)))
  intro vs hvs s R hR
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := hAll T vs hvs s R hR
  exact ⟨out, s', n, ⟨hvs, hout⟩, hev, hn, hstk, hoth⟩

end Work.Resample
