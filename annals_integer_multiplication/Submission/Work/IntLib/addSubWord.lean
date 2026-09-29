import Mathlib
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.Raw
import Submission.Work.IntLib.ofBitsAPI
import Submission.Work.IntLib.AddSub.Defs
import Submission.Work.IntLib.AddSub.Basic
import Submission.Work.IntLib.AddSub.EvKit
import Submission.Work.IntLib.AddSub.Assembly

/-!
# `IntLib` / add–sub: signed addition and subtraction in linear time

`AddSub.asw_prog false` adds the two integers on top of the value stack, `AddSub.asw_prog true`
subtracts them (it negates the second sign glyph), both at cost `O(isz a + isz b)`.
-/

namespace Work.IntLib

open HvdH

theorem addSubWord : (∃ (p : HvdH.Cmd) (K : ℕ), ∀ main, HvdH.BinOp main p (fun _ _ => True) (· + ·) (fun a b => K * (HvdH.isz a + HvdH.isz b))) ∧ (∃ (p : HvdH.Cmd) (K : ℕ), ∀ main, HvdH.BinOp main p (fun _ _ => True) (· - ·) (fun a b => K * (HvdH.isz a + HvdH.isz b))) := by
  constructor
  · obtain ⟨K, hK⟩ := AddSub.asw_word false
    refine ⟨AddSub.asw_prog false, K, fun main => ?_⟩
    intro vs hP s R hR
    obtain ⟨out, s', n, ⟨a, b, rest, hvs, hout⟩, hev, hn, hstk, hoth⟩ := hK main vs hP s R hR
    have hout' : out = (Val.int (a + b)) :: rest := by
      simpa using hout
    exact ⟨out, s', n, ⟨a, b, rest, hvs, hout'⟩, hev, hn, hstk, hoth⟩
  · obtain ⟨K, hK⟩ := AddSub.asw_word true
    refine ⟨AddSub.asw_prog true, K, fun main => ?_⟩
    intro vs hP s R hR
    obtain ⟨out, s', n, ⟨a, b, rest, hvs, hout⟩, hev, hn, hstk, hoth⟩ := hK main vs hP s R hR
    have hout' : out = (Val.int (a - b)) :: rest := by
      simpa [sub_eq_add_neg] using hout
    exact ⟨out, s', n, ⟨a, b, rest, hvs, hout'⟩, hev, hn, hstk, hoth⟩

end Work.IntLib
