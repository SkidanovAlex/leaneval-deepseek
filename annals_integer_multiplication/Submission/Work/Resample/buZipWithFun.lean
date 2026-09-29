import Mathlib
import Submission.Work.Resample.buQWscalDefs

namespace Work.Resample

open HvdH

/-- List identity behind `buZipWithFun`: if `zs` has the same length as `xs` and agrees pointwise
(in `getD` form) with `List.zipWith F xs ys`, then it *is* that `zipWith` (note `xs.length = ys.length`). -/
theorem buZipWithFun_aux_eq_zipWith (F : Val → Val → Val) {xs ys zs : List Val}
    (hlen : xs.length = ys.length) (hzs : zs.length = xs.length)
    (h : ∀ i < xs.length, zs.getD i Val.nil = F (xs.getD i Val.nil) (ys.getD i Val.nil)) :
    zs = List.zipWith F xs ys := by
  apply List.ext_getElem
  · rw [hzs, List.length_zipWith, hlen, min_self]
  · intro i hi1 hi2
    have hxs : i < xs.length := by rw [← hzs]; exact hi1
    have hys : i < ys.length := by rw [← hlen]; exact hxs
    have hp := h i hxs
    rw [List.getD_eq_getElem zs Val.nil hi1, List.getD_eq_getElem xs Val.nil hxs,
      List.getD_eq_getElem ys Val.nil hys] at hp
    rw [hp]
    exact (List.getElem_zipWith (h := hi2)).symm

/-- The `zipWith` field of `KernelLib` with a *functional* element map (the output list is a
definite `List.zipWith F xs ys`, not just specified pointwise).  Derive it from `KL.zipWith` by
instantiating `Q x y z := z = F x y` and `List.ext_getElem`. -/
theorem buZipWithFun (KL : KernelLib) :
    ∃ (comb : Cmd → Cmd) (Kz : ℕ),
    ∀ (main q : Cmd) (T : List Val) (P : Val → Val → Prop)
      (F : Val → Val → Val) (c L : ℕ),
      (∀ x y, P x y → WordR main q (fun vs => vs = x :: y :: T)
        (fun _ out => out = F x y :: T) (fun _ => c)) →
      (∀ x y, P x y → vsz (F x y) ≤ L) →
      ∀ xs ys : List Val, xs.length = ys.length →
        (∀ i < xs.length, P (xs.getD i Val.nil) (ys.getD i Val.nil)) →
        (∀ x ∈ xs ++ ys, vsz x ≤ L) →
        WordR main (comb q) (fun vs => vs = ofList xs :: ofList ys :: T)
          (fun _ out => out = ofList (List.zipWith F xs ys) :: T)
          (fun _ => xs.length * (c + Kz * (L + 1)) + Kz) := by
  obtain ⟨comb, K, hK⟩ := KL.zipWith
  refine ⟨comb, K, ?_⟩
  intro main q T P F c L hq hL xs ys hlen hP hLall
  set Q : Val → Val → Val → Prop := fun x y z => z = F x y with hQ
  -- the element word, with the pointwise postcondition expected by `KL.zipWith`
  have hq' : ∀ x y, P x y → WordR main q (fun vs => vs = x :: y :: T)
      (fun _ out => ∃ z, out = z :: T ∧ Q x y z ∧ vsz z ≤ L) (fun _ => c) := by
    intro x y hxy
    have h1 := hq x y hxy
    intro vs hv s R hR
    obtain ⟨out, s', n, hpost, hev, hn, h0, hfr⟩ := h1 vs hv s R hR
    exact ⟨out, s', n, ⟨F x y, hpost, rfl, hL x y hxy⟩, hev, hn, h0, hfr⟩
  have h2 := hK main q T P Q c L hq' xs ys hlen hP hLall
  intro vs hv s R hR
  obtain ⟨out, s', n, hpost, hev, hn, h0, hfr⟩ := h2 vs hv s R hR
  obtain ⟨zs, hout, hzslen, hpt⟩ := hpost
  -- the pointwise specification pins the whole list down
  have hzeq : zs = List.zipWith F xs ys :=
    buZipWithFun_aux_eq_zipWith F hlen hzslen (fun i hi => hpt i hi)
  exact ⟨out, s', n, by rw [hout, hzeq], hev, hn, h0, hfr⟩

end Work.Resample
