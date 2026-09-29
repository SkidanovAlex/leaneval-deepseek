import Mathlib
import Submission.Work.Resample.auPrepDefs

namespace Work.Resample

/-- `mapList` for a *fixed tail*: if every `x ∈ xs` is mapped to `F x` by the word `q` acting on
the window `x :: T` (i.e. `x` followed by the fixed values `T` and then arbitrary junk), then
`comb q` maps `ofList xs` to `ofList (xs.map F)`, with the same tail `T` underneath.

This is the `Pipe`-form of `mapListFun` in which the element word is allowed to *read* the fixed
values `T` sitting just below the element (these play the role of the parameters that the record
word of the table needs). -/
theorem auMapListTail {comb : HvdH.Cmd → HvdH.Cmd} {Kml : ℕ} (hML : Work.Resample.MapListField comb Kml)
    {main q : HvdH.Cmd} {T xs : List HvdH.Val} {F : HvdH.Val → HvdH.Val} {c L : ℕ}
    (h : ∀ x ∈ xs, Work.Resample.Pipe main q (x :: T) (F x :: T) c)
    (hx : ∀ x ∈ xs, HvdH.vsz x ≤ L) (hy : ∀ x ∈ xs, HvdH.vsz (F x) ≤ L) :
    Work.Resample.Pipe main (comb q) (HvdH.ofList xs :: T) (HvdH.ofList (xs.map F) :: T)
      (xs.length * (c + Kml * (L + 1)) + Kml) := by
  intro rest
  -- In the ambient window the tail below the list is `T ++ rest`; the element word therefore
  -- receives `x :: (T ++ rest)`.
  have hinner : ∀ x, x ∈ xs → HvdH.WordR main q
      (fun vs => vs = x :: (T ++ rest))
      (fun _ out => ∃ y, out = y :: (T ++ rest) ∧ y = F x ∧ HvdH.vsz y ≤ L) c := by
    intro x hxmem
    refine Work.Kernel.WordR_conseq (h x hxmem rest) (fun vs hv => hv) ?_ (fun vs _ => le_rfl)
    intro vs out hv hout
    exact ⟨F x, hout, rfl, hy x hxmem⟩
  have hmain := hML main q (T ++ rest) (fun x => x ∈ xs) (fun x y => y = F x) c L hinner xs
    (fun x hxm => ⟨hxm, hx x hxm⟩)
  refine Work.Kernel.WordR_conseq hmain (fun vs hv => hv) ?_ (fun vs _ => le_rfl)
  intro vs out hv hout
  obtain ⟨ys, hout, hf⟩ := hout
  rw [hout, forall₂_map_right hf]
  rfl

end Work.Resample
