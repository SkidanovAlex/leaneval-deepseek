import Mathlib
import Submission.Work.Main.defs
import Submission.Work.Main.bridge
import Submission.Work.Main.crt.Pcr_inj
import Submission.Work.Main.crt.Pcr_lt

/-!
# Reading the coefficient vector off the CRT reindexing

The `CrtWordProp` word in direction `0` transforms a list `xs` of `S = ∏sᵢ` values into a list
`ys` of the same length with `ys[crtIdx ss m] = xs[m]` (`Work.Main.CrtWordProp`).  From such a
`ys` we recover a coefficient vector `F : List (ℤ × ℤ)` of fixed-point complex values with
`ys = F.map cfxVal` and `F[crtIdx ss m] = xs[m]`: this is possible because `crtIdx ss` is a
bijection of `[0, ∏ss)` whenever the moduli are pairwise coprime and positive.

The bijection itself is proved elsewhere and used here through `Work.Main.bridge`
(`Pcr_eq_crtIdx`), `Work.Main.crt.Pcr_lt` (the range bound) and
`Work.Main.crt.Pinv_spec` (surjectivity).
-/

set_option autoImplicit false

namespace Work.Main.step

open HvdH

/-- Underlying pair of an encoded fixed-point complex value (junk on any other value). -/
def cfxExtract : Val → ℤ × ℤ
  | .cons (.int a) (.int b) => (a, b)
  | _ => (0, 0)

@[simp] theorem cfxExtract_cfxVal (z : ℤ × ℤ) : cfxExtract (cfxVal z) = z := rfl

/-- `HvdH.crtIdx` is the interface name of the flat CRT index `Work.Main.Pcr`. -/
theorem crtIdx_eq_Pcr (ss : List ℕ) (m : ℕ) : HvdH.crtIdx ss m = Work.Main.Pcr ss m :=
  (Work.Main.Pcr_eq_crtIdx ss m).symm

/-- The flat CRT index is bounded by the product of the (positive) moduli. -/
theorem crtIdx_lt {ss : List ℕ} (hpos : ∀ s ∈ ss, 0 < s) (m : ℕ) :
    HvdH.crtIdx ss m < ss.prod := by
  rw [crtIdx_eq_Pcr]; exact Work.Main.crt.Pcr_lt hpos m

/-- Surjectivity of `crtIdx ss` on `[0, ∏ss)` for pairwise coprime positive moduli. -/
theorem crtIdx_surj {ss : List ℕ} (hcop : ss.Pairwise Nat.Coprime) (hpos : ∀ s ∈ ss, 0 < s)
    {q : ℕ} (hq : q < ss.prod) : ∃ m < ss.prod, HvdH.crtIdx ss m = q := by
  obtain ⟨hlt, hPcr⟩ := Work.Main.crt.Pinv_spec hcop hpos hq
  exact ⟨Work.Main.Pinv ss q, hlt, by rw [crtIdx_eq_Pcr]; exact hPcr⟩

theorem crtExtract {ss : List ℕ} {xs : List (ℤ × ℤ)} {ys : List HvdH.Val}
    (h1 : ∀ s ∈ ss, 1 ≤ s) (hcop : ss.Pairwise Nat.Coprime)
    (hxl : xs.length = ss.prod) (hyl : ys.length = ss.prod)
    (h : ∀ m < ss.prod, ys.getD (HvdH.crtIdx ss m) HvdH.Val.nil
        = (xs.map HvdH.cfxVal).getD m HvdH.Val.nil) :
    ∃ F : List (ℤ × ℤ), ys = F.map HvdH.cfxVal ∧ F.length = ss.prod ∧
      ∀ m < ss.prod, F.getD (HvdH.crtIdx ss m) (0, 0) = xs.getD m (0, 0) := by
  have hpos : ∀ s ∈ ss, 0 < s := fun s hs => Nat.lt_of_lt_of_le Nat.zero_lt_one (h1 s hs)
  -- every index of `ys` carries an encoded fixed-point complex value
  have hys : ∀ i < ss.prod, ys.getD i HvdH.Val.nil
      = HvdH.cfxVal (xs.getD (Work.Main.Pinv ss i) (0, 0)) := by
    intro i hi
    obtain ⟨hm, hPcr⟩ := Work.Main.crt.Pinv_spec hcop hpos hi
    have hxi : Work.Main.Pinv ss i < xs.length := by rw [hxl]; exact hm
    have hxi' : Work.Main.Pinv ss i < (xs.map HvdH.cfxVal).length := by
      rw [List.length_map]; exact hxi
    have step : ys.getD (HvdH.crtIdx ss (Work.Main.Pinv ss i)) HvdH.Val.nil
        = (xs.map HvdH.cfxVal).getD (Work.Main.Pinv ss i) HvdH.Val.nil := h _ hm
    rw [crtIdx_eq_Pcr, hPcr] at step
    rw [step, List.getD_eq_getElem _ _ hxi', List.getElem_map,
      ← List.getD_eq_getElem _ _ hxi]
  -- each element of `ys` is an encoded fixed-point complex value
  have hys' : ∀ a ∈ ys, ∃ z : ℤ × ℤ, a = HvdH.cfxVal z := by
    intro a ha
    obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.mp ha
    have hi' : i < ss.prod := by rw [← hyl]; exact hi
    exact ⟨xs.getD (Work.Main.Pinv ss i) (0, 0),
      by rw [← hia, ← List.getD_eq_getElem ys HvdH.Val.nil hi]; exact hys i hi'⟩
  refine ⟨ys.map cfxExtract, ?_, ?_, ?_⟩
  · rw [List.map_map]
    have hcomp : ∀ a ∈ ys, (HvdH.cfxVal ∘ cfxExtract) a = id a := by
      intro a ha
      obtain ⟨z, hz⟩ := hys' a ha
      rw [hz]; rfl
    rw [List.map_congr_left hcomp, List.map_id]
  · rw [List.length_map, hyl]
  · intro m hm
    have hjm : HvdH.crtIdx ss m < (ys.map cfxExtract).length := by
      rw [List.length_map, hyl]; exact crtIdx_lt hpos m
    have hjm' : HvdH.crtIdx ss m < ys.length := by rw [hyl]; exact crtIdx_lt hpos m
    have hxm : m < xs.length := by rw [hxl]; exact hm
    have hxm' : m < (xs.map HvdH.cfxVal).length := by rw [List.length_map]; exact hxm
    rw [List.getD_eq_getElem _ _ hjm, List.getElem_map,
      ← List.getD_eq_getElem ys HvdH.Val.nil hjm', h _ hm,
      List.getD_eq_getElem _ _ hxm', List.getElem_map,
      ← List.getD_eq_getElem xs (0, 0) hxm]
    rfl

end Work.Main.step
