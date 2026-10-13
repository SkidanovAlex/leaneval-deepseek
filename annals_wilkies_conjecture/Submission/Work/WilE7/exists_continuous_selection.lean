import Mathlib
import Submission.Work.WilE7.SelDefs
import Submission.Work.WilE7.erF_continuous
import Submission.Work.WilE7.erF_strictMono
import Submission.Work.WilE7.artanh_continuousOn

open Set
open scoped Topology

namespace Work.WilE7

/-- **Continuous selection between two continuous `EReal`-valued functions.**

Given `a < b` pointwise on `C`, with `a`, `b` continuous on `C`, there is a continuous
real-valued `m` on `C` with `a < m < b` pointwise.  The construction is pointwise: `erF`
(`⊥ ↦ -1`, `⊤ ↦ 1`, `x ↦ tanh x`) is a strictly increasing continuous map of `EReal` into
`[-1,1]`, so the midpoint `(erF (a x) + erF (b x)) / 2` lies in `(-1,1)`, and applying its
inverse `Real.artanh` gives an admissible value depending continuously on `x`. -/
theorem exists_continuous_selection {α : Type*} [TopologicalSpace α] {C : Set α}
    {a b : α → EReal} (ha : ContinuousOn a C) (hb : ContinuousOn b C)
    (hab : ∀ x ∈ C, a x < b x) :
    ∃ m : α → ℝ, ContinuousOn m C ∧ ∀ x ∈ C, a x < (m x : EReal) ∧ (m x : EReal) < b x := by
  have hmono : Monotone erF := erF_strictMono.monotone
  have hlo : ∀ x : α, -1 ≤ erF (a x) := by
    intro x
    have h := hmono (show (⊥ : EReal) ≤ a x from bot_le)
    simpa using h
  have hhi : ∀ x : α, erF (b x) ≤ 1 := by
    intro x
    have h := hmono (show b x ≤ (⊤ : EReal) from le_top)
    simpa using h
  have hmem : ∀ x ∈ C, (erF (a x) + erF (b x)) / 2 ∈ Ioo (-1 : ℝ) 1 := by
    intro x hx
    have hlt : erF (a x) < erF (b x) := erF_strictMono.lt_iff_lt.mpr (hab x hx)
    constructor <;> linarith [hlo x, hhi x]
  have h1 : ContinuousOn (fun x => erF (a x)) C := erF_continuous.comp_continuousOn ha
  have h2 : ContinuousOn (fun x => erF (b x)) C := erF_continuous.comp_continuousOn hb
  have hmid : ContinuousOn (fun x => (erF (a x) + erF (b x)) / 2) C := (h1.add h2).div_const 2
  have hmaps : MapsTo (fun x => (erF (a x) + erF (b x)) / 2) C (Ioo (-1 : ℝ) 1) := hmem
  refine ⟨fun x => Real.artanh ((erF (a x) + erF (b x)) / 2),
    artanh_continuousOn.comp hmid hmaps, ?_⟩
  intro x hx
  have hlt : erF (a x) < erF (b x) := erF_strictMono.lt_iff_lt.mpr (hab x hx)
  have key : Real.tanh (Real.artanh ((erF (a x) + erF (b x)) / 2))
      = (erF (a x) + erF (b x)) / 2 := Real.tanh_artanh (hmem x hx)
  constructor
  · refine erF_strictMono.lt_iff_lt.mp ?_
    simp only [erF_coe]
    rw [key]
    linarith
  · refine erF_strictMono.lt_iff_lt.mp ?_
    simp only [erF_coe]
    rw [key]
    linarith

end Work.WilE7
