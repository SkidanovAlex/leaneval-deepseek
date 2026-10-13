import Mathlib
import Submission.Work.WilG4a.LipChartsDefs

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Work.WilG4a

/-- Helper: the linear reparametrisation of `(Aend, Bend)` maps `I = (0,1)` into `(Aend, Bend)`. -/
lemma chart1_lin_mem_Ioo {A B t : ℝ} (hAB : A < B) (ht : t ∈ I) :
    A + (B - A) * t ∈ Set.Ioo A B :=
  ⟨by nlinarith [hAB, ht.1, ht.2], by nlinarith [hAB, ht.1, ht.2]⟩

/-- Helper: the inverse linear reparametrisation. -/
lemma chart1_lin_inv {A B x : ℝ} (hAB : A < B) (hx : x ∈ Set.Ioo A B) :
    A + (B - A) * ((x - A) / (B - A)) = x := by
  have hden : (B - A) ≠ 0 := by linarith
  have hmul : (B - A) * ((x - A) / (B - A)) = x - A := by
    field_simp
  rw [hmul]; ring

/-- Helper: the inverse reparametrisation parameter lies in `I`. -/
lemma chart1_inv_param_mem_I {A B x : ℝ} (hAB : A < B) (hx : x ∈ Set.Ioo A B) :
    (x - A) / (B - A) ∈ I := by
  have hden : 0 < B - A := by linarith
  refine ⟨div_pos (by linarith [hx.1]) hden, ?_⟩
  rw [div_lt_one hden]; linarith [hx.2]

theorem cgo_chart1_char {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ)
    (κ : Set (Fin (p+1) → ℝ)) (l : Fin p → ℝ) {a b : ℝ}
    (hfib : Work.WilG4a.fibre κ l = Set.Ioo a b) (hne : (Work.WilG4a.fibre κ l).Nonempty)
    (hmono : StrictMonoOn (f l) (Work.WilG4a.fibre κ l) ∨
      StrictAntiOn (f l) (Work.WilG4a.fibre κ l))
    (himg : Work.WilG4a.imgFibre κ f l = Set.Ioo (Work.WilG4a.Aend κ f l) (Work.WilG4a.Bend κ f l))
    (hAB : Work.WilG4a.Aend κ f l < Work.WilG4a.Bend κ f l) :
    (∀ t ∈ Work.WilG4a.I, Work.WilG4a.chart1 f κ l t ∈ Work.WilG4a.fibre κ l ∧
      f l (Work.WilG4a.chart1 f κ l t) =
        Work.WilG4a.Aend κ f l + (Work.WilG4a.Bend κ f l - Work.WilG4a.Aend κ f l) * t) ∧
    (∀ x ∈ Work.WilG4a.fibre κ l, ∃ t ∈ Work.WilG4a.I, Work.WilG4a.chart1 f κ l t = x) := by
  have hinj : Set.InjOn (f l) (fibre κ l) := by
    rcases hmono with h | h
    · exact h.injOn
    · exact h.injOn
  constructor
  · -- the chart parametrises the image of the fibre by `t ∈ I`
    intro t ht
    have hmem : Aend κ f l + (Bend κ f l - Aend κ f l) * t ∈
        Set.Ioo (Aend κ f l) (Bend κ f l) := chart1_lin_mem_Ioo hAB ht
    have hex : ∃ y : ℝ, Fin.snoc l y ∈ κ ∧
        f l y = Aend κ f l + (Bend κ f l - Aend κ f l) * t := by
      have h : Aend κ f l + (Bend κ f l - Aend κ f l) * t ∈ imgFibre κ f l := by
        rw [himg]; exact hmem
      simpa [imgFibre] using h
    rw [chart1, dite_eq_left hex]
    exact Classical.choose_spec hex
  · -- the chart is surjective onto the fibre
    intro x hx
    have hx' : f l x ∈ imgFibre κ f l := ⟨x, hx, rfl⟩
    have hbx : f l x ∈ Set.Ioo (Aend κ f l) (Bend κ f l) := by
      rwa [himg] at hx'
    refine ⟨(f l x - Aend κ f l) / (Bend κ f l - Aend κ f l),
      chart1_inv_param_mem_I hAB hbx, ?_⟩
    have hval : Aend κ f l + (Bend κ f l - Aend κ f l) *
        ((f l x - Aend κ f l) / (Bend κ f l - Aend κ f l)) = f l x :=
      chart1_lin_inv hAB hbx
    have hex : ∃ y : ℝ, Fin.snoc l y ∈ κ ∧
        f l y = Aend κ f l + (Bend κ f l - Aend κ f l) *
          ((f l x - Aend κ f l) / (Bend κ f l - Aend κ f l)) :=
      ⟨x, hx, hval.symm⟩
    rw [chart1, dite_eq_left hex]
    have hspec := Classical.choose_spec hex
    exact hinj hspec.1 hx (hspec.2.trans hval)

end Work.WilG4a
