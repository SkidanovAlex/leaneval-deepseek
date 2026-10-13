/-
  WilG4a — the point-wise Lipschitz statement for the charts `chart1 f κ` (BNZ §5.1).

  Setting.  `κ` is a cell inside the strip `{z : ℝ^{p+1} | z (last) ∈ I}`, and for every parameter
  `l` the fibre `fibre κ l = {y | Fin.snoc l y ∈ κ}` is a subsingleton (it is empty, or a single
  point).  The chart `chart1 f κ l` is the branch of the inverse of `x ↦ f l x` over the image
  interval `[Aend κ f l, Bend κ f l]`, linearly reparametrised by `t`.

  Because the fibre is a subsingleton, the image of the fibre — hence the interval spanned by
  `Aend` and `Bend` — degenerates: `Aend κ f l = Bend κ f l = f l y` for the unique point `y` of a
  nonempty fibre.  Consequently the chart is *constant* in `t` (equal to that point on a nonempty
  fibre, and to the junk value `1/2` on an empty one), and every claim in
  `lipschitz_chart_point` follows from this constancy.
-/
import Mathlib
import Submission.Work.WilG4a.LipChartsDefs

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

open Classical

namespace Work.WilG4a

/-! ## Fibres of a cell sitting inside the strip -/

/-- Every fibre of a set contained in the strip `{z | z (last) ∈ I}` is contained in `I`. -/
lemma fibre_subset_I_of_subset_strip {p : ℕ} (κ : Set (Fin (p + 1) → ℝ))
    (hκ : κ ⊆ strip p) (l : Fin p → ℝ) : fibre κ l ⊆ I := by
  intro y hy
  have h : Fin.snoc l y ∈ strip p := hκ hy
  simpa [strip] using h

/-! ## The image of a subsingleton fibre, and its end points -/

/-- The image of a subsingleton fibre is a subsingleton. -/
lemma imgFibre_subsingleton_of_fibre_subsingleton {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ)
    (κ : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) (hpt : (fibre κ l).Subsingleton) :
    (imgFibre κ f l).Subsingleton := by
  intro s hs s' hs'
  obtain ⟨y, hy, rfl⟩ := hs
  obtain ⟨y', hy', hyy⟩ := hs'
  rw [hpt hy hy']
  exact hyy

/-- For a point of a subsingleton fibre the lower endpoint of the image is the value of `f`. -/
lemma Aend_eq_of_mem_fibre {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (κ : Set (Fin (p + 1) → ℝ))
    (l : Fin p → ℝ) {x : ℝ} (hx : x ∈ fibre κ l) (hpt : (fibre κ l).Subsingleton) :
    Aend κ f l = f l x := by
  have hsub := imgFibre_subsingleton_of_fibre_subsingleton f κ l hpt
  have hx' : f l x ∈ imgFibre κ f l := ⟨x, hx, rfl⟩
  rw [Aend, hsub.eq_singleton_of_mem hx', csInf_singleton]

/-- For a point of a subsingleton fibre the upper endpoint of the image is the value of `f`. -/
lemma Bend_eq_of_mem_fibre {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (κ : Set (Fin (p + 1) → ℝ))
    (l : Fin p → ℝ) {x : ℝ} (hx : x ∈ fibre κ l) (hpt : (fibre κ l).Subsingleton) :
    Bend κ f l = f l x := by
  have hsub := imgFibre_subsingleton_of_fibre_subsingleton f κ l hpt
  have hx' : f l x ∈ imgFibre κ f l := ⟨x, hx, rfl⟩
  rw [Bend, hsub.eq_singleton_of_mem hx', csSup_singleton]

/-! ## The chart is constant -/

/-- On a nonempty subsingleton fibre the chart is constantly the point of the fibre. -/
lemma chart1_eq_of_mem_fibre {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (κ : Set (Fin (p + 1) → ℝ))
    (l : Fin p → ℝ) {x : ℝ} (hx : x ∈ fibre κ l) (hpt : (fibre κ l).Subsingleton) :
    ∀ t : ℝ, chart1 f κ l t = x := by
  have hA := Aend_eq_of_mem_fibre f κ l hx hpt
  have hB := Bend_eq_of_mem_fibre f κ l hx hpt
  intro t
  rw [chart1]
  split_ifs with h
  · exact hpt (Classical.choose_spec h).1 hx
  · exact absurd ⟨x, hx, by rw [hA, hB]; ring⟩ h

/-- On an empty fibre the chart is constantly the junk value `1/2`. -/
lemma chart1_eq_of_fibre_eq_empty {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ)
    (κ : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) (hempty : fibre κ l = ∅) (t : ℝ) :
    chart1 f κ l t = 1 / 2 := by
  rw [chart1]
  split_ifs with h
  · have hch : Classical.choose h ∈ fibre κ l := (Classical.choose_spec h).1
    rw [hempty] at hch
    simp at hch
  · rfl

/-- A chart attached to a subsingleton fibre does not depend on `t`. -/
lemma chart1_eq_of_subsingleton {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ)
    (κ : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) (hpt : (fibre κ l).Subsingleton)
    (t₁ t₂ : ℝ) : chart1 f κ l t₁ = chart1 f κ l t₂ := by
  by_cases hne : (fibre κ l).Nonempty
  · obtain ⟨x, hx⟩ := hne
    rw [chart1_eq_of_mem_fibre f κ l hx hpt t₁, chart1_eq_of_mem_fibre f κ l hx hpt t₂]
  · rw [chart1_eq_of_fibre_eq_empty f κ l (Set.not_nonempty_iff_eq_empty.mp hne) t₁,
      chart1_eq_of_fibre_eq_empty f κ l (Set.not_nonempty_iff_eq_empty.mp hne) t₂]

/-! ## The three conclusions -/

/-- The chart of a cell inside the strip takes its values in `I`. -/
lemma chart1_mem_I_of_subset_strip {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ)
    (κ : Set (Fin (p + 1) → ℝ)) (hκ : κ ⊆ strip p) (l : Fin p → ℝ) {t : ℝ} (ht : t ∈ I) :
    chart1 f κ l t ∈ I := by
  rw [chart1]
  split_ifs with h
  · exact fibre_subset_I_of_subset_strip κ hκ l (Classical.choose_spec h).1
  · exact ⟨by norm_num, by norm_num⟩

/-- The composite of a family member with a chart of a subsingleton fibre is `C¹` on `I`. -/
lemma contDiffOn_chart1_comp {p : ℕ} (f g : (Fin p → ℝ) → ℝ → ℝ)
    (κ : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) (hpt : (fibre κ l).Subsingleton) :
    ContDiffOn ℝ 1 (fun t : ℝ => g l (chart1 f κ l t)) I := by
  have hEq : (fun t : ℝ => g l (chart1 f κ l t)) = fun _ : ℝ => g l (chart1 f κ l 0) :=
    funext fun t => by rw [chart1_eq_of_subsingleton f κ l hpt t 0]
  rw [hEq]
  exact contDiffOn_const

/-- The derivative of the composite of a family member with a chart of a subsingleton fibre
vanishes. -/
lemma iteratedDeriv_chart1_comp {p : ℕ} (f g : (Fin p → ℝ) → ℝ → ℝ)
    (κ : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) (hpt : (fibre κ l).Subsingleton) (t : ℝ) :
    iteratedDeriv 1 (fun t : ℝ => g l (chart1 f κ l t)) t = 0 := by
  have hEq : (fun t : ℝ => g l (chart1 f κ l t)) = fun _ : ℝ => g l (chart1 f κ l 0) :=
    funext fun t => by rw [chart1_eq_of_subsingleton f κ l hpt t 0]
  rw [hEq, iteratedDeriv_one, deriv_const]

/-- The chart of a subsingleton fibre is surjective onto the fibre, with a preimage in `I`. -/
lemma chart1_surjOn_fibre {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (κ : Set (Fin (p + 1) → ℝ))
    (l : Fin p → ℝ) (hpt : (fibre κ l).Subsingleton) :
    ∀ x ∈ fibre κ l, ∃ t ∈ I, chart1 f κ l t = x :=
  fun x hx => ⟨1 / 2, ⟨by norm_num, by norm_num⟩,
    chart1_eq_of_mem_fibre f κ l hx hpt (1 / 2)⟩

/-! ## The requested statement -/

theorem lipschitz_chart_point (p : ℕ) (f g : (Fin p → ℝ) → ℝ → ℝ) (κ : Set (Fin (p+1) → ℝ))
    (hκ : κ ⊆ Work.WilG4a.strip p) (hpt : ∀ l, (Work.WilG4a.fibre κ l).Subsingleton)
    (hg : ∀ l, ∀ x ∈ Work.WilG4a.I, g l x ∈ Work.WilG4a.I) :
    (∀ l, ∀ t ∈ Work.WilG4a.I, Work.WilG4a.chart1 f κ l t ∈ Work.WilG4a.I) ∧
    (∀ l, ContDiffOn ℝ 1 (fun t : ℝ => g l (Work.WilG4a.chart1 f κ l t)) Work.WilG4a.I ∧
      ∀ t ∈ Work.WilG4a.I, |iteratedDeriv 1 (fun t : ℝ => g l (Work.WilG4a.chart1 f κ l t)) t| ≤ 1) ∧
    (∀ l, ∀ x ∈ Work.WilG4a.fibre κ l, ∃ t ∈ Work.WilG4a.I, Work.WilG4a.chart1 f κ l t = x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro l t ht
    exact chart1_mem_I_of_subset_strip f κ hκ l ht
  · intro l
    exact ⟨contDiffOn_chart1_comp f g κ l (hpt l),
      fun t _ => by rw [iteratedDeriv_chart1_comp f g κ l (hpt l) t]; norm_num⟩
  · intro l
    exact chart1_surjOn_fibre f κ l (hpt l)

end Work.WilG4a
