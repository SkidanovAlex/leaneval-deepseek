import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# One-sided Dini condition implies monotonicity

A continuous function `φ` on `[a,b]` whose *upper right Dini derivative* is non-positive,
in the quantitative form

`∀ t ∈ [a,b), ∀ ε > 0, ∃ δ > 0, ∀ h ∈ (0,δ], φ (t+h) ≤ φ t + ε * h`,

is non-increasing: `φ b ≤ φ a`.

The proof momentarily trades the `ε` for a strict "no ascent" hypothesis: for fixed `ε > 0` the
function `ψ u = φ u - ε * u` satisfies `ψ (t+h) ≤ ψ t` for all small `h > 0`. A continuous
function with that property is non-increasing on `[c,d]` (`no_ascent_le`), obtained by looking at
the closed set `{t ∈ [c,d] : ψ t ≤ ψ c}`: it is nonempty, bounded by `d`, and from every point
strictly below `d` one can move a little to the right staying inside it, whence it contains `d`
(`sSup_mem_of_forall_lt_extend`). Thus `ψ b ≤ ψ a`, i.e. `φ b ≤ φ a + ε * (b - a)`, and letting
`ε → 0` gives the claim (`le_of_forall_pos_le_add_mul`).
-/

namespace Work.Diff.Alg.Pinch

/-- A closed set of reals which is bounded above by `d` and which, from each of its points
strictly below `d`, can be extended a little to the right inside itself, must contain `d`. -/
lemma sSup_mem_of_forall_lt_extend {B : Set ℝ} {d : ℝ}
    (hclosed : IsClosed B) (hne : B.Nonempty) (hbd : ∀ t ∈ B, t ≤ d)
    (hext : ∀ t ∈ B, t < d → ∃ η > 0, Set.Icc t (t + η) ⊆ B) :
    d ∈ B := by
  have hBdd : BddAbove B := ⟨d, hbd⟩
  have hsup : sSup B ∈ B := hclosed.csSup_mem hne hBdd
  have hle : sSup B ≤ d := csSup_le hne hbd
  have hsd : sSup B = d := by
    by_contra hne'
    have hlt : sSup B < d := lt_of_le_of_ne hle hne'
    obtain ⟨η, hη, hsub⟩ := hext (sSup B) hsup hlt
    have hdt : 0 < d - sSup B := sub_pos.mpr hlt
    have hmpos : 0 < min η (d - sSup B) := lt_min hη hdt
    have hmle : min η (d - sSup B) ≤ η := min_le_left _ _
    have hmem : sSup B + min η (d - sSup B) / 2 ∈ B := by
      apply hsub
      exact ⟨by linarith, by linarith⟩
    have h2 : sSup B + min η (d - sSup B) / 2 ≤ sSup B := le_csSup hBdd hmem
    linarith
  rw [← hsd]
  exact hsup

/-- If `x ≤ y + ε * k` for every `ε > 0` and `k ≥ 0`, then `x ≤ y`. -/
lemma le_of_forall_pos_le_add_mul {x y k : ℝ} (hk : 0 ≤ k)
    (h : ∀ ε > 0, x ≤ y + ε * k) : x ≤ y := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hk1 : (0 : ℝ) < k + 1 := by linarith
  have hε' : 0 < ε / (k + 1) := div_pos hε hk1
  have h1 := h (ε / (k + 1)) hε'
  have h2 : ε / (k + 1) * k ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hk1]
    nlinarith
  linarith

/-- The sublevel set of a function continuous on `[c,d]` at the level `f c` is closed. -/
lemma isClosed_setOf_le_of_continuousOn {f : ℝ → ℝ} {c d : ℝ}
    (hcont : ContinuousOn f (Set.Icc c d)) :
    IsClosed {t | t ∈ Set.Icc c d ∧ f t ≤ f c} := by
  have h : IsClosed (Set.Icc c d ∩ f ⁻¹' Set.Iic (f c)) :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  convert h using 1
  ext t
  simp [Set.mem_Icc, Set.mem_Iic]

/-- **Strong one-sided Dini condition.** A continuous function on `[c,d]` which cannot strictly
ascend locally on the right is non-increasing on `[c,d]`. -/
lemma no_ascent_le {ψ : ℝ → ℝ} {c d : ℝ} (hcd : c ≤ d)
    (hcont : ContinuousOn ψ (Set.Icc c d))
    (hna : ∀ t ∈ Set.Ico c d, ∃ δ > 0, ∀ h : ℝ, 0 < h → h ≤ δ → ψ (t + h) ≤ ψ t) :
    ψ d ≤ ψ c := by
  by_contra hcon
  have hcon' : ψ c < ψ d := not_le.mp hcon
  let B : Set ℝ := {t | t ∈ Set.Icc c d ∧ ψ t ≤ ψ c}
  have hBclosed : IsClosed B := by
    show IsClosed {t | t ∈ Set.Icc c d ∧ ψ t ≤ ψ c}
    exact isClosed_setOf_le_of_continuousOn (f := ψ) hcont
  have hBne : B.Nonempty := ⟨c, ⟨⟨le_rfl, hcd⟩, le_rfl⟩⟩
  have hBbd : ∀ t ∈ B, t ≤ d := fun t ht => ht.1.2
  have hext : ∀ t ∈ B, t < d → ∃ η > 0, Set.Icc t (t + η) ⊆ B := by
    intro t ht htd
    obtain ⟨δ, hδ, hδ'⟩ := hna t ⟨ht.1.1, htd⟩
    refine ⟨min δ (d - t) / 2, ?_, ?_⟩
    · have : 0 < min δ (d - t) := lt_min hδ (sub_pos.mpr htd)
      linarith
    · intro s hs
      have hs1 : t ≤ s := hs.1
      have hs2 : s ≤ t + min δ (d - t) / 2 := hs.2
      have hdt : min δ (d - t) / 2 < d - t := by
        have := min_le_right δ (d - t); linarith
      have hδle : min δ (d - t) / 2 ≤ δ := by
        have := min_le_left δ (d - t); linarith
      refine ⟨⟨le_trans ht.1.1 hs1, by linarith⟩, ?_⟩
      rcases eq_or_lt_of_le hs1 with heq | hlt
      · rw [← heq]; exact ht.2
      · have hpos : 0 < s - t := sub_pos.mpr hlt
        have hδ2 : s - t ≤ δ := by linarith
        have h := hδ' (s - t) hpos hδ2
        have heq2 : t + (s - t) = s := by ring
        rw [heq2] at h
        exact le_trans h ht.2
  have hd : d ∈ B := sSup_mem_of_forall_lt_extend hBclosed hBne hBbd hext
  have : ψ d ≤ ψ c := hd.2
  linarith

theorem le_of_dini_right (φ : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn φ (Set.Icc a b))
    (hD : ∀ t ∈ Set.Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, 0 < h → h ≤ δ → φ (t + h) ≤ φ t + ε * h) :
    φ b ≤ φ a := by
  have key : ∀ ε > 0, φ b ≤ φ a + ε * (b - a) := by
    intro ε hε
    have hna : ∀ t ∈ Set.Ico a b, ∃ δ > 0, ∀ h : ℝ, 0 < h → h ≤ δ →
        φ (t + h) - ε * (t + h) ≤ φ t - ε * t := by
      intro t ht
      obtain ⟨δ, hδ, hδ'⟩ := hD t ht ε hε
      exact ⟨δ, hδ, fun h hh hle => by
        have h' := hδ' h hh hle
        nlinarith [h']⟩
    have hcont' : ContinuousOn (fun u => φ u - ε * u) (Set.Icc a b) :=
      hcont.sub ((continuous_const.mul continuous_id).continuousOn)
    have hres := no_ascent_le hab hcont' hna
    have hres' : φ b - ε * b ≤ φ a - ε * a := hres
    linarith
  exact le_of_forall_pos_le_add_mul (sub_nonneg.mpr hab) key

end Work.Diff.Alg.Pinch
