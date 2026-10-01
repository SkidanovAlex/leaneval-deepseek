/-
# OffAxis/Lead/RectLam3Parts

The pieces of `Work.ZeroFreeTables.OffAxis.RectLam3` (HB Lemma 10.3, `λ₃ ≥ 856/1000`, at
rectangle height `L`, for the `IsRectStrip L` numbering) that do **not** depend on the
`ρ₁`-real branch of the near-case engine:

* `lam3BoundH_mono` — `Lam3BoundH` is antitone in the constant;
* `isRectMin_of_isRectStrip` — the strip numbering upgrades to the rectangle numbering
  (`WideDefs.isMinWideAt_of_isRectStrip`) when `λ₁ ≤ 2`;
* `rect10_3FarF2` — the `F2` (principal-triple) case of HB §10 for `1 < |Im ρ₁|`, obtained as a
  special case of the near engine `OffAxis/Lead/Rect10_3NearF2`;
* `rect10_3H_of_cases` — HB Lemma 10.3 at height `L` for an off-axis minimiser (`1 < |Im ρ₁|`,
  `λ₁ ≥ 348/1000`), from `Rect10_3H_F1` (HB Lemma 10.1) and `rect10_3FarF2` (HB Lemma 10.2);
* `Rect10_3NearStmt` and `rectLam3_of_near` — the §6 selection argument that turns the
  near-case engine into `Lam3BoundH L χ₁ (856/1000)`, with the engine passed as a hypothesis so
  that the selection argument can be checked independently of the analytic engines.

The final theorem `RectLam3` (`ZeroFreeTables/OffAxis/RectLam3.lean`) is then
`rectLam3_of_near` applied to `Work.OffAxis.Lead.Rect10_3Near`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.ZeroFreeTables.OffAxis.WideDefs
import Submission.Work.ZeroFreeTables.OffAxis.Rect10_3H_F1
import Submission.Work.OffAxis.Lead.ExistsMinLamH
import Submission.Work.OffAxis.Lead.Rect10_3NearF2

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.OffAxis.Lead

open Work.LinnikContract

/-- `Lam3BoundH` is antitone in the constant. -/
theorem lam3BoundH_mono {q : ℕ} [NeZero q] {L c c' : ℝ} {χ₁ : DirichletCharacter ℂ q}
    (h : Work.ZeroFreeTables.Lam3BoundH L χ₁ c) (hc : c' ≤ c) :
    Work.ZeroFreeTables.Lam3BoundH L χ₁ c' := by
  obtain ⟨χ₂, hχ₂⟩ := h
  exact ⟨χ₂, fun χ ρ hZ h1 h2 h3 h4 => hc.trans (hχ₂ χ ρ hZ h1 h2 h3 h4)⟩

/-- `IsRectStrip L` upgrades to the rectangle numbering `IsRectMin L` when `λ₁ ≤ 2`
(below height `L` by the strip minimality, in `(L, 10L]` by the zero-free strip). -/
theorem isRectMin_of_isRectStrip {q : ℕ} [NeZero q] {L : ℝ}
    {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} (hR : Work.ZeroFreeTables.IsRectStrip L χ₁ ρ₁)
    (hlam : lamOf q ρ₁ ≤ 2) : Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ := by
  have hmin := isMinWideAt_of_isRectStrip hR hlam
  exact ⟨⟨hmin.1, hmin.2.1, hmin.2.2.1⟩,
    fun χ u hu => hmin.2.2.2 χ u hu.1 hu.2.1 hu.2.2⟩

/-- **The `F2` case of HB §10 at height `L` is a special case of the near engine**
(`OffAxis/Lead/Rect10_3NearF2`, which assumes only `Im ρ₁ ≠ 0`): if `λ₃ > 6/7 - ε` there is
nothing to prove, and otherwise the near engine applies. -/
theorem rect10_3FarF2 : ∀ ε : ℝ, 0 < ε → ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q) (ρ₁ ρ₂ ρ₃ : ℂ),
    Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ → 1 < |ρ₁.im| →
    Work.ZeroFreeTables.IsZAt L χ₂ ρ₂ → Work.ZeroFreeTables.IsZAt L χ₃ ρ₃ →
    χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₃ ≠ χ₁ → χ₃ ≠ χ₁⁻¹ → χ₃ ≠ χ₂ → χ₃ ≠ χ₂⁻¹ →
    Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q ρ₃ →
    Work.LinnikContract.lamOf q ρ₃ ≤ 6/7 →
    (χ₁ * χ₂ * χ₃ = 1 ∨ χ₁ * χ₂ = χ₃ ∨ χ₁ * χ₃ = χ₂ ∨ χ₂ * χ₃ = χ₁) →
    6/7 - ε ≤ Work.LinnikContract.lamOf q ρ₃ := by
  intro ε hε L hL
  obtain ⟨q₀, hq₀⟩ := Work.OffAxis.Lead.Rect10_3NearF2 ε hε L hL
  refine ⟨q₀, fun q hq _inst χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hR him hZ₂ hZ₃ h21 h2i h31 h3i h32 h3ii
    hlam23 hlam3 hprod => ?_⟩
  have him0 : ρ₁.im ≠ 0 := abs_pos.mp (by linarith)
  by_cases hle : Work.LinnikContract.lamOf q ρ₃ ≤ 6/7 - ε
  · exact hq₀ q hq χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hR him0 hZ₂ hZ₃ h21 h2i h31 h3i h32 h3ii
      hlam23 hle hprod
  · push_neg at hle
    linarith

/-- **HB Lemma 10.3 at rectangle height `L` for an off-axis minimiser** (`1 < |ρ₁.im|`),
assembled from the two case lemmas `Rect10_3H_F1` (no signed triple product is principal,
HB Lemma 10.1) and `rect10_3FarF2` (`χ₁χ₂χ₃ = χ₀` up to products, HB Lemma 10.2). -/
theorem rect10_3H_of_cases : ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ → 1 < |ρ₁.im| →
      (348 : ℝ)/1000 ≤ lamOf q ρ₁ →
      Work.ZeroFreeTables.Lam3BoundH L χ₁ (6/7 - 1/1000) := by
  intro L hL
  have hL10 : L ≤ 10 * L := by linarith
  obtain ⟨q₁, hq₁⟩ := Work.ZeroFreeTables.OffAxis.Rect10_3H_F1 (1/1000) (by norm_num) L hL
  obtain ⟨q₂, hq₂⟩ := rect10_3FarF2 (1/1000) (by norm_num) L hL
  refine ⟨max q₁ q₂, fun q hq _inst χ₁ ρ₁ hm him _h348 => ?_⟩
  have hq₁' : q₁ ≤ q := le_trans (le_max_left _ _) hq
  have hq₂' : q₂ ≤ q := le_trans (le_max_right _ _) hq
  have hmono : ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), Work.ZeroFreeTables.IsZAt L χ u →
      lamOf q ρ₁ ≤ lamOf q u :=
    fun χ u hu => hm.2 χ u (Work.ZeroFreeTables.isZAt_mono hL10 hu)
  classical
  by_cases hge : (6/7 - 1/1000 : ℝ) ≤ lamOf q ρ₁
  · exact ⟨χ₁, fun χ ρ hZ _ _ _ _ => hge.trans (hmono χ ρ hZ)⟩
  · push Not at hge
    by_cases hex : ∃ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.ZeroFreeTables.IsZAt L χ ρ ∧
        χ ≠ χ₁ ∧ χ ≠ χ₁⁻¹ ∧ lamOf q ρ < (6/7 - 1/1000 : ℝ)
    · obtain ⟨χ₂, ρ₂, hZ₂, hout₂, hmin₂⟩ :=
        Work.ZeroFreeTables.OffAxis.Lead.exists_min_lam_avoiding_H L
          ({χ₁, χ₁⁻¹} : Set (DirichletCharacter ℂ q))
          (by obtain ⟨χa, ρa, hZa, hχa1, hχa2, -⟩ := hex
              exact ⟨χa, ρa, hZa, by simp [hχa1, hχa2]⟩)
      have hchi21 : χ₂ ≠ χ₁ := fun h => hout₂ (by simp [h])
      have hchi22 : χ₂ ≠ χ₁⁻¹ := fun h => hout₂ (by simp [h])
      have hlam2lt : lamOf q ρ₂ < (6/7 - 1/1000 : ℝ) := by
        obtain ⟨χa, ρa, hZa, hχa1, hχa2, hlama⟩ := hex
        exact lt_of_le_of_lt (hmin₂ χa ρa hZa (by simp [hχa1, hχa2])) hlama
      refine ⟨χ₂, fun χ₃ ρ₃ hZ₃ h31 h32 h33 h34 => ?_⟩
      by_contra hcon
      rw [not_le] at hcon
      obtain ⟨χ₃', ρ₃', hZ₃', hout₃', hmin₃⟩ :=
        Work.ZeroFreeTables.OffAxis.Lead.exists_min_lam_avoiding_H L
          (({χ₁, χ₁⁻¹} : Set (DirichletCharacter ℂ q)) ∪ {χ₂, χ₂⁻¹})
          ⟨χ₃, ρ₃, hZ₃, by simp [h31, h32, h33, h34]⟩
      have hchi31 : χ₃' ≠ χ₁ := fun h => hout₃' (by simp [h])
      have hchi32 : χ₃' ≠ χ₁⁻¹ := fun h => hout₃' (by simp [h])
      have hchi33 : χ₃' ≠ χ₂ := fun h => hout₃' (by simp [h])
      have hchi34 : χ₃' ≠ χ₂⁻¹ := fun h => hout₃' (by simp [h])
      have hlam3lt : lamOf q ρ₃' < (6/7 - 1/1000 : ℝ) :=
        lt_of_le_of_lt (hmin₃ χ₃ ρ₃ hZ₃ (by simp [h31, h32, h33, h34])) hcon
      have hle23 : lamOf q ρ₂ ≤ lamOf q ρ₃' :=
        hmin₂ χ₃' ρ₃' hZ₃' (by simp [hchi31, hchi32])
      have hle67 : lamOf q ρ₃' ≤ 6/7 := by linarith
      have hcontr : (6/7 - 1/1000 : ℝ) ≤ lamOf q ρ₃' := by
        by_cases hcase : χ₁ * χ₂ * χ₃' = 1 ∨ χ₁ * χ₂ = χ₃' ∨ χ₁ * χ₃' = χ₂ ∨ χ₂ * χ₃' = χ₁
        · exact hq₂ q hq₂' χ₁ χ₂ χ₃' ρ₁ ρ₂ ρ₃' hm him hZ₂ hZ₃' hchi21 hchi22
            hchi31 hchi32 hchi33 hchi34 hle23 hle67 hcase
        · push Not at hcase
          exact hq₁ q hq₁' χ₁ χ₂ χ₃' ρ₁ ρ₂ ρ₃' hm him hZ₂ hZ₃' hchi21 hchi22
            hchi31 hchi32 hchi33 hchi34 hle23 hle67
            hcase.1 hcase.2.1 hcase.2.2.1 hcase.2.2.2
      linarith
    · push Not at hex
      refine ⟨χ₁, fun χ ρ hZ h1 h2 _ _ => hex χ ρ hZ h1 h2⟩

/-- The statement of the near-case HB Lemma 10.3 engine (`OffAxis/Lead/Rect10_3Near`): the
contradiction form of HB's Lemma 10.3 in the configuration `|Im ρ₁| ≤ 1 ∨ λ₁ ≤ 348/1000`, with
`ρ₂` and `ρ₃` the successive `λ`-minima over the pairs outside `{χ₁^{±1}}` and
`{χ₁^{±1}, χ₂^{±1}}`.  It is kept as a `Prop` so that the final assembly `rectLam3_of_near` can
be checked without unfolding the engine's statement. -/
def Rect10_3NearStmt : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q) (ρ₁ ρ₂ ρ₃ : ℂ),
    Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ →
    Work.ZeroFreeTables.IsZAt L χ₂ ρ₂ → Work.ZeroFreeTables.IsZAt L χ₃ ρ₃ →
    χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₃ ≠ χ₁ → χ₃ ≠ χ₁⁻¹ → χ₃ ≠ χ₂ → χ₃ ≠ χ₂⁻¹ →
    (∀ (χ : DirichletCharacter ℂ q) (u : ℂ), Work.ZeroFreeTables.IsZAt L χ u →
      χ ≠ χ₁ → χ ≠ χ₁⁻¹ → Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u) →
    (∀ (χ : DirichletCharacter ℂ q) (u : ℂ), Work.ZeroFreeTables.IsZAt L χ u →
      χ ≠ χ₁ → χ ≠ χ₁⁻¹ → χ ≠ χ₂ → χ ≠ χ₂⁻¹ →
        Work.LinnikContract.lamOf q ρ₃ ≤ Work.LinnikContract.lamOf q u) →
    Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q ρ₃ →
    Work.LinnikContract.lamOf q ρ₃ ≤ 6/7 - ε →
    (|ρ₁.im| ≤ 1 ∨ Work.LinnikContract.lamOf q ρ₁ ≤ 348/1000) →
    6/7 - ε ≤ Work.LinnikContract.lamOf q ρ₃

/-- **HB Lemma 10.3 at rectangle height `L` (`λ₃ ≥ 856/1000`)**, from the near-case engine and
the off-axis case: the §6 selection argument.  If `λ₁ ≥ 856/1000` the witness is `χ₁`; if there
is no zero of `λ < 856/1000` outside `{χ₁^{±1}}` the witness is `χ₁` again; otherwise `χ₂`
realises the minimum of `λ` outside `{χ₁^{±1}}`, and any further pair outside
`{χ₁^{±1}, χ₂^{±1}}` with `λ < 856/1000` would give three conjugate pairs whose `λ`'s are
successive minima — contradicting HB Lemma 10.3 at height `L` in the near configuration
(`Rect10_3NearStmt`) or, when `1 < |Im ρ₁|` and `λ₁ ≥ 348/1000`, the off-axis case
`rect10_3H_of_cases`. -/
theorem rectLam3_of_near (hNear : Rect10_3NearStmt) : ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    Work.ZeroFreeTables.IsRectStrip L χ₁ ρ₁ →
    Work.ZeroFreeTables.Lam3BoundH L χ₁ (856/1000) := by
  intro L hL
  obtain ⟨q₁, hq₁⟩ := rect10_3H_of_cases L hL
  obtain ⟨q₂, hq₂⟩ := hNear (1/1000) (by norm_num) L hL
  refine ⟨max q₁ q₂, fun q hq _inst χ₁ ρ₁ hR => ?_⟩
  have hq₁' : q₁ ≤ q := le_trans (le_max_left _ _) hq
  have hq₂' : q₂ ≤ q := le_trans (le_max_right _ _) hq
  by_cases hbig : (856 : ℝ)/1000 ≤ lamOf q ρ₁
  · -- the numbered zero itself is above the threshold: witness `χ₂ := χ₁`
    exact ⟨χ₁, fun χ ρ hZ _ _ _ _ => hbig.trans (hR.2.1 χ ρ hZ)⟩
  · push_neg at hbig
    have hRmin : Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ :=
      isRectMin_of_isRectStrip hR (by linarith)
    by_cases hnear : (|ρ₁.im| ≤ 1 ∨ lamOf q ρ₁ ≤ 348/1000)
    · -- the near-case engine (contradiction form): the selection argument
      classical
      by_cases hex : ∃ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.ZeroFreeTables.IsZAt L χ ρ ∧
          χ ≠ χ₁ ∧ χ ≠ χ₁⁻¹ ∧ lamOf q ρ < (856 : ℝ)/1000
      · obtain ⟨χ₂, ρ₂, hZ₂, hout₂, hmin₂⟩ :=
          exists_min_lam_avoiding_H L ({χ₁, χ₁⁻¹} : Set (DirichletCharacter ℂ q))
            (by obtain ⟨χa, ρa, hZa, hχa1, hχa2, -⟩ := hex
                exact ⟨χa, ρa, hZa, by simp [hχa1, hχa2]⟩)
        have hχ₂1 : χ₂ ≠ χ₁ := fun h => hout₂ (by simp [h])
        have hχ₂2 : χ₂ ≠ χ₁⁻¹ := fun h => hout₂ (by simp [h])
        have hlam2 : lamOf q ρ₂ < (856 : ℝ)/1000 := by
          obtain ⟨χa, ρa, hZa, hχa1, hχa2, hlama⟩ := hex
          exact lt_of_le_of_lt (hmin₂ χa ρa hZa (by simp [hχa1, hχa2])) hlama
        refine ⟨χ₂, fun χ₃ ρ₃ hZ₃ h31 h32 h33 h34 => ?_⟩
        by_contra hcon
        rw [not_le] at hcon
        obtain ⟨χ₃', ρ₃', hZ₃', hout₃', hmin₃⟩ :=
          exists_min_lam_avoiding_H L
            (({χ₁, χ₁⁻¹} : Set (DirichletCharacter ℂ q)) ∪
              ({χ₂, χ₂⁻¹} : Set (DirichletCharacter ℂ q)))
            ⟨χ₃, ρ₃, hZ₃, by simp [h31, h32, h33, h34]⟩
        have hχ₃'1 : χ₃' ≠ χ₁ := fun h => hout₃' (by simp [h])
        have hχ₃'2 : χ₃' ≠ χ₁⁻¹ := fun h => hout₃' (by simp [h])
        have hχ₃'3 : χ₃' ≠ χ₂ := fun h => hout₃' (by simp [h])
        have hχ₃'4 : χ₃' ≠ χ₂⁻¹ := fun h => hout₃' (by simp [h])
        have hlam3' : lamOf q ρ₃' < (856 : ℝ)/1000 :=
          lt_of_le_of_lt (hmin₃ χ₃ ρ₃ hZ₃ (by simp [h31, h32, h33, h34])) hcon
        have hle23 : lamOf q ρ₂ ≤ lamOf q ρ₃' :=
          hmin₂ χ₃' ρ₃' hZ₃' (by simp [hχ₃'1, hχ₃'2])
        have hkey : (6/7 - (1/1000 : ℝ)) ≤ lamOf q ρ₃' :=
          hq₂ q hq₂' χ₁ χ₂ χ₃' ρ₁ ρ₂ ρ₃' hRmin hZ₂ hZ₃'
            hχ₂1 hχ₂2 hχ₃'1 hχ₃'2 hχ₃'3 hχ₃'4
            (fun χ u hZu h1 h2 => hmin₂ χ u hZu (by simp [h1, h2]))
            (fun χ u hZu h1 h2 h3 h4 => hmin₃ χ u hZu (by simp [h1, h2, h3, h4]))
            hle23 (by linarith) hnear
        linarith
      · push_neg at hex
        exact ⟨χ₁, fun χ ρ hZ h1 h2 _ _ => hex χ ρ hZ h1 h2⟩
    · -- the off-axis, large-`λ₁` case: HB Lemma 10.3 for an off-axis minimiser
      push_neg at hnear
      exact lam3BoundH_mono (hq₁ q hq₁' χ₁ ρ₁ hRmin hnear.1 (le_of_lt hnear.2)) (by norm_num)

end Work.ZeroFreeTables.OffAxis.Lead
