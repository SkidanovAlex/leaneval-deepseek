/-
# ZeroFreeTables/OffAxis — `RectC_Lam3`

The `λ₃ ≥ 0.856` clause of `Z3` at rectangle height `L`: for the height-`L` numbering
`IsRectMin L χ₁ ρ₁` of an *off-axis* pair (`1 < |Im ρ₁|`), all working-region zeros outside
at most two conjugate pairs have `λ ≥ 0.856`.

Recipe (as requested): HB Table 9 (Lemma 9.2, for complex `χ₁`) and HB Lemma 10.3 (the
`λ₃ ≥ 6/7 - ε` conclusion), run at rectangle height `L`; the height-free rational
certificates of `P9F/table9_top.lean` / `HBTable9_proof.lean` and the on-axis engine
`HBLemma10_3_engine_proof.lean` are the corresponding on-axis inputs.

The reduction carried out here is the *selection* argument of HB §6/§9: `Lam3Bound χ₁ c`
asks for a single witness character `χ₂` such that every working-region zero of a character
outside the two conjugate pairs `{χ₁^{±1}}, {χ₂^{±1}}` has `λ ≥ c`.  Given `λ₁` and the
rectangle minimality of `ρ₁`:

* if no working-region zero of a character outside `{χ₁^{±1}}` has `λ < 0.856`, the witness
  is `χ₂ := χ₁`;
* otherwise one takes for `χ₂` a zero pair realising the *minimum* of `λ` outside `{χ₁^{±1}}`
  (which exists, the candidate set being finite: `exists_min_lam_avoiding`), and any further
  pair outside `{χ₁^{±1}, χ₂^{±1}}` with `λ < 0.856` would give three conjugate pairs whose
  `λ`'s are the successive minima `λ₁ ≤ λ₂ ≤ λ₃ ≤ 6/7 - 1/1000`, contradicting HB Lemma 10.3
  at rectangle height `L` (`OffAxis/RectHB10_3`, the one analytic input).

Because the numbered zero is off-axis (`1 < |Im ρ₁|`, hence `ρ₁` complex), HB's §10 case analysis
never reaches case 3 (all characters real, `ρ₁` real), i.e. the `P₃`-based engine; the two
remaining configurations of §10 (Lemma 10.1: no signed triple is principal; Lemma 10.2:
`χ₁χ₂χ₃ = χ₀`, cf. `HB10_3_Fcases`) are the `F`-method cases, and their numerical core is
HB (10.7)/(10.8) — see `OffAxis/G72_ten_eight`.

The `λ₃`-minimising pair `(χ₃',ρ₃')` is taken *outside both* pairs, and the two orderings
`λ₂ ≤ λ₃'` and `λ₃' ≤ λ₂` are both fed to HB Lemma 10.3 (the lemma is symmetric in the last two
pairs up to that ordering), so no extra hypothesis on the order in which the pairs are given is
needed.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.ZeroFreeTables.OffAxis.RectHB10_3
import Submission.Work.ZeroFreeTables.OffAxis.exists_min_lam_avoiding

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.OffAxis

open Work.LinnikContract

/-- The rectangle minimality of `IsRectMin L χ₁ ρ₁` (`L ≥ 1`) covers the whole working region:
every zero with `|Im| ≤ 1` has `λ ≥ λ₁`. -/
theorem lam_of_isZ_ge {q : ℕ} [NeZero q] {L : ℝ} (hL : 1 ≤ L) {χ₁ : DirichletCharacter ℂ q}
    {ρ₁ : ℂ} (hm : Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁)
    {χ : DirichletCharacter ℂ q} {ρ : ℂ} (hZ : IsZ χ ρ) : lamOf q ρ₁ ≤ lamOf q ρ :=
  hm.2 χ ρ ⟨hZ.1, hZ.2.1, hZ.2.2.trans (by linarith)⟩

/-- The `λ₃ ≥ 0.856` clause of `Z3` at rectangle height `L`. -/
theorem RectC_Lam3 : ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ → 1 < |ρ₁.im| →
      Work.LinnikContract.Lam3Bound χ₁ 0.856 := by
  intro L hL
  -- HB Lemma 10.3 at rectangle height `L`, with the contract's margin `1/1000`.
  obtain ⟨q₀, hq₀⟩ := RectHB10_3 (1/1000) (by norm_num) L hL
  refine ⟨q₀, fun q hq _inst χ₁ ρ₁ hm him => ?_⟩
  classical
  suffices hmain : ∃ χ₂ : DirichletCharacter ℂ q, ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ),
      IsZ χ ρ → χ ≠ χ₁ → χ ≠ χ₁⁻¹ → χ ≠ χ₂ → χ ≠ χ₂⁻¹ →
        (856 : ℝ)/1000 ≤ lamOf q ρ by
    obtain ⟨χ₂, hχ₂⟩ := hmain
    exact ⟨χ₂, fun χ ρ hZ h1 h2 h3 h4 =>
      by simpa only [show (0.856 : ℝ) = (856 : ℝ)/1000 by norm_num]
        using hχ₂ χ ρ hZ h1 h2 h3 h4⟩
  by_cases hex : ∃ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ ∧ χ ≠ χ₁ ∧
      χ ≠ χ₁⁻¹ ∧ lamOf q ρ < (856 : ℝ)/1000
  · -- a second pair with `λ < 0.856` exists: take `(χ₂, ρ₂)` minimal among all such pairs
    obtain ⟨χ₂, ρ₂, hZ₂, hS₂, hmin₂⟩ := exists_min_lam_avoiding
      ({χ₁, χ₁⁻¹} : Set (DirichletCharacter ℂ q))
      (by obtain ⟨χa, ρa, hZa, hχa1, hχa2, -⟩ := hex
          exact ⟨χa, ρa, hZa, by simp [hχa1, hχa2]⟩)
    have hχ₂1 : χ₂ ≠ χ₁ := fun hh => hS₂ (by simp [hh])
    have hχ₂2 : χ₂ ≠ χ₁⁻¹ := fun hh => hS₂ (by simp [hh])
    have hlam2 : lamOf q ρ₂ < (856 : ℝ)/1000 := by
      obtain ⟨χa, ρa, hZa, hχa1, hχa2, hlama⟩ := hex
      exact lt_of_le_of_lt (hmin₂ χa ρa hZa (by simp [hχa1, hχa2])) hlama
    refine ⟨χ₂, fun χ₃ ρ₃ hZ₃ h31 h32 h33 h34 => ?_⟩
    by_contra hcon
    rw [not_le] at hcon
    -- the pair realising the minimum of `λ` outside *both* pairs
    obtain ⟨χ₃', ρ₃', hZ₃', hS₃', hmin₃⟩ := exists_min_lam_avoiding
      (({χ₁, χ₁⁻¹} : Set (DirichletCharacter ℂ q)) ∪
        ({χ₂, χ₂⁻¹} : Set (DirichletCharacter ℂ q)))
      ⟨χ₃, ρ₃, hZ₃, by simp [h31, h32, h33, h34]⟩
    have hχ₃'1 : χ₃' ≠ χ₁ := fun hh => hS₃' (by simp [hh])
    have hχ₃'2 : χ₃' ≠ χ₁⁻¹ := fun hh => hS₃' (by simp [hh])
    have hχ₃'3 : χ₃' ≠ χ₂ := fun hh => hS₃' (by simp [hh])
    have hχ₃'4 : χ₃' ≠ χ₂⁻¹ := fun hh => hS₃' (by simp [hh])
    have hlam3' : lamOf q ρ₃' < (856 : ℝ)/1000 :=
      lt_of_le_of_lt (hmin₃ χ₃ ρ₃ hZ₃ (by simp [h31, h32, h33, h34])) hcon
    have hconst : (856 : ℝ)/1000 < 6/7 - (1/1000 : ℝ) := by norm_num
    -- HB Lemma 10.3 in the ordering `λ₂ ≤ λ₃'`, resp. in the swapped ordering `λ₃' ≤ λ₂`
    rcases le_total (lamOf q ρ₂) (lamOf q ρ₃') with hle | hle
    · have h := hq₀ q hq χ₁ χ₂ χ₃' ρ₁ ρ₂ ρ₃' hm him hZ₂ hZ₃' hχ₂1 hχ₂2
        hχ₃'1 hχ₃'2 hχ₃'3 hχ₃'4
        (fun χ u hZu h1 h2 => hmin₂ χ u hZu (by simp [h1, h2]))
        (fun χ u hZu h1 h2 h3 h4 => hmin₃ χ u hZu (by simp [h1, h2, h3, h4]))
        hle (by linarith)
      linarith
    · have hle' : lamOf q ρ₃' ≤ lamOf q ρ₂ := hle
      have h := hq₀ q hq χ₁ χ₃' χ₂ ρ₁ ρ₃' ρ₂ hm him hZ₃' hZ₂ hχ₃'1 hχ₃'2
        hχ₂1 hχ₂2 (Ne.symm hχ₃'3) (fun hh => hχ₃'4 (by rw [hh, inv_inv]))
        (fun χ u hZu h1 h2 => by
          by_cases hc : χ = χ₂ ∨ χ = χ₂⁻¹
          · rcases hc with hc | hc
            · exact le_trans hle' (hmin₂ χ u hZu (by simp [h1, h2]))
            · exact le_trans hle' (hmin₂ χ u hZu (by simp [h1, h2]))
          · push Not at hc
            exact hmin₃ χ u hZu (by simp [h1, h2, hc.1, hc.2]))
        (fun χ u hZu h1 h2 _ _ => hmin₂ χ u hZu (by simp [h1, h2]))
        hle' (by linarith)
      linarith
  · -- no second pair with `λ < 0.856`: the witness is `χ₂ := χ₁`
    push Not at hex
    exact ⟨χ₁, fun χ ρ hZ h1 h2 _ _ => hex χ ρ hZ h1 h2⟩

end Work.ZeroFreeTables.OffAxis
