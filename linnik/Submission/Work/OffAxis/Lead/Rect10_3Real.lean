/-
# OffAxis/Rect10_3Real

**HB (1992) Lemma 10.3 at rectangle height `L`, the case `ρ₁` real.**

`Rect10_3Real` is the complement of `ZeroFreeTables/OffAxis/Rect10_3H` (which handles
`1 < |Im ρ₁|`): the numbered zero `ρ₁` of the height-`L` rectangle numbering is *real*,
`ρ₁.im = 0`.  HB §10 treats this configuration separately from the `F`-method cases, and this
file is the assembly of that treatment, on the quadruple of conditions that make the `F`-method
ledger (10.6) available:

* **(F1)** none of the four signed triple products `χ₁^{±1}χ₂^{±1}χ₃^{±1}` is principal
  (`χ₁χ₂χ₃ ≠ 1`, `χ₁χ₂ ≠ χ₃`, `χ₁χ₃ ≠ χ₂`, `χ₂χ₃ ≠ χ₁`): HB Lemma 10.1 — the ledger (10.6) and
  the numerical endgame.  `Rect10_3RealF1Clean` (the case-1 engine `hb106Real` plus the §10
  endgame `rect10_3_endgame_clean`).
* **(F2)** one of the four products is principal: after conjugating one of the pairs
  `(χ,ρ) ↦ (χ⁻¹, ρ̄)` (which preserves `IsRectMin`, `IsZAt`, all the `λ`'s and the minimality
  hypotheses) this is the case `χ₁χ₂χ₃ = χ₀` of HB Lemma 10.2, and then
  - `χ₁` complex: HB Lemma 10.2 with `ρ₁` real — `Rect10_3RealF2Complex`;
  - `χ₁` real and `χ₂`, `χ₃` real: HB §10 case 3, the all-real `P₃` argument —
    `Rect10_3AllReal`;
  - `χ₁` real and `χ₂`, `χ₃` complex: HB §10 case 3, the `(10.12)`/`β₂` argument —
    `Rect10_3OneRealEngine`.

The conjugation bookkeeping of the last group (the helpers `isZAt_inv_conj`, `lamOf_conj_eq`,
`inv_sq_ne_one`, `inv_eq_imp`, `inv_eq_imp'`, `chi3_sq_ne_one_of`) is carried out here.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.A7.zeroMult_conj_inv
import Submission.Work.OffAxis.Rect10_3RealF1Clean
import Submission.Work.OffAxis.Rect10_3RealF2Complex
import Submission.Work.OffAxis.Rect10_3AllReal
import Submission.Work.OffAxis.Lead.Rect10_3OneRealEngine

namespace Work.OffAxis.Lead

open DirichletCharacter

/-! ## Conjugating a zero pair -/

/-- Replacing a pair `(χ, ρ)` by its conjugate `(χ⁻¹, ρ̄)` preserves `IsZAt`. -/
theorem isZAt_inv_conj {q : ℕ} [NeZero q] {L : ℝ} {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (h : Work.ZeroFreeTables.IsZAt L χ ρ) :
    Work.ZeroFreeTables.IsZAt L χ⁻¹ ((starRingEnd ℂ) ρ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h1
    exact h.1 (inv_eq_one.mp h1)
  · rw [Work.A7.zeroMult_conj_inv χ ρ]
    exact h.2.1
  · rw [Complex.conj_im, abs_neg]
    exact h.2.2

/-- `λ` is invariant under conjugation of the zero. -/
theorem lamOf_conj_eq {q : ℕ} (ρ : ℂ) :
    Work.LinnikContract.lamOf q ((starRingEnd ℂ) ρ) = Work.LinnikContract.lamOf q ρ := by
  simp [Work.LinnikContract.lamOf]

/-- `(χ⁻¹)² ≠ 1` whenever `χ² ≠ 1`. -/
theorem inv_sq_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (h : χ ^ 2 ≠ 1) :
    (χ ⁻¹) ^ 2 ≠ 1 := by
  intro hc
  apply h
  have : (χ ^ 2)⁻¹ = 1 := by rw [← inv_pow, hc]
  exact inv_eq_one.mp this

/-- `χ⁻¹ = ψ` implies `χ = ψ⁻¹`. -/
theorem inv_eq_imp {q : ℕ} [NeZero q] {χ ψ : DirichletCharacter ℂ q} (h : χ⁻¹ = ψ) :
    χ = ψ⁻¹ := by
  simpa using congrArg (fun z : DirichletCharacter ℂ q => z⁻¹) h

/-- `χ⁻¹ = ψ⁻¹` implies `χ = ψ`. -/
theorem inv_eq_imp' {q : ℕ} [NeZero q] {χ ψ : DirichletCharacter ℂ q} (h : χ⁻¹ = ψ⁻¹) :
    χ = ψ := by
  simpa using congrArg (fun z : DirichletCharacter ℂ q => z⁻¹) h

/-- In the configuration `χ₁² = 1`, `χ₂² ≠ 1`, `χ₁χ₂χ₃ = 1` the third character is complex. -/
theorem chi3_sq_ne_one_of {q : ℕ} [NeZero q] {χ₁ χ₂ χ₃ : DirichletCharacter ℂ q}
    (h1 : χ₁ ^ 2 = 1) (h2 : χ₂ ^ 2 ≠ 1) (hP : χ₁ * χ₂ * χ₃ = 1) : χ₃ ^ 2 ≠ 1 := by
  intro hc
  apply h2
  have hP2 : (χ₁ * χ₂ * χ₃) ^ 2 = χ₂ ^ 2 * χ₃ ^ 2 := by
    rw [mul_pow, mul_pow, h1, one_mul]
  have key : χ₂ ^ 2 * χ₃ ^ 2 = 1 := by rw [← hP2, hP, one_pow]
  calc χ₂ ^ 2 = χ₂ ^ 2 * χ₃ ^ 2 * (χ₃ ^ 2)⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
    _ = 1 * (χ₃ ^ 2)⁻¹ := by rw [key]
    _ = 1 := by rw [one_mul, hc, inv_one]

/-! ## The target -/

/-- **HB Lemma 10.3 at rectangle height `L`, `ρ₁` real.**  For every `ε > 0` and every rectangle
height `L ≥ 1` there is `q₀` such that for `q ≥ q₀`: if `ρ₁` is a *real* non-principal zero
(`|Im ρ₁| ≤ L`, `λ₁` minimal over all non-principal zeros of height `≤ 10L`), if `(χ₂,ρ₂)` and
`(χ₃,ρ₃)` are two further conjugate pairs at height `≤ L` realising the successive minima `λ₂`,
`λ₃` of `λ` outside the pairs `{χ₁^{±1}}` and `{χ₁^{±1}, χ₂^{±1}}`, then `λ₃ ≥ 6/7 - ε`. -/
theorem Rect10_3Real : ∀ ε : ℝ, 0 < ε → ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q) (ρ₁ ρ₂ ρ₃ : ℂ), Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ → ρ₁.im = 0 → Work.ZeroFreeTables.IsZAt L χ₂ ρ₂ → Work.ZeroFreeTables.IsZAt L χ₃ ρ₃ → χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₃ ≠ χ₁ → χ₃ ≠ χ₁⁻¹ → χ₃ ≠ χ₂ → χ₃ ≠ χ₂⁻¹ → (∀ (χ : DirichletCharacter ℂ q) (u : ℂ), Work.ZeroFreeTables.IsZAt L χ u → χ ≠ χ₁ → χ ≠ χ₁⁻¹ → Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u) → (∀ (χ : DirichletCharacter ℂ q) (u : ℂ), Work.ZeroFreeTables.IsZAt L χ u → χ ≠ χ₁ → χ ≠ χ₁⁻¹ → χ ≠ χ₂ → χ ≠ χ₂⁻¹ → Work.LinnikContract.lamOf q ρ₃ ≤ Work.LinnikContract.lamOf q u) → Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q ρ₃ → Work.LinnikContract.lamOf q ρ₃ ≤ 6/7 - ε → 6/7 - ε ≤ Work.LinnikContract.lamOf q ρ₃ := by
  intro ε hε L hL
  obtain ⟨q₁, hq₁⟩ := Rect10_3RealF1Clean ε hε L hL
  obtain ⟨q₂, hq₂⟩ := Rect10_3RealF2Complex ε hε L hL
  obtain ⟨q₃, hq₃⟩ := Rect10_3AllReal ε hε L hL
  obtain ⟨q₄, hq₄⟩ := Rect10_3OneRealEngine ε hε L hL
  refine ⟨max (max (max q₁ q₂) q₃) q₄, ?_⟩
  intro q hq _inst χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hm him hZ2 hZ3
    hne21 hne2i hne31 hne3i hne32 hne3ii hmin2 hmin3 hlam23 hlam3
  have hq₁' : q₁ ≤ q := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_left _ _)) hq
  have hq₂' : q₂ ≤ q := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_left _ _)) hq
  have hq₃' : q₃ ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hq₄' : q₄ ≤ q := le_trans (le_max_right _ _) hq
  -- the `F`-method case
  have callF1 : χ₁ * χ₂ * χ₃ ≠ 1 → χ₁ * χ₂ ≠ χ₃ → χ₁ * χ₃ ≠ χ₂ → χ₂ * χ₃ ≠ χ₁ →
      6/7 - ε ≤ Work.LinnikContract.lamOf q ρ₃ := by
    intro a b c d
    exact hq₁ q hq₁' χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hm him hZ2 hZ3 hne21 hne2i hne31 hne3i hne32 hne3ii
      hmin2 hmin3 hlam23 hlam3 a b c d
  -- HB Lemma 10.2 / case 3
  have callF2 : χ₁ * χ₂ * χ₃ = 1 ∨ χ₁ * χ₂ = χ₃ ∨ χ₁ * χ₃ = χ₂ ∨ χ₂ * χ₃ = χ₁ →
      6/7 - ε ≤ Work.LinnikContract.lamOf q ρ₃ := by
    intro hdisj
    by_cases h1sq : χ₁ ^ 2 = 1
    · -- `χ₁` real: HB §10 case 3
      -- the four signed triple products, expressed through `P = χ₁χ₂χ₃`
      have hPmem : χ₁ * χ₂ * χ₃ = 1 ∨ χ₁ * χ₂ * χ₃ = χ₃ ^ 2 ∨
          χ₁ * χ₂ * χ₃ = χ₂ ^ 2 ∨ χ₁ * χ₂ * χ₃ = χ₁ ^ 2 := by
        rcases hdisj with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (by rw [h, pow_two]))
        · exact Or.inr (Or.inr (Or.inl (by
            calc χ₁ * χ₂ * χ₃ = χ₁ * χ₃ * χ₂ := by ac_rfl
              _ = χ₂ * χ₂ := by rw [h]
              _ = χ₂ ^ 2 := (pow_two χ₂).symm)))
        · exact Or.inr (Or.inr (Or.inr (by
            calc χ₁ * χ₂ * χ₃ = χ₁ * (χ₂ * χ₃) := by rw [mul_assoc]
              _ = χ₁ * χ₁ := by rw [h]
              _ = χ₁ ^ 2 := (pow_two χ₁).symm)))
      by_cases h2sq : χ₂ ^ 2 = 1
      · -- all three characters real
        have hP2 : (χ₁ * χ₂ * χ₃) ^ 2 = χ₃ ^ 2 := by
          rw [mul_pow, mul_pow, h1sq, h2sq, one_mul, one_mul]
        have hP' : χ₁ * χ₂ * χ₃ = 1 ∨ χ₁ * χ₂ * χ₃ = χ₃ ^ 2 := by
          rcases hPmem with h | h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact Or.inl (by rw [h, h2sq])
          · exact Or.inl (by rw [h, h1sq])
        have hprod : χ₁ * χ₂ * χ₃ = 1 := by
          rcases hP' with h | h
          · exact h
          · have hhh : (χ₃ ^ 2) ^ 2 = χ₃ ^ 2 := by
              calc (χ₃ ^ 2) ^ 2 = (χ₁ * χ₂ * χ₃) ^ 2 := by rw [h]
                _ = χ₃ ^ 2 := hP2
            have h3sq : χ₃ ^ 2 = 1 := by
              have hc : χ₃ ^ 2 * χ₃ ^ 2 = χ₃ ^ 2 * 1 := by
                rw [mul_one]; simpa [pow_two] using hhh
              exact mul_left_cancel hc
            rw [h, h3sq]
        have h3sq : χ₃ ^ 2 = 1 := by rw [← hP2, hprod, one_pow]
        exact hq₃ q hq₃' χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hm him h1sq h2sq h3sq hprod hZ2 hZ3
          hne21 hne2i hne31 hne3i hne32 hne3ii hmin2 hmin3 hlam23 hlam3
      · -- exactly one character (`χ₁`) is real
        rcases hPmem with hP | hP | hP | hP
        · -- `χ₁χ₂χ₃ = 1`
          have h3sq : χ₃ ^ 2 ≠ 1 := chi3_sq_ne_one_of h1sq h2sq hP
          exact hq₄ q hq₄' χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hm him h1sq h2sq h3sq hP hZ2 hZ3
            hne21 hne2i hne31 hne3i hne32 hne3ii hmin2 hmin3 hlam23 hlam3
        · -- `χ₁χ₂ = χ₃`: conjugate the third pair
          have hχ12 : χ₁ * χ₂ = χ₃ := by
            have h : (χ₁ * χ₂) * χ₃ = χ₃ * χ₃ := by rw [hP, pow_two]
            exact mul_right_cancel h
          have hprod' : χ₁ * χ₂ * χ₃⁻¹ = 1 := by rw [hχ12, mul_inv_cancel]
          have h3sq' : (χ₃⁻¹) ^ 2 ≠ 1 := chi3_sq_ne_one_of h1sq h2sq hprod'
          have hmin2' : ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), Work.ZeroFreeTables.IsZAt L χ u →
              χ ≠ χ₁ → χ ≠ χ₁⁻¹ →
              Work.LinnikContract.lamOf q ((starRingEnd ℂ) ρ₂) ≤ Work.LinnikContract.lamOf q u := by
            intro χ u hu h1 h2
            rw [lamOf_conj_eq ρ₂]
            exact hmin2 χ u hu h1 h2
          have hmin3' : ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), Work.ZeroFreeTables.IsZAt L χ u →
              χ ≠ χ₁ → χ ≠ χ₁⁻¹ → χ ≠ χ₂ → χ ≠ χ₂⁻¹ →
              Work.LinnikContract.lamOf q ((starRingEnd ℂ) ρ₃) ≤ Work.LinnikContract.lamOf q u := by
            intro χ u hu h1 h2 h3 h4
            rw [lamOf_conj_eq ρ₃]
            exact hmin3 χ u hu h1 h2 h3 h4
          have hlam23' : Work.LinnikContract.lamOf q ρ₂ ≤
              Work.LinnikContract.lamOf q ((starRingEnd ℂ) ρ₃) := by
            rw [lamOf_conj_eq ρ₃]; exact hlam23
          have hlam3' : Work.LinnikContract.lamOf q ((starRingEnd ℂ) ρ₃) ≤ 6/7 - ε := by
            rw [lamOf_conj_eq ρ₃]; exact hlam3
          have hres := hq₄ q hq₄' χ₁ χ₂ χ₃⁻¹ ρ₁ ρ₂ ((starRingEnd ℂ) ρ₃)
            hm him h1sq h2sq h3sq' hprod' hZ2 (isZAt_inv_conj hZ3)
            hne21 hne2i
            (fun h => hne3i (inv_eq_imp h))
            (fun h => hne31 (inv_eq_imp' h))
            (fun h => hne3ii (inv_eq_imp h))
            (fun h => hne32 (inv_eq_imp' h))
            hmin2' hmin3' hlam23' hlam3'
          simpa only [lamOf_conj_eq ρ₃] using hres
        · -- `χ₁χ₃ = χ₂`: conjugate the second pair
          have hχ13 : χ₁ * χ₃ = χ₂ := by
            have h : χ₂ * (χ₁ * χ₃) = χ₂ * χ₂ := by rw [← pow_two, ← hP]; ac_rfl
            exact mul_left_cancel h
          have hprod' : χ₁ * χ₂⁻¹ * χ₃ = 1 := by
            calc χ₁ * χ₂⁻¹ * χ₃ = (χ₁ * χ₃) * χ₂⁻¹ := by ac_rfl
              _ = χ₂ * χ₂⁻¹ := by rw [hχ13]
              _ = 1 := mul_inv_cancel χ₂
          have h3sq : χ₃ ^ 2 ≠ 1 := by
            intro hc
            apply h2sq
            calc χ₂ ^ 2 = (χ₁ * χ₃) ^ 2 := by rw [hχ13]
              _ = χ₁ ^ 2 * χ₃ ^ 2 := by rw [mul_pow]
              _ = 1 := by rw [h1sq, hc, one_mul]
          have hmin2' : ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), Work.ZeroFreeTables.IsZAt L χ u →
              χ ≠ χ₁ → χ ≠ χ₁⁻¹ →
              Work.LinnikContract.lamOf q ((starRingEnd ℂ) ρ₂) ≤ Work.LinnikContract.lamOf q u := by
            intro χ u hu h1 h2
            rw [lamOf_conj_eq ρ₂]
            exact hmin2 χ u hu h1 h2
          have hmin3' : ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), Work.ZeroFreeTables.IsZAt L χ u →
              χ ≠ χ₁ → χ ≠ χ₁⁻¹ → χ ≠ χ₂⁻¹ → χ ≠ χ₂⁻¹⁻¹ →
              Work.LinnikContract.lamOf q ρ₃ ≤ Work.LinnikContract.lamOf q u := by
            intro χ u hu h1 h2 h3 h4
            exact hmin3 χ u hu h1 h2 (by simpa using h4) h3
          have hlam23' : Work.LinnikContract.lamOf q ((starRingEnd ℂ) ρ₂) ≤
              Work.LinnikContract.lamOf q ρ₃ := by
            rw [lamOf_conj_eq ρ₂]; exact hlam23
          have hres := hq₄ q hq₄' χ₁ χ₂⁻¹ χ₃ ρ₁ ((starRingEnd ℂ) ρ₂) ρ₃
            hm him h1sq (inv_sq_ne_one h2sq) h3sq hprod' (isZAt_inv_conj hZ2) hZ3
            (fun h => hne2i (inv_eq_imp h))
            (fun h => hne21 (inv_eq_imp' h))
            hne31 hne3i hne3ii (fun h => hne32 (by simpa using h))
            hmin2' hmin3' hlam23' hlam3
          simpa only [lamOf_conj_eq ρ₂] using hres
        · -- `χ₁χ₂χ₃ = χ₁² = 1`
          have hP1 : χ₁ * χ₂ * χ₃ = 1 := by rw [hP, h1sq]
          have h3sq : χ₃ ^ 2 ≠ 1 := chi3_sq_ne_one_of h1sq h2sq hP1
          exact hq₄ q hq₄' χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hm him h1sq h2sq h3sq hP1 hZ2 hZ3
            hne21 hne2i hne31 hne3i hne32 hne3ii hmin2 hmin3 hlam23 hlam3
    · -- `χ₁` complex: HB Lemma 10.2 (with `ρ₁` real)
      exact hq₂ q hq₂' χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hm him h1sq hZ2 hZ3 hne21 hne2i hne31 hne3i hne32
        hne3ii hmin2 hmin3 hlam23 hlam3 hdisj
  by_cases h123 : χ₁ * χ₂ * χ₃ = 1
  · exact callF2 (Or.inl h123)
  · by_cases h12 : χ₁ * χ₂ = χ₃
    · exact callF2 (Or.inr (Or.inl h12))
    · by_cases h13 : χ₁ * χ₃ = χ₂
      · exact callF2 (Or.inr (Or.inr (Or.inl h13)))
      · by_cases h23 : χ₂ * χ₃ = χ₁
        · exact callF2 (Or.inr (Or.inr (Or.inr h23)))
        · exact callF1 (fun h => h123 h) (fun h => h12 h) (fun h => h13 h) (fun h => h23 h)

end Work.OffAxis.Lead
