import Mathlib
import Submission.Work.ZeroFreeTables.HB94.hbLemma6_2_engine_wide
import Submission.Work.ZeroFreeTables.HB94.hbLemma6_2_engine_restricted
import Submission.Work.ZeroFreeTables.HB94.Lam2Ge
import Submission.Work.ZeroFreeTables.exists_min_other_wide
import Submission.Work.ZeroFreeTables.HB95plus.Main
import Submission.Work.ZeroFreeTables.HB95plus.tf72_numeric_inputs
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi

open DirichletCharacter Complex
open Work.LinnikContract
open scoped Classical BigOperators
open MeasureTheory

noncomputable section

namespace Work.ZeroFreeTables.HB94

open Work.ZeroFreeTables

/-- **The second-minimum bound `λ₂ ≥ λ₁ + 0.472` at the wide height `|Im u| ≤ 8`.**  For
`λ₁ ≤ 0.348`, every zero `u` (of non-zero multiplicity) of a character `χ ∉ {1, χ₁, χ₁⁻¹}` with
`|Im u| ≤ 8` satisfies `λ(u) ≥ λ₁ + 472/1000`.  Proof: take the `λ`-minimal such pair `(χ₂,ρ₂)`
(`Work.ZeroFreeTables.exists_min_other_wide` at `H = 8`, with `(χ,u)` itself as witness); if
`λ₂ > 1` the claim is immediate from `λ(u) ≥ λ₂`, otherwise run the HB Lemma 6.2 engine with
`T = tf72T (17/20)`, `c = 1/6`, `ε = 1/1000` — the engine's `IsZ χ₂ ρ₂` may be relaxed to
`zeroMult χ₂ ρ₂ ≠ 0`, `χ₂ ≠ 1`, `|ρ₂.im| ≤ 8` (in `hbLemma6_2_engine_restricted`'s proof `|γ₂| ≤ 1`
is used only to bound window heights by `≤ 10`, which `|γ₂| ≤ 8` and `δ < 1` also give), so copy
that file as a local lemma — giving
`F(λ₂-λ₁) ≤ La(λ₁) - 8/9 + (68/75)(1/2+3ε) ≤ F(0.472)` by `Work.ZeroFreeTables.lam2_arith` and
`TfNumericInputs` (the true values are `La(0.348) = 1.11019` and `F(0.472) = 0.68147`, so the
`(68/75)·3ε` vs `(68/75)·4ε` slack is immaterial); `le_of_F_lt_of_le_F` then yields
`λ₂ ≥ λ₁ + 0.472`, whence `λ(u) ≥ λ₂ ≥ λ₁ + 0.472`. -/
theorem Lam2GeWide (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (q₁ : ℕ)
    (hL52 : ∀ q : ℕ, q₁ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/6) (1/1000) δ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ →
      Work.LinnikContract.lamOf q ρ₁ ≤ (348:ℝ)/1000 →
      ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), Work.LinnikContract.zeroMult χ u ≠ 0 →
        χ ≠ 1 → χ ≠ χ₁ → χ ≠ χ₁⁻¹ → |u.im| ≤ 8 →
          Work.LinnikContract.lamOf q ρ₁ + 472/1000 ≤ Work.LinnikContract.lamOf q u := by
  have hl : (0:ℝ) < (17:ℝ)/20 := by norm_num
  let T : TestFn := tf72T ((17:ℝ)/20) hl
  obtain ⟨qE, hqE⟩ := hbLemma6_2_engine_wide T ((1:ℝ)/6) ((1:ℝ)/1000) δ
    (by norm_num) hδ0 hδ1
  refine ⟨max q₁ qE, ?_⟩
  intro q hq _instq χ₁ ρ₁ hmin hl1 χ u hzm hchi1 hne1 hne2 him8
  have hq1 : q₁ ≤ q := by omega
  have hqE' : qE ≤ q := by omega
  have hF0 : T.F 0 = 8/9 := by
    show (tf72Fc ((17:ℝ)/20) ((0:ℝ) : ℂ)).re = 8/9
    rw [show ((0:ℝ) : ℂ) = 0 from by norm_num]
    exact tf72Fc_zero_re _ hl
  have hf0 : T.f 0 = 68/75 := by
    show tf72f ((17:ℝ)/20) 0 = 68/75
    rw [tf72f_at_zero _ hl]
    norm_num
  have hLa : T.F (-(lamOf q ρ₁)) ≤ (11105:ℝ)/10000 := tf72F17_le_La_aux hl _ hl1
  have hF472 : (68:ℝ)/100 ≤ T.F ((472:ℝ)/1000) := tf72F17_ge_F472_aux hl
  have hstrict : T.F (-(lamOf q ρ₁)) - 8/9 + (68/75) * (3 * ((1:ℝ)/6 + (1:ℝ)/1000))
      < T.F ((472:ℝ)/1000) := by
    have h12 := Work.ZeroFreeTables.lam2_arith hLa hF472
    have hcoef : (68:ℝ)/75 * (3 * ((1:ℝ)/6 + (1:ℝ)/1000))
        < (68:ℝ)/75 * (1/2 + 4 * ((1:ℝ)/1000)) := by norm_num
    linarith
  by_cases hcase : lamOf q u ≤ 1
  · haveI : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
    haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    haveI : NeZero (χ₁ * χ).conductor := ⟨(χ₁ * χ).conductor_ne_zero⟩
    haveI : NeZero (χ₁ * χ⁻¹).conductor := ⟨(χ₁ * χ⁻¹).conductor_ne_zero⟩
    have hneA : χ₁ * χ ≠ 1 := fun h => hne2 (eq_inv_of_mul_eq_one_right h)
    have hneB : χ₁ * χ⁻¹ ≠ 1 := fun h => hne1 ((mul_inv_eq_one.mp h).symm)
    have hcore := hqE q hqE' χ₁ χ ρ₁ u
      (hL52 q hq1 χ₁ hmin.1.1.1)
      (hL52 q hq1 χ hchi1)
      (hL52 q hq1 (χ₁ * χ) hneA)
      (hL52 q hq1 (χ₁ * χ⁻¹) hneB)
      hmin hmin.1.1 hzm hchi1 hne1 hne2 him8 (by linarith) hcase
    have hmain : T.F (lamOf q u - lamOf q ρ₁)
        ≤ T.F (-(lamOf q ρ₁)) - 8/9 + (68/75) * (3 * ((1:ℝ)/6 + (1:ℝ)/1000)) := by
      rw [hF0, hf0] at hcore
      linarith
    by_contra hcon
    push_neg at hcon
    have hle : T.F ((472:ℝ)/1000) ≤ T.F (lamOf q u - lamOf q ρ₁) := by
      refine (TestFn_F_antitone T) ?_
      linarith
    linarith [hstrict, hmain, hle]
  · push_neg at hcase
    linarith

end Work.ZeroFreeTables.HB94
