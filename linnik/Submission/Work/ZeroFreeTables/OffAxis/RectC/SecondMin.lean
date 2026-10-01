import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.ZeroFreeTables.HB94.Lam2Ge
import Submission.Work.ZeroFreeTables.HB94.L52supply
import Submission.Work.ZeroFreeTables.OffAxis.WideDefs
import Submission.Work.ZeroFreeTables.OffAxis.hbLemma6_2_engine_HH

namespace Work.ZeroFreeTables.OffAxis.RectC

open DirichletCharacter Complex
open Work.LinnikContract
open scoped Classical BigOperators

/-- **HB Lemma 6.2 (`λ₂ ≥ λ₁ + 0.472`) at rectangle height `L`, uniformly for windows of height
`≤ 5L`.**  For a height-`L` rectangle minimiser `ρ₁` of `χ₁` with `λ₁ ≤ 0.348` and `|γ₁| > 1`,
every zero `u` of a **non-principal** character `χ ∉ {1, χ₁, χ₁⁻¹}` with `|Im u| ≤ 5L` satisfies
`λ(u) ≥ λ₁ + 472/1000`.

This is the transposition of `Work.ZeroFreeTables.HB94.Lam2Ge` (proved, sorry-free, on-axis:
`IsMin1WideAt 10`, `IsZ u`, i.e. `|Im u| ≤ 1`, with the general `φ = 1/3` supply
`Work.ZeroFreeTables.HB94.L52supply` as hypothesis) from height `1` to a window of height `≤ 5L`.
The two test points of HB Lemma 6.2 sit at heights `γ₁` (`|γ₁| ≤ L`) and `γ_u` (`|γ_u| ≤ 5L`),
so every window reaches `|γ₁| + |γ₂| + δ ≤ 6L + δ ≤ 10L`, inside the minimality range of
`IsRectMin L` (`|Im| ≤ 10L`).  A refined engine with the two height bounds `L` and `5L` kept
separate (rather than the single `H` of `OffAxis/hbLemma6_2_engine_H.lean`, which forces
`3H + δ ≤ 10L`) is what the height range `5L` requires. -/
theorem SecondMin : ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ → Work.LinnikContract.lamOf q ρ₁ ≤ (348:ℝ)/1000 →
      1 < |ρ₁.im| →
      ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), χ ≠ 1 → Work.LinnikContract.zeroMult χ u ≠ 0 →
        χ ≠ χ₁ → χ ≠ χ₁⁻¹ → |u.im| ≤ 5 * L →
          Work.LinnikContract.lamOf q ρ₁ + (472:ℝ)/1000 ≤ Work.LinnikContract.lamOf q u := by
  intro L hL
  -- the unconditional log-derivative supply `L52Hyp · (1/6) (1/1000000) δ`
  obtain ⟨δ, hδ0, hδ1, q₁₆, h16⟩ := HB94.L52supply16
  have hl : (0:ℝ) < (17:ℝ)/20 := by norm_num
  let T : TestFn := tf72T ((17:ℝ)/20) hl
  -- HB Lemma 6.2 at the two heights `L` (`ρ₁`) and `5L` (`ρ₂`), room `10L`
  obtain ⟨qE, hqE⟩ := OffAxis.hbLemma6_2_engine_HH T ((1:ℝ)/6) ((1:ℝ)/1000000) δ L (5 * L)
    (10 * L) (by norm_num) hδ0 hδ1 (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith)
  refine ⟨max (max q₁₆ qE) (Nat.ceil (Real.exp L) + 1), ?_⟩
  intro q hq _instq χ₁ ρ₁ hR hl1 _hoff χ u hχ hzm hne1 hne2 hu
  have hq₁₆ : q₁₆ ≤ q := by omega
  have hqE' : qE ≤ q := by omega
  have hqexp : Nat.ceil (Real.exp L) + 1 ≤ q := by omega
  -- `q ≥ exp L` gives the height bound `6L ≤ 10 log q` of the engine
  have hlogL : L ≤ Real.log (q : ℝ) := by
    have h1 : Real.exp L ≤ (q : ℝ) := by
      have h2 : Real.exp L ≤ ((Nat.ceil (Real.exp L) : ℕ) : ℝ) := Nat.le_ceil _
      have h3 : ((Nat.ceil (Real.exp L) + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqexp
      have h3' : ((Nat.ceil (Real.exp L) : ℕ) : ℝ) + 1 ≤ (q : ℝ) := by
        push_cast at h3; linarith
      linarith
    have h := Real.log_le_log (Real.exp_pos L) h1
    rwa [Real.log_exp] at h
  -- `IsRectMin L` *is* the height-`10L` numbering
  have hmin : IsMinWideAt L (10 * L) χ₁ ρ₁ :=
    ⟨hR.1.1, hR.1.2.1, hR.1.2.2, fun χ u hχ hzm him => hR.2 χ u ⟨hχ, hzm, him⟩⟩
  -- the values of the test function `tf72T (17/20)` that the arithmetic needs
  have hF0 : T.F 0 = 8/9 := by
    show (tf72Fc ((17:ℝ)/20) ((0:ℝ) : ℂ)).re = 8/9
    rw [show ((0:ℝ) : ℂ) = 0 from by norm_num]
    exact tf72Fc_zero_re _ hl
  have hf0 : T.f 0 = 68/75 := by
    show tf72f ((17:ℝ)/20) 0 = 68/75
    rw [tf72f_at_zero _ hl]
    norm_num
  have hLa : T.F (-(lamOf q ρ₁)) ≤ (11105:ℝ)/10000 := HB94.tf72F17_le_La_aux hl _ hl1
  have hF472 : (68:ℝ)/100 ≤ T.F ((472:ℝ)/1000) := HB94.tf72F17_ge_F472_aux hl
  have hstrict : T.F (-(lamOf q ρ₁)) - 8/9 + (68/75) * (3 * ((1:ℝ)/6 + (1:ℝ)/1000000))
      < T.F ((472:ℝ)/1000) := by
    have h12 := lam2_arith hLa hF472
    have hcoef : (68:ℝ)/75 * (3 * ((1:ℝ)/6 + (1:ℝ)/1000000))
        < (68:ℝ)/75 * (1/2 + 4 * ((1:ℝ)/1000)) := by norm_num
    linarith
  by_cases hcase : lamOf q u ≤ 1
  · haveI : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
    haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    haveI : NeZero (χ₁ * χ).conductor := ⟨(χ₁ * χ).conductor_ne_zero⟩
    haveI : NeZero (χ₁ * χ⁻¹).conductor := ⟨(χ₁ * χ⁻¹).conductor_ne_zero⟩
    have hneA : χ₁ * χ ≠ 1 := fun h => hne2 (eq_inv_of_mul_eq_one_right h)
    have hneB : χ₁ * χ⁻¹ ≠ 1 := fun h => hne1 ((mul_inv_eq_one.mp h).symm)
    have hHlog : L + 5 * L ≤ 10 * Real.log (q : ℝ) := by linarith
    have hl1' : lamOf q ρ₁ ≤ 1 := by linarith
    have hcore := hqE q hqE' χ₁ χ ρ₁ u hHlog
      (h16 q hq₁₆ χ₁ hmin.1)
      (h16 q hq₁₆ χ hχ)
      (h16 q hq₁₆ (χ₁ * χ) hneA)
      (h16 q hq₁₆ (χ₁ * χ⁻¹) hneB)
      hmin hzm hχ hu hne1 hne2 hl1' hcase
    have hmain : T.F (lamOf q u - lamOf q ρ₁)
        ≤ T.F (-(lamOf q ρ₁)) - 8/9 + (68/75) * (3 * ((1:ℝ)/6 + (1:ℝ)/1000000)) := by
      rw [hF0, hf0] at hcore
      linarith
    by_contra hcon
    push_neg at hcon
    have hle : T.F ((472:ℝ)/1000) ≤ T.F (lamOf q u - lamOf q ρ₁) := by
      refine (TestFn_F_antitone T) ?_
      linarith
    linarith
  · -- `λ(u) > 1 ≥ λ₁ + 472/1000` is immediate
    push_neg at hcase
    linarith

end Work.ZeroFreeTables.OffAxis.RectC
