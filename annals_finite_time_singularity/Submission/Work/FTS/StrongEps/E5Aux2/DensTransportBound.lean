/-
# `Submission/Work/FTS/StrongEps/E5Aux2/DensTransportBound.lean`

The pointwise bound for the `Transport`-block of the scheme's right-hand side:
`K θ * |Transport (slice (JfamP ρ ε g) τ) s θ| ≤ C (1+C₀)(1+B) (Maj s + s/(1+s)²) cos θ`
on `Iθ` (with `K θ = 3 sin θ cos²θ`).  `Transport f = 3 D_θ f/(1+z)` and `EpsDecay`'s
`SlotMaj 1` bounds `|D_θ f| = |mixed 0 1 f| ≤ Maj s`; the factor `K θ ≤ 2 cos θ` and
`1/(1+s) ≤ 1` finish.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.E5Aux2.AngFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

theorem DensTransportBound :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 →
      ∀ {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {ε τ C₀ B : ℝ} {g : Fam} {Maj : ℝ → ℝ},
      Work.FTS.StrongEps.EpsDecay α ρ Φs E ε τ g Maj →
      Work.FTS.Nonlin.Xn α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 →
      Work.FTS.StrongGlobal.Xn6 α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) ≤ B →
      ∀ s ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.K θ * |Work.Coercivity.Transport (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) s θ|
          ≤ C * (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2) * Real.cos θ := by
  refine ⟨6, by norm_num, ?_⟩
  intro α hα ρ Φs E ε τ C₀ B g Maj hDec hXn hXn6 s hs θ hθ
  obtain ⟨hMaj0, hMaj1, -, hSlot1, -⟩ := hDec
  have hs0 : (0 : ℝ) < s := hs
  have hC₀0 : 0 ≤ C₀ := by
    have hX : 0 ≤ Work.FTS.Nonlin.Xn α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) :=
      Work.Spaces.HkNorm_nonneg α 4 _
    nlinarith [hX, hXn, pow_pos hα.1 2]
  have hB0 : 0 ≤ B := by
    have hX : 0 ≤ Work.FTS.StrongGlobal.Xn6 α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) :=
      Work.Spaces.HkNorm_nonneg α 6 _
    linarith
  have hA1 : 1 ≤ (1 + C₀) * (1 + B) := by nlinarith
  have hDth : |Work.Spaces.Dth (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) s θ| ≤ Maj s :=
    hSlot1 s hs θ 0 1 (by norm_num)
  have hTr : |Work.Coercivity.Transport (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) s θ|
      ≤ 3 * Maj s / (1 + s) := by
    have h1s : (0 : ℝ) < 1 + s := by linarith
    have h2 : Work.Coercivity.Transport (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) s θ
        = 3 * Work.Spaces.Dth (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) s θ / (1 + s) := rfl
    rw [h2, abs_div, abs_of_pos h1s, abs_mul]
    have h3 : |(3 : ℝ)| = 3 := by norm_num
    rw [h3]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hDth (by norm_num)) h1s.le
  obtain ⟨hKnn, hKcos, hcos0, -, -, -, -, -⟩ := AngFacts
  have hK0 : 0 ≤ Work.Spaces.K θ := hKnn θ hθ
  have hKle : Work.Spaces.K θ ≤ 2 * Real.cos θ := hKcos θ hθ
  have hc0 : 0 ≤ Real.cos θ := hcos0 θ hθ
  have hs2nn : 0 ≤ s / (1 + s) ^ 2 := div_nonneg hs0.le (sq_nonneg _)
  set Q : ℝ := Maj s + s / (1 + s) ^ 2 with hQdef
  have hQ0 : 0 ≤ Q := by rw [hQdef]; linarith [hMaj0 s]
  have hQge : Maj s ≤ Q := by rw [hQdef]; linarith
  have h1s : (0 : ℝ) < 1 + s := by linarith
  have hle3 : 3 * Maj s / (1 + s) ≤ 3 * Maj s := by
    rw [div_le_iff₀ h1s]
    nlinarith [hMaj0 s]
  have hstep : Work.Spaces.K θ * |Work.Coercivity.Transport
      (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) s θ| ≤ 6 * Q * Real.cos θ := by
    have h1 : Work.Spaces.K θ * |Work.Coercivity.Transport
        (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) s θ| ≤ Work.Spaces.K θ * (3 * Maj s / (1 + s)) :=
      mul_le_mul_of_nonneg_left hTr hK0
    have h2 : Work.Spaces.K θ * (3 * Maj s / (1 + s)) ≤ Work.Spaces.K θ * (3 * Maj s) :=
      mul_le_mul_of_nonneg_left hle3 hK0
    have h3 : Work.Spaces.K θ * (3 * Maj s) ≤ (2 * Real.cos θ) * (3 * Maj s) :=
      mul_le_mul_of_nonneg_right hKle (by linarith [hMaj0 s])
    have h4 : (2 * Real.cos θ) * (3 * Maj s) ≤ 6 * Q * Real.cos θ := by
      rw [hQdef]; nlinarith [hMaj0 s, hc0, hs2nn]
    linarith [h1, h2, h3, h4]
  have hfin : 6 * Q * Real.cos θ ≤ 6 * (1 + C₀) * (1 + B) * Q * Real.cos θ := by
    have h0 : 0 ≤ Q * Real.cos θ := mul_nonneg hQ0 hc0
    have h1 : 1 * (Q * Real.cos θ) ≤ ((1 + C₀) * (1 + B)) * (Q * Real.cos θ) :=
      mul_le_mul_of_nonneg_right hA1 h0
    nlinarith [h1]
  rw [hQdef] at hstep ⊢
  linarith [hstep, hfin]

end Work.FTS.StrongEps.E5Aux2
