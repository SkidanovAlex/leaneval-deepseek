/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/StepCoerO.lean` — the induction step of the level-four
coercivity, on the **open** class

`CoercivityFix/StepCoer/step_coer.lean` proves the generic induction step of the coercivity of
`𝓛_Γ^T` (`Lhat` plus the transfer defect): from the level-`n` coercivity and Cauchy–Schwarz data,
the `Ê₂`-defect bound and the explicit regularity ports, it produces the level-`n+1` coercivity
`cc·min 1 (min c₁ c₂)/(2D)·|f|²_{ℋ^{n+1}} ≤ HkIPStep c₁ c₂ IP (𝓛̂ f) f`.

That proof **never inspects the class**: every regularity input is an explicit hypothesis
(`hreg`, `hregDth`, …).  This file is therefore the same proof with the frozen class
`Work.FTS.Nonlin.RegQ` replaced by the open class `Work.FTS.StrongEps.EpsE4Thr.RegQo`
(`SmoothOpen` + `HkMem` + `BdryTraces`), i.e. the induction step that the open-class re-run of the
coercivity chapter consumes.  It is a *textual* port: the proof term is the frozen one.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.CoercivityFix.Step
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr



/-- **Young's inequality in the form used by the induction step.**  If `0 < lam` and
`p ^ 2 ≤ A * (4 * lam)`, then `p √x √y ≤ lam x + A y` for `x, y ≥ 0`.

This is the absorption of the `Ê₂`-pairing `p √X₀ √X₂ ≤ λ X₀ + A X₂` into the coercivity
slack: `λ = cc/4` with `A = c₂ cc/4` for the `X₀` slot and `λ = c₁ cc/4` with the same `A`
for the `X₁` slot, the two half-budgets adding to the `c₂ cc/2` spent on `X₂`. -/
private lemma young_absorb_fts {lam p x y A : ℝ} (hlam : 0 < lam) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hA : p ^ 2 ≤ A * (4 * lam)) :
    p * (Real.sqrt x * Real.sqrt y) ≤ lam * x + A * y := by
  have h4 : 0 < 4 * lam := by linarith
  have hsx : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  have hsy : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy
  have h1 : 4 * lam * (p * (Real.sqrt x * Real.sqrt y)) ≤ 4 * lam ^ 2 * x + p ^ 2 * y := by
    nlinarith [sq_nonneg (2 * lam * Real.sqrt x - p * Real.sqrt y), hsx, hsy]
  have h2 : p ^ 2 * y ≤ A * (4 * lam) * y := mul_le_mul_of_nonneg_right hA hy
  have key : 4 * lam * (p * (Real.sqrt x * Real.sqrt y)) ≤ 4 * lam * (lam * x + A * y) := by
    nlinarith [h1, h2]
  exact le_of_mul_le_mul_left key h4

theorem step_coer_O (α : ℝ) (n : ℕ) {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ} {cc CC κ c₁ c₂ D : ℝ}
    (hcc : 0 < cc) (hCC : 0 < CC) (hκ : 0 ≤ κ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hD : 0 < D)
    (hsmall : Work.FTS.CoercivityFix.StepSmall cc CC κ c₁ c₂)
    (hcoer : ∀ f : ℝ → ℝ → ℝ, Work.FTS.StrongEps.EpsE4Thr.RegQo α n f →
      cc * Work.Spaces.HkSq α n f ≤ IP (Work.FTS.CoercivityFix.Lhat f) f)
    (hcs : ∀ f g : ℝ → ℝ → ℝ, Work.FTS.StrongEps.EpsE4Thr.RegQo α n f → Work.FTS.StrongEps.EpsE4Thr.RegQo α n g →
      |IP f g| ≤ CC * Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g)
    (hE2 : ∀ f : ℝ → ℝ → ℝ, Work.FTS.StrongEps.EpsE4Thr.RegQo α (n + 1) f →
      Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.E2hat f)
        ≤ κ * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)))
    (hcongr : ∀ f f' g : ℝ → ℝ → ℝ, Work.FTS.StrongEps.EpsE4Thr.RegQo α n f → Work.FTS.StrongEps.EpsE4Thr.RegQo α n g →
      (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) → IP f g = IP f' g)
    (hadd : ∀ f₁ f₂ g : ℝ → ℝ → ℝ, Work.FTS.StrongEps.EpsE4Thr.RegQo α n f₁ → Work.FTS.StrongEps.EpsE4Thr.RegQo α n f₂ →
      Work.FTS.StrongEps.EpsE4Thr.RegQo α n g → IP (f₁ + f₂) g = IP f₁ g + IP f₂ g)
    (hdthC : ∀ f : ℝ → ℝ → ℝ, Work.FTS.StrongEps.EpsE4Thr.RegQo α (n + 1) f → ∀ z θ : ℝ,
      (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
        = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f) z θ)
    (hdzC : ∀ f : ℝ → ℝ → ℝ, Work.FTS.StrongEps.EpsE4Thr.RegQo α (n + 1) f → ∀ z θ : ℝ,
      (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
        = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ + Work.FTS.CoercivityFix.E2hat f z θ)
    (hreg : ∀ f : ℝ → ℝ → ℝ, Work.FTS.StrongEps.EpsE4Thr.RegQo α (n + 1) f → Work.FTS.StrongEps.EpsE4Thr.RegQo α n f)
    (hregDth : ∀ f : ℝ → ℝ → ℝ, Work.FTS.StrongEps.EpsE4Thr.RegQo α (n + 1) f →
      Work.FTS.StrongEps.EpsE4Thr.RegQo α n (Work.Spaces.Dth f))
    (hregDz : ∀ f : ℝ → ℝ → ℝ, Work.FTS.StrongEps.EpsE4Thr.RegQo α (n + 1) f →
      Work.FTS.StrongEps.EpsE4Thr.RegQo α n (Work.Spaces.Dz f))
    (hregLdz : ∀ f : ℝ → ℝ → ℝ, Work.FTS.StrongEps.EpsE4Thr.RegQo α (n + 1) f →
      Work.FTS.StrongEps.EpsE4Thr.RegQo α n (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)))
    (hregDthL : ∀ f : ℝ → ℝ → ℝ, Work.FTS.StrongEps.EpsE4Thr.RegQo α (n + 1) f →
      Work.FTS.StrongEps.EpsE4Thr.RegQo α n (Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f)))
    (hregDzL : ∀ f : ℝ → ℝ → ℝ, Work.FTS.StrongEps.EpsE4Thr.RegQo α (n + 1) f →
      Work.FTS.StrongEps.EpsE4Thr.RegQo α n (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f)))
    (hregE2 : ∀ f : ℝ → ℝ → ℝ, Work.FTS.StrongEps.EpsE4Thr.RegQo α (n + 1) f →
      Work.FTS.StrongEps.EpsE4Thr.RegQo α n (Work.FTS.CoercivityFix.E2hat f))
    (hnormD : ∀ f : ℝ → ℝ → ℝ, Work.FTS.StrongEps.EpsE4Thr.RegQo α (n + 1) f →
      Work.Spaces.HkSq α (n + 1) f
        ≤ D * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)
          + Work.Spaces.HkSq α n (Work.Spaces.Dz f))) :
    ∀ f : ℝ → ℝ → ℝ, Work.FTS.StrongEps.EpsE4Thr.RegQo α (n + 1) f →
      cc * min 1 (min c₁ c₂) / (2 * D) * Work.Spaces.HkSq α (n + 1) f
        ≤ Work.Coercivity.HkIPStep c₁ c₂ IP (Work.FTS.CoercivityFix.Lhat f) f := by
  intro f hf
  -- the regularity ports to level `n` (all supplied by the level-`n` data)
  have hf0 : RegQo α n f := hreg f hf
  have hf1 : RegQo α n (Work.Spaces.Dth f) := hregDth f hf
  have hf2 : RegQo α n (Work.Spaces.Dz f) := hregDz f hf
  have hL2 : RegQo α n (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) := hregLdz f hf
  have hDL : RegQo α n (Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f)) := hregDthL f hf
  have hzL : RegQo α n (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f)) := hregDzL f hf
  have hE2r : RegQo α n (Work.FTS.CoercivityFix.E2hat f) := hregE2 f hf
  -- the two commutator identities transfer the operator onto the differentiated slot
  have e1 : IP (Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dth f)
      = IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)) (Work.Spaces.Dth f) :=
    hcongr _ _ _ hDL hf1 (fun z θ h => hdthC f hf z θ h)
  have e2 : IP (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dz f)
      = IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) (Work.Spaces.Dz f)
        + IP (Work.FTS.CoercivityFix.E2hat f) (Work.Spaces.Dz f) := by
    rw [hcongr (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f))
      (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) + Work.FTS.CoercivityFix.E2hat f)
      (Work.Spaces.Dz f) hzL hf2 (fun z θ h => by simpa using hdzC f hf z θ h)]
    exact hadd _ _ _ hL2 hE2r hf2
  set X0 : ℝ := Work.Spaces.HkSq α n f with hX0
  set X1 : ℝ := Work.Spaces.HkSq α n (Work.Spaces.Dth f) with hX1
  set X2 : ℝ := Work.Spaces.HkSq α n (Work.Spaces.Dz f) with hX2
  set Y : ℝ := Work.Spaces.HkSq α (n + 1) f with hY
  set m : ℝ := min 1 (min c₁ c₂) with hm
  have hX0nn : 0 ≤ X0 := by rw [hX0]; exact Work.Spaces.HkSq_nonneg α n f
  have hX1nn : 0 ≤ X1 := by rw [hX1]; exact Work.Spaces.HkSq_nonneg α n _
  have hX2nn : 0 ≤ X2 := by rw [hX2]; exact Work.Spaces.HkSq_nonneg α n _
  have hNf : Work.Spaces.HkNorm α n f = Real.sqrt X0 := by rw [Work.Spaces.HkNorm, ← hX0]
  have hN1 : Work.Spaces.HkNorm α n (Work.Spaces.Dth f) = Real.sqrt X1 := by
    rw [Work.Spaces.HkNorm, ← hX1]
  have hN2 : Work.Spaces.HkNorm α n (Work.Spaces.Dz f) = Real.sqrt X2 := by
    rw [Work.Spaces.HkNorm, ← hX2]
  -- the smallness of the step coefficient in the two binomial forms used below
  have hp1 : (c₂ * CC * κ) ^ 2 ≤ (c₂ * cc / 4) * (4 * (cc / 4)) := by
    have h := mul_le_mul_of_nonneg_left hsmall.1 hc₂.le
    nlinarith [h]
  have hp2 : (c₂ * CC * κ) ^ 2 ≤ (c₂ * cc / 4) * (4 * (c₁ * cc / 4)) := by
    have h := mul_le_mul_of_nonneg_left hsmall.2 hc₂.le
    nlinarith [h]
  -- the `Ê₂`-pairing, absorbed into the level-`n` coercivity slack
  have hS : (c₂ * CC * κ) * (Real.sqrt X0 + Real.sqrt X1) * Real.sqrt X2
      ≤ cc / 4 * X0 + (c₁ * cc / 4) * X1 + (c₂ * cc / 2) * X2 := by
    have hy0 := young_absorb_fts (lam := cc / 4) (p := c₂ * CC * κ) (x := X0) (y := X2)
      (A := c₂ * cc / 4) (by positivity) hX0nn hX2nn hp1
    have hy1 := young_absorb_fts (lam := c₁ * cc / 4) (p := c₂ * CC * κ) (x := X1) (y := X2)
      (A := c₂ * cc / 4) (by positivity) hX1nn hX2nn hp2
    have heq : (c₂ * CC * κ) * (Real.sqrt X0 + Real.sqrt X1) * Real.sqrt X2
        = (c₂ * CC * κ) * (Real.sqrt X0 * Real.sqrt X2)
          + (c₂ * CC * κ) * (Real.sqrt X1 * Real.sqrt X2) := by ring
    rw [heq]
    linarith [hy0, hy1]
  have hE2norm : Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.E2hat f)
      ≤ κ * (Real.sqrt X0 + Real.sqrt X1) := by
    have h := hE2 f hf
    rw [hNf, hN1] at h
    exact h
  have hcsE : c₂ * |IP (Work.FTS.CoercivityFix.E2hat f) (Work.Spaces.Dz f)|
      ≤ (c₂ * CC * κ) * (Real.sqrt X0 + Real.sqrt X1) * Real.sqrt X2 := by
    have h1 := hcs (Work.FTS.CoercivityFix.E2hat f) (Work.Spaces.Dz f) hE2r hf2
    have hnn : 0 ≤ κ * (Real.sqrt X0 + Real.sqrt X1) := by positivity
    have h3 : CC * Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.E2hat f)
          * Work.Spaces.HkNorm α n (Work.Spaces.Dz f)
        ≤ CC * (κ * (Real.sqrt X0 + Real.sqrt X1)) * Real.sqrt X2 := by
      rw [hN2]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hE2norm hCC.le) le_rfl (Real.sqrt_nonneg X2)
        (mul_nonneg hCC.le hnn)
    calc c₂ * |IP (Work.FTS.CoercivityFix.E2hat f) (Work.Spaces.Dz f)|
        ≤ c₂ * (CC * Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.E2hat f)
            * Work.Spaces.HkNorm α n (Work.Spaces.Dz f)) := mul_le_mul_of_nonneg_left h1 hc₂.le
      _ ≤ c₂ * (CC * (κ * (Real.sqrt X0 + Real.sqrt X1)) * Real.sqrt X2) :=
          mul_le_mul_of_nonneg_left h3 hc₂.le
      _ = (c₂ * CC * κ) * (Real.sqrt X0 + Real.sqrt X1) * Real.sqrt X2 := by ring
  have hEB : -(c₂ * IP (Work.FTS.CoercivityFix.E2hat f) (Work.Spaces.Dz f))
      ≤ cc / 4 * X0 + (c₁ * cc / 4) * X1 + (c₂ * cc / 2) * X2 := by
    have hle : - IP (Work.FTS.CoercivityFix.E2hat f) (Work.Spaces.Dz f)
        ≤ |IP (Work.FTS.CoercivityFix.E2hat f) (Work.Spaces.Dz f)| := neg_le_abs _
    have h := mul_le_mul_of_nonneg_left hle hc₂.le
    linarith [h, hcsE, hS]
  -- level-`n` coercivity of `𝓛̂` applied to `f`, `D_θ f`, `D_z f`
  have hRlow : cc * X0 + c₁ * (cc * X1) + c₂ * (cc * X2)
      - (cc / 4 * X0 + (c₁ * cc / 4) * X1 + (c₂ * cc / 2) * X2)
      ≤ IP (Work.FTS.CoercivityFix.Lhat f) f
        + c₁ * IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)) (Work.Spaces.Dth f)
        + c₂ * (IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) (Work.Spaces.Dz f)
            + IP (Work.FTS.CoercivityFix.E2hat f) (Work.Spaces.Dz f)) := by
    have hc0 := hcoer f hf0
    have hc1 := hcoer (Work.Spaces.Dth f) hf1
    have hc2 := hcoer (Work.Spaces.Dz f) hf2
    rw [← hX0] at hc0
    rw [← hX1] at hc1
    rw [← hX2] at hc2
    have hc1' : c₁ * (cc * X1)
        ≤ c₁ * IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)) (Work.Spaces.Dth f) :=
      mul_le_mul_of_nonneg_left hc1 hc₁.le
    have hc2' : c₂ * (cc * X2)
        ≤ c₂ * IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) (Work.Spaces.Dz f) :=
      mul_le_mul_of_nonneg_left hc2 hc₂.le
    have he : IP (Work.FTS.CoercivityFix.Lhat f) f
        + c₁ * IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)) (Work.Spaces.Dth f)
        + c₂ * (IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) (Work.Spaces.Dz f)
            + IP (Work.FTS.CoercivityFix.E2hat f) (Work.Spaces.Dz f))
        = IP (Work.FTS.CoercivityFix.Lhat f) f
        + c₁ * IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)) (Work.Spaces.Dth f)
        + c₂ * IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) (Work.Spaces.Dz f)
        + c₂ * IP (Work.FTS.CoercivityFix.E2hat f) (Work.Spaces.Dz f) := by ring
    rw [he]
    linarith [hc0, hc1', hc2', hEB]
  have hm1 : m ≤ 1 := by rw [hm]; exact min_le_left _ _
  have hmc₁ : m ≤ c₁ := by rw [hm]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hmc₂ : m ≤ c₂ := by rw [hm]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  -- the coefficient bookkeeping: what survives of the level-`n` coercivity dominates
  -- `(cc · min 1 (min c₁ c₂) / 2) · (X₀ + X₁ + X₂)`
  have hcoef : (cc * m / 2) * (X0 + X1 + X2)
      ≤ cc * X0 + c₁ * (cc * X1) + c₂ * (cc * X2)
        - (cc / 4 * X0 + (c₁ * cc / 4) * X1 + (c₂ * cc / 2) * X2) := by
    have e0 : (cc * m / 2) * X0 ≤ (3 * cc / 4) * X0 := by
      have h : m / 2 ≤ (3:ℝ) / 4 := by linarith
      calc (cc * m / 2) * X0 = cc * (m / 2) * X0 := by ring
        _ ≤ cc * ((3:ℝ) / 4) * X0 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hcc.le) hX0nn
        _ = (3 * cc / 4) * X0 := by ring
    have e1 : (cc * m / 2) * X1 ≤ (3 * c₁ * cc / 4) * X1 := by
      have h : m / 2 ≤ 3 * c₁ / 4 := by linarith
      calc (cc * m / 2) * X1 = cc * (m / 2) * X1 := by ring
        _ ≤ cc * (3 * c₁ / 4) * X1 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hcc.le) hX1nn
        _ = (3 * c₁ * cc / 4) * X1 := by ring
    have e2 : (cc * m / 2) * X2 ≤ (c₂ * cc / 2) * X2 := by
      have h : m / 2 ≤ c₂ / 2 := by linarith
      calc (cc * m / 2) * X2 = cc * (m / 2) * X2 := by ring
        _ ≤ cc * (c₂ / 2) * X2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hcc.le) hX2nn
        _ = (c₂ * cc / 2) * X2 := by ring
    have hexp : (cc * m / 2) * (X0 + X1 + X2)
        = (cc * m / 2) * X0 + (cc * m / 2) * X1 + (cc * m / 2) * X2 := by ring
    have hexp2 : cc * X0 + c₁ * (cc * X1) + c₂ * (cc * X2)
          - (cc / 4 * X0 + (c₁ * cc / 4) * X1 + (c₂ * cc / 2) * X2)
        = (3 * cc / 4) * X0 + (3 * c₁ * cc / 4) * X1 + (c₂ * cc / 2) * X2 := by ring
    rw [hexp, hexp2]
    linarith [e0, e1, e2]
  -- the one-sided norm comparison, rescaled by `cc · min 1 (min c₁ c₂) / (2D)`
  have hYL : cc * m / (2 * D) * Y ≤ (cc * m / 2) * (X0 + X1 + X2) := by
    have hYD : Y ≤ D * (X0 + X1 + X2) := by
      rw [hY, hX0, hX1, hX2]
      exact hnormD f hf
    have hc : 0 ≤ cc * m / (2 * D) := by
      have hp : 0 < cc * m :=
        mul_pos hcc (by rw [hm]; exact lt_min one_pos (lt_min hc₁ hc₂))
      positivity
    calc cc * m / (2 * D) * Y ≤ cc * m / (2 * D) * (D * (X0 + X1 + X2)) :=
          mul_le_mul_of_nonneg_left hYD hc
      _ = (cc * m / 2) * (X0 + X1 + X2) := by field_simp
  have hmain := le_trans hYL (le_trans hcoef hRlow)
  rw [Work.Coercivity.HkIPStep, e1, e2]
  exact hmain

end Work.FTS.StrongEps.EpsE4Thr
