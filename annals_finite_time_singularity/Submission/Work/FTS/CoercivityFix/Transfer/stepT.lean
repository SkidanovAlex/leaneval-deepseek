/-
# `Transfer/stepT.lean` — the induction step of the transfer

This is the modification of `Assembly.coer_clause_succ` that runs the paper's induction for
`𝓛_Γ^T` on the thin class `CoerAdm` (design `N45_DESIGN_LEAD.md` §5 T2).  Compared with
`coer_clause_succ`, the three level-`n` coercivities come from **two** packages:

* the `ε`-slot `IP (𝓛_Γ^T f) f ≥ cc·|f|²_n` is `CoerDataT.coer` (the inductive hypothesis —
  the *paper's* operator);
* the `D_θ`- and `D_z`-slots are reduced, through the two identities of
  `Transfer/Profiles.lean` (`D_θ𝓛_Γ^T f = 𝓛̂(D_θf) + E1`, `D_z𝓛_Γ^T f = 𝓛̂(D_zf) + E2`), to the
  **clean** coercivity `CoerData2.coer` `IP (𝓛̂ h) h ≥ ccL·|h|²_n` for `h = D_θf`, `D_zf`,
  plus the two error pairings `IP (E1) (D_θf)`, `IP (E2) (D_zf)` bounded by `CoerData2.cs`.

`E1` is `α`-small (`|D_θΓ| ≤ 2αΓ`) and `E2` is `O(|f| + |D_θf|)` — **neither** involves `D_zf`,
which is what keeps the `|D_zf|²` slot absorbable and the coercivity constant positive.
Everything is uniform in `α`: the constants are `α`-free and the four smallness conditions
`hs1`–`hs4` are met by taking `α`, `c₁`, `c₂` small.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.CoercivityFix.Assembly.Defs
import Submission.Work.FTS.CoercivityFix.Transfer.CoreDefs
import Submission.Work.FTS.CoercivityFix.Assembly.Lhat_RegQ
import Submission.Work.FTS.CoercivityFix.Assembly.step2_data
import Submission.Work.FTS.CoercivityFix.Assembly.StepReg2_all
import Submission.Work.FTS.CoercivityFix.Assembly.RegQ_dth_ge
import Submission.Work.FTS.CoercivityFix.Assembly.RegQAux
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.CoercivityFix.Transfer.CoerDataT

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (RegQ CoerAdm)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Young's inequality in the form used by the step: for `0 < lam` and `x, y ≥ 0`,
`p·√x·√y ≤ lam·x + (p²/(4·lam))·y`. -/
private lemma young_absorb {lam p x y : ℝ} (hlam : 0 < lam) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    p * (Real.sqrt x * Real.sqrt y) ≤ lam * x + (p ^ 2 / (4 * lam)) * y := by
  have h4 : 0 < 4 * lam := by linarith
  have hsx : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  have hsy : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy
  have h1 : 0 ≤ (2 * lam * Real.sqrt x - p * Real.sqrt y) ^ 2 := sq_nonneg _
  have h3 : 4 * lam * (p * (Real.sqrt x * Real.sqrt y)) ≤ 4 * lam ^ 2 * x + p ^ 2 * y := by
    nlinarith [h1, hsx, hsy]
  have h2 : (4 * lam) * ((p ^ 2 / (4 * lam)) * y) = p ^ 2 * y := by
    field_simp
  have hkey : 4 * lam * (p * (Real.sqrt x * Real.sqrt y))
      ≤ 4 * lam * (lam * x + (p ^ 2 / (4 * lam)) * y) := by
    have h4' : 4 * lam * (lam * x + (p ^ 2 / (4 * lam)) * y)
        = 4 * lam ^ 2 * x + 4 * lam * ((p ^ 2 / (4 * lam)) * y) := by ring
    rw [h4', h2]
    linarith [h3]
  exact le_of_mul_le_mul_left hkey h4

/-- **The transfer step.** -/
theorem stepT (α : ℝ) (n : ℕ) (hα : 0 < α) (hn3 : n ≤ 3)
    {IP : Fn → Fn → ℝ} {cc CC ccL CCL κ₁ κ₂ c₁ c₂ D : ℝ}
    (ht : CoerDataT α n IP cc CC)
    (hcl : Work.FTS.CoercivityFix.Assembly.CoerData2 α n IP ccL CCL)
    (hc : Work.FTS.CoercivityFix.Transfer.CommSm α n IP)
    (hcs1 : ∀ f : Fn, CoerAdm α f →
      |IP (E1 α f) (Work.Spaces.Dth f)|
        ≤ CCL * Work.Spaces.HkNorm α n (E1 α f) * Work.Spaces.HkNorm α n (Work.Spaces.Dth f))
    (hcs2 : ∀ f : Fn, CoerAdm α f →
      |IP (E2 α f) (Work.Spaces.Dz f)|
        ≤ CCL * Work.Spaces.HkNorm α n (E2 α f) * Work.Spaces.HkNorm α n (Work.Spaces.Dz f))
    (hreg : Work.FTS.CoercivityFix.Assembly.StepReg2 α n)
    (hid1 : ∀ f : Fn, CoerAdm α f → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dth (Work.Coercivity.LGammaT α f) z θ
        = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f) z θ + E1 α f z θ)
    (hid2 : ∀ f : Fn, CoerAdm α f → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dz (Work.Coercivity.LGammaT α f) z θ
        = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ + E2 α f z θ)
    (hbk1 : ∀ f : Fn, CoerAdm α f →
      Work.FTS.CoercivityFix.Transfer.AddOKSm α n
        (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)) (E1 α f) (Work.Spaces.Dth f))
    (hbk2 : ∀ f : Fn, CoerAdm α f →
      Work.FTS.CoercivityFix.Transfer.AddOKSm α n
        (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) (E2 α f) (Work.Spaces.Dz f))
    (hn1 : ∀ f : Fn, CoerAdm α f → Work.Spaces.HkNorm α n (E1 α f)
      ≤ α * κ₁ * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)))
    (hn2 : ∀ f : Fn, CoerAdm α f → Work.Spaces.HkNorm α n (E2 α f)
      ≤ κ₂ * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)))
    (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hD : 0 < D)
    (hs1 : c₁ * (16 * (CCL * α * κ₁) ^ 2) ≤ cc * ccL)
    (hs2 : CCL * α * κ₁ ≤ ccL / 8)
    (hs3 : c₂ * (16 * (CCL * κ₂) ^ 2) ≤ cc * ccL)
    (hs4 : c₂ * (16 * (CCL * κ₂) ^ 2) ≤ c₁ * ccL ^ 2)
    (hnormD : ∀ f : Fn, CoerAdm α f →
      Work.Spaces.HkSq α (n + 1) f
        ≤ D * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)
            + Work.Spaces.HkSq α n (Work.Spaces.Dz f))) :
    CoerDataT α (n + 1) (Work.Coercivity.HkIPStep c₁ c₂ IP)
      (min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) / D)
      (3 * max 1 (max c₁ c₂) * CC) := by
  have hα' : -(1 / 10 : ℝ) ≤ α := by linarith
  have hccL : 0 < ccL := hcl.hcc
  have hCCL : 0 < CCL := hcl.hCC
  have hm₀ : 0 < min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) :=
    lt_min (by linarith [ht.hcc]) (lt_min (by positivity) (by positivity))
  have hcc' : 0 < min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) / D :=
    div_pos hm₀ hD
  have hCC' : 0 < 3 * max 1 (max c₁ c₂) * CC := by
    have h1 : (1 : ℝ) ≤ max 1 (max c₁ c₂) := le_max_left _ _
    nlinarith [ht.hCC]
  refine ⟨hcc', hCC', ?_, ?_⟩
  · -- the Cauchy–Schwarz clause
    intro f g hf hg
    exact Work.FTS.CoercivityFix.Assembly.cs_clause_succ α hα' n ht.cs (le_of_lt ht.hCC)
      (fun u hu => Work.FTS.CoercivityFix.Assembly.RegQ_dth_ge α hα' hu) hc₁ hc₂ f g hf hg
  · -- the coercivity clause
    intro f hf
    set X0 : ℝ := Work.Spaces.HkSq α n f with hX0def
    set X1 : ℝ := Work.Spaces.HkSq α n (Work.Spaces.Dth f) with hX1def
    set X2 : ℝ := Work.Spaces.HkSq α n (Work.Spaces.Dz f) with hX2def
    set Y : ℝ := Work.Spaces.HkSq α (n + 1) f with hYdef
    have hX0 : 0 ≤ X0 := by rw [hX0def]; exact Work.Spaces.HkSq_nonneg α n f
    have hX1 : 0 ≤ X1 := by rw [hX1def]; exact Work.Spaces.HkSq_nonneg α n _
    have hX2 : 0 ≤ X2 := by rw [hX2def]; exact Work.Spaces.HkSq_nonneg α n _
    have hf2 : RegQ α (n + 2) f :=
      Work.FTS.GalerkinFix.RegQ.regQ_mono hf.reg (by omega)
    have hf1 : RegQ α (n + 1) (Work.Spaces.Dth f) := hreg.dth1 f hf2
    have hf1n : RegQ α n (Work.Spaces.Dth f) := hreg.dth2 f hf2
    have hf2n : RegQ α (n + 1) (Work.Spaces.Dz f) := hreg.dz1 f hf2
    have hf2nn : RegQ α n (Work.Spaces.Dz f) := hreg.dz2 f hf2
    have hL1 : RegQ α n (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)) :=
      Work.FTS.CoercivityFix.Assembly.Lhat_RegQ α hα hf1
    have hL2 : RegQ α n (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) :=
      Work.FTS.CoercivityFix.Assembly.Lhat_RegQ α hα hf2n
    obtain ⟨hq1a, hq1b, hq1c, hm1a, hm1b, hm1c⟩ := hbk1 f hf
    obtain ⟨hq2a, hq2b, hq2c, hm2a, hm2b, hm2c⟩ := hbk2 f hf
    have e₁ : IP (Work.Spaces.Dth (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dth f)
        = IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)) (Work.Spaces.Dth f)
          + IP (E1 α f) (Work.Spaces.Dth f) := by
      rw [hc.congr (Work.Spaces.Dth (Work.Coercivity.LGammaT α f))
            (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f) + E1 α f)
            (Work.Spaces.Dth f) (fun z θ h => hid1 f hf z θ h)]
      exact hc.add _ _ _ ⟨hq1a, hq1b, hq1c, hm1a, hm1b, hm1c⟩
    have e₂ : IP (Work.Spaces.Dz (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dz f)
        = IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) (Work.Spaces.Dz f)
          + IP (E2 α f) (Work.Spaces.Dz f) := by
      rw [hc.congr (Work.Spaces.Dz (Work.Coercivity.LGammaT α f))
            (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) + E2 α f)
            (Work.Spaces.Dz f) (fun z θ h => hid2 f hf z θ h)]
      exact hc.add _ _ _ ⟨hq2a, hq2b, hq2c, hm2a, hm2b, hm2c⟩
    -- the three coercivities
    have hA : cc * X0 ≤ IP (Work.Coercivity.LGammaT α f) f := ht.coer f hf
    have hB1 : ccL * X1
        ≤ IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)) (Work.Spaces.Dth f) :=
      hcl.coer _ hf1
    have hB2 : ccL * X2
        ≤ IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) (Work.Spaces.Dz f) :=
      hcl.coer _ hf2n
    -- the two Cauchy–Schwarz bounds on the error pairings
    have hS1 : |IP (E1 α f) (Work.Spaces.Dth f)|
        ≤ CCL * Real.sqrt (Work.Spaces.HkSq α n (E1 α f)) * Real.sqrt X1 := by
      have h := hcs1 f hf
      rw [show Work.Spaces.HkNorm α n (Work.Spaces.Dth f) = Real.sqrt X1 from by
        rw [Work.Spaces.HkNorm, hX1def]] at h
      rwa [show Work.Spaces.HkNorm α n (E1 α f)
        = Real.sqrt (Work.Spaces.HkSq α n (E1 α f)) from rfl] at h
    have hS2 : |IP (E2 α f) (Work.Spaces.Dz f)|
        ≤ CCL * Real.sqrt (Work.Spaces.HkSq α n (E2 α f)) * Real.sqrt X2 := by
      have h := hcs2 f hf
      rw [show Work.Spaces.HkNorm α n (Work.Spaces.Dz f) = Real.sqrt X2 from by
        rw [Work.Spaces.HkNorm, hX2def]] at h
      rwa [show Work.Spaces.HkNorm α n (E2 α f)
        = Real.sqrt (Work.Spaces.HkSq α n (E2 α f)) from rfl] at h
    -- the two defect norms
    have hν1 : Real.sqrt (Work.Spaces.HkSq α n (E1 α f)) * CCL
        ≤ (α * κ₁ * CCL) * (Real.sqrt X0 + Real.sqrt X1) := by
      have h := hn1 f hf
      rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, Work.Spaces.HkNorm, ← hX0def, ← hX1def] at h
      nlinarith [h, le_of_lt hCCL]
    have hν2 : Real.sqrt (Work.Spaces.HkSq α n (E2 α f)) * CCL
        ≤ (κ₂ * CCL) * (Real.sqrt X0 + Real.sqrt X1) := by
      have h := hn2 f hf
      rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, Work.Spaces.HkNorm, ← hX0def, ← hX1def] at h
      nlinarith [h, le_of_lt hCCL]
    have hn1' : CCL * Real.sqrt (Work.Spaces.HkSq α n (E1 α f)) * Real.sqrt X1
        ≤ (α * κ₁ * CCL) * (Real.sqrt X0 * Real.sqrt X1) + (α * κ₁ * CCL) * X1 := by
      have h := mul_le_mul_of_nonneg_right hν1 (Real.sqrt_nonneg X1)
      have hsq : (Real.sqrt X1) ^ 2 = X1 := Real.sq_sqrt hX1
      nlinarith [h, hsq]
    have hn2' : CCL * Real.sqrt (Work.Spaces.HkSq α n (E2 α f)) * Real.sqrt X2
        ≤ (κ₂ * CCL) * (Real.sqrt X0 * Real.sqrt X2)
          + (κ₂ * CCL) * (Real.sqrt X1 * Real.sqrt X2) := by
      have h := mul_le_mul_of_nonneg_right hν2 (Real.sqrt_nonneg X2)
      have hsq : (Real.sqrt X2) ^ 2 = X2 := Real.sq_sqrt hX2
      nlinarith [h, hsq]
    -- Young
    have hp1 : (c₁ * (α * κ₁ * CCL)) * (Real.sqrt X0 * Real.sqrt X1)
        ≤ (cc / 8) * X0 + (2 * (c₁ * (α * κ₁ * CCL)) ^ 2 / cc) * X1 := by
      have h := young_absorb (lam := cc / 8) (p := c₁ * (α * κ₁ * CCL)) (x := X0) (y := X1)
        (div_pos ht.hcc (by norm_num)) hX0 hX1
      have heq : (c₁ * (α * κ₁ * CCL)) ^ 2 / (4 * (cc / 8))
          = 2 * (c₁ * (α * κ₁ * CCL)) ^ 2 / cc := by field_simp; ring
      rwa [heq] at h
    have hp2 : (c₂ * (κ₂ * CCL)) * (Real.sqrt X0 * Real.sqrt X2)
        ≤ (cc / 8) * X0 + (2 * (c₂ * (κ₂ * CCL)) ^ 2 / cc) * X2 := by
      have h := young_absorb (lam := cc / 8) (p := c₂ * (κ₂ * CCL)) (x := X0) (y := X2)
        (div_pos ht.hcc (by norm_num)) hX0 hX2
      have heq : (c₂ * (κ₂ * CCL)) ^ 2 / (4 * (cc / 8))
          = 2 * (c₂ * (κ₂ * CCL)) ^ 2 / cc := by field_simp; ring
      rwa [heq] at h
    have hp3 : (c₂ * (κ₂ * CCL)) * (Real.sqrt X1 * Real.sqrt X2)
        ≤ (c₁ * ccL / 8) * X1 + (2 * (c₂ * (κ₂ * CCL)) ^ 2 / (c₁ * ccL)) * X2 := by
      have h := young_absorb (lam := c₁ * ccL / 8) (p := c₂ * (κ₂ * CCL)) (x := X1) (y := X2)
        (by positivity) hX1 hX2
      have heq : (c₂ * (κ₂ * CCL)) ^ 2 / (4 * (c₁ * ccL / 8))
          = 2 * (c₂ * (κ₂ * CCL)) ^ 2 / (c₁ * ccL) := by field_simp; ring
      rwa [heq] at h
    -- the Young tails fit in the budgets
    have hd1 : 2 * (c₁ * (α * κ₁ * CCL)) ^ 2 / cc ≤ c₁ * ccL / 8 := by
      rw [div_le_iff₀ ht.hcc]
      have h := mul_le_mul_of_nonneg_left hs1 hc₁.le
      nlinarith [h]
    have hd2 : 2 * (c₂ * (κ₂ * CCL)) ^ 2 / cc ≤ c₂ * ccL / 8 := by
      rw [div_le_iff₀ ht.hcc]
      have h := mul_le_mul_of_nonneg_left hs3 hc₂.le
      nlinarith [h]
    have hd3 : 2 * (c₂ * (κ₂ * CCL)) ^ 2 / (c₁ * ccL) ≤ c₂ * ccL / 8 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < c₁ * ccL)]
      have h := mul_le_mul_of_nonneg_left hs4 hc₂.le
      nlinarith [h]
    have hd4 : c₁ * (α * κ₁ * CCL) * X1 ≤ (c₁ * ccL / 8) * X1 := by
      have h : α * κ₁ * CCL ≤ ccL / 8 := by linarith [hs2]
      have h' : c₁ * (α * κ₁ * CCL) ≤ c₁ * ccL / 8 := by
        have := mul_le_mul_of_nonneg_left h hc₁.le
        linarith [this]
      exact mul_le_mul_of_nonneg_right h' hX1
    -- the two error terms, fully estimated
    have herr1 : c₁ * (CCL * Real.sqrt (Work.Spaces.HkSq α n (E1 α f)) * Real.sqrt X1)
        ≤ (cc / 8) * X0 + (c₁ * ccL / 4) * X1 := by
      have h4 : c₁ * (c₁ * (α * κ₁ * CCL) * X1) ≤ c₁ * ((c₁ * ccL / 8) * X1) :=
        mul_le_mul_of_nonneg_left hd4 hc₁.le
      calc c₁ * (CCL * Real.sqrt (Work.Spaces.HkSq α n (E1 α f)) * Real.sqrt X1)
          ≤ c₁ * ((α * κ₁ * CCL) * (Real.sqrt X0 * Real.sqrt X1) + (α * κ₁ * CCL) * X1) :=
            mul_le_mul_of_nonneg_left hn1' hc₁.le
        _ = (c₁ * (α * κ₁ * CCL)) * (Real.sqrt X0 * Real.sqrt X1)
              + c₁ * (α * κ₁ * CCL) * X1 := by ring
        _ ≤ ((cc / 8) * X0 + (2 * (c₁ * (α * κ₁ * CCL)) ^ 2 / cc) * X1)
              + (c₁ * ccL / 8) * X1 := add_le_add hp1 hd4
        _ ≤ ((cc / 8) * X0 + (c₁ * ccL / 8) * X1) + (c₁ * ccL / 8) * X1 := by
            have h3 := mul_le_mul_of_nonneg_right hd1 hX1
            linarith [h3]
        _ = (cc / 8) * X0 + (c₁ * ccL / 4) * X1 := by ring
    have herr2 : c₂ * (CCL * Real.sqrt (Work.Spaces.HkSq α n (E2 α f)) * Real.sqrt X2)
        ≤ (cc / 8) * X0 + (c₁ * ccL / 8) * X1 + (c₂ * ccL / 4) * X2 := by
      have h4 : (2 * (c₂ * (κ₂ * CCL)) ^ 2 / cc) * X2 ≤ (c₂ * ccL / 8) * X2 :=
        mul_le_mul_of_nonneg_right hd2 hX2
      have h5 : (2 * (c₂ * (κ₂ * CCL)) ^ 2 / (c₁ * ccL)) * X2 ≤ (c₂ * ccL / 8) * X2 :=
        mul_le_mul_of_nonneg_right hd3 hX2
      calc c₂ * (CCL * Real.sqrt (Work.Spaces.HkSq α n (E2 α f)) * Real.sqrt X2)
          ≤ c₂ * ((κ₂ * CCL) * (Real.sqrt X0 * Real.sqrt X2)
              + (κ₂ * CCL) * (Real.sqrt X1 * Real.sqrt X2)) :=
            mul_le_mul_of_nonneg_left hn2' hc₂.le
        _ = (c₂ * (κ₂ * CCL)) * (Real.sqrt X0 * Real.sqrt X2)
              + (c₂ * (κ₂ * CCL)) * (Real.sqrt X1 * Real.sqrt X2) := by ring
        _ ≤ ((cc / 8) * X0 + (2 * (c₂ * (κ₂ * CCL)) ^ 2 / cc) * X2)
              + ((c₁ * ccL / 8) * X1 + (2 * (c₂ * (κ₂ * CCL)) ^ 2 / (c₁ * ccL)) * X2) :=
            add_le_add hp2 hp3
        _ ≤ ((cc / 8) * X0 + (c₂ * ccL / 8) * X2)
              + ((c₁ * ccL / 8) * X1 + (c₂ * ccL / 8) * X2) := add_le_add
            (add_le_add le_rfl h4) (add_le_add le_rfl h5)
        _ = (cc / 8) * X0 + (c₁ * ccL / 8) * X1 + (c₂ * ccL / 4) * X2 := by ring
    -- the two lower bounds on the differentiated slots
    have hN1 : -(IP (E1 α f) (Work.Spaces.Dth f))
        ≤ CCL * Real.sqrt (Work.Spaces.HkSq α n (E1 α f)) * Real.sqrt X1 :=
      le_trans (neg_le_abs _) hS1
    have hN2 : -(IP (E2 α f) (Work.Spaces.Dz f))
        ≤ CCL * Real.sqrt (Work.Spaces.HkSq α n (E2 α f)) * Real.sqrt X2 :=
      le_trans (neg_le_abs _) hS2
    have hstep1 : c₁ * IP (Work.Spaces.Dth (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dth f)
        ≥ c₁ * (ccL * X1)
          - c₁ * (CCL * Real.sqrt (Work.Spaces.HkSq α n (E1 α f)) * Real.sqrt X1) := by
      rw [e₁]
      have h1 : c₁ * (ccL * X1)
          ≤ c₁ * IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)) (Work.Spaces.Dth f) :=
        mul_le_mul_of_nonneg_left hB1 hc₁.le
      have h2 : -(c₁ * (CCL * Real.sqrt (Work.Spaces.HkSq α n (E1 α f)) * Real.sqrt X1))
          ≤ c₁ * IP (E1 α f) (Work.Spaces.Dth f) := by
        have := mul_le_mul_of_nonneg_left hN1 hc₁.le
        linarith
      linarith
    have hstep2 : c₂ * IP (Work.Spaces.Dz (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dz f)
        ≥ c₂ * (ccL * X2)
          - c₂ * (CCL * Real.sqrt (Work.Spaces.HkSq α n (E2 α f)) * Real.sqrt X2) := by
      rw [e₂]
      have h1 : c₂ * (ccL * X2)
          ≤ c₂ * IP (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) (Work.Spaces.Dz f) :=
        mul_le_mul_of_nonneg_left hB2 hc₂.le
      have h2 : -(c₂ * (CCL * Real.sqrt (Work.Spaces.HkSq α n (E2 α f)) * Real.sqrt X2))
          ≤ c₂ * IP (E2 α f) (Work.Spaces.Dz f) := by
        have := mul_le_mul_of_nonneg_left hN2 hc₂.le
        linarith
      linarith
    have hIP : IP (Work.Coercivity.LGammaT α f) f
          + c₁ * IP (Work.Spaces.Dth (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dth f)
          + c₂ * IP (Work.Spaces.Dz (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dz f)
        ≥ cc * X0 + c₁ * ccL * X1 + c₂ * ccL * X2
          - (c₁ * (CCL * Real.sqrt (Work.Spaces.HkSq α n (E1 α f)) * Real.sqrt X1)
              + c₂ * (CCL * Real.sqrt (Work.Spaces.HkSq α n (E2 α f)) * Real.sqrt X2)) := by
      linarith [hA, hstep1, hstep2]
    have hsurv : min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) * (X0 + X1 + X2)
        ≤ cc * X0 + c₁ * ccL * X1 + c₂ * ccL * X2
          - (c₁ * (CCL * Real.sqrt (Work.Spaces.HkSq α n (E1 α f)) * Real.sqrt X1)
              + c₂ * (CCL * Real.sqrt (Work.Spaces.HkSq α n (E2 α f)) * Real.sqrt X2)) := by
      have h0 : min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) ≤ 3 * cc / 4 :=
        min_le_left _ _
      have h1 : min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4))
          ≤ 5 * c₁ * ccL / 8 := le_trans (min_le_right _ _) (min_le_left _ _)
      have h2 : min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4))
          ≤ 3 * c₂ * ccL / 4 := le_trans (min_le_right _ _) (min_le_right _ _)
      have e0 : min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) * X0
          ≤ (3 * cc / 4) * X0 := mul_le_mul_of_nonneg_right h0 hX0
      have e1' : min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) * X1
          ≤ (5 * c₁ * ccL / 8) * X1 := mul_le_mul_of_nonneg_right h1 hX1
      have e2' : min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) * X2
          ≤ (3 * c₂ * ccL / 4) * X2 := mul_le_mul_of_nonneg_right h2 hX2
      have hexp : min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4))
            * (X0 + X1 + X2)
          = min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) * X0
            + min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) * X1
            + min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) * X2 := by ring
      rw [hexp]
      linarith [e0, e1', e2', herr1, herr2]
    have hYD : Y ≤ D * (X0 + X1 + X2) := by
      have h := hnormD f hf
      rw [hYdef, hX0def, hX1def, hX2def]
      exact h
    have hscale : min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) / D * Y
        ≤ min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) * (X0 + X1 + X2) := by
      have hc0 : 0 ≤ min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) / D :=
        le_of_lt hcc'
      calc min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) / D * Y
          ≤ min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4)) / D
              * (D * (X0 + X1 + X2)) := mul_le_mul_of_nonneg_left hYD hc0
        _ = min (3 * cc / 4) (min (5 * c₁ * ccL / 8) (3 * c₂ * ccL / 4))
              * (X0 + X1 + X2) := by field_simp
    rw [Work.Coercivity.HkIPStep]
    exact le_trans hscale (le_trans hsurv hIP)

end Work.FTS.CoercivityFix.Transfer
