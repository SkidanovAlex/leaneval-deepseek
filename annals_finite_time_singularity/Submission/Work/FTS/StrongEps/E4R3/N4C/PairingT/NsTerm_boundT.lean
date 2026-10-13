/-
# `E4R3/N4C/PairingT/NsTerm_boundT` — the honest `N_*` term of the §8 assembly

This is the honest (`class-C` / open-quadrant) analogue of the `N_*` part of
`Work.FTS.Nonlinear.Assembly`: from the context `BlkCtxO` (the `N4ExtraH` interface, the honest
per-piece table `RowInputsTO`, and the constant bookkeeping) and the `μ`-bound

  `|μ| ≤ 4·C·(α + α^{-1}·X + α^{-5/2}·X²)`,   `X = Xn α g`,

the collapse `N_* μ (λ(μ)) g = N_*^{λ} μ g = μ (D_z g - g)` (`RowInputsTO.hNs`) together with the
lossless `D_z`-self-pairing (`N4ExtraH.dz`) and Cauchy–Schwarz (`N4ExtraH.cs`) give

  `|IP α (N_* μ (λ μ) g) g| ≤ 24·(K₀(C+1)·Pbd α (Xn α g))`.

The proof is the verbatim adaptation of the `N_*` block of `Nonlinear.Assembly`; the only
differences are that the smoothness of `D_z g` and of `g` comes from the honest table
(`RowInputsTO.hkDz` and `classC_hqo4`) and that the `μ`-bound is a hypothesis rather than a
consequence of the `L₁₂`-rows.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.N4C.PairingT.RowInputs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C.PairingT

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin
open Work.FTS.VocabO (HQo)
open Work.FTS.StrongEps.E4R3.N4C

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The `N_*` term** of the honest §8 assembly: `|IP α (N_* μ (λ μ) g) g| ≤ 24·K₀(C+1)·Pbd α X`. -/
theorem NsTerm_boundT {IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ}
    {α₂ Ct K₀ C C₀ α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn} {μ : ℝ}
    (h : Work.FTS.StrongEps.E4R3.N4C.BlkCtxO IP α₂ Ct K₀ C C₀ α g Φs Φg) (hμ1 : μ ≠ -1)
    (hμ4 : |μ| ≤ 4 * C * (α + α ^ (-(1 : ℝ)) * Work.FTS.Nonlin.Xn α g
      + α ^ (-(5 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)) :
    |IP α (Work.Construction.Nstar μ (Work.Construction.lamfun μ) g) g|
      ≤ 24 * (K₀ * (C + 1) * Work.FTS.Nonlin.Pbd α (Work.FTS.Nonlin.Xn α g)) := by
  set X := Work.FTS.Nonlin.Xn α g with hXdef
  have hE : N4ExtraH IP α₂ Ct := h.hE
  have hα : 0 < α := h.hα
  have hα1 : α ≤ 1 := h.hα1
  have hαIoc : α ∈ Set.Ioc 0 α₂ := h.hαIoc
  have hCt : 0 < Ct := h.hCt
  have hK₀Ct : Ct ≤ K₀ := h.hK₀Ct
  have hK₀pos : 0 < K₀ := lt_of_lt_of_le hCt hK₀Ct
  have hC : 0 < C := h.hC
  have hR : RowInputsTO IP α C g Φs Φg := h.hR
  have hg4 : HQo α 4 g := BlkCtxO.hg4 h
  have hkDz : GoodO α (Work.Spaces.Dz g) := hR.hkDz
  have hreg5 := BlkCtxO.hreg5 h
  have hX0 : 0 ≤ X := by rw [hXdef]; exact Work.Spaces.HkNorm_nonneg α 4 g
  have hPbd0 : 0 ≤ Work.FTS.Nonlin.Pbd α X := Pbd_nonneg hα.le hX0
  have hM0 : 0 ≤ α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2 := by
    have h1 : (0 : ℝ) ≤ α ^ (-(1 : ℝ)) * X :=
      mul_nonneg (Real.rpow_nonneg hα.le _) hX0
    have h2 : (0 : ℝ) ≤ α ^ (-(5 / 2 : ℝ)) * X ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hα.le _) (by positivity)
    linarith [hα.le]
  have hμ4X : |μ| ≤ 4 * C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) := by
    rw [hXdef]; exact hμ4
  -- ## the collapse `N_* μ (λ μ) g = μ (D_z g - g)`
  have hcollapse : Work.Construction.Nstar μ (Work.Construction.lamfun μ) g = NstarLam μ g := by
    funext z θ
    exact hR.hNs μ hμ1 z θ
  rw [hcollapse]
  have hdecomp : NstarLam μ g = (fun z θ => μ * Work.Spaces.Dz g z θ)
      + (fun z θ => (-μ) * g z θ) := by
    funext z θ
    simp only [NstarLam, Pi.add_apply]
    ring
  have hIPs : IP α (NstarLam μ g) g
      = μ * IP α (Work.Spaces.Dz g) g + (-μ) * IP α g g := by
    rw [hdecomp,
      hE.add α hαIoc (fun z θ => μ * Work.Spaces.Dz g z θ) (fun z θ => (-μ) * g z θ) g
        (goodO_const_mul μ hkDz) (goodO_const_mul (-μ) hg4) hg4,
      hE.smul α hαIoc μ (Work.Spaces.Dz g) g hkDz hg4,
      hE.smul α hαIoc (-μ) g g hg4 hg4]
  have hdz : |IP α (Work.Spaces.Dz g) g| ≤ Ct * X ^ 2 := hE.dz α hαIoc g hreg5
  have hgg : |IP α g g| ≤ Ct * X ^ 2 := by
    have h1 : |IP α g g| ≤ Ct * Work.FTS.Nonlin.Xn α g * Work.FTS.Nonlin.Xn α g :=
      hE.cs α hαIoc g g hg4 hg4
    have h2 : Ct * Work.FTS.Nonlin.Xn α g * Work.FTS.Nonlin.Xn α g = Ct * X ^ 2 := by
      rw [hXdef]; ring
    linarith [h1, h2.le, h2.ge]
  have htri : |IP α (NstarLam μ g) g| ≤ |μ| * (|IP α (Work.Spaces.Dz g) g| + |IP α g g|) := by
    rw [hIPs]
    have he : μ * IP α (Work.Spaces.Dz g) g + (-μ) * IP α g g
        = μ * (IP α (Work.Spaces.Dz g) g - IP α g g) := by ring
    rw [he, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg μ)
    simpa [sub_eq_add_neg] using abs_add_le (IP α (Work.Spaces.Dz g) g) (-(IP α g g))
  -- ## the `μ`-bound, turned into a `Pbd`-bound
  have hmid : |μ| * (|IP α (Work.Spaces.Dz g) g| + |IP α g g|)
      ≤ 8 * K₀ * C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) * X ^ 2 := by
    have h1 : |IP α (Work.Spaces.Dz g) g| + |IP α g g| ≤ 2 * Ct * X ^ 2 := by
      have h := add_le_add hdz hgg
      linarith [h]
    have h2 : |μ| * (|IP α (Work.Spaces.Dz g) g| + |IP α g g|)
        ≤ (4 * C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2))
          * (2 * Ct * X ^ 2) :=
      mul_le_mul hμ4X h1 (by positivity) (by positivity)
    have h3 : (4 * C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2))
          * (2 * Ct * X ^ 2)
        ≤ 8 * K₀ * C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) * X ^ 2 := by
      have h8 : (0 : ℝ) ≤ 4 * C
          * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) * X ^ 2 :=
        mul_nonneg (mul_nonneg (by positivity) hM0) (by positivity)
      nlinarith [hK₀Ct, h8, hC.le]
    linarith [h2, h3]
  have hm1 : α * X ^ 2 ≤ Work.FTS.Nonlin.Pbd α X := by
    have hαle_sqrt : α ≤ Real.sqrt α := by
      have hle1 : Real.sqrt α ≤ 1 := Real.sqrt_le_one.mpr hα1
      have hsq : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα.le
      nlinarith [Real.sqrt_nonneg α, hle1, hsq]
    exact le_trans (mul_le_mul_of_nonneg_right hαle_sqrt (by positivity))
      (sqrt_mul_sq_le_Pbd hα hX0)
  have hm2 : α ^ (-(1 : ℝ)) * X ^ 3 ≤ Work.FTS.Nonlin.Pbd α X :=
    rpow_neg_one_mul_cube_le_Pbd hα hα1 hX0
  have hm3 : α ^ (-(5 / 2 : ℝ)) * X ^ 4 ≤ Work.FTS.Nonlin.Pbd α X := by
    rw [Work.FTS.Nonlin.Pbd]
    have h1 : (0 : ℝ) ≤ α ^ 2 * X := mul_nonneg (by positivity) hX0
    have h2 : (0 : ℝ) ≤ Real.sqrt α * X ^ 2 := mul_nonneg (Real.sqrt_nonneg α) (by positivity)
    have h3 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 3 :=
      mul_nonneg (Real.rpow_nonneg hα.le _) (by positivity)
    linarith
  have hfin : 8 * K₀ * C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) * X ^ 2
      ≤ 24 * (K₀ * (C + 1) * Work.FTS.Nonlin.Pbd α X) := by
    have hexp : 8 * K₀ * C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) * X ^ 2
        = 8 * K₀ * C * (α * X ^ 2 + α ^ (-(1 : ℝ)) * X ^ 3
            + α ^ (-(5 / 2 : ℝ)) * X ^ 4) := by ring
    have hsum : α * X ^ 2 + α ^ (-(1 : ℝ)) * X ^ 3 + α ^ (-(5 / 2 : ℝ)) * X ^ 4
        ≤ 3 * Work.FTS.Nonlin.Pbd α X := by linarith [hm1, hm2, hm3]
    have hsum' : 8 * K₀ * C * (α * X ^ 2 + α ^ (-(1 : ℝ)) * X ^ 3
          + α ^ (-(5 / 2 : ℝ)) * X ^ 4) ≤ 8 * K₀ * C * (3 * Work.FTS.Nonlin.Pbd α X) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    have h3P : 8 * K₀ * C * (3 * Work.FTS.Nonlin.Pbd α X)
        ≤ 24 * (K₀ * (C + 1) * Work.FTS.Nonlin.Pbd α X) := by
      have h1 : 8 * K₀ * C * (3 * Work.FTS.Nonlin.Pbd α X)
          = 24 * K₀ * C * Work.FTS.Nonlin.Pbd α X := by ring
      have h2 : 24 * (K₀ * (C + 1) * Work.FTS.Nonlin.Pbd α X)
          = 24 * K₀ * C * Work.FTS.Nonlin.Pbd α X + 24 * K₀ * Work.FTS.Nonlin.Pbd α X := by
        ring
      have h3 : (0 : ℝ) ≤ 24 * K₀ * Work.FTS.Nonlin.Pbd α X := by positivity
      linarith [h1.le, h1.ge, h2.le, h2.ge, h3]
    linarith [hexp.le, hexp.ge, hsum', h3P]
  exact le_trans htri (le_trans hmid hfin)

end Work.FTS.StrongEps.E4R3.N4C.PairingT
