import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB6Est.lhyR3Integral
import Submission.Work.BoseB6Est.reg_far
import Submission.Work.BoseB6Est.reg_mid
import Submission.Work.BoseB6Est.reg_small
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6-est — the `I₁` estimate `fsI1_le` (FS `eq:LebesgueError-Total`)

FS's estimate for the scaled Bogoliubov zero-point integral

  `I₁ = ∫_{ℝ³} [α − √(α²−β²) − β²/(2t²)] dt`,  `α = τ̃ + β`,

at FS's parameters: `fsI1 K εT c₁ c₂ ≤ −lhyValue(8π) + 10⁶·ε(μ,ρ_z)`.

Radial strategy (`eq:LebesgueError-Total`).  `fsI1 = 4π ∫₀^∞ r² G(r) dr` with

  `G(r) = (τ̃(r)+β(r)) − √((τ̃(r)+β(r))²−β(r)²) − β(r)²/(2r²) = gFun (τ̃ r) (β r) r`

and the model integrand `G₀ = fsG0R = lhyRad (8π)` has `4π ∫₀^∞ r² G₀ = −lhyValue(8π)`.
`G − G₀` is a *two-variable increment* of `gFun` — in `τ` (from `τ̃(r)` to `r²`)
and in `b` (from `β(r)` to `8π`) — and each increment is estimated by the
sibling modules:

* `gFun_tau_diff` (`GTau`): the `τ`-increment, `≤ 2b²(r²−τ)/(r²(2τ+b))`.  On the
  far region `4 ≤ r` this is `O((c₁ + ε_Tc₂)/r)` once `τ̃(r) ≥ r²/2`
  (`fsTau_ge_half`) and `r² − τ̃(r) ≤ 2r(c₁+ε_Tc₂)` (`radialTauDiffBound`); on the
  bounded ones it is `O(ε_T r² + (c₁+ε_Tc₂) r)`;
* `gFun_beta_diff_lin`, `gFun_beta_diff_sq` (`GBeta`): the `b`-increment, linear
  in `max(b,8π)|b − 8π|/r²` and quadratic in `2(max(b,8π))²|b − 8π|/r⁴`, with
  `|β(r) − 8π| ≤ η r` (`FsKernel.close`) and `β ≤ 8π+1` (`beta_close_bounds`);
* beyond the kernel's cutoff, `G = 0` and only `G₀` contributes
  (`tailIntegralBound`), bounded by `hTtail`.

The four regions — `(0,c₁]` (`reg_small`), `(c₁, min 4 T]` (`reg_mid`),
`(min 4 T, T]` (`reg_far`) and `(T,∞)` (`tailIntegralBound`) — are pairwise
disjoint because `c₁ ≤ 1 ≤ min 4 K.T`, and cover `(0,∞)`; their bounds
(`31ε`, `3900ε`, `2750ε`, `ε`) add up to `6682ε ≤ 10⁶ε/(4π)`, which is
`eq:LebesgueError-Total` at FS's parameters.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseB6Est

local notation "ℝ³" => Fin 3 → ℝ

/-! ## 1. The radial reduction -/

theorem fsI1Integrand_eq (K : FsKernel) (εT c1 c2 : ℝ) :
    Work.BoseB6Est.fsI1Integrand K εT c1 c2
      = fun t : ℝ³ => fsGR K εT c1 c2 (nrm t) := rfl

/-- **The radial reduction of `fsI1`:** `fsI1 = 4π ∫₀^∞ r² G(r) dr`. -/
theorem fsI1_eq_radial (K : FsKernel) (εT c1 c2 : ℝ) :
    fsI1 K εT c1 c2
      = 4 * Real.pi * ∫ r in Set.Ioi (0 : ℝ), (r ^ 2 * fsGR K εT c1 c2 r) := by
  rw [fsI1, fsI1Integrand_eq]
  exact Work.BoseBox.integral_eucNorm3_fun (g := fsGR K εT c1 c2)

/-- **The model integral, radial form:** `4π ∫₀^∞ r² G₀ = −lhyValue(8π)`. -/
theorem fsG0R_integral :
    4 * Real.pi * (∫ r in Set.Ioi (0 : ℝ), (r ^ 2 * fsG0R r))
      = -Work.BoseB6.lhyValue (8 * Real.pi) := by
  rw [← lhyR3Integral]
  rw [show (fun x : ℝ³ => Work.BoseB6.lhyR3 (8 * Real.pi) x)
        = fun x => fsG0R (nrm x) from funext (fun x => lhyR3_eq_fsG0R x)]
  exact (Work.BoseBox.integral_eucNorm3_fun (g := fsG0R)).symm

/-! ## 2. The region decomposition and the main estimate -/

/-- **FS `lem:BogIntegral`, the assembled `I₁` estimate.**  The four region
bounds of the sibling modules plus the tail bound add up to
`6682·ε ≤ 10⁶·ε/(4π)`. -/
theorem fsI1_main (K : FsKernel) {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) :
    4 * Real.pi * (∫ r in Set.Ioi (0:ℝ), (r ^ 2 * (fsGR K εT c1 c2 r - fsG0R r)))
      ≤ 10 ^ 6 * Work.BoseB6.lhyEps a R εT Kl s d μ := by
  set eps := Work.BoseB6.lhyEps a R εT Kl s d μ with hepsdef
  have hε0 : 0 ≤ eps := by rw [hepsdef]; exact FsI1Regime.lhyEps_nonneg h
  have hε1' : εT ≤ 1 := by linarith [h.hε1]
  have hc1one : c1 ≤ 1 := FsI1Regime.c1_le_one h
  have h1m : (1:ℝ) ≤ min 4 K.T := le_min (by norm_num) h.hT1
  have hc1m : c1 ≤ min 4 K.T := le_trans hc1one h1m
  set f : ℝ → ℝ := fun r => r ^ 2 * (fsGR K εT c1 c2 r - fsG0R r) with hfdef
  have hf : IntegrableOn f (Set.Ioi 0) := by
    rw [hfdef]
    have h1 : IntegrableOn (fun r : ℝ => r ^ 2 * fsGR K εT c1 c2 r - r ^ 2 * fsG0R r)
        (Set.Ioi 0) :=
      (integrableOn_r2_fsGR K h.hε0 hε1' h.hηT).sub integrableOn_r2_fsG0R
    refine (MeasureTheory.integrableOn_congr_fun
      (f := fun r : ℝ => r ^ 2 * fsGR K εT c1 c2 r - r ^ 2 * fsG0R r)
      (g := fun r : ℝ => r ^ 2 * (fsGR K εT c1 c2 r - fsG0R r))
      (fun r _ => by ring) measurableSet_Ioi).mp h1
  -- the cover
  have hunion : Set.Ioi (0:ℝ)
      = Set.Ioc 0 c1 ∪ (Set.Ioc c1 (min 4 K.T) ∪ (Set.Ioc (min 4 K.T) K.T ∪ Set.Ioi K.T)) := by
    ext r
    simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro hr
      by_cases h1 : r ≤ c1
      · exact Or.inl ⟨hr, h1⟩
      · push_neg at h1
        by_cases h2 : r ≤ min 4 K.T
        · exact Or.inr (Or.inl ⟨h1, h2⟩)
        · push_neg at h2
          by_cases h3 : r ≤ K.T
          · exact Or.inr (Or.inr (Or.inl ⟨h2, h3⟩))
          · exact Or.inr (Or.inr (Or.inr (not_le.mp h3)))
    · rintro (⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | h3)
      · exact h1
      · exact lt_of_le_of_lt h.hc1 h1
      · exact lt_trans (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) h1m) h1
      · exact lt_of_le_of_lt K.Tnn h3
  -- pairwise disjointness (`c₁ ≤ 1 ≤ min 4 T`)
  have hd1 : Disjoint (Set.Ioc (0:ℝ) c1)
      (Set.Ioc c1 (min 4 K.T) ∪ (Set.Ioc (min 4 K.T) K.T ∪ Set.Ioi K.T)) := by
    rw [Set.disjoint_left]
    intro r h1 h2
    rw [Set.mem_union] at h2
    rcases h2 with h2 | h2
    · exact absurd h1.2 (not_le.mpr h2.1)
    · rw [Set.mem_union] at h2
      rcases h2 with h2 | h2
      · have h3 : c1 < r := lt_of_le_of_lt hc1m h2.1
        exact absurd h1.2 (not_le.mpr h3)
      · have h3 : min 4 K.T < r :=
          lt_of_le_of_lt (min_le_right (4:ℝ) K.T) (Set.mem_Ioi.mp h2)
        have h4 : c1 < r := lt_of_le_of_lt hc1m h3
        exact absurd h1.2 (not_le.mpr h4)
  have hd2 : Disjoint (Set.Ioc c1 (min 4 K.T)) (Set.Ioc (min 4 K.T) K.T ∪ Set.Ioi K.T) := by
    rw [Set.disjoint_left]
    intro r h1 h2
    rw [Set.mem_union] at h2
    rcases h2 with h2 | h2
    · exact absurd h1.2 (not_le.mpr h2.1)
    · have h3 : min 4 K.T < r :=
        lt_of_le_of_lt (min_le_right (4:ℝ) K.T) (Set.mem_Ioi.mp h2)
      exact absurd h1.2 (not_le.mpr h3)
  have hd3 : Disjoint (Set.Ioc (min 4 K.T) K.T) (Set.Ioi K.T) := by
    rw [Set.disjoint_left]
    intro r h1 h2
    exact absurd h1.2 (not_le.mpr (Set.mem_Ioi.mp h2))
  -- integrability on the pieces
  have hIA : IntegrableOn f (Set.Ioc 0 c1) :=
    hf.mono_set (fun r hr => hr.1)
  have hIB : IntegrableOn f (Set.Ioc c1 (min 4 K.T)) :=
    hf.mono_set (fun r hr => lt_of_le_of_lt h.hc1 hr.1)
  have hIC : IntegrableOn f (Set.Ioc (min 4 K.T) K.T) :=
    hf.mono_set (fun r hr =>
      lt_trans (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) h1m) hr.1)
  have hID : IntegrableOn f (Set.Ioi K.T) :=
    hf.mono_set (fun r hr => lt_of_le_of_lt K.Tnn hr)
  have hICD : IntegrableOn f (Set.Ioc (min 4 K.T) K.T ∪ Set.Ioi K.T) := hIC.union hID
  have hIBCD : IntegrableOn f
      (Set.Ioc c1 (min 4 K.T) ∪ (Set.Ioc (min 4 K.T) K.T ∪ Set.Ioi K.T)) := hIB.union hICD
  have hsplit : (∫ r in Set.Ioi (0:ℝ), f r)
      = (∫ r in Set.Ioc 0 c1, f r)
        + ((∫ r in Set.Ioc c1 (min 4 K.T), f r)
          + ((∫ r in Set.Ioc (min 4 K.T) K.T, f r) + (∫ r in Set.Ioi K.T, f r))) := by
    rw [hunion,
      MeasureTheory.setIntegral_union hd1
        (measurableSet_Ioc.union (measurableSet_Ioc.union measurableSet_Ioi)) hIA hIBCD,
      MeasureTheory.setIntegral_union hd2 (measurableSet_Ioc.union measurableSet_Ioi) hIB hICD,
      MeasureTheory.setIntegral_union hd3 measurableSet_Ioi hIC hID]
  -- the four pieces
  have hp1 : (∫ r in Set.Ioc 0 c1, f r) ≤ 31 * eps := by
    rw [hfdef, hepsdef]; exact reg_small K h
  have hp2 : (∫ r in Set.Ioc c1 (min 4 K.T), f r) ≤ 3900 * eps := by
    rw [hfdef, hepsdef]; exact reg_mid K h
  have hp3 : (∫ r in Set.Ioc (min 4 K.T) K.T, f r) ≤ 2750 * eps := by
    rw [hfdef, hepsdef]; exact reg_far K h
  have hp4 : (∫ r in Set.Ioi K.T, f r) ≤ eps := by
    have hTpos : 0 < K.T := FsI1Regime.T_pos h
    have h1 : (∫ r in Set.Ioi K.T, f r) ≤ (8 * Real.pi) ^ 3 / (2 * K.T) := by
      rw [hfdef]; exact tailIntegralBound K h.hε0 hε1' hTpos
    have h2 : (8 * Real.pi) ^ 3 / (2 * K.T) ≤ eps := by
      have h4 : 4 * Real.pi * (8 * Real.pi) ^ 3 / (2 * K.T) ≤ eps := by
        rw [hepsdef]; exact h.hTtail
      have h5 : (1 : ℝ) ≤ 4 * Real.pi := by nlinarith [Real.pi_gt_three]
      have h6 : (0 : ℝ) ≤ (8 * Real.pi) ^ 3 / (2 * K.T) := by positivity
      have h7 : (8 * Real.pi) ^ 3 / (2 * K.T) ≤ 4 * Real.pi * (8 * Real.pi) ^ 3 / (2 * K.T) := by
        calc (8 * Real.pi) ^ 3 / (2 * K.T) = (8 * Real.pi) ^ 3 / (2 * K.T) * 1 := (mul_one _).symm
          _ ≤ (8 * Real.pi) ^ 3 / (2 * K.T) * (4 * Real.pi) :=
              mul_le_mul_of_nonneg_left h5 h6
          _ = 4 * Real.pi * (8 * Real.pi) ^ 3 / (2 * K.T) := by ring
      linarith [h4, h7]
    linarith [h1, h2]
  have htot : (∫ r in Set.Ioi (0:ℝ), f r) ≤ (31 + (3900 + (2750 + 1))) * eps := by
    rw [hsplit]; linarith [hp1, hp2, hp3, hp4]
  have hfinal : 4 * Real.pi * (∫ r in Set.Ioi (0:ℝ), f r)
      ≤ 4 * Real.pi * (6682 * eps) := by
    have h1 : (31 + (3900 + (2750 + 1)) : ℝ) * eps ≤ 6682 * eps := by
      norm_num
    exact mul_le_mul_of_nonneg_left (le_trans htot h1) (by positivity)
  have hnum : 4 * Real.pi * (6682 * eps) ≤ 10 ^ 6 * eps := by
    have hπ : Real.pi ≤ 3.15 := Real.pi_lt_d2.le
    have h2 : (4 * Real.pi * 6682) * eps ≤ 10 ^ 6 * eps := by
      refine mul_le_mul_of_nonneg_right ?_ hε0
      nlinarith [hπ, Real.pi_pos]
    calc 4 * Real.pi * (6682 * eps) = (4 * Real.pi * 6682) * eps := by ring
      _ ≤ 10 ^ 6 * eps := h2
  linarith [hfinal, hnum]

/-! ## 3. The estimate in FS's form -/

/-- **FS `lem:BogIntegral` at FS's parameters** (`eq:LebesgueError-Total`):

  `I₁ ≤ −lhyValue(8π) + 10⁶·ε(μ,ρ_z)`.

Deliverable item 1 of this chapter: this removes the `hI1` hypothesis of node
B6's `lem_bogIntegral`. -/
theorem fsI1_le {K : FsKernel} {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) :
    fsI1 K εT c1 c2 ≤ -Work.BoseB6.lhyValue (8 * Real.pi)
      + 10 ^ 6 * Work.BoseB6.lhyEps a R εT Kl s d μ := by
  set eps := Work.BoseB6.lhyEps a R εT Kl s d μ with hepsdef
  have hε1' : εT ≤ 1 := by linarith [h.hε1]
  have hg1 : IntegrableOn (fun r : ℝ => r ^ 2 * fsGR K εT c1 c2 r) (Set.Ioi 0) :=
    integrableOn_r2_fsGR K h.hε0 hε1' h.hηT
  have hdiff : (∫ r in Set.Ioi (0:ℝ), (r ^ 2 * (fsGR K εT c1 c2 r - fsG0R r)))
      = (∫ r in Set.Ioi (0:ℝ), (r ^ 2 * fsGR K εT c1 c2 r))
        - (∫ r in Set.Ioi (0:ℝ), (r ^ 2 * fsG0R r)) := by
    have h1 : (fun r : ℝ => r ^ 2 * (fsGR K εT c1 c2 r - fsG0R r))
        = fun r : ℝ => r ^ 2 * fsGR K εT c1 c2 r - r ^ 2 * fsG0R r := by
      funext r; ring
    rw [h1]
    exact MeasureTheory.integral_sub hg1 integrableOn_r2_fsG0R
  have hB : (∫ r in Set.Ioi (0:ℝ), (r ^ 2 * fsG0R r))
      = (-Work.BoseB6.lhyValue (8 * Real.pi)) / (4 * Real.pi) := by
    rw [eq_div_iff (by positivity : (4 * Real.pi) ≠ 0), mul_comm]
    exact fsG0R_integral
  have hMain := fsI1_main K h
  have hle : (∫ r in Set.Ioi (0:ℝ), (r ^ 2 * (fsGR K εT c1 c2 r - fsG0R r)))
      ≤ (10 ^ 6 * eps) / (4 * Real.pi) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 4 * Real.pi), mul_comm]
    exact hMain
  rw [fsI1_eq_radial]
  have hsub : (∫ r in Set.Ioi (0:ℝ), (r ^ 2 * fsGR K εT c1 c2 r))
      = (∫ r in Set.Ioi (0:ℝ), (r ^ 2 * (fsGR K εT c1 c2 r - fsG0R r)))
        + (∫ r in Set.Ioi (0:ℝ), (r ^ 2 * fsG0R r)) := by
    rw [hdiff]; ring
  rw [hsub, hB]
  have hmul : 4 * Real.pi * ((∫ r in Set.Ioi (0:ℝ), (r ^ 2 * (fsGR K εT c1 c2 r - fsG0R r)))
        + (-Work.BoseB6.lhyValue (8 * Real.pi)) / (4 * Real.pi))
      ≤ 4 * Real.pi * ((10 ^ 6 * eps) / (4 * Real.pi)
        + (-Work.BoseB6.lhyValue (8 * Real.pi)) / (4 * Real.pi)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith [hle]
  have hsimp : 4 * Real.pi * ((10 ^ 6 * eps) / (4 * Real.pi)
        + (-Work.BoseB6.lhyValue (8 * Real.pi)) / (4 * Real.pi))
      = 10 ^ 6 * eps - Work.BoseB6.lhyValue (8 * Real.pi) := by
    field_simp
    ring
  linarith [hmul, hsimp]

/-! ## 4. FS's `eq:BogIntegral` display, with the `I₁` hypothesis discharged -/

/-- **FS's `eq:BogIntegral` display at FS's parameters, with the `I₁` hypothesis
discharged**: this is node B6's `lem_bogIntegral_lhyEps` fed with this module's
`fsI1_le`.  The only extra input is the box side `ℓ > 0` (every caller has it,
e.g. `FsZeroRegime.hℓ`); the numerical identity `½(2π)⁻³lhyValue(8π) = 4π·lhySharp`
is `Work.BoseB6.lhyValue_eight_pi`. -/
theorem fsBogIntegral_display {K : FsKernel} {a R ρz μ εT c1 c2 Kl s d ℓ : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) (hℓ : 0 < ℓ) :
    4 * Real.pi * Work.BoseB6.lhySharp * (ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3)) * ℓ ^ 3
        - (1 / 2) * (((2 * Real.pi) ^ 3)⁻¹) * ℓ ^ 3 * (ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3))
          * (10 ^ 6 * Work.BoseB6.lhyEps a R εT Kl s d μ)
      ≤ -(1 / 2) * (((2 * Real.pi) ^ 3)⁻¹) * ℓ ^ 3 * (ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3))
          * (fsI1 K εT c1 c2) := by
  have hconst : (1 / 2) * (((2 * Real.pi) ^ 3)⁻¹) * Work.BoseB6.lhyValue (8 * Real.pi)
      = 4 * Real.pi * Work.BoseB6.lhySharp := by
    rw [Work.BoseB6.lhyValue_eight_pi]
    have h2 : ((2 * Real.pi) ^ 3) ≠ 0 := by positivity
    field_simp
    ring
  exact Work.BoseB6.lem_bogIntegral_lhyEps h.hρz h.ha hℓ hconst (fsI1_le h)

end Work.BoseB6Est
