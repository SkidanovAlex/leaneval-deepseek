import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.RB5FSFixAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/FarThreeQSlots.lean` — the provable slots of `FarThreeQ`

`Work.BoseFixR.FarThreeQ` (`Submission/Work/BoseFixR/FarThreeQ.lean`, FS §9's `eq:Rough0` +
`eq:Rough1` at the honest family) requires a `K₀`-free quantitative bound on `Ŵ₁` over the
high-momentum region `P_H` (`Σ_{k∈P_H} Ŵ₁(k)²/‖k‖² ≲ aℓ³`), which its hypotheses do not carry (see
`FINDING_FarThreeQ.md`).  This module proves the two other slots of the same group, for a general
`KzDatum` satisfying the view:

* `FarQ2exSlot`  — `⟨f, Q₂^ex f⟩ ≥ −32πρ(a v)·16𝓜·‖f‖²`
  (`Ŵ₁ω`-row at `k = 0`, the view's Bessel conjunct `Cn ≤ 16`, the window `⟨T.N⟩ ≤ 𝓜‖f‖²`);
* `FarLinOpSlot` — `|⟨f, T.linOpT f⟩| ≤ 2·16π(a v)·ρ√(ρℓ³)·(Σ_s|χ̂²_s|)·√𝓜·‖f‖²`
  (Cauchy–Schwarz in the Fock form against the window, `Σ_s‖ã_s f‖² ≤ ⟨T.N f, f⟩ ≤ 𝓜‖f‖²`);

together with the assembly (`farThreeQ_of_slots`): the requested conclusion follows from the three
slot bounds and the single scalar inequality `A + B + C ≤ (7/8)·ErrRes`.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox
open Work.BoseBoxFix Work.BoseBoxFock Work.BoseB7 Work.BoseB7A

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. Extractors of the view -/

/-- The Bessel conjunct of `RViewFS`: `∃ Cn ≤ 16`, `⟨Σ_k nₖ g, g⟩ ≤ Cn⟨T.N g, g⟩`. -/
lemma view_bessel {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {μ : ℝ}
    (D : KzDatum) (hview : D.viewFS v h μ) :
    ∃ Cn : ℝ, 0 ≤ Cn ∧ Cn ≤ 16 ∧ ∀ g : D.F.H,
      D.F.bp ((∑ k : D.Mode, D.F.nOp k) g) g ≤ Cn * D.F.bp (D.T.N g) g := by
  unfold KzDatum.viewFS RViewFS at hview
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hB, -⟩ := hview
  exact hB

/-- The Bessel conjunct at the honest family (the form used by the far-leg assembly). -/
lemma honest_bessel {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {μ : ℝ}
    {fc fu : LowCut} {HM : ∀ μ : ℝ, HonestModes v μ}
    (hview : (HonestBoxFam v h fc fu HM μ).viewFS v h μ) :
    ∃ Cn : ℝ, 0 ≤ Cn ∧ Cn ≤ 16 ∧ ∀ g : (HonestBoxFam v h fc fu HM μ).F.H,
      (HonestBoxFam v h fc fu HM μ).F.bp
          ((∑ k : Lab (HM μ).N, (HonestBoxFam v h fc fu HM μ).F.nOp k) g) g
        ≤ Cn * (HonestBoxFam v h fc fu HM μ).F.bp ((HonestBoxFam v h fc fu HM μ).T.N g) g :=
  view_bessel _ hview

/-- `0 ≤ 𝓜` (from `FSParamsView`). -/
lemma view_bigM_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {μ : ℝ}
    (D : KzDatum) (hview : D.viewFS v h μ) : 0 ≤ D.E.bigM := by
  unfold KzDatum.viewFS RViewFS at hview
  obtain ⟨hFSP, -⟩ := hview
  exact le_trans zero_le_one (Classical.choice hFSP).one_le_bigM

/-- `0 < ℓ` (from the view's `ell`-pin and FS's parameter choice). -/
lemma view_ell_pos {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {μ : ℝ}
    (D : KzDatum) (hμ : 0 < μ) (hav : 0 < a v) (hview : D.viewFS v h μ) : 0 < D.E.ell := by
  unfold KzDatum.viewFS RViewFS at hview
  obtain ⟨-, -, -, hell, -⟩ := hview
  have hdil : 0 < dil v μ := by unfold dil; positivity
  rw [hell, ell, sideAt]
  refine Work.BoseBox.boxSide_pos hμ hav ?_
  simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
  exact Work.BoseBox.fsXp_pos hdil

/-- `KzEnvAt`'s derived density is the density it is named after: `(KzEnvAt E ρ).rho = ρ`. -/
lemma view_rho_KzEnvAt {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {μ : ℝ}
    (D : KzDatum) (hμ : 0 < μ) (hav : 0 < a v) (hview : D.viewFS v h μ)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (KzEnvAt D.E ρ).rho = ρ := by
  have hℓpos := view_ell_pos D hμ hav hview
  rw [Work.BoseB7.Q3Env.rho, Work.BoseB7.rhoZ, KzEnvAt,
    Real.sq_sqrt (mul_nonneg hρ (pow_nonneg (le_of_lt hℓpos) 3))]
  rw [div_eq_iff (pow_ne_zero 3 (ne_of_gt hℓpos))]

/-! ## 1. The `Q₂^ex` slot -/

/-- **The `Q₂^ex` slot of the far leg.**  `Q₂^ex` is diagonal, so no `K₀`-row is needed: the
`Ŵ₁ω`-bound at each mode, the view's Bessel conjunct (`Cn ≤ 16`) and the window suffice. -/
theorem FarQ2exSlot {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {μ : ℝ}
    (D : KzDatum) (hav : 0 < BoseGases.a v) (hμ : 0 < μ) (hview : D.viewFS v h μ)
    (hW1o : ∀ k : D.Mode, |D.E.W1omega k| ≤ 16 * Real.pi * BoseGases.a v)
    (hW1o0 : |D.E.W1omega0| ≤ 16 * Real.pi * BoseGases.a v)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (f : D.F.H) (hf : D.T.NWindow D.E.bigM f) :
    -((32 * Real.pi * ρ * BoseGases.a v) * (16 * D.E.bigM)) * D.F.normSq f
      ≤ D.F.qw f (D.F.Q2ex (KzEnvAt D.E ρ)) := by
  obtain ⟨Cn, hCn0, hCn16, hCn⟩ := view_bessel D hview
  have hMnn : 0 ≤ D.E.bigM := view_bigM_nonneg D hview
  have hns : 0 ≤ D.F.normSq f := D.F.normSq_nonneg f
  have hTN : D.F.bp (D.T.N f) f ≤ D.E.bigM * D.F.normSq f := NWindow_bp_N_le D.F D.T hMnn hf
  -- the total χ-mode occupation
  have hTot : D.F.bp ((∑ k : D.Mode, D.F.nOp k) f) f ≤ 16 * D.E.bigM * D.F.normSq f := by
    refine le_trans (hCn f) ?_
    calc Cn * D.F.bp (D.T.N f) f ≤ Cn * (D.E.bigM * D.F.normSq f) :=
          mul_le_mul_of_nonneg_left hTN hCn0
      _ ≤ 16 * (D.E.bigM * D.F.normSq f) :=
          mul_le_mul_of_nonneg_right hCn16 (mul_nonneg hMnn hns)
      _ = 16 * D.E.bigM * D.F.normSq f := by ring
  -- each summand is bounded below
  have hnnk : ∀ k : D.Mode, 0 ≤ D.F.bp (D.F.nOp k f) f := by
    intro k
    rw [FockData.nOp, LinearMap.comp_apply, FockData.aDag_adjoint]
    exact D.F.bp_nonneg _
  have hpoint : ∀ k ∈ Work.BoseB7.excited D.Mode,
      -((32 * Real.pi * ρ * BoseGases.a v)) * D.F.bp (D.F.nOp k f) f
        ≤ (ρ * (D.E.W1omega k + D.E.W1omega0)) * D.F.bp (D.F.nOp k f) f := by
    intro k _
    have h1 := abs_le.mp (hW1o k)
    have h2 := abs_le.mp hW1o0
    have hc : -(32 * Real.pi * ρ * BoseGases.a v) ≤ ρ * (D.E.W1omega k + D.E.W1omega0) := by
      nlinarith [h1.1, h1.2, h2.1, h2.2, hρ, Real.pi_pos, hav.le]
    exact mul_le_mul_of_nonneg_right hc (hnnk k)
  -- the diagonal decomposition of `Q₂^ex`
  have hdiag : D.F.qw f (D.F.Q2ex (KzEnvAt D.E ρ))
      = ∑ k ∈ Work.BoseB7.excited D.Mode,
          (ρ * (D.E.W1omega k + D.E.W1omega0)) * D.F.bp (D.F.nOp k f) f := by
    rw [FockData.Q2ex, FockData.qw, view_rho_KzEnvAt D hμ hav hview ρ hρ]
    simp only [KzEnvAt, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
  -- the sum of the individual bounds
  have hsum1 : -((32 * Real.pi * ρ * BoseGases.a v))
        * (∑ k ∈ Work.BoseB7.excited D.Mode, D.F.bp (D.F.nOp k f) f)
      ≤ ∑ k ∈ Work.BoseB7.excited D.Mode,
          (ρ * (D.E.W1omega k + D.E.W1omega0)) * D.F.bp (D.F.nOp k f) f := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hpoint
  -- compare the excited sum with the full sum
  have hsub : (∑ k ∈ Work.BoseB7.excited D.Mode, D.F.bp (D.F.nOp k f) f)
      ≤ ∑ k : D.Mode, D.F.bp (D.F.nOp k f) f :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun k _ _ => hnnk k)
  have hfull : (∑ k : D.Mode, D.F.bp (D.F.nOp k f) f)
      = D.F.bp ((∑ k : D.Mode, D.F.nOp k) f) f := by
    simp only [map_sum, LinearMap.sum_apply]
  have hcneg : -(32 * Real.pi * ρ * BoseGases.a v) ≤ 0 := by
    nlinarith [Real.pi_pos, mul_nonneg hρ hav.le]
  have hstep1 : -((32 * Real.pi * ρ * BoseGases.a v))
        * (∑ k : D.Mode, D.F.bp (D.F.nOp k f) f)
      ≤ -((32 * Real.pi * ρ * BoseGases.a v))
        * (∑ k ∈ Work.BoseB7.excited D.Mode, D.F.bp (D.F.nOp k f) f) :=
    mul_le_mul_of_nonpos_left hsub hcneg
  have hstep2 : -((32 * Real.pi * ρ * BoseGases.a v)) * (16 * D.E.bigM * D.F.normSq f)
      ≤ -((32 * Real.pi * ρ * BoseGases.a v))
        * (∑ k : D.Mode, D.F.bp (D.F.nOp k f) f) := by
    rw [hfull]
    exact mul_le_mul_of_nonpos_left hTot hcneg
  rw [hdiag]
  linarith [hstep1, hstep2, hsum1]

/-! ## 2. The linear-word (`linOpT`) slot -/

/-- `0 ≤ τ̃` (`Work.BoseBoxFock.tauProf ≥ 0`, from `exists_tauProf`). -/
lemma tauProf_nonneg' (r : ℝ) : 0 ≤ Work.BoseBoxFock.tauProf r := by
  have h := Work.BoseBoxFock.tauProf_spec.2.2.1 r
  linarith [sq_nonneg (max 0 (r - 2))]

/-- The view's `ε_T`-pin: `0 ≤ ε_T ≤ 1` (from `FSParamsView`). -/
lemma view_eT_bounds {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {μ : ℝ}
    (D : KzDatum) (hview : D.viewFS v h μ) : 0 ≤ D.E.eT ∧ D.E.eT ≤ 1 := by
  unfold KzDatum.viewFS RViewFS at hview
  obtain ⟨hFSP, -⟩ := hview
  have hv := Classical.choice hFSP
  refine ⟨?_, ?_⟩
  · rw [hv.eT_eq]; exact (Work.BoseBox.fsXp_pos hv.t_pos).le
  · rw [hv.eT_eq]
    exact Work.BoseBox.fsXp_le_one hv.t_pos hv.t_le_one (by norm_num)

/-- `0 ≤ τ_k` at a view-satisfying datum (the `τ`-pin is the smoothed `τ̃ ≥ 0`). -/
lemma view_tau_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {μ : ℝ}
    (D : KzDatum) (hview : D.viewFS v h μ) (k : D.Mode) : 0 ≤ D.E.tau k := by
  obtain ⟨heT0, heT1⟩ := view_eT_bounds D hview
  unfold KzDatum.viewFS RViewFS at hview
  obtain ⟨-, -, -, -, -, -, -, -, heTpin, -, -, htau, -⟩ := hview
  rw [htau, ← heTpin]
  simp only [Work.BoseBoxFock.tauSm]
  exact add_nonneg
    (mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (tauProf_nonneg' _))
    (mul_nonneg (mul_nonneg heT0 (sq_nonneg _)) (tauProf_nonneg' _))

/-- **The linear-word slot of the far leg** (FS §9 `eq:Rough0`'s `𝒬₁`-group, i.e. `T.linOpT`):
Cauchy–Schwarz in the Fock form against the window, with `Σ_s‖ã_s f‖² ≤ ⟨T.N f, f⟩ ≤ 𝓜‖f‖²`
from `TildeData.ta_le_N` and the window.  (`hchiSq1` is the `|χ̂²_s| ≤ 1` row, which the honest
family derives from the view's `hatChiSq`-pin and `Work.BoseK15.hatChi_le_one`.) -/
theorem FarLinOpSlot {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {μ : ℝ}
    (D : KzDatum) (hav : 0 < BoseGases.a v) (hμ : 0 < μ) (hview : D.viewFS v h μ)
    (hW1o0 : |D.E.W1omega0| ≤ 16 * Real.pi * BoseGases.a v)
    (hchiSq1 : ∀ k ∈ Work.BoseB7.excited D.Mode, |D.E.hatChiSq k| ≤ 1)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (f : D.F.H) (hf : D.T.NWindow D.E.bigM f) :
    |D.F.qw f (D.T.linOpT (KzEnvAt D.E ρ))|
      ≤ 2 * (16 * Real.pi * BoseGases.a v) * (ρ * Real.sqrt (ρ * D.E.ell ^ 3))
          * (∑ k ∈ Work.BoseB7.excited D.Mode, |D.E.hatChiSq k|)
          * Real.sqrt D.E.bigM * D.F.normSq f := by
  have hMnn : 0 ≤ D.E.bigM := view_bigM_nonneg D hview
  have hx : 0 ≤ D.F.normSq f := D.F.normSq_nonneg f
  have hTN : D.F.bp (D.T.N f) f ≤ D.E.bigM * D.F.normSq f := NWindow_bp_N_le D.F D.T hMnn hf
  set Y : ℝ := ∑ t ∈ Work.BoseB7.excited D.Mode, D.F.bp (D.T.ta t f) (D.T.ta t f) with hY
  have hYnn : 0 ≤ Y := by
    rw [hY]; exact Finset.sum_nonneg (fun t _ => D.F.bp_nonneg _)
  have hYle : Y ≤ D.E.bigM * D.F.normSq f := by
    have hne : ∀ s ∈ Work.BoseB7.excited D.Mode, s ≠ 0 := by
      intro s hs
      rw [Work.BoseB7.excited, Finset.mem_erase] at hs
      exact hs.1
    have hta := D.T.ta_le_N (Work.BoseB7.excited D.Mode) hne f
    have hsum : (∑ s ∈ Work.BoseB7.excited D.Mode, D.F.bp (D.T.taDag s (D.T.ta s f)) f)
        = D.F.bp ((∑ s ∈ Work.BoseB7.excited D.Mode, (D.T.taDag s ∘ₗ D.T.ta s)) f) f := by
      simp only [map_sum, LinearMap.sum_apply, LinearMap.comp_apply]
    rw [hY]
    calc (∑ s ∈ Work.BoseB7.excited D.Mode, D.F.bp (D.T.ta s f) (D.T.ta s f))
        = ∑ s ∈ Work.BoseB7.excited D.Mode, D.F.bp (D.T.taDag s (D.T.ta s f)) f := by
          refine Finset.sum_congr rfl (fun s _ => ?_)
          exact (D.T.taDag_adjoint s (D.T.ta s f) f).symm
      _ = D.F.bp ((∑ s ∈ Work.BoseB7.excited D.Mode, (D.T.taDag s ∘ₗ D.T.ta s)) f) f := hsum
      _ ≤ D.F.bp (D.T.N f) f := hta
      _ ≤ D.E.bigM * D.F.normSq f := hTN
  -- each coefficient is bounded by `2√Y√‖f‖²`
  have hper : ∀ s ∈ Work.BoseB7.excited D.Mode,
      |D.F.bp ((D.T.taDag s + D.T.ta s) f) f|
        ≤ 2 * Real.sqrt Y * Real.sqrt (D.F.normSq f) := by
    intro s hs
    have hy : D.F.bp (D.T.ta s f) (D.T.ta s f) ≤ Y := by
      rw [hY]
      refine Finset.single_le_sum (f := fun t => D.F.bp (D.T.ta t f) (D.T.ta t f))
        (fun t _ => D.F.bp_nonneg _) hs
    have hcs := Work.BoseB7.bp_cauchy_abs D.F (D.T.ta s f) f
    have h2 : D.F.bp ((D.T.taDag s + D.T.ta s) f) f = 2 * D.F.bp (D.T.ta s f) f := by
      rw [LinearMap.add_apply, map_add, LinearMap.add_apply, D.T.taDag_adjoint,
        D.F.bp_symm (D.T.ta s f) f]
      ring
    have hysq : Real.sqrt (D.F.bp (D.T.ta s f) (D.T.ta s f)) ≤ Real.sqrt Y :=
      Real.sqrt_le_sqrt hy
    have hcs' : |D.F.bp (D.T.ta s f) f|
        ≤ Real.sqrt (D.F.bp (D.T.ta s f) (D.T.ta s f)) * Real.sqrt (D.F.normSq f) := hcs
    rw [h2, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    nlinarith [hcs', hysq, Real.sqrt_nonneg (D.F.normSq f),
      abs_nonneg (D.F.bp (D.T.ta s f) f)]
  -- the sum of the coefficients
  set Sw : ℝ := ∑ k ∈ Work.BoseB7.excited D.Mode, |D.E.hatChiSq k| with hSw
  have hSwnn : 0 ≤ Sw := by
    rw [hSw]; exact Finset.sum_nonneg (fun k _ => abs_nonneg _)
  have hSbound : |∑ s ∈ Work.BoseB7.excited D.Mode,
        D.E.hatChiSq s * D.F.bp ((D.T.taDag s + D.T.ta s) f) f|
      ≤ Sw * (2 * Real.sqrt Y * Real.sqrt (D.F.normSq f)) := by
    calc |∑ s ∈ Work.BoseB7.excited D.Mode,
            D.E.hatChiSq s * D.F.bp ((D.T.taDag s + D.T.ta s) f) f|
        ≤ ∑ s ∈ Work.BoseB7.excited D.Mode,
            |D.E.hatChiSq s * D.F.bp ((D.T.taDag s + D.T.ta s) f) f| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ Work.BoseB7.excited D.Mode,
            |D.E.hatChiSq s| * (2 * Real.sqrt Y * Real.sqrt (D.F.normSq f)) := by
          refine Finset.sum_le_sum (fun s hs => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hper s hs) (abs_nonneg _)
      _ = Sw * (2 * Real.sqrt Y * Real.sqrt (D.F.normSq f)) := by
          rw [hSw, Finset.sum_mul]
  -- the value of the form
  have hval : D.F.qw f (D.T.linOpT (KzEnvAt D.E ρ))
      = (ρ * Real.sqrt (ρ * D.E.ell ^ 3) * D.E.W1omega0) *
          ∑ s ∈ Work.BoseB7.excited D.Mode,
            D.E.hatChiSq s * D.F.bp ((D.T.taDag s + D.T.ta s) f) f := by
    rw [TildeData.linOpT, FockData.qw, view_rho_KzEnvAt D hμ hav hview ρ hρ]
    simp only [KzEnvAt, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul, Finset.mul_sum]
  -- the coefficient of `linOpT`
  have hcc : |ρ * Real.sqrt (ρ * D.E.ell ^ 3) * D.E.W1omega0|
      ≤ 16 * Real.pi * BoseGases.a v * (ρ * Real.sqrt (ρ * D.E.ell ^ 3)) := by
    have hpos : 0 ≤ ρ * Real.sqrt (ρ * D.E.ell ^ 3) := mul_nonneg hρ (Real.sqrt_nonneg _)
    rw [abs_mul, abs_of_nonneg hpos]
    have h1 := abs_le.mp hW1o0
    nlinarith [h1.1, h1.2, hpos, Real.pi_pos, hav.le]
  -- the square-root comparison
  have hYsqrt : Real.sqrt Y ≤ Real.sqrt D.E.bigM * Real.sqrt (D.F.normSq f) := by
    calc Real.sqrt Y ≤ Real.sqrt (D.E.bigM * D.F.normSq f) := Real.sqrt_le_sqrt hYle
      _ = Real.sqrt D.E.bigM * Real.sqrt (D.F.normSq f) := Real.sqrt_mul hMnn _
  have hxx : Real.sqrt (D.F.normSq f) * Real.sqrt (D.F.normSq f) = D.F.normSq f := by
    rw [← sq, Real.sq_sqrt hx]
  have h2 : 2 * Real.sqrt Y * Real.sqrt (D.F.normSq f)
      ≤ 2 * Real.sqrt D.E.bigM * D.F.normSq f := by
    have hx0 : 0 ≤ Real.sqrt (D.F.normSq f) := Real.sqrt_nonneg _
    have h3 : Real.sqrt Y * Real.sqrt (D.F.normSq f)
        ≤ Real.sqrt D.E.bigM * Real.sqrt (D.F.normSq f) * Real.sqrt (D.F.normSq f) :=
      mul_le_mul_of_nonneg_right hYsqrt hx0
    calc 2 * Real.sqrt Y * Real.sqrt (D.F.normSq f)
        = 2 * (Real.sqrt Y * Real.sqrt (D.F.normSq f)) := by ring
      _ ≤ 2 * (Real.sqrt D.E.bigM * Real.sqrt (D.F.normSq f) * Real.sqrt (D.F.normSq f)) := by
          linarith
      _ = 2 * Real.sqrt D.E.bigM * D.F.normSq f := by rw [mul_assoc, hxx]; ring
  have hA0 : 0 ≤ 16 * Real.pi * BoseGases.a v * (ρ * Real.sqrt (ρ * D.E.ell ^ 3)) :=
    mul_nonneg (by positivity) (mul_nonneg hρ (Real.sqrt_nonneg _))
  have hbd : |ρ * Real.sqrt (ρ * D.E.ell ^ 3) * D.E.W1omega0|
        * |∑ s ∈ Work.BoseB7.excited D.Mode,
            D.E.hatChiSq s * D.F.bp ((D.T.taDag s + D.T.ta s) f) f|
      ≤ 2 * (16 * Real.pi * BoseGases.a v) * (ρ * Real.sqrt (ρ * D.E.ell ^ 3)) * Sw
          * Real.sqrt D.E.bigM * D.F.normSq f := by
    calc |ρ * Real.sqrt (ρ * D.E.ell ^ 3) * D.E.W1omega0|
          * |∑ s ∈ Work.BoseB7.excited D.Mode,
              D.E.hatChiSq s * D.F.bp ((D.T.taDag s + D.T.ta s) f) f|
        ≤ (16 * Real.pi * BoseGases.a v * (ρ * Real.sqrt (ρ * D.E.ell ^ 3)))
            * (Sw * (2 * Real.sqrt Y * Real.sqrt (D.F.normSq f))) :=
          mul_le_mul hcc hSbound (abs_nonneg _) hA0
      _ ≤ (16 * Real.pi * BoseGases.a v * (ρ * Real.sqrt (ρ * D.E.ell ^ 3)))
            * (Sw * (2 * Real.sqrt D.E.bigM * D.F.normSq f)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hSwnn) hA0
      _ = 2 * (16 * Real.pi * BoseGases.a v) * (ρ * Real.sqrt (ρ * D.E.ell ^ 3)) * Sw
            * Real.sqrt D.E.bigM * D.F.normSq f := by ring
  rw [hval, abs_mul]
  exact hbd

/-! ## 2b. The two slots at the honest family (the vocabulary of `FarThreeQ`) -/

/-- `FarQ2exSlot` at the honest family, in the vocabulary of the requested statement. -/
theorem FarQ2exSlotHonest {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ} {μ : ℝ}
    (hav : 0 < BoseGases.a v) (hμ : 0 < μ)
    (hview : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ)
    (hW1o : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega k|
          ≤ 16 * Real.pi * BoseGases.a v)
    (hW1o0 : |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega0|
          ≤ 16 * Real.pi * BoseGases.a v)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (f : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.H)
    (hf : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NWindow
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM f) :
    -((32 * Real.pi * ρ * BoseGases.a v) * (16 * Work.BoseFixR.bigMV v μ))
        * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f
      ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
          ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.Q2ex
            (Work.BoseFixR.KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ)) := by
  obtain ⟨-, -, -, hbigM, -, -, -, -, -, -⟩ := honest_view_basics hview
  have h := FarQ2exSlot (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ) hav hμ hview hW1o hW1o0
    ρ hρ f hf
  rwa [hbigM] at h

/-- `FarLinOpSlot` at the honest family, in the vocabulary of the requested statement. -/
theorem FarLinOpSlotHonest {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ} {μ : ℝ}
    (hav : 0 < BoseGases.a v) (hμ : 0 < μ)
    (hview : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ)
    (hW1o0 : |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega0|
          ≤ 16 * Real.pi * BoseGases.a v)
    (hchiSq1 : ∀ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChiSq k| ≤ 1)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (f : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.H)
    (hf : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NWindow
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM f) :
    |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
        ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.linOpT
          (Work.BoseFixR.KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ))|
      ≤ 2 * (16 * Real.pi * BoseGases.a v) * (ρ * Real.sqrt (ρ * Work.BoseFixR.ell v μ ^ 3))
          * (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
              |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChiSq k|)
          * Real.sqrt (Work.BoseFixR.bigMV v μ)
          * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f := by
  obtain ⟨-, -, hell, hbigM, -, -, -, -, -, -⟩ := honest_view_basics hview
  have h := FarLinOpSlot (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ) hav hμ hview hW1o0
    hchiSq1 ρ hρ f hf
  rw [hell, hbigM] at h
  exact h

/-! ## 3. The `ετ`-reserve, and the assembly of `FarThreeQ` -/

/-- The `ε`-split's kinetic reserve `Σ_k epsFar·τ_k·n_k` is nonnegative (the `τ`-pin is the
smoothed `τ̃ ≥ 0` and `epsFar = √· ≥ 0`). -/
theorem farReserve_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {μ : ℝ} (D : KzDatum) (hview : D.viewFS v h μ) (ρ : ℝ) (f : D.F.H) :
    0 ≤ D.F.qw f (∑ k : D.Mode, (Work.BoseFixR.epsFar v μ ρ * D.E.tau k) • D.F.nOp k) := by
  rw [FockData.qw]
  simp only [map_sum, LinearMap.sum_apply, FockData.nOp, LinearMap.comp_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_nonneg (fun k _ => ?_)
  exact mul_nonneg
    (mul_nonneg (by rw [Work.BoseFixR.epsFar]; exact Real.sqrt_nonneg _)
      (view_tau_nonneg D hview k))
    (by
      rw [FockData.aDag_adjoint]
      exact D.F.bp_nonneg _)

/-- The pure arithmetic of the far-leg assembly: the three slot bounds (`−A‖f‖² ≤ E₁`, …) plus
`A + B + C ≤ (7/8)·Err` beat the target once the reserve `E₄` and the `ε`-correction `B₀` are
nonnegative. -/
lemma farArith {N A B C E₁ E₂ E₃ E₄ B₀ Err : ℝ} (hN : 0 ≤ N)
    (hA : -A * N ≤ E₁) (hB : -B * N ≤ E₂) (hC : -C * N ≤ E₃)
    (h4 : 0 ≤ E₄) (h5 : 0 ≤ B₀) (harith : A + B + C ≤ (7 / 8) * Err) :
    -((7 / 8) * Err) * N ≤ E₁ + E₂ + E₃ + E₄ + B₀ := by
  have hkey : (A + B + C) * N ≤ (7 / 8) * Err * N := mul_le_mul_of_nonneg_right harith hN
  nlinarith [hA, hB, hC, h4, h5, hkey]

/-- **The assembly of `FarThreeQ`.**  The requested conclusion follows from the three slot bounds
(with constants `A`, `B`, `C`) and the *single* scalar inequality `A + B + C ≤ (7/8)·ErrRes`;
the `ετ`-reserve and the `32ρε^{−1/2}a𝓜` slack are nonnegative and are dropped. -/
theorem farThreeQ_of_slots {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    {μ : ℝ} (hμ : 0 < μ)
    (hview : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (f : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.H)
    (hf : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NWindow
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM f)
    (A B C : ℝ)
    (hA : -A * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f
        ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
            ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.linOpT
              (Work.BoseFixR.KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ)))
    (hB : -B * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f
        ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
            ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.Q2ex
              (Work.BoseFixR.KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ)))
    (hC : -C * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f
        ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
            ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.Q3T
              (Work.BoseFixR.KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ)))
    (harith : A + B + C ≤ (7 / 8) * Work.BoseFixR.ErrRes v μ ρ) :
    -((7 / 8) * Work.BoseFixR.ErrRes v μ ρ)
        * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f
      ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
            ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.linOpT
              (Work.BoseFixR.KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ))
        + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
            ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.Q2ex
              (Work.BoseFixR.KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ))
        + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
            ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.Q3T
              (Work.BoseFixR.KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ))
        + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
            (∑ k : Work.BoseBoxFock.Lab (HM μ).N,
              (Work.BoseFixR.epsFar v μ ρ
                  * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau k)
                • (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.nOp k)
        + ρ * (Work.BoseFixR.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v
            * (32 * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM)
            * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f := by
  have hres := farReserve_nonneg (v := v) (h := h) (μ := μ)
    (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ) hview ρ f
  have hN : 0 ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f :=
    (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq_nonneg f
  have hε : 0 ≤ (Work.BoseFixR.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) := by
    rw [Work.BoseFixR.epsFar]
    exact Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hbonus : 0 ≤ ρ * (Work.BoseFixR.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v
      * (32 * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM)
      * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hρ hε) hav.le)
      (mul_nonneg (by norm_num) (view_bigM_nonneg _ hview))) hN
  exact farArith hN hA hB hC hres hbonus harith

end Work.BoseFixR
