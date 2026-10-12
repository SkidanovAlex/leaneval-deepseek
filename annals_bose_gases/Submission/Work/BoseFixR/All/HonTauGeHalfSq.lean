import ChallengeDeps
import Submission.Work.BoseFixR.All.RB5FSFixAux
import Submission.Work.BoseFixR.eT_le_and_ratio_le
import Submission.Work.BoseFixR.halfSq_le_tau_of_threshold
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.All.HonTauGeHalfSq` — the kinetic symbol dominates `‖k‖²/2` on `P_H`

The target is the `P_H` domination of the honest kinetic symbol `τ̃` at the honest
box model: for every lattice label `k` in FS's high-momentum region
`P_H = {‖k‖ ≥ (2K_Ha)⁻¹}`,

  `‖kmom k‖²/2 ≤ τ̃(k)`  (`E.tau` of the honest environment).

## The mathematics

`τ̃ eT s d ℓ k = (1−ε_T)c²τ̃_profile(‖k‖/c) + ε_T c'²τ̃_profile(‖k‖/c')` with
`c = (2sℓ)⁻¹`, `c' = (2dsℓ)⁻¹` (`Work.BoseBoxFock.tauSm`) and the profile
dominating `(max 0 (r−2))²` (`Work.BoseBoxFock.exists_tauProf`).  Hence

  `τ̃(k) ≥ (1−ε_T)(max 0 (‖k‖ − (sℓ)⁻¹))²`

(`Work.BoseGateFS.tauTilde_ge_kink`, the doubled thresholds of the smoothed
symbol).  Two numeric facts turn this into the claim:

* `a·K_H/(sℓ) ≤ 1/16`: FS's monomials give `a·K_H/(sℓ) = (μa³)^{99/1292}`, so
  this is the diluteness hypothesis `μa³ ≤ 10⁻⁴⁰⁰⁰`.  With `‖k‖ ≥ (2K_Ha)⁻¹`
  it yields `(sℓ)⁻¹ ≤ ‖k‖/8`, i.e. `‖k‖ − (sℓ)⁻¹ ≥ (7/8)‖k‖`;
* `ε_T = (μa³)^{23/1292} ≤ 9/49`, so `1 − ε_T ≥ 40/49` and
  `(1−ε_T)(7/8)² ≥ (40/49)(49/64) = 5/8 > 1/2`:

  `‖k‖²/2 ≤ (5/8)‖k‖² ≤ (1−ε_T)(7‖k‖/8)² ≤ τ̃(k)`.

Both numeric facts are `Work.BoseFixR.eT_le_and_ratio_le`; the one-variable
kinetic step is `Work.BoseFixR.halfSq_le_tau_of_threshold`; the assembly below
only extracts `FSParamsView` from the view `hview`, transports the diluteness
bound `μa³ ≤ ε₀ ≤ 10⁻⁴⁰⁰⁰` to `hv.t`, and turns `P_H` into the threshold
condition.
-/

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

/-! ## 0. The radius `chiR0` under its requested name

The requested statement writes the localisation radius as `Submission.Gases.chiR0`;
the object in the corpus is `Submission.BoseGases.chiR0` (`Submission/ChiWitness.lean`,
the radius on which `χ⋆χ ≥ 1/2`).  The two names denote the *same* radius: the
`abbrev` below is definitionally `Submission.BoseGases.chiR0` (it is `abbrev`, hence
reducible, so every application site that supplies
`hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0` still elaborates against the
statement below without any rewriting).  Nothing else about the statement is
touched. -/

namespace Submission

namespace Gases

/-- `Submission.Gases.chiR0`, definitionally `Submission.BoseGases.chiR0`. -/
noncomputable abbrev chiR0 : ℝ := Submission.BoseGases.chiR0

end Gases

end Submission

namespace Work.BoseFixR.All
open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox
open Work.BoseBoxFix Work.BoseBoxFock Work.BoseB7 Work.BoseB7A

set_option autoImplicit false
set_option linter.unusedVariables false

theorem HonTauGeHalfSq {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    {ε₀ μ : ℝ} (hε₀ : ε₀ ≤ 10 ^ (-(4000 : ℤ)))
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hview : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFSAll v h μ)
    (hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.Gases.chiR0) :
    ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PH
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KH
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.aScat k →
      ‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖ ^ 2 / 2
        ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau k := by
  intro k hk
  -- FS's parameter point: the view exposes `FSParamsView` of the honest environment
  obtain ⟨hvE⟩ := hview.1
  -- the diluteness bound `t = μa³ ≤ ε₀ ≤ 10⁻⁴⁰⁰⁰`, transported to `hvE.t`
  have htv : hvE.t ≤ 10 ^ (-(4000 : ℤ)) := by
    rw [← hvE.mu_eq]
    show μ * BoseGases.a v ^ 3 ≤ 10 ^ (-(4000 : ℤ))
    exact le_trans hAdm.2.1 hε₀
  -- the two numeric facts: `ε_T ≤ 9/49` and `aK_H/(sℓ) ≤ 1/16`
  obtain ⟨heT, hratio⟩ :=
    eT_le_and_ratio_le (HonestBoxFam v h fc fu HM μ).E hvE htv
  -- the `τ̃`-pin of the honest environment
  have htau : ∀ k : Lab (HM μ).N,
      (HonestBoxFam v h fc fu HM μ).E.tau k
        = tauSm (HonestBoxFam v h fc fu HM μ).E.eT (HonestBoxFam v h fc fu HM μ).E.s
            (HonestBoxFam v h fc fu HM μ).E.d (HonestBoxFam v h fc fu HM μ).E.ell
            ((HonestBoxFam v h fc fu HM μ).F.kmom k) := by
    intro k
    simp only [HonestBoxFam, KzEnvHon, KzEnvFs]
  -- `P_H` (`‖k‖ ≥ (2K_Ha)⁻¹`) plus `aK_H/(sℓ) ≤ 1/16` give `(sℓ)⁻¹ ≤ ‖k‖/8`
  have hx : ((HonestBoxFam v h fc fu HM μ).E.s * (HonestBoxFam v h fc fu HM μ).E.ell)⁻¹
      ≤ ‖(HonestBoxFam v h fc fu HM μ).F.kmom k‖ / 8 := by
    have hKH : 0 < (HonestBoxFam v h fc fu HM μ).E.KH :=
      lt_of_lt_of_le zero_lt_one hvE.one_le_KH
    have ha : 0 < (HonestBoxFam v h fc fu HM μ).E.aScat := hvE.a_pos
    have hstep : (1 / ((HonestBoxFam v h fc fu HM μ).E.aScat
            * (HonestBoxFam v h fc fu HM μ).E.KH))
          * ((HonestBoxFam v h fc fu HM μ).E.aScat * (HonestBoxFam v h fc fu HM μ).E.KH
              / ((HonestBoxFam v h fc fu HM μ).E.s * (HonestBoxFam v h fc fu HM μ).E.ell))
        ≤ (1 / ((HonestBoxFam v h fc fu HM μ).E.aScat
            * (HonestBoxFam v h fc fu HM μ).E.KH)) * (1 / 16) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    have hL : (1 / ((HonestBoxFam v h fc fu HM μ).E.aScat
            * (HonestBoxFam v h fc fu HM μ).E.KH))
          * ((HonestBoxFam v h fc fu HM μ).E.aScat * (HonestBoxFam v h fc fu HM μ).E.KH
              / ((HonestBoxFam v h fc fu HM μ).E.s * (HonestBoxFam v h fc fu HM μ).E.ell))
        = ((HonestBoxFam v h fc fu HM μ).E.s * (HonestBoxFam v h fc fu HM μ).E.ell)⁻¹ := by
      field_simp
    have hR : (1 / ((HonestBoxFam v h fc fu HM μ).E.aScat
            * (HonestBoxFam v h fc fu HM μ).E.KH)) * (1 / 16)
        = (1 / (2 * ((HonestBoxFam v h fc fu HM μ).E.KH
            * (HonestBoxFam v h fc fu HM μ).E.aScat))) / 8 := by
      field_simp
      ring
    rw [hL, hR] at hstep
    have h4 : 1 / (2 * ((HonestBoxFam v h fc fu HM μ).E.KH
          * (HonestBoxFam v h fc fu HM μ).E.aScat))
        ≤ ‖(HonestBoxFam v h fc fu HM μ).F.kmom k‖ := by
      have h5 : 2 * ((HonestBoxFam v h fc fu HM μ).E.KH
          * (HonestBoxFam v h fc fu HM μ).E.aScat)
          = 2 * (HonestBoxFam v h fc fu HM μ).E.KH
              * (HonestBoxFam v h fc fu HM μ).E.aScat := by ring
      rw [h5]
      exact hk
    linarith
  exact halfSq_le_tau_of_threshold htau hvE heT k hx

end Work.BoseFixR.All
