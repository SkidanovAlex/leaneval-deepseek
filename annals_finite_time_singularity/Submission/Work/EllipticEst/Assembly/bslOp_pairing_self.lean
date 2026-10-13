/-
Copyright: work module for the Elgindi finite-time singularity project.

# Self-adjointness of `bslOp α` for the weight `z^{(5-α)/α} cos θ`

`Work.EllipticEst.Assembly.bslOp_pairing_self`: for `Φ, φ` `C^∞` on the open quadrant
`Q0 = (0,∞) × (0,π/2)` with `φ` compactly supported inside `Q0`,

  `∫_{Q0} (L Φ)·φ·w = ∫_{Q0} Φ·(L φ)·w`,  `w = z^{(5-α)/α} cos θ`,  `L = bslOp α`.

The weight is exactly the one that puts `L` into divergence form (see `PairDefs.lean`):
with `β = (5-α)/α`, `A = α²z^{β+2}cos θ(∂_zφ·Φ - ∂_zΦ·φ)` and
`B = z^β cos θ(∂_θφ·Φ - ∂_θΦ·φ)` one has the pointwise identity
`w·(LΦ·φ - Φ·Lφ) = ∂_z A + ∂_θ B` (`PairAuxDiv.pairDivIdentityAux`).  Enclosing the compact
support of `φ` in a rectangle `[a₁,b₁] × [a₂,b₂] ⊆ Q0` (`PairAuxRest.existsBoxQ0Aux`) and
integrating the divergence over it with the planar divergence theorem, the four boundary terms
vanish (both `A` and `B` vanish off `tsupport φ`), which gives
`∫_{Q0} (LΦ·φ - Φ·Lφ)·w = 0`, i.e. the claim.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.EllipticEst.Assembly.PairDefs
import Submission.Work.EllipticEst.Assembly.PairAuxBasic
import Submission.Work.EllipticEst.Assembly.PairAuxDiv
import Submission.Work.EllipticEst.Assembly.PairAuxRest

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Assembly

set_option autoImplicit false
set_option maxHeartbeats 1600000
/-! ## The main theorem -/

theorem bslOp_pairing_self {α : ℝ} (hα : 0 < α) {Φ φ : ℝ → ℝ → ℝ}
    (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ)
    (hφ : Work.FTS.EllipticEst.SmoothOpen φ) (hcφ : HasCompactSupport (Function.uncurry φ))
    (hsub : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0) :
    (∫ p in Work.FTS.EllipticEst.Q0,
        Work.Elliptic.bslOp α Φ p.1 p.2 * φ p.1 p.2
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in Work.FTS.EllipticEst.Q0,
          Φ p.1 p.2 * Work.Elliptic.bslOp α φ p.1 p.2
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2) := by
  change (∫ p in Work.FTS.EllipticEst.Q0,
      Work.Elliptic.bslOp α Φ p.1 p.2 * φ p.1 p.2 * pairWeight α p)
    = ∫ p in Work.FTS.EllipticEst.Q0,
        Φ p.1 p.2 * Work.Elliptic.bslOp α φ p.1 p.2 * pairWeight α p
  -- ## the support of `φ` and a rectangle around it
  have hK : IsCompact (tsupport (Function.uncurry φ)) := hcφ
  obtain ⟨a, b, hab, ha1, ha2, hb2, hbox⟩ := existsBoxQ0Aux hK hsub
  have hKIcc : tsupport (Function.uncurry φ) ⊆ Set.Icc a b := by
    intro x hx
    rw [Set.Icc_prod_eq]
    exact Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self (hbox hx)
  have hboxQ0 : Set.Icc a b ⊆ Work.FTS.EllipticEst.Q0 := by
    intro x hx
    rw [Set.Icc_prod_eq] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [Work.FTS.EllipticEst.mem_Q0]
    exact ⟨lt_of_lt_of_le ha1 hx1.1, lt_of_lt_of_le ha2 hx2.1, lt_of_le_of_lt hx2.2 hb2⟩
  have hIcc_compact : IsCompact (Set.Icc a b) := by
    rw [Set.Icc_prod_eq]
    exact isCompact_Icc.prod isCompact_Icc
  have hpt : ∀ x ∈ Set.Icc a b, (0 : ℝ) < x.1 ∧ x.2 ∈ Set.Ioo 0 (π / 2) := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := Work.FTS.EllipticEst.mem_Q0.mp (hboxQ0 hx)
    exact ⟨h1, h2, h3⟩
  -- ## the integrands
  set F1 : ℝ × ℝ → ℝ := fun x =>
    Work.Elliptic.bslOp α Φ x.1 x.2 * φ x.1 x.2 * pairWeight α x with hF1
  set F2 : ℝ × ℝ → ℝ := fun x =>
    Φ x.1 x.2 * Work.Elliptic.bslOp α φ x.1 x.2 * pairWeight α x with hF2
  have hWcont : ContinuousOn (pairWeight α) Work.FTS.EllipticEst.Q0 :=
    continuousOn_pairWeight α
  -- ## integrability of the two integrands on the rectangle
  have hF1cont : ContinuousOn F1 (Set.Icc a b) := by
    rw [hF1]
    exact ((continuousOn_bslOp_smoothOpen hΦ).mul hφ.continuousOn).mul
      hWcont |>.mono hboxQ0
  have hF2cont : ContinuousOn F2 (Set.Icc a b) := by
    rw [hF2]
    exact (hΦ.continuousOn.mul (continuousOn_bslOp_smoothOpen hφ)).mul
      hWcont |>.mono hboxQ0
  have hF1int : IntegrableOn F1 (Set.Icc a b) := hF1cont.integrableOn_compact hIcc_compact
  have hF2int : IntegrableOn F2 (Set.Icc a b) := hF2cont.integrableOn_compact hIcc_compact
  -- ## differentiability and continuity of the two halves of the divergence form
  have hRadDiff : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ (pairRad α Φ φ) x := by
    intro x hx
    exact ((contDiffOnPairAux hΦ hφ).1.contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds (hboxQ0 hx))).differentiableAt (by norm_num)
  have hAngDiff : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ (pairAng α Φ φ) x := by
    intro x hx
    exact ((contDiffOnPairAux hΦ hφ).2.contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds (hboxQ0 hx))).differentiableAt (by norm_num)
  have hRadCont : ContinuousOn (pairRad α Φ φ) (Set.Icc a b) :=
    (contDiffOnPairAux hΦ hφ).1.continuousOn.mono hboxQ0
  have hAngCont : ContinuousOn (pairAng α Φ φ) (Set.Icc a b) :=
    (contDiffOnPairAux hΦ hφ).2.continuousOn.mono hboxQ0
  have hDsmooth : ContinuousOn (fderiv ℝ (pairRad α Φ φ)) Work.FTS.EllipticEst.Q0 :=
    (contDiffOnPairAux hΦ hφ).1.continuousOn_fderiv_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0 le_rfl
  have hEsmooth : ContinuousOn (fderiv ℝ (pairAng α Φ φ)) Work.FTS.EllipticEst.Q0 :=
    (contDiffOnPairAux hΦ hφ).2.continuousOn_fderiv_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0 le_rfl
  have hdivInt : IntegrableOn (fun x : ℝ × ℝ =>
      (fderiv ℝ (pairRad α Φ φ) x) (1, 0) + (fderiv ℝ (pairAng α Φ φ) x) (0, 1))
      (Set.Icc a b) :=
    (ContinuousOn.add ((hDsmooth.mono hboxQ0).clm_apply continuousOn_const)
      ((hEsmooth.mono hboxQ0).clm_apply continuousOn_const)).integrableOn_compact hIcc_compact
  -- ## the pointwise identity on the rectangle
  have hdiv_pt : ∀ x ∈ Set.Icc a b, F1 x - F2 x =
      deriv (fun z' => pairRad α Φ φ (z', x.2)) x.1
        + deriv (fun θ' => pairAng α Φ φ (x.1, θ')) x.2 := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hpt x hx
    have h := pairDivIdentityAux hα hx1 hx2
      (hasDerivAt_slice_z hΦ hx1 hx2) (hasDerivAt_slice_pz hΦ hx1 hx2)
      (hasDerivAt_slice_z hφ hx1 hx2) (hasDerivAt_slice_pz hφ hx1 hx2)
      (hasDerivAt_slice_θ hΦ hx1 hx2) (hasDerivAt_slice_pth hΦ hx1 hx2)
      (hasDerivAt_slice_θ hφ hx1 hx2) (hasDerivAt_slice_pth hφ hx1 hx2)
    rw [← h]
    show Work.Elliptic.bslOp α Φ x.1 x.2 * φ x.1 x.2 * pairWeight α x
        - Φ x.1 x.2 * Work.Elliptic.bslOp α φ x.1 x.2 * pairWeight α x
      = pairWeight α (x.1, x.2) * (Work.Elliptic.bslOp α Φ x.1 x.2 * φ x.1 x.2
        - Φ x.1 x.2 * Work.Elliptic.bslOp α φ x.1 x.2)
    simp only [Prod.mk.eta]
    ring
  have hbox_eq1 : (∫ x in Set.Icc a b, (F1 x - F2 x)) =
      ∫ x in Set.Icc a b, ((fderiv ℝ (pairRad α Φ φ) x) (1, 0)
        + (fderiv ℝ (pairAng α Φ φ) x) (0, 1)) := by
    refine setIntegral_congr_fun measurableSet_Icc (fun x hx => ?_)
    rw [hdiv_pt x hx, fderiv_fst_eq_deriv (hRadDiff x hx),
      fderiv_snd_eq_deriv (hAngDiff x hx)]
  -- ## the planar divergence theorem
  have hdiv := MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le
    (pairRad α Φ φ) (pairAng α Φ φ) (fun x => fderiv ℝ (pairRad α Φ φ) x)
    (fun x => fderiv ℝ (pairAng α Φ φ) x) a b hab ∅ countable_empty
    hRadCont hAngCont
    (fun x hx => (hRadDiff x (by
      obtain ⟨hx1, hx2⟩ := Set.mem_prod.mp hx.1
      rw [Set.Icc_prod_eq]
      exact ⟨⟨hx1.1.le, hx1.2.le⟩, ⟨hx2.1.le, hx2.2.le⟩⟩)).hasFDerivAt)
    (fun x hx => (hAngDiff x (by
      obtain ⟨hx1, hx2⟩ := Set.mem_prod.mp hx.1
      rw [Set.Icc_prod_eq]
      exact ⟨⟨hx1.1.le, hx1.2.le⟩, ⟨hx2.1.le, hx2.2.le⟩⟩)).hasFDerivAt)
    hdivInt
  -- ## the four boundary integrals vanish
  have hB_b2 : ∀ x : ℝ, pairAng α Φ φ (x, b.2) = 0 := by
    intro x
    refine pairAng_eq_zero_off_tsupport (fun hmem => ?_)
    exact absurd (hbox hmem).2.2 (lt_irrefl b.2)
  have hB_a2 : ∀ x : ℝ, pairAng α Φ φ (x, a.2) = 0 := by
    intro x
    refine pairAng_eq_zero_off_tsupport (fun hmem => ?_)
    exact absurd (hbox hmem).2.1 (lt_irrefl a.2)
  have hA_b1 : ∀ y : ℝ, pairRad α Φ φ (b.1, y) = 0 := by
    intro y
    refine pairRad_eq_zero_off_tsupport (fun hmem => ?_)
    exact absurd (hbox hmem).1.2 (lt_irrefl b.1)
  have hA_a1 : ∀ y : ℝ, pairRad α Φ φ (a.1, y) = 0 := by
    intro y
    refine pairRad_eq_zero_off_tsupport (fun hmem => ?_)
    exact absurd (hbox hmem).1.1 (lt_irrefl a.1)
  have hbdry : (((∫ x in a.1..b.1, pairAng α Φ φ (x, b.2))
        - ∫ x in a.1..b.1, pairAng α Φ φ (x, a.2))
      + ∫ y in a.2..b.2, pairRad α Φ φ (b.1, y))
      - ∫ y in a.2..b.2, pairRad α Φ φ (a.1, y) = 0 := by
    have h1 : (∫ x in a.1..b.1, pairAng α Φ φ (x, b.2)) = 0 := by
      rw [show (∫ x in a.1..b.1, pairAng α Φ φ (x, b.2))
          = ∫ x in a.1..b.1, (0 : ℝ) from
        intervalIntegral.integral_congr (fun x _ => hB_b2 x),
        intervalIntegral.integral_zero]
    have h2 : (∫ x in a.1..b.1, pairAng α Φ φ (x, a.2)) = 0 := by
      rw [show (∫ x in a.1..b.1, pairAng α Φ φ (x, a.2))
          = ∫ x in a.1..b.1, (0 : ℝ) from
        intervalIntegral.integral_congr (fun x _ => hB_a2 x),
        intervalIntegral.integral_zero]
    have h3 : (∫ y in a.2..b.2, pairRad α Φ φ (b.1, y)) = 0 := by
      rw [show (∫ y in a.2..b.2, pairRad α Φ φ (b.1, y))
          = ∫ y in a.2..b.2, (0 : ℝ) from
        intervalIntegral.integral_congr (fun y _ => hA_b1 y),
        intervalIntegral.integral_zero]
    have h4 : (∫ y in a.2..b.2, pairRad α Φ φ (a.1, y)) = 0 := by
      rw [show (∫ y in a.2..b.2, pairRad α Φ φ (a.1, y))
          = ∫ y in a.2..b.2, (0 : ℝ) from
        intervalIntegral.integral_congr (fun y _ => hA_a1 y),
        intervalIntegral.integral_zero]
    rw [h1, h2, h3, h4]
    ring
  have hzero : (∫ x in Set.Icc a b, (F1 x - F2 x)) = 0 := by
    rw [hbox_eq1, hdiv, hbdry]
  have hIcc_eq : (∫ x in Set.Icc a b, F1 x) = ∫ x in Set.Icc a b, F2 x := by
    have h := hzero
    rw [MeasureTheory.integral_sub hF1int hF2int] at h
    exact sub_eq_zero.mp h
  -- ## reduce both `Q0`-integrals to the rectangle
  have hF1vanish : ∀ x ∈ Work.FTS.EllipticEst.Q0 \ Set.Icc a b, F1 x = 0 := by
    intro x hx
    have hxK : x ∉ tsupport (Function.uncurry φ) := fun h => hx.2 (hKIcc h)
    obtain ⟨h1, -, -⟩ := supportVanishAux (g := φ) hxK
    show Work.Elliptic.bslOp α Φ x.1 x.2 * φ x.1 x.2 * pairWeight α x = 0
    rw [h1]; ring
  have hF2vanish : ∀ x ∈ Work.FTS.EllipticEst.Q0 \ Set.Icc a b, F2 x = 0 := by
    intro x hx
    have hxK : x ∉ tsupport (Function.uncurry φ) := fun h => hx.2 (hKIcc h)
    show Φ x.1 x.2 * Work.Elliptic.bslOp α φ x.1 x.2 * pairWeight α x = 0
    rw [bslOp_eq_zero_off_tsupport hxK]; ring
  have hQ1 : (∫ x in Work.FTS.EllipticEst.Q0, F1 x) = ∫ x in Set.Icc a b, F1 x :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Work.FTS.EllipticEst.isOpen_Q0.measurableSet
      hboxQ0 hF1vanish
  have hQ2 : (∫ x in Work.FTS.EllipticEst.Q0, F2 x) = ∫ x in Set.Icc a b, F2 x :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Work.FTS.EllipticEst.isOpen_Q0.measurableSet
      hboxQ0 hF2vanish
  rw [hQ1, hQ2]
  exact hIcc_eq

end Work.EllipticEst.Assembly
