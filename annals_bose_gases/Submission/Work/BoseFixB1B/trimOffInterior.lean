import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1B.bandCostAbsorb
import Submission.Work.BoseFixB1B.perBoxCrudeGoodOfPerBoxF
import Submission.Work.BoseFixB1B.thinShellCrude
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.trimOffInterior` — the `I₋` → `ℝ³` bookkeeping (FS `eq:badset`)

This module reduces the interior `u`-integral `∫_{I₋} sbWord` to the full one `∫_{ℝ³} sbWord`,
at the cost of the a-priori error `C·μ²(a v)ℓ³K_B³(μ(a v)³)^{1/2}‖Φ‖²`.

## Inputs (see `FINDING_trimOffInterior_gate.md` for the full analysis)

The whole content of the node is a **crude per-`u` lower bound on the band** (`bandSet`), since
off the cube `sbPot ≡ 0` and `sbKin ≥ 0` and `(I₋)ᶜ ∩ cube ⊆ bandSet`.  It is sourced from

* `Work.BoseFixB1B.perBoxCrudeGoodOfPerBoxF` — the same bound on `goodSet`, from the LIVE node
  `Work.BoseFixB1.PerBoxF` (FS `thm:smallbox`; its residual `perSectorBoundG_holds` is the project's
  single open analytic input), via `Work.BoseFixB1.perBoxFWeight_holds`;
* `Work.BoseFixB1B.thinShellCrude` — the same bound on `bandSet ∖ goodSet` (the outermost slab,
  outside `goodSet(mμ)` for every `m ≥ 1`), which needs a count bound for low states;
* `Work.BoseFixB1B.bandCostAbsorb` (proved) — absorbs the band cost into the target's error term.

The previous gate `Work.BoseFixB1B.perBoxCrudeLower` is **false as formalised** (its two halves
carry different localisation windows: `sbKin` the ball-based `chiB`, `sbPot` the product-based
`chiSmallB`, while FS uses one product bump) — see
`Submission/Work/BoseFixB1S/FINDING_perBoxCrudeB1.md`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1 Work.BoseKinLoc

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The support of the localised word -/

/-- `sbPot` at FS's parameters is the corpus's localised potential word (definitional). -/
theorem sbPot_eq_qLHSwordB {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {μ : ℝ} {n : ℕ}
    (u : EuclideanSpace ℝ (Fin 3)) (Φ : X n → ℝ) :
    sbPot h μ u Φ
      = qLHSwordB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ u Φ := rfl

/-- `sbWord = sbKin + sbPot` (definitional). -/
theorem sbWord_eq_add {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {μ : ℝ} {n : ℕ}
    (u : EuclideanSpace ℝ (Fin 3)) (Φ : X n → ℝ) :
    sbWord h μ u Φ = sbKin (v := v) μ (paramsAt μ (a v)).M u Φ + sbPot h μ u Φ := rfl

/-- **The localised kernels vanish outside the sliding cube**: if `chiSmallB M ℓ d u` vanishes
identically then so does every localised pair kernel. -/
theorem wSmallPair_eq_zero_of_chiB_eq_zero {M : ℕ} {ℓ d : ℝ} {u : ℝ³} {w : ℝ³ → ℝ}
    (hc : ∀ x : ℝ³, chiSmallB M ℓ d u x = 0) (x y : ℝ³) :
    wSmallPair M ℓ d u w x y = 0 := by
  simp only [wSmallPair, hc x, hc y, zero_mul, mul_zero]

/-- **The localised potential word vanishes outside the sliding cube.**  On the corpus's
`farSet` the small box misses the big box, `chiSmallB M ℓ d u` vanishes identically, hence so do
the localised kernels `wSmallPair`, `wSmall1Pair` and the potential word. -/
theorem sbPot_eq_zero_of_mem_farSet {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v}
    {μ : ℝ} {u : EuclideanSpace ℝ (Fin 3)}
    (hℓ : 0 < sideAt μ (a v)) (hd : 0 < (paramsAt μ (a v)).d)
    (hu : u ∈ farSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ) {n : ℕ} (Φ : X n → ℝ) :
    sbPot h μ u Φ = 0 := by
  let M : ℕ := (paramsAt μ (a v)).M
  have hcB : ∀ x : ℝ³, chiSmallB M (sideAt μ (a v)) (paramsAt μ (a v)).d u x = 0 :=
    fun x => farSet_chiSmallB_zero hℓ hd hu x
  have hzero : ∀ x : X n, Φ x ^ 2 *
      (-μ * (∑ i : Fin n, ∫ y in acube (sideAt μ (a v)),
          wSmall1Pair h M (sideAt μ (a v)) (paramsAt μ (a v)).d u (x i) y)
        + (1 / 2) * (∑ p ∈ pairSet n,
            wSmallPair M (sideAt μ (a v)) (paramsAt μ (a v)).d u v (x p.1) (x p.2))) = 0 := by
    intro x
    have h1 : (∑ i : Fin n, ∫ y in acube (sideAt μ (a v)),
        wSmall1Pair h M (sideAt μ (a v)) (paramsAt μ (a v)).d u (x i) y) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      have hz : (fun y : ℝ³ => wSmall1Pair h M (sideAt μ (a v)) (paramsAt μ (a v)).d u
          (x i) y) = fun _ => (0 : ℝ) := by
        funext y
        simp only [wSmall1Pair]
        exact wSmallPair_eq_zero_of_chiB_eq_zero hcB (x i) y
      rw [hz]
      exact integral_zero _ _
    have h2 : (∑ p ∈ pairSet n,
        wSmallPair M (sideAt μ (a v)) (paramsAt μ (a v)).d u v (x p.1) (x p.2)) = 0 :=
      Finset.sum_eq_zero fun p _ => by
        simpa only [wSmallPair] using wSmallPair_eq_zero_of_chiB_eq_zero hcB (x p.1) (x p.2)
    rw [h1, h2]
    ring
  subst M
  rw [sbPot_eq_qLHSwordB, qLHSwordB_eq_integral]
  rw [show (fun x : X n => qLHSBIntegrand h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d μ Φ u x) = fun _ => (0 : ℝ) from by
    funext x
    simp only [qLHSBIntegrand]
    exact hzero x]
  exact integral_zero _ _

/-! ## 2. `sbKin ≥ 0` -/

/-- FS's small-box kinetic word is nonnegative at an admissible point. -/
theorem sbKin_nonneg_local {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ε₀ μ : ℝ} (hadm : Adm v ε₀ μ)
    {n : ℕ} (u : EuclideanSpace ℝ (Fin 3)) (Φ : X n → ℝ) :
    0 ≤ sbKin (v := v) μ (paramsAt μ (a v)).M u Φ := by
  rw [show sbKin (v := v) μ (paramsAt μ (a v)).M u Φ
      = Work.UBBInputs8.tBwordBInd n (sideAt μ (a v)) (paramsAt μ (a v)).d
          (paramsAt μ (a v)).eT (sbCut μ (a v)) u Φ from rfl]
  exact Work.UBBInputs9.A.tBwordBInd_nonneg (adm_ell_pos hadm) (adm_eT_bounds hadm).1 u Φ

/-! ## 3. The sliding cube and the band inclusion -/

/-- The sliding cube `{|((ℓd)•u)_j| ≤ ½ℓ(1+d)}`; its complement lies in the corpus's `farSet`. -/
def cube (ℓ d : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {u : EuclideanSpace ℝ (Fin 3) |
    ∀ j : Fin 3, |((ℓ * d) • u).ofLp j| ≤ (1 / 2) * ℓ * (1 + d)}

lemma measurableSet_cube (ℓ d : ℝ) : MeasurableSet (cube ℓ d) := by
  have hset : cube ℓ d
      = ⋂ j : Fin 3, {u : EuclideanSpace ℝ (Fin 3) |
          |((ℓ * d) • u).ofLp j| ≤ (1 / 2) * ℓ * (1 + d)} := by
    ext u; simp [cube]
  rw [hset]
  refine MeasurableSet.iInter fun j => ?_
  have hcont : Continuous (fun u : EuclideanSpace ℝ (Fin 3) => |((ℓ * d) • u).ofLp j|) := by
    fun_prop
  exact hcont.measurable measurableSet_Iic

/-- The complement of the cube is contained in the corpus's `farSet`. -/
lemma cube_compl_subset_farSet {ℓ d μ : ℝ} : (cube ℓ d)ᶜ ⊆ farSet ℓ d μ := by
  intro u hu
  simp only [cube, Set.mem_setOf_eq, Set.mem_compl_iff, not_forall] at hu
  obtain ⟨j, hj⟩ := hu
  exact ⟨j, lt_of_not_ge hj⟩

/-- `(I₋)ᶜ ∩ cube ⊆ bandSet`. -/
lemma compl_inter_cube_subset_bandSet {ℓ d μ : ℝ} :
    (interiorSet ℓ d μ)ᶜ ∩ cube ℓ d ⊆ bandSet ℓ d μ := by
  intro u hu
  obtain ⟨hu1, hu2⟩ := hu
  simp only [interiorSet, Set.mem_setOf_eq, Set.mem_compl_iff, not_forall] at hu1
  obtain ⟨j, hj⟩ := hu1
  exact ⟨⟨j, le_of_lt (lt_of_not_ge hj)⟩, hu2⟩

/-! ## 4. The reduction -/

/-- **The reduction**: the target follows from the pointwise per-box bound `hpb` and the
numerical absorption `habs` of the band cost. -/
theorem trimOffInterior_of_inputs
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {J : ℝ} (hJ : Work.UBB.lhyC ≤ J)
    {ε₁ C₁ : ℝ} (hε₁ : 0 < ε₁) (hC₁ : 0 ≤ C₁)
    (hpb : ∀ μ : ℝ, Adm v ε₁ μ → J ≤ (paramsAt μ (a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : BoxState n (sideAt μ (a v))) (u : EuclideanSpace ℝ (Fin 3)),
        IsLowB v h J μ n Φ →
        -(C₁ * (μ ^ 2 * (a v)
                * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
              + μ * (a v))) * normB v μ n Φ ≤ sbWord h μ u Φ)
    {ε₂ C₂ : ℝ} (hε₂ : 0 < ε₂) (hC₂ : 0 ≤ C₂)
    (habs : ∀ μ : ℝ, Adm v ε₂ μ →
      C₁ * (μ ^ 2 * (a v)
              * (∫ u in bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
                  chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)
            + μ * (a v)
              * (volume (bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)).toReal)
        ≤ C₂ * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * (paramsAt μ (a v)).KB ^ 3
                * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
    :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ μ : ℝ, Adm v ε₀ μ →
      J ≤ (paramsAt μ (a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : BoxState n (sideAt μ (a v))), IsLowB v h J μ n Φ →
        (∫ u in interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
            sbWord h μ u (Φ : X n → ℝ))
          ≤ (∫ u : EuclideanSpace ℝ (Fin 3), sbWord h μ u (Φ : X n → ℝ))
            + C * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * (paramsAt μ (a v)).KB ^ 3
                    * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) * normB v μ n (Φ : X n → ℝ) := by
  obtain ⟨ε_R, hε_R, hregR⟩ := regime_sideAt_ge (v := v) hav hR
  obtain ⟨ε_F, hε_F, hFS⟩ := fsRegimeAt (A := _root_.BoseGases.a v) (R := R) hav hR
  refine ⟨min (min (min ε₁ ε₂) ε_R) (min ε_F 1), C₂,
    lt_min (lt_min (lt_min hε₁ hε₂) hε_R) (lt_min hε_F one_pos), hC₂, ?_⟩
  intro μ hAdm hJK n Φ hlow
  have hA1 : (min (min (min ε₁ ε₂) ε_R) (min ε_F 1) : ℝ) ≤ ε₁ :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hA2 : (min (min (min ε₁ ε₂) ε_R) (min ε_F 1) : ℝ) ≤ ε₂ :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hAR : (min (min (min ε₁ ε₂) ε_R) (min ε_F 1) : ℝ) ≤ ε_R :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hAF : (min (min (min ε₁ ε₂) ε_R) (min ε_F 1) : ℝ) ≤ ε_F :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hA1' : (min (min (min ε₁ ε₂) ε_R) (min ε_F 1) : ℝ) ≤ 1 :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hAdm1 : Adm v ε₁ μ := Adm.mono hAdm hA1
  have hAdm2 : Adm v ε₂ μ := Adm.mono hAdm hA2
  have hAdmR : Adm v ε_R μ := Adm.mono hAdm hAR
  have htR : μ * (a v) ^ 3 ≤ ε_R := adm_dilute hAdmR
  have hμ : 0 < μ := adm_mu_pos hAdm
  have hℓ : 0 < sideAt μ (a v) := adm_ell_pos hAdm
  have hd : 0 < (paramsAt μ (a v)).d := adm_d_pos hAdm
  obtain ⟨hRd, hRchi⟩ := hregR μ hμ htR
  have hFSμ := hFS μ hμ (le_trans (adm_dilute hAdm) hAF)
  obtain ⟨_, _, _, _, _, _, _, _, hμinv, hA0, hM⟩ := hFSμ
  have hμa : 0 ≤ μ * (a v) := mul_nonneg hμ.le (le_of_lt hav)
  have hC₁nB : 0 ≤ C₁ * normB v μ n (Φ : X n → ℝ) :=
    mul_nonneg hC₁ (normB_nonneg (v := v) (μ := μ) (Φ : X n → ℝ))
  -- the `u`-marginal integrability of the word (corpus lemmas)
  have hIntK : Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      sbKin (v := v) μ (paramsAt μ (a v)).M u (Φ : X n → ℝ)) :=
    integrable_sbKin_marginal (v := v) (μ := μ) hℓ hd Φ
  have hIntP : Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      sbPot h μ u (Φ : X n → ℝ)) :=
    (sbPot_integral_le_potWordU (v := v) (h := h) hv1 hvrad hR hv_supp hav hℓ hd hM
      hRd hRchi Φ).1
  have hIntW : Integrable (fun u : EuclideanSpace ℝ (Fin 3) => sbWord h μ u (Φ : X n → ℝ)) := by
    have heq : (fun u : EuclideanSpace ℝ (Fin 3) => sbWord h μ u (Φ : X n → ℝ))
        = (fun u : EuclideanSpace ℝ (Fin 3) => sbKin (v := v) μ (paramsAt μ (a v)).M u
            (Φ : X n → ℝ))
          + (fun u : EuclideanSpace ℝ (Fin 3) => sbPot h μ u (Φ : X n → ℝ)) := by
      funext u; rw [Pi.add_apply, sbWord_eq_add]
    rw [heq]; exact hIntK.add hIntP
  have hImeas : MeasurableSet (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ) :=
    measurableSet_interiorSet _ _ _
  have hsplit := integral_add_compl hImeas hIntW
  -- the truncated pointwise bound (`sbWord ≥ 0` off the cube)
  have hpt : ∀ u : EuclideanSpace ℝ (Fin 3),
      -(C₁ * (μ ^ 2 * (a v) * chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                (paramsAt μ (a v)).d u + μ * (a v))) * normB v μ n (Φ : X n → ℝ)
        ≤ sbWord h μ u (Φ : X n → ℝ) := by
    intro u
    by_cases hu : u ∈ cube (sideAt μ (a v)) (paramsAt μ (a v)).d
    · exact hpb μ hAdm1 hJK n Φ u hlow
    · have hfar : u ∈ farSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ :=
        cube_compl_subset_farSet hu
      have hz := sbPot_eq_zero_of_mem_farSet (v := v) (h := h) (μ := μ) (n := n) hℓ hd hfar (Φ : X n → ℝ)
      rw [sbWord_eq_add, hz, add_zero]
      have hnn : 0 ≤ μ ^ 2 * (a v) * chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
          (paramsAt μ (a v)).d u + μ * (a v) :=
        add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) (le_of_lt hav))
          (Work.SmallBoxSliding.chiMass_nonneg _ _ _ _)) (mul_nonneg hμ.le (le_of_lt hav))
      refine le_trans ?_ (sbKin_nonneg_local hAdm1 u (Φ : X n → ℝ))
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg hC₁ hnn))
        (normB_nonneg (v := v) (μ := μ) (Φ : X n → ℝ))
  -- the finiteness of the cube slice
  have hcube_meas : MeasurableSet (cube (sideAt μ (a v)) (paramsAt μ (a v)).d) :=
    measurableSet_cube _ _
  have hslice_meas : MeasurableSet ((interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ
      ∩ cube (sideAt μ (a v)) (paramsAt μ (a v)).d) := hImeas.compl.inter hcube_meas
  have hbmeas : MeasurableSet (bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ) :=
    measurableSet_bandSet _ _ _
  have hslice_fin : volume ((interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ
      ∩ cube (sideAt μ (a v)) (paramsAt μ (a v)).d) < ⊤ := by
    refine lt_of_le_of_lt (measure_mono (compl_inter_cube_subset_bandSet)) ?_
    refine lt_of_le_of_lt (bandSet_volume_le_d3 hℓ hd hμ
      (by simpa only [neg_div] using hμinv) (by simpa only [neg_div] using hA0))
      ENNReal.ofReal_lt_top
  -- the `bandSet`-restricted integrability of `chiMass`
  have hchi_int : Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) := by
    simpa only [chiMass_def] using integrable_chiSmallB_mass hM hℓ hd
  -- the truncated bound is integrable on the slice
  have h2b : Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      μ ^ 2 * (a v) * chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u + μ * (a v))
      (volume.restrict ((interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ
        ∩ cube (sideAt μ (a v)) (paramsAt μ (a v)).d)) :=
    ((hchi_int.integrableOn).const_mul (μ ^ 2 * (a v))).add
      (integrableOn_const (s := (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ
        ∩ cube (sideAt μ (a v)) (paramsAt μ (a v)).d) (μ := volume) (C := μ * (a v))
        (ne_of_lt hslice_fin))
  have hslice_int : Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      -(C₁ * (μ ^ 2 * (a v) * chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u + μ * (a v))) * normB v μ n (Φ : X n → ℝ))
      (volume.restrict ((interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ
        ∩ cube (sideAt μ (a v)) (paramsAt μ (a v)).d)) :=
    ((Integrable.const_mul h2b C₁).neg).mul_const (normB v μ n (Φ : X n → ℝ))
  -- the monotonicity on the slice
  have hmono : (∫ u in (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ
        ∩ cube (sideAt μ (a v)) (paramsAt μ (a v)).d,
        -(C₁ * (μ ^ 2 * (a v) * chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                (paramsAt μ (a v)).d u + μ * (a v))) * normB v μ n (Φ : X n → ℝ))
      ≤ ∫ u in (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ
        ∩ cube (sideAt μ (a v)) (paramsAt μ (a v)).d, sbWord h μ u (Φ : X n → ℝ) :=
    integral_mono_ae hslice_int hIntW.integrableOn (Eventually.of_forall hpt)
  -- the value of the truncated integral, bounded by minus the band cost
  have hband : (∫ u in (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ
        ∩ cube (sideAt μ (a v)) (paramsAt μ (a v)).d,
        -(C₁ * (μ ^ 2 * (a v) * chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                (paramsAt μ (a v)).d u + μ * (a v))) * normB v μ n (Φ : X n → ℝ))
      ≥ -(C₁ * (μ ^ 2 * (a v)
            * (∫ u in bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
                chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)
          + μ * (a v)
            * (volume (bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)).toReal))
          * normB v μ n (Φ : X n → ℝ) := by
    set nB := normB v μ n (Φ : X n → ℝ) with hnBdef
    set S := (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ
      ∩ cube (sideAt μ (a v)) (paramsAt μ (a v)).d with hSdef
    have hSfin : volume S < ⊤ := hslice_fin
    have hSmeas : MeasurableSet S := hslice_meas
    -- expand the slice integral
    have hval : (∫ u in S, -(C₁ * (μ ^ 2 * (a v) * chiMass (paramsAt μ (a v)).M
            (sideAt μ (a v)) (paramsAt μ (a v)).d u + μ * (a v))) * nB)
        = -(C₁ * nB) * ((μ ^ 2 * (a v)) * (∫ u in S, chiMass (paramsAt μ (a v)).M
              (sideAt μ (a v)) (paramsAt μ (a v)).d u) + (μ * (a v)) * (volume S).toReal) := by
      rw [show (fun u : EuclideanSpace ℝ (Fin 3) =>
            -(C₁ * (μ ^ 2 * (a v) * chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                (paramsAt μ (a v)).d u + μ * (a v))) * nB)
          = (fun u => (-(C₁ * nB)) * (μ ^ 2 * (a v) * chiMass (paramsAt μ (a v)).M
                (sideAt μ (a v)) (paramsAt μ (a v)).d u + μ * (a v))) from by
        funext u; ring_nf]
      rw [integral_const_mul, integral_add, integral_const_mul, setIntegral_const]
      all_goals first
        | (simp only [MeasureTheory.measureReal_def]; ring_nf)
        | exact (hchi_int.integrableOn).const_mul _
        | exact integrableOn_const (s := S) (μ := volume) (C := μ * (a v)) (ne_of_lt hSfin)
    have hχmono : (∫ u in S, chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
          (paramsAt μ (a v)).d u)
        ≤ ∫ u in bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
            chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u := by
      refine setIntegral_mono_set (hchi_int.integrableOn) ?_ ?_
      · exact Eventually.of_forall fun u => Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
      · exact Eventually.of_forall fun u hu => compl_inter_cube_subset_bandSet hu
    have hvolmono : (volume S).toReal
        ≤ (volume (bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)).toReal := by
      refine ENNReal.toReal_mono ?_ (measure_mono compl_inter_cube_subset_bandSet)
      exact ne_of_lt (lt_of_le_of_lt (bandSet_volume_le_d3 hℓ hd hμ
        (by simpa only [neg_div] using hμinv) (by simpa only [neg_div] using hA0))
        ENNReal.ofReal_lt_top)
    -- assemble
    have hkey : (∫ u in S, chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
          (paramsAt μ (a v)).d u)
        + 0 ≤ (∫ u in bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
              chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) + 0 := by
      linarith [hχmono]
    have hcomb : (μ ^ 2 * (a v)) * (∫ u in S, chiMass (paramsAt μ (a v)).M
            (sideAt μ (a v)) (paramsAt μ (a v)).d u) + (μ * (a v)) * (volume S).toReal
        ≤ (μ ^ 2 * (a v)) * (∫ u in bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
              chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)
          + (μ * (a v)) * (volume (bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)).toReal := by
      have h0 : 0 ≤ (μ ^ 2 * (a v)) := by positivity
      have h1 : 0 ≤ (μ * (a v)) := hμa
      nlinarith [hχmono, hvolmono, h0, h1]
    rw [hval]
    have hC1nBnn : 0 ≤ C₁ * nB := mul_nonneg hC₁ (normB_nonneg _)
    nlinarith [hcomb, hC1nBnn]
  -- `sbWord ≥ 0` off the cube, hence the complement integral dominates the slice integral
  have hnonneg_off : 0 ≤ ∫ u in (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ
      \ cube (sideAt μ (a v)) (paramsAt μ (a v)).d, sbWord h μ u (Φ : X n → ℝ) := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem (hImeas.compl.diff hcube_meas)] with u hu
    have hc : u ∉ cube (sideAt μ (a v)) (paramsAt μ (a v)).d := hu.2
    have hfar : u ∈ farSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ :=
      cube_compl_subset_farSet hc
    have hz := sbPot_eq_zero_of_mem_farSet (v := v) (h := h) (μ := μ) (n := n) hℓ hd hfar (Φ : X n → ℝ)
    rw [sbWord_eq_add, hz, add_zero]
    exact sbKin_nonneg_local hAdm1 u (Φ : X n → ℝ)
  have hdecomp : (∫ u in (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ,
        sbWord h μ u (Φ : X n → ℝ))
      = (∫ u in (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ
            ∩ cube (sideAt μ (a v)) (paramsAt μ (a v)).d, sbWord h μ u (Φ : X n → ℝ))
        + ∫ u in (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ
            \ cube (sideAt μ (a v)) (paramsAt μ (a v)).d, sbWord h μ u (Φ : X n → ℝ) := by
    have hdisj : Disjoint ((interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ
        ∩ cube (sideAt μ (a v)) (paramsAt μ (a v)).d)
        ((interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ
          \ cube (sideAt μ (a v)) (paramsAt μ (a v)).d) := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      exact hx2.2 hx1.2
    rw [← setIntegral_union hdisj (hImeas.compl.diff hcube_meas)
      (hIntW.integrableOn.mono_set Set.inter_subset_left)
      (hIntW.integrableOn.mono_set Set.sdiff_subset)]
    congr 1
    ext x
    simp [Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]
  have habsμ := habs μ hAdm2
  have hstep : -(C₁ * (μ ^ 2 * (a v)
          * (∫ u in bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
              chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)
        + μ * (a v)
          * (volume (bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)).toReal))
        * normB v μ n (Φ : X n → ℝ)
      ≥ -(C₂ * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * (paramsAt μ (a v)).KB ^ 3
          * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))) * normB v μ n (Φ : X n → ℝ) := by
    have h1 : C₁ * (μ ^ 2 * (a v)
          * (∫ u in bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
              chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)
        + μ * (a v)
          * (volume (bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)).toReal)
        ≤ C₂ * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * (paramsAt μ (a v)).KB ^ 3
          * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) := habsμ
    nlinarith [h1, normB_nonneg (v := v) (μ := μ) (Φ : X n → ℝ)]
  have hkey : -(C₂ * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * (paramsAt μ (a v)).KB ^ 3
        * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))) * normB v μ n (Φ : X n → ℝ)
      ≤ ∫ u in (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ,
          sbWord h μ u (Φ : X n → ℝ) := by
    linarith [hdecomp, hmono, hband, hnonneg_off, hstep]
  linarith [hsplit, hkey]

/-- **FS `eq:badset` bookkeeping at FS's parameters**: the `I₋`-integral of the small-box word is
dominated by the full `u`-integral plus `C·μ²(a v)ℓ³K_B³(μ(a v)³)^{1/2}‖Φ‖²`. -/
theorem trimOffInterior {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {J : ℝ} (hJ : Work.UBB.lhyC ≤ J) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
            (∫ u in Work.SmallBoxSliding.interiorSet
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                  Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ))
              ≤ (∫ u : EuclideanSpace ℝ (Fin 3),
                  Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ))
                + C * (μ ^ 2 * (_root_.BoseGases.a v)
                        * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
                        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                        * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
                  * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
  -- 1. the LIVE node: FS `thm:smallbox` at the sliding box, on the good set
  obtain ⟨εp, cp, Cp, hεp, hcp, hCp, hPF⟩ :=
    perBoxFWeight_holds h hv hv1 hvrad hR hv_supp hav
  -- 2. its crude form on `goodSet`
  obtain ⟨εg, Cg, hεg, hCg, hgood⟩ :=
    perBoxCrudeGoodOfPerBoxF h hv hv1 hvrad hR hv_supp hav hJ hεp hcp hCp hPF
  -- 3. the crude form on the thin shell `bandSet ∖ goodSet`
  obtain ⟨εt, Ct, hεt, hCt, hthin⟩ := thinShellCrude h hv hv1 hvrad hR hv_supp hav hJ
  -- 4. the band-cost absorption at the larger constant
  obtain ⟨ε₂, C₂, hε₂, hC₂, habs⟩ :=
    bandCostAbsorb h hv hvrad hR hv_supp hav (max Cg Ct)
  refine trimOffInterior_of_inputs h hv hv1 hvrad hR hv_supp hav hJ (lt_min hεg hεt)
    (le_trans hCg (le_max_left _ _)) ?_ hε₂ hC₂ habs
  -- the pointwise crude bound, on the whole space
  intro μ hAdm hJK n Φ u hlow
  have hAdmg : Adm v εg μ := Adm.mono hAdm (min_le_left _ _)
  have hAdmt : Adm v εt μ := Adm.mono hAdm (min_le_right _ _)
  have hℓ : 0 < sideAt μ (a v) := adm_ell_pos hAdm
  have hd : 0 < (paramsAt μ (a v)).d := adm_d_pos hAdm
  have hμ : 0 < μ := adm_mu_pos hAdm
  set XX : ℝ := μ ^ 2 * (a v) * chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
      (paramsAt μ (a v)).d u + μ * (a v) with hXdef
  have hX0 : 0 ≤ XX := by
    rw [hXdef]
    exact add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) (le_of_lt hav))
      (Work.SmallBoxSliding.chiMass_nonneg _ _ _ _)) (mul_nonneg hμ.le (le_of_lt hav))
  have hnB0 : 0 ≤ normB v μ n (Φ : X n → ℝ) := normB_nonneg _
  by_cases hg : u ∈ goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ
  · -- on the good set: the `PerBoxF` route
    have h1 := hgood μ hAdmg hJK n Φ hlow u hg
    have h2 : Cg * XX * normB v μ n (Φ : X n → ℝ) ≤ (max Cg Ct) * XX * normB v μ n (Φ : X n → ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hX0) hnB0
    rw [hXdef] at h2 ⊢
    nlinarith [h1, h2]
  · by_cases hb : u ∈ bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ
    · -- on the thin shell
      have h1 := hthin μ hAdmt hJK n Φ hlow u hb hg
      have h2 : Ct * XX * normB v μ n (Φ : X n → ℝ) ≤ (max Cg Ct) * XX * normB v μ n (Φ : X n → ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hX0) hnB0
      rw [hXdef] at h2 ⊢
      nlinarith [h1, h2]
    · -- outside the cube (`u ∉ goodSet`, `u ∉ bandSet` forces `u ∈ farSet`): `sbWord ≥ 0`
      have hfar : u ∈ farSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ := by
        have hg' : ¬ (∀ j : Fin 3, |(((sideAt μ (a v)) * (paramsAt μ (a v)).d) • u).ofLp j|
            ≤ (1 / 2) * (sideAt μ (a v)) * (1 + (paramsAt μ (a v)).d) - μ ^ (-1 / 3 : ℝ)) := by
          simpa only [goodSet, Set.mem_setOf_eq] using hg
        have hb' : ¬ (((∃ j : Fin 3,
              (1 / 2) * (sideAt μ (a v)) * (1 + (paramsAt μ (a v)).d) - 2 * μ ^ (-1 / 3 : ℝ)
                ≤ |(((sideAt μ (a v)) * (paramsAt μ (a v)).d) • u).ofLp j|)
            ∧ (∀ j : Fin 3, |(((sideAt μ (a v)) * (paramsAt μ (a v)).d) • u).ofLp j|
                ≤ (1 / 2) * (sideAt μ (a v)) * (1 + (paramsAt μ (a v)).d)))) := by
          simpa only [bandSet, Set.mem_setOf_eq] using hb
        obtain ⟨j, hj⟩ := not_forall.mp hg'
        have hj' : (1 / 2) * (sideAt μ (a v)) * (1 + (paramsAt μ (a v)).d) - μ ^ (-1 / 3 : ℝ)
            < |(((sideAt μ (a v)) * (paramsAt μ (a v)).d) • u).ofLp j| := not_le.mp hj
        by_contra hcon
        have hcon' : ∀ j : Fin 3, |(((sideAt μ (a v)) * (paramsAt μ (a v)).d) • u).ofLp j|
            ≤ (1 / 2) * (sideAt μ (a v)) * (1 + (paramsAt μ (a v)).d) := by
          intro j
          by_contra hjA
          exact hcon ⟨j, not_le.mp hjA⟩
        refine hb' ⟨⟨j, ?_⟩, hcon'⟩
        have hδ : 0 ≤ μ ^ (-1 / 3 : ℝ) := Real.rpow_nonneg hμ.le _
        linarith
      have hz := sbPot_eq_zero_of_mem_farSet (v := v) (h := h) (μ := μ) (n := n)
        hℓ hd hfar (Φ : X n → ℝ)
      have hkin := sbKin_nonneg_local hAdmg u (Φ : X n → ℝ)
      have hsw : 0 ≤ sbWord h μ u (Φ : X n → ℝ) := by
        rw [sbWord_eq_add, hz, add_zero]; exact hkin
      have h3 : -((max Cg Ct) * XX) * normB v μ n (Φ : X n → ℝ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (mul_nonneg (le_trans hCg (le_max_left _ _)) hX0)) hnB0
      rw [hXdef] at h3 ⊢
      linarith

end Work.BoseFixB1B
