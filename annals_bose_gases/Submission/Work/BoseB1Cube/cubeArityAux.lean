import ChallengeDeps
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.cubePerBox_sector
import Submission.Work.BoseFixB1B.slotDemandAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.cubeArityAux` — the elementary pieces of the cube arity passage

Helpers for `Work.BoseB1Cube.cubePerBox_of_inBoxCubeRow` (the cube twin of
`Work.BoseFixB1B.perBoxFTotal_of_inBox`).  This module contains the parts of the passage that
involve no fibre decomposition:

* `perBoxCubeLHSFun_const_mul` — the pointwise demand is `2`-homogeneous in the state (the cube twin
  of `Work.BoseFixB1B.totalDemand_const_mul`; the word half is the PROVED
  `Work.BoseFixB1S.sbWordCube_smul`);
* `tendsto_perBoxCubeLHSFun_cutProd` — the demand converges along the smooth-cutoff approximants
  `cutProd (γ δ) ψ` of the sharp state (needed by the smooth → sharp extension);
* `sbKinCube_nonneg` and `sbWordCube_slotPiece_empty_nonneg` — the empty-slot-set case of the
  fibre decomposition.

The fibre decomposition itself (the demand splitting, the word additivity and the word fibre
factorisation) is delegated, and the assembly lives in the target file.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.FockBridge Work.PerSector Work.SlotWord Work.BoseFixB1B
open Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

/-! ## 1. The `F`-weight of the demand, and the homogeneity of the demand -/

/-- The `F`-weight of the pointwise demand: `ψ(nCountB/chiMass)` at FS's parameters.  It is a
functional of the *configuration*, so it is state-independent. -/
noncomputable def demandWeight {v : E3 → ℝ} (μ : ℝ) {n : ℕ} (u : E3) (x : X n) : ℝ :=
  psiWeight 1 μ (Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x
    / chiMass (PBM v μ) (PBℓ v μ) (PBd v μ) u)

/-- **The pointwise demand, written out as a polynomial in the mass and the `F`-weighted
integral.**  This is the shape in which the convergence along the cutoff approximants is
assembled. -/
theorem perBoxCubeLHSFun_eq {v : E3 → ℝ} {h : ScatSol v} {R c₁ C μ : ℝ} {n : ℕ}
    (Φ : X n → ℝ) (u : E3) :
    perBoxCubeLHSFun v h R c₁ C μ n Φ u
      = c₁ * (w1MassB h (PBM v μ) (PBℓ v μ) (PBd v μ) u
            * (∫ x in abox n (PBℓ v μ), (Φ x) ^ 2 * demandWeight (v := v) μ u x))
          - ((1 / 2) * μ ^ 2 * w1MassB h (PBM v μ) (PBℓ v μ) (PBd v μ) u)
              * Work.BoseBoxFix.normB v μ n Φ
          - C * (((μ ^ 2 * (a v) * ((R / (PBℓ v μ * PBd v μ)) ^ 2
                  + PBKB v μ ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
                * chiMass (PBM v μ) (PBℓ v μ) (PBd v μ) u)
              * Work.BoseBoxFix.normB v μ n Φ
            + μ * (a v) * Work.BoseBoxFix.normB v μ n Φ) := by
  unfold perBoxCubeLHSFun demandWeight
  ring

/-- **The pointwise demand is `2`-homogeneous in the state.**  Both state-dependent factors are
quadratic in `Φ`: the `F`-weighted integral (the weight is a function of the *configuration*, not of
the amplitude) and the mass `normB`. -/
theorem perBoxCubeLHSFun_const_mul {v : E3 → ℝ} {h : ScatSol v} {R c₁ C μ : ℝ} {n : ℕ}
    (Φ : X n → ℝ) (u : E3) (t : ℝ) :
    perBoxCubeLHSFun v h R c₁ C μ n (fun x => t * Φ x) u
      = t ^ 2 * perBoxCubeLHSFun v h R c₁ C μ n Φ u := by
  unfold perBoxCubeLHSFun
  have h1 : ∀ w : X n → ℝ,
      (∫ x in abox n (sideAt μ (a v)), (t * Φ x) ^ 2 * w x)
        = t ^ 2 * (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 * w x) := by
    intro w
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Eventually.of_forall (fun x => by ring))
  rw [h1]
  rw [Work.BoseFixB1B.normB_const_mul]
  ring

/-! ## 2. The demand converges along the cutoff approximants -/

/-- `demandWeight` is continuous on the whole space (the divisor `1 + t μ⁻¹` is positive on the
range of `nCountB/chiMass`, which is nonnegative). -/
lemma continuous_demandWeight {v : E3 → ℝ} {μ : ℝ} (hμ : 0 < μ) {n : ℕ} (u : E3) :
    Continuous (demandWeight (v := v) μ (n := n) u) := by
  have hchi : Continuous (fun x : E3 => chiSmallB (PBM v μ) (PBℓ v μ) (PBd v μ) u x) := by
    rw [show (fun x : E3 => chiSmallB (PBM v μ) (PBℓ v μ) (PBd v μ) u x)
        = fun x => chiScale (PBℓ v μ) x
            * chiSmall (PBM v μ) (((PBℓ v μ) * (PBd v μ))⁻¹ • x - u) from by
      funext x; rw [chiSmallB]]
    exact (chiScale_continuous _).mul
      ((chiSmall_continuous_all _).comp (by fun_prop))
  have hn : Continuous (fun x : X n => Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x) := by
    rw [show (fun x : X n => Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x)
        = fun x => ∑ i : Fin n,
            (chiSmallB (PBM v μ) (PBℓ v μ) (PBd v μ) u (x i)) ^ 2 from by
      funext x; rw [Work.BoseFixB1.nCountB]]
    exact continuous_finsetSum _ fun i _ => (hchi.comp (continuous_apply i)).pow 2
  have ht : Continuous (fun x : X n => Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x
      / chiMass (PBM v μ) (PBℓ v μ) (PBd v μ) u) := by
    by_cases hc : chiMass (PBM v μ) (PBℓ v μ) (PBd v μ) u = 0
    · rw [show (fun x : X n => Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x
          / chiMass (PBM v μ) (PBℓ v μ) (PBd v μ) u) = fun _ => (0 : ℝ) from by
        funext x; rw [hc, div_zero]]
      exact continuous_const
    · exact hn.div continuous_const (fun _ => hc)
  have ht0 : ∀ x : X n, 0 ≤ Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x
      / chiMass (PBM v μ) (PBℓ v μ) (PBd v μ) u := fun x =>
    div_nonneg (Work.BoseFixB1.nCountB_nonneg (PBM v μ) (PBℓ v μ) (PBd v μ) u x)
      (Work.SmallBoxSliding.chiMass_nonneg (PBM v μ) (PBℓ v μ) (PBd v μ) u)
  rw [show demandWeight (v := v) μ (n := n) u
      = fun x => ((Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x
            / chiMass (PBM v μ) (PBℓ v μ) (PBd v μ) u) - μ) ^ 2
          / (1 + (Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x
              / chiMass (PBM v μ) (PBℓ v μ) (PBd v μ) u) * μ⁻¹) from by
    funext x; rw [demandWeight, Work.SmallBoxSliding.psiWeight]; ring]
  refine Continuous.div ((ht.sub continuous_const).pow 2)
    (continuous_const.add (ht.mul continuous_const)) ?_
  intro x
  have h1 : 0 ≤ (Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x
      / chiMass (PBM v μ) (PBℓ v μ) (PBd v μ) u) * μ⁻¹ :=
    mul_nonneg (ht0 x) (inv_nonneg.mpr hμ.le)
  linarith

/-- The `F`-weight of the demand is nonnegative. -/
lemma demandWeight_nonneg {v : E3 → ℝ} {μ : ℝ} (hμ : 0 < μ) {n : ℕ} (u : E3) (x : X n) :
    0 ≤ demandWeight (v := v) μ (n := n) u x := by
  rw [demandWeight, Work.SmallBoxSliding.psiWeight]
  refine div_nonneg (mul_nonneg zero_le_one (sq_nonneg _)) ?_
  have h := mul_nonneg (div_nonneg (Work.BoseFixB1.nCountB_nonneg (PBM v μ) (PBℓ v μ) (PBd v μ) u x)
    (Work.SmallBoxSliding.chiMass_nonneg (PBM v μ) (PBℓ v μ) (PBd v μ) u))
    (inv_nonneg.mpr hμ.le)
  linarith

/-- **The demand converges along the smooth-cutoff approximants of the sharp state.**  The weight
`demandWeight` is a *configuration* functional, so the only convergence is that of
`(cutProd (γ δ) ψ)²`, which is dominated convergence against `Cb²·K`. -/
theorem tendsto_perBoxCubeLHSFun_cutProd {v : E3 → ℝ} {h : ScatSol v} {R c₁ C μ : ℝ} {n : ℕ}
    {u : E3} {ψ : X n → ℝ} {K Cb : ℝ} {γ : ℝ → E3 → ℝ}
    (hμ : 0 < μ) (hℓ : 0 < PBℓ v μ) (hd : 0 < PBd v μ)
    (hcut : IsCutFamily (PBℓ v μ) (PBd v μ) u K γ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hCb : 0 ≤ Cb)
    (hψb : ∀ x ∈ abox n (PBℓ v μ), |ψ x| ≤ Cb) :
    Tendsto (fun δ : ℝ => perBoxCubeLHSFun v h R c₁ C μ n (cutProd (γ δ) ψ) u)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (perBoxCubeLHSFun v h R c₁ C μ n
        (sharpBoxState (dlBox (PBℓ v μ) (PBd v μ) u) ψ) u)) := by
  classical
  have hwcont : Continuous (demandWeight (v := v) μ (n := n) u) := continuous_demandWeight hμ u
  obtain ⟨Kw, hKw⟩ := (abox_compact n hℓ).exists_bound_of_continuousOn hwcont.continuousOn
  have hK0 : 0 ≤ K := hcut.1
  have hcutδ := hcut.2
  have hγsupp : ∀ δ : ℝ, 0 < δ → ∀ y, γ δ y ≠ 0 → y ∈ dlBox (PBℓ v μ) (PBd v μ) u := fun δ hδ y hy =>
    (hcutδ δ hδ).2.1 (subset_tsupport _ (Function.mem_support.mpr hy))
  have hγone : ∀ δ : ℝ, 0 < δ → ∀ y, boxMargin (PBℓ v μ) (PBd v μ) u y ≥ δ → γ δ y = 1 :=
    fun δ hδ => (hcutδ δ hδ).2.2.2.1
  have hnull : (volume : Measure (X n))
      {x : X n | ¬ GoodCollar (PBℓ v μ) (PBd v μ) u x} = 0 :=
    volume_goodCollar_compl (k := n) (L := PBℓ v μ) (d := PBd v μ) u
  have hae : ∀ᵐ x ∂((volume : Measure (X n)).restrict (abox n (PBℓ v μ))),
      GoodCollar (PBℓ v μ) (PBd v μ) u x := by
    rw [MeasureTheory.ae_iff]
    exact le_antisymm (le_trans (Measure.restrict_apply_le _ _) hnull.le) bot_le
  have hfin : IsFiniteMeasure ((volume : Measure (X n)).restrict (abox n (PBℓ v μ))) :=
    isFiniteMeasure_restrict.mpr (ne_of_lt (abox_compact n hℓ).measure_lt_top)
  set Kb : ℝ := max Kw 0 with hKbdef
  have hKb0 : 0 ≤ Kb := le_max_right _ _
  -- the convergence of the `F`-weighted integral
  have hI : Tendsto
      (fun δ : ℝ => ∫ x in abox n (PBℓ v μ),
        (cutProd (γ δ) ψ x) ^ 2 * demandWeight (v := v) μ (n := n) u x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ x in abox n (PBℓ v μ),
        (sharpBoxState (dlBox (PBℓ v μ) (PBd v μ) u) ψ x) ^ 2
          * demandWeight (v := v) μ (n := n) u x)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure (X n)).restrict (abox n (PBℓ v μ)))
      (l := nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (F := fun δ x => (cutProd (γ δ) ψ x) ^ 2 * demandWeight (v := v) μ (n := n) u x)
      (f := fun x => (sharpBoxState (dlBox (PBℓ v μ) (PBd v μ) u) ψ x) ^ 2
        * demandWeight (v := v) μ (n := n) u x)
      (bound := fun _ => Cb ^ 2 * Kb) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hprod : Continuous (fun x : X n => ∏ i : Fin n, γ δ (x i)) :=
        continuous_finsetProd (Finset.univ : Finset (Fin n))
          (fun i _ => (hcutδ δ hδ).1.continuous.comp (continuous_apply i))
      exact ((hprod.mul hψ.continuous).pow 2 |>.mul hwcont).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      filter_upwards [ae_restrict_mem (abox_isClosed n (PBℓ v μ)).measurableSet] with x hx
      have h01 : ∀ y, 0 ≤ γ δ y ∧ γ δ y ≤ 1 := (hcutδ δ hδ).2.2.1
      have hprod : 0 ≤ ∏ i : Fin n, γ δ (x i) := Finset.prod_nonneg (fun i _ => (h01 (x i)).1)
      have hprod1 : (∏ i : Fin n, γ δ (x i)) ≤ 1 :=
        Finset.prod_le_one₀ (fun i _ => (h01 (x i)).1) (fun i _ => (h01 (x i)).2)
      have hsq : (cutProd (γ δ) ψ x) ^ 2 ≤ Cb ^ 2 := by
        have hcutb : |cutProd (γ δ) ψ x| ≤ Cb := by
          rw [cutProd_apply, abs_mul, abs_of_nonneg hprod]
          calc (∏ i : Fin n, γ δ (x i)) * |ψ x| ≤ 1 * Cb :=
                mul_le_mul hprod1 (hψb x hx) (abs_nonneg _) zero_le_one
            _ = Cb := one_mul Cb
        simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg (cutProd (γ δ) ψ x)) hcutb 2
      have hwle : demandWeight (v := v) μ (n := n) u x ≤ Kb :=
        le_trans (le_trans (le_abs_self _) (hKw x hx)) (le_max_left _ _)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
        (demandWeight_nonneg hμ u x))]
      exact mul_le_mul hsq hwle (demandWeight_nonneg hμ u x) (by positivity)
    · exact integrable_const _
    · filter_upwards [hae] with x hx
      exact (tendsto_cutProd_sq_pointwise hγsupp hγone hx).mul_const
        (demandWeight (v := v) μ (n := n) u x)
  -- the convergence of the mass
  have hN : Tendsto (fun δ : ℝ => Work.BoseBoxFix.normB v μ n (cutProd (γ δ) ψ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (Work.BoseBoxFix.normB v μ n (sharpBoxState (dlBox (PBℓ v μ) (PBd v μ) u) ψ))) := by
    have h := tendsto_cutProd_mass (k := n) (L := PBℓ v μ) (d := PBd v μ) (u := u) (ψ := ψ)
      (K := K) (γ := γ) hℓ hd hcut hψ.continuous
    simpa only [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB] using h
  -- assembly of the convergent pieces
  have hcomb := ((((hI.const_mul (w1MassB h (PBM v μ) (PBℓ v μ) (PBd v μ) u)).const_mul c₁).sub
      (hN.const_mul ((1 / 2) * μ ^ 2 * w1MassB h (PBM v μ) (PBℓ v μ) (PBd v μ) u))).sub
      (((hN.const_mul (((μ ^ 2 * (a v) * ((R / (PBℓ v μ * PBd v μ)) ^ 2
            + PBKB v μ ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
              * chiMass (PBM v μ) (PBℓ v μ) (PBd v μ) u))).add
        (hN.const_mul (μ * (a v)))).const_mul C))
  convert hcomb using 1
  · funext δ
    rw [perBoxCubeLHSFun_eq]
  · rw [perBoxCubeLHSFun_eq]

/-! ## 3. Nonnegativity of the matched kinetic word, and the empty slot set -/

/-- **The matched kinetic word is nonnegative** (both slots are sums of squares). -/
theorem sbKinCube_nonneg {v : E3 → ℝ} {μ : ℝ} {u : E3} {ε₀ : ℝ}
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) {n : ℕ} (Ψ : X n → ℝ) :
    0 ≤ Work.BoseFixB1B.sbKinCube v μ u Ψ := by
  have hε : 0 ≤ (paramsAt μ (a v)).eT := (Work.BoseFixB1.adm_eT_bounds hAdm).1
  have hgap : 0 ≤ Work.BoseFixB1.bGapCoeff v μ := by
    rw [Work.BoseFixB1.bGapCoeff]
    exact Work.SmallBoxTBWord.tbGapCoeff_nonneg hε
  unfold Work.BoseFixB1B.sbKinCube Work.BoseFixB1B.cubeSpectral Work.UBBInputs8.tBwordKinInd
    Work.UBBInputs8.tBdiagFormInd
  refine add_nonneg (mul_nonneg hgap (Work.BoseFixB1S.cnPlusBoxInd_nonneg _ _ _ _)) ?_
  refine Finset.sum_nonneg fun i _ => mul_nonneg ?_ ?_
  · positivity
  refine integral_nonneg fun p => mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg _ _) ?_
  refine mul_nonneg (inv_nonneg.mpr (pow_nonneg (le_of_lt (Work.BoseFixB1.adm_ell_pos hAdm)) 3)) ?_
  exact integral_nonneg fun x => sq_nonneg _

/-- **The matched word of a `0`-particle state vanishes**: every slot sum is empty and the
potential density `qLHSden 0` is `0`. -/
theorem sbWordCube_zero_particle {v : E3 → ℝ} (h : ScatSol v) (μ : ℝ) (u : E3)
    (Ψ : X 0 → ℝ) : Work.BoseFixB1B.sbWordCube v h μ u Ψ = 0 := by
  simp only [Work.BoseFixB1B.sbWordCube, Work.BoseFixB1B.sbKinCube, Work.BoseFixB1B.cubeSpectral,
    Work.BoseFixB1.sbPot, Work.SmallBoxSliding.qLHSwordB, Work.UBBInputs8.cnPlusBoxInd,
    Work.UBBInputs8.tBwordKinInd, Work.UBBInputs8.tBdiagFormInd, Work.BoseFixB1.sbCut,
    Submission.BoseGases.qLHSword, Submission.BoseGases.qLHSden]
  rw [show Submission.BoseGases.pairSet 0 = ∅ from Subsingleton.elim _ _]
  simp

/-- **The word of the empty slot piece is nonnegative**: its potential word vanishes
(`qLHSwordB_slotPiece_empty_eq_zero`) and its kinetic word is nonnegative. -/
theorem sbWordCube_slotPiece_empty_nonneg {v : E3 → ℝ} {h : ScatSol v} {μ : ℝ} {ε₀ : ℝ}
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ)) (u : E3) :
    0 ≤ Work.BoseFixB1B.sbWordCube v h μ u
      (slotPiece (dlBox (PBℓ v μ) (PBd v μ) u) (∅ : Finset (Fin n)) (Φ : X n → ℝ)) := by
  have hkin : 0 ≤ Work.BoseFixB1B.sbKinCube v μ u
      (slotPiece (dlBox (PBℓ v μ) (PBd v μ) u) (∅ : Finset (Fin n)) (Φ : X n → ℝ)) :=
    sbKinCube_nonneg hAdm _
  have hpot : Work.BoseFixB1.sbPot h μ u
      (slotPiece (dlBox (PBℓ v μ) (PBd v μ) u) (∅ : Finset (Fin n)) (Φ : X n → ℝ)) = 0 :=
    Work.BoseFixB1B.qLHSwordB_slotPiece_empty_eq_zero (v := v) (h := h) hAdm Φ u
  rw [Work.BoseFixB1B.sbWordCube, hpot, add_zero]
  exact hkin

end Work.BoseB1Cube
