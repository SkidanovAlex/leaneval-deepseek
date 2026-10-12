import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseSWE.DefsE
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseSWE.nomSharpRowE_body` — smooth ⟹ sharp in the **slack-carrying**
# nominal arity passage

Verbatim copy of the PROVED `Work.BoseB1Cube.nomSharpRow_body`
(`Submission/Work/BoseB1Cube/nomArbAux.lean` §5), with the nominal demand `nomRow` replaced by its
slack-carrying twin `nomRowE` and `nomCoeff` by `nomCoeffE`.  The three places where the twin's
proof touches the row are:

* the degenerate case (vanishing sharp mass): the slack-carrying row vanishes together with the
  `abox`-mass (`nomRowE_eq_zero_of_normB_eq_zero`), instead of `nomRow_eq_coeff`;
* the demand convergence along the cutoff approximants (`tendsto_nomRowE_cutProd`);
* the two homogeneity steps (`nomRowE_const_mul`).

Everything else (`sbWordCube_eq_zero_of_ae_eq_zero`, `sbWordCube_zero_particle`,
`sharpState_ae_zero_of_normB_eq_zero`, `CutProdConvBody`, `sbWordCube_smul`,
`tendsto_cutProd_mass`, `exists_isCutFamily_of_smoothCutoff`, `exists_smoothCutoffB`) transfers
verbatim.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseSWE

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical

theorem nomSharpRowE_body {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R c₁ C CE ε₀ : ℝ}
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (hε₀ : 0 < ε₀)
    (hinB : Work.BoseSWE.NomInBoxRowBodyE v h R c₁ C CE ε₀)
    (hconvB : Work.BoseB1Cube.CutProdConvBody v h R ε₀) :
    Work.BoseSWE.NomSharpRowBodyE v h R c₁ C CE ε₀ := by
  classical
  intro μ hμ k ψ hψcd hψperm u hu
  have hℓ : 0 < Work.BoseFixB1B.PBℓ v μ := Work.BoseFixB1.adm_ell_pos hμ
  have hd : 0 < Work.BoseFixB1B.PBd v μ := Work.BoseFixB1.adm_d_pos hμ
  rcases eq_or_ne (Work.BoseBoxFix.normB v μ k
      (Work.BoseFixB1B.sharpBoxState (Work.BoseFixB1B.PBB v μ u) ψ)) 0 with hm0 | hm0
  · -- degenerate case: the demand vanishes and so does the word
    have hae := Work.BoseB1Cube.sharpState_ae_zero_of_normB_eq_zero (v := v) (μ := μ) (u := u)
      hψcd.continuous hm0
    have hword : Work.BoseFixB1B.sbWordCube v h μ u
        (Work.BoseFixB1B.sharpBoxState (Work.BoseFixB1B.PBB v μ u) ψ) = 0 := by
      rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact Work.BoseB1Cube.sbWordCube_zero_particle (v := v) h μ u _
      · refine Work.BoseB1Cube.sbWordCube_eq_zero_of_ae_eq_zero (v := v) (h := h) (μ := μ)
          (u := u) (N := k) hℓ hd (Nat.pos_of_ne_zero hk0) ?_ hae
        exact hψcd.continuous.measurable.indicator
          (Work.PerSector.Work.PerSector.slotBox_measurable
            (ι := Fin k) (Work.SmallBoxSliding.measurableSet_dlBox
              (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u))
    rw [hword, nomRowE_eq_zero_of_normB_eq_zero (h := h) hm0]
  · -- nondegenerate case: the cutoff approximants and the limit
    have hmpos : 0 < Work.BoseBoxFix.normB v μ k
        (Work.BoseFixB1B.sharpBoxState (Work.BoseFixB1B.PBB v μ u) ψ) :=
      lt_of_le_of_ne (Work.BoseFixB1.normB_nonneg _) (Ne.symm hm0)
    obtain ⟨K, γ, hcut⟩ := Work.BoseFixB1B.exists_isCutFamily_of_smoothCutoff
      (Work.BoseFixB1B.exists_smoothCutoffB hℓ hd u)
    obtain ⟨Cb0, hCb0⟩ := (Submission.BoseGases.abox_compact k hℓ).exists_bound_of_continuousOn
      hψcd.continuous.continuousOn
    set Cb : ℝ := max Cb0 0 with hCbdef
    have hCb : 0 ≤ Cb := le_max_right _ _
    have hψb : ∀ x ∈ Submission.BoseGases.abox k (Work.BoseFixB1B.PBℓ v μ), |ψ x| ≤ Cb := by
      intro x hx
      rw [← Real.norm_eq_abs]
      exact le_trans (hCb0 x hx) (le_max_left _ _)
    have hdem := tendsto_nomRowE_cutProd (v := v) (h := h) (R := R) (c₁ := c₁) (C := C)
      (CE := CE) (μ := μ) (n := k) (u := u) (ψ := ψ) (K := K) (γ := γ)
      hℓ hd hcut hψcd.continuous
    have hword := hconvB μ hμ u hu k ψ hψcd hCb hψb hcut
    have hmass := Work.BoseFixB1B.tendsto_cutProd_mass (k := k) (L := Work.BoseFixB1B.PBℓ v μ)
      (d := Work.BoseFixB1B.PBd v μ) (u := u) (ψ := ψ) (K := K) (γ := γ)
      hℓ hd hcut hψcd.continuous
    refine le_of_tendsto_of_tendsto hdem hword ?_
    filter_upwards [hmass.eventually (Ioi_mem_nhds hmpos), self_mem_nhdsWithin] with δ hδm hδpos
    -- the normalised approximant
    set t : ℝ := (Real.sqrt (∫ x in Submission.BoseGases.abox k (Work.BoseFixB1B.PBℓ v μ),
      (Work.BoseFixB1B.cutProd (γ δ) ψ x) ^ 2))⁻¹ with ht
    have htne : t ≠ 0 := inv_ne_zero (Real.sqrt_pos_of_pos hδm).ne'
    have hcdδ : ContDiff ℝ (⊤ : ENat)
        (fun x : X k => t * Work.BoseFixB1B.cutProd (γ δ) ψ x) :=
      contDiff_const.mul (Work.BoseFixB1B.contDiff_cutProd (hcut.2 δ hδpos).1 hψcd)
    have hpermδ : Submission.BoseGases.PermInvariant k
        (fun x : X k => t * Work.BoseFixB1B.cutProd (γ δ) ψ x) := by
      intro σ x
      show t * Work.BoseFixB1B.cutProd (γ δ) ψ (Submission.BoseGases.actPerm k σ x)
        = t * Work.BoseFixB1B.cutProd (γ δ) ψ x
      congr 1
      simp only [Work.BoseFixB1B.cutProd_apply]
      rw [hψperm σ x]
      congr 1
      simpa only [Submission.BoseGases.actPerm] using
        Equiv.prod_comp σ (fun j : Fin k => γ δ (x j))
    have hmassδ : 0 < ∫ x in Submission.BoseGases.abox k (Work.BoseFixB1B.PBℓ v μ),
        (t * Work.BoseFixB1B.cutProd (γ δ) ψ x) ^ 2 := by
      rw [show (fun x : X k => (t * Work.BoseFixB1B.cutProd (γ δ) ψ x) ^ 2)
          = (fun x => t ^ 2 * (Work.BoseFixB1B.cutProd (γ δ) ψ x) ^ 2) from by funext x; ring]
      rw [MeasureTheory.integral_const_mul]
      exact mul_pos (sq_pos_of_ne_zero htne) hδm
    have hnormδ : (∫ x in Submission.BoseGases.abox k (Work.BoseFixB1B.PBℓ v μ),
        (t * Work.BoseFixB1B.cutProd (γ δ) ψ x) ^ 2) = 1 := by
      rw [show (fun x : X k => (t * Work.BoseFixB1B.cutProd (γ δ) ψ x) ^ 2)
          = (fun x => t ^ 2 * (Work.BoseFixB1B.cutProd (γ δ) ψ x) ^ 2) from by funext x; ring]
      rw [MeasureTheory.integral_const_mul]
      have ht2 : t ^ 2 = (∫ x in Submission.BoseGases.abox k (Work.BoseFixB1B.PBℓ v μ),
          (Work.BoseFixB1B.cutProd (γ δ) ψ x) ^ 2)⁻¹ := by
        rw [ht, inv_pow, Real.sq_sqrt hδm.le]
      rw [ht2, inv_mul_cancel₀ (ne_of_gt hδm)]
    have hneδ : (fun x : X k => t * Work.BoseFixB1B.cutProd (γ δ) ψ x) ≠ 0 := by
      intro hzero
      have h0 : (∫ x in Submission.BoseGases.abox k (Work.BoseFixB1B.PBℓ v μ),
          (t * Work.BoseFixB1B.cutProd (γ δ) ψ x) ^ 2) = 0 := by
        have hfun : (fun x : X k => (t * Work.BoseFixB1B.cutProd (γ δ) ψ x) ^ 2) = 0 := by
          funext x
          rw [congrFun hzero x]
          simp
        rw [hfun]
        simp
      linarith [hmassδ]
    have hsuppδ : ∀ᵐ x ∂((volume : Measure (X k)).restrict
        (Submission.BoseGases.abox k (Work.BoseFixB1B.PBℓ v μ))),
        (fun x : X k => t * Work.BoseFixB1B.cutProd (γ δ) ψ x) x ≠ 0 →
          ∀ i : Fin k, x i ∈ Submission.BoseGases.dlBox
            (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u := by
      refine Eventually.of_forall (fun x hx i => ?_)
      have hcp : Work.BoseFixB1B.cutProd (γ δ) ψ x ≠ 0 := by
        intro h0
        exact hx (by simp only [h0, mul_zero])
      rw [Work.BoseFixB1B.cutProd_apply] at hcp
      have hγ : γ δ (x i) ≠ 0 := by
        intro h0
        exact hcp (by rw [Finset.prod_eq_zero (Finset.mem_univ i) h0, zero_mul])
      exact (hcut.2 δ hδpos).2.1 (subset_tsupport _ (Function.mem_support.mpr hγ))
    -- the in-box row at the normalised approximant
    let Φbd : Work.BoseKinLoc.BoxState k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) :=
      { toFun := fun x : X k => t * Work.BoseFixB1B.cutProd (γ δ) ψ x,
        contDiff := hcdδ, symm := hpermδ, nezero := hneδ }
    have hPer := hinB μ hμ k Φbd u hu (by simpa only [Φbd] using hsuppδ)
    have hrow : nomRowE v h R c₁ C CE μ k u
          (fun x : X k => t * Work.BoseFixB1B.cutProd (γ δ) ψ x)
        ≤ Work.BoseFixB1B.sbWordCube v h μ u
          (fun x : X k => t * Work.BoseFixB1B.cutProd (γ δ) ψ x) := hPer
    -- strip the normalisation
    rw [nomRowE_const_mul, Work.BoseFixB1S.sbWordCube_smul] at hrow
    exact le_of_mul_le_mul_left hrow (by positivity : 0 < t ^ 2)

end Work.BoseSWE
