import ChallengeDeps
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.FarResidBaux.farEnvSideB
import Submission.Work.BoseFixR.FarThreeQSlots
import Submission.Work.BoseFixR.LatGreen.W1fun_cellPair_eq_fullPair
import Submission.Work.BoseFixR.LatGreen.W1fun_pairKernel_latDistL_lintegral_lt_top
import Submission.Work.BoseFixR.LatGreen.coulomb_pair_eq_autocorr_integral_ae
import Submission.Work.BoseFixR.absBpSumSmulLe
import Submission.Work.BoseFixR.farLatRow
import Submission.Work.BoseFixR.farLinArith
import Submission.Work.BoseFixR.farRadSlot
import Submission.Work.BoseFixR.qwPairLinEq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.latRow_le_sharp_ae`

The sharp weighted lattice-to-continuum sampling bound for `W₁ = W1fun v h (ell v μ)`, in the form
in which the a.e.-nonnegativity of `W₁` (`Submission.BoseGases.wScaled_g0_nonneg_ae`) replaces the
pointwise nonnegativity used in `Work.BoseFixR.lattice_W1sq_over_tau_le_sharp`.

Three steps of the pointwise proof are factored out into delegated lemmas:

* `Work.BoseFixR.LatGreen.W1fun_pairKernel_latDistL_lintegral_lt_top` — finiteness of the cell pair
  `∫⁻` in the periodic-distance form `(latDistL ℓ ·)⁻¹` (the `hfin` block);
* `Work.BoseFixR.LatGreen.W1fun_cellPair_eq_fullPair` — the cell double integral of the
  periodisation against the full-space Coulomb pair integral of the charge (the
  `hstep5`/`hstep6a`/`hstep6b` block);
* `Work.BoseFixR.LatGreen.coulomb_pair_eq_autocorr_integral_ae` — the position-space
  Coulomb/autocorrelation identity for an a.e.-nonnegative kernel (the only place where pointwise
  nonnegativity was genuinely used, through the `U⁺ = max U 0` representative).

Everything else is the `LatGreen`-chain of `lattice_W1sq_over_tau_le_sharp.lean`, which already
takes the a.e. form.
-/

noncomputable section

open MeasureTheory Metric
open scoped Real BigOperators

namespace Work.BoseFixR

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The sharp full-lattice row at a.e.-nonnegative `W₁` -/

/-- **The sharp full-lattice row, a.e.-nonnegativity form.**  At the small-support regime
`100 R ≤ ℓ`,

`Σ'_{k≠0} Ŵ₁(q_k)²/‖q_k‖² ≤ 2·(2π)⁻³·ℓ³·∫ Ŵ₁(q)²/(2‖q‖²)`

under the *a.e.* hypothesis `0 ≤ᵐ W₁`.  This is `Work.BoseFixR.lwsq_lattice_row_sharp` with the
pointwise hypothesis replaced by the a.e. one; the only step of the pointwise proof that consumed
pointwise nonnegativity was the position-space Coulomb identity, now taken in the a.e. form
(`Work.BoseFixR.LatGreen.coulomb_pair_eq_autocorr_integral_ae`). -/
theorem lwsq_lattice_row_sharp_ae {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) (hreg : 100 * R ≤ ℓ)
    (hW : MeasureTheory.Integrable (W1fun v h ℓ))
    (hWae : 0 ≤ᵐ[(MeasureTheory.volume : Measure E3)] (W1fun v h ℓ)) :
    (∑' k : Fin 3 → ℤ, if k = 0 then 0 else
        (chat (W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec k)) ^ 2 / ‖ℓ⁻¹ • Work.BoseB4.vec k‖ ^ 2)
      ≤ 2 * ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
          ∫ q : E3, (chat (W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2) := by
  classical
  have hWev : ∀ x : E3, W1fun v h ℓ (-x) = W1fun v h ℓ x := isEven_W1fun h hvrad ℓ
  have hWper : ∀ x : E3, Summable (fun n : Fin 3 → ℤ => W1fun v h ℓ (x - lat ℓ n)) :=
    LatGreen.W1funPeriodSummable h hR hℓ hv_supp
  have hsum := chat_sq_div_summable h hv hvrad hR hℓ hv_supp hRℓ
  have hint : MeasureTheory.Integrable
      (fun q : E3 => (chat (W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2)) :=
    IntegrableChatW1sq h hv hvrad hR hℓ hv_supp hRℓ
  -- ## 1.1 finiteness of the `(latDistL)⁻¹` pair integral on the cell (delegated)
  have hfin : (∫⁻ p in (cell ℓ ×ˢ cell ℓ),
      ENNReal.ofReal (LatGreen.period (W1fun v h ℓ) ℓ p.1
        * LatGreen.period (W1fun v h ℓ) ℓ p.2
        * (latDistL ℓ (p.1 - p.2))⁻¹)) < ⊤ :=
    LatGreen.W1fun_pairKernel_latDistL_lintegral_lt_top h hv hvrad hR hℓ hv_supp hRℓ
  -- ## 1.2 its three consumers, and the lattice Parseval identity
  have hB := FarLat.latGreen_period_integrable hℓ hW hWae hWper hfin
  have hmono := FarLat.latGreen_le_latDistL_pair hℓ hW hWae hWper hB hfin
  have hP := LatGreen.LatGreenParsevalB hℓ hW hWev hWper hsum hB
  -- ## 1.3 the cell integral of the Green kernel equals the full-space pair integral (delegated:
  -- `hstep5` + `hstep6a` + `hstep6b`)
  have hstep := LatGreen.W1fun_cellPair_eq_fullPair h hℓ hv_supp hreg
  -- ## 1.4 the iterated cell integral is the product cell integral (Fubini)
  have hμc : MeasureTheory.volume.restrict (cell ℓ ×ˢ cell ℓ)
      = ((MeasureTheory.volume : Measure E3).restrict (cell ℓ)).prod
        ((MeasureTheory.volume : Measure E3).restrict (cell ℓ)) := by
    rw [MeasureTheory.Measure.volume_eq_prod E3 E3]
    exact (MeasureTheory.Measure.prod_restrict _ _).symm
  have hfub : (∫ x in cell ℓ, ∫ y in cell ℓ,
        LatGreen.period (W1fun v h ℓ) ℓ x * LatGreen.period (W1fun v h ℓ) ℓ y
          * (ℓ ^ 2 * LatGreen.latGreen (ℓ⁻¹ • (x - y))))
      = ∫ p in (cell ℓ ×ˢ cell ℓ),
          LatGreen.period (W1fun v h ℓ) ℓ p.1 * LatGreen.period (W1fun v h ℓ) ℓ p.2
            * (ℓ ^ 2 * LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2))) := by
    have hPae : AEMeasurable (LatGreen.period (W1fun v h ℓ) ℓ)
        ((MeasureTheory.volume : Measure E3).restrict (cell ℓ)) :=
      (LatGreen.integrableOn_period hℓ hW hWper).1.aemeasurable
    have hasm : AEStronglyMeasurable
        (fun p : E3 × E3 =>
          LatGreen.period (W1fun v h ℓ) ℓ p.1 * LatGreen.period (W1fun v h ℓ) ℓ p.2
            * (ℓ ^ 2 * LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2))))
        (((MeasureTheory.volume : Measure E3).restrict (cell ℓ)).prod
          ((MeasureTheory.volume : Measure E3).restrict (cell ℓ))) := by
      have h1 : AEMeasurable (fun p : E3 × E3 => LatGreen.period (W1fun v h ℓ) ℓ p.1)
          (((MeasureTheory.volume : Measure E3).restrict (cell ℓ)).prod
            ((MeasureTheory.volume : Measure E3).restrict (cell ℓ))) := hPae.comp_fst
      have h2 : AEMeasurable (fun p : E3 × E3 => LatGreen.period (W1fun v h ℓ) ℓ p.2)
          (((MeasureTheory.volume : Measure E3).restrict (cell ℓ)).prod
            ((MeasureTheory.volume : Measure E3).restrict (cell ℓ))) := hPae.comp_snd
      have h3 : AEMeasurable
          (fun p : E3 × E3 => ℓ ^ 2 * LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2)))
          (((MeasureTheory.volume : Measure E3).restrict (cell ℓ)).prod
            ((MeasureTheory.volume : Measure E3).restrict (cell ℓ))) := by
        refine ((LatGreen.measurable_latGreen.comp
          ((measurable_fst.sub measurable_snd).const_smul (ℓ⁻¹ : ℝ))).const_mul _).aemeasurable
      exact ((h1.mul h2).mul h3).aestronglyMeasurable
    have hint' : MeasureTheory.Integrable
        (fun p : E3 × E3 =>
          LatGreen.period (W1fun v h ℓ) ℓ p.1 * LatGreen.period (W1fun v h ℓ) ℓ p.2
            * (ℓ ^ 2 * LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2))))
        (((MeasureTheory.volume : Measure E3).restrict (cell ℓ)).prod
          ((MeasureTheory.volume : Measure E3).restrict (cell ℓ))) := by
      have hB' : MeasureTheory.Integrable
          (fun p : E3 × E3 =>
            |LatGreen.period (W1fun v h ℓ) ℓ p.1 * LatGreen.period (W1fun v h ℓ) ℓ p.2
              * (ℓ ^ 2 * LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2)))|)
          (((MeasureTheory.volume : Measure E3).restrict (cell ℓ)).prod
            ((MeasureTheory.volume : Measure E3).restrict (cell ℓ))) := by
        rw [← hμc]
        exact hB
      exact hB'.mono' hasm (Filter.Eventually.of_forall fun p => le_of_eq (by
        rw [Real.norm_eq_abs]))
    have h := MeasureTheory.integral_prod
      (fun p : E3 × E3 =>
        LatGreen.period (W1fun v h ℓ) ℓ p.1 * LatGreen.period (W1fun v h ℓ) ℓ p.2
          * (ℓ ^ 2 * LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2)))) hint'
    rw [hμc]
    exact h.symm
  -- ## 1.5 the two Coulomb identities
  have hpair := LatGreen.coulomb_pair_eq_autocorr_integral_ae hW hWae hWev hint
  have hcoul := coulomb_autocorr_eq hW hWae hWev hint
  -- ## 1.6 the chain
  calc (∑' k : Fin 3 → ℤ, if k = 0 then 0 else
        (chat (W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec k)) ^ 2
          / ‖ℓ⁻¹ • Work.BoseB4.vec k‖ ^ 2)
      = ∫ x in cell ℓ, ∫ y in cell ℓ,
          LatGreen.period (W1fun v h ℓ) ℓ x * LatGreen.period (W1fun v h ℓ) ℓ y
            * (ℓ ^ 2 * LatGreen.latGreen (ℓ⁻¹ • (x - y))) := hP
    _ = ∫ p in (cell ℓ ×ˢ cell ℓ),
          LatGreen.period (W1fun v h ℓ) ℓ p.1 * LatGreen.period (W1fun v h ℓ) ℓ p.2
            * (ℓ ^ 2 * LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2))) := hfub
    _ ≤ (ℓ ^ 3 / (4 * Real.pi)) * ∫ p in (cell ℓ ×ˢ cell ℓ),
          LatGreen.period (W1fun v h ℓ) ℓ p.1 * LatGreen.period (W1fun v h ℓ) ℓ p.2
            * (latDistL ℓ (p.1 - p.2))⁻¹ := hmono
    _ = (ℓ ^ 3 / (4 * Real.pi)) *
          ∫ p : E3 × E3, W1fun v h ℓ p.1 * W1fun v h ℓ p.2 * (‖p.1 - p.2‖)⁻¹ := by
        rw [hstep]
    _ = (ℓ ^ 3 / (4 * Real.pi)) *
          ∫ u : E3, (∫ x : E3, W1fun v h ℓ x * W1fun v h ℓ (x + u)) / ‖u‖ := by
        rw [← hpair]
        refine congrArg (fun t => (ℓ ^ 3 / (4 * Real.pi)) * t) ?_
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
    _ = (ℓ ^ 3 / (4 * Real.pi)) *
          (8 * Real.pi * (((2 * Real.pi) ^ 3)⁻¹ *
            ∫ q : E3, (chat (W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2))) := by rw [hcoul]
    _ = 2 * ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
          ∫ q : E3, (chat (W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2) := by
        have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
        field_simp
        ring

/-! ## 2. The cube row -/

/-- **The cube row with the sharp constant, a.e.-nonnegativity form.**  This is
`Work.BoseFixR.lattice_W1sq_over_tau_le_sharp` with the pointwise hypothesis on `W₁` replaced by
the a.e. one, on top of `lwsq_lattice_row_sharp_ae`. -/
theorem lattice_W1sq_over_tau_le_sharp_ae {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v) {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) (hreg : 100 * R ≤ ℓ)
    (hW : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ))
    (hWae : 0 ≤ᵐ[(MeasureTheory.volume : Measure E3)] (Work.BoseFixR.W1fun v h ℓ)) (N : ℕ) :
    (∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (Work.BoseBoxFock.kmomLab ℓ N k)) ^ 2
          / (2 * ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2))
      ≤ (6 / 5) * ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
          ∫ q : EuclideanSpace ℝ (Fin 3),
            (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2) := by
  classical
  have hsum := chat_sq_div_summable h hv hvrad hR hℓ hv_supp hRℓ
  have hkey := lwsq_lattice_row_sharp_ae h hv hvrad hR hℓ hv_supp hRℓ hreg hW hWae
  set F : (Fin 3 → ℤ) → ℝ := fun m => if m = 0 then 0
      else (chat (W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec m)) ^ 2
        / ‖ℓ⁻¹ • Work.BoseB4.vec m‖ ^ 2 with hF
  set T : Finset (Fin 3 → ℤ) :=
    ((Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0).image
      (Work.BoseBoxFock.labVec N) with hT
  have hFnn : ∀ m : Fin 3 → ℤ, 0 ≤ F m := by
    intro m
    rw [hF]
    by_cases hm : m = 0
    · simp [hm]
    · simp only [hm, if_false]
      exact div_nonneg (sq_nonneg _) (by positivity)
  have hlabVec_zero : Work.BoseBoxFock.labVec N (0 : Work.BoseBoxFock.Lab N) = 0 := by
    funext i
    simp [Work.BoseBoxFock.labVec]
  have hT0 : (0 : Fin 3 → ℤ) ∉ T := by
    rw [hT, Finset.mem_image]
    rintro ⟨k, hk, hk0⟩
    rw [Finset.mem_erase] at hk
    exact hk.1 (Work.BoseFixR.labVec_injective N (by rw [hk0, hlabVec_zero]))
  have hsumF : Summable F := by rw [hF]; exact hsum
  have hTsummand : ∀ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
      (chat (W1fun v h ℓ) (Work.BoseBoxFock.kmomLab ℓ N k)) ^ 2
          / (2 * ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2)
        = (1 / 2) * F (Work.BoseBoxFock.labVec N k) := by
    intro k hk
    have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
    have hlv : Work.BoseBoxFock.labVec N k ≠ 0 := by
      intro hh
      exact hk0 (Work.BoseFixR.labVec_injective N (by rw [hh, hlabVec_zero]))
    rw [hF]
    simp only [hlv, if_false]
    rw [Work.BoseBoxFock.GramLab.kmomLab_eq_smul_vec]
    ring
  have hcube : (∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
        (chat (W1fun v h ℓ) (Work.BoseBoxFock.kmomLab ℓ N k)) ^ 2
          / (2 * ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2))
      = (1 / 2) * ∑ m ∈ T, F m := by
    rw [hT, Finset.mul_sum]
    rw [Finset.sum_image (f := fun m => (1 / 2) * F m)
      (g := Work.BoseBoxFock.labVec N)
      (fun x _ y _ hxy => Work.BoseFixR.labVec_injective N hxy)]
    exact Finset.sum_congr rfl fun k hk => hTsummand k hk
  have hle : (∑ m ∈ T, F m) ≤ ∑' m : Fin 3 → ℤ, F m :=
    Summable.sum_le_tsum T (fun i _ => hFnn i) hsumF
  have hInt : 0 ≤ ∫ q : EuclideanSpace ℝ (Fin 3),
      (chat (W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2) :=
    integral_nonneg fun q => div_nonneg (sq_nonneg _) (by positivity)
  have hkey' : (∑' m : Fin 3 → ℤ, F m) ≤ 2 * ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
      ∫ q : EuclideanSpace ℝ (Fin 3), (chat (W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2) := by
    rw [hF]; exact hkey
  calc (∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
        (chat (W1fun v h ℓ) (Work.BoseBoxFock.kmomLab ℓ N k)) ^ 2
          / (2 * ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2))
      = (1 / 2) * ∑ m ∈ T, F m := hcube
    _ ≤ (1 / 2) * ∑' m : Fin 3 → ℤ, F m :=
        mul_le_mul_of_nonneg_left hle (by norm_num)
    _ ≤ (1 / 2) * (2 * ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
          ∫ q : EuclideanSpace ℝ (Fin 3), (chat (W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hkey' (by norm_num)
    _ = ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
          ∫ q : EuclideanSpace ℝ (Fin 3), (chat (W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2) := by ring
    _ ≤ (6 / 5) * ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
          ∫ q : EuclideanSpace ℝ (Fin 3), (chat (W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2) := by
        nlinarith [hInt, mul_nonneg (by positivity : (0:ℝ) ≤ ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3) hInt]

/-! ## 3. The target -/

/-- **The sharp weighted lattice row at `ℓ = ell v μ` (a.e.-nonnegativity form).**

`Work.BoseFixR.latRow v h μ N` is `Σ_{k ∈ excited (Lab N)} Ŵ₁(q_k)²/(2‖q_k‖²)` with
`Ŵ₁ = chat (W1fun v h (ell v μ))` and `q_k = kmomLab (ell v μ) N k`.  The claim is that it is at
most `(6/5)·(ell v μ)³·farMass v h μ`, where `farMass v h μ = (2π)⁻³ ∫ Ŵ₁(q)²/(2‖q‖²) dq`.

This is the sharp form of `Work.BoseFixR.lattice_W1sq_over_tau_le_sharp` (in this workspace,
sorry-free, with the constant `6/5`) but with the pointwise hypothesis `0 ≤ W1fun v h ℓ` replaced by
the only available a.e. statement.  The pointwise nonnegativity is *not* derivable in the workspace
(`W1fun = wScaled ℓ (g0 v h)`, `g0 v h = v·(1 − Classical.choose h)` and only `0 ≤ᵐ g0` is known),
while `0 ≤ᵐ[volume] (W1fun v h (ell v μ))` and the integrability of `W1fun` both follow from the
hypotheses through `Submission.BoseGases.wScaled_g0_nonneg_ae` and
`Submission.BoseGases.wScaled_g0_integrable` (with `0 < ell v μ` from `Work.BoseFixR.ell_pos'`),
so no extra hypothesis is needed here.

Route: copy the proofs of `lwsq_lattice_row_sharp` and `lattice_W1sq_over_tau_le_sharp`
(`Submission/Work/BoseFixR/lattice_W1sq_over_tau_le_sharp.lean`), replacing `0 ≤ W1fun v h ℓ` by
`0 ≤ᵐ[volume] (W1fun v h ℓ)`.  In those proofs the pointwise hypothesis `hWnn` is used in exactly
two places, both of which accept the a.e. form: (i) the definition
`hWae := Filter.Eventually.of_forall hWnn` (delete it and take `hWae` as the hypothesis); (ii) the
single line `have hpair := LatGreen.coulomb_pair_eq_autocorr_integral hW hWnn hWev hint`, which must
be replaced by an a.e. version of that position-space identity.  The latter is available by the same
`U⁺ = max U 0` trick that the already-proved `Work.BoseFixR.coulomb_autocorr_eq`
(`Submission/Work/BoseFixR/farLatFourier.lean`) uses: pass to `Up = max U 0` (pointwise nonneg,
even, `Up =ᵐ U`), apply `LatGreen.coulomb_pair_eq_autocorr_integral` to `Up` and transfer back along
`Up =ᵐ U` using `Work.BoseB7AK.C3Q.chat_congr_ae` and `Work.BoseFixR.autocorr_congr_ae` for the
right-hand side and `MeasureTheory.quasiMeasurePreserving_fst`/`_snd` together with
`MeasureTheory.QuasiMeasurePreserving.ae_eq_comp` (or plain `integral_congr_ae` under
`volume.prod volume`) for the left-hand side.
Everything else in the two proofs (the `W1fun`-specific `chat_sq_div_summable`, `W1funPeriodSummable`,
`IntegrableChatW1sq`, `tsupport_W1fun_subset`, `isEven_W1fun`, `lwsq_period_eq_of_mem_cell`,
`lwsq_W1fun_eq_zero_of_not_mem_cell`, and the generic `FarLat.*`/`LatGreen.*` lemmas) already takes
the a.e. form or no nonnegativity at all.

Do NOT use `Work.BoseFixR.farLatRow` (its crux `latSampling_le` is still a `sorry`; it also only
gives the constant `3`). -/
theorem latRow_le_sharp_ae {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) {μ : ℝ} (hμ : 0 < μ)
    (hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0)
    (hreg : 100 * R ≤ Work.BoseFixR.ell v μ) (N : ℕ) :
    Work.BoseFixR.latRow v h μ N
      ≤ (6 / 5) * (Work.BoseFixR.ell v μ) ^ 3 * Work.BoseFixR.farMass v h μ := by
  have hℓ : 0 < Work.BoseFixR.ell v μ := Work.BoseFixR.ell_pos' v hμ hav
  have hW : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) :=
    Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ
  have hWae : 0 ≤ᵐ[(MeasureTheory.volume : Measure E3)]
      (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) :=
    Submission.BoseGases.wScaled_g0_nonneg_ae hR hv hvrad hv_supp h
  have hsharp := lattice_W1sq_over_tau_le_sharp_ae h hv hvrad hR hℓ hv_supp hRℓ hreg hW hWae N
  calc Work.BoseFixR.latRow v h μ N
      = ∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
          (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))
              (Work.BoseBoxFock.kmomLab (Work.BoseFixR.ell v μ) N k)) ^ 2
            / (2 * ‖Work.BoseBoxFock.kmomLab (Work.BoseFixR.ell v μ) N k‖ ^ 2) := by
        simp only [Work.BoseFixR.latRow, Work.BoseB7.excited]
    _ ≤ (6 / 5) * ((2 * Real.pi) ^ 3)⁻¹ * (Work.BoseFixR.ell v μ) ^ 3 *
          ∫ q : EuclideanSpace ℝ (Fin 3),
            (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) q) ^ 2
              / (2 * ‖q‖ ^ 2) := hsharp
    _ = (6 / 5) * (Work.BoseFixR.ell v μ) ^ 3 * Work.BoseFixR.farMass v h μ := by
        simp only [Work.BoseFixR.farMass]
        ring

end Work.BoseFixR
