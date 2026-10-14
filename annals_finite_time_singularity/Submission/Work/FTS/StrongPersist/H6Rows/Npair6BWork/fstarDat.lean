import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.PhiStar.FlatWAux.Expansion
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_complete
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.CmodeDecay
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.PkgJets.cosTailB
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2W.FstarDzIterFourPsiAe
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.Decomp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false

/-!
# `Work.FTS.PhiStar.FlatWAux.Decomp` — the decomposition of `psiSeries α (RemSource α ψ)/sin 2θ`

The source `RemSource α ψ = α²·phiA α·ψ` is separable, so the mode series of the solution is
`psiSeries α (RemSource α ψ) z θ = α² Σ_m b_m · radGreen α m (phiA α) z · eFam m θ`
(`ModeExpansion.psiSeries_remSource_eq_tsum`, `RemSetup.acoeff_RemSource`).  Dividing by
`sin 2θ = s2 θ` turns `eFam m θ` into the divided angular mode `Qm m θ`, and the `J`-fold
`1/λ_m`-expansion of the radial Green function (`hexp`) then separates the `m`-dependence into
the resummed angular profiles `Wt ψ j = Σ_m b_m λ_m^{-j} Qm m` plus one remainder series:

`psiSeries α (RemSource α ψ) z θ / s2 θ
   = α² ( Σ_{j<J} α^j (𝒜^j phiA α) z · Wt ψ (j+1) θ
          + α^J Σ_m b_m λ_m^{-J} radGreen α m (𝒜^J (phiA α)) z · Qm m θ )`.

The `m = 0` term drops out because `bmode 0 ψ = 0`, so the expansion hypothesis is only needed
for `m ≥ 1`.  Summability of the finitely many angular series and of the remainder (which is what
makes the rearrangement of the double sum legitimate) follows from the three decay hypotheses
`hdec`, `hQ0`, `hrem` by comparison with `Σ_m m^{-2}`.

## Pieces

* `fts_lam_pos`, `fts_lam_ge_one`, `fts_sq_le_nine`, `fts_m_sq_inv_lam_sq` — the elementary
  estimates for `λ_m = 2m(2m+5)` used in the summability comparisons;
* `summable_bm_lam_Qm`, `summable_bm_G_Qm` — the two summability criteria;
* `decomp_algebra` — the purely algebraic core of the reindexing;
* `tsum_term`, `tsum_tail` — the evaluation of the two `tsum`s after `tsum_finsetSum`;
* `decomp_pointwise` — the pointwise (in `m`) decomposition;
* `decomp_core` — the `tsum`-level statement, and `Decomp` its `psiSeries` form.
-/

/-! ## Elementary facts about `λ_m = 2m(2m+5)` -/

private lemma fts_lam_pos {m : ℕ} (hm : 1 ≤ m) : 0 < Gegenbauer.lam m := by
  have h1 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  simp only [Gegenbauer.lam]; nlinarith

private lemma fts_lam_ge_one {m : ℕ} (hm : 1 ≤ m) : 1 ≤ Gegenbauer.lam m := by
  have h1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  simp only [Gegenbauer.lam]; nlinarith

private lemma fts_sq_le_nine {m : ℕ} (hm : 1 ≤ m) : (2*(m:ℝ)+1)^2 ≤ 9*(m:ℝ)^2 := by
  have h1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  nlinarith

/-- `m² · λ_m^{-2} ≤ 4 m^{-2}` — the decay transfer from `λ_m ≥ 4m²`. -/
private lemma fts_m_sq_inv_lam_sq {m : ℕ} (hm : 1 ≤ m) :
    (m:ℝ)^2 * ((Gegenbauer.lam m)⁻¹)^2 ≤ 4 * (m:ℝ)^(-(2:ℝ)) := by
  have h1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hxpos : (0:ℝ) < (m:ℝ) := by linarith
  have hLpos : 0 < Gegenbauer.lam m := fts_lam_pos hm
  have hlamge : 4*(m:ℝ)^2 ≤ Gegenbauer.lam m := by
    have h0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    simp only [Gegenbauer.lam]; nlinarith
  have hp4 : (m:ℝ)^4 ≤ 4 * (Gegenbauer.lam m)^2 := by
    nlinarith [sq_nonneg (Gegenbauer.lam m)]
  rw [inv_pow, show (-(2:ℝ)) = -(((2:ℕ)):ℝ) by norm_num, Real.rpow_neg (le_of_lt hxpos),
    Real.rpow_natCast]
  field_simp
  nlinarith

private lemma tsum_div_tsum (f : ℕ → ℝ) (c : ℝ) : (∑' m : ℕ, f m) / c = ∑' m : ℕ, f m / c := by
  rw [div_eq_mul_inv]
  exact (tsum_mul_right (f := f) (a := c⁻¹)).symm

/-! ## Summability of the resummed angular series -/

/-- **Summability of the `j`-th resummed angular series.**  `|b_m| ≤ Cb/(λ_m √(2m+1))` and
`|Qm m θ| ≤ Cq (2m+1)²` give, using `λ_m ≥ 4m²` and `(2m+1)² ≤ 9m²`, the bound
`Cb Cq λ_m^{-(j+2)} (2m+1)² ≤ 36 Cb Cq m^{-2}`, and `Σ_m m^{-2}` converges. -/
private lemma summable_bm_lam_Qm (ψ : ℝ → ℝ) (θ : ℝ) (Cb Cq : ℝ)
    (hCb : 0 < Cb) (hCq : 0 < Cq) (hb0 : Series.bmode 0 ψ = 0)
    (hdec : ∀ m : ℕ, 1 ≤ m → |Series.bmode m ψ|
      ≤ Cb / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hQ0 : ∀ m : ℕ, 1 ≤ m → |Qm m θ| ≤ Cq * (2 * (m : ℝ) + 1) ^ 2)
    (j : ℕ) :
    Summable (fun m : ℕ => Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (j+1) * Qm m θ) := by
  refine Summable.of_norm_bounded (g := fun m : ℕ => (36 * Cb * Cq) * (m:ℝ)^(-(2:ℝ))) ?_ ?_
  · exact ((Real.summable_nat_rpow (p := (-(2:ℝ)))).mpr (by norm_num)).mul_left _
  · intro m
    by_cases hm : m = 0
    · subst hm
      simp only [hb0, zero_mul, norm_zero]
      rw [Nat.cast_zero, Real.zero_rpow (by norm_num : (-2:ℝ) ≠ 0), mul_zero]
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have hx1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
      have hxpos : (0:ℝ) < (m:ℝ) := by linarith
      have hLpos : 0 < Gegenbauer.lam m := fts_lam_pos hm1
      have hL1 : 1 ≤ Gegenbauer.lam m := fts_lam_ge_one hm1
      have hs1 : 1 ≤ Real.sqrt (2*(m:ℝ)+1) := by rw [Real.one_le_sqrt]; linarith
      have hu2 : (2*(m:ℝ)+1)^2 ≤ 9*(m:ℝ)^2 := fts_sq_le_nine hm1
      have hkey := fts_m_sq_inv_lam_sq hm1
      have hCbdiv : Cb / (Gegenbauer.lam m * Real.sqrt (2*(m:ℝ)+1)) ≤ Cb / Gegenbauer.lam m :=
        div_le_div_of_nonneg_left (le_of_lt hCb) hLpos (by nlinarith [hs1, hLpos])
      have hpow2 : (Gegenbauer.lam m)⁻¹ ^ (j+2) ≤ (Gegenbauer.lam m)⁻¹ ^ 2 :=
        pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hL1) (Nat.le_add_left 2 j)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_inv, abs_of_pos hLpos]
      calc |Series.bmode m ψ| * (Gegenbauer.lam m)⁻¹ ^ (j+1) * |Qm m θ|
          ≤ (Cb / (Gegenbauer.lam m * Real.sqrt (2*(m:ℝ)+1)))
              * (Gegenbauer.lam m)⁻¹ ^ (j+1) * (Cq * (2*(m:ℝ)+1)^2) :=
            mul_le_mul (mul_le_mul (hdec m hm1) le_rfl (by positivity)
                (div_nonneg (le_of_lt hCb) (mul_nonneg (le_of_lt hLpos) (Real.sqrt_nonneg _))))
              (hQ0 m hm1) (abs_nonneg _) (by positivity)
        _ ≤ (Cb * (Gegenbauer.lam m)⁻¹ ^ 2) * (Cq * (9*(m:ℝ)^2)) := by
            refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
            · calc (Cb / (Gegenbauer.lam m * Real.sqrt (2*(m:ℝ)+1)))
                    * (Gegenbauer.lam m)⁻¹ ^ (j+1)
                  ≤ (Cb / Gegenbauer.lam m) * (Gegenbauer.lam m)⁻¹ ^ (j+1) :=
                    mul_le_mul_of_nonneg_right hCbdiv (by positivity)
                _ = Cb * (Gegenbauer.lam m)⁻¹ ^ (j+2) := by
                    rw [div_eq_mul_inv, pow_succ]; ring
                _ ≤ Cb * (Gegenbauer.lam m)⁻¹ ^ 2 :=
                    mul_le_mul_of_nonneg_left hpow2 (le_of_lt hCb)
            · exact mul_le_mul_of_nonneg_left hu2 (le_of_lt hCq)
        _ = 9*Cb*Cq * ((m:ℝ)^2 * ((Gegenbauer.lam m)⁻¹)^2) := by ring
        _ ≤ 9*Cb*Cq * (4 * (m:ℝ)^(-(2:ℝ))) := mul_le_mul_of_nonneg_left hkey (by positivity)
        _ = 36*Cb*Cq * (m:ℝ)^(-(2:ℝ)) := by ring

/-- **Summability with an extra `λ_m^{-1}`-decaying radial factor.**  With
`|G m| ≤ Cg/λ_m` the summand is bounded by `Cb Cg Cq λ_m^{-2}(2m+1)² ≤ 36 Cb Cg Cq m^{-2}`. -/
private lemma summable_bm_G_Qm (ψ : ℝ → ℝ) (θ : ℝ) (Cb Cq Cg : ℝ)
    (hCb : 0 < Cb) (hCq : 0 < Cq) (hCg : 0 < Cg) (hb0 : Series.bmode 0 ψ = 0)
    (hdec : ∀ m : ℕ, 1 ≤ m → |Series.bmode m ψ|
      ≤ Cb / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hQ0 : ∀ m : ℕ, 1 ≤ m → |Qm m θ| ≤ Cq * (2 * (m : ℝ) + 1) ^ 2)
    (G : ℕ → ℝ)
    (hg : ∀ m : ℕ, 1 ≤ m → |G m| ≤ Cg / Gegenbauer.lam m) (k : ℕ) :
    Summable (fun m : ℕ => Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ k * G m * Qm m θ) := by
  refine Summable.of_norm_bounded (g := fun m : ℕ => (36 * Cb * Cg * Cq) * (m:ℝ)^(-(2:ℝ))) ?_ ?_
  · exact ((Real.summable_nat_rpow (p := (-(2:ℝ)))).mpr (by norm_num)).mul_left _
  · intro m
    by_cases hm : m = 0
    · subst hm
      simp only [hb0, zero_mul, norm_zero]
      rw [Nat.cast_zero, Real.zero_rpow (by norm_num : (-2:ℝ) ≠ 0), mul_zero]
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have hx1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
      have hxpos : (0:ℝ) < (m:ℝ) := by linarith
      have hLpos : 0 < Gegenbauer.lam m := fts_lam_pos hm1
      have hL1 : 1 ≤ Gegenbauer.lam m := fts_lam_ge_one hm1
      have hs1 : 1 ≤ Real.sqrt (2*(m:ℝ)+1) := by rw [Real.one_le_sqrt]; linarith
      have hu2 : (2*(m:ℝ)+1)^2 ≤ 9*(m:ℝ)^2 := fts_sq_le_nine hm1
      have hkey := fts_m_sq_inv_lam_sq hm1
      have hCbdiv : Cb / (Gegenbauer.lam m * Real.sqrt (2*(m:ℝ)+1)) ≤ Cb / Gegenbauer.lam m :=
        div_le_div_of_nonneg_left (le_of_lt hCb) hLpos (by nlinarith [hs1, hLpos])
      have hpowk : (Gegenbauer.lam m)⁻¹ ^ k ≤ 1 :=
        pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hL1)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow, abs_inv, abs_of_pos hLpos]
      calc |Series.bmode m ψ| * (Gegenbauer.lam m)⁻¹ ^ k * |G m| * |Qm m θ|
          ≤ (Cb / (Gegenbauer.lam m * Real.sqrt (2*(m:ℝ)+1)))
              * (Gegenbauer.lam m)⁻¹ ^ k * (Cg / Gegenbauer.lam m)
              * (Cq * (2*(m:ℝ)+1)^2) :=
            mul_le_mul (mul_le_mul (mul_le_mul (hdec m hm1) le_rfl (by positivity)
                (div_nonneg (le_of_lt hCb) (mul_nonneg (le_of_lt hLpos) (Real.sqrt_nonneg _))))
              (hg m hm1) (by positivity) (by positivity))
              (hQ0 m hm1) (abs_nonneg _) (by positivity)
        _ ≤ (Cb * (Gegenbauer.lam m)⁻¹ * (Cg * (Gegenbauer.lam m)⁻¹))
              * (Cq * (9*(m:ℝ)^2)) := by
            refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
            · rw [div_eq_mul_inv]
              refine mul_le_mul ?_ le_rfl (by positivity) (by positivity)
              · calc (Cb / (Gegenbauer.lam m * Real.sqrt (2*(m:ℝ)+1)))
                    * (Gegenbauer.lam m)⁻¹ ^ k
                  ≤ (Cb / Gegenbauer.lam m) * 1 :=
                    mul_le_mul hCbdiv hpowk (by positivity) (by positivity)
                _ = Cb * (Gegenbauer.lam m)⁻¹ := by rw [mul_one, div_eq_mul_inv]
            · exact mul_le_mul_of_nonneg_left hu2 (le_of_lt hCq)
        _ = 9*Cb*Cg*Cq * ((m:ℝ)^2 * ((Gegenbauer.lam m)⁻¹)^2) := by ring
        _ ≤ 9*Cb*Cg*Cq * (4 * (m:ℝ)^(-(2:ℝ))) := mul_le_mul_of_nonneg_left hkey (by positivity)
        _ = 36*Cb*Cg*Cq * (m:ℝ)^(-(2:ℝ)) := by ring

/-! ## The algebraic core of the reindexing -/

/-- The purely algebraic identity underlying the decomposition: expanding
`Σ_j (α^j/λ^{j+1}) A_j + (α^J/λ^J) GJ` against `B` and `Q`. -/
private lemma decomp_algebra (m : ℕ) (α B Q GJ : ℝ) (A : ℕ → ℝ) :
    α^2 * (B * ((∑ j ∈ Finset.range J, (α^j / (Radial.lamR m)^(j+1)) * A j)
        + (α^J / (Radial.lamR m)^J) * GJ) * Q)
    = (∑ j ∈ Finset.range J,
          (α^j * A j) * (α^2 * (B * ((Gegenbauer.lam m)⁻¹)^(j+1) * Q)))
      + α^2 * (α^J * (B * ((Gegenbauer.lam m)⁻¹)^J * GJ * Q)) := by
  rw [lamR_eq_lam]
  rw [show (∑ j ∈ Finset.range J, (α^j * A j) * (α^2 * (B * ((Gegenbauer.lam m)⁻¹)^(j+1) * Q)))
      = ∑ j ∈ Finset.range J, ((α^j / (Gegenbauer.lam m)^(j+1)) * A j) * (α^2 * B * Q) from
        Finset.sum_congr rfl (fun j _ => by rw [div_eq_mul_inv, inv_pow]; ring)]
  rw [← Finset.sum_mul]
  rw [show α^2 * (α^J * (B * ((Gegenbauer.lam m)⁻¹)^J * GJ * Q))
      = ((α^J / (Gegenbauer.lam m)^J) * GJ) * (α^2 * B * Q) from by
        rw [div_eq_mul_inv, inv_pow]; ring]
  ring

/-! ## Evaluation of the two `tsum`s -/

private lemma tsum_term (α : ℝ) (ψ : ℝ → ℝ) (θ z : ℝ) (j : ℕ) :
    (∑' m : ℕ, (α^j * Ajit α j (VocabO.phiA α) z)
        * (α^2 * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹)^(j+1) * Qm m θ)))
      = α^2 * (α^j * Ajit α j (VocabO.phiA α) z * Wt ψ (j+1) θ) := by
  have h1 : (∑' m : ℕ, (α^j * Ajit α j (VocabO.phiA α) z)
        * (α^2 * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹)^(j+1) * Qm m θ)))
      = (α^j * Ajit α j (VocabO.phiA α) z)
        * (∑' m : ℕ, α^2 * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹)^(j+1) * Qm m θ)) := by
    rw [tsum_mul_left]
  have h2 : (∑' m : ℕ, α^2 * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹)^(j+1) * Qm m θ))
      = α^2 * (∑' m : ℕ, Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹)^(j+1) * Qm m θ) := by
    rw [tsum_mul_left]
  have hWt : Wt ψ (j+1) θ
      = ∑' m : ℕ, Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹)^(j+1) * Qm m θ := rfl
  rw [h1]
  rw [h2]
  rw [hWt]
  ring

private lemma tsum_tail (α : ℝ) (ψ : ℝ → ℝ) (θ z : ℝ) :
    (∑' m : ℕ, α^2 * (α^J * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹)^J
        * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z * Qm m θ)))
      = α^2 * (α^J * (∑' m : ℕ, Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹)^J
          * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z * Qm m θ)) := by
  have h1 : (∑' m : ℕ, α^2 * (α^J * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹)^J
        * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z * Qm m θ)))
      = α^2 * (∑' m : ℕ, α^J * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹)^J
        * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z * Qm m θ)) := by
    rw [tsum_mul_left]
  have h2 : (∑' m : ℕ, α^J * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹)^J
        * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z * Qm m θ))
      = α^J * (∑' m : ℕ, Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹)^J
        * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z * Qm m θ) := by
    rw [tsum_mul_left]
  rw [h1, h2]

/-! ## The pointwise decomposition -/

/-- The decomposition term by term in `m`.  For `m = 0` both sides vanish (`bmode 0 ψ = 0`); for
`m ≥ 1` it is `hexp` followed by `decomp_algebra`. -/
private lemma decomp_pointwise (α : ℝ) (ψ : ℝ → ℝ) (z θ : ℝ) (m : ℕ)
    (hz : 0 < z) (hb0 : Series.bmode 0 ψ = 0)
    (hexp : ∀ m : ℕ, 1 ≤ m → ∀ z' : ℝ, 0 < z' →
      Radial.radGreen α m (VocabO.phiA α) z'
        = (∑ j ∈ Finset.range J, (α^j / (Radial.lamR m)^(j+1)) * Ajit α j (VocabO.phiA α) z')
          + (α^J / (Radial.lamR m)^J)
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z') :
    α^2 * (Series.bmode m ψ * Radial.radGreen α m (VocabO.phiA α) z * Qm m θ)
      = (∑ j ∈ Finset.range J, (α^j * Ajit α j (VocabO.phiA α) z)
            * (α^2 * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹)^(j+1) * Qm m θ)))
        + α^2 * (α^J * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹)^J
            * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z * Qm m θ)) := by
  by_cases hm : m = 0
  · subst hm
    rw [hb0]
    simp only [zero_mul, mul_zero, Finset.sum_const_zero, zero_add]
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    rw [hexp m hm1 z hz]
    exact decomp_algebra m α (Series.bmode m ψ) (Qm m θ)
      (Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z) (fun j => Ajit α j (VocabO.phiA α) z)

/-! ## The `tsum`-level decomposition -/

private theorem decomp_core (α : ℝ) (ψ : ℝ → ℝ) (z θ : ℝ)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hz : 0 < z)
    (hb0 : Series.bmode 0 ψ = 0)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Series.bmode m ψ| ≤ C / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hQ0 : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ θ' : ℝ, θ' ∈ Set.Ioo 0 (Real.pi / 2) →
      |Qm m θ'| ≤ C * (2 * (m : ℝ) + 1) ^ 2)
    (hrem : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) / z' * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'|
        ≤ C / Gegenbauer.lam m)
    (hexp : ∀ m : ℕ, 1 ≤ m → ∀ z' : ℝ, 0 < z' →
      Radial.radGreen α m (VocabO.phiA α) z'
        = (∑ j ∈ Finset.range J, (α ^ j / (Radial.lamR m) ^ (j + 1))
              * Ajit α j (VocabO.phiA α) z')
          + (α ^ J / (Radial.lamR m) ^ J)
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z') :
    (∑' m : ℕ, α ^ 2 * (Series.bmode m ψ * Radial.radGreen α m (VocabO.phiA α) z * Qm m θ))
      = α ^ 2 * ((∑ j ∈ Finset.range J, α ^ j * Ajit α j (VocabO.phiA α) z * Wt ψ (j + 1) θ)
          + α ^ J * (∑' m : ℕ, Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z * Qm m θ)) := by
  obtain ⟨Cb, hCb, hdec⟩ := hdec
  obtain ⟨Cq, hCq, hQ0⟩ := hQ0
  obtain ⟨Cr, hCr, hrem⟩ := hrem
  -- the `λ_m^{-1}` bound for the remainder radial factor, from `hrem`
  have hGbd : ∀ m : ℕ, 1 ≤ m →
      |Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z| ≤ Cr / Gegenbauer.lam m := by
    intro m hm
    have h := hrem m hm z hz
    have hsplit : Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z
        = (z/(z+1)) * ((z+1)/z * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z) := by
      field_simp
    rw [hsplit, abs_mul, abs_of_nonneg (le_of_lt (div_pos hz (by linarith)))]
    have hle1 : z/(z+1) ≤ 1 := by
      rw [div_le_one (by linarith : (0:ℝ) < z + 1)]
      linarith
    calc (z/(z+1)) * |(z+1)/z * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z|
        ≤ 1 * (Cr / Gegenbauer.lam m) := mul_le_mul hle1 h (abs_nonneg _) (by positivity)
      _ = Cr / Gegenbauer.lam m := one_mul _
  have hsumTail : Summable (fun m : ℕ => Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J
      * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z * Qm m θ) :=
    summable_bm_G_Qm ψ θ Cb Cq Cr hCb hCq hCr hb0 (fun m hm => hdec m hm)
      (fun m hm => hQ0 m hm θ hθ) (fun m => Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z)
      hGbd J
  have hsumF : ∀ j ∈ Finset.range J, Summable (fun m : ℕ =>
      (α ^ j * Ajit α j (VocabO.phiA α) z)
        * (α ^ 2 * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (j + 1) * Qm m θ))) := by
    intro j _
    have h := summable_bm_lam_Qm ψ θ Cb Cq hCb hCq hb0 (fun m hm => hdec m hm)
      (fun m hm => hQ0 m hm θ hθ) j
    exact (h.mul_left (α^2)).mul_left (α^j * Ajit α j (VocabO.phiA α) z)
  calc (∑' m : ℕ, α ^ 2 * (Series.bmode m ψ * Radial.radGreen α m (VocabO.phiA α) z * Qm m θ))
      = ∑' m : ℕ, ((∑ j ∈ Finset.range J, (α ^ j * Ajit α j (VocabO.phiA α) z)
            * (α ^ 2 * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (j + 1) * Qm m θ)))
          + α ^ 2 * (α ^ J * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z * Qm m θ))) :=
        tsum_congr (fun m => decomp_pointwise α ψ z θ m hz hb0 hexp)
    _ = (∑' m : ℕ, ∑ j ∈ Finset.range J, (α ^ j * Ajit α j (VocabO.phiA α) z)
            * (α ^ 2 * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (j + 1) * Qm m θ)))
          + ∑' m : ℕ, α ^ 2 * (α ^ J * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z * Qm m θ)) :=
        (summable_sum hsumF).tsum_add ((hsumTail.mul_left (α^J)).mul_left (α^2))
    _ = (∑ j ∈ Finset.range J, ∑' m : ℕ, (α ^ j * Ajit α j (VocabO.phiA α) z)
            * (α ^ 2 * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (j + 1) * Qm m θ)))
          + ∑' m : ℕ, α ^ 2 * (α ^ J * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z * Qm m θ)) := by
        rw [Summable.tsum_finsetSum hsumF]
    _ = (∑ j ∈ Finset.range J, α ^ 2 * (α ^ j * Ajit α j (VocabO.phiA α) z * Wt ψ (j+1) θ))
          + ∑' m : ℕ, α ^ 2 * (α ^ J * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z * Qm m θ)) := by
        rw [Finset.sum_congr rfl (fun j _ => tsum_term α ψ θ z j)]
    _ = α ^ 2 * ((∑ j ∈ Finset.range J, α ^ j * Ajit α j (VocabO.phiA α) z * Wt ψ (j + 1) θ)
          + α ^ J * (∑' m : ℕ, Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z * Qm m θ)) := by
        rw [← Finset.mul_sum]
        rw [tsum_tail α ψ θ z]
        ring

/-- The mode expansion of `psiSeries α (RemSource α ψ)` with the `α²` inside the `tsum`, and the
division by `s2 θ = sin 2θ` turned into the divided angular modes `Qm m θ`. -/
private lemma psiSeries_div_eq_tsum (α : ℝ) (ψ : ℝ → ℝ) (z θ : ℝ) :
    Series.psiSeries α (RemSource α ψ) z θ / Work.Construction.s2 θ
      = ∑' m : ℕ, α^2 * (Series.bmode m ψ * (Radial.radGreen α m (VocabO.phiA α) z)
          * Qm m θ) := by
  have h1 : Series.psiSeries α (RemSource α ψ) z θ
      = ∑' m : ℕ, (α^2 * Series.bmode m ψ) * Radial.radGreen α m (VocabO.phiA α) z
          * Gegenbauer.eFam m θ := by
    rw [Series.psiSeries]
    exact tsum_congr (fun m => by rw [Series.acoeff_RemSource])
  have hdiv : (∑' m : ℕ, (α^2 * Series.bmode m ψ) * Radial.radGreen α m (VocabO.phiA α) z
        * Gegenbauer.eFam m θ) / Work.Construction.s2 θ
      = ∑' m : ℕ, ((α^2 * Series.bmode m ψ) * Radial.radGreen α m (VocabO.phiA α) z
        * Gegenbauer.eFam m θ) / Work.Construction.s2 θ := tsum_div_tsum _ _
  rw [h1]
  rw [hdiv]
  refine tsum_congr (fun m => ?_)
  simp only [Qm]
  ring

theorem Decomp (α : ℝ) (ψ : ℝ → ℝ) (z θ : ℝ)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hz : 0 < z)
    (hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hQ0 : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ θ' : ℝ, θ' ∈ Set.Ioo 0 (Real.pi / 2) →
      |Work.FTS.PhiStar.FlatWAux.Qm m θ'| ≤ C * (2 * (m : ℝ) + 1) ^ 2)
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ' : ℝ), θ' ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ'| ≤ C * (2 * (m : ℝ) + 1))
    (hsrc : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) / z' * Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z'|
        ≤ C / Work.FTS.PhiStar.Gegenbauer.lam m)
    (hrem : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) / z' * Work.FTS.PhiStar.Radial.radGreen α m
          (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
            (Work.FTS.VocabO.phiA α)) z'|
        ≤ C / Work.FTS.PhiStar.Gegenbauer.lam m)
    (hexp : ∀ m : ℕ, 1 ≤ m → ∀ z' : ℝ, 0 < z' →
      Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z'
        = (∑ j ∈ Finset.range Work.FTS.PhiStar.FlatWAux.J,
            (α ^ j / (Work.FTS.PhiStar.Radial.lamR m) ^ (j + 1))
              * Work.FTS.PhiStar.FlatWAux.Ajit α j (Work.FTS.VocabO.phiA α) z')
          + (α ^ Work.FTS.PhiStar.FlatWAux.J
              / (Work.FTS.PhiStar.Radial.lamR m) ^ Work.FTS.PhiStar.FlatWAux.J)
              * Work.FTS.PhiStar.Radial.radGreen α m
                  (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                    (Work.FTS.VocabO.phiA α)) z') :
    Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z θ
        / Work.Construction.s2 θ
      = α ^ 2 * ((∑ j ∈ Finset.range Work.FTS.PhiStar.FlatWAux.J,
            α ^ j * Work.FTS.PhiStar.FlatWAux.Ajit α j (Work.FTS.VocabO.phiA α) z
              * Work.FTS.PhiStar.FlatWAux.Wt ψ (j + 1) θ)
          + α ^ Work.FTS.PhiStar.FlatWAux.J * (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ Work.FTS.PhiStar.FlatWAux.J
              * Work.FTS.PhiStar.Radial.radGreen α m
                  (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                    (Work.FTS.VocabO.phiA α)) z
              * Work.FTS.PhiStar.FlatWAux.Qm m θ)) := by
  rw [psiSeries_div_eq_tsum α ψ z θ]
  exact decomp_core α ψ z θ hθ hz hb0 hdec hQ0 hrem hexp

end Work.FTS.PhiStar.FlatWAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.PsiExpansion =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false

/-! ## Elementary facts about the modes and the weight -/

/-- The set integral over `Iθ = [0, π/2]` is the interval integral over `0..π/2`. -/
private lemma iota_eq_interval (f : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, f θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), f θ := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]

/-- The normalisation `∫_{Iθ} eFam m ^ 2 cos θ` of the `m`-th mode is positive. -/
private lemma eFam_norm_pos (m : ℕ) :
    0 < ∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ := by
  rw [iota_eq_interval, Work.FTS.PhiStar.Gegenbauer.FamNormValue]
  positivity

/-- Every mode is a continuous function. -/
private lemma continuous_eFam (m : ℕ) : Continuous (Work.FTS.PhiStar.Gegenbauer.eFam m) := by
  change Continuous (fun θ : ℝ =>
    Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ))
  exact Real.continuous_cos.mul
    (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp
      Real.continuous_sin)

/-- The uniform bound `|eFam m θ| ≤ √((2m+2)(2m+3))` on the whole closed interval `Iθ`
(the sharp bound on the closed quadrant; the endpoints vanish). -/
private lemma abs_eFam_le_sqrt (m : ℕ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
      ≤ Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) := by
  obtain ⟨h0, h1⟩ := hθ
  rcases lt_or_eq_of_le h0 with h0' | h0'
  · rcases lt_or_eq_of_le h1 with h1' | h1'
    · exact (Work.FTS.PhiStar.Series.Deleg.psiAngBounds).1 m θ ⟨h0', h1'⟩
    · rw [h1', Work.FTS.PhiStar.Series.eFam_zero_left, abs_zero]
      exact Real.sqrt_nonneg _
  · rw [← h0', Work.FTS.PhiStar.Series.eFam_zero_right, abs_zero]
    exact Real.sqrt_nonneg _

/-! ## The arithmetic of the majorant `(m+1)^{-3/2}` -/

/-- `√((2m+2)(2m+3)) ≤ √6 · √(m+1) · √(2m+1)`. -/
private lemma sqrt_factor (m : ℕ) :
    Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
      ≤ Real.sqrt 6 * Real.sqrt ((m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1) := by
  have hb : (2 * (m : ℝ) + 3) ≤ 3 * (2 * (m : ℝ) + 1) := by
    have h : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  calc Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
      = Real.sqrt ((2 * ((m : ℝ) + 1)) * (2 * (m : ℝ) + 3)) := by ring_nf
    _ = Real.sqrt (2 * ((m : ℝ) + 1)) * Real.sqrt (2 * (m : ℝ) + 3) :=
        Real.sqrt_mul (by positivity) _
    _ = (Real.sqrt 2 * Real.sqrt ((m : ℝ) + 1)) * Real.sqrt (2 * (m : ℝ) + 3) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ (Real.sqrt 2 * Real.sqrt ((m : ℝ) + 1))
          * (Real.sqrt 3 * Real.sqrt (2 * (m : ℝ) + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
        exact Real.sqrt_le_sqrt hb
    _ = Real.sqrt 6 * Real.sqrt ((m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1) := by
        have h6 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
          rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
        calc (Real.sqrt 2 * Real.sqrt ((m : ℝ) + 1))
              * (Real.sqrt 3 * Real.sqrt (2 * (m : ℝ) + 1))
            = (Real.sqrt 2 * Real.sqrt 3)
                * (Real.sqrt ((m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1)) := by ring
          _ = Real.sqrt 6 * Real.sqrt ((m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1) := by
              rw [h6]; ring

/-- The cross-multiplied form of the majorant inequality:
`√((2m+2)(2m+3)) · (m+1)√(m+1) ≤ 300 λ_m √(2m+1)` for `m ≥ 1`. -/
private lemma prod_bound (m : ℕ) (hm : 1 ≤ m) :
    Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
        * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))
      ≤ 300 * (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hx : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hsx : Real.sqrt ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1) = (m : ℝ) + 1 := by
    rw [← sq, Real.sq_sqrt (le_of_lt hx)]
  have hs6 : Real.sqrt 6 ≤ 3 := by
    have h : Real.sqrt 6 ≤ Real.sqrt 9 := Real.sqrt_le_sqrt (by norm_num)
    rwa [show Real.sqrt 9 = (3 : ℝ) from by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
  have hlamdef : Work.FTS.PhiStar.Gegenbauer.lam m
      = 2 * (m : ℝ) * (2 * (m : ℝ) + 5) := rfl
  have hcore : Real.sqrt 6 * ((m : ℝ) + 1) ^ 2
      ≤ 300 * Work.FTS.PhiStar.Gegenbauer.lam m := by
    have hsq : ((m : ℝ) + 1) ^ 2 ≤ 2 * (m : ℝ) * (2 * (m : ℝ) + 5) := by nlinarith
    have h2 : (0 : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := by positivity
    calc Real.sqrt 6 * ((m : ℝ) + 1) ^ 2 ≤ 3 * ((m : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_right hs6 h2
      _ ≤ 3 * (2 * (m : ℝ) * (2 * (m : ℝ) + 5)) :=
          mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = 6 * (m : ℝ) * (2 * (m : ℝ) + 5) := by ring
      _ ≤ 300 * Work.FTS.PhiStar.Gegenbauer.lam m := by
          rw [hlamdef]
          nlinarith [show (0 : ℝ) ≤ (m : ℝ) by positivity]
  calc Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
        * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))
      ≤ (Real.sqrt 6 * Real.sqrt ((m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1))
          * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right (sqrt_factor m) (by positivity)
    _ = (Real.sqrt 6 * ((m : ℝ) + 1) ^ 2) * Real.sqrt (2 * (m : ℝ) + 1) := by
        calc (Real.sqrt 6 * Real.sqrt ((m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1))
              * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))
            = Real.sqrt 6 * (Real.sqrt ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))
                * ((m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1) := by ring
          _ = Real.sqrt 6 * ((m : ℝ) + 1) * ((m : ℝ) + 1)
                * Real.sqrt (2 * (m : ℝ) + 1) := by rw [hsx]
          _ = (Real.sqrt 6 * ((m : ℝ) + 1) ^ 2) * Real.sqrt (2 * (m : ℝ) + 1) := by ring
    _ ≤ (300 * Work.FTS.PhiStar.Gegenbauer.lam m) * Real.sqrt (2 * (m : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hcore (Real.sqrt_nonneg _)
    _ = 300 * (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) := by ring

/-- The divided form: `√((2m+2)(2m+3)) / (λ_m √(2m+1)) ≤ 300 / ((m+1)√(m+1))`. -/
private lemma expr_le (m : ℕ) (hm : 1 ≤ m) :
    Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
        / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
      ≤ 300 * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))⁻¹ := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hx : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hD : 0 < ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1) :=
    mul_pos hx (Real.sqrt_pos.2 hx)
  have hlam : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := by
    rw [show Work.FTS.PhiStar.Gegenbauer.lam m = 2 * (m : ℝ) * (2 * (m : ℝ) + 5) from rfl]
    nlinarith
  have hN : 0 < Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1) :=
    mul_pos hlam (Real.sqrt_pos.2 (by linarith))
  have hDinv : (300 : ℝ) * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))⁻¹
      = 300 / (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1)) := by
    rw [inv_eq_one_div, mul_one_div]
  rw [hDinv, div_le_iff₀ hN]
  rw [show (300 : ℝ) / (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))
        * (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
      = 300 * (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
        / (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1)) from by ring]
  rw [le_div_iff₀ hD]
  exact prod_bound m hm

/-! ## The pointwise domination by a summable majorant -/

/-- If the coefficients decay like `λ_m^{-1}(2m+1)^{-1/2}` and vanish at `m = 0`, then the
products `c_m e_m(θ)` are dominated on `Iθ` by the summable sequence
`max 1 (300C) · ((m+1)√(m+1))^{-1}`. -/
private lemma pointwise_bound {c : ℕ → ℝ} {C : ℝ} (hC : 0 < C)
    (hdec : ∀ m : ℕ, 1 ≤ m →
      |c m| ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hzero : c 0 = 0) (m : ℕ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |c m * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
      ≤ max 1 (300 * C) * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))⁻¹ := by
  have hDnn : ∀ k : ℕ, 0 ≤ (((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1))⁻¹ := fun k =>
    inv_nonneg.mpr (by positivity)
  by_cases hm : m = 0
  · subst hm
    rw [hzero, zero_mul, abs_zero]
    exact mul_nonneg (le_trans zero_le_one (le_max_left 1 (300 * C))) (hDnn 0)
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hm1R : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hlam : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := by
      rw [show Work.FTS.PhiStar.Gegenbauer.lam m = 2 * (m : ℝ) * (2 * (m : ℝ) + 5) from rfl]
      nlinarith [hm1R]
    have hN : 0 < Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1) :=
      mul_pos hlam (Real.sqrt_pos.2 (by linarith))
    rw [abs_mul]
    calc |c m| * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ (C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
            * Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) :=
          mul_le_mul (hdec m hm1) (abs_eFam_le_sqrt m hθ) (abs_nonneg _)
            (le_of_lt (div_pos hC hN))
      _ = C * (Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
            / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by ring
      _ ≤ C * (300 * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))⁻¹) :=
          mul_le_mul_of_nonneg_left (expr_le m hm1) (le_of_lt hC)
      _ = (300 * C) * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))⁻¹ := by ring
      _ ≤ max 1 (300 * C) * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_right 1 (300 * C)) (hDnn m)

/-! ## Termwise integration -/

/-- **Termwise integration of the mode series.**  If the modes are dominated by a summable
majorant `u`, the series can be integrated term by term against `eFam n · cos θ`: the `m ≠ n`
terms drop out by orthogonality and only the diagonal survives.  (Dominated convergence with
the uniform majorant; the dominated function is the constant `∑ u_m · √((2n+2)(2n+3))`.) -/
private lemma tsum_moment (b : ℕ → ℝ) (u : ℕ → ℝ) (hu : Summable u)
    (hb : ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ u m) (n : ℕ) :
    (∫ θ in Work.Spaces.Iθ, (∑' m : ℕ, b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
      = b n * (∫ θ in Work.Spaces.Iθ,
          Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) := by
  have hunn : ∀ m : ℕ, 0 ≤ u m := fun m =>
    le_trans (abs_nonneg _) (hb m 0 Work.Spaces.zero_mem_Iθ)
  set K : ℝ := Real.sqrt ((2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 3)) with hK
  have hKnn : 0 ≤ K := Real.sqrt_nonneg _
  have hprod : ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ
        * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)| ≤ u m * K := by
    intro m θ hθ
    have h1 := hb m θ hθ
    have h2 : |Work.FTS.PhiStar.Gegenbauer.eFam n θ| ≤ K := abs_eFam_le_sqrt n hθ
    have h3 : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
    have h4 : |Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ| ≤ K := by
      rw [abs_mul]
      calc |Work.FTS.PhiStar.Gegenbauer.eFam n θ| * |Real.cos θ| ≤ K * 1 :=
            mul_le_mul h2 h3 (abs_nonneg _) hKnn
        _ = K := by ring
    rw [abs_mul]
    exact mul_le_mul h1 h4 (abs_nonneg _) (hunn m)
  haveI hfin : MeasureTheory.IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) := by
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.restrict_apply_univ]
    exact measure_Icc_lt_top
  have hsumK : Summable (fun m : ℕ => u m * K) := hu.mul_right K
  have hmain := MeasureTheory.hasSum_integral_of_dominated_convergence
    (μ := volume.restrict Work.Spaces.Iθ)
    (F := fun (m : ℕ) (θ : ℝ) => b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ
      * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
    (f := fun θ : ℝ => (∑' m : ℕ, b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
      * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
    (fun (m : ℕ) (_ : ℝ) => u m * K)
    (fun m => ((continuous_const.mul (continuous_eFam m)).mul
      ((continuous_eFam n).mul Real.continuous_cos)).continuousOn.aestronglyMeasurable
        measurableSet_Icc)
    (fun m => by
      rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
      exact Filter.Eventually.of_forall (fun θ hθ => by
        simpa only [Real.norm_eq_abs] using hprod m θ hθ))
    (Filter.Eventually.of_forall (fun _ => hsumK))
    (MeasureTheory.integrable_const _)
    (by
      rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
      refine Filter.Eventually.of_forall (fun θ hθ => ?_)
      have hs : Summable (fun m : ℕ => b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
        Summable.of_norm_bounded hu (fun m => by rw [Real.norm_eq_abs]; exact hb m θ hθ)
      exact (hs.hasSum).mul_right (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
  have hFint : ∀ m : ℕ, (∫ θ in Work.Spaces.Iθ,
        b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
      = b m * (∫ θ in Work.Spaces.Iθ,
          Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ
            * Real.cos θ) := by
    intro m
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
  have horth : ∀ m : ℕ, (∫ θ in Work.Spaces.Iθ,
        Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ
          * Real.cos θ)
      = if m = n then (∫ θ in Work.Spaces.Iθ,
          Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) else 0 := by
    intro m
    by_cases hmn : m = n
    · subst hmn
      rw [if_pos rfl]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    · rw [if_neg hmn, iota_eq_interval]
      exact Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal m n hmn
  have hfun : (fun m : ℕ => if m = n then b n * (∫ θ in Work.Spaces.Iθ,
          Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) else 0)
      = fun m : ℕ => ∫ θ in Work.Spaces.Iθ,
          b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ
            * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) := by
    funext m
    rw [hFint m, horth m]
    by_cases hmn : m = n
    · subst hmn; simp
    · simp [hmn]
  have h2 : HasSum (fun m : ℕ => if m = n then b n * (∫ θ in Work.Spaces.Iθ,
        Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) else 0)
      (b n * (∫ θ in Work.Spaces.Iθ,
        Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ)) := hasSum_ite_eq n _
  rw [hfun] at h2
  have huniq := hmain.unique h2
  rw [← huniq]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)

/-! ## The main auxiliary statement -/

/-- **The eigenfunction expansion of a function whose coefficients decay like
`λ_m^{-1}(2m+1)^{-1/2}`.**  For a coefficient family `c` with those two properties (decay, and
`c 0 = 0`) which are the Fourier coefficients of `ψ`, the series `∑_m c_m e_m` converges to
`ψ` pointwise on `(0, π/2)`.  The two analysis inputs are the termwise integration
(`hTsum`) and the a.e.-to-pointwise upgrade (`hMom`). -/
private theorem psiExpansionAux (c : ℕ → ℝ)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |c m| ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hzero : c 0 = 0)
    (hTsum : ∀ (b : ℕ → ℝ) (u : ℕ → ℝ), Summable u →
      (∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
        |b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ u m) →
      ∀ n : ℕ, (∫ θ in Work.Spaces.Iθ,
          (∑' m : ℕ, b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
            * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
        = b n * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ))
    (hMom : ∀ (v w : ℝ → ℝ), ContinuousOn v (Set.Icc 0 (Real.pi / 2)) →
      ContinuousOn w (Set.Icc 0 (Real.pi / 2)) →
      (∀ n : ℕ, (∫ θ in Work.Spaces.Iθ,
          w θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
        = ∫ θ in Work.Spaces.Iθ, v θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) →
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), w θ = v θ)
    (ψ : ℝ → ℝ) (hcontψ : ContinuousOn ψ (Set.Icc 0 (Real.pi / 2)))
    (hcoeff : ∀ n : ℕ, (∫ θ in Work.Spaces.Iθ,
        ψ θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
      = c n * (∫ θ in Work.Spaces.Iθ,
          Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ)) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (∑' m : ℕ, c m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) = ψ θ := by
  obtain ⟨C, hC, hdec⟩ := hdec
  set K : ℝ := max 1 (300 * C) with hKdef
  set u : ℕ → ℝ := fun m => K * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))⁻¹ with hudef
  have hDinv : ∀ m : ℕ, (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))⁻¹
      = (((m : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹ := by
    intro m
    congr 1
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (by positivity : (0 : ℝ) < (m : ℝ) + 1), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have hu : Summable u := by
    have hbase : Summable (fun m : ℕ => (((m : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := by
      have h0 : Summable (fun n : ℕ => (((n : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
        Real.summable_nat_rpow_inv.mpr (by norm_num)
      have h1 := (summable_nat_add_iff
        (f := fun n : ℕ => (((n : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹) 1).mpr h0
      simpa only [Nat.cast_add, Nat.cast_one] using h1
    have h2 : Summable (fun m : ℕ => (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))⁻¹) :=
      hbase.congr (fun m => (hDinv m).symm)
    simpa only [hudef, hKdef] using h2.mul_left K
  have hb : ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |c m * Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ u m :=
    fun m θ hθ => pointwise_bound hC hdec hzero m hθ
  have hcont : ContinuousOn
      (fun θ => ∑' m, c m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) Work.Spaces.Iθ :=
    continuousOn_tsum (s := Work.Spaces.Iθ) (u := u)
      (fun m => ((continuous_eFam m).const_mul (c m)).continuousOn) hu
      (fun m x hx => by rw [Real.norm_eq_abs]; exact hb m x hx)
  have hmom : ∀ n : ℕ, (∫ θ in Work.Spaces.Iθ,
      ψ θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
      = ∫ θ in Work.Spaces.Iθ,
          (∑' m, c m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
            * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ := by
    intro n
    rw [hcoeff n, hTsum c u hu hb n]
  intro θ hθ
  exact hMom ψ (fun θ => ∑' m, c m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
    hcontψ hcont (fun n => (hmom n).symm) θ hθ

/-! ## The target -/

theorem PsiExpansion : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (ψ : ℝ → ℝ), 0 < α → α ≤ 1 / 5 →
    Work.FTS.PhiStar.AngModel α ψ → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (∑' m : ℕ, Work.FTS.PhiStar.Series.cmode m (fun _ θ' => ψ θ') 0
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ) = ψ θ := by
  refine ⟨1, one_pos, fun α ψ hα hα5 hψ θ hθ => ?_⟩
  -- the coefficient decay of `CmodeDecay`
  obtain ⟨C, hC, hdec0⟩ := Work.FTS.PhiStar.Series.CmodeDecay
  have hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.cmode m (fun _ θ' => ψ θ') 0|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) :=
    ⟨C, hC, fun m hm => hdec0 α ψ hα hα5 hψ m hm⟩
  -- the `m = 0` coefficient vanishes by the moment condition
  have hzero : Work.FTS.PhiStar.Series.cmode 0 (fun _ θ' => ψ θ') 0 = 0 := by
    refine Work.FTS.PhiStar.Series.eFam_zero_moment (fun _ θ' => ψ θ') ?_
    simpa only [Work.Elliptic.Fstar] using hψ.moment
  -- the coefficients are the Fourier coefficients of `ψ`
  have hcoeff : ∀ n : ℕ, (∫ θ in Work.Spaces.Iθ,
        ψ θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
      = Work.FTS.PhiStar.Series.cmode n (fun _ θ' => ψ θ') 0
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) := by
    intro n
    have hnum := iota_eq_interval
      (fun θ => ψ θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
    have hden := iota_eq_interval
      (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ)
    have hne : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) ≠ 0 := by
      rw [← hden]
      exact ne_of_gt (eFam_norm_pos n)
    have hcm : Work.FTS.PhiStar.Series.cmode n (fun _ θ' => ψ θ') 0
        = (∫ θ in (0 : ℝ)..(Real.pi / 2),
              ψ θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
          / (∫ θ in (0 : ℝ)..(Real.pi / 2),
              Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) := by
      simp only [Work.FTS.PhiStar.Series.cmode]
    rw [hnum, hden, hcm, div_mul_cancel₀ _ hne]
  exact psiExpansionAux (fun m => Work.FTS.PhiStar.Series.cmode m (fun _ θ' => ψ θ') 0)
    hdec hzero tsum_moment
    Work.FTS.PhiStar.FlatWAux.PsiExpAux.MomentEqOn
    ψ hψ.cont hcoeff θ hθ

end Work.FTS.PhiStar.FlatWAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.RadGreenExpansionPhiAj =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

open scoped ContDiff

set_option autoImplicit false

/-! ## 1. `𝒜^j φ` is `C^∞` at every `z > 0` -/

/-- **`𝒜^j φ` is `C^∞` at every `z > 0`.**  Induction on `j`: `φ` is the explicit rational
function `4αz²(z−2)/(1+z)⁴ + 2(5+α)z(1−z)/(1+z)³` (`contDiffAt_phiA`), and the step is a sum of
products of the smooth `z²`, `z` with the first and second iterated derivatives of a `C^∞`
function. -/
theorem contDiffAt_Ajit_phiA_infty (α : ℝ) (j : ℕ) {z : ℝ} (hz : 0 < z) :
    ContDiffAt ℝ ∞ (Ajit α j (Work.FTS.VocabO.phiA α)) z := by
  induction j with
  | zero => simpa only [Ajit_zero] using Work.FTS.PhiStar.contDiffAt_phiA α hz
  | succ j ih =>
      rw [Ajit_succ]
      exact (((contDiffAt_const (c := α)).mul (contDiffAt_id.pow 2)).mul
          (Work.FTS.PhiStar.contDiffAt_infty_iteratedDeriv 2 ih)).add
        (((contDiffAt_const (c := (5 + α))).mul contDiffAt_id).mul
          (Work.FTS.PhiStar.contDiffAt_infty_deriv ih))

/-- The `ContDiffOn` form of `contDiffAt_Ajit_phiA_infty` at order `2`. -/
theorem contDiffOn_Ajit_phiA_two (α : ℝ) (j : ℕ) :
    ContDiffOn ℝ 2 (Ajit α j (Work.FTS.VocabO.phiA α)) (Set.Ioi 0) :=
  fun z hz =>
    ((contDiffAt_Ajit_phiA_infty α j hz).of_le (by simp : ((2 : ℕ∞ω)) ≤ ∞)).contDiffWithinAt

/-! ## 2. The one-step resolvent identity without the redundant integrability hypothesis -/

/-- **The mode-`m` resolvent identity** `λ_m·R = c + A R` under the *weak* hypothesis set of
`RadGreenSupport.radGreen_ode_weak`: no integrability of `c t·t^{-2m/α-1}` on `(0,1)`. -/
theorem radGreen_resolvent_weak {α : ℝ} (m : ℕ) {c : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hα : 0 < α) (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    Work.FTS.PhiStar.Radial.lamR m * Work.FTS.PhiStar.Radial.radGreen α m c z
      = c z + (α ^ 2 * z ^ 2 *
            deriv (deriv (Work.FTS.PhiStar.Radial.radGreen α m c)) z
          + α * (5 + α) * z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z) := by
  have h := Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak hα m hc h0 hinf z hz
  linarith [h]

/-- **The one-step resolvent identity** `R_m c = c/λ_m + (α/λ_m)·R_m(𝒜c)` in the form needed by
the `1/λ_m`-expansion; compared with `radGreen_step` the hypothesis
`IntegrableOn (fun t => c t·t^{-2m/α-1}) (Ioo 0 1)` is dropped (it is unused, and it fails for
`c = 𝒜^j φ`). -/
theorem radGreen_step_weak {α : ℝ} (m : ℕ) (hα : 0 < α) (hα5 : α ≤ 1 / 5) (hm : 1 ≤ m)
    {c : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A) (hc : ContDiffOn ℝ 2 c (Set.Ioi 0))
    (hb : ∀ k : ℕ, k ≤ 2 → ∀ t : ℝ, 0 < t →
      |iteratedDeriv k c t| ≤ A / (1 + t ^ (k + 1)))
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    ∀ z : ℝ, 0 < z → Work.FTS.PhiStar.Radial.radGreen α m c z
      = c z / Work.FTS.PhiStar.Radial.lamR m
        + (α / Work.FTS.PhiStar.Radial.lamR m)
            * Work.FTS.PhiStar.Radial.radGreen α m (Ajit α 1 c) z := by
  intro z hz
  have hres := radGreen_resolvent_weak m hz hα hc.continuousOn h0 hinf
  have hact := RadGreenActA (α := α) m hα hα5 hm hA hc hb z hz
  have hstep : Work.FTS.PhiStar.Radial.radGreen α m (Ajit α 1 c) z
      = α * z ^ 2 * iteratedDeriv 2 (Work.FTS.PhiStar.Radial.radGreen α m c) z
        + (5 + α) * z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z := by
    rw [Ajit_succ]
    exact hact
  have hite : iteratedDeriv 2 (Work.FTS.PhiStar.Radial.radGreen α m c) z
      = deriv (deriv (Work.FTS.PhiStar.Radial.radGreen α m c)) z := by
    simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  have hkey : Work.FTS.PhiStar.Radial.lamR m
      * Work.FTS.PhiStar.Radial.radGreen α m c z
      = c z + α * Work.FTS.PhiStar.Radial.radGreen α m (Ajit α 1 c) z := by
    rw [hres, hstep, hite]
    ring
  have hne := lamR_ne_zero hm
  field_simp
  linarith [hkey]

/-! ## 3. The expansion -/

theorem RadGreenExpansionPhiAj : ∀ (α : ℝ), 0 < α → α ≤ 1 / 5 → ∀ (m : ℕ), 1 ≤ m → ∀ z : ℝ, 0 < z →
    Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z
      = (∑ j ∈ Finset.range Work.FTS.PhiStar.FlatWAux.J,
          (α ^ j / (Work.FTS.PhiStar.Radial.lamR m) ^ (j + 1))
            * Work.FTS.PhiStar.FlatWAux.Ajit α j (Work.FTS.VocabO.phiA α) z)
        + (α ^ Work.FTS.PhiStar.FlatWAux.J
            / (Work.FTS.PhiStar.Radial.lamR m) ^ Work.FTS.PhiStar.FlatWAux.J)
            * Work.FTS.PhiStar.Radial.radGreen α m
                (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                  (Work.FTS.VocabO.phiA α)) z := by
  intro α hα hα5 m hm z hz
  obtain ⟨A, hApos, hA⟩ := PhiAjFlatDecayU
  refine radGreen_expansion (z := z) m (Work.FTS.VocabO.phiA α) J (lamR_ne_zero hm) ?_
  intro j hj
  have hj8 : j ≤ 8 := hj
  have hj9 : j + 1 ≤ 9 := by omega
  have hsmooth : ContDiffOn ℝ 2 (Ajit α j (Work.FTS.VocabO.phiA α)) (Set.Ioi 0) :=
    contDiffOn_Ajit_phiA_two α j
  have hb : ∀ k : ℕ, k ≤ 2 → ∀ t : ℝ, 0 < t →
      |iteratedDeriv k (Ajit α j (Work.FTS.VocabO.phiA α)) t| ≤ A / (1 + t ^ (k + 1)) := by
    intro k hk t ht
    have hk14 : k ≤ 14 := by omega
    simpa only [Ajit_phiA α j] using (hA α hα hα5 (j + 1) hj9).1 k hk14 t ht
  obtain ⟨h0, hinf⟩ :=
    Work.FTS.PhiStar.RadGreenSupport.src_integrable hα m hApos.le hsmooth hb
  have hstep := radGreen_step_weak (α := α) m hα hα5 hm hApos.le hsmooth hb h0 hinf z hz
  simpa only [Ajit_succ, Ajit_zero] using hstep

end Work.FTS.PhiStar.FlatWAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.fstarDat =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

/-!
# `fstarDat` --- the datum package for the fundamental profile `F_*`

This is the `ℱ`-side input of the level-six `N`-row: the three fields `F_*`, `D_θF_*`, `D_zF_*`
are `C^∞` on the open quadrant, their `𝒲^{6,∞}`-membership holds with norms `≤ Cα`, and every
slot `D_z^jD_θ^i` (`j + i ≤ 6`) obeys the *flat* pointwise price

  `|D_z^jD_θ^i F| ≤ Cα·z/(1+z)² · (1 if i = 0 else sin(2θ)^{α/3})`.

## Route

The pieces are already available, so the lemma is an assembly:

* `H6Pair6Aux.smoothOpen_Fstar` (with `SmoothOpen.Dth`, `SmoothOpen.Dz`) gives the three
  smoothness clauses (no hypothesis on `α`);
* `StrongPersist.Fstar_W6`, `StrongPersist.DthFstar_W6`, `StrongPersist.DzFstar_W6` give the
  `WlInfMem`/`WlInf` clauses (the `D_θ`-one with `α²`, which is `≤ α` since `α ≤ 1`);
* the pointwise clauses are `FS.G0_le`/`FS.G0_le_sin`, `FS.G1_le`/`FS.G1_le_sin`,
  `FS.G2_le`/`FS.G2_le_sin` from `fstar_slots` (where `F_* = c₀·(Γ ⊗ φ)`, `φ = z/(1+z)²`,
  `Γ = (sinθcos²θ)^{α/3}` and the `sin(2θ)^{α/3}` gain comes from `Γ ≤ sin(2θ)^{α/3}`).
-/

/-- The `i = 0` shape of the pointwise bound: the angular factor is `1`. -/
private lemma fd_plain_le {X a A α Hz : ℝ} (h : X ≤ a * α * Hz) (haA : a ≤ A) (hα : 0 ≤ α)
    (hHz : 0 ≤ Hz) : X ≤ A * α * Hz * 1 := by
  calc X ≤ a * α * Hz := h
    _ = a * (α * Hz) := by ring
    _ ≤ A * (α * Hz) := mul_le_mul_of_nonneg_right haA (mul_nonneg hα hHz)
    _ = A * α * Hz * 1 := by ring

/-- The `i ≥ 1` shape of the pointwise bound: the extra angular factor is
`sin(2θ)^{α/3}`. -/
private lemma fd_sin_le {X a A α Hz s : ℝ} (h : X ≤ a * α * s * Hz) (haA : a ≤ A) (hα : 0 ≤ α)
    (hs : 0 ≤ s) (hHz : 0 ≤ Hz) : X ≤ A * α * Hz * s := by
  calc X ≤ a * α * s * Hz := h
    _ = a * (α * (s * Hz)) := by ring
    _ ≤ A * (α * (s * Hz)) := mul_le_mul_of_nonneg_right haA (mul_nonneg hα (mul_nonneg hs hHz))
    _ = A * α * Hz * s := by ring

theorem fstarDat : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth (Work.Construction.Fstar α)) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz (Work.Construction.Fstar α)) ∧
    Work.Spaces.WlInfMem α 6 (Work.Construction.Fstar α) ∧
    Work.Spaces.WlInf α 6 (Work.Construction.Fstar α) ≤ C * α ∧
    Work.Spaces.WlInfMem α 6 (Work.Spaces.Dth (Work.Construction.Fstar α)) ∧
    Work.Spaces.WlInf α 6 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ C * α ∧
    Work.Spaces.WlInfMem α 6 (Work.Spaces.Dz (Work.Construction.Fstar α)) ∧
    Work.Spaces.WlInf α 6 (Work.Spaces.Dz (Work.Construction.Fstar α)) ≤ C * α ∧
    (∀ (A : Work.FTS.Galerkin.Fn),
        (A = Work.Construction.Fstar α ∨ A = Work.Spaces.Dth (Work.Construction.Fstar α) ∨
         A = Work.Spaces.Dz (Work.Construction.Fstar α)) →
        ∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |Work.Spaces.mixed j i A z θ| ≤ C * α * (z / (1 + z) ^ 2) *
            (if 1 ≤ i then (Real.sin (2 * θ)) ^ (α / 3) else 1)) := by
  obtain ⟨C1, hC1pos, hC1⟩ := Work.FTS.StrongPersist.Fstar_W6
  obtain ⟨C2, hC2pos, hC2⟩ := Work.FTS.StrongPersist.DthFstar_W6
  obtain ⟨C3, hC3pos, hC3⟩ := Work.FTS.StrongPersist.DzFstar_W6
  set C : ℝ := max C1 (max C2 (max C3 FS.Cst)) + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hC1le : C1 ≤ C := by
    rw [hCdef]
    have h := le_max_left C1 (max C2 (max C3 FS.Cst))
    linarith
  have hC2le : C2 ≤ C := by
    rw [hCdef]
    have h1 := le_max_left C2 (max C3 FS.Cst)
    have h2 := le_max_right C1 (max C2 (max C3 FS.Cst))
    linarith
  have hC3le : C3 ≤ C := by
    rw [hCdef]
    have h1 := le_max_left C3 FS.Cst
    have h2 := le_max_right C2 (max C3 FS.Cst)
    have h3 := le_max_right C1 (max C2 (max C3 FS.Cst))
    linarith
  have hCstle : FS.Cst ≤ C := by
    rw [hCdef]
    have h1 := le_max_right C3 FS.Cst
    have h2 := le_max_right C2 (max C3 FS.Cst)
    have h3 := le_max_right C1 (max C2 (max C3 FS.Cst))
    linarith
  refine ⟨C, hCpos, ?_⟩
  intro α hαIoc
  obtain ⟨hα, hα1⟩ := hαIoc
  obtain ⟨hwFmem, hwFle⟩ := hC1 α hα hα1
  obtain ⟨hwDmem, hwDle⟩ := hC2 α hα hα1
  obtain ⟨hwZmem, hwZle⟩ := hC3 α hα hα1
  refine ⟨?_, ?_, ?_, hwFmem, ?_, hwDmem, ?_, hwZmem, ?_, ?_⟩
  · exact Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  · exact (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α).Dth
  · exact (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α).Dz
  · exact le_trans hwFle (mul_le_mul_of_nonneg_right hC1le hα.le)
  · refine le_trans hwDle ?_
    calc C2 * α ^ 2 ≤ C * α ^ 2 := mul_le_mul_of_nonneg_right hC2le (sq_nonneg α)
      _ ≤ C * α := mul_le_mul_of_nonneg_left (by nlinarith [hα.le, hα1]) hCpos.le
  · exact le_trans hwZle (mul_le_mul_of_nonneg_right hC3le hα.le)
  · intro A hA j i hji z θ hz hθ0 hθ2
    have hθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ2⟩
    have hHz : 0 ≤ z / (1 + z) ^ 2 := div_nonneg hz.le (sq_nonneg (1 + z))
    have hs : 0 ≤ (Real.sin (2 * θ)) ^ (α / 3) := FS.sin_rpow_nonneg hθ
    rcases hA with rfl | rfl | rfl
    · by_cases hi : 1 ≤ i
      · rw [if_pos hi]
        have h := FS.G0_le_sin hα hα1 hi hji hz hθ
        rw [Work.Spaces.hKer_apply] at h
        exact fd_sin_le h hCstle hα.le hs hHz
      · rw [if_neg hi]
        have h := FS.G0_le hα hα1 hji hz hθ
        rw [Work.Spaces.hKer_apply] at h
        exact fd_plain_le h hCstle hα.le hHz
    · by_cases hi : 1 ≤ i
      · rw [if_pos hi]
        have h := FS.G1_le_sin hα hα1 hi hji hz hθ
        rw [Work.Spaces.hKer_apply] at h
        exact fd_sin_le h hCstle hα.le hs hHz
      · rw [if_neg hi]
        have h := FS.G1_le hα hα1 hji hz hθ
        rw [Work.Spaces.hKer_apply] at h
        exact fd_plain_le h hCstle hα.le hHz
    · by_cases hi : 1 ≤ i
      · rw [if_pos hi]
        have h := FS.G2_le_sin hα hα1 hi hji hz hθ
        rw [Work.Spaces.hKer_apply] at h
        exact fd_sin_le h hCstle hα.le hs hHz
      · rw [if_neg hi]
        have h := FS.G2_le hα hα1 hji hz hθ
        rw [Work.Spaces.hKer_apply] at h
        exact fd_plain_le h hCstle hα.le hHz

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
