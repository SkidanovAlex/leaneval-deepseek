import Mathlib
import Submission.Work.BourgainPlan.Maximal.DRDFDefs
import Submission.Work.BourgainPlan.Maximal.dyadic_reduction
import Submission.Work.BourgainPlan.Maximal.Ts_l2_decay
import Submission.Work.BourgainPlan.Maximal.Ts_lp_uniform
import Submission.Work.BourgainPlan.Maximal.MtaDefs
import Submission.Work.BourgainPlan.Maximal.mtaBlkSymSum_bound
import Submission.Work.BourgainPlan.Maximal.mtaBlkSymSum_tendsto
import Submission.Work.BourgainPlan.Maximal.mtaBlkOp_l1_linear
import Submission.Work.BourgainPlan.Maximal.mtaBlkOpSum_multiplier_ae
import Submission.Work.BourgainPlan.Maximal.dyadSum_multiplier_ae
import Submission.Work.BourgainPlan.Maximal.mtaBlkOp_trunc_interp
import Submission.Work.BourgainPlan.Maximal.mta_theta_sum_le

/-!
# The assembly of `mst_theta_real` (step 6 of `Maximal/DRDF_ROUTE.md`)

This is the final assembly of the `L^{2r}` bound for the signed lacunary sum of curve-average
differences (Bourgain's / Mirek–Stein–Trojan's input `(C2)`) from the block decomposition of the
Duoandikoetxea–Rubio de Francia route:

* the blocks `T_s` (`|s| ≤ 2^i`-lacunary) have `L²` decay `2^{-|s|/d}` (`Ts_l2_decay`) and a uniform
  `L^{p₁}` bound (`Ts_lp_uniform`);
* Marcinkiewicz interpolation at each scale (`mtaBlkOp_trunc_interp`) gives a per-block `L^p` bound
  with constant `≍ (2^{-|s|/d})^θ`, whose sum over `s ∈ ℤ` is finite (`mta_theta_sum_le`);
* the partial sums over `|s| ≤ S` are compared with the untruncated operator on the Fourier side
  (`mtaBlkOpSum_multiplier_ae`, `dyadSum_multiplier_ae`, `mtaBlkSymSum_tendsto`), and Fatou's lemma
  along an a.e.-convergent subsequence (`mta_lintegral_le_of_diag`) finishes.
-/

open MeasureTheory Finset
open scoped ENNReal BigOperators FourierTransform Topology

set_option maxHeartbeats 4000000

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal
noncomputable section

/-! ## TEMPORARY axioms (scratch development only) -/

/-! ## The assembly core -/


/-- **Fatou step.**  If `V n → dys` in `L²` and `‖V n‖_p ≤ C` uniformly, then `‖dys‖_p ≤ C`. -/
lemma mta_lintegral_le_of_diag {V : ℕ → ℝ → ℂ} {dys : ℝ → ℂ} {p : ℝ} (hp0 : 0 < p) (C : ℝ≥0∞)
    (hsm : ∀ n : ℕ, AEStronglyMeasurable (V n) volume)
    (hdys : AEStronglyMeasurable dys volume)
    (hdiag : Filter.Tendsto (fun n : ℕ => eLpNorm (V n - dys) 2 volume) Filter.atTop (𝓝 0))
    (hbdd : ∀ n : ℕ, eLpNorm (V n) (ENNReal.ofReal p) volume ≤ C) :
    eLpNorm dys (ENNReal.ofReal p) volume ≤ C := by
  have hTIM : TendstoInMeasure volume V (Filter.atTop : Filter ℕ) dys :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := (2:ℝ≥0∞)) (by norm_num) hdiag
  obtain ⟨ns, _hnsmono, hnsae⟩ := hTIM.exists_seq_tendsto_ae
  exact Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall (fun i => hbdd (ns i)))
    (fun i => hsm (ns i)) hdys hnsae

/-- A.e. strong measurability of the block operator on `L¹` (the strong form of
`Work.BourgainPlan.MtaLin.mtaBlkOp_aemeasurable`, needed for the `eLpNorm` monotonicity steps). -/
private lemma mtaBlkOp_aesm (P : Polynomial ℤ) (K : ℕ) (ε : ℕ → ℂ) (s : ℤ) {u : ℝ → ℂ}
    (hu : Integrable u) : AEStronglyMeasurable (mtaBlkOp P K ε s u) (volume : Measure ℝ) := by
  have hterm : ∀ k ∈ Finset.range K, AEStronglyMeasurable (fun x : ℝ =>
      dyadicProj dyadTilde ((P.natDegree : ℤ) * (k : ℤ) + s)
        (fun y => ε k * dyadicProj dyadPsi ((P.natDegree : ℤ) * (k : ℤ) + s) (dyadD P k u) y) x)
      (volume : Measure ℝ) := by
    intro k _
    have hD : Integrable (dyadD P k u) := by
      unfold dyadD
      exact (Work.BourgainPlan.MtaLin.integrable_curveSigma P (2^k) hu).sub
        (Work.BourgainPlan.MtaLin.integrable_curveSigma P (2^(k+1)) hu)
    exact (Work.BourgainPlan.MtaLin.continuous_dyadicProj_dyadTilde
      ((integrable_dyadicProj (m := (P.natDegree : ℤ) * (k : ℤ) + s) hD).const_mul
        (ε k))).aestronglyMeasurable
  have hsum := Finset.aestronglyMeasurable_sum (Finset.range K) hterm
  have hfun : (∑ k ∈ Finset.range K, fun x : ℝ =>
      dyadicProj dyadTilde ((P.natDegree : ℤ) * (k : ℤ) + s)
        (fun y => ε k * dyadicProj dyadPsi ((P.natDegree : ℤ) * (k : ℤ) + s) (dyadD P k u) y) x)
      = mtaBlkOp P K ε s u := by
    funext x
    simp only [mtaBlkOp, Finset.sum_apply]
  rw [← hfun]
  exact hsum

theorem mta_core (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) (hlc : 0 < P.leadingCoeff)
    (p : ℝ) (hp : 4 ≤ p) :
    ∃ A : ℝ, 0 < A ∧ ∀ (K : ℕ) (ε : ℕ → ℂ), (∀ k : ℕ, ‖ε k‖ ≤ 1) →
      ∀ (h : ℝ → ℂ), Integrable h →
      ∫⁻ x : ℝ, ‖dyadSum P K ε h x‖ₑ ^ p ∂volume
        ≤ ENNReal.ofReal (A ^ p) * ∫⁻ x : ℝ, ‖h x‖ₑ ^ p ∂volume := by
  classical
  set p₁ : ℝ := 2 * p with hp₁def
  have hp2 : 2 < p := by linarith
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  have hpp₁ : p < p₁ := by rw [hp₁def]; linarith
  have hp₁2 : 2 < p₁ := by rw [hp₁def]; linarith
  have hp₁0 : 0 < p₁ := by linarith
  set θ : ℝ := 2 * (p₁ - p) / (p * (p₁ - 2)) with hθdef
  have hθpos : 0 < θ := by
    rw [hθdef]
    exact div_pos (by linarith) (mul_pos hp0 (by linarith))
  -- constants
  obtain ⟨C₂, hC₂pos, hTs₂⟩ := Ts_l2_decay P hdeg hlc
  obtain ⟨B, hBpos, hTsP⟩ := Ts_lp_uniform P hdeg hlc p₁ hp₁2
  have hL₂ : ∀ (K : ℕ) (ε : ℕ → ℂ), (∀ k : ℕ, ‖ε k‖ ≤ 1) → ∀ (s : ℤ) (g : ℝ → ℂ),
      MemLp g 2 volume →
      eLpNorm (mtaBlkOp P K ε s g) 2 volume
        ≤ ENNReal.ofReal (C₂ * (2:ℝ) ^ (-(↑(|s|) : ℝ) / (P.natDegree : ℝ))) * eLpNorm g 2 volume := by
    intro K ε hε s g hg
    rw [Int.cast_abs]
    exact hTs₂ K ε hε s g hg
  have hLp₁ : ∀ (K : ℕ) (ε : ℕ → ℂ), (∀ k : ℕ, ‖ε k‖ ≤ 1) → ∀ (s : ℤ) (g : ℝ → ℂ),
      MemLp g (ENNReal.ofReal p₁) volume →
      eLpNorm (mtaBlkOp P K ε s g) (ENNReal.ofReal p₁) volume
        ≤ ENNReal.ofReal B * eLpNorm g (ENNReal.ofReal p₁) volume :=
    fun K ε hε s g hg => hTsP K ε hε s g hg
  have hadd : ∀ (K : ℕ) (ε : ℕ → ℂ) (s : ℤ) {u v : ℝ → ℂ}, Integrable u → Integrable v → ∀ x : ℝ,
      mtaBlkOp P K ε s (u + v) x = mtaBlkOp P K ε s u x + mtaBlkOp P K ε s v x :=
    fun K ε s u v hu hv x => (mtaBlkOp_l1_linear P K ε s).1 hu hv x
  have hsmul : ∀ (K : ℕ) (ε : ℕ → ℂ) (s : ℤ) (c : ℂ) (u : ℝ → ℂ) (x : ℝ),
      mtaBlkOp P K ε s (c • u) x = c * mtaBlkOp P K ε s u x :=
    fun K ε s c u x => (mtaBlkOp_l1_linear P K ε s).2.1 c u x
  have hmeas : ∀ (K : ℕ) (ε : ℕ → ℂ) (s : ℤ) {u : ℝ → ℂ}, Integrable u →
      AEMeasurable (fun x : ℝ => ‖mtaBlkOp P K ε s u x‖ₑ) volume :=
    fun K ε s u hu => (mtaBlkOp_l1_linear P K ε s).2.2 hu
  obtain ⟨c, hcpos, hinterp⟩ :=
    mtaBlkOp_trunc_interp P p p₁ hp2 hpp₁ C₂ B hC₂pos hBpos hL₂ hLp₁ hadd hsmul hmeas
  have hinterp' : ∀ (K : ℕ) (ε : ℕ → ℂ), (∀ k : ℕ, ‖ε k‖ ≤ 1) → ∀ (s : ℤ) (N : ℕ) (f : ℝ → ℂ),
      MemLp f (ENNReal.ofReal p) volume →
      eLpNorm (fun x : ℝ => ‖mtaBlkOp P K ε s (mtaTrunc N f) x‖ₑ) (ENNReal.ofReal p) volume
        ≤ ENNReal.ofReal (c * (C₂ * (2:ℝ) ^ (-(↑(|s|) : ℝ) / (P.natDegree : ℝ))) ^ θ * B ^ (1 - θ))
          * eLpNorm f (ENNReal.ofReal p) volume := by
    intro K ε hε s N f hf
    rw [hθdef]
    exact hinterp K ε hε s N f hf
  obtain ⟨Ageo, hAgeopos, hgeo⟩ :=
    mta_theta_sum_le C₂ B c hC₂pos hBpos hcpos P.natDegree (by omega) θ hθpos
  obtain ⟨Ageo2, hAgeo2pos, hgeo2'⟩ :=
    mta_theta_sum_le 1 1 1 one_pos one_pos one_pos P.natDegree (by omega) 1 one_pos
  have hgeo2 : ∀ S : ℕ,
      ∑ s ∈ Finset.Icc (-(S : ℤ)) (S : ℤ), (2:ℝ) ^ (-(↑(|s|) : ℝ) / (P.natDegree : ℝ)) ≤ Ageo2 := by
    intro S
    have h := hgeo2' S
    simpa using h
  refine ⟨Ageo, hAgeopos, ?_⟩
  intro K ε hε h hhint
  by_cases htop : ∫⁻ x : ℝ, ‖h x‖ₑ ^ p ∂volume = ⊤
  · rw [htop, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hAgeopos p)))]
    exact le_top
  · have hmem_p : MemLp h (ENNReal.ofReal p) volume := by
      rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_ne_zero_iff.mpr hp0)
        ENNReal.ofReal_ne_top hhint.1, ENNReal.toReal_ofReal hp0.le]
      exact (ENNReal.rpow_lt_top_iff_of_pos (by positivity : (0:ℝ) < 1/p)).mpr
        (lt_top_iff_ne_top.mpr htop)
    have hfin1 : ∫⁻ x : ℝ, ‖h x‖ₑ < ⊤ := by
      simpa only [hasFiniteIntegral_iff_enorm] using hhint.2
    have hfinp : ∫⁻ x : ℝ, ‖h x‖ₑ ^ p < ⊤ := lt_top_iff_ne_top.mpr htop
    have hmem_2 : MemLp h 2 volume := by
      rw [memLp_iff]
      have hle : ∫⁻ x : ℝ, ‖h x‖ₑ ^ (2:ℝ) ≤ ∫⁻ x : ℝ, (‖h x‖ₑ + ‖h x‖ₑ ^ p) := by
        refine lintegral_mono (fun x => ?_)
        rcases eq_or_ne (‖h x‖ₑ) ⊤ with hx | hx
        · rw [hx]; simp
        · have hpos : (0:ℝ) ≤ (‖h x‖ₑ).toReal := ENNReal.toReal_nonneg
          have hreal : (‖h x‖ₑ).toReal ^ 2 ≤ (‖h x‖ₑ).toReal + (‖h x‖ₑ).toReal ^ p := by
            by_cases h1 : (‖h x‖ₑ).toReal ≤ 1
            · nlinarith [Real.rpow_nonneg hpos p]
            · have h2 : (‖h x‖ₑ).toReal ^ (2:ℝ) ≤ (‖h x‖ₑ).toReal ^ p :=
                Real.rpow_le_rpow_of_exponent_le (not_le.mp h1).le hp2.le
              rw [Real.rpow_two] at h2
              linarith [Real.rpow_nonneg hpos p]
          rw [← ENNReal.ofReal_toReal hx,
            ENNReal.ofReal_rpow_of_nonneg hpos (by norm_num : (0:ℝ) ≤ 2), Real.rpow_two,
            ENNReal.ofReal_rpow_of_nonneg hpos hp0.le,
            ← ENNReal.ofReal_add hpos (Real.rpow_nonneg hpos p)]
          exact ENNReal.ofReal_le_ofReal hreal
      have hsum : ∫⁻ x : ℝ, (‖h x‖ₑ + ‖h x‖ₑ ^ p) = (∫⁻ x : ℝ, ‖h x‖ₑ) + ∫⁻ x : ℝ, ‖h x‖ₑ ^ p :=
        lintegral_add_left' (hhint.aemeasurable.enorm) _
      have hkey : ∫⁻ x : ℝ, ‖h x‖ₑ ^ (2:ℝ) < ⊤ :=
        lt_of_le_of_lt hle (by rw [hsum]; exact ENNReal.add_lt_top.mpr ⟨hfin1, hfinp⟩)
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num : (2:ℝ≥0∞) ≠ ⊤)
          hhint.1,
        show (2:ℝ≥0∞).toReal = 2 by norm_num]
      exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0:ℝ) < 1/2)).mpr hkey
    have hint_trunc : ∀ N : ℕ, Integrable (mtaTrunc N h) volume := by
      intro N
      have hmeas : AEStronglyMeasurable (fun x : ℝ => mtaTrunc N h x) volume :=
        AEStronglyMeasurable.mul (hhint.1)
          ((measurable_const.indicator measurableSet_Icc).aestronglyMeasurable)
      refine ⟨hmeas, lt_of_le_of_lt (lintegral_mono (fun x => ?_)) hhint.2⟩
      rw [enorm_ofReal_eq_cplx, enorm_ofReal_eq_cplx]
      exact ENNReal.ofReal_le_ofReal (norm_mtaTrunc_apply_le N h x)
    have hmem2_trunc : ∀ N : ℕ, MemLp (mtaTrunc N h) 2 volume := by
      intro N
      exact MemLp.mono (f := mtaTrunc N h) (g := h) hmem_2 ((hint_trunc N).1)
        (Filter.Eventually.of_forall (fun x => norm_mtaTrunc_apply_le N h x))
    have hmem2_diff : ∀ N : ℕ, MemLp (fun x : ℝ => mtaTrunc N h x - h x) 2 volume := by
      intro N
      refine MemLp.mono (f := fun x : ℝ => mtaTrunc N h x - h x) (g := h) hmem_2
        (((hint_trunc N).1).sub (hhint.1)) (Filter.Eventually.of_forall (fun x => ?_))
      rw [mtaTrunc]
      rcases Set.indicator_eq_zero_or_self (s := Set.Icc (-(N:ℝ)) (N:ℝ)) (f := fun _ => (1:ℂ)) x with hh | hh
      · rw [hh, mul_zero, zero_sub, norm_neg]
      · rw [hh, mul_one, sub_self, norm_zero]; exact norm_nonneg _
    -- (A) the per-block bound
    have hblk : ∀ (s : ℤ) (N : ℕ) (f : ℝ → ℂ), MemLp f (ENNReal.ofReal p) volume →
        eLpNorm (mtaBlkOp P K ε s (mtaTrunc N f)) (ENNReal.ofReal p) volume
          ≤ ENNReal.ofReal (c * (C₂ * (2:ℝ) ^ (-(↑(|s|) : ℝ) / (P.natDegree : ℝ))) ^ θ * B ^ (1 - θ))
              * eLpNorm f (ENNReal.ofReal p) volume := by
      intro s N f hf
      have h1 := hinterp' K ε hε s N f hf
      rwa [eLpNorm_enorm _ (mtaBlkOp_aesm P K ε s (integrable_mtaTrunc_of_memLp N hp1 hf))] at h1
    -- (B) uniform bound for truncated partial sums
    have hfac : ∀ S N : ℕ,
        eLpNorm (fun x : ℝ => ∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ),
            mtaBlkOp P K ε s (mtaTrunc N h) x) (ENNReal.ofReal p) volume
          ≤ ENNReal.ofReal (∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ),
              c * (C₂ * (2:ℝ) ^ (-(↑(|s|) : ℝ) / (P.natDegree : ℝ))) ^ θ * B ^ (1 - θ))
            * eLpNorm h (ENNReal.ofReal p) volume := by
      intro S N
      have h1 : eLpNorm (fun x : ℝ => ∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ),
            mtaBlkOp P K ε s (mtaTrunc N h) x) (ENNReal.ofReal p) volume
          ≤ ∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ),
              eLpNorm (fun x : ℝ => ‖mtaBlkOp P K ε s (mtaTrunc N h) x‖ₑ) (ENNReal.ofReal p) volume := by
        have hpt : ∀ x : ℝ,
            ‖∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ), mtaBlkOp P K ε s (mtaTrunc N h) x‖ₑ
              ≤ ‖(∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ),
                  ‖mtaBlkOp P K ε s (mtaTrunc N h) x‖ₑ : ℝ≥0∞)‖ₑ := by
          intro x
          rw [enorm_eq_self]
          exact enorm_sum_le _ _
        refine (eLpNorm_mono_enorm_ae (Finset.aestronglyMeasurable_fun_sum _
          (fun s _ => mtaBlkOp_aesm P K ε s (hint_trunc N))) (Filter.Eventually.of_forall hpt)).trans ?_
        exact Commons.MeasureTheory.Lp.eLpNorm_finset_sum_le_ennreal (ENNReal.one_le_ofReal.mpr hp1)
          (fun s _ => hmeas K ε s (hint_trunc N))
      calc eLpNorm (fun x : ℝ => ∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ),
            mtaBlkOp P K ε s (mtaTrunc N h) x) (ENNReal.ofReal p) volume
          ≤ ∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ),
              eLpNorm (fun x : ℝ => ‖mtaBlkOp P K ε s (mtaTrunc N h) x‖ₑ) (ENNReal.ofReal p) volume := h1
        _ = ∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ),
              eLpNorm (mtaBlkOp P K ε s (mtaTrunc N h)) (ENNReal.ofReal p) volume := by
              exact Finset.sum_congr rfl fun s _ =>
                eLpNorm_enorm _ (mtaBlkOp_aesm P K ε s (hint_trunc N))
        _ ≤ ∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ),
              ENNReal.ofReal (c * (C₂ * (2:ℝ) ^ (-(↑(|s|) : ℝ) / (P.natDegree : ℝ))) ^ θ * B ^ (1 - θ))
                * eLpNorm h (ENNReal.ofReal p) volume := by
              refine Finset.sum_le_sum (fun s _ => ?_)
              exact hblk s N h hmem_p
        _ = ENNReal.ofReal (∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ),
              c * (C₂ * (2:ℝ) ^ (-(↑(|s|) : ℝ) / (P.natDegree : ℝ))) ^ θ * B ^ (1 - θ))
              * eLpNorm h (ENNReal.ofReal p) volume := by
              rw [← Finset.sum_mul]
              congr 1
              rw [ENNReal.ofReal_sum_of_nonneg (fun s _ => by positivity)]
    have hbound : ∀ S N : ℕ,
        eLpNorm (fun x : ℝ => ∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ),
            mtaBlkOp P K ε s (mtaTrunc N h) x) (ENNReal.ofReal p) volume
          ≤ ENNReal.ofReal Ageo * eLpNorm h (ENNReal.ofReal p) volume :=
      fun S N => (hfac S N).trans
        (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hgeo S)) zero_le)
    -- (C) the truncation difference
    have hdiff : ∀ S N : ℕ,
        eLpNorm (fun x : ℝ => (∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ), mtaBlkOp P K ε s (mtaTrunc N h) x)
            - (∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ), mtaBlkOp P K ε s h x)) 2 volume
          ≤ ENNReal.ofReal (C₂ * Ageo2) * eLpNorm (fun x : ℝ => mtaTrunc N h x - h x) 2 volume := by
      intro S N
      have hpt : (fun x : ℝ => (∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ), mtaBlkOp P K ε s (mtaTrunc N h) x)
            - (∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ), mtaBlkOp P K ε s h x))
          = fun x : ℝ => ∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ),
              mtaBlkOp P K ε s (mtaTrunc N h - h) x := by
        funext x
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        have h2 : mtaBlkOp P K ε s (mtaTrunc N h) x
            = mtaBlkOp P K ε s (mtaTrunc N h - h) x + mtaBlkOp P K ε s h x := by
          have hh2 := hadd K ε s ((hint_trunc N).sub hhint) hhint x
          rwa [sub_add_cancel] at hh2
        rw [h2]; ring
      rw [hpt]
      have h1 : eLpNorm (fun x : ℝ => ∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ),
            mtaBlkOp P K ε s (mtaTrunc N h - h) x) 2 volume
          ≤ ∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ),
              eLpNorm (fun x : ℝ => ‖mtaBlkOp P K ε s (mtaTrunc N h - h) x‖ₑ) 2 volume := by
        have hpt : ∀ x : ℝ,
            ‖∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ), mtaBlkOp P K ε s (mtaTrunc N h - h) x‖ₑ
              ≤ ‖(∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ),
                  ‖mtaBlkOp P K ε s (mtaTrunc N h - h) x‖ₑ : ℝ≥0∞)‖ₑ := by
          intro x
          rw [enorm_eq_self]
          exact enorm_sum_le _ _
        refine (eLpNorm_mono_enorm_ae (Finset.aestronglyMeasurable_fun_sum _
          (fun s _ => mtaBlkOp_aesm P K ε s ((hint_trunc N).sub hhint)))
          (Filter.Eventually.of_forall hpt)).trans ?_
        exact Commons.MeasureTheory.Lp.eLpNorm_finset_sum_le_ennreal (by norm_num)
          (fun s _ => hmeas K ε s ((hint_trunc N).sub hhint))
      calc eLpNorm (fun x : ℝ => ∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ),
            mtaBlkOp P K ε s (mtaTrunc N h - h) x) 2 volume
          ≤ ∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ),
              eLpNorm (fun x : ℝ => ‖mtaBlkOp P K ε s (mtaTrunc N h - h) x‖ₑ) 2 volume := h1
        _ = ∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ),
              eLpNorm (mtaBlkOp P K ε s (mtaTrunc N h - h)) 2 volume := by
              exact Finset.sum_congr rfl fun s _ =>
                eLpNorm_enorm _ (mtaBlkOp_aesm P K ε s ((hint_trunc N).sub hhint))
        _ ≤ ∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ),
              ENNReal.ofReal (C₂ * (2:ℝ) ^ (-(↑(|s|) : ℝ) / (P.natDegree : ℝ)))
                * eLpNorm (fun x : ℝ => mtaTrunc N h x - h x) 2 volume := by
              refine Finset.sum_le_sum (fun s _ => ?_)
              rw [Int.cast_abs]
              exact hTs₂ K ε hε s _ (hmem2_diff N)
        _ = ENNReal.ofReal (C₂ * (∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ),
              (2:ℝ) ^ (-(↑(|s|) : ℝ) / (P.natDegree : ℝ)))) * eLpNorm (fun x : ℝ => mtaTrunc N h x - h x) 2 volume := by
              rw [← Finset.sum_mul]
              congr 1
              rw [ENNReal.ofReal_mul hC₂pos.le,
                ENNReal.ofReal_sum_of_nonneg (fun s _ => by positivity), Finset.mul_sum]
              refine Finset.sum_congr rfl (fun s _ => ?_)
              rw [ENNReal.ofReal_mul hC₂pos.le]
        _ ≤ ENNReal.ofReal (C₂ * Ageo2) * eLpNorm (fun x : ℝ => mtaTrunc N h x - h x) 2 volume := by
              refine mul_le_mul_of_nonneg_right ?_ zero_le
              exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hgeo2 S) hC₂pos.le)
    -- (D) the truncation vanishes
    have hΔ : Filter.Tendsto (fun N : ℕ => eLpNorm (fun x : ℝ => mtaTrunc N h x - h x) 2 volume)
        Filter.atTop (𝓝 0) := by
      set h' : ℝ → ℂ := hhint.aemeasurable.mk h with h'h'
      have h'meas : Measurable h' := hhint.aemeasurable.measurable_mk
      have h'ae : h =ᵐ[volume] h' := hhint.aemeasurable.ae_eq_mk
      have heq : ∀ N : ℕ,
          (fun x : ℝ => mtaTrunc N h x - h x) =ᵐ[volume] (fun x : ℝ => mtaTrunc N h' x - h' x) := by
        intro N
        filter_upwards [h'ae] with x hx
        rw [mtaTrunc, mtaTrunc, hx]
      rw [show (fun N : ℕ => eLpNorm (fun x : ℝ => mtaTrunc N h x - h x) 2 volume)
          = fun N : ℕ => eLpNorm (fun x : ℝ => mtaTrunc N h' x - h' x) 2 volume from
            funext (fun N => eLpNorm_congr_ae (heq N))]
      have h'ham : AEStronglyMeasurable h' volume := h'meas.aestronglyMeasurable
      have hmem2' : MemLp h' 2 volume := hmem_2.ae_eq (by filter_upwards [h'ae] with x hx; rw [hx])
      have hkeylin : Filter.Tendsto (fun N : ℕ =>
          ∫⁻ x : ℝ, ‖mtaTrunc N h' x - h' x‖ₑ ^ (2:ℝ) ∂volume) Filter.atTop (𝓝 0) := by
        have hmeasF : ∀ N : ℕ, Measurable (fun x : ℝ => ‖mtaTrunc N h' x - h' x‖ₑ ^ (2:ℝ)) := by
          intro N
          have hm : Measurable (fun x : ℝ => mtaTrunc N h' x - h' x) := by
            unfold mtaTrunc
            exact (h'meas.mul (measurable_const.indicator measurableSet_Icc)).sub h'meas
          exact hm.enorm.pow_const (2:ℝ)
        have hbd : ∀ N : ℕ, (fun x : ℝ => ‖mtaTrunc N h' x - h' x‖ₑ ^ (2:ℝ))
            ≤ᵐ[volume] (fun x : ℝ => ‖h' x‖ₑ ^ (2:ℝ)) := by
          intro N
          refine Filter.Eventually.of_forall (fun x => ?_)
          refine ENNReal.rpow_le_rpow ?_ (by norm_num)
          rw [mtaTrunc]
          rcases Set.indicator_eq_zero_or_self (s := Set.Icc (-(N:ℝ)) (N:ℝ)) (f := fun _ => (1:ℂ)) x with hh | hh
          · rw [hh, mul_zero, zero_sub, enorm_neg]
          · rw [hh, mul_one, sub_self, enorm_zero]; exact bot_le
        have hfinb : ∫⁻ x : ℝ, ‖h' x‖ₑ ^ (2:ℝ) ∂volume ≠ ⊤ := by
          rw [lintegral_rpow_eq_eLpNorm_rpow (by norm_num : (0:ℝ) < 2) _ h'ham.enorm,
            eLpNorm_enorm _ h'ham]
          exact ENNReal.rpow_ne_top_of_nonneg (by norm_num)
            (by simpa using (ne_of_lt hmem2'.eLpNorm_lt_top))
        have hlim : ∀ᵐ x ∂volume, Filter.Tendsto (fun N : ℕ =>
            ‖mtaTrunc N h' x - h' x‖ₑ ^ (2:ℝ)) Filter.atTop (𝓝 0) := by
          refine Filter.Eventually.of_forall (fun x => ?_)
          have hx : ∀ N : ℕ, Nat.ceil |x| ≤ N → mtaTrunc N h' x - h' x = 0 := by
            intro N hN
            have hN' : |x| ≤ (N : ℝ) := le_trans (Nat.le_ceil |x|) (by exact_mod_cast hN)
            rw [mtaTrunc_eq_self_of_mem (show x ∈ Set.Icc (-(N:ℝ)) (N:ℝ) from
              ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩), sub_self]
          refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
          filter_upwards [Filter.eventually_ge_atTop (Nat.ceil |x|)] with N hN
          rw [hx N hN]; simp
        have := tendsto_lintegral_of_dominated_convergence (fun x : ℝ => ‖h' x‖ₑ ^ (2:ℝ))
          hmeasF hbd hfinb hlim
        simpa using this
      have heq2 : ∀ N : ℕ, eLpNorm (fun x : ℝ => mtaTrunc N h' x - h' x) 2 volume
          = (∫⁻ x : ℝ, ‖mtaTrunc N h' x - h' x‖ₑ ^ (2:ℝ) ∂volume) ^ ((1:ℝ)/2) := by
        intro N
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num : (2:ℝ≥0∞) ≠ ⊤)
          (f := fun x : ℝ => mtaTrunc N h' x - h' x)
          (by
            unfold mtaTrunc
            exact ((h'meas.mul (measurable_const.indicator measurableSet_Icc)).sub
              h'meas).aestronglyMeasurable)]
        norm_num
      simp_rw [heq2]
      have hcont : Filter.Tendsto (fun a : ℝ≥0∞ => a ^ ((1:ℝ)/2)) (𝓝 (0:ℝ≥0∞)) (𝓝 0) := by
        have h := (ENNReal.continuous_rpow_const (y := (1:ℝ)/2)).tendsto 0
        rwa [ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 1/2)] at h
      exact hcont.comp hkeylin

    -- (E) the reconstruction: the untruncated partial sums converge to `dyadSum`
    obtain ⟨Csym, hCsympos, hCsymbd⟩ := mtaBlkSymSum_bound P hdeg hlc
    obtain ⟨Cμ, hCμpos, hCμbd⟩ := sum_norm_muSym_le P hdeg hlc
    have hFullbd : ∀ ξ : ℝ, ‖mtaFullSym P K ε ξ‖ ≤ Cμ := by
      intro ξ
      rw [mtaFullSym]
      calc ‖∑ k ∈ Finset.range K, ε k * muSym P k ξ‖
          ≤ ∑ k ∈ Finset.range K, ‖ε k * muSym P k ξ‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.range K, ‖muSym P k ξ‖ := by
            refine Finset.sum_le_sum (fun k _ => ?_)
            rw [norm_mul]
            simpa using mul_le_mul_of_nonneg_right (hε k) (norm_nonneg (muSym P k ξ))
        _ ≤ Cμ := hCμbd K ξ
    have hEq : ∀ S : ℕ,
        eLpNorm (fun x : ℝ => (∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ), mtaBlkOp P K ε s h x)
            - dyadSum P K ε h x) 2 volume
          = (∫⁻ ξ : ℝ, ‖mtaBlkSymSum P K ε S ξ - mtaFullSym P K ε ξ‖ₑ ^ (2:ℝ)
              * ‖𝓕 h ξ‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
      intro S
      obtain ⟨hmS, hSae⟩ := mtaBlkOpSum_multiplier_ae P K ε S hhint hmem_2
      obtain ⟨hmF, hFae⟩ := dyadSum_multiplier_ae P K ε hhint hmem_2
      set M1 : Lp ℂ 2 (volume : Measure ℝ) :=
        Commons.Analysis.Fourier.BoundaryLayer.multiplier (mtaBlkSymSum P K ε S) hmS
          (MemLp.toLp h hmem_2) with hM1
      set M2 : Lp ℂ 2 (volume : Measure ℝ) :=
        Commons.Analysis.Fourier.BoundaryLayer.multiplier (mtaFullSym P K ε) hmF
          (MemLp.toLp h hmem_2) with hM2
      set MΔ : Lp ℂ 2 (volume : Measure ℝ) :=
        Commons.Analysis.Fourier.BoundaryLayer.multiplier
          (fun ξ : ℝ => mtaBlkSymSum P K ε S ξ - mtaFullSym P K ε ξ) (hmS.sub hmF)
          (MemLp.toLp h hmem_2) with hMΔ
      have hD : MΔ = M1 - M2 := (multiplier_sub_sym (mtaBlkSymSum P K ε S) (mtaFullSym P K ε)
        hmS hmF (hmS.sub hmF) (MemLp.toLp h hmem_2))
      have hae : (fun x : ℝ => (∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ), mtaBlkOp P K ε s h x)
            - dyadSum P K ε h x) =ᵐ[volume] (MΔ : ℝ → ℂ) := by
        refine (hSae.sub hFae).trans ?_
        refine ((Lp.coeFn_sub M1 M2).symm.trans ?_)
        rw [← hD]
      calc eLpNorm (fun x : ℝ => (∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ), mtaBlkOp P K ε s h x)
            - dyadSum P K ε h x) 2 volume
          = eLpNorm ((MΔ : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) 2 volume := eLpNorm_congr_ae hae
        _ = ‖MΔ‖ₑ := (Lp.enorm_def MΔ).symm
        _ = (∫⁻ ξ : ℝ, ‖mtaBlkSymSum P K ε S ξ - mtaFullSym P K ε ξ‖ₑ ^ (2:ℝ)
              * ‖((𝓕 (MemLp.toLp h hmem_2) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
            rw [hMΔ, Commons.Analysis.Fourier.BoundaryLayer.multiplier,
              Commons.Analysis.Fourier.BoundaryLayer.enorm_fourierInv,
              Commons.Analysis.Fourier.BoundaryLayer.enorm_mulLp]
        _ = (∫⁻ ξ : ℝ, ‖mtaBlkSymSum P K ε S ξ - mtaFullSym P K ε ξ‖ₑ ^ (2:ℝ)
              * ‖𝓕 h ξ‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
            refine congrArg (fun t : ℝ≥0∞ => t ^ ((1:ℝ)/2)) ?_
            refine lintegral_congr_ae ?_
            filter_upwards [Commons.Analysis.Fourier.fourier_toLp_ae_eq_fourier_of_memLp
              (memLp_one_iff_integrable.mpr hhint) hmem_2] with ξ hξ
            rw [hξ]
    have hDCT : Filter.Tendsto (fun S : ℕ => ∫⁻ ξ : ℝ,
        ‖mtaBlkSymSum P K ε S ξ - mtaFullSym P K ε ξ‖ₑ ^ (2:ℝ) * ‖𝓕 h ξ‖ₑ ^ (2:ℝ))
        Filter.atTop (𝓝 0) := by
      have hlim : ∀ᵐ ξ ∂volume, Filter.Tendsto (fun S : ℕ =>
          ‖mtaBlkSymSum P K ε S ξ - mtaFullSym P K ε ξ‖ₑ ^ (2:ℝ) * ‖𝓕 h ξ‖ₑ ^ (2:ℝ))
          Filter.atTop (𝓝 0) := by
        refine Filter.Eventually.of_forall (fun ξ => ?_)
        have h1 : Filter.Tendsto (fun S : ℕ => mtaBlkSymSum P K ε S ξ) Filter.atTop
            (𝓝 (mtaFullSym P K ε ξ)) := mtaBlkSymSum_tendsto P K ε ξ
        have h2 : Filter.Tendsto (fun S : ℕ => mtaBlkSymSum P K ε S ξ - mtaFullSym P K ε ξ)
            Filter.atTop (𝓝 0) := by
          have hc : Filter.Tendsto (fun _ : ℕ => mtaFullSym P K ε ξ) Filter.atTop
              (𝓝 (mtaFullSym P K ε ξ)) := tendsto_const_nhds
          have hh := h1.sub hc
          simpa using hh
        have h3 : Filter.Tendsto (fun S : ℕ =>
            ‖mtaBlkSymSum P K ε S ξ - mtaFullSym P K ε ξ‖ₑ) Filter.atTop (𝓝 0) := by
          simpa only [Function.comp_def, enorm_zero] using (continuous_enorm.tendsto (0 : ℂ)).comp h2
        have h4 : Filter.Tendsto (fun S : ℕ =>
            ‖mtaBlkSymSum P K ε S ξ - mtaFullSym P K ε ξ‖ₑ ^ (2:ℝ)) Filter.atTop (𝓝 0) := by
          have hcont : Filter.Tendsto (fun a : ℝ≥0∞ => a ^ (2:ℝ)) (𝓝 (0:ℝ≥0∞)) (𝓝 0) := by
            have hh := (ENNReal.continuous_rpow_const (y := (2:ℝ))).tendsto 0
            rwa [ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2)] at hh
          exact hcont.comp h3
        have hh := ENNReal.Tendsto.const_mul (a := ‖𝓕 h ξ‖ₑ ^ (2:ℝ)) h4
          (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
            (ne_of_lt (enorm_lt_top : ‖𝓕 h ξ‖ₑ < ⊤))))
        simpa [mul_comm] using hh
      have hbd : ∀ S : ℕ, (fun ξ : ℝ =>
            ‖mtaBlkSymSum P K ε S ξ - mtaFullSym P K ε ξ‖ₑ ^ (2:ℝ) * ‖𝓕 h ξ‖ₑ ^ (2:ℝ))
          ≤ᵐ[volume] (fun ξ : ℝ => ENNReal.ofReal ((Csym + Cμ) ^ 2) * ‖𝓕 h ξ‖ₑ ^ (2:ℝ)) := by
        intro S
        refine Filter.Eventually.of_forall (fun ξ => ?_)
        have hb : ‖mtaBlkSymSum P K ε S ξ - mtaFullSym P K ε ξ‖ₑ ≤ ENNReal.ofReal (Csym + Cμ) := by
          rw [← ofReal_norm]
          refine ENNReal.ofReal_le_ofReal ?_
          refine (norm_sub_le _ _).trans ?_
          have h1 := hCsymbd K ε hε S ξ
          have h2 := hFullbd ξ
          linarith
        calc ‖mtaBlkSymSum P K ε S ξ - mtaFullSym P K ε ξ‖ₑ ^ (2:ℝ) * ‖𝓕 h ξ‖ₑ ^ (2:ℝ)
            ≤ ENNReal.ofReal (Csym + Cμ) ^ (2:ℝ) * ‖𝓕 h ξ‖ₑ ^ (2:ℝ) :=
              mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow hb (by norm_num)) zero_le
          _ = ENNReal.ofReal ((Csym + Cμ) ^ 2) * ‖𝓕 h ξ‖ₑ ^ (2:ℝ) := by
              rw [ENNReal.ofReal_rpow_of_nonneg (by linarith [hCsympos, hCμpos]) (by norm_num : (0:ℝ) ≤ 2),
                show (Csym + Cμ) ^ (2:ℝ) = (Csym + Cμ) ^ 2 from Real.rpow_two _]
      have hfinb : ∫⁻ ξ : ℝ, ENNReal.ofReal ((Csym + Cμ) ^ 2) * ‖𝓕 h ξ‖ₑ ^ (2:ℝ) ∂volume ≠ ⊤ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
        have haeF : (fun ξ : ℝ => ‖𝓕 h ξ‖ₑ ^ (2:ℝ))
            =ᵐ[volume] (fun ξ : ℝ => ‖((𝓕 (MemLp.toLp h hmem_2) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖ₑ ^ (2:ℝ)) := by
          filter_upwards [Commons.Analysis.Fourier.fourier_toLp_ae_eq_fourier_of_memLp
            (memLp_one_iff_integrable.mpr hhint) hmem_2] with ξ hξ
          rw [hξ]
        rw [lintegral_congr_ae haeF,
          ← Commons.Analysis.Fourier.BoundaryLayer.lp_enorm_sq_eq_lintegral (𝓕 (MemLp.toLp h hmem_2)),
          Commons.Analysis.Fourier.BoundaryLayer.enorm_fourier]
        have hlt : ‖MemLp.toLp h hmem_2‖ₑ < ⊤ := by
          rw [Lp.enorm_def]
          exact (Lp.memLp (MemLp.toLp h hmem_2)).eLpNorm_lt_top
        exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ne_of_lt hlt)
      have hmeasF : ∀ S : ℕ, Measurable (fun ξ : ℝ =>
          ‖mtaBlkSymSum P K ε S ξ - mtaFullSym P K ε ξ‖ₑ ^ (2:ℝ) * ‖𝓕 h ξ‖ₑ ^ (2:ℝ)) := by
        intro S
        have h1 : Continuous (fun ξ : ℝ => mtaBlkSymSum P K ε S ξ - mtaFullSym P K ε ξ) :=
          (continuous_finsetSum (s := Finset.Icc (-(S:ℤ)) (S:ℤ))
            (fun s _ => continuous_mtaBlkSym P K ε s)).sub (continuous_mtaFullSym P K ε)
        have h2 : Continuous (fun ξ : ℝ => 𝓕 h ξ) :=
          Commons.Analysis.Fourier.continuous_fourier_of_integrable h hhint
        exact (((ENNReal.continuous_rpow_const (y := (2:ℝ))).comp
            (continuous_enorm.comp h1)).measurable.mul
          (((ENNReal.continuous_rpow_const (y := (2:ℝ))).comp (continuous_enorm.comp h2))).measurable)
      have hDCT' := tendsto_lintegral_of_dominated_convergence
        (fun ξ : ℝ => ENNReal.ofReal ((Csym + Cμ) ^ 2) * ‖𝓕 h ξ‖ₑ ^ (2:ℝ)) hmeasF hbd hfinb hlim
      simpa using hDCT'
    have hSlim : Filter.Tendsto (fun S : ℕ => eLpNorm
        (fun x : ℝ => (∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ), mtaBlkOp P K ε s h x)
          - dyadSum P K ε h x) 2 volume) Filter.atTop (𝓝 0) := by
      simp_rw [hEq]
      have hcont : Filter.Tendsto (fun a : ℝ≥0∞ => a ^ ((1:ℝ)/2)) (𝓝 (0:ℝ≥0∞)) (𝓝 0) := by
        have hh := (ENNReal.continuous_rpow_const (y := (1:ℝ)/2)).tendsto 0
        rwa [ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 1/2)] at hh
      exact hcont.comp hDCT
    -- (F) measurability of the objects involved
    have haesm_S : ∀ S : ℕ, AEStronglyMeasurable
        (fun x : ℝ => ∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ), mtaBlkOp P K ε s h x) volume := by
      intro S
      obtain ⟨hm, hae⟩ := mtaBlkOpSum_multiplier_ae P K ε S hhint hmem_2
      exact (Lp.aestronglyMeasurable (Commons.Analysis.Fourier.BoundaryLayer.multiplier
        (mtaBlkSymSum P K ε S) hm (MemLp.toLp h hmem_2))).congr hae.symm
    have haesm_dys : AEStronglyMeasurable (dyadSum P K ε h) volume := by
      obtain ⟨hm, hae⟩ := dyadSum_multiplier_ae P K ε hhint hmem_2
      exact (Lp.aestronglyMeasurable (Commons.Analysis.Fourier.BoundaryLayer.multiplier
        (mtaFullSym P K ε) hm (MemLp.toLp h hmem_2))).congr hae.symm
    have haesm_tr : ∀ S : ℕ, AEStronglyMeasurable
        (fun x : ℝ => ∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ), mtaBlkOp P K ε s (mtaTrunc S h) x) volume := by
      intro S
      obtain ⟨hm, hae⟩ := mtaBlkOpSum_multiplier_ae P K ε S (hint_trunc S) (hmem2_trunc S)
      exact (Lp.aestronglyMeasurable (Commons.Analysis.Fourier.BoundaryLayer.multiplier
        (mtaBlkSymSum P K ε S) hm (MemLp.toLp (mtaTrunc S h) (hmem2_trunc S)))).congr hae.symm
    -- (G) the diagonal converges to `dyadSum` in L²
    have hdiag : Filter.Tendsto (fun n : ℕ => eLpNorm
        (fun x : ℝ => (∑ s ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), mtaBlkOp P K ε s (mtaTrunc n h) x)
          - dyadSum P K ε h x) 2 volume) Filter.atTop (𝓝 0) := by
      have hsumlim : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (C₂ * Ageo2)
            * eLpNorm (fun x : ℝ => mtaTrunc n h x - h x) 2 volume
          + eLpNorm (fun x : ℝ => (∑ s ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), mtaBlkOp P K ε s h x)
              - dyadSum P K ε h x) 2 volume) Filter.atTop (𝓝 0) := by
        have h1 : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (C₂ * Ageo2)
            * eLpNorm (fun x : ℝ => mtaTrunc n h x - h x) 2 volume) Filter.atTop (𝓝 0) := by
          have hh := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (C₂ * Ageo2)) hΔ
            (Or.inr ENNReal.ofReal_ne_top)
          simpa using hh
        have h2 : Filter.Tendsto (fun n : ℕ => eLpNorm (fun x : ℝ =>
            (∑ s ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), mtaBlkOp P K ε s h x) - dyadSum P K ε h x)
            2 volume) Filter.atTop (𝓝 0) := hSlim
        simpa using h1.add h2
      have hbd : ∀ n : ℕ, eLpNorm
          (fun x : ℝ => (∑ s ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), mtaBlkOp P K ε s (mtaTrunc n h) x)
            - dyadSum P K ε h x) 2 volume
          ≤ ENNReal.ofReal (C₂ * Ageo2) * eLpNorm (fun x : ℝ => mtaTrunc n h x - h x) 2 volume
            + eLpNorm (fun x : ℝ => (∑ s ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), mtaBlkOp P K ε s h x)
              - dyadSum P K ε h x) 2 volume := by
        intro n
        have hsplit : (fun x : ℝ => (∑ s ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), mtaBlkOp P K ε s (mtaTrunc n h) x)
              - dyadSum P K ε h x)
            = (fun x : ℝ => (∑ s ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), mtaBlkOp P K ε s (mtaTrunc n h) x)
                - (∑ s ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), mtaBlkOp P K ε s h x))
              + (fun x : ℝ => (∑ s ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), mtaBlkOp P K ε s h x)
                - dyadSum P K ε h x) := by
          funext x; simp only [Pi.add_apply]; ring
        rw [hsplit]
        have h1 : AEStronglyMeasurable (fun x : ℝ =>
            (∑ s ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), mtaBlkOp P K ε s (mtaTrunc n h) x)
              - (∑ s ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), mtaBlkOp P K ε s h x)) volume :=
          (haesm_tr n).sub (haesm_S n)
        have h2 : AEStronglyMeasurable (fun x : ℝ =>
            (∑ s ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), mtaBlkOp P K ε s h x)
              - dyadSum P K ε h x) volume := (haesm_S n).sub haesm_dys
        calc eLpNorm ((fun x : ℝ =>
              (∑ s ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), mtaBlkOp P K ε s (mtaTrunc n h) x)
                - (∑ s ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), mtaBlkOp P K ε s h x))
            + (fun x : ℝ => (∑ s ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), mtaBlkOp P K ε s h x)
                - dyadSum P K ε h x)) 2 volume
            ≤ eLpNorm (fun x : ℝ =>
                (∑ s ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), mtaBlkOp P K ε s (mtaTrunc n h) x)
                  - (∑ s ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), mtaBlkOp P K ε s h x)) 2 volume
              + eLpNorm (fun x : ℝ =>
                (∑ s ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), mtaBlkOp P K ε s h x)
                  - dyadSum P K ε h x) 2 volume := eLpNorm_add_le (by norm_num)
          _ ≤ ENNReal.ofReal (C₂ * Ageo2) * eLpNorm (fun x : ℝ => mtaTrunc n h x - h x) 2 volume
              + eLpNorm (fun x : ℝ => (∑ s ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), mtaBlkOp P K ε s h x)
                - dyadSum P K ε h x) 2 volume :=
              add_le_add (hdiff n n) (le_refl _)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsumlim
        (Filter.Eventually.of_forall (fun n => bot_le)) (Filter.Eventually.of_forall hbd)
    -- (H) an a.e. convergent subsequence, and Fatou
    set V : ℕ → ℝ → ℂ := fun n x => ∑ s ∈ Finset.Icc (-(n:ℤ)) (n:ℤ),
      mtaBlkOp P K ε s (mtaTrunc n h) x with hV
    have hsmV : ∀ n : ℕ, AEStronglyMeasurable (V n) volume := by
      intro n
      simp only [hV]
      exact haesm_tr n
    have hbddV : ∀ n : ℕ, eLpNorm (V n) (ENNReal.ofReal p) volume
        ≤ ENNReal.ofReal Ageo * eLpNorm h (ENNReal.ofReal p) volume := by
      intro n
      simp only [hV]
      exact (hfac n n).trans
        (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hgeo n)) zero_le)
    have hdiagV : Filter.Tendsto (fun n : ℕ => eLpNorm (V n - dyadSum P K ε h) 2 volume)
        Filter.atTop (𝓝 0) := by
      simp only [hV]
      exact hdiag
    have hfinal : eLpNorm (dyadSum P K ε h) (ENNReal.ofReal p) volume
        ≤ ENNReal.ofReal Ageo * eLpNorm h (ENNReal.ofReal p) volume :=
      mta_lintegral_le_of_diag (V := V) (dys := dyadSum P K ε h) (p := p) hp0
        (ENNReal.ofReal Ageo * eLpNorm h (ENNReal.ofReal p) volume) hsmV haesm_dys hdiagV hbddV
    calc ∫⁻ x : ℝ, ‖dyadSum P K ε h x‖ₑ ^ p ∂volume
        = (eLpNorm (dyadSum P K ε h) (ENNReal.ofReal p) volume) ^ p := by
          rw [lintegral_rpow_eq_eLpNorm_rpow hp0 (fun x => ‖dyadSum P K ε h x‖ₑ) haesm_dys.enorm,
            eLpNorm_enorm _ haesm_dys]
      _ ≤ (ENNReal.ofReal Ageo * eLpNorm h (ENNReal.ofReal p) volume) ^ p :=
          ENNReal.rpow_le_rpow hfinal hp0.le
      _ = ENNReal.ofReal (Ageo ^ p) * ∫⁻ x : ℝ, ‖h x‖ₑ ^ p ∂volume := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ENNReal.ofReal_rpow_of_nonneg hAgeopos.le hp0.le,
            lintegral_rpow_eq_eLpNorm_rpow hp0 (fun x => ‖h x‖ₑ) hhint.aestronglyMeasurable.enorm,
            eLpNorm_enorm _ hhint.aestronglyMeasurable]

/-- The target statement, deduced from `mta_core` and `dyadic_reduction`. -/
theorem mst_theta_real_assembly (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) (hlc : 0 < P.leadingCoeff) (r : ℕ) (hr : 2 ≤ r) : ∃ A : ℝ, 0 < A ∧ ∀ (i M : ℕ) (ε : ℕ → ℂ), (∀ j : ℕ, ‖ε j‖ ≤ 1) → ∀ (h : ℝ → ℂ), MeasureTheory.Integrable h → ∫⁻ x : ℝ, ‖∑ j ∈ Finset.range M, ε j * ((∫ t in (0:ℝ)..1, h (x - (Work.BourgainPlan.Maximal.toRealPoly P).eval (((2:ℝ) ^ (j * 2 ^ i)) * t))) - (∫ t in (0:ℝ)..1, h (x - (Work.BourgainPlan.Maximal.toRealPoly P).eval (((2:ℝ) ^ ((j+1) * 2 ^ i)) * t))))‖ₑ ^ (2 * (r : ℝ)) ∂MeasureTheory.volume ≤ ENNReal.ofReal (A ^ (2 * (r : ℝ))) * ∫⁻ x : ℝ, ‖h x‖ₑ ^ (2 * (r : ℝ)) ∂MeasureTheory.volume := by
  have hp4 : 4 ≤ 2 * (r : ℝ) := by
    have h1 : (2:ℝ) * 2 ≤ 2 * (r : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hr) (by norm_num)
    linarith
  obtain ⟨A, hApos, hcore⟩ := mta_core P hdeg hlc (2 * (r : ℝ)) hp4
  refine ⟨A, hApos, ?_⟩
  intro i M ε hε h hhint
  have hmain := hcore (M * 2 ^ i) (fun k => ε (k / 2 ^ i)) (fun k => hε (k / 2 ^ i)) h hhint
  have key : (fun x : ℝ => ‖∑ j ∈ Finset.range M, ε j *
        ((∫ t in (0:ℝ)..1, h (x - (toRealPoly P).eval (((2:ℝ) ^ (j * 2 ^ i)) * t)))
          - (∫ t in (0:ℝ)..1, h (x - (toRealPoly P).eval (((2:ℝ) ^ ((j+1) * 2 ^ i)) * t))))‖ₑ
        ^ (2 * (r : ℝ)))
      = fun x : ℝ => ‖dyadSum P (M * 2 ^ i) (fun k => ε (k / 2 ^ i)) h x‖ₑ ^ (2 * (r : ℝ)) := by
    funext x
    rw [show (∑ j ∈ Finset.range M, ε j *
        ((∫ t in (0:ℝ)..1, h (x - (toRealPoly P).eval (((2:ℝ) ^ (j * 2 ^ i)) * t)))
          - (∫ t in (0:ℝ)..1, h (x - (toRealPoly P).eval (((2:ℝ) ^ ((j+1) * 2 ^ i)) * t)))))
        = mstThetaOp P i M ε h x from rfl]
    rw [← congrFun (dyadic_reduction P i M ε) h]
  rw [key]
  exact hmain

end
end Work.BourgainPlan.Maximal
