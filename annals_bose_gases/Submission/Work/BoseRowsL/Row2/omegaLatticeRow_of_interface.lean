import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Submission.Work.BoseBoxFock.AliasAux
import Submission.Work.BoseBoxFock.combHeat
import Submission.Work.BoseRowsFS.omega_lattice_honest_decay
import Submission.Work.BoseRowsL.Bookkeeping.integrable_crossInt
import Submission.Work.BoseRowsL.Bookkeeping.sum_lab_eq_latBall
import Submission.Work.BoseRowsL.Regime.fourR_le_ell
import Submission.Work.BoseRowsL.Row2.chat_conv
import Submission.Work.BoseRowsL.Row2.heatA_integrable
import Submission.Work.BoseRowsL.Row2.heatB_integrable
import Submission.Work.BoseRowsL.Row2.largeT_bound
import Submission.Work.BoseRowsL.Row2.smallT_bound
import Submission.Work.BoseRowsL.Tails.lattice_energy_summable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsL.Row2

open MeasureTheory Metric
open scoped Real BigOperators Topology

/-!
# Row 2 (`omega_lattice`) from the decay-free interface `HonestInterfaceL`

Route (see `FINDING_BoseRowsL.md` and the `Work.BoseRowsL.Defs` docstring):

* `W1omega0 = (2π)⁻³∫ Ŵ₁ĝ/(2p²)` is the exact mass identity
  (`Work.BoseRowsFS.honE_W1omega0_eq_integral`);
* the *lattice* sum is compared with that integral through the **torus/free
  Green-function comparison**: with `h = W₁ ∗ g₀` (so that `ĥ = Ŵ₁·ĝ`), both
  `(2π)⁻³∫ĥ(p)/(2p²)dp` and `ℓ⁻³Σ_{n≠0}ĥ(k_n)/(2k_n²)` are the free / periodic
  Green-function bilinear forms of `h`, and their difference is `O(‖h‖₁/ℓ)`;
* the `uvCut` truncation of the box sum is a lattice tail beyond `uvRad`, which is
  the interface field `tailL`.
-/

noncomputable section

/-- The box momenta `k_n = ℓ⁻¹ • vec n = (2π/ℓ)·n`. -/
noncomputable def kvec (ℓ : ℝ) (n : Fin 3 → ℤ) : ℝ³ := Work.BoseBoxFock.kmomInt ℓ n

/-- The torus (lattice) side of the comparison, heat-evolved. -/
noncomputable def hA (ℓ : ℝ) (h : ℝ³ → ℝ) (t : ℝ) : ℝ :=
  (ℓ ^ 3)⁻¹ * ((∑' n : Fin 3 → ℤ,
      Work.BoseFixR.chat h (kvec ℓ n) * Real.exp (-(t * ‖kvec ℓ n‖ ^ 2)))
    - Work.BoseFixR.chat h 0)

/-- The free (continuum) side of the comparison, heat-evolved. -/
noncomputable def hB (h : ℝ³ → ℝ) (t : ℝ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, Work.BoseFixR.chat h p * Real.exp (-(t * ‖p‖ ^ 2))

/-- The image (Poisson) form of the torus side. -/
noncomputable def hM (ℓ : ℝ) (h : ℝ³ → ℝ) (t : ℝ) : ℝ :=
  (∑' m : Fin 3 → ℤ,
      ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - x))
    - (ℓ ^ 3)⁻¹ * ∫ x : ℝ³, h x

end

/-- The real part of `a·e^{−ix}` is `a cos x`. -/
lemma re_ofReal_mul_cexp_neg_I (a x : ℝ) :
    ((a : ℂ) * Complex.exp (-(Complex.I * (x : ℂ)))).re = a * Real.cos x := by
  have h : (-(Complex.I * (x : ℂ))) = ((-x : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, Real.cos_neg, add_zero]
  ring

/-- **The Poisson (theta) identity in real form**: the lattice sum of the heat-evolved box modes
equals the image sum of the heat kernel.  Derived from `Work.BoseBoxFock.combHeat` by taking the
real part (the sine companion vanishes by symmetry). -/
theorem combHeat_re {ℓ : ℝ} (hℓ : 0 < ℓ) {t : ℝ} (ht : 0 < t) (u : ℝ³) :
    (ℓ ^ 3)⁻¹ * Work.BoseBoxFock.thetaSum ℓ t u
      = ∑' m : Fin 3 → ℤ, Work.BoseBoxFock.heatK t (u - ℓ • Work.BoseBoxFock.latVec m) := by
  have hsumL : Summable (fun n : Fin 3 → ℤ =>
      ((ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2)) : ℂ)
        * Complex.exp (-(Complex.I * (inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) u : ℂ)))) := by
    refine Summable.of_norm_bounded (Work.BoseBoxFock.summable_weight hℓ ht) (fun n => ?_)
    have h1 : ‖(↑(ℓ ^ 3)⁻¹ * ↑(Real.exp (-(t * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2))) : ℂ)‖
        = (ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2)) := by
      rw [norm_mul]
      rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self (by positivity)]
      rw [Complex.norm_def, Complex.normSq_ofReal,
        Real.sqrt_mul_self (le_of_lt (Real.exp_pos _))]
    have hz : (-(Complex.I * (inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) u : ℂ))).re = 0 := by
      rw [show (-(Complex.I * (inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) u : ℂ)))
            = ((-(inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) u) : ℝ) : ℂ) * Complex.I by
          push_cast; ring]
      simp
    rw [norm_mul, h1, Complex.norm_exp, hz, Real.exp_zero, mul_one]
  have h := congrArg Complex.re (Work.BoseBoxFock.combHeat (ℓ := ℓ) hℓ ht u)
  rw [Complex.re_tsum hsumL, ← Complex.ofReal_tsum] at h
  simp only [Complex.ofReal_re] at h
  rw [← h, Work.BoseBoxFock.thetaSum, ← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  rw [← Complex.ofReal_mul,
    re_ofReal_mul_cexp_neg_I ((ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2)))
      (inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) u)]
  ring

/-! ## 3. The Poisson (image) form of the torus side -/

/-- Summability of the Gaussian family `n ↦ e^{−t‖k_n‖²}`. -/
lemma summable_exp_neg_kvec {ℓ t : ℝ} (hℓ : 0 < ℓ) (ht : 0 < t) :
    Summable (fun n : Fin 3 → ℤ => Real.exp (-(t * ‖kvec ℓ n‖ ^ 2))) := by
  refine (Work.BoseBoxFock.summable_weight (ℓ := ℓ) hℓ ht).mul_left (ℓ ^ 3) |>.congr (fun n => ?_)
  simp only [kvec, Work.BoseBoxFock.kmomInt]
  rw [← mul_assoc, mul_inv_cancel₀ (by positivity : (ℓ ^ 3 : ℝ) ≠ 0), one_mul]

/-- For `m ≠ 0` and `x ∈ tsupport h ⊆ closedBall 0 (ℓ/2)`, `‖x − ℓm‖ ≥ ℓ‖m‖/2`. -/
lemma sq_norm_sub_latVec_ge {ℓ : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ}
    (hsupp : tsupport h ⊆ Metric.closedBall 0 (ℓ / 2)) {m : Fin 3 → ℤ}
    (hm : (1 : ℝ) ≤ ‖Work.BoseBoxFock.latVec m‖) {x : ℝ³} (hx : x ∈ tsupport h) :
    ‖x - ℓ • Work.BoseBoxFock.latVec m‖ ^ 2
      ≥ ℓ ^ 2 * ‖Work.BoseBoxFock.latVec m‖ ^ 2 / 4 := by
  have hx' : ‖x‖ ≤ ℓ / 2 := by
    have h := hsupp hx
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  have h1 : ‖ℓ • Work.BoseBoxFock.latVec m‖ = ℓ * ‖Work.BoseBoxFock.latVec m‖ := by
    rw [norm_smul, Real.norm_of_nonneg hℓ.le]
  have h2 : ℓ * ‖Work.BoseBoxFock.latVec m‖ / 2 ≤ ‖x - ℓ • Work.BoseBoxFock.latVec m‖ := by
    have h3 := abs_norm_sub_norm_le (ℓ • Work.BoseBoxFock.latVec m) x
    rw [norm_sub_rev, h1] at h3
    have h4 := (abs_le.mp h3).2
    have h5 : ‖x‖ ≤ ℓ * ‖Work.BoseBoxFock.latVec m‖ / 2 := by
      have : ℓ / 2 ≤ ℓ * ‖Work.BoseBoxFock.latVec m‖ / 2 := by nlinarith
      linarith
    linarith
  have h6 : (0 : ℝ) ≤ ℓ * ‖Work.BoseBoxFock.latVec m‖ / 2 := by positivity
  calc ‖x - ℓ • Work.BoseBoxFock.latVec m‖ ^ 2
      ≥ (ℓ * ‖Work.BoseBoxFock.latVec m‖ / 2) ^ 2 := pow_le_pow_left₀ h6 h2 2
    _ = ℓ ^ 2 * ‖Work.BoseBoxFock.latVec m‖ ^ 2 / 4 := by ring

/-- The heat kernel at the lattice displacement is dominated by the Gaussian of the lattice norm. -/
lemma heatK_flip_le {ℓ t : ℝ} (hℓ : 0 < ℓ) (ht : 0 < t) {h : ℝ³ → ℝ}
    (hsupp : tsupport h ⊆ Metric.closedBall 0 (ℓ / 2)) (m : Fin 3 → ℤ) {x : ℝ³}
    (hx : x ∈ tsupport h) :
    Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - x)
      ≤ (4 * Real.pi * t) ^ (-(3 : ℝ) / 2)
        * Real.exp (-(ℓ ^ 2 / (16 * t)) * ‖Work.BoseBoxFock.latVec m‖ ^ 2) := by
  have hz : Work.BoseBoxFock.latVec (0 : Fin 3 → ℤ) = 0 := by
    ext i
    simp [Work.BoseBoxFock.latVec]
  rcases eq_or_ne m 0 with hm | hm
  · subst hm
    have h0 : ℓ • Work.BoseBoxFock.latVec (0 : Fin 3 → ℤ) - x = -x := by
      rw [hz, smul_zero, zero_sub]
    have harg : (-(ℓ ^ 2 / (16 * t)) * ‖Work.BoseBoxFock.latVec (0 : Fin 3 → ℤ)‖ ^ 2) = 0 := by
      rw [hz, norm_zero]
      ring
    rw [h0, harg, Real.exp_zero, mul_one]
    exact Work.BoseBoxFock.heatK_bound ht (-x)
  · have hmn : (1 : ℝ) ≤ ‖Work.BoseBoxFock.latVec m‖ := by
      have h := Work.BoseRowsFS.LatRiemann.one_le_norm_zvec hm
      simpa only [Work.BoseRowsFS.zvec, Work.BoseBoxFock.latVec] using h
    have hfn : ℓ • Work.BoseBoxFock.latVec m - x
        = -(x - ℓ • Work.BoseBoxFock.latVec m) := by abel
    rw [hfn, Work.BoseBoxFock.heatK, norm_neg]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by positivity) _)
    rw [Real.exp_le_exp]
    have hR : -(ℓ ^ 2 / (16 * t)) * ‖Work.BoseBoxFock.latVec m‖ ^ 2
        = -(ℓ ^ 2 * ‖Work.BoseBoxFock.latVec m‖ ^ 2 / (16 * t)) := by ring
    rw [hR, neg_le_neg_iff]
    have hsq := sq_norm_sub_latVec_ge hℓ hsupp hmn hx
    have h2 : ℓ ^ 2 * ‖Work.BoseBoxFock.latVec m‖ ^ 2 / (16 * t)
        = (ℓ ^ 2 * ‖Work.BoseBoxFock.latVec m‖ ^ 2 / 4) / (4 * t) := by
      field_simp
      norm_num
    rw [h2]
    exact div_le_div_of_nonneg_right hsq (by positivity)

/-- The elementary arithmetic of the last step of `hA_eq`. -/
lemma hA_arith {ℓ M I : ℝ} (hℓ : ℓ ≠ 0) :
    (ℓ ^ 3)⁻¹ * (ℓ ^ 3 * M - I) = M - (ℓ ^ 3)⁻¹ * I := by
  field_simp

/-- **The image (Poisson) form of the torus side**: for `t > 0` the lattice sum of the
heat-evolved box modes is the image sum of the heat kernel against `h`. -/
theorem hA_eq {ℓ : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ} (hI : MeasureTheory.Integrable h)
    (hsupp : tsupport h ⊆ Metric.closedBall 0 (ℓ / 2)) {t : ℝ} (ht : 0 < t) :
    hA ℓ h t = (∑' m : Fin 3 → ℤ,
        ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - x))
      - (ℓ ^ 3)⁻¹ * ∫ x : ℝ³, h x := by
  have hℓ3 : (0 : ℝ) < ℓ ^ 3 := by positivity
  have hchat : ∀ n : Fin 3 → ℤ, Work.BoseFixR.chat h (kvec ℓ n)
      = ∫ x : ℝ³, h x * Real.cos (inner ℝ (kvec ℓ n) x) :=
    fun n => Work.BoseB7AK.W1low.chat_eq_integral_cos hI _
  have hIntn : ∀ n : Fin 3 → ℤ, MeasureTheory.Integrable (fun x : ℝ³ =>
      h x * (Real.cos (inner ℝ (kvec ℓ n) x) * Real.exp (-(t * ‖kvec ℓ n‖ ^ 2)))) := by
    intro n
    refine hI.mul_bdd ?_ (c := Real.exp (-(t * ‖kvec ℓ n‖ ^ 2)))
      (Filter.Eventually.of_forall ?_)
    · exact (((Real.continuous_cos.comp (continuous_const.inner continuous_id)).aestronglyMeasurable).mul
        aestronglyMeasurable_const)
    · intro x
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_left (Real.exp_pos _).le (Real.abs_cos_le_one _)
  have hSummn : Summable (fun n : Fin 3 → ℤ => ∫ x : ℝ³, ‖h x *
      (Real.cos (inner ℝ (kvec ℓ n) x) * Real.exp (-(t * ‖kvec ℓ n‖ ^ 2)))‖) := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg (fun x => norm_nonneg _))
      (fun n => ?_) ((summable_exp_neg_kvec hℓ ht).mul_left (∫ x : ℝ³, |h x|))
    rw [← MeasureTheory.integral_mul_const]
    refine MeasureTheory.integral_mono (hIntn n).norm (hI.abs.mul_const _) (fun x => ?_)
    have hexp : (0 : ℝ) < Real.exp (-(t * ‖kvec ℓ n‖ ^ 2)) := Real.exp_pos _
    have hb : |Real.cos (inner ℝ (kvec ℓ n) x)| ≤ 1 := Real.abs_cos_le_one _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hexp]
    calc |h x| * (|Real.cos (inner ℝ (kvec ℓ n) x)| * Real.exp (-(t * ‖kvec ℓ n‖ ^ 2)))
        ≤ |h x| * (1 * Real.exp (-(t * ‖kvec ℓ n‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb hexp.le) (abs_nonneg _)
      _ = |h x| * Real.exp (-(t * ‖kvec ℓ n‖ ^ 2)) := by ring
  have hIntm : ∀ m : Fin 3 → ℤ, MeasureTheory.Integrable (fun x : ℝ³ =>
      h x * Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - x)) := by
    intro m
    refine hI.mul_bdd ?_ (c := (4 * Real.pi * t) ^ (-(3 : ℝ) / 2))
      (Filter.Eventually.of_forall ?_)
    · exact ((Work.BoseBoxFock.heatK_continuous ht).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable
    · intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (Work.BoseBoxFock.heatK_nonneg ht.le _)]
      exact Work.BoseBoxFock.heatK_bound ht _
  have hSummm : Summable (fun m : Fin 3 → ℤ => ∫ x : ℝ³,
      ‖h x * Work.BoseBoxFock.heatK t (ℓ • Work.BoseBoxFock.latVec m - x)‖) := by
    have hgs : Summable (fun m : Fin 3 → ℤ =>
        Real.exp (-(ℓ ^ 2 / (16 * t)) * ‖Work.BoseBoxFock.latVec m‖ ^ 2)) := by
      have h := Work.BoseFixR.LatGreen.latticeGaussSummable (0 : ℝ³)
        (c := ℓ ^ 2 / (16 * t)) (by positivity)
      refine h.congr (fun m => ?_)
      rw [Work.BoseFixR.LatGreen.latVec, Work.BoseBoxFock.latVec, zero_sub, norm_neg]
    refine Summable.of_nonneg_of_le (fun m => integral_nonneg (fun x => norm_nonneg _))
      (fun m => ?_)
      ((hgs.mul_left ((4 * Real.pi * t) ^ (-(3 : ℝ) / 2))).mul_left (∫ x : ℝ³, |h x|))
    rw [← MeasureTheory.integral_mul_const]
    refine MeasureTheory.integral_mono (hIntm m).norm (hI.abs.mul_const _) (fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Work.BoseBoxFock.heatK_nonneg ht.le _)]
    by_cases hx : x ∈ tsupport h
    · exact mul_le_mul_of_nonneg_left (heatK_flip_le hℓ ht hsupp m hx) (abs_nonneg _)
    · have h0 : h x = 0 := by
        by_contra hne
        exact hx (subset_tsupport h (Function.mem_support.mpr hne))
      rw [h0, abs_zero, zero_mul, zero_mul]
  have hstep : (∑' n : Fin 3 → ℤ,
        Work.BoseFixR.chat h (kvec ℓ n) * Real.exp (-(t * ‖kvec ℓ n‖ ^ 2)))
      = ℓ ^ 3 * (∑' m : Fin 3 → ℤ, ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t
          (ℓ • Work.BoseBoxFock.latVec m - x)) := by
    have h1 : (∑' n : Fin 3 → ℤ,
          Work.BoseFixR.chat h (kvec ℓ n) * Real.exp (-(t * ‖kvec ℓ n‖ ^ 2)))
        = ∑' n : Fin 3 → ℤ, ∫ x : ℝ³,
            h x * (Real.cos (inner ℝ (kvec ℓ n) x) * Real.exp (-(t * ‖kvec ℓ n‖ ^ 2))) := by
      refine tsum_congr (fun n => ?_)
      rw [hchat n, ← MeasureTheory.integral_mul_const]
      exact MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall (fun x => by ring))
    rw [h1, MeasureTheory.integral_tsum_of_summable_integral_norm hIntn hSummn]
    have h2 : ∀ x : ℝ³, (∑' n : Fin 3 → ℤ,
          h x * (Real.cos (inner ℝ (kvec ℓ n) x) * Real.exp (-(t * ‖kvec ℓ n‖ ^ 2))))
        = h x * Work.BoseBoxFock.thetaSum ℓ t x := by
      intro x
      rw [tsum_mul_left, Work.BoseBoxFock.thetaSum]
      congr 1
      refine tsum_congr (fun n => ?_)
      simp only [kvec]
      ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h2)]
    have h3 : ∀ x : ℝ³, Work.BoseBoxFock.thetaSum ℓ t x
        = ℓ ^ 3 * (∑' m : Fin 3 → ℤ,
            Work.BoseBoxFock.heatK t (x - ℓ • Work.BoseBoxFock.latVec m)) := by
      intro x
      calc Work.BoseBoxFock.thetaSum ℓ t x
          = ℓ ^ 3 * ((ℓ ^ 3)⁻¹ * Work.BoseBoxFock.thetaSum ℓ t x) := by field_simp
        _ = ℓ ^ 3 * (∑' m : Fin 3 → ℤ,
              Work.BoseBoxFock.heatK t (x - ℓ • Work.BoseBoxFock.latVec m)) := by
            rw [combHeat_re hℓ ht x]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by rw [h3 x]))]
    rw [show (fun x : ℝ³ => h x * (ℓ ^ 3 * (∑' m : Fin 3 → ℤ,
            Work.BoseBoxFock.heatK t (x - ℓ • Work.BoseBoxFock.latVec m))))
        = (fun x : ℝ³ => ℓ ^ 3 * (h x * (∑' m : Fin 3 → ℤ,
            Work.BoseBoxFock.heatK t (x - ℓ • Work.BoseBoxFock.latVec m)))) from
      funext (fun x => by ring)]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
      (fun x => (tsum_mul_left (a := h x) (f := fun m : Fin 3 → ℤ =>
        Work.BoseBoxFock.heatK t (x - ℓ • Work.BoseBoxFock.latVec m))).symm))]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x =>
      tsum_congr (fun m => by
        rw [show x - ℓ • Work.BoseBoxFock.latVec m
              = -(ℓ • Work.BoseBoxFock.latVec m - x) by abel,
          Work.BoseBoxFock.heatK_even])))]
    exact (MeasureTheory.integral_tsum_of_summable_integral_norm hIntm hSummm).symm
  rw [hA, hstep, Work.BoseB7AK.W1rows.chat_zero, hA_arith (ne_of_gt hℓ)]

/-! ## 4. The free (continuum) side -/

/-- The free heat kernel: the inverse Fourier transform of the Gaussian. -/
lemma heatK_free {t : ℝ} (ht : 0 < t) (x : ℝ³) :
    ∫ p : ℝ³, Real.exp (-(t * ‖p‖ ^ 2)) * Real.cos (inner ℝ p x)
      = (2 * Real.pi) ^ 3 * Work.BoseBoxFock.heatK t x := by
  have hf : MeasureTheory.Integrable (fun p : ℝ³ =>
      ((Real.exp (-(t * ‖p‖ ^ 2)) : ℝ) : ℂ)
        * Complex.exp (-(Complex.I * (inner ℝ p x : ℂ)))) := by
    refine MeasureTheory.Integrable.mono'
      (Work.BoseBoxFock.integrable_exp_neg_mul_norm_sq t ht) ?_ ?_
    · have hcont : Continuous (fun p : ℝ³ =>
          ((Real.exp (-(t * ‖p‖ ^ 2)) : ℝ) : ℂ)
            * Complex.exp (-(Complex.I * (inner ℝ p x : ℂ)))) := by fun_prop
      exact hcont.aestronglyMeasurable
    · filter_upwards with p
      have h1 : ‖(↑(Real.exp (-(t * ‖p‖ ^ 2)) : ℝ) : ℂ)‖ = Real.exp (-(t * ‖p‖ ^ 2)) := by
        rw [Complex.norm_def, Complex.normSq_ofReal,
          Real.sqrt_mul_self (le_of_lt (Real.exp_pos _))]
      have h2 : ‖Complex.exp (-(Complex.I * (inner ℝ p x : ℂ)))‖ = 1 := by
        rw [Complex.norm_exp]
        have hz : (-(Complex.I * (inner ℝ p x : ℂ))).re = 0 := by
          rw [show (-(Complex.I * (inner ℝ p x : ℂ)))
              = ((-(inner ℝ p x) : ℝ) : ℂ) * Complex.I by push_cast; ring]
          rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
          ring
        rw [hz, Real.exp_zero]
      rw [norm_mul, h1, h2, mul_one]
  have h1 := ContinuousLinearMap.integral_comp_comm Complex.reCLM hf
  rw [Work.BoseBoxFock.heatK_fourier ht x] at h1
  simp only [Complex.reCLM_apply, Complex.ofReal_re] at h1
  rw [← h1]
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall (fun p =>
      (re_ofReal_mul_cexp_neg_I (Real.exp (-(t * ‖p‖ ^ 2))) (inner ℝ p x)).symm))

/-- The free side in heat form. -/
theorem hB_eq {h : ℝ³ → ℝ} (hI : MeasureTheory.Integrable h) {t : ℝ} (ht : 0 < t) :
    hB h t = ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t x := by
  have hchat : ∀ p : ℝ³, Work.BoseFixR.chat h p
      = ∫ x : ℝ³, h x * Real.cos (inner ℝ p x) :=
    fun p => Work.BoseB7AK.W1low.chat_eq_integral_cos hI _
  have hmaj : MeasureTheory.Integrable (fun z : ℝ³ × ℝ³ =>
      Real.exp (-(t * ‖z.1‖ ^ 2)) * |h z.2|)
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    (Work.BoseBoxFock.integrable_exp_neg_mul_norm_sq t ht).mul_prod hI.abs
  have hjoint : MeasureTheory.Integrable (fun z : ℝ³ × ℝ³ =>
      h z.2 * Real.cos (inner ℝ z.1 z.2) * Real.exp (-(t * ‖z.1‖ ^ 2)))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
    · have hcos : AEStronglyMeasurable (fun z : ℝ³ × ℝ³ => Real.cos (inner ℝ z.1 z.2))
          (MeasureTheory.volume.prod MeasureTheory.volume) := by fun_prop
      have hexp : AEStronglyMeasurable (fun z : ℝ³ × ℝ³ => Real.exp (-(t * ‖z.1‖ ^ 2)))
          (MeasureTheory.volume.prod MeasureTheory.volume) := by fun_prop
      exact ((hI.aestronglyMeasurable.comp_snd).mul hcos).mul hexp
    · filter_upwards with z
      have hc := Real.abs_cos_le_one (inner ℝ z.1 z.2)
      have he : (0 : ℝ) < Real.exp (-(t * ‖z.1‖ ^ 2)) := Real.exp_pos _
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos he]
      calc |h z.2| * |Real.cos (inner ℝ z.1 z.2)| * Real.exp (-(t * ‖z.1‖ ^ 2))
          ≤ |h z.2| * 1 * Real.exp (-(t * ‖z.1‖ ^ 2)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hc (abs_nonneg _)) he.le
        _ = Real.exp (-(t * ‖z.1‖ ^ 2)) * |h z.2| := by ring
  rw [hB]
  have hstep1 : (∫ p : ℝ³, Work.BoseFixR.chat h p * Real.exp (-(t * ‖p‖ ^ 2)))
      = ∫ p : ℝ³, (∫ x : ℝ³, h x * Real.cos (inner ℝ p x))
          * Real.exp (-(t * ‖p‖ ^ 2)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    simp only [hchat p]
  rw [hstep1]
  have hstep2 : (∫ p : ℝ³, (∫ x : ℝ³, h x * Real.cos (inner ℝ p x))
        * Real.exp (-(t * ‖p‖ ^ 2)))
      = ∫ p : ℝ³, ∫ x : ℝ³, h x * Real.cos (inner ℝ p x) * Real.exp (-(t * ‖p‖ ^ 2)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    show (∫ x : ℝ³, h x * Real.cos (inner ℝ p x)) * Real.exp (-(t * ‖p‖ ^ 2))
        = ∫ x : ℝ³, (h x * Real.cos (inner ℝ p x)) * Real.exp (-(t * ‖p‖ ^ 2))
    rw [MeasureTheory.integral_mul_const]
  rw [hstep2,
    MeasureTheory.integral_integral_swap (f := fun p x => h x * Real.cos (inner ℝ p x)
      * Real.exp (-(t * ‖p‖ ^ 2))) hjoint]
  have hstep3 : (∫ x : ℝ³, ∫ p : ℝ³, h x * Real.cos (inner ℝ p x)
        * Real.exp (-(t * ‖p‖ ^ 2)))
      = (2 * Real.pi) ^ 3 * ∫ x : ℝ³, h x * Work.BoseBoxFock.heatK t x := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    show (∫ p : ℝ³, h x * Real.cos (inner ℝ p x) * Real.exp (-(t * ‖p‖ ^ 2)))
        = (2 * Real.pi) ^ 3 * (h x * Work.BoseBoxFock.heatK t x)
    rw [show (∫ p : ℝ³, h x * Real.cos (inner ℝ p x) * Real.exp (-(t * ‖p‖ ^ 2)))
          = ∫ p : ℝ³, (h x * (Real.exp (-(t * ‖p‖ ^ 2)) * Real.cos (inner ℝ p x))) from
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => by ring)),
      MeasureTheory.integral_const_mul, heatK_free ht x]
    ring
  rw [hstep3]
  field_simp

/-! ## 5. The box sum as a full lattice sum -/

/-- **The box sum over the excited modes is the full lattice sum of the cut kernel.**

The filter `‖kmomLab‖ ≤ 2·uvRad` loses nothing (`uvCut` vanishes beyond `2·uvRad`), and the
lattice points of the ball are exactly the labels of the cube `Lab N` (`sum_lab_eq_latBall`). -/
lemma cube_sum_eq_tsum {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {fc fu : Work.BoseBoxFix.LowCut}
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ) (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v)
    (hΛpos : 0 < Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N) :
    ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        (Work.BoseRowsFS.honE v h fc fu HM μ).W1 k
          * Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
              ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k)
          / (2 * ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ ^ 2)
      = ∑' n : Fin 3 → ℤ,
          Work.BoseBoxFock.uvCut fu
              (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N)
              (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n)
            * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
                (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n)
            * Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
                (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n)
          / (2 * ‖Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n‖ ^ 2) := by
  classical
  have hℓpos : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  -- the summand as a function of the momentum
  set G : ℝ³ → ℝ := fun q =>
      Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N) q
        * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) q
        * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) q / (2 * ‖q‖ ^ 2) with hGdef
  have hbox : (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        (Work.BoseRowsFS.honE v h fc fu HM μ).W1 k
          * Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
              ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k)
          / (2 * ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ ^ 2))
      = ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
          G (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N k) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Work.BoseRowsFS.honE_W1_apply v h fc fu HM μ hμ hav k,
      Work.BoseRowsFS.honF_kmom v h fc fu HM μ]
  rw [hbox]
  -- the terms outside the cut vanish
  have hcut : (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        G (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N k))
      = ∑ k ∈ (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
          (fun k => ‖Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N k‖
            ≤ 2 * Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N),
        G (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N k) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro k hk hknot
    have hgt : 2 * Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N
        < ‖Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N k‖ := by
      by_contra hcon
      exact hknot (Finset.mem_filter.mpr ⟨hk, not_lt.mp hcon⟩)
    have hz : Work.BoseBoxFock.uvCut fu
        (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N)
        (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N k) = 0 := by
      rw [Work.BoseBoxFock.uvCut]
      refine fu.zero _ ?_
      rw [le_div_iff₀ hΛpos]
      linarith
    rw [hGdef]
    simp only [hz, zero_mul, zero_div]
  rw [hcut]
  -- the lattice reindexing
  have hK : 2 * Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N
      ≤ 2 * Real.pi * ((HM μ).N : ℝ) / Work.BoseBoxFock.ellH v μ := by
    have hN : (0 : ℝ) ≤ ((HM μ).N : ℝ) := Nat.cast_nonneg _
    have hrw : 2 * Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N
        = Real.pi * ((HM μ).N : ℝ) / Work.BoseBoxFock.ellH v μ := by
      rw [Work.BoseBoxFock.uvRad]
      ring
    rw [hrw]
    have h0 : 0 ≤ Real.pi * ((HM μ).N : ℝ) / Work.BoseBoxFock.ellH v μ :=
      div_nonneg (mul_nonneg Real.pi_pos.le hN) hℓpos.le
    calc Real.pi * ((HM μ).N : ℝ) / Work.BoseBoxFock.ellH v μ
        = 1 * (Real.pi * ((HM μ).N : ℝ) / Work.BoseBoxFock.ellH v μ) := by ring
      _ ≤ 2 * (Real.pi * ((HM μ).N : ℝ) / Work.BoseBoxFock.ellH v μ) := by linarith
      _ = 2 * Real.pi * ((HM μ).N : ℝ) / Work.BoseBoxFock.ellH v μ := by ring
  obtain ⟨S, hS₁, hS₂, hSsum⟩ := Work.BoseRowsL.Bookkeeping.sum_lab_eq_latBall
    (v := v) (h := h) (fc := fc) (fu := fu)
    (Work.BoseBoxFock.ellH v μ) (HM μ).N
    (2 * Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N) G hℓpos hK
  rw [hSsum]
  -- the sum over `S` is the full lattice sum: the summand vanishes outside `S`
  refine (tsum_eq_sum (s := S) ?_).symm
  intro n hnS
  have hk0 : (Work.BoseBoxFock.ellH v μ)⁻¹ • Work.BoseB4.vec (0 : Fin 3 → ℤ) = 0 := by
    ext i
    simp [Work.BoseB4.vec]
  by_cases hn0 : n = 0
  · rw [hn0, hk0, hGdef]
    simp
  · have hgt : 2 * Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N
        < ‖(Work.BoseBoxFock.ellH v μ)⁻¹ • Work.BoseB4.vec n‖ := by
      by_contra hcon
      exact hnS (hS₂ n hn0 (not_lt.mp hcon))
    have hz : Work.BoseBoxFock.uvCut fu
        (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N)
        ((Work.BoseBoxFock.ellH v μ)⁻¹ • Work.BoseB4.vec n) = 0 := by
      rw [Work.BoseBoxFock.uvCut]
      refine fu.zero _ ?_
      rw [le_div_iff₀ hΛpos]
      linarith
    rw [hGdef]
    simp only [hz, zero_mul, zero_div]

/-! ## 6. The interface inputs: integrability, summability and the UV tail -/

/-- The cross kernel `Ŵ₁ĝ` against `1/(2‖p‖²)` is integrable (Newtonian self-energies). -/
lemma integrable_crossW1g0 {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ}
    (hR : 0 < R) (hℓ : 0 < ℓ) (hv_nonneg : ∀ x : ℝ³, 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v) (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hRchi : R ≤ ℓ * Submission.BoseGases.chiR0) :
    MeasureTheory.Integrable (fun p : ℝ³ => Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p
      * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p / (2 * ‖p‖ ^ 2)) := by
  obtain ⟨h1, h2, h3⟩ := Work.BoseRowsFS.W1_g0_finite hR hℓ hv_nonneg hvrad hv_supp h hRchi
  exact Work.BoseRowsL.Bookkeeping.integrable_crossInt
    (Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRchi)
    (Submission.BoseGases.g0_integrable hR hv_supp h)
    (Submission.BoseGases.wScaled_g0_nonneg_ae hR hv_nonneg hvrad hv_supp h)
    (Submission.BoseGases.g0_nonneg_ae hR hv_nonneg hvrad hv_supp h)
    (Work.BoseFixR.isEven_W1fun h hvrad ℓ)
    (Submission.BoseGases.g0_even hvrad h) h1 h2 h3

/-- **The lattice kernel `|Ŵ₁ĝ|/‖k‖²` is summable** (AM–GM from the two quadratic lattice rows). -/
lemma summable_abs_cross {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v) (hv_nonneg : ∀ x : ℝ³, 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v) (hv_supp : tsupport v ⊆ Metric.ball 0 R) :
    ∀ ℓ : ℝ, 1 ≤ ℓ → R ≤ ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 →
      Summable (fun n : Fin 3 → ℤ =>
        |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (Work.BoseRowsFS.kvec ℓ n)
          * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (Work.BoseRowsFS.kvec ℓ n)|
          / ‖Work.BoseRowsFS.kvec ℓ n‖ ^ 2) := by
  intro ℓ hℓ1 hRℓ hRchi
  have hs := Work.BoseRowsL.Tails.lattice_energy_summable (h := h) hR hav hv_nonneg hvrad
    hv_supp ℓ hℓ1 hRℓ hRchi
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
  rw [abs_mul]
  set X : ℝ := Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (Work.BoseRowsFS.kvec ℓ n) with hX
  set Y : ℝ := Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (Work.BoseRowsFS.kvec ℓ n) with hY
  have h1 := sq_abs X
  have h2 := sq_abs Y
  have h3 : 0 ≤ |X| * |Y| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have h4 : 2 * (|X| * |Y|) ≤ |X| ^ 2 + |Y| ^ 2 := by
    nlinarith [sq_nonneg (|X| - |Y|)]
  linarith

/-! ## 7. The `uvCut` tail of the lattice sum (the interface field `tailL`) -/

/-- `uvCut` is `1` inside the ball of radius `Λ`. -/
lemma uvCut_eq_one {fu : Work.BoseBoxFix.LowCut} {Λ : ℝ} (hΛ : 0 < Λ) {k : ℝ³}
    (hk : ‖k‖ ≤ Λ) : Work.BoseBoxFock.uvCut fu Λ k = 1 := by
  rw [Work.BoseBoxFock.uvCut]
  refine fu.one _ ?_
  rw [div_le_one hΛ]
  exact hk

/-- **The `uvCut` tail**: beyond `uvRad` the `ℓ⁻³`-weighted lattice sum of `Ŵ₁ĝ` against
`1/(2‖k‖²)` is bounded by the interface field `tailL`. -/
lemma zeta_tail_le {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {fc fu : Work.BoseBoxFix.LowCut}
    {R : ℝ} (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v)
    (hthr : Work.BoseGateFS.GateThresholds v h fc fu R)
    (H : Work.BoseRowsL.HonestInterfaceL R hthr)
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (hNg : ∀ μ, H.Ng' μ ≤ (HM μ).N)
    (μ : ℝ) (hμ : 0 < μ) (hdil : μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg)
    (hΛpos : 0 < Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N) :
    |(Work.BoseBoxFock.ellH v μ) ^ (-(3 : ℝ)) * ∑' n : Fin 3 → ℤ,
        (1 - Work.BoseBoxFock.uvCut fu
            (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N)
            (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n))
          * (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
                (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n)
              * Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
                (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n)
              / (2 * ‖Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n‖ ^ 2))|
      ≤ H.Cw ^ 2 * _root_.BoseGases.a v * (R / Work.BoseBoxFock.ellH v μ) ^ 4 / 4 := by
  classical
  set ℓ := Work.BoseBoxFock.ellH v μ with hℓdef
  set Λ := Work.BoseBoxFock.uvRad ℓ (HM μ).N with hΛdef
  set C : ℝ := H.Cw ^ 2 * _root_.BoseGases.a v * (R / ℓ) ^ 4 with hCdef
  have hℓpos : 0 < ℓ := by rw [hℓdef]; exact Work.BoseBoxFock.ellH_pos v μ
  have hℓ3 : (0 : ℝ) < ℓ ^ (3 : ℝ) := Real.rpow_pos_of_pos hℓpos 3
  have hΛpos' : 0 < Λ := by rw [hΛdef]; exact hΛpos
  -- the `tailL` row, in the vocabulary of `ℓ`
  have hrow : ∀ S : Finset (Fin 3 → ℤ), (∀ n ∈ S, Λ < ‖ℓ⁻¹ • Work.BoseB4.vec n‖) →
      ℓ ^ (-(3 : ℝ)) * ∑ n ∈ S,
          (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec n) ^ 2
            + Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (ℓ⁻¹ • Work.BoseB4.vec n) ^ 2)
            / ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2 ≤ C := by
    intro S hS
    rw [hCdef]
    have h1 := H.tailL μ hμ hdil (HM μ).N (hNg μ) S (fun n hn => by
      rw [hΛdef] at hS
      exact hS n hn)
    have hswap : (∑ n ∈ S,
          (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec n) ^ 2
            + Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (ℓ⁻¹ • Work.BoseB4.vec n) ^ 2)
            / ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2)
        = ∑ n ∈ S,
          (Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (ℓ⁻¹ • Work.BoseB4.vec n) ^ 2
            + Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec n) ^ 2)
            / ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2 := by
      refine Finset.sum_congr rfl (fun n _ => ?_)
      ring
    rw [hswap]
    exact h1
  -- the `if`-majorant
  have hmaj : Summable (fun n : Fin 3 → ℤ => if Λ < ‖ℓ⁻¹ • Work.BoseB4.vec n‖ then
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec n) ^ 2
          + Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (ℓ⁻¹ • Work.BoseB4.vec n) ^ 2)
          / (4 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2) else 0) := by
    refine summable_of_sum_le (c := ℓ ^ (3:ℝ) * C / 4) (fun n => ?_) ?_
    · split_ifs with hh
      · positivity
      · exact le_rfl
    · intro u
      rw [← Finset.sum_filter]
      have h1 := hrow (u.filter (fun n => Λ < ‖ℓ⁻¹ • Work.BoseB4.vec n‖))
        (fun n hn => (Finset.mem_filter.mp hn).2)
      have h2 : (∑ n ∈ u.filter (fun n => Λ < ‖ℓ⁻¹ • Work.BoseB4.vec n‖),
            (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec n) ^ 2
              + Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (ℓ⁻¹ • Work.BoseB4.vec n) ^ 2)
              / (4 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2))
          = (1 / 4) * ∑ n ∈ u.filter (fun n => Λ < ‖ℓ⁻¹ • Work.BoseB4.vec n‖),
            (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec n) ^ 2
              + Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (ℓ⁻¹ • Work.BoseB4.vec n) ^ 2)
              / ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        ring
      rw [h2]
      have h3 := mul_le_mul_of_nonneg_left h1 hℓ3.le
      rw [show ℓ ^ (-(3 : ℝ)) = (ℓ ^ (3 : ℝ))⁻¹ by rw [Real.rpow_neg hℓpos.le]] at h3
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hℓ3), one_mul] at h3
      linarith
  have hif : (∑' n : Fin 3 → ℤ, if Λ < ‖ℓ⁻¹ • Work.BoseB4.vec n‖ then
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec n) ^ 2
          + Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (ℓ⁻¹ • Work.BoseB4.vec n) ^ 2)
          / (4 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2) else 0) ≤ ℓ ^ (3:ℝ) * C / 4 := by
    refine Real.tsum_le_of_sum_le (fun n => ?_) ?_
    · split_ifs with hh
      · positivity
      · exact le_rfl
    · intro u
      rw [← Finset.sum_filter]
      have h1 := hrow (u.filter (fun n => Λ < ‖ℓ⁻¹ • Work.BoseB4.vec n‖))
        (fun n hn => (Finset.mem_filter.mp hn).2)
      have h2 : (∑ n ∈ u.filter (fun n => Λ < ‖ℓ⁻¹ • Work.BoseB4.vec n‖),
            (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec n) ^ 2
              + Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (ℓ⁻¹ • Work.BoseB4.vec n) ^ 2)
              / (4 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2))
          = (1 / 4) * ∑ n ∈ u.filter (fun n => Λ < ‖ℓ⁻¹ • Work.BoseB4.vec n‖),
            (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec n) ^ 2
              + Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (ℓ⁻¹ • Work.BoseB4.vec n) ^ 2)
              / ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        ring
      rw [h2]
      have h3 := mul_le_mul_of_nonneg_left h1 hℓ3.le
      rw [show ℓ ^ (-(3 : ℝ)) = (ℓ ^ (3 : ℝ))⁻¹ by rw [Real.rpow_neg hℓpos.le]] at h3
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hℓ3), one_mul] at h3
      linarith
  -- the termwise bound
  have hterm : ∀ n : Fin 3 → ℤ,
      ‖(1 - Work.BoseBoxFock.uvCut fu Λ (ℓ⁻¹ • Work.BoseB4.vec n))
          * (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec n)
            * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (ℓ⁻¹ • Work.BoseB4.vec n)
            / (2 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2))‖
      ≤ (if Λ < ‖ℓ⁻¹ • Work.BoseB4.vec n‖ then
          (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec n) ^ 2
            + Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (ℓ⁻¹ • Work.BoseB4.vec n) ^ 2)
            / (4 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2) else 0) := by
    intro n
    by_cases hh : Λ < ‖ℓ⁻¹ • Work.BoseB4.vec n‖
    · rw [if_pos hh]
      have hz0 : 0 ≤ 1 - Work.BoseBoxFock.uvCut fu Λ (ℓ⁻¹ • Work.BoseB4.vec n) :=
        sub_nonneg.mpr (Work.BoseBoxFix.LowCut.le_one fu _)
      have hz1 : 1 - Work.BoseBoxFock.uvCut fu Λ (ℓ⁻¹ • Work.BoseB4.vec n) ≤ 1 := by
        have := Work.BoseBoxFix.LowCut.nonneg fu (‖ℓ⁻¹ • Work.BoseB4.vec n‖ / Λ)
        rw [Work.BoseBoxFock.uvCut]
        linarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hz0]
      have hAM : 2 * |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec n)
            * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (ℓ⁻¹ • Work.BoseB4.vec n)|
          ≤ (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec n)) ^ 2
            + (Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (ℓ⁻¹ • Work.BoseB4.vec n)) ^ 2 := by
        rw [abs_mul]
        nlinarith [sq_nonneg (|Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec n)|
            - |Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (ℓ⁻¹ • Work.BoseB4.vec n)|),
          sq_abs (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec n)),
          sq_abs (Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (ℓ⁻¹ • Work.BoseB4.vec n)),
          abs_nonneg (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec n)),
          abs_nonneg (Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (ℓ⁻¹ • Work.BoseB4.vec n))]
      rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2)]
      have h0 : (0 : ℝ) ≤ |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec n)
          * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (ℓ⁻¹ • Work.BoseB4.vec n)|
          / (2 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2) :=
        div_nonneg (abs_nonneg _) (by positivity)
      have hstep1 : (1 - Work.BoseBoxFock.uvCut fu Λ (ℓ⁻¹ • Work.BoseB4.vec n))
            * (|Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec n)
                * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (ℓ⁻¹ • Work.BoseB4.vec n)|
                / (2 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2))
          ≤ |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec n)
              * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (ℓ⁻¹ • Work.BoseB4.vec n)|
              / (2 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2) := by
        nlinarith [hz1, h0]
      have hstep2 : |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec n)
              * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (ℓ⁻¹ • Work.BoseB4.vec n)|
              / (2 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2)
          = (2 * |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec n)
              * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (ℓ⁻¹ • Work.BoseB4.vec n)|)
              / (4 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2) := by
        ring
      have hstep3 : (2 * |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec n)
              * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (ℓ⁻¹ • Work.BoseB4.vec n)|)
              / (4 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2)
          ≤ (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec n) ^ 2
              + Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (ℓ⁻¹ • Work.BoseB4.vec n) ^ 2)
              / (4 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2) :=
        div_le_div_of_nonneg_right hAM (by positivity)
      linarith
    · rw [if_neg hh]
      have hz : Work.BoseBoxFock.uvCut fu Λ (ℓ⁻¹ • Work.BoseB4.vec n) = 1 :=
        uvCut_eq_one hΛpos' (not_lt.mp hh)
      rw [hz, sub_self, zero_mul, norm_zero]
  have hsumm : Summable (fun n : Fin 3 → ℤ =>
      (1 - Work.BoseBoxFock.uvCut fu Λ (ℓ⁻¹ • Work.BoseB4.vec n))
        * (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec n)
          * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (ℓ⁻¹ • Work.BoseB4.vec n)
          / (2 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2))) :=
    Summable.of_norm_bounded hmaj hterm
  have hmain : ‖∑' n : Fin 3 → ℤ,
      (1 - Work.BoseBoxFock.uvCut fu Λ (ℓ⁻¹ • Work.BoseB4.vec n))
        * (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec n)
          * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (ℓ⁻¹ • Work.BoseB4.vec n)
          / (2 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2))‖ ≤ ℓ ^ (3:ℝ) * C / 4 := by
    refine le_trans (norm_tsum_le_tsum_norm hsumm.norm) ?_
    exact le_trans (Summable.tsum_le_tsum hterm hsumm.norm hmaj) hif
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ℓ ^ (-(3 : ℝ)))]
  calc ℓ ^ (-(3 : ℝ)) * ‖∑' n : Fin 3 → ℤ,
        (1 - Work.BoseBoxFock.uvCut fu Λ (ℓ⁻¹ • Work.BoseB4.vec n))
          * (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec n)
            * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (ℓ⁻¹ • Work.BoseB4.vec n)
            / (2 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2))‖
      ≤ ℓ ^ (-(3 : ℝ)) * (ℓ ^ (3:ℝ) * C / 4) := mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = C / 4 := by
        rw [Real.rpow_neg hℓpos.le]
        field_simp

/-! ## 8. The torus/free Green-function comparison -/

-- NOTE: the requested statement `Work.BoseRowsL.Row2.smallT_bound` omitted the parentheses
-- around `∫ x : ℝ³, h x`; as elaborated the binder swallows the second subtraction and the
-- statement is FALSE.  We use the corrected (parenthesised) statement
-- `Work.BoseRowsL.Row2.smallT_bound_repaired` from `Row2/smallT_bound.lean`.

/-- **The torus/free Green-function comparison**: the lattice sum `ℓ⁻³Σ_{n≠0}ĥ(k_n)/(2k_n²)`
and the continuum integral `(2π)⁻³∫ĥ(p)/(2p²)dp` differ by at most `1550 ‖h‖₁/ℓ`. -/
theorem torus_free_comparison {ℓ : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ} (hI : MeasureTheory.Integrable h)
    (hsupp : tsupport h ⊆ Metric.closedBall 0 (ℓ / 2))
    (hInt : MeasureTheory.Integrable (fun p : ℝ³ => Work.BoseFixR.chat h p / (2 * ‖p‖ ^ 2)))
    (hsumm : Summable (fun n : Fin 3 → ℤ => |Work.BoseFixR.chat h (kvec ℓ n)| / ‖kvec ℓ n‖ ^ 2)) :
    |(ℓ ^ 3)⁻¹ * (∑' n : Fin 3 → ℤ, Work.BoseFixR.chat h (kvec ℓ n) / (2 * ‖kvec ℓ n‖ ^ 2))
      - ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, Work.BoseFixR.chat h p / (2 * ‖p‖ ^ 2)|
      ≤ 3100 * (∫ x : ℝ³, |h x|) / ℓ := by
  have hℓpos : 0 < ℓ := hℓ
  -- (a) the two heat representations
  have hAid : (ℓ ^ 3)⁻¹ * (∑' n : Fin 3 → ℤ, Work.BoseFixR.chat h (kvec ℓ n)
      / (2 * ‖kvec ℓ n‖ ^ 2)) = (1 / 2) * ∫ t in Set.Ioi (0:ℝ), hA ℓ h t :=
    -- `kvec ℓ n` is *definitionally* `kmomInt ℓ n` and `hA ℓ h t` is *definitionally* the
    -- integrand of `hA_heat_integral`, so this is the same statement (no rewriting needed).
    Work.BoseRowsL.Row2.hA_heat_integral (ℓ := ℓ) hℓ (h := h) (hsumm := hsumm)
  have hBid : ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³, Work.BoseFixR.chat h p / (2 * ‖p‖ ^ 2))
      = (1 / 2) * ∫ t in Set.Ioi (0:ℝ), hB h t := by
    rw [Work.BoseRowsL.Row2.heatFubini (h := h) hInt]
    have hconst : (∫ t in Set.Ioi (0:ℝ), hB h t)
        = ((2 * Real.pi) ^ 3)⁻¹ * ∫ t in Set.Ioi (0:ℝ),
            ∫ p : ℝ³, Work.BoseFixR.chat h p * Real.exp (-(t * ‖p‖ ^ 2)) := by
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => rfl))
    rw [hconst]
    ring
  -- (b) integrability on `(0,∞)`
  have hAintg : MeasureTheory.Integrable (fun t : ℝ => hA ℓ h t)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (Work.BoseRowsL.Row2.heatA_integrable (ℓ := ℓ) hℓ (h := h) hsumm).congr
      (Filter.Eventually.of_forall (fun t => rfl))
  have hBintg : MeasureTheory.Integrable (fun t : ℝ => hB h t)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (Work.BoseRowsL.Row2.heatB_integrable (h := h) hInt).congr
      (Filter.Eventually.of_forall (fun t => rfl))
  -- (c) the two interval bounds
  have hsmall : (∫ t in Set.Ioo (0:ℝ) (ℓ ^ 2), |hA ℓ h t - hB h t|)
      ≤ 3000 * (∫ x : ℝ³, |h x|) / ℓ := by
    refine le_of_eq_of_le ?_ (Work.BoseRowsL.Row2.smallT_bound_repaired (ℓ := ℓ) hℓ (h := h) hI hsupp)
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
    rw [hA_eq hℓ hI hsupp ht.1, hB_eq hI ht.1]
  have hlarge : (∫ t in Set.Ioi (ℓ ^ 2), |hA ℓ h t - hB h t|)
      ≤ 100 * (∫ x : ℝ³, |h x|) / ℓ :=
    Work.BoseRowsL.Row2.largeT_bound (ℓ := ℓ) hℓ (h := h) hI
  -- (d) the split
  have hsplit : (∫ t in Set.Ioi (0:ℝ), (hA ℓ h t - hB h t))
      = (∫ t in Set.Ioo (0:ℝ) (ℓ ^ 2), (hA ℓ h t - hB h t))
        + ∫ t in Set.Ioi (ℓ ^ 2), (hA ℓ h t - hB h t) := by
    have h0 : (∫ t in Set.Ioi (0:ℝ), (hA ℓ h t - hB h t))
        = (∫ t in Set.Ioc (0:ℝ) (ℓ ^ 2), (hA ℓ h t - hB h t))
          + ∫ t in Set.Ioi (ℓ ^ 2), (hA ℓ h t - hB h t) := by
      rw [← Set.Ioc_union_Ioi_eq_Ioi (by positivity : (0:ℝ) ≤ ℓ ^ 2)]
      have hsub₁ : Set.Ioc (0:ℝ) (ℓ ^ 2) ⊆ Set.Ioi (0:ℝ) := fun t ht => by
        simpa only [Set.mem_Ioc, Set.mem_Ioi] using ht.1
      have hsub₂ : Set.Ioi (ℓ ^ 2) ⊆ Set.Ioi (0:ℝ) := fun t ht => by
        simp only [Set.mem_Ioi] at ht ⊢
        have hp : (0:ℝ) < ℓ ^ 2 := by positivity
        linarith
      have hI0int : MeasureTheory.IntegrableOn (fun t : ℝ => hA ℓ h t - hB h t)
          (Set.Ioi (0:ℝ)) volume := hAintg.sub hBintg
      exact MeasureTheory.setIntegral_union (μ := volume) Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hI0int.mono_set hsub₁) (hI0int.mono_set hsub₂)
    rw [h0]
    congr 1
    refine MeasureTheory.setIntegral_congr_set ?_
    exact (MeasureTheory.Ioo_ae_eq_Ioc' (measure_singleton (ℓ ^ 2))).symm
  -- (e) the assembly
  rw [hAid, hBid]
  rw [← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (1/2))]
  rw [← MeasureTheory.integral_sub hAintg hBintg, hsplit]
  have h1 : |∫ t in Set.Ioo (0:ℝ) (ℓ ^ 2), (hA ℓ h t - hB h t)|
      ≤ 3000 * (∫ x : ℝ³, |h x|) / ℓ :=
    le_trans (by
      simpa only [Real.norm_eq_abs] using MeasureTheory.norm_integral_le_integral_norm
        (f := fun t : ℝ => hA ℓ h t - hB h t)
        (μ := MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) (ℓ ^ 2)))) hsmall
  have h2 : |∫ t in Set.Ioi (ℓ ^ 2), (hA ℓ h t - hB h t)|
      ≤ 100 * (∫ x : ℝ³, |h x|) / ℓ :=
    le_trans (by
      simpa only [Real.norm_eq_abs] using MeasureTheory.norm_integral_le_integral_norm
        (f := fun t : ℝ => hA ℓ h t - hB h t)
        (μ := MeasureTheory.volume.restrict (Set.Ioi (ℓ ^ 2)))) hlarge
  have hX : (0 : ℝ) ≤ ∫ x : ℝ³, |h x| := integral_nonneg (fun x => abs_nonneg _)
  calc (1 / 2) * |(∫ t in Set.Ioo (0:ℝ) (ℓ ^ 2), (hA ℓ h t - hB h t))
        + ∫ t in Set.Ioi (ℓ ^ 2), (hA ℓ h t - hB h t)|
      ≤ (1 / 2) * (|∫ t in Set.Ioo (0:ℝ) (ℓ ^ 2), (hA ℓ h t - hB h t)|
          + |∫ t in Set.Ioi (ℓ ^ 2), (hA ℓ h t - hB h t)|) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact abs_add_le _ _
    _ ≤ (1 / 2) * (3100 * (∫ x : ℝ³, |h x|) / ℓ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        calc |∫ t in Set.Ioo (0:ℝ) (ℓ ^ 2), (hA ℓ h t - hB h t)|
              + |∫ t in Set.Ioi (ℓ ^ 2), (hA ℓ h t - hB h t)|
            ≤ (3000 * (∫ x : ℝ³, |h x|)) / ℓ + (100 * (∫ x : ℝ³, |h x|)) / ℓ :=
              add_le_add h1 h2
          _ = (3100 * (∫ x : ℝ³, |h x|)) / ℓ := by ring
    _ = 1550 * (∫ x : ℝ³, |h x|) / ℓ := by ring
    _ ≤ 3100 * (∫ x : ℝ³, |h x|) / ℓ := by
        rw [div_le_div_iff_of_pos_right hℓpos]
        linarith

/-- **Pure bookkeeping arithmetic for the last row.**  Multiplying by `ℓ > 1` the leading
`3100·(8π Cw A²)` cancels against `24800 π Cw A²` (`3100·8 = 24800`), and
`(R/ℓ)⁴·ℓ = R⁴/ℓ³ ≤ R⁴` because `ℓ ≥ 1`. -/
lemma omega_row_arith {A R ℓ Cw : ℝ} (hA : 0 < A) (hℓ : 1 ≤ ℓ) (hCw : 0 ≤ Cw) :
    3100 * (8 * Real.pi * Cw * A ^ 2) / ℓ + Cw ^ 2 * A * (R / ℓ) ^ 4 / 4
      ≤ (24800 * Real.pi * Cw + Cw ^ 2 * R ^ 4 / (4 * A) + 1) * A ^ 2 / ℓ := by
  have hℓpos : 0 < ℓ := lt_of_lt_of_le one_pos hℓ
  have hℓ3 : (1 : ℝ) ≤ ℓ ^ 3 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hℓ 3
  have hR4 : (0 : ℝ) ≤ R ^ 4 := by positivity
  have hkey : (R / ℓ) ^ 4 * ℓ ≤ R ^ 4 := by
    rw [div_pow,
      show R ^ 4 / ℓ ^ 4 * ℓ = R ^ 4 / ℓ ^ 3 by field_simp]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ℓ ^ 3)]
    nlinarith [hℓ3, hR4]
  have hmain : 3100 * (8 * Real.pi * Cw * A ^ 2) + Cw ^ 2 * A * ((R / ℓ) ^ 4 * ℓ) / 4
      ≤ (24800 * Real.pi * Cw + Cw ^ 2 * R ^ 4 / (4 * A) + 1) * A ^ 2 := by
    have h1 : Cw ^ 2 * A * ((R / ℓ) ^ 4 * ℓ) / 4 ≤ Cw ^ 2 * R ^ 4 * A / 4 := by
      rw [show Cw ^ 2 * R ^ 4 * A / 4 = Cw ^ 2 * A * R ^ 4 / 4 by ring]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hkey (by positivity)) (by norm_num)
    have h2 : Cw ^ 2 * R ^ 4 * A / 4
        ≤ Cw ^ 2 * R ^ 4 / (4 * A) * A ^ 2 + A ^ 2 := by
      rw [show Cw ^ 2 * R ^ 4 / (4 * A) * A ^ 2 = Cw ^ 2 * R ^ 4 * A / 4 by
        field_simp]
      linarith [sq_nonneg A]
    have h3 : (24800 : ℝ) * Real.pi * Cw * A ^ 2 = 3100 * (8 * Real.pi * Cw * A ^ 2) := by
      ring
    nlinarith [h1, h2, h3]
  have h4 : (0 : ℝ) < 4 * ℓ := by linarith
  rw [show 3100 * (8 * Real.pi * Cw * A ^ 2) / ℓ + Cw ^ 2 * A * (R / ℓ) ^ 4 / 4
      = (4 * (3100 * (8 * Real.pi * Cw * A ^ 2)) + Cw ^ 2 * A * (R / ℓ) ^ 4 * ℓ) / (4 * ℓ) by
    field_simp]
  rw [show (24800 * Real.pi * Cw + Cw ^ 2 * R ^ 4 / (4 * A) + 1) * A ^ 2 / ℓ
      = (4 * ((24800 * Real.pi * Cw + Cw ^ 2 * R ^ 4 / (4 * A) + 1) * A ^ 2)) / (4 * ℓ) by
    field_simp]
  exact div_le_div_of_nonneg_right (by linarith [hmain]) h4.le

theorem omegaLatticeRow_of_interface {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hthr : Work.BoseGateFS.GateThresholds v h fc fu R) (H : Work.BoseRowsL.HonestInterfaceL R hthr) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ),
      (∀ μ, H.Ng' μ ≤ (HM μ).N) →
      ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
        |(Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
          - (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
            ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
              (Work.BoseRowsFS.honE v h fc fu HM μ).W1 k
                * Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
                    ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k)
                / (2 * ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ ^ 2)|
          ≤ K₀ * _root_.BoseGases.a v ^ 2 / (Work.BoseRowsFS.honE v h fc fu HM μ).ell := by
  -- the constant
  have hCw0 : 0 ≤ H.Cw := H.Cw_nonneg
  refine ⟨24800 * Real.pi * H.Cw + H.Cw ^ 2 * R ^ 4 / (4 * _root_.BoseGases.a v) + 1,
    by positivity, ?_⟩
  intro HM hNg μ hμ hdil
  -- the interface rows
  have hNg' : ∀ μ' : ℝ, hthr.Ng μ' ≤ (HM μ').N := fun μ' => le_trans (H.Ng'_ge μ') (hNg μ')
  obtain ⟨hℓ1, hR2KH, hRchi, hdil323, hKL, hKH32⟩ := hthr.dil HM hNg' μ hμ hdil
  obtain ⟨hΛ1, hΛ2, hΛ3, hΛ4⟩ := hthr.cube HM hNg' μ hμ hdil
  have h4R : 4 * R ≤ Work.BoseBoxFock.ellH v μ :=
    Work.BoseRowsL.Regime.fourR_le_ell R hav hthr HM hNg' μ hμ hdil
  have hℓpos : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  have hΛpos : 0 < Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N :=
    lt_of_lt_of_le one_pos hΛ1
  set ℓ := Work.BoseBoxFock.ellH v μ with hℓdef
  -- the mass identity
  have hmass := Work.BoseRowsFS.honE_W1omega0_eq_integral (v := v) (h := h) (fc := fc) (fu := fu)
    R hR hv_nonneg hvrad hv_supp HM μ hμ hav hℓ1 hRchi
  -- the convolution `h0 = W₁ ∗ g₀`
  set h0 : ℝ³ → ℝ := fun y => ∫ x, Work.BoseFixR.W1fun v h ℓ x
      * Submission.BoseGases.g0 v h (y - x) with hh0def
  have hW1funI : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ) :=
    Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓpos hRchi
  have hg0I : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  have hg0even : ∀ x : ℝ³, Submission.BoseGases.g0 v h (-x) = Submission.BoseGases.g0 v h x :=
    Submission.BoseGases.g0_even hvrad h
  have h0chat : ∀ k : ℝ³, Work.BoseFixR.chat h0 k
      = Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) k
        * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) k :=
    fun k => Work.BoseRowsL.Row2.chat_conv_chat_eq hW1funI hg0I hg0even k
  have h0supp : tsupport h0 ⊆ Metric.closedBall 0 (ℓ / 2) := by
    have hW1b : tsupport (Work.BoseFixR.W1fun v h ℓ) ⊆ Metric.closedBall 0 R :=
      fun x hx => Metric.ball_subset_closedBall (Work.BoseFixR.tsupport_W1fun_subset h hv_supp ℓ hx)
    have hg0b : tsupport (Submission.BoseGases.g0 v h) ⊆ Metric.closedBall 0 R :=
      fun x hx => Metric.ball_subset_closedBall (Work.BoseRowsL.Tails.tsupport_g0_subset h hv_supp hx)
    refine subset_trans (Work.BoseRowsL.Row2.tsupport_conv_subset hW1b hg0b) ?_
    exact Metric.closedBall_subset_closedBall (by linarith : 2 * R ≤ ℓ / 2)
  have h0I : MeasureTheory.Integrable h0 :=
    Work.BoseRowsL.Row2.chat_conv_integrable hW1funI hg0I
  have h0Int : MeasureTheory.Integrable (fun p : ℝ³ => Work.BoseFixR.chat h0 p / (2 * ‖p‖ ^ 2)) :=
    (integrable_crossW1g0 (h := h) hR hℓpos hv_nonneg hvrad hv_supp hRchi).congr
      (Filter.Eventually.of_forall (fun p => by
        show Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p
            * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p / (2 * ‖p‖ ^ 2)
          = Work.BoseFixR.chat h0 p / (2 * ‖p‖ ^ 2)
        rw [h0chat p]))
  have hsumm0 : Summable (fun n : Fin 3 → ℤ =>
      |Work.BoseFixR.chat h0 (kvec ℓ n)| / ‖kvec ℓ n‖ ^ 2) := by
    have hs := summable_abs_cross (h := h) hR hav hv_nonneg hvrad hv_supp ℓ hℓ1
      (by linarith : R ≤ ℓ) hRchi
    refine hs.congr (fun n => ?_)
    -- `Work.BoseRowsFS.kvec` agrees with our `kvec` (= `BoseBoxFock.kmomInt`)
    have hk : Work.BoseRowsFS.kvec ℓ n = kvec ℓ n := (Work.BoseRowsFS.kvec_eq ℓ n).trans rfl
    rw [hk, h0chat (kvec ℓ n)]
  -- the norm bound
  have hW1int : (∫ x : ℝ³, |Work.BoseFixR.W1fun v h ℓ x|) ≤ H.Cw * _root_.BoseGases.a v := by
    have hnn : ∀ᵐ x : ℝ³, 0 ≤ Work.BoseFixR.W1fun v h ℓ x :=
      Submission.BoseGases.wScaled_g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
    rw [MeasureTheory.integral_congr_ae (hnn.mono (fun x hx => abs_of_nonneg hx))]
    rw [← Work.BoseB7AK.W1rows.chat_zero]
    exact le_trans (le_abs_self _) (H.bndW ℓ hℓ1 hRchi 0)
  have hg0int : (∫ x : ℝ³, |Submission.BoseGases.g0 v h x|) = 8 * Real.pi * _root_.BoseGases.a v := by
    have hnn : ∀ᵐ x : ℝ³, 0 ≤ Submission.BoseGases.g0 v h x :=
      Submission.BoseGases.g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
    rw [MeasureTheory.integral_congr_ae (hnn.mono (fun x hx => abs_of_nonneg hx))]
    exact Submission.BoseGases.g0_integral hR hv_supp h
  have h0norm : (∫ x : ℝ³, |h0 x|) ≤ 8 * Real.pi * H.Cw * (_root_.BoseGases.a v) ^ 2 := by
    have h1 := Work.BoseRowsL.Row2.chat_conv_abs_integral_le hW1funI hg0I
    have hWnn : (0 : ℝ) ≤ ∫ x : ℝ³, |Work.BoseFixR.W1fun v h ℓ x| :=
      integral_nonneg (fun x => abs_nonneg _)
    have hgnn : (0 : ℝ) ≤ ∫ x : ℝ³, |Submission.BoseGases.g0 v h x| :=
      integral_nonneg (fun x => abs_nonneg _)
    refine le_trans h1 ?_
    calc (∫ x : ℝ³, |Work.BoseFixR.W1fun v h ℓ x|) * ∫ x : ℝ³, |Submission.BoseGases.g0 v h x|
        ≤ (H.Cw * _root_.BoseGases.a v) * (8 * Real.pi * _root_.BoseGases.a v) :=
          mul_le_mul hW1int hg0int.le hgnn (by positivity)
      _ = 8 * Real.pi * H.Cw * (_root_.BoseGases.a v) ^ 2 := by ring
  -- the comparison
  have hcmp := torus_free_comparison (ℓ := ℓ) hℓpos (h := h0) h0I h0supp h0Int hsumm0
  -- the cube sum and the tail
  have hcube := cube_sum_eq_tsum (v := v) (h := h) (fc := fc) (fu := fu) HM μ hμ hav hΛpos
  have htail := zeta_tail_le (v := v) (h := h) (fc := fc) (fu := fu) (R := R) hR hav hthr H HM hNg
    μ hμ hdil hΛpos
  -- the mass identity in terms of `h0`
  have hI0 : (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, Work.BoseFixR.chat h0 p / (2 * ‖p‖ ^ 2) := by
    rw [hmass]
    refine congrArg _ (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_)))
    show Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p
          * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p / (2 * ‖p‖ ^ 2)
        = Work.BoseFixR.chat h0 p / (2 * ‖p‖ ^ 2)
    rw [h0chat p]
  -- the cube sum in terms of `h0`
  have hcube0 : (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        (Work.BoseRowsFS.honE v h fc fu HM μ).W1 k
          * Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
              ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k)
          / (2 * ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ ^ 2))
      = ∑' n : Fin 3 → ℤ,
          Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ (HM μ).N) (kvec ℓ n)
            * (Work.BoseFixR.chat h0 (kvec ℓ n) / (2 * ‖kvec ℓ n‖ ^ 2)) := by
    rw [hcube]
    refine tsum_congr (fun n => ?_)
    rw [h0chat (kvec ℓ n)]
    simp only [kvec, hℓdef]
    ring
  -- the tail decomposition
  have hsumabs : Summable (fun n : Fin 3 → ℤ =>
      |Work.BoseFixR.chat h0 (kvec ℓ n)| / (2 * ‖kvec ℓ n‖ ^ 2)) :=
    (hsumm0.div_const 2).congr (fun n => by rw [div_div]; ring)
  have hsumf : Summable (fun n : Fin 3 → ℤ =>
      Work.BoseFixR.chat h0 (kvec ℓ n) / (2 * ‖kvec ℓ n‖ ^ 2)) := by
    refine Summable.of_norm_bounded hsumabs (fun n => ?_)
    rw [Real.norm_eq_abs, abs_div,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ‖kvec ℓ n‖ ^ 2)]
  have hsumzf : Summable (fun n : Fin 3 → ℤ =>
      Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ (HM μ).N) (kvec ℓ n)
        * (Work.BoseFixR.chat h0 (kvec ℓ n) / (2 * ‖kvec ℓ n‖ ^ 2))) := by
    refine Summable.of_norm_bounded hsumabs (fun n => ?_)
    have hle : |Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ (HM μ).N) (kvec ℓ n)| ≤ 1 := by
      rw [Work.BoseBoxFock.uvCut]
      refine abs_le.mpr ⟨?_, Work.BoseBoxFix.LowCut.le_one _ _⟩
      have := Work.BoseBoxFix.LowCut.nonneg fu
        (‖kvec ℓ n‖ / Work.BoseBoxFock.uvRad ℓ (HM μ).N)
      linarith
    have hnn : (0 : ℝ) ≤ |Work.BoseFixR.chat h0 (kvec ℓ n)| / (2 * ‖kvec ℓ n‖ ^ 2) := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_div,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ‖kvec ℓ n‖ ^ 2)]
    exact mul_le_of_le_one_left hnn hle
  have hdecomp : (∑' n : Fin 3 → ℤ,
        Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ (HM μ).N) (kvec ℓ n)
          * (Work.BoseFixR.chat h0 (kvec ℓ n) / (2 * ‖kvec ℓ n‖ ^ 2)))
      = (∑' n : Fin 3 → ℤ, Work.BoseFixR.chat h0 (kvec ℓ n) / (2 * ‖kvec ℓ n‖ ^ 2))
        - ∑' n : Fin 3 → ℤ,
            (1 - Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ (HM μ).N) (kvec ℓ n))
              * (Work.BoseFixR.chat h0 (kvec ℓ n) / (2 * ‖kvec ℓ n‖ ^ 2)) := by
    have h1 : (∑' n : Fin 3 → ℤ,
          (1 - Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ (HM μ).N) (kvec ℓ n))
            * (Work.BoseFixR.chat h0 (kvec ℓ n) / (2 * ‖kvec ℓ n‖ ^ 2)))
        = (∑' n : Fin 3 → ℤ, Work.BoseFixR.chat h0 (kvec ℓ n) / (2 * ‖kvec ℓ n‖ ^ 2))
          - ∑' n : Fin 3 → ℤ,
              Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ (HM μ).N) (kvec ℓ n)
                * (Work.BoseFixR.chat h0 (kvec ℓ n) / (2 * ‖kvec ℓ n‖ ^ 2)) := by
      rw [show (∑' n : Fin 3 → ℤ,
            (1 - Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ (HM μ).N) (kvec ℓ n))
              * (Work.BoseFixR.chat h0 (kvec ℓ n) / (2 * ‖kvec ℓ n‖ ^ 2)))
          = ∑' n : Fin 3 → ℤ, (Work.BoseFixR.chat h0 (kvec ℓ n) / (2 * ‖kvec ℓ n‖ ^ 2)
              - Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ (HM μ).N) (kvec ℓ n)
                * (Work.BoseFixR.chat h0 (kvec ℓ n) / (2 * ‖kvec ℓ n‖ ^ 2))) from
        tsum_congr (fun n => by ring),
        Summable.tsum_sub hsumf hsumzf]
    rw [h1]
    ring
  -- the tail bound in the vocabulary of `h0`
  have htail' : |ℓ ^ (-(3 : ℝ)) * ∑' n : Fin 3 → ℤ,
        (1 - Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N)
            (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n))
          * (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
                (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n)
              * Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
                (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n)
              / (2 * ‖Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n‖ ^ 2))|
      ≤ H.Cw ^ 2 * _root_.BoseGases.a v * (R / Work.BoseBoxFock.ellH v μ) ^ 4 / 4 := htail
  have htail0 : |ℓ ^ (-(3 : ℝ)) * ∑' n : Fin 3 → ℤ,
        (1 - Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ (HM μ).N) (kvec ℓ n))
          * (Work.BoseFixR.chat h0 (kvec ℓ n) / (2 * ‖kvec ℓ n‖ ^ 2))|
      ≤ H.Cw ^ 2 * _root_.BoseGases.a v * (R / ℓ) ^ 4 / 4 := by
    rw [show H.Cw ^ 2 * _root_.BoseGases.a v * (R / ℓ) ^ 4 / 4
          = H.Cw ^ 2 * _root_.BoseGases.a v * (R / Work.BoseBoxFock.ellH v μ) ^ 4 / 4 from rfl]
    refine le_of_eq ?_ |>.trans htail'
    congr 2
    refine tsum_congr (fun n => ?_)
    rw [h0chat (kvec ℓ n)]
    simp only [kvec, hℓdef]
  -- the arithmetic
  have harith : 3100 * (8 * Real.pi * H.Cw * (_root_.BoseGases.a v) ^ 2) / ℓ
      + H.Cw ^ 2 * _root_.BoseGases.a v * (R / ℓ) ^ 4 / 4
      ≤ (24800 * Real.pi * H.Cw + H.Cw ^ 2 * R ^ 4 / (4 * _root_.BoseGases.a v) + 1)
          * (_root_.BoseGases.a v) ^ 2 / ℓ :=
    omega_row_arith hav hℓ1 hCw0
  -- the final assembly
  have hrpow3 : ℓ ^ (-(3 : ℝ)) = (ℓ ^ 3)⁻¹ := by
    rw [Real.rpow_neg hℓpos.le]
    exact congrArg Inv.inv (Real.rpow_natCast ℓ 3)
  have hcomp' : |((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³, Work.BoseFixR.chat h0 p / (2 * ‖p‖ ^ 2))
      - ℓ ^ (-(3 : ℝ)) * ∑' n : Fin 3 → ℤ,
          Work.BoseFixR.chat h0 (kvec ℓ n) / (2 * ‖kvec ℓ n‖ ^ 2)|
      ≤ 3100 * (8 * Real.pi * H.Cw * (_root_.BoseGases.a v) ^ 2) / ℓ := by
    rw [hrpow3]
    refine le_trans (le_of_eq (abs_sub_comm _ _)) ?_
    refine le_trans hcmp ?_
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left h0norm (by norm_num : (0 : ℝ) ≤ 3100)) hℓpos.le
  -- convert the goal's `(honE …).ell` into the local `ℓ`
  have hℓE : ℓ = (Work.BoseRowsFS.honE v h fc fu HM μ).ell := by
    rw [hℓdef]
    exact (Work.BoseRowsFS.honE_ell v h fc fu HM μ hμ hav).symm
  rw [← hℓE]
  calc |(Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
        - ℓ ^ (-(3 : ℝ)) * (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
            (Work.BoseRowsFS.honE v h fc fu HM μ).W1 k
              * Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
                  ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k)
              / (2 * ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ ^ 2))|
      = |(Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
          - ℓ ^ (-(3 : ℝ)) * ∑' n : Fin 3 → ℤ,
              Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ (HM μ).N) (kvec ℓ n)
                * (Work.BoseFixR.chat h0 (kvec ℓ n) / (2 * ‖kvec ℓ n‖ ^ 2))| := by
        rw [hcube0]
    _ = |(Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
          - ℓ ^ (-(3 : ℝ)) * ((∑' n : Fin 3 → ℤ,
                Work.BoseFixR.chat h0 (kvec ℓ n) / (2 * ‖kvec ℓ n‖ ^ 2))
              - ∑' n : Fin 3 → ℤ,
                  (1 - Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ (HM μ).N) (kvec ℓ n))
                    * (Work.BoseFixR.chat h0 (kvec ℓ n) / (2 * ‖kvec ℓ n‖ ^ 2)))| := by
        rw [hdecomp]
    _ = |((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³, Work.BoseFixR.chat h0 p / (2 * ‖p‖ ^ 2))
          - ℓ ^ (-(3 : ℝ)) * (∑' n : Fin 3 → ℤ,
                Work.BoseFixR.chat h0 (kvec ℓ n) / (2 * ‖kvec ℓ n‖ ^ 2))
          + ℓ ^ (-(3 : ℝ)) * ∑' n : Fin 3 → ℤ,
                  (1 - Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ (HM μ).N) (kvec ℓ n))
                    * (Work.BoseFixR.chat h0 (kvec ℓ n) / (2 * ‖kvec ℓ n‖ ^ 2))| := by
        rw [hI0]
        ring_nf
    _ ≤ |((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³, Work.BoseFixR.chat h0 p / (2 * ‖p‖ ^ 2))
          - ℓ ^ (-(3 : ℝ)) * (∑' n : Fin 3 → ℤ,
                Work.BoseFixR.chat h0 (kvec ℓ n) / (2 * ‖kvec ℓ n‖ ^ 2))|
        + |ℓ ^ (-(3 : ℝ)) * ∑' n : Fin 3 → ℤ,
                  (1 - Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ (HM μ).N) (kvec ℓ n))
                    * (Work.BoseFixR.chat h0 (kvec ℓ n) / (2 * ‖kvec ℓ n‖ ^ 2))| :=
        abs_add_le _ _
    _ ≤ 3100 * (8 * Real.pi * H.Cw * (_root_.BoseGases.a v) ^ 2) / ℓ
        + H.Cw ^ 2 * _root_.BoseGases.a v * (R / ℓ) ^ 4 / 4 := by
        refine add_le_add ?_ ?_
        · exact hcomp'
        · exact htail0
    _ ≤ (24800 * Real.pi * H.Cw + H.Cw ^ 2 * R ^ 4 / (4 * _root_.BoseGases.a v) + 1)
          * (_root_.BoseGases.a v) ^ 2 / ℓ := harith

end Work.BoseRowsL.Row2
