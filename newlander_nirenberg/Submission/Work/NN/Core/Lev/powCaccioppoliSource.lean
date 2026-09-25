import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Polydisc.dbarCoord_mul
import Submission.Work.NN.Core.integral_normSq_dCoord_eq_dbarCoord
import Submission.Work.NN.Core.weighted_energy_le
import Submission.Work.NN.Core.contDiff_one_mul_of_support
import Submission.Work.NN.Core.exists_contDiff_bump_of_isCompact_subset

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff ENNReal Topology

namespace Work.NN.Core.Lev

/-! ## Auxiliary calculus lemmas for `powCaccioppoliSource`

The perturbed weighted-energy estimate `weightedEnergyPerturbed` below is the analytic core; the
remaining lemmas are the calculus needed to instantiate it at `H = u ^ k`. -/

/-- The `(1,0)`- and `(0,1)`-parts reconstruct the derivative: `∂_j H + ∂̄_j H = dH(e_j)`. -/
lemma dCoord_add_dbarCoord {n : ℕ} (j : Fin n) (H : Cn n → ℂ) (z : Cn n) :
    Work.CR.Flat.dCoord j H z + Work.CR.Flat.dbarCoord j H z
      = fderiv ℝ H z (Pi.single j (1 : ℂ)) := by
  rw [Work.CR.Flat.dCoord, Work.CR.Flat.dbarCoord]; ring

/-- The `(1,0)`- and `(0,1)`-parts differ by the imaginary-direction derivative:
`∂_j H - ∂̄_j H = -i dH(i e_j)`. -/
lemma dCoord_sub_dbarCoord {n : ℕ} (j : Fin n) (H : Cn n → ℂ) (z : Cn n) :
    Work.CR.Flat.dCoord j H z - Work.CR.Flat.dbarCoord j H z
      = -Complex.I * fderiv ℝ H z (Pi.single j (Complex.I : ℂ)) := by
  rw [Work.CR.Flat.dCoord, Work.CR.Flat.dbarCoord]; ring

/-- Leibniz rule for the perturbed `∂̄`-operator `dbarCn J`. -/
lemma dbarCn_mul {n : ℕ} (J : Cn n → Cn n →L[ℝ] Cn n) (f g : Cn n → ℂ) (z v : Cn n)
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dbarCn J (fun w => f w * g w) z v = f z * dbarCn J g z v + g z * dbarCn J f z v := by
  have hmul : (fun w => f w * g w) = f * g := by funext w; rw [Pi.mul_apply]
  have hfg : fderiv ℝ (fun w => f w * g w) z = f z • fderiv ℝ g z + g z • fderiv ℝ f z := by
    rw [hmul]
    have h := (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv
    simpa using h
  rw [dbarCn_apply, dbarCn_apply, dbarCn_apply, hfg]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Chain rule for the perturbed `∂̄`-operator on a power. -/
lemma dbarCn_pow_succ {n : ℕ} (J : Cn n → Cn n →L[ℝ] Cn n) (u : Cn n → ℂ) (z v : Cn n)
    (m : ℕ) (hu : DifferentiableAt ℝ u z) :
    dbarCn J (fun w => (u w) ^ (m + 1)) z v
      = ((m + 1 : ℕ) : ℂ) * (u z) ^ m * dbarCn J u z v := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hd : DifferentiableAt ℝ (fun w => (u w) ^ (m + 1)) z := hu.pow (m + 1)
    have hfun : (fun w => (u w) ^ (m + 1 + 1)) = fun w => (u w) ^ (m + 1) * u w := by
      funext w; rw [pow_succ]
    rw [hfun, dbarCn_mul J _ u z v hd hu, ih, pow_succ (u z) m]
    push_cast
    ring

/-- Chain rule for the flat `∂`-operator on a power. -/
lemma dCoord_pow_succ {n : ℕ} (j : Fin n) (u : Cn n → ℂ) (z : Cn n) (m : ℕ)
    (hu : DifferentiableAt ℝ u z) :
    Work.CR.Flat.dCoord j (fun w => (u w) ^ (m + 1)) z
      = ((m + 1 : ℕ) : ℂ) * (u z) ^ m * Work.CR.Flat.dCoord j u z := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hd : DifferentiableAt ℝ (fun w => (u w) ^ (m + 1)) z := hu.pow (m + 1)
    have hfun : (fun w => (u w) ^ (m + 1 + 1)) = fun w => (u w) ^ (m + 1) * u w := by
      funext w; rw [pow_succ]
    rw [hfun, Work.NN.Core.dCoord_mul j _ u z hd hu, ih, pow_succ (u z) m]
    push_cast
    ring

/-- Chain rule for the flat `∂̄`-operator on a power. -/
lemma dbarCoord_pow_succ {n : ℕ} (j : Fin n) (u : Cn n → ℂ) (z : Cn n) (m : ℕ)
    (hu : DifferentiableAt ℝ u z) :
    Work.CR.Flat.dbarCoord j (fun w => (u w) ^ (m + 1)) z
      = ((m + 1 : ℕ) : ℂ) * (u z) ^ m * Work.CR.Flat.dbarCoord j u z := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hd : DifferentiableAt ℝ (fun w => (u w) ^ (m + 1)) z := hu.pow (m + 1)
    have hfun : (fun w => (u w) ^ (m + 1 + 1)) = fun w => (u w) ^ (m + 1) * u w := by
      funext w; rw [pow_succ]
    rw [hfun, Work.CR.Flat.Polydisc.dbarCoord_mul j _ u z hd hu, ih, pow_succ (u z) m]
    push_cast
    ring



/-- Bound on the perturbed coefficient: if the `j`-th column of `A' z` is componentwise bounded by
`ε`, then `‖Lcoef A' H j z‖ ≤ ε Σ_i (‖∂_i H z‖ + ‖∂̄_i H z‖)`. -/
lemma Lcoef_norm_le {n : ℕ} {A' : Cn n → Cn n →L[ℝ] Cn n} {H : Cn n → ℂ} {z : Cn n}
    {ε : ℝ} (j : Fin n) (hA : ∀ i : Fin n, ‖A' z (Pi.single j (1 : ℂ)) i‖ ≤ ε) :
    ‖Lcoef A' H j z‖
      ≤ ε * ∑ i : Fin n, (‖Work.CR.Flat.dCoord i H z‖ + ‖Work.CR.Flat.dbarCoord i H z‖) := by
  set L : Cn n →L[ℝ] ℂ := fderiv ℝ H z with hL
  set w : Cn n := A' z (Pi.single j (1 : ℂ)) with hw
  have hdecomp : w = ∑ i : Fin n, ((w i).re • (Pi.single i (1 : ℂ) : Cn n)
      + (w i).im • (Pi.single i (Complex.I : ℂ) : Cn n)) := by
    rw [← Finset.univ_sum_single w]
    refine Finset.sum_congr rfl fun i _ => ?_
    ext m
    rcases eq_or_ne m i with rfl | hm
    · simp [Complex.re_add_im]
    · simp [Pi.single_eq_of_ne hm]
  have hLw : L w = ∑ i : Fin n, ((w i).re • L (Pi.single i (1 : ℂ))
      + (w i).im • L (Pi.single i (Complex.I : ℂ))) := by
    conv_lhs => rw [hdecomp]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_add, map_smul, map_smul]
  -- per-coordinate bounds
  have hc1 : ∀ i : Fin n, ‖L (Pi.single i (1 : ℂ))‖
      ≤ ‖Work.CR.Flat.dCoord i H z‖ + ‖Work.CR.Flat.dbarCoord i H z‖ := by
    intro i
    have := dCoord_add_dbarCoord i H z
    rw [← this]
    exact norm_add_le _ _
  have hc2 : ∀ i : Fin n, ‖L (Pi.single i (Complex.I : ℂ))‖
      ≤ ‖Work.CR.Flat.dCoord i H z‖ + ‖Work.CR.Flat.dbarCoord i H z‖ := by
    intro i
    have h := dCoord_sub_dbarCoord i H z
    have h2 : Complex.I * L (Pi.single i (Complex.I : ℂ))
        = -(Work.CR.Flat.dCoord i H z - Work.CR.Flat.dbarCoord i H z) := by
      rw [h]; ring
    have h3 : ‖L (Pi.single i (Complex.I : ℂ))‖
        = ‖Work.CR.Flat.dCoord i H z - Work.CR.Flat.dbarCoord i H z‖ := by
      have hI : ‖Complex.I * L (Pi.single i (Complex.I : ℂ))‖
          = ‖L (Pi.single i (Complex.I : ℂ))‖ := by
        rw [norm_mul, Complex.norm_I, one_mul]
      rw [← hI, h2, norm_neg]
    rw [h3]
    exact norm_sub_le _ _
  have hwi : ∀ i : Fin n, ‖w i‖ ≤ ε := by
    intro i
    rw [hw]
    exact hA i
  have hbound : ‖L w‖
      ≤ 2 * ε * ∑ i : Fin n, (‖Work.CR.Flat.dCoord i H z‖ + ‖Work.CR.Flat.dbarCoord i H z‖) := by
    rw [hLw]
    refine (norm_sum_le _ _).trans ?_
    have h2 : ∀ i ∈ Finset.univ,
        ‖(w i).re • L (Pi.single i (1 : ℂ)) + (w i).im • L (Pi.single i (Complex.I : ℂ))‖
          ≤ 2 * ε * (‖Work.CR.Flat.dCoord i H z‖ + ‖Work.CR.Flat.dbarCoord i H z‖) := by
      intro i _
      set c : ℝ := ‖Work.CR.Flat.dCoord i H z‖ + ‖Work.CR.Flat.dbarCoord i H z‖ with hc
      have hc0 : 0 ≤ c := by positivity
      have h3 : 0 ≤ ε := le_trans (norm_nonneg _) (hwi i)
      have h1 : |(w i).re| ≤ ε := le_trans (Complex.abs_re_le_norm (w i)) (hwi i)
      have h2 : |(w i).im| ≤ ε := le_trans (Complex.abs_im_le_norm (w i)) (hwi i)
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      have e1 : |(w i).re| * ‖L (Pi.single i (1 : ℂ))‖ ≤ ε * c :=
        mul_le_mul h1 (by rw [hc]; exact hc1 i) (norm_nonneg _) h3
      have e2 : |(w i).im| * ‖L (Pi.single i (Complex.I : ℂ))‖ ≤ ε * c :=
        mul_le_mul h2 (by rw [hc]; exact hc2 i) (norm_nonneg _) h3
      linarith
    calc ∑ i, ‖(w i).re • L (Pi.single i (1 : ℂ)) + (w i).im • L (Pi.single i (Complex.I : ℂ))‖
        ≤ ∑ i, 2 * ε * (‖Work.CR.Flat.dCoord i H z‖ + ‖Work.CR.Flat.dbarCoord i H z‖) :=
          Finset.sum_le_sum h2
      _ = 2 * ε * ∑ i : Fin n, (‖Work.CR.Flat.dCoord i H z‖
            + ‖Work.CR.Flat.dbarCoord i H z‖) := by rw [Finset.mul_sum]
  have hfin : ‖Lcoef A' H j z‖
      ≤ ε * ∑ i : Fin n, (‖Work.CR.Flat.dCoord i H z‖ + ‖Work.CR.Flat.dbarCoord i H z‖) := by
    have hLc : Lcoef A' H j z = (Complex.I / 2) * L w := by
      simp only [Lcoef, hL, hw]
    calc ‖Lcoef A' H j z‖ = ‖(Complex.I / 2) * L w‖ := by rw [hLc]
      _ = (1 / 2) * ‖L w‖ := by rw [norm_mul]; norm_num
      _ ≤ (1 / 2) * (2 * ε * ∑ i : Fin n, (‖Work.CR.Flat.dCoord i H z‖
            + ‖Work.CR.Flat.dbarCoord i H z‖)) :=
          mul_le_mul_of_nonneg_left hbound (by norm_num)
      _ = ε * ∑ i : Fin n, (‖Work.CR.Flat.dCoord i H z‖ + ‖Work.CR.Flat.dbarCoord i H z‖) := by
          ring
  exact hfin



/-- Continuity of the perturbed `∂̄`-coefficient function. -/
lemma continuous_dbarCn_apply {n : ℕ} {J : Cn n → Cn n →L[ℝ] Cn n} (hJ : Continuous J)
    {H : Cn n → ℂ} (hH : ContDiff ℝ 1 H) (v : Cn n) :
    Continuous (fun z => dbarCn J H z v) := by
  have hfd : Continuous (fun z : Cn n => fderiv ℝ H z) := hH.continuous_fderiv (by norm_num)
  have h1 : Continuous (fun z : Cn n => fderiv ℝ H z v) := hfd.clm_apply continuous_const
  have h2 : Continuous (fun z : Cn n => J z v) := hJ.clm_apply continuous_const
  have h3 : Continuous (fun z : Cn n => fderiv ℝ H z (J z v)) := hfd.clm_apply h2
  rw [show (fun z => dbarCn J H z v)
      = fun z => (1 / 2 : ℂ) * (fderiv ℝ H z v + Complex.I * fderiv ℝ H z (J z v)) from by
    funext z; exact dbarCn_apply J H z v]
  exact continuous_const.mul (h1.add (continuous_const.mul h3))

/-- **Perturbed weighted energy estimate.**

For `η, H : ℂⁿ → ℂ` of class `C¹` (at least one of them with compact support), if the
`(0,1)`-energy of `H` can be measured against the *perturbed* `∂̄`-energy
`Y(z) = Σ_j ‖∂̄_{Jstd+A'} H(z)(e_j)‖²` through

  `Σ_j ‖∂̄_j H(z)‖² ≤ 2 Y(z) + c · Σ_j (‖∂_j H(z)‖² + ‖∂̄_j H(z)‖²)`

with `6 c ≤ 1/2`, then

  `∫ η² Σ_j(‖∂_j H‖² + ‖∂̄_j H‖²) ≤ 20 ∫ η² Y + 8 ∫ ‖H‖² Σ_j(‖∂_j η‖² + ‖∂̄_j η‖²)`.

The pointwise smallness hypothesis is supplied by `Lcoef_norm_le`: the perturbed `∂̄` differs from
the flat one by the first-order term `Lcoef`, whose size is controlled by the componentwise bound
`‖A' z e_i j‖ ≤ ε` on the support of `η`, yielding `c = 4 n² ε²`. -/
theorem weightedEnergyPerturbed {n : ℕ} {η H : Cn n → ℂ}
    {A' : Cn n → Cn n →L[ℝ] Cn n} {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : 24 * (n : ℝ) ^ 2 * ε ^ 2 ≤ 1 / 2)
    (hη : ContDiff ℝ 1 η) (hH : ContDiff ℝ 1 H)
    (hηcs : HasCompactSupport η) (hHcs : HasCompactSupport H)
    (hA'cont : Continuous A')
    (hAsm : ∀ z ∈ tsupport η, ∀ i j : Fin n, ‖A' z (Pi.single i 1) j‖ ≤ ε) :
    (∫ z, ‖η z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j H z‖ ^ 2
        + ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2)))
      ≤ 20 * (∫ z, ‖η z‖ ^ 2 * (∑ j : Fin n,
              ‖dbarCn (JstdCn n + A') H z (Pi.single j (1 : ℂ))‖ ^ 2))
        + 8 * (∫ z, ‖H z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j η z‖ ^ 2
              + ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2))) := by
  classical
  set c : ℝ := 4 * (n : ℝ) ^ 2 * ε ^ 2 with hcdef
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  have hc12 : 6 * c ≤ 1 / 2 := by rw [hcdef]; linarith [hε]
  have hc1 : c ≤ 1 := by linarith [hc12, hc0]
  set fA : Cn n → ℝ := fun z => ∑ j : Fin n, ‖Work.CR.Flat.dCoord j H z‖ ^ 2 with hfA
  set fB : Cn n → ℝ := fun z => ∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2 with hfB
  set gA : Cn n → ℝ := fun z => ∑ j : Fin n, ‖Work.CR.Flat.dCoord j η z‖ ^ 2 with hgA
  set gB : Cn n → ℝ := fun z => ∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2 with hgB
  set Y : Cn n → ℝ := fun z => ∑ j : Fin n,
      ‖dbarCn (JstdCn n + A') H z (Pi.single j (1 : ℂ))‖ ^ 2 with hY
  set u : Cn n → ℂ := fun w => η w * H w with hu
  set Phi1 : Cn n → ℝ := fun z => ∑ j : Fin n, ‖Work.CR.Flat.dCoord j u z‖ ^ 2 with hPhi1
  set Phi2 : Cn n → ℝ := fun z => ∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j u z‖ ^ 2 with hPhi2
  have hfAc : Continuous fA := by
    rw [hfA]; exact continuous_finsetSum _ (fun j _ => (continuous_dCoord j hH).norm.pow 2)
  have hfBc : Continuous fB := by
    rw [hfB]; exact continuous_finsetSum _ (fun j _ => (continuous_dbarCoord j hH).norm.pow 2)
  have hgAc : Continuous gA := by
    rw [hgA]; exact continuous_finsetSum _ (fun j _ => (continuous_dCoord j hη).norm.pow 2)
  have hgBc : Continuous gB := by
    rw [hgB]; exact continuous_finsetSum _ (fun j _ => (continuous_dbarCoord j hη).norm.pow 2)
  have hJ' : Continuous (fun z : Cn n => (JstdCn n + A') z) := by
    have heq : (fun z : Cn n => (JstdCn n + A') z) = fun z => JstdCn n z + A' z := by
      funext z; simp [Pi.add_apply]
    rw [heq]
    exact (continuous_const : Continuous (fun z : Cn n => JstdCn n z)).add hA'cont
  have hYcont : Continuous Y := by
    rw [hY]
    exact continuous_finsetSum _ (fun j _ =>
      (continuous_dbarCn_apply hJ' hH (Pi.single j (1 : ℂ))).norm.pow 2)
  have hu_ct : ContDiff ℝ 1 u := by rw [hu]; exact hη.mul hH
  have hu_cs : HasCompactSupport u := by rw [hu]; exact hηcs.mul_right
  have hInt_L : Integrable (fun z => ‖η z‖ ^ 2 * fA z) :=
    integrable_normSq_mul hη.continuous hfAc hηcs
  have hInt_LB : Integrable (fun z => ‖η z‖ ^ 2 * fB z) :=
    integrable_normSq_mul hη.continuous hfBc hηcs
  have hInt_Ma : Integrable (fun z => ‖H z‖ ^ 2 * gA z) :=
    integrable_normSq_mul hH.continuous hgAc hHcs
  have hInt_Mb : Integrable (fun z => ‖H z‖ ^ 2 * gB z) :=
    integrable_normSq_mul hH.continuous hgBc hHcs
  have hInt_M : Integrable (fun z => ‖H z‖ ^ 2 * (gA z + gB z)) :=
    integrable_normSq_mul hH.continuous (hgAc.add hgBc) hHcs
  have hInt_P1 : Integrable Phi1 := by rw [hPhi1]; exact integrable_sum_sq_dCoord hu_ct hu_cs
  have hInt_P2 : Integrable Phi2 := by rw [hPhi2]; exact integrable_sum_sq_dbarCoord hu_ct hu_cs
  have hInt_Y : Integrable (fun z => ‖η z‖ ^ 2 * Y z) := by
    have hcont : Continuous (fun z => ‖η z‖ ^ 2 * Y z) := (hη.continuous.norm.pow 2).mul hYcont
    have hsub : tsupport (fun z : Cn n => ‖η z‖ ^ 2 * Y z) ⊆ tsupport η := by
      rw [tsupport, tsupport]
      refine closure_mono ?_
      intro z hz
      rw [Function.mem_support] at hz ⊢
      intro hz0
      exact hz (by rw [hz0, norm_zero]; ring)
    exact Continuous.integrable_of_hasCompactSupport hcont
      (IsCompact.of_isClosed_subset hηcs (isClosed_tsupport _) hsub)
  -- Pointwise product expansion
  have hperD : ∀ z j, ‖η z‖ ^ 2 * ‖Work.CR.Flat.dCoord j H z‖ ^ 2
      ≤ 2 * ‖Work.CR.Flat.dCoord j u z‖ ^ 2
        + 2 * (‖H z‖ ^ 2 * ‖Work.CR.Flat.dCoord j η z‖ ^ 2) := by
    intro z j
    have hηd : DifferentiableAt ℝ η z := hη.differentiable_one z
    have hHd : DifferentiableAt ℝ H z := hH.differentiable_one z
    have hpr : Work.CR.Flat.dCoord j u z
        = Work.CR.Flat.dCoord j η z * H z + η z * Work.CR.Flat.dCoord j H z := by
      rw [hu]; exact Work.NN.Core.dCoord_mul j η H z hηd hHd
    have heq : η z * Work.CR.Flat.dCoord j H z
        = Work.CR.Flat.dCoord j u z - H z * Work.CR.Flat.dCoord j η z := by
      rw [hpr]; ring
    have hnorm : ‖η z‖ * ‖Work.CR.Flat.dCoord j H z‖
        = ‖Work.CR.Flat.dCoord j u z - H z * Work.CR.Flat.dCoord j η z‖ := by
      rw [← norm_mul, heq]
    have hle : ‖η z‖ * ‖Work.CR.Flat.dCoord j H z‖
        ≤ ‖Work.CR.Flat.dCoord j u z‖ + ‖H z‖ * ‖Work.CR.Flat.dCoord j η z‖ := by
      rw [hnorm]
      calc ‖Work.CR.Flat.dCoord j u z - H z * Work.CR.Flat.dCoord j η z‖
          ≤ ‖Work.CR.Flat.dCoord j u z‖ + ‖H z * Work.CR.Flat.dCoord j η z‖ := norm_sub_le _ _
        _ = ‖Work.CR.Flat.dCoord j u z‖ + ‖H z‖ * ‖Work.CR.Flat.dCoord j η z‖ := by rw [norm_mul]
    have hsq := sq_le_two_sq_add_two_sq (a := ‖η z‖ * ‖Work.CR.Flat.dCoord j H z‖)
      (b := ‖Work.CR.Flat.dCoord j u z‖) (c := ‖H z‖ * ‖Work.CR.Flat.dCoord j η z‖)
      (by positivity) (norm_nonneg _) (by positivity) hle
    rw [mul_pow, mul_pow] at hsq
    exact hsq
  have hperB : ∀ z j, ‖Work.CR.Flat.dbarCoord j u z‖ ^ 2
      ≤ 2 * (‖η z‖ ^ 2 * ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2)
        + 2 * (‖H z‖ ^ 2 * ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2) := by
    intro z j
    have hηd : DifferentiableAt ℝ η z := hη.differentiable_one z
    have hHd : DifferentiableAt ℝ H z := hH.differentiable_one z
    have hpr : Work.CR.Flat.dbarCoord j u z
        = Work.CR.Flat.dbarCoord j η z * H z + η z * Work.CR.Flat.dbarCoord j H z := by
      rw [hu]; exact Work.CR.Flat.Polydisc.dbarCoord_mul j η H z hηd hHd
    have hnorm : ‖Work.CR.Flat.dbarCoord j u z‖
        ≤ ‖η z‖ * ‖Work.CR.Flat.dbarCoord j H z‖ + ‖H z‖ * ‖Work.CR.Flat.dbarCoord j η z‖ := by
      rw [hpr]
      calc ‖Work.CR.Flat.dbarCoord j η z * H z + η z * Work.CR.Flat.dbarCoord j H z‖
          ≤ ‖Work.CR.Flat.dbarCoord j η z * H z‖ + ‖η z * Work.CR.Flat.dbarCoord j H z‖ :=
            norm_add_le _ _
        _ = ‖η z‖ * ‖Work.CR.Flat.dbarCoord j H z‖ + ‖H z‖ * ‖Work.CR.Flat.dbarCoord j η z‖ := by
            rw [norm_mul, norm_mul]; ring
    have hsq := sq_le_two_sq_add_two_sq (norm_nonneg _) (by positivity) (by positivity) hnorm
    rw [mul_pow, mul_pow] at hsq
    exact hsq
  have hpt1 : ∀ z : Cn n, ‖η z‖ ^ 2 * fA z ≤ 2 * Phi1 z + 2 * (‖H z‖ ^ 2 * gA z) := by
    intro z
    have hsum : ∑ j : Fin n, ‖η z‖ ^ 2 * ‖Work.CR.Flat.dCoord j H z‖ ^ 2
        ≤ ∑ j : Fin n, (2 * ‖Work.CR.Flat.dCoord j u z‖ ^ 2
            + 2 * (‖H z‖ ^ 2 * ‖Work.CR.Flat.dCoord j η z‖ ^ 2)) :=
      Finset.sum_le_sum (fun j _ => hperD z j)
    have e1 : ‖η z‖ ^ 2 * fA z = ∑ j : Fin n, ‖η z‖ ^ 2 * ‖Work.CR.Flat.dCoord j H z‖ ^ 2 := by
      rw [hfA, Finset.mul_sum]
    have e2 : (∑ j : Fin n, (2 * ‖Work.CR.Flat.dCoord j u z‖ ^ 2
            + 2 * (‖H z‖ ^ 2 * ‖Work.CR.Flat.dCoord j η z‖ ^ 2)))
        = 2 * Phi1 z + 2 * (‖H z‖ ^ 2 * gA z) := by
      simp only [hPhi1, hgA, Finset.sum_add_distrib, Finset.mul_sum]
    rw [e1]
    exact le_trans hsum (le_of_eq e2)
  have hpt2 : ∀ z : Cn n, Phi2 z ≤ 2 * (‖η z‖ ^ 2 * fB z) + 2 * (‖H z‖ ^ 2 * gB z) := by
    intro z
    have hsum : ∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j u z‖ ^ 2
        ≤ ∑ j : Fin n, (2 * (‖η z‖ ^ 2 * ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2)
            + 2 * (‖H z‖ ^ 2 * ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2)) :=
      Finset.sum_le_sum (fun j _ => hperB z j)
    have e1 : Phi2 z = ∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j u z‖ ^ 2 := by rw [hPhi2]
    have e2 : (∑ j : Fin n, (2 * (‖η z‖ ^ 2 * ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2)
            + 2 * (‖H z‖ ^ 2 * ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2)))
        = 2 * (‖η z‖ ^ 2 * fB z) + 2 * (‖H z‖ ^ 2 * gB z) := by
      simp only [hfB, hgB, Finset.sum_add_distrib, Finset.mul_sum]
    rw [e1]
    exact le_trans hsum (le_of_eq e2)
  -- Pointwise smallness of the `(0,1)`-energy against the perturbed energy
  have hBsq : ∀ z : Cn n, (1 - c) * (‖η z‖ ^ 2 * fB z)
      ≤ 2 * (‖η z‖ ^ 2 * Y z) + c * (‖η z‖ ^ 2 * fA z) := by
    intro z
    by_cases hz : z ∈ Function.support η
    · have hzts : z ∈ tsupport η := subset_closure hz
      set S : ℝ := ∑ i : Fin n, (‖Work.CR.Flat.dCoord i H z‖ + ‖Work.CR.Flat.dbarCoord i H z‖)
        with hS
      have hS2 : S ^ 2 ≤ 2 * (n : ℝ) * (fA z + fB z) := by
        have h1 := sq_sum_le_card_mul_sum_sq
          (s := Finset.univ)
          (f := fun i : Fin n => (‖Work.CR.Flat.dCoord i H z‖ + ‖Work.CR.Flat.dbarCoord i H z‖))
        rw [Finset.card_univ, Fintype.card_fin] at h1
        have h2 : ∑ i : Fin n, (‖Work.CR.Flat.dCoord i H z‖
              + ‖Work.CR.Flat.dbarCoord i H z‖) ^ 2
            ≤ ∑ i : Fin n, 2 * (‖Work.CR.Flat.dCoord i H z‖ ^ 2
                + ‖Work.CR.Flat.dbarCoord i H z‖ ^ 2) :=
          Finset.sum_le_sum (fun i _ => by
            nlinarith [sq_nonneg (‖Work.CR.Flat.dCoord i H z‖ - ‖Work.CR.Flat.dbarCoord i H z‖)])
        have h3 : ∑ i : Fin n, 2 * (‖Work.CR.Flat.dCoord i H z‖ ^ 2
              + ‖Work.CR.Flat.dbarCoord i H z‖ ^ 2) = 2 * (fA z + fB z) := by
          simp only [hfA, hfB, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
        rw [hS]
        calc (∑ i : Fin n, (‖Work.CR.Flat.dCoord i H z‖
                + ‖Work.CR.Flat.dbarCoord i H z‖)) ^ 2
            ≤ (n:ℝ) * ∑ i : Fin n, (‖Work.CR.Flat.dCoord i H z‖
                + ‖Work.CR.Flat.dbarCoord i H z‖) ^ 2 := h1
          _ ≤ (n:ℝ) * (2 * (fA z + fB z)) := by
                exact mul_le_mul_of_nonneg_left (h2.trans (le_of_eq h3)) (Nat.cast_nonneg n)
          _ = 2 * (n:ℝ) * (fA z + fB z) := by ring
      have hstep : ∀ j : Fin n, ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2
          ≤ 2 * ‖dbarCn (JstdCn n + A') H z (Pi.single j (1 : ℂ))‖ ^ 2 + 2 * (ε * S) ^ 2 := by
        intro j
        have hlin : Work.CR.Flat.dbarCoord j H z
            = dbarCn (JstdCn n + A') H z (Pi.single j (1 : ℂ)) - Lcoef A' H j z := by
          have := dbarCoef_lin A' H j z
          rw [this]; ring
        have hLc : ‖Lcoef A' H j z‖ ≤ ε * S := by
          rw [hS]
          exact Lcoef_norm_le (A' := A') (H := H) (z := z) (ε := ε) j (fun i => hAsm z hzts j i)
        have hb : ‖Work.CR.Flat.dbarCoord j H z‖
            ≤ ‖dbarCn (JstdCn n + A') H z (Pi.single j (1 : ℂ))‖ + ε * S := by
          rw [hlin]
          exact (norm_sub_le _ _).trans (add_le_add le_rfl hLc)
        exact sq_le_two_sq_add_two_sq (norm_nonneg _) (norm_nonneg _) (by positivity) hb
      have hsum : fB z ≤ 2 * Y z + 2 * (n:ℝ) * (ε * S) ^ 2 := by
        simp only [hfB, hY]
        refine (Finset.sum_le_sum (fun j _ => hstep j)).trans (le_of_eq ?_)
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [Finset.mul_sum]
        · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      have hkey : fB z ≤ 2 * Y z + c * (fA z + fB z) := by
        have h4 : 2 * (n:ℝ) * (ε * S) ^ 2 ≤ 2 * (n:ℝ) * ε ^ 2 * (2 * (n:ℝ) * (fA z + fB z)) := by
          have h5 : (ε * S) ^ 2 = ε ^ 2 * S ^ 2 := by ring
          rw [h5]
          have h6 : 0 ≤ 2 * (n:ℝ) * ε ^ 2 := by positivity
          calc 2 * (n:ℝ) * (ε ^ 2 * S ^ 2) = (2 * (n:ℝ) * ε ^ 2) * S ^ 2 := by ring_nf
            _ ≤ (2 * (n:ℝ) * ε ^ 2) * (2 * (n:ℝ) * (fA z + fB z)) :=
                mul_le_mul_of_nonneg_left hS2 h6
            _ = 2 * (n:ℝ) * ε ^ 2 * (2 * (n:ℝ) * (fA z + fB z)) := by ring
        have h7 : 2 * (n:ℝ) * ε ^ 2 * (2 * (n:ℝ) * (fA z + fB z)) = c * (fA z + fB z) := by
          rw [hcdef]; ring
        linarith [hsum, h4, le_of_eq h7]
      have hηn : 0 ≤ ‖η z‖ ^ 2 := sq_nonneg _
      have h1 : (1 - c) * fB z ≤ 2 * Y z + c * fA z := by linarith [hkey]
      have h2 := mul_le_mul_of_nonneg_right h1 hηn
      nlinarith [h2]
    · simp only [Function.mem_support, not_not] at hz
      rw [hz, norm_zero]; simp
  -- Zero order: integrate the product bounds
  have hL_le : ∫ z, ‖η z‖ ^ 2 * fA z
      ≤ 2 * (∫ z, Phi1 z) + 2 * (∫ z, ‖H z‖ ^ 2 * gA z) := by
    have h := integral_mono hInt_L ((hInt_P1.const_mul 2).add (hInt_Ma.const_mul 2)) hpt1
    simp only [Pi.add_apply] at h
    rw [integral_add (hInt_P1.const_mul 2) (hInt_Ma.const_mul 2), integral_const_mul,
      integral_const_mul] at h
    exact h
  have hP_le : ∫ z, Phi2 z
      ≤ 2 * (∫ z, ‖η z‖ ^ 2 * fB z) + 2 * (∫ z, ‖H z‖ ^ 2 * gB z) := by
    have h := integral_mono hInt_P2 ((hInt_LB.const_mul 2).add (hInt_Mb.const_mul 2)) hpt2
    simp only [Pi.add_apply] at h
    rw [integral_add (hInt_LB.const_mul 2) (hInt_Mb.const_mul 2), integral_const_mul,
      integral_const_mul] at h
    exact h
  have hP_eq : (∫ z, Phi1 z) = (∫ z, Phi2 z) := by
    have h := integral_normSq_dCoord_eq_dbarCoord hu_ct hu_cs
    simpa only [hPhi1, hPhi2] using h
  have hQA_le : ∫ z, ‖η z‖ ^ 2 * fA z
      ≤ 4 * (∫ z, ‖η z‖ ^ 2 * fB z) + 4 * (∫ z, ‖H z‖ ^ 2 * gB z)
        + 2 * (∫ z, ‖H z‖ ^ 2 * gA z) := by linarith [hL_le, hP_le, hP_eq]
  have hQB_le : (1 - c) * (∫ z, ‖η z‖ ^ 2 * fB z)
      ≤ 2 * (∫ z, ‖η z‖ ^ 2 * Y z) + c * (∫ z, ‖η z‖ ^ 2 * fA z) := by
    have h := integral_mono (hInt_LB.const_mul (1 - c))
      ((hInt_Y.const_mul 2).add (hInt_L.const_mul c)) hBsq
    simp only [Pi.add_apply] at h
    rw [integral_add (hInt_Y.const_mul 2) (hInt_L.const_mul c), integral_const_mul,
      integral_const_mul, integral_const_mul] at h
    exact h
  -- Assembly
  have hXsplit : ∫ z, ‖η z‖ ^ 2 * (fA z + fB z)
      = (∫ z, ‖η z‖ ^ 2 * fA z) + ∫ z, ‖η z‖ ^ 2 * fB z := by
    rw [← integral_add hInt_L hInt_LB]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    ring
  have hXnneg : 0 ≤ ∫ z, ‖η z‖ ^ 2 * (fA z + fB z) := by
    have h := integral_nonneg (μ := volume) (f := fun z => ‖η z‖ ^ 2 * (fA z + fB z))
      (fun z => by
        have h1 : 0 ≤ fA z := by rw [hfA]; positivity
        have h2 : 0 ≤ fB z := by rw [hfB]; positivity
        positivity)
    exact h
  have hMA : 0 ≤ ∫ z, ‖H z‖ ^ 2 * gA z :=
    integral_nonneg (fun z => by
      have h1 : 0 ≤ gA z := by rw [hgA]; positivity
      positivity)
  have hMB : 0 ≤ ∫ z, ‖H z‖ ^ 2 * gB z :=
    integral_nonneg (fun z => by
      have h1 : 0 ≤ gB z := by rw [hgB]; positivity
      positivity)
  have hkey : ∫ z, ‖η z‖ ^ 2 * (fA z + fB z)
      ≤ 20 * (∫ z, ‖η z‖ ^ 2 * Y z) + 8 * (∫ z, ‖H z‖ ^ 2 * (gA z + gB z)) := by
    have h5 : (1 - 6 * c) * (∫ z, ‖η z‖ ^ 2 * (fA z + fB z))
        ≤ 10 * (∫ z, ‖η z‖ ^ 2 * Y z)
          + (4 * (∫ z, ‖H z‖ ^ 2 * gB z) + 2 * (∫ z, ‖H z‖ ^ 2 * gA z)) := by
      have e1 : (1 - c) * (∫ z, ‖η z‖ ^ 2 * (fA z + fB z))
          ≤ (1 - c) * (5 * (∫ z, ‖η z‖ ^ 2 * fB z)
              + 4 * (∫ z, ‖H z‖ ^ 2 * gB z) + 2 * (∫ z, ‖H z‖ ^ 2 * gA z)) :=
        mul_le_mul_of_nonneg_left (by linarith [hQA_le, hXsplit]) (by linarith [hc0])
      have e2 : (1 - c) * (5 * (∫ z, ‖η z‖ ^ 2 * fB z))
          ≤ 5 * (2 * (∫ z, ‖η z‖ ^ 2 * Y z) + c * (∫ z, ‖η z‖ ^ 2 * fA z)) := by
        have h := mul_le_mul_of_nonneg_left hQB_le (by norm_num : (0:ℝ) ≤ 5)
        linarith [h]
      have e3 : (∫ z, ‖η z‖ ^ 2 * fA z) ≤ ∫ z, ‖η z‖ ^ 2 * (fA z + fB z) := by
        rw [hXsplit]; linarith [integral_nonneg (μ := volume)
          (f := fun z => ‖η z‖ ^ 2 * fB z) (fun z => by
            have h1 : 0 ≤ fB z := by rw [hfB]; positivity
            positivity)]
      nlinarith [e1, e2, e3, hc0]
    have h6 : (1:ℝ) / 2 ≤ 1 - 6 * c := by linarith [hc12]
    have h7 : (1/2) * (∫ z, ‖η z‖ ^ 2 * (fA z + fB z))
        ≤ (1 - 6 * c) * (∫ z, ‖η z‖ ^ 2 * (fA z + fB z)) :=
      mul_le_mul_of_nonneg_right h6 hXnneg
    have h8 : 8 * (∫ z, ‖H z‖ ^ 2 * gB z) + 4 * (∫ z, ‖H z‖ ^ 2 * gA z)
        ≤ 8 * (∫ z, ‖H z‖ ^ 2 * gA z) + 8 * (∫ z, ‖H z‖ ^ 2 * gB z) := by linarith [hMA]
    have h9 : ∫ z, ‖H z‖ ^ 2 * (gA z + gB z)
        = (∫ z, ‖H z‖ ^ 2 * gA z) + (∫ z, ‖H z‖ ^ 2 * gB z) := by
      rw [← integral_add hInt_Ma hInt_Mb]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      ring
    linarith [h5, h7, h8, h9]
  -- Rewriting back to the displayed form
  have hLHS_eq : (∫ z, ‖η z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j H z‖ ^ 2
        + ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2)))
      = ∫ z, ‖η z‖ ^ 2 * (fA z + fB z) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only [hfA, hfB, Finset.sum_add_distrib]
  have hY_eq : (∫ z, ‖η z‖ ^ 2 * (∑ j : Fin n,
        ‖dbarCn (JstdCn n + A') H z (Pi.single j (1 : ℂ))‖ ^ 2))
      = ∫ z, ‖η z‖ ^ 2 * Y z := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only [hY]
  have hM_eq : (∫ z, ‖H z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j η z‖ ^ 2
        + ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2)))
      = ∫ z, ‖H z‖ ^ 2 * (gA z + gB z) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only [hgA, hgB, Finset.sum_add_distrib]
  rw [hLHS_eq, hY_eq, hM_eq]
  exact hkey



/-! ## Further auxiliary lemmas for the main theorem -/

/-- `∂_j` depends only on the germ of the function. -/
lemma dCoord_congr_of_eventuallyEq {n : ℕ} (j : Fin n) {f g : Cn n → ℂ} {z : Cn n}
    (h : f =ᶠ[𝓝 z] g) : Work.CR.Flat.dCoord j f z = Work.CR.Flat.dCoord j g z := by
  rw [Work.CR.Flat.dCoord, Work.CR.Flat.dCoord, h.fderiv_eq]

/-- `∂̄_j` depends only on the germ of the function. -/
lemma dbarCoord_congr_of_eventuallyEq {n : ℕ} (j : Fin n) {f g : Cn n → ℂ} {z : Cn n}
    (h : f =ᶠ[𝓝 z] g) : Work.CR.Flat.dbarCoord j f z = Work.CR.Flat.dbarCoord j g z := by
  rw [Work.CR.Flat.dbarCoord, Work.CR.Flat.dbarCoord, h.fderiv_eq]

/-- Chain rule for `∂_j` on a power, in the form valid for all `k`. -/
lemma dCoord_pow {n : ℕ} (j : Fin n) (u : Cn n → ℂ) (z : Cn n) (k : ℕ)
    (hu : DifferentiableAt ℝ u z) :
    Work.CR.Flat.dCoord j (fun w => (u w) ^ k) z
      = (k : ℂ) * (u z) ^ (k - 1) * Work.CR.Flat.dCoord j u z := by
  rcases k with _ | m
  · simp [Work.CR.Flat.dCoord]
  · rw [dCoord_pow_succ j u z m hu, Nat.succ_sub_one]

/-- Chain rule for `∂̄_j` on a power, in the form valid for all `k`. -/
lemma dbarCoord_pow {n : ℕ} (j : Fin n) (u : Cn n → ℂ) (z : Cn n) (k : ℕ)
    (hu : DifferentiableAt ℝ u z) :
    Work.CR.Flat.dbarCoord j (fun w => (u w) ^ k) z
      = (k : ℂ) * (u z) ^ (k - 1) * Work.CR.Flat.dbarCoord j u z := by
  rcases k with _ | m
  · simp [Work.CR.Flat.dbarCoord]
  · rw [dbarCoord_pow_succ j u z m hu, Nat.succ_sub_one]

/-- Chain rule for the perturbed `∂̄`-operator on a power, valid for all `k`. -/
lemma dbarCn_pow {n : ℕ} (J : Cn n → Cn n →L[ℝ] Cn n) (u : Cn n → ℂ) (z v : Cn n)
    (k : ℕ) (hu : DifferentiableAt ℝ u z) :
    dbarCn J (fun w => (u w) ^ k) z v
      = (k : ℂ) * (u z) ^ (k - 1) * dbarCn J u z v := by
  rcases k with _ | m
  · have h1 : (fun w : Cn n => (u w) ^ 0) = fun _ => (1 : ℂ) := by funext w; rw [pow_zero]
    rw [h1, dbarCn_apply]
    simp
  · rw [dbarCn_pow_succ J u z v m hu, Nat.succ_sub_one]

/-- The power of a `C¹` function on a set is `C¹`. -/
lemma contDiffOn_pow {n : ℕ} {u : Cn n → ℂ} {s : Set (Cn n)} (hu : ContDiffOn ℝ 1 u s)
    (k : ℕ) : ContDiffOn ℝ 1 (fun z => (u z) ^ k) s := by
  induction k with
  | zero =>
    have : (fun z : Cn n => (u z) ^ 0) = fun _ => (1 : ℂ) := by funext z; rw [pow_zero]
    rw [this]; exact contDiffOn_const
  | succ m ih =>
    have h := ih.mul hu
    refine h.congr fun z _ => ?_
    rw [pow_succ]

/-- The topological support of `z ↦ (φ z : ℂ)` is that of `φ`. -/
lemma tsupport_ofReal {n : ℕ} (φ : Cn n → ℝ) :
    tsupport (fun z => (φ z : ℂ)) = tsupport φ := by
  rw [tsupport, tsupport]
  congr 1
  ext z
  simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero]

/-- A smooth compactly supported function times a function that is `C¹` on an open set containing
its support is `C¹`. -/
lemma contDiff_mul_of_tsupp_subset {n : ℕ} {χ u : Cn n → ℂ} {U : Set (Cn n)}
    (hU : IsOpen U) (hχ : ContDiff ℝ 1 χ) (hχcs : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ U) (hu : ContDiffOn ℝ 1 u U) :
    ContDiff ℝ 1 (fun z => χ z * u z) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · have hux : ContDiffAt ℝ 1 u x := hu.contDiffAt (hU.mem_nhds hx)
    exact hχ.contDiffAt.mul hux
  · have hx' : x ∉ tsupport χ := fun h => hx (hχU h)
    have hnhds : (tsupport χ)ᶜ ∈ 𝓝 x := (isClosed_tsupport χ).isOpen_compl.mem_nhds hx'
    have hev : (fun z => χ z * u z) =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
      filter_upwards [hnhds] with z hz
      have hz0 : χ z = 0 := by
        by_contra h
        exact hz (subset_closure (Function.mem_support.mpr h))
      rw [hz0, zero_mul]
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hev

/-- The norm of the Fréchet-derivative of a real function viewed in `ℂ` is bounded by that of the
real derivative. -/
lemma norm_fderiv_ofReal_le {n : ℕ} {φ : Cn n → ℝ} {z : Cn n} (hφ : DifferentiableAt ℝ φ z) :
    ‖fderiv ℝ (fun w => (φ w : ℂ)) z‖ ≤ ‖fderiv ℝ φ z‖ := by
  have h1 : HasFDerivAt φ (fderiv ℝ φ z) z := hφ.hasFDerivAt
  have h2 : HasFDerivAt (fun x : ℝ => (x : ℂ)) (Complex.ofRealCLM : ℝ →L[ℝ] ℂ) (φ z) :=
    Complex.ofRealCLM.hasFDerivAt
  have h3 : HasFDerivAt (fun w : Cn n => (φ w : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ φ z)) z := h2.comp z h1
  rw [h3.fderiv]
  have h4 : ‖Complex.ofRealCLM.comp (fderiv ℝ φ z)‖
      ≤ ‖Complex.ofRealCLM‖ * ‖fderiv ℝ φ z‖ := ContinuousLinearMap.opNorm_comp_le _ _
  have h5 : ‖Complex.ofRealCLM‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun v => ?_)
    simp only [Complex.ofRealCLM_apply, one_mul]
    rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs, Real.norm_eq_abs]
  refine h4.trans ?_
  calc ‖Complex.ofRealCLM‖ * ‖fderiv ℝ φ z‖ ≤ 1 * ‖fderiv ℝ φ z‖ :=
        mul_le_mul_of_nonneg_right h5 (norm_nonneg _)
    _ = ‖fderiv ℝ φ z‖ := by rw [one_mul]

/-- Bound of the flat `∂`/`∂̄` energy of `z ↦ (φ z : ℂ)` by that of `φ`. -/
lemma sum_dCoord_ofReal_le {n : ℕ} {φ : Cn n → ℝ} {z : Cn n}
    (hφ : DifferentiableAt ℝ φ z) :
    (∑ j : Fin n, (‖Work.CR.Flat.dCoord j (fun w => (φ w : ℂ)) z‖ ^ 2
        + ‖Work.CR.Flat.dbarCoord j (fun w => (φ w : ℂ)) z‖ ^ 2))
      ≤ 2 * (n : ℝ) * ‖fderiv ℝ φ z‖ ^ 2 := by
  have hnorm := norm_fderiv_ofReal_le hφ
  calc ∑ j : Fin n, (‖Work.CR.Flat.dCoord j (fun w => (φ w : ℂ)) z‖ ^ 2
          + ‖Work.CR.Flat.dbarCoord j (fun w => (φ w : ℂ)) z‖ ^ 2)
      ≤ ∑ _j : Fin n, 2 * ‖fderiv ℝ φ z‖ ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h1 : ‖Work.CR.Flat.dCoord j (fun w => (φ w : ℂ)) z‖ ≤ ‖fderiv ℝ φ z‖ :=
          le_trans (Work.NN.Core.norm_dCoord_le j _ z) hnorm
        have h2 : ‖Work.CR.Flat.dbarCoord j (fun w => (φ w : ℂ)) z‖ ≤ ‖fderiv ℝ φ z‖ :=
          le_trans (Work.NN.Core.norm_dbarCoord_le j _ z) hnorm
        have ha := norm_nonneg (Work.CR.Flat.dCoord j (fun w => (φ w : ℂ)) z)
        have hb := norm_nonneg (Work.CR.Flat.dbarCoord j (fun w => (φ w : ℂ)) z)
        have hc := norm_nonneg (fderiv ℝ φ z)
        nlinarith [h1, h2, ha, hb, hc]
    _ = 2 * (n : ℝ) * ‖fderiv ℝ φ z‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring



/-- `dbarCn J` depends only on the germ of the function. -/
lemma dbarCn_congr_of_eventuallyEq {n : ℕ} (J : Cn n → Cn n →L[ℝ] Cn n) {f g : Cn n → ℂ}
    {z v : Cn n} (h : f =ᶠ[𝓝 z] g) : dbarCn J f z v = dbarCn J g z v := by
  rw [dbarCn_apply, dbarCn_apply, h.fderiv_eq]

/-- An integral over `s` of a function that vanishes off `s` is the integral over all of space. -/
lemma setIntegral_eq_integral_of_eq_zero_off {n : ℕ} {f : Cn n → ℝ} {s : Set (Cn n)}
    (hs : MeasurableSet s) (hf : ∀ z ∉ s, f z = 0) : ∫ z in s, f z = ∫ z, f z := by
  rw [← integral_indicator hs]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  by_cases hz : z ∈ s
  · rw [Set.indicator_of_mem hz]
  · rw [Set.indicator_of_notMem hz, hf z hz]



/-- If `f` vanishes off the topological support of `g`, then so is its topological support
contained in that of `g`. -/
lemma tsupport_subset_of_eq_zero_off {n : ℕ} {f g : Cn n → ℝ}
    (h : ∀ z ∉ tsupport g, f z = 0) : tsupport f ⊆ tsupport g := by
  rw [tsupport]
  refine closure_minimal ?_ (isClosed_tsupport g)
  intro z hz
  rw [Function.mem_support] at hz
  by_contra hc
  exact hz (h z hc)



/-- An integral over all of space of a function that vanishes off `s` and agrees with `g` on `s`
is the integral of `g` over `s`. -/
lemma integral_eq_setIntegral_of_eq_on {n : ℕ} {f g : Cn n → ℝ} {s : Set (Cn n)}
    (hs : MeasurableSet s) (hoff : ∀ z ∉ s, f z = 0) (hon : ∀ z ∈ s, f z = g z) :
    ∫ z, f z = ∫ z in s, g z := by
  rw [← integral_indicator hs]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  by_cases hz : z ∈ s
  · rw [Set.indicator_of_mem hz, hon z hz]
  · rw [Set.indicator_of_notMem hz, hoff z hz]


theorem powCaccioppoliSource {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ0 : ∀ j, 0 < ρ j) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ A : ℝ, 0 < A ∧
      ∀ {A' : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n},
        (∀ m : ℕ, ContDiff ℝ m A') → ∀ {ε : ℝ}, ε ≤ ε₀ →
        (∀ i j : Fin n, Work.CR.Flat.holderNorm 1 α
            (fun z => A' z (Pi.single i 1) j) (Work.CR.Flat.polydisc 0 ρ) ≤ ENNReal.ofReal ε) →
        (∀ z v : Work.NN.Core.Cn n,
          (Work.NN.Core.JstdCn n + A') z ((Work.NN.Core.JstdCn n + A') z v) = -v) →
        ∀ (k : ℕ), 1 ≤ k → ∀ (u : Work.NN.Core.Cn n → ℂ),
          ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρ) → ∀ {Λ : ℝ}, 0 ≤ Λ →
          (∀ z ∈ Work.CR.Flat.polydisc 0 ρ,
            ∑ j : Fin n,
              ‖Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A') u z (Pi.single j 1)‖^2 ≤ Λ^2) →
          ∀ φ : Work.NN.Core.Cn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
            tsupport φ ⊆ Work.CR.Flat.polydisc 0 ρ → (∀ z, 0 ≤ φ z) →
            ∫ z in Work.CR.Flat.polydisc 0 ρ,
                (k : ℝ)^2 * (φ z)^2 * (‖u z‖^2)^(k-1) *
                  (∑ j : Fin n, (‖Work.CR.Flat.dCoord j u z‖^2
                    + ‖Work.CR.Flat.dbarCoord j u z‖^2))
              ≤ A * ((∫ z in Work.CR.Flat.polydisc 0 ρ,
                        ‖fderiv ℝ φ z‖^2 * (‖u z‖^2)^k)
                    + (k : ℝ)^2 * ∫ z in Work.CR.Flat.polydisc 0 ρ,
                        (φ z)^2 * (‖u z‖^2)^(k-1) * Λ^2) := by
  set ε₀ : ℝ := 1 / (16 * ((n : ℝ) + 1)) with hε₀def
  have hε₀pos : 0 < ε₀ := by rw [hε₀def]; positivity
  have hε₀ineq : 24 * (n : ℝ) ^ 2 * ε₀ ^ 2 ≤ 1 / 2 := by
    rw [hε₀def, div_eq_mul_inv, mul_pow, inv_pow]
    have h1 : (16 * ((n : ℝ) + 1)) ≠ 0 := by positivity
    have h2 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have h3 : (n:ℝ)^2 ≤ ((n:ℝ)+1)^2 := by nlinarith
    field_simp
    nlinarith [h2, h3]
  set A : ℝ := max 20 (16 * (n : ℝ)) with hAdef
  have hApos : 0 < A := by
    rw [hAdef]; exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hAle20 : (20:ℝ) ≤ A := by rw [hAdef]; exact le_max_left _ _
  have hAle16n : (16:ℝ) * (n:ℝ) ≤ A := by rw [hAdef]; exact le_max_right _ _
  refine ⟨ε₀, hε₀pos, A, hApos, ?_⟩
  intro A' hA'sm ε hεle hholder hJ k hk u hu Λ hΛ hdbar φ hφsm hφcs hφsupp hφ0
  have hφC1 : ContDiff ℝ 1 φ := hφsm.of_le (by simp)
  have hφd : ∀ z : Cn n, DifferentiableAt ℝ φ z := fun z => hφC1.differentiable_one z
  obtain ⟨χ, V, hχsm, hχcs, hχU, hVopen, hφV, hχone⟩ :=
    exists_contDiff_bump_of_isCompact_subset hφcs (Work.CR.Flat.isOpen_polydisc 0 ρ) hφsupp
  have hχC1 : ContDiff ℝ 1 χ := hχsm.of_le (by norm_num)
  set η : Cn n → ℂ := fun z => (φ z : ℂ) with hηdef
  set H : Cn n → ℂ := fun z => χ z * (u z) ^ k with hHdef
  set u' : Cn n → ℂ := fun z => χ z * u z with hu'def
  have hηc : ContDiff ℝ 1 η := by
    have h2 : ContDiff ℝ 1 (⇑Complex.ofRealCLM ∘ φ) :=
      (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := 1) Complex.ofRealCLM).comp (hφsm.of_le (by simp))
    simpa [hηdef, Function.comp_def, Complex.ofRealCLM_apply] using h2
  have hηcs : HasCompactSupport η := by
    rw [hηdef]
    exact IsCompact.of_isClosed_subset hφcs (isClosed_tsupport _) (by rw [tsupport_ofReal])
  have hu'c : ContDiff ℝ 1 u' := by
    rw [hu'def]
    exact contDiff_mul_of_tsupp_subset (Work.CR.Flat.isOpen_polydisc 0 ρ) hχC1 hχcs hχU hu
  have huPow : ContDiffOn ℝ 1 (fun z => (u z) ^ k) (Work.CR.Flat.polydisc 0 ρ) :=
    contDiffOn_pow hu k
  have hHc : ContDiff ℝ 1 H := by
    rw [hHdef]
    exact contDiff_mul_of_tsupp_subset (Work.CR.Flat.isOpen_polydisc 0 ρ) hχC1 hχcs hχU huPow
  have hHcs : HasCompactSupport H := by rw [hHdef]; exact hχcs.mul_right
  have hA'cont : Continuous A' := contDiff_zero.mp (hA'sm 0)
  have hAsm : ∀ z ∈ tsupport η, ∀ i j : Fin n, ‖A' z (Pi.single i 1) j‖ ≤ ε₀ := by
    intro z hz i j
    have hz1 : z ∈ Work.CR.Flat.polydisc 0 ρ := by
      rw [hηdef, tsupport_ofReal] at hz
      exact hφsupp hz
    have h1 := Work.CR.Flat.norm_apply_le_holderNorm 1 α
      (fun z => A' z (Pi.single i 1) j) (Work.CR.Flat.polydisc 0 ρ) hz1
    have h2 := hholder i j
    have h3 : ENNReal.ofReal ‖A' z (Pi.single i 1) j‖ ≤ ENNReal.ofReal ε₀ :=
      le_trans h1 (le_trans h2 (ENNReal.ofReal_le_ofReal hεle))
    exact (ENNReal.ofReal_le_ofReal_iff hε₀pos.le).mp h3
  have hI := weightedEnergyPerturbed (n := n) (A' := A') (ε := ε₀)
    hε₀pos.le hε₀ineq hηc hHc hηcs hHcs hA'cont hAsm
  have hηsq : ∀ z : Cn n, ‖η z‖ ^ 2 = (φ z) ^ 2 := by
    intro z
    rw [hηdef, Complex.norm_def, Complex.normSq_ofReal, Real.sq_sqrt (mul_self_nonneg (φ z)), sq]
  have hzp_of : ∀ z ∈ tsupport φ, z ∈ Work.CR.Flat.polydisc 0 ρ := fun z hz => hφsupp hz
  have hud : ∀ z ∈ tsupport φ, DifferentiableAt ℝ u z := by
    intro z hz
    have h1 : ContDiffAt ℝ 1 u z :=
      hu.contDiffAt ((Work.CR.Flat.isOpen_polydisc 0 ρ).mem_nhds (hzp_of z hz))
    exact h1.differentiableAt (by norm_num)
  have hevV : ∀ z ∈ tsupport φ, H =ᶠ[𝓝 z] (fun w => (u w) ^ k) := by
    intro z hz
    rw [hHdef]
    filter_upwards [hVopen.mem_nhds (hφV hz)] with w hw
    rw [hχone w hw, one_mul]
  have hu'eq : ∀ z ∈ tsupport φ, u' z = u z := by
    intro z hz
    simp only [hu'def, hχone z (hφV hz), one_mul]
  have hL : ∀ z : Cn n, (‖u z‖ ^ (k - 1)) ^ 2 = (‖u z‖ ^ 2) ^ (k - 1) := by
    intro z
    rw [← pow_mul, ← pow_mul, show (k - 1) * 2 = 2 * (k - 1) from by ring]
  -- ===== the left hand side =====
  have hGT : ∀ z : Cn n, ‖η z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j H z‖ ^ 2
        + ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2))
      = (k : ℝ) ^ 2 * (φ z) ^ 2 * (‖u z‖ ^ 2) ^ (k - 1)
        * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j u z‖ ^ 2
            + ‖Work.CR.Flat.dbarCoord j u z‖ ^ 2)) := by
    intro z
    rw [hηsq z]
    by_cases hz : φ z = 0
    · rw [hz]; simp
    · have hzts : z ∈ tsupport φ := subset_closure (Function.mem_support.mpr hz)
      have hd := hud z hzts
      have hev := hevV z hzts
      have hsum : (∑ j : Fin n, (‖Work.CR.Flat.dCoord j H z‖ ^ 2
            + ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2))
          = (k : ℝ) ^ 2 * (‖u z‖ ^ 2) ^ (k - 1) * (∑ j : Fin n,
              (‖Work.CR.Flat.dCoord j u z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j u z‖ ^ 2)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hcd : Work.CR.Flat.dCoord j H z = (k : ℂ) * (u z) ^ (k - 1)
            * Work.CR.Flat.dCoord j u z := by
          rw [dCoord_congr_of_eventuallyEq j hev, dCoord_pow j u z k hd]
        have hbd : Work.CR.Flat.dbarCoord j H z = (k : ℂ) * (u z) ^ (k - 1)
            * Work.CR.Flat.dbarCoord j u z := by
          rw [dbarCoord_congr_of_eventuallyEq j hev, dbarCoord_pow j u z k hd]
        have e1 : ‖Work.CR.Flat.dCoord j H z‖ ^ 2
            = (k:ℝ)^2 * (‖u z‖^2)^(k-1) * ‖Work.CR.Flat.dCoord j u z‖ ^ 2 := by
          have hc := congrArg (fun w : ℂ => ‖w‖ ^ 2) hcd
          simp only [norm_mul, mul_pow, Complex.norm_natCast, norm_pow] at hc
          rw [hc, hL z]
        have e2 : ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2
            = (k:ℝ)^2 * (‖u z‖^2)^(k-1) * ‖Work.CR.Flat.dbarCoord j u z‖ ^ 2 := by
          have hc := congrArg (fun w : ℂ => ‖w‖ ^ 2) hbd
          simp only [norm_mul, mul_pow, Complex.norm_natCast, norm_pow] at hc
          rw [hc, hL z]
        rw [e1, e2]; ring
      rw [hsum]; ring
  -- ===== the `Y` term =====
  have hYbd : ∀ z : Cn n, ‖η z‖ ^ 2 * (∑ j : Fin n,
        ‖dbarCn (JstdCn n + A') H z (Pi.single j (1:ℂ))‖ ^ 2)
      ≤ (k:ℝ)^2 * (φ z)^2 * (‖u z‖^2)^(k-1) * Λ^2 := by
    intro z
    rw [hηsq z]
    by_cases hz : φ z = 0
    · rw [hz]; simp
    · have hzts : z ∈ tsupport φ := subset_closure (Function.mem_support.mpr hz)
      have hzp2 := hzp_of z hzts
      have hd := hud z hzts
      have hev := hevV z hzts
      have hY : (∑ j : Fin n, ‖dbarCn (JstdCn n + A') H z (Pi.single j (1:ℂ))‖ ^ 2)
          = (k:ℝ)^2 * (‖u z‖^2)^(k-1) * (∑ j : Fin n,
              ‖dbarCn (JstdCn n + A') u z (Pi.single j (1:ℂ))‖ ^ 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have h1 : dbarCn (JstdCn n + A') H z (Pi.single j (1:ℂ))
            = (k:ℂ) * (u z)^(k-1) * dbarCn (JstdCn n + A') u z (Pi.single j (1:ℂ)) := by
          rw [dbarCn_congr_of_eventuallyEq _ hev,
            dbarCn_pow (JstdCn n + A') u z (Pi.single j (1:ℂ)) k hd]
        have hc := congrArg (fun w : ℂ => ‖w‖ ^ 2) h1
        simp only [norm_mul, mul_pow, Complex.norm_natCast, norm_pow] at hc
        rw [hc, hL z]
      rw [hY]
      have h1 : (k:ℝ)^2 * (‖u z‖^2)^(k-1) * (∑ j : Fin n,
            ‖dbarCn (JstdCn n + A') u z (Pi.single j (1:ℂ))‖ ^ 2)
          ≤ (k:ℝ)^2 * (‖u z‖^2)^(k-1) * Λ^2 :=
        mul_le_mul_of_nonneg_left (hdbar z hzp2) (by positivity)
      calc (φ z) ^ 2 * ((k:ℝ)^2 * (‖u z‖^2)^(k-1) * (∑ j : Fin n,
              ‖dbarCn (JstdCn n + A') u z (Pi.single j (1:ℂ))‖ ^ 2))
          ≤ (φ z) ^ 2 * ((k:ℝ)^2 * (‖u z‖^2)^(k-1) * Λ^2) :=
            mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        _ = (k:ℝ)^2 * (φ z)^2 * (‖u z‖^2)^(k-1) * Λ^2 := by ring
  -- ===== the `M` term =====
  have hMbd : ∀ z : Cn n, ‖H z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j η z‖ ^ 2
        + ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2))
      ≤ 2 * (n:ℝ) * ‖fderiv ℝ φ z‖ ^ 2 * (‖u' z‖ ^ 2) ^ k := by
    intro z
    by_cases hz : (∑ j : Fin n, (‖Work.CR.Flat.dCoord j η z‖ ^ 2
        + ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2)) = 0
    · rw [hz, mul_zero]; positivity
    · have hzts : z ∈ tsupport φ := by
        by_contra hc
        refine hz ?_
        have hf0 : fderiv ℝ η z = 0 := by
          rw [hηdef]
          exact fderiv_of_notMem_tsupport ℝ (by rwa [tsupport_ofReal])
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [Work.CR.Flat.dCoord, Work.CR.Flat.dbarCoord, hf0]
        simp
      have hHz : ‖H z‖ ^ 2 = (‖u' z‖ ^ 2) ^ k := by
        have h1 : H z = (u z)^k := by
          simp only [hHdef, hχone z (hφV hzts), one_mul]
        have h2 : u' z = u z := hu'eq z hzts
        rw [h1, h2, norm_pow]
        rw [show (‖u z‖ ^ k) ^ 2 = (‖u z‖ ^ 2) ^ k from by
          rw [← pow_mul, ← pow_mul, show k * 2 = 2 * k from by ring]]
      rw [hHz]
      have h1 := sum_dCoord_ofReal_le (hφd z)
      have h2 : (0:ℝ) ≤ (‖u' z‖ ^ 2) ^ k := by positivity
      calc (‖u' z‖ ^ 2) ^ k * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j η z‖ ^ 2
              + ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2))
          ≤ (‖u' z‖ ^ 2) ^ k * (2 * (n:ℝ) * ‖fderiv ℝ φ z‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h1 h2
        _ = 2 * (n:ℝ) * ‖fderiv ℝ φ z‖ ^ 2 * (‖u' z‖ ^ 2) ^ k := by ring
  -- ===== integrability =====
  have hJ' : Continuous (fun z : Cn n => (JstdCn n + A') z) := by
    have heq : (fun z : Cn n => (JstdCn n + A') z) = fun z => JstdCn n z + A' z := by
      funext z; simp [Pi.add_apply]
    rw [heq]
    exact (continuous_const : Continuous (fun z : Cn n => JstdCn n z)).add hA'cont
  have hGYint : Integrable (fun z => ‖η z‖ ^ 2 * (∑ j : Fin n,
      ‖dbarCn (JstdCn n + A') H z (Pi.single j (1:ℂ))‖ ^ 2)) := by
    have hcont : Continuous (fun z => ‖η z‖ ^ 2 * (∑ j : Fin n,
        ‖dbarCn (JstdCn n + A') H z (Pi.single j (1:ℂ))‖ ^ 2)) :=
      (hηc.continuous.norm.pow 2).mul
        (continuous_finsetSum _ (fun j _ => (continuous_dbarCn_apply hJ' hHc _).norm.pow 2))
    have hsub : tsupport (fun z => ‖η z‖ ^ 2 * (∑ j : Fin n,
        ‖dbarCn (JstdCn n + A') H z (Pi.single j (1:ℂ))‖ ^ 2)) ⊆ tsupport φ :=
      tsupport_subset_of_eq_zero_off
        (f := fun z => ‖η z‖ ^ 2 * (∑ j : Fin n,
          ‖dbarCn (JstdCn n + A') H z (Pi.single j (1:ℂ))‖ ^ 2))
        (g := φ) (fun z hz => by
          have h0 : φ z = 0 := by
            by_contra h
            exact hz (subset_closure (Function.mem_support.mpr h))
          have hη0 : η z = 0 := by simp only [hηdef, h0, Complex.ofReal_zero]
          rw [hη0, norm_zero]; ring)
    exact Continuous.integrable_of_hasCompactSupport hcont
      (IsCompact.of_isClosed_subset hφcs (isClosed_tsupport _) hsub)
  have hYu'int : Integrable (fun z => (k:ℝ)^2 * (φ z)^2 * (‖u' z‖^2)^(k-1) * Λ^2) := by
    have hcont : Continuous (fun z => (k:ℝ)^2 * (φ z)^2 * (‖u' z‖^2)^(k-1) * Λ^2) :=
      (((continuous_const.mul ((hφC1.continuous).pow 2)).mul
        ((hu'c.continuous.norm.pow 2).pow (k-1))).mul continuous_const)
    have hsub : tsupport (fun z => (k:ℝ)^2 * (φ z)^2 * (‖u' z‖^2)^(k-1) * Λ^2) ⊆ tsupport φ :=
      tsupport_subset_of_eq_zero_off
        (f := fun z => (k:ℝ)^2 * (φ z)^2 * (‖u' z‖^2)^(k-1) * Λ^2)
        (g := φ) (fun z hz => by
          have h0 : φ z = 0 := by
            by_contra h; exact hz (subset_closure (Function.mem_support.mpr h))
          rw [h0]; ring)
    exact Continuous.integrable_of_hasCompactSupport hcont
      (IsCompact.of_isClosed_subset hφcs (isClosed_tsupport _) hsub)
  have hGMint : Integrable (fun z => ‖H z‖ ^ 2 * (∑ j : Fin n,
      (‖Work.CR.Flat.dCoord j η z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2))) := by
    have hcont : Continuous (fun z => ‖H z‖ ^ 2 * (∑ j : Fin n,
        (‖Work.CR.Flat.dCoord j η z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2))) :=
      (hHc.continuous.norm.pow 2).mul (continuous_finsetSum _ (fun j _ =>
        ((Work.NN.Core.continuous_dCoord j hηc).norm.pow 2).add
          ((Work.NN.Core.continuous_dbarCoord j hηc).norm.pow 2)))
    have hsub : tsupport (fun z => ‖H z‖ ^ 2 * (∑ j : Fin n,
        (‖Work.CR.Flat.dCoord j η z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2))) ⊆ tsupport φ :=
      tsupport_subset_of_eq_zero_off
        (f := fun z => ‖H z‖ ^ 2 * (∑ j : Fin n,
          (‖Work.CR.Flat.dCoord j η z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2)))
        (g := φ) (fun z hz => by
          have hzη : z ∉ tsupport η := by rwa [hηdef, tsupport_ofReal]
          have hf0 : fderiv ℝ η z = 0 := fderiv_of_notMem_tsupport ℝ hzη
          have hsum0 : (∑ j : Fin n, (‖Work.CR.Flat.dCoord j η z‖ ^ 2
              + ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2)) = 0 := by
            refine Finset.sum_eq_zero fun j _ => ?_
            rw [Work.CR.Flat.dCoord, Work.CR.Flat.dbarCoord, hf0]
            simp
          rw [hsum0, mul_zero])
    exact Continuous.integrable_of_hasCompactSupport hcont
      (IsCompact.of_isClosed_subset hφcs (isClosed_tsupport _) hsub)
  have hMu'int : Integrable (fun z => 2 * (n:ℝ) * ‖fderiv ℝ φ z‖ ^ 2 * (‖u' z‖ ^ 2) ^ k) := by
    have hcont : Continuous (fun z => 2 * (n:ℝ) * ‖fderiv ℝ φ z‖ ^ 2 * (‖u' z‖ ^ 2) ^ k) :=
      ((continuous_const.mul (((hφC1.continuous_fderiv (by norm_num)).norm).pow 2)).mul
        ((hu'c.continuous.norm.pow 2).pow k))
    have hsub : tsupport (fun z => 2 * (n:ℝ) * ‖fderiv ℝ φ z‖ ^ 2 * (‖u' z‖ ^ 2) ^ k)
        ⊆ tsupport φ :=
      tsupport_subset_of_eq_zero_off
        (f := fun z => 2 * (n:ℝ) * ‖fderiv ℝ φ z‖ ^ 2 * (‖u' z‖ ^ 2) ^ k)
        (g := φ) (fun z hz => by
          have hf0 : fderiv ℝ φ z = 0 := fderiv_of_notMem_tsupport ℝ hz
          rw [hf0, norm_zero]; ring)
    exact Continuous.integrable_of_hasCompactSupport hcont
      (IsCompact.of_isClosed_subset hφcs (isClosed_tsupport _) hsub)
  -- ===== integral bounds =====
  have hYle : ∫ z, ‖η z‖ ^ 2 * (∑ j : Fin n,
        ‖dbarCn (JstdCn n + A') H z (Pi.single j (1:ℂ))‖ ^ 2)
      ≤ (k:ℝ)^2 * ∫ z in Work.CR.Flat.polydisc 0 ρ,
          (φ z)^2 * (‖u z‖^2)^(k-1) * Λ^2 := by
    have h1 : ∫ z, ‖η z‖ ^ 2 * (∑ j : Fin n,
          ‖dbarCn (JstdCn n + A') H z (Pi.single j (1:ℂ))‖ ^ 2)
        ≤ ∫ z, (k:ℝ)^2 * (φ z)^2 * (‖u' z‖^2)^(k-1) * Λ^2 := by
      refine integral_mono hGYint hYu'int (fun z => le_trans (hYbd z) (le_of_eq ?_))
      by_cases hz : φ z = 0
      · rw [hz]; ring
      · rw [hu'eq z (subset_closure (Function.mem_support.mpr hz))]
    have h2 : (∫ z, (k:ℝ)^2 * (φ z)^2 * (‖u' z‖^2)^(k-1) * Λ^2)
        = (k:ℝ)^2 * ∫ z, (φ z)^2 * (‖u' z‖^2)^(k-1) * Λ^2 := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun z => by ring))
    refine (h1.trans (le_of_eq h2)).trans (le_of_eq ?_)
    congr 1
    exact integral_eq_setIntegral_of_eq_on (Work.CR.Flat.isOpen_polydisc 0 ρ).measurableSet
      (fun z hz => by
        have h0 : φ z = 0 := by
          by_contra h
          exact hz (hφsupp (subset_closure (Function.mem_support.mpr h)))
        rw [h0]; ring)
      (fun z hz => by
        by_cases hz0 : φ z = 0
        · rw [hz0]; ring
        · rw [hu'eq z (subset_closure (Function.mem_support.mpr hz0))])
  have hMle : ∫ z, ‖H z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j η z‖ ^ 2
        + ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2))
      ≤ 2 * (n:ℝ) * ∫ z in Work.CR.Flat.polydisc 0 ρ,
          ‖fderiv ℝ φ z‖ ^ 2 * (‖u z‖ ^ 2) ^ k := by
    have h1 : ∫ z, ‖H z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j η z‖ ^ 2
          + ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2))
        ≤ ∫ z, 2 * (n:ℝ) * ‖fderiv ℝ φ z‖ ^ 2 * (‖u' z‖ ^ 2) ^ k :=
      integral_mono hGMint hMu'int hMbd
    have h2 : (∫ z, 2 * (n:ℝ) * ‖fderiv ℝ φ z‖ ^ 2 * (‖u' z‖ ^ 2) ^ k)
        = 2 * (n:ℝ) * ∫ z, ‖fderiv ℝ φ z‖ ^ 2 * (‖u' z‖ ^ 2) ^ k := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun z => by ring))
    refine (h1.trans (le_of_eq h2)).trans (le_of_eq ?_)
    congr 1
    exact integral_eq_setIntegral_of_eq_on (Work.CR.Flat.isOpen_polydisc 0 ρ).measurableSet
      (fun z hz => by
        have hf0 : fderiv ℝ φ z = 0 := fderiv_of_notMem_tsupport ℝ (by
          intro hmem; exact hz (hφsupp hmem))
        rw [hf0, norm_zero]; ring)
      (fun z hz => by
        by_cases hf : fderiv ℝ φ z = 0
        · rw [hf, norm_zero]; ring
        · rw [hu'eq z (by
            by_contra hc; exact hf (fderiv_of_notMem_tsupport ℝ hc))])
  -- ===== the left hand side as a space integral =====
  have hTL : (∫ z in Work.CR.Flat.polydisc 0 ρ,
        (k : ℝ)^2 * (φ z)^2 * (‖u z‖^2)^(k-1) *
          (∑ j : Fin n, (‖Work.CR.Flat.dCoord j u z‖^2
            + ‖Work.CR.Flat.dbarCoord j u z‖^2)))
      = ∫ z, ‖η z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j H z‖ ^ 2
          + ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2)) := by
    have hz0 : ∀ z ∉ Work.CR.Flat.polydisc 0 ρ,
        (k : ℝ)^2 * (φ z)^2 * (‖u z‖^2)^(k-1) *
          (∑ j : Fin n, (‖Work.CR.Flat.dCoord j u z‖^2
            + ‖Work.CR.Flat.dbarCoord j u z‖^2)) = 0 := by
      intro z hz
      have h : φ z = 0 := by
        by_contra hc
        exact hz (hφsupp (subset_closure (Function.mem_support.mpr hc)))
      rw [h]; ring
    rw [setIntegral_eq_integral_of_eq_zero_off (Work.CR.Flat.isOpen_polydisc 0 ρ).measurableSet hz0]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun z => (hGT z).symm))
  rw [hTL]
  set R1 : ℝ := ∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ φ z‖ ^ 2 * (‖u z‖ ^ 2) ^ k
    with hR1def
  set R2 : ℝ := ∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z) ^ 2 * (‖u z‖ ^ 2) ^ (k-1) * Λ ^ 2
    with hR2def
  have hR1nn : 0 ≤ R1 := integral_nonneg (fun z => by positivity)
  have hR2nn : 0 ≤ R2 := integral_nonneg (fun z => by positivity)
  calc ∫ z, ‖η z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j H z‖ ^ 2
        + ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2))
      ≤ 20 * (∫ z, ‖η z‖ ^ 2 * (∑ j : Fin n,
            ‖dbarCn (JstdCn n + A') H z (Pi.single j (1:ℂ))‖ ^ 2))
        + 8 * (∫ z, ‖H z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j η z‖ ^ 2
            + ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2))) := hI
    _ ≤ 20 * ((k:ℝ)^2 * R2) + 16 * (n:ℝ) * R1 := by
        have h1 : 20 * (∫ z, ‖η z‖ ^ 2 * (∑ j : Fin n,
              ‖dbarCn (JstdCn n + A') H z (Pi.single j (1:ℂ))‖ ^ 2)) ≤ 20 * ((k:ℝ)^2 * R2) := by
          linarith [hYle]
        have h2 : 8 * (∫ z, ‖H z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j η z‖ ^ 2
              + ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2))) ≤ 16 * (n:ℝ) * R1 := by
          linarith [hMle]
        linarith [h1, h2]
    _ ≤ A * ((k:ℝ)^2 * R2) + A * R1 := by
        have h1 : 20 * ((k:ℝ)^2 * R2) ≤ A * ((k:ℝ)^2 * R2) :=
          mul_le_mul_of_nonneg_right hAle20 (by positivity)
        have h2 : 16 * (n:ℝ) * R1 ≤ A * R1 := mul_le_mul_of_nonneg_right hAle16n hR1nn
        linarith [h1, h2]
    _ = A * (R1 + (k:ℝ)^2 * R2) := by ring


end Work.NN.Core.Lev
