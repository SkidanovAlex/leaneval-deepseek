import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Submission.Work.BoseBoxFock.PCFU.UnivFrames
import Submission.Work.BoseBoxFock.PCFU.slotExchange
import Submission.Work.BoseBoxFock.pinQk_fibre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.pairSum_MiddleV_star_MiddleU`

The `pairSet n`-sum of the **mirror (h.c.) middle kernel** `MiddleV` is the complex conjugate of
the `pairSet n`-sum of the cubic middle kernel `MiddleU` with the condensate pin `pinCond` sitting
on the first slot.  This is the `Middle`-analogue of `PCFU/pairSumAtomConj.lean` (the same identity
for the four-function *atom*), and the last analytic row of the cubic dictionary.

## The mathematics

With `Θ` bounded, measurable and supported in the box `boxPow n ℓ` (`ℓ = ellH v μ`), and with the
two kernels

    MiddleU(x,y,u) = Σ_{s∈excited} Σ_k f_L(s)Ŵ₁(k)·conj(pinQ(s−k) y)·pinTheta_s x·conj(pinQ_k u)
    MiddleV(x_i,y,x_j,u)
      = Σ_{s∈excited} Σ_k f_L(s)Ŵ₁(k)·pinQ_k x_i·conj(pinTheta_s y)·pinQ(s−k) x_j·conj(pinCond u)

(`pinCond = c·θ_Λ`), the per-pair identity is

    conj(∫_x∫_y∫_u conj(Θ x)·pinCond(x_i)·MiddleU(x_j,y,u)·Θ(x[i↦y][j↦u]))
      = ∫_x∫_y∫_u conj(Θ x)·MiddleV(x_j,y,x_i,u)·Θ(x[j↦y][i↦u]),

proved exactly as in the atom case: `star` of the integral is the integral of the conjugate
(unconditional), Fubini turns the iterated integral into an integral over
`X n × (E³ × E³)`, and the *measure-preserving* substitution
`(momentum swap) followed by (slot roll)` (the composite of `PCFU/slotExchange.pairSlotRoll` with
the swap of the two momentum coordinates) turns the conjugate integrand into the integrand of the
other side.  The pointwise core is a *finite sum* identity,
`MiddleV b u a y = star (pinCond y)·star (MiddleU u a b)`, which holds term by term (the weights
`f_L(s)Ŵ₁(k)` are real and the two `s,k`-sums agree after commuting the factors).

The `MiddleV`/`MiddleU` integrands are everywhere bounded (finite sums of the bounded pins
`pinQ`/`pinTheta`/`pinCond`) and — because `Θ` and `Θ∘update` vanish off the box — supported in the
finite-measure set `boxPow n ℓ × (boxL ℓ × boxL ℓ)` (resp. `boxL ℓ × boxL ℓ` for the inner
integrals), so `Work.MB.integrable_of_bdd_of_support` supplies every integrability that Fubini
needs; no integrability hypothesis appears in the statement.

The development uses no unfinished proof obligation: every declaration in this file is closed.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-! ## 1. The pinned modes: measurability, uniform bounds, support -/

/-- `pinQ` is bounded *uniformly in the label*: the bound of `pinQ_bdd` does not depend on `k`. -/
theorem pinQ_bdd_uniform (v : E3 → ℝ) (μ : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : Lab N) (z : E3), ‖pinQ v μ N k z‖ ≤ C := by
  obtain ⟨Cχ, hCχ⟩ := chiLam_bdd (ellH v μ) (ne_of_gt (ellH_pos v μ))
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  have hs : 0 < (Real.sqrt ((ellH v μ) ^ 3))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos_of_pos (pow_pos hℓ 3))
  have hθ : ∀ z : E3, ‖Work.BoseK15.corpusBox.thetaFun (ellH v μ) z‖ ≤ 1 := by
    intro z
    rw [Work.BoseB4.BoxData.thetaFun_apply]; split <;> simp
  refine ⟨(Real.sqrt ((ellH v μ) ^ 3))⁻¹ * (max Cχ 0 + 1), by positivity, fun k z => ?_⟩
  have hq : ‖Work.BoseK15.corpusBox.qVec (ellH v μ) (kmomLab (ellH v μ) N k) z‖ ≤ max Cχ 0 + 1 := by
    rw [Work.BoseB4.BoxData.qVec_apply, Work.BoseB4.BoxData.modeVec_apply]
    refine le_trans (norm_sub_le _ _) ?_
    have h1 : ‖Complex.exp (Complex.I * ((inner ℝ (kmomLab (ellH v μ) N k) z : ℝ) : ℂ)) *
        ((Work.BoseK15.corpusBox.chiLam (ellH v μ) z : ℝ) : ℂ)‖ ≤ max Cχ 0 := by
      rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, norm_ofReal_c]
      exact le_trans (hCχ z) (le_max_left _ _)
    have h2 : ‖((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N k) : ℝ) : ℂ) *
        Work.BoseK15.corpusBox.thetaFun (ellH v μ) z‖ ≤ 1 := by
      rw [norm_mul, norm_ofReal_c]
      have hh := Work.BoseK15.hatChi_le_one.1 ((ellH v μ) • kmomLab (ellH v μ) N k)
      exact le_trans (mul_le_mul hh (hθ z) (norm_nonneg _) (by norm_num)) (by norm_num)
    linarith
  rw [pinQ, norm_mul, norm_ofReal_c, abs_of_pos hs]
  exact mul_le_mul_of_nonneg_left hq hs.le

/-- `pinTheta` is measurable (`(√ℓ³)⁻¹·e^{i⟪p,x⟫}·θ_Λ`). -/
theorem pinTheta_measurable (v : E3 → ℝ) (μ : ℝ) (N : ℕ) (s : Lab N) :
    Measurable (pinTheta v μ N s) := by
  have hθ : Measurable (Work.BoseK15.corpusBox.thetaFun (ellH v μ)) :=
    thetaFun_measurable_aux (ellH v μ)
  have hexp : Measurable (fun x : E3 =>
      Complex.exp (Complex.I * ((inner ℝ (kmomLab (ellH v μ) N s) x : ℝ) : ℂ))) := by fun_prop
  rw [show pinTheta v μ N s = fun x : E3 => (((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ) *
      (Complex.exp (Complex.I * ((inner ℝ (kmomLab (ellH v μ) N s) x : ℝ) : ℂ))
        * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x) from rfl]
  exact (hexp.mul hθ).const_mul _

/-- `pinTheta` is bounded *uniformly in the label* by the normalising scalar `(√ℓ³)⁻¹`. -/
theorem pinTheta_bdd_uniform (v : E3 → ℝ) (μ : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Lab N) (z : E3), ‖pinTheta v μ N s z‖ ≤ C := by
  refine ⟨((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ), by positivity, fun s z => ?_⟩
  have hθ : ‖Work.BoseK15.corpusBox.thetaFun (ellH v μ) z‖ ≤ 1 := by
    rw [Work.BoseB4.BoxData.thetaFun_apply]; split <;> simp
  rw [pinTheta, Work.BoseB4.BoxData.thetaExp, norm_mul, Complex.norm_of_nonneg (by positivity),
    norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  exact (mul_le_mul_of_nonneg_left hθ (by positivity)).trans_eq (mul_one _)

/-- `pinTheta` is bounded by the (real) normalising scalar `(√ℓ³)⁻¹`. -/
theorem pinTheta_bdd (v : E3 → ℝ) (μ : ℝ) (N : ℕ) (s : Lab N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E3, ‖pinTheta v μ N s z‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := pinTheta_bdd_uniform v μ N
  exact ⟨C, hC0, fun z => hC s z⟩

/-- `pinTheta` is supported in the box `boxL (ellH v μ)`. -/
theorem pinTheta_support_subset (v : E3 → ℝ) (μ : ℝ) (N : ℕ) (s : Lab N) :
    Function.support (pinTheta v μ N s) ⊆ Work.BoseK15.corpusBox.boxL (ellH v μ) := by
  intro x hx
  by_contra hx'
  exact hx (by rw [pinTheta, Work.BoseB4.BoxData.thetaExp,
    Work.BoseB4.BoxData.thetaFun_apply, if_neg hx']; ring)

/-! ## 2. Boundedness and measurability of the two middle kernels -/

/-- `MiddleU` is bounded (a finite sum of products of the bounded pins). -/
theorem MiddleU_bdd (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y u : E3, ‖MiddleU v h fc fu μ N x y u‖ ≤ C := by
  obtain ⟨Cq, hCq0, hCq⟩ := pinQ_bdd_uniform v μ N
  obtain ⟨Ct, hCt0, hCt⟩ := pinTheta_bdd_uniform v μ N
  refine ⟨∑ s ∈ Work.BoseB7.excited (Lab N), ∑ k : Lab N,
      ‖(((fLh v fc μ N s * W1h v h μ fu N k : ℝ)) : ℂ)‖ * (Cq * (Ct * Cq)), ?_, ?_⟩
  · exact Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun k _ =>
      mul_nonneg (norm_nonneg _) (mul_nonneg hCq0 (mul_nonneg hCt0 hCq0))
  · intro x y u
    rw [MiddleU]
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun s hs => ?_)
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun k hk => ?_)
    have h1 : ‖pinQ v μ N (s - k) y‖ ≤ Cq := hCq _ y
    have h2 : ‖pinTheta v μ N s x‖ ≤ Ct := hCt _ x
    have h3 : ‖pinQ v μ N k u‖ ≤ Cq := hCq _ u
    have h12 : ‖pinQ v μ N (s - k) y‖ * ‖pinTheta v μ N s x‖ ≤ Cq * Ct :=
      mul_le_mul h1 h2 (norm_nonneg _) hCq0
    have h123 : ‖pinQ v μ N (s - k) y‖ * ‖pinTheta v μ N s x‖ * ‖pinQ v μ N k u‖
        ≤ (Cq * Ct) * Cq := mul_le_mul h12 h3 (norm_nonneg _) (mul_nonneg hCq0 hCt0)
    rw [norm_mul, norm_mul, norm_mul, norm_star, norm_star]
    calc ‖(((fLh v fc μ N s * W1h v h μ fu N k : ℝ)) : ℂ)‖ * ‖pinQ v μ N (s - k) y‖
          * ‖pinTheta v μ N s x‖ * ‖pinQ v μ N k u‖
        = ‖(((fLh v fc μ N s * W1h v h μ fu N k : ℝ)) : ℂ)‖
          * (‖pinQ v μ N (s - k) y‖ * ‖pinTheta v μ N s x‖ * ‖pinQ v μ N k u‖) := by ring
      _ ≤ ‖(((fLh v fc μ N s * W1h v h μ fu N k : ℝ)) : ℂ)‖ * (Cq * (Ct * Cq)) :=
          mul_le_mul_of_nonneg_left (by simpa [mul_assoc] using h123) (norm_nonneg _)

/-- `MiddleV` is bounded. -/
theorem MiddleV_bdd (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (c : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ xi y xj u : E3, ‖MiddleV v h fc fu μ N c xi y xj u‖ ≤ C := by
  obtain ⟨Cq, hCq0, hCq⟩ := pinQ_bdd_uniform v μ N
  obtain ⟨Ct, hCt0, hCt⟩ := pinTheta_bdd_uniform v μ N
  obtain ⟨Cp, hCp0, hCp⟩ := pinCond_bdd v μ c
  refine ⟨∑ s ∈ Work.BoseB7.excited (Lab N), ∑ k : Lab N,
      ‖(((fLh v fc μ N s * W1h v h μ fu N k : ℝ)) : ℂ)‖ * (Cq * (Ct * (Cq * Cp))), ?_, ?_⟩
  · exact Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun k _ =>
      mul_nonneg (norm_nonneg _) (mul_nonneg hCq0 (mul_nonneg hCt0 (mul_nonneg hCq0 hCp0)))
  · intro xi y xj u
    rw [MiddleV]
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun s hs => ?_)
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun k hk => ?_)
    have h1 : ‖pinQ v μ N k xi‖ ≤ Cq := hCq _ xi
    have h2 : ‖pinTheta v μ N s y‖ ≤ Ct := hCt _ y
    have h3 : ‖pinQ v μ N (s - k) xj‖ ≤ Cq := hCq _ xj
    have h4 : ‖pinCond v μ c u‖ ≤ Cp := hCp u
    have h12 : ‖pinQ v μ N k xi‖ * ‖pinTheta v μ N s y‖ ≤ Cq * Ct :=
      mul_le_mul h1 h2 (norm_nonneg _) hCq0
    have h123 : ‖pinQ v μ N k xi‖ * ‖pinTheta v μ N s y‖ * ‖pinQ v μ N (s - k) xj‖
        ≤ (Cq * Ct) * Cq := mul_le_mul h12 h3 (norm_nonneg _) (mul_nonneg hCq0 hCt0)
    have h1234 : ‖pinQ v μ N k xi‖ * ‖pinTheta v μ N s y‖ * ‖pinQ v μ N (s - k) xj‖
        * ‖pinCond v μ c u‖ ≤ (Cq * Ct * Cq) * Cp :=
      mul_le_mul h123 h4 (norm_nonneg _) (mul_nonneg (mul_nonneg hCq0 hCt0) hCq0)
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_star, norm_star]
    calc ‖(((fLh v fc μ N s * W1h v h μ fu N k : ℝ)) : ℂ)‖ * ‖pinQ v μ N k xi‖
          * ‖pinTheta v μ N s y‖ * ‖pinQ v μ N (s - k) xj‖ * ‖pinCond v μ c u‖
        = ‖(((fLh v fc μ N s * W1h v h μ fu N k : ℝ)) : ℂ)‖
          * (‖pinQ v μ N k xi‖ * ‖pinTheta v μ N s y‖ * ‖pinQ v μ N (s - k) xj‖
            * ‖pinCond v μ c u‖) := by ring
      _ ≤ ‖(((fLh v fc μ N s * W1h v h μ fu N k : ℝ)) : ℂ)‖ * (Cq * (Ct * (Cq * Cp))) :=
          mul_le_mul_of_nonneg_left (by simpa [mul_assoc] using h1234) (norm_nonneg _)

/-- `MiddleU`, as a function of the triple `(x,y,u)`, is measurable. -/
theorem MiddleU_measurable (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) :
    Measurable (fun p : E3 × E3 × E3 => MiddleU v h fc fu μ N p.1 p.2.1 p.2.2) := by
  refine Finset.measurable_sum _ (fun s hs => ?_)
  refine Finset.measurable_sum _ (fun k hk => ?_)
  have hQa : Measurable (fun p : E3 × E3 × E3 => star (pinQ v μ N (s - k) p.2.1)) :=
    continuous_star.measurable.comp
      ((pinQ_measurable v μ N (s - k)).comp (measurable_fst.comp measurable_snd))
  have hQb : Measurable (fun p : E3 × E3 × E3 => star (pinQ v μ N k p.2.2)) :=
    continuous_star.measurable.comp
      ((pinQ_measurable v μ N k).comp (measurable_snd.comp measurable_snd))
  have hT : Measurable (fun p : E3 × E3 × E3 => pinTheta v μ N s p.1) :=
    (pinTheta_measurable v μ N s).comp measurable_fst
  have hp : Measurable (fun p : E3 × E3 × E3 =>
      ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ) * star (pinQ v μ N (s - k) p.2.1)
        * pinTheta v μ N s p.1 * star (pinQ v μ N k p.2.2)) :=
    (((measurable_const.mul hQa).mul hT).mul hQb)
  simpa only [MiddleU] using hp

/-- `MiddleV`, as a function of the quadruple `(x_i,y,x_j,u)`, is measurable. -/
theorem MiddleV_measurable (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (c : ℂ) :
    Measurable (fun p : E3 × E3 × E3 × E3 =>
      MiddleV v h fc fu μ N c p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  refine Finset.measurable_sum _ (fun s hs => ?_)
  refine Finset.measurable_sum _ (fun k hk => ?_)
  have hQa : Measurable (fun p : E3 × E3 × E3 × E3 => pinQ v μ N k p.1) :=
    (pinQ_measurable v μ N k).comp measurable_fst
  have hQb : Measurable (fun p : E3 × E3 × E3 × E3 => star (pinTheta v μ N s p.2.1)) :=
    continuous_star.measurable.comp
      ((pinTheta_measurable v μ N s).comp (measurable_fst.comp measurable_snd))
  have hQc : Measurable (fun p : E3 × E3 × E3 × E3 => pinQ v μ N (s - k) p.2.2.1) :=
    (pinQ_measurable v μ N (s - k)).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hQd : Measurable (fun p : E3 × E3 × E3 × E3 => star (pinCond v μ c p.2.2.2)) :=
    continuous_star.measurable.comp
      ((pinCond_measurable v μ c).comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have hp : Measurable (fun p : E3 × E3 × E3 × E3 =>
      ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ) * pinQ v μ N k p.1
        * star (pinTheta v μ N s p.2.1) * pinQ v μ N (s - k) p.2.2.1
        * star (pinCond v μ c p.2.2.2)) :=
    ((((measurable_const.mul hQa).mul hQb).mul hQc).mul hQd)
  simpa only [MiddleV] using hp

/-! ## 3. The pointwise identity between the two middle kernels -/

/-- **The pointwise conjugation identity**: `MiddleV b u a y = conj(pinCond y)·conj(MiddleU u a b)`.
Both sides are the same finite `(s,k)`-sum: the weights `f_L(s)Ŵ₁(k)` are real (`conj` fixes them)
and the six pin factors agree after commuting them. -/
theorem MiddleV_eq_star_pinCond_mul_star_MiddleU (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (c : ℂ) (b u a y : E3) :
    MiddleV v h fc fu μ N c b u a y
      = star (pinCond v μ c y) * star (MiddleU v h fc fu μ N u a b) := by
  rw [MiddleU, MiddleV]
  rw [star_sum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  rw [star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  simp only [star_mul, star_star]
  rw [Complex.star_def, Complex.conj_ofReal]
  ring

/-! ## 4. The measure-preserving substitutions on `X n × (E³ × E³)` -/

/-- The swap of the two momentum coordinates of `X n × (E³ × E³)`. -/
private def momsSwapEquiv (n : ℕ) : (Xn n × (E3 × E3)) ≃ᵐ (Xn n × (E3 × E3)) :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Xn n)) (MeasurableEquiv.prodComm)

private lemma momsSwapEquiv_apply (n : ℕ) (q : Xn n × (E3 × E3)) :
    momsSwapEquiv n q = (q.1, (q.2.2, q.2.1)) := rfl

private lemma momsSwapEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (momsSwapEquiv n) (volume : Measure (Xn n × (E3 × E3)))
      (volume : Measure (Xn n × (E3 × E3))) := by
  have hsw : MeasurePreserving (Prod.swap : E3 × E3 → E3 × E3)
      (volume : Measure (E3 × E3)) (volume : Measure (E3 × E3)) :=
    MeasureTheory.Measure.measurePreserving_swap
  have h := (MeasurePreserving.id (volume : Measure (Xn n))).prod hsw
  change MeasurePreserving (momsSwapEquiv n) (volume.prod volume) (volume.prod volume)
  simpa [momsSwapEquiv, MeasurableEquiv.prodCongr, Equiv.prodCongr, MeasurableEquiv.prodComm,
    Equiv.prodComm, Prod.map] using h

/-- The composite *momentum swap then slot roll*: this is the substitution that exchanges the two
particle slots with the two momentum variables, in the order that produces the `(j,i)` pair out of
the `(i,j)` pair. -/
private def slotMomsSwapEquiv {n : ℕ} (i j : Fin n) :
    (Xn n × (E3 × E3)) ≃ᵐ (Xn n × (E3 × E3)) :=
  (momsSwapEquiv n).trans (pairSlotRollEquiv i j)

private lemma slotMomsSwapEquiv_apply {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (q : Xn n × (E3 × E3)) :
    slotMomsSwapEquiv i j q = pairSlotRoll i j (q.1, (q.2.2, q.2.1)) := by
  rw [slotMomsSwapEquiv, MeasurableEquiv.trans_apply, momsSwapEquiv_apply,
    pairSlotRollEquiv_apply hij]

private lemma slotMomsSwapEquiv_measurePreserving {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    MeasurePreserving (slotMomsSwapEquiv i j) (volume : Measure (Xn n × (E3 × E3)))
      (volume : Measure (Xn n × (E3 × E3))) :=
  (momsSwapEquiv_measurePreserving n).trans (pairSlotRollEquiv_measurePreserving i j)

/-! ## 5. Integrability of the two product-space integrands -/

/-- The general support set: configurations in the box, the two momentum variables in `boxL`. -/
private def mvBoxSet (n : ℕ) (ℓ : ℝ) : Set (Xn n × (E3 × E3)) :=
  Work.MB.boxPow n ℓ ×ˢ (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)

private lemma mvBoxSet_measurableSet (n : ℕ) (ℓ : ℝ) : MeasurableSet (mvBoxSet n ℓ) :=
  (Work.MB.measurableSet_boxPow n ℓ).prod
    ((Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ).prod
      (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ))

private lemma mvBoxSet_measure_ne_top (n : ℕ) (ℓ : ℝ) :
    (volume : Measure (Xn n × (E3 × E3))) (mvBoxSet n ℓ) ≠ ⊤ := by
  rw [mvBoxSet, MeasureTheory.Measure.volume_eq_prod (Xn n) (E3 × E3),
    MeasureTheory.Measure.prod_prod, MeasureTheory.Measure.volume_eq_prod E3 E3,
    MeasureTheory.Measure.prod_prod]
  exact ENNReal.mul_ne_top (Work.MB.volume_boxPow_lt_top n ℓ)
    (ENNReal.mul_ne_top
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).measure_lt_top.ne
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).measure_lt_top.ne)

/-- **The `MiddleU`-integrand is integrable on the product space.**  It is bounded by
`‖Θ‖·‖pinCond‖·‖MiddleU‖·‖Θ‖` and vanishes off `boxPow n ℓ × (boxL ℓ × boxL ℓ)`: outside the
configuration box `Θ q.1` vanishes, and if one of the two momentum variables is outside the box
then the *updated* configuration `q.1[i↦y][j↦u]` is outside it (its `i`-th resp. `j`-th coordinate
is `y` resp. `u`), so the second `Θ`-factor vanishes. -/
private theorem PairU_integrable {n : ℕ} {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ} {c : ℂ} {i j : Fin n} (hij : i ≠ j)
    {Θ : Xn n → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n (ellH v μ)) :
    Integrable (fun q : Xn n × (E3 × E3) => star (Θ q.1) * pinCond v μ c (q.1 i)
      * MiddleU v h fc fu μ N (q.1 j) q.2.1 q.2.2
      * Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2)) volume := by
  classical
  obtain ⟨Cm, hCm0, hCm⟩ := MiddleU_bdd v h fc fu μ N
  obtain ⟨Cp, hCp0, hCp⟩ := pinCond_bdd v μ c
  obtain ⟨CT, hCT⟩ := hΘb
  have hmeas : Measurable (fun q : Xn n × (E3 × E3) => star (Θ q.1) * pinCond v μ c (q.1 i)
      * MiddleU v h fc fu μ N (q.1 j) q.2.1 q.2.2
      * Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2)) := by
    have h1 : Measurable (fun q : Xn n × (E3 × E3) => star (Θ q.1)) :=
      continuous_star.measurable.comp (hΘm.comp measurable_fst)
    have h2 : Measurable (fun q : Xn n × (E3 × E3) => pinCond v μ c (q.1 i)) :=
      (pinCond_measurable v μ c).comp ((measurable_pi_apply i).comp measurable_fst)
    have h3 : Measurable (fun q : Xn n × (E3 × E3) =>
        MiddleU v h fc fu μ N (q.1 j) q.2.1 q.2.2) := by
      have hMU := MiddleU_measurable v h fc fu μ N
      fun_prop
    have h4 : Measurable (fun q : Xn n × (E3 × E3) =>
        Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2)) := by fun_prop
    exact ((h1.mul h2).mul h3).mul h4
  refine Work.MB.integrable_of_bdd_of_support (S := mvBoxSet n (ellH v μ))
    (mvBoxSet_measurableSet n (ellH v μ)) (mvBoxSet_measure_ne_top n (ellH v μ))
    hmeas.aestronglyMeasurable
    (C := (max CT 0 * max Cp 0) * (max Cm 0 * max CT 0)) ?_ ?_
  · intro q
    have h1 : ‖Θ q.1‖ ≤ max CT 0 := (hCT q.1).trans (le_max_left _ _)
    have h2 : ‖pinCond v μ c (q.1 i)‖ ≤ max Cp 0 := (hCp _).trans (le_max_left _ _)
    have h3 : ‖MiddleU v h fc fu μ N (q.1 j) q.2.1 q.2.2‖ ≤ max Cm 0 :=
      (hCm _ _ _).trans (le_max_left _ _)
    have h4 : ‖Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2)‖ ≤ max CT 0 :=
      (hCT _).trans (le_max_left _ _)
    have h12 : ‖Θ q.1‖ * ‖pinCond v μ c (q.1 i)‖ ≤ max CT 0 * max Cp 0 :=
      mul_le_mul h1 h2 (norm_nonneg _) (le_max_right _ _)
    have h123 : ‖Θ q.1‖ * ‖pinCond v μ c (q.1 i)‖
        * ‖MiddleU v h fc fu μ N (q.1 j) q.2.1 q.2.2‖ ≤ (max CT 0 * max Cp 0) * max Cm 0 :=
      mul_le_mul h12 h3 (norm_nonneg _) (mul_nonneg (le_max_right _ _) (le_max_right _ _))
    rw [norm_mul, norm_mul, norm_mul, norm_star]
    calc ‖Θ q.1‖ * ‖pinCond v μ c (q.1 i)‖ * ‖MiddleU v h fc fu μ N (q.1 j) q.2.1 q.2.2‖
          * ‖Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2)‖
        ≤ (max CT 0 * max Cp 0) * max Cm 0 * max CT 0 :=
          mul_le_mul h123 h4 (norm_nonneg _) (mul_nonneg (mul_nonneg (le_max_right _ _)
            (le_max_right _ _)) (le_max_right _ _))
      _ = (max CT 0 * max Cp 0) * (max Cm 0 * max CT 0) := by ring
  · intro q hq
    by_cases hx : q.1 ∈ Work.MB.boxPow n (ellH v μ)
    · by_cases hy : q.2.1 ∈ Work.BoseK15.corpusBox.boxL (ellH v μ)
      · by_cases hu : q.2.2 ∈ Work.BoseK15.corpusBox.boxL (ellH v μ)
        · exact absurd ⟨hx, ⟨hy, hu⟩⟩ hq
        · have h0 : Function.update (Function.update q.1 i q.2.1) j q.2.2
              ∉ Work.MB.boxPow n (ellH v μ) := by
            intro hmem
            exact hu (by
              have hc := (Work.MB.mem_boxPow_iff.mp hmem) j
              rwa [Function.update_self] at hc)
          have hΘ0 : Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) = 0 :=
            Function.notMem_support.mp fun hmem => h0 (hΘs hmem)
          simp only [hΘ0, mul_zero]
      · have h0 : Function.update (Function.update q.1 i q.2.1) j q.2.2
            ∉ Work.MB.boxPow n (ellH v μ) := by
          intro hmem
          exact hy (by
            have hc := (Work.MB.mem_boxPow_iff.mp hmem) i
            rwa [Function.update_of_ne hij, Function.update_self] at hc)
        have hΘ0 : Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) = 0 :=
          Function.notMem_support.mp fun hmem => h0 (hΘs hmem)
        simp only [hΘ0, mul_zero]
    · have hΘ0 : Θ q.1 = 0 := Function.notMem_support.mp fun hmem => hx (hΘs hmem)
      simp only [hΘ0, star_zero, zero_mul, mul_zero]

/-- **The inner `MiddleU`-integrand is integrable** for every fixed configuration. -/
private theorem PairU_integrable_inner {n : ℕ} {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ} {c : ℂ} {i j : Fin n} (hij : i ≠ j)
    {Θ : Xn n → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n (ellH v μ)) (x : Xn n) :
    Integrable (fun z : E3 × E3 => star (Θ x) * pinCond v μ c (x i)
      * MiddleU v h fc fu μ N (x j) z.1 z.2
      * Θ (Function.update (Function.update x i z.1) j z.2)) volume := by
  classical
  obtain ⟨Cm, hCm0, hCm⟩ := MiddleU_bdd v h fc fu μ N
  obtain ⟨Cp, hCp0, hCp⟩ := pinCond_bdd v μ c
  obtain ⟨CT, hCT⟩ := hΘb
  have hmeas : Measurable (fun z : E3 × E3 => star (Θ x) * pinCond v μ c (x i)
      * MiddleU v h fc fu μ N (x j) z.1 z.2
      * Θ (Function.update (Function.update x i z.1) j z.2)) := by
    have h1 : Measurable (fun z : E3 × E3 => star (Θ x)) := measurable_const
    have h2 : Measurable (fun z : E3 × E3 => pinCond v μ c (x i)) := measurable_const
    have h3 : Measurable (fun z : E3 × E3 => MiddleU v h fc fu μ N (x j) z.1 z.2) := by
      have hMU := MiddleU_measurable v h fc fu μ N
      fun_prop
    have h4 : Measurable (fun z : E3 × E3 =>
        Θ (Function.update (Function.update x i z.1) j z.2)) := by fun_prop
    exact ((h1.mul h2).mul h3).mul h4
  refine Work.MB.integrable_of_bdd_of_support
    (S := Work.BoseK15.corpusBox.boxL (ellH v μ) ×ˢ Work.BoseK15.corpusBox.boxL (ellH v μ))
    ((Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox (ellH v μ)).prod
      (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox (ellH v μ)))
    ?_ hmeas.aestronglyMeasurable
    (C := (max CT 0 * max Cp 0) * (max Cm 0 * max CT 0)) ?_ ?_
  · rw [MeasureTheory.Measure.volume_eq_prod E3 E3, MeasureTheory.Measure.prod_prod]
    exact ENNReal.mul_ne_top
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox (ellH v μ)).measure_lt_top.ne
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox (ellH v μ)).measure_lt_top.ne
  · intro z
    have h1 : ‖Θ x‖ ≤ max CT 0 := (hCT x).trans (le_max_left _ _)
    have h2 : ‖pinCond v μ c (x i)‖ ≤ max Cp 0 := (hCp _).trans (le_max_left _ _)
    have h3 : ‖MiddleU v h fc fu μ N (x j) z.1 z.2‖ ≤ max Cm 0 := (hCm _ _ _).trans (le_max_left _ _)
    have h4 : ‖Θ (Function.update (Function.update x i z.1) j z.2)‖ ≤ max CT 0 :=
      (hCT _).trans (le_max_left _ _)
    have h12 : ‖Θ x‖ * ‖pinCond v μ c (x i)‖ ≤ max CT 0 * max Cp 0 :=
      mul_le_mul h1 h2 (norm_nonneg _) (le_max_right _ _)
    have h123 : ‖Θ x‖ * ‖pinCond v μ c (x i)‖ * ‖MiddleU v h fc fu μ N (x j) z.1 z.2‖
        ≤ (max CT 0 * max Cp 0) * max Cm 0 :=
      mul_le_mul h12 h3 (norm_nonneg _) (mul_nonneg (le_max_right _ _) (le_max_right _ _))
    rw [norm_mul, norm_mul, norm_mul, norm_star]
    calc ‖Θ x‖ * ‖pinCond v μ c (x i)‖ * ‖MiddleU v h fc fu μ N (x j) z.1 z.2‖
          * ‖Θ (Function.update (Function.update x i z.1) j z.2)‖
        ≤ (max CT 0 * max Cp 0) * max Cm 0 * max CT 0 :=
          mul_le_mul h123 h4 (norm_nonneg _) (mul_nonneg (mul_nonneg (le_max_right _ _)
            (le_max_right _ _)) (le_max_right _ _))
      _ = (max CT 0 * max Cp 0) * (max Cm 0 * max CT 0) := by ring
  · intro z hz
    by_cases hy : z.1 ∈ Work.BoseK15.corpusBox.boxL (ellH v μ)
    · by_cases hu : z.2 ∈ Work.BoseK15.corpusBox.boxL (ellH v μ)
      · exact absurd ⟨hy, hu⟩ hz
      · have h0 : Function.update (Function.update x i z.1) j z.2
            ∉ Work.MB.boxPow n (ellH v μ) := by
          intro hmem
          exact hu (by
            have hc := (Work.MB.mem_boxPow_iff.mp hmem) j
            rwa [Function.update_self] at hc)
        have hΘ0 : Θ (Function.update (Function.update x i z.1) j z.2) = 0 :=
          Function.notMem_support.mp fun hmem => h0 (hΘs hmem)
        simp only [hΘ0, mul_zero]
    · have h0 : Function.update (Function.update x i z.1) j z.2
          ∉ Work.MB.boxPow n (ellH v μ) := by
        intro hmem
        exact hy (by
          have hc := (Work.MB.mem_boxPow_iff.mp hmem) i
          rwa [Function.update_of_ne hij, Function.update_self] at hc)
      have hΘ0 : Θ (Function.update (Function.update x i z.1) j z.2) = 0 :=
        Function.notMem_support.mp fun hmem => h0 (hΘs hmem)
      simp only [hΘ0, mul_zero]

/-- **The `MiddleV`-integrand is integrable on the product space** (same argument, with the two
slots replaced in the opposite order). -/
private theorem PairV_integrable {n : ℕ} {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ} {c : ℂ} {i j : Fin n} (hij : i ≠ j)
    {Θ : Xn n → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n (ellH v μ)) :
    Integrable (fun q : Xn n × (E3 × E3) => star (Θ q.1)
      * MiddleV v h fc fu μ N c (q.1 j) q.2.1 (q.1 i) q.2.2
      * Θ (Function.update (Function.update q.1 j q.2.1) i q.2.2)) volume := by
  classical
  obtain ⟨Cm, hCm0, hCm⟩ := MiddleV_bdd v h fc fu μ N c
  obtain ⟨CT, hCT⟩ := hΘb
  have hmeas : Measurable (fun q : Xn n × (E3 × E3) => star (Θ q.1)
      * MiddleV v h fc fu μ N c (q.1 j) q.2.1 (q.1 i) q.2.2
      * Θ (Function.update (Function.update q.1 j q.2.1) i q.2.2)) := by
    have h1 : Measurable (fun q : Xn n × (E3 × E3) => star (Θ q.1)) :=
      continuous_star.measurable.comp (hΘm.comp measurable_fst)
    have h2 : Measurable (fun q : Xn n × (E3 × E3) =>
        MiddleV v h fc fu μ N c (q.1 j) q.2.1 (q.1 i) q.2.2) := by
      have hMV := MiddleV_measurable v h fc fu μ N c
      fun_prop
    have h3 : Measurable (fun q : Xn n × (E3 × E3) =>
        Θ (Function.update (Function.update q.1 j q.2.1) i q.2.2)) := by fun_prop
    exact (h1.mul h2).mul h3
  refine Work.MB.integrable_of_bdd_of_support (S := mvBoxSet n (ellH v μ))
    (mvBoxSet_measurableSet n (ellH v μ)) (mvBoxSet_measure_ne_top n (ellH v μ))
    hmeas.aestronglyMeasurable
    (C := (max CT 0 * max Cm 0) * max CT 0) ?_ ?_
  · intro q
    have h1 : ‖Θ q.1‖ ≤ max CT 0 := (hCT q.1).trans (le_max_left _ _)
    have h3 : ‖MiddleV v h fc fu μ N c (q.1 j) q.2.1 (q.1 i) q.2.2‖ ≤ max Cm 0 :=
      (hCm _ _ _ _).trans (le_max_left _ _)
    have h4 : ‖Θ (Function.update (Function.update q.1 j q.2.1) i q.2.2)‖ ≤ max CT 0 :=
      (hCT _).trans (le_max_left _ _)
    have h13 : ‖Θ q.1‖ * ‖MiddleV v h fc fu μ N c (q.1 j) q.2.1 (q.1 i) q.2.2‖
        ≤ max CT 0 * max Cm 0 := mul_le_mul h1 h3 (norm_nonneg _) (le_max_right _ _)
    rw [norm_mul, norm_mul, norm_star]
    calc ‖Θ q.1‖ * ‖MiddleV v h fc fu μ N c (q.1 j) q.2.1 (q.1 i) q.2.2‖
          * ‖Θ (Function.update (Function.update q.1 j q.2.1) i q.2.2)‖
        ≤ (max CT 0 * max Cm 0) * max CT 0 :=
          mul_le_mul h13 h4 (norm_nonneg _) (mul_nonneg (le_max_right _ _) (le_max_right _ _))
      _ = (max CT 0 * max Cm 0) * max CT 0 := rfl
  · intro q hq
    by_cases hx : q.1 ∈ Work.MB.boxPow n (ellH v μ)
    · by_cases hy : q.2.1 ∈ Work.BoseK15.corpusBox.boxL (ellH v μ)
      · by_cases hu : q.2.2 ∈ Work.BoseK15.corpusBox.boxL (ellH v μ)
        · exact absurd ⟨hx, ⟨hy, hu⟩⟩ hq
        · have h0 : Function.update (Function.update q.1 j q.2.1) i q.2.2
              ∉ Work.MB.boxPow n (ellH v μ) := by
            intro hmem
            exact hu (by
              have hc := (Work.MB.mem_boxPow_iff.mp hmem) i
              rwa [Function.update_self] at hc)
          have hΘ0 : Θ (Function.update (Function.update q.1 j q.2.1) i q.2.2) = 0 :=
            Function.notMem_support.mp fun hmem => h0 (hΘs hmem)
          simp only [hΘ0, mul_zero]
      · have h0 : Function.update (Function.update q.1 j q.2.1) i q.2.2
            ∉ Work.MB.boxPow n (ellH v μ) := by
          intro hmem
          exact hy (by
            have hc := (Work.MB.mem_boxPow_iff.mp hmem) j
            rwa [Function.update_of_ne (Ne.symm hij), Function.update_self] at hc)
        have hΘ0 : Θ (Function.update (Function.update q.1 j q.2.1) i q.2.2) = 0 :=
          Function.notMem_support.mp fun hmem => h0 (hΘs hmem)
        simp only [hΘ0, mul_zero]
    · have hΘ0 : Θ q.1 = 0 := Function.notMem_support.mp fun hmem => hx (hΘs hmem)
      simp only [hΘ0, star_zero, zero_mul, mul_zero]

/-- **The inner `MiddleV`-integrand is integrable** for every fixed configuration. -/
private theorem PairV_integrable_inner {n : ℕ} {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ} {c : ℂ} {i j : Fin n} (hij : i ≠ j)
    {Θ : Xn n → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n (ellH v μ)) (x : Xn n) :
    Integrable (fun z : E3 × E3 => star (Θ x)
      * MiddleV v h fc fu μ N c (x j) z.1 (x i) z.2
      * Θ (Function.update (Function.update x j z.1) i z.2)) volume := by
  classical
  obtain ⟨Cm, hCm0, hCm⟩ := MiddleV_bdd v h fc fu μ N c
  obtain ⟨CT, hCT⟩ := hΘb
  have hmeas : Measurable (fun z : E3 × E3 => star (Θ x)
      * MiddleV v h fc fu μ N c (x j) z.1 (x i) z.2
      * Θ (Function.update (Function.update x j z.1) i z.2)) := by
    have h1 : Measurable (fun z : E3 × E3 => star (Θ x)) := measurable_const
    have h2 : Measurable (fun z : E3 × E3 =>
        MiddleV v h fc fu μ N c (x j) z.1 (x i) z.2) := by
      have hMV := MiddleV_measurable v h fc fu μ N c
      fun_prop
    have h3 : Measurable (fun z : E3 × E3 =>
        Θ (Function.update (Function.update x j z.1) i z.2)) := by fun_prop
    exact (h1.mul h2).mul h3
  refine Work.MB.integrable_of_bdd_of_support
    (S := Work.BoseK15.corpusBox.boxL (ellH v μ) ×ˢ Work.BoseK15.corpusBox.boxL (ellH v μ))
    ((Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox (ellH v μ)).prod
      (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox (ellH v μ)))
    ?_ hmeas.aestronglyMeasurable
    (C := (max CT 0 * max Cm 0) * max CT 0) ?_ ?_
  · rw [MeasureTheory.Measure.volume_eq_prod E3 E3, MeasureTheory.Measure.prod_prod]
    exact ENNReal.mul_ne_top
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox (ellH v μ)).measure_lt_top.ne
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox (ellH v μ)).measure_lt_top.ne
  · intro z
    have h1 : ‖Θ x‖ ≤ max CT 0 := (hCT x).trans (le_max_left _ _)
    have h3 : ‖MiddleV v h fc fu μ N c (x j) z.1 (x i) z.2‖ ≤ max Cm 0 :=
      (hCm _ _ _ _).trans (le_max_left _ _)
    have h4 : ‖Θ (Function.update (Function.update x j z.1) i z.2)‖ ≤ max CT 0 :=
      (hCT _).trans (le_max_left _ _)
    have h13 : ‖Θ x‖ * ‖MiddleV v h fc fu μ N c (x j) z.1 (x i) z.2‖ ≤ max CT 0 * max Cm 0 :=
      mul_le_mul h1 h3 (norm_nonneg _) (le_max_right _ _)
    rw [norm_mul, norm_mul, norm_star]
    calc ‖Θ x‖ * ‖MiddleV v h fc fu μ N c (x j) z.1 (x i) z.2‖
          * ‖Θ (Function.update (Function.update x j z.1) i z.2)‖
        ≤ (max CT 0 * max Cm 0) * max CT 0 :=
          mul_le_mul h13 h4 (norm_nonneg _) (mul_nonneg (le_max_right _ _) (le_max_right _ _))
      _ = (max CT 0 * max Cm 0) * max CT 0 := rfl
  · intro z hz
    by_cases hy : z.1 ∈ Work.BoseK15.corpusBox.boxL (ellH v μ)
    · by_cases hu : z.2 ∈ Work.BoseK15.corpusBox.boxL (ellH v μ)
      · exact absurd ⟨hy, hu⟩ hz
      · have h0 : Function.update (Function.update x j z.1) i z.2
            ∉ Work.MB.boxPow n (ellH v μ) := by
          intro hmem
          exact hu (by
            have hc := (Work.MB.mem_boxPow_iff.mp hmem) i
            rwa [Function.update_self] at hc)
        have hΘ0 : Θ (Function.update (Function.update x j z.1) i z.2) = 0 :=
          Function.notMem_support.mp fun hmem => h0 (hΘs hmem)
        simp only [hΘ0, mul_zero]
    · have h0 : Function.update (Function.update x j z.1) i z.2
          ∉ Work.MB.boxPow n (ellH v μ) := by
        intro hmem
        exact hy (by
          have hc := (Work.MB.mem_boxPow_iff.mp hmem) j
          rwa [Function.update_of_ne (Ne.symm hij), Function.update_self] at hc)
      have hΘ0 : Θ (Function.update (Function.update x j z.1) i z.2) = 0 :=
        Function.notMem_support.mp fun hmem => h0 (hΘs hmem)
      simp only [hΘ0, mul_zero]

/-! ## 6. The per-pair conjugation -/

/-- `star` commutes with the Bochner integral, unconditionally. -/
private theorem star_integral_aux {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℂ) :
    star (∫ a, f a ∂μ) = ∫ a, star (f a) ∂μ := by
  simpa using (integral_conj (μ := μ) (𝕜 := ℂ) (f := f)).symm

/-- **The per-pair conjugation.**  For `i ≠ j`,
`star (∫∫∫ conj(Θ x)·pinCond(x_i)·MiddleU(x_j,y,u)·Θ(x[i↦y][j↦u]))` is the `MiddleV`-integral at the
*swapped* pair `(j,i)` with the two momentum variables exchanged. -/
private theorem pair_conj {n : ℕ} {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ} {c : ℂ}
    {Θ : Xn n → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n (ellH v μ))
    {i j : Fin n} (hij : i ≠ j) :
    star (∫ x : Xn n, ∫ y : E3, ∫ u : E3,
        star (Θ x) * pinCond v μ c (x i) * MiddleU v h fc fu μ N (x j) y u
          * Θ (Function.update (Function.update x i y) j u))
      = ∫ x : Xn n, ∫ y : E3, ∫ u : E3,
        star (Θ x) * MiddleV v h fc fu μ N c (x j) y (x i) u
          * Θ (Function.update (Function.update x j y) i u) := by
  classical
  set RU : Xn n × (E3 × E3) → ℂ := fun q => star (Θ q.1) * pinCond v μ c (q.1 i)
      * MiddleU v h fc fu μ N (q.1 j) q.2.1 q.2.2
      * Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) with hRUdef
  set RV : Xn n × (E3 × E3) → ℂ := fun q => star (Θ q.1)
      * MiddleV v h fc fu μ N c (q.1 j) q.2.1 (q.1 i) q.2.2
      * Θ (Function.update (Function.update q.1 j q.2.1) i q.2.2) with hRVdef
  have hRUint : Integrable RU volume := by
    simp only [hRUdef]
    exact PairU_integrable hij hΘm hΘb hΘs
  have hRVint : Integrable RV volume := by
    simp only [hRVdef]
    exact PairV_integrable hij hΘm hΘb hΘs
  have hRUinner : ∀ x : Xn n, Integrable (fun z : E3 × E3 => RU (x, z)) volume := by
    intro x
    simp only [hRUdef]
    exact PairU_integrable_inner hij hΘm hΘb hΘs x
  have hRVinner : ∀ x : Xn n, Integrable (fun z : E3 × E3 => RV (x, z)) volume := by
    intro x
    simp only [hRVdef]
    exact PairV_integrable_inner hij hΘm hΘb hΘs x
  have hRUconv : (∫ x : Xn n, ∫ y : E3, ∫ u : E3,
      star (Θ x) * pinCond v μ c (x i) * MiddleU v h fc fu μ N (x j) y u
        * Θ (Function.update (Function.update x i y) j u)) = ∫ q : Xn n × (E3 × E3), RU q := by
    have h1 : (∫ x : Xn n, ∫ y : E3, ∫ u : E3,
        star (Θ x) * pinCond v μ c (x i) * MiddleU v h fc fu μ N (x j) y u
          * Θ (Function.update (Function.update x i y) j u))
        = ∫ x : Xn n, ∫ z : E3 × E3, RU (x, z) := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      exact (MeasureTheory.integral_prod (f := fun z : E3 × E3 => star (Θ x) * pinCond v μ c (x i)
        * MiddleU v h fc fu μ N (x j) z.1 z.2
        * Θ (Function.update (Function.update x i z.1) j z.2)) (hRUinner x)).symm
    exact h1.trans (MeasureTheory.integral_prod (μ := (volume : Measure (Xn n)))
      (ν := (volume : Measure (E3 × E3))) RU hRUint).symm
  have hRVconv : (∫ x : Xn n, ∫ y : E3, ∫ u : E3,
      star (Θ x) * MiddleV v h fc fu μ N c (x j) y (x i) u
        * Θ (Function.update (Function.update x j y) i u)) = ∫ q : Xn n × (E3 × E3), RV q := by
    have h1 : (∫ x : Xn n, ∫ y : E3, ∫ u : E3,
        star (Θ x) * MiddleV v h fc fu μ N c (x j) y (x i) u
          * Θ (Function.update (Function.update x j y) i u))
        = ∫ x : Xn n, ∫ z : E3 × E3, RV (x, z) := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      exact (MeasureTheory.integral_prod (f := fun z : E3 × E3 => star (Θ x)
        * MiddleV v h fc fu μ N c (x j) z.1 (x i) z.2
        * Θ (Function.update (Function.update x j z.1) i z.2)) (hRVinner x)).symm
    exact h1.trans (MeasureTheory.integral_prod (μ := (volume : Measure (Xn n)))
      (ν := (volume : Measure (E3 × E3))) RV hRVint).symm
  have hpoint : ∀ q : Xn n × (E3 × E3), star (RU (slotMomsSwapEquiv i j q)) = RV q := by
    intro q
    obtain ⟨x, y, u⟩ := q
    rw [slotMomsSwapEquiv_apply hij]
    have hxi : (Function.update (Function.update x i u) j y) i = u := by
      rw [Function.update_of_ne hij, Function.update_self]
    have hxj : (Function.update (Function.update x i u) j y) j = y := by
      rw [Function.update_self]
    have hundo : Function.update (Function.update (Function.update (Function.update x i u) j y)
        i (x i)) j (x j) = x := by
      funext k
      by_cases hki : k = i
      · subst hki
        simp [Function.update_apply, hij]
      · by_cases hkj : k = j
        · subst hkj
          simp [Function.update_apply, hki, hij, hij.symm]
        · simp [Function.update_apply, hki, hkj]
    have hcomm : Function.update (Function.update x i u) j y
        = Function.update (Function.update x j y) i u := Function.update_comm hij u y x
    have hMV := MiddleV_eq_star_pinCond_mul_star_MiddleU v h fc fu μ N c (x j) y (x i) u
    simp only [hRUdef, hRVdef, pairSlotRoll, hxi, hxj, hundo, star_mul, star_star]
    rw [hMV, hcomm]
    ring
  calc star (∫ x : Xn n, ∫ y : E3, ∫ u : E3,
        star (Θ x) * pinCond v μ c (x i) * MiddleU v h fc fu μ N (x j) y u
          * Θ (Function.update (Function.update x i y) j u))
      = star (∫ q : Xn n × (E3 × E3), RU q) := by rw [hRUconv]
    _ = ∫ q : Xn n × (E3 × E3), star (RU q) := star_integral_aux volume RU
    _ = ∫ q : Xn n × (E3 × E3), star (RU (slotMomsSwapEquiv i j q)) :=
        ((slotMomsSwapEquiv_measurePreserving hij).integral_comp'
          (fun q : Xn n × (E3 × E3) => star (RU q))).symm
    _ = ∫ q : Xn n × (E3 × E3), RV q :=
        integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∫ x : Xn n, ∫ y : E3, ∫ u : E3,
        star (Θ x) * MiddleV v h fc fu μ N c (x j) y (x i) u
          * Θ (Function.update (Function.update x j y) i u) := hRVconv.symm

/-! ## 7. The pair sum -/

theorem pairSum_MiddleV_star_MiddleU {n : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {fc fu : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ} {c : ℂ}
    (Θ : Work.BoseDict.Xn n → ℂ) (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n (Work.BoseBoxFock.ellH v μ)) :
    (∑ p ∈ Submission.BoseGases.pairSet n,
        ∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3),
          ∫ u : EuclideanSpace ℝ (Fin 3),
          star (Θ x) * Work.BoseBoxFock.PCFU.MiddleV v h fc fu μ N c (x p.1) y (x p.2) u
            * Θ (Function.update (Function.update x p.1 y) p.2 u))
      = star (∑ p ∈ Submission.BoseGases.pairSet n,
          ∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3),
            ∫ u : EuclideanSpace ℝ (Fin 3),
            star (Θ x) * Work.BoseBoxFock.pinCond v μ c (x p.1)
              * Work.BoseBoxFock.PCFU.MiddleU v h fc fu μ N (x p.2) y u
              * Θ (Function.update (Function.update x p.1 y) p.2 u)) := by
  classical
  have hmem : ∀ p : Fin n × Fin n,
      p ∈ Submission.BoseGases.pairSet n ↔ p.1 ≠ p.2 := by
    intro p
    simp [Submission.BoseGases.pairSet]
  have key : ∀ p ∈ Submission.BoseGases.pairSet n,
      star (∫ x : Xn n, ∫ y : E3, ∫ u : E3,
          star (Θ x) * pinCond v μ c (x p.2) * MiddleU v h fc fu μ N (x p.1) y u
            * Θ (Function.update (Function.update x p.2 y) p.1 u))
        = ∫ x : Xn n, ∫ y : E3, ∫ u : E3,
          star (Θ x) * MiddleV v h fc fu μ N c (x p.1) y (x p.2) u
            * Θ (Function.update (Function.update x p.1 y) p.2 u) := by
    intro p hp
    exact pair_conj (i := p.2) (j := p.1) hΘm hΘb hΘs ((hmem p).mp hp).symm
  have hbij : (∑ p ∈ Submission.BoseGases.pairSet n,
        star (∫ x : Xn n, ∫ y : E3, ∫ u : E3,
          star (Θ x) * pinCond v μ c (x p.2) * MiddleU v h fc fu μ N (x p.1) y u
            * Θ (Function.update (Function.update x p.2 y) p.1 u)))
      = ∑ p ∈ Submission.BoseGases.pairSet n,
        star (∫ x : Xn n, ∫ y : E3, ∫ u : E3,
          star (Θ x) * pinCond v μ c (x p.1) * MiddleU v h fc fu μ N (x p.2) y u
            * Θ (Function.update (Function.update x p.1 y) p.2 u)) := by
    refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p hp
      exact (hmem _).mpr ((hmem p).mp hp).symm
    · intro p₁ _ p₂ _ hh
      exact Prod.ext (congrArg Prod.snd hh) (congrArg Prod.fst hh)
    · intro q hq
      exact ⟨(q.2, q.1), (hmem _).mpr ((hmem q).mp hq).symm, rfl⟩
    · intro p _
      rfl
  calc (∑ p ∈ Submission.BoseGases.pairSet n,
        ∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3),
          ∫ u : EuclideanSpace ℝ (Fin 3),
          star (Θ x) * Work.BoseBoxFock.PCFU.MiddleV v h fc fu μ N c (x p.1) y (x p.2) u
            * Θ (Function.update (Function.update x p.1 y) p.2 u))
      = ∑ p ∈ Submission.BoseGases.pairSet n,
          star (∫ x : Xn n, ∫ y : E3, ∫ u : E3,
            star (Θ x) * pinCond v μ c (x p.2) * MiddleU v h fc fu μ N (x p.1) y u
              * Θ (Function.update (Function.update x p.2 y) p.1 u)) :=
        Finset.sum_congr rfl (fun p hp => (key p hp).symm)
    _ = ∑ p ∈ Submission.BoseGases.pairSet n,
          star (∫ x : Xn n, ∫ y : E3, ∫ u : E3,
            star (Θ x) * pinCond v μ c (x p.1) * MiddleU v h fc fu μ N (x p.2) y u
              * Θ (Function.update (Function.update x p.1 y) p.2 u)) := hbij
    _ = star (∑ p ∈ Submission.BoseGases.pairSet n,
          ∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3),
            ∫ u : EuclideanSpace ℝ (Fin 3),
            star (Θ x) * Work.BoseBoxFock.pinCond v μ c (x p.1)
              * Work.BoseBoxFock.PCFU.MiddleU v h fc fu μ N (x p.2) y u
              * Θ (Function.update (Function.update x p.1 y) p.2 u)) :=
        (star_sum _ _).symm

end Work.BoseBoxFock.PCFU
