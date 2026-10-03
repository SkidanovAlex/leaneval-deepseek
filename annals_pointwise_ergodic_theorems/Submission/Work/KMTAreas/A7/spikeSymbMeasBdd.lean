/-
# `Work.KMTAreas.A7.spikeSymbMeasBdd`

Measurability on `𝕋² = (ℝ/ℤ)²` and uniform boundedness of the §6 *spike symbol*

  `spikeSymb ρ P l₁ l₂ k₁ k₂ N β₁ β₂ θ₁ θ₂
     = Φ₁(θ₁ - β₁) · Φ₂(θ₂ - β₂) · M₀(β₁,β₂)(lift (θ₁ - β₁), lift (θ₂ - β₂))`,

where `Φ₁ = periodize (varphiN N k₁)`, `Φ₂ = periodize (varphitildeN d N k₂)` are the two
periodised narrow bumps of the §6 collapse (`A7/spikeDefs.lean`) and

  `M₀ = weylAvg - m_Ẑ · m̃_{N,ℝ}`

is the symbol difference of Proposition `mod-approx` (`A7/ModelApproxDefs.lean`).

This pair of facts (a measurable and bounded symbol on the probability space `𝕋²`) is exactly the
hypothesis under which the double Fourier coefficient `coeff` is defined by an absolutely
convergent iterated Bochner integral, hence under which the linearity of `coeff`
(`A7/coeffLinear.lean`) applies to the spike decomposition of §6.  It is consumed by
`A7/spikeFinsetMassBound.lean`.

The two facts are proved directly from the definitions:

* **Measurability.**  Using the support hypotheses `hsup₁`, `hsup₂` (`wᵢ < 1/2`) the periodisation
  collapses: `periodize φ (θ - β) = φ (lift (θ - β))` (`A7/liftCollapse.lean`).  There remains the
  measurability of `(θ₁,θ₂) ↦ M₀(…)(lift (θ₁-β₁), lift (θ₂-β₂))`: `lift` is measurable (the
  canonical representative map of `AddCircle.equivIco`), `weylAvg` is a finite sum of characters
  hence continuous in the real variables `(ξ₁,ξ₂)`, and `mTilde` is a *parametric* interval
  integral: the integrand `(t,ξ₁,ξ₂) ↦ e(ξ₁Nt + ξ₂P(Nt))` is continuous, so the integral over
  `[1/2,1]` is measurable in `(ξ₁,ξ₂)` by
  `MeasureTheory.StronglyMeasurable.integral_prod_right'`.

* **Boundedness.**  `‖M₀‖ ≤ ‖weylAvg‖ + ‖m_Ẑ‖·‖m̃‖ ≤ ‖N⁻¹‖·#(N/2,N] + ‖m_Ẑ‖·(1/2)`
  (the oscillatory integral of a unimodular integrand over `[1/2,1]` has modulus `≤ 1/2`), and
  `‖Φᵢ‖ ≤ 2` by the collapse together with `‖η‖ ≤ 1`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.spikeDefs
import Submission.Work.KMTAreas.A7.M0_iteratedDeriv_bound

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset

/-! ## §1  Elementary facts about the cutoff `η` and the bumps `φ_N`, `φ̃_N` -/

/-- The continuous exponential `e(x) = exp(2πix)` is continuous. -/
private lemma continuous_ee_local : Continuous ee := by
  unfold ee; fun_prop

/-- `‖e(x)‖ = 1`. -/
private lemma norm_ee_local (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee
  rw [show (2 : ℂ) * ↑Real.pi * Complex.I * ↑x = ↑(2 * Real.pi * x) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The additive character `fourier n` of `𝕋 = ℝ/ℤ` is unimodular. -/
private lemma norm_fourier_local (n : ℤ) (x : AddCircle (1 : ℝ)) :
    ‖fourier (T := 1) n x‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

/-- The cutoff `η = kmtEta` is continuous. -/
private lemma continuous_kmtEta_local : Continuous Work.KMTContract.kmtEta :=
  Complex.continuous_ofReal.comp
    ((ContDiffBump.contDiff Work.KMTContract.kmtBump (n := ⊤)).continuous)

/-- `‖η a - η b‖ ≤ 2`, since `‖η‖ ≤ 1`. -/
private lemma norm_kmtEta_sub_le_two (a b : ℝ) :
    ‖Work.KMTContract.kmtEta a - Work.KMTContract.kmtEta b‖ ≤ 2 := by
  have ha := Work.KMTContract.norm_kmtEta_le a
  have hb := Work.KMTContract.norm_kmtEta_le b
  have h := norm_sub_le (Work.KMTContract.kmtEta a) (Work.KMTContract.kmtEta b)
  linarith

/-- `varphiN N k` is continuous. -/
private lemma continuous_varphiN_local (N k : ℕ) : Continuous (varphiN N k) := by
  unfold varphiN
  split_ifs with hk
  · exact continuous_kmtEta_local.comp (continuous_const.mul continuous_id)
  · exact (continuous_kmtEta_local.comp (continuous_const.mul continuous_id)).sub
      (continuous_kmtEta_local.comp (continuous_const.mul continuous_id))

/-- `varphitildeN d N k` is continuous. -/
private lemma continuous_varphitildeN_local (d N k : ℕ) : Continuous (varphitildeN d N k) := by
  unfold varphitildeN
  split_ifs with hk
  · exact continuous_kmtEta_local.comp (continuous_const.mul continuous_id)
  · exact (continuous_kmtEta_local.comp (continuous_const.mul continuous_id)).sub
      (continuous_kmtEta_local.comp (continuous_const.mul continuous_id))

/-- `varphiN N k` is measurable. -/
private lemma measurable_varphiN_local (N k : ℕ) : Measurable (varphiN N k) :=
  (continuous_varphiN_local N k).measurable

/-- `varphitildeN d N k` is measurable. -/
private lemma measurable_varphitildeN_local (d N k : ℕ) : Measurable (varphitildeN d N k) :=
  (continuous_varphitildeN_local d N k).measurable

/-- `‖φ_N‖ ≤ 2`. -/
private lemma norm_varphiN_le_two_local (N k : ℕ) (x : ℝ) : ‖varphiN N k x‖ ≤ 2 := by
  unfold varphiN
  split_ifs with hk
  · exact le_trans (Work.KMTContract.norm_kmtEta_le _) (by norm_num)
  · exact norm_kmtEta_sub_le_two _ _

/-- `‖φ̃_N‖ ≤ 2`. -/
private lemma norm_varphitildeN_le_two_local (d N k : ℕ) (x : ℝ) :
    ‖varphitildeN d N k x‖ ≤ 2 := by
  unfold varphitildeN
  split_ifs with hk
  · exact le_trans (Work.KMTContract.norm_kmtEta_le _) (by norm_num)
  · exact norm_kmtEta_sub_le_two _ _

/-! ## §2  The discrete average `weylAvg` and the symbol difference `M₀` -/

/-- Every summand of the discrete average is unimodular. -/
private lemma norm_momPhase_local (P : Polynomial ℤ) (N : ℕ)
    (α₁ α₂ : AddCircle (1 : ℝ)) (ξ₁ ξ₂ : ℝ) (n : ℤ) :
    ‖momPhase P N α₁ α₂ ξ₁ ξ₂ n‖ = 1 := by
  rw [momPhase, norm_mul, norm_mul, norm_fourier_local, norm_fourier_local, norm_ee_local]
  norm_num

/-- The oscillatory integral `m̃` of a unimodular integrand over an interval of length `1/2`. -/
private lemma norm_mTilde_local (P : Polynomial ℤ) (N : ℕ) (ξ₁ ξ₂ : ℝ) :
    ‖mTilde P N ξ₁ ξ₂‖ ≤ 1 / 2 := by
  unfold mTilde
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 1) (fun t _ => ?_)).trans
    (le_of_eq ?_)
  · exact le_of_eq (norm_ee_local _)
  · rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 - 1/2)]; norm_num

/-- The discrete average is bounded by `‖N⁻¹‖ · #(N/2,N]`. -/
private lemma norm_weylAvg_local (P : Polynomial ℤ) (N : ℕ)
    (α₁ α₂ : AddCircle (1 : ℝ)) (ξ₁ ξ₂ : ℝ) :
    ‖weylAvg P N α₁ α₂ ξ₁ ξ₂‖ ≤ ‖((N : ℂ))⁻¹‖ * ((Finset.Ioc (N / 2) N).card : ℝ) := by
  unfold weylAvg
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖∑ n ∈ Finset.Ioc (N / 2) N, momPhase P N α₁ α₂ ξ₁ ξ₂ (n : ℤ)‖
      ≤ ∑ n ∈ Finset.Ioc (N / 2) N, ‖momPhase P N α₁ α₂ ξ₁ ξ₂ (n : ℤ)‖ := norm_sum_le _ _
    _ = ∑ _n ∈ Finset.Ioc (N / 2) N, (1 : ℝ) :=
        Finset.sum_congr rfl (fun n _ => norm_momPhase_local P N α₁ α₂ ξ₁ ξ₂ (n : ℤ))
    _ = ((Finset.Ioc (N / 2) N).card : ℝ) := by simp

/-- The elementary bound for the symbol difference `M₀`. -/
private lemma norm_M0_local (P : Polynomial ℤ) (N q : ℕ) (α₁ α₂ : AddCircle (1 : ℝ))
    (ξ₁ ξ₂ : ℝ) :
    ‖M0 P N q α₁ α₂ ξ₁ ξ₂‖
      ≤ ‖((N : ℂ))⁻¹‖ * ((Finset.Ioc (N / 2) N).card : ℝ) + ‖mZ P q α₁ α₂‖ * (1 / 2) := by
  unfold M0
  refine (norm_sub_le _ _).trans (add_le_add (norm_weylAvg_local P N α₁ α₂ ξ₁ ξ₂) ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_mTilde_local P N ξ₁ ξ₂) (norm_nonneg _)

/-! ## §3  Measurability of `M₀` in the real variables -/

/-- `weylAvg` is continuous in the pair `(ξ₁,ξ₂) ∈ ℝ²`. -/
private lemma continuous_weylAvg_pair (P : Polynomial ℤ) (N : ℕ)
    (α₁ α₂ : AddCircle (1 : ℝ)) :
    Continuous (fun p : ℝ × ℝ => weylAvg P N α₁ α₂ p.1 p.2) := by
  have h : (fun p : ℝ × ℝ => weylAvg P N α₁ α₂ p.1 p.2)
      = fun p : ℝ × ℝ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
          momPhase P N α₁ α₂ p.1 p.2 (n : ℤ) := rfl
  rw [h]
  refine Continuous.const_mul ?_ _
  refine continuous_finsetSum _ (fun n _ => ?_)
  refine ((continuous_const.mul continuous_const).mul ?_)
  refine continuous_ee_local.comp ?_
  exact (continuous_fst.mul continuous_const).add (continuous_snd.mul continuous_const)

/-- The oscillatory integral `mTilde` is measurable in the pair `(ξ₁,ξ₂) ∈ ℝ²` (a parametric
interval integral of a continuous integrand). -/
private lemma measurable_mTilde_pair (P : Polynomial ℤ) (N : ℕ) :
    Measurable (fun p : ℝ × ℝ => mTilde P N p.1 p.2) := by
  have hP : Continuous (fun t : ℝ => PevalR P ((N : ℝ) * t)) :=
    (Polynomial.continuous (P.map (Int.castRingHom ℝ))).comp (continuous_const.mul continuous_id)
  have hK : Measurable (fun q : ℝ × (ℝ × ℝ) =>
      ee (q.2.1 * (N : ℝ) * q.1 + q.2.2 * PevalR P ((N : ℝ) * q.1))) := by
    refine continuous_ee_local.measurable.comp ?_
    exact (((continuous_snd.fst.mul continuous_const).mul continuous_fst).add
      (continuous_snd.snd.mul (hP.comp continuous_fst))).measurable
  rw [show (fun p : ℝ × ℝ => mTilde P N p.1 p.2)
      = fun p : ℝ × ℝ => ∫ t in (1 / 2 : ℝ)..1,
          ee (p.1 * (N : ℝ) * t + p.2 * PevalR P ((N : ℝ) * t)) from rfl]
  rw [show (fun p : ℝ × ℝ => ∫ t in (1 / 2 : ℝ)..1,
        ee (p.1 * (N : ℝ) * t + p.2 * PevalR P ((N : ℝ) * t)))
      = fun p : ℝ × ℝ => ∫ t, ee (p.1 * (N : ℝ) * t + p.2 * PevalR P ((N : ℝ) * t))
          ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) from
    funext fun p => intervalIntegral.integral_of_le (by norm_num)]
  exact (MeasureTheory.StronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))
    (f := fun q : (ℝ × ℝ) × ℝ =>
      ee (q.1.1 * (N : ℝ) * q.2 + q.1.2 * PevalR P ((N : ℝ) * q.2)))
    (hK.comp (measurable_snd.prodMk measurable_fst)).stronglyMeasurable).measurable

/-- `M₀` is measurable in the pair `(ξ₁,ξ₂) ∈ ℝ²`. -/
private lemma measurable_M0_pair (P : Polynomial ℤ) (N q : ℕ) (α₁ α₂ : AddCircle (1 : ℝ)) :
    Measurable (fun p : ℝ × ℝ => M0 P N q α₁ α₂ p.1 p.2) := by
  have hw : Continuous (fun p : ℝ × ℝ => weylAvg P N α₁ α₂ p.1 p.2) :=
    continuous_weylAvg_pair P N α₁ α₂
  have hmt : Measurable (fun p : ℝ × ℝ => mTilde P N p.1 p.2) := measurable_mTilde_pair P N
  have h : (fun p : ℝ × ℝ => M0 P N q α₁ α₂ p.1 p.2)
      = fun p : ℝ × ℝ =>
          weylAvg P N α₁ α₂ p.1 p.2 - mZ P q α₁ α₂ * mTilde P N p.1 p.2 := rfl
  rw [h]
  exact hw.measurable.sub (measurable_const.mul hmt)

/-- The canonical representative `lift : 𝕋 → ℝ` is measurable. -/
private lemma measurable_lift_local : Measurable (lift : AddCircle (1 : ℝ) → ℝ) := by
  unfold lift
  exact measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) (-(1/2))).measurable

/-! ## §4  The spike symbol: measurability and uniform boundedness -/

theorem spikeSymbMeasBdd (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ N : ℕ)
    {w₁ w₂ : ℝ} (hw₁2 : w₁ < 1 / 2) (hw₂2 : w₂ < 1 / 2)
    (hsup₁ : ∀ x : ℝ, Work.KMTAreas.A7.varphiN N k₁ x ≠ 0 → |x| ≤ w₁)
    (hsup₂ : ∀ x : ℝ, Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ x ≠ 0 → |x| ≤ w₂)
    (β₁ β₂ : Work.Analysis.IonescuWainger.Circle) :
    Measurable (fun p : Work.Analysis.IonescuWainger.Circle × Work.Analysis.IonescuWainger.Circle =>
        Work.KMTAreas.A7.spikeSymb ρ P l₁ l₂ k₁ k₂ N β₁ β₂ p.1 p.2) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ θ₁ θ₂ : Work.Analysis.IonescuWainger.Circle,
        ‖Work.KMTAreas.A7.spikeSymb ρ P l₁ l₂ k₁ k₂ N β₁ β₂ θ₁ θ₂‖ ≤ C := by
  have hlift : Measurable (lift : AddCircle (1 : ℝ) → ℝ) := measurable_lift_local
  have hφ : Measurable (fun p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) =>
      varphiN N k₁ (lift (p.1 - β₁))) :=
    (measurable_varphiN_local N k₁).comp (hlift.comp (measurable_fst.sub measurable_const))
  have hψ : Measurable (fun p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) =>
      varphitildeN P.natDegree N k₂ (lift (p.2 - β₂))) :=
    (measurable_varphitildeN_local P.natDegree N k₂).comp
      (hlift.comp (measurable_snd.sub measurable_const))
  have hpair : Measurable (fun p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) =>
      (lift (p.1 - β₁), lift (p.2 - β₂))) :=
    (hlift.comp (measurable_fst.sub measurable_const)).prodMk
      (hlift.comp (measurable_snd.sub measurable_const))
  have hM : Measurable (fun p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) =>
      M0 P N (arithQ ρ (max l₁ l₂)) β₁ β₂ (lift (p.1 - β₁)) (lift (p.2 - β₂))) := by
    change Measurable ((fun q : ℝ × ℝ => M0 P N (arithQ ρ (max l₁ l₂)) β₁ β₂ q.1 q.2) ∘
      (fun p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) =>
        (lift (p.1 - β₁), lift (p.2 - β₂))))
    exact (measurable_M0_pair P N (arithQ ρ (max l₁ l₂)) β₁ β₂).comp hpair
  have hsym : (fun p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) =>
        spikeSymb ρ P l₁ l₂ k₁ k₂ N β₁ β₂ p.1 p.2)
      = fun p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) => varphiN N k₁ (lift (p.1 - β₁))
          * varphitildeN P.natDegree N k₂ (lift (p.2 - β₂))
          * M0 P N (arithQ ρ (max l₁ l₂)) β₁ β₂ (lift (p.1 - β₁)) (lift (p.2 - β₂)) := by
    funext p
    simp only [spikeSymb, bumpSymb]
    rw [periodize_eq_lift hw₁2 hsup₁ (p.1 - β₁), periodize_eq_lift hw₂2 hsup₂ (p.2 - β₂)]
  refine ⟨?_, ?_⟩
  · rw [hsym]
    exact (hφ.mul hψ).mul hM
  · refine ⟨2 * 2 * (‖((N : ℂ))⁻¹‖ * ((Finset.Ioc (N / 2) N).card : ℝ)
        + ‖mZ P (arithQ ρ (max l₁ l₂)) β₁ β₂‖ * (1 / 2)), by positivity, fun θ₁ θ₂ => ?_⟩
    rw [spikeSymb, bumpSymb, periodize_eq_lift hw₁2 hsup₁ (θ₁ - β₁),
      periodize_eq_lift hw₂2 hsup₂ (θ₂ - β₂), norm_mul, norm_mul]
    refine mul_le_mul
      (mul_le_mul (norm_varphiN_le_two_local N k₁ (lift (θ₁ - β₁)))
        (norm_varphitildeN_le_two_local P.natDegree N k₂ (lift (θ₂ - β₂)))
        (norm_nonneg _) (by norm_num))
      (norm_M0_local P N (arithQ ρ (max l₁ l₂)) β₁ β₂ (lift (θ₁ - β₁)) (lift (θ₂ - β₂)))
      (norm_nonneg _) ?_
    positivity

end

end Work.KMTAreas.A7
