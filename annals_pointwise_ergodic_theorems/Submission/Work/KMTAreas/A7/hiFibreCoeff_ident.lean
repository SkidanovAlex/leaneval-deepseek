import Mathlib
import Submission.Work.KMTAreas.A7.hiFibreCoeffAux

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.A7
 Work.A7

/-! ## The pointwise factorisation of the discrete average -/

/-- The pointwise factorisation of the `n`-th summand of the discrete average. -/
lemma momPhase_factor (P : Polynomial ℤ) (d N k₁ k₂ : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (p : ℤ × ℤ) (θ₁ θ₂ : ℝ) (n : ℤ) :
    varphiN N k₁ θ₁ * varphitildeN d N k₂ θ₂ * momPhase P N α₁ α₂ θ₁ θ₂ n
        * ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂))
      = acCoefW P α₁ α₂ n
          * (varphiN N k₁ θ₁ * ee (θ₁ * ((n : ℝ) - (p.1 : ℝ))))
          * (varphitildeN d N k₂ θ₂ * ee (θ₂ * (PevalR P (n : ℝ) - (p.2 : ℝ)))) := by
  have key : ee (θ₁ * (n:ℝ) + θ₂ * PevalR P (n:ℝ)) * ee (-((p.1:ℝ) * θ₁ + (p.2:ℝ) * θ₂))
      = ee (θ₁ * ((n:ℝ) - (p.1:ℝ))) * ee (θ₂ * (PevalR P (n:ℝ) - (p.2:ℝ))) := by
    rw [← ee_add, ← ee_add]
    congr 1
    ring
  simp only [momPhase, acCoefW]
  calc varphiN N k₁ θ₁ * varphitildeN d N k₂ θ₂
        * (fourier (T := 1) n α₁ * fourier (T := 1) (P.eval n) α₂
            * ee (θ₁ * (n:ℝ) + θ₂ * PevalR P (n:ℝ)))
        * ee (-((p.1:ℝ) * θ₁ + (p.2:ℝ) * θ₂))
      = (fourier (T := 1) n α₁ * fourier (T := 1) (P.eval n) α₂)
          * (varphiN N k₁ θ₁ * varphitildeN d N k₂ θ₂)
          * (ee (θ₁ * (n:ℝ) + θ₂ * PevalR P (n:ℝ))
              * ee (-((p.1:ℝ) * θ₁ + (p.2:ℝ) * θ₂))) := by ring
    _ = (fourier (T := 1) n α₁ * fourier (T := 1) (P.eval n) α₂)
          * (varphiN N k₁ θ₁ * varphitildeN d N k₂ θ₂)
          * (ee (θ₁ * ((n:ℝ) - (p.1:ℝ))) * ee (θ₂ * (PevalR P (n:ℝ) - (p.2:ℝ)))) := by
          rw [key]
    _ = (fourier (T := 1) n α₁ * fourier (T := 1) (P.eval n) α₂)
          * (varphiN N k₁ θ₁ * ee (θ₁ * ((n:ℝ) - (p.1:ℝ))))
          * (varphitildeN d N k₂ θ₂ * ee (θ₂ * (PevalR P (n:ℝ) - (p.2:ℝ)))) := by ring

/-! ## Pulling constants and finite sums out of an integral -/

/-- **Pull a constant and a finite sum out of an integral**: with `B i` integrable,
`∫ θ, c * ∑_{i ∈ s} C i * B i θ = c * ∑_{i ∈ s} C i * ∫ θ, B i θ`. -/
lemma integral_const_mul_finsetSum {ι : Type*} (s : Finset ι) (c : ℂ) (C K : ι → ℂ)
    (B : ι → ℝ → ℂ) (hB : ∀ i, Integrable (B i)) :
    (∫ θ : ℝ, c * ∑ i ∈ s, C i * B i θ) = c * ∑ i ∈ s, C i * ∫ θ : ℝ, B i θ := by
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum _ (fun i _ => (hB i).const_mul (C i))]
  exact Finset.sum_congr rfl (fun i _ => integral_const_mul _ _)

/-- **Pull a finite sum with constant coefficients out of an integral**:
`∫ θ, ∑_{i ∈ s} c i * A i θ * K i = ∑_{i ∈ s} c i * K i * ∫ θ, A i θ`. -/
lemma integral_finsetSum_mul_const {ι : Type*} (s : Finset ι) (c K : ι → ℂ)
    (A : ι → ℝ → ℂ) (hA : ∀ i, Integrable (A i)) :
    (∫ θ : ℝ, ∑ i ∈ s, c i * A i θ * K i) = ∑ i ∈ s, c i * K i * ∫ θ : ℝ, A i θ := by
  rw [integral_finsetSum _ (fun i _ => ((hA i).const_mul (c i)).mul_const (K i))]
  exact Finset.sum_congr rfl (fun i _ => by rw [integral_mul_const, integral_const_mul]; ring)

/-- The fibre integral of the discrete average part. -/
theorem weylAvg_fibre (P : Polynomial ℤ) (N k₁ k₂ : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (p : ℤ × ℤ) :
    (∫ θ₁ : ℝ, ∫ θ₂ : ℝ, varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
        * weylAvg P N α₁ α₂ θ₁ θ₂ * ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂)))
      = (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
          acCoefW P α₁ α₂ (n : ℤ) * psiHi P N k₁ k₂ p (n : ℝ) := by
  have hpt : ∀ θ₁ θ₂ : ℝ,
      varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂ * weylAvg P N α₁ α₂ θ₁ θ₂
        * ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂))
      = (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
          acCoefW P α₁ α₂ (n : ℤ)
            * (varphiN N k₁ θ₁ * ee (θ₁ * ((n : ℝ) - (p.1 : ℝ))))
            * (varphitildeN P.natDegree N k₂ θ₂ * ee (θ₂ * (PevalR P (n : ℝ) - (p.2 : ℝ)))) := by
    intro θ₁ θ₂
    have key : varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
          * ((N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, momPhase P N α₁ α₂ θ₁ θ₂ (n : ℤ))
          * ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂))
        = (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
            varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
              * momPhase P N α₁ α₂ θ₁ θ₂ (n : ℤ) * ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂)) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun n _ => by ring)
    rw [weylAvg, key]
    congr 1
    exact Finset.sum_congr rfl (fun n _ =>
      momPhase_factor P P.natDegree N k₁ k₂ α₁ α₂ p θ₁ θ₂ n)
  calc (∫ θ₁ : ℝ, ∫ θ₂ : ℝ, varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
        * weylAvg P N α₁ α₂ θ₁ θ₂ * ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂)))
      = ∫ θ₁ : ℝ, ∫ θ₂ : ℝ, (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
          acCoefW P α₁ α₂ (n : ℤ)
            * (varphiN N k₁ θ₁ * ee (θ₁ * ((n : ℝ) - (p.1 : ℝ))))
            * (varphitildeN P.natDegree N k₂ θ₂ * ee (θ₂ * (PevalR P (n : ℝ) - (p.2 : ℝ)))) := by
        refine integral_congr_ae ?_
        filter_upwards with θ₁
        refine integral_congr_ae ?_
        filter_upwards with θ₂
        exact hpt θ₁ θ₂
    _ = ∫ θ₁ : ℝ, (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
          acCoefW P α₁ α₂ (n : ℤ)
            * (varphiN N k₁ θ₁ * ee (θ₁ * ((n : ℝ) - (p.1 : ℝ))))
            * (∫ θ₂ : ℝ, varphitildeN P.natDegree N k₂ θ₂ * ee (θ₂ * (PevalR P (n : ℝ) - (p.2 : ℝ)))) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun θ₁ => ?_))
        exact integral_const_mul_finsetSum (Finset.Ioc (N / 2) N) (N : ℂ)⁻¹
          (fun n => acCoefW P α₁ α₂ (n : ℤ) * (varphiN N k₁ θ₁ * ee (θ₁ * ((n : ℝ) - (p.1 : ℝ)))))
          (fun n => ∫ θ₂ : ℝ, varphitildeN P.natDegree N k₂ θ₂ * ee (θ₂ * (PevalR P (n : ℝ) - (p.2 : ℝ))))
          (fun n θ₂ => varphitildeN P.natDegree N k₂ θ₂ * ee (θ₂ * (PevalR P (n : ℝ) - (p.2 : ℝ))))
          (fun n => integrable_varphitildeN_mul_ee P.natDegree N k₂ _)
    _ = (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
          (acCoefW P α₁ α₂ (n : ℤ)
            * (∫ θ₂ : ℝ, varphitildeN P.natDegree N k₂ θ₂ * ee (θ₂ * (PevalR P (n : ℝ) - (p.2 : ℝ)))))
            * (∫ θ₁ : ℝ, varphiN N k₁ θ₁ * ee (θ₁ * ((n : ℝ) - (p.1 : ℝ)))) := by
        rw [integral_const_mul]
        congr 1
        exact integral_finsetSum_mul_const (Finset.Ioc (N / 2) N)
          (fun n => acCoefW P α₁ α₂ (n : ℤ))
          (fun n => ∫ θ₂ : ℝ, varphitildeN P.natDegree N k₂ θ₂ * ee (θ₂ * (PevalR P (n : ℝ) - (p.2 : ℝ))))
          (fun n θ₁ => varphiN N k₁ θ₁ * ee (θ₁ * ((n : ℝ) - (p.1 : ℝ))))
          (fun n => integrable_varphiN_mul_ee N k₁ _)
    _ = (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, acCoefW P α₁ α₂ (n : ℤ) * psiHi P N k₁ k₂ p (n : ℝ) := by
        congr 1
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [← bumpFT_eq, ← bumpFT_eq]
        simp only [psiHi, psiP]
        ring

/-! ## Norm bounds for the symbols -/

/-- The Fourier character has modulus one at every point. -/
lemma norm_fourier (n : ℤ) (α : Work.Analysis.IonescuWainger.Circle) :
    ‖fourier (T := 1) n α‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

/-- The summand of the discrete average has modulus one. -/
lemma norm_momPhase (P : Polynomial ℤ) (N : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (ξ₁ ξ₂ : ℝ) (n : ℤ) :
    ‖momPhase P N α₁ α₂ ξ₁ ξ₂ n‖ = 1 := by
  rw [momPhase, norm_mul, norm_mul, norm_fourier, norm_fourier, norm_ee]
  ring

/-- `‖(q : ℂ)⁻¹‖ * q ≤ 1`. -/
lemma norm_inv_natCast_mul_le_one (q : ℕ) : ‖((q : ℂ))⁻¹‖ * (q : ℝ) ≤ 1 := by
  rcases Nat.eq_zero_or_pos q with h | h
  · subst h; simp
  · rw [norm_inv, Complex.norm_natCast, inv_mul_cancel₀ (by positivity)]

/-- The discrete average is bounded by one. -/
lemma norm_weylAvg_le_one (P : Polynomial ℤ) (N : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (ξ₁ ξ₂ : ℝ) :
    ‖weylAvg P N α₁ α₂ ξ₁ ξ₂‖ ≤ 1 := by
  have hcard : (Finset.Ioc (N / 2) N).card ≤ N := by
    have h : (Finset.Ioc (N / 2) N).card = N - N / 2 := by simp
    rw [h]; exact Nat.sub_le _ _
  have hsum : ‖∑ n ∈ Finset.Ioc (N / 2) N, momPhase P N α₁ α₂ ξ₁ ξ₂ (n : ℤ)‖ ≤ (N : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∑ n ∈ Finset.Ioc (N / 2) N, ‖momPhase P N α₁ α₂ ξ₁ ξ₂ (n : ℤ)‖
        = ((Finset.Ioc (N / 2) N).card : ℝ) := by
      simp [norm_momPhase]
    rw [h1]
    exact_mod_cast hcard
  rw [weylAvg]
  refine (norm_mul_le _ _).trans ?_
  calc ‖((N : ℂ))⁻¹‖ * ‖∑ n ∈ Finset.Ioc (N / 2) N, momPhase P N α₁ α₂ ξ₁ ξ₂ (n : ℤ)‖
      ≤ ‖((N : ℂ))⁻¹‖ * (N : ℝ) := mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ ≤ 1 := norm_inv_natCast_mul_le_one N

/-- The arithmetic symbol `m_Ẑ` is bounded by one. -/
lemma norm_mZ_le_one_ident (P : Polynomial ℤ) (q : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) : ‖mZ P q α₁ α₂‖ ≤ 1 := by
  have hsum : ‖∑ n ∈ Finset.range q,
      fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ ≤ (q : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∑ n ∈ Finset.range q,
        ‖fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ = (q : ℝ) := by
      have h2 : ∀ n : ℕ,
          ‖fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ = 1 := by
        intro n
        rw [norm_mul, norm_fourier, norm_fourier, mul_one]
      rw [Finset.sum_congr rfl (fun n _ => h2 n)]
      simp
    rw [h1]
  rw [mZ]
  refine (norm_mul_le _ _).trans ?_
  calc ‖((q : ℂ))⁻¹‖ * ‖∑ n ∈ Finset.range q,
        fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖
      ≤ ‖((q : ℂ))⁻¹‖ * (q : ℝ) := mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ ≤ 1 := norm_inv_natCast_mul_le_one q

/-- The oscillatory integral `m̃_{N,ℝ}` is bounded by `1/2`. -/
lemma norm_mTilde_le_half (P : Polynomial ℤ) (N : ℕ) (ξ₁ ξ₂ : ℝ) :
    ‖mTilde P N ξ₁ ξ₂‖ ≤ 1 / 2 := by
  rw [mTilde]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1 / 2 : ℝ)) (b := (1 : ℝ))
    (C := 1) (f := fun t : ℝ =>
      ee (ξ₁ * (N : ℝ) * t + ξ₂ * PevalR P ((N : ℝ) * t)))
    (fun t _ => by rw [norm_ee])
  rw [one_mul, show |(1 : ℝ) - 1 / 2| = 1 / 2 by norm_num] at h
  exact h

/-! ## Measurability of the symbols as functions of the pair -/

/-- `weylAvg` is continuous in the pair `(θ₁,θ₂)`. -/
lemma continuous_weylAvg_pair (P : Polynomial ℤ) (N : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) :
    Continuous (fun z : ℝ × ℝ => weylAvg P N α₁ α₂ z.1 z.2) := by
  simp only [weylAvg]
  refine Continuous.mul continuous_const ?_
  refine continuous_finsetSum _ (fun n _ => ?_)
  simp only [momPhase]
  refine Continuous.mul (continuous_const.mul continuous_const) ?_
  refine continuous_ee.comp ?_
  refine Continuous.add ?_ ?_
  · exact continuous_fst.mul continuous_const
  · exact continuous_snd.mul continuous_const

/-- `PevalR P` is continuous. -/
lemma continuous_PevalR (P : Polynomial ℤ) : Continuous (fun t : ℝ => PevalR P t) := by
  have h2 : (fun t : ℝ => PevalR P t)
      = fun t : ℝ => ∑ i ∈ Finset.range ((P.map (Int.castRingHom ℝ)).natDegree + 1),
          (P.map (Int.castRingHom ℝ)).coeff i * t ^ i := by
    funext t; rw [PevalR, Polynomial.eval_eq_sum_range]
  rw [h2]
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_id.pow i))

/-- The character `ee` evaluated at the linear form `-(p₁θ₁ + p₂θ₂)`. -/
lemma continuous_ee_pair (p : ℤ × ℤ) :
    Continuous (fun z : ℝ × ℝ => ee (-((p.1 : ℝ) * z.1 + (p.2 : ℝ) * z.2))) := by
  refine continuous_ee.comp ?_
  refine Continuous.neg ?_
  refine Continuous.add ?_ ?_
  · exact continuous_const.mul continuous_fst
  · exact continuous_const.mul continuous_snd

/-- `mTilde` is strongly measurable in the pair `(θ₁,θ₂)`. -/
lemma stronglyMeasurable_mTilde_pair (P : Polynomial ℤ) (N : ℕ) :
    StronglyMeasurable (fun z : ℝ × ℝ => mTilde P N z.1 z.2) := by
  have hP : Continuous (fun t : ℝ => PevalR P t) := continuous_PevalR P
  have hA : Continuous (fun w : (ℝ × ℝ) × ℝ => w.1.1) :=
    (continuous_fst : Continuous (fun q : ℝ × ℝ => q.1)).comp
      (continuous_fst : Continuous (fun w : (ℝ × ℝ) × ℝ => w.1))
  have hB : Continuous (fun w : (ℝ × ℝ) × ℝ => w.1.2) :=
    (continuous_snd : Continuous (fun q : ℝ × ℝ => q.2)).comp
      (continuous_fst : Continuous (fun w : (ℝ × ℝ) × ℝ => w.1))
  have hC : Continuous (fun w : (ℝ × ℝ) × ℝ => w.2) := continuous_snd
  have hD : Continuous (fun w : (ℝ × ℝ) × ℝ => PevalR P ((N : ℝ) * w.2)) :=
    hP.comp (continuous_const.mul hC)
  have harg : Continuous (fun w : (ℝ × ℝ) × ℝ =>
      w.1.1 * (N : ℝ) * w.2 + w.1.2 * PevalR P ((N : ℝ) * w.2)) :=
    ((hA.mul continuous_const).mul hC).add (hB.mul hD)
  have hsm : StronglyMeasurable (fun z : ℝ × ℝ => ∫ t : ℝ,
      ee (z.1 * (N : ℝ) * t + z.2 * PevalR P ((N : ℝ) * t))
        ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))) :=
    StronglyMeasurable.integral_prod_right'
      ((continuous_ee.comp harg).stronglyMeasurable)
  have hfun : (fun z : ℝ × ℝ => mTilde P N z.1 z.2)
      = fun z : ℝ × ℝ => ∫ t : ℝ, ee (z.1 * (N : ℝ) * t + z.2 * PevalR P ((N : ℝ) * t))
          ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) := by
    funext z
    rw [mTilde, intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
  rw [hfun]
  exact hsm

/-- `varphiN N k ∘ fst` is a.e.-strongly-measurable on the product. -/
lemma aestronglyMeasurable_varphiN_fst (P : Polynomial ℤ) (N k : ℕ) :
    AEStronglyMeasurable (fun z : ℝ × ℝ => varphiN N k z.1) (volume.prod volume) :=
  ((Work.A7.varphiN_integrable_measurable N k).2.comp measurable_fst).aestronglyMeasurable

/-- `varphitildeN d N k ∘ snd` is a.e.-strongly-measurable on the product. -/
lemma aestronglyMeasurable_varphitildeN_snd (P : Polynomial ℤ) (N k : ℕ) :
    AEStronglyMeasurable (fun z : ℝ × ℝ => varphitildeN P.natDegree N k z.2)
      (volume.prod volume) :=
  ((Work.A7.varphitildeN_integrable_measurable P.natDegree N k).2.comp
    measurable_snd).aestronglyMeasurable

/-! ## Integrability of the uncurried integrands on the product -/

/-- The product of the two bumps is integrable on `ℝ × ℝ`. -/
lemma integrable_bumps_prod (P : Polynomial ℤ) (N k₁ k₂ : ℕ) :
    Integrable (fun z : ℝ × ℝ => varphiN N k₁ z.1 * varphitildeN P.natDegree N k₂ z.2)
      (volume.prod volume) :=
  Integrable.op_fst_snd (μ := volume) (ν := volume) continuous_mul
    ⟨1, fun x y => by rw [one_mul]; exact norm_mul_le x y⟩
    (Work.A7.varphiN_integrable_measurable N k₁).1
    (Work.A7.varphitildeN_integrable_measurable P.natDegree N k₂).1

/-- The discrete-average part of the `M₀` integrand is integrable on the product. -/
lemma integrable_uncurry_weylAvg (P : Polynomial ℤ) (N k₁ k₂ : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (p : ℤ × ℤ) :
    Integrable (Function.uncurry (fun θ₁ θ₂ : ℝ =>
      varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
        * weylAvg P N α₁ α₂ θ₁ θ₂ * ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂))))
      (volume.prod volume) := by
  have hfun : Function.uncurry (fun θ₁ θ₂ : ℝ =>
      varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
        * weylAvg P N α₁ α₂ θ₁ θ₂ * ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂)))
      = fun z : ℝ × ℝ => varphiN N k₁ z.1 * varphitildeN P.natDegree N k₂ z.2
        * weylAvg P N α₁ α₂ z.1 z.2 * ee (-((p.1 : ℝ) * z.1 + (p.2 : ℝ) * z.2)) := by
    funext z; rfl
  rw [hfun]
  refine (integrable_bumps_prod P N k₁ k₂).norm.mono' ?_ ?_
  · have h3 : AEStronglyMeasurable (fun z : ℝ × ℝ => weylAvg P N α₁ α₂ z.1 z.2)
        (volume.prod volume) :=
      (continuous_weylAvg_pair P N α₁ α₂).measurable.aestronglyMeasurable
    have h4 : AEStronglyMeasurable
        (fun z : ℝ × ℝ => ee (-((p.1 : ℝ) * z.1 + (p.2 : ℝ) * z.2))) (volume.prod volume) :=
      (continuous_ee_pair p).measurable.aestronglyMeasurable
    have hφ : AEStronglyMeasurable
        (fun z : ℝ × ℝ => varphiN N k₁ z.1 * varphitildeN P.natDegree N k₂ z.2)
        (volume.prod volume) :=
      (aestronglyMeasurable_varphiN_fst P N k₁).mul
        (aestronglyMeasurable_varphitildeN_snd P N k₂)
    exact (hφ.mul h3).mul h4
  · filter_upwards with z
    have hw := norm_weylAvg_le_one P N α₁ α₂ z.1 z.2
    have he : ‖ee (-((p.1 : ℝ) * z.1 + (p.2 : ℝ) * z.2))‖ = 1 := norm_ee _
    have hAB : (0 : ℝ) ≤ ‖varphiN N k₁ z.1‖ * ‖varphitildeN P.natDegree N k₂ z.2‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hbound : ‖varphiN N k₁ z.1‖ * ‖varphitildeN P.natDegree N k₂ z.2‖
          * ‖weylAvg P N α₁ α₂ z.1 z.2‖
        ≤ ‖varphiN N k₁ z.1‖ * ‖varphitildeN P.natDegree N k₂ z.2‖ := by
      calc ‖varphiN N k₁ z.1‖ * ‖varphitildeN P.natDegree N k₂ z.2‖
              * ‖weylAvg P N α₁ α₂ z.1 z.2‖
          ≤ ‖varphiN N k₁ z.1‖ * ‖varphitildeN P.natDegree N k₂ z.2‖ * 1 :=
            mul_le_mul_of_nonneg_left hw hAB
        _ = ‖varphiN N k₁ z.1‖ * ‖varphitildeN P.natDegree N k₂ z.2‖ := by ring
    rw [norm_mul, norm_mul, norm_mul, he, mul_one]
    exact hbound

/-- The `m̃`-part of the `M₀` integrand is integrable on the product. -/
lemma integrable_uncurry_mTilde (P : Polynomial ℤ) (N k₁ k₂ : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (q : ℕ) (p : ℤ × ℤ) :
    Integrable (Function.uncurry (fun θ₁ θ₂ : ℝ => mZ P q α₁ α₂ *
      (varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
        * mTilde P N θ₁ θ₂ * ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂)))))
      (volume.prod volume) := by
  have hfun : Function.uncurry (fun θ₁ θ₂ : ℝ => mZ P q α₁ α₂ *
      (varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
        * mTilde P N θ₁ θ₂ * ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂))))
      = fun z : ℝ × ℝ => mZ P q α₁ α₂ *
        (varphiN N k₁ z.1 * varphitildeN P.natDegree N k₂ z.2
          * mTilde P N z.1 z.2 * ee (-((p.1 : ℝ) * z.1 + (p.2 : ℝ) * z.2))) := by
    funext z; rfl
  rw [hfun]
  refine (integrable_bumps_prod P N k₁ k₂).norm.mono' ?_ ?_
  · have hT : AEStronglyMeasurable (fun z : ℝ × ℝ => mTilde P N z.1 z.2)
        (volume.prod volume) := (stronglyMeasurable_mTilde_pair P N).aestronglyMeasurable
    have h4 : AEStronglyMeasurable
        (fun z : ℝ × ℝ => ee (-((p.1 : ℝ) * z.1 + (p.2 : ℝ) * z.2))) (volume.prod volume) :=
      (continuous_ee_pair p).measurable.aestronglyMeasurable
    have hφ : AEStronglyMeasurable
        (fun z : ℝ × ℝ => varphiN N k₁ z.1 * varphitildeN P.natDegree N k₂ z.2)
        (volume.prod volume) :=
      (aestronglyMeasurable_varphiN_fst P N k₁).mul
        (aestronglyMeasurable_varphitildeN_snd P N k₂)
    have hmz : AEStronglyMeasurable (fun _ : ℝ × ℝ => mZ P q α₁ α₂) (volume.prod volume) :=
      measurable_const.aestronglyMeasurable
    exact hmz.mul ((hφ.mul hT).mul h4)
  · filter_upwards with z
    have hw := norm_mZ_le_one_ident P q α₁ α₂
    have he : ‖ee (-((p.1 : ℝ) * z.1 + (p.2 : ℝ) * z.2))‖ = 1 := norm_ee _
    have hAB : (0 : ℝ) ≤ ‖varphiN N k₁ z.1‖ * ‖varphitildeN P.natDegree N k₂ z.2‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have h2 : ‖mTilde P N z.1 z.2‖ ≤ 1 := by linarith [norm_mTilde_le_half P N z.1 z.2]
    have hX : ‖varphiN N k₁ z.1‖ * ‖varphitildeN P.natDegree N k₂ z.2‖ * ‖mTilde P N z.1 z.2‖
        ≤ ‖varphiN N k₁ z.1‖ * ‖varphitildeN P.natDegree N k₂ z.2‖ * 1 :=
      mul_le_mul_of_nonneg_left h2 hAB
    have hbound : ‖mZ P q α₁ α₂‖ * (‖varphiN N k₁ z.1‖ * ‖varphitildeN P.natDegree N k₂ z.2‖
          * ‖mTilde P N z.1 z.2‖)
        ≤ ‖varphiN N k₁ z.1‖ * ‖varphitildeN P.natDegree N k₂ z.2‖ := by
      calc ‖mZ P q α₁ α₂‖ * (‖varphiN N k₁ z.1‖ * ‖varphitildeN P.natDegree N k₂ z.2‖
            * ‖mTilde P N z.1 z.2‖)
          ≤ 1 * (‖varphiN N k₁ z.1‖ * ‖varphitildeN P.natDegree N k₂ z.2‖ * 1) :=
            mul_le_mul hw hX (by positivity) (by norm_num)
        _ = ‖varphiN N k₁ z.1‖ * ‖varphitildeN P.natDegree N k₂ z.2‖ := by ring
    rw [norm_mul, norm_mul, norm_mul, norm_mul, he, mul_one]
    exact hbound

/-! ## The split of the double integral -/

/-- **Linearity of the iterated integral of a difference** on `ℝ × ℝ`. -/
theorem iterated_integral_sub {F G : ℝ → ℝ → ℂ}
    (hF : Integrable (Function.uncurry F) (volume.prod volume))
    (hG : Integrable (Function.uncurry G) (volume.prod volume)) :
    (∫ θ₁ : ℝ, ∫ θ₂ : ℝ, (F θ₁ θ₂ - G θ₁ θ₂))
      = (∫ θ₁ : ℝ, ∫ θ₂ : ℝ, F θ₁ θ₂) - (∫ θ₁ : ℝ, ∫ θ₂ : ℝ, G θ₁ θ₂) := by
  have hfun : Function.uncurry (fun θ₁ θ₂ : ℝ => F θ₁ θ₂ - G θ₁ θ₂)
      = Function.uncurry F - Function.uncurry G := by
    funext z; rfl
  have hFG : Integrable (Function.uncurry (fun θ₁ θ₂ : ℝ => F θ₁ θ₂ - G θ₁ θ₂))
      (volume.prod volume) := by
    rw [hfun]; exact hF.sub hG
  have h2 : (∫ z : ℝ × ℝ, (F z.1 z.2 - G z.1 z.2) ∂(volume.prod volume))
      = (∫ z : ℝ × ℝ, F z.1 z.2 ∂(volume.prod volume))
        - (∫ z : ℝ × ℝ, G z.1 z.2 ∂(volume.prod volume)) :=
    integral_sub hF hG
  rw [integral_integral hFG, h2, ← integral_integral hF, ← integral_integral hG]

/-- Pulling the constant `m_Ẑ` out of the `m̃`-term of the `M₀` split. -/
lemma integral_mZ_mul_mTilde (P : Polynomial ℤ) (N k₁ k₂ : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (q : ℕ) (p : ℤ × ℤ) :
    (∫ θ₁ : ℝ, ∫ θ₂ : ℝ, mZ P q α₁ α₂ *
        (varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
          * mTilde P N θ₁ θ₂ * ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂))))
      = mZ P q α₁ α₂ *
        (∫ θ₁ : ℝ, ∫ θ₂ : ℝ, varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
          * mTilde P N θ₁ θ₂ * ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂))) := by
  simp_rw [integral_const_mul]

/-! ## The residue reindexing -/

/-- **The residue reindexing of a `q`-periodic coefficient sequence.** -/
theorem hiFibreCoeff_reindex_aux (P : Polynomial ℤ) (q : ℕ) (hq : 0 < q) (N k₁ k₂ : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (h₁ : q • α₁ = 0) (h₂ : q • α₂ = 0)
    (p : ℤ × ℤ) :
    (∑ r ∈ Finset.range q, acCoefW P α₁ α₂ (r : ℤ)
        * (∑ n ∈ Finset.Ioc (N / 2) N, if n % q = r then psiHi P N k₁ k₂ p (n : ℝ) else 0))
      = ∑ n ∈ Finset.Ioc (N / 2) N, acCoefW P α₁ α₂ (n : ℤ) * psiHi P N k₁ k₂ p (n : ℝ) := by
  have h1 : (∑ r ∈ Finset.range q, acCoefW P α₁ α₂ (r : ℤ)
        * (∑ n ∈ Finset.Ioc (N / 2) N, if n % q = r then psiHi P N k₁ k₂ p (n : ℝ) else 0))
      = ∑ r ∈ Finset.range q, ∑ n ∈ Finset.Ioc (N / 2) N,
          acCoefW P α₁ α₂ (r : ℤ)
            * (if n % q = r then psiHi P N k₁ k₂ p (n : ℝ) else 0) :=
    Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  have hmod : n % q < q := Nat.mod_lt _ hq
  refine (Finset.sum_eq_single (n % q) ?_ ?_).trans ?_
  · intro r _ hne
    rw [if_neg (fun h => hne h.symm), mul_zero]
  · intro hnot
    exact absurd (Finset.mem_range.mpr hmod) hnot
  · rw [if_pos rfl, acCoefW_nat_mod P q hq α₁ α₂ h₁ h₂ n]

/-! ## The Fubini swap between the time integral and the frequency integrals -/

/-- The iterated integral of a constant times a separated product. -/
lemma integral_integral_const_mul_sep (c : ℂ) (f g : ℝ → ℂ) :
    (∫ θ₁ : ℝ, ∫ θ₂ : ℝ, c * (f θ₁ * g θ₂)) = c * ((∫ θ₁ : ℝ, f θ₁) * (∫ θ₂ : ℝ, g θ₂)) := by
  rw [show (fun θ₁ : ℝ => ∫ θ₂ : ℝ, c * (f θ₁ * g θ₂))
      = fun θ₁ : ℝ => ∫ θ₂ : ℝ, (c * f θ₁) * g θ₂ from by
        funext θ₁; congr 1; ext θ₂; ring]
  rw [integral_integral_mul_sep]
  rw [integral_const_mul]
  ring

/-- **Fubini between the time integral and the two frequency integrals**. -/
theorem interval_integral_iterated_swap {a b : ℝ} (hab : a ≤ b) {G : ℝ → ℝ → ℝ → ℂ}
    (h : Integrable (fun w : ℝ × (ℝ × ℝ) => G w.2.1 w.2.2 w.1)
        ((volume.restrict (Set.Ioc a b)).prod (volume.prod volume))) :
    (∫ θ₁ : ℝ, ∫ θ₂ : ℝ, ∫ u in a..b, G θ₁ θ₂ u)
      = ∫ u in a..b, ∫ θ₁ : ℝ, ∫ θ₂ : ℝ, G θ₁ θ₂ u := by
  have h' : Integrable (fun w : ℝ × (ℝ × ℝ) => G w.2.1 w.2.2 w.1)
      ((volume.restrict (Set.uIoc a b)).prod (volume.prod volume)) := by
    rwa [Set.uIoc_of_le hab]
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc a b)) := by
    rw [Set.uIoc_of_le hab]
    exact ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have hM : Integrable (fun z : ℝ × ℝ => ∫ u in Set.uIoc a b, G z.1 z.2 u)
      (volume.prod volume) := h'.swap.integral_prod_left
  have hint : ∀ (X : ℝ → ℂ),
      (∫ u in a..b, X u) = ∫ u, X u ∂(volume.restrict (Set.uIoc a b)) := by
    intro X
    rw [intervalIntegral.integral_of_le hab, Set.uIoc_of_le hab]
  have e1 : (∫ θ₁ : ℝ, ∫ θ₂ : ℝ, ∫ u in a..b, G θ₁ θ₂ u)
      = ∫ z : ℝ × ℝ,
          (∫ u, G z.1 z.2 u ∂(volume.restrict (Set.uIoc a b))) ∂(volume.prod volume) := by
    simp_rw [hint]
    exact (integral_prod _ hM).symm
  have e2 : (∫ z : ℝ × ℝ,
          (∫ u, G z.1 z.2 u ∂(volume.restrict (Set.uIoc a b))) ∂(volume.prod volume))
      = ∫ u in a..b, ∫ z : ℝ × ℝ, G z.1 z.2 u ∂(volume.prod volume) := by
    have hswap := MeasureTheory.intervalIntegral_integral_swap (a := a) (b := b)
      (μ := volume.prod volume) (f := fun u (z : ℝ × ℝ) => G z.1 z.2 u) h'
    rw [hswap]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    exact (hint (fun u => G z.1 z.2 u)).symm
  have e3 : (∫ u in a..b, ∫ z : ℝ × ℝ, G z.1 z.2 u ∂(volume.prod volume))
      = ∫ u in a..b, ∫ θ₁ : ℝ, ∫ θ₂ : ℝ, G θ₁ θ₂ u := by
    rw [hint (fun u => ∫ z : ℝ × ℝ, G z.1 z.2 u ∂(volume.prod volume)),
      hint (fun u => ∫ θ₁ : ℝ, ∫ θ₂ : ℝ, G θ₁ θ₂ u)]
    refine integral_congr_ae ?_
    filter_upwards [h'.prod_right_ae] with u hu
    exact (integral_integral (f := fun θ₁ θ₂ : ℝ => G θ₁ θ₂ u) hu).symm
  rw [e1, e2, e3]

/-! ## The `m̃`-part of the fibre-coefficient identity -/

/-! ## The assembly of the fibre-coefficient identity -/

end

end Work.KMTAreas.A7
