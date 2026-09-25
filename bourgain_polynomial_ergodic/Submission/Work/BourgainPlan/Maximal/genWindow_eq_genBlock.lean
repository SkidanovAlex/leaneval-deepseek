import Mathlib
import Submission.Work.BourgainPlan.Maximal.genWindow_defs
import Submission.Work.Analysis.ExponentialSums.model721_bundle

/-!
# `genWindow = genBlock`: the change of variables `x = yq + z` for the general-`P` model

This file proves the `P`-general analogue of Bourgain's change of variables (7.22): the

`∑_{0 ≤ a < q}`-form of (7.21) at the parameter `m = y q + z` is the `z`-th block evaluated at
the quotient `y`,

`genWindow P k q D φ g s (y q + z) = genBlock P k q D φ g s z y`.

The proof is the same residue computation as in the `d = 2` bundle
(`Submission/Work/Analysis/ExponentialSums/model721_bundle.lean`, `windowBlock_eq_slicedBlock`)
and its `d`-general transcription
(`Submission/Work/BourgainPlan/Maximal/ppWindowBlock_eq_ppBlock.lean`), with the Fresnel profile
`Φ(-N²·)` replaced by the conjugated oscillatory profile `conj (polyProfile P (2^k) ·)` of §7.2.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Work.BourgainPlan.Maximal

noncomputable section

/-- The conjugated oscillatory profile `conj (polyProfile P (2^k) ·)` of the `k`-th block. -/
noncomputable def genProf (P : Polynomial ℤ) (k : ℕ) (β : ℝ) : ℂ :=
  starRingEnd ℂ (polyProfile P (2 ^ k) β)

/-- The weight `conj(polyProfile P (2^k) β) · φ(Dβ)` of the window model. -/
noncomputable def genWeight (P : Polynomial ℤ) (k : ℕ) (D : ℝ) (φ : ℝ → ℂ) (β : ℝ) : ℂ :=
  genProf P k β * φ (D * β)

/-- The `a`-th summand's residue factor, with the phase `e(2πi z a/q)` pulled out. -/
noncomputable def genWindowFac (q : ℕ) (z : ℤ) (a : ℕ) (g : ℤ → ℂ) (s : Finset ℤ) (β : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (z : ℂ) / (q : ℂ)))
  * (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I *
      ((j : ℂ) * ((((a : ℝ) / (q : ℝ) + β : ℝ)) : ℂ))))

/-- One summand of the `a`-sum, i.e. the integrand of `genWindowBlock`. -/
noncomputable def genWindowSummand (P : Polynomial ℤ) (k : ℕ) (q : ℕ) (z : ℤ) (a : ℕ)
    (g : ℤ → ℂ) (s : Finset ℤ) (m : ℤ) (D : ℝ) (φ : ℝ → ℂ) (β : ℝ) : ℂ :=
  genWindowFac q z a g s β * genWeight P k D φ β
  * Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) * (β : ℂ)))

/-- The `z`-residue part of the `a`-sum. -/
noncomputable def genWindowResidue (P : Polynomial ℤ) (k : ℕ) (q : ℕ) (z : ℤ) (g : ℤ → ℂ)
    (s : Finset ℤ) (m : ℤ) (D : ℝ) (φ : ℝ → ℂ) (β : ℝ) : ℂ :=
  (∑ j ∈ s.filter (fun j => (q : ℤ) ∣ (z + j)), g j * Complex.exp (2 * Real.pi * Complex.I *
      ((j : ℂ) * (β : ℂ)))) * genWeight P k D φ β
  * Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) * (β : ℂ)))

/-- The `∑_{0≤a<q}`-form of (7.21) with the conjugated profile, integrated over all of `ℝ`
(equal to `genWindow` because `φ` vanishes outside the window `|β| ≤ 1/(2D)`). -/
noncomputable def genWindowBlock (P : Polynomial ℤ) (k : ℕ) (q : ℕ) (D : ℝ) (φ : ℝ → ℂ)
    (g : ℤ → ℂ) (s : Finset ℤ) (m : ℤ) : ℂ :=
  ∑ a ∈ Finset.range q, ∫ β : ℝ,
    (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I *
        ((j : ℂ) * ((((a : ℝ) / (q : ℝ) + β : ℝ)) : ℂ))))
    * genWeight P k D φ β
    * Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) * ((((a : ℝ) / (q : ℝ) + β : ℝ)) : ℂ)))

/-! ## Elementary facts about the weight -/

/-- The conjugated profile as a dilation integral: the integrand appearing in `genWindow`. -/
lemma genProf_eq_integral (P : Polynomial ℤ) (k : ℕ) (β : ℝ) :
    genProf P k β
      = ∫ t in (0 : ℝ)..1, Complex.exp (-(2 * Real.pi * Complex.I *
          (((β : ℝ) * (P.map (Int.castRingHom ℝ)).eval (((2 : ℝ) ^ k) * t) : ℝ) : ℂ))) := by
  rw [genProf, star_polyProfile]
  apply intervalIntegral.integral_congr
  intro t _
  show polyE (-(β * (toRealPoly P).eval (((2^k : ℕ) : ℝ) * t)))
    = Complex.exp (-(2 * Real.pi * Complex.I * (((β : ℝ) * (P.map (Int.castRingHom ℝ)).eval (((2 : ℝ) ^ k) * t) : ℝ) : ℂ)))
  have hE : (toRealPoly P).eval (((2^k:ℕ):ℝ) * t)
      = (P.map (Int.castRingHom ℝ)).eval (((2:ℝ)^k) * t) := by
    rw [toRealPoly]
    congr 1
    rw [Nat.cast_pow, Nat.cast_ofNat]
  rw [hE]
  unfold polyE
  congr 1
  push_cast
  ring

/-- Continuity of the weight. -/
lemma continuous_genWeight (P : Polynomial ℤ) (k : ℕ) (D : ℝ) (φ : ℝ → ℂ)
    (hφc : Continuous φ) : Continuous (genWeight P k D φ) := by
  rw [show genWeight P k D φ = fun β : ℝ => genProf P k β * φ (D * β)
      from funext (fun β => by rw [genWeight])]
  exact (continuous_conj_polyProfile P (2^k)).mul (hφc.comp (continuous_const.mul continuous_id))

/-- Integrability of the weight: it is continuous and compactly supported. -/
lemma integrable_genWeight (P : Polynomial ℤ) (k : ℕ) (D : ℝ) (φ : ℝ → ℂ) (hD : 0 < D)
    (hφc : Continuous φ) (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0) :
    Integrable (genWeight P k D φ) := by
  rw [show genWeight P k D φ = fun β : ℝ => genProf P k β * φ (D * β)
      from funext (fun β => by rw [genWeight])]
  have hcont : Continuous (fun β : ℝ => genProf P k β * φ (D * β)) :=
    (continuous_conj_polyProfile P (2^k)).mul (hφc.comp (continuous_const.mul continuous_id))
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (-(1/(2*D))) (1/(2*D))) isCompact_Icc ?_
  intro β hβ
  rw [Function.mem_support] at hβ
  by_contra hcon
  exact hβ (by rw [phi_dilate_eq_zero hD hφs hcon, mul_zero])

/-! ## Continuity, integrability and norm bounds of the summands -/

/-- `genWindowFac` is continuous. -/
lemma continuous_genWindowFac (q : ℕ) (z : ℤ) (a : ℕ) (g : ℤ → ℂ) (s : Finset ℤ) :
    Continuous (genWindowFac q z a g s) := by
  rw [show genWindowFac q z a g s = fun β : ℝ =>
      Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (z : ℂ) / (q : ℂ)))
      * (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I *
          ((j : ℂ) * ((((a : ℝ) / (q : ℝ) + β : ℝ)) : ℂ))))
      from funext (fun β => by rw [genWindowFac])]
  fun_prop

/-- `genWindowSummand` is continuous. -/
lemma continuous_genWindowSummand (P : Polynomial ℤ) (k : ℕ) (q : ℕ) (z : ℤ) (a : ℕ) (g : ℤ → ℂ)
    (s : Finset ℤ) (m : ℤ) (D : ℝ) (φ : ℝ → ℂ) (hφc : Continuous φ) :
    Continuous (genWindowSummand P k q z a g s m D φ) := by
  have h1 : Continuous (fun β : ℝ => genWindowFac q z a g s β * genWeight P k D φ β
      * Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) * (β : ℂ)))) := by
    refine (((continuous_genWindowFac q z a g s).mul
      (continuous_genWeight P k D φ hφc)).mul ?_)
    fun_prop
  rw [show genWindowSummand P k q z a g s m D φ = fun β : ℝ =>
      genWindowFac q z a g s β * genWeight P k D φ β
      * Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) * (β : ℂ)))
      from funext (fun β => by rw [genWindowSummand])]
  exact h1

/-- Norm bound on a single summand. -/
lemma norm_genWindowSummand_le (P : Polynomial ℤ) (k : ℕ) (q : ℕ) (z : ℤ) (a : ℕ) (g : ℤ → ℂ)
    (s : Finset ℤ) (m : ℤ) (D : ℝ) (φ : ℝ → ℂ) (β : ℝ) :
    ‖genWindowSummand P k q z a g s m D φ β‖ ≤ (∑ j ∈ s, ‖g j‖) * ‖genWeight P k D φ β‖ := by
  rw [genWindowSummand, genWindowFac]
  have h1 : ‖Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (z : ℂ) / (q : ℂ)))‖ = 1 := by
    have harg : 2 * Real.pi * Complex.I * ((a : ℂ) * (z : ℂ) / (q : ℂ))
        = (↑(2 * Real.pi * ((a:ℝ) * (z:ℝ) / (q:ℝ))) : ℂ) * Complex.I := by push_cast; ring
    rw [harg, Complex.norm_exp_ofReal_mul_I]
  have h3 : ‖Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) * (β : ℂ)))‖ = 1 := by
    have harg : 2 * Real.pi * Complex.I * ((m : ℂ) * (β : ℂ))
        = (↑(2 * Real.pi * ((m:ℝ) * β)) : ℂ) * Complex.I := by push_cast; ring
    rw [harg, Complex.norm_exp_ofReal_mul_I]
  have h4 : ∀ j : ℤ, ‖Complex.exp (2 * Real.pi * Complex.I *
      ((j : ℂ) * ((((a : ℝ) / (q : ℝ) + β : ℝ)) : ℂ)))‖ = 1 := by
    intro j
    have harg : 2 * Real.pi * Complex.I * ((j : ℂ) * ((((a : ℝ) / (q : ℝ) + β : ℝ)) : ℂ))
        = (↑(2 * Real.pi * ((j:ℝ) * ((a:ℝ)/(q:ℝ) + β))) : ℂ) * Complex.I := by push_cast; ring
    rw [harg, Complex.norm_exp_ofReal_mul_I]
  have h5 : ‖∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I *
      ((j : ℂ) * ((((a : ℝ) / (q : ℝ) + β : ℝ)) : ℂ)))‖ ≤ ∑ j ∈ s, ‖g j‖ := by
    calc _ ≤ ∑ j ∈ s, ‖g j * Complex.exp (2 * Real.pi * Complex.I *
            ((j : ℂ) * ((((a : ℝ) / (q : ℝ) + β : ℝ)) : ℂ)))‖ := norm_sum_le _ _
      _ = ∑ j ∈ s, ‖g j‖ := Finset.sum_congr rfl (fun j _ => by rw [norm_mul, h4 j, mul_one])
  rw [norm_mul, norm_mul, norm_mul, h1, h3, one_mul, mul_one]
  exact mul_le_mul_of_nonneg_right h5 (norm_nonneg _)

/-! ## The residue identity and the `a`-sum -/

/-- The residue identity (7.23) in the shape of `genWindowFac`. -/
lemma genWindowFac_sum (q : ℕ) (z : ℤ) (g : ℤ → ℂ) (s : Finset ℤ) (β : ℝ) :
    (∑ a ∈ Finset.range q, genWindowFac q z a g s β)
      = (q : ℂ) * ∑ j ∈ s.filter (fun j => (q : ℤ) ∣ (z + j)),
          g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (β : ℂ))) := by
  simp only [genWindowFac]
  rw [Commons.Analysis.ExponentialSums.residue_sum_identity]

/-- The sum of the `a`-summands is `q` times the residue part. -/
lemma sum_genWindowSummand (P : Polynomial ℤ) (k : ℕ) (q : ℕ) (z : ℤ) (g : ℤ → ℂ) (s : Finset ℤ)
    (m : ℤ) (D : ℝ) (φ : ℝ → ℂ) (β : ℝ) :
    (∑ a ∈ Finset.range q, genWindowSummand P k q z a g s m D φ β)
      = (q : ℂ) * genWindowResidue P k q z g s m D φ β := by
  rw [show (∑ a ∈ Finset.range q, genWindowSummand P k q z a g s m D φ β)
      = ∑ a ∈ Finset.range q, (genWindowFac q z a g s β
          * (genWeight P k D φ β * Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) * (β : ℂ)))))
      from Finset.sum_congr rfl (fun a _ => by rw [genWindowSummand]; ring),
    ← Finset.sum_mul, genWindowFac_sum, genWindowResidue]
  ring

/-- The pointwise content of the change of variables `x = yq+z`: the `z`-slice at `γ/q`. -/
lemma genWindowResidue_apply (P : Polynomial ℤ) (k : ℕ) (q : ℕ) (z : ℤ) (g : ℤ → ℂ)
    (s : Finset ℤ) (y : ℤ) (D : ℝ) (φ : ℝ → ℂ) (γ : ℝ) (hq : 0 < q) :
    genWindowResidue P k q z g s (y * (q:ℤ) + z) D φ (γ/(q:ℝ))
      = Commons.Analysis.ExponentialSums.slicedAmp q D φ g s z γ
          * genProf P k (γ/(q:ℝ))
          * Complex.exp (2 * Real.pi * Complex.I * ((y : ℝ)) * γ) := by
  have hqC : (((q:ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [genWindowResidue, Commons.Analysis.ExponentialSums.slicedAmp, genWeight]
  have hqa : (((γ/(q:ℝ)) : ℝ) : ℂ) = (γ : ℂ) / ((q:ℝ) : ℂ) := by push_cast; ring
  have hET : Complex.exp (2 * Real.pi * Complex.I *
        ((((y * (q:ℤ) + z : ℤ)) : ℂ) * (((γ/(q:ℝ)) : ℝ) : ℂ)))
      = Complex.exp (2 * Real.pi * Complex.I * ((y : ℂ) * (γ : ℂ)))
        * Complex.exp (2 * Real.pi * Complex.I * ((z : ℂ) * (((γ/(q:ℝ)) : ℝ) : ℂ))) := by
    have hinner : (((y * (q:ℤ) + z : ℤ)) : ℂ) * (((γ/(q:ℝ)) : ℝ) : ℂ)
        = (y : ℂ) * (γ : ℂ) + (z : ℂ) * (((γ/(q:ℝ)) : ℝ) : ℂ) := by
      have hmC : (((y * (q:ℤ) + z : ℤ)) : ℂ) = (y : ℂ) * (q : ℂ) + (z : ℂ) := by push_cast; ring
      have hmul : ((y : ℂ) * (q : ℂ)) * ((γ : ℂ) / ((q:ℝ) : ℂ)) = (y : ℂ) * (γ : ℂ) := by
        have h1 : ((y : ℂ) * (q : ℂ)) = (y : ℂ) * (((q:ℝ)) : ℂ) := by push_cast; ring
        rw [h1, ← mul_div_assoc, div_eq_iff hqC]; ring
      rw [hmC, hqa, add_mul, hmul]
    rw [hinner, mul_add, Complex.exp_add]
  have hSy : Complex.exp (2 * Real.pi * Complex.I * ((y : ℂ) * (γ : ℂ)))
      = Complex.exp (2 * Real.pi * Complex.I * ((y : ℝ)) * γ) := by
    congr 1
    push_cast
    ring
  have hSE : (∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (z+j)), g j * Complex.exp (2 * Real.pi * Complex.I *
        ((j : ℂ) * (((γ/(q:ℝ)) : ℝ) : ℂ))))
        * Complex.exp (2 * Real.pi * Complex.I * ((z : ℂ) * (((γ/(q:ℝ)) : ℝ) : ℂ)))
      = ∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (z+j)), g j * Complex.exp (2 * Real.pi * Complex.I *
        (((j : ℂ) + (z : ℂ)) * (γ : ℂ) / ((q:ℝ) : ℂ))) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_assoc, ← Complex.exp_add]
    rw [show 2 * Real.pi * Complex.I * ((j : ℂ) * (((γ/(q:ℝ)) : ℝ) : ℂ))
          + 2 * Real.pi * Complex.I * ((z : ℂ) * (((γ/(q:ℝ)) : ℝ) : ℂ))
        = 2 * Real.pi * Complex.I * (((j : ℂ) + (z : ℂ)) * (γ : ℂ) / ((q:ℝ) : ℂ)) by
      rw [hqa]; ring]
  have hPhid : φ (D * (γ/(q:ℝ))) = φ (D * γ / (q:ℝ)) := by congr 1; ring
  rw [hPhid, hET, ← hSE, hSy]
  ac_rfl

/-- The phase split of the `m = yq+z`-shift. -/
lemma genExp_phase_split {q : ℕ} (hq : 0 < q) (y z m : ℤ) (hm : m = y * (q:ℤ) + z)
    (a : ℕ) (β : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) * ((((a : ℝ) / (q : ℝ) + β : ℝ)) : ℂ)))
      = Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (z : ℂ) / (q : ℂ)))
        * Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) * (β : ℂ))) := by
  have h1 : 2 * Real.pi * Complex.I * ((m : ℂ) * ((((a : ℝ) / (q : ℝ) + β : ℝ)) : ℂ))
      = 2 * Real.pi * Complex.I * (m : ℂ) * ((((a : ℝ) / (q : ℝ) + β : ℝ)) : ℂ) := by ring
  have h2 : 2 * Real.pi * Complex.I * ((m : ℂ) * (β : ℂ))
      = 2 * Real.pi * Complex.I * (m : ℂ) * (β : ℂ) := by ring
  rw [h1, Commons.Analysis.ExponentialSums.exp_phase_split hq y z m hm a β, h2]

/-- Step 1 of the bridge: the phase split of the `m = yq+z`-shift. -/
lemma genWindowBlock_eq_sum_genWindowSummand (P : Polynomial ℤ) (k q : ℕ) (D : ℝ) (φ : ℝ → ℂ)
    (g : ℤ → ℂ) (s : Finset ℤ) (m : ℤ) (y z : ℤ) (hq : 0 < q) (hm : m = y * (q:ℤ) + z) :
    genWindowBlock P k q D φ g s m
      = ∑ a ∈ Finset.range q, ∫ β : ℝ, genWindowSummand P k q z a g s m D φ β := by
  rw [genWindowBlock]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall (fun β => ?_))
  simp only []
  rw [genExp_phase_split hq y z m hm a β, genWindowSummand, genWindowFac, genWeight]
  ring

/-! ## The interval integral versus the full integral -/

/-- An interval integral of a weight containing `φ (D·)` (which vanishes off `[-1/(2D),1/(2D)]`)
equals the integral over all of `ℝ`. -/
lemma interval_integral_phi_mid (D : ℝ) (hD : 0 < D) {φ : ℝ → ℂ}
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0) (F G : ℝ → ℂ) :
    (∫ β in (-(1/(2*D)))..(1/(2*D)), F β * φ (D * β) * G β)
      = ∫ β : ℝ, F β * φ (D * β) * G β := by
  have hzero : ∀ β, β ∉ Set.Icc (-(1/(2*D))) (1/(2*D)) → F β * φ (D * β) * G β = 0 := by
    intro β hβ
    rw [phi_dilate_eq_zero hD hφs hβ, mul_zero, zero_mul]
  have hab : -(1/(2*D)) ≤ 1/(2*D) := by
    have : (0:ℝ) < 1/(2*D) := by positivity
    linarith
  calc ∫ β in (-(1/(2*D)))..(1/(2*D)), F β * φ (D * β) * G β
      = ∫ β in Set.Ioc (-(1/(2*D))) (1/(2*D)), F β * φ (D * β) * G β :=
        intervalIntegral.integral_of_le hab
    _ = ∫ β in Set.Icc (-(1/(2*D))) (1/(2*D)), F β * φ (D * β) * G β :=
        MeasureTheory.setIntegral_congr_set MeasureTheory.Ioc_ae_eq_Icc
    _ = ∫ β : ℝ, F β * φ (D * β) * G β :=
        MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero

/-- One `a`-term of `genWindow` is the corresponding term of `genWindowBlock`. -/
lemma genWindowTerm_eq (P : Polynomial ℤ) (k q : ℕ) (D : ℝ) (φ : ℝ → ℂ) (g : ℤ → ℂ)
    (s : Finset ℤ) (m : ℤ) (a : ℕ) (hD : 0 < D)
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0) :
    (∫ β in (-(1/(2*D)))..(1/(2*D)),
        (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) *
            ((((a : ℝ) / (q : ℝ)) + β : ℝ) : ℂ))))
        * (∫ t in (0 : ℝ)..1, Complex.exp (-(2 * Real.pi * Complex.I *
            (((β : ℝ) * (P.map (Int.castRingHom ℝ)).eval (((2 : ℝ) ^ k) * t) : ℝ) : ℂ))))
        * φ (D * β)
        * Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) *
            ((((a : ℝ) / (q : ℝ)) + β : ℝ) : ℂ))))
      = ∫ β : ℝ, (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) *
            ((((a : ℝ) / (q : ℝ)) + β : ℝ) : ℂ))))
        * genWeight P k D φ β
        * Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) *
            ((((a : ℝ) / (q : ℝ)) + β : ℝ) : ℂ))) := by
  have hprof : ∀ β : ℝ, (∫ t in (0 : ℝ)..1, Complex.exp (-(2 * Real.pi * Complex.I *
      (((β : ℝ) * (P.map (Int.castRingHom ℝ)).eval (((2 : ℝ) ^ k) * t) : ℝ) : ℂ))))
      = genProf P k β := fun β => (genProf_eq_integral P k β).symm
  simp only [hprof]
  rw [interval_integral_phi_mid D hD hφs
        (fun β => (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) *
            ((((a : ℝ) / (q : ℝ)) + β : ℝ) : ℂ)))) * genProf P k β)
        (fun β => Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) *
            ((((a : ℝ) / (q : ℝ)) + β : ℝ) : ℂ))))]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun β => ?_))
  simp only [genWeight]
  ring

/-- **The model `∑_{a<q}`-form is the full-line block.** -/
lemma genWindow_eq_genWindowBlock (P : Polynomial ℤ) (k q : ℕ) (D : ℝ) (φ : ℝ → ℂ) (g : ℤ → ℂ)
    (s : Finset ℤ) (m : ℤ) (hD : 0 < D)
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0) :
    genWindow P k q D φ g s m = genWindowBlock P k q D φ g s m := by
  rw [genWindow_apply, genWindowBlock]
  exact Finset.sum_congr rfl (fun a _ => genWindowTerm_eq P k q D φ g s m a hD hφs)

/-! ## The block as an integral of the `z`-slice symbol -/

/-- `genBlock` at `y` is the full-line integral of the `z`-slice symbol. -/
lemma genBlock_eq_integral (P : Polynomial ℤ) (k q : ℕ) (D : ℝ) (φ : ℝ → ℂ) (g : ℤ → ℂ)
    (s : Finset ℤ) (z : ℤ) (y : ℤ) (hq : 0 < q) :
    genBlock P k q D φ g s z (y : ℝ)
      = ∫ γ : ℝ, Commons.Analysis.ExponentialSums.slicedAmp q D φ g s z γ
          * genProf P k (γ / (q:ℝ))
          * Complex.exp (2 * Real.pi * Complex.I * ((y : ℝ)) * γ) := by
  rw [genBlock, Commons.Analysis.ExponentialSums.fourierInv_eq_integral]
  let H : ℝ → ℂ := fun β => genAmpF P k q D φ g s z β
      * Complex.exp (2 * Real.pi * Complex.I * ((((q:ℝ) * (y:ℝ) : ℝ)) : ℂ) * (β : ℂ))
  rw [Commons.Analysis.ExponentialSums.mul_integral_comp_div q hq H]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun γ => ?_))
  simp only [H]
  have hexp : Complex.exp (2 * Real.pi * Complex.I * (↑((q:ℝ) * (y:ℝ)) : ℂ) * (↑(γ / (q:ℝ)) : ℂ))
      = Complex.exp (2 * Real.pi * Complex.I * (↑(y:ℝ) : ℂ) * (↑γ : ℂ)) := by
    have hqC : ((q:ℂ)) ≠ 0 := by exact_mod_cast hq.ne'
    congr 1
    push_cast
    field_simp
  have hb : genBetaAmp q D φ g s z (γ / (q:ℝ))
      = Commons.Analysis.ExponentialSums.slicedAmp q D φ g s z γ := by
    rw [genBetaAmp, Commons.Analysis.ExponentialSums.slicedAmp]
    have hsum : (∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (z+j)), g j * Complex.exp (2 * Real.pi * Complex.I *
          (((j:ℂ) + (z:ℂ)) * (↑(γ / (q:ℝ)) : ℂ))))
        = ∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (z+j)), g j * Complex.exp (2 * Real.pi * Complex.I *
          (((j:ℂ) + (z:ℂ)) * (γ:ℂ) / ((q:ℝ):ℂ))) := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [show 2 * Real.pi * Complex.I * (((j:ℂ) + (z:ℂ)) * (↑(γ / (q:ℝ)) : ℂ))
            = 2 * Real.pi * Complex.I * (((j:ℂ) + (z:ℂ)) * (γ:ℂ) / ((q:ℝ):ℂ)) by
            push_cast; ring]
    rw [hsum]
    rw [show φ (D * (γ/(q:ℝ))) = φ (D * γ / (q:ℝ)) by congr 1; ring]
    ring
  have hAmp : genAmpF P k q D φ g s z (γ / (q:ℝ))
      = Commons.Analysis.ExponentialSums.slicedAmp q D φ g s z γ * genProf P k (γ / (q:ℝ)) := by
    rw [genAmpF, hb, genProf]
  rw [hAmp, hexp]

/-! ## The main identity -/

theorem genWindow_eq_genBlock (P : Polynomial ℤ) (k q : ℕ) (hq : 0 < q) (D : ℝ) (hD : 0 < D)
    {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0)
    (g : ℤ → ℂ) (s : Finset ℤ) (z y : ℤ) :
    genWindow P k q D φ g s (y * (q : ℤ) + z) = genBlock P k q D φ g s z (y : ℝ) := by
  rw [genWindow_eq_genWindowBlock P k q D φ g s (y * (q:ℤ) + z) hD hφs]
  rw [genWindowBlock_eq_sum_genWindowSummand P k q D φ g s (y * (q:ℤ) + z) y z hq rfl]
  have hintL : ∀ a : ℕ, Integrable (genWindowSummand P k q z a g s (y * (q:ℤ) + z) D φ) := by
    intro a
    refine Integrable.mono' (g := fun β : ℝ => (∑ j ∈ s, ‖g j‖) * ‖genWeight P k D φ β‖) ?_ ?_ ?_
    · exact (integrable_genWeight P k D φ hD hφ hφs).norm.const_mul _
    · exact (continuous_genWindowSummand P k q z a g s (y * (q:ℤ) + z) D φ hφ).aestronglyMeasurable
    · filter_upwards with β
      exact norm_genWindowSummand_le P k q z a g s (y * (q:ℤ) + z) D φ β
  have hswap : (∑ a ∈ Finset.range q, ∫ β : ℝ,
        genWindowSummand P k q z a g s (y * (q:ℤ) + z) D φ β)
      = ∫ β : ℝ, ∑ a ∈ Finset.range q,
        genWindowSummand P k q z a g s (y * (q:ℤ) + z) D φ β :=
    (MeasureTheory.integral_finsetSum (Finset.range q) (fun a _ => hintL a)).symm
  have h3 : (∫ β : ℝ, ∑ a ∈ Finset.range q,
        genWindowSummand P k q z a g s (y * (q:ℤ) + z) D φ β)
      = ∫ β : ℝ, (q : ℂ) * genWindowResidue P k q z g s (y * (q:ℤ) + z) D φ β :=
    integral_congr_ae (Filter.Eventually.of_forall
      (fun β => sum_genWindowSummand P k q z g s (y * (q:ℤ) + z) D φ β))
  have h4 : (∫ β : ℝ, (q : ℂ) * genWindowResidue P k q z g s (y * (q:ℤ) + z) D φ β)
      = (q : ℂ) * ∫ β : ℝ, genWindowResidue P k q z g s (y * (q:ℤ) + z) D φ β :=
    MeasureTheory.integral_const_mul (q : ℂ) _
  have h6 : (∫ γ : ℝ, genWindowResidue P k q z g s (y * (q:ℤ) + z) D φ (γ/(q:ℝ)))
      = genBlock P k q D φ g s z ((y:ℝ)) := by
    rw [genBlock_eq_integral P k q D φ g s z y hq]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun γ => ?_))
    exact genWindowResidue_apply P k q z g s y D φ γ hq
  rw [hswap, h3, h4, Commons.Analysis.ExponentialSums.mul_integral_comp_div q hq
        (genWindowResidue P k q z g s (y * (q:ℤ) + z) D φ), h6]

end

end Work.BourgainPlan.Maximal
