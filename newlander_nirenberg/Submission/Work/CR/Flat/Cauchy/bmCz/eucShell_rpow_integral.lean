import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmCz.eucRadialBound

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace Work.CR.Flat.Cauchy.bmCz

/-! ## The integral of a power of the Euclidean norm over an annulus

We compute `∫_{a ≤ eucNorm x < b} eucNorm x ^ s` for `s ≠ -2n`.  The main point is to
identify `(Fin n → ℂ, eucNorm)` measure-theoretically with the Euclidean space
`ℝ^{2n} = EuclideanSpace ℝ (Fin n × Fin 2)` (real and imaginary parts), and to use the
general polar-coordinate formula `MeasureTheory.integral_fun_norm_addHaar`. -/

/-! ### A measure preserving reindexing of a product measure -/

/-- The currying equivalence between `ι → α → β` and `ι × α → β` preserves Lebesgue
measure. -/
theorem measurePreserving_curry (n : ℕ) :
    MeasurePreserving ((Equiv.curry (Fin n) (Fin 2) ℝ).symm)
      (volume : Measure (Fin n → Fin 2 → ℝ))
      (volume : Measure (Fin n × Fin 2 → ℝ)) := by
  have hmeas : Measurable ((Equiv.curry (Fin n) (Fin 2) ℝ).symm :
      (Fin n → Fin 2 → ℝ) → (Fin n × Fin 2 → ℝ)) := by fun_prop
  refine ⟨hmeas, ?_⟩
  change Measure.map (⇑(Equiv.curry (Fin n) (Fin 2) ℝ).symm)
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin 2 => (volume : Measure ℝ))
    = Measure.pi (fun _ : Fin n × Fin 2 => (volume : Measure ℝ))
  refine (Measure.pi_eq (fun s hs => ?_)).symm
  have hpre : ((Equiv.curry (Fin n) (Fin 2) ℝ).symm ⁻¹' (Set.univ.pi s))
      = Set.univ.pi (fun i => Set.univ.pi (fun k => s (i, k))) := by
    ext g
    simp only [Set.mem_preimage, Set.mem_univ_pi, Equiv.curry_symm_apply,
      Function.uncurry_apply_pair, Prod.forall]
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs), hpre]
  simp only [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

/-! ### Identification of `ℂⁿ` with the Euclidean space `ℝ^{2n}` -/

/-- The currying measurable equivalence, as a `MeasurableEquiv`. -/
def curryME (n : ℕ) : (Fin n → Fin 2 → ℝ) ≃ᵐ (Fin n × Fin 2 → ℝ) :=
  ⟨(Equiv.curry (Fin n) (Fin 2) ℝ).symm, by fun_prop, by
     show Measurable (Equiv.curry (Fin n) (Fin 2) ℝ)
     fun_prop⟩

/-- The measurable equivalence between `ℂⁿ` (with Lebesgue volume) and `ℝ^{2n}` as a
Euclidean space, given by real and imaginary parts. -/
def eucToEuclidean (n : ℕ) : (Fin n → ℂ) ≃ᵐ EuclideanSpace ℝ (Fin n × Fin 2) :=
  (MeasurableEquiv.arrowCongr' (Equiv.refl (Fin n)) Complex.measurableEquivPi).trans
    ((curryME n).trans (MeasurableEquiv.toLp 2 (Fin n × Fin 2 → ℝ)))

/-- `eucToEuclidean` is measure preserving. -/
theorem measurePreserving_eucToEuclidean (n : ℕ) :
    MeasurePreserving (eucToEuclidean n) (volume : Measure (Fin n → ℂ))
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) := by
  have h1 : MeasurePreserving (fun x : Fin n → ℂ => fun i => Complex.measurableEquivPi (x i))
      (volume : Measure (Fin n → ℂ)) (volume : Measure (Fin n → Fin 2 → ℝ)) :=
    volume_preserving_pi (fun _ : Fin n => Complex.volume_preserving_equiv_pi)
  have h2 : MeasurePreserving (⇑(curryME n))
      (volume : Measure (Fin n → Fin 2 → ℝ)) (volume : Measure (Fin n × Fin 2 → ℝ)) := by
    have hfun : (⇑(curryME n)) = (Equiv.curry (Fin n) (Fin 2) ℝ).symm := rfl
    rw [hfun]
    exact measurePreserving_curry n
  have h3 : MeasurePreserving (⇑(MeasurableEquiv.toLp 2 (Fin n × Fin 2 → ℝ)))
      (volume : Measure (Fin n × Fin 2 → ℝ))
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n × Fin 2)).symm
  have hcomp := h3.comp (h2.comp h1)
  have hfun : (⇑(eucToEuclidean n)) = (⇑(MeasurableEquiv.toLp 2 (Fin n × Fin 2 → ℝ))) ∘
      ((⇑(curryME n)) ∘ (fun x : Fin n → ℂ => fun i => Complex.measurableEquivPi (x i))) := rfl
  rwa [hfun]

/-- `eucToEuclidean` turns the Euclidean norm into `eucNorm`. -/
theorem eucToEuclidean_norm (n : ℕ) (x : Fin n → ℂ) :
    ‖eucToEuclidean n x‖ = eucNorm x := by
  have hnorm : eucToEuclidean n x
      = MeasurableEquiv.toLp 2 (Fin n × Fin 2 → ℝ)
          (fun p : Fin n × Fin 2 => (Complex.measurableEquivPi (x p.1)) p.2) := rfl
  rw [hnorm, PiLp.norm_eq_of_L2, eucNorm]
  congr 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_two]
  simp only [MeasurableEquiv.toLp_apply, PiLp.toLp_apply, Complex.measurableEquivPi_apply,
    Fin.isValue, Real.norm_eq_abs, Matrix.cons_val_zero, Matrix.cons_val_one, sq_abs]
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-! ### The shell integral in a Euclidean space -/

/-- The integral of `‖y‖ ^ s` over the annulus `a ≤ ‖y‖ < b` in `EuclideanSpace ℝ ι`. -/
theorem euclideanSpace_shell_integral {ι : Type*} [Fintype ι] [Nonempty ι]
    {s : ℝ} (hs : s ≠ -(Fintype.card ι : ℝ)) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ y in {y : EuclideanSpace ℝ ι | a ≤ ‖y‖ ∧ ‖y‖ < b}, ‖y‖ ^ s
      = ((Fintype.card ι : ℝ) * (volume : Measure (EuclideanSpace ℝ ι)).real (Metric.ball 0 1))
          * ((b ^ (s + (Fintype.card ι : ℝ)) - a ^ (s + (Fintype.card ι : ℝ)))
              / (s + (Fintype.card ι : ℝ))) := by
  have hD : Module.finrank ℝ (EuclideanSpace ℝ ι) = Fintype.card ι := finrank_euclideanSpace
  have hD1 : 1 ≤ Fintype.card ι := Fintype.card_pos
  have hmeasSet : MeasurableSet {y : EuclideanSpace ℝ ι | a ≤ ‖y‖ ∧ ‖y‖ < b} :=
    (isClosed_le continuous_const continuous_norm).measurableSet.inter
      (isOpen_lt continuous_norm continuous_const).measurableSet
  set g : ℝ → ℝ := fun r => if a ≤ r ∧ r < b then r ^ s else 0 with hg
  have hstep2 : ∫ y in {y : EuclideanSpace ℝ ι | a ≤ ‖y‖ ∧ ‖y‖ < b}, ‖y‖ ^ s
      = ∫ y in {y : EuclideanSpace ℝ ι | a ≤ ‖y‖ ∧ ‖y‖ < b}, g ‖y‖ := by
    apply setIntegral_congr_fun hmeasSet
    intro y hy
    rw [hg]; simp only
    rw [ite_eq_left (show a ≤ ‖y‖ ∧ ‖y‖ < b from hy)]
  have hstep1 : ∫ y in {y : EuclideanSpace ℝ ι | a ≤ ‖y‖ ∧ ‖y‖ < b}, g ‖y‖
      = ∫ y : EuclideanSpace ℝ ι, g ‖y‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [hg]; simp only
    rw [ite_eq_right]
    exact fun h => hy h
  have hcast : ((Module.finrank ℝ (EuclideanSpace ℝ ι) - 1 : ℕ) : ℝ) + 1
      = (Fintype.card ι : ℝ) := by
    rw [hD]; exact_mod_cast (Nat.sub_add_cancel hD1)
  have hInt : ∫ y in Set.Ioi (0:ℝ),
        y ^ (Module.finrank ℝ (EuclideanSpace ℝ ι) - 1) • g y
      = (b ^ (s + (Fintype.card ι : ℝ)) - a ^ (s + (Fintype.card ι : ℝ)))
          / (s + (Fintype.card ι : ℝ)) := by
    have hcongr : Set.EqOn
        (fun y : ℝ => y ^ (Module.finrank ℝ (EuclideanSpace ℝ ι) - 1) • g y)
        ((Set.Ico a b).indicator
          (fun y => y ^ (s + ((Module.finrank ℝ (EuclideanSpace ℝ ι) - 1 : ℕ) : ℝ))))
        (Set.Ioi 0) := by
      intro y hy
      have hy0 : 0 < y := hy
      simp only [smul_eq_mul]
      by_cases h1 : a ≤ y
      · by_cases h2 : y < b
        · rw [hg]; simp only
          rw [ite_eq_left (show a ≤ y ∧ y < b from ⟨h1, h2⟩),
            Set.indicator_of_mem (show y ∈ Set.Ico a b from ⟨h1, h2⟩)]
          rw [← Real.rpow_natCast y (Module.finrank ℝ (EuclideanSpace ℝ ι) - 1),
            ← Real.rpow_add hy0]
          congr 1
          ring
        · rw [hg]; simp only
          rw [ite_eq_right (show ¬ (a ≤ y ∧ y < b) from fun h => h2 h.2),
            Set.indicator_of_notMem (fun h => h2 h.2), mul_zero]
      · rw [hg]; simp only
        rw [ite_eq_right (show ¬ (a ≤ y ∧ y < b) from fun h => h1 h.1),
          Set.indicator_of_notMem (fun h => h1 h.1), mul_zero]
    have hinter : (Set.Ioi (0:ℝ)) ∩ Set.Ico a b = Set.Ico a b := by
      apply Set.inter_eq_right.mpr
      intro y hy
      exact lt_of_lt_of_le ha hy.1
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
      setIntegral_indicator measurableSet_Ico, hinter,
      setIntegral_congr_set MeasureTheory.Ico_ae_eq_Ioc,
      ← intervalIntegral.integral_of_le hab]
    have hrne : s + ((Module.finrank ℝ (EuclideanSpace ℝ ι) - 1 : ℕ) : ℝ) ≠ -1 := by
      intro hcon
      apply hs
      have h2 : s + ((Module.finrank ℝ (EuclideanSpace ℝ ι) - 1 : ℕ) : ℝ) + 1 = 0 := by
        linarith
      rw [add_assoc, hcast] at h2
      linarith
    have h0 : (0:ℝ) ∉ Set.uIcc a b := by
      rw [Set.uIcc_of_le hab]
      intro hy
      have := (Set.mem_Icc.mp hy).1
      linarith
    rw [integral_rpow (Or.inr ⟨hrne, h0⟩)]
    rw [add_assoc, hcast]
  rw [hstep2, hstep1, MeasureTheory.integral_fun_norm_addHaar
    (volume : Measure (EuclideanSpace ℝ ι)) g, hInt, hD]
  simp only [nsmul_eq_mul, smul_eq_mul]
  ring

/-! ### The requested shell integral on `ℂⁿ` -/

theorem eucShell_rpow_integral {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ {s : ℝ}, s ≠ -(2 * (n : ℝ)) → ∀ {a b : ℝ}, 0 < a → a ≤ b →
      ∫ x in Work.CR.Flat.Cauchy.eucShell (n := n) a b, (Work.CR.Flat.Cauchy.eucNorm x) ^ s
        = C * ((b ^ (s + 2 * (n : ℝ)) - a ^ (s + 2 * (n : ℝ))) / (s + 2 * (n : ℝ))) := by
  have hcard : (Fintype.card (Fin n × Fin 2) : ℝ) = 2 * (n : ℝ) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.cast_mul]
    ring
  refine ⟨(Fintype.card (Fin n × Fin 2) : ℝ) *
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))).real (Metric.ball 0 1), ?_, ?_⟩
  · refine mul_pos ?_ ?_
    · rw [hcard]
      have hn' : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
      linarith
    · rw [Measure.real_def]
      exact ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos volume 0 one_pos))
        (ne_of_lt MeasureTheory.measure_ball_lt_top)
  · intro s hs a b ha hab
    haveI : Nonempty (Fin n × Fin 2) := ⟨(⟨0, hn⟩, 0)⟩
    have hs' : s ≠ -(Fintype.card (Fin n × Fin 2) : ℝ) := by
      rw [hcard]; exact hs
    have key := (measurePreserving_eucToEuclidean n).setIntegral_preimage_emb
      (eucToEuclidean n).measurableEmbedding
      (fun y : EuclideanSpace ℝ (Fin n × Fin 2) => ‖y‖ ^ s)
      {y : EuclideanSpace ℝ (Fin n × Fin 2) | a ≤ ‖y‖ ∧ ‖y‖ < b}
    have hpre : (eucToEuclidean n) ⁻¹'
        {y : EuclideanSpace ℝ (Fin n × Fin 2) | a ≤ ‖y‖ ∧ ‖y‖ < b}
        = eucShell (n := n) a b := by
      ext x
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, mem_eucShell, eucToEuclidean_norm]
    rw [hpre] at key
    simp_rw [eucToEuclidean_norm] at key
    rw [key, euclideanSpace_shell_integral hs' ha hab, hcard]

end Work.CR.Flat.Cauchy.bmCz
