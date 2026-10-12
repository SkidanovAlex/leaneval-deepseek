import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.Analysis.Fourier.continuous_parametric_intervalIntegral_general
import Submission.Commons.Analysis.Fourier.cos_parseval_scaled_hasSum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Fourier

open MeasureTheory Set
open scoped Topology BigOperators

noncomputable section


/-- The centred interval `[-s/2, s/2]`. -/
def boxB (s : ℝ) : Set ℝ := Set.Icc (-(s / 2)) (s / 2)

/-- The box `[-s/2, s/2]^n`, as a product set in `Fin n → ℝ`. -/
def boxSet (n : ℕ) (s : ℝ) : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ : Fin n => boxB s)

/-- The Neumann cosine mode: `cos ((k π / ℓ)(x + ℓ/2))`. -/
def boxMode (ℓ : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  Real.cos (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2))

/-- The squared `L²`-norm of the `k`-th Neumann mode on `[-ℓ/2, ℓ/2]`. -/
def boxWgt (ℓ : ℝ) (k : ℕ) : ℝ := if k = 0 then ℓ else ℓ / 2

lemma boxWgt_pos {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) : 0 < boxWgt ℓ k := by
  unfold boxWgt
  split <;> linarith

lemma boxWgt_ne_zero {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) : boxWgt ℓ k ≠ 0 :=
  ne_of_gt (boxWgt_pos hℓ k)

lemma measurableSet_boxB (s : ℝ) : MeasurableSet (boxB s) := measurableSet_Icc

lemma measurableSet_boxSet (n : ℕ) (s : ℝ) : MeasurableSet (boxSet n s) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

lemma isCompact_boxSet (n : ℕ) (s : ℝ) : IsCompact (boxSet n s) := by
  unfold boxSet
  exact isCompact_univ_pi (fun _ => isCompact_Icc)

lemma boxSet_zero (s : ℝ) : boxSet 0 s = Set.univ := by
  ext x; simp [boxSet]

lemma boxMode_zero (ℓ : ℝ) (x : ℝ) : boxMode ℓ 0 x = 1 := by
  simp [boxMode]


/-- The map `p ↦ Fin.cons p.1 p.2` is continuous. -/
lemma continuous_cons_prod {n : ℕ} :
    Continuous (fun p : ℝ × (Fin n → ℝ) => (Fin.cons p.1 p.2 : Fin (n+1) → ℝ)) := by
  apply continuous_pi
  intro i
  cases i using Fin.cases with
  | zero => simpa using continuous_fst
  | succ j => exact (continuous_apply j).comp continuous_snd

/-- The map `a ↦ Fin.cons a rest` is continuous. -/
lemma continuous_cons_right {n : ℕ} (rest : Fin n → ℝ) :
    Continuous (fun a : ℝ => (Fin.cons a rest : Fin (n+1) → ℝ)) :=
  continuous_cons_prod.comp (continuous_id.prodMk continuous_const)

/-- The integral over the `0`-dimensional box is evaluation. -/
lemma integral_boxSet_zero {s : ℝ} (G : (Fin 0 → ℝ) → ℝ) :
    (∫ x in boxSet 0 s, G x) = G (fun _ => (0 : ℝ)) := by
  have h : boxSet 0 s = Set.univ := boxSet_zero s
  rw [h, Measure.restrict_univ, integral_unique, Measure.real_def]
  have h1 : (volume : Measure (Fin 0 → ℝ)) univ = 1 := by
    change Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ)) univ = 1
    rw [Measure.pi_of_empty, Measure.dirac_apply_of_mem (Set.mem_univ _)]
  rw [h1, ENNReal.toReal_one, one_smul]
  congr 1
  exact Subsingleton.elim _ _

lemma hasSum_const_unique {ι : Type*} [Fintype ι] [Unique ι] {c : ℝ} :
    HasSum (fun _ : ι => c) c := by
  have h := hasSum_fintype (fun _ : ι => c)
  rw [Fintype.sum_unique] at h
  exact h

/-- Fubini: splitting off the first coordinate of the box. -/
lemma setIntegral_boxSet_succ (n : ℕ) (s : ℝ) (f : (Fin (n+1) → ℝ) → ℝ) (hf : Continuous f) :
    (∫ x in boxSet (n+1) s, f x)
      = ∫ a in boxB s, ∫ rest in boxSet n s, f (Fin.cons a rest) := by
  set e : ℝ × (Fin n → ℝ) ≃ᵐ (Fin (n+1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm with he
  have hem : MeasurePreserving e volume volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  have heapp : ∀ (a : ℝ) (rest : Fin n → ℝ), e (a, rest) = Fin.cons a rest := by
    intro a rest
    rw [he]
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk]
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ j => simp
  have hbox : e ⁻¹' boxSet (n+1) s = boxB s ×ˢ boxSet n s := by
    ext p
    constructor
    · intro hp
      rw [Set.mem_preimage] at hp
      rw [boxSet, Set.mem_univ_pi] at hp
      refine ⟨?_, ?_⟩
      · have := hp 0
        rwa [heapp] at this
      · rw [boxSet, Set.mem_univ_pi]
        intro j
        have := hp j.succ
        rwa [heapp, Fin.cons_succ] at this
    · rintro ⟨h0, hrest⟩
      rw [Set.mem_preimage, boxSet, Set.mem_univ_pi]
      intro i
      rw [boxSet, Set.mem_univ_pi] at hrest
      cases i using Fin.cases with
      | zero => rwa [heapp, Fin.cons_zero]
      | succ j => rw [heapp, Fin.cons_succ]; exact hrest j
  have hcompact : IsCompact (boxB s ×ˢ boxSet n s) :=
    isCompact_Icc.prod (isCompact_boxSet n s)
  have hInt : IntegrableOn (fun p : ℝ × (Fin n → ℝ) => f (e p)) (boxB s ×ˢ boxSet n s) volume := by
    rw [show (fun p : ℝ × (Fin n → ℝ) => f (e p)) = fun p => f (Fin.cons p.1 p.2) by
      funext p; rw [heapp]]
    exact ContinuousOn.integrableOn_compact hcompact ((hf.comp (by fun_prop)).continuousOn)
  rw [← hem.map_eq, setIntegral_map_equiv, hbox]
  change (∫ (x : ℝ × (Fin n → ℝ)) in boxB s ×ˢ boxSet n s, f (e x)
      ∂(Measure.prod (volume : Measure ℝ) (volume : Measure (Fin n → ℝ))))
      = ∫ a in boxB s, ∫ rest in boxSet n s, f (Fin.cons a rest)
  rw [setIntegral_prod (f := fun p : ℝ × (Fin n → ℝ) => f (e p))
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin n → ℝ))) hInt]
  simp only [heapp]

/-- Fubini (swapped): splitting off the first coordinate of the box, outer variable the rest. -/
lemma setIntegral_boxSet_succ_swap (n : ℕ) (s : ℝ) (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : Continuous f) :
    (∫ x in boxSet (n+1) s, f x)
      = ∫ rest in boxSet n s, ∫ a in boxB s, f (Fin.cons a rest) := by
  set e : ℝ × (Fin n → ℝ) ≃ᵐ (Fin (n+1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm with he
  have hem : MeasurePreserving e volume volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  have heapp : ∀ (a : ℝ) (rest : Fin n → ℝ), e (a, rest) = Fin.cons a rest := by
    intro a rest
    rw [he]
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk]
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ j => simp
  have hbox : e ⁻¹' boxSet (n+1) s = boxB s ×ˢ boxSet n s := by
    ext p
    constructor
    · intro hp
      rw [Set.mem_preimage] at hp
      rw [boxSet, Set.mem_univ_pi] at hp
      refine ⟨?_, ?_⟩
      · have := hp 0
        rwa [heapp] at this
      · rw [boxSet, Set.mem_univ_pi]
        intro j
        have := hp j.succ
        rwa [heapp, Fin.cons_succ] at this
    · rintro ⟨h0, hrest⟩
      rw [Set.mem_preimage, boxSet, Set.mem_univ_pi]
      intro i
      rw [boxSet, Set.mem_univ_pi] at hrest
      cases i using Fin.cases with
      | zero => rwa [heapp, Fin.cons_zero]
      | succ j => rw [heapp, Fin.cons_succ]; exact hrest j
  have hcompact : IsCompact (boxB s ×ˢ boxSet n s) :=
    isCompact_Icc.prod (isCompact_boxSet n s)
  have hInt : IntegrableOn (fun p : ℝ × (Fin n → ℝ) => f (e p)) (boxB s ×ˢ boxSet n s) volume := by
    rw [show (fun p : ℝ × (Fin n → ℝ) => f (e p)) = fun p => f (Fin.cons p.1 p.2) by
      funext p; rw [heapp]]
    exact ContinuousOn.integrableOn_compact hcompact ((hf.comp (by fun_prop)).continuousOn)
  rw [← hem.map_eq, setIntegral_map_equiv, hbox]
  change (∫ (x : ℝ × (Fin n → ℝ)) in boxB s ×ˢ boxSet n s, f (e x)
      ∂(Measure.prod (volume : Measure ℝ) (volume : Measure (Fin n → ℝ))))
      = ∫ rest in boxSet n s, ∫ a in boxB s, f (Fin.cons a rest)
  rw [← setIntegral_prod_swap (boxB s) (boxSet n s) (fun p : ℝ × (Fin n → ℝ) => f (e p))]
  rw [setIntegral_prod (f := fun p : (Fin n → ℝ) × ℝ => f (e p.swap))
    (μ := (volume : Measure (Fin n → ℝ))) (ν := (volume : Measure ℝ)) (s := boxSet n s) (t := boxB s)]
  · apply setIntegral_congr_fun (measurableSet_boxSet n s)
    intro rest _
    apply setIntegral_congr_fun (measurableSet_boxB s)
    intro a _
    simp only [heapp, Prod.swap_prod_mk]
  · -- integrability for setIntegral_prod
    apply ContinuousOn.integrableOn_compact (isCompact_boxSet n s |>.prod isCompact_Icc)
    rw [show (fun p : (Fin n → ℝ) × ℝ => f (e p.swap)) = fun p => f (Fin.cons p.2 p.1) by
      funext p
      rw [show p.swap = (p.2, p.1) from rfl, heapp]]
    exact (hf.comp (by fun_prop)).continuousOn


/-- The set integral over `boxB ℓ` is the interval integral. -/
lemma setIntegral_boxB_eq_interval {ℓ : ℝ} (hℓ : 0 < ℓ) (g : ℝ → ℝ) :
    (∫ x in boxB ℓ, g x) = ∫ x in (-(ℓ/2))..(ℓ/2), g x := by
  rw [boxB, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -(ℓ/2) ≤ ℓ/2)]

/-- The weight of a `cons`-tuple is the product of the weights. -/
lemma boxWgt_prod_cons {n : ℕ} {ℓ : ℝ} (k0 : ℕ) (k : Fin n → ℕ) :
    (∏ i : Fin (n+1), boxWgt ℓ ((Fin.cons k0 k : Fin (n+1) → ℕ) i))
      = boxWgt ℓ k0 * ∏ i : Fin n, boxWgt ℓ (k i) := by
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- The Parseval coefficient of a `cons`-tuple factorises by Fubini. -/
lemma boxCoeff_cons {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (F : (Fin (n+1) → ℝ) → ℝ)
    (hF : Continuous F) (k0 : ℕ) (k : Fin n → ℕ) :
    (∫ x in boxSet (n+1) ℓ, F x * ∏ i : Fin (n+1), boxMode ℓ ((Fin.cons k0 k : Fin (n+1) → ℕ) i) (x i))
      = ∫ rest in boxSet n ℓ,
          (∫ a in (-(ℓ/2))..(ℓ/2), F (Fin.cons a rest) * boxMode ℓ k0 a)
            * ∏ i : Fin n, boxMode ℓ (k i) (rest i) := by
  have hcont : Continuous (fun x : Fin (n+1) → ℝ =>
      F x * ∏ i : Fin (n+1), boxMode ℓ ((Fin.cons k0 k : Fin (n+1) → ℕ) i) (x i)) := by
    apply Continuous.mul hF
    apply continuous_finsetProd
    intro i _
    simp only [boxMode]
    fun_prop
  rw [setIntegral_boxSet_succ_swap (n := n) (s := ℓ)
    (f := fun x => F x * ∏ i : Fin (n+1), boxMode ℓ ((Fin.cons k0 k : Fin (n+1) → ℕ) i) (x i)) hcont]
  apply setIntegral_congr_fun (measurableSet_boxSet n ℓ)
  intro rest _
  dsimp only
  rw [setIntegral_boxB_eq_interval hℓ]
  trans ∫ x in (-(ℓ/2))..(ℓ/2),
      F (Fin.cons x rest) * boxMode ℓ k0 x * ∏ i : Fin n, boxMode ℓ (k i) (rest i)
  · apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    ring
  · rw [intervalIntegral.integral_mul_const]

/-- The `n`-dimensional box Parseval identity, in `HasSum` form. -/
theorem boxParseval_hasSum (n : ℕ) :
    ∀ (ℓ : ℝ), 0 < ℓ → ∀ (F : (Fin n → ℝ) → ℝ), Continuous F →
      HasSum (fun k : Fin n → ℕ =>
          (∫ x in boxSet n ℓ, F x * ∏ i : Fin n, boxMode ℓ (k i) (x i)) ^ 2
            / ∏ i : Fin n, boxWgt ℓ (k i))
        (∫ x in boxSet n ℓ, (F x) ^ 2) := by
  induction n with
  | zero =>
      intro ℓ hℓ F hF
      have hg : ∀ k : Fin 0 → ℕ,
          (∫ x in boxSet 0 ℓ, F x * ∏ i : Fin 0, boxMode ℓ (k i) (x i)) ^ 2
              / ∏ i : Fin 0, boxWgt ℓ (k i)
            = (∫ x in boxSet 0 ℓ, F x) ^ 2 := by
        intro k
        simp only [Fin.prod_univ_zero, mul_one, div_one]
      rw [show (fun k : Fin 0 → ℕ =>
            (∫ x in boxSet 0 ℓ, F x * ∏ i : Fin 0, boxMode ℓ (k i) (x i)) ^ 2
              / ∏ i : Fin 0, boxWgt ℓ (k i)) = fun _ => (∫ x in boxSet 0 ℓ, F x) ^ 2
            from funext hg]
      rw [integral_boxSet_zero (fun x => (F x) ^ 2), integral_boxSet_zero F]
      exact hasSum_const_unique
  | succ n ih =>
      intro ℓ hℓ F hF
      set A : ℕ → (Fin n → ℝ) → ℝ :=
        fun k0 rest => ∫ a in (-(ℓ/2))..(ℓ/2), F (Fin.cons a rest) * boxMode ℓ k0 a with hA
      have hAcont : ∀ k0, Continuous (A k0) := by
        intro k0
        change Continuous (fun rest : Fin n → ℝ =>
          ∫ a in (-(ℓ/2))..(ℓ/2), F (Fin.cons a rest) * boxMode ℓ k0 a)
        exact continuous_parametric_intervalIntegral_general
          (g := fun p : ℝ × (Fin n → ℝ) => F (Fin.cons p.1 p.2) * boxMode ℓ k0 p.1) (by
            apply Continuous.mul
            · exact hF.comp continuous_cons_prod
            · simp only [boxMode]; fun_prop)
      have hfiber : ∀ k0, HasSum (fun k : Fin n → ℕ =>
          (∫ rest in boxSet n ℓ, A k0 rest * ∏ i : Fin n, boxMode ℓ (k i) (rest i)) ^ 2
            / ∏ i : Fin n, boxWgt ℓ (k i))
          (∫ rest in boxSet n ℓ, (A k0 rest) ^ 2) :=
        fun k0 => ih ℓ hℓ (A k0) (hAcont k0)
      have hlim : ∀ rest : Fin n → ℝ,
          HasSum (fun k0 : ℕ => (A k0 rest) ^ 2 / boxWgt ℓ k0)
            (∫ a in (-(ℓ/2))..(ℓ/2), (F (Fin.cons a rest)) ^ 2) := by
        intro rest
        have h := cos_parseval_scaled_hasSum hℓ (hF.comp (continuous_cons_right rest))
        simpa [hA, boxMode, boxWgt] using h
      have hval : (∫ x in boxSet (n+1) ℓ, (F x) ^ 2)
          = ∫ rest in boxSet n ℓ, ∫ a in (-(ℓ/2))..(ℓ/2), (F (Fin.cons a rest)) ^ 2 := by
        rw [setIntegral_boxSet_succ_swap (n := n) (s := ℓ) (f := fun x => (F x) ^ 2)
          (hF.pow 2)]
        apply setIntegral_congr_fun (measurableSet_boxSet n ℓ)
        intro rest _
        dsimp only
        exact setIntegral_boxB_eq_interval hℓ (fun a => (F (Fin.cons a rest)) ^ 2)
      have hInt : Integrable (fun rest => ∑' k0 : ℕ, (A k0 rest) ^ 2 / boxWgt ℓ k0)
          (volume.restrict (boxSet n ℓ)) := by
        have htsum : (fun rest => ∑' k0 : ℕ, (A k0 rest) ^ 2 / boxWgt ℓ k0)
            = fun rest => ∫ a in (-(ℓ/2))..(ℓ/2), (F (Fin.cons a rest)) ^ 2 := by
          funext rest
          exact (hlim rest).tsum_eq
        rw [htsum]
        apply ContinuousOn.integrableOn_compact (isCompact_boxSet n ℓ)
        apply (continuous_parametric_intervalIntegral_general
          (g := fun p : ℝ × (Fin n → ℝ) => (F (Fin.cons p.1 p.2)) ^ 2)
          ((hF.comp continuous_cons_prod).pow 2)).continuousOn
      have hbase : HasSum (fun k0 : ℕ => ∫ rest in boxSet n ℓ, (A k0 rest) ^ 2 / boxWgt ℓ k0)
          (∫ rest in boxSet n ℓ, ∫ a in (-(ℓ/2))..(ℓ/2), (F (Fin.cons a rest)) ^ 2) := by
        refine hasSum_integral_of_dominated_convergence
          (μ := volume.restrict (boxSet n ℓ))
          (F := fun k0 rest => (A k0 rest) ^ 2 / boxWgt ℓ k0)
          (bound := fun k0 rest => (A k0 rest) ^ 2 / boxWgt ℓ k0)
          (f := fun rest => ∫ a in (-(ℓ/2))..(ℓ/2), (F (Fin.cons a rest)) ^ 2)
          (fun k0 => (((hAcont k0).pow 2).div_const _).aestronglyMeasurable)
          (fun k0 => Filter.Eventually.of_forall (fun rest => le_of_eq (Real.norm_of_nonneg
              (div_nonneg (sq_nonneg _) (le_of_lt (boxWgt_pos hℓ k0))))))
          (Filter.Eventually.of_forall (fun rest => (hlim rest).summable))
          hInt
          (Filter.Eventually.of_forall hlim)
      have hterm1 : ∀ k0 : ℕ, (1/boxWgt ℓ k0) * ∫ rest in boxSet n ℓ, (A k0 rest) ^ 2
          = ∫ rest in boxSet n ℓ, (A k0 rest) ^ 2 / boxWgt ℓ k0 := by
        intro k0
        rw [integral_div]
        ring
      have h1 : HasSum (fun k0 : ℕ => (1/boxWgt ℓ k0) * ∫ rest in boxSet n ℓ, (A k0 rest) ^ 2)
          (∫ rest in boxSet n ℓ, ∫ a in (-(ℓ/2))..(ℓ/2), (F (Fin.cons a rest)) ^ 2) :=
        hbase.congr_fun (fun k0 => hterm1 k0)
      have hnonneg : ∀ p : (Σ _ : ℕ, Fin n → ℕ),
          0 ≤ (1/boxWgt ℓ p.1) * ((∫ rest in boxSet n ℓ,
              A p.1 rest * ∏ i : Fin n, boxMode ℓ (p.2 i) (rest i)) ^ 2
                / ∏ i : Fin n, boxWgt ℓ (p.2 i)) := by
        intro p
        apply mul_nonneg
        · exact le_of_lt (one_div_pos.mpr (boxWgt_pos hℓ p.1))
        · exact div_nonneg (sq_nonneg _)
            (le_of_lt (Finset.prod_pos (fun i _ => boxWgt_pos hℓ (p.2 i))))
      have hsigma : HasSum (fun p : (Σ _ : ℕ, Fin n → ℕ) =>
          (1/boxWgt ℓ p.1) * ((∫ rest in boxSet n ℓ,
              A p.1 rest * ∏ i : Fin n, boxMode ℓ (p.2 i) (rest i)) ^ 2
                / ∏ i : Fin n, boxWgt ℓ (p.2 i)))
          (∫ rest in boxSet n ℓ, ∫ a in (-(ℓ/2))..(ℓ/2), (F (Fin.cons a rest)) ^ 2) := by
        refine HasSum.sigma_of_hasSum
          (f := fun p : (Σ _ : ℕ, Fin n → ℕ) =>
            (1/boxWgt ℓ p.1) * ((∫ rest in boxSet n ℓ,
              A p.1 rest * ∏ i : Fin n, boxMode ℓ (p.2 i) (rest i)) ^ 2
                / ∏ i : Fin n, boxWgt ℓ (p.2 i))) h1 ?_ ?_
        · intro k0
          exact (hfiber k0).mul_left (1/boxWgt ℓ k0)
        · refine (summable_sigma_of_nonneg hnonneg).mpr ⟨fun k0 => ?_, ?_⟩
          · exact (hfiber k0).summable.mul_left (1/boxWgt ℓ k0)
          · refine h1.summable.congr (fun k0 => ?_)
            have heq : (fun y : Fin n → ℕ =>
                (1 / boxWgt ℓ (⟨k0, y⟩ : (Σ _ : ℕ, Fin n → ℕ)).1) *
                  ((∫ rest in boxSet n ℓ, A (⟨k0, y⟩ : (Σ _ : ℕ, Fin n → ℕ)).1 rest
                    * ∏ i : Fin n, boxMode ℓ ((⟨k0, y⟩ : (Σ _ : ℕ, Fin n → ℕ)).2 i) (rest i)) ^ 2
                    / ∏ i : Fin n, boxWgt ℓ ((⟨k0, y⟩ : (Σ _ : ℕ, Fin n → ℕ)).2 i)))
              = fun y : Fin n → ℕ => (1 / boxWgt ℓ k0) *
                  ((∫ rest in boxSet n ℓ, A k0 rest * ∏ i : Fin n, boxMode ℓ (y i) (rest i)) ^ 2
                    / ∏ i : Fin n, boxWgt ℓ (y i)) := by
              funext y; rfl
            rw [heq, tsum_mul_left, (hfiber k0).tsum_eq]
      have hprod : HasSum (fun p : ℕ × (Fin n → ℕ) =>
          (1/boxWgt ℓ p.1) * ((∫ rest in boxSet n ℓ,
              A p.1 rest * ∏ i : Fin n, boxMode ℓ (p.2 i) (rest i)) ^ 2
                / ∏ i : Fin n, boxWgt ℓ (p.2 i)))
          (∫ rest in boxSet n ℓ, ∫ a in (-(ℓ/2))..(ℓ/2), (F (Fin.cons a rest)) ^ 2) :=
        (Equiv.hasSum_iff (Equiv.sigmaEquivProd ℕ (Fin n → ℕ)).symm).mpr hsigma
      have hfin : HasSum (fun K : Fin (n+1) → ℕ =>
          (1/boxWgt ℓ (K 0)) * ((∫ rest in boxSet n ℓ,
              A (K 0) rest * ∏ i : Fin n, boxMode ℓ (K i.succ) (rest i)) ^ 2
                / ∏ i : Fin n, boxWgt ℓ (K i.succ)))
          (∫ rest in boxSet n ℓ, ∫ a in (-(ℓ/2))..(ℓ/2), (F (Fin.cons a rest)) ^ 2) :=
        (Equiv.hasSum_iff (Fin.insertNthEquiv (fun _ : Fin (n+1) => ℕ) 0)).mp hprod
      rw [hval]
      refine hfin.congr_fun (fun K => ?_)
      have hK : (Fin.cons (K 0) (fun i => K i.succ) : Fin (n+1) → ℕ) = K := by
        funext i
        cases i using Fin.cases with
        | zero => simp
        | succ j => simp
      have hc := boxCoeff_cons hℓ F hF (K 0) (fun i => K i.succ)
      have hw := boxWgt_prod_cons (ℓ := ℓ) (K 0) (fun i => K i.succ)
      rw [hK] at hc hw
      rw [hc, hw]
      simp only [hA]
      have hw0 : boxWgt ℓ (K 0) ≠ 0 := boxWgt_ne_zero hℓ _
      have hP : (∏ i : Fin n, boxWgt ℓ (K i.succ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun i _ => boxWgt_ne_zero hℓ _)
      field_simp

/-- **The three-dimensional box Parseval identity** (the requested statement). -/
theorem box3_parseval_cos {ℓ : ℝ} (hℓ : 0 < ℓ) {F : (Fin 3 → ℝ) → ℝ} (hF : Continuous F) :
    (∫ x in Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-(ℓ / 2)) (ℓ / 2)), (F x) ^ 2)
      = ∑' k : Fin 3 → ℕ,
          ((∫ x in Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-(ℓ / 2)) (ℓ / 2)),
              F x * ∏ i : Fin 3,
                Real.cos (((k i : ℝ) * Real.pi / ℓ) * (x i + ℓ / 2))) ^ 2)
          / ∏ i : Fin 3, (if k i = 0 then ℓ else ℓ / 2) := by
  have h := boxParseval_hasSum 3 ℓ hℓ F hF
  change (∫ x in boxSet 3 ℓ, (F x) ^ 2)
      = ∑' k : Fin 3 → ℕ,
          (∫ x in boxSet 3 ℓ, F x * ∏ i : Fin 3, boxMode ℓ (k i) (x i)) ^ 2
            / ∏ i : Fin 3, boxWgt ℓ (k i)
  rw [h.tsum_eq]

end

end Commons.Analysis.Fourier
