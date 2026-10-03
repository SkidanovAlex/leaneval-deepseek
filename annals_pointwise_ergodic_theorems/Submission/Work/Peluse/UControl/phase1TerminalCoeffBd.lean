import Mathlib
import Submission.Work.Peluse.UControl.ctrlDefs

/-!
# The coefficient bound at the terminal state of the phase-1 chain

The terminal state `histTerminal P hd` of Peluse's phase-1 chain has live slots of `y`-degree
`d - 1`, and its slot polynomials are the differences `Q_h(y + a_new) - Q_0` of the phase-1
top-slot polynomials.  This file proves the coefficient-wise bound `coeffBd d C` for them: every
`y^j`-coefficient, evaluated at tower parameters `|a_s| ≤ B`, is bounded by `C · B^{d - j}`.

The route is the invariant `Ctrl` of `ctrlDefs.lean` (the `y^j`-coefficient has total degree at most
`d - j`), preserved by one PET step (`histData_ctrl_step`), hence along the whole phase-1 chain
(`histData_ctrl_phase1Chain`); the closing step is again an instance of the step lemma.  The final
passage from the degree invariant to the evaluated bound is `coeffBd_of_ctrl`, whose engine is the
monomial bound `norm_eval_le_coeffMass`.

The statement of the target theorem is fixed; only the proof is supplied here.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Polynomial

variable {n : ℕ}

/-! ## Elementary norm bounds for integer polynomials -/

/-- The norm of a finite product of integers is at most the product of the norms. -/
lemma norm_finset_prod_int_le {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, ‖f i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, norm_mul]
    exact mul_le_mul_of_nonneg_left ih (norm_nonneg _)

/-- The monomial `∏ i, a i ^ m i` evaluated at parameters bounded by `B` is bounded by
`B ^ (total degree of m)`. -/
lemma norm_prod_pow_int_le {n : ℕ} (a : Fin n → ℤ) (B : ℝ) (ha : ∀ i, ‖a i‖ ≤ B)
    (m : Fin n →₀ ℕ) : ‖∏ i, a i ^ m i‖ ≤ B ^ (m.sum fun _ e => e) := by
  have h1 : ‖∏ i, a i ^ m i‖ ≤ ∏ i, ‖a i ^ m i‖ := by
    simpa using norm_finset_prod_int_le Finset.univ (fun i => a i ^ m i)
  have h2 : ∏ i : Fin n, ‖a i ^ m i‖ = ∏ i, ‖a i‖ ^ (m i) := by
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [norm_pow]
  rw [h2] at h1
  refine le_trans h1 ?_
  have h3 : ∏ i : Fin n, ‖a i‖ ^ (m i) ≤ ∏ i : Fin n, B ^ (m i) := by
    refine Finset.prod_le_prod₀ (fun i _ => by positivity)
      (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (ha i) _)
  refine le_trans h3 ?_
  rw [Finset.prod_pow_eq_pow_sum, Finsupp.sum_fintype m (fun _ e => e) (by intro i; rfl)]

/-- The mass of a multivariate polynomial: the sum of the norms of its coefficients. -/
def slotMass {n : ℕ} (c : MvPolynomial (Fin n) ℤ) : ℝ :=
  c.support.sum fun m => ‖c.coeff m‖

lemma coeffMass_nonneg {n : ℕ} (c : MvPolynomial (Fin n) ℤ) : 0 ≤ slotMass c :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- **The evaluation bound.**  Evaluating a multivariate polynomial with integer coefficients at
parameters of modulus at most `B ≥ 1` costs at most its coefficient mass times
`B ^ (total degree)`. -/
lemma norm_eval_le_coeffMass {n : ℕ} (c : MvPolynomial (Fin n) ℤ) (B : ℝ) (hB : 1 ≤ B)
    (a : Fin n → ℤ) (ha : ∀ s, ‖a s‖ ≤ B) :
    ‖c.eval a‖ ≤ slotMass c * B ^ c.totalDegree := by
  rw [MvPolynomial.eval_eq']
  refine le_trans (norm_sum_le _ _) ?_
  have hterms : ∀ m ∈ c.support,
      ‖c.coeff m * ∏ i, a i ^ m i‖ ≤ ‖c.coeff m‖ * B ^ c.totalDegree := by
    intro m hm
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact le_trans (norm_prod_pow_int_le a B ha m)
      (pow_le_pow_right₀ hB (MvPolynomial.le_totalDegree hm))
  refine le_trans (Finset.sum_le_sum hterms) ?_
  rw [slotMass, Finset.sum_mul]

/-! ## The invariant at the initial state and its preservation by one step -/

/-- The initial state of the phase-1 chain satisfies the coefficient-degree invariant. -/
lemma petHistInit_ctrl (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) :
    (petHistInit P hd).Ctrl := by
  rintro ⟨i | i, h₀⟩ - j
  · show (((Polynomial.X ^ (i.val + 1)).map
        (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 0) ℤ)).coeff j).totalDegree
      ≤ P.natDegree - j
    rw [Polynomial.coeff_map, Polynomial.coeff_X_pow]
    split_ifs
    · rw [MvPolynomial.totalDegree_C]
      exact Nat.zero_le _
    · rw [MvPolynomial.totalDegree_C]
      exact Nat.zero_le _
  · show ((P.map (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 0) ℤ)).coeff j).totalDegree
      ≤ P.natDegree - j
    rw [Polynomial.coeff_map, MvPolynomial.totalDegree_C]
    exact Nat.zero_le _

/-- The new parameter's shift has total degree at most `1`. -/
lemma stepShift_totalDegree {n : ℕ} (h' : Fin (n + 1) → Bool) :
    (stepShift h').totalDegree ≤ 1 := by
  rw [stepShift]
  split_ifs
  · rw [MvPolynomial.totalDegree_X]
  · rw [MvPolynomial.totalDegree_zero]
    exact Nat.zero_le 1

/-- **One PET step preserves the coefficient-degree invariant.**  The new slot polynomial is
`Q(y + a_new) - Q_{i₀}`; both summands are `Ctrl d` by `Ctrl.map_rename`, `Ctrl.comp_X_add_C` and
`Ctrl.sub'`. -/
lemma histData_ctrl_step {d n : ℕ} (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (hh : (i₀, h₀) ∈ X.H) (hX : X.Ctrl) : (X.step i₀ h₀ hh).Ctrl := by
  rintro ⟨j, h'⟩ hx
  change Ctrl d (X.stepQ i₀ h₀ j h')
  have hxH : (j, Fin.init h') ∈ X.H := by
    change (j, h') ∈ X.stepH i₀ h₀ at hx
    simp only [HistData.stepH, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact hx.1
  have hA : Ctrl d (((X.Q j (Fin.init h')).map (histRen n)).comp
      (Polynomial.X + Polynomial.C (stepShift h'))) := by
    refine Ctrl.comp_X_add_C ?_ ?_ (stepShift_totalDegree h')
    · exact Ctrl.map_rename (hX (j, Fin.init h') hxH) Fin.castSucc
    · exact le_trans Polynomial.natDegree_map_le (X.hd (j, Fin.init h') hxH)
  have hB : Ctrl d ((X.Q i₀ h₀).map (histRen n)) :=
    Ctrl.map_rename (hX (i₀, h₀) hh) Fin.castSucc
  exact Ctrl.sub' hA hB

/-- **The invariant along the phase-1 chain.**  The chain only ever takes PET steps, so `Ctrl`
propagates from the initial state to the state reached by `phase1Chain`. -/
theorem histData_ctrl_phase1Chain {d : ℕ} :
    ∀ X : HState d, X.2.Ctrl → (phase1Chain X).2.Ctrl := by
  intro X
  induction X using WellFounded.induction (HState.rel_wf d) with
  | h X ih =>
    intro h
    rw [phase1Chain, WellFounded.fix_eq]
    by_cases hstop : X.2.IsLinearX ∨ Phase1Done X.2
    · rw [dif_pos hstop]
      exact h
    · rw [dif_neg hstop]
      refine ih (HState.step X (X.2.H_nonempty_of_not_linear (fun hl => hstop (Or.inl hl))))
        (X.2.weightH_step_sel_lt _) ?_
      exact histData_ctrl_step X.2 (X.2.sel _).1 (X.2.sel _).2 (X.2.sel_mem_H _) h

/-! ## From the degree invariant to the evaluated coefficient bound -/

/-- The constant attached to a finite family of slot polynomials: one plus the total coefficient
mass of all their `y^j`-coefficients, `j ≤ d`. -/
def slotConstant (d : ℕ) {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial (MvPolynomial (Fin n) ℤ)) : ℝ :=
  1 + ∑ i ∈ s, ∑ j ∈ Finset.range (d + 1), slotMass ((f i).coeff j)

lemma one_le_slotConstant {n : ℕ} (d : ℕ) {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial (MvPolynomial (Fin n) ℤ)) : 1 ≤ slotConstant d s f := by
  rw [slotConstant]
  have h0 : 0 ≤ ∑ i ∈ s, ∑ j ∈ Finset.range (d + 1), slotMass ((f i).coeff j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => coeffMass_nonneg _
  linarith

lemma zero_le_slotConstant {n : ℕ} (d : ℕ) {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial (MvPolynomial (Fin n) ℤ)) : 0 ≤ slotConstant d s f :=
  le_trans zero_le_one (one_le_slotConstant d s f)

lemma coeffMass_le_slotConstant {n : ℕ} (d : ℕ) {ι : Type*} {s : Finset ι}
    {g : ι → Polynomial (MvPolynomial (Fin n) ℤ)} {i : ι} (hi : i ∈ s) {j : ℕ}
    (hj : j ∈ Finset.range (d + 1)) : slotMass ((g i).coeff j) ≤ slotConstant d s g := by
  have h1 : slotMass ((g i).coeff j)
      ≤ ∑ j' ∈ Finset.range (d + 1), slotMass ((g i).coeff j') :=
    Finset.single_le_sum (f := fun j' => slotMass ((g i).coeff j'))
      (fun j' _ => coeffMass_nonneg _) hj
  have h2 : (∑ j' ∈ Finset.range (d + 1), slotMass ((g i).coeff j'))
      ≤ ∑ i' ∈ s, ∑ j' ∈ Finset.range (d + 1), slotMass ((g i').coeff j') :=
    Finset.single_le_sum
      (f := fun i' => ∑ j' ∈ Finset.range (d + 1), slotMass ((g i').coeff j'))
      (fun i' _ => Finset.sum_nonneg fun j' _ => coeffMass_nonneg _) hi
  exact (h1.trans h2).trans (le_add_of_nonneg_left zero_le_one)

/-- **The constant extraction.**  A finite family of slot polynomials which all satisfy the
coefficient-degree invariant `Ctrl d` (and have `y`-degree at most `d`) admits a single constant `C`
for the evaluated coefficient bound `coeffBd d C`. -/
theorem coeffBd_of_ctrl {n d : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial (MvPolynomial (Fin n) ℤ))
    (hdeg : ∀ i ∈ s, (f i).natDegree ≤ d) (h : ∀ i ∈ s, Ctrl d (f i)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ i ∈ s, coeffBd d C (f i) := by
  refine ⟨slotConstant d s f, one_le_slotConstant d s f, ?_⟩
  intro i hi B hB a ha j
  have hnorm : ∀ t : Fin n, ‖a t‖ ≤ B := by
    intro t
    rw [Int.norm_eq_abs, ← Int.cast_abs]
    exact ha t
  by_cases hj : j ≤ d
  · calc ‖((f i).coeff j).eval a‖
        ≤ slotMass ((f i).coeff j) * B ^ ((f i).coeff j).totalDegree :=
          norm_eval_le_coeffMass _ B hB a hnorm
      _ ≤ slotConstant d s f * B ^ (d - j) :=
          mul_le_mul (coeffMass_le_slotConstant d hi (Finset.mem_range.mpr (by omega)))
            (pow_le_pow_right₀ hB (h i hi j)) (by positivity) (zero_le_slotConstant d s f)
  · have hdegi : (f i).natDegree ≤ d := hdeg i hi
    have hz : (f i).coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hz]
    have hzero : MvPolynomial.eval a (0 : MvPolynomial (Fin n) ℤ) = 0 := map_zero _
    rw [hzero, norm_zero]
    exact mul_nonneg (zero_le_slotConstant d s f) (by positivity)

theorem phase1TerminalCoeffBd (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x ∈ (Work.Peluse.UControl.histTerminal P hd).H,
      Work.Peluse.UControl.coeffBd P.natDegree C ((Work.Peluse.UControl.histTerminal P hd).Q x.1 x.2) := by
  have hd1 : 1 ≤ P.natDegree := by omega
  have hY : (histTerminal P hd).Ctrl := by
    have hinit : (petHistInit P hd1).Ctrl := petHistInit_ctrl P hd1
    have hchain : (phase1Chain (⟨0, petHistInit P hd1⟩ : HState P.natDegree)).2.Ctrl :=
      histData_ctrl_phase1Chain _ hinit
    have hphase := histPhase1Inv hd P.leadingCoeff
      (⟨0, petHistInit P hd1⟩ : HState P.natDegree) (petHistInit_phase1 P hd1)
    exact histData_ctrl_step (X := (phase1Chain (⟨0, petHistInit P hd1⟩ : HState P.natDegree)).2)
      (Sum.inr 0) 0 (hphase.pLive 0) hchain
  obtain ⟨C, hC1, hC⟩ := coeffBd_of_ctrl (s := (histTerminal P hd).H)
    (f := fun x => (histTerminal P hd).Q x.1 x.2)
    (fun x hx => (histTerminal P hd).hd x hx) hY
  exact ⟨C, hC1, hC⟩

end

end Work.Peluse.UControl
