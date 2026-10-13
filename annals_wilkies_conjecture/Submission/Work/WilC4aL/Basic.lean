/-
  annals_wilkies_conjecture, area C4aL (`C4a_lift`): basic API.

  Elementary facts about `rexp`, the index layout `piIdx`, the substitutions
  `valE`/`valC`/`rvE`, the monomial reversal `ddMon`, and analyticity of `Ppart`.
-/
import Submission.Work.WilC4aL.Defs

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilC4aL
open WilkiesDesign WilkiesDesign.CG.C4a
open scoped BigOperators

variable {k m : ℕ}

/-! ## 1. `rexp` -/

theorem rexp_of_abs_lt_one {x : ℝ} (h : |x| < 1) : rexp x = Real.exp x := by
  simp [rexp, le_of_lt h]

theorem rexp_of_abs_le_one {x : ℝ} (h : |x| ≤ 1) : rexp x = Real.exp x := by
  simp [rexp, h]

theorem rexp_of_one_lt_abs {x : ℝ} (h : 1 < |x|) : rexp x = 0 := by
  simp [rexp, not_le.mpr h]

theorem rexp_of_sq_eq_one {x : ℝ} (h : x ^ 2 = 1) : rexp x = Real.exp x := by
  have h1 : |x| = 1 := by
    have h2 : |x| ^ 2 = 1 := by rw [sq_abs, h]
    nlinarith [abs_nonneg x, sq_nonneg (|x| - 1)]
  rw [rexp_of_abs_le_one (by rw [h1])]

theorem rexp_inv_of_abs_lt_one {x : ℝ} (h : |x| < 1) (hx : x ≠ 0) : rexp x⁻¹ = 0 := by
  refine rexp_of_one_lt_abs ?_
  rw [abs_inv, one_lt_inv₀ (abs_pos.mpr hx)]
  exact h

/-! ## 2. The index layout -/

theorem piIdx_of_lt_two {i : Fin (k + 2 + m)} (h : (i : ℕ) < 2) :
    piIdx i = Sum.inr ⟨(i : ℕ), by omega⟩ := by
  rw [piIdx, dite_eq_left h]

theorem piIdx_of_ge_two {i : Fin (k + 2 + m)} (h : ¬ (i : ℕ) < 2) (h2 : (i : ℕ) < k + 2) :
    piIdx i = Sum.inl ⟨(i : ℕ) - 2, by omega⟩ := by
  rw [piIdx, dite_eq_right h, dite_eq_left h2]

theorem piIdx_of_ge {i : Fin (k + 2 + m)} (h : ¬ (i : ℕ) < 2) (h2 : ¬ (i : ℕ) < k + 2) :
    piIdx i = Sum.inr ⟨(i : ℕ) - k, by omega⟩ := by
  rw [piIdx, dite_eq_right h, dite_eq_right h2]

theorem val_idxX : (idxX (k := k) (m := m) : ℕ) = 0 := rfl

theorem val_idxY : (idxY (k := k) (m := m) : ℕ) = 1 := rfl

theorem val_idxC (j : Fin k) : (idxC (m := m) j : ℕ) = (j : ℕ) + 2 := rfl

theorem val_idxW (j : Fin m) : (idxW (k := k) j : ℕ) = (k + 2) + (j : ℕ) := rfl

theorem piIdx_idxX : piIdx (idxX (k := k) (m := m)) = Sum.inr 0 := by
  rw [piIdx_of_lt_two (i := idxX) (by rw [val_idxX]; exact Nat.zero_lt_two)]
  rfl

theorem piIdx_idxY : piIdx (idxY (k := k) (m := m)) = Sum.inr 1 := by
  rw [piIdx_of_lt_two (i := idxY) (by rw [val_idxY]; exact Nat.one_lt_two)]
  rfl

theorem piIdx_idxC (j : Fin k) : piIdx (idxC (m := m) j) = Sum.inl j := by
  rw [piIdx_of_ge_two (i := idxC j) (by rw [val_idxC]; omega) (by rw [val_idxC]; omega)]
  refine congrArg Sum.inl (Fin.ext ?_)
  show ((idxC (m := m) j : ℕ)) - 2 = (j : ℕ)
  rw [val_idxC]; omega

theorem piIdx_idxW (j : Fin m) : piIdx (idxW (k := k) j) = Sum.inr (Fin.succ (Fin.succ j)) := by
  rw [piIdx_of_ge (i := idxW j) (by rw [val_idxW]; omega) (by rw [val_idxW]; omega)]
  refine congrArg Sum.inr (Fin.ext ?_)
  show ((idxW (k := k) j : ℕ)) - k = (j : ℕ) + 2
  rw [val_idxW]; omega

/-- Every index of the `k+2` block is `0`, `1`, or `Fin.succ (Fin.succ j)`. -/
theorem fin_two_cases {C : (i : Fin (k + 2)) → Prop} (h0 : C 0)
    (h1 : C (Fin.succ (0 : Fin (k + 1))))
    (hj : ∀ j : Fin k, C (Fin.succ (Fin.succ j))) : ∀ i : Fin (k + 2), C i := by
  intro i
  rcases Nat.lt_or_ge (i : ℕ) 2 with h | h
  · by_cases hi0 : (i : ℕ) = 0
    · rw [show i = 0 from Fin.ext hi0]; exact h0
    · have hi1 : (i : ℕ) = 1 := by omega
      have hie : i = Fin.succ (0 : Fin (k + 1)) := by
        refine Fin.ext ?_
        show (i : ℕ) = 0 + 1
        omega
      rw [hie]; exact h1
  · have hik : i = Fin.succ (Fin.succ ⟨(i : ℕ) - 2, by omega⟩) := by
      refine Fin.ext ?_
      show (i : ℕ) = ((i : ℕ) - 2) + 1 + 1
      omega
    rw [hik]; exact hj _

/-! ## 3. The substitutions -/

theorem valE_idxX (cc : Fin k → ℝ) (σ : Fin (m + 2) → VC) (z : Fin (m + 2) → ℝ) :
    valE cc σ (idxX (k := k) (m := m)) z = if σ 0 = VC.big then (z 0)⁻¹ else z 0 := by
  simp only [valE, piIdx_idxX, Sum.elim_inr]

theorem valE_idxY (cc : Fin k → ℝ) (σ : Fin (m + 2) → VC) (z : Fin (m + 2) → ℝ) :
    valE cc σ (idxY (k := k) (m := m)) z = if σ 1 = VC.big then (z 1)⁻¹ else z 1 := by
  simp only [valE, piIdx_idxY, Sum.elim_inr]

theorem valE_idxC (cc : Fin k → ℝ) (σ : Fin (m + 2) → VC) (j : Fin k)
    (z : Fin (m + 2) → ℝ) :
    valE cc σ (idxC (m := m) j) z = cc j := by
  simp only [valE, piIdx_idxC, Sum.elim_inl]

theorem valE_idxW (cc : Fin k → ℝ) (σ : Fin (m + 2) → VC) (j : Fin m)
    (z : Fin (m + 2) → ℝ) :
    valE cc σ (idxW (k := k) j) z =
      if σ (Fin.succ (Fin.succ j)) = VC.big then (z (Fin.succ (Fin.succ j)))⁻¹
        else z (Fin.succ (Fin.succ j)) := by
  simp only [valE, piIdx_idxW, Sum.elim_inr]

theorem rvE_idxC (cc : Fin k → ℝ) (σ : Fin (m + 2) → VC) (j : Fin k)
    (z : Fin (m + 2) → ℝ) : rvE cc σ (idxC (m := m) j) z = rexp (cc j) := by
  simp only [rvE, piIdx_idxC, Sum.elim_inl]

theorem isBigB_true_iff (σ : Fin (m + 2) → VC) (i : Fin (k + 2 + m)) :
    isBigB σ i = true ↔ ∃ j, piIdx i = Sum.inr j ∧ σ j = VC.big := by
  rcases hp : piIdx i with j | j
  · rw [isBigB, hp, Sum.elim_inl]; simp
  · rw [isBigB, hp, Sum.elim_inr, decide_eq_true_eq]
    exact ⟨fun h => ⟨j, rfl, h⟩, fun ⟨j', hj', hb⟩ => by
      rw [Sum.inr.inj_iff] at hj'; exact hj' ▸ hb⟩

theorem isBigB_false_iff (σ : Fin (m + 2) → VC) (i : Fin (k + 2 + m)) :
    isBigB σ i = false ↔ ∀ j, piIdx i = Sum.inr j → σ j ≠ VC.big := by
  rcases hp : piIdx i with j | j
  · rw [isBigB, hp, Sum.elim_inl]; simp
  · rw [isBigB, hp, Sum.elim_inr, decide_eq_false_iff_not]
    exact ⟨fun h j' hj' => by rw [Sum.inr.inj_iff] at hj'; exact hj' ▸ h,
      fun h => h j rfl⟩

theorem rvE_eq_zero_of_big (cc : Fin k → ℝ) (σ : Fin (m + 2) → VC) (i : Fin (k + 2 + m))
    (h : isBigB σ i = true) (z : Fin (m + 2) → ℝ) : rvE cc σ i z = 0 := by
  obtain ⟨j, hj, hbig⟩ := (isBigB_true_iff σ i).mp h
  simp only [rvE, hj, Sum.elim_inr, hbig, ite_true]

theorem valE_eq_inv_of_big (cc : Fin k → ℝ) (σ : Fin (m + 2) → VC) (i : Fin (k + 2 + m))
    (h : isBigB σ i = true) (z : Fin (m + 2) → ℝ) :
    valE cc σ i z = (z (coordOf i))⁻¹ := by
  obtain ⟨j, hj, hbig⟩ := (isBigB_true_iff σ i).mp h
  have hc : coordOf i = j := by simp only [coordOf, hj, Sum.elim_inr, id_eq]
  rw [hc]
  simp only [valE, hj, Sum.elim_inr, hbig, ite_true]

theorem valC_eq_val_of_big (cc : Fin k → ℝ) (σ : Fin (m + 2) → VC) (i : Fin (k + 2 + m))
    (h : isBigB σ i = true) (z : Fin (m + 2) → ℝ) :
    valC cc σ i z = z (coordOf i) := by
  obtain ⟨j, hj, _⟩ := (isBigB_true_iff σ i).mp h
  have hc : coordOf i = j := by simp only [coordOf, hj, Sum.elim_inr, id_eq]
  rw [hc]
  simp only [valC, hj, Sum.elim_inr]

theorem valC_eq_valE_of_not_big (cc : Fin k → ℝ) (σ : Fin (m + 2) → VC)
    (i : Fin (k + 2 + m)) (h : isBigB σ i = false) (z : Fin (m + 2) → ℝ) :
    valC cc σ i z = valE cc σ i z := by
  rcases hp : piIdx i with j | j
  · simp only [valC, valE, hp, Sum.elim_inl]
  · have hbig : σ j ≠ VC.big := (isBigB_false_iff σ i).mp h j hp
    simp only [valC, valE, hp, Sum.elim_inr, if_neg hbig]

theorem bigSum_inl (σ : Fin (m + 2) → VC) (i : Fin (k + 2 + m)) :
    bigSum σ (Sum.inl i) = isBigB σ i := rfl

theorem bigSum_inr (σ : Fin (m + 2) → VC) (i : Fin (k + 2 + m)) :
    bigSum σ (Sum.inr i) = false := rfl

theorem coordOf_big (σ : Fin (m + 2) → VC) {i : Fin (k + 2 + m)} (h : isBigB σ i = true) :
    piIdx i = Sum.inr (coordOf i) ∧ σ (coordOf i) = VC.big := by
  obtain ⟨j, hj, hb⟩ := (isBigB_true_iff σ i).mp h
  have hc : coordOf i = j := by simp only [coordOf, hj, Sum.elim_inr, id_eq]
  exact ⟨by rw [hc]; exact hj, by rw [hc]; exact hb⟩

/-! ## 4. Reversal of monomial exponents -/

theorem ddMon_apply (σ : Fin (m + 2) → VC) (D : ℕ)
    (d : Fin (k + 2 + m) ⊕ Fin (k + 2 + m) →₀ ℕ)
    (x : Fin (k + 2 + m) ⊕ Fin (k + 2 + m)) :
    ddMon σ D d x = ddExp σ D d x := rfl

theorem ddMon_apply_of_big (σ : Fin (m + 2) → VC) (D : ℕ)
    (d : Fin (k + 2 + m) ⊕ Fin (k + 2 + m) →₀ ℕ)
    {x : Fin (k + 2 + m) ⊕ Fin (k + 2 + m)} (h : bigSum σ x = true) :
    ddMon σ D d x = D - d x := by
  rw [ddMon_apply, ddExp, if_pos h]

theorem ddMon_apply_of_not_big (σ : Fin (m + 2) → VC) (D : ℕ)
    (d : Fin (k + 2 + m) ⊕ Fin (k + 2 + m) →₀ ℕ)
    {x : Fin (k + 2 + m) ⊕ Fin (k + 2 + m)} (h : bigSum σ x = false) :
    ddMon σ D d x = d x := by
  rw [ddMon_apply, ddExp, if_neg (by simp [h])]

/-- Every exponent of a monomial in the support is at most the total degree. -/
theorem exp_le_totalDegree {σ : Type*} {P : MvPolynomial σ ℝ} {d : σ →₀ ℕ} (hd : d ∈ P.support)
    (x : σ) : d x ≤ P.totalDegree := by
  refine le_trans ?_ (MvPolynomial.le_totalDegree hd)
  have h1 : d x ≤ ∑ y ∈ d.support, d y := by
    by_cases hx : x ∈ d.support
    · exact Finset.single_le_sum (fun i _ => Nat.zero_le _) hx
    · rw [Finsupp.mem_support_iff] at hx
      simp only [not_not] at hx
      rw [hx]; exact Nat.zero_le _
  have h2 : d.sum (fun _ e => e) = ∑ y ∈ d.support, d y := rfl
  rwa [h2]

/-! ## 5. Analyticity -/

theorem analyticAt_proj (j : Fin (m + 2)) (z : Fin (m + 2) → ℝ) :
    AnalyticAt ℝ (fun w : Fin (m + 2) → ℝ => w j) z := by
  have hfun : (fun w : Fin (m + 2) → ℝ => w j)
      = ⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (m + 2) => ℝ) j) :=
    funext fun w => (ContinuousLinearMap.proj_apply j w).symm
  rw [hfun]
  exact ContinuousLinearMap.analyticAt _ z

theorem analyticAt_ite {f g : (Fin (m + 2) → ℝ) → ℝ} {z : Fin (m + 2) → ℝ} (c : Prop)
    [Decidable c] (hf : AnalyticAt ℝ f z) (hg : AnalyticAt ℝ g z) :
    AnalyticAt ℝ (fun w => if c then f w else g w) z := by
  by_cases h : c
  · rw [show (fun w => if c then f w else g w) = f from funext fun w => if_pos h]
    exact hf
  · rw [show (fun w => if c then f w else g w) = g from funext fun w => if_neg h]
    exact hg

theorem analyticAt_finset_sum {ι : Type*} {f : ι → (Fin (m + 2) → ℝ) → ℝ} {s : Finset ι}
    {z : Fin (m + 2) → ℝ} (h : ∀ i ∈ s, AnalyticAt ℝ (f i) z) :
    AnalyticAt ℝ (fun w => ∑ i ∈ s, f i w) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using analyticAt_const (v := (0 : ℝ))
  | insert a s ha ih =>
      have h1 : AnalyticAt ℝ (f a) z := h a (Finset.mem_insert_self a s)
      have h2 : AnalyticAt ℝ (fun w => ∑ i ∈ s, f i w) z :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have hsum : (fun w : Fin (m + 2) → ℝ => ∑ i ∈ insert a s, f i w)
          = (fun w => f a w + ∑ i ∈ s, f i w) := by
        funext w; rw [Finset.sum_insert ha]
      rw [hsum]
      exact h1.add h2

theorem analyticAt_valC (cc : Fin k → ℝ) (σ : Fin (m + 2) → VC) (i : Fin (k + 2 + m))
    (z : Fin (m + 2) → ℝ) : AnalyticAt ℝ (fun w => valC cc σ i w) z := by
  rcases hp : piIdx i with j | j
  · rw [show (fun w => valC cc σ i w) = fun _ => cc j by
      funext w; simp only [valC, hp, Sum.elim_inl]]
    exact analyticAt_const
  · rw [show (fun w => valC cc σ i w) = fun w => w j by
      funext w; simp only [valC, hp, Sum.elim_inr]]
    exact analyticAt_proj j z

theorem analyticAt_rvE (cc : Fin k → ℝ) (σ : Fin (m + 2) → VC) (i : Fin (k + 2 + m))
    (z : Fin (m + 2) → ℝ) : AnalyticAt ℝ (fun w => rvE cc σ i w) z := by
  rcases hp : piIdx i with j | j
  · rw [show (fun w => rvE cc σ i w) = fun _ => rexp (cc j) by
      funext w; simp only [rvE, hp, Sum.elim_inl]]
    exact analyticAt_const
  · by_cases hb : σ j = VC.big
    · rw [show (fun w => rvE cc σ i w) = fun _ => (0 : ℝ) by
        funext w; simp only [rvE, hp, Sum.elim_inr, hb, ite_true]]
      exact analyticAt_const
    · rw [show (fun w => rvE cc σ i w) = fun w => Real.exp (w j) by
        funext w; simp only [rvE, hp, Sum.elim_inr, hb, ite_false]]
      exact (analyticAt_proj j z).rexp'

theorem analyticAt_Ppart (cc : Fin k → ℝ) (σ : Fin (m + 2) → VC) (D : ℕ)
    (P : MvPolynomial (Fin (k + 2 + m) ⊕ Fin (k + 2 + m)) ℝ) (z : Fin (m + 2) → ℝ) :
    AnalyticAt ℝ (fun w => Ppart cc σ D P w) z := by
  have hmain : ∀ x : Fin (k + 2 + m) ⊕ Fin (k + 2 + m),
      AnalyticAt ℝ (fun w => Sum.elim (fun i => valC cc σ i w) (fun i => rvE cc σ i w) x) z := by
    intro x
    rcases x with i | i
    · simpa only [Sum.elim_inl] using analyticAt_valC cc σ i z
    · simpa only [Sum.elim_inr] using analyticAt_rvE cc σ i z
  have h := AnalyticAt.aeval_mvPolynomial (𝕜 := ℝ) (A := ℝ) (B := ℝ)
    (f := fun w (x : Fin (k + 2 + m) ⊕ Fin (k + 2 + m)) =>
      Sum.elim (fun i => valC cc σ i w) (fun i => rvE cc σ i w) x)
    (z := z) hmain (clePoly σ D P)
  simpa only [Ppart, MvPolynomial.aeval_eq_eval] using h

theorem analyticAt_pieceF (cc : Fin k → ℝ) (σ : Fin (m + 2) → VC) (D : ℕ)
    (P : MvPolynomial (Fin (k + 2 + m) ⊕ Fin (k + 2 + m)) ℝ) (z : Fin (m + 2) → ℝ) :
    AnalyticAt ℝ (fun w => pieceF cc σ D P w) z := by
  refine (analyticAt_Ppart cc σ D P z).pow 2 |>.add ?_
  refine analyticAt_finset_sum (s := Finset.univ) (f := fun j (w : Fin (m + 2) → ℝ) =>
    if σ j = VC.one then (w j ^ 2 - 1) ^ 2 else 0) (fun j _ => ?_)
  exact analyticAt_ite (σ j = VC.one)
    ((((analyticAt_proj j z).pow 2).sub analyticAt_const).pow 2) analyticAt_const

theorem analyticAt_pieceG (σ : Fin (m + 2) → VC) (j : Fin (m + 2)) (q : Fin 2)
    (z : Fin (m + 2) → ℝ) : AnalyticAt ℝ (fun w => pieceG σ j q w) z := by
  have h0 : AnalyticAt ℝ (fun w : Fin (m + 2) → ℝ => w 0) z := analyticAt_proj 0 z
  have hj : AnalyticAt ℝ (fun w : Fin (m + 2) → ℝ => w j) z := analyticAt_proj j z
  have hc : AnalyticAt ℝ (fun _ : Fin (m + 2) → ℝ => (1 : ℝ)) z := analyticAt_const
  simp only [pieceG]
  exact analyticAt_ite ((j : ℕ) = 0)
    (analyticAt_ite ((q : ℕ) = 0) h0 (hc.sub h0))
    (analyticAt_ite (σ j = VC.small)
      (analyticAt_ite ((q : ℕ) = 0) (hc.sub (hj.pow 2)) hc)
      (analyticAt_ite (σ j = VC.one) hc
        (analyticAt_ite ((q : ℕ) = 0) (hj.pow 2) (hc.sub (hj.pow 2)))))

end Work.WilC4aL
