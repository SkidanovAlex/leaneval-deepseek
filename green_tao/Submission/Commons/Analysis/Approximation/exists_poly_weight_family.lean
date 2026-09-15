import Mathlib
import Submission.Commons.Analysis.Approximation.exists_mvpolynomial_near_of_continuousOn

noncomputable section
open Finset
open scoped BigOperators

namespace Commons.Analysis.Approximation

/-! ## Real coefficient ℓ¹ "mass" of a multivariate polynomial -/

/-- The coefficient-`ℓ¹` mass of a multivariate polynomial over `ℝ`: the sum of the
absolute values of its coefficients. -/
def coeffMass {σ : Type*} [DecidableEq σ] (P : MvPolynomial σ ℝ) : ℝ :=
  ∑ m ∈ P.support, |P.coeff m|

lemma coeffMass_nonneg {σ : Type*} [DecidableEq σ] (P : MvPolynomial σ ℝ) : 0 ≤ coeffMass P :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma coeffMass_monomial {σ : Type*} [DecidableEq σ] (m : σ →₀ ℕ) (a : ℝ) :
    coeffMass (MvPolynomial.monomial m a) = |a| := by
  rw [coeffMass]
  by_cases h : a = 0
  · subst h; simp
  · rw [MvPolynomial.support_monomial, if_neg h, Finset.sum_singleton,
      MvPolynomial.coeff_monomial]; simp

lemma coeffMass_one {σ : Type*} [DecidableEq σ] :
    coeffMass (1 : MvPolynomial σ ℝ) = 1 := by
  have : (1 : MvPolynomial σ ℝ) = MvPolynomial.monomial 0 1 := by
    rw [MvPolynomial.monomial_zero']; simp
  rw [this, coeffMass_monomial]; norm_num

lemma coeffMass_sum_le {σ ι : Type*} [DecidableEq σ] (s : Finset ι)
    (A : ι → MvPolynomial σ ℝ) :
    coeffMass (∑ i ∈ s, A i) ≤ ∑ i ∈ s, coeffMass (A i) := by
  unfold coeffMass
  have key : ∀ i ∈ s, ∑ m ∈ (∑ i ∈ s, A i).support, |MvPolynomial.coeff m (A i)|
      ≤ ∑ m ∈ (A i).support, |MvPolynomial.coeff m (A i)| := by
    intro i hi
    have hsub : (A i).support ⊆ (∑ i ∈ s, A i).support ∪ (A i).support := Finset.subset_union_right
    have hzero : ∀ x ∈ (∑ i ∈ s, A i).support ∪ (A i).support,
        x ∉ (A i).support → |MvPolynomial.coeff x (A i)| = 0 := by
      intro x _ hxn
      have h0 : MvPolynomial.coeff x (A i) = 0 := by
        by_contra h
        exact hxn (MvPolynomial.mem_support_iff.mpr h)
      simp [h0]
    rw [Finset.sum_subset hsub hzero]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      (fun m _ _ => abs_nonneg _)
  calc ∑ m ∈ (∑ i ∈ s, A i).support, |MvPolynomial.coeff m (∑ i ∈ s, A i)|
      ≤ ∑ m ∈ (∑ i ∈ s, A i).support, ∑ i ∈ s, |MvPolynomial.coeff m (A i)| := by
        apply Finset.sum_le_sum
        intro m hm
        rw [MvPolynomial.coeff_sum]
        exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, ∑ m ∈ (∑ i ∈ s, A i).support, |MvPolynomial.coeff m (A i)| := by
        rw [Finset.sum_comm]
    _ ≤ ∑ i ∈ s, ∑ m ∈ (A i).support, |MvPolynomial.coeff m (A i)| :=
        Finset.sum_le_sum key

lemma coeffMass_mul_le {σ : Type*} [DecidableEq σ] (P Q : MvPolynomial σ ℝ) :
    coeffMass (P * Q) ≤ coeffMass P * coeffMass Q := by
  have hPQ : P * Q = ∑ a ∈ P.support, ∑ b ∈ Q.support,
      MvPolynomial.monomial (a + b)
        (MvPolynomial.coeff a P * MvPolynomial.coeff b Q) := by
    nth_rewrite 1 [MvPolynomial.as_sum P]
    nth_rewrite 1 [MvPolynomial.as_sum Q]
    simp only [Finset.sum_mul, Finset.mul_sum, MvPolynomial.monomial_mul]
    exact Finset.sum_comm
  rw [hPQ]
  calc coeffMass (∑ a ∈ P.support, ∑ b ∈ Q.support,
          MvPolynomial.monomial (a + b)
            (MvPolynomial.coeff a P * MvPolynomial.coeff b Q))
      ≤ ∑ a ∈ P.support, coeffMass (∑ b ∈ Q.support,
          MvPolynomial.monomial (a + b)
            (MvPolynomial.coeff a P * MvPolynomial.coeff b Q)) :=
        coeffMass_sum_le _ _
    _ ≤ ∑ a ∈ P.support, ∑ b ∈ Q.support, coeffMass (MvPolynomial.monomial (a + b)
          (MvPolynomial.coeff a P * MvPolynomial.coeff b Q)) :=
        Finset.sum_le_sum (fun a _ => coeffMass_sum_le _ _)
    _ = ∑ a ∈ P.support, ∑ b ∈ Q.support,
          |MvPolynomial.coeff a P| * |MvPolynomial.coeff b Q| := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        rw [coeffMass_monomial, abs_mul]
    _ = (∑ a ∈ P.support, |MvPolynomial.coeff a P|) *
          (∑ b ∈ Q.support, |MvPolynomial.coeff b Q|) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
    _ = coeffMass P * coeffMass Q := by rfl

lemma coeffMass_prod_le {σ ι : Type*} [DecidableEq σ] (s : Finset ι)
    (A : ι → MvPolynomial σ ℝ) :
    coeffMass (∏ i ∈ s, A i) ≤ ∏ i ∈ s, coeffMass (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using le_of_eq (coeffMass_one (σ := σ))
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      calc coeffMass (A a * ∏ i ∈ s, A i) ≤ coeffMass (A a) * coeffMass (∏ i ∈ s, A i) :=
            coeffMass_mul_le _ _
        _ ≤ coeffMass (A a) * ∏ i ∈ s, coeffMass (A i) :=
            mul_le_mul_of_nonneg_left ih (coeffMass_nonneg _)

/-! ## The shifted one-variable polynomial -/

/-- For a bivariate polynomial `Q`, the one-variable polynomial in the variable `j`
obtained by substituting `X 0 ↦ C u` and `X 1 ↦ X j`. -/
def shiftPoly {K : ℕ} (Q : MvPolynomial (Fin 2) ℝ) (j : Fin K) (u : ℝ) :
    MvPolynomial (Fin K) ℝ :=
  ∑ m ∈ Q.support, MvPolynomial.monomial (Finsupp.single j (m (1 : Fin 2)))
    (Q.coeff m * u ^ (m (0 : Fin 2)))

lemma eval_shiftPoly {K : ℕ} (Q : MvPolynomial (Fin 2) ℝ) (j : Fin K) (u : ℝ)
    (t : Fin K → ℝ) :
    MvPolynomial.eval t (shiftPoly Q j u)
      = ∑ m ∈ Q.support, Q.coeff m * u ^ (m (0 : Fin 2)) * (t j) ^ (m (1 : Fin 2)) := by
  rw [shiftPoly, MvPolynomial.eval_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [MvPolynomial.eval_monomial, Finsupp.prod_single_index (h := fun n e => (t n) ^ e)]
  ring

lemma eval_Q_point {K : ℕ} (Q : MvPolynomial (Fin 2) ℝ) (j : Fin K) (u : ℝ)
    (t : Fin K → ℝ) :
    MvPolynomial.eval (fun i : Fin 2 => if i = (0 : Fin 2) then u else t j) Q
      = ∑ m ∈ Q.support, Q.coeff m * u ^ (m (0 : Fin 2)) * (t j) ^ (m (1 : Fin 2)) := by
  rw [MvPolynomial.eval_eq']
  apply Finset.sum_congr rfl
  intro m hm
  have hprod : ∏ i : Fin 2, (if i = (0 : Fin 2) then u else t j) ^ (m i)
      = u ^ (m (0 : Fin 2)) * (t j) ^ (m (1 : Fin 2)) := by
    rw [Fin.prod_univ_two]; simp
  rw [hprod]; ring

lemma eval_shiftPoly_eq {K : ℕ} (Q : MvPolynomial (Fin 2) ℝ) (j : Fin K) (u : ℝ)
    (t : Fin K → ℝ) :
    MvPolynomial.eval t (shiftPoly Q j u)
      = MvPolynomial.eval (fun i : Fin 2 => if i = (0 : Fin 2) then u else t j) Q := by
  rw [eval_shiftPoly, eval_Q_point]

lemma coeffMass_shiftPoly_le {K : ℕ} (Q : MvPolynomial (Fin 2) ℝ) (j : Fin K)
    {u C : ℝ} (hC : 0 ≤ C) (hu : |u| ≤ C) :
    coeffMass (shiftPoly Q j u) ≤ ∑ m ∈ Q.support, |Q.coeff m| * C ^ (m (0 : Fin 2)) := by
  rw [shiftPoly]
  refine le_trans (coeffMass_sum_le _ _) ?_
  apply Finset.sum_le_sum
  intro m hm
  rw [coeffMass_monomial, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg u) hu _) (abs_nonneg _)

/-! ## Telescoping product inequality -/

lemma abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ) {M : ℝ}
    (hM : 1 ≤ M) (ha : ∀ i ∈ s, |a i| ≤ M) (hb : ∀ i ∈ s, |b i| ≤ M) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ M ^ s.card * ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      have ha' : ∀ k ∈ s, |a k| ≤ M := fun k hk => ha k (Finset.mem_insert_of_mem hk)
      have hb' : ∀ k ∈ s, |b k| ≤ M := fun k hk => hb k (Finset.mem_insert_of_mem hk)
      have hAi : |a i| ≤ M := ha i (Finset.mem_insert_self i s)
      have hprodB : |∏ k ∈ s, b k| ≤ M ^ s.card := by
        rw [Finset.abs_prod]
        calc ∏ k ∈ s, |b k| ≤ ∏ k ∈ s, M :=
              Finset.prod_le_prod (fun k _ => abs_nonneg _) (fun k hk => hb' k hk)
          _ = M ^ s.card := Finset.prod_const M
      have hih := ih ha' hb'
      rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi,
        Finset.card_insert_of_notMem hi]
      calc |a i * ∏ k ∈ s, a k - b i * ∏ k ∈ s, b k|
          = |a i * (∏ k ∈ s, a k - ∏ k ∈ s, b k) + (a i - b i) * ∏ k ∈ s, b k| := by ring_nf
        _ ≤ |a i * (∏ k ∈ s, a k - ∏ k ∈ s, b k)| + |(a i - b i) * ∏ k ∈ s, b k| :=
              abs_add_le _ _
        _ = |a i| * |∏ k ∈ s, a k - ∏ k ∈ s, b k| + |a i - b i| * |∏ k ∈ s, b k| := by
              rw [abs_mul, abs_mul]
        _ ≤ M * (M ^ s.card * ∑ k ∈ s, |a k - b k|) + |a i - b i| * M ^ s.card := by
              apply add_le_add
              · exact mul_le_mul hAi hih (abs_nonneg _) (le_trans zero_le_one hM)
              · exact mul_le_mul_of_nonneg_left hprodB (abs_nonneg _)
        _ ≤ M * (M ^ s.card * ∑ k ∈ s, |a k - b k|) + |a i - b i| * M ^ (s.card + 1) := by
              exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
                (pow_le_pow_right₀ hM (Nat.le_succ s.card)) (abs_nonneg _))
        _ = M ^ (s.card + 1) * (|a i - b i| + ∑ k ∈ s, |a k - b k|) := by
              rw [pow_succ']; ring

/-! ## Continuous extension of `ψ` by clamping -/

lemma continuous_clamp_comp {M ε C : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hC : 0 ≤ C) {ψ : ℝ → ℝ}
    (hψ : ContinuousOn ψ (Set.Icc (-((C + M) / ε)) ((C + M) / ε))) :
    Continuous (fun y : ℝ => ψ (max (-((C + M) / ε)) (min ((C + M) / ε) y))) := by
  have hab : -((C + M) / ε) ≤ (C + M) / ε := by
    have : 0 ≤ (C + M) / ε := div_nonneg (by linarith) hε.le
    linarith
  have hclamp : Continuous (fun y : ℝ => max (-((C + M) / ε)) (min ((C + M) / ε) y)) :=
    Continuous.max continuous_const (Continuous.min continuous_const continuous_id)
  have hrange : ∀ y : ℝ,
      max (-((C + M) / ε)) (min ((C + M) / ε) y) ∈ Set.Icc (-((C + M) / ε)) ((C + M) / ε) :=
    fun y => ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  exact hψ.comp_continuous hclamp hrange

lemma clamp_eq_of_mem {M ε C : ℝ} {ψ : ℝ → ℝ} {y : ℝ}
    (hy : y ∈ Set.Icc (-((C + M) / ε)) ((C + M) / ε)) :
    ψ (max (-((C + M) / ε)) (min ((C + M) / ε) y)) = ψ y := by
  congr 1
  rw [min_eq_right hy.2, max_eq_right hy.1]

/-! ## The main result -/

theorem exists_poly_weight_family {K : ℕ} {M ε C η' : ℝ} (hM : 0 ≤ M) (hε : 0 < ε)
    (hC : 0 ≤ C) (hη' : 0 < η') {ψ : ℝ → ℝ}
    (hψ : ContinuousOn ψ (Set.Icc (-((C + M) / ε)) ((C + M) / ε)))
    (hψ01 : ∀ u ∈ Set.Icc (-((C + M) / ε)) ((C + M) / ε), 0 ≤ ψ u ∧ ψ u ≤ 1) :
    ∃ E₀ : ℝ, 0 ≤ E₀ ∧ ∀ c : Fin K → ℝ, (∀ j, |c j| ≤ C) →
      ∃ P : MvPolynomial (Fin K) ℝ,
        (∀ t ∈ Set.pi Set.univ (fun _ : Fin K => Set.Icc (-M) M),
          |∏ j, ψ ((t j - c j) / ε) - MvPolynomial.eval t P| ≤ η') ∧
        (∑ m ∈ P.support, |P.coeff m|) ≤ E₀ := by
  have hψe : Continuous (fun y : ℝ => ψ (max (-((C + M) / ε)) (min ((C + M) / ε) y))) :=
    continuous_clamp_comp hM hε hC hψ
  set I : ℝ := max C M with hIdef
  have hI : 0 ≤ I := by rw [hIdef]; exact le_trans hC (le_max_left C M)
  have hCI : C ≤ I := by rw [hIdef]; exact le_max_left C M
  have hMI : M ≤ I := by rw [hIdef]; exact le_max_right C M
  have hlin : Continuous (fun x : Fin 2 → ℝ => (x (1 : Fin 2) - x (0 : Fin 2)) / ε) := by
    apply Continuous.div_const
    apply Continuous.sub
    · exact continuous_apply (1 : Fin 2)
    · exact continuous_apply (0 : Fin 2)
  have hcont : Continuous
      (fun x : Fin 2 → ℝ => ψ (max (-((C + M) / ε)) (min ((C + M) / ε)
        ((x (1 : Fin 2) - x (0 : Fin 2)) / ε)))) :=
    hψe.comp hlin
  set T : ℝ := (2 : ℝ) ^ K * (K : ℝ) with hTdef
  have hTnn : 0 ≤ T := by rw [hTdef]; positivity
  set δ : ℝ := min 1 (η' / (T + 1)) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min one_pos (div_pos hη' (by linarith))
  have hδle1 : δ ≤ 1 := by rw [hδdef]; exact min_le_left _ _
  have hδle : δ ≤ η' / (T + 1) := by rw [hδdef]; exact min_le_right _ _
  obtain ⟨Q, hQ⟩ := exists_mvpolynomial_near_of_continuousOn I hI
    (fun x : Fin 2 → ℝ => ψ (max (-((C + M) / ε)) (min ((C + M) / ε)
      ((x (1 : Fin 2) - x (0 : Fin 2)) / ε)))) hcont.continuousOn hδpos
  set B : ℝ := ∑ m ∈ Q.support, |Q.coeff m| * C ^ (m (0 : Fin 2)) with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    exact Finset.sum_nonneg (fun m _ => mul_nonneg (abs_nonneg _) (pow_nonneg hC _))
  refine ⟨B ^ K, pow_nonneg hBnn K, ?_⟩
  intro c hc
  refine ⟨∏ j : Fin K, shiftPoly Q j (c j), ?_, ?_⟩
  · intro t ht
    have ht' : ∀ j, t j ∈ Set.Icc (-M) M := fun j =>
      (Set.mem_pi.mp ht) j (Set.mem_univ j)
    have harg : ∀ j, (t j - c j) / ε ∈ Set.Icc (-((C + M) / ε)) ((C + M) / ε) := by
      intro j
      have ht1 : -M ≤ t j := (ht' j).1
      have ht2 : t j ≤ M := (ht' j).2
      have hc1 : -C ≤ c j := (abs_le.mp (hc j)).1
      have hc2 : c j ≤ C := (abs_le.mp (hc j)).2
      constructor
      · have h : -((C + M) / ε) = (-(C + M)) / ε := by rw [neg_div]
        rw [h]
        exact (div_le_div_iff_of_pos_right hε).mpr (by linarith)
      · exact (div_le_div_iff_of_pos_right hε).mpr (by linarith)
    have habs : ∀ j, |ψ ((t j - c j) / ε)
        - MvPolynomial.eval t (shiftPoly Q j (c j))| ≤ δ := by
      intro j
      set x : Fin 2 → ℝ := fun i => if i = (0 : Fin 2) then c j else t j with hxdef
      have hx0 : x (0 : Fin 2) = c j := by simp [hxdef]
      have hx1 : x (1 : Fin 2) = t j := by simp [hxdef]
      have hxl : x ∈ Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (-I) I) := by
        rw [Set.mem_pi]
        intro i _
        fin_cases i
        · change x (0 : Fin 2) ∈ Set.Icc (-I) I
          have h := abs_le.mp (hc j)
          rw [Set.mem_Icc, hx0]
          exact ⟨by linarith [h.1, hCI], le_trans h.2 hCI⟩
        · change x (1 : Fin 2) ∈ Set.Icc (-I) I
          have h := ht' j
          rw [Set.mem_Icc, hx1]
          exact ⟨by linarith [h.1, hMI], le_trans h.2 hMI⟩
      have hQx := hQ x hxl
      have hPhi : ψ (max (-((C + M) / ε)) (min ((C + M) / ε) ((x (1 : Fin 2) - x (0 : Fin 2)) / ε)))
          = ψ ((t j - c j) / ε) := by
        rw [hx1, hx0]
        exact clamp_eq_of_mem (harg j)
      have hbx : MvPolynomial.eval x Q = MvPolynomial.eval t (shiftPoly Q j (c j)) := by
        rw [hxdef]
        exact (eval_shiftPoly_eq Q j (c j) t).symm
      rw [hPhi, hbx] at hQx
      exact hQx
    have ha1 : ∀ j, |ψ ((t j - c j) / ε)| ≤ 1 := by
      intro j
      have h01 := hψ01 _ (harg j)
      rw [abs_le]
      exact ⟨by linarith [h01.1], h01.2⟩
    have hbD : ∀ j, |MvPolynomial.eval t (shiftPoly Q j (c j))| ≤ 1 + δ := by
      intro j
      have h := habs j
      have h1 := ha1 j
      calc |MvPolynomial.eval t (shiftPoly Q j (c j))|
          = |(MvPolynomial.eval t (shiftPoly Q j (c j)) - ψ ((t j - c j) / ε))
              + ψ ((t j - c j) / ε)| := by ring_nf
        _ ≤ |MvPolynomial.eval t (shiftPoly Q j (c j)) - ψ ((t j - c j) / ε)|
              + |ψ ((t j - c j) / ε)| := abs_add_le _ _
        _ ≤ δ + 1 := by
              apply add_le_add
              · rw [abs_sub_comm]; exact h
              · exact h1
        _ = 1 + δ := by ring
    rw [MvPolynomial.eval_prod]
    have hkey := abs_prod_sub_prod_le (Finset.univ : Finset (Fin K))
      (fun j => ψ ((t j - c j) / ε))
      (fun j => MvPolynomial.eval t (shiftPoly Q j (c j)))
      (M := 1 + δ) (by linarith)
      (fun j _ => le_trans (ha1 j) (by linarith))
      (fun j _ => hbD j)
    have hkey' : |∏ j : Fin K, ψ ((t j - c j) / ε)
        - ∏ j : Fin K, MvPolynomial.eval t (shiftPoly Q j (c j))|
        ≤ (1 + δ) ^ K * ∑ j : Fin K, |ψ ((t j - c j) / ε)
          - MvPolynomial.eval t (shiftPoly Q j (c j))| := by
      simpa [Finset.card_univ, Fintype.card_fin] using hkey
    have hsum : ∑ j : Fin K, |ψ ((t j - c j) / ε)
        - MvPolynomial.eval t (shiftPoly Q j (c j))| ≤ (K : ℝ) * δ := by
      calc ∑ j : Fin K, |ψ ((t j - c j) / ε)
              - MvPolynomial.eval t (shiftPoly Q j (c j))|
          ≤ ∑ _j : Fin K, δ := Finset.sum_le_sum (fun j _ => habs j)
        _ = (K : ℝ) * δ := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hpow : (1 + δ) ^ K ≤ (2 : ℝ) ^ K :=
      pow_le_pow_left₀ (by linarith) (by linarith) K
    calc |∏ j : Fin K, ψ ((t j - c j) / ε)
            - ∏ j : Fin K, MvPolynomial.eval t (shiftPoly Q j (c j))|
        ≤ (1 + δ) ^ K * ∑ j : Fin K, |ψ ((t j - c j) / ε)
            - MvPolynomial.eval t (shiftPoly Q j (c j))| := hkey'
      _ ≤ (2 : ℝ) ^ K * ((K : ℝ) * δ) := by
            apply mul_le_mul hpow hsum (by positivity) (by positivity)
      _ = T * δ := by rw [hTdef]; ring
      _ ≤ η' := by
            calc T * δ ≤ T * (η' / (T + 1)) := mul_le_mul_of_nonneg_left hδle hTnn
              _ = T * η' / (T + 1) := by ring
              _ ≤ η' := by
                  rw [div_le_iff₀ (by linarith)]
                  nlinarith [hη']
  · change coeffMass (∏ j : Fin K, shiftPoly Q j (c j)) ≤ B ^ K
    calc coeffMass (∏ j : Fin K, shiftPoly Q j (c j))
        ≤ ∏ j : Fin K, coeffMass (shiftPoly Q j (c j)) := coeffMass_prod_le _ _
      _ ≤ ∏ _j : Fin K, B :=
            Finset.prod_le_prod (fun j _ => coeffMass_nonneg _)
              (fun j _ => by rw [hBdef]; exact coeffMass_shiftPoly_le Q j hC (hc j))
      _ = B ^ K := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Commons.Analysis.Approximation
