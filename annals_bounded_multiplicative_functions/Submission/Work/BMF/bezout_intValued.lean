import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.intval_basis
import Submission.Work.BMF.adi_basic
import Submission.Work.BMF.adi_defs
import Submission.Work.BMF.newton_series
import Submission.Work.BMF.binP_intValued

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF
open Polynomial Finset

section Helpers

private theorem dil_eval (c x : ℝ) (P : ℝ[X]) : (dil c P).eval x = P.eval (c * x) := by
  unfold dil
  rw [eval_comp, show eval x (C c * X) = c * x by rw [eval_mul, eval_C, eval_X]]

private theorem dil_sum (c : ℝ) {ι : Type*} (s : Finset ι) (f : ι → ℝ[X]) :
    dil c (∑ i ∈ s, f i) = ∑ i ∈ s, dil c (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, dil, zero_comp]
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, dil_add, ih]

private theorem natDegree_dil_sub_C_pow_le {P : ℝ[X]} {c : ℝ} {j : ℕ} (hP : P.natDegree ≤ j) :
    (dil c P - C (c ^ j) * P).natDegree ≤ j - 1 := by
  have hzero : ∀ N : ℕ, j ≤ N → (dil c P - C (c ^ j) * P).coeff N = 0 := by
    intro N hN
    rw [coeff_sub, coeff_dil, coeff_C_mul]
    by_cases h : N = j
    · subst h; ring
    · have hlj : P.natDegree < N := lt_of_le_of_lt hP (lt_of_le_of_ne hN (Ne.symm h))
      rw [coeff_eq_zero_of_natDegree_lt hlj]; ring
  have hdeg : (dil c P - C (c ^ j) * P).degree < (j : WithBot ℕ) :=
    (degree_lt_iff_coeff_zero _ j).mpr hzero
  by_cases hD : dil c P - C (c ^ j) * P = 0
  · rw [hD]; simp
  · have := (natDegree_lt_iff_degree_lt hD).mpr hdeg
    omega

private def IntVal (P : ℝ[X]) : Prop := ∀ n : ℤ, ∃ m : ℤ, P.eval (n : ℝ) = (m : ℝ)

private theorem IntVal.toIntegralOn {P : ℝ[X]} (h : IntVal P) : IntegralOn 1 P := by
  intro n; obtain ⟨m, hm⟩ := h n; exact ⟨m, by simpa using hm⟩

private theorem IntegralOn.toIntVal {P : ℝ[X]} (h : IntegralOn 1 P) : IntVal P := by
  intro n; obtain ⟨m, hm⟩ := h n; exact ⟨m, by simpa using hm⟩

private theorem IntVal_binP (j : ℕ) : IntVal (binP j) := fun n => binP_intValued j n

private theorem IntVal.add {P Q : ℝ[X]} (hP : IntVal P) (hQ : IntVal Q) : IntVal (P + Q) := by
  intro n; obtain ⟨m, hm⟩ := hP n; obtain ⟨l, hl⟩ := hQ n
  exact ⟨m + l, by rw [eval_add, hm, hl]; push_cast; ring⟩

private theorem IntVal.sub {P Q : ℝ[X]} (hP : IntVal P) (hQ : IntVal Q) : IntVal (P - Q) := by
  intro n; obtain ⟨m, hm⟩ := hP n; obtain ⟨l, hl⟩ := hQ n
  exact ⟨m - l, by rw [eval_sub, hm, hl]; push_cast; ring⟩

private theorem IntVal.zero : IntVal (0 : ℝ[X]) := fun n => ⟨0, by simp⟩

private theorem IntVal.sum {ι : Type*} (s : Finset ι) (f : ι → ℝ[X])
    (h : ∀ i ∈ s, IntVal (f i)) : IntVal (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact IntVal.zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact IntVal.add (h a (Finset.mem_insert_self a s))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

private theorem IntVal.dil {P : ℝ[X]} (c : ℕ) (hP : IntVal P) : IntVal (dil (c : ℝ) P) := by
  intro n; obtain ⟨m, hm⟩ := hP (c * n)
  refine ⟨m, ?_⟩
  rw [dil_eval, show (c : ℝ) * (n : ℝ) = ((c * n : ℤ) : ℝ) by push_cast; ring]
  simpa using hm

private def Good (j : ℕ) (P : ℝ[X]) : Prop := IntegralOn 1 P ∧ P.natDegree ≤ j

private theorem Good.mono {j j' : ℕ} (h : j ≤ j') {P : ℝ[X]} (hP : Good j P) : Good j' P :=
  ⟨hP.1, le_trans hP.2 h⟩

private theorem Good.zero (j : ℕ) : Good j 0 :=
  ⟨by simpa using (IntegralOn.const (δ := 1) (0 : ℤ)), by simp⟩

private theorem Good.const (j : ℕ) (m : ℤ) : Good j (Polynomial.C (m : ℝ)) :=
  ⟨IntegralOn.const (δ := 1) m, by rw [Polynomial.natDegree_C]; exact Nat.zero_le j⟩

private theorem Good.add {j : ℕ} {P Q : ℝ[X]} (hP : Good j P) (hQ : Good j Q) :
    Good j (P + Q) :=
  ⟨hP.1.add hQ.1, le_trans (natDegree_add_le P Q) (max_le hP.2 hQ.2)⟩

private theorem Good.sub {j : ℕ} {P Q : ℝ[X]} (hP : Good j P) (hQ : Good j Q) :
    Good j (P - Q) :=
  ⟨hP.1.sub hQ.1, le_trans (natDegree_sub_le P Q) (max_le hP.2 hQ.2)⟩

private theorem Good.const_mul {j : ℕ} {P : ℝ[X]} (m : ℤ) (hP : Good j P) :
    Good j (C (m : ℝ) * P) :=
  ⟨hP.1.const_mul m, le_trans (natDegree_C_mul_le _ _) hP.2⟩

private theorem Good.sum {ι : Type*} (s : Finset ι) (j : ℕ) (f : ι → ℝ[X])
    (h : ∀ i ∈ s, Good j (f i)) : Good j (∑ i ∈ s, f i) :=
  ⟨(IntVal.sum s f (fun i hi => (h i hi).1.toIntVal)).toIntegralOn,
    natDegree_finset_sum_le s f (fun i hi => (h i hi).2)⟩

end Helpers

private theorem decompose_binP (a b : ℕ) (hab : Nat.Coprime a b) :
    ∀ j : ℕ, ∀ i : ℕ, i ≤ j →
      ∃ R S : ℝ[X], Good j R ∧ Good j S ∧ binP i = dil (a : ℝ) R + dil (b : ℝ) S := by
  intro j
  induction j with
  | zero =>
      intro i hi
      obtain rfl : i = 0 := Nat.eq_zero_of_le_zero hi
      refine ⟨C 1, 0, by simpa using Good.const 0 (1 : ℤ), Good.zero 0, ?_⟩
      simp [binP_zero, dil]
  | succ j ih =>
      intro i hi
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · obtain ⟨R, S, hR, hS, hRS⟩ := ih i (Nat.lt_succ_iff.mp hlt)
        exact ⟨R, S, hR.mono (Nat.le_succ j), hS.mono (Nat.le_succ j), hRS⟩
      · have hi' : i = j + 1 := le_antisymm hi hge
        subst hi'
        have hAc : ((a ^ (j + 1) : ℤ) : ℝ) = (a : ℝ) ^ (j + 1) := by push_cast; ring
        have hBc : ((b ^ (j + 1) : ℤ) : ℝ) = (b : ℝ) ^ (j + 1) := by push_cast; ring
        have hAint : IntegralOn 1 (dil (a : ℝ) (binP (j + 1)) - C ((a : ℝ) ^ (j + 1)) * binP (j + 1)) := by
          have h1 : IntegralOn 1 (dil (a : ℝ) (binP (j + 1))) :=
            (IntVal.dil a (IntVal_binP (j + 1))).toIntegralOn
          have h2 : IntegralOn 1 (C ((a : ℝ) ^ (j + 1)) * binP (j + 1)) := by
            have h := IntegralOn.const_mul (IntVal_binP (j + 1)).toIntegralOn (a ^ (j + 1) : ℤ)
            simpa only [hAc] using h
          exact h1.sub h2
        have hBint : IntegralOn 1 (dil (b : ℝ) (binP (j + 1)) - C ((b : ℝ) ^ (j + 1)) * binP (j + 1)) := by
          have h1 : IntegralOn 1 (dil (b : ℝ) (binP (j + 1))) :=
            (IntVal.dil b (IntVal_binP (j + 1))).toIntegralOn
          have h2 : IntegralOn 1 (C ((b : ℝ) ^ (j + 1)) * binP (j + 1)) := by
            have h := IntegralOn.const_mul (IntVal_binP (j + 1)).toIntegralOn (b ^ (j + 1) : ℤ)
            simpa only [hBc] using h
          exact h1.sub h2
        have hAdeg : (dil (a : ℝ) (binP (j + 1)) - C ((a : ℝ) ^ (j + 1)) * binP (j + 1)).natDegree ≤ j := by
          have h := natDegree_dil_sub_C_pow_le (P := binP (j + 1)) (c := (a : ℝ)) (j := j + 1)
            (binP_natDegree_le (j + 1))
          simpa using h
        have hBdeg : (dil (b : ℝ) (binP (j + 1)) - C ((b : ℝ) ^ (j + 1)) * binP (j + 1)).natDegree ≤ j := by
          have h := natDegree_dil_sub_C_pow_le (P := binP (j + 1)) (c := (b : ℝ)) (j := j + 1)
            (binP_natDegree_le (j + 1))
          simpa using h
        obtain ⟨c, hc⟩ := newton_series j _ hAint hAdeg
        obtain ⟨d, hd⟩ := newton_series j _ hBint hBdeg
        have hdec : ∀ i : ℕ, ∃ p : ℝ[X] × ℝ[X],
            i ≤ j → Good j p.1 ∧ Good j p.2 ∧ binP i = dil (a : ℝ) p.1 + dil (b : ℝ) p.2 := by
          intro i
          by_cases hi : i ≤ j
          · obtain ⟨R, S, hR, hS, hRS⟩ := ih i hi
            exact ⟨(R, S), fun _ => ⟨hR, hS, hRS⟩⟩
          · exact ⟨0, fun h => absurd h hi⟩
        choose p hp using hdec
        let R' : ℝ[X] := ∑ i ∈ Finset.range (j + 1), C ((c i : ℝ)) * (p i).1
        let S' : ℝ[X] := ∑ i ∈ Finset.range (j + 1), C ((c i : ℝ)) * (p i).2
        let R'' : ℝ[X] := ∑ i ∈ Finset.range (j + 1), C ((d i : ℝ)) * (p i).1
        let S'' : ℝ[X] := ∑ i ∈ Finset.range (j + 1), C ((d i : ℝ)) * (p i).2
        have hR' : Good j R' :=
          Good.sum _ j _ (fun i hi => Good.const_mul (c i) (hp i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).1)
        have hS' : Good j S' :=
          Good.sum _ j _ (fun i hi => Good.const_mul (c i) (hp i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).2.1)
        have hR'' : Good j R'' :=
          Good.sum _ j _ (fun i hi => Good.const_mul (d i) (hp i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).1)
        have hS'' : Good j S'' :=
          Good.sum _ j _ (fun i hi => Good.const_mul (d i) (hp i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).2.1)
        have hA' : dil (a : ℝ) (binP (j + 1)) - C ((a : ℝ) ^ (j + 1)) * binP (j + 1) =
            dil (a : ℝ) R' + dil (b : ℝ) S' := by
          have hbinp : ∑ i ∈ Finset.range (j + 1), C ((c i : ℝ)) * binP i
              = ∑ i ∈ Finset.range (j + 1),
                  (dil (a : ℝ) (C ((c i : ℝ)) * (p i).1) + dil (b : ℝ) (C ((c i : ℝ)) * (p i).2)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [(hp i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).2.2, mul_add,
              ← dil_C_mul (a : ℝ) ((c i : ℝ)) (p i).1, ← dil_C_mul (b : ℝ) ((c i : ℝ)) (p i).2]
          rw [hc, hbinp, Finset.sum_add_distrib,
            ← dil_sum (a : ℝ) (Finset.range (j + 1)) (fun i => C ((c i : ℝ)) * (p i).1),
            ← dil_sum (b : ℝ) (Finset.range (j + 1)) (fun i => C ((c i : ℝ)) * (p i).2)]
        have hB' : dil (b : ℝ) (binP (j + 1)) - C ((b : ℝ) ^ (j + 1)) * binP (j + 1) =
            dil (a : ℝ) R'' + dil (b : ℝ) S'' := by
          have hbinp : ∑ i ∈ Finset.range (j + 1), C ((d i : ℝ)) * binP i
              = ∑ i ∈ Finset.range (j + 1),
                  (dil (a : ℝ) (C ((d i : ℝ)) * (p i).1) + dil (b : ℝ) (C ((d i : ℝ)) * (p i).2)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [(hp i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).2.2, mul_add,
              ← dil_C_mul (a : ℝ) ((d i : ℝ)) (p i).1, ← dil_C_mul (b : ℝ) ((d i : ℝ)) (p i).2]
          rw [hd, hbinp, Finset.sum_add_distrib,
            ← dil_sum (a : ℝ) (Finset.range (j + 1)) (fun i => C ((d i : ℝ)) * (p i).1),
            ← dil_sum (b : ℝ) (Finset.range (j + 1)) (fun i => C ((d i : ℝ)) * (p i).2)]
        obtain ⟨u, v, huv⟩ := (Nat.Coprime.isCoprime hab).pow (m := j + 1) (n := j + 1)
        have huvR : (u : ℝ) * (a : ℝ) ^ (j + 1) + (v : ℝ) * (b : ℝ) ^ (j + 1) = 1 := by
          have h := congrArg (fun z : ℤ => (z : ℝ)) huv
          push_cast at h
          simpa using h
        have huvP : C ((u : ℝ)) * C ((a : ℝ) ^ (j + 1)) + C ((v : ℝ)) * C ((b : ℝ) ^ (j + 1)) = (1 : ℝ[X]) := by
          rw [← C_mul, ← C_mul, ← C_add, huvR, C_1]
        refine ⟨C ((u : ℝ)) * binP (j + 1) - (C ((u : ℝ)) * R' + C ((v : ℝ)) * R''),
          C ((v : ℝ)) * binP (j + 1) - (C ((u : ℝ)) * S' + C ((v : ℝ)) * S''), ?_, ?_, ?_⟩
        · have h1 : Good (j + 1) (C ((u : ℝ)) * binP (j + 1)) :=
            Good.const_mul u ⟨(IntVal_binP (j + 1)).toIntegralOn, binP_natDegree_le (j + 1)⟩
          have h2 : Good j (C ((u : ℝ)) * R' + C ((v : ℝ)) * R'') :=
            (Good.const_mul u hR').add (Good.const_mul v hR'')
          exact h1.sub (h2.mono (Nat.le_succ j))
        · have h1 : Good (j + 1) (C ((v : ℝ)) * binP (j + 1)) :=
            Good.const_mul v ⟨(IntVal_binP (j + 1)).toIntegralOn, binP_natDegree_le (j + 1)⟩
          have h2 : Good j (C ((u : ℝ)) * S' + C ((v : ℝ)) * S'') :=
            (Good.const_mul u hS').add (Good.const_mul v hS'')
          exact h1.sub (h2.mono (Nat.le_succ j))
        · have hdila : dil (a : ℝ) (binP (j + 1)) =
              C ((a : ℝ) ^ (j + 1)) * binP (j + 1) + (dil (a : ℝ) R' + dil (b : ℝ) S') := by
            linear_combination hA'
          have hdilb : dil (b : ℝ) (binP (j + 1)) =
              C ((b : ℝ) ^ (j + 1)) * binP (j + 1) + (dil (a : ℝ) R'' + dil (b : ℝ) S'') := by
            linear_combination hB'
          have hsum : dil (a : ℝ) (C ((u : ℝ)) * binP (j + 1) - (C ((u : ℝ)) * R' + C ((v : ℝ)) * R''))
                + dil (b : ℝ) (C ((v : ℝ)) * binP (j + 1) - (C ((u : ℝ)) * S' + C ((v : ℝ)) * S''))
              = (C ((u : ℝ)) * C ((a : ℝ) ^ (j + 1)) + C ((v : ℝ)) * C ((b : ℝ) ^ (j + 1))) * binP (j + 1) := by
            simp only [dil_add, dil_sub, dil_C_mul]
            rw [hdila, hdilb]
            ring
          rw [hsum, huvP, one_mul]

theorem bezout_intValued (k : ℕ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (γ : Polynomial ℝ) (hγ : γ ∈ Polynomial.degreeLE ℝ (k : WithBot ℕ)) (hint : IntegralOn 1 γ) :
    ∃ γa γb : Polynomial ℝ, γa ∈ Polynomial.degreeLE ℝ (k : WithBot ℕ) ∧
      γb ∈ Polynomial.degreeLE ℝ (k : WithBot ℕ) ∧ IntegralOn (1 / (a : ℝ)) γa ∧
      IntegralOn (1 / (b : ℝ)) γb ∧ γ = γa + γb := by
  have hγdeg : γ.natDegree ≤ k := by
    rw [Polynomial.mem_degreeLE] at hγ
    exact natDegree_le_iff_degree_le.mpr hγ
  obtain ⟨c, hc⟩ := newton_series k γ hint hγdeg
  have hdec : ∀ i : ℕ, ∃ p : ℝ[X] × ℝ[X],
      i ≤ k → Good k p.1 ∧ Good k p.2 ∧ binP i = dil (a : ℝ) p.1 + dil (b : ℝ) p.2 := by
    intro i
    by_cases hi : i ≤ k
    · obtain ⟨R, S, hR, hS, hRS⟩ := decompose_binP a b hab k i hi
      exact ⟨(R, S), fun _ => ⟨hR, hS, hRS⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose p hp using hdec
  let Ra : ℝ[X] := ∑ i ∈ Finset.range (k + 1), C ((c i : ℝ)) * (p i).1
  let Rb : ℝ[X] := ∑ i ∈ Finset.range (k + 1), C ((c i : ℝ)) * (p i).2
  have hRa : Good k Ra :=
    Good.sum _ k _ (fun i hi => Good.const_mul (c i) (hp i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).1)
  have hRb : Good k Rb :=
    Good.sum _ k _ (fun i hi => Good.const_mul (c i) (hp i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).2.1)
  have hsum : γ = dil (a : ℝ) Ra + dil (b : ℝ) Rb := by
    have hbinp : ∑ i ∈ Finset.range (k + 1), C ((c i : ℝ)) * binP i
        = ∑ i ∈ Finset.range (k + 1),
            (dil (a : ℝ) (C ((c i : ℝ)) * (p i).1) + dil (b : ℝ) (C ((c i : ℝ)) * (p i).2)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(hp i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).2.2, mul_add,
        ← dil_C_mul (a : ℝ) ((c i : ℝ)) (p i).1, ← dil_C_mul (b : ℝ) ((c i : ℝ)) (p i).2]
    rw [hc, hbinp, Finset.sum_add_distrib,
      ← dil_sum (a : ℝ) (Finset.range (k + 1)) (fun i => C ((c i : ℝ)) * (p i).1),
      ← dil_sum (b : ℝ) (Finset.range (k + 1)) (fun i => C ((c i : ℝ)) * (p i).2)]
  refine ⟨dil (a : ℝ) Ra, dil (b : ℝ) Rb, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Polynomial.mem_degreeLE]
    exact natDegree_le_iff_degree_le.mp (le_trans (natDegree_dil_le _ _) hRa.2)
  · rw [Polynomial.mem_degreeLE]
    exact natDegree_le_iff_degree_le.mp (le_trans (natDegree_dil_le _ _) hRb.2)
  · have haR : (a : ℝ) ≠ 0 := by positivity
    intro n
    obtain ⟨m, hm⟩ := hRa.1 n
    refine ⟨m, ?_⟩
    rw [dil_eval]
    rw [show (a : ℝ) * ((1 / (a : ℝ)) * (n : ℝ)) = (n : ℝ) by
      rw [one_div, ← mul_assoc, mul_inv_cancel₀ haR, one_mul]]
    simpa using hm
  · have hbR : (b : ℝ) ≠ 0 := by positivity
    intro n
    obtain ⟨m, hm⟩ := hRb.1 n
    refine ⟨m, ?_⟩
    rw [dil_eval]
    rw [show (b : ℝ) * ((1 / (b : ℝ)) * (n : ℝ)) = (n : ℝ) by
      rw [one_div, ← mul_assoc, mul_inv_cancel₀ hbR, one_mul]]
    simpa using hm
  · exact hsum

end Work.BMF
