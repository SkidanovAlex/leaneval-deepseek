import Mathlib
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_root_weightSpace_finrank_eq_one
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_W_eq_bot_of_not_cone
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_weightSpace_descent

set_option maxRecDepth 200000
set_option linter.unusedVariables false

namespace Commons.Algebra.Lie.SerreConstruction

open CartanMatrix

private def e8inv : Matrix (Fin 8) (Fin 8) ℤ :=
  !![4,5,7,10,8,6,4,2; 5,8,10,15,12,9,6,3; 7,10,14,20,16,12,8,4;
     10,15,20,30,24,18,12,6; 8,12,16,24,20,15,10,5; 6,9,12,18,15,12,8,4;
     4,6,8,12,10,8,6,3; 2,3,4,6,5,4,3,2]

private lemma e8inv_mul_E8 : e8inv * CartanMatrix.E₈ = 1 := by decide
private lemma E8_mul_e8inv : CartanMatrix.E₈ * e8inv = 1 := by decide

private def cvec (μ : Fin 8 → ℤ) : Fin 8 → ℤ := Matrix.mulVec e8inv μ

private lemma E8_mulVec_cvec (μ : Fin 8 → ℤ) : Matrix.mulVec CartanMatrix.E₈ (cvec μ) = μ := by
  rw [cvec, Matrix.mulVec_mulVec, E8_mul_e8inv, Matrix.one_mulVec]

private lemma cvec_mulVec_E8 (n : Fin 8 → ℤ) : cvec (Matrix.mulVec CartanMatrix.E₈ n) = n := by
  rw [cvec, Matrix.mulVec_mulVec, e8inv_mul_E8, Matrix.one_mulVec]

private lemma cvec_neg (μ : Fin 8 → ℤ) : cvec (-μ) = -cvec μ := by
  rw [cvec, cvec, Matrix.mulVec_neg]

private lemma WtSum_eq_mulVec_cast (m : Fin 8 → ℤ) (j : Fin 8) :
    WtSum m j = ((Matrix.mulVec CartanMatrix.E₈ m) j : ℂ) := by
  simp only [WtSum, alpha, Matrix.mulVec, dotProduct]
  rw [Int.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show CartanMatrix.E₈ i j = CartanMatrix.E₈ j i from E8_symm i j]
  push_cast
  ring

private lemma NWtSum_cast_eq (n : Fin 8 → ℕ) (j : Fin 8) :
    NWtSum n j = ((Matrix.mulVec CartanMatrix.E₈ (fun i => (n i : ℤ))) j : ℂ) := by
  simp only [NWtSum]
  exact WtSum_eq_mulVec_cast (fun i => (n i : ℤ)) j

private lemma eq_mulVec_of_eq_NWtSum {μ : Fin 8 → ℤ} {n : Fin 8 → ℕ}
    (hn : NWtSum n = fun i => (μ i : ℂ)) :
    μ = Matrix.mulVec CartanMatrix.E₈ (fun i => (n i : ℤ)) := by
  funext j
  apply Int.cast_injective (α := ℂ)
  rw [← NWtSum_cast_eq n j]
  exact (congrFun hn j).symm

private lemma eq_neg_mulVec_of_eq_neg_NWtSum {μ : Fin 8 → ℤ} {n : Fin 8 → ℕ}
    (hn : -(NWtSum n) = fun i => (μ i : ℂ)) :
    μ = -(Matrix.mulVec CartanMatrix.E₈ (fun i => (n i : ℤ))) := by
  funext j
  apply Int.cast_injective (α := ℂ)
  have h3 : -(NWtSum n j) = (μ j : ℂ) := by
    have := congrFun hn j
    simpa using this
  rw [← h3]
  simp only [Pi.neg_apply, Int.cast_neg, NWtSum_cast_eq]

private lemma wtSpace_eq_bot_of_cvec_mixed (μ : Fin 8 → ℤ) (h0 : μ ≠ 0)
    (hneg : ∃ i, cvec μ i < 0) (hpos : ∃ i, 0 < cvec μ i) : wtSpace μ = ⊥ := by
  rw [show wtSpace μ = W (fun i => (μ i : ℂ)) from rfl]
  refine e8_W_eq_bot_of_not_cone ?_ ?_ ?_
  · intro h
    apply h0
    funext i
    have h2 := congrFun h i
    simp only [Pi.zero_apply] at h2
    exact_mod_cast h2
  · rintro n hn
    obtain ⟨i, hi⟩ := hneg
    have hμ := eq_mulVec_of_eq_NWtSum hn
    rw [hμ, cvec_mulVec_E8] at hi
    exact absurd hi (by omega)
  · rintro n hn
    obtain ⟨i, hi⟩ := hpos
    have hμ := eq_neg_mulVec_of_eq_neg_NWtSum hn
    rw [hμ, cvec_neg, cvec_mulVec_E8] at hi
    simp only [Pi.neg_apply] at hi
    omega

private lemma wtSpace_reflect_ne_bot (i : Fin 8) (μ : Fin 8 → ℤ) (h : wtSpace μ ≠ ⊥) :
    wtSpace (wtReflect i μ) ≠ ⊥ := by
  have h' : W (fun i => (μ i : ℂ)) ≠ ⊥ := h
  have hν : (fun j => ((wtReflect i μ j : ℤ) : ℂ)) = sMu i (fun j => (μ j : ℂ)) := by
    funext j; simp only [wtReflect, sMu]; push_cast; ring
  rw [show wtSpace (wtReflect i μ) = W (fun j => ((wtReflect i μ j : ℤ) : ℂ)) from rfl, hν]
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff (W (fun i => (μ i : ℂ)))).mp h'
  have hx' : reflAut i x ∈ W (sMu i (fun j => (μ j : ℂ))) :=
    maps_W i (reflAut i) (reflAut_H i) hx
  have hne : reflAut i x ≠ 0 := by
    intro h0
    have h2 : (reflAut i).symm ((reflAut i) x) = (reflAut i).symm (0 : L8) := congrArg _ h0
    rw [LieEquiv.symm_apply_apply, map_zero] at h2
    exact hx0 h2
  exact (Submodule.ne_bot_iff _).mpr ⟨reflAut i x, hx', hne⟩

private lemma wtSpace_foldl_ne_bot (L : List (Fin 8)) (μ : Fin 8 → ℤ) (h : wtSpace μ ≠ ⊥) :
    wtSpace (L.foldl (fun v i => wtReflect i v) μ) ≠ ⊥ := by
  induction L generalizing μ with
  | nil => simpa using h
  | cons i L ih => exact ih _ (wtSpace_reflect_ne_bot i μ h)

/-- The indicator vector of a finset, as an integral weight. -/
private def ind (S : Finset (Fin 8)) : Fin 8 → ℤ := fun i => if i ∈ S then 1 else 0

/-- Apply a list of simple reflections to a weight. -/
private def applyS (L : List (Fin 8)) (μ : Fin 8 → ℤ) : Fin 8 → ℤ :=
  L.foldl (fun v i => wtReflect i v) μ

private abbrev Mixed (m : Fin 8 → ℤ) : Prop := (∃ i, 0 < m i) ∧ (∃ i, m i < 0)

private def cox : List (Fin 8) := [7,6,5,4,3,1,2,0]
private def coxR : List (Fin 8) := [0,2,1,3,4,5,6,7]

private abbrev disj (S : Finset (Fin 8)) : Prop :=
    (Mixed (cvec (applyS (coxR ++ coxR ++ coxR ++ coxR ++ coxR ++ coxR ++ coxR) (ind S)))
     ∨ Mixed (cvec (applyS (cox ++ cox ++ cox ++ cox ++ cox ++ cox) (ind S)))
     ∨ Mixed (cvec (applyS (coxR ++ coxR ++ coxR ++ coxR ++ coxR ++ coxR) (ind S))))

set_option maxHeartbeats 10000000 in
private lemma disj_all : ∀ S : Finset (Fin 8), S.Nonempty →
    S ≠ ({(7 : Fin 8)} : Finset (Fin 8)) → disj S := by decide

private lemma eq_theta_of_01 (ν : Fin 8 → ℤ) (h01 : ∀ i, ν i = 0 ∨ ν i = 1) (hν : ν ≠ 0)
    (h : wtSpace ν ≠ ⊥) : ν = fun i => if i = 7 then 1 else 0 := by
  set S : Finset (Fin 8) := Finset.univ.filter (fun i => ν i = 1) with hS
  have hνS : ν = ind S := by
    funext i
    have hi : ind S i = if ν i = 1 then 1 else 0 := by
      simp only [ind, hS, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hi]
    rcases h01 i with h0 | h1
    · rw [if_neg (by omega), h0]
    · rw [if_pos h1]; exact h1
  by_cases h7 : S = {(7 : Fin 8)}
  · rw [hνS, h7]
    funext i
    simp [ind, Finset.mem_singleton]
  · have hne : S.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      apply hν
      rw [hνS, hempty]
      funext i
      simp [ind]
    have hd := disj_all S hne h7
    have key : ∀ L : List (Fin 8), Mixed (cvec (applyS L (ind S))) → False := by
      intro L hL
      have hμ : wtSpace (applyS L (ind S)) ≠ ⊥ := by
        rw [← hνS]
        exact wtSpace_foldl_ne_bot L ν h
      have h0 : applyS L (ind S) ≠ 0 := by
        intro hz
        rw [hz] at hL
        obtain ⟨⟨i, hi⟩, _⟩ := hL
        have hz' : cvec (0 : Fin 8 → ℤ) i = 0 := by rw [cvec, Matrix.mulVec_zero]; rfl
        omega
      exact hμ (wtSpace_eq_bot_of_cvec_mixed _ h0 hL.2 hL.1)
    rcases hd with h1 | h2 | h3
    · exact (key _ h1).elim
    · exact (key _ h2).elim
    · exact (key _ h3).elim

/-- The column sums of `A⁻¹` (equivalently `A⁻¹ · 1`). -/
private def e8c : Fin 8 → ℤ := ![46,68,91,135,110,84,57,29]

/-- The height `∑ᵢ cᵢνᵢ` of a weight. -/
private def ht (ν : Fin 8 → ℤ) : ℤ := ∑ i, e8c i * ν i

private lemma e8c_dot_all : ∀ i : Fin 8, ∑ j, e8c j * CartanMatrix.E₈ i j = 1 := by decide

private lemma E8_diag_i : ∀ i : Fin 8, CartanMatrix.E₈ i i = 2 := by decide

private lemma E8_offdiag_nonpos (i k : Fin 8) (h : i ≠ k) : CartanMatrix.E₈ i k ≤ 0 := by
  fin_cases i <;> fin_cases k <;> simp_all [CartanMatrix.E₈, CartanMatrix.E_eight_eq]

private lemma ht_descent (ν : Fin 8 → ℤ) (i : Fin 8) :
    ht (ν - fun j => CartanMatrix.E₈ i j) = ht ν - 1 := by
  simp only [ht, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [e8c_dot_all i]

private lemma ht_pos {ν : Fin 8 → ℤ} (hdom : ∀ i, 0 ≤ ν i) (hν : ν ≠ 0) : 0 < ht ν := by
  obtain ⟨i, hi⟩ : ∃ i, 0 < ν i := by
    by_contra hc
    simp only [not_exists, not_lt] at hc
    exact hν (funext fun i => le_antisymm (hc i) (hdom i))
  have h1 : e8c i * ν i ≤ ht ν := by
    rw [ht]
    refine Finset.single_le_sum (f := fun j => e8c j * ν j) (fun j _ => ?_) (Finset.mem_univ i)
    have : (0:ℤ) ≤ e8c j := by fin_cases j <;> decide
    exact mul_nonneg this (hdom j)
  have h2 : (1:ℤ) ≤ e8c i * ν i := by
    have hc : (1:ℤ) ≤ e8c i := by fin_cases i <;> decide
    nlinarith [hi, hdom i]
  omega

private lemma exists_neg_E8 (i : Fin 8) : ∃ k, CartanMatrix.E₈ i k = -1 := by
  fin_cases i <;> decide

private lemma not_dom_simple (i : Fin 8) : ¬ (∀ k, 0 ≤ (fun j => CartanMatrix.E₈ i j) k) := by
  intro h
  obtain ⟨k, hk⟩ := exists_neg_E8 i
  have h1 := h k
  simp only at h1
  rw [hk] at h1
  omega

private lemma not_dom_theta_add (i : Fin 8) :
    ¬ (∀ k, 0 ≤ (if k = 7 then (1:ℤ) else 0) + CartanMatrix.E₈ i k) := by
  fin_cases i <;> decide

theorem e8_dominant_weight_eq_zero_or_theta (ν : Fin 8 → ℤ) (hν : ν ≠ 0)
    (hdom : ∀ i, 0 ≤ ν i) (h : Commons.Algebra.Lie.SerreConstruction.wtSpace ν ≠ ⊥) :
    ν = fun i => if i = 7 then 1 else 0 := by
  suffices key : ∀ N : ℕ, ∀ ν : Fin 8 → ℤ, (∀ i, 0 ≤ ν i) → ν ≠ 0 → wtSpace ν ≠ ⊥ →
      (ht ν).toNat = N → ν = fun i => if i = 7 then 1 else 0 from
    key (ht ν).toNat ν hdom hν h rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro ν hdom hν h hN
    by_cases hbig : ∃ i, 2 ≤ ν i
    · obtain ⟨i, hi⟩ := hbig
      have hdesc : wtSpace (ν - fun j => CartanMatrix.E₈ i j) ≠ ⊥ :=
        e8_weightSpace_descent ν i (by omega) h
      have hdom' : ∀ k, 0 ≤ (ν - fun j => CartanMatrix.E₈ i j) k := by
        intro k
        simp only [Pi.sub_apply]
        rcases eq_or_ne k i with hki | hk
        · rw [hki, E8_diag_i i]; omega
        · have hA : CartanMatrix.E₈ i k ≤ 0 := E8_offdiag_nonpos i k (Ne.symm hk)
          have hk0 : 0 ≤ ν k := hdom k
          omega
      have hne' : (ν - fun j => CartanMatrix.E₈ i j) ≠ 0 := by
        intro hz
        have hνeq : ν = fun j => CartanMatrix.E₈ i j := sub_eq_zero.mp hz
        exact not_dom_simple i (fun k => hνeq ▸ hdom k)
      have hlt : (ht (ν - fun j => CartanMatrix.E₈ i j)).toNat < N := by
        rw [ht_descent, ← hN]
        have hp := ht_pos hdom hν
        exact Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.int_toNat_lt (by omega) (by omega)
      have hres := ih _ hlt _ hdom' hne' hdesc rfl
      have hνeq : ν = fun k => (if k = 7 then (1:ℤ) else 0) + CartanMatrix.E₈ i k := by
        funext k
        have h2 := congrFun hres k
        simp only [Pi.sub_apply] at h2
        linarith
      apply absurd _ (not_dom_theta_add i)
      intro k
      have hk := hdom k
      rw [hνeq] at hk
      simpa using hk
    · simp only [not_exists, not_le] at hbig
      exact eq_theta_of_01 ν (fun i => by have := hdom i; have := hbig i; omega) hν h


end Commons.Algebra.Lie.SerreConstruction
