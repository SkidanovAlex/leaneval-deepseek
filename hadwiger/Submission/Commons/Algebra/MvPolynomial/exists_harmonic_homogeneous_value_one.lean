import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Commons.Algebra.MvPolynomial.lap_monomial_two

open MvPolynomial
open scoped BigOperators

namespace Commons.Algebra.MvPolynomial

noncomputable section

private abbrev P (n : ℕ) := MvPolynomial (Fin n) ℝ

private def alpha (k t : ℕ) : ℕ := (k - 2 * t) * (k - 2 * t - 1)
private def gamma (t : ℕ) : ℕ := (2 * t) * (2 * t - 1)

/-- coefficient sequence:  c 0 = 1,  c (t+1) = - c t * alpha k t / gamma (t+1) -/
private def ccoef (k : ℕ) : ℕ → ℝ
  | 0 => 1
  | t + 1 => -(ccoef k t) * ((alpha k t : ℕ) : ℝ) / (gamma (t + 1) : ℝ)

private lemma gamma_pos (t : ℕ) : 0 < gamma (t + 1) := by
  dsimp [gamma]
  have h1 : 0 < 2 * (t + 1) := by positivity
  have h2 : 0 < 2 * (t + 1) - 1 := by omega
  exact Nat.mul_pos h1 h2

private lemma ccoef_rec (k t : ℕ) :
    ccoef k (t + 1) * (gamma (t + 1) : ℝ) = - ccoef k t * (alpha k t : ℝ) := by
  have hg : (gamma (t + 1) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (gamma_pos t))
  simp only [ccoef]
  rw [div_mul_cancel₀ _ hg]

-- monomials
private def u (n : ℕ) (k t : ℕ) (e0 e1 : Fin n) : P n :=
  (MvPolynomial.X e0 ^ (k - 2 * t)) * (MvPolynomial.X e1 ^ (2 * t))

private def w (n : ℕ) (k t : ℕ) (e0 e1 : Fin n) : P n :=
  (MvPolynomial.X e0 ^ (k - 2 * t - 2)) * (MvPolynomial.X e1 ^ (2 * t))

private def v (n : ℕ) (k t : ℕ) (e0 e1 : Fin n) : P n :=
  (MvPolynomial.X e0 ^ (k - 2 * t)) * (MvPolynomial.X e1 ^ (2 * t - 2))

private def lapF (n : ℕ) (f : P n) : P n :=
  ∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i f)

private lemma lapF_add (n : ℕ) (f g : P n) : lapF n (f + g) = lapF n f + lapF n g := by
  unfold lapF
  simp only [map_add]
  rw [Finset.sum_add_distrib]

private lemma lapF_smul (n : ℕ) (a : ℝ) (f : P n) : lapF n (a • f) = a • lapF n f := by
  unfold lapF
  simp
  rw [← Finset.smul_sum]

private lemma lapF_sum_range (n : ℕ) (N : ℕ) (f : ℕ → P n) :
    lapF n (∑ t ∈ Finset.range N, f t) = ∑ t ∈ Finset.range N, lapF n (f t) := by
  induction N with
  | zero => simp [lapF]
  | succ N ih =>
      rw [Finset.sum_range_succ]
      rw [lapF_add]
      rw [ih]
      rw [Finset.sum_range_succ]

/-- lap of the basic monomial (two-variable) -/
private lemma lapF_u (n : ℕ) (e0 e1 : Fin n) (hne : e0 ≠ e1) (k t : ℕ) :
    lapF n (u n k t e0 e1) =
      ((alpha k t : ℕ) : ℝ) • w n k t e0 e1 + ((gamma t : ℕ) : ℝ) • v n k t e0 e1 := by
  simpa [lapF, u, w, v, alpha, gamma] using
    (lap_monomial_two (n := n) (a := k - 2 * t) (b := 2 * t) e0 e1 hne)

-- polynomial
private def Ph (n : ℕ) (e0 e1 : Fin n) (k : ℕ) : P n :=
  ∑ t ∈ Finset.range (k / 2 + 1), (ccoef k t) • u n k t e0 e1

private lemma two_mul_le_of_le_div_two {k t : ℕ} (ht : t ≤ k / 2) : 2 * t ≤ k := by
  calc 2 * t ≤ 2 * (k / 2) := Nat.mul_le_mul_left 2 ht
       _ ≤ k := by
         rw [mul_comm]
         exact Nat.div_mul_le_self k 2

private lemma sub_two_mul_add {k t : ℕ} (ht : 2 * t ≤ k) : (k - 2 * t) + 2 * t = k :=
  Nat.sub_add_cancel ht

/-- homogeneous degree k of the monomial u -/
private lemma u_mem (n : ℕ) (e0 e1 : Fin n) (k : ℕ) {t : ℕ} (ht : t ≤ k / 2) :
    u n k t e0 e1 ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k := by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  have h2t : 2 * t ≤ k := two_mul_le_of_le_div_two ht
  have hX0 : ((MvPolynomial.X e0 : P n) ^ (k - 2 * t)).IsHomogeneous (k - 2 * t) :=
    MvPolynomial.isHomogeneous_X_pow (R := ℝ) e0 (k - 2 * t)
  have hX1 : ((MvPolynomial.X e1 : P n) ^ (2 * t)).IsHomogeneous (2 * t) :=
    MvPolynomial.isHomogeneous_X_pow (R := ℝ) e1 (2 * t)
  have hm : (((MvPolynomial.X e0 : P n) ^ (k - 2 * t)) * ((MvPolynomial.X e1 : P n) ^ (2 * t))).IsHomogeneous ((k - 2 * t) + 2 * t) := hX0.mul hX1
  simpa [u, sub_two_mul_add h2t] using hm

private lemma Ph_mem_homogeneous (n : ℕ) (e0 e1 : Fin n) (k : ℕ) :
    Ph n e0 e1 k ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k := by
  unfold Ph
  refine (MvPolynomial.homogeneousSubmodule (Fin n) ℝ k).sum_mem ?_
  intro t ht
  exact (MvPolynomial.homogeneousSubmodule (Fin n) ℝ k).smul_mem _ (u_mem n e0 e1 k (Nat.le_of_lt_succ (Finset.mem_range.mp ht)))


private lemma alpha_top_zero (k : ℕ) : alpha k (k / 2) = 0 := by
  dsimp [alpha]
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · have h1 := Nat.mod_add_div k 2
    rw [h, zero_add] at h1
    rw [← h1]
    simp
  · have h1 := Nat.mod_add_div k 2
    rw [h] at h1
    have hsub : k - 2 * (k / 2) = 1 := by omega
    rw [hsub]

private lemma gamma_zero : gamma 0 = 0 := by
  norm_num [gamma]

/-- v (t+1) is the same monomial as w t -/
private lemma v_succ_eq_w (n : ℕ) (e0 e1 : Fin n) (k t : ℕ) :
    v n k (t + 1) e0 e1 = w n k t e0 e1 := by
  unfold v w
  rw [show 2 * (t + 1) - 2 = 2 * t by omega]
  rw [show k - 2 * (t + 1) = k - 2 * t - 2 by omega]

/-- Laplacian of the whole sum vanishes -/
private lemma lapF_Ph_zero (n : ℕ) (e0 e1 : Fin n) (hne : e0 ≠ e1) (k : ℕ) :
    lapF n (Ph n e0 e1 k) = 0 := by
  classical
  let K : ℕ := k / 2
  -- step 1: push lapF into the sum
  have h1 : lapF n (Ph n e0 e1 k) =
      ∑ t ∈ Finset.range (K + 1), (ccoef k t) • (lapF n (u n k t e0 e1)) := by
    unfold Ph
    simp only [K]
    rw [lapF_sum_range]
    apply Finset.sum_congr rfl
    intro t ht
    exact lapF_smul n (ccoef k t) (u n k t e0 e1)
  -- step 2: expand each lapF u, then distribute scalar and split the sum
  have h2 : lapF n (Ph n e0 e1 k) =
      (∑ t ∈ Finset.range (K + 1), (ccoef k t * (alpha k t : ℝ)) • w n k t e0 e1) +
      (∑ t ∈ Finset.range (K + 1), (ccoef k t * (gamma t : ℝ)) • v n k t e0 e1) := by
    rw [h1]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    rw [lapF_u n e0 e1 hne k t]
    simp only [smul_add, smul_smul]
  -- definitions of the pieces
  let A1 : P n := ∑ t ∈ Finset.range K, (ccoef k t * (alpha k t : ℝ)) • w n k t e0 e1
  let A2 : P n := ∑ t ∈ Finset.range K,
      (ccoef k (t + 1) * (gamma (t + 1) : ℝ)) • v n k (t + 1) e0 e1
  let fK : P n := (ccoef k K * (alpha k K : ℝ)) • w n k K e0 e1
  let g0 : P n := (ccoef k 0 * (gamma 0 : ℝ)) • v n k 0 e0 e1
  have hS1 : (∑ t ∈ Finset.range (K + 1), (ccoef k t * (alpha k t : ℝ)) • w n k t e0 e1) =
      A1 + fK := by
    rw [Finset.sum_range_succ]
  have hS2 : (∑ t ∈ Finset.range (K + 1), (ccoef k t * (gamma t : ℝ)) • v n k t e0 e1) =
      A2 + g0 := by
    rw [Finset.sum_range_succ']
  have h2' : lapF n (Ph n e0 e1 k) = (A1 + fK) + (A2 + g0) := by
    rw [h2, hS1, hS2]
  -- pairing A1 + A2 vanishes
  have hz : ∀ t : ℕ,
      ccoef k t * (alpha k t : ℝ) + ccoef k (t + 1) * (gamma (t + 1) : ℝ) = 0 := by
    intro t
    have hr := ccoef_rec k t
    calc
      ccoef k t * (alpha k t : ℝ) + ccoef k (t + 1) * (gamma (t + 1) : ℝ)
          = ccoef k t * (alpha k t : ℝ) + (-(ccoef k t) * (alpha k t : ℝ)) := by rw [hr]
      _ = 0 := by ring
  have hA12 : A1 + A2 = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro t ht
    rw [v_succ_eq_w n e0 e1 k t]
    rw [← add_smul]
    rw [hz t]
    simp
  have hfK : fK = 0 := by
    have hα : (alpha k K : ℝ) = 0 := by
      dsimp [K]
      exact_mod_cast (alpha_top_zero k)
    dsimp [fK]
    rw [hα]
    simp
  have hg0 : g0 = 0 := by
    have hγ : (gamma 0 : ℝ) = 0 := by exact_mod_cast gamma_zero
    dsimp [g0]
    rw [hγ]
    simp
  rw [h2']
  have hAC : (A1 + fK) + (A2 + g0) = (A1 + A2) + (fK + g0) := by
    ac_rfl
  rw [hAC, hA12, hfK, hg0]
  simp

/-- evaluation of the whole polynomial -/
private lemma eval_Ph (n : ℕ) (e0 e1 : Fin n) (x : Fin n → ℝ) (k : ℕ) :
    MvPolynomial.eval x (Ph n e0 e1 k) =
      ∑ t ∈ Finset.range (k / 2 + 1), (ccoef k t) * (x e0 ^ (k - 2 * t)) * (x e1 ^ (2 * t)) := by
  calc
    MvPolynomial.eval x (Ph n e0 e1 k)
        = ∑ t ∈ Finset.range (k / 2 + 1), (ccoef k t) * MvPolynomial.eval x (u n k t e0 e1) := by
            unfold Ph
            simp [u, MvPolynomial.smul_eval]
    _ = ∑ t ∈ Finset.range (k / 2 + 1),
          (ccoef k t) * (x e0 ^ (k - 2 * t)) * (x e1 ^ (2 * t)) := by
            apply Finset.sum_congr rfl
            intro t ht
            simp [u, mul_assoc]

/-- eval at the first basis vector is 1 -/
private lemma eval_Ph_one (n : ℕ) [NeZero n] (k : ℕ) (e0 e1 : Fin n)
    (he0 : e0 = (0 : Fin n)) (he1 : e1 ≠ (0 : Fin n)) :
    MvPolynomial.eval (fun i : Fin n => (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) i)
      (Ph n e0 e1 k) = 1 := by
  classical
  let x : Fin n → ℝ := fun i => (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) i
  have hx0 : x e0 = 1 := by
    dsimp [x]
    rw [he0]
    simp
  have hx1 : x e1 = 0 := by
    dsimp [x]
    simp [he1]
  rw [eval_Ph n e0 e1 x k]
  rw [hx0, hx1]
  -- sum: only the t = 0 term survives, and c 0 = 1
  have hmain : (∑ t ∈ Finset.range (k / 2 + 1),
      (ccoef k t) * (1 ^ (k - 2 * t)) * (0 ^ (2 * t))) =
      (ccoef k 0) * (1 ^ (k - 2 * 0)) * (0 ^ (2 * 0)) := by
    refine Finset.sum_eq_single 0 ?_ ?_
    · intro t ht hne
      have htpos : 0 < t := by
        by_contra hle
        have ht0 : t = 0 := by omega
        exact hne ht0
      have h2t : 2 * t ≠ 0 := by omega
      rw [zero_pow h2t]
      ring
    · intro h0not
      exact (h0not (Finset.mem_range.mpr (by omega : 0 < k / 2 + 1))).elim
  rw [hmain]
  simp [ccoef]

theorem exists_harmonic_homogeneous_value_one
    {n : ℕ} {k : ℕ} [NeZero n] (hn2 : 2 ≤ n) :
    ∃ P : MvPolynomial (Fin n) ℝ,
      P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k ∧
      (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) = 0 ∧
      MvPolynomial.eval (fun i : Fin n =>
        (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) i) P = 1 := by
  let e0 : Fin n := (0 : Fin n)
  let e1 : Fin n := ⟨1, Nat.lt_of_lt_of_le (by norm_num : 1 < 2) hn2⟩
  have hne : e0 ≠ e1 := by
    intro h
    have hv : (0 : ℕ) = 1 := by
      simpa [e0, e1] using congrArg Fin.val h
    omega
  refine ⟨Ph n e0 e1 k, ?_, ?_, ?_⟩
  · exact Ph_mem_homogeneous n e0 e1 k
  · simpa [lapF] using (lapF_Ph_zero n e0 e1 hne k)
  · exact eval_Ph_one n k e0 e1 (by rfl)
      (by intro h1; exact hne (by simpa [e0] using h1.symm))
