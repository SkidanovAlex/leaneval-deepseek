import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Submission.Commons.Algebra.MvPolynomial.lap_mem_homogeneousSubmodule
import Submission.Commons.Algebra.MvPolynomial.pderiv_mem_homogeneousSubmodule

open MvPolynomial
open scoped BigOperators

namespace Commons.Algebra.MvPolynomial

section lap_helpers

variable {n : ℕ}

private abbrev P (n : ℕ) := MvPolynomial (Fin n) ℝ

-- ============================================================
-- Level 1 : lap, Euler, r2, basic identities
-- ============================================================

private noncomputable def lapLinear : P n →ₗ[ℝ] P n :=
  ∑ i : Fin n, ((pderiv (R := ℝ) i : P n →ₗ[ℝ] P n).comp
                (pderiv (R := ℝ) i : P n →ₗ[ℝ] P n))

private noncomputable def lap (u : P n) : P n :=
  ∑ i : Fin n, pderiv (R := ℝ) i (pderiv (R := ℝ) i u)

private lemma lapLinear_apply (u : P n) : lapLinear u = lap u := by
  simp [lapLinear, lap]

private lemma lap_add (f g : P n) : lap (f + g) = lap f + lap g := by
  unfold lap
  simp only [map_add]
  rw [Finset.sum_add_distrib]

private lemma lap_smul (a : ℝ) (f : P n) : lap (a • f) = a • lap f := by
  unfold lap
  simp
  rw [← Finset.smul_sum]

private lemma lap_sum_range (N : ℕ) (f : ℕ → P n) :
    lap (∑ r ∈ Finset.range N, f r) = ∑ r ∈ Finset.range N, lap (f r) := by
  induction N with
  | zero =>
      rw [Finset.sum_range_zero]
      unfold lap
      simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      rw [lap_add]
      rw [ih]
      rw [← Finset.sum_range_succ]

private noncomputable def Euler (f : P n) : P n :=
  ∑ i : Fin n, X i * pderiv (R := ℝ) i f

private noncomputable def r2 : P n := ∑ j : Fin n, (X j)^2

private lemma Euler_homogeneous_smul (g : P n) {d : ℕ} (hg : g.IsHomogeneous d) :
    Euler g = (d : ℝ) • g := by
  have h := hg.sum_X_mul_pderiv
  unfold Euler
  rw [← Nat.cast_smul_eq_nsmul ℝ d g] at h
  exact h

private lemma r2_IsHomogeneous : (r2 : P n).IsHomogeneous 2 := by
  unfold r2
  apply MvPolynomial.IsHomogeneous.sum
  intro j hj
  simpa using (MvPolynomial.isHomogeneous_X (R := ℝ) (σ := Fin n) j).pow 2

private lemma pderiv_r2 (i : Fin n) : pderiv (R := ℝ) i r2 = (2 : ℝ) • (X i : P n) := by
  unfold r2
  classical
  rw [map_sum]
  rw [Finset.sum_eq_single i]
  · rw [pow_two, MvPolynomial.pderiv_mul]
    simp only [pderiv_X_self, mul_one, one_mul]
    rw [← two_smul ℝ]
  · intro j _ hj
    rw [pow_two, MvPolynomial.pderiv_mul]
    simp [hj]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private lemma lap_r2 : lap (r2 : P n) = (2 * (n : ℝ)) • (1 : P n) := by
  calc
    lap r2 = ∑ i : Fin n, pderiv (R := ℝ) i ((2 : ℝ) • (X i : P n)) := by
      unfold lap
      simp_rw [pderiv_r2]
    _ = ∑ i : Fin n, (2 : ℝ) • pderiv (R := ℝ) i (X i : P n) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp
    _ = ∑ i : Fin n, (2 : ℝ) • (1 : P n) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [MvPolynomial.pderiv_X_self]
    _ = (2 * (n : ℝ)) • (1 : P n) := by
      rw [← Finset.smul_sum]
      rw [Finset.sum_const]
      change (2 : ℝ) • (Fintype.card (Fin n) • (1 : P n)) = (2 * (n : ℝ)) • (1 : P n)
      rw [Fintype.card_fin]
      rw [← Nat.cast_smul_eq_nsmul ℝ n (1 : P n)]
      rw [← mul_smul]

private lemma pderiv2_mul (i : Fin n) (f g : P n) :
    pderiv (R := ℝ) i (pderiv (R := ℝ) i (f * g)) =
      pderiv (R := ℝ) i (pderiv (R := ℝ) i f) * g
        + (2 : ℝ) • (pderiv (R := ℝ) i f * pderiv (R := ℝ) i g)
        + f * pderiv (R := ℝ) i (pderiv (R := ℝ) i g) := by
  rw [MvPolynomial.pderiv_mul]
  rw [map_add]
  rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul]
  rw [two_smul ℝ (pderiv (R := ℝ) i f * pderiv (R := ℝ) i g)]
  ring

private lemma lap_mul (f g : P n) :
    lap (f * g) =
      lap f * g + (2 : ℝ) • (∑ i : Fin n, pderiv (R := ℝ) i f * pderiv (R := ℝ) i g)
        + f * lap g := by
  unfold lap
  trans ∑ i : Fin n,
    (pderiv (R := ℝ) i (pderiv (R := ℝ) i f) * g
      + (2 : ℝ) • (pderiv (R := ℝ) i f * pderiv (R := ℝ) i g)
      + f * pderiv (R := ℝ) i (pderiv (R := ℝ) i g))
  · apply Finset.sum_congr rfl
    intro i hi
    exact pderiv2_mul i f g
  · rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, ← Finset.smul_sum, ← Finset.mul_sum]

private lemma lap_r2_mul (g : P n) :
    lap (r2 * g) = r2 * lap g + (4 : ℝ) • Euler g + (2 * (n : ℝ)) • g := by
  have hcross : (2 : ℝ) •
      (∑ i : Fin n, pderiv (R := ℝ) i r2 * pderiv (R := ℝ) i g) = (4 : ℝ) • Euler g := by
    have hsum : (∑ i : Fin n, pderiv (R := ℝ) i r2 * pderiv (R := ℝ) i g)
        = (2 : ℝ) • Euler g := by
      unfold Euler
      simp_rw [pderiv_r2]
      calc
        (∑ i : Fin n, ((2 : ℝ) • X i) * pderiv (R := ℝ) i g)
            = (∑ i : Fin n, (2 : ℝ) • (X i * pderiv (R := ℝ) i g)) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [smul_mul_assoc]
        _ = (2 : ℝ) • (∑ i : Fin n, X i * pderiv (R := ℝ) i g) := by
              rw [← Finset.smul_sum]
    calc
      (2 : ℝ) • (∑ i : Fin n, pderiv (R := ℝ) i r2 * pderiv (R := ℝ) i g)
          = (2 : ℝ) • ((2 : ℝ) • Euler g) := by rw [hsum]
      _ = (4 : ℝ) • Euler g := by norm_num [smul_smul]
  calc
    lap (r2 * g) = lap r2 * g
        + (2 : ℝ) • (∑ i : Fin n, pderiv (R := ℝ) i r2 * pderiv (R := ℝ) i g)
        + r2 * lap g := lap_mul r2 g
    _ = ((2 * (n : ℝ)) • (1 : P n)) * g + (4 : ℝ) • Euler g + r2 * lap g := by
      rw [lap_r2, hcross]
    _ = r2 * lap g + (4 : ℝ) • Euler g + (2 * (n : ℝ)) • g := by
      rw [smul_mul_assoc]
      simp [add_comm, add_left_comm, add_assoc]

-- ============================================================
-- Level 2 : lap (r2^j * g) for homogeneous g
-- ============================================================

private lemma lap_r2pow_hom (j : ℕ) (hj : 1 ≤ j) {g : P n} {d : ℕ} (hg : g.IsHomogeneous d) :
    lap (r2 ^ j * g) = r2 ^ j * lap g +
      ((j : ℝ) * (4 * (d : ℝ) + 4 * (j : ℝ) + 2 * (n : ℝ) - 4)) •
        (r2 ^ (j - 1) * g) := by
  induction j with
  | zero => omega
  | succ j ih =>
      by_cases h0 : j = 0
      · subst j
        have hm := lap_r2_mul (n := n) g
        have hE0 := Euler_homogeneous_smul (n := n) g hg
        rw [show r2 ^ (0 + 1) * g = r2 * g by norm_num]
        rw [hm, hE0]
        rw [smul_smul]
        rw [add_assoc, ← add_smul]
        rw [show r2 ^ (0 + 1) * lap g = r2 * lap g by norm_num]
        rw [show r2 ^ (0 + 1 - 1) * g = g by norm_num]
        have hcoef : (4 * (d : ℝ) + 2 * (n : ℝ)) =
            ((0 + 1 : ℕ) : ℝ) * (4 * (d : ℝ) + 4 * ((0 + 1 : ℕ) : ℝ)
              + 2 * (n : ℝ) - 4) := by
          norm_num
          ring
        rw [← hcoef]
      · have hj1 : 1 ≤ j := by omega
        have ihj := ih hj1
        have hpow : r2 ^ (j + 1) * g = r2 * (r2 ^ j * g) := by
          rw [pow_succ', mul_assoc]
        rw [hpow]
        have hb := lap_r2_mul (n := n) (r2 ^ j * g)
        rw [hb]
        have hhom : (r2 ^ j * g).IsHomogeneous (2 * j + d) := by
          exact (r2_IsHomogeneous).pow j |>.mul hg
        have hE1 := Euler_homogeneous_smul (n := n) (r2 ^ j * g) hhom
        rw [hE1]
        rw [ihj]
        rw [mul_add]
        rw [mul_smul_comm]
        have hrpow : r2 * (r2 ^ (j - 1) * g) = r2 ^ j * g := by
          rw [← mul_assoc]
          congr 1
          calc
            r2 * r2 ^ (j - 1) = r2 ^ (j - 1) * r2 := by rw [mul_comm]
            _ = r2 ^ ((j - 1) + 1) := by rw [pow_succ]
            _ = r2 ^ j := by congr 1; omega
        rw [hrpow]
        rw [smul_smul]
        rw [← mul_assoc, ← pow_succ']
        rw [add_assoc, ← add_smul, add_assoc, ← add_smul]
        have hjj : j + 1 - 1 = j := by omega
        rw [hjj]
        congr 1
        congr 1
        norm_num
        ring

-- ============================================================
-- Level 3 : iterated laplacian
-- ============================================================

private noncomputable def lapIter (w : P n) : ℕ → P n
  | 0 => w
  | t + 1 => lap (lapIter w t)

private lemma lapIter_succ (w : P n) (t : ℕ) : lapIter w (t + 1) = lap (lapIter w t) := by
  rfl

private lemma lapIter_mem (w : P n) {m : ℕ} (hw : w ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ m)
    (t : ℕ) : lapIter w t ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (m - 2 * t) := by
  induction t with
  | zero =>
      change w ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (m - 2 * 0)
      simpa using hw
  | succ t ih =>
      rw [lapIter_succ]
      unfold lap
      have h' := lap_mem_homogeneousSubmodule (n := n) (φ := lapIter w t) ih
      -- h' : lap (lapIter w t) ∈ V ((m - 2*t) - 2)
      have hdeg : (m - 2 * t) - 2 = m - 2 * (t + 1) := by omega
      simpa [hdeg] using h'

private lemma pderiv_eq_zero_of_mem_homogeneous_zero (i : Fin n) (p : P n)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ 0) :
    pderiv (R := ℝ) i p = 0 := by
  have h' : p ∈ (1 : Submodule ℝ (P n)) := by
    simpa [MvPolynomial.homogeneousSubmodule_zero] using hp
  obtain ⟨y, hy⟩ := Submodule.mem_one.mp h'
  rw [← hy]
  simpa using (MvPolynomial.pderiv_C (R := ℝ) (σ := Fin n) (a := y) (i := i))

private lemma lap_eq_zero_of_mem_homogeneous_le_one (p : P n) {d : ℕ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ d) (hd : d ≤ 1) :
    lap p = 0 := by
  unfold lap
  apply Finset.sum_eq_zero
  intro i hi
  have hpder : pderiv (R := ℝ) i p ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (d - 1) :=
    pderiv_mem_homogeneousSubmodule (n := n) i hp
  have hd0 : d - 1 = 0 := by omega
  rw [hd0] at hpder
  exact pderiv_eq_zero_of_mem_homogeneous_zero i (pderiv (R := ℝ) i p) hpder

-- ============================================================
-- Level 4 : the telescoping identity
-- ============================================================

private lemma tel_helper (x v y : P n) (a b : ℝ) :
    (x + a • y) + (v + b • y) = x + v + (a + b) • y := by
  calc
    (x + a • y) + (v + b • y) = x + v + (a • y + b • y) := by ac_rfl
    _ = x + v + (a + b) • y := by rw [← add_smul]

private lemma telescope_generic (N : ℕ) (hN : 1 ≤ N) (p : P n) (z : ℕ → P n)
    (A c : ℕ → ℝ) :
    (∀ r, r < N → lap (p * z r) = z (r + 1) + c (r + 1) • z r) →
    A 1 * c 1 = 1 →
    (∀ t, 1 ≤ t → t < N → A t + A (t + 1) * c (t + 1) = 0) →
    lap (∑ r ∈ Finset.range N, A (r + 1) • (p * z r)) = z 0 + A N • z N := by
  intro hformula hA1 hid
  induction N with
  | zero => omega
  | succ N ih =>
      by_cases h0 : N = 0
      · subst N
        rw [show (∑ r ∈ Finset.range 1, A (r + 1) • (p * z r)) = A (0 + 1) • (p * z 0) by simp]
        rw [lap_smul, hformula 0 (by omega)]
        rw [smul_add, smul_smul, hA1]
        simp [add_comm]
      · have hN1 : 1 ≤ N := by omega
        have hformulaN : ∀ r, r < N → lap (p * z r) = z (r + 1) + c (r + 1) • z r :=
          fun r hr => hformula r (by omega)
        have hidN : ∀ t, 1 ≤ t → t < N → A t + A (t + 1) * c (t + 1) = 0 :=
          fun t ht1 ht => hid t ht1 (by omega)
        have ihN := ih hN1 hformulaN hidN
        rw [Finset.sum_range_succ]
        rw [lap_add, ihN, lap_smul, hformula N (by omega)]
        rw [smul_add, smul_smul]
        rw [tel_helper]
        have hidN' := hid N (by omega) (by omega)
        rw [hidN']
        simp

private lemma lap_sub (f g : P n) : lap (f - g) = lap f - lap g := by
  unfold lap
  simp only [map_sub]
  rw [Finset.sum_sub_distrib]

end lap_helpers

-- ============================================================
-- Level 5 : coefficients (explicit n)
-- ============================================================

private noncomputable def invCoeff (n m : ℕ) : ℕ → ℝ
  | 0 => 0
  | 1 => (4 * (m : ℝ) + 2 * (n : ℝ))⁻¹
  | s + 2 => -invCoeff n m (s + 1) / ((s + 2 : ℝ) * (4 * (m : ℝ) + 2 * (n : ℝ) - 4 * (s + 1 : ℝ)))

private def coeffC (n m : ℕ) (s : ℕ) : ℝ :=
  (s : ℝ) * (4 * (m : ℝ) + 2 * (n : ℝ) - 4 * ((s - 1 : ℕ) : ℝ))

private lemma invCoeff_eq (n m : ℕ) {t : ℕ} (h : 2 ≤ t) :
    invCoeff n m t = - invCoeff n m (t - 1) /
      ((t : ℝ) * (4 * (m : ℝ) + 2 * (n : ℝ) - 4 * ((t - 1 : ℕ) : ℝ))) := by
  cases t with
  | zero => omega
  | succ t0 =>
      cases t0 with
      | zero => omega
      | succ s =>
          simp [invCoeff, show s + 2 - 1 = s + 1 by omega]
          ring

private lemma invCoeff_one_mul (n m : ℕ) (hn : 0 < (n : ℝ)) :
    invCoeff n m 1 * coeffC n m 1 = 1 := by
  dsimp [invCoeff, coeffC]
  have hden : (4 * (m : ℝ) + 2 * (n : ℝ)) ≠ 0 := by nlinarith
  norm_num
  field_simp [hden]

private lemma invCoeff_succ_mul (n m : ℕ) {t : ℕ} (ht : 1 ≤ t) (hn : 0 < (n : ℝ))
    (h2t : 2 * t ≤ m) :
    invCoeff n m t + invCoeff n m (t + 1) * coeffC n m (t + 1) = 0 := by
  have ht2 : 2 ≤ t + 1 := by omega
  rw [invCoeff_eq (n := n) (m := m) ht2]
  dsimp [coeffC]
  have hden : (t + 1 : ℝ) * (4 * (m : ℝ) + 2 * (n : ℝ) - 4 * (t : ℝ)) ≠ 0 := by
    have h1 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
    have hc : (0 : ℝ) < 4 * (m : ℝ) - 4 * (t : ℝ) := by
      have h2t' : (2 * (t : ℝ)) ≤ (m : ℝ) := by exact_mod_cast h2t
      nlinarith
    nlinarith
  simp
  have hden2 : ((t : ℝ) + 1) * (4 * (m : ℝ) + 2 * (n : ℝ) - 4 * (t : ℝ)) ≠ 0 := by
    simpa using hden
  rw [div_mul_cancel₀ _ hden2]
  ring


-- ============================================================
-- Level 6 : the main theorem
-- ============================================================

private theorem lap_X2_surjective_aux {n : ℕ} {k : ℕ} (hk : 2 ≤ k) [Nonempty (Fin n)]
    (w : MvPolynomial (Fin n) ℝ)
    (hw : w ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (k - 2)) :
    ∃ Q : MvPolynomial (Fin n) ℝ,
      Q ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (k - 2) ∧
      (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i (r2 * Q))) = w := by
  classical
  have hn : 0 < (n : ℝ) := by
    have hn0 : 0 < n := by
      obtain ⟨i⟩ := ‹Nonempty (Fin n)›
      exact lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
    exact_mod_cast hn0
  let m := k - 2
  have hw' : w ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ m := by
    simpa [m] using hw
  have hk2 : m + 2 = k := by omega
  let S := m / 2
  let N := S + 1
  let q : P n := r2
  let D := fun t : ℕ => lapIter (n := n) w t
  let z := fun r : ℕ => q ^ r * D r
  let A := invCoeff (n := n) m
  let c := coeffC (n := n) m
  let u : P n := ∑ r ∈ Finset.range N, A (r + 1) • (q * z r)
  -- u membership in V (m + 2)
  have htwo : ∀ {r m : ℕ}, r ≤ m / 2 → 2 * r ≤ m := by
    intro r m hr
    exact le_trans (Nat.mul_le_mul_left 2 hr) (by rw [mul_comm]; exact Nat.div_mul_le_self m 2)
  have z_mem : ∀ r, r ≤ S → z r ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ m := by
    intro r hr
    have h2r : 2 * r ≤ m := htwo (by simpa [S] using hr)
    have hq : (q ^ r).IsHomogeneous (2 * r) := by
      dsimp [q]
      simpa using (r2_IsHomogeneous (n := n)).pow r
    have hDr : (D r).IsHomogeneous (m - 2 * r) := by
      have hDmem : D r ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (m - 2 * r) := by
        dsimp [D]
        exact lapIter_mem (n := n) w hw' r
      exact (MvPolynomial.mem_homogeneousSubmodule (n := m - 2 * r) (p := D r)).mp hDmem
    have hdeg : 2 * r + (m - 2 * r) = m := by omega
    have hprod : (q ^ r * D r).IsHomogeneous (2 * r + (m - 2 * r)) := hq.mul hDr
    rw [MvPolynomial.mem_homogeneousSubmodule]
    simpa [z, hdeg] using hprod
  have u_mem : u ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (m + 2) := by
    unfold u
    apply (MvPolynomial.homogeneousSubmodule (Fin n) ℝ (m + 2)).sum_mem
    intro r hr
    have hrN : r < N := Finset.mem_range.mp hr
    have hrS : r ≤ S := Nat.le_of_lt_succ (by simpa [N] using hrN)
    have h2r : 2 * r ≤ m := htwo (by simpa [S] using hrS)
    have hq2 : (q ^ (r + 1)).IsHomogeneous (2 * (r + 1)) := by
      dsimp [q]
      simpa using (r2_IsHomogeneous (n := n)).pow (r + 1)
    have hdeg : 2 * (r + 1) + (m - 2 * r) = m + 2 := by omega
    have hD : (D r).IsHomogeneous (m - 2 * r) := by
      have hDmem : D r ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (m - 2 * r) := by
        dsimp [D]
        exact lapIter_mem (n := n) w hw' r
      exact (MvPolynomial.mem_homogeneousSubmodule (n := m - 2 * r) (p := D r)).mp hDmem
    have hprod : (q ^ (r + 1) * D r).IsHomogeneous (2 * (r + 1) + (m - 2 * r)) := hq2.mul hD
    have hmem : (q ^ (r + 1) * D r) ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (m + 2) := by
      rw [MvPolynomial.mem_homogeneousSubmodule]
      simpa [hdeg] using hprod
    have hzr : q * z r = q ^ (r + 1) * D r := by
      dsimp [z]
      rw [pow_succ']
      rw [mul_assoc]
    have hmem' : (q * z r) ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (m + 2) := by
      simpa [hzr] using hmem
    exact (MvPolynomial.homogeneousSubmodule (Fin n) ℝ (m + 2)).smul_mem (A (r + 1)) hmem'
  -- the Laplacian of u equals w : per-term formula
  have hper : ∀ r, r < N → lap (q * z r) = z (r + 1) + c (r + 1) • z r := by
    intro r hr
    have hrS : r ≤ S := Nat.le_of_lt_succ (by simpa [N] using hr)
    have h2r : 2 * r ≤ m := htwo (by simpa [S] using hrS)
    have hD : (D r).IsHomogeneous (m - 2 * r) := by
      have hDmem : D r ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (m - 2 * r) := by
        dsimp [D]
        exact lapIter_mem (n := n) w hw' r
      exact (MvPolynomial.mem_homogeneousSubmodule (n := m - 2 * r) (p := D r)).mp hDmem
    have hf := lap_r2pow_hom (n := n) (r + 1) (by omega) hD
    have hzr : q * z r = q ^ (r + 1) * D r := by
      dsimp [z]
      rw [pow_succ']
      rw [mul_assoc]
    have hlapD : lap (D r) = D (r + 1) := by
      dsimp [D]
      rw [lapIter_succ]
    have hcoef : ((r + 1 : ℕ) : ℝ) * (4 * ((m - 2 * r : ℕ) : ℝ)
          + 4 * ((r + 1 : ℕ) : ℝ) + 2 * (n : ℝ) - 4) = coeffC (n := n) m (r + 1) := by
      dsimp [coeffC]
      have hsub : ((m - 2 * r : ℕ) : ℝ) = (m : ℝ) - (2 * (r : ℝ)) := by
        rw [Nat.cast_sub h2r]
        norm_num
      rw [hsub]
      rw [Nat.cast_add]
      ring_nf
    rw [hzr]
    rw [hf]
    rw [hlapD]
    dsimp [z]
    rw [hcoef]
  -- A1 c1 = 1
  have hA1 : A 1 * c 1 = 1 := by
    dsimp [A, c]
    exact invCoeff_one_mul (n := n) m hn
  -- hid
  have hid : ∀ t, 1 ≤ t → t < N → A t + A (t + 1) * c (t + 1) = 0 := by
    intro t ht1 htN
    have htS : t ≤ S := Nat.le_of_lt_succ (by simpa [N] using htN)
    have h2t : 2 * t ≤ m := htwo (by simpa [S] using htS)
    dsimp [A, c]
    exact invCoeff_succ_mul (n := n) m ht1 hn h2t
  have hu_lap : lap (n := n) u = w := by
    dsimp [u]
    have hNpos : 1 ≤ N := by dsimp [N]; omega
    have ht := telescope_generic (n := n) N hNpos (p := q) z A c hper hA1 hid
    -- z 0 = w
    have hz0 : z 0 = w := by
      simp [z, D, lapIter]
    -- z N = 0
    have hDzero : D N = 0 := by
      dsimp [D, N]
      have hmid : lapIter (n := n) w (m / 2) ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ
          (m - 2 * (m / 2)) :=
        lapIter_mem (n := n) w hw' (m / 2)
      have hdeg1 : m - 2 * (m / 2) ≤ 1 := by omega
      have hzero : lap (n := n) (lapIter (n := n) w (m / 2)) = 0 :=
        lap_eq_zero_of_mem_homogeneous_le_one (n := n) (lapIter (n := n) w (m / 2)) hmid hdeg1
      rw [lapIter_succ]
      exact hzero
    have hzN : z N = 0 := by
      dsimp [z]
      rw [hDzero]
      simp
    rw [ht, hz0, hzN]
    simp
  -- The strengthened statement: build Q = sum_r A(r+1) • z r, so that u = q * Q.
  let Q : P n := ∑ r ∈ Finset.range N, A (r + 1) • z r
  have Q_mem : Q ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ m := by
    unfold Q
    apply (MvPolynomial.homogeneousSubmodule (Fin n) ℝ m).sum_mem
    intro r hr
    have hrN : r < N := Finset.mem_range.mp hr
    have hrS : r ≤ S := Nat.le_of_lt_succ (by simpa [N] using hrN)
    exact (MvPolynomial.homogeneousSubmodule (Fin n) ℝ m).smul_mem (A (r + 1)) (z_mem r hrS)
  have hident : q * Q = u := by
    dsimp [Q, u]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [mul_smul_comm]
  have hlapQ : lap (q * Q) = w := by
    rw [hident]
    exact hu_lap
  refine ⟨Q, ?_, ?_⟩
  · -- Q ∈ V (k - 2)
    have hQm : Q ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ m := Q_mem
    simpa [m] using hQm
  · -- (sum_i pderiv_i pderiv_i (r2 * Q)) = w
    change (lap (r2 * Q)) = w
    simpa [q] using hlapQ


-- ============================================================
-- The requested decomposition: any homogeneous P is a harmonic
-- homogeneous part plus r2 times a homogeneous polynomial of
-- degree k - 2.
-- ============================================================

theorem homogeneous_decompose {n : ℕ} {k : ℕ} [Nonempty (Fin n)]
    (P : MvPolynomial (Fin n) ℝ)
    (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k) :
    ∃ (H : MvPolynomial (Fin n) ℝ) (Q : MvPolynomial (Fin n) ℝ),
      H ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k ∧
      Q ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (k - 2) ∧
      (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i H)) = 0 ∧
      P = H + (∑ j : Fin n, (MvPolynomial.X j)^2) * Q := by
  classical
  by_cases hkle : k ≤ 1
  · -- k ≤ 1 : P itself is harmonic and Q := 0 works
    refine ⟨P, 0, hP, ?_, ?_, ?_⟩
    · exact (MvPolynomial.homogeneousSubmodule (Fin n) ℝ (k - 2)).zero_mem
    · change lap P = 0
      exact lap_eq_zero_of_mem_homogeneous_le_one (n := n) P hP hkle
    · simp
  · -- k ≥ 2 : decompose via the Laplacian
    have hk : 2 ≤ k := by omega
    let w : MvPolynomial (Fin n) ℝ :=
      ∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)
    have hw : w ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (k - 2) := by
      dsimp [w]
      exact lap_mem_homogeneousSubmodule hP
    rcases lap_X2_surjective_aux (n := n) (k := k) hk w hw with ⟨Q, hQ, hQlap⟩
    refine ⟨P - r2 * Q, Q, ?_, hQ, ?_, ?_⟩
    · -- H = P - r2 * Q ∈ V k
      have hQiso : Q.IsHomogeneous (k - 2) :=
        (MvPolynomial.mem_homogeneousSubmodule (n := k - 2) (p := Q)).mp hQ
      have hRiso : (r2 * Q).IsHomogeneous (2 + (k - 2)) := r2_IsHomogeneous.mul hQiso
      have hRmem : r2 * Q ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k := by
        rw [MvPolynomial.mem_homogeneousSubmodule]
        have hdeg : 2 + (k - 2) = k := by omega
        simpa [hdeg] using hRiso
      exact sub_mem hP hRmem
    · -- lap H = 0
      change lap (P - r2 * Q) = 0
      have hwlap : lap P = w := by rfl
      have hlapR : lap (r2 * Q) = w := by
        simpa [lap] using hQlap
      calc
        lap (P - r2 * Q) = lap P - lap (r2 * Q) := lap_sub P (r2 * Q)
        _ = w - w := by rw [hwlap, hlapR]
        _ = 0 := by rw [sub_self]
    · -- P = H + r2 * Q
      change P = P - r2 * Q + r2 * Q
      rw [sub_add_cancel]

end Commons.Algebra.MvPolynomial
