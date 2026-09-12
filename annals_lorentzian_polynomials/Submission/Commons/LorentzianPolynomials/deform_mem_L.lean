import Mathlib
import Submission.Commons.LorentzianPolynomials.hessian_aeval_eq
import Submission.Commons.LorentzianPolynomials.strict_lorentzian_quadratic_stable
import Submission.Commons.LorentzianPolynomials.S_closed
import Submission.Commons.LorentzianPolynomials.strict_subset_L
import Submission.Commons.LorentzianPolynomials.closure_strict_eq_L_of_degree_le_two
import Submission.Commons.LorentzianPolynomials.quad_deform_stable
import Submission.Commons.LorentzianPolynomials.deform_support_MConvex
import Submission.Commons.LorentzianPolynomials.deriv_support_MConvex
import Submission.Commons.LorentzianPolynomials.partials_mem_L_exact2
import Submission.Commons.LorentzianPolynomials.partials_mem_L_exact3
import Submission.Commons.LorentzianPolynomials.cubic_deform_mem_S2
import Submission.Commons.Combinatorics.MvPolynomial.interval_convex_of_rayleigh

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set
open Commons.Combinatorics.MvPolynomial
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Commons.LorentzianPolynomials

noncomputable section

namespace DML

/-! ## 1. The deformed polynomial -/

def defPoly (n d : ℕ) (θ : ℝ) (i j : Fin n) (f : H n d) : MvPolynomial (Fin n) ℝ :=
  f.1 + (C θ) * X i * pderiv j f.1

lemma defPoly_homogeneous {n d : ℕ} (f : H n d) (i j : Fin n) (θ : ℝ) :
    (defPoly n d θ i j f).IsHomogeneous d := by
  classical
  dsimp [defPoly]
  have hf : f.1.IsHomogeneous d := f.2
  by_cases hd0 : d = 0
  · subst d
    have hp : pderiv j f.1 = 0 := by
      apply MvPolynomial.ext
      intro m
      rw [MvPolynomial.coeff_pderiv]
      have hz : f.1.coeff (m + Finsupp.single j 1) = 0 := by
        apply MvPolynomial.IsHomogeneous.coeff_eq_zero (φ := f.1) (n := 0) hf
        rw [Finsupp.degree_eq_weight_one]
        have hw : Finsupp.weight (fun _ : Fin n => (1 : ℕ)) (m + Finsupp.single j 1) =
            Finsupp.weight (fun _ : Fin n => (1 : ℕ)) m + 1 := by
          rw [map_add]
          simp [Finsupp.weight_single]
        rw [hw]
        omega
      simp [hz]
    simpa [hp] using hf
  · have hdpos : 1 ≤ d := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hd0)
    have hp : (pderiv j f.1).IsHomogeneous (d - 1) := hf.pderiv
    have hX : (X i : MvPolynomial (Fin n) ℝ).IsHomogeneous 1 := MvPolynomial.isHomogeneous_X ℝ i
    have hC : ((C θ : MvPolynomial (Fin n) ℝ) * X i).IsHomogeneous 1 := by
      simpa using (MvPolynomial.isHomogeneous_C (Fin n) θ).mul hX
    have hprod := hC.mul hp
    have hdeg : 1 + (d - 1) = d := by omega
    have hterm : ((C θ : MvPolynomial (Fin n) ℝ) * X i * pderiv j f.1).IsHomogeneous d := by
      simpa [hdeg] using hprod
    simpa [add_comm] using hf.add hterm

noncomputable def defElem (n d : ℕ) (θ : ℝ) (i j : Fin n) (f : H n d) : H n d :=
  ⟨defPoly n d θ i j f, defPoly_homogeneous f i j θ⟩

lemma defElem_apply (n d : ℕ) (θ : ℝ) (i j : Fin n) (f : H n d) :
    (defElem n d θ i j f).1 = f.1 + (C θ) * X i * pderiv j f.1 := rfl

lemma coeff_X_nonneg {n : ℕ} (i : Fin n) (m : Fin n →₀ ℕ) :
    0 ≤ (X i : MvPolynomial (Fin n) ℝ).coeff m := by
  classical
  rw [MvPolynomial.coeff_X]
  by_cases h : Finsupp.single i 1 = m
  · simp [h]
  · simp [h]

lemma coeff_pderiv_nonneg {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m) (i : Fin n) :
    ∀ m : Fin n →₀ ℕ, 0 ≤ (pderiv i p).coeff m := by
  intro m
  rw [MvPolynomial.coeff_pderiv]
  exact mul_nonneg (hnn (m + Finsupp.single i 1)) (by positivity)

lemma coeff_mul_nonneg_of_nonneg {n : ℕ} (p q : MvPolynomial (Fin n) ℝ)
    (hp : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m) (hq : ∀ m : Fin n →₀ ℕ, 0 ≤ q.coeff m) :
    ∀ m : Fin n →₀ ℕ, 0 ≤ (p * q).coeff m := by
  classical
  intro m
  rw [MvPolynomial.coeff_mul]
  exact Finset.sum_nonneg (fun x hx => mul_nonneg (hp x.1) (hq x.2))

lemma defPoly_coeff_nonneg {n d : ℕ} (θ : ℝ) (hθ : 0 ≤ θ) (i j : Fin n)
    (f : H n d) (hfnn : ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m) :
    ∀ m : Fin n →₀ ℕ, 0 ≤ (defPoly n d θ i j f).coeff m := by
  classical
  intro m
  dsimp [defPoly]
  rw [MvPolynomial.coeff_add]
  rw [mul_assoc]
  rw [MvPolynomial.coeff_C_mul]
  exact add_nonneg (hfnn m)
    (mul_nonneg hθ (coeff_mul_nonneg_of_nonneg (X i) (pderiv j f.1)
      (fun a => coeff_X_nonneg i a) (coeff_pderiv_nonneg f.1 hfnn j) m))

/-! ## 2. list partials (commons pderivL) + eraseOnce + Leibniz -/

lemma pderivL_isHomogeneous {n : ℕ} (l : List (Fin n)) (p : MvPolynomial (Fin n) ℝ) {d : ℕ}
    (hp : p.IsHomogeneous d) : (pderivL l p).IsHomogeneous (d - l.length) := by
  classical
  induction l generalizing p d with
  | nil => simpa using hp
  | cons i l ih =>
      change (pderivL l (pderiv i p)).IsHomogeneous (d - (i :: l).length)
      have hpd : (pderiv i p).IsHomogeneous (d - 1) := hp.pderiv
      have hlen : d - 1 - l.length = d - (l.length + 1) := by omega
      have hih := ih (p := pderiv i p) (d := d - 1) hpd
      simpa [hlen, Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hih

lemma pderivL_coeff_nonneg {n : ℕ} (l : List (Fin n)) (p : MvPolynomial (Fin n) ℝ)
    (hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m) : ∀ m : Fin n →₀ ℕ, 0 ≤ (pderivL l p).coeff m := by
  induction l generalizing p hnn with
  | nil => simpa using hnn
  | cons i l ih =>
      intro m
      have hp : ∀ m : Fin n →₀ ℕ, 0 ≤ (pderiv i p).coeff m := coeff_pderiv_nonneg p hnn i
      simpa [pderivL_cons] using ih (p := pderiv i p) (hnn := hp) m

/-- remove the first occurrence of `i` -/
def eraseOnce {n : ℕ} (i : Fin n) : List (Fin n) → List (Fin n)
  | [] => []
  | j :: l => if j = i then l else j :: eraseOnce i l

lemma eraseOnce_cons_same {n : ℕ} (i : Fin n) (l : List (Fin n)) : eraseOnce i (i :: l) = l := by
  simp [eraseOnce]

lemma eraseOnce_cons_ne {n : ℕ} (i j : Fin n) (hij : j ≠ i) (l : List (Fin n)) :
    eraseOnce i (j :: l) = j :: eraseOnce i l := by
  simp [eraseOnce, hij]

lemma eraseOnce_of_not_mem {n : ℕ} (i : Fin n) (l : List (Fin n)) (hi : i ∉ l) :
    eraseOnce i l = l := by
  induction l with
  | nil => rfl
  | cons j l ih =>
      have hj : j ≠ i := by
        intro hji
        exact hi (List.mem_cons.mpr (Or.inl hji.symm))
      rw [eraseOnce_cons_ne i j hj]
      rw [ih]
      intro hi'
      exact hi (List.mem_cons.mpr (Or.inr hi'))

lemma singleton_append_perm {n : ℕ} (i : Fin n) (l : List (Fin n)) :
    (i :: l).Perm (l ++ [i]) := by
  induction l with
  | nil => simpa
  | cons a l ih =>
      exact (List.Perm.swap a i l).trans (List.Perm.cons a ih)

lemma eraseOnce_append_perm {n : ℕ} (i : Fin n) (l : List (Fin n)) (hi : i ∈ l) :
    (eraseOnce i l ++ [i]).Perm l := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
      by_cases hij : j = i
      · subst j
        rw [eraseOnce_cons_same]
        exact (singleton_append_perm i l).symm
      · rw [eraseOnce_cons_ne i j hij]
        have hi' : i ∈ l := (List.mem_cons.mp hi).resolve_left (Ne.symm hij)
        have hih := ih hi'
        exact List.Perm.cons j hih

lemma pderivL_add {n : ℕ} (l : List (Fin n)) (p q : MvPolynomial (Fin n) ℝ) :
    pderivL l (p + q) = pderivL l p + pderivL l q := by
  induction l generalizing p q with
  | nil => simp
  | cons i l ih =>
      have hd : pderiv i (p + q) = pderiv i p + pderiv i q := by simp
      rw [pderivL_cons, hd]
      exact ih (pderiv i p) (pderiv i q)

/-- Leibniz rule along a list, coefficient form. -/
lemma pderivL_mul_X {n : ℕ} (l : List (Fin n)) (i : Fin n) (h : MvPolynomial (Fin n) ℝ) :
    pderivL l ((X i : MvPolynomial (Fin n) ℝ) * h) =
      (X i : MvPolynomial (Fin n) ℝ) * pderivL l h +
        C (l.count i : ℝ) * pderivL (eraseOnce i l) h := by
  classical
  induction l generalizing h with
  | nil => simp
  | cons j l ih =>
      by_cases hij : i = j
      · subst j
        have hprod : pderiv i ((X i) * h) = h + (X i) * pderiv i h := by
          rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X]
          simp
        rw [pderivL_cons, eraseOnce_cons_same, pderivL_cons]
        rw [hprod, pderivL_add]
        have hih := ih (pderiv i h)
        rw [hih]
        by_cases hmem : i ∈ l
        · have hcancel : pderivL (eraseOnce i l) (pderiv i h) = pderivL l h := by
            calc
              pderivL (eraseOnce i l) (pderiv i h) = pderivL (eraseOnce i l ++ [i]) h := by
                rw [pderivL_cons_append]
                exact pderivL_perm (singleton_append_perm i (eraseOnce i l)) h
              _ = pderivL l h := pderivL_perm (eraseOnce_append_perm i l hmem) h
          have hC : (C ((l.count i + 1 : ℕ) : ℝ) : MvPolynomial (Fin n) ℝ) = C (l.count i : ℝ) + 1 := by
            rw [Nat.cast_add, Nat.cast_one, MvPolynomial.C_add, MvPolynomial.C_1]
          have hcount : ((i :: l).count i : ℕ) = l.count i + 1 := by simp
          rw [hcount, hC, hcancel]
          ring
        · have hnot : i ∉ l := hmem
          have hci : l.count i = 0 := List.count_eq_zero.mpr hnot
          have hC : (C ((l.count i + 1 : ℕ) : ℝ) : MvPolynomial (Fin n) ℝ) = C (l.count i : ℝ) + 1 := by
            rw [Nat.cast_add, Nat.cast_one, MvPolynomial.C_add, MvPolynomial.C_1]
          have hcount : ((i :: l).count i : ℕ) = l.count i + 1 := by simp
          rw [hcount, hC, hci]
          simp
          ring
      · have hprod : pderiv j ((X i) * h) = (X i) * pderiv j h := by
          rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X]
          simp [hij]
        rw [pderivL_cons, eraseOnce_cons_ne i j (Ne.symm hij)]
        rw [hprod]
        have hih := ih (pderiv j h)
        rw [pderivL_cons, hih]
        have hrc : pderivL (j :: eraseOnce i l) h = pderivL (eraseOnce i l) (pderiv j h) := by
          rw [pderivL_cons]
        have hcnt : (j :: l).count i = l.count i := List.count_cons_of_ne (Ne.symm hij)
        rw [hrc, hcnt]

/-! ## 3. deformed element is in M -/

lemma deformElem_mem_M {n d : ℕ} (θ : ℝ) (hθ : 0 ≤ θ) (i j : Fin n) (f : H n d)
    (hf : f ∈ M n d) : defElem n d θ i j f ∈ M n d := by
  classical
  rcases hf with ⟨hM, hnn⟩
  constructor
  · exact deform_support_MConvex n d θ hθ i j f.1 f.2 hM hnn
  · exact defPoly_coeff_nonneg θ hθ i j f hnn


/-! ## 4. criterion: M-convex + all (d-2)-partials in S n 2  ⟹  f ∈ L n d -/

lemma L_mem_of_M_and_partials {n : ℕ} (k : ℕ) (f : H n (k + 3))
    (hM : f ∈ M n (k + 3))
    (h2 : ∀ l : List (Fin n), l.length = (k + 3) - 2 →
      ∃ u : H n 2, u ∈ S n 2 ∧ u.1 = pderivL l f.1) :
    f ∈ L n (k + 3) := by
  classical
  induction k with
  | zero =>
      change f ∈ {f : H n (0 + 3) | f ∈ M n (0 + 3) ∧ ∀ i : Fin n,
        ⟨f.1.pderiv i, f.2.pderiv⟩ ∈ L n (0 + 2)}
      constructor
      · exact hM
      · intro i
        rcases h2 [i] (by simp) with ⟨u, hu, hu_eq⟩
        have hu1 : u.1 = f.1.pderiv i := by
          rw [hu_eq]
          simp [pderivL_cons]
        have heq : (⟨f.1.pderiv i, f.2.pderiv⟩ : H n 2) = u := by
          apply Subtype.ext
          exact hu1.symm
        rw [heq]
        simpa [L] using hu
  | succ k ih =>
      change f ∈ {f : H n (Nat.succ k + 3) | f ∈ M n (Nat.succ k + 3) ∧ ∀ i : Fin n,
        ⟨f.1.pderiv i, f.2.pderiv⟩ ∈ L n (Nat.succ k + 2)}
      constructor
      · exact hM
      · intro i
        have hfM : ⟨f.1.pderiv i, f.2.pderiv⟩ ∈ M n (k + 3) := by
          constructor
          · have hMder := deriv_support_MConvex (n := n) (d := Nat.succ k + 3) i f.1 f.2 hM.1
            simpa using hMder
          · intro m
            rw [MvPolynomial.coeff_pderiv]
            exact mul_nonneg (hM.2 (m + Finsupp.single i 1)) (by positivity)
        have hh2 : ∀ l : List (Fin n), l.length = (k + 3) - 2 →
            ∃ u : H n 2, u ∈ S n 2 ∧ u.1 = pderivL l (f.1.pderiv i) := by
          intro l hl
          have hlen2 : (i :: l).length = (Nat.succ k + 3) - 2 := by
            have hll : l.length = (k + 3) - 2 := hl
            have hlencons : (i :: l).length = l.length + 1 := by simp
            omega
          rcases h2 (i :: l) hlen2 with ⟨u, hu, hu_eq⟩
          refine ⟨u, hu, ?_⟩
          have hperm : pderivL (i :: l) f.1 = pderivL l (pderiv i f.1) := by
            rw [pderivL_cons]
          rwa [← hperm]
        have hmem := ih ⟨f.1.pderiv i, f.2.pderiv⟩ hfM hh2
        simpa [Nat.succ_eq_add_one, add_assoc, add_comm, add_left_comm] using hmem


/-! ## 5. assembly: partials of the deformed element lie in S n 2 -/

lemma pderivL_C_mul {n : ℕ} (l : List (Fin n)) (a : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    pderivL l ((C a : MvPolynomial (Fin n) ℝ) * p) = (C a : MvPolynomial (Fin n) ℝ) * pderivL l p := by
  induction l generalizing p with
  | nil => simp
  | cons i l ih =>
      have hd : pderiv i ((C a) * p) = (C a) * pderiv i p := by
        rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C]
        simp
      rw [pderivL_cons, hd]
      exact ih (pderiv i p)

lemma pderiv_commD {n : ℕ} (i j : Fin n) (p : MvPolynomial (Fin n) ℝ) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) :=
  Commons.Combinatorics.MvPolynomial.pderiv_comm i j p

lemma pderivL_comm_single {n : ℕ} (l : List (Fin n)) (i : Fin n) (p : MvPolynomial (Fin n) ℝ) :
    pderivL l (pderiv i p) = pderiv i (pderivL l p) := by
  induction l generalizing p with
  | nil => simp
  | cons j l ih =>
      rw [pderivL_cons]
      -- pderivL l (pderiv j (pderiv i p)) = pderiv i (pderivL (j :: l) p)
      have hc : pderiv j (pderiv i p) = pderiv i (pderiv j p) := pderiv_commD j i p
      rw [hc]
      have hih := ih (pderiv j p)
      rw [hih]
      rw [← pderivL_cons]

/-- eraseOnce drops the first occurrence of `i` (assumed to be in `l`). -/
lemma eraseOnce_length_eq {n : ℕ} (i : Fin n) (l : List (Fin n)) (hi : i ∈ l) :
    (eraseOnce i l).length + 1 = l.length := by
  have hp := eraseOnce_append_perm i l hi
  have hl := List.Perm.length_eq hp
  have hc : (eraseOnce i l ++ [i]).length = (eraseOnce i l).length + 1 := by simp
  omega

-- c = 0 case: `i` not in `l`
lemma defPoly_pderiv_zero {n d : ℕ} (θ : ℝ) (i j : Fin n) (f : H n d) (l : List (Fin n))
    (hni : i ∉ l) :
    pderivL l (defPoly n d θ i j f) =
      pderivL l f.1 + (C θ) * X i * pderiv j (pderivL l f.1) := by
  classical
  dsimp [defPoly]
  rw [mul_assoc]
  rw [pderivL_add, pderivL_C_mul]
  have herase : eraseOnce i l = l := eraseOnce_of_not_mem i l hni
  have hcount0 : l.count i = 0 := List.count_eq_zero.mpr hni
  rw [pderivL_mul_X, herase, hcount0]
  simp
  rw [pderivL_comm_single]
  ring

lemma partial_deform_S2_of_not_mem {n k : ℕ} (hn : 0 < n) (θ : ℝ) (hθ : 0 ≤ θ)
    (i j : Fin n) (f : H n (k + 3)) (hf : f ∈ L n (k + 3))
    (l : List (Fin n)) (hl : l.length = (k + 3) - 2) (hni : i ∉ l) :
    ∃ u : H n 2, u ∈ S n 2 ∧ u.1 = pderivL l (defPoly n (k + 3) θ i j f) := by
  classical
  rcases partials_mem_L_exact2 (n := n) (d := k + 3) (by omega : 2 ≤ k + 3) l hl f hf with ⟨q2, hq2S, hq2eq⟩
  have heq : pderivL l (defPoly n (k + 3) θ i j f) = q2.1 + (C θ) * X i * pderiv j q2.1 := by
    rw [defPoly_pderiv_zero θ i j f l hni]
    rw [← hq2eq]
  have hstab := quad_deform_stable (n := n) i j θ q2.1 q2.2 hq2S.1 hq2S.2 hθ
  have hstab' : IsStable (pderivL l (defPoly n (k + 3) θ i j f)) := by
    rw [heq]
    exact hstab
  have hfM : f ∈ M n (k + 3) := by
    have : f ∈ L n (k + 3) := hf
    change f ∈ {f : H n (k + 3) | f ∈ M n (k + 3) ∧
      ∀ i : Fin n, ⟨f.1.pderiv i, f.2.pderiv⟩ ∈ L n (k + 2)} at this
    exact this.1
  have hfnn : ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m := hfM.2
  have hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ (pderivL l (defPoly n (k + 3) θ i j f)).coeff m :=
    pderivL_coeff_nonneg l (defPoly n (k + 3) θ i j f)
      (defPoly_coeff_nonneg θ hθ i j f hfnn)
  let u : H n 2 := ⟨pderivL l (defPoly n (k + 3) θ i j f), by
    have hh := pderivL_isHomogeneous l (defPoly n (k + 3) θ i j f) (defPoly_homogeneous f i j θ)
    have hdeg : (k + 3) - l.length = 2 := by rw [hl]; omega
    simpa [hdeg] using hh⟩
  refine ⟨u, ?_, ?_⟩
  · dsimp [S, u]
    constructor
    · exact hstab'
    · exact hnn
  · rfl

-- c > 0 case: `i` in `l`
lemma defPoly_pderiv_pos {n d : ℕ} (θ : ℝ) (i j : Fin n) (f : H n d) (l : List (Fin n))
    (hi : i ∈ l) :
    pderivL l (defPoly n d θ i j f) =
      pderiv i (pderivL (eraseOnce i l) f.1) +
        C (θ * (l.count i : ℝ)) * pderiv j (pderivL (eraseOnce i l) f.1) +
          (C θ) * X i * pderiv i (pderiv j (pderivL (eraseOnce i l) f.1)) := by
  classical
  dsimp [defPoly]
  rw [mul_assoc]
  rw [pderivL_add, pderivL_C_mul]
  rw [pderivL_mul_X]
  have hperm : (eraseOnce i l ++ [i]).Perm l := eraseOnce_append_perm i l hi
  have hA : pderivL l f.1 = pderiv i (pderivL (eraseOnce i l) f.1) := by
    calc
      pderivL l f.1 = pderivL (eraseOnce i l ++ [i]) f.1 := (pderivL_perm hperm f.1).symm
      _ = pderivL [i] (pderivL (eraseOnce i l) f.1) := by rw [pderivL_append]
      _ = pderiv i (pderivL (eraseOnce i l) f.1) := by simpa [pderivL_cons]
  have hB : pderivL (eraseOnce i l) (pderiv j f.1) = pderiv j (pderivL (eraseOnce i l) f.1) :=
    pderivL_comm_single (eraseOnce i l) j f.1
  have hC : pderivL l (pderiv j f.1) = pderiv i (pderiv j (pderivL (eraseOnce i l) f.1)) := by
    calc
      pderivL l (pderiv j f.1) = pderiv j (pderivL l f.1) := pderivL_comm_single l j f.1
      _ = pderiv j (pderiv i (pderivL (eraseOnce i l) f.1)) := by rw [hA]
      _ = pderiv i (pderiv j (pderivL (eraseOnce i l) f.1)) := (pderiv_commD i j (pderivL (eraseOnce i l) f.1)).symm
  rw [hA, hC, hB]
  have hcm : (C θ : MvPolynomial (Fin n) ℝ) * C (l.count i : ℝ) = C (θ * (l.count i : ℝ)) := by
    rw [← MvPolynomial.C_mul]
  simp [hcm]
  ring

lemma partial_deform_S2_of_mem {n k : ℕ} (hn : 0 < n) (θ : ℝ) (hθ : 0 ≤ θ)
    (i j : Fin n) (f : H n (k + 3)) (hf : f ∈ L n (k + 3))
    (l : List (Fin n)) (hl : l.length = (k + 3) - 2) (hi : i ∈ l) :
    ∃ u : H n 2, u ∈ S n 2 ∧ u.1 = pderivL l (defPoly n (k + 3) θ i j f) := by
  classical
  let l' : List (Fin n) := eraseOnce i l
  have hlen' : l'.length = (k + 3) - 3 := by
    dsimp [l']
    have h1 : (eraseOnce i l).length + 1 = l.length := eraseOnce_length_eq i l hi
    rw [hl] at h1
    omega
  rcases partials_mem_L_exact3 (n := n) (d := k + 3) (by omega : 3 ≤ k + 3) l' hlen' f hf with ⟨h3, hh3, hh3eq⟩
  have hφ : 0 ≤ θ * (l.count i : ℝ) := mul_nonneg hθ (by positivity)
  rcases cubic_deform_mem_S2 n hn (θ * (l.count i : ℝ)) θ hφ hθ i j h3 hh3 with ⟨v, hvS, hv_eq⟩
  have heq : pderivL l (defPoly n (k + 3) θ i j f) = v.1 := by
    rw [hv_eq]
    have hde : pderiv i h3.1 + C (θ * (l.count i : ℝ)) * pderiv j h3.1 +
          C θ * X i * pderiv i (pderiv j h3.1) = pderivL l (defPoly n (k + 3) θ i j f) := by
      have he1 := defPoly_pderiv_pos θ i j f l hi
      rw [he1]
      rw [← hh3eq]
    exact hde.symm
  have hstab' : IsStable (pderivL l (defPoly n (k + 3) θ i j f)) := by
    rw [heq]
    exact hvS.1
  have hfM : f ∈ M n (k + 3) := by
    have : f ∈ L n (k + 3) := hf
    change f ∈ {f : H n (k + 3) | f ∈ M n (k + 3) ∧
      ∀ i : Fin n, ⟨f.1.pderiv i, f.2.pderiv⟩ ∈ L n (k + 2)} at this
    exact this.1
  have hfnn : ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m := hfM.2
  have hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ (pderivL l (defPoly n (k + 3) θ i j f)).coeff m :=
    pderivL_coeff_nonneg l (defPoly n (k + 3) θ i j f)
      (defPoly_coeff_nonneg θ hθ i j f hfnn)
  let u : H n 2 := ⟨pderivL l (defPoly n (k + 3) θ i j f), by
    have hh := pderivL_isHomogeneous l (defPoly n (k + 3) θ i j f) (defPoly_homogeneous f i j θ)
    have hdeg : (k + 3) - l.length = 2 := by rw [hl]; omega
    simpa [hdeg] using hh⟩
  refine ⟨u, ?_, ?_⟩
  · dsimp [S, u]
    constructor
    · exact hstab'
    · exact hnn
  · rfl

lemma partial_deform_S2 {n k : ℕ} (hn : 0 < n) (θ : ℝ) (hθ : 0 ≤ θ) (i j : Fin n)
    (f : H n (k + 3)) (hf : f ∈ L n (k + 3))
    (l : List (Fin n)) (hl : l.length = (k + 3) - 2) :
    ∃ u : H n 2, u ∈ S n 2 ∧ u.1 = pderivL l (defPoly n (k + 3) θ i j f) := by
  classical
  by_cases hi : i ∈ l
  · exact partial_deform_S2_of_mem hn θ hθ i j f hf l hl hi
  · exact partial_deform_S2_of_not_mem hn θ hθ i j f hf l hl hi
end DML

/-! ## 6. main theorem -/

lemma pderiv_const_zero_of_hom0 {n : ℕ} (f : H n 0) (j : Fin n) : pderiv j f.1 = 0 := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.coeff_pderiv]
  have hz : f.1.coeff (m + Finsupp.single j 1) = 0 := by
    apply MvPolynomial.IsHomogeneous.coeff_eq_zero (φ := f.1) (n := 0) f.2
    rw [Finsupp.degree_eq_weight_one]
    have hw : Finsupp.weight (fun _ : Fin n => (1 : ℕ)) (m + Finsupp.single j 1) =
        Finsupp.weight (fun _ : Fin n => (1 : ℕ)) m + 1 := by
      rw [map_add]
      simp [Finsupp.weight_single]
    rw [hw]
    omega
  simp [hz]

lemma defElem_eq_of_deg0 {n : ℕ} (θ : ℝ) (i j : Fin n) (f : H n 0) :
    DML.defElem n 0 θ i j f = f := by
  apply Subtype.ext
  dsimp [DML.defElem, DML.defPoly]
  rw [pderiv_const_zero_of_hom0 f j]
  simp

theorem deform_mem_L (n d : ℕ) (hn : 0 < n) (θ : ℝ) (hθ : 0 ≤ θ) (i j : Fin n)
    (f : Commons.LorentzianPolynomials.H n d) (hf : f ∈ Commons.LorentzianPolynomials.L n d) :
    ∃ g : Commons.LorentzianPolynomials.H n d, g ∈ Commons.LorentzianPolynomials.L n d ∧
      g.1 = f.1 + MvPolynomial.C θ * MvPolynomial.X i * MvPolynomial.pderiv j f.1 := by
  classical
  by_cases hd3 : 3 ≤ d
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, d = k + 3 := by
      refine ⟨d - 3, ?_⟩
      omega
    subst d
    let g : H n (k + 3) := DML.defElem n (k + 3) θ i j f
    refine ⟨g, ?_, ?_⟩
    · have hfM : f ∈ M n (k + 3) := by
        change f ∈ {f : H n (k + 3) | f ∈ M n (k + 3) ∧ ∀ i : Fin n,
          ⟨f.1.pderiv i, f.2.pderiv⟩ ∈ L n (k + 2)} at hf
        exact hf.1
      have hgM : g ∈ M n (k + 3) := DML.deformElem_mem_M θ hθ i j f hfM
      have hg2 : ∀ l : List (Fin n), l.length = (k + 3) - 2 →
          ∃ u : H n 2, u ∈ S n 2 ∧ u.1 = pderivL l g.1 := by
        intro l hl
        rcases DML.partial_deform_S2 hn θ hθ i j f hf l hl with ⟨u, hu, hu_eq⟩
        refine ⟨u, hu, ?_⟩
        dsimp [g, DML.defElem]
        exact hu_eq
      exact DML.L_mem_of_M_and_partials k g hgM hg2
    · dsimp [g]
      rfl
  · have hd2 : d ≤ 2 := by omega
    cases d with
    | zero =>
        let g : H n 0 := DML.defElem n 0 θ i j f
        refine ⟨g, ?_, ?_⟩
        · have hg_eq : g = f := defElem_eq_of_deg0 θ i j f
          rw [hg_eq]
          simpa [L] using hf
        · dsimp [g]
          rfl
    | succ d0 =>
        cases d0 with
        | zero =>
            -- d = 1
            let g : H n 1 := DML.defElem n 1 θ i j f
            refine ⟨g, ?_, ?_⟩
            · have hfnn : ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m := by
                have : f ∈ S n 1 := by simpa [L] using hf
                exact this.2
              have hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ g.1.coeff m := by
                dsimp [g]
                exact DML.defPoly_coeff_nonneg θ hθ i j f hfnn
              have hstab : IsStable g.1 := by
                dsimp [g]
                exact Commons.Analysis.MvPolynomial.isStable_of_degree_le_one
                  n 1 (by norm_num) (DML.defElem n 1 θ i j f) hnn
              have hS : g ∈ S n 1 := ⟨hstab, hnn⟩
              simpa [L] using hS
            · dsimp [g]
              rfl
        | succ d1 =>
            cases d1 with
            | zero =>
                -- d = 2
                let g : H n 2 := DML.defElem n 2 θ i j f
                refine ⟨g, ?_, ?_⟩
                · have hfS : f ∈ S n 2 := by simpa [L] using hf
                  have hstab : IsStable (f.1 + (C θ) * X i * pderiv j f.1) := by
                    exact quad_deform_stable i j θ f.1 f.2 hfS.1 hfS.2 hθ
                  have hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ g.1.coeff m := by
                    dsimp [g]
                    exact DML.defPoly_coeff_nonneg θ hθ i j f hfS.2
                  have hS : g ∈ S n 2 := by
                    dsimp [g]
                    -- g.1 = defPoly ... ; membership S n 2 needs IsStable g.1
                    constructor
                    · change IsStable (DML.defPoly n 2 θ i j f)
                      dsimp [DML.defPoly]
                      exact hstab
                    · exact hnn
                  simpa [L] using hS
                · dsimp [g]
                  rfl
            | succ k =>
                omega


end
end Commons.LorentzianPolynomials
