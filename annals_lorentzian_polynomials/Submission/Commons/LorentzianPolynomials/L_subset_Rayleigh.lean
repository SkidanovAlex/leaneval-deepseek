import Mathlib
import Submission.Commons.LorentzianPolynomials.strict_subset_L
import Submission.Commons.LorentzianPolynomials.S_closed
import Submission.Commons.LorentzianPolynomials.strict_lorentzian_quadratic_stable
import Submission.Commons.LorentzianPolynomials.hessian_aeval_eq
import Submission.Commons.LorentzianPolynomials.rayleigh_of_hessian_roots_le_one
import Submission.Commons.LorentzianPolynomials.L_pderivL_mem
import Submission.Commons.LorentzianPolynomials.L_hessian_index_le_one

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Commons.LorentzianPolynomials

noncomputable section

namespace LSR

/-- iterated partial derivative over a list -/
def pderivL {n : ℕ} (l : List (Fin n)) (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  l.foldl (fun q i => MvPolynomial.pderiv i q) p

lemma pderivL_cons {n : ℕ} (i : Fin n) (l : List (Fin n)) (p : MvPolynomial (Fin n) ℝ) :
    pderivL (i :: l) p = pderivL l (MvPolynomial.pderiv i p) := by
  rfl

lemma pderiv_pderivL {n : ℕ} (i : Fin n) (l : List (Fin n)) :
    ∀ p : MvPolynomial (Fin n) ℝ,
      MvPolynomial.pderiv i (pderivL l p) = pderivL l (MvPolynomial.pderiv i p) := by
  induction l with
  | nil => intro p; simp [pderivL]
  | cons a l ih =>
      intro p
      rw [pderivL_cons, pderivL_cons]
      rw [ih (MvPolynomial.pderiv a p)]
      congr 1
      exact rayleigh_pre.pderiv_comm i a p

lemma pderivL_cons_left {n : ℕ} (i : Fin n) (l : List (Fin n)) (p : MvPolynomial (Fin n) ℝ) :
    pderivL (i :: l) p = MvPolynomial.pderiv i (pderivL l p) := by
  rw [pderivL_cons, pderiv_pderivL]

lemma pderivL_two {n : ℕ} (i j : Fin n) (l : List (Fin n)) (p : MvPolynomial (Fin n) ℝ) :
    pderivL (i :: j :: l) p = MvPolynomial.pderiv i (MvPolynomial.pderiv j (pderivL l p)) := by
  rw [pderivL_cons_left]
  rw [pderivL_cons_left]

lemma pderivL_one {n : ℕ} (i : Fin n) (l : List (Fin n)) (p : MvPolynomial (Fin n) ℝ) :
    pderivL (i :: l) p = MvPolynomial.pderiv i (pderivL l p) := by
  exact pderivL_cons_left i l p

lemma pderivL_zero {n : ℕ} (l : List (Fin n)) : pderivL l (0 : MvPolynomial (Fin n) ℝ) = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      rw [pderivL_cons]
      simpa using ih

lemma pderivL_IsHomogeneous {n : ℕ} (l : List (Fin n)) {d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous d) : (pderivL l p).IsHomogeneous (d - l.length) := by
  have hmain : ∀ (d : ℕ) (p : MvPolynomial (Fin n) ℝ), p.IsHomogeneous d →
      (pderivL l p).IsHomogeneous (d - l.length) := by
    induction l with
    | nil => intro d p hp; simpa [pderivL] using hp
    | cons i l ih =>
        intro d p hp
        rw [pderivL_cons]
        have h1 : (MvPolynomial.pderiv i p).IsHomogeneous (d - 1) := hp.pderiv (i := i)
        have h2 := ih (d - 1) (MvPolynomial.pderiv i p) h1
        have hsub : (d - 1) - l.length = d - (l.length + 1) := by omega
        change (pderivL l (MvPolynomial.pderiv i p)).IsHomogeneous (d - (l.length + 1))
        simpa [hsub] using h2
  exact hmain d p hp

lemma L_subset_nonneg (n d : ℕ) :
    L n d ⊆ {f : H n d | ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m} := by
  intro f hf
  cases d with
  | zero => simpa [L] using hf.2
  | succ d =>
      cases d with
      | zero => simpa [L] using hf.2
      | succ d =>
          cases d with
          | zero => simpa [L] using hf.2
          | succ d =>
              simpa [L] using hf.1.2

lemma weight_nonzero_ge_one {n : ℕ} {m : Fin n →₀ ℕ} (hm : m ≠ 0) :
    1 ≤ Finsupp.weight (1 : Fin n → ℕ) m := by
  by_contra h1
  have hz : Finsupp.weight (1 : Fin n → ℕ) m = 0 := by omega
  have hne : ∃ i : Fin n, m i ≠ 0 := by
    by_contra h2
    apply hm
    apply Finsupp.ext
    intro i
    exact not_not.mp (by
      intro hmi
      exact h2 ⟨i, hmi⟩)
  rcases hne with ⟨i, hmi⟩
  have hge1 : 1 ≤ m i := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hmi)
  have hw := Finsupp.weight_eq_sum (w := (1 : Fin n → ℕ)) (f := m)
  have hsum : Finsupp.weight (1 : Fin n → ℕ) m = ∑ j : Fin n, m j := by
    simpa using hw
  have hle : m i ≤ ∑ j : Fin n, m j := by
    simpa using (Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_univ i))
  omega

lemma coeff_pderivL_nonneg {n : ℕ} (l : List (Fin n)) (p : MvPolynomial (Fin n) ℝ)
    (hp : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m) :
    ∀ m : Fin n →₀ ℕ, 0 ≤ (pderivL l p).coeff m := by
  classical
  induction l generalizing p with
  | nil => intro m; simpa [pderivL] using hp m
  | cons i l ih =>
      intro m
      rw [pderivL_cons]
      have hpderiv : ∀ m0 : Fin n →₀ ℕ, 0 ≤ (MvPolynomial.pderiv i p).coeff m0 := by
        intro m0
        rw [MvPolynomial.coeff_pderiv]
        have hpos : (0 : ℝ) ≤ ↑(m0 i) + 1 := by positivity
        exact mul_nonneg (hp (m0 + Finsupp.single i 1)) hpos
      exact ih (MvPolynomial.pderiv i p) hpderiv m

lemma eval_nonneg_of_coeff_nonneg' {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m) {w : Fin n → ℝ} (hw : ∀ k : Fin n, 0 ≤ w k) :
    0 ≤ MvPolynomial.eval w p := by
  classical
  rw [← MvPolynomial.support_sum_monomial_coeff p]
  rw [MvPolynomial.eval_sum]
  exact Finset.sum_nonneg (fun a ha => by
    rw [MvPolynomial.eval_monomial]
    exact mul_nonneg (hp a) (by
      rw [Finsupp.prod_pow]
      exact Finset.prod_nonneg (fun k _ => pow_nonneg (hw k) (a k))))

lemma eval_pderivL_nonneg {n : ℕ} (l : List (Fin n)) (p : MvPolynomial (Fin n) ℝ)
    (hp : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m) {w : Fin n → ℝ} (hw : ∀ k : Fin n, 0 ≤ w k) :
    0 ≤ MvPolynomial.eval w (pderivL l p) :=
  eval_nonneg_of_coeff_nonneg' (pderivL l p) (coeff_pderivL_nonneg l p hp) hw

lemma pderivL_eq_zero_of_length_gt {n : ℕ} (l : List (Fin n)) {d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous d) (hl : d < l.length) : pderivL l p = 0 := by
  classical
  induction l generalizing p d with
  | nil =>
      have hz : d < 0 := by simpa using hl
      omega
  | cons i l ih =>
      rw [pderivL_cons]
      by_cases hd0 : d = 0
      · have hp0 : p.IsHomogeneous 0 := by simpa [hd0] using hp
        have hw : p.IsWeightedHomogeneous (1 : Fin n → ℕ) 0 := by
          simpa [MvPolynomial.IsHomogeneous] using hp0
        have hpderiv : MvPolynomial.pderiv i p = 0 := by
          ext m
          rw [MvPolynomial.coeff_pderiv]
          by_cases hm0 : m = 0
          · subst m
            have hz : p.coeff (Finsupp.single i 1) = 0 := by
              apply MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero hw
              rw [Finsupp.weight_single]
              norm_num
            simpa [hz]
          · have hz : p.coeff (m + Finsupp.single i 1) = 0 := by
              apply MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero hw
              have hnz : m + Finsupp.single i 1 ≠ 0 := by
                intro h
                have hsub := congrArg (fun s : Fin n →₀ ℕ => s i) h
                simp at hsub
              have hposw : 1 ≤ Finsupp.weight (1 : Fin n → ℕ) (m + Finsupp.single i 1) :=
                weight_nonzero_ge_one hnz
              omega
            simpa [hz]
        rw [hpderiv]
        simpa using pderivL_zero l
      · have hl' : d - 1 < l.length := by
          have hl'' : d < l.length + 1 := by simpa using hl
          omega
        have h1 : (MvPolynomial.pderiv i p).IsHomogeneous (d - 1) := hp.pderiv (i := i)
        exact ih (d := d - 1) (p := MvPolynomial.pderiv i p) h1 hl'

lemma ray_const_le {d m : ℕ} (hd : 2 ≤ d) (hm : 2 ≤ m) (hle : m ≤ d) :
    (2 : ℝ) * (1 - 1 / (m : ℝ)) ≤ (2 : ℝ) * (1 - 1 / (d : ℝ)) := by
  have hdpos : 0 < (d : ℝ) := by positivity
  have hmpos : 0 < (m : ℝ) := by positivity
  have hmd : (m : ℝ) ≤ (d : ℝ) := by exact_mod_cast hle
  have hquot : (1 : ℝ) / (d : ℝ) ≤ (1 : ℝ) / (m : ℝ) := by
    exact one_div_le_one_div_of_le hmpos hmd
  nlinarith

lemma ray_const_nonneg {d : ℕ} (hd : 2 ≤ d) : 0 ≤ (2 : ℝ) * (1 - 1 / (d : ℝ)) := by
  have hdpos : 0 < (d : ℝ) := by positivity
  have hone : (1 : ℝ) / (d : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hdpos]
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ d)
    nlinarith
  nlinarith

/-- degree-m Rayleigh inequality for elements of L n m (m ≥ 2), via the index condition. -/
lemma rayleigh_deg_L {n m : ℕ} (hm : 2 ≤ m) (g : H n m) (hg : g ∈ L n m)
    (i j : Fin n) (w : Fin n → ℝ) (hw : ∀ k : Fin n, 0 ≤ w k) :
    MvPolynomial.eval w g.1 * MvPolynomial.eval w (MvPolynomial.pderiv i (MvPolynomial.pderiv j g.1)) ≤
      (2 : ℝ) * (1 - 1 / (m : ℝ)) *
        (MvPolynomial.eval w (MvPolynomial.pderiv i g.1) *
          MvPolynomial.eval w (MvPolynomial.pderiv j g.1)) := by
  have hnn : ∀ m0 : Fin n →₀ ℕ, 0 ≤ g.1.coeff m0 := L_subset_nonneg n m hg
  have hindex : ∀ w0 : Fin n → ℝ, (∀ k : Fin n, 0 < w0 k) →
      ((Matrix.of (fun a b : Fin n => MvPolynomial.eval w0
          (MvPolynomial.pderiv a (MvPolynomial.pderiv b g.1)))).charpoly.roots.filter
            (fun r : ℝ => 0 < r)).card ≤ 1 := by
    intro w0 hw0
    exact L_hessian_index_le_one n m hm g hg w0 hw0
  exact rayleigh_of_hessian_roots_le_one hm g.1 g.2 hnn hindex i j w hw

end LSR

/-- Every element of `L n d` (d ≥ 2) satisfies the full c-Rayleigh inequality with
constant `c = 2(1 - 1/d)`: for every list `l` of indices and all `i j`, for every
nonnegative evaluation point `w`. This is Proposition 2.19 of Brändén--Huh. -/
theorem L_subset_Rayleigh (n d : ℕ) (hn : 0 < n) (hd : 2 ≤ d) :
    ∀ f : H n d, f ∈ L n d →
      ∀ (l : List (Fin n)) (i j : Fin n) (w : Fin n → ℝ),
        (∀ k : Fin n, 0 ≤ w k) →
          MvPolynomial.eval w (l.foldl (fun q i => MvPolynomial.pderiv i q) f.1) *
              MvPolynomial.eval w ((i :: j :: l).foldl (fun q i => MvPolynomial.pderiv i q) f.1) ≤
            ((2 : ℝ) * (1 - 1 / (d : ℝ))) *
              (MvPolynomial.eval w ((i :: l).foldl (fun q i => MvPolynomial.pderiv i q) f.1) *
                MvPolynomial.eval w ((j :: l).foldl (fun q i => MvPolynomial.pderiv i q) f.1)) := by
  intro f hf l i j w hw
  change MvPolynomial.eval w (LSR.pderivL l f.1) *
        MvPolynomial.eval w (LSR.pderivL (i :: j :: l) f.1) ≤
      (2 : ℝ) * (1 - 1 / (d : ℝ)) *
        (MvPolynomial.eval w (LSR.pderivL (i :: l) f.1) * MvPolynomial.eval w (LSR.pderivL (j :: l) f.1))
  by_cases hk : l.length ≤ d - 2
  · let m := d - l.length
    have hm : 2 ≤ m := by
      dsimp [m]
      omega
    rcases L_pderivL_mem l f hf hk with ⟨g, hg1, hg2⟩
    have hg1' : g.1 = LSR.pderivL l f.1 := by
      simpa [LSR.pderivL] using hg1
    have hR := LSR.rayleigh_deg_L hm g hg2 i j w hw
    have hR' : MvPolynomial.eval w (LSR.pderivL l f.1) *
          MvPolynomial.eval w (LSR.pderivL (i :: j :: l) f.1) ≤
        (2 : ℝ) * (1 - 1 / (m : ℝ)) *
          (MvPolynomial.eval w (LSR.pderivL (i :: l) f.1) *
            MvPolynomial.eval w (LSR.pderivL (j :: l) f.1)) := by
      simpa [LSR.pderivL_two, LSR.pderivL_one, hg1'] using hR
    have hnnf : ∀ m0 : Fin n →₀ ℕ, 0 ≤ f.1.coeff m0 := LSR.L_subset_nonneg n d hf
    have hprod_nonneg : 0 ≤ MvPolynomial.eval w (LSR.pderivL (i :: l) f.1) *
        MvPolynomial.eval w (LSR.pderivL (j :: l) f.1) :=
      mul_nonneg (LSR.eval_pderivL_nonneg (i :: l) f.1 hnnf hw) (LSR.eval_pderivL_nonneg (j :: l) f.1 hnnf hw)
    have hle_c : (2 : ℝ) * (1 - 1 / (m : ℝ)) ≤ (2 : ℝ) * (1 - 1 / (d : ℝ)) := by
      dsimp [m]
      exact LSR.ray_const_le hd hm (by omega)
    have hc : (2 : ℝ) * (1 - 1 / (m : ℝ)) *
          (MvPolynomial.eval w (LSR.pderivL (i :: l) f.1) * MvPolynomial.eval w (LSR.pderivL (j :: l) f.1)) ≤
        (2 : ℝ) * (1 - 1 / (d : ℝ)) *
          (MvPolynomial.eval w (LSR.pderivL (i :: l) f.1) * MvPolynomial.eval w (LSR.pderivL (j :: l) f.1)) :=
      mul_le_mul_of_nonneg_right hle_c hprod_nonneg
    exact le_trans hR' hc
  · have hnnf : ∀ m0 : Fin n →₀ ℕ, 0 ≤ f.1.coeff m0 := LSR.L_subset_nonneg n d hf
    have hlen : (i :: j :: l).length = l.length + 2 := by simp
    have hz : LSR.pderivL (i :: j :: l) f.1 = 0 := by
      apply LSR.pderivL_eq_zero_of_length_gt (i :: j :: l) f.2
      rw [hlen]
      omega
    have hLHS0 : MvPolynomial.eval w (LSR.pderivL l f.1) *
        MvPolynomial.eval w (LSR.pderivL (i :: j :: l) f.1) = 0 := by
      rw [hz]
      simp
    rw [hLHS0]
    exact mul_nonneg (LSR.ray_const_nonneg hd)
      (mul_nonneg (LSR.eval_pderivL_nonneg (i :: l) f.1 hnnf hw) (LSR.eval_pderivL_nonneg (j :: l) f.1 hnnf hw))

end
end Commons.LorentzianPolynomials
