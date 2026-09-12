import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Finsupp.Pointwise
import Submission.Commons.Analysis.MvPolynomial.eval_support_subset_two

namespace Commons.Analysis.MvPolynomial

open scoped BigOperators

noncomputable section

/-- A finitely-supported exponent vector is "supported on `{a, b}`" when it vanishes
outside those two coordinates. -/
private def SupportedOnTwo {n : ℕ} (a b : Fin n) (d : Fin n →₀ ℕ) : Prop :=
  ∀ i : Fin n, i ≠ a → i ≠ b → d i = 0

/-- Decompose an exponent vector into its `a`-part, `b`-part, and the rest. -/
private lemma add_decomp {n : ℕ} (a b : Fin n) (hab : a ≠ b) (d : Fin n →₀ ℕ) :
    d = Finsupp.single a (d a) + Finsupp.single b (d b) +
        (d - Finsupp.single a (d a) - Finsupp.single b (d b)) := by
  ext i
  by_cases hia : i = a
  · subst i
    simp [hab]
  · by_cases hib : i = b
    · subst i
      simp [hab]
    · simp [hia, hib]

/-- `weight 1 (single a x + single b y) = x + y`. -/
private lemma weight_single_add {n : ℕ} (a b : Fin n) (_hab : a ≠ b) (x y : ℕ) :
    Finsupp.weight (1 : Fin n → ℕ) (Finsupp.single a x + Finsupp.single b y) = x + y := by
  rw [map_add]
  simp [Finsupp.weight_single]

/-- The (total) degree of `d` splits as `d a + d b` plus the degree of the rest. -/
private lemma weight_split {n : ℕ} (a b : Fin n) (hab : a ≠ b) (d : Fin n →₀ ℕ) :
    Finsupp.weight (1 : Fin n → ℕ) d =
      d a + d b + Finsupp.weight (1 : Fin n → ℕ) (d - Finsupp.single a (d a) - Finsupp.single b (d b)) := by
  let rest : Fin n →₀ ℕ := d - Finsupp.single a (d a) - Finsupp.single b (d b)
  have hd : d = Finsupp.single a (d a) + Finsupp.single b (d b) + rest := by
    simpa [rest] using add_decomp a b hab d
  have hcalc : Finsupp.weight (1 : Fin n → ℕ) d = d a + d b + Finsupp.weight (1 : Fin n → ℕ) rest := by
    calc
      Finsupp.weight (1 : Fin n → ℕ) d
          = Finsupp.weight (1 : Fin n → ℕ) (Finsupp.single a (d a) + Finsupp.single b (d b) + rest) := by
              conv_lhs => rw [hd]
      _ = d a + d b + Finsupp.weight (1 : Fin n → ℕ) rest := by
              rw [map_add, weight_single_add a b hab (d a) (d b)]
  simpa [rest] using hcalc

/-- An exponent vector supported on `{a,b}` equals its `a`- and `b`-parts. -/
private lemma supportedOn_eq_add {n : ℕ} (a b : Fin n) (hab : a ≠ b) (d : Fin n →₀ ℕ) :
    SupportedOnTwo a b d → d = Finsupp.single a (d a) + Finsupp.single b (d b) := by
  intro h
  ext i
  by_cases hia : i = a
  · subst i
    simp [hab]
  · by_cases hib : i = b
    · subst i
      simp [hab]
    · simp [hia, hib, h i hia hib]

/-- A finitely-supported `ℕ`-valued function of total degree zero is zero. -/
private lemma weight_one_eq_zero_iff {n : ℕ} (e : Fin n →₀ ℕ) :
    Finsupp.weight (1 : Fin n → ℕ) e = 0 ↔ e = 0 := by
  constructor
  · intro h
    apply Finsupp.ext
    intro i
    by_contra hne
    have hle := Finsupp.le_weight (1 : Fin n → ℕ) (s := i) (by norm_num : (1 : Fin n → ℕ) i ≠ 0) e
    rw [h] at hle
    exact hne (Nat.eq_zero_of_le_zero hle)
  · intro h
    rw [h, map_zero]

/-- If `d a + d b` already accounts for the whole degree of `d`, then `d` is supported
on `{a,b}`. -/
private lemma supportedOn_of_sum {n : ℕ} (a b : Fin n) (hab : a ≠ b) (d : Fin n →₀ ℕ)
    {k : ℕ} (hdeg : Finsupp.weight (1 : Fin n → ℕ) d = k) (hsum : d a + d b = k) :
    SupportedOnTwo a b d := by
  let rest : Fin n →₀ ℕ := d - Finsupp.single a (d a) - Finsupp.single b (d b)
  have hw : Finsupp.weight (1 : Fin n → ℕ) rest = 0 := by
    have hws := weight_split a b hab d
    rw [hdeg, hsum] at hws
    have hws' : k + 0 = k + Finsupp.weight (1 : Fin n → ℕ) rest := by simpa [rest] using hws
    exact (Nat.add_left_cancel hws').symm
  have hrest : rest = 0 := (weight_one_eq_zero_iff rest).mp hw
  intro i hia hib
  have hri : rest i = 0 := by
    rw [hrest]; rfl
  simpa [rest, hia, hib] using hri

/-- If `d` is supported on `{a,b}` and has degree `k`, then `d a + d b = k`. -/
private lemma sum_of_supportedOn {n : ℕ} (a b : Fin n) (hab : a ≠ b) (d : Fin n →₀ ℕ)
    {k : ℕ} (hdeg : Finsupp.weight (1 : Fin n → ℕ) d = k) (hc : SupportedOnTwo a b d) :
    d a + d b = k := by
  have hd := supportedOn_eq_add a b hab d hc
  calc
    d a + d b = Finsupp.weight (1 : Fin n → ℕ) (Finsupp.single a (d a) + Finsupp.single b (d b)) :=
      (weight_single_add a b hab (d a) (d b)).symm
    _ = Finsupp.weight (1 : Fin n → ℕ) d := by rw [← hd]
    _ = k := hdeg

/-- Reindexing: the sum over monomials `d` in the support of a degree-`k` homogeneous
`P` with `d a + d b = k` (only those with even `d b` survive, by `hodd`) is the sum over
`j ∈ range (k/2 + 1)` of the monomials `single a (k - 2j) + single b (2j)`. -/
private lemma filter_sum_to_range {n : ℕ} (a b : Fin n) (hab : a ≠ b)
    (P : MvPolynomial (Fin n) ℝ) {k : ℕ}
    (hdeg : ∀ d : Fin n →₀ ℕ, d ∈ P.support → Finsupp.weight (1 : Fin n → ℕ) d = k)
    (hodd : ∀ d : Fin n →₀ ℕ, Odd (d b) → P.coeff d = 0)
    (s t : ℝ) :
    (∑ d ∈ P.support.filter (fun d : Fin n →₀ ℕ => d a + d b = k),
        P.coeff d * s ^ (d a) * t ^ (d b))
    = ∑ j ∈ Finset.range (k / 2 + 1),
        P.coeff (Finsupp.single a (k - 2 * j) + Finsupp.single b (2 * j)) *
          s ^ (k - 2 * j) * t ^ (2 * j) := by
  classical
  let e : ℕ → Fin n →₀ ℕ := fun j => Finsupp.single a (k - 2 * j) + Finsupp.single b (2 * j)
  let D : Finset (Fin n →₀ ℕ) := Finset.image e (Finset.range (k / 2 + 1))
  let G : (Fin n →₀ ℕ) → ℝ := fun d => P.coeff d * s ^ (d a) * t ^ (d b)
  have hSsubD : (P.support.filter (fun d : Fin n →₀ ℕ => d a + d b = k)) ⊆ D := by
    intro d hd
    have hdS : d ∈ P.support ∧ d a + d b = k := by simpa using hd
    rcases hdS with ⟨hdsp, hdsum⟩
    have hcond : SupportedOnTwo a b d := supportedOn_of_sum a b hab d (hdeg d hdsp) hdsum
    have hcd : P.coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hdsp
    have hodd' : ¬ Odd (d b) := by
      intro ho
      exact hcd (hodd d ho)
    have hev : Even (d b) := by
      rcases Nat.even_or_odd (d b) with h | h
      · exact h
      · exact False.elim (hodd' h)
    rcases hev with ⟨j, hj⟩
    have hjm : j ≤ k / 2 := by
      rw [Nat.le_div_iff_mul_le (k := 2) (x := j) (y := k) (by norm_num : 0 < 2)]
      omega
    have hjr : j ∈ Finset.range (k / 2 + 1) := by
      rw [Finset.mem_range]
      omega
    have hej : e j = d := by
      ext i
      by_cases hia : i = a
      · subst i
        simp [e, hab]
        omega
      · by_cases hib : i = b
        · subst i
          simp [e, hab]
          omega
        · have hdi : d i = 0 := hcond i hia hib
          simp [e, hia, hib, hdi]
    exact Finset.mem_image.mpr ⟨j, hjr, hej⟩
  have hDzero : ∀ x ∈ D, x ∉ (P.support.filter (fun d : Fin n →₀ ℕ => d a + d b = k)) → G x = 0 := by
    intro x hx hnotS
    rcases Finset.mem_image.mp hx with ⟨j, hjr, hxj⟩
    have hjm : j ≤ k / 2 := by
      rw [Finset.mem_range] at hjr
      omega
    have hxsum : x a + x b = k := by
      subst x
      simp [e, hab]
      omega
    have hxsp : x ∉ P.support := by
      intro hsp
      apply hnotS
      simp [hsp, hxsum]
    have hcx : P.coeff x = 0 := MvPolynomial.notMem_support_iff.mp hxsp
    simp [G, hcx]
  have hsumD : (∑ d ∈ P.support.filter (fun d : Fin n →₀ ℕ => d a + d b = k), G d) =
      ∑ x ∈ D, G x := by
    exact Finset.sum_subset hSsubD hDzero
  have hinj : Set.InjOn e ↑(Finset.range (k / 2 + 1)) := by
    intro j1 hj1 j2 hj2 heq
    have hb1 : (e j1) b = 2 * j1 := by simp [e, hab]
    have hb2 : (e j2) b = 2 * j2 := by simp [e, hab]
    have : 2 * j1 = 2 * j2 := by
      calc
        2 * j1 = (e j1) b := hb1.symm
        _ = (e j2) b := by rw [heq]
        _ = 2 * j2 := hb2
    omega
  have himage : (∑ x ∈ D, G x) = ∑ j ∈ Finset.range (k / 2 + 1), G (e j) := by
    rw [Finset.sum_image]
    exact hinj
  have hterm : ∀ j ∈ Finset.range (k / 2 + 1),
      G (e j) = P.coeff (Finsupp.single a (k - 2 * j) + Finsupp.single b (2 * j)) *
          s ^ (k - 2 * j) * t ^ (2 * j) := by
    intro j hj
    simp [G, e, hab]
  calc
    (∑ d ∈ P.support.filter (fun d : Fin n →₀ ℕ => d a + d b = k),
        P.coeff d * s ^ (d a) * t ^ (d b))
        = ∑ d ∈ P.support.filter (fun d : Fin n →₀ ℕ => d a + d b = k), G d := by
            simp [G]
    _ = ∑ x ∈ D, G x := hsumD
    _ = ∑ j ∈ Finset.range (k / 2 + 1), G (e j) := himage
    _ = ∑ j ∈ Finset.range (k / 2 + 1),
        P.coeff (Finsupp.single a (k - 2 * j) + Finsupp.single b (2 * j)) *
          s ^ (k - 2 * j) * t ^ (2 * j) := Finset.sum_congr rfl hterm

end

theorem eval_two_var_even {n : ℕ} (a b : Fin n) (hab : a ≠ b)
    (P : MvPolynomial (Fin n) ℝ) {k : ℕ}
    (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k)
    (hodd : ∀ d : Fin n →₀ ℕ, Odd (d b) → P.coeff d = 0)
    (s t : ℝ) :
    MvPolynomial.eval (fun i : Fin n => if i = a then s else if i = b then t else 0) P
      = ∑ j ∈ Finset.range (k / 2 + 1),
          P.coeff (Finsupp.single a (k - 2 * j) + Finsupp.single b (2 * j)) *
            s ^ (k - 2 * j) * t ^ (2 * j) := by
  classical
  have hdeg : ∀ d : Fin n →₀ ℕ, d ∈ P.support → Finsupp.weight (1 : Fin n → ℕ) d = k := by
    intro d hd
    exact (MvPolynomial.mem_homogeneousSubmodule (n := k) P).mp hP (d := d)
      (MvPolynomial.mem_support_iff.mp hd)
  rw [eval_support_subset_two a b hab P hP s t]
  exact filter_sum_to_range a b hab P hdeg hodd s t

end Commons.Analysis.MvPolynomial