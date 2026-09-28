import Mathlib
import Submission.Work.HP.Defs

/-!
# Auxiliary definitions for the N02 bridge (`Work.HP.bridge`)

This file collects the objects that the bridge between the challenge's projective
statements and the primitive-coefficient counting of `Submission/Work/HP/Defs.lean`
needs:

* `Mon.toFinsupp` is injective and has total degree `d`;
* `toHom a` is the homogeneous degree-`d` polynomial attached to a coefficient vector;
* `toV a` is the corresponding point of `𝕍 d n = ℙ ℚ (homogeneousSubmodule _ ℚ d)`;
* `aeval_formOf` identifies `aeval` on `formOf d n a` with `formEval`;
* `finite_primSet`: height balls of primitive vectors are finite;
* `exists_map_ne_zero_of_span_range_eq_top`: a unimodular vector stays non-zero under a
  ring hom to a nontrivial ring (used to pass an adelic solution to a single place).
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset
open scoped LinearAlgebra.Projectivization

namespace Work.HP

variable {d n : ℕ}

/-! ## The monomial index -/

lemma Mon_toFinsupp_apply (m : Mon d n) (i : Fin (n + 1)) : m.toFinsupp i = (m.1 i : ℕ) := by
  simp [Mon.toFinsupp]

lemma Mon_degree_toFinsupp (m : Mon d n) : Finsupp.degree m.toFinsupp = d := by
  rw [Finsupp.degree_eq_sum]
  simp only [Mon_toFinsupp_apply]
  exact m.2

lemma Mon_toFinsupp_injective : Function.Injective (Mon.toFinsupp (d := d) (n := n)) := by
  intro m m' h
  have h1 : m.1 = m'.1 := by
    funext i
    have hi : (m.1 i : ℕ) = (m'.1 i : ℕ) := by
      rw [← Mon_toFinsupp_apply m i, ← Mon_toFinsupp_apply m' i, h]
    exact Fin.ext (by omega)
  exact Subtype.ext h1

/-! ## Coefficients of `formOf` -/

lemma formOf_coeff (a : Mon d n → ℤ) (m : Mon d n) :
    (formOf d n a).coeff (Mon.toFinsupp m) = (a m : ℚ) := by
  simp only [formOf, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single m]
  · simp
  · intro m' _ hm'
    rw [if_neg (fun hc => hm' (Mon_toFinsupp_injective hc))]
  · intro h; exact absurd (Finset.mem_univ m) h

lemma formOf_zero : formOf d n (0 : Mon d n → ℤ) = 0 := by
  simp only [Pi.zero_apply, Int.cast_zero, formOf, MvPolynomial.monomial_zero,
    Finset.sum_const_zero]

lemma formOf_eq_zero_iff (a : Mon d n → ℤ) : formOf d n a = 0 ↔ a = 0 := by
  constructor
  · intro h
    funext m
    have hc : (a m : ℚ) = 0 := by
      rw [← formOf_coeff a m, h]
      simp
    exact_mod_cast hc
  · intro h
    subst h
    exact formOf_zero

/-! ## The homogeneous degree-`d` polynomial attached to a coefficient vector -/

/-- The homogeneous degree-`d` rational polynomial with coefficient vector `a`. -/
def toHom (a : Mon d n → ℤ) : homogeneousSubmodule (Fin (n + 1)) ℚ d :=
  ⟨formOf d n a, by
    rw [mem_homogeneousSubmodule, formOf]
    exact IsHomogeneous.sum _ _ _ fun m _ => isHomogeneous_monomial _ (Mon_degree_toFinsupp m)⟩

@[simp] lemma toHom_coe (a : Mon d n → ℤ) :
    ((toHom a : homogeneousSubmodule (Fin (n + 1)) ℚ d) : MvPolynomial (Fin (n + 1)) ℚ) =
      formOf d n a := rfl

lemma toHom_eq_zero_iff (a : Mon d n → ℤ) : toHom a = 0 ↔ a = 0 := by
  constructor
  · intro h
    rw [← formOf_eq_zero_iff]
    have := congrArg (fun x : homogeneousSubmodule (Fin (n + 1)) ℚ d =>
      (x : MvPolynomial (Fin (n + 1)) ℚ)) h
    simpa using this
  · intro h
    subst h
    exact Subtype.ext formOf_zero

/-- A fixed non-zero element of the homogeneous submodule, used as a junk value. -/
def unitHom : homogeneousSubmodule (Fin (n + 1)) ℚ d :=
  ⟨MvPolynomial.X (0 : Fin (n + 1)) ^ d, by
    rw [mem_homogeneousSubmodule]
    simpa using (isHomogeneous_X ℚ (0 : Fin (n + 1))).pow d⟩

lemma unitHom_ne_zero : unitHom (d := d) (n := n) ≠ 0 := by
  intro h
  have h1 : (MvPolynomial.X (0 : Fin (n + 1)) ^ d : MvPolynomial (Fin (n + 1)) ℚ) = 0 := by
    have := congrArg (fun x : homogeneousSubmodule (Fin (n + 1)) ℚ d =>
      (x : MvPolynomial (Fin (n + 1)) ℚ)) h
    simpa [unitHom] using this
  exact pow_ne_zero d (MvPolynomial.X_ne_zero (0 : Fin (n + 1))) h1

/-- The point of `𝕍 d n` attached to a coefficient vector (junk value at `a = 0`). -/
def toV (a : Mon d n → ℤ) : HassePrincipleRandomFano.𝕍 d n :=
  if h : toHom a = 0 then Projectivization.mk ℚ (unitHom (d := d) (n := n)) unitHom_ne_zero
  else Projectivization.mk ℚ (toHom a) h

lemma toV_of_ne_zero (a : Mon d n → ℤ) (h : toHom a ≠ 0) :
    toV a = Projectivization.mk ℚ (toHom a) h := by
  rw [toV]
  exact dif_neg h

lemma toV_ne_zero_of_ne_zero (a : Mon d n → ℤ) (ha : a ≠ 0) : toHom a ≠ 0 :=
  fun h => ha ((toHom_eq_zero_iff a).1 h)

/-! ## Evaluation -/

lemma aeval_formOf {R : Type*} [CommRing R] [Algebra ℚ R] (a : Mon d n → ℤ)
    (x : Fin (n + 1) → R) : aeval x (formOf d n a) = formEval d n a x := by
  simp only [formOf, formEval]
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [aeval_monomial]
  congr 1
  · simp
  · rw [Finsupp.prod]
    rw [Finset.prod_subset (Finset.subset_univ _) ?_]
    · exact Finset.prod_congr rfl fun i _ => by rw [Mon_toFinsupp_apply]
    · intro i _ hi
      rw [Finsupp.notMem_support_iff.1 hi]
      simp

/-! ## Norms and primitivity -/

lemma eNorm_neg {ι : Type*} [Fintype ι] (v : ι → ℤ) : eNorm (-v) = eNorm v := by
  unfold eNorm
  congr 1
  exact Finset.sum_congr rfl fun i _ => by simp

lemma finset_gcd_neg {ι : Type*} [Fintype ι] (v : ι → ℤ) :
    Finset.univ.gcd (fun i => -v i) = Finset.univ.gcd v := by
  apply Int.dvd_antisymm <;> try exact Finset.Int.finsetGcd_nonneg
  · exact Finset.dvd_gcd fun i _ => dvd_neg.1 (Finset.gcd_dvd (Finset.mem_univ i))
  · exact Finset.dvd_gcd fun i _ => dvd_neg.2 (Finset.gcd_dvd (Finset.mem_univ i))

lemma IsPrim_neg {ι : Type*} [Fintype ι] (v : ι → ℤ) : IsPrim (-v) ↔ IsPrim v := by
  unfold IsPrim
  change Finset.univ.gcd (fun i => -v i) = 1 ↔ Finset.univ.gcd v = 1
  rw [finset_gcd_neg]

lemma abs_apply_le_eNorm {ι : Type*} [Fintype ι] (v : ι → ℤ) (i : ι) :
    |(v i : ℝ)| ≤ eNorm v := by
  have h : ((v i : ℝ)) ^ 2 ≤ ∑ j, ((v j : ℝ)) ^ 2 :=
    Finset.single_le_sum (f := fun j => ((v j : ℝ)) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  simpa [eNorm] using Real.abs_le_sqrt h

/-- Height balls of primitive vectors are finite. -/
lemma finite_primSet (A : ℝ) (P : (Mon d n → ℤ) → Prop) : (primSet d n A P).Finite := by
  set N : ℕ := ⌈max A 0⌉₊ with hN
  have hbox : (Set.univ.pi fun _ : Mon d n => Set.Icc (-(N : ℤ)) (N : ℤ)).Finite :=
    Set.Finite.pi fun _ => Set.finite_Icc _ _
  refine hbox.subset ?_
  intro a ha
  obtain ⟨_, hA, _⟩ := ha
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  intro m
  have h1 : |(a m : ℝ)| ≤ (N : ℝ) := by
    refine le_trans (abs_apply_le_eNorm a m) (le_trans hA ?_)
    exact le_trans (le_max_left _ _) (Nat.le_ceil _)
  obtain ⟨h2, h3⟩ := abs_le.1 h1
  exact ⟨by exact_mod_cast h2, by exact_mod_cast h3⟩

/-! ## Unimodularity is preserved by ring homs -/

lemma exists_map_ne_zero_of_span_range_eq_top {R S σ : Type*} [CommRing R] [CommRing S]
    [Nontrivial S] [Fintype σ] (φ : R →+* S) (y : σ → R)
    (h : Ideal.span (Set.range y) = ⊤) : ∃ i, φ (y i) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h1 : (1 : R) ∈ (Ideal.span (Set.range y) : Submodule R R) := by
    rw [h]; exact Submodule.mem_top
  rw [Submodule.mem_span_range_iff_exists_fun] at h1
  obtain ⟨c, hc⟩ := h1
  have h2 : (1 : S) = 0 := by
    have h3 := congrArg φ hc
    simpa [map_sum, map_mul, hcon] using h3.symm
  exact one_ne_zero h2

end Work.HP
