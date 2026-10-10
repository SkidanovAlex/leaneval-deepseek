import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Commons.RingTheory.Valuation.approximation_of_independent_ne_top_pos
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Valuation

/-- `(∑ i ∈ s, f i).coeff m = ∑ i ∈ s, (f i).coeff m`: the `m`-th coefficient of a finite sum
of polynomials is the sum of the `m`-th coefficients. -/
theorem coeff_finset_sum_of_monomials {R : Type*} [Semiring R] {ι : Type*}
    (s : Finset ι) (f : ι → Polynomial R) (m : ℕ) :
    (∑ i ∈ s, f i).coeff m = ∑ i ∈ s, (f i).coeff m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Polynomial.coeff_add, ih]

/-- **Simultaneous approximation of coefficients by a monic polynomial.**

Let `C₁`, `C₂` be two proper valuation subrings of a field `F` with no proper valuation subring
containing both.  Given two monic polynomials `f`, `h` of the same degree and nonzero elements
`c₁`, `c₂`, there is a monic polynomial `g` of degree `deg f` whose coefficients are
simultaneously `c₁`-close to those of `f` in the valuation of `C₁` and `c₂`-close to those of
`h` in the valuation of `C₂`.

The higher coefficients `j ≥ natDegree f` are forced by monicity: for `j > natDegree f` all three
polynomials have vanishing `j`-th coefficient, and for `j = natDegree f` all three equal `1`.
For the remaining coefficients the claim is exactly two-element weak approximation
(`approximation_of_independent_ne_top_pos`). -/
theorem exists_monic_close_coeffs {F : Type*} [Field F] (C₁ C₂ : ValuationSubring F) (h₁ : C₁ ≠ ⊤) (h₂ : C₂ ≠ ⊤) (hind : ∀ D : ValuationSubring F, C₁ ≤ D → C₂ ≤ D → D = ⊤) {f h : Polynomial F} (hfm : f.Monic) (hhm : h.Monic) (hdeg : h.natDegree = f.natDegree) {c₁ c₂ : F} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) : ∃ g : Polynomial F, g.Monic ∧ g.natDegree = f.natDegree ∧ (∀ j : ℕ, C₁.valuation (g.coeff j - f.coeff j) < C₁.valuation c₁) ∧ (∀ j : ℕ, C₂.valuation (g.coeff j - h.coeff j) < C₂.valuation c₂) := by
  classical
  have hc₁pos : 0 < C₁.valuation c₁ :=
    lt_of_le_of_ne' zero_le (fun h0 => hc₁ ((Valuation.zero_iff C₁.valuation).mp h0))
  have hc₂pos : 0 < C₂.valuation c₂ :=
    lt_of_le_of_ne' zero_le (fun h0 => hc₂ ((Valuation.zero_iff C₂.valuation).mp h0))
  have hwit : ∀ j : ℕ, ∃ z : F, C₁.valuation (z - f.coeff j) < C₁.valuation c₁ ∧
      C₂.valuation (z - h.coeff j) < C₂.valuation c₂ :=
    fun j => approximation_of_independent_ne_top_pos C₁ C₂ h₁ h₂ hind (f.coeff j) (h.coeff j)
      (C₁.valuation c₁) (C₂.valuation c₂) hc₁pos hc₂pos
  choose x hx using hwit
  let p : Polynomial F := ∑ j ∈ Finset.range f.natDegree, Polynomial.monomial j (x j)
  let g : Polynomial F := Polynomial.X ^ f.natDegree + p
  have hcoeff_p : ∀ m : ℕ, p.coeff m = if m < f.natDegree then x m else 0 := by
    intro m
    change (∑ j ∈ Finset.range f.natDegree, Polynomial.monomial j (x j)).coeff m
        = if m < f.natDegree then x m else 0
    rw [coeff_finset_sum_of_monomials]
    have h1 : (∑ j ∈ Finset.range f.natDegree, (Polynomial.monomial j (x j)).coeff m)
        = ∑ j ∈ Finset.range f.natDegree, (if j = m then x j else 0) :=
      Finset.sum_congr rfl (fun j _ => Polynomial.coeff_monomial)
    rw [h1, Finset.sum_ite_eq']
    simp only [Finset.mem_range]
  have hcoeff_g : ∀ m : ℕ,
      g.coeff m = (if m = f.natDegree then 1 else 0) + (if m < f.natDegree then x m else 0) := by
    intro m
    change (Polynomial.X ^ f.natDegree + p).coeff m
        = (if m = f.natDegree then 1 else 0) + (if m < f.natDegree then x m else 0)
    rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, hcoeff_p]
  have hg_lt : ∀ m : ℕ, m < f.natDegree → g.coeff m = x m := by
    intro m hm
    rw [hcoeff_g m, if_neg hm.ne, if_pos hm, zero_add]
  have hg_eq : g.coeff f.natDegree = 1 := by
    rw [hcoeff_g f.natDegree, if_pos rfl, if_neg (lt_irrefl f.natDegree), add_zero]
  have hg_gt : ∀ m : ℕ, f.natDegree < m → g.coeff m = 0 := by
    intro m hm
    rw [hcoeff_g m, if_neg hm.ne', if_neg (not_lt.mpr hm.le), add_zero]
  have hp_deg : p.natDegree ≤ f.natDegree := by
    change (∑ j ∈ Finset.range f.natDegree, Polynomial.monomial j (x j)).natDegree
        ≤ f.natDegree
    refine Polynomial.natDegree_sum_le_of_forall_le (Finset.range f.natDegree)
      (fun j => Polynomial.monomial j (x j)) ?_
    intro j hj
    rw [Finset.mem_range] at hj
    exact le_trans (Polynomial.natDegree_monomial_le (x j)) (le_of_lt hj)
  have hg_deg_le : g.natDegree ≤ f.natDegree := by
    change (Polynomial.X ^ f.natDegree + p).natDegree ≤ f.natDegree
    calc (Polynomial.X ^ f.natDegree + p).natDegree
        ≤ max (Polynomial.X ^ f.natDegree).natDegree p.natDegree := Polynomial.natDegree_add_le _ _
      _ = max f.natDegree p.natDegree := by rw [Polynomial.natDegree_X_pow]
      _ = f.natDegree := max_eq_left hp_deg
  have hg_natDegree : g.natDegree = f.natDegree :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hg_deg_le (by rw [hg_eq]; exact one_ne_zero)
  have hg_monic : g.Monic := by
    rw [Polynomial.Monic.def, ← Polynomial.coeff_natDegree]
    exact hg_natDegree.symm ▸ hg_eq
  have hfn : f.coeff f.natDegree = 1 := hfm.coeff_natDegree
  have hhn : h.coeff f.natDegree = 1 := by rw [← hdeg]; exact hhm.coeff_natDegree
  have hfzero : ∀ m : ℕ, f.natDegree < m → f.coeff m = 0 :=
    fun m hm => Polynomial.coeff_eq_zero_of_natDegree_lt hm
  have hhzero : ∀ m : ℕ, f.natDegree < m → h.coeff m = 0 :=
    fun m hm => Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg.symm ▸ hm)
  refine ⟨g, hg_monic, hg_natDegree, ?_, ?_⟩
  · intro j
    rcases lt_trichotomy j f.natDegree with hlt | heq | hgt
    · rw [hg_lt j hlt]; exact (hx j).1
    · rw [heq, hg_eq, hfn, sub_self, Valuation.map_zero]; exact hc₁pos
    · rw [hg_gt j hgt, hfzero j hgt, sub_self, Valuation.map_zero]; exact hc₁pos
  · intro j
    rcases lt_trichotomy j f.natDegree with hlt | heq | hgt
    · rw [hg_lt j hlt]; exact (hx j).2
    · rw [heq, hg_eq, hhn, sub_self, Valuation.map_zero]; exact hc₂pos
    · rw [hg_gt j hgt, hhzero j hgt, sub_self, Valuation.map_zero]; exact hc₂pos

end Commons.RingTheory.Valuation
