import Mathlib
import Submission.Work.DSSEC.PSChart
import Submission.Work.DSSEC.PSChartAwayArith
import Submission.Work.DSG2.ChartRingBasic

namespace Work.DSSEC
namespace PSGen

attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry
universe u

section Gen

variable {A : Type u} [CommRing A] {N : ℕ}

/-- The product of the variables over `S` equals the product over the subtype. -/
theorem tPS_eq_prod_attach (S : Finset (Idx N)) :
    tPS (A := A) (N := N) S =
      ∏ m : {m // m ∈ S}, (MvPolynomial.X m.1.down : MvPolynomial (Fin (N + 1)) A) := by
  rw [tPS, ← Finset.prod_attach S
    (fun m => (MvPolynomial.X m.down : MvPolynomial (Fin (N + 1)) A))]
  rw [Finset.attach_eq_univ]

/-- The monomial `∏ j, X_j ^ (w j)` is homogeneous of degree `w.degree`. -/
theorem isHomogeneous_prod_X (w : Fin (N + 1) →₀ ℕ) :
    (∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j)).IsHomogeneous w.degree := by
  rw [Finsupp.degree_eq_sum]
  exact MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun j => (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j)) w
    (fun j _ => by simpa using (MvPolynomial.isHomogeneous_X A j).pow (w j))

/-- The monomial `∏ j, X_j ^ (w j)` lies in the graded piece of degree `n * |S|`. -/
theorem mem_PGr_prod_X (S : Finset (Idx N)) (n : ℕ) (w : Fin (N + 1) →₀ ℕ)
    (hw : w.degree = n * S.card) :
    (∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j))
      ∈ DSMap.PGr A N (n • S.card) := by
  rw [MvPolynomial.mem_homogeneousSubmodule, nsmul_nat_eq_mul, ← hw]
  exact isHomogeneous_prod_X (A := A) (N := N) w

/-- `(∏_{m∈S} x_{l₀}/x_m) · ∏_{m∈S} x_m = x_{l₀}^{|S|}` in the localisation. -/
theorem prod_val_mul_tPS (S : Finset (Idx N)) (l₀ : Idx N) (_hl₀ : l₀ ∈ S) :
    (∏ m : {m // m ∈ S}, (chartFracPS (A := A) (N := N) S m.1 m.2 l₀).val) *
      algebraMap (MvPolynomial (Fin (N + 1)) A)
        (Localization.Away (tPS (A := A) (N := N) S)) (tPS (A := A) (N := N) S)
      = (algebraMap (MvPolynomial (Fin (N + 1)) A)
          (Localization.Away (tPS (A := A) (N := N) S))
          (MvPolynomial.X l₀.down)) ^ S.card := by
  have hmap : algebraMap (MvPolynomial (Fin (N + 1)) A)
        (Localization.Away (tPS (A := A) (N := N) S)) (tPS (A := A) (N := N) S)
      = ∏ m : {m // m ∈ S}, algebraMap (MvPolynomial (Fin (N + 1)) A)
          (Localization.Away (tPS (A := A) (N := N) S)) (MvPolynomial.X m.1.down) := by
    rw [← map_prod]
    exact congrArg _ (tPS_eq_prod_attach (A := A) (N := N) S)
  rw [hmap, ← Finset.prod_mul_distrib]
  rw [show (∏ m : {m // m ∈ S}, (chartFracPS (A := A) (N := N) S m.1 m.2 l₀).val *
        algebraMap (MvPolynomial (Fin (N + 1)) A)
          (Localization.Away (tPS (A := A) (N := N) S)) (MvPolynomial.X m.1.down))
      = ∏ _m : {m // m ∈ S}, algebraMap (MvPolynomial (Fin (N + 1)) A)
          (Localization.Away (tPS (A := A) (N := N) S)) (MvPolynomial.X l₀.down) from
    Finset.prod_congr rfl (fun m _ => val_chartFracPS_mul (A := A) (N := N) S m.1 m.2 l₀)]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]

/-- `(∏_j (x_j/x_{l₀})^{w j}) · x_{l₀}^{w.degree} = ∏_j x_j^{w j}` in the localisation. -/
theorem prod_pow_val_chartFracPS (S : Finset (Idx N)) (l₀ : Idx N) (hl₀ : l₀ ∈ S)
    (w : Fin (N + 1) →₀ ℕ) :
    (∏ j : Fin (N + 1), (chartFracPS (A := A) (N := N) S l₀ hl₀ (ULift.up j)).val ^ (w j)) *
      (algebraMap (MvPolynomial (Fin (N + 1)) A)
        (Localization.Away (tPS (A := A) (N := N) S)) (MvPolynomial.X l₀.down)) ^ (w.degree)
      = algebraMap (MvPolynomial (Fin (N + 1)) A)
        (Localization.Away (tPS (A := A) (N := N) S))
        (∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j)) := by
  rw [Finsupp.degree_eq_sum, ← Finset.prod_pow_eq_pow_sum]
  rw [← Finset.prod_mul_distrib]
  rw [show (∏ j : Fin (N + 1),
        (chartFracPS (A := A) (N := N) S l₀ hl₀ (ULift.up j)).val ^ (w j) *
        (algebraMap (MvPolynomial (Fin (N + 1)) A)
          (Localization.Away (tPS (A := A) (N := N) S)) (MvPolynomial.X l₀.down)) ^ (w j))
      = ∏ j : Fin (N + 1), ((chartFracPS (A := A) (N := N) S l₀ hl₀ (ULift.up j)).val *
        algebraMap (MvPolynomial (Fin (N + 1)) A)
          (Localization.Away (tPS (A := A) (N := N) S)) (MvPolynomial.X l₀.down)) ^ (w j) from
    Finset.prod_congr rfl (fun j _ => (mul_pow _ _ _).symm)]
  rw [show (∏ j : Fin (N + 1), ((chartFracPS (A := A) (N := N) S l₀ hl₀ (ULift.up j)).val *
        algebraMap (MvPolynomial (Fin (N + 1)) A)
          (Localization.Away (tPS (A := A) (N := N) S)) (MvPolynomial.X l₀.down)) ^ (w j))
      = ∏ j : Fin (N + 1), (algebraMap (MvPolynomial (Fin (N + 1)) A)
          (Localization.Away (tPS (A := A) (N := N) S)) (MvPolynomial.X j)) ^ (w j) from
    Finset.prod_congr rfl
      (fun j _ => by rw [val_chartFracPS_mul (A := A) (N := N) S l₀ hl₀ (ULift.up j)])]
  rw [show (∏ j : Fin (N + 1), (algebraMap (MvPolynomial (Fin (N + 1)) A)
          (Localization.Away (tPS (A := A) (N := N) S)) (MvPolynomial.X j)) ^ (w j))
      = ∏ j : Fin (N + 1), algebraMap (MvPolynomial (Fin (N + 1)) A)
          (Localization.Away (tPS (A := A) (N := N) S))
          ((MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j)) from
    Finset.prod_congr rfl (fun j _ => (map_pow _ _ _).symm)]
  rw [← map_prod]

/-- The value of `Away.mk` on a monomial: for `w.degree = n * |S|`,
`(∏_j x_j^{w j}) / f^n = (∏_j (x_j/x_{l₀})^{w j}) · (∏_{m∈S} x_{l₀}/x_m)^n`. -/
theorem Away_mk_prod_X (S : Finset (Idx N)) (l₀ : Idx N) (hl₀ : l₀ ∈ S)
    (n : ℕ) (w : Fin (N + 1) →₀ ℕ) (hw : w.degree = n * S.card)
    (h : (∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j))
        ∈ DSMap.PGr A N (n • S.card)) :
    HomogeneousLocalization.Away.mk (DSMap.PGr A N) (tPS_mem S) n
        (∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j)) h
      = (∏ j : Fin (N + 1), chartFracPS (A := A) (N := N) S l₀ hl₀ (ULift.up j) ^ (w j)) *
        (∏ m : {m // m ∈ S}, chartFracPS (A := A) (N := N) S m.1 m.2 l₀) ^ n := by
  have hvalRHS : ((∏ j : Fin (N + 1),
          chartFracPS (A := A) (N := N) S l₀ hl₀ (ULift.up j) ^ (w j)) *
        (∏ m : {m // m ∈ S}, chartFracPS (A := A) (N := N) S m.1 m.2 l₀) ^ n).val
      = (∏ j : Fin (N + 1),
          ((chartFracPS (A := A) (N := N) S l₀ hl₀ (ULift.up j)).val) ^ (w j)) *
        (∏ m : {m // m ∈ S}, (chartFracPS (A := A) (N := N) S m.1 m.2 l₀).val) ^ n := by
    rw [← HomogeneousLocalization.algebraMap_apply (𝒜 := DSMap.PGr A N)
      (x := Submonoid.powers (tPS (A := A) (N := N) S))]
    simp only [map_mul, map_pow, map_prod, HomogeneousLocalization.algebraMap_apply]
    rfl
  have hunit : IsUnit (algebraMap (MvPolynomial (Fin (N + 1)) A)
      (Localization.Away (tPS (A := A) (N := N) S)) ((tPS (A := A) (N := N) S) ^ n)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit (tPS (A := A) (N := N) S)).pow n
  apply HomogeneousLocalization.val_injective (Submonoid.powers (tPS (A := A) (N := N) S))
  rw [HomogeneousLocalization.Away.val_mk, hvalRHS, Localization.mk_eq_mk']
  refine IsUnit.mul_right_cancel hunit ?_
  rw [IsLocalization.mk'_spec, map_pow, mul_assoc, ← mul_pow,
    prod_val_mul_tPS (A := A) (N := N) S l₀ hl₀, ← pow_mul, Nat.mul_comm S.card n, ← hw]
  exact (prod_pow_val_chartFracPS (A := A) (N := N) S l₀ hl₀ w).symm

/-- The value of `Away.mk` on a monomial times a constant. -/
theorem Away_mk_mon (S : Finset (Idx N)) (l₀ : Idx N) (hl₀ : l₀ ∈ S)
    (n : ℕ) (w : Fin (N + 1) →₀ ℕ) (c : A) (hw : w.degree = n * S.card)
    (h : (MvPolynomial.C c * ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j))
        ∈ DSMap.PGr A N (n • S.card)) :
    HomogeneousLocalization.Away.mk (DSMap.PGr A N) (tPS_mem S) n
        (MvPolynomial.C c * ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j)) h
      = AtoAwayS (A := A) (N := N) S c *
        (∏ j : Fin (N + 1), chartFracPS (A := A) (N := N) S l₀ hl₀ (ULift.up j) ^ (w j)) *
        (∏ m : {m // m ∈ S}, chartFracPS (A := A) (N := N) S m.1 m.2 l₀) ^ n := by
  rw [Away_mk_C_mul (S := S) (n := n) (c := c)
      (p := ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j))
      (mem_PGr_prod_X (A := A) (N := N) S n w hw) (mem_PGr_C (A := A) (N := N) S c) h]
  rw [Away_mk_C (S := S) c (mem_PGr_C (A := A) (N := N) S c)]
  rw [Away_mk_prod_X (S := S) (l₀ := l₀) (hl₀ := hl₀) (n := n) (w := w) hw
      (mem_PGr_prod_X (A := A) (N := N) S n w hw)]
  ring


/-- **Generation of the chart ring.** `Away (PGr A N) (tPS S)` is generated over `A` (via
`AtoAwayS S`) by the chart coordinates `x_k/x_l`, `l ∈ S`. -/
theorem awayGenPS_aux (S : Finset (Idx N)) (hS : S.Nonempty) :
    Function.Surjective fun p : MvPolynomial ({l // l ∈ S} × Idx N) A =>
      MvPolynomial.eval₂ (AtoAwayS (A := A) (N := N) S)
        (fun q : {l // l ∈ S} × Idx N =>
          chartFracPS (A := A) S q.1.1 q.1.2 q.2) p := by
  obtain ⟨l₀, hl₀⟩ := hS
  let C : Subring (HomogeneousLocalization.Away (DSMap.PGr A N) (tPS (A := A) (N := N) S)) :=
    Subring.closure (Set.range (fun q : {l // l ∈ S} × Idx N =>
        chartFracPS (A := A) S q.1.1 q.1.2 q.2) ∪
      Set.range (AtoAwayS (A := A) (N := N) S))
  have hmem_gen : ∀ q : {l // l ∈ S} × Idx N,
      chartFracPS (A := A) S q.1.1 q.1.2 q.2 ∈ C :=
    fun q => Subring.subset_closure (Or.inl ⟨q, rfl⟩)
  have hmem_A : ∀ a : A, AtoAwayS (A := A) (N := N) S a ∈ C :=
    fun a => Subring.subset_closure (Or.inr ⟨a, rfl⟩)
  have hgen : ∀ y : HomogeneousLocalization.Away (DSMap.PGr A N) (tPS (A := A) (N := N) S),
      y ∈ C := by
    intro y
    obtain ⟨n, p, hp, hz⟩ :=
      HomogeneousLocalization.Away.mk_surjective (𝒜 := DSMap.PGr A N) (tPS_mem S) y
    rw [← hz]
    have hp' : p.IsHomogeneous (n • S.card) := by
      rw [MvPolynomial.mem_homogeneousSubmodule] at hp; exact hp
    have hdeg : ∀ w ∈ p.support, w.degree = n * S.card := fun w hw => by
      by_contra h
      refine (MvPolynomial.mem_support_iff.mp hw) (MvPolynomial.IsHomogeneous.coeff_eq_zero hp' ?_)
      rw [nsmul_nat_eq_mul]
      exact h
    have hG : ∀ w : Fin (N + 1) →₀ ℕ, MvPolynomial.C (p.coeff w) *
        ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j)
          ∈ DSMap.PGr A N (n • S.card) := fun w => by
      by_cases hw : w ∈ p.support
      · have hmon : (MvPolynomial.C (p.coeff w) *
            ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j))
            = MvPolynomial.monomial w (p.coeff w) := by
          rw [MvPolynomial.monomial_eq, ← Work.DSG2.prod_eq_finsupp_prod A N w]
        rw [hmon, MvPolynomial.mem_homogeneousSubmodule, nsmul_nat_eq_mul, ← hdeg w hw]
        exact MvPolynomial.isHomogeneous_monomial (p.coeff w) rfl
      · rw [show p.coeff w = 0 from by
          by_contra h
          exact hw (MvPolynomial.mem_support_iff.mpr h)]
        simp
    have hdecomp : p = ∑ w ∈ p.support, MvPolynomial.C (p.coeff w) *
        ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j) := by
      conv_lhs => rw [MvPolynomial.as_sum p]
      apply Finset.sum_congr rfl
      intro w _
      rw [MvPolynomial.monomial_eq, ← Work.DSG2.prod_eq_finsupp_prod A N w]
    have hsummem : (∑ w ∈ p.support, MvPolynomial.C (p.coeff w) *
        ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j))
        ∈ DSMap.PGr A N (n • S.card) := by
      rw [← hdecomp]; exact hp
    have hmem : ∀ w : Fin (N + 1) →₀ ℕ,
        HomogeneousLocalization.Away.mk (DSMap.PGr A N) (tPS_mem S) n
          (MvPolynomial.C (p.coeff w) *
            ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j)) (hG w) ∈ C := by
      intro w
      by_cases hw : w ∈ p.support
      · rw [Away_mk_mon (A := A) (N := N) S l₀ hl₀ n w (p.coeff w) (hdeg w hw) (hG w)]
        refine Subring.mul_mem C (Subring.mul_mem C ?_ ?_) ?_
        · exact hmem_A (p.coeff w)
        · exact Subring.prod_mem C
            (fun j _ => Subring.pow_mem C (hmem_gen (⟨l₀, hl₀⟩, ULift.up j)) (w j))
        · exact Subring.pow_mem C
            (Subring.prod_mem C (fun m _ => hmem_gen (m, l₀))) n
      · have hc : p.coeff w = 0 := by
          by_contra h; exact hw (MvPolynomial.mem_support_iff.mpr h)
        have hnum : MvPolynomial.C (p.coeff w) *
            ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j) = 0 := by
          rw [hc]; simp
        rw [Away_mk_congr (tPS_mem S) n hnum (hG w) (zero_mem _)]
        rw [Away_mk_zero (A := A) (N := N) S n (zero_mem _)]
        exact Subring.zero_mem C
    rw [Away_mk_congr (tPS_mem S) n hdecomp hp hsummem]
    rw [Away_mk_sum (tPS_mem S) n p.support
      (fun w => MvPolynomial.C (p.coeff w) *
        ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j)) hG hsummem]
    exact Subring.sum_mem C (fun w _ => hmem w)
  intro y
  change ∃ r, MvPolynomial.eval₂Hom (AtoAwayS (A := A) (N := N) S)
      (fun q : {l // l ∈ S} × Idx N => chartFracPS (A := A) S q.1.1 q.1.2 q.2) r = y
  refine Subring.closure_induction (p := fun y _ => ∃ r, MvPolynomial.eval₂Hom
      (AtoAwayS (A := A) (N := N) S)
      (fun q : {l // l ∈ S} × Idx N => chartFracPS (A := A) S q.1.1 q.1.2 q.2) r = y)
    ?_ ?_ ?_ ?_ ?_ ?_ (hgen y)
  · rintro x (hx | hx)
    · obtain ⟨q, rfl⟩ := hx
      exact ⟨MvPolynomial.X (⟨q.1, ULift.up q.2.down⟩ : {l // l ∈ S} × Idx N),
        MvPolynomial.eval₂Hom_X' _ _ _⟩
    · obtain ⟨a, rfl⟩ := hx
      exact ⟨MvPolynomial.C a, MvPolynomial.eval₂Hom_C _ _ a⟩
  · exact ⟨0, map_zero _⟩
  · exact ⟨1, map_one _⟩
  · rintro x y _ _ ⟨q1, h1⟩ ⟨q2, h2⟩
    exact ⟨q1 + q2, by rw [map_add, h1, h2]⟩
  · rintro x _ ⟨q, h⟩
    exact ⟨-q, by rw [map_neg, h]⟩
  · rintro x y _ _ ⟨q1, h1⟩ ⟨q2, h2⟩
    exact ⟨q1 * q2, by rw [map_mul, h1, h2]⟩

end Gen

end PSGen

end Work.DSSEC
