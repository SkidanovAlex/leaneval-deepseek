import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.Algebra.MvPolynomial.exists_polynomial_ncard_notMem

open MvPolynomial
open scoped MonomialOrder

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option linter.style.longLine false

namespace Commons.RingTheory.Ideal.Hilbert

variable {k : Type} [Field k] {n : ℕ}

/-- The set of "standard monomials" of degree `t` for `I`: monomials of total degree `t` that
are not divisible by the leading monomial (w.r.t. `degLex`) of any nonzero element of `I`. -/
def stdSet (I : Ideal (MvPolynomial (Fin n) k)) (t : ℕ) : Set (Fin n →₀ ℕ) :=
  {c | c.degree = t ∧ ∀ b ∈ I, b ≠ 0 → ¬ (MonomialOrder.degLex.degree b ≤ c)}

/-- **Macaulay's theorem.** The dimension of the degree-`t` piece of `R ⧸ I` equals the number of
standard monomials of degree `t`. -/
theorem finrank_homogeneous_quotient_eq_ncard_standard
    (I : Ideal (MvPolynomial (Fin n) k))
    (hI : ∀ x ∈ I, ∀ j, MvPolynomial.homogeneousComponent j x ∈ I) (t : ℕ) :
    Module.finrank k (Submodule.map (I.mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin n) k t))
      = Set.ncard {c : Fin n →₀ ℕ | c.degree = t ∧ ∀ b ∈ I, b ≠ 0 →
          ¬ (MonomialOrder.degLex.degree b ≤ c)} := by
  classical
  rw [← stdSet]
  set Std : Set (Fin n →₀ ℕ) := stdSet I t with hStd
  have hStdfin : Set.Finite Std :=
    (Finsupp.finite_of_degree_eq (σ := Fin n) t).subset (fun c hc => hc.1)
  haveI : Fintype Std := hStdfin.fintype
  let q : MvPolynomial (Fin n) k →ₗ[k] MvPolynomial (Fin n) k ⧸ I := I.mkQ.restrictScalars k
  have hq : ∀ x, q x = I.mkQ x := fun x => rfl
  set W : Submodule k (MvPolynomial (Fin n) k) :=
    Submodule.span k (Set.range (fun c : Std => MvPolynomial.monomial c.1 (1 : k))) with hW
  -- linear independence of the images of the standard monomials in the quotient
  have hlin : LinearIndependent k
      (fun c : Std => q (MvPolynomial.monomial c.1 (1 : k))) := by
    rw [Fintype.linearIndependent_iff]
    intro g hsum
    set v : MvPolynomial (Fin n) k := ∑ c : Std, g c • MvPolynomial.monomial c.1 (1 : k) with hv
    have hmem : v ∈ I := by
      have h : q v = 0 := by rw [hv]; rw [map_sum]; simpa using hsum
      rw [hq, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
      exact h
    by_contra hg
    obtain ⟨c₀, hc₀⟩ := not_forall.mp hg
    have hcoeff : MvPolynomial.coeff c₀.1 v = g c₀ := by
      rw [hv, MvPolynomial.coeff_sum]
      simp only [MvPolynomial.coeff_smul, smul_eq_mul, MvPolynomial.coeff_monomial]
      rw [Finset.sum_eq_single c₀]
      · simp
      · intro c _ hc
        rw [if_neg (fun h => hc (Subtype.ext h)), mul_zero]
      · intro h; exact absurd (Finset.mem_univ c₀) h
    have hvne : v ≠ 0 := by
      intro h0
      rw [h0, MvPolynomial.coeff_zero] at hcoeff
      exact hc₀ hcoeff.symm
    have hsupport : ∀ d ∈ v.support, ∃ c : Std, c.1 = d := by
      intro d hd
      rw [MvPolynomial.mem_support_iff] at hd
      by_contra hcon
      rw [not_exists] at hcon
      apply hd
      rw [hv, MvPolynomial.coeff_sum]
      apply Finset.sum_eq_zero
      intro c _
      rw [MvPolynomial.coeff_smul, smul_eq_mul]
      rw [show MvPolynomial.coeff d (MvPolynomial.monomial c.1 (1 : k)) = 0 from ?_, mul_zero]
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro h; exact hcon c h
    obtain ⟨c₁, hc₁⟩ : ∃ c : Std, c.1 = MonomialOrder.degLex.degree v := by
      refine hsupport _ ?_
      rw [MonomialOrder.degree_mem_support_iff]; exact hvne
    exact c₁.2.2 v hmem hvne (by rw [hc₁])
  have hmapW : Submodule.map q W =
      Submodule.span k (Set.range (fun c : Std => q (MvPolynomial.monomial c.1 (1 : k)))) := by
    rw [hW, Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩; exact ⟨c, rfl⟩
    · rintro ⟨c, rfl⟩; exact ⟨_, ⟨c, rfl⟩, rfl⟩
  have hfrW : Module.finrank k ↥(Submodule.map q W) = Std.ncard := by
    rw [hmapW, finrank_span_eq_card hlin]
    rw [Set.ncard_eq_toFinset_card Std hStdfin, hStdfin.card_toFinset]
  -- `W` consists of homogeneous polynomials of degree `t`
  have hWle : W ≤ MvPolynomial.homogeneousSubmodule (Fin n) k t := by
    rw [hW]
    refine Submodule.span_le.mpr ?_
    rintro x ⟨c, rfl⟩
    exact MvPolynomial.mem_homogeneousSubmodule t _ |>.mpr
      (MvPolynomial.isHomogeneous_monomial (1 : k) c.2.1)
  have hle : Submodule.map q (MvPolynomial.homogeneousSubmodule (Fin n) k t) ≤
      Submodule.map q W := by
    rintro y ⟨f, hf, rfl⟩
    have hB : ∀ b ∈ ({b : MvPolynomial (Fin n) k | b ∈ I ∧ b ≠ 0} : Set _),
        IsUnit (MonomialOrder.degLex.leadingCoeff b) := fun b hb =>
      isUnit_iff_ne_zero.mpr (MonomialOrder.leadingCoeff_ne_zero_iff.mpr hb.2)
    obtain ⟨g, r, hgr, hdeg, hstd⟩ := MonomialOrder.div_set (m := MonomialOrder.degLex)
      (R := k) (B := {b : MvPolynomial (Fin n) k | b ∈ I ∧ b ≠ 0}) hB f
    refine Submodule.mem_map.mpr ⟨MvPolynomial.homogeneousComponent t r, ?_, ?_⟩
    · rw [hW]
      rw [MvPolynomial.homogeneousComponent_apply]
      refine Submodule.sum_mem _ (fun d hd => ?_)
      rw [Finset.mem_filter] at hd
      obtain ⟨hdmem, hddeg⟩ := hd
      rw [show MvPolynomial.monomial d (MvPolynomial.coeff d r) =
        (MvPolynomial.coeff d r) • MvPolynomial.monomial d (1 : k) from by
          rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨d, hddeg, ?_⟩, rfl⟩)
      intro b hb hbne
      exact hstd d hdmem b ⟨hb, hbne⟩
    · rw [hq, hq, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      have hfr : f - r ∈ I := by
        rw [hgr, add_sub_cancel_right, Finsupp.linearCombination_apply]
        exact I.sum_mem (fun b _ => I.smul_mem (g b) b.2.1)
      have h2 : MvPolynomial.homogeneousComponent t (f - r) ∈ I := hI _ hfr t
      rw [map_sub, MvPolynomial.homogeneousComponent_eq_self
        (MvPolynomial.mem_homogeneousSubmodule t f |>.mp hf)] at h2
      simpa using I.neg_mem h2
  have hEq : Submodule.map q W = Submodule.map q (MvPolynomial.homogeneousSubmodule (Fin n) k t) :=
    le_antisymm (Submodule.map_mono hWle) hle
  rw [← hEq]
  exact hfrW

/-- The Hilbert function of the quotient of a polynomial ring by a homogeneous ideal is
eventually given by a polynomial with rational coefficients. -/
theorem exists_hilbertPoly_homogeneous_quotient {k : Type} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (hI : ∀ x ∈ I, ∀ j, MvPolynomial.homogeneousComponent j x ∈ I) :
    ∃ p : Polynomial ℚ, ∃ N : ℕ, ∀ t : ℕ, N ≤ t →
      (Module.finrank k (Submodule.map (I.mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin n) k t)) : ℚ) = p.eval (t : ℚ) := by
  obtain ⟨p, N, hp⟩ := Commons.Algebra.MvPolynomial.exists_polynomial_ncard_notMem n
    {b : Fin n →₀ ℕ | ∃ x ∈ I, x ≠ 0 ∧ MonomialOrder.degLex.degree x = b}
  refine ⟨p, N, fun t ht => ?_⟩
  have hset : {c : Fin n →₀ ℕ | c.degree = t ∧ ∀ b ∈ I, b ≠ 0 →
        ¬ (MonomialOrder.degLex.degree b ≤ c)}
      = {c : Fin n →₀ ℕ | c.degree = t ∧
          ∀ s ∈ ({b : Fin n →₀ ℕ | ∃ x ∈ I, x ≠ 0 ∧ MonomialOrder.degLex.degree x = b} : Set _),
            ¬ (s ≤ c)} := by
    ext c
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun s hs => by
        obtain ⟨x, hx, hxne, rfl⟩ := hs
        exact h2 x hx hxne⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun b hb hbne => h2 (MonomialOrder.degLex.degree b) ⟨b, hb, hbne, rfl⟩⟩
  rw [finrank_homogeneous_quotient_eq_ncard_standard I hI t, hset]
  exact hp t ht

end Commons.RingTheory.Ideal.Hilbert