import Mathlib
import Submission.Work.MotK.TGen.ZTwistDivGeomDefs
import Submission.Work.MotK.TGen.ZpgI4MonoOrderU
import Submission.Work.MotK.TGen.ZpgI4NInterI
import Submission.Work.MotK.TGen.ZpgW4NonZeroDivMain

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.ZpgI4NormalForm`

Normal form for the chart ideal `zpgI4 a b h` of the twisted Klein curve with respect to a
monomial order whose leading monomials are the five `X₀², X₀X₁, X₁², X₁X₂, X₂²`.

The existence of the order is `Work.MotK.TGen.ZpgI4MonoOrderU`.  The two algebraic inputs are

* `Work.MotK.TGen.ZpgI4NInterI` : no nonzero element whose support avoids the five leading
  monomials lies in the ideal (the Gröbner property for that order);
* `Work.MotK.TGen.ZpgI4W4NonZeroDiv` : `zpgW4` is a non-zero-divisor modulo the ideal.

The normal form itself is provided by Mathlib's division algorithm (`MonomialOrder.div`); it is
*linear* because the "reduced" representative of a residue class is unique.
-/

set_option maxHeartbeats 2000000
set_option autoImplicit false

namespace Work.MotK.TGen

open MvPolynomial

/-- The five monomials `X₀², X₀X₁, X₁², X₁X₂, X₂²` which are the leading monomials of the five
chart quadrics for the order of `ZpgI4MonoOrder`. -/
noncomputable def zpgStd : Fin 5 → (Fin 4 →₀ ℕ) :=
  ![Finsupp.single 0 2, Finsupp.single 0 1 + Finsupp.single 1 1, Finsupp.single 1 2,
    Finsupp.single 1 1 + Finsupp.single 2 1, Finsupp.single 2 2]

/-- An exponent `c` is *reduced* when it is divisible by none of the five leading monomials. -/
def IsZpgReduced (c : Fin 4 →₀ ℕ) : Prop :=
  ∀ k : Fin 5, ¬ (zpgStd k ≤ c)

theorem isZpgReduced_iff (c : Fin 4 →₀ ℕ) :
    IsZpgReduced c ↔
      (¬ ((Finsupp.single 0 2 : Fin 4 →₀ ℕ) ≤ c) ∧
       ¬ ((Finsupp.single 0 1 + Finsupp.single 1 1 : Fin 4 →₀ ℕ) ≤ c) ∧
       ¬ ((Finsupp.single 1 2 : Fin 4 →₀ ℕ) ≤ c) ∧
       ¬ ((Finsupp.single 1 1 + Finsupp.single 2 1 : Fin 4 →₀ ℕ) ≤ c) ∧
       ¬ ((Finsupp.single 2 2 : Fin 4 →₀ ℕ) ≤ c)) := by
  unfold IsZpgReduced zpgStd
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2,
      by simpa using h 3, by simpa using h 4⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ k
    fin_cases k
    · simpa using h0
    · simpa using h1
    · simpa using h2
    · simpa using h3
    · simpa using h4

theorem zpgRed_iff {K : Type} [Field K] (a b h : K) {m : MonomialOrder (Fin 4)}
    (hd0 : m.degree (Work.MotK.TGen.zpgQ a b h 0)
      = (Finsupp.single 1 1 + Finsupp.single 2 1 : Fin 4 →₀ ℕ))
    (hd1 : m.degree (Work.MotK.TGen.zpgQ a b h 1) = (Finsupp.single 1 2 : Fin 4 →₀ ℕ))
    (hd2 : m.degree (Work.MotK.TGen.zpgQ a b h 2)
      = (Finsupp.single 0 1 + Finsupp.single 1 1 : Fin 4 →₀ ℕ))
    (hd3 : m.degree (Work.MotK.TGen.zpgQ a b h 3) = (Finsupp.single 0 2 : Fin 4 →₀ ℕ))
    (hd4 : m.degree (Work.MotK.TGen.zpgQ a b h 4) = (Finsupp.single 2 2 : Fin 4 →₀ ℕ))
    (c : Fin 4 →₀ ℕ) :
    (∀ k : Fin 5, ¬ (m.degree (Work.MotK.TGen.zpgQ a b h k) ≤ c)) ↔ IsZpgReduced c := by
  rw [isZpgReduced_iff]
  constructor
  · intro h
    exact ⟨by rw [← hd3]; exact h 3, by rw [← hd2]; exact h 2, by rw [← hd1]; exact h 1,
      by rw [← hd0]; exact h 0, by rw [← hd4]; exact h 4⟩
  · intro h k
    have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by fin_cases k <;> simp
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · simpa only [hd0] using h.2.2.2.1
    · simpa only [hd1] using h.2.2.1
    · simpa only [hd2] using h.2.1
    · simpa only [hd3] using h.1
    · simpa only [hd4] using h.2.2.2.2

theorem ZpgI4NormalForm (K : Type) [Field K] (a b h : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    ∃ (m : MonomialOrder.{0, 0} (Fin 4))
      (NF : MvPolynomial (Fin 4) K →ₗ[K] MvPolynomial (Fin 4) K),
      (∀ k : Fin 5, IsUnit (m.leadingCoeff (Work.MotK.TGen.zpgQ a b h k))) ∧
      (m.degree (Work.MotK.TGen.zpgQ a b h 0)
        = (Finsupp.single 1 1 + Finsupp.single 2 1 : Fin 4 →₀ ℕ)) ∧
      (m.degree (Work.MotK.TGen.zpgQ a b h 1)
        = (Finsupp.single 1 2 : Fin 4 →₀ ℕ)) ∧
      (m.degree (Work.MotK.TGen.zpgQ a b h 2)
        = (Finsupp.single 0 1 + Finsupp.single 1 1 : Fin 4 →₀ ℕ)) ∧
      (m.degree (Work.MotK.TGen.zpgQ a b h 3)
        = (Finsupp.single 0 2 : Fin 4 →₀ ℕ)) ∧
      (m.degree (Work.MotK.TGen.zpgQ a b h 4)
        = (Finsupp.single 2 2 : Fin 4 →₀ ℕ)) ∧
      (∀ f : MvPolynomial (Fin 4) K,
        f - NF f ∈ Work.MotK.TGen.zpgI4 a b h) ∧
      (∀ f : MvPolynomial (Fin 4) K,
        f ∈ Work.MotK.TGen.zpgI4 a b h → NF f = 0) ∧
      (∀ f : MvPolynomial (Fin 4) K, ∀ c ∈ (NF f).support, ∀ k : Fin 5,
        ¬ (m.degree (Work.MotK.TGen.zpgQ a b h k) ≤ c)) ∧
      (∀ n : MvPolynomial (Fin 4) K,
        (∀ c ∈ n.support, ∀ k : Fin 5,
          ¬ (m.degree (Work.MotK.TGen.zpgQ a b h k) ≤ c)) →
        n ≠ 0 → NF (Work.MotK.TGen.zpgW4 a b h * n) ≠ 0) := by
  classical
  obtain ⟨m, hmunit, hd0, hd1, hd2, hd3, hd4⟩ := ZpgI4MonoOrderU K a b h ha hb hh
  have hRred : ∀ c : Fin 4 →₀ ℕ,
      ((∀ k : Fin 5, ¬ (m.degree (Work.MotK.TGen.zpgQ a b h k) ≤ c)) ↔ IsZpgReduced c) :=
    zpgRed_iff a b h hd0 hd1 hd2 hd3 hd4
  -- Existence of a reduced representative modulo the ideal (Mathlib's division algorithm).
  have hex : ∀ f : MvPolynomial (Fin 4) K, ∃ r : MvPolynomial (Fin 4) K,
      f - r ∈ Work.MotK.TGen.zpgI4 a b h ∧
        ∀ c ∈ r.support, ∀ k : Fin 5, ¬ (m.degree (Work.MotK.TGen.zpgQ a b h k) ≤ c) := by
    intro f
    obtain ⟨g, r, hgr, -, hrred⟩ := MonomialOrder.div hmunit f
    refine ⟨r, ?_, hrred⟩
    have hfe : f - r = Finsupp.linearCombination (MvPolynomial (Fin 4) K)
        (Work.MotK.TGen.zpgQ a b h) g := by
      rw [hgr]; abel
    rw [hfe, Work.MotK.TGen.zpgI4, Finsupp.linearCombination_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_mem _ _ (Ideal.subset_span (Set.mem_range_self i))
  -- The (noncomputable) normal form.
  let NF₀ : MvPolynomial (Fin 4) K → MvPolynomial (Fin 4) K :=
    fun f => Classical.choose (hex f)
  have hNF₀sub : ∀ f : MvPolynomial (Fin 4) K,
      f - NF₀ f ∈ Work.MotK.TGen.zpgI4 a b h := fun f =>
    (Classical.choose_spec (hex f)).1
  have hNF₀red : ∀ f : MvPolynomial (Fin 4) K, ∀ c ∈ (NF₀ f).support, ∀ k : Fin 5,
      ¬ (m.degree (Work.MotK.TGen.zpgQ a b h k) ≤ c) := fun f =>
    (Classical.choose_spec (hex f)).2
  -- Uniqueness of the reduced representative.
  have huniq : ∀ (f r r' : MvPolynomial (Fin 4) K),
      f - r ∈ Work.MotK.TGen.zpgI4 a b h →
        (∀ c ∈ r.support, ∀ k : Fin 5, ¬ (m.degree (Work.MotK.TGen.zpgQ a b h k) ≤ c)) →
      f - r' ∈ Work.MotK.TGen.zpgI4 a b h →
        (∀ c ∈ r'.support, ∀ k : Fin 5, ¬ (m.degree (Work.MotK.TGen.zpgQ a b h k) ≤ c)) →
      r = r' := by
    intro f r r' hr hrr hr' hr'r
    have hmem : r - r' ∈ Work.MotK.TGen.zpgI4 a b h := by
      have hsplit : r - r' = (f - r') - (f - r) := by abel
      rw [hsplit]
      exact Submodule.sub_mem _ hr' hr
    have hredr : ∀ c ∈ (r - r').support, IsZpgReduced c := by
      intro c hc
      have hcn : (r - r').coeff c ≠ 0 := MvPolynomial.mem_support_iff.mp hc
      have hcases : c ∈ r.support ∨ c ∈ r'.support := by
        by_contra hcon
        rw [not_or] at hcon
        exact hcn (by
          rw [MvPolynomial.coeff_sub, MvPolynomial.notMem_support_iff.mp hcon.1,
            MvPolynomial.notMem_support_iff.mp hcon.2, sub_zero])
      rcases hcases with hc' | hc'
      · exact (hRred c).mp (hrr c hc')
      · exact (hRred c).mp (hr'r c hc')
    have h0 := ZpgI4NInterI K a b h ha hb hh (r - r')
      (fun c hc => (isZpgReduced_iff c).mp (hredr c hc)) hmem
    exact sub_eq_zero.mp h0
  -- `NF₀` vanishes on the ideal.
  have hNF₀zero : ∀ f : MvPolynomial (Fin 4) K,
      f ∈ Work.MotK.TGen.zpgI4 a b h → NF₀ f = 0 := by
    intro f hf
    symm
    refine huniq f 0 (NF₀ f) ?_ ?_ (hNF₀sub f) (hNF₀red f)
    · simpa using hf
    · intro c hc
      simp at hc
  -- Additivity.
  have hNF₀add : ∀ f g : MvPolynomial (Fin 4) K, NF₀ (f + g) = NF₀ f + NF₀ g := by
    intro f g
    symm
    refine huniq (f + g) (NF₀ f + NF₀ g) (NF₀ (f + g)) ?_ ?_ (hNF₀sub (f + g))
      (hNF₀red (f + g))
    · have hsplit : f + g - (NF₀ f + NF₀ g) = (f - NF₀ f) + (g - NF₀ g) := by abel
      rw [hsplit]
      exact Submodule.add_mem _ (hNF₀sub f) (hNF₀sub g)
    · intro c hc
      have hcn : (NF₀ f + NF₀ g).coeff c ≠ 0 := MvPolynomial.mem_support_iff.mp hc
      have hcases : c ∈ (NF₀ f).support ∨ c ∈ (NF₀ g).support := by
        by_contra hcon
        rw [not_or] at hcon
        exact hcn (by
          rw [MvPolynomial.coeff_add, MvPolynomial.notMem_support_iff.mp hcon.1,
            MvPolynomial.notMem_support_iff.mp hcon.2, add_zero])
      rcases hcases with hc' | hc'
      · exact hNF₀red f c hc'
      · exact hNF₀red g c hc'
  -- Homogeneity.
  have hNF₀smul : ∀ (c : K) (f : MvPolynomial (Fin 4) K), NF₀ (c • f) = c • NF₀ f := by
    intro c f
    symm
    refine huniq (c • f) (c • NF₀ f) (NF₀ (c • f)) ?_ ?_ (hNF₀sub (c • f)) (hNF₀red (c • f))
    · rw [← smul_sub, MvPolynomial.smul_eq_C_mul]
      exact Ideal.mul_mem_left _ (MvPolynomial.C c) (hNF₀sub f)
    · intro d hd
      by_cases hc : c = 0
      · subst hc
        simp at hd
      · have hdn : (c • NF₀ f).coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
        have : d ∈ (NF₀ f).support := by
          by_contra hcon
          refine hdn ?_
          rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.coeff_C_mul,
            MvPolynomial.notMem_support_iff.mp hcon, mul_zero]
        exact hNF₀red f d this
  refine ⟨m, ?_, hmunit, hd0, hd1, hd2, hd3, hd4, ?_, ?_, ?_, ?_⟩
  · exact { toFun := NF₀, map_add' := hNF₀add, map_smul' := hNF₀smul }
  · intro f
    exact hNF₀sub f
  · intro f hf
    exact hNF₀zero f hf
  · intro f c hc
    exact hNF₀red f c hc
  · intro n hn hn0 hcontra
    have hmem : Work.MotK.TGen.zpgW4 a b h * n ∈ Work.MotK.TGen.zpgI4 a b h := by
      have hW := hNF₀sub (Work.MotK.TGen.zpgW4 a b h * n)
      have hc0 : NF₀ (Work.MotK.TGen.zpgW4 a b h * n) = 0 := hcontra
      rw [hc0] at hW
      simpa using hW
    have hnin : n ∈ Work.MotK.TGen.zpgI4 a b h :=
      ZpgI4W4NonZeroDiv K a b h ha hb hh n hmem
    exact hn0 (ZpgI4NInterI K a b h ha hb hh n
      (fun c hc => (isZpgReduced_iff c).mp ((hRred c).mp (hn c hc))) hnin)

end Work.MotK.TGen
