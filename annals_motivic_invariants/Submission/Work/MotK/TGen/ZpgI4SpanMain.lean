import Mathlib
import Submission.Work.MotK.TGen.ZpgI4W4NonZeroDiv
import Submission.Work.MotK.TGen.ZpgI4MonoOrderU
import Submission.Work.MotK.TGen.ZpgI4NInterI

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.ZpgI4SpanMain`

The chart ideal `zpgI4 a b h` of the twisted Klein curve is spanned, as a `K[X₃]`-module, by the
five standard monomials `1, X₀, X₁, X₂, X₀X₂`.

The proof is a *division-algorithm* argument: the monomial order of
`Work.MotK.TGen.ZpgI4MonoOrderU` has leading monomials `X₁X₂, X₁², X₀X₁, X₀², X₂²` for the
five chart quadrics (none of them involving `X₃`), so the standard monomials — the monomials
divisible by none of these five — are precisely

  `X₀ᵉ⁰ X₁ᵉ¹ X₂ᵉ² X₃ᵉ³` with `(e₀,e₁,e₂) ∈ {(0,0,0),(1,0,0),(0,1,0),(0,0,1),(1,0,1)}`,

i.e. a power of `X₃` times one of `1, X₀, X₁, X₂, X₀X₂`.  Dividing `f` by the five quadrics gives
`f - r ∈ zpgI4` with `r` a `K`-combination of standard monomials; collecting the coefficient of
each of the five shapes into a polynomial in `X₃` exhibits `r` in the required form.
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Work.MotK.TGen

open MvPolynomial

/-! ## 1. The five reduced monomial shapes -/

/-- The exponent vectors of the five standard monomials `1, X₀, X₁, X₂, X₀X₂`. -/
noncomputable def zpgShapeExp : Fin 5 → (Fin 4 →₀ ℕ) :=
  ![0, Finsupp.single 0 1, Finsupp.single 1 1, Finsupp.single 2 1,
    Finsupp.single 0 1 + Finsupp.single 2 1]

/-- The exponent vectors of the leading monomials of the five chart quadrics `zpgQ a b h k`, in
the monomial order of `Work.MotK.TGen.ZpgI4MonoOrderU` (the same order as `zpgQ`'s index). -/
noncomputable def zpgLTe : Fin 5 → (Fin 4 →₀ ℕ)
  | 0 => Finsupp.single 1 1 + Finsupp.single 2 1
  | 1 => Finsupp.single 1 2
  | 2 => Finsupp.single 0 1 + Finsupp.single 1 1
  | 3 => Finsupp.single 0 2
  | 4 => Finsupp.single 2 2

/-- An exponent is *reduced* (a standard monomial) when it is divisible by none of the five
leading monomials. -/
def IsRed (c : Fin 4 →₀ ℕ) : Prop := ∀ k : Fin 5, ¬ (zpgLTe k ≤ c)

/-- The shape index of a reduced exponent: which of `1, X₀, X₁, X₂, X₀X₂` it is (up to the
power of `X₃`). -/
def zpgShapeIdx (c : Fin 4 →₀ ℕ) : Fin 5 :=
  if c 1 = 1 then 2 else if c 0 = 1 then (if c 2 = 1 then 4 else 1) else (if c 2 = 1 then 3 else 0)

/-! ## 2. Combinatorics of the reduced exponents -/

theorem one_one_add_le_iff (c : Fin 4 →₀ ℕ) :
    (Finsupp.single (0 : Fin 4) 1 + Finsupp.single 1 1 ≤ c) ↔ 1 ≤ c 0 ∧ 1 ≤ c 1 := by
  rw [Finsupp.le_def]
  constructor
  · intro h
    exact ⟨by have := h 0; simpa using this, by have := h 1; simpa using this⟩
  · intro h i
    fin_cases i <;> simp_all [Finsupp.add_apply]

theorem one_two_add_le_iff (c : Fin 4 →₀ ℕ) :
    (Finsupp.single (1 : Fin 4) 1 + Finsupp.single 2 1 ≤ c) ↔ 1 ≤ c 1 ∧ 1 ≤ c 2 := by
  rw [Finsupp.le_def]
  constructor
  · intro h
    exact ⟨by have := h 1; simpa using this, by have := h 2; simpa using this⟩
  · intro h i
    fin_cases i <;> simp_all [Finsupp.add_apply]

/-- A combinatorial description of the reduced exponents: each of `c 0, c 1, c 2` is `0` or `1`,
and `c 0, c 1` are not both `1`, nor are `c 1, c 2`. -/
theorem isRed_iff (c : Fin 4 →₀ ℕ) :
    IsRed c ↔ c 0 ≤ 1 ∧ c 1 ≤ 1 ∧ c 2 ≤ 1 ∧ (c 0 = 0 ∨ c 1 = 0) ∧ (c 1 = 0 ∨ c 2 = 0) := by
  constructor
  · intro h
    have h0 : c 0 ≤ 1 := by
      have h3 : ¬ ((Finsupp.single (0 : Fin 4) 2 : Fin 4 →₀ ℕ) ≤ c) := h 3
      rw [Finsupp.single_le_iff] at h3
      omega
    have h1 : c 1 ≤ 1 := by
      have h1' : ¬ ((Finsupp.single (1 : Fin 4) 2 : Fin 4 →₀ ℕ) ≤ c) := h 1
      rw [Finsupp.single_le_iff] at h1'
      omega
    have h2 : c 2 ≤ 1 := by
      have h4 : ¬ ((Finsupp.single (2 : Fin 4) 2 : Fin 4 →₀ ℕ) ≤ c) := h 4
      rw [Finsupp.single_le_iff] at h4
      omega
    have h01 : c 0 = 0 ∨ c 1 = 0 := by
      have h2' : ¬ (Finsupp.single (0 : Fin 4) 1 + Finsupp.single 1 1 ≤ c) := h 2
      rw [one_one_add_le_iff] at h2'
      omega
    have h12 : c 1 = 0 ∨ c 2 = 0 := by
      have h0' : ¬ (Finsupp.single (1 : Fin 4) 1 + Finsupp.single 2 1 ≤ c) := h 0
      rw [one_two_add_le_iff] at h0'
      omega
    exact ⟨h0, h1, h2, h01, h12⟩
  · rintro ⟨h0, h1, h2, h01, h12⟩ k
    fin_cases k
    · show ¬ ((Finsupp.single (1 : Fin 4) 1 + Finsupp.single 2 1 : Fin 4 →₀ ℕ) ≤ c)
      rw [one_two_add_le_iff]; omega
    · show ¬ ((Finsupp.single (1 : Fin 4) 2 : Fin 4 →₀ ℕ) ≤ c)
      rw [Finsupp.single_le_iff]; omega
    · show ¬ ((Finsupp.single (0 : Fin 4) 1 + Finsupp.single 1 1 : Fin 4 →₀ ℕ) ≤ c)
      rw [one_one_add_le_iff]; omega
    · show ¬ ((Finsupp.single (0 : Fin 4) 2 : Fin 4 →₀ ℕ) ≤ c)
      rw [Finsupp.single_le_iff]; omega
    · show ¬ ((Finsupp.single (2 : Fin 4) 2 : Fin 4 →₀ ℕ) ≤ c)
      rw [Finsupp.single_le_iff]; omega

/-- Every reduced exponent is the exponent of `X₃^{c 3}` times one of the five shapes. -/
theorem shape_of_isRed {c : Fin 4 →₀ ℕ} (hc : IsRed c) :
    c = Finsupp.single 3 (c 3) + zpgShapeExp (zpgShapeIdx c) := by
  obtain ⟨h0, h1, h2, h01, h12⟩ := (isRed_iff c).mp hc
  ext i
  fin_cases i <;> simp only [Finsupp.add_apply, zpgShapeExp, zpgShapeIdx] <;>
    split_ifs <;> simp_all <;> omega

/-! ## 3. The standard monomials and the reduced monomials -/

/-- The five standard monomials are the monomials of the five shape exponents. -/
theorem zpgStdM_eq_monomial {K : Type} [CommSemiring K] (k : Fin 5) :
    zpgStdM (K := K) k = MvPolynomial.monomial (zpgShapeExp k) 1 := by
  fin_cases k <;>
    simp [zpgShapeExp, zpgStdM, MvPolynomial.X, MvPolynomial.monomial_mul_monomial]

/-- A reduced monomial is a standard monomial with a coefficient in `K[X₃]`. -/
theorem monomial_reduced {K : Type} [CommSemiring K] {c : Fin 4 →₀ ℕ} (hc : IsRed c) (x : K) :
    MvPolynomial.monomial c x
      = zpgEmb K (MvPolynomial.monomial (Finsupp.single (0 : Fin 1) (c 3)) x)
        * zpgStdM (K := K) (zpgShapeIdx c) := by
  have hsplit : MvPolynomial.monomial c x
      = MvPolynomial.monomial (Finsupp.single (3 : Fin 4) (c 3)) x
        * MvPolynomial.monomial (zpgShapeExp (zpgShapeIdx c)) (1 : K) := by
    conv_lhs => rw [shape_of_isRed hc]
    rw [MvPolynomial.monomial_mul_monomial, mul_one]
  rw [hsplit, zpgStdM_eq_monomial]
  congr 1
  show MvPolynomial.monomial (Finsupp.single (3 : Fin 4) (c 3)) x
      = zpgEmb K (MvPolynomial.monomial (Finsupp.single (0 : Fin 1) (c 3)) x)
  rw [show zpgEmb K = MvPolynomial.rename (fun _ : Fin 1 => (3 : Fin 4)) from rfl]
  rw [MvPolynomial.rename_monomial, Finsupp.mapDomain_single]

/-! ## 4. The `K`-linear span map and its range -/

/-- The `K`-linear map `(g₀,…,g₄) ↦ ∑ᵢ gᵢ(X₃)·Sᵢ` whose range is the `K[X₃]`-span of the five
standard monomials. -/
noncomputable def zpgSpanMap (K : Type) [CommSemiring K] :
    (Fin 5 → MvPolynomial (Fin 1) K) →ₗ[K] MvPolynomial (Fin 4) K where
  toFun g := ∑ i : Fin 5, zpgEmb K (g i) * zpgStdM (K := K) i
  map_add' g g' := by
    simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' a g := by
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_mul_assoc]

/-- Every `K`-combination of reduced monomials lies in the range of `zpgSpanMap`. -/
theorem mem_range_zpgSpanMap {K : Type} [Field K] {P : MvPolynomial (Fin 4) K}
    (hP : ∀ c ∈ P.support, IsRed c) : P ∈ LinearMap.range (zpgSpanMap K) := by
  rw [MvPolynomial.as_sum P]
  refine Submodule.sum_mem _ fun c hc => ?_
  have hc' : IsRed c := hP c hc
  refine ⟨fun i => if zpgShapeIdx c = i then
      MvPolynomial.monomial (Finsupp.single (0 : Fin 1) (c 3)) (P.coeff c) else 0, ?_⟩
  rw [monomial_reduced hc' (P.coeff c)]
  change (∑ i : Fin 5, zpgEmb K
      (if zpgShapeIdx c = i then
        MvPolynomial.monomial (Finsupp.single (0 : Fin 1) (c 3)) (P.coeff c) else 0)
        * zpgStdM (K := K) i)
    = zpgEmb K (MvPolynomial.monomial (Finsupp.single (0 : Fin 1) (c 3)) (P.coeff c))
        * zpgStdM (K := K) (zpgShapeIdx c)
  have hsingle := Fintype.sum_eq_single (f := fun i : Fin 5 => zpgEmb K
      (if zpgShapeIdx c = i then
        MvPolynomial.monomial (Finsupp.single (0 : Fin 1) (c 3)) (P.coeff c) else 0)
        * zpgStdM (K := K) i) (zpgShapeIdx c) (fun i hi => by
      rw [ite_eq_right (fun hh => hi hh.symm), map_zero, zero_mul])
  simpa using hsingle

/-! ## 5. The spanning theorem -/

theorem ZpgI4SpanMain (K : Type) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0)
    (f : MvPolynomial (Fin 4) K) :
    ∃ g : Fin 5 → MvPolynomial (Fin 1) K,
      f - (Work.MotK.TGen.zpgEmb K (g 0)
        + Work.MotK.TGen.zpgEmb K (g 1) * (MvPolynomial.X 0 : MvPolynomial (Fin 4) K)
        + Work.MotK.TGen.zpgEmb K (g 2) * MvPolynomial.X 1
        + Work.MotK.TGen.zpgEmb K (g 3) * MvPolynomial.X 2
        + Work.MotK.TGen.zpgEmb K (g 4) * (MvPolynomial.X 0 * MvPolynomial.X 2))
      ∈ Work.MotK.TGen.zpgI4 a b h := by
  classical
  obtain ⟨m, hmunit, hd0, hd1, hd2, hd3, hd4⟩ := ZpgI4MonoOrderU.{0} K a b h ha hb hh
  obtain ⟨q, r, hqr, -, hrred⟩ := MonomialOrder.div (m := m) hmunit f
  -- The exponents of `r` are reduced.
  have hLTe : ∀ k : Fin 5, zpgLTe k = m.degree (zpgQ a b h k) := by
    intro k
    fin_cases k
    · exact hd0.symm
    · exact hd1.symm
    · exact hd2.symm
    · exact hd3.symm
    · exact hd4.symm
  have hred : ∀ c ∈ r.support, IsRed c := by
    intro c hc k
    have h := hrred c hc k
    rw [hLTe k]
    exact h
  -- `f - r` lies in the ideal.
  have hmem : f - r ∈ zpgI4 a b h := by
    have hfe : f - r = Finsupp.linearCombination (MvPolynomial (Fin 4) K) (zpgQ a b h) q := by
      rw [hqr]; abel
    rw [hfe, zpgI4, Finsupp.linearCombination_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_mem _ _ (Ideal.subset_span (Set.mem_range_self i))
  -- `r` is a combination of the five standard monomials.
  obtain ⟨g, hg⟩ := LinearMap.mem_range.mp (mem_range_zpgSpanMap hred)
  refine ⟨g, ?_⟩
  have hexp : zpgEmb K (g 0) + zpgEmb K (g 1) * (X 0 : MvPolynomial (Fin 4) K)
      + zpgEmb K (g 2) * X 1 + zpgEmb K (g 3) * X 2 + zpgEmb K (g 4) * (X 0 * X 2) = r := by
    rw [← zpgSum_eq g]
    exact hg
  rw [hexp]
  exact hmem

end Work.MotK.TGen
