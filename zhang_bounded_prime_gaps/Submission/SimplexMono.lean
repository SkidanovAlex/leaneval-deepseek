import Mathlib
import Submission.Variational
import Submission.Commons.MeasureTheory.Integral.simplex_integral_scaled

/-!
# Simplex integrals of labelled monomial (symmetric) polynomials

This module formalises the master integral formula underlying the exact
evaluation of the Maynard--Polymath8 variational functionals `M_{k,ε}`
(Polymath8a, Lemma 7.2 and the polynomial basis of Section 7.2).

For a signature `α : List ℕ` (the exponents of a symmetric monomial) and a
dimension `k`, the *labelled monomial sum* is

  `lmono α k t = Σ_{e : Fin α.length ↪ Fin k} ∏ i, t_{e i} ^ (α_i)`,

which is `∏_v (multiplicity of v in α)!` times the monomial symmetric
polynomial `m_α`.  Since the variational quotient `Σ_i J_i / I` is invariant
under rescaling each basis element by a nonzero constant, the labelled version
is an equally good basis; it has the advantage of being built from injective
placements, which makes the combinatorics of the following theorem transparent.

The master formula (Polymath8a Lemma 7.2 combined with the symmetric basis) is

  `∫_{c·R^k} (c - Σ t_i)^A · m_α · m_β
     = c^{k + A + |α| + |β|} · A! · S(α,β,k) / (A + |α| + |β| + k)!`

where `S(α,β,k)` is the labelled assignment sum

  `S(α,β,k) = Σ_{e,e'} ∏_c (exp_e c + exp_{e'} c)!`,

`exp_e c` being the total exponent placed at coordinate `c` by the placement
`e`.  In terms of the *distinct* placements used in `Variational.Ssum` this is
`∏_v (mult_v α)! · ∏_w (mult_w β)! · Ssum α β k`.

The proof expands the two finite sums over placements and applies the
one-monomial formula `Commons.MeasureTheory.Integral.simplex_integral_scaled`
term by term (the integrands are polynomials, hence integrable on the compact
simplex).
-/

open MeasureTheory Finset
open scoped BigOperators

namespace Commons.NumberTheory.MaynardSieve

noncomputable section

/-- The scaled simplex `c · R^k = {t ≥ 0 : Σ t_i ≤ c}`. -/
def simplexC (k : ℕ) (c : ℝ) : Set (Fin k → ℝ) :=
  {t | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ c}

/-- The exponent vector of a labelled placement: coordinate `c` receives the sum of
those parts of `α` placed there. -/
def expOf (α : List ℕ) (k : ℕ) (e : Fin α.length ↪ Fin k) : Fin k → ℕ :=
  fun c => ∑ i : Fin α.length, if e i = c then α.get i else 0

/-- The labelled monomial sum `Σ_{e : Fin α.length ↪ Fin k} ∏ i, t_{e i}^{α_i}`;
it equals `∏_v (mult_v α)!` times the monomial symmetric polynomial `m_α`. -/
def lmono (α : List ℕ) (k : ℕ) (t : Fin k → ℝ) : ℝ :=
  ∑ e : Fin α.length ↪ Fin k, ∏ i : Fin α.length, (t (e i)) ^ (α.get i)

/-- The labelled assignment sum `S(α,β,k) = Σ_{e,e'} ∏_c (exp_e c + exp_{e'} c)!`. -/
def Slab (α β : List ℕ) (k : ℕ) : ℕ :=
  ∑ e : Fin α.length ↪ Fin k, ∑ e' : Fin β.length ↪ Fin k,
    ∏ c : Fin k, Nat.factorial (expOf α k e c + expOf β k e' c)


/-- The simplex is closed. -/
lemma isClosed_simplexC (k : ℕ) (c : ℝ) : IsClosed (simplexC k c) := by
  have h : simplexC k c = (⋂ i, {t : Fin k → ℝ | t i ∈ Set.Ici (0:ℝ)})
      ∩ {t : Fin k → ℝ | (∑ i, t i) ∈ Set.Iic c} := by
    ext t
    simp [simplexC, Set.mem_iInter]
  rw [h]
  exact (isClosed_iInter (fun i => isClosed_Ici.preimage (continuous_apply i))).inter
    (isClosed_Iic.preimage (continuous_finset_sum _ (fun i _ => continuous_apply i)))

/-- The simplex is contained in the box `[0,c]^k`. -/
lemma simplexC_subset_box (k : ℕ) (c : ℝ) :
    simplexC k c ⊆ Set.pi Set.univ (fun _ : Fin k => Set.Icc (0:ℝ) c) := by
  intro t ht
  simp only [Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Icc]
  intro i
  exact ⟨ht.1 i, le_trans (Finset.single_le_sum (fun j _ => ht.1 j) (Finset.mem_univ i)) ht.2⟩

/-- The simplex `c·R^k` is compact. -/
lemma isCompact_simplexC (k : ℕ) (c : ℝ) : IsCompact (simplexC k c) :=
  (isCompact_univ_pi (fun _ : Fin k => isCompact_Icc)).of_isClosed_subset
    (isClosed_simplexC k c) (simplexC_subset_box k c)

/-- Monomials are integrable on the simplex. -/
lemma integrableOn_simplexC_poly (k : ℕ) (c : ℝ) (A : ℕ) (b : Fin k → ℕ) :
    IntegrableOn (fun t : Fin k → ℝ => (c - ∑ i, t i)^A * ∏ i, (t i)^(b i))
      (simplexC k c) :=
  ContinuousOn.integrableOn_compact (isCompact_simplexC k c) (by fun_prop)

/-! ## Elementary properties -/

/-- Rearranging a labelled monomial as a product over coordinates. -/
lemma prod_pow_expOf (α : List ℕ) (k : ℕ) (e : Fin α.length ↪ Fin k) (t : Fin k → ℝ) :
    ∏ i : Fin α.length, (t (e i)) ^ (α.get i)
      = ∏ c : Fin k, (t c) ^ (expOf α k e c) := by
  have hinner : ∀ i : Fin α.length,
      ∏ c : Fin k, (t c) ^ (if e i = c then α.get i else 0) = (t (e i)) ^ (α.get i) := by
    intro i
    rw [Finset.prod_eq_single (e i)]
    · simp
    · intro b _ hb
      rw [if_neg (fun h : e i = b => hb h.symm), pow_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  calc ∏ i : Fin α.length, (t (e i)) ^ (α.get i)
      = ∏ i : Fin α.length,
          ∏ c : Fin k, (t c) ^ (if e i = c then α.get i else 0) := by
        refine Finset.prod_congr rfl (fun i _ => ?_)
        rw [hinner i]
    _ = ∏ c : Fin k,
          ∏ i : Fin α.length, (t c) ^ (if e i = c then α.get i else 0) := Finset.prod_comm
    _ = ∏ c : Fin k, (t c) ^ (expOf α k e c) := by
        refine Finset.prod_congr rfl (fun c _ => ?_)
        rw [expOf, ← Finset.prod_pow_eq_pow_sum]

/-- The total degree placed by a labelled placement is the degree of the signature. -/
lemma sum_expOf (α : List ℕ) (k : ℕ) (e : Fin α.length ↪ Fin k) :
    ∑ c : Fin k, expOf α k e c = α.sum := by
  have hinner : ∀ y : Fin α.length,
      (∑ x : Fin k, (if e y = x then α.get y else 0)) = α.get y := by
    intro y
    rw [Finset.sum_eq_single (e y)]
    · simp
    · intro b _ hb
      rw [if_neg (fun h : e y = b => hb h.symm)]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h1 : ∑ c : Fin k, expOf α k e c
      = ∑ c : Fin k, ∑ i : Fin α.length, (if e i = c then α.get i else 0) := rfl
  have h : ∑ c : Fin k, expOf α k e c = ∑ y : Fin α.length, α.get y := by
    rw [h1, Finset.sum_comm]
    exact Finset.sum_congr rfl (fun y _ => hinner y)
  rw [h, ← List.sum_ofFn (f := α.get), List.ofFn_get]

/-! ## The master formula -/

/-- **Master simplex integral formula.**  For smooth/compact data and `c > 0`, the
integral of `(c - Σ t_i)^A` against a product of two labelled monomial sums is
`c^{k+A+|α|+|β|} A! S(α,β,k)/(A+|α|+|β|+k)!`. -/
theorem simplex_integral_lmono (k : ℕ) (c : ℝ) (hc : 0 < c) (A : ℕ) (α β : List ℕ) :
    ∫ t in {t : Fin k → ℝ | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ c},
        (c - ∑ i, t i)^A * lmono α k t * lmono β k t
      = c ^ (k + A + α.sum + β.sum) * (A.factorial : ℝ) * (Slab α β k : ℝ) /
          ((A + α.sum + β.sum + k).factorial : ℝ) := by
  have hpoint : ∀ t : Fin k → ℝ,
      (c - ∑ i, t i)^A * lmono α k t * lmono β k t
      = ∑ e : Fin α.length ↪ Fin k, ∑ e' : Fin β.length ↪ Fin k,
          (c - ∑ i, t i)^A * ∏ x : Fin k, (t x) ^ (expOf α k e x + expOf β k e' x) := by
    intro t
    simp only [lmono]
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e' _ => ?_)
    rw [prod_pow_expOf α k e t, prod_pow_expOf β k e' t, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl (fun x _ => ?_)
    rw [← pow_add]
  have hval : ∀ (e : Fin α.length ↪ Fin k) (e' : Fin β.length ↪ Fin k),
      ∫ t in {t : Fin k → ℝ | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ c},
          (c - ∑ i, t i)^A * ∏ x : Fin k, (t x) ^ (expOf α k e x + expOf β k e' x)
        = c ^ (k + A + α.sum + β.sum) / (((A + α.sum + β.sum + k).factorial : ℕ) : ℝ) *
            ((A.factorial : ℝ) *
              ∏ x : Fin k, ((expOf α k e x + expOf β k e' x).factorial : ℝ)) := by
    intro e e'
    have hsum : ∑ x : Fin k, (expOf α k e x + expOf β k e' x) = α.sum + β.sum := by
      rw [Finset.sum_add_distrib, sum_expOf, sum_expOf]
    have h := Commons.MeasureTheory.Integral.simplex_integral_scaled c hc A
      (fun x : Fin k => expOf α k e x + expOf β k e' x)
    rw [h, hsum, Nat.cast_mul, Nat.cast_prod]
    ring
  have hfac : (∑ e : Fin α.length ↪ Fin k, ∑ e' : Fin β.length ↪ Fin k,
        c ^ (k + A + α.sum + β.sum) / (((A + α.sum + β.sum + k).factorial : ℕ) : ℝ) *
          ((A.factorial : ℝ) *
            ∏ x : Fin k, ((expOf α k e x + expOf β k e' x).factorial : ℝ)))
      = c ^ (k + A + α.sum + β.sum) / (((A + α.sum + β.sum + k).factorial : ℕ) : ℝ) *
          (A.factorial : ℝ) *
          (∑ e : Fin α.length ↪ Fin k, ∑ e' : Fin β.length ↪ Fin k,
            ∏ x : Fin k, ((expOf α k e x + expOf β k e' x).factorial : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e' _ => ?_)
    ring
  have hSlabR : ((Slab α β k : ℕ) : ℝ) =
      ∑ e : Fin α.length ↪ Fin k, ∑ e' : Fin β.length ↪ Fin k,
        ∏ x : Fin k, ((expOf α k e x + expOf β k e' x).factorial : ℝ) := by
    rw [Slab, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl (fun e' _ => ?_)
    rw [Nat.cast_prod]
  calc ∫ t in {t : Fin k → ℝ | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ c},
          (c - ∑ i, t i)^A * lmono α k t * lmono β k t
      = ∫ t in {t : Fin k → ℝ | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ c}, ∑ e : Fin α.length ↪ Fin k, ∑ e' : Fin β.length ↪ Fin k,
          (c - ∑ i, t i)^A * ∏ x : Fin k, (t x) ^ (expOf α k e x + expOf β k e' x) := by
        rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    _ = ∑ e : Fin α.length ↪ Fin k,
          ∫ t in {t : Fin k → ℝ | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ c},
          ∑ e' : Fin β.length ↪ Fin k,
            (c - ∑ i, t i)^A * ∏ x : Fin k, (t x) ^ (expOf α k e x + expOf β k e' x) := by
        rw [MeasureTheory.integral_finsetSum]
        intro e _
        exact MeasureTheory.integrable_finsetSum _ (fun e' _ => integrableOn_simplexC_poly k c A _)
    _ = ∑ e : Fin α.length ↪ Fin k, ∑ e' : Fin β.length ↪ Fin k,
          ∫ t in {t : Fin k → ℝ | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ c},
            (c - ∑ i, t i)^A * ∏ x : Fin k, (t x) ^ (expOf α k e x + expOf β k e' x) := by
        refine Finset.sum_congr rfl (fun e _ => ?_)
        rw [MeasureTheory.integral_finsetSum]
        intro e' _
        exact integrableOn_simplexC_poly k c A _
    _ = ∑ e : Fin α.length ↪ Fin k, ∑ e' : Fin β.length ↪ Fin k,
          c ^ (k + A + α.sum + β.sum) / (((A + α.sum + β.sum + k).factorial : ℕ) : ℝ) *
            ((A.factorial : ℝ) *
              ∏ x : Fin k, ((expOf α k e x + expOf β k e' x).factorial : ℝ)) := by
        exact Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun e' _ => hval e e'))
    _ = c ^ (k + A + α.sum + β.sum) * (A.factorial : ℝ) * (Slab α β k : ℝ) /
          ((A + α.sum + β.sum + k).factorial : ℝ) := by
        rw [hSlabR, hfac]
        ring

/-! ## Labelled form (arbitrary exponent functions)

The following generalises the master formula from signatures (lists of exponents) to
arbitrary exponent functions `a : Fin l → ℕ`.  It is the form used by the `J`-functional
(`∫_{(1-ε)R^{k-1}}(∫_0^{(1+ε)-Σ'} F dt_i)²`), where the placement of the distinguished
coordinate's exponent has to be tracked separately. -/

/-- The exponent vector of a labelled placement of an arbitrary exponent function. -/
def expOfF {l : ℕ} (a : Fin l → ℕ) (k : ℕ) (e : Fin l ↪ Fin k) : Fin k → ℕ :=
  fun c => ∑ i : Fin l, if e i = c then a i else 0

/-- The labelled monomial sum attached to an exponent function. -/
def lmonoF {l : ℕ} (a : Fin l → ℕ) (k : ℕ) (t : Fin k → ℝ) : ℝ :=
  ∑ e : Fin l ↪ Fin k, ∏ i : Fin l, (t (e i)) ^ (a i)

/-- The labelled assignment sum `Σ_{e,e'} ∏_c (exp_e c + exp_{e'} c)!`. -/
def SlabF {l1 l2 : ℕ} (a : Fin l1 → ℕ) (b : Fin l2 → ℕ) (k : ℕ) : ℕ :=
  ∑ e : Fin l1 ↪ Fin k, ∑ e' : Fin l2 ↪ Fin k,
    ∏ c : Fin k, Nat.factorial (expOfF a k e c + expOfF b k e' c)

lemma prod_pow_expOfF {l k : ℕ} (a : Fin l → ℕ) (e : Fin l ↪ Fin k) (t : Fin k → ℝ) :
    ∏ i : Fin l, (t (e i)) ^ (a i) = ∏ c : Fin k, (t c) ^ (expOfF a k e c) := by
  have hinner : ∀ i : Fin l,
      ∏ c : Fin k, (t c) ^ (if e i = c then a i else 0) = (t (e i)) ^ (a i) := by
    intro i
    rw [Finset.prod_eq_single (e i)]
    · simp
    · intro b _ hb
      rw [if_neg (fun h : e i = b => hb h.symm), pow_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  calc ∏ i : Fin l, (t (e i)) ^ (a i)
      = ∏ i : Fin l, ∏ c : Fin k, (t c) ^ (if e i = c then a i else 0) := by
        refine Finset.prod_congr rfl (fun i _ => ?_)
        rw [hinner i]
    _ = ∏ c : Fin k, ∏ i : Fin l, (t c) ^ (if e i = c then a i else 0) := Finset.prod_comm
    _ = ∏ c : Fin k, (t c) ^ (expOfF a k e c) := by
        refine Finset.prod_congr rfl (fun c _ => ?_)
        rw [expOfF, ← Finset.prod_pow_eq_pow_sum]

lemma sum_expOfF {l k : ℕ} (a : Fin l → ℕ) (e : Fin l ↪ Fin k) :
    ∑ c : Fin k, expOfF a k e c = ∑ i : Fin l, a i := by
  have hinner : ∀ y : Fin l,
      (∑ x : Fin k, (if e y = x then a y else 0)) = a y := by
    intro y
    rw [Finset.sum_eq_single (e y)]
    · simp
    · intro b _ hb
      rw [if_neg (fun h : e y = b => hb h.symm)]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h1 : ∑ c : Fin k, expOfF a k e c
      = ∑ c : Fin k, ∑ i : Fin l, (if e i = c then a i else 0) := rfl
  rw [h1, Finset.sum_comm]
  exact Finset.sum_congr rfl (fun y _ => hinner y)

theorem simplex_integral_lmonoF (k : ℕ) (c : ℝ) (hc : 0 < c) (A : ℕ) {l1 l2 : ℕ}
    (a : Fin l1 → ℕ) (b : Fin l2 → ℕ) :
    ∫ t in {t : Fin k → ℝ | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ c},
        (c - ∑ i, t i)^A * lmonoF a k t * lmonoF b k t
      = c ^ (k + A + (∑ i, a i) + (∑ i, b i)) * (A.factorial : ℝ) *
          (SlabF a b k : ℝ) / ((A + (∑ i, a i) + (∑ i, b i) + k).factorial : ℝ) := by
  have hpoint : ∀ t : Fin k → ℝ,
      (c - ∑ i, t i)^A * lmonoF a k t * lmonoF b k t
      = ∑ e : Fin l1 ↪ Fin k, ∑ e' : Fin l2 ↪ Fin k,
          (c - ∑ i, t i)^A * ∏ x : Fin k, (t x) ^ (expOfF a k e x + expOfF b k e' x) := by
    intro t
    simp only [lmonoF]
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e' _ => ?_)
    rw [prod_pow_expOfF a e t, prod_pow_expOfF b e' t, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl (fun x _ => ?_)
    rw [← pow_add]
  have hval : ∀ (e : Fin l1 ↪ Fin k) (e' : Fin l2 ↪ Fin k),
      ∫ t in {t : Fin k → ℝ | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ c},
          (c - ∑ i, t i)^A * ∏ x : Fin k, (t x) ^ (expOfF a k e x + expOfF b k e' x)
        = c ^ (k + A + (∑ i, a i) + (∑ i, b i)) /
            (((A + (∑ i, a i) + (∑ i, b i) + k).factorial : ℕ) : ℝ) *
            ((A.factorial : ℝ) *
              ∏ x : Fin k, ((expOfF a k e x + expOfF b k e' x).factorial : ℝ)) := by
    intro e e'
    have hsum : ∑ x : Fin k, (expOfF a k e x + expOfF b k e' x) = (∑ i, a i) + ∑ i, b i := by
      rw [Finset.sum_add_distrib, sum_expOfF, sum_expOfF]
    have h := Commons.MeasureTheory.Integral.simplex_integral_scaled c hc A
      (fun x : Fin k => expOfF a k e x + expOfF b k e' x)
    rw [h, hsum, Nat.cast_mul, Nat.cast_prod]
    ring
  have hfac : (∑ e : Fin l1 ↪ Fin k, ∑ e' : Fin l2 ↪ Fin k,
        c ^ (k + A + (∑ i, a i) + (∑ i, b i)) /
            (((A + (∑ i, a i) + (∑ i, b i) + k).factorial : ℕ) : ℝ) *
          ((A.factorial : ℝ) *
            ∏ x : Fin k, ((expOfF a k e x + expOfF b k e' x).factorial : ℝ)))
      = c ^ (k + A + (∑ i, a i) + (∑ i, b i)) /
          (((A + (∑ i, a i) + (∑ i, b i) + k).factorial : ℕ) : ℝ) *
          (A.factorial : ℝ) *
          (∑ e : Fin l1 ↪ Fin k, ∑ e' : Fin l2 ↪ Fin k,
            ∏ x : Fin k, ((expOfF a k e x + expOfF b k e' x).factorial : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e' _ => ?_)
    ring
  have hSlabR : ((SlabF a b k : ℕ) : ℝ) =
      ∑ e : Fin l1 ↪ Fin k, ∑ e' : Fin l2 ↪ Fin k,
        ∏ x : Fin k, ((expOfF a k e x + expOfF b k e' x).factorial : ℝ) := by
    rw [SlabF, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl (fun e' _ => ?_)
    rw [Nat.cast_prod]
  calc ∫ t in {t : Fin k → ℝ | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ c},
          (c - ∑ i, t i)^A * lmonoF a k t * lmonoF b k t
      = ∫ t in {t : Fin k → ℝ | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ c},
          ∑ e : Fin l1 ↪ Fin k, ∑ e' : Fin l2 ↪ Fin k,
            (c - ∑ i, t i)^A * ∏ x : Fin k, (t x) ^ (expOfF a k e x + expOfF b k e' x) := by
        rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    _ = ∑ e : Fin l1 ↪ Fin k,
          ∫ t in {t : Fin k → ℝ | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ c},
            ∑ e' : Fin l2 ↪ Fin k,
              (c - ∑ i, t i)^A * ∏ x : Fin k, (t x) ^ (expOfF a k e x + expOfF b k e' x) := by
        rw [MeasureTheory.integral_finsetSum]
        intro e _
        exact MeasureTheory.integrable_finsetSum _ (fun e' _ => integrableOn_simplexC_poly k c A _)
    _ = ∑ e : Fin l1 ↪ Fin k, ∑ e' : Fin l2 ↪ Fin k,
          ∫ t in {t : Fin k → ℝ | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ c},
            (c - ∑ i, t i)^A * ∏ x : Fin k, (t x) ^ (expOfF a k e x + expOfF b k e' x) := by
        refine Finset.sum_congr rfl (fun e _ => ?_)
        rw [MeasureTheory.integral_finsetSum]
        intro e' _
        exact integrableOn_simplexC_poly k c A _
    _ = ∑ e : Fin l1 ↪ Fin k, ∑ e' : Fin l2 ↪ Fin k,
          c ^ (k + A + (∑ i, a i) + (∑ i, b i)) /
            (((A + (∑ i, a i) + (∑ i, b i) + k).factorial : ℕ) : ℝ) *
            ((A.factorial : ℝ) *
              ∏ x : Fin k, ((expOfF a k e x + expOfF b k e' x).factorial : ℝ)) := by
        exact Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun e' _ => hval e e'))
    _ = c ^ (k + A + (∑ i, a i) + (∑ i, b i)) * (A.factorial : ℝ) * (SlabF a b k : ℝ) /
          ((A + (∑ i, a i) + (∑ i, b i) + k).factorial : ℝ) := by
        rw [hSlabR, hfac]
        ring

end

end Commons.NumberTheory.MaynardSieve
