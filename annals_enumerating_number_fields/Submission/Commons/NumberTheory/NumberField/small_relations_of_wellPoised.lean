import Mathlib
import Submission.Commons.Algebra.MvPolynomial.finrank_restrictTotalDegree
import Submission.Commons.LinearAlgebra.Submodule.exists_finset_injective_on_span
import Submission.Commons.Lattice.Minkowski.exists_short_independent
import Submission.Commons.Lattice.Minkowski.minkowski_second_upper
import Submission.Commons.Lattice.SuccessiveMinima.realisation_linearIndependent
import Submission.Commons.Lattice.SuccessiveMinima.Basic
import Submission.Commons.Analysis.InnerProductSpace.unitBall_volume_lower_bound
import Submission.Commons.Analysis.InnerProductSpace.unitBall_volume_pos
import Submission.Commons.Analysis.Real.coeff_bound_arith
import Submission.Commons.Analysis.InnerProductSpace.intCoords_linearIndependent_real
import Submission.Commons.Lattice.Minkowski.exists_short_independent_of_basis
import Submission.Commons.Lattice.Minkowski.kerLattice_basis_wedge_le
import Submission.Commons.NumberTheory.NumberField.short_relations_of_relation_lattice
/-!
# Small relations of a well-poised point

We prove that a well-poised point `κ : Fin r → 𝓞 K` (i.e. the jet map
`f ↦ (f(κ), ∂₁f(κ), …, ∂ᵣf(κ))` from degree-`≤ d` polynomials over `ℚ` onto `K^{r+1}` is
surjective) admits `r` integer relations of degree `≤ d` with independent gradients and with
coefficients bounded by `(n (r+1) d (H+1))^(r+d+10)`, where `H` bounds the house of the `κ j`.

## Proved here

* `MvPolynomial`-level coefficient bounds for the minimum-polynomial relation
  (`prod_X_sub_C_coeff_bound`, `minpoly_coeff_bound` — the latter also in the shared commons);
* `jetMap` and the fact that well-poisedness is exactly surjectivity of the jet map
  (`jetMap_surjective_of_wellPoised`, `aeval_surjective_of_wellPoised`);
* the dimension count `span_K_eq_top_of_finrank_lt`: a `ℚ`-subspace of `K^r` of
  `ℚ`-dimension `> [K:ℚ]·(r-1)` has `K`-span `K^r`;
* the greedy extraction `exists_linearIndependent_coords`.

## Roadmap for the target theorem

Write `ψ` for the jet map.  The plan (Couveignes, *Enumerating number fields*, §3, made
d_K-free by passing to a "minimal" set of monomials):

1. `hκ` makes `ψ` surjective; hence there is a subset `S` of monomials with `|S| = n(r+1)`
   such that `ψ|_S` is an isomorphism (choose a non-vanishing maximal minor of `ψ`; `S` must be
   a coordinate subset, so that "degree `≤ d`" and "integer coefficients" are preserved).
2. Let `Λ_S = {E ∈ ℤ^S : E(κ) = 0}` (the lattice of degree-`≤ d` monomial relations supported
   on `S`).  It has `ℤ`-rank `|S| - n = nr` and the gradient map `∇ = (∂₁,…,∂_r)` is
   *injective* on `Λ_S` (if `ψ(E) = 0` then `E = 0`, by the isomorphism in step 1).
3. Covolume bound (`Commons.Lattice.Minkowski.kerLattice_basis_wedge_le`, a commons lemma
   requested from the fleet; the mixed-embedding variant with the values `κ^α`): the relation
   lattice has a `ℤ`-basis whose exterior product has norm `≤ ∏_α ‖value of κ^α‖`, and each
   value has mixed-embedding norm `≤ H^{|α|} ≤ H^d`.  (This replaces the paper's discriminant
   factor `d_K^{2d/n}` by `1`: the *image* lattice is a sublattice of the lattice of `𝓞 K`,
   whose covolume is `√d_K ≥ 1`.)
4. Minkowski's second theorem
   (`Commons.Lattice.Minkowski.minkowski_second_upper`) together with the realisation of
   successive minima by independent vectors
   (`Commons.Lattice.SuccessiveMinima.exists_linearIndependent_of_successiveMinimum`) gives
   `m := n(r-1) + 1` independent relations `E_1, …, E_m ∈ Λ_S` with all coefficients bounded by
   `4^r · (2·n(r+1))^{1/2} · H^d · (n r / (2π))^{r/2} ≤ (n(r+1)d(H+1))^{r+d+10}`.
5. Their gradients span a `ℚ`-subspace of `K^r` of dimension `m = n(r-1)+1 > n(r-1)`
   (injectivity), so by step (dimension count) `span_K_eq_top_of_finrank_lt` the `K`-span of
   the gradients is `K^r`; the greedy lemma `exists_linearIndependent_coords` extracts `r` of
   the `E_i` whose gradients are `K`-independent, whence
   `det (∂_j E_{i}) ≠ 0`.
6. Embed the chosen relations into `ℤ[x₁,…,xᵣ]` (zero coefficients outside `S`), concluding.

-/

open MvPolynomial Polynomial NumberField

namespace Commons.NumberTheory.NumberField

/-- Coefficient bound for a product of linear factors over `ℂ` whose roots are bounded by
`H ≥ 1`: all coefficients are bounded by `2 ^ card * H ^ card`. -/
lemma prod_X_sub_C_coeff_bound (t : Multiset ℂ) (H : ℝ) (hH : ∀ r ∈ t, ‖r‖ ≤ H)
    (hH1 : 1 ≤ H) :
    ∀ k, ‖(t.map (fun r => (Polynomial.X - Polynomial.C r : ℂ[X]))).prod.coeff k‖
      ≤ 2 ^ t.card * H ^ t.card := by
  induction t using Multiset.induction with
  | empty =>
      intro k
      rw [Multiset.map_zero, Multiset.prod_zero, Multiset.card_zero, pow_zero, pow_zero, mul_one]
      simp only [Polynomial.coeff_one]
      split_ifs <;> norm_num
  | cons a t ih =>
      intro k
      have haH : ‖a‖ ≤ H := hH a (Multiset.mem_cons_self a t)
      have hH' : ∀ r ∈ t, ‖r‖ ≤ H := fun r hr => hH r (Multiset.mem_cons_of_mem hr)
      have hih := ih hH'
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
      have key : ∀ k, ‖((Polynomial.X - Polynomial.C a) *
          (t.map (fun r => (Polynomial.X - Polynomial.C r : ℂ[X]))).prod).coeff k‖
          ≤ 2 ^ (t.card+1) * H ^ (t.card+1) := by
        intro k
        rw [sub_mul]
        have hPk := hih k
        have h2 : ‖(Polynomial.C a * (t.map (fun r => (Polynomial.X - Polynomial.C r : ℂ[X]))).prod).coeff k‖
            ≤ H * (2 ^ t.card * H ^ t.card) := by
          rw [Polynomial.coeff_C_mul, norm_mul]
          exact mul_le_mul haH hPk (norm_nonneg _) (le_trans (by norm_num) hH1)
        have hX : ‖(Polynomial.X * (t.map (fun r => (Polynomial.X - Polynomial.C r : ℂ[X]))).prod).coeff k‖
            ≤ 2 ^ t.card * H ^ t.card := by
          rcases Nat.eq_zero_or_pos k with hk | hk
          · subst hk; rw [Polynomial.coeff_X_mul_zero]; simp; positivity
          · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
            rw [Polynomial.coeff_X_mul]; exact hih n
        calc ‖_ - _‖ ≤ _ + _ := norm_sub_le _ _
          _ ≤ 2 ^ t.card * H ^ t.card + H * (2 ^ t.card * H ^ t.card) := add_le_add hX h2
          _ = 2 ^ t.card * H ^ t.card * (1 + H) := by ring
          _ ≤ 2 ^ t.card * H ^ t.card * (2 * H) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
          _ = 2 ^ (t.card+1) * H ^ (t.card+1) := by rw [pow_succ]; ring
      exact key k

/-- The minimum polynomial over `ℤ` of an algebraic integer `x` with `house x ≤ H` has all
coefficients bounded by `2 ^ [K:ℚ] * H ^ [K:ℚ]`. -/
lemma minpoly_coeff_bound (K : Type*) [Field K] [NumberField K]
    (x : RingOfIntegers K) (H : ℝ)
    (hH : house ((x : RingOfIntegers K) : K) ≤ H) (hH1 : 1 ≤ H) (k : ℕ) :
    ‖(((minpoly ℤ x).coeff k : ℤ) : ℝ)‖ ≤ 2 ^ (Module.finrank ℚ K) * H ^ (Module.finrank ℚ K) := by
  set q : ℚ[X] := minpoly ℚ ((x : RingOfIntegers K) : K) with hqdef
  have hxint : IsIntegral ℤ x := IsIntegralClosure.isIntegral ℤ K x
  have hmonicq : q.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral _)
  have hmap : (minpoly ℤ x).map (algebraMap ℤ ℚ) = q := by
    rw [hqdef]
    exact (minpoly.isIntegrallyClosed_eq_field_fractions (R := ℤ) (K := ℚ)
      (S := RingOfIntegers K) (L := K) hxint).symm
  set qc : ℂ[X] := q.map (algebraMap ℚ ℂ) with hqcdef
  have hmonicc : qc.Monic := hmonicq.map _
  have hsplit : qc.Splits := IsAlgClosed.splits _
  have hqc0 : qc ≠ 0 := hmonicc.ne_zero
  have hcoeff_rel : ∀ k, ((minpoly ℤ x).coeff k : ℚ) = q.coeff k := by
    intro k
    have h2 := congrArg (fun (p : ℚ[X]) => p.coeff k) hmap
    simpa using h2
  have hcard : q.natDegree ≤ Module.finrank ℚ K := by
    rw [hqdef]
    exact minpoly.natDegree_le (A := ℚ) (B := K) (x := ((x : RingOfIntegers K) : K))
  have hprod : qc = (qc.roots.map (fun r => (Polynomial.X - Polynomial.C r : ℂ[X]))).prod :=
    hsplit.eq_prod_roots_of_monic hmonicc
  have hroots : ∀ r ∈ qc.roots, ‖r‖ ≤ H := by
    intro r hr
    rw [Polynomial.mem_roots hqc0, Polynomial.IsRoot.def] at hr
    have hr1 : Polynomial.aeval r ((minpoly ℚ ((x : RingOfIntegers K) : K))) = 0 := by
      rw [← Polynomial.aeval_map_algebraMap (R := ℚ) (A := ℂ) (B := ℂ) r
        (minpoly ℚ ((x : RingOfIntegers K) : K))]
      exact hr
    have hr' : r ∈ (minpoly ℚ ((x : RingOfIntegers K) : K)).rootSet ℂ := by
      rw [Polynomial.mem_rootSet]
      exact ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral _), hr1⟩
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly (F := ℚ) ℂ
      ((x : RingOfIntegers K) : K)] at hr'
    obtain ⟨ψ, rfl⟩ := hr'
    exact (norm_embedding_le_house _ ψ.toRingHom).trans hH
  have hcb := prod_X_sub_C_coeff_bound qc.roots H hroots hH1 k
  rw [← hprod] at hcb
  have hcard2 : qc.roots.card = q.natDegree := by
    rw [← hsplit.natDegree_eq_card_roots, hqcdef, Polynomial.natDegree_map]
  rw [hcard2] at hcb
  have hrel2 : qc.coeff k = ((q.coeff k : ℚ) : ℂ) := by
    rw [hqcdef, Polynomial.coeff_map]; rfl
  have hH0 : 0 ≤ H := (house_nonneg _).trans hH
  have hcbq : ‖(q.coeff k : ℝ)‖ ≤ 2 ^ q.natDegree * H ^ q.natDegree := by
    rw [hrel2, Complex.norm_ratCast] at hcb
    exact hcb
  have heq2 : ‖(((minpoly ℤ x).coeff k : ℤ) : ℝ)‖ = ‖(q.coeff k : ℝ)‖ := by
    rw [← hcoeff_rel k]
    simp
  rw [heq2]
  refine hcbq.trans ?_
  exact mul_le_mul (pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) hcard)
    (pow_le_pow_right₀ hH1 hcard) (pow_nonneg hH0 _) (by positivity)

end Commons.NumberTheory.NumberField

namespace Commons.NumberTheory.NumberField

/-- Evaluating a univariate integer polynomial substituted at `X j` equals evaluating the
polynomial at `κ j`. -/
lemma mp_eval2 (r : ℕ) (j : Fin r) (p : Polynomial ℤ) (K : Type*) [CommSemiring K] [Algebra ℤ K]
    (κ : Fin r → K) :
    MvPolynomial.aeval κ (p.eval₂ MvPolynomial.C (MvPolynomial.X j))
      = Polynomial.eval₂ (algebraMap ℤ K) (κ j) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [Polynomial.eval₂_add, map_add, hp, hq]
  | monomial k c =>
      simp only [Polynomial.eval₂_monomial, map_mul, map_pow]
      rw [show (MvPolynomial.aeval κ) (MvPolynomial.C c) = algebraMap ℤ K c from MvPolynomial.aeval_C κ c]
      rw [MvPolynomial.aeval_X]

/-- Partial derivative of `p(X j)`. -/
lemma mp_pderivE (r : ℕ) (i j : Fin r) (p : Polynomial ℤ) :
    MvPolynomial.pderiv i (p.eval₂ MvPolynomial.C (MvPolynomial.X j : MvPolynomial (Fin r) ℤ))
      = if i = j then p.derivative.eval₂ MvPolynomial.C (MvPolynomial.X j) else 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.eval₂_add, map_add, hp, hq]; split_ifs <;> simp
  | monomial k c =>
      simp only [Polynomial.eval₂_monomial, Polynomial.derivative_monomial]
      rw [MvPolynomial.pderiv_C_mul]
      by_cases h : i = j
      · subst h
        rw [if_pos rfl, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X_self, mul_one]
        cases k with
        | zero => simp
        | succ k => simp [Polynomial.eval₂_monomial, mul_assoc, mul_comm, mul_left_comm]
      · rw [if_neg h, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X_of_ne (Ne.symm h), mul_zero, mul_zero]

/-- Total degree of `p(X j)` is at most `p.natDegree`. -/
lemma mp_totalDegree (r : ℕ) (j : Fin r) (p : Polynomial ℤ) :
    (p.eval₂ MvPolynomial.C (MvPolynomial.X j : MvPolynomial (Fin r) ℤ)).totalDegree ≤ p.natDegree := by
  rw [Polynomial.eval₂_eq_sum_range]
  refine MvPolynomial.totalDegree_finsetSum_le ?_
  intro k hk
  rw [Finset.mem_range] at hk
  rcases eq_or_ne (p.coeff k) 0 with h | h
  · rw [h]; simp
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X_pow]
    omega

end Commons.NumberTheory.NumberField
namespace Commons.NumberTheory.NumberField

/-- The jet map `f ↦ (f(κ), ∂₁f(κ), …, ∂ᵣf(κ))`, as a `ℚ`-linear map. -/
noncomputable def jetMap {K : Type*} [Field K] [CharZero K] (r : ℕ) (κ : Fin r → K) :
    MvPolynomial (Fin r) ℚ →ₗ[ℚ] (K × (Fin r → K)) where
  toFun f := (MvPolynomial.aeval κ f, fun j => MvPolynomial.aeval κ (MvPolynomial.pderiv j f))
  map_add' f g := by
    ext j <;> simp
  map_smul' a f := by
    ext j <;> simp

@[simp] lemma jetMap_apply {K : Type*} [Field K] [CharZero K] (r : ℕ) (κ : Fin r → K)
    (f : MvPolynomial (Fin r) ℚ) :
    jetMap (K := K) r κ f =
      (MvPolynomial.aeval κ f, fun j => MvPolynomial.aeval κ (MvPolynomial.pderiv j f)) :=
  rfl

/-- The well-poised hypothesis says exactly that the jet map is surjective. -/
lemma jetMap_surjective_of_wellPoised {K : Type*} [Field K] [CharZero K] (r d : ℕ)
    (κ : Fin r → K)
    (hκ : ∀ g : K × (Fin r → K), ∃ f : MvPolynomial (Fin r) ℚ,
      f.totalDegree ≤ d ∧ jetMap (K := K) r κ f = g) :
    Function.Surjective (jetMap (K := K) r κ) := fun g => by
  obtain ⟨f, -, hf⟩ := hκ g
  exact ⟨f, hf⟩

/-- Well-poisedness in particular gives that *every* element of `K` is the value at `κ` of a
polynomial of total degree `≤ d`. -/
lemma aeval_surjective_of_wellPoised {K : Type*} [Field K] [CharZero K] (r d : ℕ)
    (κ : Fin r → K)
    (hκ : ∀ g : K × (Fin r → K), ∃ f : MvPolynomial (Fin r) ℚ,
      f.totalDegree ≤ d ∧ jetMap (K := K) r κ f = g) :
    Function.Surjective (fun f : MvPolynomial (Fin r) ℚ => MvPolynomial.aeval κ f) := by
  intro a
  obtain ⟨f, -, hf⟩ := hκ (a, fun _ => 0)
  exact ⟨f, congrArg Prod.fst hf⟩

/-- **Dimension count for the gradient space.**  If a `ℚ`-subspace `V` of `K^r` has
`ℚ`-dimension exceeding `[K:ℚ]·(r-1)`, then its `K`-span is all of `K^r`; in particular any
family of relations whose gradients span such a `V` already has `r` members with
`K`-independent gradients. -/
lemma span_K_eq_top_of_finrank_lt {K : Type*} [Field K] [CharZero K] [FiniteDimensional ℚ K]
    (r : ℕ) (V : Submodule ℚ (Fin r → K))
    (h : Module.finrank ℚ K * (r - 1) < Module.finrank ℚ V) :
    Submodule.span K (V : Set (Fin r → K)) = ⊤ := by
  classical
  by_contra hne
  set W : Submodule K (Fin r → K) := Submodule.span K (V : Set (Fin r → K)) with hW
  have hVle : V ≤ Submodule.restrictScalars ℚ W := Submodule.subset_span
  have hWlt : W < ⊤ := lt_of_le_of_ne le_top hne
  have hfr : Module.finrank K W < Module.finrank K (Fin r → K) := by
    have h := Submodule.finrank_lt_finrank_of_lt hWlt
    rwa [finrank_top] at h
  have hfrK : Module.finrank K (Fin r → K) = r := by simp
  rw [hfrK] at hfr
  have hle : Module.finrank K W ≤ r - 1 := by omega
  haveI hfinW : Module.Finite ℚ ↥W := Module.Finite.trans K ↥W
  have h1 : Module.finrank ℚ V ≤ Module.finrank ℚ (Submodule.restrictScalars ℚ W) :=
    Submodule.finrank_mono hVle
  have h2 : Module.finrank ℚ (Submodule.restrictScalars ℚ W) =
      Module.finrank ℚ K * Module.finrank K W :=
    (Module.finrank_mul_finrank ℚ K W).symm
  have h3 : Module.finrank ℚ K * Module.finrank K W ≤ Module.finrank ℚ K * (r - 1) :=
    Nat.mul_le_mul_left _ hle
  omega

/-- **Greedy extraction of `r` independent gradients.**  From any family of vectors of `K^r`
whose `K`-span is everything, one can select `r` members whose coordinate vectors are
`K`-linearly independent. -/
lemma exists_linearIndependent_coords {K : Type*} [Field K] (r : ℕ) {ι : Type*}
    (v : ι → (Fin r → K)) (h : Submodule.span K (Set.range v) = ⊤) :
    ∃ g : Fin r → ι, LinearIndependent K (fun i => v (g i)) := by
  classical
  obtain ⟨f, hfmem, -, hfind⟩ := Submodule.exists_fun_fin_finrank_span_eq K (Set.range v)
  have hfin : Module.finrank K (Submodule.span K (Set.range v)) = r := by rw [h]; simp
  let f' : Fin r → (Fin r → K) := fun i => f (Fin.cast hfin.symm i)
  have hf'ind : LinearIndependent K f' := hfind.comp _ (Fin.cast_injective hfin.symm)
  have hmem' : ∀ i, f' i ∈ Set.range v := fun i => hfmem _
  choose g hg using hmem'
  refine ⟨g, ?_⟩
  have : (fun i => v (g i)) = f' := funext fun i => (hg i)
  rw [this]
  exact hf'ind

end Commons.NumberTheory.NumberField
namespace Commons.NumberTheory.NumberField

/-! ## Auxiliary lemmas for the monomial lattice construction -/

/-- Exponent vectors of total degree at most `d` in `r` variables form a finite type. -/
noncomputable instance instFintypeTotalDegreeLe (r d : ℕ) :
    Fintype {m : Fin r →₀ ℕ // m.sum (fun _ e => e) ≤ d} := by
  classical
  have hle : ∀ (m : {m : Fin r →₀ ℕ // m.sum (fun _ e => e) ≤ d}) (i : Fin r), m.1 i ≤ d := by
    intro m i
    have h1 := Finsupp.single_le_sum (f := m.1) (g := fun (_ : Fin r) (e : ℕ) => e)
      (fun _ _ => Nat.zero_le _) i
    have h2 : (Finsupp.single i (m.1 i)).sum (fun _ e => e) = m.1 i := by simp
    rw [h2] at h1
    exact le_trans h1 m.2
  have hfin : Finite {m : Fin r →₀ ℕ // m.sum (fun _ e => e) ≤ d} :=
    Finite.of_injective
      (fun m : {m : Fin r →₀ ℕ // m.sum (fun _ e => e) ≤ d} => fun i : Fin r =>
        (⟨m.1 i, Nat.lt_succ_of_le (hle m i)⟩ : Fin (d + 1)))
      (by
        intro a b hab
        refine Subtype.ext (Finsupp.ext fun i => ?_)
        have := congrFun hab i
        simpa using congrArg Fin.val this)
  exact Fintype.ofFinite _

/-- The house of a finite product is at most the product of the houses. -/
lemma house_finset_prod_le {K : Type*} [Field K] [NumberField K] {ι : Type*}
    (s : Finset ι) (f : ι → K) :
    house (∏ i ∈ s, f i) ≤ ∏ i ∈ s, house (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; simp [house]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      exact (house_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left ih (house_nonneg _))

/-- House bound for the value of a monomial of total degree `≤ d` at `κ`. -/
lemma house_finsupp_prod_le {K : Type*} [Field K] [NumberField K] {r : ℕ} (κ : Fin r → K)
    {H : ℝ} (hH : ∀ j, house (κ j) ≤ H) (hH1 : 1 ≤ H) {d : ℕ} (m : Fin r →₀ ℕ)
    (hm : m.sum (fun _ e => e) ≤ d) :
    house (m.prod (fun j k => κ j ^ k)) ≤ H ^ d := by
  classical
  have h1 : house (m.prod (fun j k => κ j ^ k)) ≤ m.prod (fun j k => house (κ j) ^ k) := by
    rw [Finsupp.prod, Finsupp.prod]
    calc house (∏ j ∈ m.support, κ j ^ m j) ≤ ∏ j ∈ m.support, house (κ j ^ m j) :=
          house_finset_prod_le _ _
      _ ≤ ∏ j ∈ m.support, house (κ j) ^ m j :=
          Finset.prod_le_prod (fun j _ => house_nonneg _) (fun j _ => house_pow_le _ _)
  have h2 : m.prod (fun j k => house (κ j) ^ k) ≤ H ^ (m.sum (fun _ e => e)) := by
    rw [Finsupp.prod, Finsupp.sum]
    calc ∏ j ∈ m.support, house (κ j) ^ m j ≤ ∏ j ∈ m.support, H ^ m j :=
          Finset.prod_le_prod (fun j _ => pow_nonneg (house_nonneg _) _) (fun j _ =>
            pow_le_pow_left₀ (house_nonneg _) (hH j) _)
      _ = H ^ (∑ j ∈ m.support, m j) := Finset.prod_pow_eq_pow_sum m.support m H
  exact h1.trans (h2.trans (pow_le_pow_right₀ hH1 hm))

/-- A coefficient of a sum of monomials indexed by an injective exponent map. -/
lemma coeff_sum_monomial_eq {r : ℕ} {ι : Type*} [Fintype ι] (α : ι → (Fin r →₀ ℕ))
    (c : ι → ℤ) (m : Fin r →₀ ℕ) :
    (∑ k, MvPolynomial.monomial (α k) (c k) : MvPolynomial (Fin r) ℤ).coeff m
      = ∑ k, if α k = m then c k else 0 := by
  classical
  rw [MvPolynomial.coeff_sum]
  exact Finset.sum_congr rfl (fun k _ => MvPolynomial.coeff_monomial m (α k) (c k))

/-- A single coefficient of a sum of monomials with distinct exponents is bounded by the
`ℓ∞` norm of the coefficient vector. -/
lemma abs_sum_ite_le {ι : Type*} [Fintype ι] {M : Type*} [DecidableEq M] (α : ι → M)
    (hα : Function.Injective α)
    (c : ι → ℤ) (m : M) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ k, |(c k : ℝ)| ≤ B) :
    |(∑ k, (if α k = m then (c k : ℝ) else 0))| ≤ B := by
  classical
  set s : Finset ι := Finset.univ.filter (fun k => α k = m) with hs
  have hsum : (∑ k, (if α k = m then (c k : ℝ) else 0)) = ∑ k ∈ s, (c k : ℝ) := by
    rw [hs, Finset.sum_filter]
  have hcard : s.card ≤ 1 := Finset.card_le_one_iff.mpr (fun ha hb =>
    hα ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm))
  rw [hsum]
  rcases Finset.eq_empty_or_nonempty s with h | ⟨k0, hk0⟩
  · rw [h]; simpa using hB0
  · have hs1 : s = {k0} := by
      ext k
      constructor
      · intro hk
        have := (Finset.card_le_one_iff.mp hcard) hk hk0
        simpa using this
      · intro hk
        rw [Finset.mem_singleton] at hk
        subst hk
        exact hk0
    rw [hs1, Finset.sum_singleton]
    exact hB k0

end Commons.NumberTheory.NumberField
namespace Commons.NumberTheory.NumberField

/-! ## Auxiliary lemmas for the final assembly -/

/-- A coordinate of a vector of `EuclideanSpace ℝ (Fin M)` is bounded by its norm. -/
lemma abs_coord_le_norm {M : ℕ} (f : Fin M → ℝ) (k : Fin M) :
    |f k| ≤ ‖(WithLp.equiv 2 (Fin M → ℝ)).symm f‖ := by
  have h := PiLp.norm_apply_le ((WithLp.equiv 2 (Fin M → ℝ)).symm f) k
  simpa using h

/-- Coefficient identity for a linear combination of monomials, in `ℝ`. -/
lemma coeff_sum_monomial_eq_real {r : ℕ} {ι : Type*} [Fintype ι] (α : ι → (Fin r →₀ ℕ))
    (c : ι → ℤ) (m : Fin r →₀ ℕ) :
    (((∑ k, MvPolynomial.monomial (α k) (c k) : MvPolynomial (Fin r) ℤ).coeff m : ℤ) : ℝ)
      = ∑ k, (if α k = m then (c k : ℝ) else 0) := by
  classical
  rw [coeff_sum_monomial_eq]
  push_cast
  exact Finset.sum_congr rfl (fun k _ => by split_ifs <;> simp)

/-- The value of a monomial at `κ`, coerced to `K`. -/
lemma coe_aeval_monomial {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (κ : Fin r → NumberField.RingOfIntegers K) (m : Fin r →₀ ℕ) :
    (((MvPolynomial.aeval κ (MvPolynomial.monomial m 1) : NumberField.RingOfIntegers K)) : K)
      = m.prod (fun j k => (((κ j : NumberField.RingOfIntegers K) : K)) ^ k) := by
  rw [MvPolynomial.aeval_monomial]
  simp only [map_one, one_mul]
  rw [Finsupp.prod, Finsupp.prod]
  exact map_prod (algebraMap (NumberField.RingOfIntegers K) K) _ _

end Commons.NumberTheory.NumberField
namespace Commons.NumberTheory.NumberField

lemma li_rat_of_li_real {ι M : Type*} [Fintype ι] [Fintype M] (v : ι → (M → ℤ))
    (h : LinearIndependent ℝ (fun i => (WithLp.equiv 2 (M → ℝ)).symm (fun k => (v i k : ℝ)))) :
    LinearIndependent ℚ (fun i => fun k => (v i k : ℚ)) := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro q hq i
  have hsum : (∑ j, (q j : ℝ) • (WithLp.equiv 2 (M → ℝ)).symm (fun k => (v j k : ℝ))) = 0 := by
    ext k
    show (∑ j, (q j : ℝ) • (WithLp.equiv 2 (M → ℝ)).symm (fun k => (v j k : ℝ))).ofLp k
      = (0 : EuclideanSpace ℝ M).ofLp k
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_zero, WithLp.equiv_symm_apply,
      WithLp.ofLp_toLp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hk := congrFun hq k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hk
    have hk' : (∑ j, (q j : ℝ) * (v j k : ℝ)) = 0 := by
      have := congrArg (fun t : ℚ => (t : ℝ)) hk
      push_cast at this
      simpa using this
    exact hk'
  have hqi : ((q i : ℝ)) = 0 := h (fun j => (q j : ℝ)) hsum i
  exact_mod_cast hqi

end Commons.NumberTheory.NumberField

namespace Commons.NumberTheory.NumberField

/-- **Main statement**: a well-poised point `κ` of a number field `K` of degree `n` admits
integer relations `E i` of total degree `≤ d`, with coefficients bounded by
`(n (r+1) d (H+1)) ^ (r + d + 10)`, vanishing at `κ`, and with invertible Jacobian
determinant at `κ`. -/
theorem small_relations_of_wellPoised (K : Type*) [Field K] [NumberField K] (n r d : ℕ) (hn : Module.finrank ℚ K = n) (κ : Fin r → NumberField.RingOfIntegers K) (H : ℝ) (hH : ∀ j, NumberField.house (((κ j : NumberField.RingOfIntegers K) : K)) ≤ H) (hκ : ∀ g : K × (Fin r → K), ∃ f : MvPolynomial (Fin r) ℚ, f.totalDegree ≤ d ∧ (MvPolynomial.aeval (fun j : Fin r => (((κ j : NumberField.RingOfIntegers K) : K)))) f = g.1 ∧ ∀ j : Fin r, (MvPolynomial.aeval (fun j : Fin r => (((κ j : NumberField.RingOfIntegers K) : K)))) (MvPolynomial.pderiv j f) = g.2 j) (hd : 0 < d) (hr : 1 ≤ r) : ∃ E : Fin r → MvPolynomial (Fin r) ℤ, (∀ i, (E i).totalDegree ≤ d) ∧ (∀ i j, |(E i).coeff j| ≤ (↑n * ↑(r+1) * ↑d * (H + 1)) ^ (r + d + 10)) ∧ (∀ i, (MvPolynomial.aeval (fun j : Fin r => (((κ j : NumberField.RingOfIntegers K) : K)))) ((E i).map (algebraMap ℤ ℚ)) = 0) ∧ IsUnit ((MvPolynomial.aeval (fun j : Fin r => (((κ j : NumberField.RingOfIntegers K) : K)))) (Matrix.det fun i j => MvPolynomial.pderiv j ((E i).map (algebraMap ℤ ℚ)))) := by
  classical
  set κK : Fin r → K := fun j => ((κ j : NumberField.RingOfIntegers K) : K) with hκK
  have hnpos : 0 < n := by rw [← hn]; exact Module.finrank_pos
  have hn1 : 1 ≤ n := hnpos
  have hH0 : 0 ≤ H := (house_nonneg (κK ⟨0, hr⟩)).trans (hH ⟨0, hr⟩)
  -- (1) jet surjectivity
  have hκjet : ∀ g : K × (Fin r → K), ∃ f : MvPolynomial (Fin r) ℚ,
      f.totalDegree ≤ d ∧ jetMap (K := K) r κK f = g := by
    intro g
    obtain ⟨f, hdeg, h1, h2⟩ := hκ g
    refine ⟨f, hdeg, ?_⟩
    refine Prod.ext ?_ ?_
    · simpa [jetMap, hκK] using h1
    · funext j
      simpa [jetMap, hκK] using h2 j
  have hsurj : Function.Surjective (jetMap (K := K) r κK) :=
    jetMap_surjective_of_wellPoised r d κK hκjet
  -- (2) monomial jets span everything
  set Φ : {m : Fin r →₀ ℕ // m.sum (fun _ e => e) ≤ d} → (K × (Fin r → K)) :=
    fun m => jetMap (K := K) r κK (MvPolynomial.monomial m.1 1) with hΦdef
  have hspanΦ : Submodule.span ℚ (Set.range Φ) = ⊤ := by
    rw [eq_top_iff]
    rintro g -
    obtain ⟨f, hdeg, hf⟩ := hκjet g
    have hset : Set.range (fun m : {m : Fin r →₀ ℕ // m.sum (fun _ e => e) ≤ d} =>
            MvPolynomial.monomial m.1 1)
        = ((fun x : Fin r →₀ ℕ => MvPolynomial.monomial x 1) ''
          {m : Fin r →₀ ℕ | m.sum (fun _ e => e) ≤ d}) := by
      ext z
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨m, rfl⟩
        exact ⟨m.1, m.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    have hfmem : f ∈ Submodule.span ℚ (Set.range fun m : {m : Fin r →₀ ℕ // m.sum (fun _ e => e) ≤ d} =>
        MvPolynomial.monomial m.1 1) := by
      have h3 : MvPolynomial.restrictTotalDegree (Fin r) ℚ d ≤
          Submodule.span ℚ (Set.range fun m : {m : Fin r →₀ ℕ // m.sum (fun _ e => e) ≤ d} =>
            MvPolynomial.monomial m.1 1) := by
        rw [show MvPolynomial.restrictTotalDegree (Fin r) ℚ d = MvPolynomial.restrictSupport ℚ
            {m : Fin r →₀ ℕ | m.sum (fun _ e => e) ≤ d} from rfl,
          MvPolynomial.restrictSupport_eq_span, Submodule.span_le]
        rintro z ⟨x, hx, rfl⟩
        exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
      exact h3 ((MvPolynomial.mem_restrictTotalDegree (Fin r) d f).mpr hdeg)
    have hmap : jetMap (K := K) r κK f ∈
        Submodule.map (jetMap (K := K) r κK)
          (Submodule.span ℚ (Set.range fun m : {m : Fin r →₀ ℕ // m.sum (fun _ e => e) ≤ d} =>
            MvPolynomial.monomial m.1 1)) := Submodule.mem_map_of_mem hfmem
    rw [Submodule.map_span] at hmap
    have himg : (⇑(jetMap (K := K) r κK)) '' (Set.range fun m : {m : Fin r →₀ ℕ //
          m.sum (fun _ e => e) ≤ d} => MvPolynomial.monomial m.1 1) = Set.range Φ := by
      ext z
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨y, ⟨m, rfl⟩, rfl⟩
        exact ⟨m, rfl⟩
      · rintro ⟨m, rfl⟩
        exact ⟨MvPolynomial.monomial m.1 1, ⟨m, rfl⟩, rfl⟩
    rw [himg] at hmap
    rw [← hf]
    exact hmap
  obtain ⟨S, hScard, hSind⟩ :=
    Commons.LinearAlgebra.Submodule.exists_finset_linearIndependent_card_eq_finrank Φ hspanΦ
  have hfinprod : Module.finrank ℚ (K × (Fin r → K)) = n * (r + 1) := by
    rw [Module.finrank_prod, Module.finrank_pi_fintype, hn]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have hScard' : S.card = n * (r + 1) := by rw [hScard, hfinprod]
  let π : Fin (n * (r + 1)) ≃ ↥S := (Fintype.equivFinOfCardEq (by simpa using hScard')).symm
  have hΦind : ∀ c : Fin (n * (r + 1)) → ℚ, (∑ i, c i • Φ (π i)) = 0 → c = 0 := by
    intro c hc
    have hc' : (∑ s : ↥S, c (π.symm s) • Φ s) = 0 := by
      rw [← hc, Fintype.sum_equiv π (fun i => c i • Φ (π i)) (fun s => c (π.symm s) • Φ s)
        (fun i => by simp)]
    have hz := (Fintype.linearIndependent_iff.mp hSind) (fun s => c (π.symm s)) hc'
    funext i
    have h2 := hz (π i)
    simpa using h2
  -- (3) the values
  set y : Fin (n * (r + 1)) → NumberField.RingOfIntegers K :=
    fun i => MvPolynomial.aeval κ (MvPolynomial.monomial ((π i).1).1 1) with hydef
  have hyprod : ∀ i, (((y i : NumberField.RingOfIntegers K)) : K)
      = ((π i).1).1.prod (fun j m => κK j ^ m) := by
    intro i
    simp only [hydef, hκK, coe_aeval_monomial]
  have hΦprod : ∀ i, (Φ (π i)).1 = ((π i).1).1.prod (fun j m => κK j ^ m) := by
    intro i
    simp only [hΦdef, jetMap_apply, hκK, MvPolynomial.aeval_monomial]
    simp
  have hyval : ∀ i, (((y i : NumberField.RingOfIntegers K)) : K) = (Φ (π i)).1 :=
    fun i => (hyprod i).trans (hΦprod i).symm
  -- (4) the linear maps
  set comb : (Fin (n * (r + 1)) → ℚ) →ₗ[ℚ] MvPolynomial (Fin r) ℚ :=
    { toFun := fun c => ∑ k, c k • MvPolynomial.monomial ((π k).1).1 1
      map_add' := by
        intro a b
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro a c
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl (fun k _ => by rw [mul_smul]) } with hcombdef
  have hcombapply : ∀ c : Fin (n * (r + 1)) → ℚ,
      comb c = ∑ k, c k • MvPolynomial.monomial ((π k).1).1 1 := by
    intro c
    rw [hcombdef]
    rfl
  set Ψ : (Fin (n * (r + 1)) → ℚ) →ₗ[ℚ] (K × (Fin r → K)) :=
    (jetMap (K := K) r κK).comp comb with hΨdef
  have hΨapply : ∀ c : Fin (n * (r + 1)) → ℚ, Ψ c = ∑ i, c i • Φ (π i) := by
    intro c
    rw [hΨdef, LinearMap.comp_apply, hcombapply]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul, hΦdef]
  have hΨfst : ∀ c : Fin (n * (r + 1)) → ℚ, (Ψ c).1 = ∑ i, c i • (((y i : 𝓞 K)) : K) := by
    intro c
    have h1 : (Ψ c).1 = (LinearMap.fst ℚ K (Fin r → K)) (∑ i, c i • Φ (π i)) := by
      rw [hΨapply c]
      rfl
    rw [h1, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul]
    congr 1
    exact (hyval i).symm
  have hΨinj : Function.Injective Ψ := by
    intro a b hab
    have hzero : (∑ i, (a - b) i • Φ (π i)) = 0 := by
      rw [← hΨapply (a - b), map_sub, hab, sub_self]
    have hc := hΦind (a - b) hzero
    funext i
    have h2 := congrFun hc i
    simpa [sub_eq_zero] using h2
  have hΨrange : Ψ.range = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [LinearMap.finrank_range_of_inj hΨinj, Module.finrank_pi, Fintype.card_fin, hfinprod]
  -- (5) the value map is onto
  have hvalSurj : Function.Surjective (fun c : Fin (n * (r + 1)) → ℚ =>
      ∑ i, c i • (((y i : 𝓞 K)) : K)) := by
    intro z
    have hmem : (z, 0) ∈ Ψ.range := by rw [hΨrange]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := hmem
    refine ⟨c, ?_⟩
    have h2 : (Ψ c).1 = z := by
      rw [hc]
    rw [hΨfst c] at h2
    exact h2
  have hspanY : Submodule.span ℚ (Set.range (fun i : Fin (n * (r + 1)) => (((y i : 𝓞 K)) : K))) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨c, hc⟩ := hvalSurj z
    rw [← hc]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  -- (6) house bound
  have hyB : ∀ i : Fin (n * (r + 1)), house (((y i : 𝓞 K)) : K) ≤ (H + 1) ^ d := by
    intro i
    rw [hyprod i]
    exact house_finsupp_prod_le (κ := κK)
      (fun j => (hH j).trans (le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1)))
      (by linarith [hH0]) ((π i).1).1 ((π i).1).2
  -- (7) the lattice step
  have hshort : ∃ x : Fin (n * (r - 1) + 1) → (Fin (n * (r + 1)) → ℤ),
      (∀ i, (∑ k : Fin (n * (r + 1)), (((x i k : ℤ) : K) * (((y k : 𝓞 K)) : K))) = 0) ∧
      LinearIndependent ℝ (fun i => (WithLp.equiv 2 (Fin (n * (r + 1)) → ℝ)).symm (fun k => (x i k : ℝ))) ∧
      (∀ i, ‖(WithLp.equiv 2 (Fin (n * (r + 1)) → ℝ)).symm (fun k => (x i k : ℝ))‖ ≤
        ((4:ℝ) ^ (n * (r + 1) - Module.finrank ℚ K) *
            (Real.sqrt ((n * (r + 1) : ℕ)) * ((H + 1) ^ d + 1)) ^ (Module.finrank ℚ K) /
          ENNReal.toReal (MeasureTheory.volume
            (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n * (r + 1) - Module.finrank ℚ K))) 1)))
          ^ ((1:ℝ) / (((n * (r + 1) - Module.finrank ℚ K) + 1 - (n * (r - 1) + 1) : ℕ) : ℝ)) + 1) := by
    refine Commons.NumberTheory.NumberField.short_relations_of_relation_lattice K (n * (r + 1)) y
      ((H + 1) ^ d) (by positivity) hyB hspanY (n * (r - 1) + 1) (by omega) ?_
    rw [hn]
    have h1 : n * (r + 1) - n = n * r := by rw [Nat.mul_succ, Nat.add_sub_cancel]
    rw [h1]
    have h2 : n * r = n * (r - 1) + n := by
      conv_lhs => rw [show r = (r - 1) + 1 by omega]
      rw [Nat.mul_add, Nat.mul_one]
    rw [h2]
    omega
  obtain ⟨x, hxrel, hxind, hxnorm⟩ := hshort
  -- (8) the volume bound and the coefficient bound
  have hnrn : 0 < n * r := Nat.mul_pos hnpos (by omega)
  have hNeZero : NeZero (n * r) := ⟨hnrn.ne'⟩
  haveI := hNeZero
  have hvolpos : 0 < ENNReal.toReal (MeasureTheory.volume
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n * r))) 1)) :=
    Commons.Analysis.InnerProductSpace.unitBall_volume_pos
  have hvol : (2 / Real.sqrt ((n : ℝ) * (r : ℝ))) ^ (n * r) ≤ ENNReal.toReal (MeasureTheory.volume
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n * r))) 1)) := by
    have h := Commons.Analysis.InnerProductSpace.unitBall_volume_lower_bound (m := n * r) hnrn
    simpa [Nat.cast_mul] using h
  have hnm : n * (r + 1) - n = n * r := by rw [Nat.mul_succ, Nat.add_sub_cancel]
  have hnrm : (n * r + 1 - (n * (r - 1) + 1) : ℕ) = n := by
    rw [Nat.add_sub_add_right, ← Nat.mul_sub_left_distrib]
    have h1 : r - (r - 1) = 1 := by omega
    rw [h1, mul_one]
  have hnormbound : ∀ i : Fin (n * (r - 1) + 1),
      ‖(WithLp.equiv 2 (Fin (n * (r + 1)) → ℝ)).symm (fun k => (x i k : ℝ))‖ ≤
        (4 ^ (n * r) * (Real.sqrt ((n : ℝ) * ((r : ℝ) + 1)) * ((H + 1) ^ d + 1)) ^ n /
          ENNReal.toReal (MeasureTheory.volume
            (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n * r))) 1)))
          ^ ((1 : ℝ) / (n : ℝ)) + 1 := by
    intro i
    have h := hxnorm i
    rw [hn, hnm, hnrm] at h
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using h
  have hBndM := Commons.Analysis.Real.coeff_bound_arith n r d H hn1 hr (by omega) hH0 hvolpos hvol
  have hBnd0 : 0 ≤ (4 ^ (n * r) * (Real.sqrt ((n : ℝ) * ((r : ℝ) + 1)) * ((H + 1) ^ d + 1)) ^ n /
      ENNReal.toReal (MeasureTheory.volume
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n * r))) 1))) ^ ((1 : ℝ) / (n : ℝ)) + 1 := by
    positivity
  -- (9) from R-independence to Q-independence
  set xi : Fin (n * (r - 1) + 1) → (Fin (n * (r + 1)) → ℚ) := fun i k => (x i k : ℚ) with hxidef
  have hxiind : LinearIndependent ℚ xi := li_rat_of_li_real x hxind
  have hrelc : ∀ i, (∑ k, xi i k • (((y k : 𝓞 K)) : K)) = 0 := by
    intro i
    have hpt : ∀ k, xi i k • (((y k : 𝓞 K)) : K)
        = (((x i k : ℤ)) : K) * (((y k : 𝓞 K)) : K) := by
      intro k
      simp [hxidef, Algebra.smul_def]
    exact (Finset.sum_congr rfl (fun k _ => hpt k)).trans (hxrel i)
  -- (10) the gradient map
  set grad : (Fin (n * (r + 1)) → ℚ) →ₗ[ℚ] (Fin r → K) :=
    { toFun := fun c => fun j => (Ψ c).2 j
      map_add' := by
        intro a b
        funext j
        simp [map_add]
      map_smul' := by
        intro a c
        funext j
        simp [map_smul] } with hgraddef
  have hgradapply : ∀ (c : Fin (n * (r + 1)) → ℚ) (j : Fin r), grad c j = (Ψ c).2 j := fun c j => rfl
  have hΛker : ∀ c : Fin (n * (r + 1)) → ℚ,
      (∑ k, c k • (((y k : 𝓞 K)) : K)) = 0 → grad c = 0 → c = 0 := by
    intro c hv hg
    have hΨ0 : Ψ c = 0 := by
      refine Prod.ext ?_ ?_
      · rw [hΨfst c]; exact hv
      · funext j
        have h2 := congrFun hg j
        rw [hgradapply] at h2
        exact h2
    exact hΨinj (by rw [hΨ0, map_zero])
  have hgradind : LinearIndependent ℚ (fun i => grad (xi i)) := by
    rw [Fintype.linearIndependent_iff]
    intro q hq
    have h0 : grad (∑ i, q i • xi i) = 0 := by
      rw [map_sum]
      simpa using hq
    have hv0 : (∑ k, (∑ i, q i • xi i) k • (((y k : 𝓞 K)) : K)) = 0 := by
      have h1 : ∀ k : Fin (n * (r + 1)),
          (∑ i, q i • xi i) k = ∑ i, q i * (xi i) k := by
        intro k
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      simp only [h1]
      have h2 : ∀ k : Fin (n * (r + 1)),
          (∑ i, q i * (xi i) k) • (((y k : 𝓞 K)) : K)
            = ∑ i, q i • ((xi i) k • (((y k : 𝓞 K)) : K)) := by
        intro k
        rw [Finset.sum_smul]
        exact Finset.sum_congr rfl (fun i _ => by rw [mul_smul])
      simp only [h2]
      rw [Finset.sum_comm]
      simp only [← Finset.smul_sum]
      rw [Finset.sum_eq_zero]
      intro i _
      rw [hrelc i, smul_zero]
    exact (Fintype.linearIndependent_iff.mp hxiind) q (hΛker _ hv0 h0)
  -- (11) dimension count
  have hspanGrad : Submodule.span K (Set.range (fun i => grad (xi i))) = ⊤ := by
    have hVdim : n * (r - 1) < Module.finrank ℚ (Submodule.span ℚ (Set.range (fun i => grad (xi i)))) := by
      rw [finrank_span_eq_card hgradind]
      simp
    have hVtop := span_K_eq_top_of_finrank_lt r (Submodule.span ℚ (Set.range (fun i => grad (xi i))))
      (by rw [hn]; exact hVdim)
    rw [eq_top_iff]
    intro z hz
    have hle : Submodule.span ℚ (Set.range (fun i => grad (xi i))) ≤
        (Submodule.span K (Set.range (fun i => grad (xi i)))).restrictScalars ℚ :=
      Submodule.span_le.mpr (fun x hx => Submodule.subset_span hx)
    have hz' : z ∈ Submodule.span K (Submodule.span ℚ (Set.range (fun i => grad (xi i))) : Set (Fin r → K)) := by
      rw [hVtop]; exact Submodule.mem_top
    have hVeq : Submodule.span K (Submodule.span ℚ (Set.range (fun i => grad (xi i))) : Set (Fin r → K))
        = Submodule.span K (Set.range (fun i => grad (xi i))) := by
      refine le_antisymm ?_ (Submodule.span_mono Submodule.subset_span)
      rw [Submodule.span_le]
      intro x hx
      exact hle hx
    rwa [hVeq] at hz'
  obtain ⟨g, hgLI⟩ := exists_linearIndependent_coords r (fun i => grad (xi i)) hspanGrad
  -- (12) the polynomials
  let Ef : Fin r → MvPolynomial (Fin r) ℤ :=
    fun i => ∑ k : Fin (n * (r + 1)), MvPolynomial.monomial ((π k).1).1 (x (g i) k)
  have hmapE : ∀ i, (Ef i).map (algebraMap ℤ ℚ)
      = ∑ k, MvPolynomial.monomial ((π k).1).1 (((x (g i) k : ℤ) : ℚ)) := by
    intro i
    rw [show Ef i = ∑ k, MvPolynomial.monomial ((π k).1).1 (x (g i) k) from rfl, map_sum]
    exact Finset.sum_congr rfl (fun k _ => by rw [MvPolynomial.map_monomial]; rfl)
  have hpderivE : ∀ i j, MvPolynomial.pderiv j ((Ef i).map (algebraMap ℤ ℚ))
      = ∑ k, (((x (g i) k : ℤ) : ℚ)) • MvPolynomial.pderiv j (MvPolynomial.monomial ((π k).1).1 1) := by
    intro i j
    rw [hmapE i, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show MvPolynomial.monomial ((π k).1).1 (((x (g i) k : ℤ) : ℚ))
        = (((x (g i) k : ℤ) : ℚ)) • MvPolynomial.monomial ((π k).1).1 1 from ?_]
    · exact Derivation.map_smul (MvPolynomial.pderiv j) _ _
    · rw [← map_smul (MvPolynomial.monomial ((π k).1).1) (((x (g i) k : ℤ) : ℚ)) (1:ℚ),
        smul_eq_mul, mul_one]
  have hgradE : ∀ i, (fun j => MvPolynomial.aeval κK (MvPolynomial.pderiv j ((Ef i).map (algebraMap ℤ ℚ))))
      = grad (xi (g i)) := by
    intro i
    funext j
    rw [hpderivE i j, map_sum, hgradapply, hΨapply]
    have hsplit : (∑ k, (xi (g i)) k • Φ (π k)).2
        = ∑ k, (xi (g i)) k • (Φ (π k)).2 :=
      map_sum (LinearMap.snd ℚ K (Fin r → K)) (fun k => (xi (g i)) k • Φ (π k)) Finset.univ
    rw [hsplit, Finset.sum_apply]
    exact Finset.sum_congr rfl (fun k _ => by
      simp only [Pi.smul_apply, hxidef, map_smul, hΦdef, jetMap_apply])
  -- (13) the conclusion
  refine ⟨Ef, ?_, ?_, ?_, ?_⟩
  · intro i
    refine MvPolynomial.totalDegree_finsetSum_le (fun k _ => ?_)
    exact (MvPolynomial.totalDegree_monomial_le ((π k).1).1 (x (g i) k)).trans ((π k).1).2
  · intro i m
    have hinj : Function.Injective (fun k : Fin (n * (r + 1)) => ((π k).1).1) := by
      intro a b hab
      exact π.injective (Subtype.ext (Subtype.ext hab))
    have hcoef : (((Ef i).coeff m : ℤ) : ℝ)
        = ∑ k, (if ((π k).1).1 = m then (x (g i) k : ℝ) else 0) := by
      simp only [Ef]
      exact coeff_sum_monomial_eq_real _ _ _
    have habs : |(Ef i).coeff m| = |(((Ef i).coeff m : ℤ) : ℝ)| := by simp
    rw [habs, hcoef]
    refine (abs_sum_ite_le (fun k : Fin (n * (r + 1)) => ((π k).1).1) hinj (fun k => x (g i) k) m
      hBnd0 (fun k => ?_)).trans ?_
    · exact (abs_coord_le_norm (fun k => (x (g i) k : ℝ)) k).trans (hnormbound (g i))
    · simpa only [Nat.cast_add, Nat.cast_one] using hBndM
  · intro i
    rw [hmapE i, map_sum]
    have hterm : ∀ k : Fin (n * (r + 1)),
        MvPolynomial.aeval κK (MvPolynomial.monomial ((π k).1).1 (((x (g i) k : ℤ) : ℚ)))
          = (((x (g i) k : ℤ)) : K) * (((y k : 𝓞 K)) : K) := by
      intro k
      rw [MvPolynomial.aeval_monomial, ← hyprod k]
      simp
    exact (Finset.sum_congr rfl (fun k _ => hterm k)).trans (hxrel (g i))
  · have hrows : LinearIndependent K (fun i : Fin r =>
        (fun j => MvPolynomial.aeval κK (MvPolynomial.pderiv j ((Ef i).map (algebraMap ℤ ℚ))))) := by
      have hfun : (fun i : Fin r => (fun j => MvPolynomial.aeval κK
          (MvPolynomial.pderiv j ((Ef i).map (algebraMap ℤ ℚ))))) = (fun i => grad (xi (g i))) :=
        funext hgradE
      rw [hfun]
      exact hgLI
    have hunit := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
    have hunit2 : IsUnit (Matrix.of (fun i j => MvPolynomial.aeval κK
        (MvPolynomial.pderiv j ((Ef i).map (algebraMap ℤ ℚ))))).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp hunit
    have hdet : (MvPolynomial.aeval κK)
          (Matrix.det (fun i j => MvPolynomial.pderiv j ((Ef i).map (algebraMap ℤ ℚ))))
        = (RingHom.mapMatrix ((MvPolynomial.aeval κK).toRingHom)
            (fun i j => MvPolynomial.pderiv j ((Ef i).map (algebraMap ℤ ℚ)))).det :=
      RingHom.map_det _ _
    have hmat : RingHom.mapMatrix ((MvPolynomial.aeval κK).toRingHom)
        (fun i j => MvPolynomial.pderiv j ((Ef i).map (algebraMap ℤ ℚ)))
        = Matrix.of (fun i j => MvPolynomial.aeval κK
            (MvPolynomial.pderiv j ((Ef i).map (algebraMap ℤ ℚ)))) := rfl
    rw [hdet, hmat]
    exact hunit2

end Commons.NumberTheory.NumberField

