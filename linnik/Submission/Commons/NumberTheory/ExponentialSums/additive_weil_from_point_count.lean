import Mathlib
import Submission.Commons.Algebra.Polynomial.eulerProduct_logDeriv_monic
import Submission.Commons.Algebra.Polynomial.exists_powerSums_of_recurrence
import Submission.Commons.Analysis.Complex.pow_sum_norm_le_root
import Submission.Commons.Algebra.Polynomial.power_sums_determine_multiset_domain
import Submission.Commons.FieldTheory.Polynomial.X_pow_card_sub_X_eq_prod_X_sub_C
import Submission.Commons.FieldTheory.Polynomial.multiset_psum_newton
import Submission.Commons.NumberTheory.FunctionField.artin_schreier_extension_bound
import Submission.Commons.NumberTheory.CharacterSum.mulchar_char_sum_extension_eq_psi_sum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 800000

/-! # Additive (Artin--Schreier) Weil bound from the point-count hypothesis

**Target** (proved here): `Commons.NumberTheory.ExponentialSums.additive_weil_from_point_count`.
From the point-count hypothesis `hpc` (the Artin--Schreier curves `z ^ p - z = g x` have
`q + O(√q)` points over every even-degree extension `E/F_p` with `[E : F_p] > deg g`) it
deduces the Weil bound for the additive character sums over the prime field:
`‖∑_{x : ZMod p} ψ (g x)‖ ≤ C (deg g) √p` for every nontrivial additive character `ψ`.

## Structure of the proof

1. **The `L`-function weights** `Ψ(A) = ψ (asTrace A)` for monic `A ∈ F_p[X]`, where
   `asTrace A` is the root sum `∑_{A(α) = 0} g(α)` — an element of the prime field, obtained by
   showing that this root sum is Frobenius-fixed (`exists_algebraMap_eq_rootSum`).  The key facts
   are multiplicativity (`psiAS_mul`) and the normalisation `Ψ(1) = 1` (`psiAS_one`), so that the
   Euler product for the `L`-function applies.
2. **Vanishing of the coefficients of the `L`-polynomial.**  Via Newton's identities the root sum
   is a polynomial expression in the coefficients of `A`; shifting the coefficient of
   `X ^ (deg A - deg g)` changes the root sum by `- leadingCoeff · deg g ≠ 0` in `ZMod p`
   (`asTrace_translate`, `psumK_translate`), and `ψ` is nontrivial, whence
   `C_m = ∑_{deg A = m} Ψ(A) = 0` for `m ≥ deg g` (`Cm_eq_zero`).
3. **The `L`-polynomial and the power sums.**  `Commons.Algebra.Polynomial.eulerProduct_logDeriv_monic`
   gives the recurrence `∑_{m < n} L_m S_{n-m} = n L_n` for the coefficients `L_m = C_m` and the
   log-derivative coefficients `S_n = ∑_{d ∣ n} d ∑_{deg P = d, P irred.} Ψ(P) ^ (n/d)`
   (`recurrence`), and `Commons.Algebra.Polynomial.exists_powerSums_of_recurrence` produces
   `γ_1, …, γ_t` with `t ≤ L.natDegree ≤ deg g - 1` and `S_n = -∑_{j} γ_j ^ n`
   (`Sm_eq_powerSums`).
4. **Identification.**  Grouping the elements of `E` by their minimal polynomial over `F_p`,
   `Tr_{E/F_p} (g a) = (n / d) · asTrace (minpoly a)` where `d = deg (minpoly a) ∣ n`
   (`trace_eval_eq_nsmul_asTrace`, using the orbit description of the trace and of the roots of
   the minimal polynomial), whence `∑_{a : E} ψ (Tr (g a)) = S_n` (`char_sum_eq_Sm`).
5. **Transference.**  The point-count hypothesis bounds the sums over even-degree extensions, and
   a Cesàro/level-set argument (`addchar_pow_sum_transference`) upgrades those `O(p^k)` bounds,
   valid for the exponents `k` coprime to `p`, to `|γ_j| ≤ √p`; the bound for the prime field
   `E = ZMod p` (which is the `n = 1` case) follows.

-/

namespace Commons.NumberTheory.ExponentialSums

open Polynomial

/-- Roots of a split monic polynomial are permuted by a ring endomorphism fixing it. -/
theorem roots_map_of_map_eq {K : Type*} [Field K] {B : Polynomial K} (hmon : B.Monic)
    (hspl : B.Splits) (σ : K →+* K) (hB : B.map σ = B) : B.roots.map σ = B.roots := by
  classical
  have hfac : B = (B.roots.map (fun x => Polynomial.X - Polynomial.C x)).prod :=
    hspl.eq_prod_roots_of_monic hmon
  have hkey : (B.roots.map (fun x => Polynomial.X - Polynomial.C (σ x))).prod
      = (B.roots.map (fun x => Polynomial.X - Polynomial.C x)).prod := by
    have h1 : (B.roots.map (fun x => Polynomial.X - Polynomial.C x)).prod.map σ
        = (B.roots.map (fun x => Polynomial.X - Polynomial.C (σ x))).prod := by
      rw [Polynomial.map_multiset_prod, Multiset.map_map]
      congr 1
      refine Multiset.map_congr rfl fun x _ => ?_
      simp
    have h2 : (B.roots.map (fun x => Polynomial.X - Polynomial.C x)).prod.map σ
        = (B.roots.map (fun x => Polynomial.X - Polynomial.C x)).prod := by
      rw [← hfac, hB]
    rw [h1] at h2
    exact h2
  calc B.roots.map σ
      = ((B.roots.map (fun x => Polynomial.X - Polynomial.C (σ x))).prod).roots := by
        rw [show (B.roots.map (fun x => Polynomial.X - Polynomial.C (σ x)))
            = (B.roots.map σ).map (fun x => Polynomial.X - Polynomial.C x) from by
          rw [Multiset.map_map]; rfl]
        exact (Polynomial.roots_multiset_prod_X_sub_C (B.roots.map σ)).symm
    _ = ((B.roots.map (fun x => Polynomial.X - Polynomial.C x)).prod).roots := by rw [hkey]
    _ = B.roots := Polynomial.roots_multiset_prod_X_sub_C B.roots

/-- The `p`-th power map is a ring endomorphism of a field of characteristic `p`. -/
noncomputable def frobeniusPow (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] : K →+* K where
  toFun := fun x => x ^ p
  map_one' := one_pow p
  map_mul' := fun x y => mul_pow x y p
  map_zero' := zero_pow (Fact.out : p.Prime).ne_zero
  map_add' := fun x y => add_pow_char x y p

/-- The sum of a multiset of `p`-th powers in characteristic `p`. -/
lemma multiset_sum_pow_char {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (s : Multiset K) : s.sum ^ p = (s.map (fun x => x ^ p)).sum := by
  induction s using Multiset.induction with
  | empty => rw [Multiset.sum_zero, Multiset.map_zero, Multiset.sum_zero, zero_pow (Fact.out : p.Prime).ne_zero]
  | cons a s ih =>
      rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, add_pow_char a s.sum p, ih]

/-- The root sum of `g` over the roots of a monic `A` lies in the prime field. -/
theorem exists_algebraMap_eq_rootSum (p : ℕ) [Fact p.Prime] (g A : Polynomial (ZMod p))
    (hA : A.Monic) :
    ∃ c : ZMod p, algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) c =
      ((A.aroots (AlgebraicClosure (ZMod p))).map
        (fun r => (g.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).eval r)).sum := by
  classical
  set K := AlgebraicClosure (ZMod p) with hK
  set F := ZMod p with hF
  set R : Multiset K := A.aroots K with hRdef
  set f : K → K := fun r => (g.map (algebraMap F K)).eval r with hfdef
  have hcomp : (frobeniusPow K p).comp (algebraMap F K) = algebraMap F K := by
    ext a
    show (algebraMap F K a) ^ p = algebraMap F K a
    rw [← map_pow, ZMod.pow_card]
  have hfeval : ∀ r : K, f (r ^ p) = (f r) ^ p := by
    intro r
    have h1 := Polynomial.hom_eval₂ g (algebraMap F K) (frobeniusPow K p) r
    rw [hcomp] at h1
    have h2 : (Polynomial.eval₂ (algebraMap F K) r g) ^ p
        = Polynomial.eval₂ (algebraMap F K) (r ^ p) g := h1
    simpa only [hfdef, Polynomial.eval_map] using h2.symm
  have hperm : R.map (fun r => r ^ p) = R := by
    rw [hRdef, Polynomial.aroots_def]
    exact roots_map_of_map_eq (hA.map (algebraMap F K)) (IsAlgClosed.splits _)
      (frobeniusPow K p) (by rw [Polynomial.map_map, hcomp])
  have hyfix : ((R.map f).sum) ^ p = (R.map f).sum := by
    rw [multiset_sum_pow_char (R.map f)]
    rw [show (R.map f).map (fun x => x ^ p) = R.map (fun r => f (r ^ p)) from by
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun r _ => ?_
      exact (hfeval r).symm]
    rw [show R.map (fun r => f (r ^ p)) = (R.map (fun r => r ^ p)).map f from by
      rw [Multiset.map_map]; rfl]
    rw [show (R.map (fun r => r ^ p)).map f = R.map f from by rw [hperm]]
  -- the pullback
  have hprod : (Polynomial.X ^ p - Polynomial.X : Polynomial K)
      = ∏ a : F, (Polynomial.X - Polynomial.C (algebraMap F K a)) := by
    have hcard : Fintype.card F = p := ZMod.card p
    have h := Commons.FieldTheory.Polynomial.X_pow_card_sub_X_eq_prod_X_sub_C (F := F)
    rw [hcard] at h
    have h2 : (Polynomial.X ^ p - Polynomial.X : Polynomial K)
        = Polynomial.map (algebraMap F K) (Polynomial.X ^ p - Polynomial.X : Polynomial F) := by
      simp
    rw [h2, h, Polynomial.map_prod]
    exact Finset.prod_congr rfl fun a _ => by simp
  have hroot : (Polynomial.eval ((R.map f).sum) (Polynomial.X ^ p - Polynomial.X : Polynomial K)) = 0 := by
    simp [hyfix]
  rw [hprod, Polynomial.eval_prod] at hroot
  obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.mp hroot
  refine ⟨a, ?_⟩
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at ha
  exact (sub_eq_zero.mp ha).symm

/-- The sum of `g` over the roots of `A`, computed in the algebraic closure. -/
noncomputable def rootSumK (p : ℕ) [Fact p.Prime] (g A : Polynomial (ZMod p)) :
    AlgebraicClosure (ZMod p) :=
  ((A.aroots (AlgebraicClosure (ZMod p))).map
    (fun r => (g.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).eval r)).sum

lemma rootSumK_one (p : ℕ) [Fact p.Prime] (g : Polynomial (ZMod p)) :
    rootSumK p g 1 = 0 := by
  rw [rootSumK, Polynomial.aroots_def, Polynomial.map_one, Polynomial.roots_one]
  rfl

lemma rootSumK_mul (p : ℕ) [Fact p.Prime] (g A B : Polynomial (ZMod p))
    (hA : A.Monic) (hB : B.Monic) :
    rootSumK p g (A * B) = rootSumK p g A + rootSumK p g B := by
  rw [rootSumK, rootSumK, rootSumK, Polynomial.aroots_mul (by simp [hA.ne_zero, hB.ne_zero]),
    Multiset.map_add, Multiset.sum_add]

/-- The `ZMod p`-valued trace of `g` at the roots of `A` (for monic `A`). -/
noncomputable def asTrace (p : ℕ) [Fact p.Prime] (g A : Polynomial (ZMod p)) : ZMod p := by
  classical
  exact if _h : ∃ c : ZMod p, algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) c = rootSumK p g A
    then _h.choose else 0

lemma asTrace_spec (p : ℕ) [Fact p.Prime] (g A : Polynomial (ZMod p)) (hA : A.Monic) :
    algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) (asTrace p g A) = rootSumK p g A := by
  classical
  rw [asTrace]
  split_ifs with h
  · exact h.choose_spec
  · exact absurd (exists_algebraMap_eq_rootSum p g A hA) h

lemma asTrace_mul (p : ℕ) [Fact p.Prime] (g A B : Polynomial (ZMod p))
    (hA : A.Monic) (hB : B.Monic) :
    asTrace p g (A * B) = asTrace p g A + asTrace p g B := by
  refine FaithfulSMul.algebraMap_injective (ZMod p) (AlgebraicClosure (ZMod p)) ?_
  rw [map_add, asTrace_spec p g A hA, asTrace_spec p g B hB,
    asTrace_spec p g (A * B) (hA.mul hB), rootSumK_mul p g A B hA hB]

lemma asTrace_one (p : ℕ) [Fact p.Prime] (g : Polynomial (ZMod p)) :
    asTrace p g 1 = 0 := by
  refine FaithfulSMul.algebraMap_injective (ZMod p) (AlgebraicClosure (ZMod p)) ?_
  rw [map_zero, asTrace_spec p g 1 Polynomial.monic_one, rootSumK_one]

/-- The Artin--Schreier `L`-function weight `Ψ(A) = ψ (tr_A g)`. -/
noncomputable def psiAS (p : ℕ) [Fact p.Prime] (ψ : AddChar (ZMod p) ℂ) (g : Polynomial (ZMod p))
    (A : Polynomial (ZMod p)) : ℂ :=
  if A.Monic then ψ (asTrace p g A) else 1

lemma psiAS_mul (p : ℕ) [Fact p.Prime] (ψ : AddChar (ZMod p) ℂ) (g : Polynomial (ZMod p))
    (A B : Polynomial (ZMod p)) (hA : A.Monic) (hB : B.Monic) :
    psiAS p ψ g (A * B) = psiAS p ψ g A * psiAS p ψ g B := by
  simp only [psiAS, if_pos (hA.mul hB), if_pos hA, if_pos hB, asTrace_mul p g A B hA hB,
    AddChar.map_add_eq_mul]

lemma psiAS_one (p : ℕ) [Fact p.Prime] (ψ : AddChar (ZMod p) ℂ) (g : Polynomial (ZMod p)) :
    psiAS p ψ g 1 = 1 := by
  simp only [psiAS, if_pos Polynomial.monic_one, asTrace_one, AddChar.map_zero_eq_one]



noncomputable def arootsK (p : ℕ) [Fact p.Prime] (A : Polynomial (ZMod p)) :
    Multiset (AlgebraicClosure (ZMod p)) := A.aroots (AlgebraicClosure (ZMod p))

noncomputable def psumK (p : ℕ) [Fact p.Prime] (A : Polynomial (ZMod p)) (k : ℕ) :
    AlgebraicClosure (ZMod p) := ((arootsK p A).map (fun r => r ^ k)).sum

lemma arootsK_card (p : ℕ) [Fact p.Prime] (A : Polynomial (ZMod p)) (hA : A.Monic) :
    (arootsK p A).card = A.natDegree := by
  rw [arootsK, Polynomial.aroots_def,
    ← (IsAlgClosed.splits (Polynomial.map (algebraMap (ZMod p)
      (AlgebraicClosure (ZMod p))) A)).natDegree_eq_card_roots]
  exact Polynomial.natDegree_map_eq_of_injective
    (FaithfulSMul.algebraMap_injective (ZMod p) (AlgebraicClosure (ZMod p))) A

lemma C_neg_one_pow (j : ℕ) (K : Type*) [Ring K] :
    ((-1 : Polynomial K) ^ j) = Polynomial.C ((-1 : K) ^ j) := by
  rw [Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_1]

lemma esymm_arootsK (p : ℕ) [Fact p.Prime] (A : Polynomial (ZMod p)) (hA : A.Monic)
    (i : ℕ) (hi : i ≤ A.natDegree) :
    (arootsK p A).esymm i = (-1 : AlgebraicClosure (ZMod p)) ^ i *
      algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) (A.coeff (A.natDegree - i)) := by
  classical
  set K := AlgebraicClosure (ZMod p) with hK
  set B := A.map (algebraMap (ZMod p) K) with hB
  have hmon : B.Monic := hA.map _
  have hfac : B = (B.roots.map (fun x => Polynomial.X - Polynomial.C x)).prod :=
    (IsAlgClosed.splits B).eq_prod_roots_of_monic hmon
  have hcard : B.roots.card = A.natDegree := by
    rw [← arootsK_card p A hA]; rfl
  have hprod := Multiset.prod_X_sub_X_eq_sum_esymm B.roots
  rw [← hfac, hcard] at hprod
  have h1 := congrArg (fun f : Polynomial K => f.coeff (A.natDegree - i)) hprod
  have hneg : ∀ j : ℕ, ((-1 : Polynomial K) ^ j) = Polynomial.C ((-1 : K) ^ j) :=
    fun j => C_neg_one_pow j K
  simp only [hneg] at h1
  rw [Polynomial.finsetSum_coeff] at h1
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] at h1
  have hsingle : (∑ x ∈ Finset.range (A.natDegree + 1),
      (-1) ^ x * (B.roots.esymm x * if A.natDegree - i = A.natDegree - x then 1 else 0))
      = (-1) ^ i * (B.roots.esymm i * if A.natDegree - i = A.natDegree - i then 1 else 0) := by
    refine Finset.sum_eq_single i ?_ ?_
    · intro b hb hbne
      have hb' : b < A.natDegree + 1 := Finset.mem_range.mp hb
      simp only [if_neg (fun h : A.natDegree - i = A.natDegree - b => hbne (by omega)), mul_zero]
    · intro hi'
      exact absurd (Finset.mem_range.mpr (by omega)) hi'
  rw [hsingle, if_pos rfl, mul_one] at h1
  rw [hB, Polynomial.coeff_map] at h1
  have h2 : (-1 : K) ^ i * algebraMap (ZMod p) K (A.coeff (A.natDegree - i))
      = (A.aroots K).esymm i := by
    rw [h1, ← mul_assoc, ← pow_add, show i + i = 2 * i by ring, pow_mul]
    norm_num
  rw [arootsK]
  exact h2.symm

/-- The `i`-th elementary symmetric function of the roots after shifting the coefficient of
`X ^ (n - D)` by one. -/
lemma esymm_arootsK_translate (p : ℕ) [Fact p.Prime] (A : Polynomial (ZMod p)) (hA : A.Monic)
    (D : ℕ) (hD1 : 1 ≤ D) (hDn : D ≤ A.natDegree) (i : ℕ) (hi : i ≤ A.natDegree) :
    (arootsK p (A + Polynomial.C 1 * Polynomial.X ^ (A.natDegree - D))).esymm i
      = (arootsK p A).esymm i + (if i = D then (-1 : AlgebraicClosure (ZMod p)) ^ i else 0) := by
  classical
  set K := AlgebraicClosure (ZMod p) with hK
  set τ := A + Polynomial.C 1 * Polynomial.X ^ (A.natDegree - D) with hτdef
  have hdeg_lt : (Polynomial.C 1 * Polynomial.X ^ (A.natDegree - D) : Polynomial (ZMod p)).degree
      < A.degree := by
    refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ 1) ?_
    rw [Polynomial.degree_eq_natDegree hA.ne_zero]
    exact_mod_cast (by omega : A.natDegree - D < A.natDegree)
  have hτmon : τ.Monic := hA.add_of_left hdeg_lt
  have hτdeg : τ.natDegree = A.natDegree := Polynomial.natDegree_add_eq_left_of_degree_lt hdeg_lt
  rw [esymm_arootsK p τ hτmon i (by rw [hτdeg]; exact hi), esymm_arootsK p A hA i hi, hτdeg]
  have hcoeff : τ.coeff (A.natDegree - i)
      = A.coeff (A.natDegree - i) + (if A.natDegree - i = A.natDegree - D then (1 : ZMod p) else 0) := by
    rw [hτdef, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
  rw [hcoeff]
  by_cases h : i = D
  · rw [if_pos h, if_pos (by rw [h]), map_add, map_one]
    ring
  · simp only [if_neg h,
      if_neg (fun hh : A.natDegree - i = A.natDegree - D => h (by omega)),
      add_zero, map_add, map_zero, mul_zero]

/-- **Affinity of the power sums in the shifted coefficient.** -/
lemma psumK_translate (p : ℕ) [Fact p.Prime] (D : ℕ) (A : Polynomial (ZMod p)) (hA : A.Monic)
    (hD1 : 1 ≤ D) (hDn : D ≤ A.natDegree) :
    ∀ k, 1 ≤ k → k ≤ D →
      psumK p (A + Polynomial.C 1 * Polynomial.X ^ (A.natDegree - D)) k
        = psumK p A k - (if k = D then (D : AlgebraicClosure (ZMod p)) else 0) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk1 hkD
    set K := AlgebraicClosure (ZMod p) with hK
    set τ := A + Polynomial.C 1 * Polynomial.X ^ (A.natDegree - D) with hτdef
    have hdeg_lt : (Polynomial.C 1 * Polynomial.X ^ (A.natDegree - D) : Polynomial (ZMod p)).degree
        < A.degree := by
      refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ 1) ?_
      rw [Polynomial.degree_eq_natDegree hA.ne_zero]
      exact_mod_cast (by omega : A.natDegree - D < A.natDegree)
    have hτmon : τ.Monic := hA.add_of_left hdeg_lt
    have hτdeg : τ.natDegree = A.natDegree := Polynomial.natDegree_add_eq_left_of_degree_lt hdeg_lt
    have hcardτ : (arootsK p τ).card = A.natDegree := by rw [arootsK_card p τ hτmon, hτdeg]
    have hcardA : (arootsK p A).card = A.natDegree := arootsK_card p A hA
    have hNτ := Commons.FieldTheory.Polynomial.multiset_psum_newton (arootsK p τ) k hk1
      (by rw [hcardτ]; omega)
    have hNA := Commons.FieldTheory.Polynomial.multiset_psum_newton (arootsK p A) k hk1
      (by rw [hcardA]; omega)
    -- the sums agree
    have hsum : (∑ i ∈ Finset.Icc 1 (k - 1),
          (-1 : K) ^ i * (arootsK p τ).esymm i
            * (Multiset.map (fun x => x ^ (k - i)) (arootsK p τ)).sum)
        = (∑ i ∈ Finset.Icc 1 (k - 1),
          (-1 : K) ^ i * (arootsK p A).esymm i
            * (Multiset.map (fun x => x ^ (k - i)) (arootsK p A)).sum) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hi2 : i ≤ k - 1 := (Finset.mem_Icc.mp hi).2
      have he : (arootsK p τ).esymm i = (arootsK p A).esymm i := by
        rw [esymm_arootsK_translate p A hA D hD1 hDn i (by omega),
          if_neg (by omega : i ≠ D), add_zero]
      have hp : (Multiset.map (fun x => x ^ (k - i)) (arootsK p τ)).sum
          = (Multiset.map (fun x => x ^ (k - i)) (arootsK p A)).sum := by
        have h2 := ih (k - i) (by omega) (by omega) (by omega)
        simp only [psumK] at h2
        rw [h2, if_neg (by omega : k - i ≠ D), sub_zero]
      rw [he, hp]
    have hesymmτ : (arootsK p τ).esymm k
        = (arootsK p A).esymm k + (if k = D then (-1 : K) ^ k else 0) :=
      esymm_arootsK_translate p A hA D hD1 hDn k (by omega)
    rw [hesymmτ] at hNτ
    have key : psumK p τ k = psumK p A k - (if k = D then (D : K) else 0) := by
      simp only [psumK]
      rw [hNτ, hsum, hNA]
      have h1 : (-1 : K) ^ (k + 1) * (-1 : K) ^ k = -1 := by
        rw [← pow_add, show k + 1 + k = 2 * k + 1 by omega, pow_succ, pow_mul]
        norm_num
      by_cases hk : k = D
      · rw [if_pos hk, if_pos hk, mul_add]
        have h2 : (-1 : K) ^ (k + 1) * (k : K) * (-1 : K) ^ k = -(k : K) := by
          calc (-1 : K) ^ (k + 1) * (k : K) * (-1 : K) ^ k
              = (-1 : K) ^ (k + 1) * ((-1 : K) ^ k * (k : K)) := by ring
            _ = ((-1 : K) ^ (k + 1) * (-1 : K) ^ k) * (k : K) := by ring
            _ = -1 * (k : K) := by rw [h1]
            _ = -(k : K) := by ring
        rw [h2, ← hk]
        ring
      · rw [if_neg hk, if_neg hk]; ring
    exact key

lemma rootSumK_eq_sum_psumK (p : ℕ) [Fact p.Prime] (g A : Polynomial (ZMod p)) (hA : A.Monic) :
    rootSumK p g A = ∑ k ∈ Finset.range (g.natDegree + 1),
      algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) (g.coeff k) * psumK p A k := by
  classical
  set K := AlgebraicClosure (ZMod p) with hK
  rw [rootSumK]
  have h1 : ∀ r : K,
      (g.map (algebraMap (ZMod p) K)).eval r
        = ∑ k ∈ Finset.range (g.natDegree + 1),
            algebraMap (ZMod p) K (g.coeff k) * r ^ k := by
    intro r
    rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
  rw [show (Multiset.map (fun r => (g.map (algebraMap (ZMod p) K)).eval r)
      (A.aroots K)).sum
      = (Multiset.map (fun r => ∑ k ∈ Finset.range (g.natDegree + 1),
            algebraMap (ZMod p) K (g.coeff k) * r ^ k) (A.aroots K)).sum from by
    congr 1
    exact Multiset.map_congr rfl (fun r _ => h1 r)]
  rw [Multiset.sum_map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Multiset.sum_map_mul_left]
  rfl


/-- Norm of a nonnegative real, viewed as a complex number. -/
lemma norm_coe_real (r : ℝ) (hr : 0 ≤ r) : ‖(r:ℂ)‖ = r := by
  have h2 : ‖(r:ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
  nlinarith [norm_nonneg (r:ℂ)]

open Filter Topology in
/-- Cesàro mean of a unit-modulus geometric sequence. -/
lemma tendsto_cesaro_pow {γ : ℂ} (hγ : ‖γ‖ = 1) :
    Tendsto (fun M : ℕ => (M:ℂ)⁻¹ * ∑ m ∈ Finset.range M, γ ^ m) atTop
      (𝓝 (if γ = 1 then 1 else 0)) := by
  rcases eq_or_ne γ 1 with h | h
  · subst h
    rw [if_pos rfl]
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_gt_atTop 0] with M hM
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hM' : (M:ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    field_simp
  · rw [if_neg h]
    have hinv : Tendsto (fun M : ℕ => (M:ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hb : Tendsto (fun M : ℕ => (2 / ‖1 - γ‖) * (M:ℝ)⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hinv :
        Tendsto (fun M : ℕ => (2 / ‖1 - γ‖) * (M:ℝ)⁻¹) atTop (𝓝 ((2/‖1-γ‖) * 0)))
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_gt_atTop 0] with M hM
    have h3 : 0 < ‖1 - γ‖ := by
      rw [norm_pos_iff]; intro hc
      exact h (by rw [sub_eq_zero] at hc; exact hc.symm)
    have h2 : ‖γ ^ M - 1‖ ≤ 2 := by
      calc ‖γ ^ M - 1‖ ≤ ‖γ ^ M‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ = 1 + 1 := by rw [norm_pow, hγ, one_pow, norm_one]
        _ = 2 := by ring
    calc ‖(M:ℂ)⁻¹ * ∑ m ∈ Finset.range M, γ ^ m‖
        = (M:ℝ)⁻¹ * (‖γ ^ M - 1‖ / ‖γ - 1‖) := by
          rw [geom_sum_eq h, norm_mul, norm_inv, Complex.norm_natCast, norm_div]
      _ ≤ (M:ℝ)⁻¹ * (2 / ‖1 - γ‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [show ‖γ - 1‖ = ‖1 - γ‖ by rw [← norm_neg, neg_sub]]
          exact div_le_div_of_nonneg_right h2 h3.le
      _ = (2 / ‖1 - γ‖) * (M:ℝ)⁻¹ := by ring

open Filter Topology in
lemma tendsto_cesaro_zero {a : ℕ → ℂ} (h : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun M : ℕ => (M:ℂ)⁻¹ * ∑ m ∈ Finset.range M, a m) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop] at h ⊢
  intro ε hε
  have hε4 : 0 < ε / 4 := by linarith
  obtain ⟨N, hN⟩ := h (ε / 4) hε4
  set S : ℝ := ∑ m ∈ Finset.range N, ‖a m‖ with hS
  refine ⟨max N (Nat.ceil (4*S/ε) + 1), fun M hM => ?_⟩
  rw [dist_eq_norm, sub_zero]
  have hMN : N ≤ M := le_trans (le_max_left _ _) hM
  have hMpos : 0 < M := by omega
  have hMge : 4*S/ε ≤ (M:ℝ) := by
    have h1 : Nat.ceil (4*S/ε) + 1 ≤ M := le_trans (le_max_right _ _) hM
    have h2 : (Nat.ceil (4*S/ε) : ℝ) ≤ (M:ℝ) := by
      exact_mod_cast le_trans (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h1)) le_rfl
    exact le_trans (Nat.le_ceil _) h2
  have hsplit : ∑ m ∈ Finset.range M, ‖a m‖ = S + ∑ m ∈ Finset.Ico N M, ‖a m‖ := by
    rw [hS]
    exact (Finset.sum_range_add_sum_Ico (fun m => ‖a m‖) hMN).symm
  have htail : ∑ m ∈ Finset.Ico N M, ‖a m‖ ≤ ((M - N : ℕ) : ℝ) * (ε/4) := by
    calc ∑ m ∈ Finset.Ico N M, ‖a m‖ ≤ ∑ _m ∈ Finset.Ico N M, (ε/4) := by
          refine Finset.sum_le_sum fun m hm => ?_
          exact le_of_lt (by simpa [dist_eq_norm] using hN m (Finset.mem_Ico.mp hm).1)
      _ = ((M - N : ℕ) : ℝ) * (ε/4) := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]
  have hMle : ((M - N : ℕ) : ℝ) ≤ (M:ℝ) := by
    rw [Nat.cast_sub hMN]
    have : (0:ℝ) ≤ (N:ℝ) := by positivity
    linarith
  calc ‖(M:ℂ)⁻¹ * ∑ m ∈ Finset.range M, a m‖
      ≤ (M:ℝ)⁻¹ * ∑ m ∈ Finset.range M, ‖a m‖ := by
        rw [norm_mul, norm_inv, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = (M:ℝ)⁻¹ * (S + ∑ m ∈ Finset.Ico N M, ‖a m‖) := by rw [hsplit]
    _ ≤ (M:ℝ)⁻¹ * (S + ((M - N : ℕ) : ℝ) * (ε/4)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact add_le_add (le_refl S) htail
    _ ≤ ε / 4 + ε / 4 := by
        have h1 : (M:ℝ)⁻¹ * S ≤ ε / 4 := by
          rw [inv_mul_le_iff₀ (by positivity : (0:ℝ) < (M:ℝ))]
          have hSe : S = ε/4 * (4*S/ε) := by field_simp
          calc S = ε/4 * (4*S/ε) := hSe
            _ ≤ ε/4 * (M:ℝ) := mul_le_mul_of_nonneg_left hMge hε4.le
            _ = (M:ℝ) * (ε/4) := by ring
        have h2 : (M:ℝ)⁻¹ * (((M - N : ℕ) : ℝ) * (ε/4)) ≤ ε / 4 := by
          rw [← mul_assoc]
          calc (M:ℝ)⁻¹ * ((M - N : ℕ) : ℝ) * (ε/4) ≤ (M:ℝ)⁻¹ * (M:ℝ) * (ε/4) := by
                refine mul_le_mul_of_nonneg_right ?_ hε4.le
                exact mul_le_mul_of_nonneg_left hMle (by positivity)
              _ = ε/4 := by field_simp
        rw [mul_add]; linarith [h1, h2]
    _ < ε := by linarith

open Filter Topology in
lemma unitExp_level_sum_eq_one {ι : Type*} [Fintype ι] {c β : ι → ℂ} (hβ : ∀ i, ‖β i‖ = 1)
    (h : Tendsto (fun m : ℕ => ∑ i, c i * β i ^ m) atTop (𝓝 0)) :
    ∑ i ∈ Finset.univ.filter (fun i => β i = 1), c i = 0 := by
  have hces := tendsto_cesaro_zero h
  have heq : ∀ M : ℕ, (M:ℂ)⁻¹ * ∑ m ∈ Finset.range M, ∑ i, c i * β i ^ m
      = ∑ i, c i * ((M:ℂ)⁻¹ * ∑ m ∈ Finset.range M, β i ^ m) := by
    intro M
    rw [Finset.mul_sum]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [funext heq] at hces
  have hkey : Tendsto (fun M : ℕ => ∑ i, c i * ((M:ℂ)⁻¹ * ∑ m ∈ Finset.range M, β i ^ m))
      atTop (𝓝 (∑ i, c i * (if β i = 1 then 1 else 0))) := by
    refine tendsto_finsetSum Finset.univ (fun i _ => ?_)
    exact (tendsto_cesaro_pow (hβ i)).const_mul (c i)
  have hlim : (∑ i, c i * (if β i = 1 then 1 else 0)) = 0 := tendsto_nhds_unique hkey hces
  rw [← hlim, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : β i = 1
  · rw [if_pos hi, if_pos hi, mul_one]
  · rw [if_neg hi, if_neg hi, mul_zero]

open Filter Topology in
/-- Multiplying a sequence tending to `0` by the powers of a unit-modulus number keeps it
tending to `0`. -/
lemma tendsto_unit_pow_mul {a : ℂ} (ha : ‖a‖ = 1) {f : ℕ → ℂ} (hf : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun m : ℕ => a ^ m * f m) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero] at hf ⊢
  refine hf.congr' (Eventually.of_forall fun m => ?_)
  simp only [norm_mul, norm_pow, ha, one_pow, one_mul]

open Filter Topology in
/-- **Level-set lemma.**  If `∑ i, c i * β i ^ m → 0` with `‖β i‖ = 1`, then the `c i` sum to
zero over each level set of `β`. -/
lemma unitExp_level_sum_eq_zero {ι : Type*} [Fintype ι] {c β : ι → ℂ} (hβ : ∀ i, ‖β i‖ = 1)
    (h : Tendsto (fun m : ℕ => ∑ i, c i * β i ^ m) atTop (𝓝 0)) (i₀ : ι) :
    ∑ i ∈ Finset.univ.filter (fun i => β i = β i₀), c i = 0 := by
  have hβi₀ : β i₀ ≠ 0 := by
    intro h0; have := hβ i₀; rw [h0, norm_zero] at this; exact one_ne_zero this.symm
  have hmain : Tendsto (fun m : ℕ => ∑ i, c i * (β i / β i₀) ^ m) atTop (𝓝 0) := by
    have h2 : (fun m : ℕ => (β i₀)⁻¹ ^ m * ∑ i, c i * β i ^ m)
        = fun m : ℕ => ∑ i, c i * (β i / β i₀) ^ m := by
      funext m
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [div_pow, inv_pow]
      ring
    rw [← h2]
    exact tendsto_unit_pow_mul (by rw [norm_inv, hβ i₀, inv_one]) h
  have hlev := unitExp_level_sum_eq_one (c := c) (β := fun i => β i / β i₀)
    (fun i => by rw [norm_div, hβ i, hβ i₀, div_one]) hmain
  rw [← hlev]
  refine Finset.sum_congr ?_ fun i _ => rfl
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi; rw [hi, div_self hβi₀]
  · intro hi; rwa [div_eq_one_iff_eq hβi₀] at hi

open Filter Topology in
/-- Subtype form of the level-set lemma: the `c i` sum to zero over the level set of `β` at `i₀`. -/
lemma unitExp_level_sum_eq_zero' {ι : Type*} [Fintype ι] {c β : ι → ℂ} (hβ : ∀ i, ‖β i‖ = 1)
    (h : Tendsto (fun m : ℕ => ∑ i, c i * β i ^ m) atTop (𝓝 0)) (i₀ : ι) :
    ∑ i : {i : ι // β i = β i₀}, c i.1 = 0 := by
  have h1 := unitExp_level_sum_eq_zero (c := c) (β := β) hβ h i₀
  rwa [Finset.sum_subtype (s := Finset.univ.filter (fun i => β i = β i₀))
    (p := fun i => β i = β i₀) (fun x => by simp) c] at h1

/-- **Power sums of unit-modulus numbers.**  If `‖z i‖ = 1` for all `i` and the power sums
`∑ i, z i ^ k` vanish for `k = 1, …, #ι`, then `ι` is empty. -/
lemma card_eq_zero_of_unit_power_sums {ι : Type*} [Fintype ι] (z : ι → ℂ)
    (hz : ∀ i, ‖z i‖ = 1)
    (h : ∀ k : ℕ, 1 ≤ k → k ≤ Fintype.card ι → ∑ i, z i ^ k = 0) :
    Fintype.card ι = 0 := by
  classical
  by_contra hne
  have hpos : 0 < Fintype.card ι := Nat.pos_of_ne_zero hne
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with hedef
  set z' : Fin (Fintype.card ι) → ℂ := fun j => z (e.symm j) with hz'def
  have hne' : ∀ j : ℕ, 1 ≤ j → j ≤ Fintype.card ι → ((-1 : ℂ) ^ (j + 1)) * (j : ℂ) ≠ 0 := by
    intro j hj1 hj2
    have hj : (j : ℂ) ≠ 0 := by
      have : j ≠ 0 := by omega
      exact_mod_cast this
    simp [hj]
  have hpow : ∀ m : ℕ, 1 ≤ m → m ≤ Fintype.card ι →
      (∑ i, z' i ^ m) = ∑ _i : Fin (Fintype.card ι), (0:ℂ) ^ m := by
    intro m hm1 hm2
    have h1 : (∑ i : Fin (Fintype.card ι), z' i ^ m) = ∑ i : ι, z i ^ m := by
      refine Fintype.sum_equiv e.symm (fun i : Fin (Fintype.card ι) => z' i ^ m)
        (fun i : ι => z i ^ m) (fun i => ?_)
      simp [hz'def]
    rw [h1, h m hm1 hm2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      zero_pow (by omega : m ≠ 0), mul_zero]
  have hmain := Commons.Algebra.Polynomial.power_sums_determine_multiset_domain hne' z'
    (fun _ : Fin (Fintype.card ι) => (0:ℂ)) hpow
  have hmem : z' ⟨0, hpos⟩ ∈ (Finset.univ.val.map z') :=
    Multiset.mem_map.mpr ⟨⟨0, hpos⟩, by simp, rfl⟩
  rw [hmain] at hmem
  simp only [Multiset.map_const'] at hmem
  have h0 : z' ⟨0, hpos⟩ = 0 := (Multiset.mem_replicate.mp hmem).2
  have hn1 : ‖z' ⟨0, hpos⟩‖ = 1 := hz _
  rw [h0, norm_zero] at hn1
  exact one_ne_zero hn1.symm



open Filter Topology in
/-- The transference: if the even Artin--Schreier sums are the power sums of at most `t < p`
numbers and are `O(p^k)` for `k` coprime to `p`, then each number has modulus at most `p`. -/
lemma addchar_pow_sum_transference {p : ℕ} [Fact p.Prime] {t : ℕ} (ht : t < p) (γ : Fin t → ℂ)
    {C : ℝ} (hC : 0 < C)
    (h : ∀ k : ℕ, 0 < k → ¬ p ∣ k → ‖∑ j : Fin t, (γ j ^ 2) ^ k‖ ≤ C * (p:ℝ) ^ k) :
    ∀ j : Fin t, ‖γ j ^ 2‖ ≤ (p:ℝ) := by
  rcases Nat.eq_zero_or_pos t with ht0 | htpos
  · subst ht0
    intro j
    exact j.elim0
  intro j
  by_contra hj
  push_neg at hj
  haveI : NeZero t := ⟨by omega⟩
  obtain ⟨j₁, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin t)) (fun j => ‖γ j ^ 2‖)
      Finset.univ_nonempty
  set R : ℝ := ‖γ j₁ ^ 2‖ with hRdef
  have hle : ∀ j, ‖γ j ^ 2‖ ≤ R := fun j => hmax j (Finset.mem_univ j)
  have hpR : (p:ℝ) < R := lt_of_lt_of_le hj (hmax j (Finset.mem_univ j))
  have hppos : (0:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hRpos : 0 < R := lt_trans hppos hpR
  set S : Finset (Fin t) := Finset.univ.filter (fun j => ‖γ j ^ 2‖ = R) with hS
  have hj₁S : j₁ ∈ S := by simp [hS, hRdef]
  set w : Fin t → ℂ := fun j => γ j ^ 2 / (R:ℂ) with hwdef
  have hwnorm : ∀ j, ‖w j‖ = ‖γ j ^ 2‖ / R := by
    intro j
    rw [hwdef, norm_div, norm_coe_real R hRpos.le]
  have hwle : ∀ j, ‖w j‖ ≤ 1 := by
    intro j
    rw [hwnorm j]
    exact div_le_one_of_le₀ (hle j) hRpos.le
  have hwnormS : ∀ j ∈ S, ‖w j‖ = 1 := by
    intro j hj
    rw [hwnorm j, (Finset.mem_filter.mp hj).2, div_self (ne_of_gt hRpos)]
  have hboundK : ∀ K : ℕ, 0 < K → ¬ p ∣ K → ‖∑ j : Fin t, w j ^ K‖ ≤ C * ((p:ℝ)/R) ^ K := by
    intro K hK hKp
    have h1 : (∑ j : Fin t, w j ^ K) = (∑ j : Fin t, (γ j ^ 2) ^ K) / (R:ℂ) ^ K := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hwdef, div_pow]
    rw [h1, norm_div, norm_pow, norm_coe_real R hRpos.le, div_pow]
    refine le_trans (div_le_div_of_nonneg_right (h K hK hKp) (by positivity)) (le_of_eq ?_)
    ring
  have hgeo : Tendsto (fun m : ℕ => ((p:ℝ)/R) ^ (m * p)) atTop (𝓝 0) := by
    have h0 : 0 ≤ ((p:ℝ)/R) ^ p := by positivity
    have h1 : ((p:ℝ)/R) ^ p < 1 := by
      rw [div_pow, div_lt_one (by positivity : (0:ℝ) < R ^ p)]
      exact pow_lt_pow_left₀ hpR (by positivity) (by omega : p ≠ 0)
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
    have hfun : (fun m : ℕ => ((p:ℝ)/R) ^ (m*p)) = fun m : ℕ => (((p:ℝ)/R)^p)^m := by
      funext m
      rw [← pow_mul, Nat.mul_comm m p]
    rw [hfun]
    exact h
  have huniv : ∀ k : ℕ, 0 < k → ¬ p ∣ k →
      Tendsto (fun m : ℕ => ∑ j : Fin t, w j ^ (k + m*p)) atTop (𝓝 0) := by
    intro k hk hkp
    have hbk : ∀ m : ℕ, ‖∑ j : Fin t, w j ^ (k + m*p)‖
        ≤ (C * ((p:ℝ)/R)^k) * ((p:ℝ)/R) ^ (m*p) := by
      intro m
      have hkp' : ¬ p ∣ k + m*p := by
        intro hd
        have h1 : p ∣ m * p := dvd_mul_left p m
        have h2 : p ∣ (k + m*p) - m*p := Nat.dvd_sub hd h1
        exact hkp (by rwa [Nat.add_sub_cancel_right] at h2)
      have hb := hboundK (k + m*p) (by omega) hkp'
      rw [pow_add] at hb
      refine le_trans hb (le_of_eq ?_)
      rw [Nat.mul_comm m p]; ring
    refine squeeze_zero_norm' (Eventually.of_forall hbk) ?_
    have hg2 : Tendsto (fun m : ℕ => (C * ((p:ℝ)/R)^k) * ((p:ℝ)/R)^(m*p)) atTop (𝓝 0) := by
      simpa using hgeo.const_mul (C * ((p:ℝ)/R)^k)
    exact hg2
  have hcompl : ∀ k : ℕ, 0 < k → ¬ p ∣ k →
      Tendsto (fun m : ℕ => ∑ j ∈ Sᶜ, w j ^ (k + m*p)) atTop (𝓝 0) := by
    intro k hk hkp
    have hinner : ∀ j ∈ Sᶜ, Tendsto (fun m : ℕ => w j ^ (k + m*p)) atTop (𝓝 0) := by
      intro j hj
      have hjS : j ∉ S := by simpa using hj
      have hwj : ‖w j‖ < 1 := by
        refine lt_of_le_of_ne (hwle j) ?_
        intro hcontra
        have h2 : ‖γ j ^ 2‖ / R = 1 := by rw [← hwnorm j, hcontra]
        have h3 : ‖γ j ^ 2‖ = R := (div_eq_one_iff_eq (ne_of_gt hRpos)).mp h2
        exact hjS (by simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]; exact h3)
      have h1 : Tendsto (fun m : ℕ => (w j)^k * ((w j)^p)^m) atTop (𝓝 0) := by
        have hltp : ‖(w j)^p‖ < 1 := by
          rw [norm_pow]
          exact pow_lt_one₀ (norm_nonneg _) hwj (by omega : p ≠ 0)
        simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hltp).const_mul ((w j)^k)
      refine h1.congr' (Eventually.of_forall fun m => ?_)
      show (w j)^k * ((w j)^p)^m = w j ^ (k + m*p)
      rw [← pow_mul, ← pow_add, Nat.mul_comm p m]
    have hsum := tendsto_finsetSum (s := Sᶜ) (f := fun j m => w j ^ (k + m*p))
      (a := fun _ => (0:ℂ)) (x := atTop) hinner
    simpa using hsum
  have hS_tend : ∀ k : ℕ, 0 < k → ¬ p ∣ k →
      Tendsto (fun m : ℕ => ∑ j ∈ S, w j ^ (k + m*p)) atTop (𝓝 0) := by
    intro k hk hkp
    have h1 : (fun m : ℕ => ∑ j ∈ S, w j ^ (k + m*p))
        = fun m : ℕ => (∑ j : Fin t, w j ^ (k + m*p)) - ∑ j ∈ Sᶜ, w j ^ (k + m*p) := by
      funext m
      have := Finset.sum_compl_add_sum (s := S) (f := fun j => w j ^ (k + m*p))
      rw [← this]
      ring
    rw [h1]
    simpa using ((huniv k hk hkp).sub (hcompl k hk hkp))
  -- reindex over `S`
  have hkey : ∀ k : ℕ, 0 < k → ¬ p ∣ k →
      Tendsto (fun m : ℕ => ∑ j : {j : Fin t // j ∈ S}, (w j.1) ^ k * ((w j.1) ^ p) ^ m)
        atTop (𝓝 0) := by
    intro k hk hkp
    have h2 : (fun m : ℕ => ∑ j : {j : Fin t // j ∈ S}, (w j.1) ^ k * ((w j.1) ^ p) ^ m)
        = fun m : ℕ => ∑ j : {j : Fin t // j ∈ S}, w j.1 ^ (k + m*p) := by
      funext m
      refine Finset.sum_congr rfl fun j _ => ?_
      show (w ↑j) ^ k * ((w ↑j) ^ p) ^ m = (w ↑j) ^ (k + m*p)
      rw [← pow_mul, ← pow_add, Nat.mul_comm p m]
    rw [h2]
    have h3 : (fun m : ℕ => ∑ j : {j : Fin t // j ∈ S}, w j.1 ^ (k + m*p))
        = fun m : ℕ => ∑ j ∈ S, w j ^ (k + m*p) := by
      funext m
      exact (Finset.sum_subtype S (fun x => Iff.rfl) (fun j => w j ^ (k + m*p))).symm
    rw [h3]
    exact hS_tend k hk hkp
  -- the level-set sums vanish
  have hlevel : ∀ k : ℕ, 0 < k → ¬ p ∣ k →
      ∑ i : {i : {j : Fin t // j ∈ S} // (w i.1) ^ p = (w j₁) ^ p}, (w i.1.1) ^ k = 0 := by
    intro k hk hkp
    exact unitExp_level_sum_eq_zero'
      (c := fun i : {j : Fin t // j ∈ S} => (w i.1) ^ k)
      (β := fun i : {j : Fin t // j ∈ S} => (w i.1) ^ p)
      (fun i => by rw [norm_pow, hwnormS i.1 i.2, one_pow]) (hkey k hk hkp) ⟨j₁, hj₁S⟩
  -- cardinality bound for the level set
  have hcardT : Fintype.card {i : {j : Fin t // j ∈ S} // (w i.1) ^ p = (w j₁) ^ p} ≤ t := by
    have h1 : Fintype.card {i : {j : Fin t // j ∈ S} // (w i.1) ^ p = (w j₁) ^ p}
        ≤ Fintype.card {j : Fin t // j ∈ S} :=
      Fintype.card_le_of_injective
        (fun i : {i : {j : Fin t // j ∈ S} // (w i.1) ^ p = (w j₁) ^ p} => i.1)
        (fun a b hab => Subtype.ext hab)
    have h2 : Fintype.card {j : Fin t // j ∈ S} = S.card := Fintype.card_coe S
    have h3 : S.card ≤ t := by
      calc S.card ≤ (Finset.univ : Finset (Fin t)).card :=
            Finset.card_le_card (Finset.subset_univ S)
        _ = t := by simp
    omega
  have hzero : Fintype.card {i : {j : Fin t // j ∈ S} // (w i.1) ^ p = (w j₁) ^ p} = 0 := by
    refine card_eq_zero_of_unit_power_sums
      (fun i : {i : {j : Fin t // j ∈ S} // (w i.1) ^ p = (w j₁) ^ p} => w i.1.1)
      (fun i => hwnormS i.1.1 i.1.2) (fun k hk1 hk2 => ?_)
    have hkp : ¬ p ∣ k := by
      intro hd
      have h4 : p ≤ k := Nat.le_of_dvd hk1 hd
      have h5 : k ≤ Fintype.card {i : {j : Fin t // j ∈ S} // (w i.1) ^ p = (w j₁) ^ p} := hk2
      omega
    exact hlevel k hk1 hkp
  haveI : Nonempty {i : {j : Fin t // j ∈ S} // (w i.1) ^ p = (w j₁) ^ p} :=
    ⟨⟨⟨j₁, hj₁S⟩, rfl⟩⟩
  have hpos : 0 < Fintype.card {i : {j : Fin t // j ∈ S} // (w i.1) ^ p = (w j₁) ^ p} :=
    Fintype.card_pos
  omega



/-! ## The Artin--Schreier `L`-function: coefficients and their vanishing -/

/-- A nontrivial additive character of `ZMod p` takes the value `1` only at `0`. -/
lemma addchar_apply_eq_one_iff (p : ℕ) [Fact p.Prime] (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    {y : ZMod p} : ψ y = 1 ↔ y = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, AddChar.map_zero_eq_one]⟩
  by_contra hy
  have hgen : ∀ x : ZMod p, ψ x = 1 := by
    intro x
    obtain ⟨m, hm⟩ := ZMod.intCast_surjective (x * y⁻¹)
    have hxy : x = (m : ZMod p) * y := by rw [hm, mul_assoc, inv_mul_cancel₀ hy, mul_one]
    rw [hxy, ← zsmul_eq_mul y m, AddChar.map_zsmul_eq_zpow, h, one_zpow]
  exact hψ (AddChar.ext ψ 1 fun x => by rw [hgen x, AddChar.one_apply])

/-- The `0`-th power sum of the roots of a monic polynomial is its degree. -/
lemma psumK_zero (p : ℕ) [Fact p.Prime] (A : Polynomial (ZMod p)) (hA : A.Monic) :
    psumK p A 0 = ((A.natDegree : ℕ) : AlgebraicClosure (ZMod p)) := by
  rw [psumK]
  rw [show (arootsK p A).map (fun r => r ^ 0)
      = (arootsK p A).map (fun _ => (1 : AlgebraicClosure (ZMod p))) from
    Multiset.map_congr rfl fun r _ => pow_zero r]
  rw [Multiset.map_const', Multiset.sum_replicate, arootsK_card p A hA, nsmul_eq_mul, mul_one]

/-- Shifting the coefficient of `X ^ (deg A - deg g)` shifts the root sum by `- deg g`. -/
lemma asTrace_translate (p : ℕ) [Fact p.Prime] (g A : Polynomial (ZMod p)) (hA : A.Monic)
    (hg1 : 1 ≤ g.natDegree) (hgn : g.natDegree ≤ A.natDegree) :
    asTrace p g (A + Polynomial.C 1 * Polynomial.X ^ (A.natDegree - g.natDegree))
      = asTrace p g A - g.coeff g.natDegree * (g.natDegree : ZMod p) := by
  classical
  set K := AlgebraicClosure (ZMod p) with hK
  set τ := A + Polynomial.C 1 * Polynomial.X ^ (A.natDegree - g.natDegree) with hτ
  have hdeg_lt : (Polynomial.C 1 * Polynomial.X ^ (A.natDegree - g.natDegree)
      : Polynomial (ZMod p)).degree < A.degree := by
    refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ 1) ?_
    rw [Polynomial.degree_eq_natDegree hA.ne_zero]
    exact_mod_cast (by omega : A.natDegree - g.natDegree < A.natDegree)
  have hτmon : τ.Monic := hA.add_of_left hdeg_lt
  have hτdeg : τ.natDegree = A.natDegree := Polynomial.natDegree_add_eq_left_of_degree_lt hdeg_lt
  refine FaithfulSMul.algebraMap_injective (ZMod p) K ?_
  rw [map_sub, map_mul, map_natCast, asTrace_spec p g A hA, asTrace_spec p g τ hτmon,
    rootSumK_eq_sum_psumK p g A hA, rootSumK_eq_sum_psumK p g τ hτmon,
    show τ = A + Polynomial.C 1 * Polynomial.X ^ (A.natDegree - g.natDegree) from hτ]
  have hpt : ∀ k ∈ Finset.range (g.natDegree + 1),
      algebraMap (ZMod p) K (g.coeff k) * psumK p (A + Polynomial.C 1 *
          Polynomial.X ^ (A.natDegree - g.natDegree)) k
        = algebraMap (ZMod p) K (g.coeff k) * psumK p A k
          - (if k = g.natDegree then algebraMap (ZMod p) K (g.coeff k) * (g.natDegree : K)
              else 0) := by
    intro k hk
    have hkD : k ≤ g.natDegree := by have := Finset.mem_range.mp hk; omega
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      rw [if_neg (by omega : ¬ ((0 : ℕ) = g.natDegree)), sub_zero]
      rw [psumK_zero p A hA, psumK_zero p τ hτmon, hτdeg]
    · rw [psumK_translate p g.natDegree A hA hg1 hgn k hkpos hkD, mul_sub]
      by_cases hkk : k = g.natDegree <;> simp [hkk]
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (Nat.lt_succ_self _))]

/-- Adding `1` to the `j`-th coefficient of the coefficient vector of a monic polynomial. -/
lemma repPoly_add_single {R : Type*} [CommSemiring R] (n : ℕ) (c : Fin n → R) (j : Fin n) :
    Commons.FieldTheory.Polynomial.repPoly n (c + Pi.single j 1)
      = Commons.FieldTheory.Polynomial.repPoly n c + Polynomial.C 1 * Polynomial.X ^ (j : ℕ) := by
  unfold Commons.FieldTheory.Polynomial.repPoly
  have h1 : (∑ i : Fin n, Polynomial.C ((c + (Pi.single j (1 : R) : Fin n → R)) i)
        * Polynomial.X ^ (i : ℕ))
      = (∑ i : Fin n, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ))
        + ∑ i : Fin n, Polynomial.C (((Pi.single j (1 : R) : Fin n → R)) i)
            * Polynomial.X ^ (i : ℕ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.add_apply, Polynomial.C_add, add_mul]
  rw [h1, add_assoc]
  congr 1
  rw [show (∑ i : Fin n, Polynomial.C (((Pi.single j (1 : R) : Fin n → R)) i)
        * Polynomial.X ^ (i : ℕ)) = Polynomial.C 1 * Polynomial.X ^ (j : ℕ) from by
    rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same]
    · intro b _ hb
      have hb' : ((Pi.single j (1 : R) : Fin n → R)) b = 0 := by
        rw [Pi.single_eq_of_ne]
        exact hb
      rw [hb', map_zero, zero_mul]
    · intro hj; exact absurd (Finset.mem_univ j) hj]

/-- The `L`-polynomial coefficient `C_m = ∑_{A monic, deg A = m} Ψ(A)`. -/
noncomputable def Cm (p : ℕ) [Fact p.Prime] (ψ : AddChar (ZMod p) ℂ) (g : Polynomial (ZMod p))
    (m : ℕ) : ℂ :=
  ∑ c : Fin m → ZMod p, psiAS p ψ g (Commons.FieldTheory.Polynomial.repPoly m c)

/-- Pointwise shift identity for the `L`-function weight. -/
lemma psiAS_add_single (p : ℕ) [Fact p.Prime] (ψ : AddChar (ZMod p) ℂ) (g : Polynomial (ZMod p))
    (hg : 1 ≤ g.natDegree) {n : ℕ} (hn : g.natDegree ≤ n) (c : Fin n → ZMod p) (j : Fin n)
    (hj : (j : ℕ) = n - g.natDegree) :
    psiAS p ψ g (Commons.FieldTheory.Polynomial.repPoly n (c + Pi.single j 1))
      = ψ (-(g.coeff g.natDegree * (g.natDegree : ZMod p)))
          * psiAS p ψ g (Commons.FieldTheory.Polynomial.repPoly n c) := by
  rw [repPoly_add_single n c j, hj]
  have hdeg_lt : (Polynomial.C 1 * Polynomial.X ^ (n - g.natDegree)
      : Polynomial (ZMod p)).degree
      < (Commons.FieldTheory.Polynomial.repPoly n c).degree := by
    refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ 1) ?_
    rw [Polynomial.degree_eq_natDegree (Commons.FieldTheory.Polynomial.repPoly_monic n c).ne_zero,
      Commons.FieldTheory.Polynomial.repPoly_natDegree]
    exact_mod_cast (by omega : n - g.natDegree < n)
  have hmon : (Commons.FieldTheory.Polynomial.repPoly n c
      + Polynomial.C 1 * Polynomial.X ^ (n - g.natDegree)).Monic :=
    (Commons.FieldTheory.Polynomial.repPoly_monic n c).add_of_left hdeg_lt
  have hnt : n - g.natDegree
      = (Commons.FieldTheory.Polynomial.repPoly n c).natDegree - g.natDegree := by
    rw [Commons.FieldTheory.Polynomial.repPoly_natDegree]
  rw [psiAS, if_pos hmon, psiAS, if_pos (Commons.FieldTheory.Polynomial.repPoly_monic n c),
    hnt,
    asTrace_translate p g (Commons.FieldTheory.Polynomial.repPoly n c)
      (Commons.FieldTheory.Polynomial.repPoly_monic n c) hg
      (by rw [Commons.FieldTheory.Polynomial.repPoly_natDegree]; exact hn),
    sub_eq_add_neg, AddChar.map_add_eq_mul, mul_comm]

/-- **Vanishing of the `L`-function coefficients** in degrees `≥ deg g`. -/
theorem Cm_eq_zero (p : ℕ) [Fact p.Prime] (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    (g : Polynomial (ZMod p)) (hg : 1 ≤ g.natDegree) (hgp : g.natDegree < p)
    {n : ℕ} (hn : g.natDegree ≤ n) : Cm p ψ g n = 0 := by
  classical
  have hg0 : g ≠ 0 := by rintro rfl; simp at hg
  have hlc : g.coeff g.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hg0
  have hD0 : (g.natDegree : ZMod p) ≠ 0 := by
    intro h0
    exact absurd (Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff g.natDegree p).mp h0))
      (by omega)
  have hne : g.coeff g.natDegree * (g.natDegree : ZMod p) ≠ 0 := mul_ne_zero hlc hD0
  have hψne : ψ (-(g.coeff g.natDegree * (g.natDegree : ZMod p))) ≠ 1 := by
    intro h
    exact hne (neg_eq_zero.mp ((addchar_apply_eq_one_iff p ψ hψ).mp h))
  set j : Fin n := ⟨n - g.natDegree, by omega⟩ with hj
  have hjval : (j : ℕ) = n - g.natDegree := by rw [hj]
  have hbij : (∑ c : Fin n → ZMod p,
        psiAS p ψ g (Commons.FieldTheory.Polynomial.repPoly n (c + Pi.single j 1)))
      = ∑ c : Fin n → ZMod p,
          psiAS p ψ g (Commons.FieldTheory.Polynomial.repPoly n c) :=
    Equiv.sum_comp (Equiv.addRight (Pi.single j (1 : ZMod p) : Fin n → ZMod p))
      (fun c => psiAS p ψ g (Commons.FieldTheory.Polynomial.repPoly n c))
  have hstep : Cm p ψ g n
      = ψ (-(g.coeff g.natDegree * (g.natDegree : ZMod p))) * Cm p ψ g n := by
    have hmain : Cm p ψ g n = ∑ c : Fin n → ZMod p,
        ψ (-(g.coeff g.natDegree * (g.natDegree : ZMod p)))
          * psiAS p ψ g (Commons.FieldTheory.Polynomial.repPoly n c) := by
      rw [Cm, ← hbij]
      exact Finset.sum_congr rfl fun c _ => psiAS_add_single p ψ g hg hn c j hjval
    calc Cm p ψ g n
        = ∑ c : Fin n → ZMod p, ψ (-(g.coeff g.natDegree * (g.natDegree : ZMod p)))
            * psiAS p ψ g (Commons.FieldTheory.Polynomial.repPoly n c) := hmain
      _ = ψ (-(g.coeff g.natDegree * (g.natDegree : ZMod p)))
            * ∑ c : Fin n → ZMod p,
                psiAS p ψ g (Commons.FieldTheory.Polynomial.repPoly n c) := by
          rw [Finset.mul_sum]
      _ = ψ (-(g.coeff g.natDegree * (g.natDegree : ZMod p))) * Cm p ψ g n := by rw [Cm]
  have h1 : (1 - ψ (-(g.coeff g.natDegree * (g.natDegree : ZMod p)))) * Cm p ψ g n = 0 := by
    rw [sub_mul, one_mul, ← hstep, sub_self]
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hψne
  · exact h



/-! ## Step 2: the Euler product and the recurrence for the power sums -/

/-- The log-derivative coefficients of the `L`-function:
`S_N = ∑_{d ∣ N} d ∑_{deg P = d, P irred.} Ψ(P) ^ (N / d)`. -/
noncomputable def Sm (p : ℕ) [Fact p.Prime] (ψ : AddChar (ZMod p) ℂ) (g : Polynomial (ZMod p))
    (N : ℕ) : ℂ := by
  classical
  exact ∑ d ∈ N.divisors, (d : ℂ) * ∑ c : Fin d → ZMod p,
    if Irreducible (Polynomial.X ^ d + ∑ i : Fin d, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ))
      then (psiAS p ψ g
        (Polynomial.X ^ d + ∑ i : Fin d, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ))) ^ (N / d)
      else 0

/-- The `L`-polynomial `L(T) = ∑_{m < deg g} C_m T ^ m`. -/
noncomputable def Lp (p : ℕ) [Fact p.Prime] (ψ : AddChar (ZMod p) ℂ) (g : Polynomial (ZMod p)) :
    Polynomial ℂ :=
  ∑ m ∈ Finset.range (g.natDegree), Polynomial.C (Cm p ψ g m) * Polynomial.X ^ m

/-- The Euler-product identity at level `N`. -/
lemma eulerProduct_identity (p : ℕ) [Fact p.Prime] (ψ : AddChar (ZMod p) ℂ)
    (g : Polynomial (ZMod p)) (N : ℕ) (hN : 1 ≤ N) :
    (∑ m ∈ Finset.range N, Cm p ψ g m * Sm p ψ g (N - m))
      = (N : ℂ) * Cm p ψ g N := by
  simpa only [Cm, Sm, Commons.FieldTheory.Polynomial.repPoly] using
    (Commons.Algebra.Polynomial.eulerProduct_logDeriv_monic (F := ZMod p) (Ψ := psiAS p ψ g)
      (psiAS_one p ψ g) (fun A B hA hB => psiAS_mul p ψ g A B hA hB) N hN)

lemma repPoly_zero {R : Type*} [CommSemiring R] (c : Fin 0 → R) :
    Commons.FieldTheory.Polynomial.repPoly 0 c = 1 := by
  simp [Commons.FieldTheory.Polynomial.repPoly]

lemma Cm_zero (p : ℕ) [Fact p.Prime] (ψ : AddChar (ZMod p) ℂ) (g : Polynomial (ZMod p)) :
    Cm p ψ g 0 = 1 := by
  have hconst : (∑ c : Fin 0 → ZMod p,
        psiAS p ψ g (Commons.FieldTheory.Polynomial.repPoly 0 c))
      = ∑ _c : Fin 0 → ZMod p, (1 : ℂ) :=
    Finset.sum_congr rfl fun c _ => by
      rw [repPoly_zero c, psiAS_one p ψ g]
  rw [Cm, hconst, Finset.sum_const]
  simp

lemma Lp_coeff_lt (p : ℕ) [Fact p.Prime] (ψ : AddChar (ZMod p) ℂ) (g : Polynomial (ZMod p))
    {m : ℕ} (hm : m < g.natDegree) : (Lp p ψ g).coeff m = Cm p ψ g m := by
  rw [Lp, Polynomial.finsetSum_coeff]
  have hsingle : (∑ b ∈ Finset.range (g.natDegree),
      (Polynomial.C (Cm p ψ g b) * Polynomial.X ^ b).coeff m)
      = (Polynomial.C (Cm p ψ g m) * Polynomial.X ^ m).coeff m := by
    refine Finset.sum_eq_single m ?_ ?_
    · intro b _ hb
      rw [Polynomial.coeff_C_mul_X_pow, if_neg (fun h => hb h.symm)]
    · intro hm'; exact absurd (Finset.mem_range.mpr hm) hm'
  rw [hsingle, Polynomial.coeff_C_mul_X_pow, if_pos rfl]

lemma Lp_natDegree_le (p : ℕ) [Fact p.Prime] (ψ : AddChar (ZMod p) ℂ) (g : Polynomial (ZMod p)) :
    (Lp p ψ g).natDegree ≤ g.natDegree - 1 := by
  rw [Lp]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  exact (Polynomial.natDegree_C_mul_X_pow_le (Cm p ψ g m) m).trans
    (Nat.le_pred_of_lt (Finset.mem_range.mp hm))

lemma Lp_coeff_ge (p : ℕ) [Fact p.Prime] (ψ : AddChar (ZMod p) ℂ) (g : Polynomial (ZMod p))
    (hg : 1 ≤ g.natDegree) {m : ℕ} (hm : g.natDegree ≤ m) : (Lp p ψ g).coeff m = 0 := by
  refine Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (Lp_natDegree_le p ψ g) ?_)
  omega

/-- The coefficients of `L` are the `Ψ`-sums `C_m`. -/
lemma Lp_coeff (p : ℕ) [Fact p.Prime] (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    (g : Polynomial (ZMod p)) (hg : 1 ≤ g.natDegree) (hgp : g.natDegree < p) (m : ℕ) :
    (Lp p ψ g).coeff m = Cm p ψ g m := by
  by_cases hm : m < g.natDegree
  · exact Lp_coeff_lt p ψ g hm
  · rw [Lp_coeff_ge p ψ g hg (by omega),
      Cm_eq_zero p ψ hψ g hg hgp (by omega)]

/-- The recurrence `∑_{m < N} L_m S_{N-m} = N L_N`. -/
lemma recurrence (p : ℕ) [Fact p.Prime] (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    (g : Polynomial (ZMod p)) (hg : 1 ≤ g.natDegree) (hgp : g.natDegree < p)
    (N : ℕ) (hN : 1 ≤ N) :
    (∑ m ∈ Finset.range N, (Lp p ψ g).coeff m * Sm p ψ g (N - m))
      = (N : ℂ) * (Lp p ψ g).coeff N := by
  have heuler := eulerProduct_identity p ψ g N hN
  have h1 : (∑ m ∈ Finset.range N, (Lp p ψ g).coeff m * Sm p ψ g (N - m))
      = ∑ m ∈ Finset.range N, Cm p ψ g m * Sm p ψ g (N - m) :=
    Finset.sum_congr rfl fun m _ => by rw [Lp_coeff p ψ hψ g hg hgp m]
  rw [h1, heuler, Lp_coeff p ψ hψ g hg hgp N]

/-- **The `L`-function power sums.**  The sums `S_N` are power sums of at most
`deg g - 1` complex numbers. -/
theorem Sm_eq_powerSums (p : ℕ) [Fact p.Prime] (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    (g : Polynomial (ZMod p)) (hg : 1 ≤ g.natDegree) (hgp : g.natDegree < p) :
    ∃ (t : ℕ) (_ : t ≤ g.natDegree - 1) (γ : Fin t → ℂ),
      ∀ N : ℕ, 1 ≤ N → Sm p ψ g N = - ∑ j : Fin t, γ j ^ N := by
  have hL0 : (Lp p ψ g).coeff 0 = 1 := by
    rw [Lp_coeff p ψ hψ g hg hgp 0]
    exact Cm_zero p ψ g
  have hS0 : Sm p ψ g 0 = 0 := by
    simp [Sm, Nat.divisors_zero]
  obtain ⟨t, ht, γ, hγ⟩ :=
    Commons.Algebra.Polynomial.exists_powerSums_of_recurrence (Lp p ψ g) hL0 (Sm p ψ g) hS0
      (recurrence p ψ hψ g hg hgp)
  exact ⟨t, ht.trans (Lp_natDegree_le p ψ g), γ, hγ⟩



/-! ### (b) sums of a periodic sequence -/

lemma shift_mul {M : Type*} (f : ℕ → M) {m : ℕ} (hf : ∀ i, f (i + m) = f i) :
    ∀ k i, f (m * k + i) = f i := by
  intro k
  induction k with
  | zero => intro i; simp
  | succ k ihk =>
    intro i
    have h1 : m * (k + 1) + i = (m * k + i) + m := by ring
    rw [h1, hf, ihk]

lemma sum_range_mul_of_period {M : Type*} [AddCommMonoid M] (f : ℕ → M) {m : ℕ} (_hm : 0 < m)
    (hf : ∀ i, f (i + m) = f i) (k : ℕ) :
    ∑ i ∈ Finset.range (m * k), f i = k • (∑ i ∈ Finset.range m, f i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact shift_mul f hf k i

/-! ### (a) the root sum of the minimal polynomial is the Frobenius orbit sum -/

theorem eval_map_algHom {F E K : Type*} [Field F] [Field E] [Field K] [Algebra F E]
    [Algebra F K] (φ : E →ₐ[F] K) (g : Polynomial F) (y : E) :
    φ ((g.map (algebraMap F E)).eval y) = (g.map (algebraMap F K)).eval (φ y) := by
  have hcomp : (φ : E →+* K).comp (algebraMap F E) = algebraMap F K :=
    AlgHom.comp_algebraMap φ
  rw [Polynomial.eval_map, Polynomial.eval_map]
  have h := Polynomial.hom_eval₂ g (algebraMap F E) (φ : E →+* K) y
  rw [hcomp] at h
  exact h

theorem asTrace_minpoly_eq_sum_orbit (p : ℕ) [Fact p.Prime]
    {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
    [Module.Finite (ZMod p) E] [Module.Free (ZMod p) E]
    (g : Polynomial (ZMod p)) (a : E) :
    algebraMap (ZMod p) E (asTrace p g (minpoly (ZMod p) a))
      = ∑ i ∈ Finset.range (minpoly (ZMod p) a).natDegree,
          (g.map (algebraMap (ZMod p) E)).eval (a ^ (p ^ i)) := by
  classical
  set K := AlgebraicClosure (ZMod p) with hK
  set P : Polynomial (ZMod p) := minpoly (ZMod p) a with hP
  set m : ℕ := P.natDegree with hm
  have hPmon : P.Monic := minpoly.monic (IsIntegral.of_finite (ZMod p) a)
  let φ : E →ₐ[ZMod p] K := IsAlgClosed.lift
  have hfacE : P.map (algebraMap (ZMod p) E)
      = ∏ i : Fin m, (Polynomial.X - Polynomial.C (a ^ (p ^ (i : ℕ)))) := by
    have h := Commons.FieldTheory.Finite.minpoly_map_eq_prod_pow_card (F := ZMod p) a
    rw [ZMod.card p] at h
    rw [← hP, ← hm] at h
    exact h
  have hfacK : P.map (algebraMap (ZMod p) K)
      = ∏ i : Fin m, (Polynomial.X - Polynomial.C ((φ a) ^ (p ^ (i : ℕ)))) := by
    have h1 := Polynomial.map_map (p := P) (f := algebraMap (ZMod p) E) (g := (φ : E →+* K))
    have hcomp : (φ : E →+* K).comp (algebraMap (ZMod p) E) = algebraMap (ZMod p) K :=
      AlgHom.comp_algebraMap φ
    rw [hcomp] at h1
    rw [← h1, hfacE, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_pow]
    rfl
  have hroots : (P.map (algebraMap (ZMod p) K)).roots
      = Finset.univ.val.map (fun i : Fin m => (φ a) ^ (p ^ (i : ℕ))) := by
    rw [hfacK, Finset.prod_eq_multiset_prod]
    have h := Polynomial.roots_multiset_prod_X_sub_C
      ((Finset.univ.val.map (fun i : Fin m => (φ a) ^ (p ^ (i : ℕ)))) : Multiset K)
    simp only [Multiset.map_map, Function.comp] at h
    rw [h]
  have hL : rootSumK p g P
      = ∑ i ∈ Finset.range m, (g.map (algebraMap (ZMod p) K)).eval ((φ a) ^ (p ^ i)) := by
    rw [rootSumK, Polynomial.aroots_def, hroots]
    rw [show (Multiset.map (fun r : K => (g.map (algebraMap (ZMod p) K)).eval r)
          (Multiset.map (fun i : Fin m => (φ a) ^ (p ^ (i : ℕ))) Finset.univ.val)).sum
        = ∑ i : Fin m, (g.map (algebraMap (ZMod p) K)).eval ((φ a) ^ (p ^ (i : ℕ))) from by
      rw [Multiset.map_map]
      rw [Finset.sum_eq_multiset_sum]
      rfl]
    rw [Fin.sum_univ_eq_sum_range
      (fun i => (g.map (algebraMap (ZMod p) K)).eval ((φ a) ^ (p ^ i))) m]
  have hR : φ (∑ i ∈ Finset.range m,
        (g.map (algebraMap (ZMod p) E)).eval (a ^ (p ^ i)))
      = ∑ i ∈ Finset.range m, (g.map (algebraMap (ZMod p) K)).eval ((φ a) ^ (p ^ i)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [eval_map_algHom φ g (a ^ (p ^ i)), map_pow]
  refine φ.injective ?_
  rw [show φ.toRingHom (algebraMap (ZMod p) E (asTrace p g P)) = algebraMap (ZMod p) K (asTrace p g P)
      from AlgHom.commutes φ (asTrace p g P), asTrace_spec p g P hPmon,
    show φ.toRingHom (∑ i ∈ Finset.range m,
        (g.map (algebraMap (ZMod p) E)).eval (a ^ (p ^ i)))
      = ∑ i ∈ Finset.range m, (g.map (algebraMap (ZMod p) K)).eval ((φ a) ^ (p ^ i)) from hR]
  exact hL

/-! ### (c) the trace is the orbit sum -/

theorem trace_eval_eq_nsmul_asTrace (p : ℕ) [Fact p.Prime]
    {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
    [Module.Finite (ZMod p) E] [Module.Free (ZMod p) E]
    (n : ℕ) (hn : Module.finrank (ZMod p) E = n) (g : Polynomial (ZMod p)) (a : E) :
    Algebra.trace (ZMod p) E ((g.map (algebraMap (ZMod p) E)).eval a)
      = (n / (minpoly (ZMod p) a).natDegree) • asTrace p g (minpoly (ZMod p) a) := by
  classical
  set m : ℕ := (minpoly (ZMod p) a).natDegree with hm
  have ha : IsIntegral (ZMod p) a := IsIntegral.of_finite (ZMod p) a
  have hnpos : 0 < n := by rw [← hn]; exact Module.finrank_pos
  have hmdvd : m ∣ n := by
    have h1 : m = Module.finrank (ZMod p) ↥(IntermediateField.adjoin (ZMod p) {a}) := by
      rw [hm]; exact (IntermediateField.adjoin.finrank ha).symm
    have h2 : Module.finrank (ZMod p) ↥(IntermediateField.adjoin (ZMod p) {a})
        ∣ Module.finrank (ZMod p) ↥(⊤ : IntermediateField (ZMod p) E) :=
      IntermediateField.finrank_dvd_of_le_right (le_top :
        (IntermediateField.adjoin (ZMod p) {a}) ≤ (⊤ : IntermediateField (ZMod p) E))
    rw [IntermediateField.finrank_top'] at h2
    rw [h1, ← hn]
    exact h2
  have hfix : a ^ (p ^ m) = a := by
    rw [hm]
    simpa using Commons.FieldTheory.Finite.minpoly_pow_card_pow_eq_self (F := ZMod p) a
  have hstep : ∀ j : ℕ, (a ^ (p ^ j)) ^ (p ^ m) = a ^ (p ^ j) := by
    intro j
    rw [← pow_mul, mul_comm, pow_mul, hfix]
  have hper : ∀ i, (g.map (algebraMap (ZMod p) E)).eval (a ^ (p ^ (i + m)))
      = (g.map (algebraMap (ZMod p) E)).eval (a ^ (p ^ i)) := by
    intro i
    congr 1
    rw [pow_add, pow_mul]
    exact hstep i
  have hsum : (∑ i ∈ Finset.range n, (g.map (algebraMap (ZMod p) E)).eval (a ^ (p ^ i)))
      = (n / m) • (∑ i ∈ Finset.range m,
          (g.map (algebraMap (ZMod p) E)).eval (a ^ (p ^ i))) := by
    have h1 : n = m * (n / m) := (Nat.mul_div_cancel' hmdvd).symm
    conv_lhs => rw [h1]
    exact sum_range_mul_of_period (fun i => (g.map (algebraMap (ZMod p) E)).eval (a ^ (p ^ i)))
      (Nat.pos_of_dvd_of_pos hmdvd hnpos) hper (n / m)
  refine (algebraMap (ZMod p) E).injective ?_
  rw [map_nsmul, asTrace_minpoly_eq_sum_orbit p g a,
    FiniteField.algebraMap_trace_eq_sum_pow (ZMod p) E
      ((g.map (algebraMap (ZMod p) E)).eval a), hn]
  simp only [Nat.card_eq_fintype_card, ZMod.card]
  have hterm : ∀ i : ℕ, ((g.map (algebraMap (ZMod p) E)).eval a) ^ (p ^ i)
      = (g.map (algebraMap (ZMod p) E)).eval (a ^ (p ^ i)) := by
    intro i
    have h := Commons.NumberTheory.CharacterSum.eval_pow_card_pow (F := ZMod p) (E := E) g a i
    simpa only [ZMod.card] using h
  simp only [hterm]
  exact hsum

/-! ### (d) the pointwise identification -/

theorem psi_trace_eval_eq (p : ℕ) [Fact p.Prime]
    {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
    [Module.Finite (ZMod p) E] [Module.Free (ZMod p) E]
    (ψ : AddChar (ZMod p) ℂ) (g : Polynomial (ZMod p)) (n : ℕ)
    (hn : Module.finrank (ZMod p) E = n) (a : E) :
    ψ (Algebra.trace (ZMod p) E ((g.map (algebraMap (ZMod p) E)).eval a))
      = (psiAS p ψ g (minpoly (ZMod p) a)) ^ (n / (minpoly (ZMod p) a).natDegree) := by
  rw [trace_eval_eq_nsmul_asTrace p n hn g a, AddChar.map_nsmul_eq_pow, psiAS,
    if_pos (minpoly.monic (IsIntegral.of_finite (ZMod p) a))]

/-! ### (e) the character sum over `E` is the `L`-function coefficient `S_n` -/

open Classical in
theorem char_sum_eq_Sm (p : ℕ) [Fact p.Prime] (ψ : AddChar (ZMod p) ℂ) (g : Polynomial (ZMod p))
    (n : ℕ) (hn : 0 < n)
    (E : Type*) [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
    [Module.Finite (ZMod p) E] [Module.Free (ZMod p) E]
    (hfnr : Module.finrank (ZMod p) E = n) :
    (∑ a : E, ψ (Algebra.trace (ZMod p) E ((g.map (algebraMap (ZMod p) E)).eval a)))
      = Sm p ψ g n := by
  classical
  haveI : Fintype (ConjRootClass (ZMod p) E) :=
    Fintype.ofSurjective (ConjRootClass.mk (ZMod p))
      (fun c => Quotient.inductionOn c (fun x => ⟨x, rfl⟩))
  haveI : Normal (ZMod p) E := inferInstance
  have hnne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  have deg_dvd : ∀ c : ConjRootClass (ZMod p) E, c.minpoly.natDegree ∣ n := by
    intro c
    induction c using ConjRootClass.ind with
    | h x =>
      rw [ConjRootClass.minpoly_mk]
      have h1 : (minpoly (ZMod p) x).natDegree
          = Module.finrank (ZMod p) ↥(IntermediateField.adjoin (ZMod p) {x}) :=
        (IntermediateField.adjoin.finrank (IsIntegral.of_finite (ZMod p) x)).symm
      have h2 : Module.finrank (ZMod p) ↥(IntermediateField.adjoin (ZMod p) {x})
          ∣ Module.finrank (ZMod p) ↥(⊤ : IntermediateField (ZMod p) E) :=
        IntermediateField.finrank_dvd_of_le_right
          (le_top : (IntermediateField.adjoin (ZMod p) {x}) ≤ (⊤ : IntermediateField (ZMod p) E))
      rw [IntermediateField.finrank_top'] at h2
      rw [h1, ← hfnr]
      exact h2
  have hgroup : (∑ a : E, ψ (Algebra.trace (ZMod p) E ((g.map (algebraMap (ZMod p) E)).eval a)))
      = ∑ c : ConjRootClass (ZMod p) E, (c.minpoly.natDegree : ℂ)
          * (psiAS p ψ g c.minpoly) ^ (n / c.minpoly.natDegree) := by
    rw [Commons.FieldTheory.Minpoly.sum_eq_sum_conjRootClass_commmonoid (K := ZMod p) (L := E)
      (f := fun a : E => ψ (Algebra.trace (ZMod p) E ((g.map (algebraMap (ZMod p) E)).eval a)))]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hconst : (∑ a ∈ c.carrier.toFinset,
          ψ (Algebra.trace (ZMod p) E ((g.map (algebraMap (ZMod p) E)).eval a)))
        = ∑ _a ∈ c.carrier.toFinset,
            (psiAS p ψ g c.minpoly) ^ (n / c.minpoly.natDegree) := by
      refine Finset.sum_congr rfl fun a ha => ?_
      have hca : minpoly (ZMod p) a = c.minpoly := by
        rw [← ConjRootClass.minpoly_mk,
          ConjRootClass.mem_carrier.mp ((Set.mem_toFinset).mp ha)]
      rw [psi_trace_eval_eq p ψ g n hfnr a, hca]
    rw [hconst, Finset.sum_const, Commons.FieldTheory.Minpoly.conjRootClass_card_carrier c,
      nsmul_eq_mul]
  have hstep5 : (∑ c : ConjRootClass (ZMod p) E, (c.minpoly.natDegree : ℂ)
        * (psiAS p ψ g c.minpoly) ^ (n / c.minpoly.natDegree))
      = ∑ m ∈ n.divisors, (m : ℂ)
          * ∑ c : {c : ConjRootClass (ZMod p) E // c.minpoly.natDegree = m},
              (psiAS p ψ g c.1.minpoly) ^ (n / c.1.minpoly.natDegree) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := n.divisors)
      (g := fun c : ConjRootClass (ZMod p) E => c.minpoly.natDegree)
      (f := fun c => (c.minpoly.natDegree : ℂ)
        * (psiAS p ψ g c.minpoly) ^ (n / c.minpoly.natDegree))
      (h := fun c _ => by rw [Nat.mem_divisors]; exact ⟨deg_dvd c, hnne⟩)]
    refine Finset.sum_congr rfl fun m _ => ?_
    have h1 : (∑ c ∈ Finset.univ.filter (fun c : ConjRootClass (ZMod p) E =>
            c.minpoly.natDegree = m),
          (c.minpoly.natDegree : ℂ) * (psiAS p ψ g c.minpoly) ^ (n / c.minpoly.natDegree))
        = ∑ c ∈ Finset.univ.filter (fun c : ConjRootClass (ZMod p) E =>
            c.minpoly.natDegree = m),
          (m : ℂ) * (psiAS p ψ g c.minpoly) ^ (n / c.minpoly.natDegree) := by
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [Finset.mem_filter] at hc
      rw [hc.2]
    rw [h1, Finset.mul_sum]
    exact Finset.sum_subtype
      (Finset.univ.filter (fun c : ConjRootClass (ZMod p) E => c.minpoly.natDegree = m))
      (fun c => by simp [Finset.mem_filter])
      (fun c => (m : ℂ) * (psiAS p ψ g c.minpoly) ^ (n / c.minpoly.natDegree))
  rw [hgroup, hstep5]
  refine Finset.sum_congr rfl fun m hm => ?_
  congr 1
  rw [← Commons.NumberTheory.CharacterSum.sum_fin_irreducible_eq_sum_conjRootClass_monoid n hfnr m hm
    (fun P : Polynomial (ZMod p) => (psiAS p ψ g P) ^ (n / P.natDegree))]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hdeg : (Polynomial.X ^ m + ∑ i : Fin m,
      Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)).natDegree = m :=
    Commons.FieldTheory.Polynomial.repPoly_natDegree m c
  by_cases hc : Irreducible (Polynomial.X ^ m + ∑ i : Fin m,
      Polynomial.C (c i) * Polynomial.X ^ (i : ℕ))
  · rw [if_pos hc, if_pos hc, hdeg]
  · rw [if_neg hc, if_neg hc]


/-! ## The Artin–Schreier L-function power sums -/

/-- **Structural input.**  The Artin--Schreier sums over extensions `E/F_p` are power sums
of at most `deg g - 1` complex numbers.  This is the classical Artin--Schreier `L`-function
identity: the point counts over the Artin--Schreier curves make the `L`-polynomial a polynomial
of degree `≤ deg g - 1`, whose reciprocal roots are the `γ_j`. -/
theorem addchar_char_sum_power_sums (p : ℕ) [Fact p.Prime] (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    (g : Polynomial (ZMod p)) (hg : 1 ≤ g.natDegree) (hgp : g.natDegree < p) :
    ∃ (t : ℕ) (_ : t ≤ g.natDegree - 1) (γ : Fin t → ℂ),
      ∀ (n : ℕ), 1 ≤ n → ∀ (E : Type*) [Field E] [Fintype E] [DecidableEq E]
        [Algebra (ZMod p) E] [Module.Finite (ZMod p) E] [Module.Free (ZMod p) E],
        Module.finrank (ZMod p) E = n →
        ((∑ a : E, ψ (Algebra.trace (ZMod p) E ((g.map (algebraMap (ZMod p) E)).eval a))) : ℂ)
          = - ∑ j : Fin t, γ j ^ n := by
  obtain ⟨t, ht, γ, hγ⟩ := Sm_eq_powerSums p ψ hψ g hg hgp
  refine ⟨t, ht, γ, fun n hn E _ _ _ _ _ _ hfnr => ?_⟩
  rw [show ((∑ a : E, ψ (Algebra.trace (ZMod p) E
        ((g.map (algebraMap (ZMod p) E)).eval a))) : ℂ) = Sm p ψ g n from
      char_sum_eq_Sm p ψ g n (by omega) E hfnr,
    hγ n hn]

/-! ## The extension bound from the point-count hypothesis -/

/-- **Extension bound.**  The point-count hypothesis bounds the Artin–Schreier sums over
every even-degree extension. -/
theorem addchar_char_sum_extension_bound (p : ℕ) [Fact p.Prime] (d : ℕ) (hd : 1 ≤ d)
    (hdp : d < p)
    (hpc : ∀ (d' : ℕ), 1 ≤ d' → ∃ C : ℝ, 0 < C ∧
      ∀ {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
        [Module.Finite (ZMod p) E] [Module.Free (ZMod p) E],
        d' < p → 2 ∣ Module.finrank (ZMod p) E →
        ∀ (g : Polynomial (ZMod p)), 1 ≤ g.natDegree → g.natDegree ≤ d' →
        (∀ q : ℕ, q.Prime → q ∣ p → ∀ (a : ZMod p) (h : Polynomial (ZMod p)),
          g ≠ Polynomial.C a * h ^ q) →
        |(({z : E × E | z.2 ^ p - z.2 = (g.map (algebraMap (ZMod p) E)).eval z.1} : Set (E × E)).ncard : ℝ)
            - (Fintype.card E : ℝ)|
          ≤ C * Real.sqrt ((Fintype.card E : ℕ) : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ψ : AddChar (ZMod p) ℂ), ψ ≠ 1 → ∀ (g : Polynomial (ZMod p)),
      1 ≤ g.natDegree → g.natDegree ≤ d →
      ∀ (n : ℕ), 0 < n → ¬ p ∣ n → ∀ (E : Type*) [Field E] [Fintype E] [DecidableEq E]
        [Algebra (ZMod p) E] [Module.Finite (ZMod p) E] [Module.Free (ZMod p) E],
        Module.finrank (ZMod p) E = n →
        ‖∑ a : E, ψ (Algebra.trace (ZMod p) E ((g.map (algebraMap (ZMod p) E)).eval a))‖
          ≤ C * Real.sqrt (Fintype.card E : ℝ) :=
  Commons.NumberTheory.FunctionField.artin_schreier_extension_bound p d hd hdp hpc

/-! ## The main theorem -/

theorem additive_weil_from_point_count (p : ℕ) [Fact p.Prime]
    (hpc : ∀ (d : ℕ), 1 ≤ d → ∃ C : ℝ, 0 < C ∧
      ∀ {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
        [Module.Finite (ZMod p) E] [Module.Free (ZMod p) E],
        d < p → 2 ∣ Module.finrank (ZMod p) E →
        ∀ (g : Polynomial (ZMod p)), 1 ≤ g.natDegree → g.natDegree ≤ d →
        (∀ q : ℕ, q.Prime → q ∣ p → ∀ (a : ZMod p) (h : Polynomial (ZMod p)),
          g ≠ Polynomial.C a * h ^ q) →
        |(({z : E × E | z.2 ^ p - z.2 = (g.map (algebraMap (ZMod p) E)).eval z.1} : Set (E × E)).ncard : ℝ)
            - (Fintype.card E : ℝ)|
          ≤ C * Real.sqrt ((Fintype.card E : ℕ) : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ψ : AddChar (ZMod p) ℂ), ψ ≠ 1 → ∀ (g : Polynomial (ZMod p)),
      1 ≤ g.natDegree → g.natDegree < p →
      ‖∑ x : ZMod p, ψ (g.eval x)‖ ≤ C * (g.natDegree : ℝ) * Real.sqrt (p : ℝ) := by
  have h2le : 2 ≤ p := (Fact.out : p.Prime).two_le
  rcases eq_or_lt_of_le h2le with hp2 | hp3
  · -- p = 2 : trivial bound (at most two terms of modulus one)
    subst hp2
    refine ⟨2, by norm_num, ?_⟩
    intro ψ hψ g hg hlt
    have hle : ‖∑ x : ZMod 2, ψ (g.eval x)‖ ≤ 2 := by
      calc ‖∑ x : ZMod 2, ψ (g.eval x)‖ ≤ ∑ x : ZMod 2, ‖ψ (g.eval x)‖ := norm_sum_le _ _
        _ = ∑ _x : ZMod 2, (1:ℝ) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            simp [AddChar.norm_apply]
        _ = 2 := by simp
    refine hle.trans ?_
    have hd : (1:ℝ) ≤ (g.natDegree : ℝ) := by exact_mod_cast hg
    have hs : (1:ℝ) ≤ Real.sqrt 2 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    have hprod : (1:ℝ) ≤ (g.natDegree : ℝ) * Real.sqrt 2 :=
      one_le_mul_of_one_le_of_one_le hd hs
    calc (2:ℝ) = 2 * 1 := by ring
      _ ≤ 2 * ((g.natDegree : ℝ) * Real.sqrt 2) :=
          mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = 2 * (g.natDegree : ℝ) * Real.sqrt 2 := by ring
  · -- p ≥ 3
    obtain ⟨C₀, hC₀pos, hC₀⟩ := addchar_char_sum_extension_bound p (p-1) (by omega)
      (by omega) hpc
    refine ⟨max C₀ 1, lt_max_of_lt_left hC₀pos, ?_⟩
    intro ψ hψ g hg hlt
    obtain ⟨t, ht, γ, hγ⟩ := addchar_char_sum_power_sums p ψ hψ g hg hlt
    have hbdd' : ∀ k : ℕ, 0 < k → ¬ p ∣ k → ‖∑ j : Fin t, (γ j ^ 2) ^ k‖ ≤ C₀ * (p:ℝ) ^ k := by
      intro k hk hkop
      have h2k : 0 < 2*k := by omega
      letI hF : Fintype (GaloisField p (2*k)) := Fintype.ofFinite _
      letI hD : DecidableEq (GaloisField p (2*k)) := Classical.decEq _
      have hcard : (Fintype.card (GaloisField p (2*k)) : ℝ) = ((p:ℝ)^k)^2 := by
        rw [← Nat.card_eq_fintype_card, GaloisField.card p (2*k) (by omega), Nat.cast_pow]
        ring
      have hfin : Module.finrank (ZMod p) (GaloisField p (2*k)) = 2*k :=
        GaloisField.finrank p (by omega : 2*k ≠ 0)
      have hpk : ¬ p ∣ 2*k := by
        intro hdvd
        rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).mp hdvd with h | h
        · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
        · exact hkop h
      have hineq := hC₀ ψ hψ g hg (by omega) (2*k) h2k hpk (GaloisField p (2*k)) hfin
      have hsum : (∑ a : GaloisField p (2*k),
            ψ (Algebra.trace (ZMod p) (GaloisField p (2*k))
              ((g.map (algebraMap (ZMod p) (GaloisField p (2*k)))).eval a)))
          = - ∑ j : Fin t, γ j ^ (2*k) := by
        have := hγ (2*k) (by omega) (GaloisField p (2*k)) hfin
        simpa using this
      have h3 : (∑ j : Fin t, (γ j ^ 2) ^ k) = ∑ j : Fin t, γ j ^ (2*k) := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [← pow_mul, mul_comm]
      rw [h3, show (∑ j : Fin t, γ j ^ (2*k)) = -(- ∑ j : Fin t, γ j ^ (2*k)) by ring,
        ← hsum, norm_neg]
      refine hineq.trans_eq ?_
      rw [hcard, Real.sqrt_sq (by positivity)]
    have hroot := addchar_pow_sum_transference (p := p)
      (by have := hlt; omega : t < p) γ hC₀pos hbdd'
    have hnorm : ∀ j : Fin t, ‖γ j‖ ≤ Real.sqrt p := by
      intro j
      have hj := hroot j
      rw [norm_pow] at hj
      calc ‖γ j‖ = Real.sqrt (‖γ j‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt p := Real.sqrt_le_sqrt hj
    have hT1 : (∑ x : ZMod p, ψ (g.eval x)) = - ∑ j : Fin t, γ j := by
      have h1 := hγ 1 le_rfl (ZMod p) (Module.finrank_self (ZMod p))
      simpa only [pow_one, Algebra.trace_self, LinearMap.id_coe, id_eq,
        Algebra.algebraMap_self (R := ZMod p), Polynomial.map_id] using h1
    calc ‖∑ x : ZMod p, ψ (g.eval x)‖
        = ‖∑ j : Fin t, γ j‖ := by rw [hT1, norm_neg]
      _ ≤ ∑ j : Fin t, ‖γ j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin t, Real.sqrt p := Finset.sum_le_sum fun j _ => hnorm j
      _ = (t:ℝ) * Real.sqrt p := by simp
      _ ≤ (g.natDegree : ℝ) * Real.sqrt p := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          have ht' : t ≤ g.natDegree := le_trans ht (Nat.sub_le _ _)
          exact_mod_cast ht'
      _ ≤ max C₀ 1 * (g.natDegree : ℝ) * Real.sqrt p := by
          calc (g.natDegree : ℝ) * Real.sqrt p
              = 1 * ((g.natDegree : ℝ) * Real.sqrt p) := by ring
            _ ≤ max C₀ 1 * ((g.natDegree : ℝ) * Real.sqrt p) :=
                mul_le_mul_of_nonneg_right (le_max_right C₀ 1) (by positivity)
            _ = max C₀ 1 * (g.natDegree : ℝ) * Real.sqrt p := by ring

end Commons.NumberTheory.ExponentialSums
