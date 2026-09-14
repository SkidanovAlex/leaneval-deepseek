import Mathlib
import Submission.Vdw.PolyIndex

open Polynomial
open scoped BigOperators

set_option autoImplicit false

/-!
# Factorization algebra of the index of a polynomial over a field (discindex, step 1a)

Bhargava's *index* of a monic polynomial `f` over a field
(`Submission.Vdw.polyIndex f = natDegree f − natDegree (rad f)`, with `rad f`
the product of the distinct monic irreducible factors) equals
`Σ_i (e_i − 1)·deg P_i` over the distinct factors `P_i` of the monic
factorisation `f = ∏ P_i^{e_i}` (see `polyIndex_eq_factors_sum`).

This module records the factorization algebra that the *discindex bridge*
(Lemma 24 of Bhargava 2025: `index_{F_p}(f̄) ≥ v_p(D_f)` for `p > n`) needs
in its reduction step — "the index of a product is at least the sum of the
indices, with equality for coprime factors":

* `polyIndex_mul_ge_add`: monic `a b`: `polyIndex (a·b) ≥ polyIndex a + polyIndex b`
  (the mod-`p` index is superadditive over a factorization of `f̄`);
* `polyIndex_mul_eq_add`: monic `a b`, `IsCoprime a b`:
  `polyIndex (a·b) = polyIndex a + polyIndex b` (exact additivity over the
  coprime factors);
* `polyIndex_pow_irreducible`: irreducible monic `q`, `1 ≤ k`:
  `polyIndex (q^k) = (k−1)·natDegree q`;
* `polyIndex_eq_factors_sum`: the canonical `Σ (count−1)·deg` expression;
* `polyIndex_irreducible`, `polyIndex_eq_zero_iff_eq_radical`:
  irreducibles have index `0`; index `0` ⟺ `f` equals its radical (no
  repeated factor).

Engine: the unconditional multiset identity
`normalizedFactors (a·b) = normalizedFactors a + normalizedFactors b`
(`UniqueFactorizationMonoid.normalizedFactors_mul`): the distinct factors of
`a·b` are the union of those of `a` and `b`, so the radical of the product
divides the product of the radicals.
-/

namespace Submission.Vdw

noncomputable section

open UniqueFactorizationMonoid
open Commons.FieldTheory.Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-- The distinct irreducible factors of `a·b` are the union of those of `a`
and of `b` (the multiset `normalizedFactors` is additive over products). -/
theorem normalizedFactors_mul_toFinset (a b : F[X]) (ha : a ≠ 0) (hb : b ≠ 0) :
    (normalizedFactors (a * b)).toFinset =
      (normalizedFactors a).toFinset ∪ (normalizedFactors b).toFinset := by
  classical
  rw [normalizedFactors_mul ha hb]
  exact Multiset.toFinset_add (s := normalizedFactors a) (t := normalizedFactors b)

/-- The radical of a product divides the product of the radicals: every
distinct irreducible factor of `a·b` is a distinct irreducible factor of
`a` or of `b`. -/
theorem radical_mul_dvd_mul (a b : F[X]) (ha : a ≠ 0) (hb : b ≠ 0) :
    UniqueFactorizationMonoid.radical (a * b) ∣
      UniqueFactorizationMonoid.radical a * UniqueFactorizationMonoid.radical b := by
  classical
  let A : Finset (F[X]) := (normalizedFactors a).toFinset
  let B : Finset (F[X]) := (normalizedFactors b).toFinset
  have hrad : ∀ p : F[X],
      (∏ x ∈ (normalizedFactors p).toFinset, x) = UniqueFactorizationMonoid.radical p := by
    intro p
    rw [radical_eq_toFinset_prod (F := F) p]
    rfl
  rw [← hrad (a * b), ← hrad a, ← hrad b]
  rw [normalizedFactors_mul_toFinset a b ha hb]
  have hpart : (∏ x ∈ A, x) * (∏ x ∈ B, x) =
      (∏ x ∈ A ∪ B, x) * (∏ x ∈ B ∩ A, x) := by
    have hdisjAB : Disjoint A (B \ A) := by
      rw [Finset.disjoint_left]
      intro x hxA hxBA
      exact (Finset.mem_sdiff.mp hxBA).2 hxA
    have hAB : A ∪ (B \ A) = A ∪ B := by
      ext x
      by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;> simp [hxA, hxB]
    have hsplitB : (∏ x ∈ B, x) = (∏ x ∈ B \ A, x) * (∏ x ∈ B ∩ A, x) := by
      have hdisj : Disjoint (B \ A) (B ∩ A) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        exact (Finset.mem_sdiff.mp hx1).2 (Finset.mem_inter.mp hx2).2
      have hcover : B \ A ∪ (B ∩ A) = B := by
        ext x
        by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;> simp [hxA, hxB]
      rw [← Finset.prod_union hdisj, hcover]
    calc
      (∏ x ∈ A, x) * (∏ x ∈ B, x)
          = (∏ x ∈ A, x) * ((∏ x ∈ B \ A, x) * (∏ x ∈ B ∩ A, x)) := by
              rw [hsplitB]
      _ = (∏ x ∈ A ∪ (B \ A), x) * (∏ x ∈ B ∩ A, x) := by
              rw [Finset.prod_union hdisjAB]
              ac_rfl
      _ = (∏ x ∈ A ∪ B, x) * (∏ x ∈ B ∩ A, x) := by rw [hAB]
  rw [hpart]
  exact dvd_mul_right (∏ x ∈ A ∪ B, x) (∏ x ∈ B ∩ A, x)

/-- The radical of any polynomial is monic. -/
theorem radical_monic_of (p : F[X]) : (UniqueFactorizationMonoid.radical p).Monic := by
  rw [← monicRadical_eq_radical p]
  exact monicRadical_monic p

/-- Degree version: `deg rad (a·b) ≤ deg rad a + deg rad b`. -/
theorem natDegree_radical_mul_le (a b : F[X]) (ha : a ≠ 0) (hb : b ≠ 0) :
    (UniqueFactorizationMonoid.radical (a * b)).natDegree ≤
      (UniqueFactorizationMonoid.radical a).natDegree +
        (UniqueFactorizationMonoid.radical b).natDegree := by
  have hdvd := radical_mul_dvd_mul a b ha hb
  have hne : UniqueFactorizationMonoid.radical a * UniqueFactorizationMonoid.radical b ≠ 0 := by
    exact mul_ne_zero (radical_monic_of a).ne_zero (radical_monic_of b).ne_zero
  have hdeg := Polynomial.natDegree_le_of_dvd hdvd hne
  calc
    (UniqueFactorizationMonoid.radical (a * b)).natDegree
        ≤ (UniqueFactorizationMonoid.radical a * UniqueFactorizationMonoid.radical b).natDegree :=
          hdeg
    _ = (UniqueFactorizationMonoid.radical a).natDegree +
          (UniqueFactorizationMonoid.radical b).natDegree :=
          Polynomial.natDegree_mul (radical_monic_of a).ne_zero (radical_monic_of b).ne_zero

/-- The index of a product is at least the sum of the indices (monic factors)
— the superadditivity used in the reduction step of the discindex bridge. -/
theorem polyIndex_mul_ge_add (a b : F[X]) (haM : a.Monic) (hbM : b.Monic) :
    polyIndex a + polyIndex b ≤ polyIndex (a * b) := by
  classical
  dsimp [polyIndex]
  have hdegmul : (a * b).natDegree = a.natDegree + b.natDegree :=
    Polynomial.natDegree_mul haM.ne_zero hbM.ne_zero
  rw [hdegmul]
  have hle := natDegree_radical_mul_le a b haM.ne_zero hbM.ne_zero
  have h1 : (UniqueFactorizationMonoid.radical a).natDegree ≤ a.natDegree :=
    Commons.FieldTheory.Polynomial.natDegree_radical_le a haM.ne_zero
  have h2 : (UniqueFactorizationMonoid.radical b).natDegree ≤ b.natDegree :=
    Commons.FieldTheory.Polynomial.natDegree_radical_le b hbM.ne_zero
  omega

/-- If the distinct irreducible factor sets of two nonzero polynomials are
disjoint, the radical of their product is the product of the radicals. -/
theorem radical_mul_eq_mul_of_disjoint (a b : F[X]) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdisj : Disjoint (normalizedFactors a).toFinset (normalizedFactors b).toFinset) :
    UniqueFactorizationMonoid.radical (a * b) =
      UniqueFactorizationMonoid.radical a * UniqueFactorizationMonoid.radical b := by
  classical
  rw [radical_eq_toFinset_prod (a * b), radical_eq_toFinset_prod a,
    radical_eq_toFinset_prod b]
  rw [normalizedFactors_mul_toFinset a b ha hb]
  exact Finset.prod_union hdisj

/-- **Index additivity over coprime factors** (monic): if `IsCoprime a b`,
then `polyIndex (a·b) = polyIndex a + polyIndex b`. -/
theorem polyIndex_mul_eq_add (a b : F[X]) (haM : a.Monic) (hbM : b.Monic)
    (hcop : IsCoprime a b) :
    polyIndex (a * b) = polyIndex a + polyIndex b := by
  classical
  -- disjointness of the distinct-factor sets follows from coprimality
  have hdisj : Disjoint (normalizedFactors a).toFinset (normalizedFactors b).toFinset := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    have hmemA : x ∈ normalizedFactors a := Multiset.mem_toFinset.mp hxA
    have hmemB : x ∈ normalizedFactors b := Multiset.mem_toFinset.mp hxB
    have hirr : Irreducible x := irreducible_of_mem_normalizedFactors haM.ne_zero hmemA
    have hxda : x ∣ a := ((Polynomial.mem_normalizedFactors_iff haM.ne_zero).mp hmemA).2.2
    have hxdb : x ∣ b := ((Polynomial.mem_normalizedFactors_iff hbM.ne_zero).mp hmemB).2.2
    obtain ⟨u, v, hbe⟩ := hcop
    obtain ⟨a₁, ha1⟩ := hxda
    obtain ⟨b₁, hb1⟩ := hxdb
    have hx1 : x ∣ (1 : F[X]) := by
      refine ⟨u * a₁ + v * b₁, ?_⟩
      calc
        1 = u * a + v * b := hbe.symm
        _ = u * (x * a₁) + v * (x * b₁) := by rw [ha1, hb1]
        _ = x * (u * a₁ + v * b₁) := by ring
    exact hirr.not_isUnit (isUnit_of_dvd_one hx1)
  have hrad : UniqueFactorizationMonoid.radical (a * b) =
      UniqueFactorizationMonoid.radical a * UniqueFactorizationMonoid.radical b :=
    radical_mul_eq_mul_of_disjoint a b haM.ne_zero hbM.ne_zero hdisj
  dsimp [polyIndex]
  have hdegmul : (a * b).natDegree = a.natDegree + b.natDegree :=
    Polynomial.natDegree_mul haM.ne_zero hbM.ne_zero
  rw [hdegmul, hrad]
  have hdegR : (UniqueFactorizationMonoid.radical a * UniqueFactorizationMonoid.radical b).natDegree =
      (UniqueFactorizationMonoid.radical a).natDegree +
        (UniqueFactorizationMonoid.radical b).natDegree :=
    Polynomial.natDegree_mul (radical_monic_of a).ne_zero (radical_monic_of b).ne_zero
  rw [hdegR]
  have h1 : (UniqueFactorizationMonoid.radical a).natDegree ≤ a.natDegree :=
    Commons.FieldTheory.Polynomial.natDegree_radical_le a haM.ne_zero
  have h2 : (UniqueFactorizationMonoid.radical b).natDegree ≤ b.natDegree :=
    Commons.FieldTheory.Polynomial.natDegree_radical_le b hbM.ne_zero
  omega

/-- The distinct normalized factors of a monic irreducible polynomial are the
singleton `{q}`. -/
theorem normalizedFactors_toFinset_irreducible {q : F[X]} (hq : q.Monic) (hirr : Irreducible q) :
    (normalizedFactors q).toFinset = {q} := by
  classical
  ext g
  constructor
  · intro hg
    rw [Finset.mem_singleton]
    have hmem : g ∈ normalizedFactors q := Multiset.mem_toFinset.mp hg
    have hgM : g.Monic := monic_of_mem_normalizedFactors hq.ne_zero hmem
    have hgI : Irreducible g := irreducible_of_mem_normalizedFactors hq.ne_zero hmem
    have hgdvd : g ∣ q := ((Polynomial.mem_normalizedFactors_iff hq.ne_zero).mp hmem).2.2
    rcases hgdvd with ⟨s, hs⟩
    have hgdiv : g ∣ q := ⟨s, hs⟩
    have hsne : s ≠ 0 := by
      intro h0
      have : q = 0 := by rw [hs, h0, mul_zero]
      exact hq.ne_zero this
    have hfac := hirr.isUnit_or_isUnit (a := g) (b := s) hs
    rcases hfac with hgu | hsu
    · exact False.elim (hgI.not_isUnit hgu)
    · have hsnd : s.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hsu
      have hdeg : q.natDegree = g.natDegree := by
        calc
          q.natDegree = (g * s).natDegree := by rw [hs]
          _ = g.natDegree + s.natDegree := Polynomial.natDegree_mul hgM.ne_zero hsne
          _ = g.natDegree := by rw [hsnd]; simp
      exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (p := g) (q := q) hgM hq hgdiv
        (le_of_eq hdeg)).symm
  · intro hg
    rw [Finset.mem_singleton] at hg
    subst g
    exact Multiset.mem_toFinset.mpr
      ((Polynomial.mem_normalizedFactors_iff hq.ne_zero).2 ⟨hirr, hq, dvd_rfl⟩)

/-- An irreducible monic polynomial has index `0`. -/
theorem polyIndex_irreducible {q : F[X]} (hq : q.Monic) (hirr : Irreducible q) :
    polyIndex q = 0 := by
  classical
  have hsing : (normalizedFactors q).toFinset = {q} :=
    normalizedFactors_toFinset_irreducible hq hirr
  have hrad : UniqueFactorizationMonoid.radical q = q := by
    rw [radical_eq_toFinset_prod, hsing]
    simp
  dsimp [polyIndex]
  rw [hrad]
  simp

/-- **Index of a prime power**: for monic irreducible `q` and `1 ≤ k`,
`polyIndex (q^k) = (k−1)·natDegree q`. -/
theorem polyIndex_pow_irreducible {q : F[X]} (hq : q.Monic) (hirr : Irreducible q)
    {k : ℕ} (hk1 : 1 ≤ k) :
    polyIndex (q ^ k) = (k - 1) * q.natDegree := by
  classical
  have hq0 : q ≠ 0 := hq.ne_zero
  have hqk0 : q ^ k ≠ 0 := pow_ne_zero k hq0
  have hsing : (normalizedFactors (q ^ k)).toFinset = {q} := by
    ext g
    constructor
    · intro hg
      rw [Finset.mem_singleton]
      have hmem : g ∈ normalizedFactors (q ^ k) := Multiset.mem_toFinset.mp hg
      have hgM : g.Monic := monic_of_mem_normalizedFactors hqk0 hmem
      have hgI : Irreducible g := irreducible_of_mem_normalizedFactors hqk0 hmem
      have hgdvd : g ∣ q ^ k := ((Polynomial.mem_normalizedFactors_iff hqk0).mp hmem).2.2
      have hgp : Prime g := (irreducible_iff_prime.mp hgI)
      have hgq : g ∣ q := Prime.dvd_of_dvd_pow hgp hgdvd
      -- g ∈ normalizedFactors q, hence g = q
      have hmemq : g ∈ normalizedFactors q :=
        (Polynomial.mem_normalizedFactors_iff hq0).2 ⟨hgI, hgM, hgq⟩
      have hsingq : (normalizedFactors q).toFinset = {q} :=
        normalizedFactors_toFinset_irreducible hq hirr
      have : g ∈ ({q} : Finset (F[X])) := by
        rw [← hsingq]
        exact Multiset.mem_toFinset.mpr hmemq
      simpa using this
    · intro hg
      rw [Finset.mem_singleton] at hg
      subst g
      exact Multiset.mem_toFinset.mpr
        ((Polynomial.mem_normalizedFactors_iff hqk0).2
          ⟨hirr, hq, ⟨q ^ (k - 1), by
            have hk : k = (k - 1) + 1 := by omega
            calc
              q ^ k = q ^ ((k - 1) + 1) := congrArg (fun m : ℕ => q ^ m) hk
              _ = q ^ (k - 1) * q := by rw [pow_succ]
              _ = q * q ^ (k - 1) := by rw [mul_comm]⟩⟩)
  have hrad : UniqueFactorizationMonoid.radical (q ^ k) = q := by
    rw [radical_eq_toFinset_prod, hsing]
    simp
  dsimp [polyIndex]
  rw [hrad]
  rw [Polynomial.natDegree_pow]
  have hk2 : k = (k - 1) + 1 := by omega
  have hcalc : k * q.natDegree - q.natDegree = (k - 1) * q.natDegree := by
    calc
      k * q.natDegree - q.natDegree
          = ((k - 1) + 1) * q.natDegree - q.natDegree := by nth_rw 1 [hk2]
      _ = (k - 1) * q.natDegree + q.natDegree - q.natDegree := by
              rw [add_mul, one_mul]
      _ = (k - 1) * q.natDegree := by rw [Nat.add_sub_cancel]
  exact hcalc

/-- The canonical expression of the index in terms of the factorization:
`polyIndex p = Σ (count h − 1) · natDegree h` over the distinct factors. -/
theorem polyIndex_eq_factors_sum (p : F[X]) (hp : p.Monic) :
    polyIndex p =
      ∑ h ∈ (normalizedFactors p).toFinset,
        ((normalizedFactors p).count h - 1) * h.natDegree := by
  classical
  dsimp [polyIndex]
  have hdeg_p : p.natDegree = ((normalizedFactors p).map Polynomial.natDegree).sum := by
    calc
      p.natDegree = (normalizedFactors p).prod.natDegree := by
        rw [prod_normalizedFactors_of_monic p hp]
      _ = ((normalizedFactors p).map Polynomial.natDegree).sum := by
        exact natDegree_multiset_prod_monic (normalizedFactors p)
          (fun g hg => monic_of_mem_normalizedFactors hp.ne_zero hg)
  have hdeg_rad : (UniqueFactorizationMonoid.radical p).natDegree =
      ∑ h ∈ (normalizedFactors p).toFinset, h.natDegree := by
    rw [radical_eq_toFinset_prod]
    exact Polynomial.natDegree_prod ((normalizedFactors p).toFinset) (fun h => h)
      (fun g hg => (monic_of_mem_normalizedFactors hp.ne_zero (Multiset.mem_toFinset.mp hg)).ne_zero)
  have hweighted : ((normalizedFactors p).map Polynomial.natDegree).sum =
      ∑ h ∈ (normalizedFactors p).toFinset,
        (normalizedFactors p).count h * h.natDegree := by
    induction (normalizedFactors p) using Multiset.induction_on with
    | empty => simp
    | cons x m ih =>
        have hcount (h : F[X]) : (x ::ₘ m).count h = m.count h + if h = x then 1 else 0 := by
          by_cases hx : h = x
          · subst h
            simp
          · simp [hx]
        have hrhs : (∑ h ∈ (x ::ₘ m).toFinset, (x ::ₘ m).count h * h.natDegree) =
            x.natDegree + ∑ h ∈ m.toFinset, m.count h * h.natDegree := by
          rw [Multiset.toFinset_cons]
          simp_rw [hcount]
          simp_rw [add_mul]
          rw [Finset.sum_add_distrib]
          have hfirst : (∑ h ∈ insert x m.toFinset, m.count h * h.natDegree) =
              ∑ h ∈ m.toFinset, m.count h * h.natDegree := by
            by_cases hxT : x ∈ m.toFinset
            · rw [Finset.insert_eq_of_mem hxT]
            · rw [Finset.sum_insert hxT]
              have hcx : m.count x = 0 :=
                Multiset.count_eq_zero.mpr (by simpa using hxT)
              simp [hcx]
          have hsecond : (∑ h ∈ insert x m.toFinset, (if h = x then (1 : ℕ) else 0) *
              h.natDegree) = x.natDegree := by
            have hstep : (∑ h ∈ insert x m.toFinset, (if h = x then (1 : ℕ) else 0) *
                  h.natDegree) =
                (∑ h ∈ insert x m.toFinset, if h = x then h.natDegree else 0) := by
              apply Finset.sum_congr rfl
              intro h hh
              by_cases hx2 : h = x <;> simp [hx2]
            rw [hstep, Finset.sum_ite_eq']
            simp
          rw [hfirst, hsecond]
          abel
        calc
          ((x ::ₘ m).map Polynomial.natDegree).sum
              = x.natDegree + (m.map Polynomial.natDegree).sum := by
                  rw [Multiset.map_cons]
                  simp
          _ = x.natDegree + ∑ h ∈ m.toFinset, m.count h * h.natDegree := by rw [ih]
          _ = ∑ h ∈ (x ::ₘ m).toFinset, (x ::ₘ m).count h * h.natDegree := hrhs.symm
  have hsplit : (∑ h ∈ (normalizedFactors p).toFinset,
        ((normalizedFactors p).count h - 1) * h.natDegree) +
          ∑ h ∈ (normalizedFactors p).toFinset, h.natDegree =
      ∑ h ∈ (normalizedFactors p).toFinset,
        (normalizedFactors p).count h * h.natDegree := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h hh
    have hcpos : 0 < (normalizedFactors p).count h :=
      Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hh)
    have hc1 : 1 ≤ (normalizedFactors p).count h := hcpos
    have hc : (normalizedFactors p).count h - 1 + 1 = (normalizedFactors p).count h :=
      Nat.sub_add_cancel hc1
    calc
      ((normalizedFactors p).count h - 1) * h.natDegree + h.natDegree
          = (((normalizedFactors p).count h - 1) + 1) * h.natDegree := by
              rw [add_mul, one_mul]
          _ = (normalizedFactors p).count h * h.natDegree := by rw [hc]
  rw [hdeg_p, hweighted, hdeg_rad]
  rw [← hsplit]
  exact Nat.add_sub_cancel _ _

/-- `polyIndex f = 0` iff `f` equals its radical (i.e. `f` has no repeated
irreducible factor). -/
theorem polyIndex_eq_zero_iff_eq_radical (f : F[X]) (hf : f.Monic) :
    polyIndex f = 0 ↔ UniqueFactorizationMonoid.radical f = f := by
  classical
  constructor
  · intro h
    have hdeg : f.natDegree ≤ (UniqueFactorizationMonoid.radical f).natDegree := by
      dsimp [polyIndex] at h
      omega
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (p := UniqueFactorizationMonoid.radical f)
      (q := f) (radical_monic_of f) hf (UniqueFactorizationMonoid.radical_dvd_self) hdeg).symm
  · intro h
    dsimp [polyIndex]
    rw [h]
    exact Nat.sub_self f.natDegree

/-- The index of `1` is `0`. -/
theorem polyIndex_one : polyIndex (1 : F[X]) = 0 := by
  dsimp [polyIndex]
  have hrad : UniqueFactorizationMonoid.radical (1 : F[X]) = 1 := by
    rw [radical_eq_toFinset_prod]
    simp
  rw [hrad]
  simp

/-- **Index is additive over a pairwise-coprime family of monic factors**:
`polyIndex (∏_{i ∈ s} q i) = ∑_{i ∈ s} polyIndex (q i)`.  This is the
residue-side identity behind the discindex reduction: the mod-`p` index of a
product of pairwise-coprime lifted factors adds up. -/
theorem polyIndex_prod_eq_sum_of_coprime {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (q : ι → F[X]) (hqmon : ∀ i ∈ s, (q i).Monic)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (q i) (q j)) :
    polyIndex (∏ i ∈ s, q i) = ∑ i ∈ s, polyIndex (q i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [polyIndex_one]
  | insert i₀ s' hi₀ ih =>
      -- step: peel the first factor off the product
      have hmoni : (q i₀).Monic := hqmon i₀ (by simp)
      have hmonprod : (∏ j ∈ s', q j).Monic := by
        refine monic_prod_of_monic s' q ?_
        intro j hj
        exact hqmon j (by simp [hj])
      have hcopiprod : IsCoprime (q i₀) (∏ j ∈ s', q j) := by
        apply IsCoprime.prod_right
        intro j hj
        apply hcop i₀ (by simp) j (by simp [hj])
        intro hij
        exact hi₀ (hij.symm ▸ hj)
      calc
        polyIndex (∏ i ∈ insert i₀ s', q i)
            = polyIndex (q i₀ * ∏ j ∈ s', q j) := by
                rw [Finset.prod_insert hi₀]
        _ = polyIndex (q i₀) + polyIndex (∏ j ∈ s', q j) :=
                polyIndex_mul_eq_add (q i₀) (∏ j ∈ s', q j) hmoni hmonprod hcopiprod
        _ = polyIndex (q i₀) + ∑ j ∈ s', polyIndex (q j) := by
                rw [ih (fun i hi => hqmon i (by simp [hi]))
                  (fun i hi j hj hij => hcop i (by simp [hi]) j (by simp [hj]) hij)]
        _ = ∑ i ∈ insert i₀ s', polyIndex (q i) := by
                rw [Finset.sum_insert hi₀]

/-- The index of a power of a monic irreducible in a family
(`q i = h ^ (e i)` contributes `(e i − 1)·natDegree h`).  Convenience form of
`polyIndex_pow_irreducible` with the hypotheses grouped as in the splitting
type `h^e`. -/
theorem polyIndex_pow_irreducible_of_monic {q : F[X]} (hq : q.Monic) (hirr : Irreducible q)
    (e : ℕ) (he : 1 ≤ e) : polyIndex (q ^ e) = (e - 1) * q.natDegree :=
  polyIndex_pow_irreducible hq hirr he

/-- **Splitting-type index**: if `f` factors over a field as a product of
powers `∏_{i ∈ s} (h i) ^ (e i)` with the `h i` monic irreducible and
pairwise coprime (equivalently: distinct irreducibles), then
`polyIndex f = ∑_{i ∈ s} (e i − 1) · natDegree (h i)` — the
`Σ (e_i − 1) deg P_i` formula of Bhargava's index in full Finset form. -/
theorem polyIndex_splitting_type {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (h : ι → F[X]) (e : ι → ℕ) (hmon : ∀ i ∈ s, (h i).Monic)
    (hirr : ∀ i ∈ s, Irreducible (h i))
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (h i) (h j))
    (he : ∀ i ∈ s, 1 ≤ e i) :
    polyIndex (∏ i ∈ s, (h i) ^ (e i)) =
      ∑ i ∈ s, (e i - 1) * (h i).natDegree := by
  classical
  have hqmon : ∀ i ∈ s, ((h i) ^ (e i)).Monic := by
    intro i hi
    exact (hmon i hi).pow (e i)
  have hqcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime ((h i) ^ (e i)) ((h j) ^ (e j)) := by
    intro i hi j hj hij
    exact ((hcop i hi j hj hij).pow_right).pow_left
  have hmain := polyIndex_prod_eq_sum_of_coprime s (fun i => (h i) ^ (e i)) hqmon hqcop
  rw [hmain]
  apply Finset.sum_congr rfl
  intro i hi
  exact polyIndex_pow_irreducible_of_monic (hmon i hi) (hirr i hi) (e i) (he i hi)


end
end Submission.Vdw
