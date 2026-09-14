import Mathlib
import Submission.Vdw.IndexFactor

open Polynomial
open UniqueFactorizationMonoid
open Submission.Vdw
open Commons.FieldTheory.Polynomial
open scoped BigOperators

set_option autoImplicit false

/-!
# Index base-change invariance over a perfect base field (discindex, step 1c(i))

Bhargava's *index* of a monic polynomial over a field (`Submission.Vdw.polyIndex`:
`deg f − deg(rad f)`) is invariant under scalar extension: for monic `f` over a
**perfect** base field `F` and any field homomorphism `φ : F →+* E` into a field
`E`,

    polyIndex (map φ f) = polyIndex f                       (`polyIndex_map_eq`)

This is the pure-algebra step of Lemma 24 of Bhargava 2025
(`index_{F_p}(f̄) ≥ v_p(D_f)` for primes `p > n`): in its proof one works over
the residue field `F_q = F_{p^f}` of the unramified subfield `ℚ_q ⊆ L` and uses
that "the index of `g` over `F_p` is equal to the index of `g` over `F_q` for
any extension `F_q` of `F_p`".  Perfectness of the base field is exactly the
right hypothesis (finite fields `F_p`, `F_q` are perfect — `PerfectField.ofFinite`):
every irreducible `g` over a perfect field is separable, `g` stays separable —
hence squarefree — after base change, and distinct (monic) irreducibles remain
coprime, so the multiset of irreducible factors of `map φ f` over `E` is the
"refinement" of the factorisation of `f` over `F`, with each multiplicity
preserved.  The index (degree of the non-squarefree part, counted with
multiplicity) is unchanged.

Supporting lemmas (all in `Submission.Vdw`), each reusable:

* `multiset_prod_eq_prod_pow_count`: a multiset product is the Finset product
  of its distinct elements raised to their counts.
* `polyIndex_pow_monic`: monic `a`, `1 ≤ k`: `polyIndex (a^k) =
  (k−1)·deg a + polyIndex a` (a prime power of exponent `k` contributes
  exactly `k−1` extra degrees beyond the index of the base).
* `polyIndex_prod_pow_eq_sum_of_coprime`: over a **pairwise-coprime** monic
  family the index of the product of powers is the sum of the per-factor
  contributions — index additivity in its powered form (extends
  `IndexFactor.polyIndex_prod_eq_sum_of_coprime`).
* `separable_polyIndex_zero`: separable monic polynomials have index `0`
  (no repeated irreducible factor).
* `monic_irreducible_coprime_of_ne` / `normalizedFactors_coprime`: distinct
  monic irreducibles (in particular, distinct members of the normalized
  factorisation of one monic polynomial) are coprime.
* `polyIndex_map_eq` (**main**): index is invariant under base change for
  monic polynomials over a perfect field.

Proof of `polyIndex_map_eq` in one line of mathematics: write
`f = ∏_{g ∈ factors f} g^{e_g}` over `F` with the `g` distinct monic
irreducibles; over `E`, `map φ f = ∏ (map φ g)^{e_g}` with the `map φ g`
monic, pairwise coprime and squarefree (separable), so

    polyIndex_E (map φ f) = ∑_g (e_g − 1)·deg(map φ g)
                          = ∑_g (e_g − 1)·deg g
                          = polyIndex_F f.
-/

namespace Submission.Vdw

noncomputable section

variable {F : Type*} [Field F] [DecidableEq F]

/-- A multiset product is the Finset product of its distinct elements raised
to their multiplicities. -/
theorem multiset_prod_eq_prod_pow_count {R : Type*} [CommMonoid R] [DecidableEq R]
    (m : Multiset R) : m.prod = ∏ x ∈ m.toFinset, x ^ m.count x := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
      have hcount (x : R) : (a ::ₘ m).count x = m.count x + if x = a then 1 else 0 := by
        by_cases hx : x = a
        · subst x
          rw [Multiset.count_cons_self]
          simp
        · rw [Multiset.count_cons_of_ne hx]
          simp [hx]
      have hnotmem : a ∉ m.toFinset → a ∉ m := by
        intro h ham
        exact h (Multiset.mem_toFinset.mpr ham)
      by_cases hamem : a ∈ m.toFinset
      · have hT : (∏ x ∈ (a ::ₘ m).toFinset, x ^ (a ::ₘ m).count x) = a * m.prod := by
          have hf (b : R) (hb : b ≠ a) : b ^ (if b = a then 1 else 0) = 1 := by
            simp [hb]
          have hind : (∏ x ∈ m.toFinset, x ^ (if x = a then 1 else 0)) = a := by
            calc
              (∏ x ∈ m.toFinset, x ^ (if x = a then 1 else 0))
                  = a ^ (if a = a then 1 else 0) *
                      ∏ x ∈ m.toFinset \ {a}, x ^ (if x = a then 1 else 0) := by
                      exact Finset.prod_eq_mul_prod_sdiff_singleton a
                        (fun x => x ^ (if x = a then 1 else 0))
                        (by intro hna; exact False.elim (hna hamem))
              _ = a * 1 := by
                      congr 1
                      · simp
                      · apply Finset.prod_eq_one
                        intro x hx
                        have hxa : x ≠ a := by
                          intro hxa
                          exact (Finset.mem_sdiff.mp hx).2 (by simp [hxa])
                        exact hf x hxa
              _ = a := by simp
          calc
            ∏ x ∈ (a ::ₘ m).toFinset, x ^ (a ::ₘ m).count x
                = ∏ x ∈ m.toFinset, x ^ (a ::ₘ m).count x := by
                    rw [Multiset.toFinset_cons, Finset.insert_eq_of_mem hamem]
            _ = ∏ x ∈ m.toFinset, x ^ (m.count x + (if x = a then 1 else 0)) := by
                    apply Finset.prod_congr rfl
                    intro x hx
                    rw [hcount x]
            _ = ∏ x ∈ m.toFinset, (x ^ m.count x) * (x ^ (if x = a then 1 else 0)) := by
                    apply Finset.prod_congr rfl
                    intro x hx
                    rw [pow_add]
            _ = (∏ x ∈ m.toFinset, x ^ m.count x) *
                (∏ x ∈ m.toFinset, x ^ (if x = a then 1 else 0)) := by
                    rw [Finset.prod_mul_distrib]
            _ = m.prod * a := by rw [← ih, hind]
            _ = a * m.prod := by rw [mul_comm]
        rw [Multiset.prod_cons]
        exact hT.symm
      · have hT : (∏ x ∈ (a ::ₘ m).toFinset, x ^ (a ::ₘ m).count x) = a * m.prod := by
          have hprod : (∏ x ∈ m.toFinset, x ^ (a ::ₘ m).count x) = m.prod := by
            trans ∏ x ∈ m.toFinset, x ^ m.count x
            · apply Finset.prod_congr rfl
              intro x hx
              have hxa : x ≠ a := by
                intro hxa
                exact hamem (by simpa [hxa] using hx)
              have hxcount : (a ::ₘ m).count x = m.count x := by
                rw [hcount x]
                simp [hxa]
              rw [hxcount]
            · exact ih.symm
          calc
            ∏ x ∈ (a ::ₘ m).toFinset, x ^ (a ::ₘ m).count x
                = ∏ x ∈ insert a m.toFinset, x ^ (a ::ₘ m).count x := by
                    rw [Multiset.toFinset_cons]
            _ = a ^ (a ::ₘ m).count a * ∏ x ∈ m.toFinset, x ^ (a ::ₘ m).count x := by
                    rw [Finset.prod_insert hamem]
            _ = a * m.prod := by
                    have hca : (a ::ₘ m).count a = 1 := by
                      rw [Multiset.count_cons_self]
                      have ha0 : m.count a = 0 := Multiset.count_eq_zero.mpr (hnotmem hamem)
                      rw [ha0]
                    simp [hca, hprod]
        rw [Multiset.prod_cons]
        exact hT.symm

/-- The index of a prime power: monic `a`, `1 ≤ k`:
`polyIndex (a^k) = (k−1)·deg a + polyIndex a`.  (The radical of `a^k` is the
radical of `a`, by `UniqueFactorizationMonoid.radical_pow`.) -/
theorem polyIndex_pow_monic (a : F[X]) (haM : a.Monic) (k : ℕ) (hk : 1 ≤ k) :
    polyIndex (a ^ k) = (k - 1) * a.natDegree + polyIndex a := by
  classical
  have hk' : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
  have hle : (UniqueFactorizationMonoid.radical a).natDegree ≤ a.natDegree :=
    Commons.FieldTheory.Polynomial.natDegree_radical_le a haM.ne_zero
  dsimp [polyIndex]
  rw [Polynomial.natDegree_pow]
  rw [UniqueFactorizationMonoid.radical_pow a (ne_of_gt hk)]
  calc
    k * a.natDegree - (UniqueFactorizationMonoid.radical a).natDegree
        = ((k - 1) + 1) * a.natDegree - (UniqueFactorizationMonoid.radical a).natDegree := by
            nth_rw 1 [hk']
    _ = ((k - 1) * a.natDegree + a.natDegree) -
          (UniqueFactorizationMonoid.radical a).natDegree := by
            rw [add_mul, one_mul]
    _ = (k - 1) * a.natDegree +
          (a.natDegree - (UniqueFactorizationMonoid.radical a).natDegree) := by
            rw [Nat.add_sub_assoc hle]

/-- Index additivity in powered form: for a monic **pairwise-coprime** family
`(a i)`, `polyIndex (∏ (a i)^(e i)) = ∑ ((e i −1)·deg(a i) + polyIndex (a i))`
(`1 ≤ e i`). -/
theorem polyIndex_prod_pow_eq_sum_of_coprime {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a : ι → F[X]) (e : ι → ℕ)
    (hmon : ∀ i ∈ s, (a i).Monic)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (a i) (a j))
    (he : ∀ i ∈ s, 1 ≤ e i) :
    polyIndex (∏ i ∈ s, (a i) ^ (e i)) =
      ∑ i ∈ s, ((e i - 1) * (a i).natDegree + polyIndex (a i)) := by
  classical
  have hqmon : ∀ i ∈ s, ((a i) ^ (e i)).Monic := by
    intro i hi
    exact (hmon i hi).pow (e i)
  have hqcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime ((a i) ^ (e i)) ((a j) ^ (e j)) := by
    intro i hi j hj hij
    exact ((hcop i hi j hj hij).pow_right).pow_left
  have hmain := polyIndex_prod_eq_sum_of_coprime s (fun i => (a i) ^ (e i)) hqmon hqcop
  calc
    polyIndex (∏ i ∈ s, (a i) ^ (e i)) = ∑ i ∈ s, polyIndex ((a i) ^ (e i)) := hmain
    _ = ∑ i ∈ s, ((e i - 1) * (a i).natDegree + polyIndex (a i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact polyIndex_pow_monic (a i) (hmon i hi) (e i) (he i hi)

/-- Separable monic polynomials have index `0` (no repeated irreducible
factor). -/
theorem separable_polyIndex_zero (f : F[X]) (hf : f.Monic) (hsep : f.Separable) :
    polyIndex f = 0 := by
  classical
  have hf0 : f ≠ 0 := hf.ne_zero
  have hsq : Squarefree f := Polynomial.Separable.squarefree hsep
  have hnod : (normalizedFactors f).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hf0).mp hsq
  rw [polyIndex_eq_factors_sum f hf]
  apply Finset.sum_eq_zero
  intro g hg
  have hmemg : g ∈ normalizedFactors f := Multiset.mem_toFinset.mp hg
  have hcle : (normalizedFactors f).count g ≤ 1 := (Multiset.nodup_iff_count_le_one.mp hnod) g
  have hcgt : 0 < (normalizedFactors f).count g := (Multiset.count_pos).mpr hmemg
  have hc1 : (normalizedFactors f).count g = 1 := by omega
  rw [hc1]
  simp

/-- Distinct **monic** irreducibles over a field are coprime (non-associate
irreducibles have gcd a unit; monic makes 'associated' collapse to 'equal'). -/
theorem monic_irreducible_coprime_of_ne {g h : F[X]} (hgI : Irreducible g)
    (hhI : Irreducible h) (hgM : g.Monic) (hhM : h.Monic) (hgh : g ≠ h) :
    IsCoprime g h := by
  classical
  let d : F[X] := EuclideanDomain.gcd g h
  have hdvdA : d ∣ g := EuclideanDomain.gcd_dvd_left g h
  have hdvdB : d ∣ h := EuclideanDomain.gcd_dvd_right g h
  have hdu : IsUnit d := by
    by_contra hdnu
    have hcas : Associated g d := by
      have := (Irreducible.dvd_iff hgI).mp hdvdA
      exact Or.elim this (fun hu => False.elim (hdnu hu)) id
    have hgdh : g ∣ h := dvd_trans (Associated.dvd hcas) hdvdB
    have := (Irreducible.dvd_iff hhI).mp hgdh
    have hhg : Associated h g := by
      exact Or.elim this (fun hu => False.elim (hgI.not_isUnit hu)) id
    have : h = g := Polynomial.eq_of_monic_of_associated hhM hgM hhg
    exact hgh this.symm
  obtain ⟨t, ht⟩ := isUnit_iff_dvd_one.mp hdu
  have hbez : d = g * EuclideanDomain.gcdA g h + h * EuclideanDomain.gcdB g h := by
    simpa [d] using (EuclideanDomain.gcd_eq_gcd_ab (R := F[X]) g h)
  refine ⟨EuclideanDomain.gcdA g h * t, EuclideanDomain.gcdB g h * t, ?_⟩
  calc
    EuclideanDomain.gcdA g h * t * g + EuclideanDomain.gcdB g h * t * h
        = (g * EuclideanDomain.gcdA g h + h * EuclideanDomain.gcdB g h) * t := by ring
    _ = d * t := by rw [← hbez]
    _ = 1 := ht.symm

/-- Distinct members of the normalized (monic) factorisation of a monic
polynomial are coprime. -/
theorem normalizedFactors_coprime (f : F[X]) (hf : f.Monic) {g h : F[X]}
    (hg : g ∈ normalizedFactors f) (hh : h ∈ normalizedFactors f) (hgh : g ≠ h) :
    IsCoprime g h := by
  have hf0 : f ≠ 0 := hf.ne_zero
  exact monic_irreducible_coprime_of_ne
    (irreducible_of_mem_normalizedFactors hf0 hg)
    (irreducible_of_mem_normalizedFactors hf0 hh)
    (monic_of_mem_normalizedFactors hf0 hg)
    (monic_of_mem_normalizedFactors hf0 hh) hgh

/-- **Index is invariant under base change** (main, discindex step 1c(i)):
for monic `f` over a perfect field `F` and a field homomorphism `φ : F →+* E`
into a field `E`, `polyIndex (map φ f) = polyIndex f`.  (Finite fields are
perfect, so this covers the `F_p ↪ F_q` passage of Lemma 24.) -/
theorem polyIndex_map_eq {E : Type*} [Field E] [DecidableEq E] (φ : F →+* E)
    [PerfectField F] {f : F[X]} (hf : f.Monic) :
    polyIndex (Polynomial.map φ f) = polyIndex f := by
  classical
  let ms : Multiset (F[X]) := normalizedFactors f
  let s : Finset (F[X]) := ms.toFinset
  have hf0 : f ≠ 0 := hf.ne_zero
  have hmem : ∀ g ∈ s, g ∈ normalizedFactors f := by
    intro g hg
    exact Multiset.mem_toFinset.mp hg
  have hmon : ∀ g ∈ s, g.Monic := by
    intro g hg
    exact monic_of_mem_normalizedFactors hf0 (hmem g hg)
  have hirr : ∀ g ∈ s, Irreducible g := by
    intro g hg
    exact irreducible_of_mem_normalizedFactors hf0 (hmem g hg)
  have hsep : ∀ g ∈ s, g.Separable := by
    intro g hg
    exact PerfectField.separable_of_irreducible (K := F) (f := g) (hirr g hg)
  have hcpos : ∀ g ∈ s, 1 ≤ ms.count g := by
    intro g hg
    exact Multiset.count_pos.mpr (hmem g hg)
  have hcop : ∀ g ∈ s, ∀ h ∈ s, g ≠ h → IsCoprime g h := by
    intro g hg h hh hgh
    exact normalizedFactors_coprime f hf (hmem g hg) (hmem h hh) hgh
  -- factorization of f over F
  have hfid : f = ∏ g ∈ s, g ^ ms.count g := by
    calc
      f = ms.prod := by
            simpa [ms] using (prod_normalizedFactors_of_monic f hf).symm
      _ = ∏ g ∈ s, g ^ ms.count g := by
            simpa [s] using multiset_prod_eq_prod_pow_count ms
  -- factorization transported to E
  have hmapf : Polynomial.map φ f = ∏ g ∈ s, (Polynomial.map φ g) ^ ms.count g := by
    calc
      Polynomial.map φ f = Polynomial.map φ (∏ g ∈ s, g ^ ms.count g) := by rw [hfid]
      _ = ∏ g ∈ s, Polynomial.map φ (g ^ ms.count g) := by
            simpa using (Polynomial.map_prod φ (fun g : F[X] => g ^ ms.count g) s)
      _ = ∏ g ∈ s, (Polynomial.map φ g) ^ ms.count g := by
            apply Finset.prod_congr rfl
            intro g hg
            rw [Polynomial.map_pow]
  -- over-E hypotheses
  have hmonE : ∀ g ∈ s, ((Polynomial.map φ g) : E[X]).Monic := by
    intro g hg
    exact (hmon g hg).map φ
  have hcopE : ∀ g ∈ s, ∀ h ∈ s, g ≠ h →
      IsCoprime ((Polynomial.map φ g) : E[X]) ((Polynomial.map φ h) : E[X]) := by
    intro g hg h hh hgh
    exact IsCoprime.map (hcop g hg h hh hgh) (Polynomial.mapRingHom φ)
  have hindexE : ∀ g ∈ s, polyIndex ((Polynomial.map φ g) : E[X]) = 0 := by
    intro g hg
    apply separable_polyIndex_zero (F := E)
    · exact (hmon g hg).map φ
    · exact Polynomial.Separable.map (hsep g hg) (f := φ)
  calc
    polyIndex (Polynomial.map φ f)
        = ∑ g ∈ s, ((ms.count g - 1) * ((Polynomial.map φ g) : E[X]).natDegree +
            polyIndex ((Polynomial.map φ g) : E[X])) := by
            rw [hmapf]
            exact polyIndex_prod_pow_eq_sum_of_coprime (F := E) s
              (fun g => (Polynomial.map φ g) : F[X] → E[X]) (fun g => ms.count g)
              hmonE hcopE hcpos
    _ = ∑ g ∈ s, (ms.count g - 1) * g.natDegree := by
            apply Finset.sum_congr rfl
            intro g hg
            have hdeg : ((Polynomial.map φ g) : E[X]).natDegree = g.natDegree :=
              (hmon g hg).natDegree_map φ
            rw [hdeg, hindexE g hg]
            simp
    _ = polyIndex f := by
            rw [polyIndex_eq_factors_sum f hf]


/-- **Index superadditivity over a monic family** (no coprimality needed):
`∑ polyIndex (q i) ≤ polyIndex (∏ (q i))` — the mod-`p` index of a product
is at least the sum of the indices of the factors (Lemma 24 of Bhargava
2025: "if `h = h₁·h₂` then the index of `h` over `F_p` is at least the sum of
the indices of `h₁` and `h₂`"). -/
theorem polyIndex_prod_ge_sum_of_monic {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (q : ι → F[X]) (hmon : ∀ i ∈ s, (q i).Monic) :
    ∑ i ∈ s, polyIndex (q i) ≤ polyIndex (∏ i ∈ s, q i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [polyIndex_one]
  | insert i₀ s' hi₀ ih =>
      have hmoni : (q i₀).Monic := hmon i₀ (by simp)
      have hmonprod : (∏ j ∈ s', q j).Monic := by
        refine monic_prod_of_monic s' q ?_
        intro j hj
        exact hmon j (by simp [hj])
      calc
        ∑ i ∈ insert i₀ s', polyIndex (q i)
            = polyIndex (q i₀) + ∑ j ∈ s', polyIndex (q j) := by
                rw [Finset.sum_insert hi₀]
        _ ≤ polyIndex (q i₀) + polyIndex (∏ j ∈ s', q j) := by
                exact Nat.add_le_add_left (ih (fun j hj => hmon j (by simp [hj]))) _
        _ ≤ polyIndex (q i₀ * ∏ j ∈ s', q j) :=
                polyIndex_mul_ge_add (q i₀) (∏ j ∈ s', q j) hmoni hmonprod
        _ = polyIndex (∏ i ∈ insert i₀ s', q i) := by
                rw [Finset.prod_insert hi₀]

end
end Submission.Vdw
