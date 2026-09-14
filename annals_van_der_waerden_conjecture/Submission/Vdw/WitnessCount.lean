import Mathlib
import Submission.Commons.NumberTheory.Polynomial.ncard_intpoly_mahler_le
import Submission.Commons.Data.Set.ncard_le_sum_fiber

open Polynomial

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The witness count: algebraic integers of degree `m` with bounded height

The imprimitive slice is counted by fixing a *generator* `γ` of the subfield `L`
of degree `m` (`γ` a small integer combination of the block polynomial
coefficients) and then counting the block-polynomial coordinates inside `L`.
The number of possible `γ` is controlled by the elementary fact proved here:

`#\{γ : complex algebraic integer, (minpoly ℤ γ).natDegree = m,
   M(minpoly ℤ γ) ≤ S\} ≤ m·(2^(m+1)S+1)^(m+1)`,

i.e. `≪ S^(m+1)`.  The `S^(m+1)` is the count of integer polynomials of degree
`m` with Mahler measure `≤ S`
(`Commons.NumberTheory.Polynomial.ncard_intpoly_mahler_le`, a coefficient-box
bound: every coefficient of such a polynomial is bounded by `2^m S`), and the
factor `m` bounds the number of roots of a degree-`m` polynomial.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

/-- The `ncard` of a finset regarded as a set is its cardinality. -/
lemma ncard_finset_coe {α : Type*} (t : Finset α) : ((t : Set α)).ncard = t.card := by
  rw [Set.ncard_eq_toFinset_card _ (Finset.finite_toSet t)]
  congr 1
  ext x
  rw [Set.Finite.mem_toFinset, Finset.mem_coe]

/-- A degree-`m` integer polynomial has at most `m` roots in `ℂ` (mapping to `ℂ`
does not increase the degree). -/
lemma roots_card_le_of_natDegree_eq {g : Polynomial ℤ} {m : ℕ} (hg : g.natDegree = m) :
    {z : ℂ | (g.map (Int.castRingHom ℂ)).IsRoot z}.ncard ≤ m := by
  classical
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [Polynomial.natDegree_zero] at hg
    subst hg
    have hmap0 : ((0 : Polynomial ℤ).map (Int.castRingHom ℂ)) = 0 := Polynomial.map_zero _
    rw [hmap0]
    have : ({z : ℂ | (0 : ℂ[X]).IsRoot z} : Set ℂ) = Set.univ := by
      ext z
      simp [Polynomial.IsRoot]
    rw [this, Set.ncard_univ]
    exact le_of_eq (Nat.card_eq_zero_of_infinite)
  have hmap0 : g.map (Int.castRingHom ℂ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (fun a b h => Int.cast_injective h)).mpr hg0
  calc {z : ℂ | (g.map (Int.castRingHom ℂ)).IsRoot z}.ncard
      ≤ (((g.map (Int.castRingHom ℂ)).roots.toFinset : Finset ℂ) : Set ℂ).ncard := by
        refine Set.ncard_le_ncard (fun z hz => ?_) (Finset.finite_toSet _)
        rw [Finset.mem_coe, Multiset.mem_toFinset]
        exact (Polynomial.mem_roots hmap0).mpr hz
    _ = (g.map (Int.castRingHom ℂ)).roots.toFinset.card := ncard_finset_coe _
    _ ≤ (g.map (Int.castRingHom ℂ)).roots.card := Multiset.toFinset_card_le _
    _ ≤ (g.map (Int.castRingHom ℂ)).natDegree := Polynomial.card_roots' _
    _ ≤ g.natDegree := Polynomial.natDegree_map_le
    _ = m := hg

/-- **Fibre-counting.**  For a map `φ : α → β` whose image on `s` is finite and
whose fibres inside `s` are finite of cardinality at most `N`,
`s.ncard ≤ N * (φ '' s).ncard`. -/
lemma ncard_le_mul_ncard_image_of_fiber_le {α β : Type*} (φ : α → β) (s : Set α) (N : ℕ)
    (himg : (φ '' s).Finite)
    (hfib : ∀ b ∈ φ '' s, (s ∩ φ ⁻¹' {b}).Finite ∧ (s ∩ φ ⁻¹' {b}).ncard ≤ N) :
    s.ncard ≤ N * (φ '' s).ncard := by
  classical
  have hsfib : s.Finite := by
    have hcover : s ⊆ ⋃ b ∈ (φ '' s), (s ∩ φ ⁻¹' {b}) := by
      intro a ha
      exact Set.mem_iUnion.mpr ⟨φ a, Set.mem_iUnion.mpr ⟨⟨a, ha, rfl⟩, ⟨ha, rfl⟩⟩⟩
    exact Set.Finite.subset (himg.biUnion fun b hb => (hfib b hb).1) hcover
  set P : Set (β × α) := {p | p.2 ∈ s ∧ φ p.2 = p.1} with hP
  have hPfin : P.Finite := by
    have heq : P = (fun a : α => (φ a, a)) '' s := by
      ext p
      constructor
      · rintro ⟨hp2, hφ⟩
        exact ⟨p.2, hp2, Prod.ext_iff.mpr ⟨hφ, rfl⟩⟩
      · rintro ⟨a, ha, haeq⟩
        have h1 : a = p.2 := by simpa using congrArg Prod.snd haeq
        have h2 : φ a = p.1 := by simpa using congrArg Prod.fst haeq
        exact ⟨h1 ▸ ha, by rw [← h1]; exact h2⟩
    rw [heq]
    exact hsfib.image _
  have hmain := Commons.Data.Set.ncard_le_sum_fiber (P := P) hPfin himg.toFinset (fun _ => N)
    (fun p hp => (Set.Finite.mem_toFinset himg).mpr ⟨p.2, hp.1, hp.2⟩)
    (fun b hb => by
      have hb' : b ∈ φ '' s := (Set.Finite.mem_toFinset himg).mp hb
      have hset : ({a : α | (b, a) ∈ P} : Set α) = s ∩ φ ⁻¹' {b} := by
        ext a
        constructor
        · rintro ⟨ha, hφ⟩
          exact ⟨ha, hφ⟩
        · rintro ⟨ha, hφ⟩
          exact ⟨ha, hφ⟩
      rw [hset]
      exact (hfib b hb').2)
  have hcard : P.ncard = s.ncard := by
    have heq : P = (fun a : α => (φ a, a)) '' s := by
      ext p
      constructor
      · rintro ⟨hp2, hφ⟩
        exact ⟨p.2, hp2, Prod.ext_iff.mpr ⟨hφ, rfl⟩⟩
      · rintro ⟨a, ha, haeq⟩
        have h1 : a = p.2 := by simpa using congrArg Prod.snd haeq
        have h2 : φ a = p.1 := by simpa using congrArg Prod.fst haeq
        exact ⟨h1 ▸ ha, by rw [← h1]; exact h2⟩
    rw [heq, Set.ncard_image_of_injective s (f := fun a : α => (φ a, a))
      (fun a b h => by simpa using congrArg Prod.snd h)]
  rw [hcard] at hmain
  calc s.ncard ≤ ∑ _b ∈ himg.toFinset, N := hmain
    _ = N * (φ '' s).ncard := by
        rw [Finset.sum_const, nsmul_eq_mul, (Set.ncard_eq_toFinset_card _ himg).symm, mul_comm]
        rfl

/-- **The witness count.**  The number of complex algebraic integers of degree `m`
whose minimal polynomial has Mahler measure at most `S` is at most
`m·(2^(m+1)S+1)^(m+1)`. -/
theorem ncard_minpoly_mahler_le (m : ℕ) (hm : 1 ≤ m) (S : ℝ) (hS : 1 ≤ S) :
    (({z : ℂ | (minpoly ℤ z).natDegree = m ∧
        Polynomial.mapMahlerMeasure (minpoly ℤ z) (Int.castRingHom ℂ) ≤ S} : Set ℂ).ncard : ℝ)
      ≤ (m : ℝ) * ((2 : ℝ) ^ (m + 1) * S + 1) ^ (m + 1) := by
  classical
  set Z : Set ℂ := {z : ℂ | (minpoly ℤ z).natDegree = m ∧
      Polynomial.mapMahlerMeasure (minpoly ℤ z) (Int.castRingHom ℂ) ≤ S} with hZ
  set T : Set (Polynomial ℤ) :=
    {g | g.natDegree = m ∧ Polynomial.mapMahlerMeasure g (Int.castRingHom ℂ) ≤ S} with hT
  have hcoeff : ∀ g ∈ T, ∀ i ≤ m, |((g.coeff i : ℤ) : ℝ)| ≤ (2 : ℝ) ^ m * S := by
    intro g hg i hi
    calc |((g.coeff i : ℤ) : ℝ)|
        ≤ (2 : ℝ) ^ g.natDegree * g.mapMahlerMeasure (Int.castRingHom ℂ) :=
          Commons.NumberTheory.Polynomial.coeff_abs_le_two_pow_natDegree_mul_mapMahlerMeasure g i
      _ ≤ (2 : ℝ) ^ m * S := by
          have h2 : (2 : ℝ) ^ g.natDegree ≤ (2 : ℝ) ^ m := by rw [hg.1]
          exact mul_le_mul h2 hg.2 (Polynomial.mapMahlerMeasure_nonneg _ _) (by positivity)
  have hTfin : T.Finite := by
    set N : ℤ := ⌊(2 : ℝ) ^ m * S⌋ with hN
    set box : Set (Fin (m + 1) → ℤ) :=
      ((Fintype.piFinset (fun _ : Fin (m + 1) => Finset.Icc (-N) N) :
        Finset (Fin (m + 1) → ℤ)) : Set (Fin (m + 1) → ℤ)) with hboxdef
    have hbox : box.Finite := Finset.finite_toSet _
    have hmapsto : Set.MapsTo (fun g : Polynomial ℤ => fun i : Fin (m + 1) => g.coeff (i : ℕ))
        T box := by
      intro g hg
      simp only [hboxdef, Finset.mem_coe, Fintype.mem_piFinset]
      intro i
      simp only [Finset.mem_Icc]
      have hi : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp i.isLt
      obtain ⟨h1, h2⟩ := abs_le.mp (hcoeff g hg (i : ℕ) hi)
      refine ⟨?_, Int.le_floor.mpr h2⟩
      have hthis : ((-(g.coeff (i : ℕ)) : ℤ) : ℝ) ≤ (2 : ℝ) ^ m * S := by
        have : -(g.coeff (i : ℕ) : ℝ) ≤ (2 : ℝ) ^ m * S := by linarith
        simpa using this
      have h3 := Int.le_floor.mpr hthis
      linarith
    have hinj : Set.InjOn (fun g : Polynomial ℤ => fun i : Fin (m + 1) => g.coeff (i : ℕ)) T := by
      intro a ha b hb hab
      ext k
      by_cases hk : k ≤ m
      · have := congrFun hab ⟨k, Nat.lt_succ_iff.mpr hk⟩
        simpa using this
      · have hka : a.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt
          (p := a) (by rw [ha.1]; exact lt_of_not_ge hk)
        have hkb : b.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt
          (p := b) (by rw [hb.1]; exact lt_of_not_ge hk)
        rw [hka, hkb]
    exact Set.Finite.of_injOn hmapsto hinj hbox
  have hZT : ∀ z ∈ Z, minpoly ℤ z ∈ T := fun z hz => ⟨hz.1, hz.2⟩
  have himg : ((fun z : ℂ => minpoly ℤ z) '' Z).Finite :=
    hTfin.subset (by rintro g ⟨z, hz, rfl⟩; exact hZT z hz)
  have hfib : ∀ g ∈ (fun z : ℂ => minpoly ℤ z) '' Z,
      (Z ∩ (fun z : ℂ => minpoly ℤ z) ⁻¹' {g}).Finite ∧
      (Z ∩ (fun z : ℂ => minpoly ℤ z) ⁻¹' {g}).ncard ≤ m := by
    rintro g ⟨z0, hz0, rfl⟩
    have hg : (minpoly ℤ z0).natDegree = m := hz0.1
    have hg0 : minpoly ℤ z0 ≠ 0 := by
      intro h
      rw [h, Polynomial.natDegree_zero] at hg
      omega
    have hmap0 : (minpoly ℤ z0).map (Int.castRingHom ℂ) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (fun a b h => Int.cast_injective h)).mpr hg0
    have hrootfin : ({z : ℂ | ((minpoly ℤ z0).map (Int.castRingHom ℂ)).IsRoot z} : Set ℂ).Finite :=
      Set.Finite.subset
        (Finset.finite_toSet (((minpoly ℤ z0).map (Int.castRingHom ℂ)).roots.toFinset))
        (fun z hz => by
          rw [Finset.mem_coe, Multiset.mem_toFinset]
          exact (Polynomial.mem_roots hmap0).mpr hz)
    have hsub : (Z ∩ (fun z : ℂ => minpoly ℤ z) ⁻¹' {minpoly ℤ z0})
        ⊆ {z : ℂ | ((minpoly ℤ z0).map (Int.castRingHom ℂ)).IsRoot z} := by
      rintro z ⟨-, hzeq⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hzeq
      have haeval : aeval z (minpoly ℤ z) = 0 := minpoly.aeval ℤ z
      rw [hzeq, Polynomial.aeval_def] at haeval
      simpa [Polynomial.IsRoot, Polynomial.eval₂_eq_eval_map] using haeval
    exact ⟨hrootfin.subset hsub,
      (Set.ncard_le_ncard hsub hrootfin).trans (roots_card_le_of_natDegree_eq hg)⟩
  have hmain := ncard_le_mul_ncard_image_of_fiber_le (fun z : ℂ => minpoly ℤ z) Z m himg hfib
  have himgsub : ((fun z : ℂ => minpoly ℤ z) '' Z) ⊆ T := by
    rintro g ⟨z, hz, rfl⟩
    exact hZT z hz
  have himgle : (((fun z : ℂ => minpoly ℤ z) '' Z).ncard : ℝ) ≤ (T.ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard himgsub hTfin
  have hTbd : ((T.ncard : ℕ) : ℝ) ≤ ((2 : ℝ) ^ (m + 1) * S + 1) ^ (m + 1) := by
    rw [hT]
    exact Commons.NumberTheory.Polynomial.ncard_intpoly_mahler_le m S hS
  have hcast : (Z.ncard : ℝ) ≤ (m : ℝ) * (((fun z : ℂ => minpoly ℤ z) '' Z).ncard : ℝ) := by
    exact_mod_cast hmain
  exact hcast.trans (mul_le_mul_of_nonneg_left (himgle.trans hTbd) (Nat.cast_nonneg m))

end Submission.Vdw
