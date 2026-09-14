import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.NumberTheory.Polynomial.ncard_monic_intpoly_mahler_le
import Submission.Commons.NumberTheory.Polynomial.ncard_intpoly_mahler_le
import Submission.Commons.NumberTheory.Polynomial.finite_monic_poly_coeff_le
import Submission.Commons.Data.Set.ncard_le_sum_fiber

open Polynomial

namespace Commons.NumberTheory.Polynomial

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- The `ncard` of a finset regarded as a set is its cardinality. -/
lemma nmm_ncard_finset_coe {α : Type*} (t : Finset α) : ((t : Set α)).ncard = t.card := by
  rw [Set.ncard_eq_toFinset_card _ (Finset.finite_toSet t)]
  congr 1
  ext x
  rw [Set.Finite.mem_toFinset, Finset.mem_coe]

/-- A degree-`m` integer polynomial has at most `m` roots in `ℂ` (mapping to `ℂ` does
not increase the degree). -/
lemma nmm_roots_card_le_of_natDegree_eq {g : Polynomial ℤ} {m : ℕ} (hg : g.natDegree = m) :
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
    _ = (g.map (Int.castRingHom ℂ)).roots.toFinset.card := nmm_ncard_finset_coe _
    _ ≤ (g.map (Int.castRingHom ℂ)).roots.card := Multiset.toFinset_card_le _
    _ ≤ (g.map (Int.castRingHom ℂ)).natDegree := Polynomial.card_roots' _
    _ ≤ g.natDegree := Polynomial.natDegree_map_le
    _ = m := hg

/-- **Fibre-counting.**  For a map `φ : α → β` whose image on `s` is finite and
whose fibres inside `s` are finite of cardinality at most `N`,
`s.ncard ≤ N * (φ '' s).ncard`. -/
lemma nmm_ncard_le_mul_ncard_image_of_fiber_le {α β : Type*} (φ : α → β) (s : Set α) (N : ℕ)
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
`m·(2^(m+2)·S)^m`. -/
theorem ncard_monic_minpoly_mahler_le (m : ℕ) (hm : 1 ≤ m) (S : ℝ) (hS : 1 ≤ S) :
    (({z : ℂ | (minpoly ℤ z).Monic ∧ (minpoly ℤ z).natDegree = m ∧
        Polynomial.mapMahlerMeasure (minpoly ℤ z) (Int.castRingHom ℂ) ≤ S} : Set ℂ).ncard : ℝ)
      ≤ (m : ℝ) * ((2 : ℝ) ^ (m + 2) * S) ^ m := by
  classical
  set Z : Set ℂ := {z : ℂ | (minpoly ℤ z).Monic ∧ (minpoly ℤ z).natDegree = m ∧
      Polynomial.mapMahlerMeasure (minpoly ℤ z) (Int.castRingHom ℂ) ≤ S} with hZ
  set T : Set (Polynomial ℤ) :=
    {g | g.Monic ∧ g.natDegree = m ∧ Polynomial.mapMahlerMeasure g (Int.castRingHom ℂ) ≤ S}
    with hT
  -- `T` is finite: its members are monic of degree `m` with all coefficients bounded.
  have hTfin : T.Finite := by
    refine (finite_monic_poly_coeff_le (n := m) (fun _ => (2 : ℝ) ^ m * S)).subset ?_
    intro g hg
    rw [hT] at hg
    refine ⟨hg.1, hg.2.1, fun i _ => ?_⟩
    have h := coeff_abs_le_two_pow_natDegree_mul_mapMahlerMeasure g i
    rw [hg.2.1] at h
    exact h.trans (mul_le_mul_of_nonneg_left hg.2.2 (by positivity))
  have hZT : ∀ z ∈ Z, minpoly ℤ z ∈ T := fun z hz => by rw [hT]; exact hz
  have himg : ((fun z : ℂ => minpoly ℤ z) '' Z).Finite :=
    hTfin.subset (by rintro g ⟨z, hz, rfl⟩; exact hZT z hz)
  -- Fibres over a fixed minimal polynomial are roots of that polynomial.
  have hfib : ∀ g ∈ (fun z : ℂ => minpoly ℤ z) '' Z,
      (Z ∩ (fun z : ℂ => minpoly ℤ z) ⁻¹' {g}).Finite ∧
      (Z ∩ (fun z : ℂ => minpoly ℤ z) ⁻¹' {g}).ncard ≤ m := by
    rintro g ⟨z0, hz0, rfl⟩
    have hg0 : minpoly ℤ z0 ≠ 0 := hz0.1.ne_zero
    have hmap0 : (minpoly ℤ z0).map (Int.castRingHom ℂ) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (fun a b h => Int.cast_injective h)).mpr hg0
    have hrootfin :
        ({z : ℂ | ((minpoly ℤ z0).map (Int.castRingHom ℂ)).IsRoot z} : Set ℂ).Finite :=
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
      (Set.ncard_le_ncard hsub hrootfin).trans
        (nmm_roots_card_le_of_natDegree_eq hz0.2.1)⟩
  have hmain := nmm_ncard_le_mul_ncard_image_of_fiber_le (fun z : ℂ => minpoly ℤ z) Z m himg hfib
  have himgsub : ((fun z : ℂ => minpoly ℤ z) '' Z) ⊆ T := by
    rintro g ⟨z, hz, rfl⟩
    exact hZT z hz
  have himgle : ((((fun z : ℂ => minpoly ℤ z) '' Z).ncard : ℕ) : ℝ) ≤ (T.ncard : ℝ) :=
    by exact_mod_cast Set.ncard_le_ncard himgsub hTfin
  have hTbd : ((T.ncard : ℕ) : ℝ) ≤ ((2 : ℝ) ^ (m + 2) * S) ^ m := by
    rw [hT]
    exact ncard_monic_intpoly_mahler_le m S hS
  have hcast : (Z.ncard : ℝ) ≤ (m : ℝ) * (((fun z : ℂ => minpoly ℤ z) '' Z).ncard : ℝ) := by
    exact_mod_cast hmain
  exact hcast.trans (mul_le_mul_of_nonneg_left (himgle.trans hTbd) (Nat.cast_nonneg m))

end Commons.NumberTheory.Polynomial