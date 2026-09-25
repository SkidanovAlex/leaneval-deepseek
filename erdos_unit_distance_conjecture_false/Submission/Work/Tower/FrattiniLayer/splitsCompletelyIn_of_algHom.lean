import Mathlib
import Submission.Work.Tower.Defs
import Submission.Work.Tower.FrattiniLayer.Basic
import Submission.Work.Tower.FrattiniLayer.splitsCompletelyIn_bot
import Submission.Work.Tower.FrattiniLayer.splitsCompletelyIn_of_finset

/-!
# Complete splitting descends along embeddings of number fields

If the prime `𝔭` of `𝓞 F` splits completely in the number field `L`, and `L'` is a number
field that embeds into `L` over `F` (via an `F`-algebra homomorphism `φ : L' →ₐ[F] L`), then
`𝔭` splits completely in `L'` as well.

The proof is the classical one.  View `L'` as an intermediate field of `L` through `φ`, and
compare the primes above `𝔭` in the two rings of integers:

* `𝔭 ≠ ⊥`.  Every prime `𝔔` of `𝓞 L` over `𝔭` has an image `𝔔.under (𝓞 L')` in `𝓞 L'`, again a
  prime over `𝔭`, and the residue ring of the image is isomorphic to that of `𝔔` (the inclusions
  `(𝓞 F)⧸𝔭 ↪ (𝓞 L')⧸𝔔.under ↪ (𝓞 L)⧸𝔔` form a chain of injections between finite rings whose
  total cardinality is unchanged).
* The fibres of this map `𝔔 ↦ 𝔔.under (𝓞 L')` are the primes above `𝔔.under (𝓞 L')`, of which
  there are at most `[L : L']` by the fundamental identity `∑ e f = [L : L']`.  Hence the image
  of the `[L : F]` primes over `𝔭` in `L` has at least `[L : F]/[L : L'] = [L' : F]` elements,
  all of which are primes of `𝓞 L'` over `𝔭` with residue ring `(𝓞 F)⧸𝔭`.  This is exactly the
  (one-sided) content of `SplitsCompletelyIn F L' 𝔭`.
* `𝔭 = ⊥`.  Then the only prime of `𝓞 L` over `𝔭` is `⊥`, so complete splitting forces
  `[L : F] = 1`, hence also `[L' : F] = 1` and `SplitsCompletelyIn F L' ⊥` holds trivially
  (`splitsCompletelyIn_bot`).

## Main result

* `splitsCompletelyIn_of_algHom`.
-/

open NumberField
open scoped Classical

namespace Work.Tower.FrattiniLayer

/-- **Residue rings of contractions.**  Let `Q` be a prime of `𝓞 L` over `𝔭 ≠ ⊥` whose residue
ring is `(𝓞 F) ⧸ 𝔭`.  Then the contraction `Q.under (𝓞 L')` (with respect to an algebra structure
`L'`-on-`L`) also has residue ring `(𝓞 F) ⧸ 𝔭`.

Indeed, the inclusions `(𝓞 F)⧸𝔭 → (𝓞 L')⧸Q.under → (𝓞 L)⧸Q` are injective maps between finite
rings whose composite has source and target of the same cardinality, so the first one is
bijective. -/
theorem residueIso_of_under {F L L' : Type*} [Field F] [NumberField F] [Field L] [NumberField L]
    [Field L'] [NumberField L'] [Algebra F L] [Algebra F L'] [FiniteDimensional F L]
    [FiniteDimensional F L'] [Algebra L' L] [IsScalarTower F L' L]
    (𝔭 : Ideal (𝓞 F)) (h𝔭 : 𝔭 ≠ ⊥) (Q : Ideal (𝓞 L)) [hQp : Q.IsPrime] [hQ : Q.LiesOver 𝔭]
    (e : (𝓞 L) ⧸ Q ≃+* (𝓞 F) ⧸ 𝔭) :
    Nonempty ((𝓞 L') ⧸ (Q.under (𝓞 L')) ≃+* (𝓞 F) ⧸ 𝔭) := by
  set P' : Ideal (𝓞 L') := Q.under (𝓞 L') with hP'def
  haveI hP'lies : P'.LiesOver 𝔭 := Ideal.LiesOver.tower_bot Q P' 𝔭
  have hP'ne : P' ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭 P'
  haveI hP'prime : P'.IsPrime := hQp.under (𝓞 L')
  have hQne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭 Q
  haveI : FaithfulSMul ((𝓞 F) ⧸ 𝔭) ((𝓞 L') ⧸ P') := Ideal.Quotient.instFaithfulSMul P' 𝔭
  have hf : Function.Injective (algebraMap ((𝓞 F) ⧸ 𝔭) ((𝓞 L') ⧸ P')) :=
    FaithfulSMul.algebraMap_injective _ _
  have hH : ∀ a : 𝓞 L', a ∈ P' → ((Ideal.Quotient.mk Q).comp (algebraMap (𝓞 L') (𝓞 L))) a = 0 := by
    intro a ha
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    rw [hP'def, Ideal.under_def] at ha
    exact Ideal.mem_comap.mp ha
  set g : (𝓞 L') ⧸ P' →+* (𝓞 L) ⧸ Q :=
    Ideal.Quotient.lift P' ((Ideal.Quotient.mk Q).comp (algebraMap (𝓞 L') (𝓞 L))) hH with hgdef
  have hg : Function.Injective g := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hgdef] at hxy
    simp only [Ideal.Quotient.lift_mk, RingHom.comp_apply] at hxy
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hxy ⊢
    rw [← map_sub] at hxy
    rw [hP'def, Ideal.under_def, Ideal.mem_comap]
    exact hxy
  haveI hfinB : Finite ((𝓞 L') ⧸ P') := Ring.HasFiniteQuotients.finiteQuotient hP'ne
  haveI hfinC : Finite ((𝓞 L) ⧸ Q) := Ring.HasFiniteQuotients.finiteQuotient hQne
  haveI hfinA : Finite ((𝓞 F) ⧸ 𝔭) := Ring.HasFiniteQuotients.finiteQuotient h𝔭
  have h1 : Nat.card ((𝓞 F) ⧸ 𝔭) ≤ Nat.card ((𝓞 L') ⧸ P') := Nat.card_le_card_of_injective _ hf
  have h2 : Nat.card ((𝓞 L') ⧸ P') ≤ Nat.card ((𝓞 L) ⧸ Q) := Nat.card_le_card_of_injective _ hg
  have h3 : Nat.card ((𝓞 L) ⧸ Q) = Nat.card ((𝓞 F) ⧸ 𝔭) := Nat.card_congr e.toEquiv
  have heq : Nat.card ((𝓞 F) ⧸ 𝔭) = Nat.card ((𝓞 L') ⧸ P') := le_antisymm h1 (h2.trans_eq h3)
  letI : Fintype ((𝓞 F) ⧸ 𝔭) := Fintype.ofFinite _
  letI : Fintype ((𝓞 L') ⧸ P') := Fintype.ofFinite _
  refine ⟨(RingEquiv.ofBijective (algebraMap ((𝓞 F) ⧸ 𝔭) ((𝓞 L') ⧸ P')) ?_).symm⟩
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨hf, ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  exact heq

/-- **Finitely many primes, bounded by the degree.**  For a prime `P'` of `𝓞 L'` over `𝔭 ≠ ⊥`,
the number of primes of `𝓞 L` lying over `P'` is at most `[L : L']`.  This is the fundamental
identity `∑_{Q | P'} e(Q/P') f(Q/P') = [L : L']` of ramification theory together with
`e, f ≥ 1`. -/
theorem ncard_primesOver_le_finrank {F L L' : Type*} [Field F] [NumberField F] [Field L]
    [NumberField L] [Field L'] [NumberField L'] [Algebra F L] [Algebra F L']
    [FiniteDimensional F L] [FiniteDimensional F L'] [Algebra L' L] [IsScalarTower F L' L]
    (𝔭 : Ideal (𝓞 F)) (h𝔭 : 𝔭 ≠ ⊥) (P' : Ideal (𝓞 L')) [hP'p : P'.IsPrime] [hP'l : P'.LiesOver 𝔭] :
    (P'.primesOver (𝓞 L)).ncard ≤ Module.finrank L' L := by
  have hP'ne : P' ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭 P'
  haveI hP'max : P'.IsMaximal := Ideal.IsPrime.isMaximal hP'p hP'ne
  haveI hfin : Fintype (P'.primesOver (𝓞 L)) :=
    (IsDedekindDomain.primesOver_finite P' (𝓞 L)).fintype
  have hsum := Ideal.sum_ramification_inertia (𝓞 L) L' L (p := P') hP'ne
  have hcard : (P'.primesOver (𝓞 L)).ncard =
      (IsDedekindDomain.primesOverFinset P' (𝓞 L)).card := by
    rw [← IsDedekindDomain.coe_primesOverFinset hP'ne, Set.ncard_coe_finset]
  rw [hcard, ← hsum]
  have h := Finset.card_nsmul_le_sum (IsDedekindDomain.primesOverFinset P' (𝓞 L))
      (fun P => P'.ramificationIdx' P * P'.inertiaDeg' P) 1 (fun Q hQ => ?_)
  · simpa using h
  · have hmem : Q ∈ P'.primesOver (𝓞 L) :=
      (IsDedekindDomain.mem_primesOverFinset_iff hP'ne (𝓞 L)).mp hQ
    haveI : Q.IsPrime := hmem.1
    haveI : Q.LiesOver P' := hmem.2
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver Q hP'ne)
        (P'.inertiaDeg'_pos Q).ne')

theorem splitsCompletelyIn_of_algHom {F L L' : Type*} [Field F] [NumberField F] [Field L]
    [NumberField L] [Field L'] [NumberField L']
    [Algebra F L] [Algebra F L'] [FiniteDimensional F L] [FiniteDimensional F L']
    (𝔭 : Ideal (NumberField.RingOfIntegers F))
    (φ : L' →ₐ[F] L) (h : Work.Tower.SplitsCompletelyIn F L 𝔭) :
    Work.Tower.SplitsCompletelyIn F L' 𝔭 := by
  by_cases hbot : 𝔭 = ⊥
  · subst hbot
    exact splitsCompletelyIn_bot φ h
  · obtain ⟨𝔔, h𝔔prime, h𝔔lies, h𝔔inj, h𝔔res⟩ := h
    -- view `L` as an `L'`-algebra via `φ`
    letI : Algebra L' L := φ.toRingHom.toAlgebra
    haveI hst : IsScalarTower F L' L := IsScalarTower.of_algebraMap_eq (fun x => by
      rw [RingHom.algebraMap_toAlgebra]; exact (φ.commutes x).symm)
    have hn : 0 < Module.finrank F L := Module.finrank_pos
    haveI h0p : (𝔔 ⟨0, hn⟩).IsPrime := h𝔔prime _
    haveI h0l : (𝔔 ⟨0, hn⟩).LiesOver 𝔭 := h𝔔lies _
    have h𝔭prime : 𝔭.IsPrime := Ideal.isPrime_of_liesOver (𝔔 ⟨0, hn⟩) 𝔭
    -- the contraction of the primes over `𝔭` in `L` down to `L'`
    let g : Fin (Module.finrank F L) → Ideal (𝓞 L') := fun i => (𝔔 i).under (𝓞 L')
    have hgprime : ∀ i, (g i).IsPrime := fun i => (h𝔔prime i).under (𝓞 L')
    have hglies : ∀ i, (g i).LiesOver 𝔭 := fun i => by
      haveI := h𝔔lies i
      exact Ideal.LiesOver.tower_bot (𝔔 i) (g i) 𝔭
    have hgres : ∀ i, Nonempty ((𝓞 L') ⧸ g i ≃+* (𝓞 F) ⧸ 𝔭) := fun i => by
      haveI := h𝔔prime i
      haveI := h𝔔lies i
      obtain ⟨e⟩ := h𝔔res i
      exact residueIso_of_under 𝔭 hbot (𝔔 i) e
    -- every fibre of `g` has at most `[L : L']` elements
    have hfiber : ∀ b ∈ Finset.univ.image g,
        (Finset.univ.filter (fun i => g i = b)).card ≤ Module.finrank L' L := by
      intro b hb
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hb
      haveI : (g i).IsPrime := hgprime i
      haveI : (g i).LiesOver 𝔭 := hglies i
      have hgine : g i ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hbot (g i)
      haveI : (g i).IsMaximal := Ideal.IsPrime.isMaximal (hgprime i) hgine
      have hsub : (Finset.univ.filter (fun j => g j = g i)).image (fun j => 𝔔 j) ⊆
          IsDedekindDomain.primesOverFinset (g i) (𝓞 L) := by
        intro Q hQ
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hQ
        rw [Finset.mem_filter] at hj
        rw [IsDedekindDomain.mem_primesOverFinset_iff hgine (𝓞 L)]
        exact ⟨h𝔔prime j, ⟨hj.2.symm⟩⟩
      have hinj : Set.InjOn (fun j : Fin (Module.finrank F L) => 𝔔 j)
          ↑(Finset.univ.filter (fun j => g j = g i)) := fun a _ c _ hac => h𝔔inj hac
      calc (Finset.univ.filter (fun j => g j = g i)).card
          = ((Finset.univ.filter (fun j => g j = g i)).image (fun j => 𝔔 j)).card :=
            (Finset.card_image_of_injOn hinj).symm
        _ ≤ (IsDedekindDomain.primesOverFinset (g i) (𝓞 L)).card := Finset.card_le_card hsub
        _ = ((g i).primesOver (𝓞 L)).ncard := by
            rw [← IsDedekindDomain.coe_primesOverFinset hgine (𝓞 L), Set.ncard_coe_finset]
        _ ≤ Module.finrank L' L := ncard_primesOver_le_finrank 𝔭 hbot (g i)
    -- the pigeonhole bound `[L : F] ≤ [L' : F] · #image`
    have hpigeon : Module.finrank F L ≤ Module.finrank L' L * (Finset.univ.image g).card := by
      have h := Finset.card_le_mul_card_image (Finset.univ : Finset (Fin (Module.finrank F L)))
        (Module.finrank L' L) hfiber
      simpa using h
    have htower : Module.finrank F L' * Module.finrank L' L = Module.finrank F L :=
      Module.finrank_mul_finrank F L' L
    have hmpos : 0 < Module.finrank L' L := Module.finrank_pos
    have hcard : Module.finrank F L' ≤ (Finset.univ.image g).card := by
      refine Nat.le_of_mul_le_mul_right ?_ hmpos
      calc Module.finrank F L' * Module.finrank L' L = Module.finrank F L := htower
        _ ≤ Module.finrank L' L * (Finset.univ.image g).card := hpigeon
        _ = (Finset.univ.image g).card * Module.finrank L' L := Nat.mul_comm _ _
    exact splitsCompletelyIn_of_finset 𝔭 (Finset.univ.image g) (fun P hP => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hP
      exact ⟨hgprime i, hglies i, hgres i⟩) hcard

end Work.Tower.FrattiniLayer
