import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.P2Core.siblingPlace
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.inv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Bookkeeping for the place set `TBlock` and the datum `prescDatum` of the `p = 2` recursion

This file collects the elementary facts about the `TwoRec` objects that the one-stage step
`preTwo_step` of the `p = 2` §4 recursion consumes, beyond what `ZDataTwo/TwoRec/defs.lean`
already provides:

* `exists_isFinPlace` — there *is* a finite place of `Ω` over `k` (needed to start the recursion:
  the state type `TwoRec.St` bundles the finiteness of every entry);
* `tblock_congr` — `TBlock S f m` depends only on `f 0, …, f (m-1)`;
* `tblock_covers_ram` — `TBlock` covers the places above `2` and the places ramified in `Λ` up to
  `K`-conjugacy (the oracle's `hTcov`);
* `tblock_mem_conjPlace`, `tblock_not_conjPlace_S` — the `k`-conjugacy case distinction for a block;
* `attach_unique` — at most one sibling attachment `(l, ρ)` (with `l < m`) is `K`-conjugate to a
  block, as soon as the escape primes are `K`-split and pairwise non-`k`-conjugate;
* `tblock_not_gesKConj_sibling` — no block of `TBlock S f j` is `K`-conjugate to a *genuine* sibling
  `siblingPlace K ρ (f j).1` (`ρ ≠ 1`) of its own escape prime;
* `prescDatum_attach` — the collapse of the `Finset.sum` defining `prescDatum` at a block with a
  unique attachment, in the general form (the attached index `ρ = 1` included).
-/

open scoped Pointwise

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.SSGRoute.NodeS37

open _root_.SSGRoute

open Work.SSGRoute.ZDataTwo.TwoRec (TBlock prescDatum eScalar attScalar)

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

section Exists

variable [IsAlgClosed Ω]

/-- **A finite place of `Ω` over `k` exists.**  Take a nonzero prime `𝔭` of `𝓞 k` and extend its
valuation ring to `Ω` (`Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime`,
applied to an algebraic extension). -/
theorem exists_isFinPlace (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] : ∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A := by
  haveI : Algebra.IsAlgebraic k Ω := IsAlgClosure.isAlgebraic
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (NumberField.RingOfIntegers k)
  have hne : M ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField k)
  obtain ⟨A, hA⟩ := Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime
    (K := k) (K' := Ω)
    (⟨M, hM.isPrime, hne⟩ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
  refine ⟨A, ?_⟩
  rw [SSGRoute.IsFinPlace, hA]
  exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top _

end Exists

section Basics

variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω] [IsAlgClosed Ω]

/-- `K`-conjugacy of places implies `k`-conjugacy. -/
theorem gesKConj_isConjPlace {A B : ValuationSubring Ω} (h : Work.SSGRoute.gesKConj K A B) :
    SSGRoute.IsConjPlace k A B :=
  h.imp (fun _ hτ => hτ.2)

/-- A sibling of a place is a `k`-conjugate of it. -/
theorem siblingPlace_isConjPlace (ρ : K ≃ₐ[k] K) (B : ValuationSubring Ω) :
    SSGRoute.IsConjPlace k (Work.SSGRoute.ZDataMup.siblingPlace K ρ B) B :=
  ⟨(Work.SSGRoute.ZDataMup.galLift K ρ)⁻¹,
    by rw [Work.SSGRoute.ZDataMup.siblingPlace, inv_smul_smul]⟩

/-- **`TBlock S f m` depends only on `f 0, …, f (m-1)`.** -/
theorem tblock_congr (S : Finset (ValuationSubring Ω)) {m : ℕ}
    {f g : ℕ → (ValuationSubring Ω × (↥K)ˣ)} (h : ∀ i < m, f i = g i) :
    TBlock (K := K) S f m = TBlock (K := K) S g m := by
  classical
  have hb : (Finset.range m).biUnion
        (fun j => Work.SSGRoute.ZDataMup.kleadReps K {((f j).1 : ValuationSubring Ω)}) =
      (Finset.range m).biUnion
        (fun j => Work.SSGRoute.ZDataMup.kleadReps K {((g j).1 : ValuationSubring Ω)}) :=
    Finset.biUnion_congr rfl (fun j hj => by rw [h j (Finset.mem_range.mp hj)])
  rw [Work.SSGRoute.ZDataTwo.TwoRec.TBlock, Work.SSGRoute.ZDataTwo.TwoRec.TBlock, hb]

/-- **`TBlock` covers the places above `2` and the places ramified in `Λ`** (up to `K`-conjugacy):
the oracle's hypothesis `hTcov`. -/
theorem tblock_covers_ram {Λ : IntermediateField k Ω} [FiniteDimensional k Λ] [IsGalois k Λ]
    (S : Finset (ValuationSubring Ω)) {m : ℕ} (f : ℕ → (ValuationSubring Ω × (↥K)ˣ))
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (2 : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B) :
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (2 : Ω) < 1) →
      ∃ A ∈ TBlock (K := K) S f m, Work.SSGRoute.gesKConj K A B := by
  intro B hB hram
  obtain ⟨A₀, hA₀, hc⟩ := hSram B hB hram
  exact Work.SSGRoute.ZDataTwo.TwoRec.TBlock_covers_S (K := K) hA₀ hc

/-- **Every block of `TBlock S f m` is a `k`-conjugate of a place of `S` or of an escape prime.** -/
theorem tblock_mem_conjPlace (S : Finset (ValuationSubring Ω)) {m : ℕ}
    {f : ℕ → (ValuationSubring Ω × (↥K)ˣ)} {A : ValuationSubring Ω}
    (hA : A ∈ TBlock (K := K) S f m) :
    (∃ B ∈ S, SSGRoute.IsConjPlace k A B) ∨
      (∃ j : ℕ, j < m ∧ SSGRoute.IsConjPlace k A (f j).1) := by
  rcases Work.SSGRoute.ZDataTwo.TwoRec.TBlock_mem_cases (K := K) hA with
    ⟨B, hB, ρ, hconj⟩ | ⟨j, hj, ρ, hconj⟩
  · exact Or.inl ⟨B, hB,
      SSGRoute.isConjPlace_trans (SSGRoute.isConjPlace_symm (gesKConj_isConjPlace hconj))
        (siblingPlace_isConjPlace (K := K) ρ B)⟩
  · exact Or.inr ⟨j, hj,
      SSGRoute.isConjPlace_trans (SSGRoute.isConjPlace_symm (gesKConj_isConjPlace hconj))
        (siblingPlace_isConjPlace (K := K) ρ (f j).1)⟩

/-- **A block that is not `k`-conjugate to a place of `S` is attached to an escape prime.** -/
theorem tblock_not_conjPlace_S (S : Finset (ValuationSubring Ω)) {m : ℕ}
    {f : ℕ → (ValuationSubring Ω × (↥K)ˣ)} {A : ValuationSubring Ω}
    (hA : A ∈ TBlock (K := K) S f m)
    (hnotS : ¬ ∃ B ∈ S, SSGRoute.IsConjPlace k A B) :
    ∃ j : ℕ, j < m ∧ SSGRoute.IsConjPlace k A (f j).1 := by
  rcases tblock_mem_conjPlace (K := K) S hA with h | h
  · exact absurd h hnotS
  · exact h

/-- **The attachment of a block to a sibling is unique.**  If `A` is `K`-conjugate both to the
`ρ`-sibling of `(f l).1` and to the `ρ'`-sibling of `(f l').1`, with `l, l' < m`, and the escape
primes `(f j).1`, `j < m`, are `K`-split and pairwise non-`k`-conjugate, then `(l, ρ) = (l', ρ')`.
This is `P2Core.siblingPlace_gesKConj_iff` in the form the collapse of the datum consumes. -/
theorem attach_unique {m : ℕ} {f : ℕ → (ValuationSubring Ω × (↥K)ˣ)}
    (hsplit : ∀ j < m, SSGRoute.IsSplitIn k K (f j).1)
    (hdisj : ∀ j l : ℕ, j < m → l < m → j ≠ l →
      ¬ SSGRoute.IsConjPlace k (f j).1 (f l).1)
    {A : ValuationSubring Ω} {q q' : ℕ × (K ≃ₐ[k] K)} (hq : q.1 < m) (hq' : q'.1 < m)
    (h : Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.siblingPlace K q.2 (f q.1).1) A)
    (h' : Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.siblingPlace K q'.2 (f q'.1).1) A) :
    q = q' := by
  classical
  have hchain : Work.SSGRoute.gesKConj K
      (Work.SSGRoute.ZDataMup.siblingPlace K q.2 (f q.1).1)
      (Work.SSGRoute.ZDataMup.siblingPlace K q'.2 (f q'.1).1) :=
    Work.SSGRoute.H9.swGesKConj_trans h (Work.SSGRoute.H9.swGesKConj_symm h')
  obtain ⟨hll, hrr⟩ := Work.SSGRoute.P2Core.siblingPlace_gesKConj_iff (K := K) m
    (fun j : Fin m => (f j.1).1)
    (fun j => hsplit j.1 j.2)
    (fun j j' hc => by
      by_contra hne
      exact hdisj j.1 j'.1 j.2 j'.2 (fun he => hne (Fin.ext he)) hc)
    ⟨q.1, hq⟩ ⟨q'.1, hq'⟩ q.2 q'.2 hchain
  exact Prod.ext (congrArg Fin.val hll) hrr

/-- **No block of a stage's place set is `K`-conjugate to a genuine sibling of its own escape
prime.**  `(f j).1` is `K`-conjugate only to its own sibling at `ρ = 1`. -/
theorem tblock_not_gesKConj_sibling (S : Finset (ValuationSubring Ω)) {m : ℕ}
    {f : ℕ → (ValuationSubring Ω × (↥K)ˣ)}
    (hdisj : ∀ i j : ℕ, i < j → j < m → ¬ SSGRoute.IsConjPlace k (f i).1 (f j).1)
    (hexcl : ∀ j < m, ∀ A ∈ TBlock (K := K) S f j,
      ¬ Work.SSGRoute.gesKConj K A (f j).1) :
    ∀ j < m, ∀ ρ : K ≃ₐ[k] K, ρ ≠ 1 →
      ∀ A' ∈ TBlock (K := K) S f j,
        ¬ Work.SSGRoute.gesKConj K A' (Work.SSGRoute.ZDataMup.siblingPlace K ρ (f j).1) := by
  intro j hj ρ _ A' hA' hconj
  have hA'k : SSGRoute.IsConjPlace k A' (f j).1 :=
    SSGRoute.isConjPlace_trans (gesKConj_isConjPlace hconj)
      (siblingPlace_isConjPlace (K := K) ρ (f j).1)
  rcases Work.SSGRoute.ZDataTwo.TwoRec.TBlock_mem_cases (K := K) hA' with
    ⟨B, hB, σ, hσ⟩ | ⟨i, hi, σ, hσ⟩
  · -- `A'` is `K`-conjugate to a sibling of a place `B ∈ S`
    have hslice : SSGRoute.IsConjPlace k (Work.SSGRoute.ZDataMup.siblingPlace K σ B) A' :=
      gesKConj_isConjPlace hσ
    have hA'B : SSGRoute.IsConjPlace k A' B :=
      SSGRoute.isConjPlace_trans (SSGRoute.isConjPlace_symm hslice)
        (siblingPlace_isConjPlace (K := K) σ B)
    have hBQ : SSGRoute.IsConjPlace k B (f j).1 :=
      SSGRoute.isConjPlace_trans (SSGRoute.isConjPlace_symm hA'B) hA'k
    obtain ⟨A'', hA'', hA''Q⟩ :=
      Work.SSGRoute.ZDataTwo.TwoRec.TBlock_covers_S (K := K) (f := f) hB hBQ
    exact hexcl j hj A'' hA'' hA''Q
  · -- `A'` is `K`-conjugate to a sibling of the escape prime `(f i).1`, `i < j`
    have hslice : SSGRoute.IsConjPlace k (Work.SSGRoute.ZDataMup.siblingPlace K σ (f i).1) A' :=
      gesKConj_isConjPlace hσ
    have hA'i : SSGRoute.IsConjPlace k A' (f i).1 :=
      SSGRoute.isConjPlace_trans (SSGRoute.isConjPlace_symm hslice)
        (siblingPlace_isConjPlace (K := K) σ (f i).1)
    exact hdisj i j hi hj (SSGRoute.isConjPlace_trans (SSGRoute.isConjPlace_symm hA'i) hA'k)

end Basics

section Datum

variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω] [IsAlgClosed Ω]

/-- **The collapse of `prescDatum` at a block with a unique attachment.**  If `A` is not
`k`-conjugate to any place of `S` and `(l, ρ)` is the *unique* pair with `l < m` and `A` in the
`K`-class of the `ρ`-sibling of `(f l).1`, then the `Finset.sum` defining `prescDatum` collapses to
the single term `-y + e_{l,ρ} · χ_{b_l}`.  Unlike `prescDatum_eq_of_attachment`, no side condition
on `ρ = 1` is needed: `eScalar` already vanishes there. -/
theorem prescDatum_attach {ζ : Ω} {hζ : IsPrimitiveRoot ζ 2} {hζK : ζ ∈ K}
    {S : Finset (ValuationSubring Ω)} {y : (Ω ≃ₐ[k] Ω) → ZMod 2}
    {f : ℕ → (ValuationSubring Ω × (↥K)ˣ)}
    {m : ℕ} {A : ValuationSubring Ω}
    (hS : ¬ ∃ A₀ ∈ S, SSGRoute.IsConjPlace k A₀ A)
    {l : ℕ} (hl : l < m) {ρ : K ≃ₐ[k] K}
    (hAtt : Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.siblingPlace K ρ (f l).1) A)
    (huniq : ∀ l' : ℕ, l' < m → ∀ ρ' : K ≃ₐ[k] K,
      Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.siblingPlace K ρ' (f l').1) A →
      l' = l ∧ ρ' = ρ) :
    prescDatum (K := K) ζ hζ hζK S y f m A
      = fun σ => - y σ + eScalar (K := K) ζ hζ hζK f l m ρ •
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f l).2 σ := by
  classical
  funext σ
  simp only [prescDatum, if_neg hS]
  congr 1
  rw [Finset.sum_eq_single (l, ρ) ?_ ?_]
  · rw [attScalar, if_pos hAtt, mul_one]
  · rintro ⟨l', ρ'⟩ hp hne
    obtain ⟨hl', -⟩ := Finset.mem_product.mp hp
    by_cases hρ' : Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.siblingPlace K ρ' (f l').1) A
    · obtain ⟨hll, hrr⟩ := huniq l' (Finset.mem_range.mp hl') ρ' hρ'
      exact absurd (by rw [hll, hrr] : (l', ρ') = (l, ρ)) hne
    · rw [attScalar, if_neg hρ', mul_zero, zero_smul]
  · intro hmem
    exact absurd (Finset.mem_product.mpr ⟨Finset.mem_range.mpr hl, Finset.mem_univ ρ⟩) hmem

end Datum

end Work.SSGRoute.NodeS37
