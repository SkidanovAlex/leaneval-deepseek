import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.H9.histChi_conj_transport
import Submission.Work.SSGRoute.H9.histChi_sibling_escape
import Submission.Work.SSGRoute.H9.histChi_zero_at_T0
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.H9

/-- **The refined confinement of a stage of the §4 recursion.**  The stage-`m` class `χ_{b_m}` of a
`HistK`-history kills the inertia at every finite place `B` outside its own escape class
(`¬ gesKConj K Q_m B`).  This strengthens `Work.SSGRoute.H9.histChi_confinement` (which needs `B`
outside `cs(S)` and not split in `N`) and is the `hconf` input of
`Work.SSGRoute.H9.ZSix_of_histK`.

Proof: the `HistK` confinement clause handles the places outside `cs(T_m) ∪ cs(Q_m)`.  For the
remaining ones, `B` is `K`-conjugate to a block `A ∈ T_m`; at `A` the realisation clause gives
`χ_m = ½y + histDatum(m)(A)`, and the accumulation is evaluated block by block:
* `A ∈ kleadReps K S`: every correction vanishes (`histDatum_eq_zero_on_T0`), so `χ_m = ½y`, which
  kills the inertia at `A` by `hyT`;
* `A` `K`-conjugate to an older escape prime `Q_l`: the total is `0` (`histDatum`'s own-class case),
  or `−χ_{b_l}` at the siblings of `Q_l` — and `χ_{b_l}` kills the inertia there by the confinement
  clause at stage `l` (`A` is neither `K`-conjugate to a block of `T_l` nor to `Q_l`).
The corrections of the *other* older stages vanish because the escape primes have pairwise distinct
`k`-places (`Work.SSGRoute.H9.histK_escape_kdisj`); the passage from `A` to `B` is the conjugation
invariance `Work.SSGRoute.ZDataMup.nodeKummerCocharZMod_conj` (together with the same invariance of
`y`, `ZDataMup.additive_conj_invariant`). -/
theorem swHistChi_confinement_proved {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {k Ω : Type} [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω))
    (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ))
    (hf : Work.SSGRoute.H9.HistK (p := p) K N ζ hζ hζK S y f) (m : ℕ) :
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      ¬ Work.SSGRoute.gesKConj K ((f m).1) B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
        Work.SSGRoute.H9.histChi K ζ hζK hζ f m σ = 0 := by
  classical
  -- Strong induction on the stage: the sibling case at stage `m` needs the confinement of the
  -- *older* stage `l < m`, which the induction hypothesis at `l` supplies.
  have key : ∀ n : ℕ, ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      ¬ Work.SSGRoute.gesKConj K ((f n).1) B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
        Work.SSGRoute.H9.histChi K ζ hζK hζ f n σ = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro B hB hQmB σ hσK hσI
      have hpres := hf.2.2.2.2.1
      have hunr := hf.2.2.2.2.2.1
      by_cases hT : ∃ A ∈ Work.SSGRoute.H9.histPlacesK (p := p) K S ζ hζK hζ n f,
          Work.SSGRoute.gesKConj K A B
      · -- `B` is `K`-conjugate to a block `A` of `T_n`: conjugate `σ` back to `A`
        obtain ⟨A, hA, τ, hτ, hτA⟩ := hT
        have hAeq : A = τ⁻¹ • B := by rw [← hτA, inv_smul_smul]
        have hAfin : SSGRoute.IsFinPlace k A := by
          rw [hAeq]
          exact (Work.SSGRoute.isFinPlace_smul_iff (k := k) B τ⁻¹).mpr hB
        have hσ'I : SSGRoute.IsInertia k A (τ⁻¹ * σ * τ) := by
          have h := (Work.SSGRoute.isInertia_conj (k := k) B τ⁻¹ σ).mpr hσI
          rw [hAeq]
          exact h
        have hσ'K : τ⁻¹ * σ * τ ∈ K.fixingSubgroup :=
          K.fixingSubgroup.mul_mem
            (K.fixingSubgroup.mul_mem (K.fixingSubgroup.inv_mem hτ) hσK) hτ
        refine histChi_conj_transport K ζ hζ hζK f n hτ ?_
        -- the case analysis at the block `A` of `T_n`
        have hA' := hA
        simp only [Work.SSGRoute.H9.histPlacesK, Work.SSGRoute.ZDataMup.histPlaces,
          Work.SSGRoute.H9.histClass, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ,
          true_and] at hA'
        rcases hA' with hA0 | ⟨l, hAesc⟩
        · -- `A` is a representative of a `K`-class above `S`
          exact histChi_zero_at_T0 K N ζ hζ hζK S y hyT f hf n hA0 hAfin hσ'K hσ'I
        · -- `A` lies in the escape class of the older stage `l < n`
          obtain ⟨A₀, hA₀mem, hc⟩ :=
            Work.SSGRoute.ZDataMup.kleadReps_mem_conjPlace (p := p) K hAesc
          rw [Finset.mem_singleton] at hA₀mem
          have hAconj : SSGRoute.IsConjPlace k ((f l.1).1) A := by
            rw [hA₀mem] at hc
            exact hc
          have hsep := histK_not_isConjPlace_of_isConjPlace K N ζ hζ hζK S y f hf hAconj
          by_cases hown : Work.SSGRoute.gesKConj K ((f l.1).1) A
          · -- `A` is the `K`-class of `Q_l` itself: the datum is `−½y`, so `χ_n = ½y − ½y = 0`
            have hdz := histDatumK_escape_block_own K S ζ hζ hζK y f n l.2 hown hsep
            have hpresA := hpres n A hA (τ⁻¹ * σ * τ)
              (Subgroup.mem_inf.mpr ⟨hσ'I.1, hσ'K⟩)
            show Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f n).2
              (τ⁻¹ * σ * τ) = 0
            rw [hpresA, hdz]
            simp
          · -- `A` is a *sibling* of `Q_l`: the datum is `−χ_{b_l} − ½y`, so `χ_n = −χ_{b_l}`
            exact histChi_sibling_escape K N ζ hζ hζK S y f hf n l.2 hA hAconj hown hsep
              hσ'K hσ'I
              (ih l.1 l.2 A hAfin hown (τ⁻¹ * σ * τ) hσ'K hσ'I)
      · -- `B` is outside `cs(T_n)`: the history's own confinement clause applies
        show Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f n).2 σ = 0
        exact hunr n B hB (fun A hA hc => hT ⟨A, hA, hc⟩) hQmB σ hσK hσI
  exact key m

end Work.SSGRoute.H9
