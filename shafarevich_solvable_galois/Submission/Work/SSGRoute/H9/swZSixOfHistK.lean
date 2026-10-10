import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.SSGRoute.H9.swHistK
import Submission.Work.SSGRoute.H9.swZSixDef
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The §4 assembly: the six conjuncts from a Kummer-form history

This file assembles Schmidt–Wingberg's auxiliary class `z` of §4 from a Kummer-form history
`f : ℕ → (Q_m, b_m)` (the invariants `Work.SSGRoute.H9.HistK` of `H9/swHistK.lean`) together with the
*chain* at the last escape prime (the two-place Hilbert reciprocity, stated in the form in which the
assembly consumes it: `χ_{b_i} + χ_{b_j}` vanishes on the local group at every *sibling* place
`galLift K σ • Q_j`, `σ ≠ 1`, of the last escape prime).

Concretely, for two stages `i < j` the class `z := χ_{b_i} + χ_{b_j}` is fed to
`Work.SSGRoute.ZSplit.sw_z_exists_odd_of_two_classes` (proved), whose hypotheses are discharged as
follows:

* additivity and local constancy: `ZSplit.nodeKummerCocharZMod_add` / `_locConst`;
* the prescribed value `2·χ_{b_m} = y` at the `cs(S)`-classes: the history's realisation clause
  together with `ZDataMup.histDatum_eq_zero_on_T0` (the accumulated corrections vanish on the blocks
  above `S`), transported from the `K`-class representatives to all `k`-conjugates by
  `ZDataMup.clause_one_of_covering`;
* the vanishing on the involutions: for odd `p`, `2·χ(c) = χ(c²) = χ(1) = 0` forces `χ(c) = 0`;
* the confinement of the ramification to `cs(Q_m)`: the history's confinement clause, plus the fact
  that every block of `T_m` is `k`-conjugate to `S` or to an *older* escape prime — so a place
  outside `cs(S)` which is not split in `N` cannot be `K`-conjugate to a block of `T_m` (older escape
  primes and their conjugates are `N`-split);
* the one-sided vanishing at the siblings of `Q_i` (the *prescription*, Schmidt–Wingberg's
  condition (3) with the corrected sign): the history's realisation clause at the stage `j`, where
  the datum at a sibling of `Q_i` is `−(χ_{b_i} + ½y)`;
* the one-sided vanishing at the siblings of `Q_j`: the **chain** `hchain`, which is the output of
  the two-place reciprocity `Work.SSGRoute.ZDataMup.swZTwoPlaceReciprocity` (proved) combined with
  the Frobenius dictionary and the shoe-box matching.
-/

namespace Work.SSGRoute.H9

open _root_.SSGRoute

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]

/-- The level-`K` Kummer cochain of the `m`-th element of a history. -/
noncomputable def histChi (K : IntermediateField k Ω) (ζ : Ω) (hζK : ζ ∈ K)
    (hζ : IsPrimitiveRoot ζ p) (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) (m : ℕ) :
    (Ω ≃ₐ[k] Ω) → ZMod p :=
  Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f m).2

/-- The class-form history of a Kummer-form history. -/
noncomputable def histClassSeq (K : IntermediateField k Ω) (ζ : Ω) (hζK : ζ ∈ K)
    (hζ : IsPrimitiveRoot ζ p) (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) :
    ℕ → (ValuationSubring Ω × ((Ω ≃ₐ[k] Ω) → ZMod p)) :=
  fun m => ((f m).1, histChi K ζ hζK hζ f m)

theorem histClassSeq_eq (K : IntermediateField k Ω) (ζ : Ω) (hζK : ζ ∈ K)
    (hζ : IsPrimitiveRoot ζ p) (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) :
    histClassSeq K ζ hζK hζ f
      = fun m => ((f m).1, Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f m).2) := rfl

/-- **A place of `T_m` is `k`-conjugate to `S` or to an older escape prime.** -/
theorem histPlacesK_mem_cases (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (S : Finset (ValuationSubring Ω)) (ζ : Ω) (hζK : ζ ∈ K) (hζ : IsPrimitiveRoot ζ p)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) (m : ℕ) {A : ValuationSubring Ω}
    (hA : A ∈ histPlacesK (p := p) K S ζ hζK hζ m f) :
    (∃ A₀ ∈ S, SSGRoute.IsConjPlace k A₀ A) ∨
      (∃ l : ℕ, l < m ∧ SSGRoute.IsConjPlace k ((f l).1) A) := by
  classical
  simp only [histPlacesK, Work.SSGRoute.ZDataMup.histPlaces, histClass,
    Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and] at hA
  rcases hA with hA | ⟨l, hA⟩
  · left
    exact Work.SSGRoute.ZDataMup.kleadReps_mem_conjPlace (p := p) K hA
  · right
    obtain ⟨A₀, hA₀, hc⟩ := Work.SSGRoute.ZDataMup.kleadReps_mem_conjPlace (p := p) K hA
    rw [Finset.mem_singleton] at hA₀
    exact ⟨l.1, l.2, hA₀ ▸ hc⟩

/-- **The escape primes of two distinct stages have distinct `k`-places** (in the form "no escape
prime is `k`-conjugate to an older one"), the consequence of the oracle's exclusion clause and of the
fact that `T_l` carries *all* the `K`-classes above the `k`-place of `Q_l`. -/
theorem histK_escape_kdisj (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) (hf : HistK (p := p) K N ζ hζ hζK S y f)
    {l m : ℕ} (hlm : l < m) : ¬ SSGRoute.IsConjPlace k ((f l).1) ((f m).1) := by
  classical
  intro hconj
  obtain ⟨-, -, -, hexcl, -⟩ := hf
  -- a representative of the `K`-class of `Q_m` inside `T_m`
  have hmem : ∃ A ∈ histPlacesK (p := p) K S ζ hζK hζ m f,
      Work.SSGRoute.gesKConj K A ((f m).1) := by
    have hT : Work.SSGRoute.ZDataMup.kleadReps K {((f l).1)} ⊆
        histPlacesK (p := p) K S ζ hζK hζ m f := by
      intro A hA
      simp only [histPlacesK, Work.SSGRoute.ZDataMup.histPlaces, histClass, Finset.mem_union,
        Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact Or.inr ⟨⟨l, hlm⟩, hA⟩
    obtain ⟨A', hA', hKA'⟩ := Work.SSGRoute.ZDataMup.kleadReps_covers K
      ({((f l).1)} : Finset (ValuationSubring Ω)) (Finset.mem_singleton_self _) hconj
    exact ⟨A', hT hA', hKA'⟩
  obtain ⟨A, hA, τ, hτ, hτA⟩ := hmem
  exact hexcl m A hA ⟨τ, hτ, hτA⟩


/-- **The half-`y` agreement at the classes of `S`.**  The stage-`m` class of a `HistK`-history
agrees with `½y` on the local group of every place of `cs(S)`: the prescribed total is `½y` plus the
accumulated corrections, and the corrections vanish on the `T₀`-blocks (the representatives of the
`K`-classes above `S`); `ZDataMup.clause_one_of_covering` transports the agreement from those
representatives to every `k`-conjugate. -/
theorem histChi_eq_halfY_at_csS (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω))
    (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) (hf : HistK (p := p) K N ζ hζ hζK S y f) (m : ℕ) :
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B →
        histChi K ζ hζK hζ f m σ = (2 : ZMod p)⁻¹ * y σ := by
  classical
  have hF : Work.SSGRoute.ZDataMup.HistInv (p := p) K N S y
      (histClassSeq (p := p) K ζ hζK hζ f) :=
    histClass_HistInv (p := p) K N ζ hζ hζK S y f hf
  have hFall := hF
  obtain ⟨-, -, -, -, -, -, hpres, -⟩ := hFall
  have hT : ∀ A ∈ Work.SSGRoute.ZDataMup.kleadReps K S,
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k A →
        (histClassSeq (p := p) K ζ hζK hζ f m).2 σ = (2 : ZMod p)⁻¹ * y σ := by
    intro A hA σ hσK hσA
    have hA' : A ∈ Work.SSGRoute.ZDataMup.histPlaces (p := p) K S
        (fun j : Fin m => histClassSeq (p := p) K ζ hζK hζ f j) :=
      Finset.mem_union_left _ hA
    have h1 := hpres m A hA' σ (Subgroup.mem_inf.mpr ⟨hσA, hσK⟩)
    have h0 := Work.SSGRoute.ZDataMup.histDatum_eq_zero_on_T0 (p := p) K N S y
      (histClassSeq (p := p) K ζ hζK hζ f) hF m A hA
    rw [h1, h0]
    simp
  refine Work.SSGRoute.ZDataMup.clause_one_of_covering (p := p) K ζ hζ hζK (f m).2
    (fun σ => (2 : ZMod p)⁻¹ * y σ) ?_ S (Work.SSGRoute.ZDataMup.kleadReps K S) ?_ ?_
  · intro g hg h hh
    show (2 : ZMod p)⁻¹ * y (g * h) = (2 : ZMod p)⁻¹ * y g + (2 : ZMod p)⁻¹ * y h
    rw [hy g hg h hh, mul_add]
  · intro B hB hconj
    obtain ⟨A, hA, hAB⟩ := hconj
    obtain ⟨A', hA', hKA'⟩ := Work.SSGRoute.ZDataMup.kleadReps_covers K S hA hAB
    obtain ⟨τ, hτ, hτA⟩ := hKA'
    exact ⟨A', hA', τ, hτ, hτA⟩
  · intro A hA σ hσK hσA
    exact hT A hA σ hσK hσA

/-- **The confinement of a stage of a `HistK`-history.**  The stage-`m` class kills the inertia at
every finite place outside `cs(S)` which is not split in `N`: such a place is `N`-split whenever it
is `k`-conjugate to a block of `T_m` (every block of `T_m` lies over `S` or over an *older* escape
prime, and the latter are `N`-split) and whenever it is `k`-conjugate to `Q_m` itself, and the
history's confinement clause applies. -/
theorem histChi_confinement (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω))
    (y : (Ω ≃ₐ[k] Ω) → ZMod p) (f : ℕ → (ValuationSubring Ω × (↥K)ˣ))
    (hf : HistK (p := p) K N ζ hζ hζK S y f) (m : ℕ) :
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
        histChi K ζ hζK hζ f m σ = 0 := by
  classical
  have hnorm : (N.fixingSubgroup).Normal := IsGalois.fixingSubgroup_normal_of_isGalois N
  obtain ⟨-, hsplit, -, -, -, hunr, -⟩ := hf
  intro B hB hS hns σ hσK hσI
  refine hunr m B hB (fun A hA hconj => ?_) (fun hconj => ?_) σ hσK hσI
  · rcases histPlacesK_mem_cases (p := p) K S ζ hζK hζ f m (A := A) hA with ⟨A₀, hA₀, hc⟩ | ⟨l, hlm, hc⟩
    · obtain ⟨τ, hτ, hτA⟩ := hconj
      obtain ⟨ρ, hρA⟩ := hc
      exact hS A₀ hA₀ (SSGRoute.isConjPlace_trans ⟨ρ, hρA⟩ ⟨τ, hτA⟩)
    · obtain ⟨τ, hτ, hτA⟩ := hconj
      obtain ⟨ρ, hρA⟩ := hc
      have hsplit_l : SSGRoute.IsSplitIn k N ((f l).1) := hsplit l
      have hB' : SSGRoute.IsSplitIn k N ((τ * ρ) • ((f l).1)) :=
        (SSGRoute.isSplitIn_conj N hnorm ((f l).1) (τ * ρ)).mpr hsplit_l
      exact hns (by rwa [mul_smul, hρA, hτA] at hB')
  · obtain ⟨τ, hτ, hτQ⟩ := hconj
    exact hns (by
      rw [← hτQ]
      exact (SSGRoute.isSplitIn_conj N hnorm ((f m).1) τ).mpr (hsplit m))

/-- **The involution clause**: for odd `p`, `χ_{b}(c) = 0` for every involution `c ∈ G_K`. -/
theorem histChi_involution_eq_zero (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (hp : p ≠ 2) (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) (m : ℕ) :
    ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → histChi K ζ hζK hζ f m c = 0 := by
  classical
  set χ : (Ω ≃ₐ[k] Ω) → ZMod p := histChi K ζ hζK hζ f m with hχdef
  have hχ1 : χ 1 = 0 := by
    have hadd := Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ (f m).2
    have h := hadd 1 K.fixingSubgroup.one_mem 1 K.fixingSubgroup.one_mem
    rw [one_mul] at h
    have h2 : χ 1 + χ 1 = χ 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h2
  intro c hc hc2
  have hadd := Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ (f m).2
  have h := hadd c hc c hc
  have hχ1' : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f m).2 1 = 0 := hχ1
  rw [← pow_two, hc2, hχ1'] at h
  have hsum : χ c + χ c = 0 := h.symm
  refine Work.SSGRoute.ZSplit.two_mul_eq_two_mul_zmod p hp (a := χ c) (b := 0) ?_
  show 2 * χ c = 2 * 0
  rw [two_mul, mul_zero]
  exact hsum


/-- **The six conjuncts of the §4 class from a Kummer-form history.**  The four non-elementary
inputs are hypotheses:

* `hconf_i`, `hconf_j` — the *refined confinement*: the stage-`m` class kills the inertia at every
  finite place outside its own escape class (`ZDataMup.HistInv`'s confinement clause alone leaves the
  blocks of `T_m` open, where the prescribed datum `½y`, `0` or `−z_j` is unramified);
* `hpresc` — the *prescription* of condition (3) at the siblings of the first escape prime:
  `χ_{b_i} + χ_{b_j}` vanishes on the local group of every `k`-conjugate of `Q_i` that is not a
  `K`-conjugate (there the stage-`j` datum is `−χ_{b_i} − ½y`);
* `hchain` — the *chain* at the last escape prime: the sibling vanishing at `Q_j`, i.e. the two-place
  Hilbert reciprocity `χ b_i ψ_j = χ b_j ψ_i` combined with the shoe-box matching.

Clause 1 and the involution clause are `ZSplit.sw_sum_conjuncts_one_four`; clauses 2 and 3 are
`ZSplit.sw_conjuncts_five_six`. -/
theorem ZSix_of_histK (hp : p ≠ 2)
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω))
    (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) (hf : HistK (p := p) K N ζ hζ hζK S y f)
    (i j : ℕ) (hij : i < j)
    (hconf_i : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      ¬ Work.SSGRoute.gesKConj K ((f i).1) B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → histChi K ζ hζK hζ f i σ = 0)
    (hconf_j : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      ¬ Work.SSGRoute.gesKConj K ((f j).1) B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → histChi K ζ hζK hζ f j σ = 0)
    (hpresc : ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k ((f i).1) Q →
      (¬ ∃ τ ∈ K.fixingSubgroup, τ • ((f i).1) = Q) →
      ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup,
        histChi K ζ hζK hζ f i τ + histChi K ζ hζK hζ f j τ = 0)
    (hchain : ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k ((f j).1) Q →
      (¬ ∃ τ ∈ K.fixingSubgroup, τ • ((f j).1) = Q) →
      ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup,
        histChi K ζ hζK hζ f i τ + histChi K ζ hζK hζ f j τ = 0) :
    ZSix p k Ω K N S y := by
  classical
  have hfin : ∀ m : ℕ, SSGRoute.IsFinPlace k ((f m).1) := hf.1
  have hsplit : ∀ m : ℕ, SSGRoute.IsSplitIn k N ((f m).1) := hf.2.1
  set zi : (Ω ≃ₐ[k] Ω) → ZMod p := histChi K ζ hζK hζ f i with hzidef
  set zj : (Ω ≃ₐ[k] Ω) → ZMod p := histChi K ζ hζK hζ f j with hzjdef
  have h2ne : (2 : ZMod p) ≠ 0 := fun h0 => hp (by
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h0
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    exact le_antisymm hle hp2)
  -- clauses 1 and 4
  have h14 := Work.SSGRoute.ZSplit.sw_sum_conjuncts_one_four (p := p) hp K S y zi zj
    (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ (f i).2)
    (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ (f j).2)
    (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ (f i).2)
    (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ (f j).2)
    (fun B hB hconj σ hσK hσd => by
      have h := histChi_eq_halfY_at_csS (p := p) K N ζ hζ hζK S y hy f hf i B hB hconj σ hσK hσd
      show 2 * histChi K ζ hζK hζ f i σ = y σ
      rw [h, ← mul_assoc, mul_inv_cancel₀ h2ne, one_mul])
    (fun B hB hconj σ hσK hσd => by
      have h := histChi_eq_halfY_at_csS (p := p) K N ζ hζ hζK S y hy f hf j B hB hconj σ hσK hσd
      show 2 * histChi K ζ hζK hζ f j σ = y σ
      rw [h, ← mul_assoc, mul_inv_cancel₀ h2ne, one_mul])
    (histChi_involution_eq_zero (p := p) K hp ζ hζ hζK f i)
    (histChi_involution_eq_zero (p := p) K hp ζ hζ hζK f j)
  obtain ⟨h1, h2, h3, h4⟩ := h14
  -- clauses 2 and 3 from the confinements and the two sibling vanishings
  have hconf : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ ∃ τ ∈ K.fixingSubgroup, τ • ((f i).1) = B) →
      (¬ ∃ τ ∈ K.fixingSubgroup, τ • ((f j).1) = B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → (zi + zj) σ = 0 := by
    intro B hB hni hnj σ hσK hσI
    rw [_root_.Pi.add_apply, hconf_i B hB hni σ hσK hσI, hconf_j B hB hnj σ hσK hσI, add_zero]
  obtain ⟨h5, h6⟩ := Work.SSGRoute.ZSplit.sw_conjuncts_five_six (p := p) K N S
    ((f i).1) ((f j).1) (hfin i) (hfin j) (hsplit i) (hsplit j) (zi + zj) hconf hpresc hchain
  exact ⟨zi + zj,
    by rw [hzidef, hzjdef] at h1; exact h1,
    h2,
    by rw [hzidef, hzjdef] at h3; exact h3,
    h4, h5, h6⟩

end Work.SSGRoute.H9
