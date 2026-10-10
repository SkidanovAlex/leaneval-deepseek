import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Basic.Complex.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.PT.archPairLocal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The involution half of the hub: the family `Work.SSGRoute.PT.archFamily`

`flags_2305` (see `PT/NOTE_s17d_flags2305_local_archPair.md`) replaces the involution half of
`G1⁺` — `E7Arch.pairArchFamily`, whose values are the explicit formula `Ach.archPair` — by the
**class-formation** pairing `PT.archPairLocal`, so that clause (7) becomes
`PT.classFormation_reciprocity_allPlaces` and clause (8) has its `hpairArch` by construction.

`PT.archPairLocal` is defined at one involution `c ≠ 1` (with its fixed level `L_c` and seam place
`u_c`) and is only meaningful there.  The hub needs a *family* `arch M H a b`, i.e. a function of the
subgroup `H`, so this file chooses the generator of `H` once and for all, and is `0` off the
involution groups *and on* `⊥ = zpowers 1` (see `PT/PING_s18_arch_zero_at_bot.md`: clause (7)'s `C'`
may contain `1`, and `PairReciprocity` for `C'' ∪ {1}` forces `pair M ⊥ a b = 0`; the zero pairing on
`⊥` does satisfy `PairClauses` there, because `IsCocycleOn act ⊥ f` forces `f 1 = 0`, i.e. every
cocycle on the trivial group is already a coboundary).

The seam embeddings `φc c hc2 hc1` are a *parameter*: they are the hub's Artin–Schreier/seam data
(`finiteS_converse_canonical_v7`'s `φc`/`hseam`); picking them once is what makes `archFamily` a
single canonical object, as the clauses require.
-/

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section GenInv

variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]

/-- The canonical generator attached to an involution `c` with `c ^ 2 = 1`: the `Classical.choose` of
the existential produced by `c` itself.  (A separate `def` so that the family's internal
`Classical.choose` and this one are *the same term*, exactly as `E7Arch.genArch` does for
`E7Arch.pairArchFamily`.) -/
noncomputable def genInv (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) : Ω ≃ₐ[k] Ω :=
  Classical.choose (show ∃ c' : Ω ≃ₐ[k] Ω, c' ^ 2 = 1 ∧ Subgroup.zpowers c = Subgroup.zpowers c'
    from ⟨c, hc2, rfl⟩)

theorem genInv_spec (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) :
    (genInv k Ω c hc2) ^ 2 = 1 ∧ Subgroup.zpowers c = Subgroup.zpowers (genInv k Ω c hc2) :=
  Classical.choose_spec (show ∃ c' : Ω ≃ₐ[k] Ω, c' ^ 2 = 1 ∧ Subgroup.zpowers c = Subgroup.zpowers c'
    from ⟨c, hc2, rfl⟩)

theorem genInv_sq (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) : (genInv k Ω c hc2) ^ 2 = 1 :=
  (genInv_spec k Ω c hc2).1

theorem zpowers_genInv (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) :
    Subgroup.zpowers (genInv k Ω c hc2) = Subgroup.zpowers c :=
  (genInv_spec k Ω c hc2).2.symm

/-- An involution generates a subgroup with at most two elements. -/
theorem eq_one_or_eq_of_mem_zpowers (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1)
    {x : Ω ≃ₐ[k] Ω} (hx : x ∈ Subgroup.zpowers c) : x = 1 ∨ x = c := by
  have hc2z : c ^ (2 : ℤ) = 1 := by simpa using hc2
  rw [Subgroup.mem_zpowers_iff] at hx
  obtain ⟨m, rfl⟩ := hx
  rw [zpow_eq_zpow_emod m hc2z]
  have hlt : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases hlt with h | h <;> rw [h] <;> simp

/-- **The canonical generator is the involution itself** (for `c ≠ 1`): `⟨c⟩` is the two-element
group `{1, c}`, and `genInv k Ω c hc2` generates it and has order dividing two, so it is not `1`. -/
theorem genInv_eq (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) :
    genInv k Ω c hc2 = c := by
  have hspec := genInv_spec k Ω c hc2
  have hmem : genInv k Ω c hc2 ∈ Subgroup.zpowers c := by
    rw [hspec.2]; exact Subgroup.mem_zpowers _
  rcases eq_one_or_eq_of_mem_zpowers k Ω c hc2 hmem with h | h
  · exfalso
    have hz : Subgroup.zpowers c = ⊥ := by rw [hspec.2, h]; simp
    refine hc1 (Subgroup.mem_bot.mp ?_)
    rw [← hz]; exact Subgroup.mem_zpowers c
  · exact h

/-- **The canonical generator of `⟨c⟩` is `c` itself, for `c ≠ 1`**: if `g` generates `⟨c⟩` then
`c ∈ ⟨g⟩ = {1, g}`, so `c = 1` or `c = g`. -/
theorem choose_zpowers_eq (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    {c : Ω ≃ₐ[k] Ω}
    (h : ∃ c' : Ω ≃ₐ[k] Ω, c' ^ 2 = 1 ∧ Subgroup.zpowers c = Subgroup.zpowers c')
    (hc1 : c ≠ 1) : Classical.choose h = c := by
  have hspec := Classical.choose_spec h
  have hmem : c ∈ Subgroup.zpowers (Classical.choose h) := by
    rw [← hspec.2]; exact Subgroup.mem_zpowers c
  rcases eq_one_or_eq_of_mem_zpowers k Ω (Classical.choose h) hspec.1 hmem with h1 | h1
  · exact absurd h1 hc1
  · exact h1.symm

end GenInv

section CongrArg

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
  (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
  (χ : G1pOwn.ChiK p k Ω K T)
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]

/-- **Substitution of the involution into `PT.archPairLocal`**: an *equality* `g = c` may be
substituted (together with an equality of the two seam embeddings), because all the other differing
arguments are proofs of `Prop`s.  `subst` is used, since only it can replace `g` inside the *types*
of the proof arguments `hg2`, `hg1`, `hgφ`. -/
theorem archPairLocal_congr_arg {g c : Ω ≃ₐ[k] Ω} (hg : g = c) {φg φ : Ω →+* ℂ} (hφg : φg = φ)
    (hg2 : g ^ 2 = 1) (hc2 : c ^ 2 = 1) (hg1 : g ≠ 1) (hc1 : c ≠ 1)
    (hgφ : ∀ x : Ω, φg (g x) = starRingEnd ℂ (φg x))
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → VFcoef p M T) :
    archPairLocal p k Ω K ζ hζ hζK T hT χ M g hg2 hg1 φg hgφ a b
      = archPairLocal p k Ω K ζ hζ hζK T hT χ M c hc2 hc1 φ hφ a b := by
  subst hg
  subst hφg
  congr 1 <;> exact Subsingleton.elim _ _

end CongrArg

section ArchFamily

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
  (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
  (χ : G1pOwn.ChiK p k Ω K T)
  (φc : (c : Ω ≃ₐ[k] Ω) → c ^ 2 = 1 → c ≠ 1 → Ω →+* ℂ)
  (hφc : ∀ (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (x : Ω),
    φc c hc2 hc1 (c x) = starRingEnd ℂ (φc c hc2 hc1 x))

/-- The seam embedding of an involution only depends on the involution (its auxiliary arguments are
proofs). -/
theorem phiSeam_congr {g c : Ω ≃ₐ[k] Ω} (hg : g = c) (hg2 : g ^ 2 = 1) (hc2 : c ^ 2 = 1)
    (hg1 : g ≠ 1) (hc1 : c ≠ 1) : φc g hg2 hg1 = φc c hc2 hc1 := by
  subst hg
  congr 1 <;> exact Subsingleton.elim _ _

/-- **The involution half of the hub's glued family**: at a subgroup generated by an involution `c`
it is `PT.archPairLocal` at the canonical generator, and it is `0` off the involution groups and on
`⊥` (see `PT/PING_s18_arch_zero_at_bot.md`). -/
noncomputable def archFamily
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → VFcoef p M T) : ZMod p := by
  classical
  exact
    if h : ∃ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 ∧ H = Subgroup.zpowers c then
      if hc1 : Classical.choose h ≠ 1 then
        archPairLocal p k Ω K ζ hζ hζK T hT χ M (Classical.choose h)
          (Classical.choose_spec h).1 hc1
          (φc (Classical.choose h) (Classical.choose_spec h).1 hc1)
          (hφc (Classical.choose h) (Classical.choose_spec h).1 hc1) a b
      else 0
    else 0

/-- **The value of the family at a nontrivial involution group** is `PT.archPairLocal`. -/
theorem archFamily_zpowers
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → VFcoef p M T) :
    archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M (Subgroup.zpowers c) a b
      = archPairLocal p k Ω K ζ hζ hζK T hT χ M c hc2 hc1 (φc c hc2 hc1) (hφc c hc2 hc1)
          a b := by
  have hp : ∃ c' : Ω ≃ₐ[k] Ω, c' ^ 2 = 1 ∧ Subgroup.zpowers c = Subgroup.zpowers c' :=
    ⟨c, hc2, rfl⟩
  simp only [archFamily]
  rw [dif_pos hp]
  by_cases h2 : Classical.choose hp ≠ 1
  · rw [dif_pos h2]
    exact archPairLocal_congr_arg p k Ω K ζ hζ hζK T hT χ M
      (g := Classical.choose hp) (c := c) (choose_zpowers_eq k Ω hp hc1)
      (phiSeam_congr k Ω φc (choose_zpowers_eq k Ω hp hc1) (Classical.choose_spec hp).1 hc2
        h2 hc1)
      (Classical.choose_spec hp).1 hc2 h2 hc1
      (hφc (Classical.choose hp) (Classical.choose_spec hp).1 h2)
      (hφc c hc2 hc1) a b
  · rw [dif_neg h2]
    exfalso
    have h2' : Classical.choose hp = 1 := not_not.mp h2
    have hz : Subgroup.zpowers c = ⊥ := by rw [(Classical.choose_spec hp).2, h2']; simp
    exact hc1 (Subgroup.mem_bot.mp (by rw [← hz]; exact Subgroup.mem_zpowers c))

/-- **The family vanishes at `⊥`**: no *nontrivial* involution generates the trivial group, and the
trivial involution is excluded by the `c ≠ 1` test.  This is what makes clause (7) consistent when
`C'` contains `1` (`PT/PING_s18_arch_zero_at_bot.md`). -/
theorem archFamily_bot
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → VFcoef p M T) :
    archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M ⊥ a b = 0 := by
  simp only [archFamily]
  by_cases h1 : ∃ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 ∧ (⊥ : Subgroup (Ω ≃ₐ[k] Ω)) = Subgroup.zpowers c
  · rw [dif_pos h1]
    by_cases h2 : Classical.choose h1 ≠ 1
    · rw [dif_pos h2]
      exfalso
      have hmem : Subgroup.zpowers (Classical.choose h1) = ⊥ :=
        (Classical.choose_spec h1).2.symm
      exact h2 (Subgroup.zpowers_eq_bot.mp hmem)
    · rw [dif_neg h2]
  · rw [dif_neg h1]

end ArchFamily

end Work.SSGRoute.PT
