import Mathlib
import Submission.Work.ProPDeficiency.Basic

/-!
# `dGens` versus `dim H¹(G, 𝔽_p)`

**Namespace** `Work.ProPDeficiency`; module `Submission.Work.ProPDeficiency.HomRank`.

For a finitely generated group `G` whose finite quotients are all `p`-groups, the minimal number of
generators equals the `𝔽_p`-dimension of `Hom(G, 𝔽_p)` (the `d = dim H¹` identity of the arithmetic
side), and the arithmetic only ever needs the *inequality* `dim H¹ ≤ dGens` for the lower bound on
the number `d` of generators of a presentation.

`𝔽_p` is written additively: the group of homomorphisms is `G →* Multiplicative (ZMod p)`, so that
the pointwise group structure is multiplicative.  Its `𝔽_p`-dimension is recorded as `Nat.log p` of
its cardinality, which is what `dim H¹` means for the finite `𝔽_p`-vector space `H¹(G, 𝔽_p)`.

## Main definitions

* `HomFp p G := G →* Multiplicative (ZMod p)`;
* `pHomDim p G := Nat.log p (Nat.card (HomFp p G))`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.ProPDeficiency

/-- `HomFp p G` : the group of homomorphisms from `G` to the additive group `𝔽_p = ZMod p`, written
multiplicatively.  This is `H¹(G, 𝔽_p)` in the discrete setting. -/
abbrev HomFp (p : ℕ) (G : Type*) [Group G] := G →* Multiplicative (ZMod p)

/-- The `𝔽_p`-dimension of `Hom(G, 𝔽_p)`, expressed as `Nat.log p` of its cardinality.  For a
finitely generated group the hom set is a finite `𝔽_p`-vector space, so this is its dimension;
`Nat.card` is `0` for infinite types, so this is `0` for groups whose hom set is infinite. -/
noncomputable def pHomDim (p : ℕ) (G : Type*) [Group G] : ℕ :=
  Nat.log p (Nat.card (HomFp p G))

theorem natCard_multiplicative_zmod {p : ℕ} [NeZero p] :
    Nat.card (Multiplicative (ZMod p)) = p := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

theorem pHomDim_eq_zero_of_infinite (p : ℕ) (G : Type*) [Group G] [Infinite (HomFp p G)] :
    pHomDim p G = 0 := by
  rw [pHomDim, Nat.card_eq_zero_of_infinite, Nat.log_zero_right]

/-- Homomorphisms to `𝔽_p` are determined by their values on a set whose closure is `⊤`. -/
theorem HomFp.ext_of_closure_eq_top {p : ℕ} {G : Type*} [Group G] {S : Set G}
    (hS : Subgroup.closure S = ⊤) {φ ψ : HomFp p G} (h : ∀ s ∈ S, φ s = ψ s) : φ = ψ := by
  let E : Subgroup G :=
    { carrier := {g : G | φ g = ψ g}
      one_mem' := by simp
      mul_mem' := by intro a b ha hb; show φ (a * b) = ψ (a * b); rw [map_mul, map_mul, ha, hb]
      inv_mem' := by intro a ha; show φ a⁻¹ = ψ a⁻¹; rw [map_inv, map_inv, ha] }
  have hle : (⊤ : Subgroup G) ≤ E := by
    rw [← hS]
    exact (Subgroup.closure_le (K := E)).mpr h
  ext g
  exact hle (Subgroup.mem_top g)

/-- For a finitely generated group, `Hom(G, 𝔽_p)` is finite (a hom is determined by its values on a
finite generating set). -/
theorem finite_homFp {p : ℕ} (hp : p ≠ 0) {G : Type*} [Group G] [Group.FG G] :
    Finite (HomFp p G) := by
  classical
  haveI : NeZero p := ⟨hp⟩
  obtain ⟨S, hSmin, -⟩ := exists_minimalGeneratingSet (G := G) (inferInstance : Group.FG G)
  refine Finite.of_injective (fun φ : HomFp p G => fun s : S => φ s) ?_
  intro φ ψ h
  refine HomFp.ext_of_closure_eq_top hSmin.1 ?_
  intro s hs
  exact congrFun h ⟨s, hs⟩

/-- `dim H¹(-, 𝔽_p)` does not increase under a surjective homomorphism. -/
theorem pHomDim_le_of_surjective {p : ℕ} (hp : p ≠ 0) {G H : Type*} [Group G] [Group H]
    [Group.FG G] (f : G →* H) (hf : Function.Surjective f) : pHomDim p H ≤ pHomDim p G := by
  haveI := finite_homFp hp (G := G)
  have hinj : Function.Injective fun φ : HomFp p H => φ.comp f := by
    intro φ ψ h
    refine HomFp.ext_of_closure_eq_top (S := Set.univ) (by simp) fun y _ => ?_
    obtain ⟨x, rfl⟩ := hf y
    exact DFunLike.congr_fun h x
  have hcard : Nat.card (HomFp p H) ≤ Nat.card (HomFp p G) :=
    Nat.card_le_card_of_injective _ hinj
  rw [pHomDim]
  exact Nat.log_mono_right hcard

end Work.ProPDeficiency
