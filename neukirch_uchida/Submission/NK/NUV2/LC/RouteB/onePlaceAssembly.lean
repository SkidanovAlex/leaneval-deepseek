import Mathlib
import Submission.NK.NUV2.LC.RouteB.hasseSurjTopDefs
import Submission.NK.NUV2.LC.h2ProfiniteAddGroup
import Submission.NK.NUV2.LC.RouteB.natCard_LocalH2_top
import Submission.NK.NUV2.LC.RouteB.open_two_place

/-!
# The `⊤`-case of the Hasse surjectivity from the isolated one-place classes

`NK.NUV2.LC.RouteB.HasseSurjTop p` (NSW (9.2.1) over a number field, `hasseSurjTopDefs.lean`) is
proved here from a *single* arithmetic input, isolated as the `Prop` `OnePlaceClasses`:

> for pairwise non-conjugate places `A i` of `F'` over finite primes of `F` there are global classes
> `a i ∈ H²(Gal(F'/F), Z/p)` with `loc (a i) (A i) ≠ 0` and `loc (a i) (A j) = 0` for `j ≠ i`.

The step from that input to `HasseSurjTop p` is pure `ZMod p`-linear algebra of the local groups,
all of which is on disk:

* the localisation is additive (`NK.NUV2.LC.H2Profinite.loc_add`) and `ZMod p`-linear
  (`NK.NUV2.LC.RouteB.H2Profinite.loc_smul`), the local group `LocalH2 p ⊤ A` has exactly `p`
  elements (`NK.NUV2.LC.RouteB.natCard_LocalH2_top`), and in a `ZMod p`-module of cardinality `p`
  every element is a scalar multiple of every non-zero element
  (`NK.NUV2.LC.RouteB.exists_smul_eq_of_card_eq_prime'`);
* hence `y i = c i • loc (a i) (A i)` and `x := Σ i c i • a i` has the required localisations.

The two representations of the one-place classes on disk are
`NK.NUV2.LC.RouteB.onePlaceClasses` and (independently)
`NK.NUV2.LC.RouteB.onePlaceClassesKummer`; either is a term of `OnePlaceClasses` (the binders
agree definitionally), so this file closes the `⊤`-case without committing to a proof route.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Pointwise

namespace NK.NUV2.LC.RouteB

open NK.BrauerHasse

set_option linter.unusedVariables false in
/-- **The isolated arithmetic crux** (hypothesis form): one-place global classes at a finite family
of pairwise non-conjugate places.  This is the statement that a prescribed local class at one place
can be realised by a global class vanishing at the other places of the family; it is the exact shape
of `NK.NUV2.LC.RouteB.onePlaceClasses` (and of its independent variant
`NK.NUV2.LC.RouteB.onePlaceClassesKummer`), written out so that a proof of either can be passed
directly as the argument of `hasseSurjTop_of_onePlaceClasses`. -/
abbrev OnePlaceClassesHyp : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2)
    {F F' : Type} [Field F] [NumberField F] [Field F'] [Algebra F F'] [IsSepClosure F F']
    (ζ : F) (hζ : IsPrimitiveRoot ζ p)
    (ι : Type) [Fintype ι]
    (A : ι → NK.BrauerHasse.OverFinitePrime F F')
    (hnot : ∀ i j : ι, i ≠ j → ¬ InOrbit (K := F) (K' := F') ⊤ (A i).1 (A j).1),
    ∃ a : ι → NK.BrauerHasse.H2Profinite (K := F) (K' := F') p ⊤,
      (∀ i : ι, NK.BrauerHasse.H2Profinite.loc p ⊤ (a i) (A i) ≠ 0) ∧
      (∀ i j : ι, i ≠ j → NK.BrauerHasse.H2Profinite.loc p ⊤ (a i) (A j) = 0)

/-- **The `⊤`-case of the classical Hasse surjectivity from the one-place classes.**

See the module docstring: the one-place classes generate the local groups, and the localisation is
linear, so every prescribed tuple of local classes is the localisation of a global class. -/
theorem hasseSurjTop_of_onePlaceClasses (h : OnePlaceClassesHyp) (p : ℕ) : HasseSurjTop p := by
  rintro hp hodd F F' _ _ _ _ _ ζ hζ hζF ι _ A hnot y
  obtain ⟨ζ₀, hζ₀⟩ := hζF
  have hζ₀' : IsPrimitiveRoot ζ₀ p := by
    have h' : IsPrimitiveRoot (algebraMap F F' ζ₀) p := by rw [hζ₀]; exact hζ
    exact h'.of_map_of_injective (algebraMap F F').injective
  obtain ⟨a, ha_ne, ha_zero⟩ := h p hp hodd ζ₀ hζ₀' ι A hnot
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hgen : ∀ i : ι, ∃ c : ZMod p,
      c • (H2Profinite.loc (K := F) (K' := F') p ⊤ (a i) (A i)) = y i :=
    fun i => exists_smul_eq_of_card_eq_prime' p
      (natCard_LocalH2_top p hp hodd F' ζ₀ hζ₀' (A i)) (ha_ne i) (y i)
  choose c hc using hgen
  refine ⟨∑ i, c i • a i, ?_⟩
  funext j
  show H2Profinite.loc (K := F) (K' := F') p ⊤ (∑ i, c i • a i) (A j) = y j
  have hsum : H2Profinite.loc (K := F) (K' := F') p ⊤ (∑ i, c i • a i) (A j)
      = ∑ i, c i • (H2Profinite.loc (K := F) (K' := F') p ⊤ (a i) (A j)) := by
    have hmap := map_sum (locAddHom' (K := F) (K' := F') p ⊤ (A j))
      (fun i => c i • a i) Finset.univ
    have h2 : (∑ i, (locAddHom' (K := F) (K' := F') p ⊤ (A j)) (c i • a i))
        = ∑ i, c i • H2Profinite.loc (K := F) (K' := F') p ⊤ (a i) (A j) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have hdef : (locAddHom' (K := F) (K' := F') p ⊤ (A j)) (c i • a i)
          = H2Profinite.loc (K := F) (K' := F') p ⊤ (c i • a i) (A j) := rfl
      rw [hdef]
      exact H2Profinite.loc_smul (K := F) (K' := F') p ⊤ (A j) (c i) (a i)
    exact hmap.trans h2
  rw [hsum, Finset.sum_eq_single j]
  · exact hc j
  · intro i _ hij
    rw [ha_zero i j hij, smul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

end NK.NUV2.LC.RouteB
