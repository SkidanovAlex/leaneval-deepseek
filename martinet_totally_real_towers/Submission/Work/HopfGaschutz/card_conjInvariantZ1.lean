import Mathlib
import Submission.Work.HopfGaschutz.Setup
import Submission.Work.HopfGaschutz.Defs
import Submission.Work.HopfGaschutz.isConjInvariant_iff_le_ker
import Submission.Work.HopfGaschutz.finite_quotient_relFrattiniIn
import Submission.Work.HopfGaschutz.finite_and_natCard_le_pow_of_comm_exp_p

/-!
# `Work.HopfGaschutz.card_conjInvariantZ1`

**Namespace** `Work.HopfGaschutz`; module `Submission.Work.HopfGaschutz.card_conjInvariantZ1`.

The *cohomological* half of the relation-rank dictionary of `Defs.lean`/`Setup.lean`: for a
generating family `gen : α → Q` of a finite group `Q` (`α` finite), the conjugation invariant
`1`-cocycles on the relation kernel `K = presKernel gen ⊆ FreeGroup α` are in bijection with the
`𝔽₂`-dual of the relation-Frattini quotient `K ⧸ K²[K,F]`.  Since a finite elementary abelian
`2`-group has as many homomorphisms to `𝔽₂` as it has elements, the two sides have the same
(finite) cardinality:

  `Nat.card {φ : Z¹(K,𝔽₂) // IsConjInvariant gen φ} = Nat.card (K ⧸ relFrattiniIn 2 K)`.

## Route

* `z1EquivMonoidHom` : for the *trivial* action of `K` on `𝔽₂`, a `1`-cocycle is exactly an
  additive homomorphism, i.e. a group homomorphism `K →* Multiplicative (ZMod 2)`
  (the map is the identity on underlying functions) -- `isCocycle1_iff_of_trivial`;
* `isConjInvariant_iff_le_ker` (in the module of that name) : conjugation invariance of such an
  `f` under the action of `F = FreeGroup α` is *exactly* the vanishing of `f` on the
  relation-Frattini subgroup `K²[K,F]`;
* `quotientEquiv` : homomorphisms `K →* M` vanishing on a normal `N ⊴ K` are the homomorphisms
  `K ⧸ N →* M`;
* `natCard_hom_zmodTwo_multiplicative` : a finite group of exponent `2` has as many homomorphisms
  to `𝔽₂` as it has elements (duality of finite `𝔽₂`-vector spaces), via
  `AddMonoidHom.toZModLinearMapEquiv` and `Subspace.dual_finrank_eq`;
* finiteness of `K ⧸ K²[K,F]` is `finite_quotient_relFrattiniIn_of_finiteIndex`: the generating
  family makes `FreeGroup.lift gen` surjective, so `K` has finite index in the finitely generated
  free group `F`, hence is finitely generated (Schreier's lemma), and a finitely generated group
  of exponent `2` is finite (Schur's bound).

Note the hypothesis is that `gen` **generates** `Q` (the closure of its range is `⊤`), not that it
is surjective: for a finite `Q` and a minimal generating family of `d` elements, `gen` is never
surjective as soon as `d < |Q|`, which is the case relevant to the chapter.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.HopfGaschutz

open Work.ConCohomology

open scoped commutatorElement

/-! ## The coefficient group `𝔽₂` has exponent `2` -/

/-- Every element of `Multiplicative (ZMod 2)` is its own inverse (the group has exponent `2`). -/
lemma mul_self_eq_one_multiplicative_zmodTwo : ∀ y : Multiplicative (ZMod 2), y * y = 1 := by
  decide

/-! ## `1`-cocycles with trivial coefficients are homomorphisms -/

section Z1Equiv

variable {α : Type*} [TopologicalSpace (FreeGroup α)] [DiscreteTopology (FreeGroup α)]
variable {Q : Type*} [Group Q]

/-- For a `1`-cochain on `K` with trivial coefficients the cocycle condition is additivity. -/
lemma z1_map_mul (gen : α → Q) (z : Z1 ↥(presKernel gen) (ZMod 2))
    (a b : ↥(presKernel gen)) :
    (z.1 : ↥(presKernel gen) → ZMod 2) (a * b)
      = (z.1 : ↥(presKernel gen) → ZMod 2) a + (z.1 : ↥(presKernel gen) → ZMod 2) b :=
  (isCocycle1_iff_of_trivial (fun (_ : ↥(presKernel gen)) (_ : ZMod 2) => rfl)
    (z.1 : ↥(presKernel gen) → ZMod 2)).mp (mem_Z1.mp z.2) a b

/-- A `1`-cocycle on `K` with trivial coefficients sends `1` to `0`. -/
lemma z1_map_one (gen : α → Q) (z : Z1 ↥(presKernel gen) (ZMod 2)) :
    (z.1 : ↥(presKernel gen) → ZMod 2) 1 = 0 := by
  have h := z1_map_mul gen z 1 1
  rw [one_mul] at h
  have h2 : (z.1 : ↥(presKernel gen) → ZMod 2) 1 + (z.1 : ↥(presKernel gen) → ZMod 2) 1
      = (z.1 : ↥(presKernel gen) → ZMod 2) 1 + 0 := by rw [add_zero, ← h]
  exact add_left_cancel h2

/-- **For trivial coefficients, `1`-cocycles are homomorphisms**: the map
`Z¹(K,𝔽₂) ≃ (K →* Multiplicative (ZMod 2))` which is the identity on underlying functions. -/
noncomputable def z1EquivMonoidHom (gen : α → Q) :
    Z1 ↥(presKernel gen) (ZMod 2) ≃ (↥(presKernel gen) →* Multiplicative (ZMod 2)) where
  toFun z :=
    { toFun := fun n => (z.1 : ↥(presKernel gen) → ZMod 2) n
      map_one' := by
        show (z.1 : ↥(presKernel gen) → ZMod 2) 1 = 0
        exact z1_map_one gen z
      map_mul' := by
        intro a b
        show (z.1 : ↥(presKernel gen) → ZMod 2) (a * b)
          = (z.1 : ↥(presKernel gen) → ZMod 2) a + (z.1 : ↥(presKernel gen) → ZMod 2) b
        exact z1_map_mul gen z a b }
  invFun f :=
    ⟨⟨fun n => f n, IsLocallyConstant.of_discrete _⟩, mem_Z1.mpr (by
      rw [isCocycle1_iff_of_trivial (fun (_ : ↥(presKernel gen)) (_ : ZMod 2) => rfl)]
      intro a b
      exact f.map_mul a b)⟩
  left_inv z := by ext n; rfl
  right_inv f := by ext n; rfl

end Z1Equiv

/-! ## Homomorphisms vanishing on a normal subgroup -/

/-- Homomorphisms `G →* M` that vanish on a normal subgroup `N` are the homomorphisms
`G ⧸ N →* M` (the universal property of the quotient). -/
noncomputable def quotientEquiv {G M : Type*} [Group G] [Monoid M]
    (N : Subgroup G) [N.Normal] : {f : G →* M // N ≤ f.ker} ≃ (G ⧸ N →* M) where
  toFun f := QuotientGroup.lift N f.1 f.2
  invFun F := ⟨F.comp (QuotientGroup.mk' N), by
    intro x hx
    show F (QuotientGroup.mk' N x) = 1
    rw [show QuotientGroup.mk' N x = 1 from (QuotientGroup.eq_one_iff x).mpr hx, map_one]⟩
  left_inv f := by
    refine Subtype.ext ?_
    ext x
    exact QuotientGroup.lift_mk' N f.2 x
  right_inv F := by
    refine MonoidHom.ext (fun x => ?_)
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    exact QuotientGroup.lift_mk' N _ g

/-! ## `𝔽₂`-duality for finite groups of exponent `2` -/

/-- The identity on underlying functions, as an equivalence between group homomorphisms
`V →* Multiplicative (ZMod 2)` and additive homomorphisms `Additive V →+ ZMod 2`. -/
def tagEquiv (V : Type*) [MulOneClass V] :
    (V →* Multiplicative (ZMod 2)) ≃ (Additive V →+ ZMod 2) where
  toFun f := { toFun := fun x => f x, map_zero' := f.map_one', map_add' := fun a b => f.map_mul a b }
  invFun g := { toFun := fun x => g x, map_one' := g.map_zero', map_mul' := fun a b => g.map_add a b }
  left_inv f := by ext x; rfl
  right_inv g := by ext x; rfl

/-- **A finite group of exponent `2` has as many homomorphisms to `𝔽₂` as it has elements.**
Both sides are `|V|` and `|V*|` for the finite dimensional `𝔽₂`-vector space `V`: the dual of a
finite dimensional vector space has the same dimension (`Subspace.dual_finrank_eq`) and the
cardinality of a finite dimensional vector space over a finite field is
`|𝔽₂| ^ finrank` (`Module.card_eq_pow_finrank`). -/
theorem natCard_hom_zmodTwo_multiplicative {V : Type*} [Group V] [IsMulCommutative V]
    [Fintype V] (h2 : ∀ v : V, v * v = 1) :
    Nat.card (V →* Multiplicative (ZMod 2)) = Nat.card V := by
  classical
  letI : CommGroup V := { ‹Group V› with mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
  letI : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule (n := 2) (by
    intro x
    rw [two_nsmul]
    exact h2 (Additive.toMul x))
  have hdual : Nat.card (Module.Dual (ZMod 2) (Additive V)) = Nat.card (Additive V) := by
    haveI : Finite (Module.Dual (ZMod 2) (Additive V)) :=
      Finite.of_injective (fun f : Module.Dual (ZMod 2) (Additive V) => (f : Additive V → ZMod 2))
        (fun f g h => by ext x; exact congrFun h x)
    haveI : Fintype (Module.Dual (ZMod 2) (Additive V)) :=
      Fintype.ofFinite (Module.Dual (ZMod 2) (Additive V))
    have hL : Nat.card (Module.Dual (ZMod 2) (Additive V))
        = Fintype.card (Module.Dual (ZMod 2) (Additive V)) := Nat.card_eq_fintype_card
    have hL2 : Fintype.card (Module.Dual (ZMod 2) (Additive V))
        = Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2)
            (Module.Dual (ZMod 2) (Additive V)) :=
      Module.card_eq_pow_finrank
    have hV : Fintype.card (Additive V)
        = Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) (Additive V) :=
      Module.card_eq_pow_finrank
    have hV2 : Nat.card (Additive V) = Fintype.card (Additive V) := Nat.card_eq_fintype_card
    rw [hL, hL2, Subspace.dual_finrank_eq, ← hV, hV2]
  have h3 : Nat.card (V →* Multiplicative (ZMod 2)) = Nat.card (Additive V →+ ZMod 2) :=
    Nat.card_congr (tagEquiv V)
  have h4 : Nat.card (Additive V →+ ZMod 2) = Nat.card (Module.Dual (ZMod 2) (Additive V)) :=
    Nat.card_congr (AddMonoidHom.toZModLinearMapEquiv 2).toEquiv
  exact h3.trans (h4.trans (hdual.trans (Nat.card_congr Additive.ofMul)))

/-! ## The relation-Frattini quotient is an elementary abelian `2`-group -/

/-- The quotient `K ⧸ K²[K,F]` of the relation kernel is commutative: it is a quotient of `K` by
a subgroup containing `[K,K] ≤ [K,F] ≤ K²[K,F]`. -/
lemma isMulCommutative_quotient {α : Type*} {Q : Type*} [Group Q] (gen : α → Q) :
    IsMulCommutative (↥(presKernel gen) ⧸ relFrattiniIn 2 (presKernel gen)) := by
  refine (Subgroup.Normal.quotient_commutative_iff_commutator_le
    (N := relFrattiniIn 2 (presKernel gen))).mpr ?_
  change ⁅(⊤ : Subgroup ↥(presKernel gen)), ⊤⁆ ≤ relFrattiniIn 2 (presKernel gen)
  rw [Subgroup.commutator_le]
  intro a _ b _
  show ((Subgroup.subtype (presKernel gen)) ⁅a, b⁆) ∈ relFrattini 2 (presKernel gen)
  rw [map_commutatorElement]
  exact Subgroup.mem_sup_right ((Subgroup.commutator_mono le_rfl le_top)
    (Subgroup.commutator_mem_commutator a.2 b.2))

/-- The quotient `K ⧸ K²[K,F]` has exponent `2` (the image of `x² ∈ K²` is trivial). -/
lemma mul_self_eq_one_quotient {α : Type*} {Q : Type*} [Group Q] (gen : α → Q)
    (v : ↥(presKernel gen) ⧸ relFrattiniIn 2 (presKernel gen)) : v * v = 1 := by
  induction v using QuotientGroup.induction_on with
  | _ x =>
    show QuotientGroup.mk' (relFrattiniIn 2 (presKernel gen)) (x * x) = 1
    refine (QuotientGroup.eq_one_iff (x * x)).mpr ?_
    show ((x * x : ↥(presKernel gen)) : FreeGroup α) ∈ relFrattini 2 (presKernel gen)
    rw [Subgroup.coe_mul]
    exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨(x : FreeGroup α), x.2, by rw [pow_two]⟩)

/-! ## The main theorem -/

theorem card_conjInvariantZ1 {α Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [TopologicalSpace (FreeGroup α)] [DiscreteTopology (FreeGroup α)] [Fintype α] [Fintype Q]
    (gen : α → Q) (hgen : Subgroup.closure (Set.range gen) = ⊤) :
    Nat.card {φ : Work.ConCohomology.Z1 ↥(Work.HopfGaschutz.presKernel gen) (ZMod 2) //
        Work.HopfGaschutz.IsConjInvariant gen φ}
      = Nat.card (↥(Work.HopfGaschutz.presKernel gen) ⧸
          Work.HopfGaschutz.relFrattiniIn 2 (Work.HopfGaschutz.presKernel gen)) := by
  classical
  -- `gen` generates, so `FreeGroup.lift gen` is surjective and `K` has finite index in `F`.
  have hsurj : Function.Surjective (FreeGroup.lift gen) :=
    (FreeGroup.lift_surjective_iff_closure_range_eq_top).mpr hgen
  haveI hquot : Finite (FreeGroup α ⧸ presKernel gen) :=
    Finite.of_equiv Q (QuotientGroup.quotientKerEquivOfSurjective (FreeGroup.lift gen)
      hsurj).symm.toEquiv
  haveI hfi : (presKernel gen).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  -- hence the relation-Frattini quotient of `K` is finite
  haveI hfin : Finite (↥(presKernel gen) ⧸ relFrattiniIn 2 (presKernel gen)) :=
    finite_quotient_relFrattiniIn_of_finiteIndex (presKernel gen)
  haveI hft : Fintype (↥(presKernel gen) ⧸ relFrattiniIn 2 (presKernel gen)) := Fintype.ofFinite _
  haveI hcomm : IsMulCommutative (↥(presKernel gen) ⧸ relFrattiniIn 2 (presKernel gen)) :=
    isMulCommutative_quotient gen
  -- invariant cocycles are the homomorphisms out of `K ⧸ K²[K,F]`
  have he : {φ : Z1 ↥(presKernel gen) (ZMod 2) // IsConjInvariant gen φ} ≃
      (↥(presKernel gen) ⧸ relFrattiniIn 2 (presKernel gen) →* Multiplicative (ZMod 2)) :=
    (Equiv.subtypeEquiv (z1EquivMonoidHom gen)
      (fun φ => isConjInvariant_iff_le_ker gen (z1EquivMonoidHom gen φ))).trans
      (quotientEquiv (relFrattiniIn 2 (presKernel gen)))
  rw [Nat.card_congr he]
  exact natCard_hom_zmodTwo_multiplicative (fun v => mul_self_eq_one_quotient gen v)

end Work.HopfGaschutz
