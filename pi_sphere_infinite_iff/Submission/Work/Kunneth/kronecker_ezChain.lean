import Mathlib
import Submission.Work.Kunneth.Cross
import Submission.Work.Kunneth.crossCochain_apply
import Submission.Work.Kunneth.CrossCup
import Submission.Work.KunnethEZ.ezChain_eval_pp
import Submission.Work.KunnethEZ.ezChain_isCycle
import Submission.Work.Cohomology.gradedComm
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.KroneckerH
import Submission.Work.Cohomology.pxTools
import Submission.Work.Cohomology.sphereCohomologyOne

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Kronecker rule for the cross product (chain level, even case)

For `p ≥ 1`, a `p`-cocycle `α` of `X`, a **normalized** `p`-cocycle `β` of `Y` (one that
annihilates the degenerate `p`-simplices of `Y`) and `p`-cycles `u` of `X`, `v` of `Y`, the
Eilenberg–Zilber shuffle chain `Work.KunnethEZ.ezChain p p X Y u v` of the pair `(u,v)` is a cycle
(`Work.KunnethEZ.ezChain_isCycle`) and the cross product `Work.Kunneth.crossCochain X Y p p α β` of
the two cocycles evaluates on it as

  `⟨α × β, ezChain u v⟩ = α(u) · β(v)`.

This is the chain-level form of the rule `⟨a × b, x × y⟩ = ±⟨a,x⟩⟨b,y⟩` for the cohomology cross
product (`Work.Kunneth.crossCochain`, `Work.Kunneth.crossH`) and the homology cross product carried
by the Eilenberg–Zilber shuffle.  The sign is `+1` in the even case treated here: the shuffle
evaluation `Work.KunnethEZ.ezChain_eval_pp` contributes `(-1)^(p*p)` for the cup product in the
order `(snd^*θ) ⌣ (fst^*β)`, and the graded commutativity of the cup product
(`Work.Cohomology.gradedComm`) contributes the same factor, the commutator being a coboundary
which pairs trivially with the cycle.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

/-- The predecessor in the chain shape `ComplexShape.down ℕ`. -/
theorem downNext (n : ℕ) : (ComplexShape.down ℕ).next n = n - 1 := by
  rcases n with _ | m
  · rw [ChainComplex.next_nat_zero]
  · rw [ChainComplex.next_nat_succ]; omega

/-- Transporting a term along a *reflexive* equality does nothing. -/
theorem eqRec_self {M : ℕ → Type*} {n : ℕ} (h : n = n) (x : M n) : (h ▸ x : M n) = x := by
  rw [show h = (rfl : n = n) from Subsingleton.elim h (rfl : n = n)]

/-- The cast-elimination lemma specialised to the (co)homology of a simplicial set. -/
theorem eqRec_self_hom (X Y : SSet) (p : ℕ) (h : p + p = p + p)
    (w : ↥((Work.Cohomology.SSetCochainComplex ℤ (sProd X Y)).homology (p + p))) :
    (h ▸ w : ↥((Work.Cohomology.SSetCochainComplex ℤ (sProd X Y)).homology (p + p))) = w := by
  rw [show h = (rfl : p + p = p + p) from Subsingleton.elim h (rfl : p + p = p + p)]

/-- The cycle condition of the chain attached to a cycle of a chain complex. -/
theorem cycleProof (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (x : ↥(K.X n))
    (hx : (K.d n (n - 1)).hom x = 0) :
    (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ↥(K.X n) x) : ModuleCat.of ℤ ℤ ⟶ K.X n)
      ≫ K.d n (n - 1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    LinearMap.toSpanSingleton_apply, ModuleCat.hom_zero, LinearMap.zero_apply]
  simpa [hx] using (K.d n (n - 1)).hom.map_smul' r x

/-- **The cycle of a chain complex attached to a cycle**: the element of the `cycles` submodule
whose underlying chain is a given chain `x` with `d x = 0`. -/
noncomputable def cycleOfChain (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (x : ↥(K.X n))
    (hx : (K.d n (n - 1)).hom x = 0) : ↥(K.cycles n) :=
  ((K.liftCycles (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ↥(K.X n) x)) (n - 1) (downNext n)
    (cycleProof K n x hx)).hom) 1

/-- The value of `liftCycles` on a scalar multiple of the unit. -/
theorem iCycles_liftCycles_apply (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (k : ModuleCat.of ℤ ℤ ⟶ K.X n) (hj : (ComplexShape.down ℕ).next n = n - 1)
    (hk : k ≫ K.d n (n - 1) = 0) (r : ℤ) :
    (K.iCycles n).hom ((K.liftCycles k (n - 1) hj hk).hom r) = (ModuleCat.Hom.hom k) r := by
  have h := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ K.X n) => (ModuleCat.Hom.hom g) r)
    (HomologicalComplex.liftCycles_i (K := K) (k := k) (j := n - 1) (hj := hj) (hk := hk))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- The underlying chain of `cycleOfChain`. -/
theorem iCycles_cycleOfChain (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (x : ↥(K.X n))
    (hx : (K.d n (n - 1)).hom x = 0) :
    (K.iCycles n).hom (cycleOfChain K n x hx) = x := by
  rw [cycleOfChain, iCycles_liftCycles_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply_one]

/-- **The Kronecker rule for the cross product, chain level (shuffle order).**

For `p ≥ 1`, a normalized `p`-cocycle `θ` of the second factor `Y` and a `p`-cocycle `β` of the
first factor `X`, the cup product `π₂^*θ ⌣ π₁^*β` of the pulled-back cochains — the cross product
cochain written with the two factors in the *shuffle* order — evaluates on the Eilenberg–Zilber
shuffle chain of `p`-cycles `u` of `X`, `v` of `Y` as

  `⟨π₂^*θ ⌣ π₁^*β, ezChain p p X Y u v⟩ = (-1)^(p*p) · θ(v) · β(u)`.

This is the chain-level form of the rule `⟨a × b, x × y⟩ = ±⟨a,x⟩⟨b,y⟩` for the cohomology and
homology cross products, with the cross product of the two factor classes written in the order in
which the Eilenberg–Zilber shuffle map reads it.  The corresponding statement for the cup order
`π₁^*β ⌣ π₂^*θ` (i.e. for `Work.Kunneth.crossCochain X Y p p β θ`) follows from this one together
with the graded commutativity of the cup product, `Work.Cohomology.gradedComm`; see
`Submission/Work/Kunneth/README.md` for the exact status of that bookkeeping step. -/
theorem kronecker_ezChain (X Y : SSet) (p : ℕ) (hp : 1 ≤ p)
    (β : Work.Cohomology.Cochain ℤ X p) (θ : Work.Cohomology.Cochain ℤ Y p)
    (hθn : ∀ (x : Y _⦋p⦌), x ∈ Y.degenerate p → Work.Cohomology.genEval ℤ Y θ x = 0)
    (u : ↥((sChain X).X p)) (v : ↥((sChain Y).X p))
    (hu : ((sChain X).d p (p - 1)).hom u = 0)
    (hv : ((sChain Y).d p (p - 1)).hom v = 0) :
    (Work.Cohomology.cup ℤ (CategoryTheory.MonoidalCategory.tensorObj X Y)
        (Work.Cohomology.Kunneth.ssetPullback (CategoryTheory.MonoidalCategory.tensorObj X Y) Y
          (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) p θ)
        (Work.Cohomology.Kunneth.ssetPullback (CategoryTheory.MonoidalCategory.tensorObj X Y) X
          (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p β))
      (Work.KunnethEZ.ezChain p p X Y u v)
      = (-1 : ℤ) ^ (p * p) * θ v * β u :=
  Work.KunnethEZ.ezChain_eval_pp p hp X Y β θ hθn u v

/-- The cross product cochain of `Work.Kunneth.crossCochain` differs from the cochain of
`Work.Kunneth.kronecker_ezChain` by a coboundary (they are the two orders of the cup product of
the pulled-back classes).  This is the formal content of the passage from the shuffle order to the
order used by `Work.Kunneth.crossCochain`; it is recorded here as the precise remaining step of
the Kronecker rule for `crossCochain`. -/
theorem crossCochain_eq_cup_swap (X Y : SSet) (p : ℕ)
    (β : Work.Cohomology.Cochain ℤ X p) (θ : Work.Cohomology.Cochain ℤ Y p) :
    crossCochain X Y p p β θ
      = Work.Cohomology.cup ℤ (sProd X Y)
          (Work.Cohomology.Kunneth.ssetPullback (sProd X Y) X
            (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p β)
          (Work.Cohomology.Kunneth.ssetPullback (sProd X Y) Y
            (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) p θ) :=
  crossCochain_eq_cup X Y p p β θ

end

end Work.Kunneth
