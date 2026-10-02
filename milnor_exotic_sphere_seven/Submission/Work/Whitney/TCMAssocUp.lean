import Mathlib
import Submission.Work.Whitney.TCMProdDefs
import Submission.Work.Whitney.tcmModelMul
import Submission.Work.Whitney.tcmPhiAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The block identities of the two coordinate worlds, upstream of `tcmCup_step`

This module is a copy of `Submission/Work/Whitney/tcmCast.lean` and
`Submission/Work/Whitney/tcmProj.lean` (and of the two lemmas of
`Submission/Work/Whitney/tcmOuter1_comp_castMap.lean`) with the import of
`Submission.Work.Whitney.tcmCup_step` replaced by `Submission.Work.Whitney.TCMProdDefs` (where the
definitions live) and with all declarations placed in the sub-namespace `Work.Whitney.TCMAssocUp`,
so that they can be used by modules that `tcmCup_step.lean` may import (the originals import
`tcmCup_step`, so they are unreachable from it).

The content is the coordinate description of `tcmPr1/2 ∘ Fib.tcmF_inv`, the transport `castMap`
along an equality of fibre degrees, the three block identities
`tcmProjKA.comp (castMap B (Nat.add_assoc m n r).symm) = tcmProjKB`, and the `relCohMap`-absorptions
`tcmRelCohMap_absorb2/3`.

Do not edit the originals; edit this copy (or its consumers) if the block identities have to change.
-/

open Work.Cohomology
open Work.Thom
open CategoryTheory

namespace Work.Whitney.TCMAssocUp

noncomputable section


-- ===== copied from Submission/Work/Whitney/tcmCast.lean =====

/-!
# The transport of a relative cohomology class along an equality of fibre degrees

`castMap B h` is the canonical identification `B × ℝ^a → B × ℝ^b` of the two coordinate worlds
induced by `h : a = b`, defined as the transport of the identity.  Being a transport, it is opaque,
but `castMap_apply`, `cast_apply_coe` and `cast_RelCoh_eq` make it computable, and
`eqRec_cast_symm_cast` flips a cast against its inverse (with the motive `P` passed explicitly —
without that the elaborator leaves the class argument as a metavariable under
`backward.isDefEq.respectTransparency false`).

This module sits *below* `tcmProd_assoc` and its companions, which all import it: the transport layer
has to be available to everything that consumes it.  Moved here verbatim from `tcmProd_assoc.lean`.
-/

open Work.Cohomology
open Work.Thom
open CategoryTheory

-- (namespace Work.Whitney opened by the enclosing namespace)

noncomputable section

/-! ## Transport of a class along an equality of the fibre degree

The target of this file compares a class living in `B × ℝ^{(m+n)+r}` with one living in
`B × ℝ^{m+(n+r)}`; the cast `Nat.add_assoc m n r` is a cast of the whole type family
`k ↦ RelCoh ℤ k (B × ℝ^k) (Punct B k)` (degree, ambient space and closed set at once).  The lemmas
below reduce such a cast to a `relCohMap`-pullback along the canonical identification
`castMap h := h ▸ ContinuousMap.id` of the two coordinate worlds (the transported identity), so that
the pullback can be computed with the usual `relCohMap`-toolkit.

Both statements are for a *variable* `h : a = b`, so that the proof can be `cases h` — this is the
only way to handle such a cast: `cases Nat.add_assoc m n r` fails by dependent elimination on the
concrete indices (the same obstruction as for `subst`). -/

/-- The canonical identification `B × ℝ^a → B × ℝ^b` of the two coordinate worlds: the transport of
the identity along `h : a = b`. -/
noncomputable def castMap (B : Type) [TopologicalSpace B] {a b : ℕ} (h : a = b) :
    C(B × EuclideanSpace ℝ (Fin a), B × EuclideanSpace ℝ (Fin b)) :=
  h ▸ ContinuousMap.id (B × EuclideanSpace ℝ (Fin a))

/-- **The values of `castMap`**: the transported identity is the transport of the points. -/
lemma castMap_apply (B : Type) [TopologicalSpace B] {a b : ℕ} (h : a = b)
    (x : B × EuclideanSpace ℝ (Fin a)) : castMap B h x = h ▸ x := by
  cases h
  rfl

/-- **The transport in coordinates**: the transport of a pair along `h : a = b` acts on the second
factor by the reindexing `finCongr h.symm` (both reviewers confirmed this is a one-line `cases h`). -/
lemma cast_apply_coe (B : Type) [TopologicalSpace B] {a b : ℕ} (h : a = b)
    (x : B × EuclideanSpace ℝ (Fin a)) (i : Fin b) :
    (((h ▸ x : B × EuclideanSpace ℝ (Fin b))).2 : Fin b → ℝ) i
      = ((x.2 : Fin a → ℝ)) (finCongr h.symm i) := by
  cases h
  rfl

/-- **Transport of a relative class along an equality of degrees.**  The cast of the whole type
family `k ↦ RelCoh ℤ k (B × ℝ^k) (Punct B k)` is, up to the degree cast inside the fixed target
world, the pullback along the canonical identification `castMap h`. -/
lemma cast_RelCoh_eq (B : Type) [TopologicalSpace B] {a b : ℕ} (h : a = b)
    (hf : ∀ x ∈ Punct B b, castMap B h.symm x ∈ Punct B a)
    (x : RelCoh ℤ a (B × EuclideanSpace ℝ (Fin a)) (Punct B a)) :
    (h ▸ x : RelCoh ℤ b (B × EuclideanSpace ℝ (Fin b)) (Punct B b))
      = h ▸ ((relCohMap (castMap B h.symm) (Punct B b) (Punct B a) hf ℤ a).hom x) := by
  cases h
  have hcf : castMap B (rfl : a = a).symm
      = ContinuousMap.id (B × EuclideanSpace ℝ (Fin a)) := rfl
  rw [relCohMap_congrA (A := Punct B a) (B := Punct B a)
      (f := castMap B rfl.symm) (f' := ContinuousMap.id (B × EuclideanSpace ℝ (Fin a)))
      hcf hf (fun _ hx => hx) ℤ a]
  rw [relCohMap_idA]
  rfl


/-- **The transported identity preserves the punctured set** (in the pullback direction): this is
the `hf` hypothesis of `cast_RelCoh_eq`.  It is the set-level shadow of the projection identities —
the transport only reindexes the `Fin`-coordinates by `finCongr`, so the zero vector stays the zero
vector. -/
lemma castMap_mem_punct (B : Type) [TopologicalSpace B] {a b : ℕ} (h : a = b)
    (x : B × EuclideanSpace ℝ (Fin b)) (hx : x ∈ Punct B b) :
    castMap B h.symm x ∈ Punct B a := by
  rw [castMap_apply]
  cases h
  exact hx


/-- General cancellation of an `Eq.rec` against its inverse (the tool that flips the cast direction of `tcmProd_eq_cup`). -/
lemma eqRec_cast_symm_cast {α : Sort*} {P : α → Sort*} {a b : α} (h : a = b) (x : P b) :
    h ▸ (h.symm ▸ x) = x := by
  cases h
  rfl



end

-- (namespace Work.Whitney)

-- ===== copied from Submission/Work/Whitney/tcmProj.lean =====

/-!
# The three block projections of the two coordinate worlds, against `castMap`

Companion of `Submission/Work/Whitney/tcmCast.lean`, one level above it and one level *below*
`tcmProd_assoc.lean`: everything here is proved from `castMap` (and the `tcmPr1`/`tcmPr2`/
`Fib.tcmF_inv` API) alone, so the deliverable can import this module and cite the block identities and
the absorptions from its final proof.

Contents: the coordinate descriptions of `tcmPr1/2 ∘ Fib.tcmF_inv` (both blocks), the three block
identities `tcmProjKA.comp (castMap B (Nat.add_assoc m n r).symm) = tcmProjKB` (pointwise and
map-level), the uniform projections `tcmProj1A/B … tcmProj3A/B`, and the `relCohMap`-absorptions
`tcmRelCohMap_absorb2/3`.  Moved here from `tcmPr1_comp_castMap_symm.lean` and
`tcmPr23_comp_castMap_symm.lean` (both of which are now redundant).
-/

open Work.Cohomology
open Work.Thom
open CategoryTheory

-- (namespace Work.Whitney opened by the enclosing namespace)

noncomputable section

/-- **The first coordinate of the inverse coordinate identification**: `(tcmSumLin p q).symm` splits
a vector of `ℝ^{p+q}` into its first `p` and its last `q` coordinates, the first block being read
along `Fin.castAdd q`. -/
lemma tcmSumLin_symm_apply_fst (p q : ℕ) (u : EuclideanSpace ℝ (Fin (p + q))) (i : Fin p) :
    ((tcmSumLin p q).symm u).1 i = u (Fin.castAdd q i) := by
  simp only [tcmSumLin, ContinuousLinearEquiv.symm_symm, EuclideanSpace.finAddEquivProd,
    EuclideanSpace.sumEquivProd, ContinuousLinearEquiv.trans_apply,
    PiLp.sumPiLpEquivProdLpPiLp_apply_ofLp, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    WithLp.prodContinuousLinearEquiv_apply]
  rfl

/-- **The first coordinate of the canonical identification of the two coordinate worlds**: the
transported identity fixes the base point. -/
lemma castMap_apply_fst (B : Type) [TopologicalSpace B] {a b : ℕ} (h : a = b)
    (x : B × EuclideanSpace ℝ (Fin a)) : (castMap B h x).1 = x.1 := by
  rw [castMap_apply]
  cases h
  rfl

/-- **The coordinates of `tcmPr1 B p q ∘ tcmF_inv B p q`**: the `i`-th coordinate of the first
factor of `y ∈ B × ℝ^{p+q}` is the `Fin.castAdd q i`-th coordinate of `y`. -/
lemma tcmPr1_tcmF_inv_snd_apply (B : Type) [TopologicalSpace B] (p q : ℕ)
    (y : B × EuclideanSpace ℝ (Fin (p + q))) (i : Fin p) :
    ((tcmPr1 B p q) ((Fib.tcmF_inv B p q) y)).2 i = y.2 (Fin.castAdd q i) := by
  rw [Fib.tcmF_inv_apply]
  exact tcmSumLin_symm_apply_fst p q y.2 i

theorem tcmPr1_comp_castMap_symm (B : Type) [TopologicalSpace B] (m n r : ℕ) :
    ((Work.Whitney.tcmPr1 B m n).comp ((Work.Whitney.Fib.tcmF_inv B m n).comp
        ((Work.Whitney.tcmPr1 B (m + n) r).comp (Work.Whitney.Fib.tcmF_inv B (m + n) r)))).comp
        (castMap B (Nat.add_assoc m n r).symm)
      = (Work.Whitney.tcmPr1 B m (n + r)).comp (Work.Whitney.Fib.tcmF_inv B m (n + r)) := by
  apply ContinuousMap.ext
  intro x
  apply Prod.ext
  · simp only [ContinuousMap.comp_apply, tcmPr1, Fib.tcmF_inv_apply]
    rw [castMap_apply_fst]
    rfl
  · apply PiLp.ext
    intro i
    simp only [ContinuousMap.comp_apply]
    rw [tcmPr1_tcmF_inv_snd_apply B m n]
    rw [tcmPr1_tcmF_inv_snd_apply B (m + n) r]
    rw [castMap_apply, cast_apply_coe]
    rw [tcmPr1_tcmF_inv_snd_apply B m (n + r)]
    rfl

/-- **The second coordinate of the inverse coordinate identification**: `(tcmSumLin p q).symm` splits
a vector of `ℝ^{p+q}` into its first `p` and its last `q` coordinates, the second block being read
along `Fin.natAdd p`. -/
lemma tcmSumLin_symm_apply_snd (p q : ℕ) (u : EuclideanSpace ℝ (Fin (p + q))) (i : Fin q) :
    ((tcmSumLin p q).symm u).2 i = u (Fin.natAdd p i) := by
  simp only [tcmSumLin, ContinuousLinearEquiv.symm_symm, EuclideanSpace.finAddEquivProd,
    EuclideanSpace.sumEquivProd, ContinuousLinearEquiv.trans_apply,
    PiLp.sumPiLpEquivProdLpPiLp_apply_ofLp, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    WithLp.prodContinuousLinearEquiv_apply]
  rfl

/-- **The coordinates of `tcmPr2 B p q ∘ tcmF_inv B p q`**: the `i`-th coordinate of the second
factor of `y ∈ B × ℝ^{p+q}` is the `Fin.natAdd p i`-th coordinate of `y`. -/
lemma tcmPr2_tcmF_inv_snd_apply (B : Type) [TopologicalSpace B] (p q : ℕ)
    (y : B × EuclideanSpace ℝ (Fin (p + q))) (i : Fin q) :
    ((tcmPr2 B p q) ((Fib.tcmF_inv B p q) y)).2 i = y.2 (Fin.natAdd p i) := by
  rw [Fib.tcmF_inv_apply]
  exact tcmSumLin_symm_apply_snd p q y.2 i

/-- **The middle and last blocks agree across the associativity transport.** -/
theorem tcmPr23_comp_castMap_symm (B : Type) [TopologicalSpace B] (m n r : ℕ) :
    (∀ x : B × EuclideanSpace ℝ (Fin (m + (n + r))),
      (Work.Whitney.tcmPr2 B m n) ((Work.Whitney.Fib.tcmF_inv B m n)
        ((Work.Whitney.tcmPr1 B (m + n) r) ((Work.Whitney.Fib.tcmF_inv B (m + n) r)
          ((castMap B (Nat.add_assoc m n r).symm) x))))
        = (Work.Whitney.tcmPr1 B n r) ((Work.Whitney.Fib.tcmF_inv B n r)
          ((Work.Whitney.tcmPr2 B m (n + r)) ((Work.Whitney.Fib.tcmF_inv B m (n + r)) x))))
    ∧ (∀ x : B × EuclideanSpace ℝ (Fin (m + (n + r))),
      (Work.Whitney.tcmPr2 B (m + n) r) ((Work.Whitney.Fib.tcmF_inv B (m + n) r)
        ((castMap B (Nat.add_assoc m n r).symm) x))
        = (Work.Whitney.tcmPr2 B n r) ((Work.Whitney.Fib.tcmF_inv B n r)
          ((Work.Whitney.tcmPr2 B m (n + r)) ((Work.Whitney.Fib.tcmF_inv B m (n + r)) x)))) := by
  constructor
  · intro x
    apply Prod.ext
    · simp only [tcmPr1, tcmPr2, Fib.tcmF_inv_apply]
      rw [castMap_apply_fst]
      rfl
    · apply PiLp.ext
      intro i
      rw [tcmPr2_tcmF_inv_snd_apply B m n]
      rw [tcmPr1_tcmF_inv_snd_apply B (m + n) r]
      rw [castMap_apply, cast_apply_coe]
      rw [tcmPr1_tcmF_inv_snd_apply B n r]
      rw [tcmPr2_tcmF_inv_snd_apply B m (n + r)]
      have hidx : finCongr (Nat.add_assoc m n r) (Fin.castAdd r (Fin.natAdd m i))
          = Fin.natAdd m (Fin.castAdd r i) := by
        ext
        simp
      rw [hidx]
  · intro x
    apply Prod.ext
    · simp only [tcmPr1, tcmPr2, Fib.tcmF_inv_apply]
      rw [castMap_apply_fst]
      rfl
    · apply PiLp.ext
      intro i
      rw [tcmPr2_tcmF_inv_snd_apply B (m + n) r]
      rw [castMap_apply, cast_apply_coe]
      rw [tcmPr2_tcmF_inv_snd_apply B n r]
      rw [tcmPr2_tcmF_inv_snd_apply B m (n + r)]
      have hidx : finCongr (Nat.add_assoc m n r) (Fin.natAdd (m + n) i)
          = Fin.natAdd m (Fin.natAdd n i) := by
        ext
        simp [Nat.add_assoc]
      rw [hidx]

/-! ## Map-level forms (the input of `relCohMap_compA` / `relCohMap_congrA`)

The pointwise identities above are lifted to equalities of `ContinuousMap`s, which is the form in
which `Work.Thom.relCohMap_compA` absorbs `castMap B (Nat.add_assoc m n r).symm` into the composite
with an `(m+n)+r`-side projection.  (The first block is already at map level:
`Work.Whitney.tcmPr1_comp_castMap_symm`.) -/

/-- **The middle `n` block at map level.** -/
lemma tcmProj2_comp_castMap (B : Type) [TopologicalSpace B] (m n r : ℕ) :
    ((tcmPr2 B m n).comp ((Fib.tcmF_inv B m n).comp
        ((tcmPr1 B (m + n) r).comp (Fib.tcmF_inv B (m + n) r)))).comp
        (castMap B (Nat.add_assoc m n r).symm)
      = (tcmPr1 B n r).comp ((Fib.tcmF_inv B n r).comp
          ((tcmPr2 B m (n + r)).comp (Fib.tcmF_inv B m (n + r)))) := by
  apply ContinuousMap.ext
  intro x
  exact (tcmPr23_comp_castMap_symm B m n r).1 x

/-- **The last `r` block at map level.** -/
lemma tcmProj3_comp_castMap (B : Type) [TopologicalSpace B] (m n r : ℕ) :
    ((tcmPr2 B (m + n) r).comp (Fib.tcmF_inv B (m + n) r)).comp
        (castMap B (Nat.add_assoc m n r).symm)
      = (tcmPr2 B n r).comp ((Fib.tcmF_inv B n r).comp
          ((tcmPr2 B m (n + r)).comp (Fib.tcmF_inv B m (n + r)))) := by
  apply ContinuousMap.ext
  intro x
  exact (tcmPr23_comp_castMap_symm B m n r).2 x

/-! ## The uniform projections of the two worlds

The three block projections of `B × ℝ^{(m+n)+r}` and of `B × ℝ^{m+(n+r)}`, named once and for all.
Written this way (one uniform expression per side), the map-level identities below, the set-preimage
layer, and the `relCohMap`-absorption all refer to the same two maps per block. -/

/-- First `m` coordinates, `(m+n)+r`-world. -/
abbrev tcmProj1A (B : Type) [TopologicalSpace B] (m n r : ℕ) :
    C(B × EuclideanSpace ℝ (Fin ((m + n) + r)), B × EuclideanSpace ℝ (Fin m)) :=
  (tcmPr1 B m n).comp ((Fib.tcmF_inv B m n).comp
    ((tcmPr1 B (m + n) r).comp (Fib.tcmF_inv B (m + n) r)))

/-- First `m` coordinates, `m+(n+r)`-world. -/
abbrev tcmProj1B (B : Type) [TopologicalSpace B] (m n r : ℕ) :
    C(B × EuclideanSpace ℝ (Fin (m + (n + r))), B × EuclideanSpace ℝ (Fin m)) :=
  (tcmPr1 B m (n + r)).comp (Fib.tcmF_inv B m (n + r))

/-- Middle `n` coordinates, `(m+n)+r`-world. -/
abbrev tcmProj2A (B : Type) [TopologicalSpace B] (m n r : ℕ) :
    C(B × EuclideanSpace ℝ (Fin ((m + n) + r)), B × EuclideanSpace ℝ (Fin n)) :=
  (tcmPr2 B m n).comp ((Fib.tcmF_inv B m n).comp
    ((tcmPr1 B (m + n) r).comp (Fib.tcmF_inv B (m + n) r)))

/-- Middle `n` coordinates, `m+(n+r)`-world. -/
abbrev tcmProj2B (B : Type) [TopologicalSpace B] (m n r : ℕ) :
    C(B × EuclideanSpace ℝ (Fin (m + (n + r))), B × EuclideanSpace ℝ (Fin n)) :=
  (tcmPr1 B n r).comp ((Fib.tcmF_inv B n r).comp
    ((tcmPr2 B m (n + r)).comp (Fib.tcmF_inv B m (n + r))))

/-- Last `r` coordinates, `(m+n)+r`-world. -/
abbrev tcmProj3A (B : Type) [TopologicalSpace B] (m n r : ℕ) :
    C(B × EuclideanSpace ℝ (Fin ((m + n) + r)), B × EuclideanSpace ℝ (Fin r)) :=
  (tcmPr2 B (m + n) r).comp (Fib.tcmF_inv B (m + n) r)

/-- Last `r` coordinates, `m+(n+r)`-world. -/
abbrev tcmProj3B (B : Type) [TopologicalSpace B] (m n r : ℕ) :
    C(B × EuclideanSpace ℝ (Fin (m + (n + r))), B × EuclideanSpace ℝ (Fin r)) :=
  (tcmPr2 B n r).comp ((Fib.tcmF_inv B n r).comp
    ((tcmPr2 B m (n + r)).comp (Fib.tcmF_inv B m (n + r))))

/-! ## The three block identities in the uniform notation

`tcmProjKA.comp (castMap B (Nat.add_assoc m n r).symm) = tcmProjKB` for `K = 1, 2, 3`: these are the
hypotheses `relCohMap_congrA` needs in order to absorb `castMap` into the projections. -/

theorem tcmProj1A_comp_castMap (B : Type) [TopologicalSpace B] (m n r : ℕ) :
    (tcmProj1A B m n r).comp (castMap B (Nat.add_assoc m n r).symm) = tcmProj1B B m n r :=
  tcmPr1_comp_castMap_symm B m n r

theorem tcmProj2A_comp_castMap (B : Type) [TopologicalSpace B] (m n r : ℕ) :
    (tcmProj2A B m n r).comp (castMap B (Nat.add_assoc m n r).symm) = tcmProj2B B m n r :=
  tcmProj2_comp_castMap B m n r

theorem tcmProj3A_comp_castMap (B : Type) [TopologicalSpace B] (m n r : ℕ) :
    (tcmProj3A B m n r).comp (castMap B (Nat.add_assoc m n r).symm) = tcmProj3B B m n r :=
  tcmProj3_comp_castMap B m n r

/-! ## Absorbing `castMap` into the projections (`Work.Thom.relCohMap_compA`)

The step that lets the outer `Work.Thom.relCohMap (castMap B (Nat.add_assoc m n r).symm)` of the left hand side
of `tcmProd_assoc` reach inside a block factor: pullback along `tcmProj*A`, followed by pullback along
`castMap …`, is pullback along the composite `tcmProj*A ∘ castMap …` — which is `tcmProj*B` by the
identities above.  Stated with the composite spelling out the B-side map, so that the sets line up
with the conclusion of `Work.Thom.relCohMap_compA` definitionally; converting the composite to `tcmProj*B` is
then `Work.Thom.relCohMap_congrA` applied to `tcmProjKA_comp_castMap` (with the set transported by
`Work.Thom.relCohMap_cast_set`/`Work.Thom.relCohMap_set_cast` of `tcmProd_assoc.lean`). -/

/-- Absorption for the middle `n` block. -/
theorem tcmWork.Thom.RelCohMap_absorb2 (B : Type) [TopologicalSpace B] (m n r : ℕ)
    (S : Set (B × EuclideanSpace ℝ (Fin n)))
    (a : Work.Thom.RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) S) :
    (Work.Thom.relCohMap (castMap B (Nat.add_assoc m n r).symm)
        ((castMap B (Nat.add_assoc m n r).symm) ⁻¹' (tcmProj2A B m n r ⁻¹' S))
        (tcmProj2A B m n r ⁻¹' S) (fun x hx => hx) ℤ n).hom
      ((Work.Thom.relCohMap (tcmProj2A B m n r) (tcmProj2A B m n r ⁻¹' S) S
          (fun x hx => hx) ℤ n).hom a)
      = (Work.Thom.relCohMap ((tcmProj2A B m n r).comp (castMap B (Nat.add_assoc m n r).symm))
          (((tcmProj2A B m n r).comp (castMap B (Nat.add_assoc m n r).symm)) ⁻¹' S) S
          (fun x hx => hx) ℤ n).hom a := by
  rw [Work.Thom.relCohMap_compA_apply ((castMap B (Nat.add_assoc m n r).symm) ⁻¹' (tcmProj2A B m n r ⁻¹' S))
      (tcmProj2A B m n r ⁻¹' S) S (castMap B (Nat.add_assoc m n r).symm) (tcmProj2A B m n r)
      (fun x hx => hx) (fun y hy => hy) (fun x hx => hx) ℤ n a]
  first | rfl | simp only [ContinuousMap.comp_apply, Set.mem_preimage, Set.mem_setOf_eq]

/-- Absorption for the last `r` block. -/
theorem tcmWork.Thom.RelCohMap_absorb3 (B : Type) [TopologicalSpace B] (m n r : ℕ)
    (S : Set (B × EuclideanSpace ℝ (Fin r)))
    (a : Work.Thom.RelCoh ℤ r (B × EuclideanSpace ℝ (Fin r)) S) :
    (Work.Thom.relCohMap (castMap B (Nat.add_assoc m n r).symm)
        ((castMap B (Nat.add_assoc m n r).symm) ⁻¹' (tcmProj3A B m n r ⁻¹' S))
        (tcmProj3A B m n r ⁻¹' S) (fun x hx => hx) ℤ r).hom
      ((Work.Thom.relCohMap (tcmProj3A B m n r) (tcmProj3A B m n r ⁻¹' S) S
          (fun x hx => hx) ℤ r).hom a)
      = (Work.Thom.relCohMap ((tcmProj3A B m n r).comp (castMap B (Nat.add_assoc m n r).symm))
          (((tcmProj3A B m n r).comp (castMap B (Nat.add_assoc m n r).symm)) ⁻¹' S) S
          (fun x hx => hx) ℤ r).hom a := by
  rw [Work.Thom.relCohMap_compA_apply ((castMap B (Nat.add_assoc m n r).symm) ⁻¹' (tcmProj3A B m n r ⁻¹' S))
      (tcmProj3A B m n r ⁻¹' S) S (castMap B (Nat.add_assoc m n r).symm) (tcmProj3A B m n r)
      (fun x hx => hx) (fun y hy => hy) (fun x hx => hx) ℤ r a]
  first | rfl | simp only [ContinuousMap.comp_apply, Set.mem_preimage, Set.mem_setOf_eq]


/-! ## The outer `m+n`-block map of the `m+(n+r)`-world

The B-side counterpart of `tcmPr1 B (m+n) r ∘ Fib.tcmF_inv B (m+n) r`: the `m`-block of `ℝ^{m+(n+r)}`
followed by the first `n` coordinates of its `(n+r)`-block, reassembled into `ℝ^{m+n}`.  Its
characterising identity — `((tcmPr1 B (m+n) r).comp (Fib.tcmF_inv B (m+n) r)).comp
(castMap B (Nat.add_assoc m n r).symm) = tcmOuter1B` — is `tcmOuter1_comp_castMap` (pointwise,
proved/being proved in its own module) transported by `ContinuousMap.ext`; step 3 of the left-hand
push then needs the `m+n`-block absorption, mirroring `tcmRelCohMap_absorb2/3`. -/
noncomputable def tcmOuter1B (B : Type) [TopologicalSpace B] (m n r : ℕ) :
    C(B × EuclideanSpace ℝ (Fin (m + (n + r))), B × EuclideanSpace ℝ (Fin (m + n))) where
  toFun x := (x.1, tcmSumLin m n
    (((tcmSumLin m (n + r)).symm x.2).1,
     ((tcmSumLin n r).symm ((tcmSumLin m (n + r)).symm x.2).2).1))
  continuous_toFun := by
    refine continuous_fst.prodMk ?_
    refine (tcmSumLin m n).continuous.comp ?_
    exact Continuous.prodMk
      (continuous_fst.comp (((tcmSumLin m (n + r)).symm.continuous).comp continuous_snd))
      (continuous_fst.comp (((tcmSumLin n r).symm.continuous).comp
        (continuous_snd.comp (((tcmSumLin m (n + r)).symm.continuous).comp continuous_snd))))

@[simp] lemma tcmOuter1B_apply (B : Type) [TopologicalSpace B] (m n r : ℕ)
    (x : B × EuclideanSpace ℝ (Fin (m + (n + r)))) :
    tcmOuter1B B m n r x = (x.1, tcmSumLin m n
      (((tcmSumLin m (n + r)).symm x.2).1,
       ((tcmSumLin n r).symm ((tcmSumLin m (n + r)).symm x.2).2).1)) := rfl

end

-- (namespace Work.Whitney)

-- ===== copied from Submission/Work/Whitney/tcmOuter1_comp_castMap.lean =====

-- (namespace Work.Whitney opened by the enclosing namespace)

noncomputable section

/-! ## The two coordinate halves of the splitting `tcmSumLin`

`tcmSumLin p q : ℝ^p × ℝ^q ≃L[ℝ] ℝ^{p+q}` keeps the coordinates in order, so on the two
standard blocks its inverse is given by `Fin.castAdd` (first block) and `Fin.natAdd`
(second block) — `tcmSumLin_symm_apply_fst` and `tcmSumLin_symm_apply_snd`.  The two lemmas
below are the same statement read in the forward direction, which is the form in which the
coordinates of `tcmOuter1B` are consumed. -/

lemma tcmSumLin_apply_castAdd (p q : ℕ) (u : EuclideanSpace ℝ (Fin p))
    (v : EuclideanSpace ℝ (Fin q)) (i : Fin p) :
    tcmSumLin p q (u, v) (Fin.castAdd q i) = u i := by
  have h := tcmSumLin_symm_apply_fst p q (tcmSumLin p q (u, v)) i
  rw [ContinuousLinearEquiv.symm_apply_apply] at h
  exact h.symm

lemma tcmSumLin_apply_natAdd (p q : ℕ) (u : EuclideanSpace ℝ (Fin p))
    (v : EuclideanSpace ℝ (Fin q)) (i : Fin q) :
    tcmSumLin p q (u, v) (Fin.natAdd p i) = v i := by
  have h := tcmSumLin_symm_apply_snd p q (tcmSumLin p q (u, v)) i
  rw [ContinuousLinearEquiv.symm_apply_apply] at h
  exact h.symm

/-- **The outer `m+n` block of the `m+(n+r)` world.**  Pulling the first `m+n` coordinates of
`ℝ^{(m+n)+r}` back along the associativity transport `castMap B (Nat.add_assoc m n r).symm` and
splitting off the last `r` coordinates gives the same map as: split `ℝ^{m+(n+r)}` into its first `m`
and last `n+r` coordinates, split the latter into `n` and `r`, and reassemble the `m`- and
`n`-blocks with `tcmSumLin m n`.  This is the pointwise statement that
`(tcmPr1 B (m+n) r ∘ Fib.tcmF_inv B (m+n) r) ∘ castMap B (Nat.add_assoc m n r).symm = tcmOuter1B`
(see `Submission/Work/Whitney/tcmProj.lean`). -/
theorem tcmOuter1_comp_castMap (B : Type) [TopologicalSpace B] (m n r : ℕ) :
    ∀ x : B × EuclideanSpace ℝ (Fin (m + (n + r))),
      (Work.Whitney.tcmPr1 B (m + n) r) ((Work.Whitney.Fib.tcmF_inv B (m + n) r)
          ((castMap B (Nat.add_assoc m n r).symm) x))
        = (x.1, Work.Whitney.tcmSumLin m n
            (((Work.Whitney.tcmSumLin m (n + r)).symm x.2).1,
             ((Work.Whitney.tcmSumLin n r).symm ((Work.Whitney.tcmSumLin m (n + r)).symm x.2).2).1)) := by
  intro x
  apply Prod.ext
  · simp only [tcmPr1, Fib.tcmF_inv_apply]
    rw [castMap_apply_fst]
    rfl
  · apply PiLp.ext
    intro i
    refine Fin.addCases ?_ ?_ i
    · -- `i = Fin.castAdd n i'`: the coordinate lies in the first `m` block.
      intro i'
      rw [tcmPr1_tcmF_inv_snd_apply B (m + n) r]
      rw [castMap_apply, cast_apply_coe]
      rw [tcmSumLin_apply_castAdd m n _ _ i']
      rw [tcmSumLin_symm_apply_fst]
      rfl
    · -- `i = Fin.natAdd m j`: the coordinate lies in the middle `n` block.
      intro j
      rw [tcmPr1_tcmF_inv_snd_apply B (m + n) r]
      rw [castMap_apply, cast_apply_coe]
      rw [tcmSumLin_apply_natAdd m n _ _ j]
      rw [tcmSumLin_symm_apply_fst]
      rw [tcmSumLin_symm_apply_snd]
      rfl

end

-- (namespace Work.Whitney)


end

end Work.Whitney.TCMAssocUp
