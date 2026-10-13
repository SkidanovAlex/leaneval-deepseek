import Mathlib

-- `haveI` registers the flatness of a stage as a local instance for the equational criterion;
-- the style linter would suggest `have`, which does not feed instance resolution here.
set_option linter.style.haveILetI false

/-!
# Flatness passes to a directed union of subrings

Let `A` be a commutative ring, `S` a commutative `A`-algebra and `R : ι → Subring S` a *monotone*
family of subrings indexed by a nonempty semilattice `ι`.  Suppose that for every `i` the subring
`↥(R i)` is equipped with an `A`-algebra structure compatible with the inclusion `↥(R i) ↪ S`
(`hcomp`), that `↥(⨆ i, R i)` is likewise an `A`-algebra compatible with `↥(⨆ i, R i) ↪ S`
(`hcomp'`), and that each `↥(R i)` is flat over `A`.  Then the union `↥(⨆ i, R i)` is flat over
`A`.

The mathematical content is that a *filtered* (here: directed) colimit of flat modules is flat.
Because `R` is monotone and `ι` is a semilattice, the family is directed and `⨆ i, R i` is its
(the set-theoretic) union, so every *finite* piece of data lives at a single stage.

The proof uses the equational criterion for flatness
(`Module.Flat.of_forall_isTrivialRelation`): given a relation `∑ i, f i • x i = 0` in the union,
each `x i` lies in some stage `R (n i)` (`Subring.mem_iSup_of_directed`); the finitely many stages
have a common upper bound `N`, so the whole relation is a relation in the flat stage `↥(R N)`
(`hzw`), where it is trivial.  The trivialisation is transported back along the (indeed
`A`-linear, by `hcomp`) inclusion `↥(R N) ↪ ↥(⨆ i, R i)` (`inclLinearMap`).

## Main result

* `Work.DSM2p.flat_iSup_subring_of_flat` — flatness passes to the directed union.
-/

namespace Work.DSM2p

section Helpers

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
  {ι : Type*} {R : ι → Subring S} [instR : ∀ i, Algebra A ↥(R i)]

/-- **`A`-linearity of the inclusion `↥(R i) ↪ ↥T`.**  If the `A`-algebra structures on `↥(R i)`
and on a further subring `T ⊇ R i` are both compatible with the inclusions into `S` (`hi`, `hT`),
then the ring inclusion `↥(R i) ↪ ↥T` sends `algebraMap A ↥(R i) a` to `algebraMap A ↥T a`. -/
theorem inclusion_algMap {i : ι} {T : Subring S} [Algebra A ↥T]
    (hi : (Subring.subtype (R i)).comp (algebraMap A ↥(R i)) = (algebraMap A S))
    (hT : (Subring.subtype T).comp (algebraMap A ↥T) = (algebraMap A S))
    (hRT : R i ≤ T) (a : A) :
    Subring.inclusion hRT (algebraMap A ↥(R i) a) = algebraMap A ↥T a := by
  apply Subtype.ext
  rw [Subring.coe_inclusion]
  have h1 := DFunLike.congr_fun hi a
  have h2 := DFunLike.congr_fun hT a
  simp only [RingHom.comp_apply] at h1 h2
  exact h1.trans h2.symm

/-- **The inclusion `↥(R i) ↪ ↥T` as an `A`-linear map.**  With the compatibility hypotheses of
`inclusion_algMap`, `Subring.inclusion hRT` commutes with the `A`-scalar action. -/
noncomputable def inclLinearMap {i : ι} {T : Subring S} [Algebra A ↥T]
    (hi : (Subring.subtype (R i)).comp (algebraMap A ↥(R i)) = (algebraMap A S))
    (hT : (Subring.subtype T).comp (algebraMap A ↥T) = (algebraMap A S))
    (hRT : R i ≤ T) : ↥(R i) →ₗ[A] ↥T where
  toFun := Subring.inclusion hRT
  map_add' := fun x y => map_add (Subring.inclusion hRT) x y
  map_smul' := fun a m => by
    -- `↥T` is an `A`-module through `Algebra A ↥T`, so `c • y = algebraMap A ↥T c * y`,
    -- while `↥(R i)` is an `A`-module through `Algebra A ↥(R i)`; `inclusion_algMap` identifies
    -- the two images of `algebraMap A _ a`.
    simp only [RingHom.id_apply, Algebra.smul_def, map_mul, inclusion_algMap hi hT hRT a]

@[simp]
theorem inclLinearMap_apply {i : ι} {T : Subring S} [Algebra A ↥T]
    (hi : (Subring.subtype (R i)).comp (algebraMap A ↥(R i)) = (algebraMap A S))
    (hT : (Subring.subtype T).comp (algebraMap A ↥T) = (algebraMap A S))
    (hRT : R i ≤ T) (x : ↥(R i)) :
    inclLinearMap (R := R) hi hT hRT x = Subring.inclusion hRT x := rfl

end Helpers

theorem flat_iSup_subring_of_flat {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    {ι : Type*} [Nonempty ι] [SemilatticeSup ι] {R : ι → Subring S} (hR : Monotone R)
    [∀ i, Algebra A ↥(R i)]
    (hcomp : ∀ i, (Subring.subtype (R i)).comp (algebraMap A ↥(R i)) = (algebraMap A S))
    [Algebra A ↥(⨆ i, R i)]
    (hcomp' : (Subring.subtype (⨆ i, R i)).comp (algebraMap A ↥(⨆ i, R i)) = (algebraMap A S))
    (h : ∀ i, Module.Flat A ↥(R i)) : Module.Flat A ↥(⨆ i, R i) := by
  classical
  -- It suffices to make every relation in `⨆ i, R i` trivial (equational criterion).
  refine Module.Flat.of_forall_isTrivialRelation ?_
  intro l f x hx
  -- The monotone family `R` is directed, since `ι` is a semilattice.
  have hdir : Directed (· ≤ ·) R := fun i j => ⟨i ⊔ j, hR le_sup_left, hR le_sup_right⟩
  -- Every `x i` lies in a stage `R (n i)` of the family.
  choose n hn using fun i : Fin l => (Subring.mem_iSup_of_directed hdir).mp (x i).2
  -- The finitely many stages have a common upper bound `N`.
  have key : ∀ s : Finset (Fin l), ∃ N : ι, ∀ i ∈ s, n i ≤ N := by
    intro s
    induction s using Finset.induction with
    | empty => exact ⟨Classical.arbitrary ι, by simp⟩
    | insert a s _ ih =>
      obtain ⟨N, hN⟩ := ih
      obtain ⟨M, haM, hNM⟩ := exists_ge_ge (n a) N
      exact ⟨M, fun i hi => by
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact haM
        · exact (hN i hi).trans hNM⟩
  obtain ⟨N, hN⟩ : ∃ N : ι, ∀ i : Fin l, n i ≤ N := by simpa using key Finset.univ
  -- The `i`-th element, viewed in the stage `N`.
  let z : Fin l → ↥(R N) := fun i => ⟨(x i : S), hR (hN i) (hn i)⟩
  -- The (`A`-linear) inclusion of that stage into the union.
  let inclTop : ↥(R N) →ₗ[A] ↥(⨆ i, R i) :=
    inclLinearMap (R := R) (hcomp N) hcomp' (le_iSup R N)
  have hinj : Function.Injective inclTop := Subring.inclusion_injective (le_iSup R N)
  have hzx : ∀ i, inclTop (z i) = x i := fun _ => Subtype.ext rfl
  -- The relation, pushed to the stage `N`, is a relation in the flat module `↥(R N)`.
  have hzw : ∑ i, f i • z i = 0 := by
    apply hinj
    rw [map_zero]
    have h1 : inclTop (∑ i, f i • z i) = ∑ i, f i • x i := by
      simp only [map_sum, map_smul, hzx]
    rw [h1, hx]
  -- It is trivial there.
  haveI : Module.Flat A ↥(R N) := h N
  obtain ⟨k, aa, yy, hdec, hrel⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (f := f) (x := z) hzw
  -- Transport the trivialisation along the inclusion into the union.
  refine ⟨k, aa, fun j => inclTop (yy j), fun i => ?_, hrel⟩
  calc x i = inclTop (z i) := (hzx i).symm
    _ = inclTop (∑ j, aa i j • yy j) := by rw [hdec i]
    _ = ∑ j, aa i j • inclTop (yy j) := by
      simp only [map_sum, map_smul]

end Work.DSM2p
