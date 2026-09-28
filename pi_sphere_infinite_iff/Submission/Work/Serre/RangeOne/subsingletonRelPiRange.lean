import Mathlib
import Submission.Work.Serre.C1CylExplicit
import Submission.Work.Serre.cylRelPi
import Submission.Work.RatHurewicz.CompressRelToRelPi

/-!
# The relative homotopy groups of the pair `(cyl f, range (cylIncl f))`

The relative homotopy data of the mapping-cylinder inclusion `cylIncl f : X → cyl f`
(`Work.Serre.cylRelPi`) is stated for the *map* `cylIncl f` — i.e. for the homotopy fibre of
`cylIncl f` — while the consumers (`Work.Serre.rangeWhiteheadPair`,
`Work.RatHurewicz.compression_of_relPiVanishing`) are stated for the *pair*
`(cyl f, Set.range (cylIncl f))`, i.e. for the inclusion of the range as a subspace.  The two
homotopy fibres are homeomorphic (path reversal and the homeomorphism of `X` with the bottom copy
of the mapping cylinder `Work.Serre.cylHomeoExplicit`), and this file transports the vanishing of
the relative homotopy groups across that homeomorphism.

* `fibreHomeoOfHomeoRange` — the homeomorphism of homotopy fibres attached to a homeomorphism
  `e : A ≃ₜ Set.range f` which is compatible with `f` (`∀ a, (e a : X) = f a`);
* `subsingleton_relPi_of_homeoRange` — the transport of `Subsingleton` of the relative homotopy
  group along it;
* `subsingletonRelPiRange` — the requested statement for the pair `(cyl f, range (cylIncl f))`.
-/

open scoped Topology Topology.Homotopy unitInterval
open Work.StemsB (PathSpace evalOne)

namespace Work.Serre.RangeOne

noncomputable section

/-- **The homotopy fibres of `f` and of the inclusion of its range are homeomorphic**, given a
homeomorphism `e : A ≃ₜ Set.range f` compatible with `f`.  Both are spaces of pairs
`(point, path)` with the *same* path space: the first components are related by `e`, the second are
the identity.  This is the general form of `Work.RatHurewicz.fibreHomeoOfIsEmbedding`, stated for an
arbitrary homeomorphism onto the range instead of `Topology.IsEmbedding.toHomeomorph`. -/
def fibreHomeoOfHomeoRange {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    (f : C(A, X)) (e : A ≃ₜ ↥(Set.range (f : A → X)))
    (he : ∀ a : A, (e a : X) = f a) (a₀ : A) :
    (Work.RatHurewicz.homotopyFibre f a₀) ≃ₜ
    (Work.RatHurewicz.homotopyFibre (Work.RatHurewicz.setIncl (Set.range (f : A → X)))
      ⟨f a₀, a₀, rfl⟩) where
  toFun p :=
    ⟨(⟨f p.1.1, p.1.1, rfl⟩, p.1.2), by
      show (evalOne X (f a₀)) p.1.2
        = Work.RatHurewicz.setIncl (Set.range (f : A → X)) ⟨f p.1.1, p.1.1, rfl⟩
      have h1 : (Work.RatHurewicz.setIncl (Set.range (f : A → X))
          ⟨f p.1.1, p.1.1, rfl⟩ : X) = f p.1.1 := rfl
      rw [h1]
      exact p.2⟩
  invFun q :=
    ⟨(e.symm q.1.1, q.1.2), by
      show (evalOne X (f a₀)) q.1.2 = f (e.symm q.1.1)
      have h1 : f (e.symm q.1.1)
          = ((e (e.symm q.1.1) : Set.range (f : A → X)) : X) := (he (e.symm q.1.1)).symm
      rw [h1, Homeomorph.apply_symm_apply]
      exact q.2⟩
  left_inv p := by
    refine Subtype.ext (Prod.ext ?_ rfl)
    show e.symm (⟨f p.1.1, p.1.1, rfl⟩ : Set.range (f : A → X)) = p.1.1
    have h2 : (⟨f p.1.1, p.1.1, rfl⟩ : Set.range (f : A → X)) = e p.1.1 :=
      Subtype.ext (he p.1.1).symm
    rw [h2, Homeomorph.symm_apply_apply]
  right_inv q := by
    refine Subtype.ext (Prod.ext (Subtype.ext ?_) rfl)
    show f (e.symm q.1.1) = ((q.1.1 : Set.range (f : A → X)) : X)
    have h1 : f (e.symm q.1.1)
        = ((e (e.symm q.1.1) : Set.range (f : A → X)) : X) := (he (e.symm q.1.1)).symm
    rw [h1, Homeomorph.apply_symm_apply]
  continuous_toFun := Continuous.subtype_mk
    (Continuous.prodMk
      (Continuous.subtype_mk
        (f.continuous.comp (continuous_fst.comp continuous_subtype_val))
        (fun p => ⟨p.1.1, rfl⟩))
      (continuous_snd.comp continuous_subtype_val))
    (fun p => by
      show (evalOne X (f a₀)) p.1.2
        = Work.RatHurewicz.setIncl (Set.range (f : A → X)) ⟨f p.1.1, p.1.1, rfl⟩
      have h1 : (Work.RatHurewicz.setIncl (Set.range (f : A → X))
          ⟨f p.1.1, p.1.1, rfl⟩ : X) = f p.1.1 := rfl
      rw [h1]
      exact p.2)
  continuous_invFun := Continuous.subtype_mk
    (Continuous.prodMk
      (e.symm.continuous.comp (continuous_fst.comp continuous_subtype_val))
      (continuous_snd.comp continuous_subtype_val))
    (fun q => by
      show (evalOne X (f a₀)) q.1.2 = f (e.symm q.1.1)
      have h1 : f (e.symm q.1.1)
          = ((e (e.symm q.1.1) : Set.range (f : A → X)) : X) := (he (e.symm q.1.1)).symm
      rw [h1, Homeomorph.apply_symm_apply]
      exact q.2)

/-- **Transport of the vanishing of the relative homotopy groups from a map to the inclusion of
its range.**  If `e : A ≃ₜ Set.range f` is a homeomorphism compatible with `f` (`∀ a, (e a : X)
= f a`), then the relative homotopy group of the pair `(Set.range f ⊆ X)` at `f a₀` is a
subsingleton as soon as the relative homotopy group of `f` at `a₀` is.  This is the reverse
direction of `Work.RatHurewicz.subsingleton_relPi_of_isEmbedding`. -/
theorem subsingleton_relPi_of_homeoRange {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    (f : C(A, X)) (e : A ≃ₜ ↥(Set.range (f : A → X)))
    (he : ∀ a : A, (e a : X) = f a) (a₀ : A) (j : ℕ)
    (h : Subsingleton (Work.RatHurewicz.RelHomotopyGroup f a₀ j)) :
    Subsingleton (Work.RatHurewicz.RelHomotopyGroup
      (Work.RatHurewicz.setIncl (Set.range (f : A → X))) ⟨f a₀, a₀, rfl⟩ j) := by
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    have hZ : Subsingleton (ZerothHomotopy (Work.RatHurewicz.homotopyFibre f a₀)) := by
      haveI := h
      refine ⟨fun u v => ?_⟩
      let ex := homotopyGroupEquivZerothHomotopyOfIsEmpty (N := Fin 0)
        (X := Work.RatHurewicz.homotopyFibre f a₀)
        (Work.RatHurewicz.homotopyFibreBasepoint f a₀)
      exact ex.symm.injective (Subsingleton.elim (ex.symm u) (ex.symm v))
    have hZ' : Subsingleton (ZerothHomotopy (Work.RatHurewicz.homotopyFibre
        (Work.RatHurewicz.setIncl (Set.range (f : A → X))) ⟨f a₀, a₀, rfl⟩)) :=
      Work.RatHurewicz.subsingleton_zerothHomotopy_of_homotopyEquiv
        (fibreHomeoOfHomeoRange f e he a₀).symm.toHomotopyEquiv hZ
    haveI := hZ'
    refine ⟨fun u v => ?_⟩
    let ex := homotopyGroupEquivZerothHomotopyOfIsEmpty (N := Fin 0)
      (X := Work.RatHurewicz.homotopyFibre (Work.RatHurewicz.setIncl (Set.range (f : A → X)))
        ⟨f a₀, a₀, rfl⟩)
      (Work.RatHurewicz.homotopyFibreBasepoint
        (Work.RatHurewicz.setIncl (Set.range (f : A → X))) ⟨f a₀, a₀, rfl⟩)
    exact ex.injective (Subsingleton.elim (ex u) (ex v))
  · haveI : Nonempty (Fin j) := ⟨⟨0, hj⟩⟩
    obtain ⟨me⟩ := Work.Stems.mulEquiv_of_homotopyEquiv (N := Fin j)
      (fibreHomeoOfHomeoRange f e he a₀).toHomotopyEquiv
      (Work.RatHurewicz.homotopyFibreBasepoint f a₀)
    exact ⟨fun u v => me.symm.injective (h.elim (me.symm u) (me.symm v))⟩

/-- **The chosen homeomorphism of `X` onto the bottom copy of the mapping cylinder.** -/
def cylRangeHomeo {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    X ≃ₜ ↥(Set.range (Work.Serre.cylIncl f)) :=
  (Work.Serre.cylHomeoExplicit f).choose

/-- The defining property of `cylRangeHomeo`: the underlying points are the bottom copy of the
mapping cylinder. -/
theorem cylRangeHomeo_coe {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    (cylRangeHomeo f x : Work.Serre.cyl f) = Work.Serre.cylIncl f x :=
  (Work.Serre.cylHomeoExplicit f).choose_spec x

theorem subsingletonRelPiRange {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : ContinuousMap X Y)
    (h : ∀ x : X, ∀ j : ℕ,
      Subsingleton (Work.RatHurewicz.RelHomotopyGroup (Work.Serre.cylIncl f) x j)) :
    ∀ a : ↥(Set.range (Work.Serre.cylIncl f)), ∀ j : ℕ,
      Subsingleton (Work.RatHurewicz.RelHomotopyGroup
        (Work.RatHurewicz.setIncl (Set.range (Work.Serre.cylIncl f))) a j) := by
  intro a j
  have ha : a = (⟨Work.Serre.cylIncl f ((cylRangeHomeo f).symm a),
      (cylRangeHomeo f).symm a, rfl⟩ : ↥(Set.range (Work.Serre.cylIncl f))) :=
    Subtype.ext ((congrArg Subtype.val ((cylRangeHomeo f).apply_symm_apply a)).symm.trans
      (cylRangeHomeo_coe f ((cylRangeHomeo f).symm a)))
  rw [ha]
  exact subsingleton_relPi_of_homeoRange (Work.Serre.cylIncl f) (cylRangeHomeo f)
    (cylRangeHomeo_coe f) ((cylRangeHomeo f).symm a) j (h ((cylRangeHomeo f).symm a) j)

end

end Work.Serre.RangeOne
