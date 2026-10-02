import Mathlib
import Submission.Work.Serre.RangeOne.Comparison
import Submission.Work.Serre.cylRelPi
import Submission.Work.Serre.C1CylExplicit
import Submission.Work.Serre.hZeroOfPiZero
import Submission.Work.RatHurewicz.exists_killed_tower

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Range-Whitehead for maps: `πᵢ`-bijectivity in a range implies rational homology isomorphisms

`Work.Serre.RangeOne.rangeWhitehead`: if `f : X → Y` is a bijection on `πᵢ` (at *every* base point)
for `i ≤ M`, then `f` induces an isomorphism on rational homology in degrees `< M`.

The proof replaces `f` by the inclusion `cylIncl f : X → cyl f` of the source into its mapping
cylinder (`Work.Serre.C1Cyl`).  The retraction `cylRetract f` is a homotopy equivalence with
`cylRetract f ∘ cylIncl f = f`, so it suffices to prove the claim for `cylIncl f`.  The pair
`(cyl f, Set.range (cylIncl f))` has the compression property in degrees `≤ M`
(`Work.Serre.cylRelPi` for the vanishing of the relative homotopy groups of `cylIncl f`, transported
to the inclusion of its range along the homeomorphism of the homotopy fibres, then
`Work.RatHurewicz.compression_of_relPiVanishing`), whence
`Work.Serre.isIso_ratHomologyMap_setIncl_of_compressRel` gives `H_t(cyl f;ℚ) ≅ H_t(↥range;ℚ)` for
`t < M`, i.e. `H_t(cyl f;ℚ) ≅ H_t(X;ℚ)` since the bottom copy of the cylinder is homeomorphic to
the source.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.RangeOne

noncomputable section

/-! ## The bottom copy of the mapping cylinder is an embedding -/

/-- **The bottom copy of the mapping cylinder is an embedding.**  `cylIncl f` is the composite of
the homeomorphism `cylHomeoExplicit` of `Work.Serre.C1CylExplicit` with the inclusion of the range
`↥(Set.range (cylIncl f)) ↪ cyl f`, which is an embedding. -/
theorem isEmbedding_cylIncl {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : Topology.IsEmbedding (Work.Serre.cylIncl f : X → Work.Serre.cyl f) := by
  obtain ⟨e, he⟩ := Work.Serre.cylHomeoExplicit f
  have hsub : Topology.IsEmbedding
      (Subtype.val : ↥(Set.range (Work.Serre.cylIncl f)) → Work.Serre.cyl f) :=
    Topology.IsEmbedding.mk (Topology.IsInducing.mk rfl) Subtype.val_injective
  have hcomp := Topology.IsEmbedding.comp hsub e.isEmbedding
  have hfun : ((Subtype.val : ↥(Set.range (Work.Serre.cylIncl f)) → Work.Serre.cyl f) ∘
      (e : X → ↥(Set.range (Work.Serre.cylIncl f))))
      = (Work.Serre.cylIncl f : X → Work.Serre.cyl f) := funext he
  rwa [hfun] at hcomp

/-! ## Subsingletonness of homotopy groups transfers along a homeomorphism -/

/-- **A homeomorphism `e : F ≃ₜ F'` induces a bijection on `π_j`**, so the triviality of
`π_j(F, x)` implies that of `π_j(F', e x)`.  The case `j = 0` goes through
`ZerothHomotopy` (there is no `Nonempty (Fin 0)` instance to apply
`Work.Stems.mulEquiv_of_homotopyEquiv`), the case `j ≥ 1` through that lemma. -/
theorem subsingleton_homotopyGroup_of_homeo {F F' : Type} [TopologicalSpace F]
    [TopologicalSpace F'] (e : F ≃ₜ F') (x : F) (j : ℕ)
    (h : Subsingleton (HomotopyGroup (Fin j) F x)) :
    Subsingleton (HomotopyGroup (Fin j) F' (e x)) := by
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    have hZ : Subsingleton (ZerothHomotopy F) := by
      have := h
      refine ⟨fun u v => ?_⟩
      let ex := homotopyGroupEquivZerothHomotopyOfIsEmpty (N := Fin 0) (X := F) x
      exact ex.symm.injective (Subsingleton.elim (ex.symm u) (ex.symm v))
    have hZ' : Subsingleton (ZerothHomotopy F') :=
      Work.RatHurewicz.subsingleton_zerothHomotopy_of_homotopyEquiv e.symm.toHomotopyEquiv hZ
    have := hZ'
    refine ⟨fun u v => ?_⟩
    let ex := homotopyGroupEquivZerothHomotopyOfIsEmpty (N := Fin 0) (X := F') (e x)
    exact ex.injective (Subsingleton.elim (ex u) (ex v))
  · have : Nonempty (Fin j) := ⟨⟨0, hj⟩⟩
    obtain ⟨me⟩ := Work.Stems.mulEquiv_of_homotopyEquiv (N := Fin j) e.toHomotopyEquiv x
    have := h
    exact ⟨fun a b => me.symm.injective (Subsingleton.elim (me.symm a) (me.symm b))⟩

/-! ## The relative groups of the inclusion of the range of `cylIncl f` -/

/-- **The relative homotopy groups of the inclusion of the range of `cylIncl f`** vanish as soon as
those of `cylIncl f` do.  The two homotopy fibres are homeomorphic
(`Work.RatHurewicz.fibreHomeoOfIsEmbedding`, which applies since `cylIncl f` is an embedding), and
triviality of `π_j` transfers along the homeomorphism. -/
theorem subsingleton_relPi_range_cylIncl {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (j : ℕ)
    (h : Subsingleton (Work.RatHurewicz.RelHomotopyGroup (Work.Serre.cylIncl f) x j)) :
    Subsingleton (Work.RatHurewicz.RelHomotopyGroup
      (Work.RatHurewicz.setIncl (Set.range (Work.Serre.cylIncl f)))
      ⟨Work.Serre.cylIncl f x, x, rfl⟩ j) := by
  have hbase : (Work.RatHurewicz.fibreHomeoOfIsEmbedding (Work.Serre.cylIncl f) x
        (isEmbedding_cylIncl f)) (Work.RatHurewicz.homotopyFibreBasepoint (Work.Serre.cylIncl f) x)
      = Work.RatHurewicz.homotopyFibreBasepoint
          (Work.RatHurewicz.setIncl (Set.range (Work.Serre.cylIncl f)))
          ⟨Work.Serre.cylIncl f x, x, rfl⟩ := rfl
  show Subsingleton (HomotopyGroup (Fin j)
    (Work.RatHurewicz.homotopyFibre (Work.RatHurewicz.setIncl (Set.range (Work.Serre.cylIncl f)))
      ⟨Work.Serre.cylIncl f x, x, rfl⟩)
    (Work.RatHurewicz.homotopyFibreBasepoint
      (Work.RatHurewicz.setIncl (Set.range (Work.Serre.cylIncl f)))
      ⟨Work.Serre.cylIncl f x, x, rfl⟩))
  rw [← hbase]
  exact subsingleton_homotopyGroup_of_homeo _ _ j h

/-! ## Every point of the mapping cylinder is joined to its bottom copy -/

/-- **The pair `(cyl f, Set.range (cylIncl f))` is `0`-connected**, from the surjectivity of `π₀(f)`
at the base point `x₀`: a point `(p, t)` of the cylinder runs vertically down to `cylIncl f p`,
and a point `x` of the target `Y` is joined there (through `cylInr f`) to `f p` for a suitable `p`,
which is the top endpoint of the vertical path of `p`. -/
theorem cyl_joined_range {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x₀ : X) (h0 : Function.Bijective (Work.Serre.piMapN f 0 x₀)) :
    ∀ y : Work.Serre.cyl f, ∃ a : ↥(Set.range (Work.Serre.cylIncl f)),
      Nonempty (Path y a.1) := by
  have hbij : Function.Bijective (Work.Serre.h0Pi0Map f) :=
    Work.Serre.h0Pi0Map_bijective f h0
  intro y
  induction y using Quotient.inductionOn with
  | h z =>
    rcases z with ⟨p, t⟩ | x
    · exact ⟨⟨Work.Serre.cylIncl f p, p, rfl⟩, ⟨Work.Serre.cylVertPath f p t⟩⟩
    · obtain ⟨q, hq⟩ := hbij.2 (ZerothHomotopy.mk x)
      obtain ⟨p, rfl⟩ := ZerothHomotopy.mk_surjective q
      rw [Work.Serre.h0Pi0Map_mk f p] at hq
      have hj : Joined (f p) x := Quotient.exact hq
      refine ⟨⟨Work.Serre.cylIncl f p, p, rfl⟩, ?_⟩
      refine ((hj.map (Work.Serre.cylInr f).continuous).symm.trans ?_)
      rw [← Work.Serre.cyl_mk_inl_one f p]
      exact ⟨Work.Serre.cylVertPath f p 1⟩

/-! ## The theorem -/

theorem rangeWhitehead (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X] (x₀ : X) (f : ContinuousMap X Y) (M : ℕ) (h : ∀ i : ℕ, i ≤ M → ∀ x : X, Function.Bijective (Work.Serre.piMapN f i x)) : ∀ t : ℕ, t < M → CategoryTheory.IsIso (Work.Serre.ratHomologyMap f t) := by
  intro t ht
  rcases Nat.eq_zero_or_pos M with hM | hM
  · omega
  · set n : ℕ := M - 1 with hn
    -- the relative groups of `cylIncl f` vanish in degrees `≤ n`
    have hrel : ∀ x : X, ∀ k : ℕ, k ≤ n →
        Subsingleton (Work.RatHurewicz.RelHomotopyGroup (Work.Serre.cylIncl f) x k) :=
      fun x k hk => (Work.Serre.cylRelPi f x n (fun i hi y => h i (by omega) y)).1 k (by omega)
    -- transport to the inclusion of the range
    have hset : ∀ a : ↥(Set.range (Work.Serre.cylIncl f)), ∀ k : ℕ, k ≤ n →
        Subsingleton (Work.RatHurewicz.RelHomotopyGroup
          (Work.RatHurewicz.setIncl (Set.range (Work.Serre.cylIncl f))) a k) := by
      intro a k hk
      obtain ⟨x, hx⟩ := a.2
      have hEq : (⟨Work.Serre.cylIncl f x, x, rfl⟩ : ↥(Set.range (Work.Serre.cylIncl f))) = a :=
        Subtype.ext hx
      exact hEq ▸ (subsingleton_relPi_range_cylIncl f x k (hrel x k hk))
    -- compression in degrees `≤ M`
    have hconn := cyl_joined_range f x₀ (h 0 (by omega) x₀)
    have hcomp : ∀ d : ℕ, d ≤ M → Work.RatHurewicz.CompressRel (Work.Serre.cyl f)
        (Set.range (Work.Serre.cylIncl f)) d := by
      have h := Work.RatHurewicz.compression_of_relPiVanishing (Y := Work.Serre.cyl f)
        (A := Set.range (Work.Serre.cylIncl f)) n hconn (fun a k hk => hset a k hk)
      intro d hd
      exact h d (by omega)
    have hsetiso : ∀ t : ℕ, t < M → IsIso (Work.Serre.ratHomologyMap
        (Work.RatHurewicz.setIncl (Set.range (Work.Serre.cylIncl f))) t) :=
      Work.Serre.isIso_ratHomologyMap_setIncl_of_compressRel hcomp
    -- the corestriction homeomorphism `X ≃ₜ ↥(Set.range (cylIncl f))`
    obtain ⟨e, he⟩ := Work.Serre.cylHomeoExplicit f
    let ecm : C(X, ↥(Set.range (Work.Serre.cylIncl f))) := e.toHomotopyEquiv.toFun
    have hfact : (Work.RatHurewicz.setIncl (Set.range (Work.Serre.cylIncl f))).comp ecm
        = Work.Serre.cylIncl f := ContinuousMap.ext (fun x => he x)
    have hcylincl : IsIso (Work.Serre.ratHomologyMap (Work.Serre.cylIncl f) t) := by
      have hsplit : Work.Serre.ratHomologyMap (Work.Serre.cylIncl f) t
          = Work.Serre.ratHomologyMap ecm t ≫ Work.Serre.ratHomologyMap
              (Work.RatHurewicz.setIncl (Set.range (Work.Serre.cylIncl f))) t := by
        rw [← Work.Serre.ratHomologyMap_comp ecm
          (Work.RatHurewicz.setIncl (Set.range (Work.Serre.cylIncl f))) t, hfact]
      rw [hsplit]
      have : IsIso (Work.Serre.ratHomologyMap ecm t) :=
        Work.Serre.IsRatHomologyIso.of_homotopyEquiv e.toHomotopyEquiv t
      have : IsIso (Work.Serre.ratHomologyMap
          (Work.RatHurewicz.setIncl (Set.range (Work.Serre.cylIncl f))) t) := hsetiso t ht
      infer_instance
    -- the retraction
    obtain ⟨E, hE⟩ := Work.Serre.cylHomotopyEquivExplicit f
    have hret : IsIso (Work.Serre.ratHomologyMap (Work.Serre.cylRetract f) t) := by
      have h1 : IsIso (Work.Serre.ratHomologyMap E.toFun t) :=
        Work.Serre.IsRatHomologyIso.of_homotopyEquiv E t
      rwa [hE] at h1
    have hff : Work.Serre.ratHomologyMap f t
        = Work.Serre.ratHomologyMap (Work.Serre.cylIncl f) t ≫
          Work.Serre.ratHomologyMap (Work.Serre.cylRetract f) t := by
      rw [← Work.Serre.ratHomologyMap_comp (Work.Serre.cylIncl f) (Work.Serre.cylRetract f) t,
        Work.Serre.cylRetract_cylIncl f]
    rw [hff]
    have := hcylincl
    have := hret
    infer_instance

end

end Work.Serre.RangeOne
