import Mathlib
import Submission.Work.Serre.DiscPair.cylBotTrimDefs
import Submission.Work.Serre.cylCollarShrink
import Submission.Work.Thom.relCohMap_homotopic

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open scoped Topology unitInterval
open CategoryTheory

namespace Work.Serre.DiscPair

/-- **Collar-shrink half of the bottom-copy trimming.**  With `N = {y : ↥(trimAp q S V) | (y : cyl q)
∈ cylCollar q}` the collar part of `trimAp q S V = (cylBot q ∪ cylPre q S) ∩ cylPre q V`, the
relative cohomology of `(N, N ∩ cylPre q S)` is that of the bottom copy `trimC q V = cylBot q ∩
cylPre q V` over `V`, again relative to `cylPre q S`.

Intended proof (the collar shrink, then a splitting argument).  Define `H_s : N → N` for
`s : unitInterval` by `H_s y = cylShrink q s ⟨(y : cyl q), y.2⟩`, using that `s ↦ H_s y` is
continuous in `s`.  Facts: `H_s` preserves `cylPre q S` (`Work.Serre.cylRetract_cylShrink`), `H_s`
fixes the points of `cylBot q` (`Work.Serre.cylShrink_fixes_bot`), `H_0 = id` and `H_1` lands in
`cylBot q` (`Work.Serre.cylShrink_one_mem_cylBot`), and `H_1` also preserves `cylPre q V`, so `H_1`
lands in `trimC q V`.  Thus `H` is a homotopy of pairs from the identity of `N` to
`iC.comp r`, where `r : N → ↥(trimC q V)` is `H_1` and `iC` is the inclusion; and `r.comp iC =
id` because `cylShrink q 1` fixes the bottom copy.  Applying `Work.Thom.relCohMap_homotopic` to
`H` (with the relative set `{y : N | (y : cyl q) ∈ cylPre q S}` on both sides) gives
`𝟙 = relCohMap (iC.comp r)`, and `Work.Thom.relCohMap_compA` turns the two composites into
`(relCohMap r) ∘ (relCohMap iC) = 𝟙` and `(relCohMap iC) ∘ (relCohMap r) = 𝟙`; hence
`relCohMap iC` is the required isomorphism.  (`hSV` is not needed here.) -/
theorem cylBotTrimShrink {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) (S V : Set B) (hSV : S ⊆ V) (n : ℕ) :
    Nonempty (Work.Thom.RelCoh ℚ n
        ↥{y : ↥(Work.Serre.DiscPair.trimAp q S V) |
            (y : Work.Serre.cyl q) ∈ Work.Serre.cylCollar q}
        {y : ↥{y : ↥(Work.Serre.DiscPair.trimAp q S V) |
              (y : Work.Serre.cyl q) ∈ Work.Serre.cylCollar q} |
          (y : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S}
      ≅ Work.Thom.RelCoh ℚ n ↥(Work.Serre.DiscPair.trimC q V)
        {y : ↥(Work.Serre.DiscPair.trimC q V) |
          (y : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S}) := by
  let N : Set ↥(trimAp q S V) := {y | (y : cyl q) ∈ cylCollar q}
  let AN : Set ↥N := {y | (y : cyl q) ∈ cylPre q S}
  let AC : Set ↥(trimC q V) := {y : ↥(trimC q V) | (y : cyl q) ∈ cylPre q S}
  show Nonempty (Work.Thom.RelCoh ℚ n ↥N AN ≅ Work.Thom.RelCoh ℚ n ↥(trimC q V) AC)
  -- the collar coordinate of a point of `N`
  let cp : ↥N → ↥(cylCollar q) := fun y => ⟨(y : cyl q), y.2⟩
  have hcp : Continuous cp := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.comp continuous_subtype_val
  have hAp_mem : ∀ y : ↥N, (cp y : cyl q) ∈ trimAp q S V := fun y => (y : ↥(trimAp q S V)).2
  -- the shrink preserves `trimAp q S V`
  have shr_mem : ∀ (s : unitInterval) (z : ↥(cylCollar q)), (z : cyl q) ∈ trimAp q S V →
      ((cylShrink q s z : ↥(cylCollar q)) : cyl q) ∈ trimAp q S V := by
    intro s z hz
    rw [mem_trimAp] at hz ⊢
    obtain ⟨h1, h2⟩ := hz
    refine ⟨?_, ?_⟩
    · rcases h1 with hb | hp
      · left
        rw [Work.Serre.cylShrink_fixes_bot q s hb]
        exact hb
      · right
        have hp' : (cylRetract q) (z : cyl q) ∈ S := hp
        change (cylRetract q) ((cylShrink q s z : ↥(cylCollar q)) : cyl q) ∈ S
        rw [Work.Serre.cylRetract_cylShrink q s z]
        exact hp'
    · have h2' : (cylRetract q) (z : cyl q) ∈ V := h2
      change (cylRetract q) ((cylShrink q s z : ↥(cylCollar q)) : cyl q) ∈ V
      rw [Work.Serre.cylRetract_cylShrink q s z]
      exact h2'
  -- joint continuity of the shrink, read off the collar shrink homotopy
  have hcontShrinkHom : Continuous fun p : unitInterval × ↥N =>
      (Work.Serre.cylShrinkHomotopy q) (p.1, cp p.2) :=
    (Work.Serre.cylShrinkHomotopy q).toContinuousMap.continuous.comp
      (continuous_fst.prodMk (hcp.comp continuous_snd))
  have hcontShrink : Continuous fun p : unitInterval × ↥N =>
      (cylShrink q p.1 (cp p.2) : ↥(cylCollar q)) :=
    hcontShrinkHom.congr (fun p => Work.Serre.cylShrinkHomotopy_apply q p.1 (cp p.2))
  have hcontv : Continuous fun p : unitInterval × ↥N => (cylShrink q p.1 (cp p.2) : cyl q) :=
    continuous_subtype_val.comp hcontShrink
  have hrc : Continuous fun y : ↥N => (cylShrink q 1 (cp y) : cyl q) :=
    continuous_subtype_val.comp ((Work.Serre.cylShrink q 1).continuous.comp hcp)
  -- the retraction `r : N → ↥(trimC q V)`, the shrink at time `1`
  have rmem : ∀ y : ↥N, (cylShrink q 1 (cp y) : cyl q) ∈ trimC q V := fun y =>
    ⟨Work.Serre.cylShrink_one_mem_cylBot q (cp y),
      show (cylRetract q) ((cylShrink q 1 (cp y) : ↥(cylCollar q)) : cyl q) ∈ V from by
        rw [Work.Serre.cylRetract_cylShrink q 1 (cp y)]
        exact (y : ↥(trimAp q S V)).2.2⟩
  let r : C(↥N, ↥(trimC q V)) :=
    ⟨fun y => ⟨(cylShrink q 1 (cp y) : cyl q), rmem y⟩,
     Continuous.subtype_mk hrc rmem⟩
  -- the inclusion `iC : ↥(trimC q V) → N`
  have imem : ∀ b : ↥(trimC q V), (b : cyl q) ∈ trimAp q S V := fun b => by
    rw [mem_trimAp]
    exact ⟨Or.inl b.2.1, b.2.2⟩
  have icol : ∀ b : ↥(trimC q V), (b : cyl q) ∈ cylCollar q := fun b =>
    cylBot_subset_cylCollar q b.2.1
  let iC : C(↥(trimC q V), ↥N) :=
    ⟨fun b => ⟨⟨(b : cyl q), imem b⟩, icol b⟩,
     Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val (fun b => imem b))
       (fun b => icol b)⟩
  -- the homotopy `H_s`
  have HNmem : ∀ p : unitInterval × ↥N, (cylShrink q p.1 (cp p.2) : cyl q) ∈ trimAp q S V :=
    fun p => shr_mem p.1 (cp p.2) (hAp_mem p.2)
  have HNcol : ∀ p : unitInterval × ↥N, (cylShrink q p.1 (cp p.2) : cyl q) ∈ cylCollar q :=
    fun p => (cylShrink q p.1 (cp p.2) : ↥(cylCollar q)).2
  have hNc : Continuous fun p : unitInterval × ↥N =>
      (⟨(cylShrink q p.1 (cp p.2) : cyl q), HNmem p⟩ : ↥(trimAp q S V)) :=
    Continuous.subtype_mk hcontv HNmem
  let HN : C(unitInterval × ↥N, ↥N) :=
    ⟨fun p => ⟨⟨(cylShrink q p.1 (cp p.2) : cyl q), HNmem p⟩, HNcol p⟩,
     Continuous.subtype_mk hNc HNcol⟩
  have h0 : ∀ z : ↥(cylCollar q), cylShrink q 0 z = z := fun z =>
    (Work.Serre.cylShrinkHomotopy_apply q 0 z).symm.trans
      ((Work.Serre.cylShrinkHomotopy q).map_zero_left z)
  let Hhom : ContinuousMap.Homotopy (ContinuousMap.id ↥N) (iC.comp r) :=
    { toContinuousMap := HN
      map_zero_left := fun y => by
        apply Subtype.ext
        apply Subtype.ext
        show ((cylShrink q 0 (cp y) : ↥(cylCollar q)) : cyl q) = (y : cyl q)
        rw [h0 (cp y)]
      map_one_left := fun y => by
        apply Subtype.ext
        apply Subtype.ext
        show ((cylShrink q 1 (cp y) : ↥(cylCollar q)) : cyl q) = (r y : cyl q)
        rfl }
  -- the pair conditions
  have hr : ∀ y ∈ AN, r y ∈ AC := fun y hy => by
    change (cylRetract q) ((cylShrink q 1 (cp y) : ↥(cylCollar q)) : cyl q) ∈ S
    rw [Work.Serre.cylRetract_cylShrink q 1 (cp y)]
    exact hy
  have hi : ∀ b ∈ AC, iC b ∈ AN := fun b hb => by
    change (b : cyl q) ∈ cylPre q S
    exact hb
  have hgf : ∀ x ∈ AN, iC (r x) ∈ AN := fun x hx => hi (r x) (hr x hx)
  have hid : ∀ x ∈ AN, (ContinuousMap.id ↥N) x ∈ AN := fun x hx => hx
  have hg : ∀ x ∈ AN, (iC.comp r) x ∈ AN := fun x hx => hgf x hx
  have hH : ∀ (t : unitInterval) (x : ↥N), x ∈ AN → Hhom (t, x) ∈ AN := fun t x hx => by
    change (cylRetract q) ((cylShrink q t (cp x) : ↥(cylCollar q)) : cyl q) ∈ S
    rw [Work.Serre.cylRetract_cylShrink q t (cp x)]
    exact hx
  -- the homotopy of pairs gives `𝟙 = relCohMap (iC.comp r)`
  have hhom := Work.Thom.relCohMap_homotopic AN AN hid hg Hhom hH ℚ n
  have hhom' : (𝟙 (Work.Thom.RelCoh ℚ n ↥N AN)) =
      Work.Thom.relCohMap (iC.comp r) AN AN hg ℚ n := by
    rw [← Work.Thom.relCohMap_id' AN ℚ n]
    exact hhom
  -- the two composite identities
  have hcomp_hom : Work.Thom.relCohMap iC AC AN hi ℚ n ≫ Work.Thom.relCohMap r AN AC hr ℚ n
      = 𝟙 (Work.Thom.RelCoh ℚ n ↥N AN) := by
    rw [Work.Thom.relCohMap_comp' AN AC AN r iC hr hi hgf ℚ n]
    exact hhom'.symm
  have hric : r.comp iC = ContinuousMap.id ↥(trimC q V) := by
    apply ContinuousMap.ext
    intro b
    apply Subtype.ext
    show (cylShrink q 1 (cp (iC b)) : cyl q) = (b : cyl q)
    rw [Work.Serre.cylShrink_fixes_bot q 1 (y := cp (iC b)) b.2.1]
    rfl
  have hgf' : ∀ x ∈ AC, r (iC x) ∈ AC := fun x hx => by
    change (cylRetract q) ((cylShrink q 1 (cp (iC x)) : ↥(cylCollar q)) : cyl q) ∈ S
    rw [Work.Serre.cylRetract_cylShrink q 1 (cp (iC x))]
    change (cylRetract q) (x : cyl q) ∈ S
    exact hx
  have hcomp_inv : Work.Thom.relCohMap r AN AC hr ℚ n ≫ Work.Thom.relCohMap iC AC AN hi ℚ n
      = 𝟙 (Work.Thom.RelCoh ℚ n ↥(trimC q V) AC) := by
    rw [Work.Thom.relCohMap_comp' AC AN AC iC r hi hr hgf' ℚ n,
      Work.Thom.relCohMap_congr' AC AC hric hgf' (fun x hx => hx) ℚ n,
      Work.Thom.relCohMap_id' AC ℚ n]
  exact ⟨{ hom := Work.Thom.relCohMap iC AC AN hi ℚ n
           inv := Work.Thom.relCohMap r AN AC hr ℚ n
           hom_inv_id := hcomp_hom
           inv_hom_id := hcomp_inv }⟩

end Work.Serre.DiscPair
