import Mathlib
import Submission.Work.ThomBordism.NullBord.lebesgue

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The image of a compact smoothly immersed manifold is a Euclidean neighbourhood retract

`Work.ThomBordism.NullBord.enrRetraction`: given a compact `T²` manifold `X` (with corners, model
`ℝ^9₊`) and a *closed embedding* `e : X → ℝ^N` which is *locally nearest-point unique* (at every
`x₀` there are an open neighbourhood `W` of `x₀` and `ν > 0` such that a nearest point `x ∈ W` of a
point `y` with `dist y (e x) < ν` is the unique nearest point among the points of `W`), the image
`e '' X` is a retract of an open neighbourhood of itself.

The proof uses only compactness, the closed embedding and this local uniqueness:

* if `y` is close enough to the image then its nearest point is unique: otherwise there are `yₙ`
  with `dist (yₙ, range e) → 0` and two distinct nearest points `e xₙ ≠ e x'ₙ`; passing to
  subsequences one gets `xₙ → x` and `x'ₙ → x` for the *same* `x` (because `‖e xₙ - e x'ₙ‖ ≤
  2 dist (yₙ, range e) → 0` and `e` is injective), and for large `n` both `xₙ` and `x'ₙ` lie in the
  neighbourhood `W` given by the local uniqueness at `x`, giving `xₙ = x'ₙ`, a contradiction;
* the nearest point map is continuous on the open set `U = {y | dist y (range e) < δ}`: if `yₙ → y`
  then any subsequential limit of the (compactly many) nearest points is a nearest point of `y` by
  continuity of the distance, hence equal to the (unique) nearest point of `y`;
* every point of the image is its own (unique) nearest point, so the map fixes `range e`. -/

open scoped Manifold ContDiff
open Set Metric

namespace Work.ThomBordism.NullBord

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace 9) X]
  [IsManifold (modelWithCornersEuclideanHalfSpace 9) ∞ X]

/-- **The image of a compact closed-embedded manifold is a Euclidean neighbourhood retract**, given
the local uniqueness of the nearest point. -/
theorem enrRetraction [T2Space X] [CompactSpace X] {N : ℕ}
    {e : X → EuclideanSpace ℝ (Fin N)} (hemb : Topology.IsClosedEmbedding e)
    (huniq : ∀ x₀ : X, ∃ (W : Set X) (_ : IsOpen W) (_ : x₀ ∈ W) (ν : ℝ) (_ : 0 < ν),
      ∀ x ∈ W, ∀ y : EuclideanSpace ℝ (Fin N),
        (∀ x'' : X, dist y (e x'') ≥ dist y (e x)) → dist y (e x) < ν →
          ∀ x' ∈ W, dist y (e x') ≤ dist y (e x) → x' = x) :
    ∃ (U : Set (EuclideanSpace ℝ (Fin N))) (_ : IsOpen U) (hrange : Set.range e ⊆ U),
      ∃ r : ↥U → ↥(Set.range e), Continuous r ∧ ∀ x : ↥(Set.range e), r ⟨x.1, hrange x.2⟩ = x := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · -- empty `X`
    refine ⟨∅, isOpen_empty, ?_, ?_⟩
    · rintro p ⟨x, -⟩; exact isEmptyElim x
    · haveI : IsEmpty ↥(Set.range e) :=
        ⟨fun y => y.2.elim fun x _ => isEmptyElim x⟩
      exact ⟨fun y => y.2.elim, continuous_iff_continuousAt.mpr fun y => y.2.elim,
        fun y => isEmptyElim y⟩
  set K : Set (EuclideanSpace ℝ (Fin N)) := Set.range e with hKdef
  have hKcompact : IsCompact K := isCompact_range hemb.continuous
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hKcompact
  choose W hWopen hWmem ν hνpos hWuniq using huniq
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x : X => W x) (fun x => hWopen x)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hWmem x⟩)
  have hcovX : ∀ z : X, ∃ i : {x // x ∈ s}, z ∈ W i.1 := by
    intro z
    have hz : z ∈ ⋃ x ∈ s, W x := hs (mem_univ z)
    rw [Set.mem_iUnion₂] at hz
    exact ⟨⟨hz.choose, hz.choose_spec.1⟩, hz.choose_spec.2⟩
  haveI : Nonempty {x // x ∈ s} := by
    obtain ⟨i, -⟩ := hcovX (Classical.arbitrary X)
    exact ⟨i⟩
  -- the corresponding open cover of `K`
  let emb : X → ↥K := fun x => ⟨e x, Set.mem_range_self x⟩
  let Kc : {x // x ∈ s} → Set ↥K := fun i => emb '' (W i.1)
  have hKcopen : ∀ i, IsOpen (Kc i) := by
    intro i
    have hcontemb : Continuous emb := hemb.continuous.subtype_mk _
    have hclosed : IsClosed (emb '' (W i.1)ᶜ) :=
      ((hWopen i.1).isClosed_compl.isCompact.image hcontemb).isClosed
    have hset : Kc i = (emb '' (W i.1)ᶜ)ᶜ := by
      ext p
      constructor
      · rintro ⟨x, hx, hxeq⟩ ⟨y, hy, hyeq⟩
        have hxy : x = y := hemb.injective (Subtype.ext_iff.mp (hxeq.trans hyeq.symm))
        exact hy (hxy ▸ hx)
      · intro hp
        obtain ⟨x, hxeq⟩ := p.2
        refine ⟨x, ?_, Subtype.ext hxeq⟩
        by_contra hx
        exact hp ⟨x, hx, Subtype.ext hxeq⟩
    rw [hset]
    exact hclosed.isOpen_compl
  have hKccov : ∀ p : ↥K, ∃ i, p ∈ Kc i := by
    rintro ⟨p, x, rfl⟩
    obtain ⟨i, hi⟩ := hcovX x
    exact ⟨i, x, hi, rfl⟩
  -- the Lebesgue number of this cover
  obtain ⟨η, hηpos, hη⟩ := exists_lebesgue_number Kc hKcopen hKccov
  -- the uniform threshold
  set νm : ℝ := (Finset.univ : Finset {x // x ∈ s}).inf' Finset.univ_nonempty
    (fun i => ν i.1) with hνmdef
  have hνmpos : 0 < νm := by
    rw [hνmdef, Finset.lt_inf'_iff]
    intro i _
    exact hνpos i.1
  have hνmle : ∀ i : {x // x ∈ s}, νm ≤ ν i.1 := by
    intro i
    rw [hνmdef]
    exact Finset.inf'_le _ (Finset.mem_univ i)
  set δ : ℝ := min (η / 2) νm with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) hνmpos
  have hδη : δ ≤ η / 2 := le_trans (min_le_left _ _) le_rfl
  have hδν : δ ≤ νm := min_le_right _ _
  -- global uniqueness of the nearest point close to `K`
  have hglob : ∀ y : EuclideanSpace ℝ (Fin N), Metric.infDist y K < δ →
      ∃! x : X, ∀ x' : X, dist y (e x) ≤ dist y (e x') := by
    intro y hy
    have hne : K.Nonempty := ⟨e (Classical.arbitrary X), Set.mem_range_self _⟩
    obtain ⟨p, hpK, hp⟩ := hKcompact.exists_infDist_eq_dist hne y
    obtain ⟨x₀, rfl⟩ := hpK
    have hx₀ : ∀ x' : X, dist y (e x₀) ≤ dist y (e x') := by
      intro x'
      rw [← hp]
      exact Metric.infDist_le_dist_of_mem (Set.mem_range_self x')
    refine ⟨x₀, hx₀, ?_⟩
    intro x hx
    by_contra hne'
    have hclose : dist (e x₀) (e x) ≤ 2 * Metric.infDist y K := by
      have h2 : dist (e x₀) y = Metric.infDist y K := by rw [dist_comm, hp]
      have h3 : dist y (e x) ≤ Metric.infDist y K := by rw [hp]; exact hx x₀
      calc dist (e x₀) (e x) ≤ dist (e x₀) y + dist y (e x) := dist_triangle _ _ _
        _ ≤ Metric.infDist y K + Metric.infDist y K := by rw [h2]; linarith
        _ = 2 * Metric.infDist y K := by ring
    have hyη : Metric.infDist y K < η / 2 := lt_of_lt_of_le hy hδη
    have hlt : dist (e x₀) (e x) < η := by linarith
    obtain ⟨i, hi, hi'⟩ := hη (emb x₀) (emb x) (by simpa [Subtype.dist_eq, emb] using hlt)
    obtain ⟨z, hzW, hze⟩ := hi
    obtain ⟨z', hz'W, hz'e⟩ := hi'
    have hz_eq : z = x₀ := hemb.injective (by simpa [emb] using Subtype.ext_iff.mp hze)
    have hz'_eq : z' = x := hemb.injective (by simpa [emb] using Subtype.ext_iff.mp hz'e)
    have hx₀W : x₀ ∈ W i.1 := hz_eq ▸ hzW
    have hxW : x ∈ W i.1 := hz'_eq ▸ hz'W
    have hνi : Metric.infDist y K < ν i.1 := lt_of_lt_of_le hy (le_trans hδν (hνmle i))
    have hνi' : dist y (e x₀) < ν i.1 := by rw [← hp]; exact hνi
    exact hne' (hWuniq i.1 x₀ hx₀W y hx₀ hνi' x hxW (hx x₀))
  -- the nearest point map
  set U : Set (EuclideanSpace ℝ (Fin N)) := {y | Metric.infDist y K < δ} with hUdef
  have hUopen : IsOpen U := isOpen_lt (continuous_infDist_pt K) continuous_const
  have hKU : K ⊆ U := by
    rintro p ⟨x, rfl⟩
    have h0 : Metric.infDist (e x) K = 0 := Metric.infDist_zero_of_mem (Set.mem_range_self x)
    rw [hUdef, Set.mem_setOf_eq, h0]
    exact hδpos
  let xsel : ↥U → X := fun y => Classical.choose (hglob y y.2)
  have hxsel : ∀ y : ↥U, ∀ x' : X, dist (y : EuclideanSpace ℝ (Fin N)) (e (xsel y)) ≤
      dist (y : EuclideanSpace ℝ (Fin N)) (e x') := fun y => (Classical.choose_spec (hglob y y.2)).1
  have hxsel_unique : ∀ y : ↥U, ∀ x : X, (∀ x' : X,
      dist (y : EuclideanSpace ℝ (Fin N)) (e x) ≤ dist (y : EuclideanSpace ℝ (Fin N)) (e x')) →
      x = xsel y := fun y x hx => (Classical.choose_spec (hglob y y.2)).2 x hx
  -- the graph of the selection is closed
  have hgraph : IsClosed {p : ↥U × ↥K | ∀ x' : X,
      dist (p.1 : EuclideanSpace ℝ (Fin N)) (p.2 : EuclideanSpace ℝ (Fin N)) ≤
        dist (p.1 : EuclideanSpace ℝ (Fin N)) (e x')} := by
    have hset : {p : ↥U × ↥K | ∀ x' : X, dist (p.1 : EuclideanSpace ℝ (Fin N))
          (p.2 : EuclideanSpace ℝ (Fin N)) ≤ dist (p.1 : EuclideanSpace ℝ (Fin N)) (e x')}
        = ⋂ x' : X, {p : ↥U × ↥K | dist (p.1 : EuclideanSpace ℝ (Fin N))
            (p.2 : EuclideanSpace ℝ (Fin N)) ≤ dist (p.1 : EuclideanSpace ℝ (Fin N)) (e x')} := by
      ext p; simp [Set.mem_iInter]
    rw [hset]
    exact isClosed_iInter fun x' => isClosed_le
      ((continuous_subtype_val.comp continuous_fst).dist
        (continuous_subtype_val.comp continuous_snd))
      ((continuous_subtype_val.comp continuous_fst).dist continuous_const)
  -- continuity, via the closed graph and compactness of `X`
  have hcont : Continuous (fun y : ↥U => (⟨e (xsel y), Set.mem_range_self _⟩ : ↥K)) := by
    rw [continuous_iff_isClosed]
    intro C hC
    have hpre : (fun y : ↥U => (⟨e (xsel y), Set.mem_range_self _⟩ : ↥K)) ⁻¹' C
        = Prod.fst '' ({p : ↥U × ↥K | ∀ x' : X,
            dist (p.1 : EuclideanSpace ℝ (Fin N)) (p.2 : EuclideanSpace ℝ (Fin N)) ≤
              dist (p.1 : EuclideanSpace ℝ (Fin N)) (e x')} ∩ (Set.univ ×ˢ C)) := by
      ext y
      constructor
      · intro hy
        exact ⟨(y, ⟨e (xsel y), Set.mem_range_self _⟩), ⟨hxsel y, mem_univ _, hy⟩, rfl⟩
      · rintro ⟨p, ⟨hp, -, hpC⟩, rfl⟩
        have h2 : (p.2 : EuclideanSpace ℝ (Fin N)) = e (xsel p.1) := by
          obtain ⟨z, hz⟩ := p.2.2
          have hz' : z = xsel p.1 := by
            apply hxsel_unique p.1 z
            intro x'
            rw [hz]
            exact hp x'
          rw [← hz, hz']
        rw [show p.2 = (⟨e (xsel p.1), Set.mem_range_self _⟩ : ↥K) from Subtype.ext h2] at hpC
        exact hpC
    rw [hpre]
    exact isClosedMap_fst_of_compactSpace _
      (hgraph.inter (isClosed_univ.prod hC))
  refine ⟨U, hUopen, hKU, fun y => (⟨e (xsel y), Set.mem_range_self _⟩ : ↥K), hcont, ?_⟩
  rintro ⟨p, xp, rfl⟩
  apply Subtype.ext
  have hxsel0 : ∀ (h : e xp ∈ U), e (xsel ⟨e xp, h⟩) = e xp := by
    intro h
    rw [(hxsel_unique ⟨e xp, h⟩ xp (fun x' => by simp)).symm]
  exact hxsel0 _

end

end Work.ThomBordism.NullBord
