
import Mathlib
import Submission.Work.Drive.Mono.FiberModel.Defs
import Submission.Work.Drive.Mono.FiberModel.planar_basic
import Submission.Work.Drive.Mono.FiberModel.planarImage
import Submission.Work.Drive.Mono.WindowCase.tls_planar_facts
import Submission.Work.Drive.Mono.WindowCase.Defs
import Submission.Work.Drive.Mono.WindowCase.tls_planarPi_disc
import Submission.Work.Drive.Mono.WindowCase.tls_of_planarDisc


/-!
# The one-sphere window of a level of the tilted sweep

`Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam` is Pardon's open box with the closed tilted
slab cut away on the side `{ℓ < lam}`.  This file proves that in the *window* (`hwinP`, `hwinM`,
`hwallP`, `hwallM`) its frontier is a single embedded `2`-sphere.

The route is the fibre model (`Submission/Work/Drive/Mono/FiberModel`):

* `tlsProj v ℓ y = (⟪v,y⟫, ℓ y)` is the projection of the level; its fibres are the lines parallel to
  a fixed direction;
* the closure of the planar image `planarImage` of the level is a plane disc
  (`tls_planarDisc_of_window`, from the planar `Π`-region lemma `tls_planarPi_disc` plus the planar
  closure facts `tls_planar_facts`), and the level is the solid over that disc between the two
  heights `fMin`/`fMax` of the closed box;
* the frontier of that solid is an embedded sphere (`tls_of_planarDisc`, the assembly, via the
  hypograph crux `tls_hypograph_sphere`).

-/
open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.Drive.Mono.WindowCase

noncomputable section

/-- The first coordinate of the plane of the fibres, as a continuous linear functional. -/
def tlsFst : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (0 : Fin 2)).comp
    (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).toLinearMap).toContinuousLinearMap

/-- The second coordinate of the plane of the fibres, as a continuous linear functional. -/
def tlsSnd : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (1 : Fin 2)).comp
    (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).toLinearMap).toContinuousLinearMap

theorem tlsFst_apply (X : EuclideanSpace ℝ (Fin 2)) : tlsFst X = WithLp.ofLp X 0 := rfl

theorem tlsSnd_apply (X : EuclideanSpace ℝ (Fin 2)) : tlsSnd X = WithLp.ofLp X 1 := rfl

/-- The identification of the plane of the fibres with `ℝ × ℝ` by its two coordinates. -/
def tlsReveal : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ℝ × ℝ :=
  LinearEquiv.toContinuousLinearEquiv (𝕜 := ℝ)
    ((WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).trans
      (LinearEquiv.piFinTwo ℝ (fun _ : Fin 2 => ℝ)))

theorem tlsReveal_apply (X : EuclideanSpace ℝ (Fin 2)) :
    tlsReveal X = (tlsFst X, tlsSnd X) := rfl

theorem tlsReveal_fst (X : EuclideanSpace ℝ (Fin 2)) : (tlsReveal X).1 = tlsFst X := rfl

theorem tlsReveal_snd (X : EuclideanSpace ℝ (Fin 2)) : (tlsReveal X).2 = tlsSnd X := rfl

theorem tlsFst_tlsProj (v : R3) (ℓ : R3 →L[ℝ] ℝ) (y : R3) :
    tlsFst (tlsProj v ℓ y) = inner ℝ v y := by
  rw [tlsFst_apply, tlsProj_apply]; simp

theorem tlsSnd_tlsProj (v : R3) (ℓ : R3 →L[ℝ] ℝ) (y : R3) :
    tlsSnd (tlsProj v ℓ y) = ℓ y := by
  rw [tlsSnd_apply, tlsProj_apply]; simp

theorem tlsReveal_tlsProj (v : R3) (ℓ : R3 →L[ℝ] ℝ) (y : R3) :
    tlsReveal (tlsProj v ℓ y) = Work.Drive.Mono.FiberModel.levPair v ℓ y := by
  rw [tlsReveal_apply, tlsFst_tlsProj, tlsSnd_tlsProj, Work.Drive.Mono.FiberModel.levPair]

/-- **The planar `Π`-region of the window, seen in the plane of the fibres, is the closure of the
planar image of the level.** -/
theorem tls_piRegion_eq_planarImage (s : ℝ) (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u h lam : ℝ) (v : R3) (ℓ : R3 →L[ℝ] ℝ) (hh : 0 < h) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    (hv : v ≠ 0)
    (hwinP : ∃ y ∈ Submission.PBox s c σ, inner ℝ v c + u + h < inner ℝ v y)
    (hwinM : ∃ y ∈ Submission.PBox s c σ, inner ℝ v y < inner ℝ v c + u - h)
    (hwallP : ∃ y ∈ Submission.PBox s c σ, inner ℝ v c + u + h < inner ℝ v y ∧ lam < ℓ y)
    (hwallM : ∃ y ∈ Submission.PBox s c σ, inner ℝ v y < inner ℝ v c + u - h ∧ lam < ℓ y) :
    tlsReveal '' (closure (tlsProj v ℓ '' Submission.PBox s c σ) ∩
        ({x : EuclideanSpace ℝ (Fin 2) | Work.Drive.Mono.FiberModel.slabA u c v + h ≤ tlsFst x} ∪
         {x : EuclideanSpace ℝ (Fin 2) | tlsFst x ≤ Work.Drive.Mono.FiberModel.slabA u c v - h} ∪
         {x : EuclideanSpace ℝ (Fin 2) | lam ≤ tlsSnd x}))
      = closure (Work.Drive.Mono.FiberModel.planarImage s c σ u v h ℓ lam) := by
  have hQ : tlsReveal '' (tlsProj v ℓ '' Submission.PBox s c σ)
      = Work.Drive.Mono.FiberModel.levPair v ℓ '' Submission.PBox s c σ := by
    ext X
    constructor
    · rintro ⟨Y, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, (tlsReveal_tlsProj v ℓ y).symm⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨tlsProj v ℓ y, ⟨y, hy, rfl⟩, tlsReveal_tlsProj v ℓ y⟩
  have hPi : tlsReveal ''
        ({x : EuclideanSpace ℝ (Fin 2) | Work.Drive.Mono.FiberModel.slabA u c v + h ≤ tlsFst x} ∪
         {x : EuclideanSpace ℝ (Fin 2) | tlsFst x ≤ Work.Drive.Mono.FiberModel.slabA u c v - h} ∪
         {x : EuclideanSpace ℝ (Fin 2) | lam ≤ tlsSnd x})
      = ({X : ℝ × ℝ | Work.Drive.Mono.FiberModel.slabA u c v + h ≤ X.1} ∪
         {X : ℝ × ℝ | X.1 ≤ Work.Drive.Mono.FiberModel.slabA u c v - h} ∪
         {X : ℝ × ℝ | lam ≤ X.2}) := by
    have hfst' : ∀ Y : EuclideanSpace ℝ (Fin 2), (tlsReveal Y).1 = tlsFst Y := tlsReveal_fst
    have hsnd' : ∀ Y : EuclideanSpace ℝ (Fin 2), (tlsReveal Y).2 = tlsSnd Y := tlsReveal_snd
    ext X
    constructor
    · rintro ⟨Y, hY, rfl⟩
      rcases hY with (h | h) | h
      · exact Or.inl (Or.inl (by simpa [hfst' Y] using h))
      · exact Or.inl (Or.inr (by simpa [hfst' Y] using h))
      · exact Or.inr (by simpa [hsnd' Y] using h)
    · intro hX
      refine ⟨tlsReveal.symm X, ?_, tlsReveal.apply_symm_apply X⟩
      have h1 : tlsFst (tlsReveal.symm X) = X.1 := by
        rw [show tlsFst (tlsReveal.symm X) = (tlsReveal (tlsReveal.symm X)).1 from (hfst' _).symm,
          tlsReveal.apply_symm_apply]
      have h2 : tlsSnd (tlsReveal.symm X) = X.2 := by
        rw [show tlsSnd (tlsReveal.symm X) = (tlsReveal (tlsReveal.symm X)).2 from (hsnd' _).symm,
          tlsReveal.apply_symm_apply]
      rcases hX with (h | h) | h
      · exact Or.inl (Or.inl (by simpa [h1] using h))
      · exact Or.inl (Or.inr (by simpa [h1] using h))
      · exact Or.inr (by simpa [h2] using h)
  rw [Set.image_inter tlsReveal.injective, ContinuousLinearEquiv.image_closure, hQ, hPi,
    ← Work.Drive.Mono.FiberModel.boxShadow_eq_closure_image,
    ← (Work.Drive.Mono.WindowCase.tls_planar_facts s hs c σ u h lam v ℓ hh hℓv hℓne hv
      hwinP hwinM hwallP hwallM).2]

/-- **The closure of the planar image of a level of the window is a plane disc**, i.e. the
`hZdisc` input of the assembly: the disc parametrisation produced by the planar `Π`-region lemma,
transported to the plane of the coordinates of the shadow. -/
theorem tls_planarDisc_of_window (s : ℝ) (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u h lam : ℝ) (v : R3) (ℓ : R3 →L[ℝ] ℝ) (hh : 0 < h) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    (hv : v ≠ 0)
    (hwinP : ∃ y ∈ Submission.PBox s c σ, inner ℝ v c + u + h < inner ℝ v y)
    (hwinM : ∃ y ∈ Submission.PBox s c σ, inner ℝ v y < inner ℝ v c + u - h)
    (hwallP : ∃ y ∈ Submission.PBox s c σ, inner ℝ v c + u + h < inner ℝ v y ∧ lam < ℓ y)
    (hwallM : ∃ y ∈ Submission.PBox s c σ, inner ℝ v y < inner ℝ v c + u - h ∧ lam < ℓ y) :
    ∃ e : C(Metric.closedBall (0 : ℂ) 1, ℝ × ℝ), Function.Injective e ∧
      Set.range e = closure (Work.Drive.Mono.FiberModel.planarImage s c σ u v h ℓ lam) ∧
      Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) =
        frontier (closure (Work.Drive.Mono.FiberModel.planarImage s c σ u v h ℓ lam)) := by
  have hsurj : Function.Surjective (tlsProj v ℓ) := tlsProj_surjective hv hℓv hℓne
  have hwallP' := hwallP
  have hwallM' := hwallM
  obtain ⟨yP, hyP, hyPf, hyPl⟩ := hwallP'
  obtain ⟨yM, hyM, hyMf, hyMl⟩ := hwallM'
  obtain ⟨e₀, hI, hR, hB⟩ :=
    tls_planarPi_disc (a := Work.Drive.Mono.FiberModel.slabA u c v) (h := h) hh
      (tlsProj v ℓ '' Submission.PBox s c σ)
      ((Work.Topology.SphereSlicing.convex_PBox s c σ).linear_image (tlsProj v ℓ).toLinearMap)
      (ContinuousLinearMap.isOpenMap (tlsProj v ℓ) hsurj _
        (Work.Topology.SphereSlicing.isOpen_PBox s c σ))
      ((Work.Drive.Mono.FiberModel.isBounded_PBox s c σ).image (tlsProj v ℓ))
      tlsFst tlsSnd
      ⟨tlsProj v ℓ yP, ⟨yP, hyP, rfl⟩, by
        rw [tlsFst_tlsProj]; exact hyPf, by
        rw [tlsSnd_tlsProj]; exact hyPl⟩
      ⟨tlsProj v ℓ yM, ⟨yM, hyM, rfl⟩, by
        rw [tlsFst_tlsProj]; exact hyMf, by
        rw [tlsSnd_tlsProj]; exact hyMl⟩
  have hkey := tls_piRegion_eq_planarImage s hs c σ u h lam v ℓ hh hℓv hℓne hv
    hwinP hwinM hwallP hwallM
  have hr : Set.range (fun z : Metric.closedBall (0 : ℂ) 1 => tlsReveal (e₀ z))
      = tlsReveal '' Set.range (⇑e₀) := by
    ext X
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨e₀ z, ⟨z, rfl⟩, rfl⟩
    · rintro ⟨Y, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, rfl⟩
  have hbd : Set.range (fun θ : ℝ => tlsReveal (e₀ (Work.CoreTopology.circlePoint θ)))
      = tlsReveal '' Set.range (e₀ ∘ Work.CoreTopology.circlePoint) := by
    ext X
    constructor
    · rintro ⟨θ, rfl⟩
      exact ⟨e₀ (Work.CoreTopology.circlePoint θ), ⟨θ, rfl⟩, rfl⟩
    · rintro ⟨Y, ⟨θ, rfl⟩, rfl⟩
      exact ⟨θ, rfl⟩
  refine ⟨⟨fun z => tlsReveal (e₀ z), tlsReveal.continuous.comp e₀.continuous⟩, ?_, ?_, ?_⟩
  · exact fun z z' h => hI (tlsReveal.injective h)
  · change Set.range (fun z : Metric.closedBall (0 : ℂ) 1 => tlsReveal (e₀ z))
      = closure (Work.Drive.Mono.FiberModel.planarImage s c σ u v h ℓ lam)
    rw [hr, hR, hkey]
  · change Set.range (fun θ : ℝ => tlsReveal (e₀ (Work.CoreTopology.circlePoint θ)))
      = frontier (closure (Work.Drive.Mono.FiberModel.planarImage s c σ u v h ℓ lam))
    have hB' : Set.range (⇑e₀ ∘ Work.CoreTopology.circlePoint) =
        frontier (closure (tlsProj v ℓ '' Submission.PBox s c σ) ∩
          ({x : EuclideanSpace ℝ (Fin 2) | Work.Drive.Mono.FiberModel.slabA u c v + h ≤ tlsFst x} ∪
           {x : EuclideanSpace ℝ (Fin 2) | tlsFst x ≤ Work.Drive.Mono.FiberModel.slabA u c v - h} ∪
           {x : EuclideanSpace ℝ (Fin 2) | lam ≤ tlsSnd x})) := hB
    have hfr : ⇑tlsReveal '' frontier (closure (tlsProj v ℓ '' Submission.PBox s c σ) ∩
          ({x : EuclideanSpace ℝ (Fin 2) | Work.Drive.Mono.FiberModel.slabA u c v + h ≤ tlsFst x} ∪
           {x : EuclideanSpace ℝ (Fin 2) | tlsFst x ≤ Work.Drive.Mono.FiberModel.slabA u c v - h} ∪
           {x : EuclideanSpace ℝ (Fin 2) | lam ≤ tlsSnd x}))
        = frontier (⇑tlsReveal '' (closure (tlsProj v ℓ '' Submission.PBox s c σ) ∩
          ({x : EuclideanSpace ℝ (Fin 2) | Work.Drive.Mono.FiberModel.slabA u c v + h ≤ tlsFst x} ∪
           {x : EuclideanSpace ℝ (Fin 2) | tlsFst x ≤ Work.Drive.Mono.FiberModel.slabA u c v - h} ∪
           {x : EuclideanSpace ℝ (Fin 2) | lam ≤ tlsSnd x}))) :=
      Homeomorph.image_frontier (ContinuousLinearEquiv.toHomeomorph tlsReveal) _
    rw [hbd, hB', hfr, hkey]

/-- **The one-sphere window of a level of the tilted sweep.** -/
theorem tls_window_oneSphere
    (s : ℝ) (hs : 0 < s)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (u h lam : ℝ)
    (v : LeanEval.KnotTheory.PardonDistortion.R3)
    (ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ)
    (hh : 0 < h) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    (hedge : ∀ (i : Fin 3) (ε : Fin 3 → Bool),
      lam = ℓ (WithLp.toLp 2 (fun k : Fin 3 => c k +
        (if k = σ i then (0 : ℝ) else
          (if ε (σ.symm k) then 1 else -1) * Submission.boxSide (σ.symm k) * s))) →
      ℓ (EuclideanSpace.single (σ i) (1 : ℝ)) ≠ 0)
    (hvertex : ∀ ε : Fin 3 → Bool,
      lam ≠ ℓ (WithLp.toLp 2 (fun j : Fin 3 => c j +
        (if ε (σ.symm j) then 1 else -1) * Submission.boxSide (σ.symm j) * s)))
    (hwallP : ∃ y ∈ Submission.PBox s c σ,
      inner ℝ v c + u + h < inner ℝ v y ∧ lam < ℓ y)
    (hwallM : ∃ y ∈ Submission.PBox s c σ,
      inner ℝ v y < inner ℝ v c + u - h ∧ lam < ℓ y)
    (hwinP : ∃ y ∈ Submission.PBox s c σ, inner ℝ v c + u + h < inner ℝ v y)
    (hwinM : ∃ y ∈ Submission.PBox s c σ, inner ℝ v y < inner ℝ v c + u - h) :
    Work.InnermostDisk.IsEmbeddedSphere
      (frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) := by
  have hv : v ≠ 0 := by
    intro hv0
    obtain ⟨y, -, hy⟩ := hwinP
    obtain ⟨y', -, hy'⟩ := hwinM
    rw [hv0, inner_zero_left, inner_zero_left] at hy hy'
    linarith
  exact tls_of_planarDisc s hs c σ u h lam v ℓ hh hℓv hℓne hv hwinP hwinM hwallP hwallM
    (tls_planarDisc_of_window s hs c σ u h lam v ℓ hh hℓv hℓne hv hwinP hwinM hwallP hwallM)

end

end Work.Drive.Mono.WindowCase
