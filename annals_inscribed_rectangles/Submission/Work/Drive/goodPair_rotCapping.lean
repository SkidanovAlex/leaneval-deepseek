import Mathlib
import Submission.Work.Drive.sideGermDefs

/-!
# `GoodPair` is invariant under a common rotation of the two charts

The germ route (`Submission/Work/Drive/sideGermDefs.lean`) defines its regularity condition for a
*pair* of plane presentations — `Work.Drive.GoodPair Q₁ Q₂ c` — as the conjunction of five clauses:

1. `Q₁` is `C^∞`,
2. `Q₂` is `C^∞`,
3. the meet set `coreMeet Q₁ c (diskPlane Q₂)` of the core loop of `Q₁` with the clamped sweep of the
   disk presentation of `Q₂` is **finite**,
4. every meet is **interior** in the parameter box `[0,1] × unitBox 2 ⊂ ℝ × ℝ³`,
5. the loop and the sweep are **transverse** at every meet (in the intrinsic form
   `range (mfderiv loop) ⊔ range (mfderiv sweep) = ⊤`).

The design's `GoodAt Ξ Q c w t` compares the perturbed chart `Ξ t.1 ∘ Q` with the *rotated*
perturbed chart `rotCapping w ∘ Ξ t.2 ∘ Q`, and the germ `sideGerm` is a limit over such
configurations — so the route needs `GoodPair` to be stable under post-composing **both** charts with
one and the same rotation `rotCapping u` of the capping space.  That is this file's theorem:

> `Work.Drive.goodPair_rotCapping` — `GoodPair Q₁ Q₂ c → GoodPair (rotCapping u ∘ Q₁) (rotCapping u ∘ Q₂) c`.

## The proof

* the rotation of the capping space acts by a *homeomorphism* which is a group action
  (`Work.Drive.rotCapping_add`, `Work.Drive.rotCapping_zero`), so `rotCapping u` is injective
  (`Work.Drive.rotCapping_injective'`) — this makes the **meet set** invariant:
  `coreMeet (rotCapping u ∘ Q₁) c (diskPlane (rotCapping u ∘ Q₂)) = coreMeet Q₁ c (diskPlane Q₂)`
  (the loop is `rotCapping u ∘ coreLoop Q₁` by `rfl`, and the sweep of the rotated plane is the
  rotation of the sweep, `Work.Drive.clampedSweep_rotCapping`).  Clauses 3 and 4 follow at once;
* the rotation is `C^∞` as a self-map of the capping space (`contMDiff_rotCapping_apply`), giving
  clauses 1 and 2 by composition;
* for clause 5, the chain rule expresses the two rotated derivatives as
  `mfderiv (rotCapping u) p ∘ mfderiv (loop or sweep) q`, at the **same** base point `p` (the common
  meet point); the derivative of a rotation is onto — its inverse rotation is a smooth inverse
  (`rotCapping_comp_neg`, `rotCapping_neg_comp`), so the chain rule for `rotCapping u ∘ rotCapping
  (-u) = id` exhibits the derivative as a split surjection (`surjective_mfderiv_rotCapping`) — and a
  linear map with `⊤` range maps the sup of the two ranges (which is `⊤` by the hypothesis) onto `⊤`
  (`range_comp_sup_eq_top`).
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-! ## The fixed rotation as an ambient smooth self-map -/

/-- **A fixed rotation of the capping space is `C^∞`** (the single-map form of
`Work.Drive.contMDiffAt_rotCapping_comp`; the rotation parameter is constant). -/
lemma contMDiff_rotCapping_apply (u : UnitAddCircle) :
    ContMDiff (𝓡 4) (𝓡 4) Ctop (fun p : CappingSpace => rotCapping u p) := by
  obtain ⟨t, ht⟩ := Quotient.mk''_surjective u
  intro p
  have h := contMDiffAt_rotCapping_comp (I := 𝓡 4) (id : CappingSpace → CappingSpace)
    (fun _ : CappingSpace => t) p contMDiffAt_id contMDiffAt_const
  simpa [ht] using h

/-- The rotation composed with its inverse rotation is the identity. -/
lemma rotCapping_comp_neg (u : UnitAddCircle) :
    (fun p : CappingSpace => rotCapping u p) ∘ (fun p : CappingSpace => rotCapping (-u) p) = id := by
  funext q
  have h : rotCapping (u + -u) q = rotCapping u (rotCapping (-u) q) := by
    rw [rotCapping_add]; rfl
  rw [add_neg_cancel, rotCapping_zero] at h
  simpa using h.symm

/-- The inverse rotation composed with the rotation is the identity. -/
lemma rotCapping_neg_comp (u : UnitAddCircle) :
    (fun p : CappingSpace => rotCapping (-u) p) ∘ (fun p : CappingSpace => rotCapping u p) = id := by
  funext q
  have h : rotCapping (-u + u) q = rotCapping (-u) (rotCapping u q) := by
    rw [rotCapping_add]; rfl
  rw [neg_add_cancel, rotCapping_zero] at h
  simpa using h.symm

/-- **The derivative of a fixed rotation of the capping space is onto** at every point: the chain
rule applied to the identity `rotCapping u ∘ rotCapping (-u) = id` exhibits it as a split
surjection. -/
lemma surjective_mfderiv_rotCapping (u : UnitAddCircle) (p : CappingSpace) :
    Function.Surjective
      (mfderiv (𝓡 4) (𝓡 4) (fun p : CappingSpace => rotCapping u p) p) := by
  have hΦ : ContMDiff (𝓡 4) (𝓡 4) Ctop (fun p : CappingSpace => rotCapping u p) :=
    contMDiff_rotCapping_apply u
  have hΨ : ContMDiff (𝓡 4) (𝓡 4) Ctop (fun p : CappingSpace => rotCapping (-u) p) :=
    contMDiff_rotCapping_apply (-u)
  have hpt : rotCapping (-u) (rotCapping u p) = p := by
    have := congrFun (rotCapping_neg_comp u) p
    simpa using this
  let S : TangentSpace (𝓡 4) (rotCapping u p) →L[ℝ] TangentSpace (𝓡 4) p :=
    mfderiv (𝓡 4) (𝓡 4) (fun q : CappingSpace => rotCapping (-u) q) (rotCapping u p)
  let T : TangentSpace (𝓡 4) p →L[ℝ] TangentSpace (𝓡 4) (rotCapping u p) :=
    mfderiv (𝓡 4) (𝓡 4) (fun q : CappingSpace => rotCapping u q) p
  have hcomp : T.comp S = ContinuousLinearMap.id ℝ (TangentSpace (𝓡 4) (rotCapping u p)) := by
    have h := mfderiv_comp (I := 𝓡 4) (I' := 𝓡 4) (I'' := 𝓡 4)
      (f := fun q : CappingSpace => rotCapping (-u) q)
      (g := fun q : CappingSpace => rotCapping u q) (rotCapping u p)
      (hΦ.mdifferentiableAt (by simp)) (hΨ.mdifferentiableAt (by simp))
    rw [rotCapping_comp_neg, mfderiv_id, hpt] at h
    exact h.symm
  intro y
  refine ⟨S y, ?_⟩
  show (T.comp S) y = y
  rw [hcomp, ContinuousLinearMap.id_apply]

/-- **Linear algebra of the transversality clause**: if the range of `T` is everything and the two
ranges `A`, `B` span, then so do the ranges of `T ∘ A` and `T ∘ B`. -/
lemma range_comp_sup_eq_top (T : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (A : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (B : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (hT : Function.Surjective T)
    (hAB : LinearMap.range A.toLinearMap ⊔ LinearMap.range B.toLinearMap = ⊤) :
    LinearMap.range (T.comp A).toLinearMap ⊔ LinearMap.range (T.comp B).toLinearMap = ⊤ := by
  rw [ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.range_comp, LinearMap.range_comp, ← Submodule.map_sup, hAB, Submodule.map_top,
    LinearMap.range_eq_top.mpr hT]

/-! ## The meet set of a rotated pair -/

/-- **The meet set is unchanged by a common rotation of the two charts**: the loop of the rotated
chart is the rotation of the loop, and the sweep of the rotated disk presentation is the rotation of
the sweep (`Work.Drive.clampedSweep_rotCapping`), so the defining equality is transported by the
injectivity of the rotation. -/
lemma coreMeet_rotCapping (Q₁ Q₂ : ℂ → CappingSpace) (c : ℝ) (u : UnitAddCircle) :
    coreMeet (fun z => rotCapping u (Q₁ z)) c (diskPlane (fun z => rotCapping u (Q₂ z)))
      = coreMeet Q₁ c (diskPlane Q₂) := by
  ext q
  simp only [coreMeet, Set.mem_ofPred_eq]
  have hloop : coreLoop (fun z => rotCapping u (Q₁ z)) q.1
      = rotCapping u (coreLoop Q₁ q.1) := rfl
  have hsweep : clampedSweep c (fun t => 1 - t) (diskPlane (fun z => rotCapping u (Q₂ z))) q.2
      = rotCapping u (clampedSweep c (fun t => 1 - t) (diskPlane Q₂) q.2) :=
    clampedSweep_rotCapping u c (fun t => 1 - t) (diskPlane Q₂) q.2
  rw [hloop, hsweep]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, rotCapping_injective' u h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, congrArg (rotCapping u) h3⟩

/-- **The chain rule for a chain followed by a fixed rotation**: the derivative of
`z ↦ rotCapping u (f z)` is the derivative of the rotation at `f z` composed with the derivative of
`f`.  (The general form of `Work.Drive.mfderiv_rotCapping_comp` in the loop and the chain case.) -/
lemma mfderiv_rotCapping_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace H Z]
    (f : Z → CappingSpace) (u : UnitAddCircle) (z : Z)
    (hf : MDifferentiableAt I (𝓡 4) f z) :
    mfderiv I (𝓡 4) (fun z => rotCapping u (f z)) z
      = (mfderiv (𝓡 4) (𝓡 4) (fun q : CappingSpace => rotCapping u q) (f z)).comp
        (mfderiv I (𝓡 4) f z) := by
  have hΦ : MDifferentiableAt (𝓡 4) (𝓡 4) (fun q : CappingSpace => rotCapping u q) (f z) :=
    (contMDiff_rotCapping_apply u).mdifferentiableAt (by simp)
  exact mfderiv_comp (f := f) (g := fun q : CappingSpace => rotCapping u q) z hΦ hf

/-! ## The theorem -/

theorem goodPair_rotCapping (Q₁ Q₂ : ℂ → Work.Drive.CappingSpace) (c : ℝ) (u : UnitAddCircle)
    (h : Work.Drive.GoodPair Q₁ Q₂ c) :
    Work.Drive.GoodPair (fun z => Work.Drive.rotCapping u (Q₁ z))
      (fun z => Work.Drive.rotCapping u (Q₂ z)) c := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (contMDiff_rotCapping_apply u).comp h.1
  · exact (contMDiff_rotCapping_apply u).comp h.2.1
  · rw [coreMeet_rotCapping]; exact h.2.2.1
  · intro q hq
    rw [coreMeet_rotCapping] at hq
    exact h.2.2.2.1 q hq
  · intro q hq
    rw [coreMeet_rotCapping] at hq
    have hqeq : coreLoop Q₁ q.1
        = clampedSweep c (fun t => 1 - t) (diskPlane Q₂) q.2 := hq.2.2
    have hgood := h.2.2.2.2 q hq
    let A : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
      mfderiv (𝓘(ℝ,ℝ)) (𝓡 4) (coreLoop Q₁) q.1
    let B : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
      mfderiv (𝓡 3) (𝓡 4) (clampedSweep c (fun t => 1 - t) (diskPlane Q₂)) q.2
    let T : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
      mfderiv (𝓡 4) (𝓡 4) (fun q : CappingSpace => rotCapping u q) (coreLoop Q₁ q.1)
    have hloopdiff : MDifferentiableAt (𝓘(ℝ,ℝ)) (𝓡 4) (coreLoop Q₁) q.1 :=
      (contMDiff_coreLoop h.1).mdifferentiableAt (by simp)
    have hsweepdiff : MDifferentiableAt (𝓡 3) (𝓡 4)
        (clampedSweep c (fun t => 1 - t) (diskPlane Q₂)) q.2 :=
      (contMDiff_clampedSweep c (fun t => 1 - t) (diskPlane Q₂)
        (by fun_prop) (contMDiff_diskPlane h.2.1)).mdifferentiableAt (by simp)
    have hA : mfderiv (𝓘(ℝ,ℝ)) (𝓡 4)
        (coreLoop (fun z => rotCapping u (Q₁ z))) q.1 = T.comp A := by
      rw [show coreLoop (fun z => rotCapping u (Q₁ z))
          = (fun t => rotCapping u (coreLoop Q₁ t)) from rfl]
      exact mfderiv_rotCapping_comp (𝓘(ℝ,ℝ)) (coreLoop Q₁) u q.1 hloopdiff
    have hB : mfderiv (𝓡 3) (𝓡 4)
        (clampedSweep c (fun t => 1 - t) (diskPlane (fun z => rotCapping u (Q₂ z)))) q.2
        = T.comp B := by
      rw [show clampedSweep c (fun t => 1 - t) (diskPlane (fun z => rotCapping u (Q₂ z)))
          = (fun x => rotCapping u
              (clampedSweep c (fun t => 1 - t) (diskPlane Q₂) x)) from
        funext (fun x => clampedSweep_rotCapping u c (fun t => 1 - t) (diskPlane Q₂) x)]
      rw [mfderiv_rotCapping_comp (𝓡 3)
        (clampedSweep c (fun t => 1 - t) (diskPlane Q₂)) u q.2 hsweepdiff]
      have hT : mfderiv (𝓡 4) (𝓡 4) (fun q : CappingSpace => rotCapping u q)
            (clampedSweep c (fun t => 1 - t) (diskPlane Q₂) q.2)
          = mfderiv (𝓡 4) (𝓡 4) (fun q : CappingSpace => rotCapping u q)
            (coreLoop Q₁ q.1) := by
        rw [hqeq]
      rw [hT]
      rfl
    rw [hA, hB]
    exact range_comp_sup_eq_top T A B
      (surjective_mfderiv_rotCapping u (coreLoop Q₁ q.1)) hgood

end

end Work.Drive
