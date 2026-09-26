import Mathlib
import Submission.Work.Drive.CollarPushAll
import Submission.Work.Drive.PushedNullHomotopy
import Submission.Work.Drive.InnermostPlaneCurve
import Submission.Work.Drive.Interfaces
import Submission.Work.CoreTopology.disk_sign_dichotomy

namespace Work.Drive

open LeanEval.KnotTheory.PardonDistortion
open Set

/-- The push data of the collar push of a torus, packaged as the hypotheses of the surgery. -/
structure PushData (ψ : R3 ≃ₜ R3) where
  pushP : R3 → ℝ → R3
  levP : R3 → ℝ
  hlev : ∀ x : R3, levP x = 1 ↔ x ∈ (Work.CoreTopology.ParamTorus.mapHomeomorph ψ).carrier
  hcont_lev : Continuous levP
  hcont : Continuous (Function.uncurry pushP)
  hzero : ∀ x : R3, pushP x 0 = x
  hshift : ∀ x : R3, ∀ δ : ℝ, levP x ∈ Set.Icc (1/2) (5/4) → |δ| ≤ 1/4 →
    levP (pushP x δ) = levP x + δ
  hge : ∀ x : R3, ∀ δ : ℝ, 3/2 ≤ levP x → pushP x δ = x
  hmono : ∀ x : R3, ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1/4 → 5/4 ≤ levP x → 5/4 ≤ levP (pushP x δ)
  hmono' : ∀ x : R3, ∀ δ : ℝ, -1/4 ≤ δ → δ ≤ 0 → levP x ≤ 1 → levP (pushP x δ) ≤ levP x

/-- **A weak innermost-disc datum**: a continuous disc map `e` spanning `α`, together with the
finite family of simple closed plane curves `kappa i` whose images under `e` are exactly the
intersection curves of `e` with `F`.  No injectivity is required, so that the induction can be
iterated over the surgery. -/
structure WeakDatum (ψ : R3 ≃ₜ R3) where
  α : Work.CoreTopology.ClosedCurve (Work.CoreTopology.ParamTorus.mapHomeomorph ψ)
  e : C(Work.InnermostDisk.Disc, R3)
  boundary : ∀ θ : ℝ, e (Work.CoreTopology.circlePoint θ) = α.γ θ
  ι : Type
  fintype : Fintype ι
  kappa : ι → Work.Smooth.Jordan.PlaneCurve
  kappa_simple : ∀ i : ι, (kappa i).IsSimple
  kappa_disj : Pairwise fun i j : ι =>
    Disjoint (Set.range (kappa i).γ) (Set.range (kappa j).γ)
  kappa_mem : ∀ (i : ι) (t : ℝ), (kappa i).γ t ∈ Metric.closedBall (0 : ℂ) 1
  curves : ι → Work.CoreTopology.ClosedCurve (Work.CoreTopology.ParamTorus.mapHomeomorph ψ)
  curves_simple : ∀ i : ι, Work.CoreTopology.IsSimple _ (curves i)
  curves_inessential : ∀ i : ι, ¬ Work.CoreTopology.IsEssential _ (curves i)
  maps_kappa : ∀ (i : ι) (t : ℝ),
    e ⟨(kappa i).γ t, kappa_mem i t⟩ = (curves i).γ t
  covers : ∀ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 →
    e z ∈ (Work.CoreTopology.ParamTorus.mapHomeomorph ψ).carrier →
    ∃ (i : ι) (t : ℝ), (kappa i).γ t = (z : ℂ)

attribute [instance] WeakDatum.fintype

namespace WeakDatum

variable {ψ : R3 ≃ₜ R3}

/-- The base case: a weak datum with no intersection curves already bounds a disc off `F`. -/
theorem boundsDiskInComplementW_of_isEmpty (D : WeakDatum ψ) (h : IsEmpty D.ι) :
    BoundsDiskInComplementW (Work.CoreTopology.ParamTorus.mapHomeomorph ψ) D.α :=
  ⟨D.e, D.boundary, fun z hz hem => by
    obtain ⟨i, -, -⟩ := D.covers z hz hem
    exact h.false i⟩

end WeakDatum

section Conversion

variable {ψ : R3 ≃ₜ R3} {S : Set R3}

/-- Every innermost-disc datum (with an *injective* disc map) gives a weak datum: the plane curves
are the preimages of the intersection curves under the disc map. -/
noncomputable def WeakDatum.ofInnermostDisc
    (D : Work.InnermostDisk.InnermostDisc (Work.CoreTopology.ParamTorus.mapHomeomorph ψ) S) :
    WeakDatum ψ := by
  classical
  set φ := (D.e.continuous.isClosedEmbedding D.inj).toIsEmbedding.toHomeomorph with hφ
  have key : ∀ (i : D.ι) (t : ℝ), (φ (φ.symm ⟨(D.curves i).γ t, D.curves_subset i ⟨t, rfl⟩⟩) : R3)
      = (D.curves i).γ t := fun i t =>
    congrArg (fun w : Set.range D.e => (w : R3)) (Homeomorph.apply_symm_apply φ _)
  refine
    { α := D.α
      e := D.e
      boundary := D.boundary
      ι := D.ι
      fintype := D.fintype
      kappa := fun i =>
        { γ := fun t => ((φ.symm ⟨(D.curves i).γ t, D.curves_subset i ⟨t, rfl⟩⟩ :
              Work.InnermostDisk.Disc) : ℂ)
          cont := continuous_subtype_val.comp (φ.symm.continuous.comp
            ((D.curves i).cont.subtype_mk (fun t => D.curves_subset i ⟨t, rfl⟩)))
          periodic := fun t => by
            have h : (⟨(D.curves i).γ (t + 2 * Real.pi), D.curves_subset i ⟨t + 2 * Real.pi, rfl⟩⟩ :
                Set.range D.e) = ⟨(D.curves i).γ t, D.curves_subset i ⟨t, rfl⟩⟩ :=
              Subtype.ext ((D.curves i).periodic t)
            exact congrArg (fun w => ((φ.symm w : Work.InnermostDisk.Disc) : ℂ)) h }
      kappa_simple := by
        intro i a ha b hb h
        have h1 : (⟨(D.curves i).γ a, D.curves_subset i ⟨a, rfl⟩⟩ : Set.range D.e) =
            ⟨(D.curves i).γ b, D.curves_subset i ⟨b, rfl⟩⟩ := by
          have hsub : (φ.symm ⟨(D.curves i).γ a, D.curves_subset i ⟨a, rfl⟩⟩ :
              Work.InnermostDisk.Disc) =
              φ.symm ⟨(D.curves i).γ b, D.curves_subset i ⟨b, rfl⟩⟩ := Subtype.ext h
          have h2 := congrArg (fun w : Work.InnermostDisk.Disc => (φ w : Set.range D.e)) hsub
          simpa only [Homeomorph.apply_symm_apply] using h2
        exact D.curves_simple i ha hb (congrArg Subtype.val h1)
      kappa_disj := by
        intro i j hij
        rw [Set.disjoint_left]
        intro x hxi hxj
        obtain ⟨t, rfl⟩ := hxi
        obtain ⟨s, hs⟩ := hxj
        have h1 : (D.curves i).γ t = (D.curves j).γ s := by
          have hsub : (φ.symm ⟨(D.curves j).γ s, D.curves_subset j ⟨s, rfl⟩⟩ :
              Work.InnermostDisk.Disc) =
              φ.symm ⟨(D.curves i).γ t, D.curves_subset i ⟨t, rfl⟩⟩ := Subtype.ext hs
          have h2 := congrArg (fun w : Work.InnermostDisk.Disc => (φ w : Set.range D.e)) hsub
          simp only [Homeomorph.apply_symm_apply] at h2
          exact congrArg Subtype.val h2.symm
        exact Set.disjoint_left.mp (D.curves_disjoint hij) ⟨t, rfl⟩ ⟨s, h1.symm⟩
      kappa_mem := fun i t => (φ.symm ⟨(D.curves i).γ t, D.curves_subset i ⟨t, rfl⟩⟩).2
      curves := D.curves
      curves_simple := D.curves_simple
      curves_inessential := D.curves_inessential
      maps_kappa := by
        intro i t
        exact key i t
      covers := by
        intro z hz hem
        obtain ⟨i, hi⟩ := D.covers z hz hem
        obtain ⟨t, ht⟩ := hi
        refine ⟨i, t, ?_⟩
        have h1 : (⟨(D.curves i).γ t, D.curves_subset i ⟨t, rfl⟩⟩ : Set.range D.e) =
            ⟨D.e z, ⟨z, rfl⟩⟩ := by
          exact Subtype.ext ht
        have h2 := congrArg (fun w : Set.range D.e => (φ.symm w : Work.InnermostDisk.Disc)) h1
        have h3 : φ.symm ⟨D.e z, ⟨z, rfl⟩⟩ = z := Homeomorph.symm_apply_apply φ z
        have : ((φ.symm ⟨(D.curves i).γ t, D.curves_subset i ⟨t, rfl⟩⟩ : Work.InnermostDisk.Disc) : ℂ)
            = (z : ℂ) := by rw [h2, h3]
        exact this }

end Conversion

section NullHomotopyLevel

variable {ψ : R3 ≃ₜ R3}

private lemma norm_circlePoint' (θ : ℝ) :
    ‖((Work.CoreTopology.circlePoint θ : Work.InnermostDisk.Disc) : ℂ)‖ = 1 := by
  rw [Work.CoreTopology.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]

private lemma norm_le_one_of_disc' (z : Work.InnermostDisk.Disc) : ‖(z : ℂ)‖ ≤ 1 := by
  have h := Metric.mem_closedBall.mp z.2
  rwa [dist_zero_right] at h

/-- **The pushed null-homotopy of an inessential curve, with its exact level.**
Every inessential closed curve `γ` of the torus bounds a continuous disc map `H` whose boundary is
`γ` and whose level is prescribed: `levP (H z) = 1 + ε * (1 - ‖z‖)` on the open disc, for every
`ε` with `|ε| ≤ 1/4`.  (This is the construction underlying `Work.Drive.PushedNullHomotopy`,
recorded with the explicit level.) -/
theorem pushedNullHomotopy_level (PD : PushData ψ)
    (γ : Work.CoreTopology.ClosedCurve (Work.CoreTopology.ParamTorus.mapHomeomorph ψ))
    (hγ : ¬ Work.CoreTopology.IsEssential _ γ) (ε : ℝ) (hε : |ε| ≤ 1/4) :
    ∃ H : C(Work.InnermostDisk.Disc, R3),
      (∀ θ : ℝ, H (Work.CoreTopology.circlePoint θ) = γ.γ θ) ∧
      ∀ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 →
        PD.levP (H z) = 1 + ε * (1 - ‖(z : ℂ)‖) := by
  obtain ⟨e, he⟩ := Work.InnermostDisk.boundsDiscInSurface_of_not_isEssential
    (Work.CoreTopology.ParamTorus.mapHomeomorph ψ) hγ
  have hecont : Continuous fun z : Work.InnermostDisk.Disc =>
      ((e z : (Work.CoreTopology.ParamTorus.mapHomeomorph ψ).carrier) : R3) :=
    continuous_subtype_val.comp e.continuous
  have hnorm : Continuous fun z : Work.InnermostDisk.Disc => ‖(z : ℂ)‖ :=
    continuous_norm.comp continuous_subtype_val
  have hlevel : ∀ z : Work.InnermostDisk.Disc,
      PD.levP ((e z : (Work.CoreTopology.ParamTorus.mapHomeomorph ψ).carrier) : R3) = 1 :=
    fun z => (PD.hlev _).mpr (e z).2
  let F : Work.InnermostDisk.Disc → R3 := fun z =>
    PD.pushP ((e z : (Work.CoreTopology.ParamTorus.mapHomeomorph ψ).carrier) : R3)
      (ε * (1 - ‖(z : ℂ)‖))
  have hcontF : Continuous F :=
    PD.hcont.comp (hecont.prodMk (continuous_const.mul (continuous_const.sub hnorm)))
  refine ⟨⟨F, hcontF⟩, ?_, ?_⟩
  · intro θ
    have h1 : ‖((Work.CoreTopology.circlePoint θ : Work.InnermostDisk.Disc) : ℂ)‖ = 1 :=
      norm_circlePoint' θ
    show F (Work.CoreTopology.circlePoint θ) = γ.γ θ
    simp only [F, h1, sub_self, mul_zero, PD.hzero]
    exact he θ
  · intro z hz
    have hze : PD.levP ((e z : (Work.CoreTopology.ParamTorus.mapHomeomorph ψ).carrier) : R3)
        = 1 := hlevel z
    have hIcc : PD.levP ((e z : (Work.CoreTopology.ParamTorus.mapHomeomorph ψ).carrier) : R3)
        ∈ Set.Icc (1/2 : ℝ) (5/4) := by
      rw [hze]; norm_num
    have hdle1 : ‖(z : ℂ)‖ ≤ 1 := norm_le_one_of_disc' z
    have hnn : 0 ≤ 1 - ‖(z : ℂ)‖ := by linarith
    have hdle : |ε * (1 - ‖(z : ℂ)‖)| ≤ 1/4 := by
      rw [abs_mul]
      have h2 : |1 - ‖(z : ℂ)‖| ≤ 1 := by rw [abs_of_nonneg hnn]; simp
      calc |ε| * |1 - ‖(z : ℂ)‖| ≤ (1/4) * 1 :=
            mul_le_mul hε h2 (abs_nonneg _) (by norm_num)
        _ ≤ 1 / 4 := by norm_num
    show PD.levP (F z) = 1 + ε * (1 - ‖(z : ℂ)‖)
    simp only [F]
    rw [PD.hshift _ _ hIcc hdle, hze]

end NullHomotopyLevel

/-- A continuous nowhere-zero real function on a preconnected set has constant sign.  (This is the
sign fact the surgery needs: the sign of `levP ∘ D.e - 1` is constant on any preconnected collar of
the innermost trace.) -/
theorem sign_const_of_preconnected {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsPreconnected s) (f : X → ℝ) (hf : Continuous f) (hne : ∀ x ∈ s, f x ≠ 0) :
    (∀ x ∈ s, 0 < f x) ∨ (∀ x ∈ s, f x < 0) := by
  have him : IsPreconnected (f '' s) := hs.image f hf.continuousOn
  have hoc : (f '' s).OrdConnected := him.ordConnected
  by_contra h
  push Not at h
  obtain ⟨⟨x, hx, hxle⟩, ⟨y, hy, hyle⟩⟩ := h
  have hx0 : f x < 0 := lt_of_le_of_ne hxle (hne x hx)
  have hy0 : 0 < f y := lt_of_le_of_ne hyle (Ne.symm (hne y hy))
  have h0 : (0:ℝ) ∈ f '' s :=
    hoc.out ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ ⟨le_of_lt hx0, le_of_lt hy0⟩
  obtain ⟨z, hz, hz0⟩ := h0
  exact hne z hz hz0

/-- **The structural data of the innermost curve** that the single surgery needs: the innermost
curve `i₀` with its planar Jordan–Schoenflies datum `hsch` (whose bounded side `hsch.V` contains no
other trace), together with a *one-sidedness* clause for the level of `D.e` on the outward tube of
the trace.

The one-sidedness clause is a *theorem* about the outward tube of a Jordan curve, not an extra
assumption on the datum: the outward tube is preconnected
(`Work.Drive.TubeOutsidePreconnectedSmall`, proved in this workspace), and on it the level
`levP ∘ D.e` takes the value `1` only on the trace itself, so `levP ∘ D.e - 1` has constant sign
there.  (The sign is genuinely needed: the push must move the two sides of the trace in opposite
directions, and the two sides of the trace are *not* separately visible to the axioms of
`PushData`.) -/
structure InnermostSignData (ψ : R3 ≃ₜ R3) (PD : PushData ψ) (D : WeakDatum ψ) where
  /-- the innermost curve -/
  i₀ : D.ι
  /-- its planar Jordan–Schoenflies datum -/
  hsch : Work.Smooth.Jordan.PlaneSchoenflies (D.kappa i₀)
  /-- no other trace meets the bounded side -/
  outside : ∀ j : D.ι, Disjoint (Set.range (D.kappa j).γ) hsch.V
  /-- the radius of the outward tube -/
  r : ℝ
  /-- it is positive -/
  hr : 0 < r
  /-- the sign of the level on the outward tube -/
  σ : ℝ
  /-- it is `±1` -/
  hσ : σ = 1 ∨ σ = -1
  /-- the outward tube avoids the other traces -/
  avoids : ∀ j : D.ι, j ≠ i₀ → ∀ z : ℂ,
    Metric.infDist z (Set.range (D.kappa i₀).γ) < r → z ∉ Set.range (D.kappa j).γ
  /-- one-sidedness of the level on the outward tube, at *interior* points of `𝔻`.

  The interior restriction is essential: `∂𝔻` is allowed to map into `F` (it is the boundary
  circle of the datum, mapping to `D.α`), so `levP ∘ D.e - 1` vanishes there and no sign can be
  demanded at boundary points. -/
  sign : ∀ z : ℂ, (hz : z ∈ Metric.closedBall (0 : ℂ) 1) → ‖z‖ < 1 →
    Metric.infDist z (Set.range (D.kappa i₀).γ) < r → z ∉ closure hsch.V →
    0 < σ * (PD.levP (D.e ⟨z, hz⟩) - 1)


end Work.Drive
