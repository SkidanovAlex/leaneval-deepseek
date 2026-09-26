import Mathlib
import Submission.Work.Drive.Mono.TiltedTraceData
import Submission.Work.Drive.Mono.frontier_tiltedLevelRemoved_eq_caps
import Submission.Work.Drive.Mono.FiberModel.height_facts
import Submission.Work.Drive.Mono.WindowCase.tls_hypograph_sphere
import Submission.Work.Drive.Mono.WindowCase.tls_planarPi_disc
import Submission.Work.Drive.Mono.WindowCase.tls_planar_facts
import Submission.Work.Drive.Mono.WindowCase.tls_fibre_model

/-!
# The frontier of a level of the tilted sweep is a single embedded sphere

in the two-sided ("one-sphere window") regime: the box pokes out of both slab faces **and**, on
both sides of the slab, strictly above the wall.

## The route

Write `B := PBox s c σ`, `p := ⟪v,·⟫`, `q := ℓ`, `a := ⟪v,c⟫ + u`, and let `R := tiltedLevelRemoved`
be the box with the closed slab cut away below the wall.  The frontier of `R` is computed in two
steps.

* **The fibre model.**  Choose `ζ` with `ker p ∩ ker q ∩ ker ζ = 0` (`tls_fibre_model`).  Then
  `Φ := fibLin` (= `fibreHomeo`), `y ↦ (xyL (⟪v,y⟫, ℓ y), ζ y)`, is a homeomorphism of `ℝ³` which
  carries `R` onto the *fibre-coordinate open solid*
  `{P | cproj P ∈ xyL '' planarImage ∧ fMin < clast P < fMax}`
  and `cl R` onto the closed solid `{cproj P ∈ K ∧ fMin ≤ clast P ≤ fMax}` with
  `K := xyL '' closure (planarImage)` (`tiltedLevelRemoved_eq_fibre`, `mem_ClBox_iff_zeta`).
* **The solid over a plane disc.**  `K` is a plane disc (`tls_planarPi_disc` for the planar
  `Π`-region, transported by `xyL`; `tls_planar_facts` identifies the closure of the planar image
  with the `Π`-region), and the heights `fMin`, `fMax` are continuous on it.  Shifting the last
  coordinate by `fMin` exhibits the frontier as the frontier of the *hypograph* of
  `g := fMax - fMin ≥ 0` over the disc `K`, whose frontier is an embedded sphere
  (`hypoSphere`, the two-disc construction of `exists_cupParam` + `frontier_hypograph_eq`).
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set
open scoped Topology

noncomputable section

/-- The coordinate identification `ℝ × ℝ ≃ ℝ²`. -/
noncomputable def xyL : (ℝ × ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (LinearEquiv.piFinTwo ℝ (fun _ : Fin 2 => ℝ)).symm.trans
    (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm

/-- `xyL` as a continuous linear equivalence. -/
noncomputable def xyLC : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (xyL : (ℝ × ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 2)).toContinuousLinearEquiv

/-! ## The coordinate functionals of the plane -/

/-- The first coordinate of the plane `ℝ²`, as a continuous linear functional. -/
def fstL : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (0 : Fin 2)).comp
    (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).toLinearMap).toContinuousLinearMap

/-- The second coordinate of the plane `ℝ²`, as a continuous linear functional. -/
def sndL : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (1 : Fin 2)).comp
    (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).toLinearMap).toContinuousLinearMap

@[simp] theorem fstL_xyL (X : ℝ × ℝ) : fstL (xyL X) = X.1 := by
  simp [fstL, xyL]

@[simp] theorem sndL_xyL (X : ℝ × ℝ) : sndL (xyL X) = X.2 := by
  simp [sndL, xyL]

/-- The frontier of the solid under a continuous nonnegative height `g` over a plane disc `K` is an
embedded sphere.  (The version with only the four hypotheses that are actually used.) -/
theorem hypoSphere {K : Set (EuclideanSpace ℝ (Fin 2))}
    (hKdisc : ∃ e : C(Metric.closedBall (0 : ℂ) 1, EuclideanSpace ℝ (Fin 2)),
      Function.Injective e ∧ Set.range e = K ∧
      Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier K)
    {g : EuclideanSpace ℝ (Fin 2) → ℝ} (hgc : ContinuousOn g K)
    (hg0 : ∀ x ∈ K, 0 ≤ g x) (hgpos : ∀ x ∈ interior K, 0 < g x) :
    Work.InnermostDisk.IsEmbeddedSphere
      (frontier {P : EuclideanSpace ℝ (Fin 3) | Work.Drive.Mono.cproj P ∈ K ∧
        0 ≤ Work.Drive.Mono.clast P ∧
        Work.Drive.Mono.clast P ≤ g (Work.Drive.Mono.cproj P)}) := by
  obtain ⟨e, he_inj, he_range, he_bdry⟩ := hKdisc
  have hKc : IsCompact K := Work.Drive.Mono.WindowCase.tls_isCompact_of_discParam he_range
  have hKcl : closure (interior K) = K :=
    Work.Drive.Mono.WindowCase.tls_closure_interior_eq_of_discParam he_inj he_range he_bdry
  obtain ⟨eC, heC_inj, heC_range, heC_bdry⟩ :=
    Work.Drive.Mono.WindowCase.exists_cupParam e he_inj he_range he_bdry hgc hg0
  have hgK : ∀ z : Metric.closedBall (0 : ℂ) 1, e z ∈ K :=
    fun z => Work.Drive.Mono.WindowCase.tls_mem_K_of_discParam he_range z
  have hgcont : Continuous fun z : Metric.closedBall (0 : ℂ) 1 => g (e z) :=
    hgc.comp_continuous e.continuous hgK
  let eT : C(Metric.closedBall (0 : ℂ) 1, EuclideanSpace ℝ (Fin 3)) :=
    ⟨fun z => Work.Drive.Mono.cmk (e z) (g (e z)),
     Work.Drive.Mono.continuous_cmk.comp (e.continuous.prodMk hgcont)⟩
  have heT_apply : ∀ z, eT z = Work.Drive.Mono.cmk (e z) (g (e z)) := fun z => rfl
  have heT_inj : Function.Injective eT := by
    intro z w h
    have h1 : e z = e w := ((Work.Drive.Mono.cmk_eq_cmk_iff _ _ _ _).mp h).1
    exact he_inj h1
  have heT_range : Set.range eT = {P : EuclideanSpace ℝ (Fin 3) |
      Work.Drive.Mono.cproj P ∈ K ∧
      Work.Drive.Mono.clast P = g (Work.Drive.Mono.cproj P)} := by
    ext P
    constructor
    · rintro ⟨z, rfl⟩
      constructor
      · rw [heT_apply, Work.Drive.Mono.cproj_cmk]
        exact Work.Drive.Mono.WindowCase.tls_mem_K_of_discParam he_range z
      · rw [heT_apply, Work.Drive.Mono.clast_cmk, Work.Drive.Mono.cproj_cmk]
    · rintro ⟨hPK, hPg⟩
      obtain ⟨z, hz⟩ := Set.mem_range.mp (by rw [he_range]; exact hPK)
      refine ⟨z, ?_⟩
      rw [heT_apply, hz, ← hPg, Work.Drive.Mono.cmk_cproj_clast]
  have hbd : ∀ θ : ℝ, eC (Work.CoreTopology.circlePoint θ) =
      eT (Work.CoreTopology.circlePoint θ) := by
    intro θ
    rw [heT_apply]
    exact heC_bdry θ
  have hint : ∀ z w : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ < 1 → ‖(w : ℂ)‖ < 1 →
      eC z = eT w → False := by
    intro z w hz hw heq
    have hmem : eT w ∈ Set.range eC := ⟨z, heq⟩
    rw [heC_range] at hmem
    have hwT : eT w = Work.Drive.Mono.cmk (e w) (g (e w)) := heT_apply w
    have hcproj : Work.Drive.Mono.cproj (eT w) ∈ interior K := by
      rw [hwT, Work.Drive.Mono.cproj_cmk]
      exact (Work.Drive.Mono.cylRegion_e_mem_interior he_inj he_range he_bdry w).mpr hw
    have hclast : Work.Drive.Mono.clast (eT w) = g (Work.Drive.Mono.cproj (eT w)) := by
      rw [hwT, Work.Drive.Mono.cproj_cmk, Work.Drive.Mono.clast_cmk]
    have hpos : 0 < Work.Drive.Mono.clast (eT w) := by
      rw [hclast]; exact hgpos _ hcproj
    rcases hmem with ⟨-, hcl⟩ | ⟨hfr, -, -⟩
    · rw [hcl] at hpos; exact lt_irrefl _ hpos
    · exact hfr.2 hcproj
  have hsphere := Work.Drive.Mono.isEmbeddedSphere_of_doubleDisc eC eT heC_inj heT_inj hbd hint
  have hset : Set.range eC ∪ Set.range eT = frontier {P : EuclideanSpace ℝ (Fin 3) |
      Work.Drive.Mono.cproj P ∈ K ∧ 0 ≤ Work.Drive.Mono.clast P ∧
      Work.Drive.Mono.clast P ≤ g (Work.Drive.Mono.cproj P)} := by
    rw [heC_range, heT_range,
      Work.Drive.Mono.WindowCase.frontier_hypograph_eq hKc hKcl hgc hg0 hgpos]
    ext P
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    tauto
  rw [hset] at hsphere
  exact hsphere



/-! ## The fibre coordinate change (inlined, so that this file does not depend on
`Submission.Work.Drive.Mono.WindowCase.tls_of_planarDisc`) -/

theorem levPair_zeta_inj {v : R3} {ℓ : R3 →L[ℝ] ℝ} {ζ : R3 →L[ℝ] ℝ}
    (hζ : Work.Drive.Mono.FiberModel.HasTrivKernel v ℓ ζ)
    {y y' : R3} (h1 : Work.Drive.Mono.FiberModel.levPair v ℓ y
        = Work.Drive.Mono.FiberModel.levPair v ℓ y')
    (h2 : ζ y = ζ y') : y = y' := by
  have h1a : (Work.Drive.Mono.FiberModel.levPair v ℓ y).1
      = (Work.Drive.Mono.FiberModel.levPair v ℓ y').1 := congrArg Prod.fst h1
  have h1b : (Work.Drive.Mono.FiberModel.levPair v ℓ y).2
      = (Work.Drive.Mono.FiberModel.levPair v ℓ y').2 := congrArg Prod.snd h1
  simp only [Work.Drive.Mono.FiberModel.levPair] at h1a h1b
  have h3 : inner ℝ v (y - y') = 0 := by rw [inner_sub_right, h1a, sub_self]
  have h4 : ℓ (y - y') = 0 := by rw [map_sub, h1b, sub_self]
  have h5 : ζ (y - y') = 0 := by rw [map_sub, h2, sub_self]
  exact sub_eq_zero.mp (hζ (y - y') h3 h4 h5)

/-- The linear coordinate change `y ↦ (xyL (⟪v,y⟫, ℓ y), ζ y)`. -/
noncomputable def fibLin (v : R3) (ℓ ζ : R3 →L[ℝ] ℝ) : R3 →ₗ[ℝ] R3 where
  toFun := fun y => Work.Drive.Mono.cmk (xyL (Work.Drive.Mono.FiberModel.levPair v ℓ y)) (ζ y)
  map_add' := by
    intro y y'
    have h1 : Work.Drive.Mono.FiberModel.levPair v ℓ (y + y')
        = Work.Drive.Mono.FiberModel.levPair v ℓ y
          + Work.Drive.Mono.FiberModel.levPair v ℓ y' := by
      rw [Work.Drive.Mono.FiberModel.levPair_eq_levPairCLM,
        map_add (Work.Drive.Mono.FiberModel.levPairCLM v ℓ) y y']
    have h2 : ζ (y + y') = ζ y + ζ y' := map_add ζ y y'
    rw [h1, h2, map_add xyL (Work.Drive.Mono.FiberModel.levPair v ℓ y)
      (Work.Drive.Mono.FiberModel.levPair v ℓ y')]
    exact (Work.Drive.Mono.cmk_add _ _ _ _).symm
  map_smul' := by
    intro c y
    have h1 : Work.Drive.Mono.FiberModel.levPair v ℓ (c • y)
        = c • Work.Drive.Mono.FiberModel.levPair v ℓ y := by
      rw [Work.Drive.Mono.FiberModel.levPair_eq_levPairCLM,
        map_smul (Work.Drive.Mono.FiberModel.levPairCLM v ℓ) c y]
    have h2 : ζ (c • y) = c • ζ y := map_smul ζ c y
    rw [h1, h2, map_smul xyL c (Work.Drive.Mono.FiberModel.levPair v ℓ y)]
    exact (Work.Drive.Mono.cmk_smul c _ _).symm

theorem fibLin_apply (v : R3) (ℓ ζ : R3 →L[ℝ] ℝ) (y : R3) :
    fibLin v ℓ ζ y = Work.Drive.Mono.cmk (xyL (Work.Drive.Mono.FiberModel.levPair v ℓ y))
      (ζ y) := rfl

theorem cproj_fibLin (v : R3) (ℓ ζ : R3 →L[ℝ] ℝ) (y : R3) :
    Work.Drive.Mono.cproj (fibLin v ℓ ζ y)
      = xyL (Work.Drive.Mono.FiberModel.levPair v ℓ y) := by
  simp [fibLin, Work.Drive.Mono.cproj_cmk]

theorem clast_fibLin (v : R3) (ℓ ζ : R3 →L[ℝ] ℝ) (y : R3) :
    Work.Drive.Mono.clast (fibLin v ℓ ζ y) = ζ y := by
  simp [fibLin, Work.Drive.Mono.clast_cmk]

theorem fibLin_injective {v : R3} {ℓ : R3 →L[ℝ] ℝ} {ζ : R3 →L[ℝ] ℝ}
    (hζ : Work.Drive.Mono.FiberModel.HasTrivKernel v ℓ ζ) :
    Function.Injective (fibLin v ℓ ζ) := by
  intro y y' h
  have h1 : xyL (Work.Drive.Mono.FiberModel.levPair v ℓ y)
      = xyL (Work.Drive.Mono.FiberModel.levPair v ℓ y') := by
    have := congrArg Work.Drive.Mono.cproj h
    simpa only [cproj_fibLin] using this
  have h2 : ζ y = ζ y' := by
    have := congrArg Work.Drive.Mono.clast h
    simpa only [clast_fibLin] using this
  exact levPair_zeta_inj hζ (xyL.injective h1) h2

theorem fibLin_surjective {v : R3} {ℓ : R3 →L[ℝ] ℝ} {ζ : R3 →L[ℝ] ℝ}
    (hζ : Work.Drive.Mono.FiberModel.HasTrivKernel v ℓ ζ) :
    Function.Surjective (fibLin v ℓ ζ) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := fibLin v ℓ ζ) (by simp)).mp (fibLin_injective hζ)

/-- **The fibre coordinate change**: `y ↦ mk (xyL (⟪v,y⟫, ℓ y)) (ζ y)` is a homeomorphism of `ℝ³`
when `ζ` is transverse to the fibres of `(⟪v,·⟫, ℓ)`. -/
noncomputable def fibreHomeo {v : R3} {ℓ : R3 →L[ℝ] ℝ}
    {ζ : R3 →L[ℝ] ℝ} (hζ : Work.Drive.Mono.FiberModel.HasTrivKernel v ℓ ζ) : R3 ≃ₜ R3 :=
  (LinearEquiv.ofBijective (fibLin v ℓ ζ)
    ⟨fibLin_injective hζ, fibLin_surjective hζ⟩).toContinuousLinearEquiv.toHomeomorph

theorem fibreHomeo_apply {v : R3} {ℓ : R3 →L[ℝ] ℝ}
    {ζ : R3 →L[ℝ] ℝ} (hζ : Work.Drive.Mono.FiberModel.HasTrivKernel v ℓ ζ) (y : R3) :
    fibreHomeo hζ y
      = Work.Drive.Mono.cmk (xyL (Work.Drive.Mono.FiberModel.levPair v ℓ y)) (ζ y) := rfl

theorem cproj_fibreHomeo {v : R3} {ℓ : R3 →L[ℝ] ℝ}
    {ζ : R3 →L[ℝ] ℝ} (hζ : Work.Drive.Mono.FiberModel.HasTrivKernel v ℓ ζ) (y : R3) :
    Work.Drive.Mono.cproj (fibreHomeo hζ y)
      = xyL (Work.Drive.Mono.FiberModel.levPair v ℓ y) := by
  rw [fibreHomeo_apply, Work.Drive.Mono.cproj_cmk]

theorem clast_fibreHomeo {v : R3} {ℓ : R3 →L[ℝ] ℝ}
    {ζ : R3 →L[ℝ] ℝ} (hζ : Work.Drive.Mono.FiberModel.HasTrivKernel v ℓ ζ) (y : R3) :
    Work.Drive.Mono.clast (fibreHomeo hζ y) = ζ y := by
  rw [fibreHomeo_apply, Work.Drive.Mono.clast_cmk]

/-! ## The one-sphere window -/

section Window

variable {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ}
  {lam : ℝ}

theorem window_sphere
    (hs : 0 < s) (hv : v ≠ 0) (hh : 0 < h) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    (hwinP : ∃ y ∈ Submission.PBox s c σ, inner ℝ v c + u + h < inner ℝ v y)
    (hwinM : ∃ y ∈ Submission.PBox s c σ, inner ℝ v y < inner ℝ v c + u - h)
    (hwallP : ∃ y ∈ Submission.PBox s c σ, inner ℝ v c + u + h < inner ℝ v y ∧ lam < ℓ y)
    (hwallM : ∃ y ∈ Submission.PBox s c σ, inner ℝ v y < inner ℝ v c + u - h ∧ lam < ℓ y) :
    Work.InnermostDisk.IsEmbeddedSphere
      (frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) := by
  classical
  have hwallP' := hwallP
  have hwallM' := hwallM
  obtain ⟨yP, hyP, hyPf, hyPl⟩ := hwallP
  obtain ⟨yM, hyM, hyMf, hyMl⟩ := hwallM
  -- the fibre model
  obtain ⟨ζ, hζ, hfib, hstrict, hmaxc, hminc, hconc, hconv⟩ :=
    WindowCase.tls_fibre_model s hs c σ h v ℓ hh hℓv hℓne hv
  obtain ⟨-, -, hle, -, hIoo, hCliff, -, -, -, -⟩ :=
    Work.Drive.Mono.FiberModel.height_facts (ζ := ζ) (c := c) (σ := σ) hζ hs
  -- the open box in the fibre coordinates
  have hpbox : ∀ y : R3, y ∈ Submission.PBox s c σ →
      Work.Drive.Mono.FiberModel.levPair v ℓ y
          ∈ interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ) ∧
      Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ (Work.Drive.Mono.FiberModel.levPair v ℓ y) < ζ y ∧
      ζ y < Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ (Work.Drive.Mono.FiberModel.levPair v ℓ y) := by
    intro y hy
    have hX : Work.Drive.Mono.FiberModel.levPair v ℓ y
        ∈ interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ) := by
      rw [← Work.Drive.Mono.FiberModel.image_PBox_eq_interior_boxShadow (s := s) c σ hv hℓv hℓne]
      exact ⟨y, hy, rfl⟩
    have hmem : ζ y ∈ ζ '' {z ∈ Submission.PBox s c σ |
        Work.Drive.Mono.FiberModel.levPair v ℓ z = Work.Drive.Mono.FiberModel.levPair v ℓ y} :=
      ⟨y, ⟨hy, rfl⟩, rfl⟩
    rw [hIoo _ hX] at hmem
    exact ⟨hX, hmem.1, hmem.2⟩
  have hpbox' : ∀ y : R3,
      Work.Drive.Mono.FiberModel.levPair v ℓ y
          ∈ interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ) →
      Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ (Work.Drive.Mono.FiberModel.levPair v ℓ y) < ζ y →
      ζ y < Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ (Work.Drive.Mono.FiberModel.levPair v ℓ y) →
      y ∈ Submission.PBox s c σ := by
    intro y hX hlo hhi
    have hyC : y ∈ Work.Drive.Mono.FiberModel.ClBox s c σ :=
      (hCliff y).mpr ⟨interior_subset hX, le_of_lt hlo, le_of_lt hhi⟩
    have hmem : ζ y ∈ ζ '' {z ∈ Submission.PBox s c σ |
        Work.Drive.Mono.FiberModel.levPair v ℓ z = Work.Drive.Mono.FiberModel.levPair v ℓ y} := by
      rw [hIoo _ hX]
      exact ⟨hlo, hhi⟩
    obtain ⟨z, hz, hzy⟩ := hmem
    have hzy' : z = y := levPair_zeta_inj hζ hz.2 hzy
    subst hzy'
    exact hz.1
  -- the planar shadow and the `Π`-region
  have hWb : Bornology.IsBounded (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ) := by
    rw [Work.Drive.Mono.FiberModel.boxShadow_eq_closure_image]
    exact ((Work.Drive.Mono.FiberModel.isBounded_PBox s c σ).image
      ((Work.Drive.Mono.FiberModel.levPairCLM v ℓ :
        R3 →L[ℝ] (ℝ × ℝ)))).closure
  have hQc : Convex ℝ (xyL '' interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ)) :=
    (Work.Drive.Mono.FiberModel.convex_boxShadow s c σ v ℓ).interior.linear_image
      xyL.toLinearMap
  have hQo : IsOpen (xyL '' interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ)) :=
    xyLC.isOpenMap _ isOpen_interior
  have hQb : Bornology.IsBounded
      (xyL '' interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ)) :=
    (hWb.image (xyLC :
      (ℝ × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2))).subset (Set.image_mono interior_subset)
  have hcruxP : ∃ x ∈ xyL '' interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ),
      inner ℝ v c + u + h < fstL x ∧ lam < sndL x := by
    refine ⟨xyL (Work.Drive.Mono.FiberModel.levPair v ℓ yP), ?_, ?_, ?_⟩
    · exact ⟨Work.Drive.Mono.FiberModel.levPair v ℓ yP, by
        rw [← Work.Drive.Mono.FiberModel.image_PBox_eq_interior_boxShadow (s := s) c σ hv hℓv hℓne]
        exact ⟨yP, hyP, rfl⟩, rfl⟩
    · rw [fstL_xyL]; exact hyPf
    · rw [sndL_xyL]; exact hyPl
  have hcruxM : ∃ x ∈ xyL '' interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ),
      fstL x < inner ℝ v c + u - h ∧ lam < sndL x := by
    refine ⟨xyL (Work.Drive.Mono.FiberModel.levPair v ℓ yM), ?_, ?_, ?_⟩
    · exact ⟨Work.Drive.Mono.FiberModel.levPair v ℓ yM, by
        rw [← Work.Drive.Mono.FiberModel.image_PBox_eq_interior_boxShadow (s := s) c σ hv hℓv hℓne]
        exact ⟨yM, hyM, rfl⟩, rfl⟩
    · rw [fstL_xyL]; exact hyMf
    · rw [sndL_xyL]; exact hyMl
  obtain ⟨e, he_inj, he_range, he_bdry⟩ :=
    WindowCase.tls_planarPi_disc (a := inner ℝ v c + u) (h := h) (lam := lam) hh _
      hQc hQo hQb fstL sndL hcruxP hcruxM
  -- the plane disc `K` is the closure of the planar image
  set K : Set (EuclideanSpace ℝ (Fin 2)) :=
    xyL '' closure (Work.Drive.Mono.FiberModel.planarImage s c σ u v h ℓ lam) with hK
  have hclW : closure (interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ))
      = Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ := by
    rw [← Work.Drive.Mono.FiberModel.image_PBox_eq_interior_boxShadow (s := s) c σ hv hℓv hℓne,
      Work.Drive.Mono.FiberModel.boxShadow_eq_closure_image]
  -- the transport of the plane coordinates through `xyL`
  set xyH : (ℝ × ℝ) ≃ₜ EuclideanSpace ℝ (Fin 2) :=
    xyLC.toHomeomorph with hxyHdef
  have hxyH : ∀ X : ℝ × ℝ, xyH X = xyL X := by intro X; rw [hxyHdef]; rfl
  have himgC : ∀ u : Set (ℝ × ℝ), xyH '' u = xyL '' u :=
    fun u => Set.image_congr' (fun X => hxyH X)
  have hfl : ∀ x : EuclideanSpace ℝ (Fin 2), fstL x = (xyL.symm x).1 :=
    fun x => by rw [← fstL_xyL (xyL.symm x), xyL.apply_symm_apply]
  have hsl : ∀ x : EuclideanSpace ℝ (Fin 2), sndL x = (xyL.symm x).2 :=
    fun x => by rw [← sndL_xyL (xyL.symm x), xyL.apply_symm_apply]
  have hclQ : closure (xyL '' interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ))
      = xyL '' Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ := by
    rw [← himgC (interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ)),
      ← Homeomorph.image_closure xyH (interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ)),
      hclW, ← himgC (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ)]
  have hc1 : ({x : EuclideanSpace ℝ (Fin 2) | inner ℝ v c + u + h ≤ fstL x} : Set _)
      = xyL '' {X : ℝ × ℝ | inner ℝ v c + u + h ≤ X.1} := by
    ext x
    constructor
    · intro hx
      refine ⟨xyL.symm x, ?_, xyL.apply_symm_apply x⟩
      simp only [Set.mem_ofPred_eq] at hx
      rw [hfl] at hx; exact hx
    · rintro ⟨X, hX, rfl⟩
      simpa only [Set.mem_ofPred_eq, fstL_xyL] using hX
  have hc2 : ({x : EuclideanSpace ℝ (Fin 2) | fstL x ≤ inner ℝ v c + u - h} : Set _)
      = xyL '' {X : ℝ × ℝ | X.1 ≤ inner ℝ v c + u - h} := by
    ext x
    constructor
    · intro hx
      refine ⟨xyL.symm x, ?_, xyL.apply_symm_apply x⟩
      simp only [Set.mem_ofPred_eq] at hx
      rw [hfl] at hx; exact hx
    · rintro ⟨X, hX, rfl⟩
      simpa only [Set.mem_ofPred_eq, fstL_xyL] using hX
  have hc3 : ({x : EuclideanSpace ℝ (Fin 2) | lam ≤ sndL x} : Set _)
      = xyL '' {X : ℝ × ℝ | lam ≤ X.2} := by
    ext x
    constructor
    · intro hx
      refine ⟨xyL.symm x, ?_, xyL.apply_symm_apply x⟩
      simp only [Set.mem_ofPred_eq] at hx
      rw [hsl] at hx; exact hx
    · rintro ⟨X, hX, rfl⟩
      simpa only [Set.mem_ofPred_eq, sndL_xyL] using hX
  have hcoord : ({x : EuclideanSpace ℝ (Fin 2) | inner ℝ v c + u + h ≤ fstL x} ∪
        {x : EuclideanSpace ℝ (Fin 2) | fstL x ≤ inner ℝ v c + u - h} ∪
        {x : EuclideanSpace ℝ (Fin 2) | lam ≤ sndL x})
      = xyL '' ({X : ℝ × ℝ | inner ℝ v c + u + h ≤ X.1} ∪
          {X : ℝ × ℝ | X.1 ≤ inner ℝ v c + u - h} ∪ {X : ℝ × ℝ | lam ≤ X.2}) := by
    rw [hc1, hc2, hc3, Set.image_union, Set.image_union]
  have hpiK : closure (xyL '' interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ))
        ∩ ({x : EuclideanSpace ℝ (Fin 2) | inner ℝ v c + u + h ≤ fstL x} ∪
           {x : EuclideanSpace ℝ (Fin 2) | fstL x ≤ inner ℝ v c + u - h} ∪
           {x : EuclideanSpace ℝ (Fin 2) | lam ≤ sndL x}) = K := by
    rw [hK, hclQ, hcoord, ← Set.image_inter xyL.injective,
      (Work.Drive.Mono.WindowCase.tls_planar_facts s hs c σ u h lam v ℓ hh hℓv hℓne hv
        hwinP hwinM hwallP' hwallM').2]
    rfl
  have hKint : interior K = xyL ''
      interior (closure (Work.Drive.Mono.FiberModel.planarImage s c σ u v h ℓ lam)) := by
    rw [hK, ← himgC (closure (Work.Drive.Mono.FiberModel.planarImage s c σ u v h ℓ lam)),
      ← Homeomorph.image_interior xyH (closure (Work.Drive.Mono.FiberModel.planarImage s c σ u v h ℓ lam)),
      ← himgC (interior (closure (Work.Drive.Mono.FiberModel.planarImage s c σ u v h ℓ lam)))]
  have hplan : closure (Work.Drive.Mono.FiberModel.planarImage s c σ u v h ℓ lam)
      = Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ ∩
        ({X : ℝ × ℝ | inner ℝ v c + u + h ≤ X.1} ∪
         {X : ℝ × ℝ | X.1 ≤ inner ℝ v c + u - h} ∪ {X : ℝ × ℝ | lam ≤ X.2}) :=
    (Work.Drive.Mono.WindowCase.tls_planar_facts s hs c σ u h lam v ℓ hh hℓv hℓne hv
      hwinP hwinM hwallP' hwallM').2
  have hplanInt : interior (closure (Work.Drive.Mono.FiberModel.planarImage s c σ u v h ℓ lam))
      = interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ) ∩
        {X : ℝ × ℝ | h < |X.1 - (inner ℝ v c + u)| ∨ lam < X.2} :=
    (Work.Drive.Mono.WindowCase.tls_planar_facts s hs c σ u h lam v ℓ hh hℓv hℓne hv
      hwinP hwinM hwallP' hwallM').1
  have hplan_iff : ∀ X : ℝ × ℝ,
      X ∈ closure (Work.Drive.Mono.FiberModel.planarImage s c σ u v h ℓ lam) ↔
      X ∈ Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ ∧
      ((inner ℝ v c + u + h ≤ X.1 ∨ X.1 ≤ inner ℝ v c + u - h) ∨ lam ≤ X.2) := by
    intro X
    rw [hplan]
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq]
  have hplanInt_iff : ∀ X : ℝ × ℝ,
      X ∈ interior (closure (Work.Drive.Mono.FiberModel.planarImage s c σ u v h ℓ lam)) ↔
      X ∈ interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ) ∧
      (h < |X.1 - (inner ℝ v c + u)| ∨ lam < X.2) := by
    intro X
    rw [hplanInt]
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq]
  have hKdisc : ∃ e : C(Metric.closedBall (0 : ℂ) 1, EuclideanSpace ℝ (Fin 2)),
      Function.Injective e ∧ Set.range e = K ∧
      Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier K :=
    ⟨e, he_inj, by rw [← hpiK]; exact he_range, by rw [← hpiK]; exact he_bdry⟩
  have hKcomp : IsCompact K := by
    obtain ⟨e', _, he'r, -⟩ := hKdisc
    exact WindowCase.tls_isCompact_of_discParam he'r
  -- the height over the disc
  set G : EuclideanSpace ℝ (Fin 2) → ℝ := fun Z =>
    Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ (xyL.symm Z)
      - Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ (xyL.symm Z) with hG
  have hKsub : ∀ Z ∈ K, xyL.symm Z ∈ Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ := by
    rintro Z hZ
    rw [hK] at hZ
    obtain ⟨X, hX, rfl⟩ := hZ
    simp only [xyL.symm_apply_apply]
    exact ((hplan_iff X).mp hX).1
  have hGc : ContinuousOn G K := by
    rw [hG]
    have h1 : ContinuousOn (fun Z : EuclideanSpace ℝ (Fin 2) =>
        Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ (xyL.symm Z)) K :=
      hmaxc.comp ((xyLC.symm.continuous).continuousOn) hKsub
    have h2 : ContinuousOn (fun Z : EuclideanSpace ℝ (Fin 2) =>
        Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ (xyL.symm Z)) K :=
      hminc.comp ((xyLC.symm.continuous).continuousOn) hKsub
    exact h1.sub h2
  have hG0 : ∀ Z ∈ K, 0 ≤ G Z := by
    intro Z hZ
    rw [hG]
    simp only
    have h := hle _ (hKsub Z hZ)
    linarith
  have hGpos : ∀ Z ∈ interior K, 0 < G Z := by
    intro Z hZ
    rw [hG]
    simp only
    rw [hKint] at hZ
    obtain ⟨X, hX, rfl⟩ := hZ
    simp only [xyL.symm_apply_apply]
    have hX' := hstrict _ (((hplanInt_iff X).mp hX).1)
    linarith
  have hsphere := hypoSphere hKdisc hGc hG0 hGpos
  -- the fibre coordinate homeomorphism
  set Λ : R3 ≃ₜ R3 := fibreHomeo hζ with hΛ
  have hΛcproj : ∀ y : R3, cproj (Λ y) = xyL (Work.Drive.Mono.FiberModel.levPair v ℓ y) := by
    intro y; rw [hΛ]; exact cproj_fibreHomeo hζ y
  have hΛclast : ∀ y : R3, clast (Λ y) = ζ y := by
    intro y; rw [hΛ]; exact clast_fibreHomeo hζ y
  -- the closed and the open solid in the fibre coordinates
  set solid : Set R3 := {P : R3 | cproj P ∈ K ∧
      Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ (xyL.symm (cproj P)) ≤ clast P ∧
      clast P ≤ Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ (xyL.symm (cproj P))} with hsolid
  set opensolid : Set R3 := {P : R3 | cproj P ∈ interior K ∧
      Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ (xyL.symm (cproj P)) < clast P ∧
      clast P < Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ (xyL.symm (cproj P))} with hopensolid
  -- the descriptions of the level in the fibre coordinates
  have hcut : Work.Drive.Mono.SlabCutsBox s c σ (inner ℝ v c + u) h v := ⟨hwinP, hwinM⟩
  have habove : ∃ y ∈ Submission.PBox s c σ, lam < ℓ y := ⟨yP, hyP, hyPl⟩
  have hclR : ∀ y : R3, y ∈ closure (tiltedLevelRemoved s c σ u v h ℓ lam) ↔
      y ∈ Work.Drive.Mono.FiberModel.ClBox s c σ ∧
      ((inner ℝ v c + u + h ≤ inner ℝ v y ∨ inner ℝ v y ≤ inner ℝ v c + u - h) ∨ lam ≤ ℓ y) := by
    intro y
    rw [Work.Drive.Mono.closure_tiltedLevelRemoved s u h lam c v σ ℓ hcut habove]
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Work.Drive.Mono.FiberModel.ClBox, Work.Drive.EpsForm.tiltedSlabClosed]
    constructor
    · rintro ⟨hy, hnot⟩
      refine ⟨hy, ?_⟩
      rcases not_and_or.mp hnot with h1 | h2
      · have h1' : h ≤ |inner ℝ v y - (inner ℝ v c + u)| := not_lt.mp h1
        rcases le_total (0 : ℝ) (inner ℝ v y - (inner ℝ v c + u)) with hpos | hneg
        · rw [abs_of_nonneg hpos] at h1'
          exact Or.inl (Or.inl (by linarith))
        · rw [abs_of_nonpos hneg] at h1'
          exact Or.inl (Or.inr (by linarith))
      · exact Or.inr (not_lt.mp h2)
    · rintro ⟨hy, (h | h) | h⟩
      · refine ⟨hy, fun hc => ?_⟩
        rw [abs_lt] at hc; linarith [hc.1, h]
      · refine ⟨hy, fun hc => ?_⟩
        rw [abs_lt] at hc; linarith [hc.2, h]
      · refine ⟨hy, fun hc => ?_⟩
        linarith [hc.2, h]
  have hintR : ∀ y : R3, y ∈ interior (tiltedLevelRemoved s c σ u v h ℓ lam) ↔
      y ∈ Submission.PBox s c σ ∧
      ((inner ℝ v c + u + h < inner ℝ v y ∨ inner ℝ v y < inner ℝ v c + u - h) ∨ lam < ℓ y) := by
    intro y
    rw [Work.Drive.Mono.interior_tiltedLevelRemoved s u h lam c v σ ℓ hv hℓne hℓv]
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Work.Drive.EpsForm.tiltedSlabClosed]
    constructor
    · rintro ⟨hy, hnot⟩
      refine ⟨hy, ?_⟩
      rcases not_and_or.mp hnot with h1 | h2
      · have h1' : h < |inner ℝ v y - (inner ℝ v c + u)| := not_le.mp h1
        rcases lt_abs.mp h1' with h3 | h3
        · exact Or.inl (Or.inl (by linarith))
        · exact Or.inl (Or.inr (by linarith))
      · exact Or.inr (not_le.mp h2)
    · rintro ⟨hy, (h | h) | h⟩
      · refine ⟨hy, fun hc => ?_⟩
        have := (abs_le.mp hc.1).2; linarith
      · refine ⟨hy, fun hc => ?_⟩
        have := (abs_le.mp hc.1).1; linarith
      · refine ⟨hy, fun hc => ?_⟩
        linarith [hc.2, h]
  have hclA : ∀ y : R3, y ∈ closure (tiltedLevelRemoved s c σ u v h ℓ lam) ↔ Λ y ∈ solid := by
    intro y
    rw [hclR y, hsolid]
    simp only [Set.mem_ofPred_eq]
    rw [hΛcproj y, hΛclast y, hK]
    constructor
    · rintro ⟨hyC, hyc⟩
      obtain ⟨h1, h2, h3⟩ := (hCliff y).mp hyC
      refine ⟨?_, ?_, ?_⟩
      · refine ⟨Work.Drive.Mono.FiberModel.levPair v ℓ y, ?_, rfl⟩
        exact (hplan_iff _).mpr ⟨h1, hyc⟩
      · simpa only [xyL.symm_apply_apply] using h2
      · simpa only [xyL.symm_apply_apply] using h3
    · rintro ⟨⟨X, hX, hXeq⟩, h2, h3⟩
      have hX' : X = Work.Drive.Mono.FiberModel.levPair v ℓ y := xyL.injective hXeq
      subst hX'
      obtain ⟨hX1, hX2⟩ := (hplan_iff _).mp hX
      refine ⟨(hCliff y).mpr ⟨hX1, ?_, ?_⟩, ?_⟩
      · simpa only [xyL.symm_apply_apply] using h2
      · simpa only [xyL.symm_apply_apply] using h3
      · simpa only [Work.Drive.Mono.FiberModel.levPair] using hX2
  have hintA : ∀ y : R3, y ∈ interior (tiltedLevelRemoved s c σ u v h ℓ lam) ↔ Λ y ∈ opensolid := by
    intro y
    rw [hintR y, hopensolid]
    simp only [Set.mem_ofPred_eq]
    rw [hΛcproj y, hΛclast y, hKint]
    constructor
    · rintro ⟨hyB, hyc⟩
      obtain ⟨h1, h2, h3⟩ := hpbox y hyB
      refine ⟨?_, ?_, ?_⟩
      · refine ⟨Work.Drive.Mono.FiberModel.levPair v ℓ y, ?_, rfl⟩
        refine (hplanInt_iff _).mpr ⟨h1, ?_⟩
        simp only [Set.mem_union, Set.mem_ofPred_eq, Work.Drive.Mono.FiberModel.levPair]
        rcases hyc with (h | h) | h
        · exact Or.inl (lt_abs.mpr (Or.inl (by linarith)))
        · exact Or.inl (lt_abs.mpr (Or.inr (by linarith)))
        · exact Or.inr h
      · simpa only [xyL.symm_apply_apply] using h2
      · simpa only [xyL.symm_apply_apply] using h3
    · rintro ⟨⟨X, hX, hXeq⟩, h2, h3⟩
      have hX' : X = Work.Drive.Mono.FiberModel.levPair v ℓ y := xyL.injective hXeq
      subst hX'
      obtain ⟨hX1, hX2⟩ := (hplanInt_iff _).mp hX
      refine ⟨hpbox' y hX1 ?_ ?_, ?_⟩
      · simpa only [xyL.symm_apply_apply] using h2
      · simpa only [xyL.symm_apply_apply] using h3
      · simp only [Set.mem_union, Set.mem_ofPred_eq, Work.Drive.Mono.FiberModel.levPair] at hX2 ⊢
        rcases hX2 with h | h
        · rcases lt_abs.mp h with h' | h'
          · exact Or.inl (Or.inl (by linarith))
          · exact Or.inl (Or.inr (by linarith))
        · exact Or.inr h
  have himageA : Λ '' closure (tiltedLevelRemoved s c σ u v h ℓ lam) = solid := by
    ext P
    constructor
    · rintro ⟨y, hy, rfl⟩; exact (hclA y).mp hy
    · intro hP
      refine ⟨Λ.symm P, (hclA (Λ.symm P)).mpr ?_, Λ.apply_symm_apply P⟩
      rwa [Λ.apply_symm_apply]
  have himageB : Λ '' interior (tiltedLevelRemoved s c σ u v h ℓ lam) = opensolid := by
    ext P
    constructor
    · rintro ⟨y, hy, rfl⟩; exact (hintA y).mp hy
    · intro hP
      refine ⟨Λ.symm P, (hintA (Λ.symm P)).mpr ?_, Λ.apply_symm_apply P⟩
      rwa [Λ.apply_symm_apply]
  have hfrontA : Λ '' frontier (tiltedLevelRemoved s c σ u v h ℓ lam) = solid \ opensolid := by
    rw [frontier, Set.image_sdiff Λ.injective, himageA, himageB]
  -- the vertical shift removing the lower graph
  set Θ : R3 → R3 := fun P => cmk (cproj P) (clast P
      - Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ (xyL.symm (cproj P))) with hΘ
  set Θi : R3 → R3 := fun P => cmk (cproj P) (clast P
      + Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ (xyL.symm (cproj P))) with hΘi
  have hΘΘi : ∀ P : R3, Θ (Θi P) = P := by
    intro P
    rw [hΘ, hΘi]
    simp only [Work.Drive.Mono.cproj_cmk, Work.Drive.Mono.clast_cmk]
    rw [add_sub_cancel_right, Work.Drive.Mono.cmk_cproj_clast]
  have hΘiΘ : ∀ P : R3, Θi (Θ P) = P := by
    intro P
    rw [hΘ, hΘi]
    simp only [Work.Drive.Mono.cproj_cmk, Work.Drive.Mono.clast_cmk]
    rw [sub_add_cancel, Work.Drive.Mono.cmk_cproj_clast]
  have hΘinj : Function.Injective Θ := fun P Q h => by rw [← hΘiΘ P, h, hΘiΘ Q]
  have hhypo : WindowCase.hypo K G = {P : R3 | cproj P ∈ K ∧ 0 ≤ clast P ∧
      clast P ≤ G (cproj P)} := rfl
  have hhypoInt : WindowCase.hypoInt K G = {P : R3 | cproj P ∈ interior K ∧ 0 < clast P ∧
      clast P < G (cproj P)} := rfl
  have hΘsolid : Θ '' solid = {P : R3 | cproj P ∈ K ∧ 0 ≤ clast P ∧ clast P ≤ G (cproj P)} := by
    ext P
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      rw [hsolid] at hQ
      obtain ⟨hQ1, hQ2, hQ3⟩ := hQ
      rw [hΘ, hG]
      simp only [Work.Drive.Mono.cproj_cmk, Work.Drive.Mono.clast_cmk, Set.mem_ofPred_eq]
      refine ⟨hQ1, by linarith, by linarith⟩
    · intro hP
      rw [hG] at hP
      simp only [Set.mem_ofPred_eq] at hP
      obtain ⟨hP1, hP2, hP3⟩ := hP
      refine ⟨Θi P, ?_, hΘΘi P⟩
      rw [hsolid]
      simp only [Set.mem_ofPred_eq, hΘi]
      rw [Work.Drive.Mono.cproj_cmk, Work.Drive.Mono.clast_cmk]
      refine ⟨hP1, by linarith, by linarith⟩
  have hΘopen : Θ '' opensolid = {P : R3 | cproj P ∈ interior K ∧ 0 < clast P ∧
      clast P < G (cproj P)} := by
    ext P
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      rw [hopensolid] at hQ
      obtain ⟨hQ1, hQ2, hQ3⟩ := hQ
      rw [hΘ, hG]
      simp only [Work.Drive.Mono.cproj_cmk, Work.Drive.Mono.clast_cmk, Set.mem_ofPred_eq]
      refine ⟨hQ1, by linarith, by linarith⟩
    · intro hP
      rw [hG] at hP
      simp only [Set.mem_ofPred_eq] at hP
      obtain ⟨hP1, hP2, hP3⟩ := hP
      refine ⟨Θi P, ?_, hΘΘi P⟩
      rw [hopensolid]
      simp only [Set.mem_ofPred_eq, hΘi]
      rw [Work.Drive.Mono.cproj_cmk, Work.Drive.Mono.clast_cmk]
      refine ⟨hP1, by linarith, by linarith⟩
  have hfrontC : Θ '' (solid \ opensolid) = frontier (WindowCase.hypo K G) := by
    have hfr : frontier (WindowCase.hypo K G) = WindowCase.hypo K G \ WindowCase.hypoInt K G := by
      rw [frontier, (WindowCase.hypo_isClosed hKcomp hGc).closure_eq, WindowCase.interior_hypo_eq hGc]
    rw [hfr, hhypo, hhypoInt, Set.image_sdiff hΘinj, hΘsolid, hΘopen]
  have hfront : frontier (tiltedLevelRemoved s c σ u v h ℓ lam)
      = (fun P : R3 => Λ.symm (Θi P)) '' frontier (WindowCase.hypo K G) := by
    have h1 : (fun P : R3 => Θ (Λ P)) '' frontier (tiltedLevelRemoved s c σ u v h ℓ lam)
        = frontier (WindowCase.hypo K G) := by
      rw [← hfrontC, ← hfrontA, Set.image_image]
    have h2 : (fun P : R3 => Λ.symm (Θi P)) ''
        ((fun P : R3 => Θ (Λ P)) '' frontier (tiltedLevelRemoved s c σ u v h ℓ lam))
        = frontier (tiltedLevelRemoved s c σ u v h ℓ lam) := by
      rw [Set.image_image]
      have hfun : (fun x : R3 => Λ.symm (Θi (Θ (Λ x)))) = id := by
        funext y
        simp only [Function.comp_apply, id_eq]
        rw [hΘiΘ, Λ.symm_apply_apply]
      rw [hfun, Set.image_id]
    rw [← h2, h1]
  -- the transport of the sphere
  have hsphere' : Work.InnermostDisk.IsEmbeddedSphere (frontier (WindowCase.hypo K G)) := hsphere
  obtain ⟨eSph, heSph_inj, heSph_range⟩ := hsphere'
  set V : Set R3 := {P : R3 | cproj P ∈ xyL ''
      Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ} with hV
  have hclsub : closure (Work.Drive.Mono.FiberModel.planarImage s c σ u v h ℓ lam)
      ⊆ Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ :=
    fun X hX => ((hplan_iff X).mp hX).1
  have hVsub : ∀ Z ∈ K, Z ∈ xyL '' Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ := by
    rintro Z hZ
    rw [hK] at hZ
    obtain ⟨X, hX, rfl⟩ := hZ
    exact ⟨X, hclsub hX, rfl⟩
  have hFMin_c : ContinuousOn (fun P : R3 => Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ
      (xyL.symm (cproj P))) V := by
    refine hminc.comp ?_ ?_
    · exact ((xyLC.symm.continuous.comp
        continuous_cproj)).continuousOn
    · intro P hP
      simp only [hV, Set.mem_ofPred_eq, Set.mem_image] at hP
      obtain ⟨X, hX, hXeq⟩ := hP
      change xyL.symm (cproj P) ∈ Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ
      rw [← hXeq, xyL.symm_apply_apply]
      exact hX
  have hΘi_cont : ContinuousOn (fun P : R3 => Θi P) V := by
    have hpair : ContinuousOn (fun P : R3 => (cproj P, clast P
        + Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ (xyL.symm (cproj P)))) V :=
      (continuous_cproj.continuousOn).prodMk ((continuous_clast.continuousOn).add hFMin_c)
    rw [hΘi]
    exact Work.Drive.Mono.continuous_cmk.comp_continuousOn hpair
  have hΨ_cont : ContinuousOn (fun P : R3 => Λ.symm (Θi P)) V := by
    refine ((Λ.symm.continuous).continuousOn).comp hΘi_cont (fun P _ => Set.mem_univ (Θi P))
  have hfrontV : ∀ P ∈ frontier (WindowCase.hypo K G), P ∈ V := by
    intro P hP
    rw [hV]
    have h1 : P ∈ WindowCase.hypo K G := by
      have h := frontier_subset_closure hP
      rwa [(WindowCase.hypo_isClosed hKcomp hGc).closure_eq] at h
    simp only [WindowCase.hypo, Set.mem_ofPred_eq] at h1
    exact hVsub _ h1.1
  refine ⟨⟨fun u => Λ.symm (Θi (eSph u)), ?_⟩, ?_, ?_⟩
  · show Continuous (fun u : Metric.sphere (0 : R3) 1 => Λ.symm (Θi (eSph u)))
    refine hΨ_cont.comp_continuous eSph.continuous (fun u => ?_)
    exact hfrontV (eSph u) (by rw [← heSph_range]; exact Set.mem_range_self u)
  · intro u v huv
    show u = v
    simp only [ContinuousMap.coe_mk] at huv
    have h2 : (fun P : R3 => Θ (Λ P)) (Λ.symm (Θi (eSph u)))
        = (fun P : R3 => Θ (Λ P)) (Λ.symm (Θi (eSph v))) := by rw [huv]
    have h3 : eSph u = eSph v := by
      simpa only [Function.comp_apply, Λ.apply_symm_apply, hΘΘi] using h2
    exact heSph_inj h3
  · show Set.range (fun u : Metric.sphere (0 : R3) 1 => Λ.symm (Θi (eSph u)))
        = frontier (tiltedLevelRemoved s c σ u v h ℓ lam)
    have hr : Set.range (fun u : Metric.sphere (0 : R3) 1 => Λ.symm (Θi (eSph u)))
        = (fun P : R3 => Λ.symm (Θi P)) '' Set.range eSph := by
      rw [show (fun u : Metric.sphere (0 : R3) 1 => Λ.symm (Θi (eSph u)))
          = (fun P : R3 => Λ.symm (Θi P)) ∘ eSph from rfl]
      exact Set.range_comp _ _
    rw [hr, heSph_range]
    exact hfront.symm

end Window

/-- **The frontier of a level of the tilted sweep is a single embedded sphere in the two-sided
(`one-sphere window`) regime.**  This is the lemma requested by the caller; the work is in
`Work.Drive.Mono.window_sphere` above. -/
theorem frontier_isEmbeddedSphere_of_twoSide (s : ℝ)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (v : LeanEval.KnotTheory.PardonDistortion.R3) (h : ℝ)
    (ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ) (lam : ℝ)
    (hv : ‖v‖ = 1) (hh : 0 < h) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    (hedge : ∀ (i : Fin 3) (ε : Fin 3 → Bool),
      lam = ℓ (WithLp.toLp 2 (fun k : Fin 3 => c k +
        (if k = σ i then (0:ℝ) else
          (if ε (σ.symm k) then 1 else -1) * Submission.boxSide (σ.symm k) * s))) →
      ℓ (EuclideanSpace.single (σ i) (1 : ℝ)) ≠ 0)
    (hvertex : ∀ ε : Fin 3 → Bool,
      lam ≠ ℓ (WithLp.toLp 2 (fun j : Fin 3 => c j +
        (if ε (σ.symm j) then 1 else -1) * Submission.boxSide (σ.symm j) * s)))
    (hseam : ((∃ y ∈ closure (Submission.PBox s c σ),
          inner ℝ v y = inner ℝ v c + u + h ∧ ℓ y = lam) →
        (∃ z ∈ Submission.PBox s c σ,
          inner ℝ v z = inner ℝ v c + u + h ∧ lam < ℓ z)) ∧
      ((∃ y ∈ closure (Submission.PBox s c σ),
          inner ℝ v y = inner ℝ v c + u - h ∧ ℓ y = lam) →
        (∃ z ∈ Submission.PBox s c σ,
          inner ℝ v z = inner ℝ v c + u - h ∧ lam < ℓ z)) ∧
      ((∃ y ∈ closure (Submission.PBox s c σ),
          |inner ℝ v y - (inner ℝ v c + u)| ≤ h ∧ ℓ y = lam) →
        (∃ z ∈ Submission.PBox s c σ,
          |inner ℝ v z - (inner ℝ v c + u)| ≤ h ∧ lam < ℓ z)))
    (hwallP : ∃ y ∈ Submission.PBox s c σ,
      inner ℝ v c + u + h < inner ℝ v y ∧ lam < ℓ y)
    (hwallM : ∃ y ∈ Submission.PBox s c σ,
      inner ℝ v y < inner ℝ v c + u - h ∧ lam < ℓ y) :
    Work.InnermostDisk.IsEmbeddedSphere
      (frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) := by
  obtain ⟨y, hy, hyp, hyl⟩ := hwallP
  obtain ⟨y', hy', hy'p, hy'l⟩ := hwallM
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hv
    exact absurd hv (by norm_num)
  -- `hwallP` produces a point of the open box, so `s` is positive
  have hs : 0 < s := by
    have h0 := (Submission.mem_PBox.mp hy) 0
    rw [Submission.boxSide_zero, one_mul] at h0
    exact lt_of_le_of_lt (abs_nonneg _) h0
  exact window_sphere (s := s) (c := c) (σ := σ) (u := u) (v := v) (h := h) (ℓ := ℓ) (lam := lam)
    hs hv0 hh hℓv hℓne ⟨y, hy, hyp⟩ ⟨y', hy', hy'p⟩ ⟨y, hy, hyp, hyl⟩ ⟨y', hy', hy'p, hy'l⟩


end

end Work.Drive.Mono
