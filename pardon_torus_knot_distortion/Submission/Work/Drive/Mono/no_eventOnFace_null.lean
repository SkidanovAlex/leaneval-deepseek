import Mathlib
import Submission.Work.Drive.Mono.Band.BandChartDefs
import Submission.Work.Drive.Mono.Band.HeightGoodDefs
import Submission.Work.Drive.Mono.Band.finite_critSet_isCompact
import Submission.Work.Drive.Mono.Band.heightGood_open
import Submission.Work.Drive.Mono.Geom2Defs

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory
open scoped _root_.Topology

noncomputable section

/-!
# Almost every `(h, τ)` has no critical point of the swept height on a slab face

This file proves `Work.Drive.Mono.no_eventOnFace_null`.

## The mathematics

Fix the slab direction `v`, an orthonormal pair `a₀, b₀` of `v^⊥` and the level
`K = ⟪v,c⟫ + u`.  For a projective parameter `τ` let `n(τ) = dirOf τ a₀ b₀` and let
`F_τ = sweepHeight ψ (innerSL ℝ (n τ)) = heightOf ψ (n τ)` be the height in the direction `n τ`,
read in the parameter plane of the parametrisation `par ψ`.

The bad set `B` consists of the pairs `(h,τ)` for which `n τ` is a `HeightGood` direction and there
is a critical point `p` of `F_τ` with image in the box whose `v`-height is the face level `K ± h`.

* For a **good** `τ` the critical points of `F_τ` inside the fundamental square are finite
  (`finite_critSet_isCompact`, using the nondegeneracy clause of `HeightGood`), so the set of `h`
  with `(h,τ) ∈ B` — the image of that finite set under `p ↦ |⟪v, par ψ p⟫ - K|` — is finite, hence
  null.
* The set `G` of good `τ` is **open** (`heightGood_open`).  Covering `G` by countably many closed
  intervals `[a,b] ⊆ G` with rational endpoints, Tonelli/Fubini on the compact sets
  `slab '' (critSet ∩ ([a,b] × fundSquare))` gives the nullity, since every `τ`-section of such a
  compact set is finite.

Finally the bad set is contained in that countable union, because every critical point of `F_τ` can
be moved into the fundamental square by a period (which preserves criticality, the value and the
image on the surface), and because `G` is open.
-/

namespace NoEventOnFace

open MeasureTheory

/-! ## The derivative of the height in a direction -/

/-- The derivative of the height in direction `n` is the `n`-component of the derivative of the
parametrisation. -/
theorem fderiv_heightOf_eq_comp (ψ : Submission.Diffeo) (n : R3) (q : ℝ × ℝ) :
    fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n) q
      = (innerSL ℝ n).comp (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q) := by
  have h1 : Work.Drive.EpsForm.heightOf ψ n
      = ⇑(innerSL ℝ n) ∘ Work.BoxShrink.Pinch.par ψ := by
    funext q
    rw [Function.comp_apply, Work.Drive.EpsForm.heightOf, innerSL_apply_apply]
  rw [h1]
  rw [fderiv_comp (x := q) (f := Work.BoxShrink.Pinch.par ψ) (g := ⇑(innerSL ℝ n))
      ((innerSL ℝ n).differentiableAt)
      ((Work.Smooth.Morse.param_contDiff ψ).differentiable (by simp) q)]
  rw [ContinuousLinearMap.fderiv]

/-- The parametrised projective direction `τ ↦ dirOf τ a₀ b₀` is continuous. -/
theorem continuous_dirOf (a₀ b₀ : R3) (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) :
    Continuous fun τ : ℝ => Work.Drive.Mono.Band.dirOf τ a₀ b₀ := by
  have hdene : ∀ τ : ℝ, ‖τ • a₀ + b₀‖ ≠ 0 := by
    intro τ
    have h1 : inner ℝ b₀ (τ • a₀ + b₀) = 1 :=
      Work.Drive.Mono.Band.inner_b₀_add_dirOf ha hb hab τ
    intro h0
    rw [norm_eq_zero] at h0
    rw [h0, inner_zero_right] at h1
    exact one_ne_zero h1.symm
  unfold Work.Drive.Mono.Band.dirOf
  exact ((continuous_norm.comp (by fun_prop)).inv₀ hdene).smul (by fun_prop)

/-- **Joint continuity of `(τ,p) ↦ dF_τ(p)`**, the derivative of the height in the direction
`dirOf τ a₀ b₀`. -/
theorem continuous_fderiv_heightOf_dirOf (ψ : Submission.Diffeo) (a₀ b₀ : R3)
    (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0) :
    Continuous (fun x : ℝ × (ℝ × ℝ) =>
      fderiv ℝ (Work.Drive.EpsForm.heightOf ψ (Work.Drive.Mono.Band.dirOf x.1 a₀ b₀)) x.2) := by
  have hdir : Continuous fun τ : ℝ => Work.Drive.Mono.Band.dirOf τ a₀ b₀ :=
    continuous_dirOf a₀ b₀ ha hb hab
  have hL : Continuous (fun x : ℝ × (ℝ × ℝ) =>
      (innerSL ℝ) (Work.Drive.Mono.Band.dirOf x.1 a₀ b₀)) :=
    (ContinuousLinearMap.continuous (innerSL ℝ)).comp (hdir.comp continuous_fst)
  have hM : Continuous (fun x : ℝ × (ℝ × ℝ) =>
      fderiv ℝ (Work.BoxShrink.Pinch.par ψ) x.2) :=
    (((Work.BoxShrink.Pinch.par_contDiff ψ).continuous_fderiv (by simp)).comp continuous_snd)
  have hcomp : Continuous (fun x : ℝ × (ℝ × ℝ) =>
      ((ContinuousLinearMap.compL ℝ (ℝ × ℝ) R3 ℝ)
        ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf x.1 a₀ b₀))
          (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) x.2))) :=
    (continuous_const.clm_apply hL).clm_apply hM
  refine hcomp.congr (fun x => ?_)
  show ((ContinuousLinearMap.compL ℝ (ℝ × ℝ) R3 ℝ)
      ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf x.1 a₀ b₀))
        (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) x.2)) = _
  rw [ContinuousLinearMap.compL_apply]
  exact (fderiv_heightOf_eq_comp ψ (Work.Drive.Mono.Band.dirOf x.1 a₀ b₀) x.2).symm

/-! ## The critical locus of the family of heights -/

/-- The set of pairs `(τ,p)` such that `p` is a critical point of the height in the direction
`dirOf τ a₀ b₀`. -/
def critSet (ψ : Submission.Diffeo) (a₀ b₀ : R3) : Set (ℝ × (ℝ × ℝ)) :=
  {x | fderiv ℝ (Work.Drive.EpsForm.heightOf ψ (Work.Drive.Mono.Band.dirOf x.1 a₀ b₀)) x.2 = 0}

theorem isClosed_critSet (ψ : Submission.Diffeo) (a₀ b₀ : R3) (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) : IsClosed (critSet ψ a₀ b₀) :=
  isClosed_eq (continuous_fderiv_heightOf_dirOf ψ a₀ b₀ ha hb hab) continuous_const

/-- The critical locus over a compact set of parameters and a compact box of parameters is
compact. -/
theorem isCompact_critSet_inter (ψ : Submission.Diffeo) (a₀ b₀ : R3) (ha : ‖a₀‖ = 1)
    (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0) (C : Set ℝ) (hC : IsCompact C)
    (D : Set (ℝ × ℝ)) (hD : IsCompact D) :
    IsCompact (critSet ψ a₀ b₀ ∩ (C ×ˢ D)) :=
  (hC.prod hD).inter_left (isClosed_critSet ψ a₀ b₀ ha hb hab)

/-! ## The slab map of the sweep -/

/-- The map that records, for a point `(τ,p)` of parameter space, the face level `|⟪v,par ψ p⟫ - K|`
and the parameter `τ`. -/
def slab (ψ : Submission.Diffeo) (v : R3) (K : ℝ) : ℝ × (ℝ × ℝ) → ℝ × ℝ :=
  fun x => (|inner ℝ v (Work.BoxShrink.Pinch.par ψ x.2) - K|, x.1)

theorem continuous_slab (ψ : Submission.Diffeo) (v : R3) (K : ℝ) :
    Continuous (slab ψ v K) := by
  have h1 : Continuous (fun x : ℝ × (ℝ × ℝ) =>
      |inner ℝ v (Work.BoxShrink.Pinch.par ψ x.2) - K|) :=
    continuous_abs.comp (((innerSL ℝ v).continuous.comp
      ((Work.BoxShrink.Pinch.par_continuous ψ).comp continuous_snd)).sub continuous_const)
  exact h1.prodMk continuous_fst

/-- The `τ`-section of a set of pairs `(h,τ)`. -/
def prodSection (τ : ℝ) (S : Set (ℝ × ℝ)) : Set ℝ := {h | (h, τ) ∈ S}

/-- **The nullity of a compact piece.**  For a good set of parameters `C`, the image under the slab
map of the critical locus over `C` (intersected with the fundamental square) is null: all its
`τ`-sections are finite, so Tonelli/Fubini applies. -/
theorem slab_image_null (ψ : Submission.Diffeo) (v a₀ b₀ : R3) (K : ℝ)
    (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (C : Set ℝ) (hC : IsCompact C)
    (hgoodC : ∀ τ ∈ C,
      Work.Drive.Mono.Band.HeightGood ψ (Work.Drive.Mono.Band.dirOf τ a₀ b₀)) :
    (volume (slab ψ v K '' (critSet ψ a₀ b₀ ∩ (C ×ˢ Work.Drive.EpsForm.fundBox)))
      : ENNReal) = 0 := by
  set S : Set (ℝ × ℝ) :=
    slab ψ v K '' (critSet ψ a₀ b₀ ∩ (C ×ˢ Work.Drive.EpsForm.fundBox)) with hSdef
  have hK : IsCompact (critSet ψ a₀ b₀ ∩ (C ×ˢ Work.Drive.EpsForm.fundBox)) :=
    isCompact_critSet_inter ψ a₀ b₀ ha hb hab C hC Work.Drive.EpsForm.fundBox
      Work.Drive.EpsForm.isCompact_fundBox
  have hcomp : IsCompact S := hK.image (continuous_slab ψ v K)
  have hmeas : MeasurableSet S := hcomp.isClosed.measurableSet
  have hsec : ∀ τ : ℝ, (prodSection τ S).Finite := by
    intro τ
    by_cases hτ : τ ∈ C
    · have hgood : Work.Drive.Mono.Band.HeightGood ψ (Work.Drive.Mono.Band.dirOf τ a₀ b₀) :=
        hgoodC τ hτ
      have hnd : ∀ p : ℝ × ℝ,
          fderiv ℝ (Work.Drive.EpsForm.heightOf ψ (Work.Drive.Mono.Band.dirOf τ a₀ b₀)) p = 0 →
          Function.Injective (fderiv ℝ (fderiv ℝ
            (Work.Drive.EpsForm.heightOf ψ (Work.Drive.Mono.Band.dirOf τ a₀ b₀))) p) := by
        intro p hp
        have h1 : fderiv ℝ
            (Work.Drive.Mono.Band.heightIn ψ (Work.Drive.Mono.Band.dirOf τ a₀ b₀)) p = 0 := by
          rw [Work.Drive.Mono.Band.heightIn_eq_heightOf]
          exact hp
        have h2 := hgood.1 p h1
        rwa [Work.Drive.Mono.Band.heightIn_eq_heightOf] at h2
      have hfin : (Work.Drive.EpsForm.fundBox ∩ {p : ℝ × ℝ |
          fderiv ℝ (Work.Drive.EpsForm.heightOf ψ
            (Work.Drive.Mono.Band.dirOf τ a₀ b₀)) p = 0}).Finite :=
        Work.Drive.Mono.Band.finite_critSet_isCompact
          (Work.Drive.EpsForm.heightOf_contDiff_two ψ _) hnd Work.Drive.EpsForm.isCompact_fundBox
      refine ((hfin.image fun p : ℝ × ℝ =>
        |inner ℝ v (Work.BoxShrink.Pinch.par ψ p) - K|)).subset ?_
      rintro h ⟨x, hx, hxeq⟩
      obtain ⟨hxZ, hxC, hxbox⟩ := hx
      have hx1 : x.1 = τ := by
        have h := congrArg Prod.snd hxeq
        simpa only [hSdef, slab] using h
      have h2 : h = |inner ℝ v (Work.BoxShrink.Pinch.par ψ x.2) - K| := by
        have h := congrArg Prod.fst hxeq
        simpa only [hSdef, slab] using h.symm
      have hxZ' : fderiv ℝ (Work.Drive.EpsForm.heightOf ψ
          (Work.Drive.Mono.Band.dirOf τ a₀ b₀)) x.2 = 0 := by
        rw [← hx1]
        exact hxZ
      exact ⟨x.2, ⟨hxbox, hxZ'⟩, h2.symm⟩
    · have hempty : prodSection τ S = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro h ⟨x, hx, hxeq⟩
        have hx1 : x.1 = τ := by
          have h := congrArg Prod.snd hxeq
          simpa only [hSdef, slab] using h
        exact hτ (hx1 ▸ (Set.mem_prod.mp hx.2).1)
      rw [hempty]
      exact Set.finite_empty
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_apply_symm hmeas]
  have hzero : (fun τ : ℝ => volume ((fun h : ℝ => (h, τ)) ⁻¹' S)) = fun _ => 0 := by
    funext τ
    exact (hsec τ).measure_zero volume
  rw [hzero]
  simp

end NoEventOnFace

/-! ## The target -/

/-- **Almost every pair `(h, τ)` has no critical point of the swept height on a slab face.**

For almost every pair `(h, τ)` there is no point `p` of the parameter plane whose image lies in the
open box, at which the swept height `sweepHeight ψ (innerSL ℝ (dirOf τ a₀ b₀))` is critical and whose
`v`-height equals the level `⟪v,c⟫ + u ± h`.  Equivalently: off a null set of `(h,τ)`, no event of
the tilted sweep lies on a slab face — the `no IsEvent on a slab face` clause of
`Work.Drive.Final.GoodSweepData2`, at the wall functional `ℓ = innerSL ℝ (dirOf τ a₀ b₀)`.

The `HeightGood` hypothesis in the bad set is what makes this provable: for a *good* direction the
critical set of the swept height in the fundamental domain is **finite**
(`Work.Drive.Mono.Band.finite_critSet_isCompact` together with
`Work.Drive.EpsForm.eventually_eq_of_crit_nondegen`, after rewriting `sweepHeight ψ (innerSL ℝ n)` as
the height in direction `n`), so each `h`-slice is finite; and for the other `τ` the slice is empty.
Tonelli/Fubini then gives the nullity (the set is measurable: an analytic condition in `(h,τ,p)` over
a compact domain in `p`).  Periodicity of `fderiv` and of `sweepHeight` reduces `par⁻¹ (PBox)` to
that compact domain. -/
theorem no_eventOnFace_null
    (ψ : Submission.Diffeo) (s u : ℝ) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3))
    (v a₀ b₀ : LeanEval.KnotTheory.PardonDistortion.R3)
    (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0) :
    MeasureTheory.volume {(h, τ) : ℝ × ℝ |
        Work.Drive.Mono.Band.HeightGood ψ (Work.Drive.Mono.Band.dirOf τ a₀ b₀) ∧
        ∃ p : ℝ × ℝ,
        Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ ∧
        fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ
          ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀))) p = 0 ∧
        |inner ℝ v (Work.BoxShrink.Pinch.par ψ p) - (inner ℝ v c + u)| = h} = 0 := by
  classical
  set G : Set ℝ :=
    {τ | Work.Drive.Mono.Band.HeightGood ψ (Work.Drive.Mono.Band.dirOf τ a₀ b₀)} with hGdef
  -- ## the good parameters form an open set
  have hGopen : IsOpen G := by
    rw [isOpen_iff_mem_nhds]
    intro τ hτ
    have hτ' : Work.Drive.Mono.Band.HeightGood ψ (Work.Drive.Mono.Band.dirOf τ a₀ b₀) := hτ
    obtain ⟨ρ, hρ, hρgood⟩ := Work.Drive.Mono.Band.heightGood_open ψ hτ'
    have hev : ∀ᶠ τ' in nhds τ, ‖Work.Drive.Mono.Band.dirOf τ' a₀ b₀ -
        Work.Drive.Mono.Band.dirOf τ a₀ b₀‖ < ρ :=
      (NoEventOnFace.continuous_dirOf a₀ b₀ ha hb hab).continuousAt.eventually
        (Metric.ball_mem_nhds _ hρ)
    show {τ' : ℝ | Work.Drive.Mono.Band.HeightGood ψ
      (Work.Drive.Mono.Band.dirOf τ' a₀ b₀)} ∈ nhds τ
    exact Filter.mem_of_superset hev (fun τ' hτ' => hρgood _ hτ')
  -- ## a good parameter lies in a closed interval with rational endpoints contained in `G`
  have hcoverG : ∀ τ ∈ G, ∃ a b : ℚ, (a : ℝ) < τ ∧ τ < (b : ℝ) ∧
      Set.Icc (a : ℝ) (b : ℝ) ⊆ G := by
    intro τ hτ
    obtain ⟨ε, hε, hεG⟩ := Metric.isOpen_iff.mp hGopen τ hτ
    obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show τ - ε < τ by linarith)
    obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show τ < τ + ε by linarith)
    refine ⟨a, b, ha2, hb1, ?_⟩
    intro y hy
    apply hεG
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  -- ## the covering family of compact pieces
  set I : Set (ℚ × ℚ) := {q | Set.Icc (q.1 : ℝ) (q.2 : ℝ) ⊆ G} with hIdef
  -- ## the bad set is contained in the union
  have hsub : {x : ℝ × ℝ |
      Work.Drive.Mono.Band.HeightGood ψ (Work.Drive.Mono.Band.dirOf x.2 a₀ b₀) ∧
      ∃ p : ℝ × ℝ,
        Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ ∧
        fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ
          ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf x.2 a₀ b₀))) p = 0 ∧
        |inner ℝ v (Work.BoxShrink.Pinch.par ψ p) - (inner ℝ v c + u)| = x.1} ⊆
      ⋃ q : {q : ℚ × ℚ // q ∈ I},
        NoEventOnFace.slab ψ v (inner ℝ v c + u) ''
          (NoEventOnFace.critSet ψ a₀ b₀ ∩
            (Set.Icc (q.1.1 : ℝ) (q.1.2 : ℝ) ×ˢ Work.Drive.EpsForm.fundBox)) := by
    rintro ⟨h, τ⟩ ⟨hgood, p, hpbox, hpcrit, hpabs⟩
    have hpcrit' : fderiv ℝ (Work.Drive.EpsForm.heightOf ψ
        (Work.Drive.Mono.Band.dirOf τ a₀ b₀)) p = 0 := by
      have h := hpcrit
      rw [Work.Drive.EpsForm.sweepHeight_innerSL] at h
      exact h
    obtain ⟨p', hp'box, hp'crit, -, -, hp'par⟩ :=
      Work.Drive.EpsForm.exists_fundBox_of_crit ψ (Work.Drive.Mono.Band.dirOf τ a₀ b₀) hpcrit'
    have hτG : τ ∈ G := hgood
    obtain ⟨a, b, hab_lt, hb_gt, hIab⟩ := hcoverG τ hτG
    refine Set.mem_iUnion.mpr ⟨⟨(a, b), hIab⟩, ?_⟩
    refine ⟨(τ, p'), ⟨hp'crit, ⟨⟨hab_lt.le, hb_gt.le⟩, hp'box⟩⟩, ?_⟩
    show NoEventOnFace.slab ψ v (inner ℝ v c + u) (τ, p') = (h, τ)
    have hslab : NoEventOnFace.slab ψ v (inner ℝ v c + u) (τ, p') =
        (|inner ℝ v (Work.BoxShrink.Pinch.par ψ p') - (inner ℝ v c + u)|, τ) := rfl
    rw [hslab]
    exact Prod.ext (by rw [hp'par]; exact hpabs) rfl
  -- ## conclusion
  refine measure_mono_null hsub ?_
  rw [MeasureTheory.measure_iUnion_null_iff]
  intro q
  exact NoEventOnFace.slab_image_null ψ v a₀ b₀ (inner ℝ v c + u) ha hb hab
    (Set.Icc (q.1.1 : ℝ) (q.1.2 : ℝ)) isCompact_Icc (fun τ hτ => q.2 hτ)

end

end Work.Drive.Mono
