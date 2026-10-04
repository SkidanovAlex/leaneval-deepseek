import Mathlib
import Submission.Work.Diff.EXT.ricCore

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Continuity in the parameter of a spatial derivative (`EXT`)

`Work.Diff.EXT.continuousAt_mvfderiv_family`: if `Φ : ℝ × M → F` is jointly `C^∞` near `(t₀, x)` and
`v ∈ TₓM`, then `t ↦ d_y Φ(t, ·)(v)` is continuous at `t₀`.

The proof fixes the preferred chart at `x`.  Writing `ψ(t,u) = Φ(t, (extChartAt I x).symm u)` for the
chart representative and `u₀ = (extChartAt I x) x` for the chart coordinates of `x`:

* (`mvfderiv_slice_eq_fderivWithin`) for `t` near `t₀` the manifold derivative of the slice
  `y ↦ Φ (t, y)` is the ordinary derivative of the coordinate representative,
  `d% (Φ (t, ·)) x v = fderivWithin ℝ (fun u ↦ ψ (t, u)) (range I) u₀ v`;
* (`contDiffWithinAt_chartRep`, `eventually_mdifferentiableAt_slice`) the chart representative `ψ` is
  `C¹` within `univ × range I`, and each slice is differentiable at `x` for `t` near `t₀`;
* (`continuousAt_fderivWithin_slice`) for a function that is `C¹` within `univ × range I` and whose
  `t`-slices are differentiable within `range I`, the `t`-slice of `fderivWithin` is continuous;
* (`fderivWithin_slice_eq`) the chain rule identifies the within-`range I` derivative of the slice
  `u ↦ ψ (t, u)` with `fderivWithin ℝ ψ (univ × range I) (t, u₀) ∘ inr`.

No `Boundaryless` assumption on the model with corners is needed: everything is phrased with
`fderivWithin` on the sets `range I` and `univ × range I`, and `UniqueDiffWithinAt ℝ (range I) _`
is supplied by `ModelWithCorners.uniqueDiffOn`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Work.Diff.EXT

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set Filter

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Reading `mvfderiv` of a `t`-slice in the chart at `x`.**  For `g : M → F` differentiable at
`x`, the manifold derivative of its slice is the ordinary derivative of the coordinate
representative `u ↦ Φ (t, (extChartAt I x).symm u)` at the chart coordinates of `x`. -/
lemma mvfderiv_slice_eq_fderivWithin {Φ : ℝ × M → F} {t : ℝ} {x : M} {v : TangentSpace I x}
    (h : MDifferentiableAt I 𝓘(ℝ,F) (fun y : M => Φ (t, y)) x) :
    mvfderiv I (fun y : M => Φ (t, y)) x v
      = fderivWithin ℝ (fun u : E => Φ (t, (extChartAt I x).symm u)) (range I)
          ((extChartAt I x) x) v := by
  rw [MDifferentiableAt.mvfderiv h]
  simp only [writtenInExtChartAt, Function.comp_def, extChartAt_self_apply, modelWithCornersSelf_coe,
    Function.id_def]
  rfl

/-- **The chart representative is `C¹` within `univ × range I`.**  If `Φ` is jointly smooth at
`(t₀, x)` then `(t, u) ↦ Φ (t, (extChartAt I x).symm u)` is `C¹` at
`(t₀, (extChartAt I x) x)` within `univ × range I`. -/
lemma contDiffWithinAt_chartRep {Φ : ℝ × M → F} {t₀ : ℝ} {x : M}
    (hΦ : ContMDiffAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,F) ∞ Φ (t₀, x)) :
    ContDiffWithinAt ℝ 1 (fun p : ℝ × E => Φ (p.1, (extChartAt I x).symm p.2))
      (univ ×ˢ range I) (t₀, (extChartAt I x) x) := by
  have hΦw : ContMDiffWithinAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,F) 1 Φ univ (t₀, x) :=
    (hΦ.of_le (show (1:ℕ∞ω) ≤ ∞ from by norm_num)).contMDiffWithinAt
  have hsnd : ContMDiffWithinAt (𝓘(ℝ,ℝ).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) 1
      (Prod.snd : ℝ × E → E) (univ ×ˢ range I) (t₀, (extChartAt I x) x) := contMDiffWithinAt_snd
  have hsymm : ContMDiffWithinAt (𝓘(ℝ,ℝ).prod 𝓘(ℝ,E)) I 1
      (fun p : ℝ × E => (extChartAt I x).symm p.2) (univ ×ˢ range I) (t₀, (extChartAt I x) x) :=
    (contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := 1) x).comp
      (t₀, (extChartAt I x) x) hsnd (fun p hp => hp.2)
  have hσ : ContMDiffWithinAt (𝓘(ℝ,ℝ).prod 𝓘(ℝ,E)) (𝓘(ℝ,ℝ).prod I) 1
      (fun p : ℝ × E => (p.1, (extChartAt I x).symm p.2)) (univ ×ˢ range I)
      (t₀, (extChartAt I x) x) :=
    contMDiffWithinAt_fst.prodMk hsymm
  have h1 : ContMDiffWithinAt (𝓘(ℝ,ℝ).prod 𝓘(ℝ,E)) 𝓘(ℝ,F) 1
      ((fun p : ℝ × M => Φ p) ∘ (fun p : ℝ × E => (p.1, (extChartAt I x).symm p.2)))
      (univ ×ˢ range I) (t₀, (extChartAt I x) x) :=
    ContMDiffWithinAt.comp_of_eq (n := 1) (t := univ) (s := univ ×ˢ range I)
      hΦw hσ (fun p hp => Set.mem_univ _) (by simp [extChartAt_to_inv])
  have h2 : ContMDiffWithinAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ,F) 1
      (fun p : ℝ × E => Φ (p.1, (extChartAt I x).symm p.2)) (univ ×ˢ range I)
      (t₀, (extChartAt I x) x) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    simpa only [Function.comp_def] using h1
  exact contMDiffWithinAt_iff_contDiffWithinAt.mp h2

/-- **Slices of a jointly smooth family are eventually differentiable.**  If `Φ` is jointly smooth
at `(t₀, x)` then for `t` near `t₀` the slice `y ↦ Φ (t, y)` is differentiable at `x`. -/
lemma eventually_mdifferentiableAt_slice {Φ : ℝ × M → F} {t₀ : ℝ} {x : M}
    (hΦ : ContMDiffAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,F) ∞ Φ (t₀, x)) :
    ∀ᶠ t in 𝓝 t₀, MDifferentiableAt I 𝓘(ℝ,F) (fun y : M => Φ (t, y)) x := by
  haveI : IsManifold I 1 M := IsManifold.of_le (show (1:ℕ∞ω) ≤ ∞ from by norm_num)
  haveI : IsManifold (𝓘(ℝ,ℝ).prod I) 1 (ℝ × M) := inferInstance
  haveI : IsManifold 𝓘(ℝ,F) 1 F := inferInstance
  have hloc : ∀ᶠ p in 𝓝 (t₀, x), ContMDiffAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,F) 1 Φ p :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := (1:ℕ∞ω)) (by decide)).mp (hΦ.of_le (by norm_num))
  filter_upwards [(continuousAt_id.prodMk continuousAt_const).eventually hloc] with t ht
  exact ((ht.comp x ((contMDiffAt_const (c := t)).prodMk contMDiffAt_id)).mdifferentiableAt
    (by norm_num))

/-- **Continuity in `t` of the `t`-slice of `fderivWithin`.**  If `Ψ` is `C¹` within
`univ × range I` at `(t₀, u₀)` with `u₀ ∈ range I`, then `t ↦ fderivWithin ℝ Ψ (univ × range I) (t, u₀)`
is continuous at `t₀`. -/
lemma continuousAt_fderivWithin_slice {Ψ : ℝ × E → F} {u₀ : E} {t₀ : ℝ}
    (hcd : ContDiffWithinAt ℝ 1 Ψ (univ ×ˢ range I) (t₀, u₀))
    (hu₀ : u₀ ∈ range I) :
    ContinuousAt (fun t : ℝ => fderivWithin ℝ Ψ (univ ×ˢ range I) (t, u₀)) t₀ := by
  have huniq : UniqueDiffOn ℝ (univ ×ˢ range I) :=
    UniqueDiffOn.prod (uniqueDiffOn_univ : UniqueDiffOn ℝ (univ : Set ℝ)) I.uniqueDiffOn
  have hmem : (t₀, u₀) ∈ (univ ×ˢ range I) := ⟨trivial, hu₀⟩
  have hcw : ContinuousWithinAt (fderivWithin ℝ Ψ (univ ×ˢ range I)) (univ ×ˢ range I) (t₀, u₀) :=
    hcd.continuousWithinAt_fderivWithin huniq (by norm_num) hmem
  have hf : ContinuousWithinAt (fun t : ℝ => (t, u₀)) univ t₀ :=
    (continuousAt_id.prodMk continuousAt_const).continuousWithinAt
  have hcomp : ContinuousWithinAt ((fderivWithin ℝ Ψ (univ ×ˢ range I))
      ∘ (fun t : ℝ => (t, u₀))) univ t₀ :=
    hcw.comp (f := fun t : ℝ => (t, u₀)) (x := t₀) hf (fun t _ => ⟨trivial, hu₀⟩)
  exact (continuousWithinAt_univ _ _).mp (by simpa only [Function.comp_def] using hcomp)

/-- **Eventual differentiability within `univ × range I`.**  If `Ψ` is `C¹` within `univ × range I`
at `(t₀, u₀)` for `u₀ ∈ range I`, then for `t` near `t₀` the derivative of `Ψ` within
`univ × range I` at `(t, u₀)` exists. -/
lemma eventually_hasFDerivWithinAt_chartRep {Ψ : ℝ × E → F} {u₀ : E} {t₀ : ℝ}
    (hcd : ContDiffWithinAt ℝ 1 Ψ (univ ×ˢ range I) (t₀, u₀))
    (hu₀ : u₀ ∈ range I) :
    ∀ᶠ t in 𝓝 t₀, HasFDerivWithinAt Ψ (fderivWithin ℝ Ψ (univ ×ˢ range I) (t, u₀))
      (univ ×ˢ range I) (t, u₀) := by
  have hmem : (t₀, u₀) ∈ (univ ×ˢ range I) := ⟨trivial, hu₀⟩
  have h1 : ∀ᶠ y in 𝓝[univ ×ˢ range I] (t₀, u₀), ContDiffWithinAt ℝ 1 Ψ (univ ×ˢ range I) y := by
    have h := hcd.eventually (by decide)
    rwa [show insert (t₀, u₀) (univ ×ˢ range I) = (univ ×ˢ range I) from Set.insert_eq_of_mem hmem]
      at h
  rw [eventually_nhdsWithin_iff] at h1
  have htend : Tendsto (fun t : ℝ => (t, u₀)) (𝓝 t₀) (𝓝 (t₀, u₀)) :=
    continuousAt_id.prodMk continuousAt_const
  filter_upwards [htend.eventually h1] with t ht
  exact ((ht ⟨trivial, hu₀⟩).differentiableWithinAt (by norm_num)).hasFDerivWithinAt

/-- **Chain rule for the `t`-slices of `fderivWithin`.**  The derivative of `u ↦ Ψ (t, u)` within
`range I` at `u₀` is the second partial derivative of `Ψ` at `(t, u₀)`, i.e. the derivative of `Ψ`
within `univ × range I` composed with the inclusion `inr`. -/
lemma fderivWithin_slice_eq (Ψ : ℝ × E → F) {t : ℝ} {u₀ : E}
    (h : HasFDerivWithinAt Ψ (fderivWithin ℝ Ψ (univ ×ˢ range I) (t, u₀))
      (univ ×ˢ range I) (t, u₀))
    (huniq : UniqueDiffWithinAt ℝ (range I) u₀) :
    fderivWithin ℝ (fun u : E => Ψ (t, u)) (range I) u₀
      = (fderivWithin ℝ Ψ (univ ×ˢ range I) (t, u₀)).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
  have h2 : HasFDerivWithinAt (fun u : E => (t, u)) (ContinuousLinearMap.inr ℝ ℝ E) (range I) u₀ :=
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) t u₀).hasFDerivWithinAt
  have hcomp : HasFDerivWithinAt (fun u : E => Ψ (t, u))
      ((fderivWithin ℝ Ψ (univ ×ˢ range I) (t, u₀)).comp (ContinuousLinearMap.inr ℝ ℝ E))
      (range I) u₀ := by
    have h' := h.comp u₀ h2 (fun u hu => ⟨trivial, hu⟩)
    simpa only [Function.comp_def] using h'
  exact hcomp.fderivWithin huniq

/-- **Continuity in the parameter of a spatial derivative.**  If `Φ : ℝ × M → F` is jointly
`C^∞` near `(t₀, x)` and `v ∈ TₓM`, then `t ↦ d_y Φ(t, ·)(v)` (the spatial derivative at the fixed
point `x` in the fixed direction `v`) is continuous at `t₀`. -/
theorem continuousAt_mvfderiv_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : ℝ × M → F} {t₀ : ℝ} {x : M}
    (hΦ : JointSmoothAt I M Φ t₀ x) (v : TangentSpace I x) :
    ContinuousAt (fun t : ℝ => mvfderiv I (fun y : M => Φ (t, y)) x v) t₀ := by
  -- the chart representative `Ψ` of `Φ` at `x`
  set Ψ : ℝ × E → F := fun p => Φ (p.1, (extChartAt I x).symm p.2) with hΨdef
  have hu₀mem : (extChartAt I x) x ∈ range I :=
    (extChartAt_target_subset_range x) (mem_extChartAt_target x)
  have huniqI : UniqueDiffWithinAt ℝ (range I) ((extChartAt I x) x) :=
    I.uniqueDiffOn.uniqueDiffWithinAt hu₀mem
  have hΨcd : ContDiffWithinAt ℝ 1 Ψ (univ ×ˢ range I) (t₀, (extChartAt I x) x) := by
    rw [hΨdef]
    exact contDiffWithinAt_chartRep (I := I) (M := M) hΦ
  -- continuity of `t ↦ (d Ψ (t, u₀)) (0, v)` (`0` dropped by `inr`)
  have hcont : ContinuousAt (fun t : ℝ =>
      (fderivWithin ℝ Ψ (univ ×ˢ range I) (t, (extChartAt I x) x))
        (ContinuousLinearMap.inr ℝ ℝ E v)) t₀ :=
    (continuousAt_fderivWithin_slice (I := I) hΨcd hu₀mem).clm_apply continuousAt_const
  refine hcont.congr_of_eventuallyEq ?_
  -- for `t` near `t₀`, the manifold derivative of the slice is that expression
  have hev1 : ∀ᶠ t in 𝓝 t₀, MDifferentiableAt I 𝓘(ℝ,F) (fun y : M => Φ (t, y)) x :=
    eventually_mdifferentiableAt_slice (I := I) (M := M) hΦ
  have hev2 : ∀ᶠ t in 𝓝 t₀,
      HasFDerivWithinAt Ψ (fderivWithin ℝ Ψ (univ ×ˢ range I) (t, (extChartAt I x) x))
        (univ ×ˢ range I) (t, (extChartAt I x) x) :=
    eventually_hasFDerivWithinAt_chartRep hΨcd hu₀mem
  filter_upwards [hev1, hev2] with t h1 h2
  rw [mvfderiv_slice_eq_fderivWithin (I := I) (M := M) h1]
  rw [show (fun u : E => Φ (t, (extChartAt I x).symm u)) = (fun u : E => Ψ (t, u)) from by
        funext u; rw [hΨdef]]
  rw [fderivWithin_slice_eq (I := I) Ψ h2 huniqI]
  exact ContinuousLinearMap.comp_apply _ _ v

end Work.Diff.EXT
