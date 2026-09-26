import Mathlib
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.Smooth.Morse.Regular.local_arc_snd

/-!
# The level set of the pulled-back function is locally an arc

`Work.Smooth.Morse.pullback ψ g = g ∘ param ψ` is the function `g` read in the parameter plane of
the embedded torus `F = ψ(standard torus)`.  This file proves `pullback_local_arc`: at a point `p`
where the pull-back takes the value `t` and the derivative of the pull-back is nonzero, the level
set `{pullback ψ g = t}` is, near `p`, the image of an injective continuous arc `σ : ℝ → ℝ × ℝ`
(defined on `(-1,1)`, with `σ 0 = p`), which moreover covers *all* points of the level set in a
ball of radius `ε` around `p`.

The mathematical input is the implicit function theorem: at a point where some partial derivative
of the pull-back is nonzero, the level set is locally the graph of a `C¹` function; parametrising
the graph by its first coordinate gives the arc.  The content of the file is

* `isInvertible_of_ne_zero` (private): a nonzero continuous linear functional `ℝ →L[ℝ] ℝ` is
  invertible (a continuous linear equivalence);
* `Work.Smooth.Morse.Regular.local_arc_snd` (proved in the sibling module
  `Submission.Work.Smooth.Morse.Regular.local_arc_snd`): the implicit function theorem gives the arc
  when the partial derivative in the *second* variable is invertible;
* `local_arc_of_fderiv_ne_zero` (private): if the total derivative is nonzero then one of the two
  partials is nonzero; the second-variable case is the lemma above, and the first-variable case is reduced to
  it by swapping the two coordinates (the swap of the parameter plane is an isometry, so no
  constant is lost);
* `pullback_local_arc`: the statement for `pullback ψ g`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped Topology

namespace Work.Smooth.Morse.Regular

/-- A nonzero continuous linear map `ℝ →L[ℝ] ℝ` is a continuous linear equivalence.  (It is
multiplication by the nonzero real number `g 1`.) -/
private theorem isInvertible_of_ne_zero {g : ℝ →L[ℝ] ℝ} (hg : g ≠ 0) : g.IsInvertible := by
  have hg_apply : ∀ x : ℝ, g x = x * g 1 := fun x => by
    simpa [smul_eq_mul] using map_smul g x (1 : ℝ)
  have hg1 : g 1 ≠ 0 := by
    intro h
    apply hg
    apply ContinuousLinearMap.ext
    intro x
    rw [hg_apply x, h, mul_zero]
    simp
  refine ContinuousLinearMap.IsInvertible.of_inverse (f := g)
    (g := ContinuousLinearMap.toSpanSingleton ℝ (g 1)⁻¹) ?_ ?_
  · apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    rw [hg_apply, mul_assoc, inv_mul_cancel₀ hg1, mul_one]
  · apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    rw [hg_apply, mul_assoc, mul_inv_cancel₀ hg1, mul_one]

/-- **Every regular point of a `C¹` function of two variables lies on a local arc of the level
set.**  If `f : ℝ × ℝ → ℝ` is `C¹` with `f p = t` and `fderiv ℝ f p ≠ 0`, then the level set
`{f = t}` is near `p` the image of an injective continuous arc through `p`, which covers every
point of the level set in a ball around `p`.

If the partial derivative in the second variable is nonzero this is `local_arc_snd` (the implicit
function theorem).  Otherwise the first partial derivative is nonzero, and the statement for `f` at
`p` follows from `local_arc_snd` applied to `f ∘ Prod.swap` at `Prod.swap p` -- whose second
partial derivative is the first partial derivative of `f` -- by swapping the coordinates back:
`Prod.swap` is a linear isometry, so the ball of radius `ε` is preserved. -/
private theorem local_arc_of_fderiv_ne_zero {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {p : ℝ × ℝ} {t : ℝ} (hp : f p = t) (hd : fderiv ℝ f p ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ σ : ℝ → ℝ × ℝ, σ 0 = p ∧
      ContinuousOn σ (Ioo (-1 : ℝ) 1) ∧ InjOn σ (Ioo (-1 : ℝ) 1) ∧
      (∀ s ∈ Ioo (-1 : ℝ) 1, f (σ s) = t) ∧
      (∀ q : ℝ × ℝ, f q = t → ‖q - p‖ < ε → ∃ s ∈ Ioo (-1 : ℝ) 1, σ s = q) := by
  set f' : ℝ × ℝ →L[ℝ] ℝ := fderiv ℝ f p with hf'_def
  have hsd : HasStrictFDerivAt f f' p := hf.contDiffAt.hasStrictFDerivAt (by norm_num)
  by_cases h2 : f' ∘L ContinuousLinearMap.inr ℝ ℝ ℝ = 0
  · -- the second partial derivative vanishes, so the first one does not
    have h1 : f' ∘L ContinuousLinearMap.inl ℝ ℝ ℝ ≠ 0 := by
      intro h1
      apply hd
      apply ContinuousLinearMap.ext
      intro v
      have hv := ContinuousLinearMap.comp_inl_add_comp_inr f' v
      rw [← hv, h1, h2]
      simp
    -- the swap of the parameters, as a continuous linear isometry
    let L : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
      (LinearIsometryEquiv.prodComm ℝ ℝ ℝ : ℝ × ℝ →L[ℝ] ℝ × ℝ)
    have hLL : ∀ x : ℝ × ℝ, L (L x) = x := fun x => by
      simp [L]
    have hLinj : Function.Injective L := fun x y hxy => by rw [← hLL x, ← hLL y, hxy]
    have hLnorm : ∀ x : ℝ × ℝ, ‖L x‖ = ‖x‖ := fun x =>
      LinearIsometryEquiv.norm_map (LinearIsometryEquiv.prodComm ℝ ℝ ℝ) x
    have hLir : (L ∘L ContinuousLinearMap.inr ℝ ℝ ℝ) = ContinuousLinearMap.inl ℝ ℝ ℝ := by
      apply ContinuousLinearMap.ext
      intro x
      simp [L]
    -- the derivative of `f ∘ L` at `L p` is `f' ∘L L`
    have hFderiv : fderiv ℝ (fun v => f (L v)) (L p) = f' ∘L L := by
      have hcomp : fderiv ℝ (fun v => f (L v)) (L p)
          = fderiv ℝ f (L (L p)) ∘L fderiv ℝ (fun v => L v) (L p) :=
        fderiv_comp (L p) (hf.differentiable (by norm_num)).differentiableAt
          (ContinuousLinearMap.differentiableAt L)
      rw [hcomp, hLL, ContinuousLinearMap.fderiv, ← hf'_def]
    have hF : HasStrictFDerivAt (fun v => f (L v)) (f' ∘L L) (L p) := by
      have h : HasStrictFDerivAt (fun v => f (L v))
          (fderiv ℝ (fun v => f (L v)) (L p)) (L p) :=
        (hf.comp (ContinuousLinearMap.contDiff L)).contDiffAt.hasStrictFDerivAt (by norm_num)
      rwa [hFderiv] at h
    have hFt : (fun v => f (L v)) (L p) = t := by
      show f (L (L p)) = t
      rw [hLL, hp]
    have hInv : ((f' ∘L L) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
      rw [ContinuousLinearMap.comp_assoc, hLir]
      exact isInvertible_of_ne_zero h1
    obtain ⟨ε, hεpos, σ, hσ0, hcont, hinj, hlev, hcov⟩ := local_arc_snd hF hFt hInv
    -- transport the arc back through the swap
    refine ⟨ε, hεpos, fun s => L (σ s), ?_, ?_, ?_, ?_, ?_⟩
    · show L (σ 0) = p
      rw [hσ0, hLL]
    · exact (ContinuousLinearMap.continuous L).continuousOn.comp hcont (Set.mapsTo_univ _ _)
    · intro a ha b hb hab
      exact hinj ha hb (hLinj hab)
    · intro s hs
      show f (L (σ s)) = t
      exact hlev s hs
    · intro q hq hdist
      have hq' : (fun v => f (L v)) (L q) = t := by
        show f (L (L q)) = t
        rw [hLL]
        exact hq
      have hdist' : ‖L q - L p‖ < ε := by
        rw [← map_sub, hLnorm]
        exact hdist
      obtain ⟨s, hs, hsq⟩ := hcov (L q) hq' hdist'
      refine ⟨s, hs, ?_⟩
      show L (σ s) = q
      rw [hsq, hLL]
  · -- the second partial derivative does not vanish
    exact local_arc_snd hsd hp (isInvertible_of_ne_zero h2)

/-- **The level set of the pull-back through the parametrised torus is locally an arc.**  At a
point `p` of the parameter plane where the pull-back `Work.Smooth.Morse.pullback ψ g = g ∘ param ψ`
takes the value `t` and its derivative is nonzero, the level set `{pullback ψ g = t}` near `p` is
the image of an injective continuous arc `σ` on `(-1,1)` with `σ 0 = p`, and every point of the
level set in the ball of radius `ε` around `p` is `σ s` for some `s ∈ (-1,1)`. -/
theorem pullback_local_arc (ψ : Submission.Diffeo) {g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ} (hg : ContDiff ℝ 1 g) (t : ℝ) (p : ℝ × ℝ) (hp : Work.Smooth.Morse.pullback ψ g p = t) (hd : fderiv ℝ (Work.Smooth.Morse.pullback ψ g) p ≠ 0) : ∃ ε : ℝ, 0 < ε ∧ ∃ σ : ℝ → ℝ × ℝ, σ 0 = p ∧ ContinuousOn σ (Set.Ioo (-1 : ℝ) 1) ∧ Set.InjOn σ (Set.Ioo (-1 : ℝ) 1) ∧ (∀ s ∈ Set.Ioo (-1 : ℝ) 1, Work.Smooth.Morse.pullback ψ g (σ s) = t) ∧ (∀ q : ℝ × ℝ, Work.Smooth.Morse.pullback ψ g q = t → ‖q - p‖ < ε → ∃ s ∈ Set.Ioo (-1 : ℝ) 1, σ s = q) := by
  exact local_arc_of_fderiv_ne_zero (Work.Smooth.Morse.pullback_contDiff_one ψ hg) hp hd

end Work.Smooth.Morse.Regular
