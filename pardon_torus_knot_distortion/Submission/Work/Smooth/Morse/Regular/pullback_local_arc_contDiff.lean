import Mathlib
import Submission.Work.Smooth.Morse.Regular.pullback_local_arc
import Submission.Work.Smooth.Morse.Regular.arc_data_snd
import Submission.Work.Smooth.Morse.Regular.local_arc_snd
import Submission.Work.Smooth.Morse.Defs

/-!
# The local arc of a regular level set, of class `C¹`

`Work.Smooth.Morse.Regular.pullback_local_arc` provides, at a regular point `p` of the level set
`{pullback ψ g = t}`, an injective continuous arc `σ` on `(-1,1)` through `p` which exhausts the
level set near `p`.  Here we strengthen the conclusion: the arc is `C¹` on `(-1,1)`.

The proof is the implicit function theorem again, but keeping the regularity: at a point where the
partial derivative of `f` in the second variable is invertible, the implicit function `ψ` is `C¹`
near `p.1` (`Work.Smooth.Morse.Regular.arc_data_snd`), so the graph parametrisation
`s ↦ (p.1 + c s, ψ (p.1 + c s))` is `C¹` on an interval, hence on `(-1,1)` after rescaling.  The
affine parametrisation `s ↦ p.1 + c s` (rather than the piecewise affine reparametrisation used in
`pullback_local_arc_ball`) is `C¹`, which is what the extra regularity needs.  When the second
partial derivative vanishes we transport the statement through the swap of the coordinates, exactly
as in `pullback_local_arc`.

## Main results

* `isInvertible_of_ne_zero` (private) -- a nonzero continuous linear functional `ℝ →L[ℝ] ℝ` is
  invertible;
* `local_arc_contDiff_snd` (private) -- the `C¹` arc when the second partial derivative is
  invertible (the implicit function theorem);
* `local_arc_contDiff_of_fderiv_ne_zero` (private) -- the case of a nonzero total derivative,
  reduced to the previous one by swapping the coordinates;
* `pullback_local_arc_contDiff` -- the statement for `pullback ψ g`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped Topology

namespace Work.Smooth.Morse.Regular

/-- A nonzero continuous linear map `ℝ →L[ℝ] ℝ` is a continuous linear equivalence. -/
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

/-- **The local model of a regular level set, with `C¹` regularity, when the partial derivative in
the second variable is invertible.**  The level set is locally the graph `x ↦ (x, ψ x)` of the
implicit function `ψ`, and `ψ` is `C¹`; parametrising the graph by `s ↦ p.1 + c s` for a small
constant `c` turns this into a `C¹` arc on `(-1,1)` through `p` which exhausts the level set near
`p`. -/
private theorem local_arc_contDiff_snd {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {p : ℝ × ℝ} {t : ℝ} (hp : f p = t)
    (hinv : (fderiv ℝ f p ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ σ : ℝ → ℝ × ℝ, σ 0 = p ∧
      ContDiffOn ℝ 1 σ (Ioo (-1 : ℝ) 1) ∧ InjOn σ (Ioo (-1 : ℝ) 1) ∧
      (∀ s ∈ Ioo (-1 : ℝ) 1, f (σ s) = t) ∧
      (∀ q : ℝ × ℝ, f q = t → ‖q - p‖ < ε → ∃ s ∈ Ioo (-1 : ℝ) 1, σ s = q) := by
  obtain ⟨ψ, ρ, U, hρ, hUopen, hpU, hψa, hdcat, hder, hdc, hψcont, hlevel, huniq⟩ :=
    Work.Smooth.Morse.Regular.arc_data_snd hf.contDiffAt hp hinv
  obtain ⟨ε₁, hε₁, hballU⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hpU)
  -- the implicit function is `C¹` on an interval around `p.1`
  have hIoo : IsOpen (Ioo (p.1 - ρ) (p.1 + ρ)) := isOpen_Ioo
  have hψcd : ContDiffOn ℝ 1 ψ (Ioo (p.1 - ρ) (p.1 + ρ)) := by
    rw [contDiffOn_one_iff_derivWithin hIoo.uniqueDiffOn]
    refine ⟨fun x hx => (hder x hx).differentiableAt.differentiableWithinAt, ?_⟩
    exact hdc.congr (fun x hx => derivWithin_of_isOpen hIoo hx)
  -- the half-width of the parametrising interval
  set c : ℝ := ρ / 2 with hcdef
  have hc : 0 < c := by rw [hcdef]; linarith
  have hcρ : c < ρ := by rw [hcdef]; linarith
  have hmap : MapsTo (fun s : ℝ => p.1 + c * s) (Ioo (-1 : ℝ) 1)
      (Ioo (p.1 - ρ) (p.1 + ρ)) := by
    intro s hs
    rw [mem_Ioo] at hs ⊢
    obtain ⟨hs1, hs2⟩ := hs
    have hlt : |c * s| < ρ := by
      rw [abs_mul, abs_of_pos hc]
      nlinarith [hc, hcρ, abs_lt.mpr ⟨hs1, hs2⟩, abs_nonneg s]
    obtain ⟨h1, h2⟩ := abs_lt.mp hlt
    constructor <;> linarith
  refine ⟨min c ε₁, lt_min hc hε₁, fun s => (p.1 + c * s, ψ (p.1 + c * s)),
    ?_, ?_, ?_, ?_, ?_⟩
  · show (p.1 + c * 0, ψ (p.1 + c * 0)) = p
    simp only [mul_zero, add_zero]
    rw [hψa]
  · -- the arc is `C¹`
    have hg0 : ContDiffOn ℝ 1 (fun s : ℝ => p.1 + c * s) (Ioo (-1 : ℝ) 1) := by fun_prop
    have hcomp : ContDiffOn ℝ 1 (fun s : ℝ => ψ (p.1 + c * s)) (Ioo (-1 : ℝ) 1) :=
      hψcd.comp hg0 hmap
    exact hg0.prodMk hcomp
  · -- the arc is injective
    intro a ha b hb hab
    have h1 : p.1 + c * a = p.1 + c * b := congrArg Prod.fst hab
    have h2 : c * a = c * b := by linarith
    exact mul_left_cancel₀ (ne_of_gt hc) h2
  · -- the arc lies in the level set
    intro s hs
    show f (p.1 + c * s, ψ (p.1 + c * s)) = t
    exact hlevel _ (hmap hs)
  · -- the arc exhausts the level set near `p`
    intro q hfq hqn
    have hqU : q ∈ U :=
      hballU (by rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_lt_of_le hqn (min_le_right _ _))
    have hq2 : q.2 = ψ q.1 := huniq q hqU hfq
    have hq1 : |q.1 - p.1| < c := by
      have h1 : ‖(q - p).1‖ ≤ ‖q - p‖ := norm_fst_le (q - p)
      have h2 : ‖(q - p).1‖ = |q.1 - p.1| := by simp [Real.norm_eq_abs]
      rw [h2] at h1
      exact lt_of_le_of_lt h1 (lt_of_lt_of_le hqn (min_le_left _ _))
    refine ⟨(q.1 - p.1)/c, ?_, ?_⟩
    · rw [mem_Ioo, ← abs_lt]
      rw [abs_div, abs_of_pos hc, div_lt_one hc]
      exact hq1
    · show (p.1 + c * ((q.1 - p.1)/c), ψ (p.1 + c * ((q.1 - p.1)/c))) = q
      have hx : p.1 + c * ((q.1 - p.1)/c) = q.1 := by
        field_simp
        ring
      rw [hx, ← hq2]

/-- **The local model of a regular level set, with `C¹` regularity.**  If `f : ℝ × ℝ → ℝ` is
`C¹` with `f p = t` and `fderiv ℝ f p ≠ 0`, then the level set `{f = t}` is near `p` the image of
an injective `C¹` arc `σ` on `(-1,1)` with `σ 0 = p`, which is contained in the level set and
exhausts every point of the level set in a small ball around `p`.

If the partial derivative in the second variable is invertible this is `local_arc_contDiff_snd`.
Otherwise the first partial derivative is nonzero and we apply `local_arc_contDiff_snd` to
`f ∘ L`, where `L` is the swap of the two coordinates (a linear isometry, so the ball is
preserved), transporting the arc back through `L`. -/
private theorem local_arc_contDiff_of_fderiv_ne_zero {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {p : ℝ × ℝ} {t : ℝ} (hp : f p = t) (hd : fderiv ℝ f p ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ σ : ℝ → ℝ × ℝ, σ 0 = p ∧
      ContDiffOn ℝ 1 σ (Ioo (-1 : ℝ) 1) ∧ InjOn σ (Ioo (-1 : ℝ) 1) ∧
      (∀ s ∈ Ioo (-1 : ℝ) 1, f (σ s) = t) ∧
      (∀ q : ℝ × ℝ, f q = t → ‖q - p‖ < ε → ∃ s ∈ Ioo (-1 : ℝ) 1, σ s = q) := by
  set f' : ℝ × ℝ →L[ℝ] ℝ := fderiv ℝ f p with hf'_def
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
    have hLL : ∀ x : ℝ × ℝ, L (L x) = x := fun x => by simp [L]
    have hLinj : Function.Injective L := fun x y hxy => by rw [← hLL x, ← hLL y, hxy]
    have hLnorm : ∀ x : ℝ × ℝ, ‖L x‖ = ‖x‖ := fun x =>
      LinearIsometryEquiv.norm_map (LinearIsometryEquiv.prodComm ℝ ℝ ℝ) x
    have hLir : (L ∘L ContinuousLinearMap.inr ℝ ℝ ℝ) = ContinuousLinearMap.inl ℝ ℝ ℝ := by
      apply ContinuousLinearMap.ext
      intro x
      simp [L]
    have hFderiv : fderiv ℝ (fun v => f (L v)) (L p) = f' ∘L L := by
      have hcomp : fderiv ℝ (fun v => f (L v)) (L p)
          = fderiv ℝ f (L (L p)) ∘L fderiv ℝ (fun v => L v) (L p) :=
        fderiv_comp (L p) (hf.differentiable (by norm_num)).differentiableAt
          (ContinuousLinearMap.differentiableAt L)
      rw [hcomp, hLL, ContinuousLinearMap.fderiv, ← hf'_def]
    have hFct : ContDiff ℝ 1 (fun v => f (L v)) := hf.comp (ContinuousLinearMap.contDiff L)
    have hFt : (fun v => f (L v)) (L p) = t := by
      show f (L (L p)) = t
      rw [hLL, hp]
    have hInv : (fderiv ℝ (fun v => f (L v)) (L p) ∘L
        ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
      rw [hFderiv, ContinuousLinearMap.comp_assoc, hLir]
      exact isInvertible_of_ne_zero h1
    obtain ⟨ε, hε, σ, hσ0, hcd, hinj, hlev, hcov⟩ := local_arc_contDiff_snd hFct hFt hInv
    -- transport the arc back through the swap
    refine ⟨ε, hε, fun s => L (σ s), ?_, ?_, ?_, ?_, ?_⟩
    · show L (σ 0) = p
      rw [hσ0, hLL]
    · exact (ContinuousLinearMap.contDiff L).contDiffOn.comp hcd (mapsTo_univ _ _)
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
      exact ⟨s, hs, by show L (σ s) = q; rw [hsq, hLL]⟩
  · -- the second partial derivative does not vanish
    exact local_arc_contDiff_snd hf hp (by simpa [hf'_def] using isInvertible_of_ne_zero h2)

theorem pullback_local_arc_contDiff (ψ : Submission.Diffeo) {g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ}
    (hg : ContDiff ℝ 1 g) (t : ℝ) (p : ℝ × ℝ)
    (hp : Work.Smooth.Morse.pullback ψ g p = t) (hd : fderiv ℝ (Work.Smooth.Morse.pullback ψ g) p ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ σ : ℝ → ℝ × ℝ, σ 0 = p ∧
      ContDiffOn ℝ 1 σ (Set.Ioo (-1 : ℝ) 1) ∧ Set.InjOn σ (Set.Ioo (-1 : ℝ) 1) ∧
      (∀ s ∈ Set.Ioo (-1 : ℝ) 1, Work.Smooth.Morse.pullback ψ g (σ s) = t) ∧
      (∀ q : ℝ × ℝ, Work.Smooth.Morse.pullback ψ g q = t → ‖q - p‖ < ε →
        ∃ s ∈ Set.Ioo (-1 : ℝ) 1, σ s = q) := by
  exact local_arc_contDiff_of_fderiv_ne_zero
    (Work.Smooth.Morse.pullback_contDiff_one ψ hg) hp hd

end Work.Smooth.Morse.Regular
