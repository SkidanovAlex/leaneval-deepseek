import Mathlib
import Submission.Work.RPB.B5.kappaDefs
import Submission.Work.RPB.B5.kappa_shape_basic
import Submission.Work.RPB.B5.kappa_near_area
import Submission.Work.RPB.B5.kappa_collar_area_all
import Submission.Work.RPB.B5.deriv_signedArea_general
import Submission.Work.RPB.B5.flux_primitive_periodic
import Submission.Work.RPB.B5.kdiagM_signedArea
import Submission.Work.RPB.B5.kshape_periodic
import Submission.Work.RPB.B5.kshape_contDiffOn
import Submission.Work.RPB.B5.uproj_chart_contDiffAt_kappa
import Submission.Work.RPB.B5.contDiff_signedArea_gen

/-!
# B5: monodromy and flux identity of the `κ`-collar phase `kac`

The collar phase of `Submission/Work/RPB/B5/kappaDefs.lean` is

`kac τ σ t = kA0 τ σ + ∫_0^t ω_ℂ(∂_σ Γ, ∂_t Γ)(τ, σ, u) du`,   `Γ = kgam`,

i.e. the `σ`-jet interpolation at `t = 0` plus the flux integral of the collar curve family
`kgam`.  This file proves the two global properties of `kac` that the collar needs:

* **monodromy** `kac τ σ (t + 2π) = kac τ σ t + 2π` (for *every* level `σ : ℝ`, not only `σ ≥ 0`),
* **flux identity** `∂_t kac = ω_ℂ(∂_σ kgam, ∂_t kgam)`,

for every `δ ∈ (0, δ₀)` with `δ₀ = min δ₀(area) 4`, every `τ ∈ [0,1]` and every `σ, t : ℝ`.

Both are consequences of the classical identity

`d/dσ signedArea (kgam τ σ) = ∮ ω_ℂ(∂_σ kgam, ∂_t kgam)`   (`deriv_signedArea_general`)

together with the exact area law `signedArea (kgam τ σ) = 2π (1 + σ)` of `kappa_collar_area_all`:
the `σ`-derivative is then the constant `2π`, so the flux integrand has total integral `2π` over
one period, which is exactly what turns `∫_0^{t+2π}` into `∫_0^t + 2π`
(`flux_primitive_periodic`).

The primitive `flux_primitive_periodic` asks for a family that is *globally* `C²` on `ℝ × ℝ` and
`2π`-periodic in `t`; for the collar family `kgam τ · ·` (with `τ ∈ [0,1]` fixed) both are
available:

* `kgam_periodic` — periodicity, from `kshape_periodic` and the fact that the normalisation
  constant `kg` does not depend on `t`;
* `kgam_contDiff_joint` — `C²` smoothness in `(σ, t)`, which uses the *global* `C¹²` smoothness of
  the glued shape `kmf_kshape_contDiff_global` below, the smoothness of the signed area in the
  family parameter (`contDiff_signedArea_gen`), and the non-vanishing of `karS`
  (`kappa_collar_area_all`), which makes `kg = 2π(1+σ)/karS` smooth everywhere.

The global smoothness of `kshape` in `σ` is the only place where the size of `δ` matters besides
the area law: the `τ = 0` correction involves `√(2 + 2σ)` (non-smooth at the branch point
`σ = -1`) and is multiplied by the cutoff `xfade δ σ`, which vanishes for `σ ≤ -δ/4`; requiring
`δ < 4` puts `-1` strictly inside that vanishing region, so the branch point is never seen.  This
is why the threshold is capped by `4`.  (The same statement is proved in the sibling module
`Submission/Work/RPB/B5/kshape_contDiff_global.lean`; the proof is reproduced here so that this
file is self-contained.)
-/

open MeasureTheory intervalIntegral
open scoped ContDiff Topology Interval

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-! ## Global smoothness of the glued shape -/

/-- The chart part of the glued shape, `(σ,t) ↦ uproj (W τ t (ρh τ t (kclamp δ σ)))`, is `C¹²`
globally in `(σ,t)`: the clamp keeps the level strictly inside `(-κ,κ)`, so `ρh` and the chart `W`
are always evaluated inside the domains of their `C¹²` regularity. -/
theorem kmf_kshape_chart_contDiff (CI : Work.RPV.CurveIsotopy) {ρ₀ : ℝ}
    {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρh : ℝ → ℝ → ℝ → ℝ}
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    {κ : ℝ} (hκ : 0 < κ)
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    {δ : ℝ} (hδ : 0 < δ) (hδκ : δ < κ) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ContDiff ℝ 12 (fun p : ℝ × ℝ =>
      Work.RPV.uproj (W τ p.2 (ρh τ p.2 (Work.RPB.B5.kclamp δ p.1)))) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  have hkσ : Work.RPB.B5.kclamp δ p.1 ∈ Set.Ioo (-κ) κ := by
    have h := Work.RPB.B5.abs_kclamp_le (δ := δ) (σ := p.1) hδ
    rw [abs_le] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hbase := (uproj_chart_contDiffAt_kappa (ρ₀ := ρ₀) (W := W) (ρh := ρh) hW hκ hρh hρhv
    hτ (σ := Work.RPB.B5.kclamp δ p.1) (t := p.2) hkσ).1
  have hclamp_at : ContDiffAt ℝ 12 (fun q : ℝ × ℝ => (Work.RPB.B5.kclamp δ q.1, q.2)) p :=
    (((Work.RPB.B5.kclamp_contDiff δ).of_le (by norm_num)).contDiffAt.comp p
      contDiffAt_fst).prodMk contDiffAt_snd
  exact hbase.comp p hclamp_at

/-- **The glued shape is `C¹²` globally in `(σ, t)`**, for fixed `τ ∈ [0,1]` and a scale
`0 < δ < κ` with `δ < 4`.  The only non-smooth ingredient, `krd σ = √(2+2σ)` at `σ = -1`, occurs
multiplied by `xfade δ σ` (in the `τ = 0` correction) and by `kblf δ σ` (weighting the far
family), and both cutoffs vanish identically for `σ ≤ -δ/4`; since `δ < 4` gives `-1 < -δ/4`, the
branch point lies in the interior of the region where those products are `0`, so they are smooth
there.  Everywhere else (`σ ≥ -δ/4 > -1`) all ingredients are smooth. -/
theorem kmf_kshape_contDiff_global (CI : Work.RPV.CurveIsotopy) {ρ₀ : ℝ}
    {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρh : ℝ → ℝ → ℝ → ℝ}
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    {κ : ℝ} (hκ : 0 < κ)
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    {δ : ℝ} (hδ : 0 < δ) (hδκ : δ < κ) (hδ4 : δ < 4) (k : ℤ) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ContDiff ℝ 12 (fun z : ℝ × ℝ => Work.RPB.B5.kshape CI W ρh δ k τ z.1 z.2) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z.1 < -(δ / 4)
  · -- the branch point of `√(2+2σ)` is invisible: both cutoffs vanish identically nearby
    have hopen : IsOpen {p : ℝ × ℝ | p.1 < -(δ / 4)} := isOpen_lt continuous_fst continuous_const
    have heq : (fun p : ℝ × ℝ => Work.RPB.B5.kshape CI W ρh δ k τ p.1 p.2) =ᶠ[𝓝 z]
        (fun p : ℝ × ℝ =>
          Work.RPV.uproj (W τ p.2 (ρh τ p.2 (Work.RPB.B5.kclamp δ p.1)))) := by
      filter_upwards [hopen.mem_nhds hz] with p hp
      have hblf : Work.RPB.B5.kblf δ p.1 = 0 := Work.RPB.B5.ksb_kblf_zero hδ (by linarith)
      have hxf : Work.RPB.B5.xfade δ p.1 = 0 := Work.RPB.B5.xfade_zero hδ (le_of_lt hp)
      simp only [Work.RPB.B5.kshape, Work.RPB.B5.knear, hblf, hxf, zero_mul, one_mul, mul_zero,
        add_zero, sub_zero]
      simp
    exact (kmf_kshape_chart_contDiff CI hW hκ hρh hρhv hδ hδκ hτ).contDiffAt
      |>.congr_of_eventuallyEq heq
  · -- `σ ≥ -δ/4 > -1`: every ingredient of the glued shape is smooth at `z`
    push Not at hz
    have hz1 : (-1 : ℝ) < z.1 := by linarith
    have hkσ : Work.RPB.B5.kclamp δ z.1 ∈ Set.Ioo (-κ) κ := by
      have h := Work.RPB.B5.abs_kclamp_le (δ := δ) (σ := z.1) hδ
      rw [abs_le] at h
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    have hclamp_at : ContDiffAt ℝ 12 (fun p : ℝ × ℝ => (Work.RPB.B5.kclamp δ p.1, p.2)) z :=
      (((Work.RPB.B5.kclamp_contDiff δ).of_le (by norm_num)).contDiffAt.comp z
        contDiffAt_fst).prodMk contDiffAt_snd
    have hNNτ : ContDiffAt ℝ 12
        (fun p : ℝ × ℝ => Work.RPV.uproj (W τ p.2 (ρh τ p.2 (Work.RPB.B5.kclamp δ p.1)))) z := by
      have hbase := (uproj_chart_contDiffAt_kappa (ρ₀ := ρ₀) (W := W) (ρh := ρh) hW hκ hρh hρhv
        hτ (σ := Work.RPB.B5.kclamp δ z.1) (t := z.2) hkσ).1
      exact hbase.comp z hclamp_at
    have hNN0 : ContDiffAt ℝ 12
        (fun p : ℝ × ℝ => Work.RPV.uproj (W 0 p.2 (ρh 0 p.2 (Work.RPB.B5.kclamp δ p.1)))) z := by
      have hbase := (uproj_chart_contDiffAt_kappa (ρ₀ := ρ₀) (W := W) (ρh := ρh) hW hκ hρh hρhv
        (show (0 : ℝ) ∈ Set.Icc 0 1 from ⟨le_refl 0, zero_le_one⟩)
        (σ := Work.RPB.B5.kclamp δ z.1) (t := z.2) hkσ).1
      exact hbase.comp z hclamp_at
    have h2 : (2 : ℝ) + 2 * z.1 ≠ 0 := by intro hc; linarith
    have hrd_at : ContDiffAt ℝ 12 (fun p : ℝ × ℝ => ((Work.RPB.B5.krd p.1 : ℝ) : ℂ)) z := by
      have hs : ContDiffAt ℝ 12 (fun p : ℝ × ℝ => Real.sqrt (2 + 2 * p.1)) z :=
        (Real.contDiffAt_sqrt h2).comp z (by fun_prop)
      have hcomp := (Complex.ofRealCLM.contDiff.contDiffAt).comp z hs
      simp only [Work.RPB.B5.krd]
      exact hcomp
    have hphcC : ContDiff ℝ 12 (fun σ : ℝ => Work.RPB.B5.kphc δ k σ) := by
      unfold Work.RPB.B5.kphc Work.RPB.B5.kstp; fun_prop
    have htarg_at : ContDiffAt ℝ 12
        (fun p : ℝ × ℝ => Work.RPB.B5.ktarg δ k p.1 p.2) z := by
      have hphc_at : ContDiffAt ℝ 12 (fun p : ℝ × ℝ => Work.RPB.B5.kphc δ k p.1) z :=
        hphcC.contDiffAt.comp z (by fun_prop)
      have hphc_C : ContDiffAt ℝ 12 (fun p : ℝ × ℝ => ((Work.RPB.B5.kphc δ k p.1 : ℝ) : ℂ)) z :=
        (Complex.ofRealCLM.contDiff.contDiffAt).comp z hphc_at
      have h2C : ContDiffAt ℝ 12 (fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ)) z :=
        (Complex.ofRealCLM.contDiff.contDiffAt).comp z (by fun_prop)
      have harg : ContDiffAt ℝ 12
          (fun p : ℝ × ℝ => (((p.2 : ℝ) : ℂ) + ((Work.RPB.B5.kphc δ k p.1 : ℝ) : ℂ))
              * Complex.I) z :=
        (h2C.add hphc_C).mul contDiffAt_const
      have hexp : ContDiffAt ℝ 12 (fun p : ℝ × ℝ =>
          Complex.exp ((((p.2 : ℝ) : ℂ) + ((Work.RPB.B5.kphc δ k p.1 : ℝ) : ℂ))
              * Complex.I)) z :=
        (Complex.contDiff_exp.contDiffAt).comp z harg
      simp only [Work.RPB.B5.ktarg]
      exact hrd_at.mul hexp
    have hfsh_at : ContDiffAt ℝ 12
        (fun p : ℝ × ℝ => Work.RPB.B5.kfsh CI δ k τ p.1 p.2) z := by
      have hrpfC : ContDiff ℝ 12 (fun σ : ℝ => Work.RPB.B5.krpf δ σ) := by
        unfold Work.RPB.B5.krpf Work.RPB.B5.kstp; fun_prop
      have hmap : ContDiffAt ℝ 12
          (fun p : ℝ × ℝ => (Work.RPB.B5.krpf δ p.1 * τ, p.2 + Work.RPB.B5.kphc δ k p.1)) z := by
        fun_prop
      have hc : ContDiffAt ℝ 12
          (fun p : ℝ × ℝ => CI.c (Work.RPB.B5.krpf δ p.1 * τ)
            (p.2 + Work.RPB.B5.kphc δ k p.1)) z :=
        (CI.smooth.contDiffAt.of_le (by norm_num)).comp z hmap
      simp only [Work.RPB.B5.kfsh]
      exact hrd_at.mul hc
    have hblfC : ContDiff ℝ 12 (fun σ : ℝ => ((Work.RPB.B5.kblf δ σ : ℝ) : ℂ)) := by
      have h : ContDiff ℝ 12 (fun σ : ℝ => Work.RPB.B5.kblf δ σ) := by
        unfold Work.RPB.B5.kblf Work.RPB.B5.kstp; fun_prop
      exact Complex.ofRealCLM.contDiff.comp h
    have hblf_at : ContDiffAt ℝ 12 (fun p : ℝ × ℝ => ((Work.RPB.B5.kblf δ p.1 : ℝ) : ℂ)) z :=
      hblfC.contDiffAt.comp z (by fun_prop)
    have hxfade_at : ContDiffAt ℝ 12 (fun p : ℝ × ℝ => ((Work.RPB.B5.xfade δ p.1 : ℝ) : ℂ)) z := by
      have h : ContDiff ℝ 12 (fun σ : ℝ => ((Work.RPB.B5.xfade δ σ : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp ((Work.RPB.B5.xfade_contDiff δ).of_le (by norm_num))
      exact h.contDiffAt.comp z (by fun_prop)
    have hconstbb : ContDiffAt ℝ 12 (fun _ : ℝ × ℝ => ((Work.RPB.B5.kbbmp δ τ : ℝ) : ℂ)) z :=
      contDiffAt_const
    simp only [Work.RPB.B5.kshape, Work.RPB.B5.knear]
    exact (((contDiffAt_const.sub hblf_at).mul
        (hNNτ.add ((hconstbb.mul hxfade_at).mul (htarg_at.sub hNN0)))).add
        (hblf_at.mul hfsh_at)).contDiffWithinAt

/-! ## The collar curve family `kgam` -/

/-- The normalised collar curve family is `2π`-periodic in the angle variable `t`: `kg` does not
depend on `t` and the glued shape `kshape` is periodic. -/
theorem kgam_periodic (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (ρh : ℝ → ℝ → ℝ → ℝ) (δ : ℝ) (k : ℤ)
    (hWper : ∀ τ t ρ, W τ (t + 2 * Real.pi) ρ = Work.RPV.Tk 1 (W τ t ρ))
    (hρhper : ∀ τ t σ, ρh τ (t + 2 * Real.pi) σ = ρh τ t σ) :
    ∀ τ σ t : ℝ, kgam CI W ρh δ k τ σ (t + 2 * Real.pi) = kgam CI W ρh δ k τ σ t := by
  intro τ σ t
  simp only [kgam]
  rw [kshape_periodic CI W ρh δ k hWper hρhper τ σ t]

/-- **Joint `C²` smoothness of the collar family.** For a fixed `τ ∈ [0,1]`, a scale
`0 < δ < κ` (so that the clamped level stays strictly inside the domain of `ρh`) with `δ < 4`
(so that the square root of the `τ = 0` correction is switched off before its branch point) and
a non-vanishing `karS`, the map `(σ, t) ↦ kgam CI W ρh δ k τ σ t` is `C²` on all of `ℝ × ℝ`. -/
theorem kgam_contDiff_joint (CI : Work.RPV.CurveIsotopy) {ρ₀ : ℝ}
    {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρh : ℝ → ℝ → ℝ → ℝ}
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    {κ : ℝ} (hκ : 0 < κ)
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    {δ : ℝ} (hδ : 0 < δ) (hδκ : δ < κ) (hδ4 : δ < 4) (k : ℤ) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hkarS : ∀ σ : ℝ, karS CI W ρh δ k τ σ ≠ 0) :
    ContDiff ℝ 2 (fun z : ℝ × ℝ => kgam CI W ρh δ k τ z.1 z.2) := by
  have hksh12 := kmf_kshape_contDiff_global CI hW hκ hρh hρhv hδ hδκ hδ4 k hτ
  have hksh3 : ContDiff ℝ 3 (fun z : ℝ × ℝ => kshape CI W ρh δ k τ z.1 z.2) :=
    hksh12.of_le (by norm_num)
  have hksh2 : ContDiff ℝ 2 (fun z : ℝ × ℝ => kshape CI W ρh δ k τ z.1 z.2) :=
    hksh12.of_le (by norm_num)
  -- the signed area of the glued shape is `C²` in the level
  have hkarScd : ContDiff ℝ 2 (fun σ : ℝ => karS CI W ρh δ k τ σ) :=
    contDiff_signedArea_gen (X := ℝ) (fun σ t => kshape CI W ρh δ k τ σ t) 2 hksh3
  -- hence so is the normalisation constant `kg = 2π(1+σ)/karS`
  have hkgcd : ContDiff ℝ 2 (fun σ : ℝ => kg CI W ρh δ k τ σ) := by
    have hnum : ContDiff ℝ 2 (fun σ : ℝ => 2 * Real.pi * (1 + σ)) := by fun_prop
    exact hnum.div hkarScd (fun σ => hkarS σ)
  -- the two components of `kdiagM`
  have hfun : (fun z : ℝ × ℝ => kgam CI W ρh δ k τ z.1 z.2)
      = fun z : ℝ × ℝ => (((kshape CI W ρh δ k τ z.1 z.2).re : ℝ) : ℂ)
          + (((kg CI W ρh δ k τ z.1) * (kshape CI W ρh δ k τ z.1 z.2).im : ℝ) : ℂ)
              * Complex.I := by
    funext z
    rfl
  rw [hfun]
  refine (Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp hksh2)).add ?_
  exact (Complex.ofRealCLM.contDiff.comp
    ((hkgcd.comp contDiff_fst).mul (Complex.imCLM.contDiff.comp hksh2))).mul contDiff_const

theorem kappa_collar_mono_flux (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a)
    (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (κ : ℝ) (hκ : 0 < κ)
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hWchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (hWper : ∀ τ t ρ, W τ (t + 2 * Real.pi) ρ = Work.RPV.Tk 1 (W τ t ρ))
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρh0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ρh τ t 0 = 0)
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    (hρhl : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      Work.RPV.K0 (W τ t (ρh τ t σ)) + 1 = -σ)
    (hρhper : ∀ τ t σ, ρh τ (t + 2 * Real.pi) σ = ρh τ t σ)
    (k : ℤ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ κ ∧
      ∀ δ ∈ Set.Ioo (0 : ℝ) δ₀, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        (∀ σ t, Work.RPB.B5.kac CI W ρh δ k τ σ (t + 2 * Real.pi)
            = Work.RPB.B5.kac CI W ρh δ k τ σ t + 2 * Real.pi) ∧
        (∀ σ t, deriv (fun s : ℝ => Work.RPB.B5.kac CI W ρh δ k τ σ s) t
            = Work.RPV.ωC (deriv (fun s : ℝ => Work.RPB.B5.kgam CI W ρh δ k τ s t) σ)
                (deriv (fun s : ℝ => Work.RPB.B5.kgam CI W ρh δ k τ σ s) t)) := by
  -- the exact area law of the collar, for every level `σ : ℝ`
  obtain ⟨δA, hδApos, hδAκ, hA⟩ :=
    kappa_collar_area_all CI a ha ρ₀ hρ₀ W ρh κ hκ hW hWchord hWper hρh hρh0 hρhv hρhl hρhper k
  refine ⟨min δA 4, lt_min hδApos (by norm_num), le_trans (min_le_left _ _) hδAκ, ?_⟩
  intro δ hδ τ hτ
  rw [Set.mem_Ioo] at hδ
  obtain ⟨hδpos, hδlt⟩ := hδ
  have hδA' : δ < δA := lt_of_lt_of_le hδlt (min_le_left _ _)
  have hδ4 : δ < 4 := lt_of_lt_of_le hδlt (min_le_right _ _)
  have hδκ : δ < κ := lt_of_lt_of_le hδA' hδAκ
  have harea : ∀ σ : ℝ,
      Work.RPB.signedArea (fun t : ℝ => kgam CI W ρh δ k τ σ t) = 2 * Real.pi * (1 + σ) :=
    fun σ => (hA δ ⟨hδpos, hδA'⟩ τ hτ σ).1
  have hkarS : ∀ σ : ℝ, karS CI W ρh δ k τ σ ≠ 0 :=
    fun σ => (hA δ ⟨hδpos, hδA'⟩ τ hτ σ).2
  have hV : ContDiff ℝ 2 (fun z : ℝ × ℝ => kgam CI W ρh δ k τ z.1 z.2) :=
    kgam_contDiff_joint CI hW hκ hρh hρhv hδpos hδκ hδ4 k hτ hkarS
  have hper : ∀ σ t : ℝ, kgam CI W ρh δ k τ σ (t + 2 * Real.pi) = kgam CI W ρh δ k τ σ t :=
    kgam_periodic CI W ρh δ k hWper hρhper τ
  -- the three flux facts at every level `σ`
  have hflux : ∀ σ : ℝ,
      (∫ u in (0 : ℝ)..(2 * Real.pi),
          Work.RPV.ωC (deriv (fun s : ℝ => kgam CI W ρh δ k τ s u) σ)
            (deriv (fun s : ℝ => kgam CI W ρh δ k τ σ s) u)) = 2 * Real.pi ∧
      (∀ t : ℝ, deriv (fun v : ℝ => ∫ u in (0 : ℝ)..v,
          Work.RPV.ωC (deriv (fun s : ℝ => kgam CI W ρh δ k τ s u) σ)
            (deriv (fun s : ℝ => kgam CI W ρh δ k τ σ s) u)) t
        = Work.RPV.ωC (deriv (fun s : ℝ => kgam CI W ρh δ k τ s t) σ)
            (deriv (fun s : ℝ => kgam CI W ρh δ k τ σ s) t)) ∧
      (∀ t : ℝ, (∫ u in (0 : ℝ)..(t + 2 * Real.pi),
          Work.RPV.ωC (deriv (fun s : ℝ => kgam CI W ρh δ k τ s u) σ)
            (deriv (fun s : ℝ => kgam CI W ρh δ k τ σ s) u))
        = (∫ u in (0 : ℝ)..t,
            Work.RPV.ωC (deriv (fun s : ℝ => kgam CI W ρh δ k τ s u) σ)
              (deriv (fun s : ℝ => kgam CI W ρh δ k τ σ s) u)) + 2 * Real.pi) := by
    intro σ
    have hderiv : HasDerivAt (fun σ' : ℝ =>
        Work.RPB.signedArea (fun t : ℝ => kgam CI W ρh δ k τ σ' t)) (2 * Real.pi) σ := by
      have heq : (fun σ' : ℝ =>
          Work.RPB.signedArea (fun t : ℝ => kgam CI W ρh δ k τ σ' t))
          = fun σ' : ℝ => 2 * Real.pi * (1 + σ') := funext harea
      rw [heq]
      simpa using ((hasDerivAt_id σ).const_add (1 : ℝ)).const_mul (2 * Real.pi)
    exact flux_primitive_periodic (fun σ t => kgam CI W ρh δ k τ σ t) σ hper hV hderiv
  constructor
  · -- monodromy: the flux over one period is `2π`
    intro σ t
    obtain ⟨-, -, h3⟩ := hflux σ
    simp only [kac]
    rw [h3 t]
    ring
  · -- flux identity: the fundamental theorem of calculus for the flux primitive
    intro σ t
    obtain ⟨-, h2, -⟩ := hflux σ
    simp only [kac]
    rw [deriv_const_add]
    exact h2 t

end Work.RPB.B5
