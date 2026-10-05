import Mathlib
import Submission.Work.RPB.B5.kappaDefs
import Submission.Work.RPB.B5.uproj_chart_contDiffAt_kappa

/-!
# B5: `C^12` regularity of the glued shape `kshape`

The glued shape

`kshape CI W ρh δ k τ σ t = (1 - kblf δ σ) * knear … + kblf δ σ * kfsh …`

is built from smooth pieces:

* `knear` — the reduced coordinate `uproj (W τ t (ρh τ t (kclamp δ σ)))` of the chart point on
  the *clamped* level, plus the `τ = 0` correction `kbbmp δ τ * xfade δ σ * (ktarg - uproj …)`.
  The clamp keeps the level inside `(-δ, δ) ⊆ (-κ, κ)`, so `ρh` and `W` are evaluated strictly
  inside their open domains of `C^12`-regularity;
* `kfsh` — the far family `krd σ * CI.c (krpf δ σ * τ) (t + kphc δ k σ)`, a reparametrisation of
  the smooth curve family `CI.c`;
* the cutoffs `kblf`, `kbbmp`, `xfade` and the radius `krd σ = √(2+2σ)` (`σ ∈ (-1,1)`).

At a point `z = (σ, t)` of the open slab `(-1,1) × ℝ` we prove `ContDiffAt ℝ 12` of each piece and
assemble.  The only place where the hypotheses enter is the chart part: the level
`kclamp δ z.1 ∈ (-δ, δ) ⊆ (-κ, κ)` is strictly interior, so the ambient `C^12` composite can be
restricted to a neighbourhood of `kclamp δ z.1` (`uproj_chart_contDiffAt_kappa`) and composed with
the smooth clamp `σ ↦ kclamp δ σ`.
-/

namespace Work.RPB.B5

open Work.RPV
open scoped ContDiff

set_option autoImplicit false

noncomputable section

theorem kshape_contDiffOn (CI : Work.RPV.CurveIsotopy) {ρ₀ : ℝ}
    {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρh : ℝ → ℝ → ℝ → ℝ}
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    {κ : ℝ} (hκ : 0 < κ)
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    {δ : ℝ} (hδ : 0 < δ) (hδκ : δ < κ) (k : ℤ)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ContDiffOn ℝ 12 (fun z : ℝ × ℝ => kshape CI W ρh δ k τ z.1 z.2)
      (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.univ) := by
  intro z hz
  have hz1 : z.1 ∈ Set.Ioo (-1 : ℝ) 1 := hz.1
  -- the clamped level sits strictly inside `(-κ, κ)`, since `|kclamp δ σ| ≤ δ < κ`
  have hkσ : kclamp δ z.1 ∈ Set.Ioo (-κ) κ := by
    have h := abs_kclamp_le (δ := δ) (σ := z.1) hδ
    rw [abs_le] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  -- the smooth clamp map `(σ, t) ↦ (kclamp δ σ, t)`
  have hclamp_at : ContDiffAt ℝ 12 (fun p : ℝ × ℝ => (kclamp δ p.1, p.2)) z :=
    (((kclamp_contDiff δ).of_le (by norm_num)).contDiffAt.comp z contDiffAt_fst).prodMk contDiffAt_snd
  -- the chart reduced coordinate `uproj (W τ t (ρh τ t (kclamp δ σ)))`
  have hNNτ : ContDiffAt ℝ 12
      (fun p : ℝ × ℝ => Work.RPV.uproj (W τ p.2 (ρh τ p.2 (kclamp δ p.1)))) z := by
    have hbase := (uproj_chart_contDiffAt_kappa (ρ₀ := ρ₀) (W := W) (ρh := ρh) hW hκ hρh hρhv
      hτ (σ := kclamp δ z.1) (t := z.2) hkσ).1
    exact hbase.comp z hclamp_at
  -- the same at `τ = 0`, used by the `τ = 0` correction
  have hNN0 : ContDiffAt ℝ 12
      (fun p : ℝ × ℝ => Work.RPV.uproj (W 0 p.2 (ρh 0 p.2 (kclamp δ p.1)))) z := by
    have hbase := (uproj_chart_contDiffAt_kappa (ρ₀ := ρ₀) (W := W) (ρh := ρh) hW hκ hρh hρhv
      (show (0 : ℝ) ∈ Set.Icc 0 1 from ⟨le_refl 0, zero_le_one⟩) (σ := kclamp δ z.1) (t := z.2)
      hkσ).1
    exact hbase.comp z hclamp_at
  -- the radius `krd σ = √(2 + 2σ)`, smooth on `(-1,1)`
  have hrd_at : ContDiffAt ℝ 12 (fun p : ℝ × ℝ => ((krd p.1 : ℝ) : ℂ)) z := by
    have h2 : (2 : ℝ) + 2 * z.1 ≠ 0 := by
      have h1 := hz1.1; have h2 := hz1.2; intro hc; nlinarith
    have hs : ContDiffAt ℝ 12 (fun p : ℝ × ℝ => Real.sqrt (2 + 2 * p.1)) z :=
      (Real.contDiffAt_sqrt h2).comp z (by fun_prop)
    have hcomp := (Complex.ofRealCLM.contDiff.contDiffAt).comp z hs
    simp only [krd]
    exact hcomp
  have hphcC : ContDiff ℝ 12 (fun σ : ℝ => kphc δ k σ) := by
    unfold kphc kstp; fun_prop
  -- the target circle family `ktarg`
  have htarg_at : ContDiffAt ℝ 12 (fun p : ℝ × ℝ => ktarg δ k p.1 p.2) z := by
    have hphc_at : ContDiffAt ℝ 12 (fun p : ℝ × ℝ => kphc δ k p.1) z :=
      hphcC.contDiffAt.comp z (by fun_prop)
    have hphc_C : ContDiffAt ℝ 12 (fun p : ℝ × ℝ => ((kphc δ k p.1 : ℝ) : ℂ)) z :=
      (Complex.ofRealCLM.contDiff.contDiffAt).comp z hphc_at
    have h2C : ContDiffAt ℝ 12 (fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ)) z :=
      (Complex.ofRealCLM.contDiff.contDiffAt).comp z (by fun_prop)
    have harg : ContDiffAt ℝ 12
        (fun p : ℝ × ℝ => (((p.2 : ℝ) : ℂ) + ((kphc δ k p.1 : ℝ) : ℂ)) * Complex.I) z :=
      (h2C.add hphc_C).mul contDiffAt_const
    have hexp : ContDiffAt ℝ 12 (fun p : ℝ × ℝ =>
        Complex.exp ((((p.2 : ℝ) : ℂ) + ((kphc δ k p.1 : ℝ) : ℂ)) * Complex.I)) z :=
      (Complex.contDiff_exp.contDiffAt).comp z harg
    simp only [ktarg]
    exact hrd_at.mul hexp
  -- the far family `kfsh` (a reparametrised translate of `CI.c`)
  have hfsh_at : ContDiffAt ℝ 12 (fun p : ℝ × ℝ => kfsh CI δ k τ p.1 p.2) z := by
    have hrpfC : ContDiff ℝ 12 (fun σ : ℝ => krpf δ σ) := by
      unfold krpf kstp; fun_prop
    have hmap : ContDiffAt ℝ 12
        (fun p : ℝ × ℝ => (krpf δ p.1 * τ, p.2 + kphc δ k p.1)) z := by
      fun_prop
    have hc : ContDiffAt ℝ 12
        (fun p : ℝ × ℝ => CI.c (krpf δ p.1 * τ) (p.2 + kphc δ k p.1)) z :=
      (CI.smooth.contDiffAt.of_le (by norm_num)).comp z hmap
    simp only [kfsh]
    exact hrd_at.mul hc
  -- the blend cutoff `kblf`
  have hblfC : ContDiff ℝ 12 (fun σ : ℝ => ((kblf δ σ : ℝ) : ℂ)) := by
    have h : ContDiff ℝ 12 (fun σ : ℝ => kblf δ σ) := by
      unfold kblf kstp; fun_prop
    exact Complex.ofRealCLM.contDiff.comp h
  have hblf_at : ContDiffAt ℝ 12 (fun p : ℝ × ℝ => ((kblf δ p.1 : ℝ) : ℂ)) z :=
    hblfC.contDiffAt.comp z (by fun_prop)
  -- the `τ = 0` correction cutoff `xfade`
  have hxfade_at : ContDiffAt ℝ 12 (fun p : ℝ × ℝ => ((xfade δ p.1 : ℝ) : ℂ)) z := by
    have h : ContDiff ℝ 12 (fun σ : ℝ => ((xfade δ σ : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp ((xfade_contDiff δ).of_le (by norm_num))
    exact h.contDiffAt.comp z (by fun_prop)
  have hconstbb : ContDiffAt ℝ 12 (fun _ : ℝ × ℝ => ((kbbmp δ τ : ℝ) : ℂ)) z :=
    contDiffAt_const
  -- assemble `kshape`
  simp only [Work.RPB.B5.kshape, Work.RPB.B5.knear]
  exact (((contDiffAt_const.sub hblf_at).mul
      (hNNτ.add ((hconstbb.mul hxfade_at).mul (htarg_at.sub hNN0)))).add
      (hblf_at.mul hfsh_at)).contDiffWithinAt

end

end Work.RPB.B5
