import Mathlib
import Submission.Work.RPB.B5.kappaDefs
import Submission.Work.RPB.B5.uproj_chart_contDiffAt_kappa
import Submission.Work.RPB.B5.kappa_collar_mono_flux

/-!
# B5: joint `C¹²`-regularity of the glued shape `kshape`

The glued shape

`kshape CI W ρh δ k τ σ t = (1 - kblf δ σ) * knear … + kblf δ σ * kfsh …`

is built from smooth pieces.  The only singularity of any ingredient is the square-root branch
point `σ = -1` of `krd σ = √(2 + 2σ)`, which occurs in the target circle `ktarg` (inside `knear`)
and in the far family `kfsh`.  Both occurrences are protected by cutoffs:

* `xfade δ σ` (the factor in front of `ktarg` in `knear`) vanishes for `σ ≤ -δ/4`, and `δ ≤ 2`
  gives `-δ/4 > -1`;
* `kblf δ σ` (the factor in front of `kfsh`) vanishes for `σ ≤ δ/2 > -1`.

Hence the domain `Icc 0 1 ×ˢ univ ×ˢ univ` is covered by the two open slabs `σ > -1` (`krd` smooth)
and `σ < -δ/4` (where `kshape` reduces to the globally smooth chart term), and we conclude with
`contDiffOn_of_locally_contDiffOn`.  The chart term `uproj (W τ t (ρh τ t (kclamp δ σ)))` is smooth
because `|kclamp δ σ| ≤ δ < κ`, so `ρh` and `W` are evaluated strictly inside their domains of
`C¹²`-regularity, while `ρh`'s values stay strictly inside `(-ρ₀, ρ₀)`.
-/

namespace Work.RPB.B5

open Work.RPV
open scoped ContDiff

set_option autoImplicit false

noncomputable section

/-- **The chart term is `C¹²`.**  The reduced coordinate `uproj (W τ t (ρh τ t (kclamp δ σ)))` of
the chart point on the clamped level is `C¹²` on `Icc 0 1 ×ˢ univ ×ˢ univ` whenever the trace
`z ↦ τf z` of the family parameter stays in `Icc 0 1`.  This is the only place where the
hypotheses `hW`, `hρh`, `hρhv` enter. -/
private theorem uproj_chart_contDiffOn {ρ₀ : ℝ} {W : ℝ → ℝ → ℝ → Work.RPV.PS}
    {ρh : ℝ → ℝ → ℝ → ℝ}
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    {κ : ℝ} (hκ : 0 < κ)
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    {δ : ℝ} (hδ : 0 < δ) (hδκ : δ < κ)
    {τf : ℝ × (ℝ × ℝ) → ℝ}
    (hτsm : ContDiffOn ℝ 12 τf (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ))
    (hτmem : ∀ z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ, τf z ∈ Set.Icc (0 : ℝ) 1) :
    ContDiffOn ℝ 12
      (fun z : ℝ × (ℝ × ℝ) =>
        Work.RPV.uproj (W (τf z) z.2.2 (ρh (τf z) z.2.2 (kclamp δ z.2.1))))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) := by
  have hup : ContDiff ℝ 12 (fun p : Work.RPV.PS => Work.RPV.uproj p) := by
    unfold Work.RPV.uproj
    have h12 : ContDiff ℝ 12 (fun p : Work.RPV.PS => ((p.1.2 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_id.fst.snd)
    have h11 : ContDiff ℝ 12 (fun p : Work.RPV.PS => ((p.1.1 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_id.fst.fst)
    have h21 : ContDiff ℝ 12 (fun p : Work.RPV.PS => ((p.2.1 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_id.snd.fst)
    exact ((Complex.contDiff_exp.comp (h12.mul contDiff_const))).mul
      (h21.add (h11.mul contDiff_const))
  have hkcl : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => kclamp δ z.2.1)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) :=
    ((kclamp_contDiff δ).of_le (by norm_num)).comp_contDiffOn (by fun_prop)
  have hz22 : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) := by fun_prop
  have hζ2 : ContDiffOn ℝ 12
      (fun z : ℝ × (ℝ × ℝ) => (τf z, (z.2.2, kclamp δ z.2.1)))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) :=
    hτsm.prodMk (hz22.prodMk hkcl)
  have hmem2 : ∀ z : ℝ × (ℝ × ℝ), z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ →
      kclamp δ z.2.1 ∈ Set.Ioo (-κ) κ := by
    intro z hz
    have h := abs_kclamp_le (δ := δ) (σ := z.2.1) hδ
    rw [abs_le] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hρhc : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh (τf z) z.2.2 (kclamp δ z.2.1))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) :=
    hρh.comp hζ2 (by
      intro z hz
      exact ⟨hτmem z hz, trivial, hmem2 z hz⟩)
  have hζ1 : ContDiffOn ℝ 12
      (fun z : ℝ × (ℝ × ℝ) => (τf z, (z.2.2, ρh (τf z) z.2.2 (kclamp δ z.2.1))))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) :=
    hτsm.prodMk (hz22.prodMk hρhc)
  have hWc : ContDiffOn ℝ 12
      (fun z : ℝ × (ℝ × ℝ) => W (τf z) z.2.2 (ρh (τf z) z.2.2 (kclamp δ z.2.1)))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) :=
    hW.comp hζ1 (by
      intro z hz
      exact ⟨hτmem z hz, trivial,
        hρhv (τf z) (hτmem z hz) z.2.2 (kclamp δ z.2.1) (hmem2 z hz)⟩)
  exact hup.comp_contDiffOn hWc

theorem kappa_kshape_contDiff_joint (CI : Work.RPV.CurveIsotopy) {ρ₀ : ℝ}
    {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρh : ℝ → ℝ → ℝ → ℝ}
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    {κ : ℝ} (hκ : 0 < κ)
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    {δ : ℝ} (hδ : 0 < δ) (hδκ : δ < κ) (hδ2 : δ ≤ 2) (k : ℤ) :
    ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => Work.RPB.B5.kshape CI W ρh δ k z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) := by
  have hδ4 : δ < 4 := by linarith
  have hkstp12 : ContDiff ℝ 12 kstp := kstp_contDiff.of_le (by norm_num)
  -- the cutoffs, as globally `C¹²` functions
  have hblf1 : ContDiff ℝ 12 (fun σ : ℝ => kblf δ σ) := by unfold kblf; fun_prop
  have hblfC : ContDiff ℝ 12 (fun σ : ℝ => ((kblf δ σ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hblf1
  have hxfade1 : ContDiff ℝ 12 (fun σ : ℝ => xfade δ σ) :=
    (xfade_contDiff δ).of_le (by norm_num)
  have hxfadeC : ContDiff ℝ 12 (fun σ : ℝ => ((xfade δ σ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hxfade1
  have hbbmp1 : ContDiff ℝ 12 (fun τ : ℝ => kbbmp δ τ) := by unfold kbbmp; fun_prop
  have hbbmpC : ContDiff ℝ 12 (fun τ : ℝ => ((kbbmp δ τ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hbbmp1
  have hkphc1 : ContDiff ℝ 12 (fun σ : ℝ => kphc δ k σ) := by unfold kphc; fun_prop
  have hkrpf1 : ContDiff ℝ 12 (fun σ : ℝ => krpf δ σ) := by unfold krpf; fun_prop
  -- the two chart terms
  have hG : ContDiffOn ℝ 12
      (fun z : ℝ × (ℝ × ℝ) =>
        Work.RPV.uproj (W z.1 z.2.2 (ρh z.1 z.2.2 (kclamp δ z.2.1))))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) :=
    uproj_chart_contDiffOn (ρ₀ := ρ₀) hW hκ hρh hρhv hδ hδκ (τf := fun z => z.1)
      (by fun_prop) (by intro z hz; exact hz.1)
  have hG0 : ContDiffOn ℝ 12
      (fun z : ℝ × (ℝ × ℝ) =>
        Work.RPV.uproj (W 0 z.2.2 (ρh 0 z.2.2 (kclamp δ z.2.1))))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) :=
    uproj_chart_contDiffOn (ρ₀ := ρ₀) hW hκ hρh hρhv hδ hδκ (τf := fun _ => (0 : ℝ))
      (by fun_prop) (by intro z hz; exact ⟨le_refl 0, zero_le_one⟩)
  -- the `σ < -δ/4` slab: `kshape` reduces to the chart term `G`
  have hS2 : ContDiffOn ℝ 12
      (fun z : ℝ × (ℝ × ℝ) => kshape CI W ρh δ k z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Iio (-(δ / 4)) ×ˢ Set.univ) := by
    refine (hG.mono ?_).congr ?_
    · intro w hw; exact ⟨hw.1, trivial, trivial⟩
    · intro w hw
      have hwσ : w.2.1 < -(δ / 4) := hw.2.1
      have hblf0 : kblf δ w.2.1 = 0 := by
        rw [kblf]
        apply kstp_zero
        exact div_nonpos_of_nonpos_of_nonneg (by linarith [hδ]) (by linarith [hδ])
      have hxf0 : xfade δ w.2.1 = 0 := xfade_zero hδ hwσ.le
      simp only [kshape, knear, hblf0, hxf0, Complex.ofReal_zero]
      ring
  -- the `σ > -1` slab: every ingredient is smooth
  have hS1 : ContDiffOn ℝ 12
      (fun z : ℝ × (ℝ × ℝ) => kshape CI W ρh δ k z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Ioi (-1) ×ˢ Set.univ) := by
    intro z hz
    have hσ : (-1 : ℝ) < z.2.1 := hz.2.1
    have hsub : (Set.Icc (0 : ℝ) 1 ×ˢ Set.Ioi (-1) ×ˢ Set.univ : Set (ℝ × (ℝ × ℝ))) ⊆
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ : Set (ℝ × (ℝ × ℝ))) :=
      fun w hw => ⟨hw.1, trivial, trivial⟩
    have hGw : ContDiffWithinAt ℝ 12
        (fun z : ℝ × (ℝ × ℝ) =>
          Work.RPV.uproj (W z.1 z.2.2 (ρh z.1 z.2.2 (kclamp δ z.2.1))))
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Ioi (-1) ×ˢ Set.univ) z := (hG.mono hsub) z hz
    have hG0w : ContDiffWithinAt ℝ 12
        (fun z : ℝ × (ℝ × ℝ) =>
          Work.RPV.uproj (W 0 z.2.2 (ρh 0 z.2.2 (kclamp δ z.2.1))))
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Ioi (-1) ×ˢ Set.univ) z := (hG0.mono hsub) z hz
    have hblfW : ContDiffWithinAt ℝ 12
        (fun z : ℝ × (ℝ × ℝ) => ((kblf δ z.2.1 : ℝ) : ℂ))
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Ioi (-1) ×ˢ Set.univ) z :=
      ((hblfC.comp (by fun_prop : ContDiff ℝ 12 (fun z : ℝ × (ℝ × ℝ) => z.2.1))).contDiffAt).contDiffWithinAt
    have hxfadeW : ContDiffWithinAt ℝ 12
        (fun z : ℝ × (ℝ × ℝ) => ((xfade δ z.2.1 : ℝ) : ℂ))
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Ioi (-1) ×ˢ Set.univ) z :=
      ((hxfadeC.comp (by fun_prop : ContDiff ℝ 12 (fun z : ℝ × (ℝ × ℝ) => z.2.1))).contDiffAt).contDiffWithinAt
    have hbbmpW : ContDiffWithinAt ℝ 12
        (fun z : ℝ × (ℝ × ℝ) => ((kbbmp δ z.1 : ℝ) : ℂ))
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Ioi (-1) ×ˢ Set.univ) z :=
      ((hbbmpC.comp (by fun_prop : ContDiff ℝ 12 (fun z : ℝ × (ℝ × ℝ) => z.1))).contDiffAt).contDiffWithinAt
    have h2 : (2 : ℝ) + 2 * z.2.1 ≠ 0 := by intro hc; linarith
    have hkrd_at : ContDiffAt ℝ 12
        (fun p : ℝ × (ℝ × ℝ) => ((krd p.2.1 : ℝ) : ℂ)) z := by
      have hs : ContDiffAt ℝ 12 (fun p : ℝ × (ℝ × ℝ) => Real.sqrt (2 + 2 * p.2.1)) z :=
        (Real.contDiffAt_sqrt h2).comp z (by fun_prop)
      exact (Complex.ofRealCLM.contDiff.contDiffAt).comp z hs
    have hkphc_at : ContDiffAt ℝ 12
        (fun p : ℝ × (ℝ × ℝ) => kphc δ k p.2.1) z :=
      hkphc1.contDiffAt.comp z (by fun_prop)
    have htarg_at : ContDiffAt ℝ 12
        (fun p : ℝ × (ℝ × ℝ) => ktarg δ k p.2.1 p.2.2) z := by
      have hpc : ContDiffAt ℝ 12
          (fun p : ℝ × (ℝ × ℝ) => ((kphc δ k p.2.1 : ℝ) : ℂ)) z :=
        (Complex.ofRealCLM.contDiff.contDiffAt).comp z hkphc_at
      have ht2 : ContDiffAt ℝ 12
          (fun p : ℝ × (ℝ × ℝ) => ((p.2.2 : ℝ) : ℂ)) z :=
        (Complex.ofRealCLM.contDiff.contDiffAt).comp z (by fun_prop)
      have harg : ContDiffAt ℝ 12
          (fun p : ℝ × (ℝ × ℝ) =>
            (((p.2.2 : ℝ) : ℂ) + ((kphc δ k p.2.1 : ℝ) : ℂ)) * Complex.I) z :=
        (ht2.add hpc).mul contDiffAt_const
      have hexp : ContDiffAt ℝ 12
          (fun p : ℝ × (ℝ × ℝ) =>
            Complex.exp ((((p.2.2 : ℝ) : ℂ) + ((kphc δ k p.2.1 : ℝ) : ℂ)) * Complex.I)) z :=
        (Complex.contDiff_exp.contDiffAt).comp z harg
      exact hkrd_at.mul hexp
    have hkfsh_at : ContDiffAt ℝ 12
        (fun p : ℝ × (ℝ × ℝ) => kfsh CI δ k p.1 p.2.1 p.2.2) z := by
      have hm : ContDiffAt ℝ 12
          (fun p : ℝ × (ℝ × ℝ) => (krpf δ p.2.1 * p.1, p.2.2 + kphc δ k p.2.1)) z :=
        ((hkrpf1.contDiffAt.comp z (by fun_prop : ContDiffAt ℝ 12 (fun p : ℝ × (ℝ × ℝ) => p.2.1) z)).mul
            (by fun_prop : ContDiffAt ℝ 12 (fun p : ℝ × (ℝ × ℝ) => p.1) z)).prodMk
          ((by fun_prop : ContDiffAt ℝ 12 (fun p : ℝ × (ℝ × ℝ) => p.2.2) z).add hkphc_at)
      have hc : ContDiffAt ℝ 12
          (fun p : ℝ × (ℝ × ℝ) => CI.c (krpf δ p.2.1 * p.1) (p.2.2 + kphc δ k p.2.1)) z :=
        ((CI.smooth.contDiffAt).of_le (by norm_num)).comp z hm
      exact hkrd_at.mul hc
    have hknear : ContDiffWithinAt ℝ 12
        (fun p : ℝ × (ℝ × ℝ) => knear CI W ρh δ k p.1 p.2.1 p.2.2)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Ioi (-1) ×ˢ Set.univ) z := by
      simp only [knear]
      exact hGw.add ((hbbmpW.mul hxfadeW).mul
        (htarg_at.contDiffWithinAt.sub hG0w))
    have hkfshW : ContDiffWithinAt ℝ 12
        (fun p : ℝ × (ℝ × ℝ) => kfsh CI δ k p.1 p.2.1 p.2.2)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Ioi (-1) ×ˢ Set.univ) z := hkfsh_at.contDiffWithinAt
    have hF : ContDiffWithinAt ℝ 12
        (fun p : ℝ × (ℝ × ℝ) => kshape CI W ρh δ k p.1 p.2.1 p.2.2)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Ioi (-1) ×ˢ Set.univ) z := by
      simp only [kshape]
      exact ((contDiffWithinAt_const.sub hblfW).mul hknear).add (hblfW.mul hkfshW)
    exact hF
  -- glue the two slabs
  apply contDiffOn_of_locally_contDiffOn
  intro z hz
  by_cases hσ : (-1 : ℝ) < z.2.1
  · refine ⟨Set.univ ×ˢ Set.Ioi (-1) ×ˢ Set.univ, ?_, ?_, ?_⟩
    · exact isOpen_univ.prod (isOpen_Ioi.prod isOpen_univ)
    · exact ⟨trivial, hσ, trivial⟩
    · exact hS1.mono (fun w hw => ⟨hw.1.1, hw.2.2.1, trivial⟩)
  · push_neg at hσ
    refine ⟨Set.univ ×ˢ Set.Iio (-(δ / 4)) ×ˢ Set.univ, ?_, ?_, ?_⟩
    · exact isOpen_univ.prod (isOpen_Iio.prod isOpen_univ)
    · exact ⟨trivial, lt_of_le_of_lt hσ (by linarith), trivial⟩
    · exact hS2.mono (fun w hw => ⟨hw.1.1, hw.2.2.1, trivial⟩)

end

end Work.RPB.B5
