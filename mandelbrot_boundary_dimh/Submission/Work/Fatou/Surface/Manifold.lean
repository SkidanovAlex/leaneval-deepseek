import Submission.Work.Fatou.Surface.Core
import Submission.Work.Fatou.Surface.localInverse

/-!
# `XF` is a Riemann surface, and the deck map `ζ ↦ ζ+1` is holomorphic

We check that the atlas `{chart D n}` makes `XF D` a one-dimensional complex manifold: the
transition maps are `id` (same index), `F` (index `n-1`) and `F⁻¹` (index `n+1`) on their sources,
and empty otherwise, hence holomorphic.  The deck transformation `T : ζ ↦ ζ+1` is the identity in
the charts `chart n → chart (n+1)`, hence holomorphic.
-/

namespace Work.Fatou

open MandelDim Filter Set Metric
open scoped Topology Manifold ContDiff

noncomputable section

/-- `Qreg b₁ b₂` is open. -/
theorem Qreg_isOpen (b₁ b₂ : Option ℂ) : IsOpen (Qreg b₁ b₂) := by
  have h1 : ∀ a : ℂ, IsOpen {z : ℂ | -|(z - a).im| < (z - a).re} := by
    intro a
    exact isOpen_lt (by fun_prop) (by fun_prop)
  have h2 : ∀ b : ℂ, IsOpen {z : ℂ | (z - b).re < |(z - b).im|} := by
    intro b
    exact isOpen_lt (by fun_prop) (by fun_prop)
  rcases b₁ with _ | a <;> rcases b₂ with _ | b
  · have : Qreg none none = Set.univ := by ext z; simp [Qreg]
    rw [this]; exact isOpen_univ
  · have : Qreg none (some b) = {z : ℂ | (z - b).re < |(z - b).im|} := by ext z; simp [Qreg]
    rw [this]; exact h2 b
  · have : Qreg (some a) none = {z : ℂ | -|(z - a).im| < (z - a).re} := by ext z; simp [Qreg]
    rw [this]; exact h1 a
  · have : Qreg (some a) (some b) =
        {z : ℂ | -|(z - a).im| < (z - a).re} ∩ {z : ℂ | (z - b).re < |(z - b).im|} := by
      ext z; simp [Qreg]
    rw [this]; exact (h1 a).inter (h2 b)

namespace FatouData

/-- The open vertical strip of half-width `1/8` around `x₀`, the domain of the local inverse. -/
def stripS (D : FatouData) : Set ℂ :=
  {z : ℂ | xOf D.b₁ D.b₂ - 1 / 8 < z.re ∧ z.re < xOf D.b₁ D.b₂ + 1 / 8}

/-- `F` is holomorphic on `Qreg`. -/
theorem contDiffOn_F (D : FatouData) : ContDiffOn ℂ 1 D.F (Qreg D.b₁ D.b₂) :=
  (D.nt.1.analyticOnNhd (Qreg_isOpen D.b₁ D.b₂)).contDiffOn_of_completeSpace

/-- The inverse of `F` on the central strip. -/
noncomputable def finv (D : FatouData) : ℂ → ℂ :=
  (Work.Fatou.Surface.localInverse D.adm D.nt).choose

theorem finv_apply (D : FatouData) {z : ℂ} (h1 : xOf D.b₁ D.b₂ - 1 / 8 < z.re)
    (h2 : z.re < xOf D.b₁ D.b₂ + 1 / 8) : D.finv (D.F z) = z :=
  (Work.Fatou.Surface.localInverse D.adm D.nt).choose_spec.1 z h1 h2

theorem F_finv_apply (D : FatouData) {w : ℂ} (hw : w ∈ D.F '' D.stripS) : D.F (D.finv w) = w :=
  (Work.Fatou.Surface.localInverse D.adm D.nt).choose_spec.2.1 w hw

theorem contDiffOn_finv (D : FatouData) : ContDiffOn ℂ 1 D.finv (D.F '' D.stripS) :=
  (Work.Fatou.Surface.localInverse D.adm D.nt).choose_spec.2.2

/-- The chart inverse, as an element of `ℂ`. -/
theorem toℂ_chart_symm (D : FatouData) (n : ℤ) (w : ℂ) :
    D.toℂ ((D.chart n).symm w) = D.devHI w + (n : ℂ) := rfl

/-- The chart-`n`-coordinate of `devH ζ` is `devH (ζ - n)`. -/
theorem chart_apply_ofℂ (D : FatouData) (n : ℤ) (ζ : ℂ) :
    D.chart n (D.ofℂ ζ) = D.devH (ζ - (n : ℂ)) := rfl

/-- The identity transition (same chart). -/
theorem transition_self (D : FatouData) (n : ℤ) :
    Set.EqOn (fun w : ℂ => D.chart n ((D.chart n).symm w)) id ((D.chart n).target) := by
  intro w hw
  exact (D.chart n).right_inv hw

theorem chart_symm_devH (D : FatouData) (n : ℤ) (ζ : ℂ) :
    (D.chart n).symm (D.devH ζ) = D.ofℂ (ζ + (n : ℂ)) := by
  show D.ofℂ (D.devHI (D.devH ζ) + (n : ℂ)) = D.ofℂ (ζ + (n : ℂ))
  rw [D.devHI_apply_devH]

theorem chart_apply_chart_symm (D : FatouData) (n : ℤ) (ζ : ℂ) :
    D.chart n ((D.chart n).symm (D.devH ζ)) = D.devH ζ := by
  rw [D.chart_symm_devH, D.chart_apply_ofℂ]
  congr 1
  ring

/-- The source of the transition `chart n → chart m` with `|m - n| ≥ 2` is empty. -/
theorem transition_source_empty (D : FatouData) {n m : ℤ} (h : m - n ≥ 2 ∨ m - n ≤ -2) :
    ((D.chart n).target ∩ (D.chart n).symm ⁻¹' (D.chart m).source) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro w hw
  obtain ⟨hwT, hwS⟩ := hw
  obtain ⟨ζ, hζ, rfl⟩ := hwT
  have hsrc : (m : ℝ) - 1 / 8 < ζ.re + (n : ℝ) ∧ ζ.re + (n : ℝ) < (m : ℝ) + 9 / 8 := by
    have h := hwS
    simp only [Set.mem_preimage] at h
    rw [D.chart_symm_devH n ζ] at h
    simpa [FatouData.chartSource] using h
  rcases h with h | h
  · have : ζ.re < 9 / 8 := hζ.2
    have : (m : ℝ) - (n : ℝ) ≥ 2 := by exact_mod_cast h
    linarith [hsrc.1]
  · have : -(1 / 8) < ζ.re := hζ.1
    have : (m : ℝ) - (n : ℝ) ≤ -2 := by exact_mod_cast h
    linarith [hsrc.2]

/-- The transition `chart n → chart (n-1)` is `F`. -/
theorem transition_pred (D : FatouData) (n : ℤ) :
    Set.EqOn (fun w : ℂ => D.chart (n - 1) ((D.chart n).symm w)) D.F
      ((D.chart n).target ∩ (D.chart n).symm ⁻¹' (D.chart (n - 1)).source) := by
  intro w hw
  obtain ⟨hwT, hwS⟩ := hw
  obtain ⟨ζ, hζ, rfl⟩ := hwT
  have hsrc : ((n - 1 : ℤ) : ℝ) - 1 / 8 < ζ.re + (n : ℝ) ∧
      ζ.re + (n : ℝ) < ((n - 1 : ℤ) : ℝ) + 9 / 8 := by
    have h := hwS
    simp only [Set.mem_preimage] at h
    rw [D.chart_symm_devH n ζ] at h
    simpa [FatouData.chartSource] using h
  have hre : ζ.re ≤ 1 / 8 := by
    have h2 : ((n - 1 : ℤ) : ℝ) = (n : ℝ) - 1 := by push_cast; ring
    linarith [hsrc.2, h2.le, h2.ge]
  change D.chart (n - 1) ((D.chart n).symm (D.devH ζ)) = D.F (D.devH ζ)
  rw [D.chart_symm_devH n ζ, D.chart_apply_ofℂ, FatouData.devH_eq]
  have hsimp : ζ + (n : ℂ) - ((n - 1 : ℤ) : ℂ) = ζ + 1 := by push_cast; ring
  rw [hsimp]
  exact devH_add_one (le_of_lt hζ.1) hre

/-- The transition `chart n → chart (n+1)` is `F⁻¹`. -/
theorem transition_succ (D : FatouData) (n : ℤ) :
    Set.EqOn (fun w : ℂ => D.chart (n + 1) ((D.chart n).symm w)) D.finv
      ((D.chart n).target ∩ (D.chart n).symm ⁻¹' (D.chart (n + 1)).source) := by
  intro w hw
  obtain ⟨hwT, hwS⟩ := hw
  obtain ⟨ζ, hζ, rfl⟩ := hwT
  have hsrc : ((n + 1 : ℤ) : ℝ) - 1 / 8 < ζ.re + (n : ℝ) ∧
      ζ.re + (n : ℝ) < ((n + 1 : ℤ) : ℝ) + 9 / 8 := by
    have h := hwS
    simp only [Set.mem_preimage] at h
    rw [D.chart_symm_devH n ζ] at h
    simpa [FatouData.chartSource] using h
  have hre : -(1 / 8) < ζ.re - 1 ∧ ζ.re - 1 < 1 / 8 := by
    have h2 : ((n + 1 : ℤ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    constructor
    · linarith [hsrc.1, h2.le, h2.ge]
    · linarith [hζ.2]
  -- the transition value is `devH (ζ - 1)`, which lies in the strip
  have hstrip : D.devH (ζ - 1) ∈ D.stripS := by
    rw [show D.devH (ζ - 1) = Work.Fatou.devH (xOf D.b₁ D.b₂) D.F (ζ - 1) from rfl,
      devH_of_le_one_eighth (le_of_lt hre.2), stripS]
    simp only [Set.mem_ofPred_eq]
    simp
    constructor <;> linarith [hre.1]
  have hF : D.F (D.devH (ζ - 1)) = D.devH ζ := by
    have h := devH_add_one (x₀ := xOf D.b₁ D.b₂) (F := D.F) (ζ := ζ - 1)
      (le_of_lt hre.1) (le_of_lt hre.2)
    rw [show ζ - 1 + 1 = ζ by ring] at h
    rw [show D.devH (ζ - 1) = Work.Fatou.devH (xOf D.b₁ D.b₂) D.F (ζ - 1) from rfl,
      show D.devH ζ = Work.Fatou.devH (xOf D.b₁ D.b₂) D.F ζ from rfl]
    exact h.symm
  change D.chart (n + 1) ((D.chart n).symm (D.devH ζ)) = D.finv (D.devH ζ)
  rw [D.chart_symm_devH n ζ, D.chart_apply_ofℂ]
  have hsimp : ζ + (n : ℂ) - ((n + 1 : ℤ) : ℂ) = ζ - 1 := by push_cast; ring
  rw [hsimp]
  show Work.Fatou.devH (xOf D.b₁ D.b₂) D.F (ζ - 1) = D.finv (D.devH ζ)
  rw [← hF]
  exact (D.finv_apply hstrip.1 hstrip.2).symm

end FatouData

open FatouData

/-- `XF D` is a one-dimensional complex manifold. -/
instance isManifoldXF (D : FatouData) :
    IsManifold (modelWithCornersSelf ℂ ℂ) 1 D.XF := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨n, rfl⟩ := he
  obtain ⟨m, rfl⟩ := he'
  have hgoal : ContDiffOn ℂ 1 (fun w : ℂ => D.chart m ((D.chart n).symm w))
      ((D.chart n).target ∩ (D.chart n).symm ⁻¹' (D.chart m).source) := by
    rcases eq_or_ne m n with hmn0 | hmn0
    · rw [hmn0]
      exact contDiffOn_id.congr fun w hw => D.transition_self n hw.1
    rcases eq_or_ne m (n + 1) with hmn1 | hmn1
    · rw [hmn1]
      have hsub : (D.chart n).target ∩ (D.chart n).symm ⁻¹' (D.chart (n + 1)).source ⊆
          D.F '' D.stripS := by
        rintro w ⟨hwT, hwS⟩
        obtain ⟨ζ, hζ, rfl⟩ := hwT
        have hsrc : ((n + 1 : ℤ) : ℝ) - 1 / 8 < ζ.re + (n : ℝ) ∧
            ζ.re + (n : ℝ) < ((n + 1 : ℤ) : ℝ) + 9 / 8 := by
          have h := hwS
          simp only [Set.mem_preimage] at h
          rw [D.chart_symm_devH n ζ] at h
          simpa [FatouData.chartSource] using h
        have h2 : ((n + 1 : ℤ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        have hre : -(1 / 8) < ζ.re - 1 ∧ ζ.re - 1 < 1 / 8 := by
          constructor
          · linarith [hsrc.1, h2.le, h2.ge]
          · linarith [hζ.2]
        refine ⟨Work.Fatou.devH (xOf D.b₁ D.b₂) D.F (ζ - 1), ?_, ?_⟩
        · rw [FatouData.stripS, devH_of_le_one_eighth (le_of_lt hre.2)]
          simp only [Set.mem_ofPred_eq]
          simp
          constructor <;> linarith [hre.1]
        · have h := devH_add_one (x₀ := xOf D.b₁ D.b₂) (F := D.F) (ζ := ζ - 1)
            (le_of_lt hre.1) (le_of_lt hre.2)
          rw [show ζ - 1 + 1 = ζ by ring] at h
          rw [show Work.Fatou.devH (xOf D.b₁ D.b₂) D.F (ζ - 1) =
              Work.Fatou.devH (xOf D.b₁ D.b₂) D.F (ζ - 1) from rfl]
          exact h.symm
      exact (D.contDiffOn_finv.mono hsub).congr fun w hw => D.transition_succ n hw
    rcases eq_or_ne m (n - 1) with hmn2 | hmn2
    · rw [hmn2]
      have hsub : (D.chart n).target ∩ (D.chart n).symm ⁻¹' (D.chart (n - 1)).source ⊆
          Qreg D.b₁ D.b₂ := by
        rintro w ⟨hwT, hwS⟩
        obtain ⟨ζ, hζ, rfl⟩ := hwT
        have hsrc : ((n - 1 : ℤ) : ℝ) - 1 / 8 < ζ.re + (n : ℝ) ∧
            ζ.re + (n : ℝ) < ((n - 1 : ℤ) : ℝ) + 9 / 8 := by
          have h := hwS
          simp only [Set.mem_preimage] at h
          rw [D.chart_symm_devH n ζ] at h
          simpa [FatouData.chartSource] using h
        have h2 : ((n - 1 : ℤ) : ℝ) = (n : ℝ) - 1 := by push_cast; ring
        have hre : ζ.re < 1 / 8 := by linarith [hsrc.2, h2.le, h2.ge]
        show Work.Fatou.devH (xOf D.b₁ D.b₂) D.F ζ ∈ Qreg D.b₁ D.b₂
        rw [devH_of_le_one_eighth hre.le]
        refine strip_eighth_subset_Qreg D.adm ?_
        simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.ofReal_re]
        exact ⟨by linarith [hζ.1], by linarith [hre]⟩
      exact (D.contDiffOn_F.mono hsub).congr fun w hw => D.transition_pred n hw
    · have hempty : (D.chart n).target ∩ (D.chart n).symm ⁻¹' (D.chart m).source = ∅ := by
        apply D.transition_source_empty
        omega
      rw [hempty]
      exact contDiffOn_empty
  simpa [OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    ModelWithCorners.Boundaryless.range_eq_univ, FatouData.chart_source, FatouData.chart_target,
    Set.preimage_id, Set.univ_inter, Function.comp_def] using hgoal

end

end Work.Fatou
