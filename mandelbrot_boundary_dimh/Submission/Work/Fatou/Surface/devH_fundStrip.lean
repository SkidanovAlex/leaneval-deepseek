import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.Fatou.Setup
import Submission.Work.Fatou.DevH.basic
import Submission.Work.Fatou.DevH.devH_deriv
import Submission.Work.Fatou.DevH.global
import Submission.Work.Fatou.Qreg.Setup
import Submission.Work.Fatou.Qreg.InjGeom
import Submission.Work.Fatou.Qreg.fatouInjOnQ

/-!
# The unit strip is a fundamental domain via `devH`

This file proves `Work.Fatou.Surface.devH_fundStrip`: for a near-translation `F` on an admissible
region `𝒬 = Qreg b₁ b₂` and `x₀ = xOf b₁ b₂`, the unfolding map
`devH x₀ F ζ = x₀ + ζ + χ(Re ζ)·ε(x₀+ζ-1)` maps the unit strip `{0 ≤ Re ζ < 1}` **onto** the
fundamental strip `fundStrip F 𝒬 x₀` and takes its values in `𝒬`.

* *Into.*  For `0 ≤ Re ζ < 1` one has `devH ζ ∈ 𝒬` (`devH_mem_Qreg`, the strip `Σ = (-1/8, 9/8)`
  stays inside `𝒬`).  Splitting at `Re ζ = 7/8`, either `devH ζ` is within `1/32` of `x₀ + ζ`
  (so `Re (devH ζ) ≥ x₀` and any `𝒬`-preimage `w` satisfies `Re w ≤ Re (devH ζ) - 31/32 < x₀`),
  or `devH ζ = F (x₀+ζ-1)` with `x₀+ζ-1 ∈ 𝒬` of real part `< x₀`, and injectivity of `F` on `𝒬`
  (`Work.Fatou.Qreg.fatouInjOnQ`) identifies the preimage.

* *Onto.*  `devH` is a globally expanding homeomorphism of `ℂ` (`DevH/global.lean`), so every `s`
  has *some* preimage `ζ ∈ ℂ`; it suffices to rule out `Re ζ ≤ -1/8` and `Re ζ ≥ 9/8`, which
  follows from the explicit form of `devH` there and the two bounds on `s ∈ fundStrip`:
  `x₀ ≤ Re s < x₀ + 1 + 1/31`.  The upper bound is the fixed point of `w ↦ s - 1 - ε(w)` in
  `B̄(s-1, 1/32)`: that closed ball lies in `𝒬` as soon as `Re s ≥ x₀ + 1 + 1/31` (it misses both
  excluded cones), the map is a `1/32`-contraction there, and its fixed point is a `𝒬`-preimage
  of `s` of real part `≥ x₀`, contradicting the defining property of the fundamental strip.
-/

namespace Work.Fatou.Surface

open MandelDim Set Metric
open scoped Topology

noncomputable section

variable {b₁ b₂ : Option ℂ} {F : ℂ → ℂ}

/-! ### `DevHBound` for `devH` (from `devH_deriv`) -/

lemma devHBound_xOf (hadm : QAdm b₁ b₂) (hF : NearTranslationOn F (Qreg b₁ b₂)) :
    Work.Fatou.DevHBound (Work.Fatou.xOf b₁ b₂) F := by
  obtain ⟨h1, h2, -, -⟩ := Work.Fatou.DevH.devH_deriv hadm hF
  exact ⟨h1, h2⟩

/-- `devH x₀ F` is surjective (it is a globally expanding homeomorphism of `ℂ`). -/
lemma devH_surjective_xOf (hadm : QAdm b₁ b₂) (hF : NearTranslationOn F (Qreg b₁ b₂)) :
    Function.Surjective (Work.Fatou.devH (Work.Fatou.xOf b₁ b₂) F) :=
  Work.Fatou.devH_surjective (devHBound_xOf hadm hF)

/-! ### The error term is `1/32`-Lipschitz along segments inside `Qreg` -/

lemma subId_lipschitz_of_segment (_hadm : QAdm b₁ b₂) (hF : NearTranslationOn F (Qreg b₁ b₂))
    {x y : ℂ} (hseg : segment ℝ x y ⊆ Qreg b₁ b₂) :
    ‖(F y - y) - (F x - x)‖ ≤ (1 / 32 : ℝ) * ‖y - x‖ := by
  have hopen : IsOpen (Qreg b₁ b₂) := Work.Fatou.Qreg.isOpen_Qreg b₁ b₂
  have hA : ∀ w ∈ segment ℝ x y, DifferentiableAt ℂ (fun z : ℂ => F z - z) w := by
    intro w hw
    exact ((hF.1 w (hseg hw)).differentiableAt (hopen.mem_nhds (hseg hw))).sub
      differentiableAt_id
  have hB : ∀ w ∈ segment ℝ x y, ‖deriv (fun z : ℂ => F z - z) w‖ ≤ (1 / 32 : ℝ) := by
    intro w hw
    have hdF : DifferentiableAt ℂ F w :=
      (hF.1 w (hseg hw)).differentiableAt (hopen.mem_nhds (hseg hw))
    have hderiv : deriv (fun z : ℂ => F z - z) w = deriv F w - 1 := by
      have hfun : (fun z : ℂ => F z - z) = (F - id) := by ext z; rfl
      rw [hfun, deriv_sub hdF differentiableAt_id, deriv_id]
    rw [hderiv]
    exact (hF.2 w (hseg hw)).2
  exact Convex.norm_image_sub_le_of_norm_deriv_le (s := segment ℝ x y)
    (f := fun z : ℂ => F z - z) hA hB (convex_segment x y)
    (left_mem_segment (𝕜 := ℝ) x y) (right_mem_segment (𝕜 := ℝ) x y)

/-! ### The ball `B̄(z-1, 1/32)` lies in `Qreg` for `Re z` large -/

lemma closedBall_sub_qreg (hadm : QAdm b₁ b₂) {z : ℂ} (hz : z ∈ Qreg b₁ b₂)
    (hzx : Work.Fatou.xOf b₁ b₂ + 1 + 1 / 31 ≤ z.re) :
    closedBall (z - 1) (1 / 32 : ℝ) ⊆ Qreg b₁ b₂ := by
  intro u hu
  rw [mem_closedBall, dist_eq_norm] at hu
  have hre : |(u - (z - 1)).re| ≤ (1 / 32 : ℝ) := le_trans (Complex.abs_re_le_norm _) hu
  have him : |(u - (z - 1)).im| ≤ (1 / 32 : ℝ) := le_trans (Complex.abs_im_le_norm _) hu
  have hre1 : -(1 / 32 : ℝ) ≤ (u - (z - 1)).re := (abs_le.mp hre).1
  have hre2 : (u - (z - 1)).re ≤ (1 / 32 : ℝ) := (abs_le.mp hre).2
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- the `b₁`-cone: `Re (u - a) > 0`
    have ha' : a.re + 1 < Work.Fatou.xOf b₁ b₂ := Work.Fatou.xOf_gt_left hadm a ha
    have hpos : 0 < (u - a).re := by
      have h1 : (u - a).re = (u - (z - 1)).re + (z - a).re - 1 := by
        simp only [Complex.sub_re, Complex.one_re]; ring
      have h2 : Work.Fatou.xOf b₁ b₂ + 1 + 1 / 31 - a.re ≤ (z - a).re := by
        simp only [Complex.sub_re]; linarith
      rw [h1]; linarith
    have habs : -|(u - a).im| ≤ 0 := neg_nonpos.mpr (abs_nonneg _)
    linarith
  · -- the `b₂`-cone
    have hb' : (z - b).re < |(z - b).im| := hz.2 b hb
    have him2 : (u - b).im - (z - b).im = (u - (z - 1)).im := by
      simp only [Complex.sub_im, Complex.one_im]; ring
    have h5 : |(z - b).im| ≤ |(u - b).im| + 1 / 32 := by
      have h6 : |(z - b).im| = |(u - b).im - ((u - b).im - (z - b).im)| := by ring_nf
      rw [h6, him2]
      calc |(u - b).im - (u - (z - 1)).im| ≤ |(u - b).im| + |(u - (z - 1)).im| := abs_sub _ _
        _ ≤ |(u - b).im| + 1 / 32 := by linarith
    have h7 : (u - b).re = (u - (z - 1)).re + (z - b).re - 1 := by
      simp only [Complex.sub_re, Complex.one_re]; ring
    rw [h7]; linarith

/-! ### A preimage in `Qreg` with real part `≥ x₀`, for `Re z` large -/

lemma exists_preimage_of_xOf_add (hadm : QAdm b₁ b₂) (hF : NearTranslationOn F (Qreg b₁ b₂))
    {z : ℂ} (hz : z ∈ Qreg b₁ b₂) (hzx : Work.Fatou.xOf b₁ b₂ + 1 + 1 / 31 ≤ z.re) :
    ∃ w ∈ Qreg b₁ b₂, F w = z ∧ Work.Fatou.xOf b₁ b₂ ≤ w.re := by
  have hball : closedBall (z - 1) (1 / 32 : ℝ) ⊆ Qreg b₁ b₂ := closedBall_sub_qreg hadm hz hzx
  set T : ℂ → ℂ := fun u => (z - 1) - Work.Fatou.eps F u with hT
  have hmaps : MapsTo T (closedBall (z - 1) (1 / 32 : ℝ)) (closedBall (z - 1) (1 / 32 : ℝ)) := by
    intro u hu
    have heps : ‖Work.Fatou.eps F u‖ ≤ (1 / 32 : ℝ) := (hF.2 u (hball hu)).1
    rw [mem_closedBall, dist_eq_norm] at hu ⊢
    have h1 : T u - (z - 1) = -(Work.Fatou.eps F u) := by
      show (z - 1) - Work.Fatou.eps F u - (z - 1) = -Work.Fatou.eps F u
      ring
    rw [h1, norm_neg]
    exact heps
  have hcontr : ∀ u ∈ closedBall (z - 1) (1 / 32 : ℝ), ∀ u' ∈ closedBall (z - 1) (1 / 32 : ℝ),
      ‖T u - T u'‖ ≤ (1 / 32 : ℝ) * ‖u - u'‖ := by
    intro u hu u' hu'
    have hseg : segment ℝ u u' ⊆ Qreg b₁ b₂ :=
      ((convex_closedBall (z - 1) (1 / 32 : ℝ)).segment_subset hu hu').trans hball
    have h := subId_lipschitz_of_segment hadm hF hseg
    have heq : T u - T u' = (F u' - u') - (F u - u) := by
      show (z - 1) - Work.Fatou.eps F u - ((z - 1) - Work.Fatou.eps F u') = _
      rw [Work.Fatou.eps_apply, Work.Fatou.eps_apply]
      ring
    rw [heq]
    simpa only [norm_sub_rev u u'] using h
  have hsf : MapsTo T (closedBall (z - 1) (1 / 32 : ℝ)) (closedBall (z - 1) (1 / 32 : ℝ)) := hmaps
  have hLipSub : LipschitzWith (1 / 32 : NNReal)
      (MapsTo.restrict T (closedBall (z - 1) (1 / 32 : ℝ))
        (closedBall (z - 1) (1 / 32 : ℝ)) hsf) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro u u'
    have hu : (u : ℂ) ∈ closedBall (z - 1) (1 / 32 : ℝ) := u.2
    have hu' : (u' : ℂ) ∈ closedBall (z - 1) (1 / 32 : ℝ) := u'.2
    have h := hcontr u.1 hu u'.1 hu'
    dsimp only [MapsTo.restrict]
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    have h32 : ((1 / 32 : NNReal) : ℝ) = 1 / 32 := by norm_num
    rw [h32]
    exact h
  have hcK : ContractingWith (1 / 32 : NNReal)
      (MapsTo.restrict T (closedBall (z - 1) (1 / 32 : ℝ))
        (closedBall (z - 1) (1 / 32 : ℝ)) hsf) :=
    ⟨(by norm_num : (1 / 32 : NNReal) < 1), hLipSub⟩
  obtain ⟨w, hwmem, hwfix, -, -⟩ := hcK.exists_fixedPoint' isClosed_closedBall.isComplete hsf
    (x := (z - 1)) (mem_closedBall_self (by norm_num)) (by simp)
  have hFw : F w = z := by
    have h0 : (z - 1) - Work.Fatou.eps F w = w := hwfix
    rw [Work.Fatou.eps_apply] at h0
    linear_combination -h0
  have hwre : Work.Fatou.xOf b₁ b₂ ≤ w.re := by
    have h1 : ‖w - (z - 1)‖ ≤ (1 / 32 : ℝ) := by
      have h1 := hwmem
      rwa [mem_closedBall, dist_eq_norm] at h1
    have h2 : |w.re - (z - 1).re| ≤ (1 / 32 : ℝ) := Work.Fatou.abs_re_sub_le h1
    have h3 : (z - 1).re = z.re - 1 := by simp
    rw [h3] at h2
    have h4 := (abs_le.mp h2).1
    linarith
  exact ⟨w, hball hwmem, hFw, hwre⟩

/-- **The unit strip is a fundamental domain via `devH`** (the "STRIP" fact of the blueprint).

With `x₀ = xOf b₁ b₂`, the unfolding map `devH x₀ F` (see `Submission/Work/Fatou/Setup.lean`) maps
the vertical strip `{0 ≤ Re ζ < 1}` of width one *onto* the fundamental strip
`fundStrip F (Qreg b₁ b₂) x₀` of `F`, and takes its values in `Qreg`.

Into: for `0 ≤ Re ζ < 1`, split `Re ζ ∈ [0,1/8]`, `(1/8,7/8)`, `[7/8,1)`.  In the first two cases
`devH ζ` is close to `x₀+ζ` (`|χ| ≤ 1`, `|ε| ≤ 1/32`), so its real part is `≥ x₀` and any
`F`-preimage `w ∈ Qreg` satisfies `Re w ≤ Re (devH ζ) - 31/32 < x₀`; in the third case
`devH ζ = F (x₀+ζ-1)` where `x₀+ζ-1 ∈ Qreg` has real part `< x₀`, and uniqueness of the preimage in
`Qreg` (`Work.Fatou.Qreg.fatouInjOnQ`) gives the condition.

Onto: `fundStrip ⊆ {Re < x₀ + 1 + 1/31}` (otherwise `s ∈ fundStrip` with `Re s ≥ x₀ + 1 + 1/31`
has a preimage in `Qreg` with real part `≥ x₀`, namely the fixed point of
`w ↦ s - 1 - ε(w)` in `B̄(s-1, 1/31)`, which lies in `Qreg` with the margins above), while
`devH (Σ) ⊇ {x₀ - 3/32 ≤ Re ≤ x₀ + 1 + 3/32}` by the Banach fixed point argument for
`ζ ↦ ζ₀ - χ(Re ζ)·ε(x₀+ζ-1)` on `B̄(ζ₀, 1/32)` (using `|χ| ≤ 1`, `|ε| ≤ 1/32` and the
Lipschitz bound `‖D(χ·ε∘(x₀+·-1))‖ ≤ 3/32` from `Work.Fatou.devH_deriv`); hence `s = devH ζ` for
some `ζ ∈ Σ`, and `Re ζ < 0` (resp. `Re ζ ≥ 1`) would contradict the fundamental-strip property
of `s`. -/
theorem devH_fundStrip {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} (hadm : MandelDim.QAdm b₁ b₂)
    (hF : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂)) :
    (∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re < 1 → Work.Fatou.devH (Work.Fatou.xOf b₁ b₂) F ζ ∈
        MandelDim.fundStrip F (MandelDim.Qreg b₁ b₂) (Work.Fatou.xOf b₁ b₂)) ∧
    (∀ s ∈ MandelDim.fundStrip F (MandelDim.Qreg b₁ b₂) (Work.Fatou.xOf b₁ b₂),
        ∃ ζ : ℂ, 0 ≤ ζ.re ∧ ζ.re < 1 ∧ Work.Fatou.devH (Work.Fatou.xOf b₁ b₂) F ζ = s) ∧
    (∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re < 1 →
        Work.Fatou.devH (Work.Fatou.xOf b₁ b₂) F ζ ∈ MandelDim.Qreg b₁ b₂) := by
  set x₀ : ℝ := Work.Fatou.xOf b₁ b₂ with hx₀
  -- membership of `devH` in `Qreg` on the unit strip
  have hmemQ : ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re < 1 → Work.Fatou.devH x₀ F ζ ∈ Qreg b₁ b₂ := by
    intro ζ h0 h1
    rw [hx₀]
    exact Work.Fatou.devH_mem_Qreg hadm hF
      (Work.Fatou.mem_Sigma.mpr ⟨by linarith, by linarith⟩)
  -- `devH` is within `1/32` of the translation on `1/8 ≤ Re ζ ≤ 15/8`
  have hnear : ∀ ζ : ℂ, (1 / 8 : ℝ) ≤ ζ.re → ζ.re ≤ 15 / 8 →
      ‖Work.Fatou.devH x₀ F ζ - ((x₀ : ℂ) + ζ)‖ ≤ (1 / 32 : ℝ) := by
    intro ζ h1 h2
    rw [hx₀]
    exact Work.Fatou.devH_sub_le hadm hF h1 h2
  -- `x₀ + ζ - 1 ∈ Qreg` for `1/8 ≤ Re ζ ≤ 15/8`
  have hvQ : ∀ ζ : ℂ, (1 / 8 : ℝ) ≤ ζ.re → ζ.re ≤ 15 / 8 →
      (x₀ : ℂ) + ζ - 1 ∈ Qreg b₁ b₂ := by
    intro ζ h1 h2
    rw [hx₀]
    exact Work.Fatou.xOf_add_mem_Qreg hadm h1 h2
  have hsurj : Function.Surjective (Work.Fatou.devH x₀ F) := by
    rw [hx₀]; exact devH_surjective_xOf hadm hF
  -- the deviation of `devH` from the translation, in the left/middle part of the unit strip
  have hdev_le : ∀ ζ : ℂ, ζ.re ≤ 7 / 8 →
      |(Work.Fatou.devH x₀ F ζ).re - (x₀ + ζ.re)| ≤ (1 / 32 : ℝ) := by
    intro ζ h78
    have hclose : ‖Work.Fatou.devH x₀ F ζ - ((x₀ : ℂ) + ζ)‖ ≤ (1 / 32 : ℝ) := by
      rcases le_or_gt ζ.re (1 / 8) with h18 | h18
      · rw [Work.Fatou.devH_of_le_one_eighth h18, sub_self, norm_zero]; norm_num
      · exact hnear ζ h18.le (by linarith)
    have h := Work.Fatou.abs_re_sub_le hclose
    simpa only [Complex.add_re, Complex.ofReal_re] using h
  refine ⟨?_, ?_, ?_⟩
  · -- INTO
    intro ζ h0 h1
    refine ⟨hmemQ ζ h0 h1, ?_, ?_⟩
    · -- `Re (devH ζ) ≥ x₀`
      rcases le_or_gt ζ.re (7 / 8) with h78 | h78
      · rcases le_or_gt ζ.re (1 / 8) with h18 | h18
        · rw [Work.Fatou.devH_of_le_one_eighth h18]
          simp only [Complex.add_re, Complex.ofReal_re]
          linarith
        · linarith [(abs_le.mp (hdev_le ζ h78)).1]
      · have hv : (x₀ : ℂ) + ζ - 1 ∈ Qreg b₁ b₂ := hvQ ζ (by linarith) (by linarith)
        have hdev : Work.Fatou.devH x₀ F ζ = F ((x₀ : ℂ) + ζ - 1) :=
          Work.Fatou.devH_of_ge (le_of_lt h78) (by linarith)
        have hstep := (Work.Fatou.Qreg.re_step_bounds (F := F) (u := (x₀ : ℂ) + ζ - 1)
          (hF.2 ((x₀ : ℂ) + ζ - 1) hv).1).1
        have hre : ((x₀ : ℂ) + ζ - 1).re = x₀ + ζ.re - 1 := by simp
        rw [hdev]
        linarith
    · -- every `Qreg`-preimage of `devH ζ` has real part `< x₀`
      intro w hwQ hFw
      rcases le_or_gt ζ.re (7 / 8) with h78 | h78
      · have hstep := (Work.Fatou.Qreg.re_step_bounds (F := F) (u := w) (hF.2 w hwQ).1).1
        rw [hFw] at hstep
        linarith [(abs_le.mp (hdev_le ζ h78)).2]
      · have hv : (x₀ : ℂ) + ζ - 1 ∈ Qreg b₁ b₂ := hvQ ζ (by linarith) (by linarith)
        have hdev : Work.Fatou.devH x₀ F ζ = F ((x₀ : ℂ) + ζ - 1) :=
          Work.Fatou.devH_of_ge (le_of_lt h78) (by linarith)
        have hinjQ : Set.InjOn F (Qreg b₁ b₂) := Work.Fatou.Qreg.fatouInjOnQ b₁ b₂ F hadm hF
        have heq : F w = F ((x₀ : ℂ) + ζ - 1) := by rw [hFw, hdev]
        have hwv : w = (x₀ : ℂ) + ζ - 1 := hinjQ hwQ hv heq
        have hre : ((x₀ : ℂ) + ζ - 1).re = x₀ + ζ.re - 1 := by simp
        rw [hwv, hre]; linarith
  · -- ONTO
    intro s hs
    -- (1) `Re s < x₀ + 1 + 1/31`
    have hslt : s.re < x₀ + 1 + 1 / 31 := by
      by_contra hcon
      have hcon' : x₀ + 1 + 1 / 31 ≤ s.re := le_of_not_gt hcon
      have hcon'' : Work.Fatou.xOf b₁ b₂ + 1 + 1 / 31 ≤ s.re := by rwa [hx₀] at hcon'
      obtain ⟨w, hwQ, hFw, hwre⟩ := exists_preimage_of_xOf_add hadm hF hs.1 hcon''
      have hwre' : x₀ ≤ w.re := by rwa [← hx₀] at hwre
      exact absurd (hs.2.2 w hwQ hFw) (not_lt.mpr hwre')
    -- (2) pick a preimage `ζ` of `s` (there is exactly one, `devH` being injective)
    obtain ⟨ζ, hζ⟩ := hsurj s
    have hζ' : Work.Fatou.devH x₀ F ζ = s := hζ
    -- (3) locate `ζ`
    have hζgt : -(1 / 8) < ζ.re := by
      by_contra hcon
      have hle : ζ.re ≤ 1 / 8 := by linarith
      have hexact : Work.Fatou.devH x₀ F ζ = (x₀ : ℂ) + ζ :=
        Work.Fatou.devH_of_le_one_eighth hle
      have : s.re = x₀ + ζ.re := by
        rw [← hζ', hexact]; simp only [Complex.add_re, Complex.ofReal_re]
      linarith [hs.2.1]
    have hζlt : ζ.re < 9 / 8 := by
      by_contra hcon
      have h98 : (9 / 8 : ℝ) ≤ ζ.re := le_of_not_gt hcon
      have hb : x₀ + 1 + 1 / 31 ≤ s.re := by
        have hb' : x₀ + 1 + 1 / 31 ≤ (Work.Fatou.devH x₀ F ζ).re := by
          rcases le_or_gt ζ.re (15 / 8) with hle | hgt
          · have hc := hnear ζ (by linarith) hle
            have hre := Work.Fatou.abs_re_sub_le hc
            simp only [Complex.add_re, Complex.ofReal_re] at hre
            linarith [(abs_le.mp hre).1]
          · rw [Work.Fatou.devH_of_ge_fifteen (le_of_lt hgt)]
            simp only [Complex.add_re, Complex.ofReal_re]
            linarith
        rwa [hζ'] at hb'
      linarith
    refine ⟨ζ, ?_, ?_, hζ'⟩
    · -- `0 ≤ Re ζ`: otherwise `devH ζ = x₀ + ζ` has real part `< x₀ ≤ Re s`
      by_contra hcon
      have hle : ζ.re ≤ 1 / 8 := by linarith [not_le.mp hcon]
      have hexact : Work.Fatou.devH x₀ F ζ = (x₀ : ℂ) + ζ :=
        Work.Fatou.devH_of_le_one_eighth hle
      have : s.re = x₀ + ζ.re := by
        rw [← hζ', hexact]; simp only [Complex.add_re, Complex.ofReal_re]
      linarith [hs.2.1]
    · -- `Re ζ < 1`: otherwise `devH ζ = F (x₀+ζ-1)` exhibits a `Qreg`-preimage with
      -- real part `≥ x₀`, contradicting the fundamental-strip property of `s`
      by_contra hcon
      have hge : (7 / 8 : ℝ) ≤ ζ.re := by linarith [le_of_not_gt hcon]
      have hv : (x₀ : ℂ) + ζ - 1 ∈ Qreg b₁ b₂ := hvQ ζ (by linarith) (by linarith)
      have hdev : Work.Fatou.devH x₀ F ζ = F ((x₀ : ℂ) + ζ - 1) :=
        Work.Fatou.devH_of_ge hge (by linarith)
      have hpre : ((x₀ : ℂ) + ζ - 1).re < x₀ := hs.2.2 _ hv (hdev ▸ hζ')
      have hre : ((x₀ : ℂ) + ζ - 1).re = x₀ + ζ.re - 1 := by simp
      rw [hre] at hpre; linarith
  · -- the values of `devH` on the unit strip lie in `Qreg`
    exact hmemQ

end

end Work.Fatou.Surface
