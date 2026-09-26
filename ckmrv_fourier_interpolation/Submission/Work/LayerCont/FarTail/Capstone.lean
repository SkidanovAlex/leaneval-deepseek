/-
# The far-side window chart of the CKMRV layer and the first recurrence

This is the capstone of `Work.LayerCont.FarTail`: for every height `s₀ > 1` there are parameters
`A₁, ξ₁, A₂, ξ₂, p, ε'` such that the window chart

  `windowChart ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r = layerLowDouble + layerTruncAt + highPartAt`

is holomorphic on `B(1 + i s₀, ε')` for every `r`, agrees with the paper's layer `paperLayer` on
the `𝒟`-side of that ball, agrees with `paperLayer + sinSqC r · resCorr r` on its far side
(`1 < Re τ`), and satisfies the **first recurrence**

  `T2op (windowChart · r) τ = -T2op (gaussTerm · r) τ`

for every `τ` whose three translates `τ, τ+1, τ+2` lie in the ball with `τ, τ+1` on the
`𝒟`-side (so that `τ+2` is on the far side, where the recurrence picks up the residue correction
`resCorr`).

The hypotheses are exactly the data of `Work.LayerCont.ECS.exists_contour_left_data` together with
the three far-side inputs established in this area:

* the far-side cleanliness of the contour from the web
  (`Work.LayerCont.FarTail.clean_axis_of_web_re_gt_one`),
* the far-side `j'`-non-degeneracy of the translate pole
  (`Work.LayerCont.FarTail.jprime_ne_zero_far`),
* the location of the removable coincidence inside the swept rectangle
  (`Work.LayerCont.FarTail.coinc_mem_openLeftRect_far`),
* the far-side tail integrability (`Work.LayerCont.FarTail.tail_integrableOn_of_clean`),

the `ε'` being chosen small enough for all of them (a factor `4` below the `4ε`-bounds of the
contour data).
-/
import Mathlib
import Submission.Work.LayerCont.FarTail.Defs
import Submission.Work.LayerCont.FarTail.Clean
import Submission.Work.LayerCont.FarTail.CuspFar
import Submission.Work.LayerCont.FarTail.CoincFar
import Submission.Work.LayerCont.FarTail.FarGeom
import Submission.Work.LayerCont.FarTail.FarIdentity
import Submission.Work.LayerCont.WindowCapstone
import Submission.Work.LayerCont.LayerT2

set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

noncomputable section

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

namespace Work.LayerCont.FarTail

open Work.Asymptotics Work.LayerCont

/-- **The far-side window chart of the CKMRV layer.**

For every `s₀ > 1` there is a chart with all three properties on a ball `B(1 + i s₀, ε')`: it is
holomorphic, it agrees with `paperLayer` on the `𝒟`-side, and it agrees with
`paperLayer + sinSqC r · resCorr r` on the far side. -/
theorem far_identity_data (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {s₀ : ℝ} (hs₀ : 0 < s₀) (hs₀1 : 1 < s₀) :
    ∃ A₁ ξ₁ A₂ ξ₂ p : ℝ, 0 < A₁ ∧ 0 < ξ₁ ∧ 0 < A₂ ∧ 0 < ξ₂ ∧ 1 ≤ p ∧
      ∃ ε' : ℝ, 0 < ε' ∧
        (∀ r : ℝ, MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
          (fun τ : UpperHalfPlane => windowChart ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r τ)
          (Metric.ball (Work.Asymptotics.onePlusI s₀ hs₀) ε')) ∧
        (∀ (τ : UpperHalfPlane) (r : ℝ), dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε' →
          τ.re < 1 → τ ∈ Work.Asymptotics.DomainD →
            windowChart ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r τ
              = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r) ∧
        (∀ (τ : UpperHalfPlane) (r : ℝ), dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε' →
          1 < τ.re →
            windowChart ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r τ
              = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r
                + Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r τ) ∧
        (∀ (τ : UpperHalfPlane) (r : ℝ), dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε' →
          dist ((1 : ℝ) +ᵥ τ) (Work.Asymptotics.onePlusI s₀ hs₀) < ε' →
          dist ((2 : ℝ) +ᵥ τ) (Work.Asymptotics.onePlusI s₀ hs₀) < ε' →
          τ.re < 1 → ((1 : ℝ) +ᵥ τ).re < 1 →
          τ ∈ Work.Asymptotics.DomainD → ((1 : ℝ) +ᵥ τ) ∈ Work.Asymptotics.DomainD →
            Work.Kernels.T2op (fun σ : UpperHalfPlane =>
              windowChart ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r σ) τ
              = -Work.Kernels.T2op (fun σ : UpperHalfPlane => Work.Kernels.gaussTerm σ r) τ) := by
  obtain ⟨ε, hεpos, A₁, ξ₁, A₂, ξ₂, hA₁, hξ₁, hA₂, hξ₂, hA₁s, hξ₁1, hA₂inv, h4sεA, h4sεξ,
    hsep1, hsep2, hclean0, hedge₀, hclass, hA₂bd, hξ₂bd, hA₂q, hξ₂q, hε4, hεa₁, hεa₂,
    rw₀, hrw₀pos, hεw, hweb⟩ := Work.LayerCont.ECS.exists_contour_left_data s₀ hs₀
  have hs₀ne : s₀ ≠ 1 := by linarith
  have hA₂pos : 0 < A₂ := (hsep2 hs₀ne).1
  have hξ₂pos : 0 < ξ₂ := (hsep2 hs₀ne).2.1
  have h4ε : 4 * ε ≤ A₂ * s₀ := (hsep2 hs₀ne).2.2.1
  have hsep0 : A₁ + A₂ < |s₀ - s₀⁻¹| := (hsep2 hs₀ne).2.2.2.2
  have habs : |s₀ - s₀⁻¹| = s₀ - s₀⁻¹ := by
    rw [abs_of_pos]
    nlinarith [hs₀1, inv_pos.mpr hs₀, mul_inv_cancel₀ (ne_of_gt hs₀)]
  rw [habs] at hsep0
  have hsA₁ : 0 < s₀ - A₁ := by linarith
  have hsep : s₀⁻¹ + A₂ < s₀ - A₁ := by linarith
  -- ### the working radius
  obtain ⟨ε₁, hε₁pos, hdeg₀⟩ := Work.Asymptotics.jprime_tauSubOne_ne_zero s₀ hs₀
  obtain ⟨ε₂, hε₂pos, hdeg₂⟩ := jprime_ne_zero_far hs₀ hs₀1
  set εb : ℝ := min (min (min (min ε (1 / 32)) ε₁) ε₂) (min (A₂ * s₀ / 16) (ξ₂ * s₀ / 16))
    with hεbdef
  have hεbpos : 0 < εb := by
    rw [hεbdef]
    exact lt_min (lt_min (lt_min (lt_min hεpos (by norm_num)) hε₁pos) hε₂pos)
      (lt_min (by positivity) (by positivity))
  have hch1 : εb ≤ min (min (min ε (1 / 32)) ε₁) ε₂ := min_le_left _ _
  have hch2 : εb ≤ min (min ε (1 / 32)) ε₁ := le_trans hch1 (min_le_left _ _)
  have hch3 : εb ≤ min ε (1 / 32) := le_trans hch2 (min_le_left _ _)
  have hεbε : εb ≤ ε := le_trans hch3 (min_le_left _ _)
  have hεb32 : εb ≤ 1 / 32 := le_trans hch3 (min_le_right _ _)
  have hεbε₁ : εb ≤ ε₁ := le_trans hch2 (min_le_right _ _)
  have hεbε₂ : εb ≤ ε₂ := le_trans hch1 (min_le_right _ _)
  have hch4 : εb ≤ min (A₂ * s₀ / 16) (ξ₂ * s₀ / 16) := min_le_right _ _
  have hεbA₂ : εb ≤ A₂ * s₀ / 16 := le_trans hch4 (min_le_left _ _)
  have hεbξ₂ : εb ≤ ξ₂ * s₀ / 16 := le_trans hch4 (min_le_right _ _)
  have hεb16 : εb ≤ 1 / 16 := by linarith
  have hεb1 : εb ≤ 1 := by linarith
  have hεbw : εb ≤ rw₀ := le_trans hεbε hεw
  have h16εbA : 16 * εb ≤ A₂ * s₀ := by linarith
  have h16εbξ : 16 * εb ≤ ξ₂ * s₀ := by linarith
  have h4εbA : 4 * εb ≤ A₂ * s₀ := by linarith
  have h4εbξ : 4 * εb ≤ ξ₂ * s₀ := by linarith
  have h4sεbA : 4 * s₀ * εb ≤ A₁ := by
    have h := mul_le_mul_of_nonneg_left hεbε (by positivity : (0 : ℝ) ≤ 4 * s₀)
    linarith [h4sεA, h]
  have h4sεbξ : 4 * s₀ * εb ≤ ξ₁ := by
    have h := mul_le_mul_of_nonneg_left hεbε (by positivity : (0 : ℝ) ≤ 4 * s₀)
    linarith [h4sεξ, h]
  -- ### the split point and the chart ball
  set p : ℝ := max (s₀ + A₁) ((s₀ - A₁)⁻¹) + 1 with hpdef
  have hp1 : 1 ≤ p := by
    have h0 : (0 : ℝ) ≤ s₀ + A₁ := by linarith
    have h1 : (0 : ℝ) ≤ max (s₀ + A₁) ((s₀ - A₁)⁻¹) := le_trans h0 (le_max_left _ _)
    rw [hpdef]; linarith
  have hp_hi : s₀ + A₁ ≤ p := by
    have h := le_max_left (s₀ + A₁) ((s₀ - A₁)⁻¹)
    rw [hpdef]; linarith
  have hp_ge : max (s₀ + A₁) ((s₀ - A₁)⁻¹) + 1 ≤ p := le_of_eq hpdef.symm
  -- ### the three cleanliness families
  have hcleanTail : ∀ (s : ℝ) (hs : 0 < s), p ≤ s →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs) :=
    clean_axis_tail_of_web hs₀ hA₁s hεbpos hεb16 hεbw h4sεbA hp_ge hweb
  have hcleanAxisLow : ∀ (s : ℝ) (hs : 0 < s),
      s ∈ (Set.Ioc (0 : ℝ) p) \ (Set.Ioo (s₀ - A₁) (s₀ + A₁)
        ∪ Set.Ioo (s₀⁻¹ - A₂) (s₀⁻¹ + A₂)) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs) :=
    fun s hs hsE τ hτ => clean_axis_retained_of_web hs₀ hA₁ hεbpos hεb16 hεbw h4sεbA h4εbA hweb
      s hs (fun hmem => hsE.2 (Or.inl hmem)) (fun hmem => hsE.2 (Or.inr hmem)) τ hτ
  -- ### the edge cleanliness of the two detour rectangles
  have hedge₁ : ∀ (u v : ℝ), 0 < v →
      ((-ξ₁ < u ∧ u < 0 ∧ (v = s₀ - A₁ ∨ v = s₀ + A₁))
        ∨ (u = -ξ₁ ∧ s₀ - A₁ < v ∧ v < s₀ + A₁)) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Asymptotics.ofReImT u v) := by
    intro u v hv hc τ hτ hjeq
    obtain ⟨σ, hσ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hjeq
    have hge : ε ≤ dist (σ • Work.Asymptotics.ofReImT u v) (Work.Asymptotics.onePlusI s₀ hs₀) := by
      refine hedge₀ σ u v hv ?_
      rcases hc with hc | hc
      · exact Or.inl hc
      · exact Or.inr (Or.inl hc)
    rw [hσ] at hge
    exact absurd (lt_of_lt_of_le hτ hεbε) (not_lt.mpr hge)
  have hedge₂ : ∀ (u v : ℝ), 0 < v →
      ((-ξ₂ < u ∧ u < 0 ∧ (v = s₀⁻¹ - A₂ ∨ v = s₀⁻¹ + A₂))
        ∨ (u = -ξ₂ ∧ s₀⁻¹ - A₂ < v ∧ v < s₀⁻¹ + A₂)) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Asymptotics.ofReImT u v) := by
    intro u v hv hc τ hτ hjeq
    obtain ⟨σ, hσ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hjeq
    have hge : ε ≤ dist (σ • Work.Asymptotics.ofReImT u v) (Work.Asymptotics.onePlusI s₀ hs₀) := by
      refine hedge₀ σ u v hv ?_
      rcases hc with hc | hc
      · exact Or.inr (Or.inr (Or.inl hc))
      · exact Or.inr (Or.inr (Or.inr hc))
    rw [hσ] at hge
    exact absurd (lt_of_lt_of_le hτ hεbε) (not_lt.mpr hge)
  -- ### the geometry of the pole `τ - 1` and of the two rectangles on the `𝒟`-side
  have hpole : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
      τ.re < 1 →
      -ξ₁ < (Work.Asymptotics.tauSubOne τ).re ∧ (Work.Asymptotics.tauSubOne τ).re < 0 ∧
        s₀ - A₁ < (Work.Asymptotics.tauSubOne τ).im ∧
        (Work.Asymptotics.tauSubOne τ).im < s₀ + A₁ := by
    intro τ hτ hτre
    obtain ⟨h1, h2⟩ := Work.Asymptotics.abs_re_im_sub_lt hs₀ hεbpos hεb1 hτ
    obtain ⟨h1a, h1b⟩ := abs_lt.mp h1
    obtain ⟨h2a, h2b⟩ := abs_lt.mp h2
    have hre : (Work.Asymptotics.tauSubOne τ).re = τ.re - 1 := Work.LayerCont.tauSubOne_re' τ
    have him : (Work.Asymptotics.tauSubOne τ).im = τ.im := Work.LayerCont.tauSubOne_im' τ
    rw [hre, him]
    have h3 : 3 * s₀ * εb ≤ A₁ := by linarith
    have h4 : 3 * s₀ * εb ≤ ξ₁ := by linarith
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hdeg : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
      τ.re < 1 → Work.Residues.jprime (Work.Asymptotics.tauSubOne τ) ≠ 0 :=
    fun τ hτ hτre => hdeg₀ τ (lt_of_lt_of_le hτ hεbε₁) hτre
  have hcl₁ : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
      τ.re < 1 → ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect s₀ A₁ ξ₁ z →
          (z ≠ γ • τ ∨ z = Work.Asymptotics.tauSubOne τ) := by
    intro τ hτ hτre γ z hz
    by_cases h : z = γ • τ
    · right
      rcases hclass τ (lt_of_lt_of_le hτ hεbε) γ z (Or.inl hz) h with h' | h'
      · exact h'
      · exfalso
        have hpos : 0 < (Work.Asymptotics.tauCoinc τ).re :=
          Work.Asymptotics.tauCoinc_re_pos τ hτre
        have hneg : z.re ≤ 0 := hz.2.1
        rw [h'] at hneg
        linarith
    · exact Or.inl h
  have hcl₂ : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
      τ.re < 1 → ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect s₀⁻¹ A₂ ξ₂ z → z ≠ γ • τ := by
    intro τ hτ hτre γ z hz hzeq
    have hτim_lo : s₀ - A₁ < τ.im := by
      have h2lo := (abs_lt.mp
        (Work.Asymptotics.abs_re_im_sub_lt hs₀ hεbpos hεb1 hτ).2).1
      have h3 : 3 * s₀ * εb ≤ A₁ := by linarith
      linarith
    rcases hclass τ (lt_of_lt_of_le hτ hεbε) γ z (Or.inr hz) hzeq with h' | h'
    · have hzim : z.im = τ.im := by rw [h', Work.LayerCont.tauSubOne_im']
      linarith [hz.2.2, hzim]
    · have hpos := Work.Asymptotics.tauCoinc_re_pos τ hτre
      rw [← h'] at hpos
      linarith [hz.2.1]
  -- ### the far-side inputs
  have hcoincFar : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
      1 < τ.re →
        Work.LayerCont.Coinc.coincℂ τ ∈ Work.Asymptotics.openLeftRectℂ s₀⁻¹ A₂ ξ₂ :=
    coinc_mem_openLeftRect_far hs₀ hA₂pos hξ₂pos hεbpos (by linarith) h16εbA h16εbξ
  have hclassb : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        (Work.Asymptotics.leftRect s₀ A₁ ξ₁ z ∨ Work.Asymptotics.leftRect s₀⁻¹ A₂ ξ₂ z) →
          z = γ • τ → z = Work.Asymptotics.tauSubOne τ ∨ z = Work.Asymptotics.tauCoinc τ :=
    fun τ hτ γ z hz hzeq => hclass τ (lt_of_lt_of_le hτ hεbε) γ z hz hzeq
  have horbit := far_orbit_rects hs₀ hsep hclassb hcoincFar
  have hcl₁Far : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
      1 < τ.re → ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect s₀ A₁ ξ₁ z → z ≠ γ • τ := horbit.1
  have hcl₂Far : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
      1 < τ.re → ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect s₀⁻¹ A₂ ξ₂ z →
          (z ≠ γ • τ ∨ z = ModularGroup.S • ((-1 : ℝ) +ᵥ τ)) := horbit.2
  have hdegFar : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
      1 < τ.re → Work.Residues.jprime τ ≠ 0 :=
    fun τ hτ _ => hdeg₂ τ (lt_of_lt_of_le hτ hεbε₂)
  have hcleanFar : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
      1 < τ.re → ∀ (t : ℝ) (ht : 0 < t),
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) :=
    farClean_of_web hs₀ hεbw hweb
  have hIntFar : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
      1 < τ.re → ∀ r : ℝ, MeasureTheory.IntegrableOn (fun t : ℝ =>
        (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
          * Work.Asymptotics.gaussWeight r t) (Set.Ici (1 : ℝ)) :=
    fun τ hτ hτre r =>
      tail_integrableOn_of_clean ℓ d hd (σ := τ) (r := r) (fun t ht => hcleanFar τ hτ hτre t ht)
  refine ⟨A₁, ξ₁, A₂, ξ₂, p, hA₁, hξ₁, hA₂pos, hξ₂pos, hp1, εb, hεbpos, ?_, ?_, ?_, ?_⟩
  · -- ### holomorphy
    intro r
    have h1 : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : UpperHalfPlane => layerLowDouble ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r τ)
        (Metric.ball (Work.Asymptotics.onePlusI s₀ hs₀) εb) :=
      mdifferentiableOn_layerLowDouble ℓ d hd (r := r) hs₀ hA₁ hξ₁ hA₂pos hξ₂pos hεbpos
        hsA₁ hp_hi hsep hA₂inv hedge₁ hedge₂ hcleanAxisLow
    have h2 : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : UpperHalfPlane => layerTruncAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ)
        (Metric.ball (Work.Asymptotics.onePlusI s₀ hs₀) εb) :=
      mdifferentiableOn_layerTruncAt ℓ d hd (p := p) hp1 hs₀ hεbpos r hcleanTail
    have h3 : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : UpperHalfPlane => highPartAt (Work.Asymptotics.Gcusp ℓ d) p r τ)
        (Metric.ball (Work.Asymptotics.onePlusI s₀ hs₀) εb) :=
      (mdifferentiableOn_highPartAt ℓ d hd p r).mono (Set.subset_univ _)
    show MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane => layerLowDouble ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r τ
        + layerTruncAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ
        + highPartAt (Work.Asymptotics.Gcusp ℓ d) p r τ)
      (Metric.ball (Work.Asymptotics.onePlusI s₀ hs₀) εb)
    exact (h1.add h2).add h3
  · -- ### the agreement on the `𝒟`-side
    intro τ r hτ hτre hD
    have hcleanAll : ∀ (t : ℝ) (ht : 0 < t), t ∈ Set.Ioc (0 : ℝ) p →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) :=
      fun t ht _ => clean_axis_of_web_re_lt_one hs₀ hεbw hweb t ht τ hτ hτre
    have hconv : layerLowDouble ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r τ = layerLowAt ℓ d p r τ :=
      layerLowDouble_eq_layerLowAt ℓ d hd (r := r) hs₀ hA₁ hξ₁ hA₂pos hξ₂pos hεbpos hsA₁ hp_hi
        hsep hA₂inv hcl₁ hpole hdeg hcl₂ hτ hτre hcleanAll
    have hIntG := tail_integrableOn_of_mem_DomainD ℓ d hd hD r
    have hpaper : layerAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ
        = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r :=
      layerAt_eq_paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d hd (r := r) hp1 τ
        (fun t ht _ => clean_axis_of_web_re_lt_one hs₀ hεbw hweb t ht τ hτ hτre) hIntG
    rw [windowChart_eq, hconv]
    exact hpaper
  · -- ### the far-side identity
    intro τ r hτ hτre
    exact far_identity ℓ d hd hs₀ hA₁ hξ₁ hA₂pos hξ₂pos hεbpos hp1 hsA₁ hp_hi hsep hA₂inv
      hcl₁Far hcl₂Far hcoincFar hdegFar hcleanFar hIntFar τ r hτ hτre
  · -- ### the first recurrence
    intro τ r hτ hτ1 hτ2 hτre hτ1re hD hD1
    have hτ2re : 1 < ((2 : ℝ) +ᵥ τ).re := by
      rw [UpperHalfPlane.vadd_re]
      linarith [hD.1]
    -- cleanliness at the three points, for `t ∈ (0,1]`
    have hclean3 : ∀ σ ∈ ({τ, (1 : ℝ) +ᵥ τ, (2 : ℝ) +ᵥ τ} : Set UpperHalfPlane),
        ∀ (t : ℝ) (ht : 0 < t), t ∈ Set.Ioc (0 : ℝ) 1 →
          Work.Kernels.jInvariantFun σ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
      intro σ hσ t ht _
      rcases hσ with hσ | hσ | hσ
      · rw [hσ]; exact clean_axis_of_web_re_lt_one hs₀ hεbw hweb t ht τ hτ hτre
      · rw [hσ]
        exact clean_axis_of_web_re_lt_one hs₀ hεbw hweb t ht ((1 : ℝ) +ᵥ τ) hτ1 hτ1re
      · rw [hσ]
        exact clean_axis_of_web_re_gt_one hs₀ hεbw hweb t ht ((2 : ℝ) +ᵥ τ) hτ2 hτ2re
    -- tail integrability at the three points
    have hInt3 : ∀ σ ∈ ({τ, (1 : ℝ) +ᵥ τ, (2 : ℝ) +ᵥ τ} : Set UpperHalfPlane),
        MeasureTheory.IntegrableOn (fun t : ℝ =>
          (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t)
            * Work.Asymptotics.gaussWeight r t) (Set.Ici (1 : ℝ)) := by
      intro σ hσ
      rcases hσ with hσ | hσ | hσ
      · rw [hσ]; exact tail_integrableOn_of_mem_DomainD ℓ d hd hD r
      · rw [hσ]; exact tail_integrableOn_of_mem_DomainD ℓ d hd hD1 r
      · rw [hσ]
        exact tail_integrableOn_of_clean ℓ d hd (σ := (2 : ℝ) +ᵥ τ) (r := r)
          (fun t ht => hcleanFar _ hτ2 hτ2re t ht)
    have hk := T2op_paperLayer ℓ d hd hclean3 hInt3
    have hfar := far_identity ℓ d hd hs₀ hA₁ hξ₁ hA₂pos hξ₂pos hεbpos hp1 hsA₁ hp_hi hsep hA₂inv
      hcl₁Far hcl₂Far hcoincFar hdegFar hcleanFar hIntFar ((2 : ℝ) +ᵥ τ) r hτ2 hτ2re
    have hnear2 : windowChart ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r τ
        = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r := by
      have hconv : layerLowDouble ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r τ = layerLowAt ℓ d p r τ :=
        layerLowDouble_eq_layerLowAt ℓ d hd (r := r) hs₀ hA₁ hξ₁ hA₂pos hξ₂pos hεbpos hsA₁ hp_hi
          hsep hA₂inv hcl₁ hpole hdeg hcl₂ hτ hτre
          (fun t ht _ => clean_axis_of_web_re_lt_one hs₀ hεbw hweb t ht τ hτ hτre)
      have hpaper : layerAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ
          = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r :=
        layerAt_eq_paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d hd (r := r) hp1 τ
          (fun t ht _ => clean_axis_of_web_re_lt_one hs₀ hεbw hweb t ht τ hτ hτre)
          (tail_integrableOn_of_mem_DomainD ℓ d hd hD r)
      rw [windowChart_eq, hconv]
      exact hpaper
    have hnear1 : windowChart ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r ((1 : ℝ) +ᵥ τ)
        = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ τ) r := by
      have hconv : layerLowDouble ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r ((1 : ℝ) +ᵥ τ)
          = layerLowAt ℓ d p r ((1 : ℝ) +ᵥ τ) :=
        layerLowDouble_eq_layerLowAt ℓ d hd (r := r) hs₀ hA₁ hξ₁ hA₂pos hξ₂pos hεbpos hsA₁ hp_hi
          hsep hA₂inv
          (fun σ hσ hσre => hcl₁ σ hσ hσre) (fun σ hσ hσre => hpole σ hσ hσre)
          (fun σ hσ hσre => hdeg σ hσ hσre) (fun σ hσ hσre => hcl₂ σ hσ hσre) hτ1 hτ1re
          (fun t ht _ => clean_axis_of_web_re_lt_one hs₀ hεbw hweb t ht _ hτ1 hτ1re)
      have hpaper : layerAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r ((1 : ℝ) +ᵥ τ)
          = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ τ) r :=
        layerAt_eq_paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d hd (r := r) hp1 _
          (fun t ht _ => clean_axis_of_web_re_lt_one hs₀ hεbw hweb t ht _ hτ1 hτ1re)
          (tail_integrableOn_of_mem_DomainD ℓ d hd hD1 r)
      rw [windowChart_eq, hconv]
      exact hpaper
    exact T2op_of_far_identity ℓ d r τ
      (fun σ : UpperHalfPlane => windowChart ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r σ)
      hfar hnear1 hnear2 hk

/-- **The assembled first recurrence for the far-side window chart.**

For every `s₀ > 1` there are chart parameters on a ball `B(1 + i s₀, ε')` such that the chart is
holomorphic, agrees with `paperLayer` on the `𝒟`-side, agrees with
`paperLayer + sinSqC r · resCorr r` on the far side, and satisfies
`T2op (windowChart · r) τ = -T2op (gaussTerm · r) τ` whenever `τ, τ+1` are on the `𝒟`-side and
`τ+2` (hence automatically on the far side) is in the ball.

This is the `hdef1` half of the socket `Work.Asymptotics.exists_pair_of_propagated_F2`. -/
theorem T2op_layerWindowContinuation (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {s₀ : ℝ} (hs₀ : 0 < s₀) (hs₀1 : 1 < s₀) :
    ∃ A₁ ξ₁ A₂ ξ₂ p : ℝ, 0 < A₁ ∧ 0 < ξ₁ ∧ 0 < A₂ ∧ 0 < ξ₂ ∧ 1 ≤ p ∧
      ∃ ε' : ℝ, 0 < ε' ∧
        (∀ r : ℝ, MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
          (fun τ : UpperHalfPlane => windowChart ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r τ)
          (Metric.ball (Work.Asymptotics.onePlusI s₀ hs₀) ε')) ∧
        (∀ (τ : UpperHalfPlane) (r : ℝ), dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε' →
          τ.re < 1 → τ ∈ Work.Asymptotics.DomainD →
            windowChart ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r τ
              = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r) ∧
        (∀ (τ : UpperHalfPlane) (r : ℝ), dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε' →
          1 < τ.re →
            windowChart ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r τ
              = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r
                + Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r τ) ∧
        (∀ (τ : UpperHalfPlane) (r : ℝ), dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε' →
          dist ((1 : ℝ) +ᵥ τ) (Work.Asymptotics.onePlusI s₀ hs₀) < ε' →
          dist ((2 : ℝ) +ᵥ τ) (Work.Asymptotics.onePlusI s₀ hs₀) < ε' →
          τ.re < 1 → ((1 : ℝ) +ᵥ τ).re < 1 →
          τ ∈ Work.Asymptotics.DomainD → ((1 : ℝ) +ᵥ τ) ∈ Work.Asymptotics.DomainD →
            Work.Kernels.T2op (fun σ : UpperHalfPlane =>
              windowChart ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r σ) τ
              = -Work.Kernels.T2op (fun σ : UpperHalfPlane => Work.Kernels.gaussTerm σ r) τ) :=
  far_identity_data ℓ d hd hs₀ hs₀1

end Work.LayerCont.FarTail
