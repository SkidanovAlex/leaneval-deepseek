import Mathlib
import Submission.Work.LayerCont.KaxisLowBound
import Submission.Work.LayerCont.TruncDominator
import Submission.Work.LayerCont.LowCoinc

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

namespace Work.LayerCont

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

/-- The low part of the layer with a **free split point** `p`: `sinSqC r · ∫_0^p K^{(d)}(τ,it)e^{-πr²t}dt`
(an interval integral, so the definition is uniform in the sign of `p`). -/
def layerLowAt (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (p r : ℝ) (τ : UpperHalfPlane) : ℂ :=
  Work.Asymptotics.sinSqC r * ∫ t in (0 : ℝ)..p,
    Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * Work.Asymptotics.gaussWeight r t

/-- The truncated part of the layer with a free split point `p`: the integral from `p` to `∞` of the
cusp-subtracted kernel. -/
def layerTruncAt (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (ℓ : Work.Kernels.LogLambdaData)
    (d : ℕ) (p r : ℝ) (τ : UpperHalfPlane) : ℂ :=
  Work.Asymptotics.sinSqC r * ∫ t in Set.Ici p,
    (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp G τ t)
      * Work.Asymptotics.gaussWeight r t

/-- The `high` (closed-form) part of the layer with a free split point `p`: the paper's `highPart`
corrected by the explicit integral of `Aexp` between `1` and `p` (a signed interval integral).
With this correction `layerLowAt + layerTruncAt + highPartAt` is **independent of `p`**. -/
def highPartAt (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (p r : ℝ) (τ : UpperHalfPlane) : ℂ :=
  Work.Asymptotics.highPart G τ r
    - Work.Asymptotics.sinSqC r * ∫ t in (1 : ℝ)..p,
        Work.Asymptotics.Aexp G τ t * Work.Asymptotics.gaussWeight r t

/-- **The CKMRV layer with a free split point.**  `layerAt G ℓ d 1 r τ = paperLayer G ℓ d τ r`. -/
def layerAt (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (p r : ℝ) (τ : UpperHalfPlane) : ℂ :=
  layerLowAt ℓ d p r τ + layerTruncAt G ℓ d p r τ + highPartAt G p r τ

/-- Boundedness of the kernel on `(0,p]` (`p > 0`) given cleanliness there: the cusp bound near
`t = 0` plus `GapBoundKaxisLow` on the compact remainder. -/
theorem KaxisBoundedIocBall (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) {p : ℝ} (hp : 0 < p)
    (hclean : ∀ (t : ℝ) (ht : 0 < t), t ∈ Set.Ioc (0 : ℝ) p →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ioc (0 : ℝ) p,
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C := by
  obtain ⟨δc, hδcpos, hcusp⟩ :=
    Work.Asymptotics.HalfFunnel.Kaxis_cusp_of_bounded ℓ d hd
      (K := {τ}) isCompact_singleton.isBounded
  obtain ⟨c, hcpos, hcb⟩ := hcusp 0 le_rfl
  set δ : ℝ := min δc (p / 2) with hδdef
  have hδpos : 0 < δ := lt_min hδcpos (by linarith)
  have hδδc : δ ≤ δc := min_le_left _ _
  have hδp : δ ≤ p := by have := min_le_right δc (p / 2); linarith
  obtain ⟨C₂, hC₂nn, hC₂b⟩ := GapBoundKaxisLow ℓ d hd (K := {τ}) isCompact_singleton
    (δ := δ) (T := p) hδpos
    (fun w hw t ht htI => by
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      exact hclean t ht ⟨lt_of_lt_of_le hδpos htI.1, htI.2⟩)
  refine ⟨max c C₂, le_trans hcpos.le (le_max_left c C₂), fun t ht => ?_⟩
  by_cases htδ : t ≤ δ
  · have : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ c := by
      simpa using hcb τ t (Set.mem_singleton τ) ht.1 (le_trans htδ hδδc)
    exact le_trans this (le_max_left c C₂)
  · exact le_trans (hC₂b τ t (Set.mem_singleton τ) ⟨le_of_lt (lt_of_not_ge htδ), ht.2⟩)
      (le_max_right c C₂)

/-- **The layer is independent of the split point.**

For `p ≥ 1`, provided the contour integrand `K^{(d)}(τ,·)e^{-πr²t}` is bounded on `(0,p]`
(cleanliness) and the cusp-subtracted integrand is integrable on `[1,∞)` (which holds for `τ ∈ 𝒟`
by the cusp expansion), the `low + trunc + high` decomposition with split point `p` reproduces the
paper's `F₂`:

  `layerAt G ℓ d p r τ = paperLayer G ℓ d τ r`.

This is what allows the continuation to *move the split point* (the `p`-independence of the layer,
used at heights `Im τ ≈ 1` where neither `s₀ + A < 1` nor `1 < s₀ - A` can hold). -/
theorem layerAt_eq_paperLayer (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) {p r : ℝ} (hp1 : 1 ≤ p)
    (τ : UpperHalfPlane)
    (hclean : ∀ (t : ℝ) (ht : 0 < t), t ∈ Set.Ioc (0 : ℝ) p →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))
    (hIntTail : IntegrableOn (fun t => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      - Work.Asymptotics.Aexp G τ t) * Work.Asymptotics.gaussWeight r t) (Set.Ici (1 : ℝ))) :
    layerAt G ℓ d p r τ = Work.Asymptotics.paperLayer G ℓ d τ r := by
  classical
  set Kf : ℝ → ℂ := fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
    * Work.Asymptotics.gaussWeight r t with hKf
  set Af : ℝ → ℂ := fun t => Work.Asymptotics.Aexp G τ t
    * Work.Asymptotics.gaussWeight r t with hAf
  set Gf : ℝ → ℂ := fun t => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
    - Work.Asymptotics.Aexp G τ t) * Work.Asymptotics.gaussWeight r t with hGf
  have hIntG : IntegrableOn Gf (Set.Ici (1 : ℝ)) := by rw [hGf]; exact hIntTail
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp1
  -- boundedness of the kernel on `(0,p]`
  obtain ⟨C, hCnn, hCb⟩ := KaxisBoundedIocBall ℓ d hd τ hp0 hclean
  have hKmeas : Measurable Kf := by
    rw [hKf]
    exact (Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).mul
      (by unfold Work.Asymptotics.gaussWeight; fun_prop)
  have hAcont : Continuous Af := by
    rw [hAf]
    simp only [Work.Asymptotics.Aexp, Work.Asymptotics.gaussWeight]
    fun_prop
  -- integrability on the three pieces
  have hIntK : IntegrableOn Kf (Set.Ioc (0 : ℝ) p) := by
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) p)) :=
      ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]
          exact ENNReal.ofReal_lt_top⟩
    refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => C)
      (MeasureTheory.integrable_const C) hKmeas.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    rw [hKf, norm_mul]
    calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
          * ‖Work.Asymptotics.gaussWeight r t‖
        ≤ C * 1 := mul_le_mul (hCb t ht) (norm_gaussWeight_le_one r t (le_of_lt ht.1))
          (norm_nonneg _) hCnn
      _ = C := mul_one _
  have hIntK01 : IntegrableOn Kf (Set.Ioc (0 : ℝ) 1) :=
    hIntK.mono_set (fun x hx => ⟨hx.1, le_trans hx.2 hp1⟩)
  have hIntK1p : IntegrableOn Kf (Set.Ioc (1 : ℝ) p) :=
    hIntK.mono_set (fun x hx => ⟨lt_of_lt_of_le zero_lt_one (le_of_lt hx.1), hx.2⟩)
  have hIntA1p : IntegrableOn Af (Set.Ioc (1 : ℝ) p) :=
    (hAcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hGf_eq : Gf = fun t => Kf t - Af t := by
    funext t
    rw [hGf, hKf, hAf]
    ring
  have hIntGp : IntegrableOn Gf (Set.Ici p) :=
    hIntG.mono_set (fun x hx => le_trans hp1 hx)
  have hIntG1p : IntegrableOn Gf (Set.Ioc (1 : ℝ) p) := by
    rw [hGf_eq]
    exact hIntK1p.sub hIntA1p
  -- (1) the low split
  have hlowSplit : ∫ t in (0 : ℝ)..p, Kf t
      = (∫ t in (0 : ℝ)..1, Kf t) + ∫ t in (1 : ℝ)..p, Kf t := by
    rw [intervalIntegral.integral_of_le (le_trans zero_le_one hp1),
      intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_of_le hp1,
      ← Set.Ioc_union_Ioc_eq_Ioc (zero_le_one : (0 : ℝ) ≤ 1) hp1]
    exact setIntegral_union
      (Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx2.1 (not_lt.mpr hx1.2)))
      measurableSet_Ioc hIntK01 hIntK1p
  -- (2) the trunc split
  have hIntGIcc : IntegrableOn Gf (Set.Icc (1 : ℝ) p) :=
    hIntG1p.congr_set_ae (Ioc_ae_eq_Icc (μ := volume) (a := (1 : ℝ)) (b := p)).symm
  have hIntGIoi : IntegrableOn Gf (Set.Ioi p) :=
    hIntG.mono_set (fun x hx => le_trans hp1 (le_of_lt hx))
  have htruncSplit : ∫ t in Set.Ici (1 : ℝ), Gf t
      = (∫ t in Set.Ici p, Gf t) + ∫ t in Set.Ioc (1 : ℝ) p, Gf t := by
    have h1 : ∫ t in Set.Ici (1 : ℝ), Gf t
        = (∫ t in Set.Icc (1 : ℝ) p, Gf t) + ∫ t in Set.Ioi p, Gf t := by
      have hunion : Set.Ici (1 : ℝ) = Set.Icc (1 : ℝ) p ∪ Set.Ioi p := by
        ext x
        constructor
        · intro hx
          by_cases h : x ≤ p
          · exact Or.inl ⟨hx, h⟩
          · exact Or.inr (lt_of_not_ge h)
        · rintro (h | h)
          · exact h.1
          · exact le_trans hp1 (le_of_lt h)
      rw [hunion]
      exact setIntegral_union
        (Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx2 (not_lt.mpr hx1.2)))
        measurableSet_Ioi hIntGIcc hIntGIoi
    have h2 : ∫ t in Set.Icc (1 : ℝ) p, Gf t = ∫ t in Set.Ioc (1 : ℝ) p, Gf t :=
      setIntegral_congr_set (Ioc_ae_eq_Icc (μ := volume) (a := (1 : ℝ)) (b := p)).symm
    have h3 : ∫ t in Set.Ioi p, Gf t = ∫ t in Set.Ici p, Gf t :=
      setIntegral_congr_set (Ioi_ae_eq_Ici' (by simp : volume ({(p : ℝ)} : Set ℝ) = 0))
    rw [h1, h2, h3, add_comm]
  have htruncSplit' : ∫ t in Set.Ici p, Gf t
      = (∫ t in Set.Ici (1 : ℝ), Gf t) - ∫ t in Set.Ioc (1 : ℝ) p, Gf t :=
    eq_sub_iff_add_eq.mpr htruncSplit.symm
  -- (3) the `Aexp` part on `(1,p]`
  have hsub1p : ∫ t in Set.Ioc (1 : ℝ) p, Gf t
      = (∫ t in Set.Ioc (1 : ℝ) p, Kf t) - ∫ t in Set.Ioc (1 : ℝ) p, Af t := by
    rw [hGf_eq]
    exact integral_sub hIntK1p hIntA1p
  have hAf1p : (∫ t in (1 : ℝ)..p, Af t) = ∫ t in Set.Ioc (1 : ℝ) p, Af t :=
    intervalIntegral.integral_of_le hp1
  -- the key arithmetic identity
  have hmain : (∫ t in (0 : ℝ)..p, Kf t) - (∫ t in Set.Ioc (1 : ℝ) p, Af t)
        + (∫ t in Set.Ici p, Gf t)
      = (∫ t in (0 : ℝ)..1, Kf t) + ∫ t in Set.Ici (1 : ℝ), Gf t := by
    rw [hlowSplit, htruncSplit', hsub1p, intervalIntegral.integral_of_le hp1]
    ring
  have hgoal : Work.Asymptotics.sinSqC r * (∫ t in (0 : ℝ)..p, Kf t)
        + Work.Asymptotics.sinSqC r * (∫ t in Set.Ici p, Gf t)
        + (Work.Asymptotics.highPart G τ r
            - Work.Asymptotics.sinSqC r * ∫ t in (1 : ℝ)..p, Af t)
      = Work.Asymptotics.sinSqC r * (∫ t in (0 : ℝ)..1, Kf t)
        + Work.Asymptotics.sinSqC r * (∫ t in Set.Ici (1 : ℝ), Gf t)
        + Work.Asymptotics.highPart G τ r := by
    rw [hAf1p]
    linear_combination Work.Asymptotics.sinSqC r * hmain
  rw [layerAt, layerLowAt, layerTruncAt, highPartAt, Work.Asymptotics.paperLayer,
    Work.Asymptotics.layerLow, Work.Asymptotics.layerTrunc]
  exact hgoal

end Work.LayerCont
