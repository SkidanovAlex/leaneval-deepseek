import Mathlib
import Submission.Work.Noncompact.ProperLine.flatManifold

/-!
# Gluing two smooth arcs of a manifold at a common point, when both are flat there

Main result: `contMDiffAt_glue_flat`.  Given two `C^∞` arcs `A B : ℝ → M` of a smooth manifold
meeting at `τ` (`A τ = B τ = q`), whose chart expressions at `q` are *flat* at `τ` on `(-∞,τ]`
resp. `[τ,∞)` (all one-sided derivatives of order `≥ 1` vanish), the glued map
`t ↦ if t ≤ τ then A t else B t` is `C^∞` at `τ`.

The proof proceeds at finite order `m` first:

* `exists_contDiff_localization_flat` localises the `C^{m+1}` germ of the chart expression to a
  globally `C^{m+1}` function, preserving the one-sided derivatives at `τ`;
* `contDiffAt_flatGlue_finite` is the finite-order flat gluing of two such functions;
* `contMDiffAt_iff_target` reduces the manifold statement to the corresponding statement for the
  chart expression, and `contMDiffAt_infty` assembles the finite orders.
-/

open Set Filter Topology
open scoped Manifold ContDiff

namespace Work.Noncompact.ProperLine

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Localisation of a `C^k` germ at a point.**  If `f` is `C^k` on a ball around `t₀`, then there
is a globally `C^k` function `g` agreeing with `f` near `t₀`.  Moreover the one-sided iterated
derivatives of `g` at `t₀` agree with those of `f`: this uses no smoothness at all, only that
`iteratedDerivWithin` is determined by the germ. -/
theorem exists_contDiff_localization_flat {f : ℝ → F} {t₀ δ : ℝ} {k : ℕ} (hδ : 0 < δ)
    (hf : ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞) f (Metric.ball t₀ δ)) :
    ∃ g : ℝ → F, ContDiff ℝ ((k : ℕ) : WithTop ℕ∞) g ∧ g =ᶠ[nhds t₀] f ∧
      (∀ j : ℕ, 0 < j → iteratedDerivWithin j g (Set.Iic t₀) t₀
        = iteratedDerivWithin j f (Set.Iic t₀) t₀) ∧
      (∀ j : ℕ, 0 < j → iteratedDerivWithin j g (Set.Ici t₀) t₀
        = iteratedDerivWithin j f (Set.Ici t₀) t₀) := by
  set χ : ℝ → ℝ :=
    fun s => Real.smoothTransition (2 - 4 * s / δ) * Real.smoothTransition (2 + 4 * s / δ)
    with hχdef
  have hχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := by
    rw [hχdef]
    exact ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp
        (by fun_prop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun s : ℝ => 2 - 4 * s / δ)).mul
      ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp
        (by fun_prop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun s : ℝ => 2 + 4 * s / δ))
  have hχnn : ∀ s, 0 ≤ χ s := fun s => by
    rw [hχdef]
    exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  have hχle : ∀ s, χ s ≤ 1 := fun s => by
    rw [hχdef]
    calc Real.smoothTransition (2 - 4 * s / δ) * Real.smoothTransition (2 + 4 * s / δ)
        ≤ 1 * 1 := mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
            (Real.smoothTransition.nonneg _) zero_le_one
      _ = 1 := by norm_num
  have hχone : ∀ s, |s| ≤ δ / 4 → χ s = 1 := by
    intro s hs
    rw [abs_le] at hs
    have h1 : 4 * s / δ ≤ 1 := by rw [div_le_one hδ]; linarith [hs.2]
    have h2 : -(1 : ℝ) ≤ 4 * s / δ := by rw [le_div_iff₀ hδ]; linarith [hs.1]
    rw [hχdef]
    change Real.smoothTransition (2 - 4 * s / δ) * Real.smoothTransition (2 + 4 * s / δ) = 1
    rw [Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ 2 - 4 * s / δ),
      Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ 2 + 4 * s / δ), mul_one]
  have hχzero : ∀ s, δ / 2 ≤ |s| → χ s = 0 := by
    intro s hs
    rw [hχdef]
    change Real.smoothTransition (2 - 4 * s / δ) * Real.smoothTransition (2 + 4 * s / δ) = 0
    by_cases h : 0 ≤ s
    · rw [abs_of_nonneg h] at hs
      have h5 : (2 : ℝ) ≤ 4 * s / δ := by rw [le_div_iff₀ hδ]; linarith [hs]
      rw [Real.smoothTransition.zero_of_nonpos (by linarith : 2 - 4 * s / δ ≤ 0), zero_mul]
    · rw [abs_of_neg (not_le.mp h)] at hs
      have h5 : 4 * s / δ ≤ -(2 : ℝ) := by rw [div_le_iff₀ hδ]; linarith [hs]
      rw [Real.smoothTransition.zero_of_nonpos (by linarith : 2 + 4 * s / δ ≤ 0), mul_zero]
  have hφid : ∀ s : ℝ, |s - t₀| ≤ δ / 4 → t₀ + (s - t₀) * χ (s - t₀) = s := by
    intro s hs
    rw [hχone (s - t₀) hs]
    ring
  have hφbound : ∀ s : ℝ, |(t₀ + (s - t₀) * χ (s - t₀)) - t₀| < δ := by
    intro s
    rw [show t₀ + (s - t₀) * χ (s - t₀) - t₀ = (s - t₀) * χ (s - t₀) by ring, abs_mul]
    rcases lt_or_ge |s - t₀| δ with h | h
    · calc |s - t₀| * |χ (s - t₀)| ≤ |s - t₀| * 1 :=
            mul_le_mul_of_nonneg_left
              (by rw [abs_of_nonneg (hχnn (s - t₀))]; exact hχle (s - t₀))
              (abs_nonneg (s - t₀))
        _ = |s - t₀| := by ring
        _ < δ := h
    · rw [hχzero (s - t₀) (by linarith), abs_zero, mul_zero]
      exact hδ
  have hge : (f ∘ fun s : ℝ => t₀ + (s - t₀) * χ (s - t₀)) =ᶠ[nhds t₀] f := by
    filter_upwards [Metric.ball_mem_nhds t₀ (by positivity : (0:ℝ) < δ / 4)] with s hs
    rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] at hs
    exact congrArg f (hφid s (le_of_lt hs))
  refine ⟨f ∘ (fun s : ℝ => t₀ + (s - t₀) * χ (s - t₀)), ?_, hge, ?_, ?_⟩
  · have hχsmk : ContDiff ℝ ((k : ℕ) : WithTop ℕ∞) χ :=
      hχsm.of_le (WithTop.coe_le_coe.mpr le_top)
    have hφsm : ContDiff ℝ ((k : ℕ) : WithTop ℕ∞)
        (fun s : ℝ => t₀ + (s - t₀) * χ (s - t₀)) := by
      simpa using contDiff_const.add ((contDiff_id.sub contDiff_const).mul
        (hχsmk.comp (contDiff_id.sub contDiff_const)))
    exact hf.comp_contDiff hφsm (fun s => hφbound s)
  · intro j _
    exact (hge.filter_mono nhdsWithin_le_nhds).iteratedDerivWithin_eq_of_nhds_insert j
  · intro j _
    exact (hge.filter_mono nhdsWithin_le_nhds).iteratedDerivWithin_eq_of_nhds_insert j

/-- The derivative of a flat glue at the junction is zero, under minimal differentiability
hypotheses (only first order differentiability on each side is used). -/
theorem hasDerivAt_flatGlue_zero' {U V : ℝ → F} {t₀ : ℝ}
    (hU : DifferentiableWithinAt ℝ U (Set.Iic t₀) t₀)
    (hV : DifferentiableWithinAt ℝ V (Set.Ici t₀) t₀) (h0 : U t₀ = V t₀)
    (hUd : derivWithin U (Set.Iic t₀) t₀ = 0) (hVd : derivWithin V (Set.Ici t₀) t₀ = 0) :
    HasDerivAt (flatGlue U V t₀) 0 t₀ := by
  have hUd' : HasDerivWithinAt U (0 : F) (Set.Iic t₀) t₀ := by
    simpa [hUd] using hU.hasDerivWithinAt
  have hVd' : HasDerivWithinAt V (0 : F) (Set.Ici t₀) t₀ := by
    simpa [hVd] using hV.hasDerivWithinAt
  have hleft : Tendsto (slope U t₀) (𝓝[<] t₀) (𝓝 (0 : F)) := by
    have h := (hasDerivWithinAt_iff_tendsto_slope).mp hUd'
    have h2 : (Set.Iic t₀ \ {t₀}) = Set.Iio t₀ := by
      ext t; simp only [Set.mem_sdiff, Set.mem_Iic, Set.mem_singleton_iff, Set.mem_Iio]
      constructor
      · rintro ⟨h1, h2⟩; exact lt_of_le_of_ne h1 h2
      · intro h1; exact ⟨le_of_lt h1, ne_of_lt h1⟩
    rw [h2] at h
    exact h
  have hright : Tendsto (slope V t₀) (𝓝[>] t₀) (𝓝 (0 : F)) := by
    have h := (hasDerivWithinAt_iff_tendsto_slope).mp hVd'
    have h2 : (Set.Ici t₀ \ {t₀}) = Set.Ioi t₀ := by
      ext t; simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
      constructor
      · rintro ⟨h1, h2⟩; exact lt_of_le_of_ne h1 (Ne.symm h2)
      · intro h1; exact ⟨le_of_lt h1, ne_of_gt h1⟩
    rw [h2] at h
    exact h
  rw [hasDerivAt_iff_tendsto_slope, ← nhdsLT_sup_nhdsGT]
  refine tendsto_sup.mpr ⟨?_, ?_⟩
  · refine hleft.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    have ht' : t < t₀ := ht
    unfold slope
    simp only [vsub_eq_sub, flatGlue_of_le (le_of_lt ht'), flatGlue_self h0]
  · refine hright.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    have ht' : t₀ < t := ht
    unfold slope
    simp only [vsub_eq_sub, flatGlue_of_gt ht', flatGlue_self h0, h0]

/-- **Finite-order flat gluing.**  If `U` is `C^{m+1}` on `(-∞,t₀]` and `V` is `C^{m+1}` on
`[t₀,∞)`, if they agree at `t₀`, and if all one-sided derivatives of order `1..m` of both vanish
at `t₀`, then the glued function is `C^m` at `t₀`. -/
theorem contDiffAt_flatGlue_finite :
    ∀ (m : ℕ) {U V : ℝ → F} {t₀ : ℝ},
    ContDiffOn ℝ (((m : ℕ) : WithTop ℕ∞) + 1) U (Set.Iic t₀) →
    ContDiffOn ℝ (((m : ℕ) : WithTop ℕ∞) + 1) V (Set.Ici t₀) → U t₀ = V t₀ →
    (∀ k : ℕ, 0 < k → k ≤ m → iteratedDerivWithin k U (Set.Iic t₀) t₀ = 0) →
    (∀ k : ℕ, 0 < k → k ≤ m → iteratedDerivWithin k V (Set.Ici t₀) t₀ = 0) →
    ContDiffAt ℝ ((m : ℕ) : WithTop ℕ∞) (flatGlue U V t₀) t₀ := by
  intro m
  induction m with
  | zero =>
    intro U V t₀ hU hV h0 hUf hVf
    have h1 : ContinuousOn (flatGlue U V t₀) (Set.Iic t₀) :=
      hU.continuousOn.congr (fun x hx => flatGlue_of_le hx)
    have h2 : ContinuousOn (flatGlue U V t₀) (Set.Ici t₀) :=
      hV.continuousOn.congr (fun x hx => flatGlue_of_ge h0 hx)
    have h3 : Continuous (flatGlue U V t₀) := by
      have h := h1.union_of_isClosed h2 isClosed_Iic isClosed_Ici
      rw [Set.Iic_union_Ici, continuousOn_univ] at h
      exact h
    rw [show ((0 : ℕ) : WithTop ℕ∞) = 0 from by simp, contDiffAt_zero]
    exact ⟨Set.univ, Filter.univ_mem, continuousOn_univ.mpr h3⟩
  | succ m ih =>
    intro U V t₀ hU hV h0 hUf hVf
    have hle : (((m : ℕ) : WithTop ℕ∞) + 1) + 1 ≤ ((((Nat.succ m : ℕ)) : WithTop ℕ∞)) + 1 := by
      norm_num
    have hne : ((((Nat.succ m : ℕ)) : WithTop ℕ∞)) + 1 ≠ 0 := by norm_num
    set U' : ℝ → F := derivWithin U (Set.Iic t₀) with hU'def
    set V' : ℝ → F := derivWithin V (Set.Ici t₀) with hV'def
    have hU'c : ContDiffOn ℝ (((m : ℕ) : WithTop ℕ∞) + 1) U' (Set.Iic t₀) := by
      simpa [hU'def] using hU.derivWithin (uniqueDiffOn_Iic t₀) hle
    have hV'c : ContDiffOn ℝ (((m : ℕ) : WithTop ℕ∞) + 1) V' (Set.Ici t₀) := by
      simpa [hV'def] using hV.derivWithin (uniqueDiffOn_Ici t₀) hle
    have hderivU : derivWithin U (Set.Iic t₀) t₀ = 0 := by
      simpa [iteratedDerivWithin_one] using hUf 1 one_pos (Nat.succ_pos m)
    have hderivV : derivWithin V (Set.Ici t₀) t₀ = 0 := by
      simpa [iteratedDerivWithin_one] using hVf 1 one_pos (Nat.succ_pos m)
    have h0' : U' t₀ = V' t₀ := by simp only [hU'def, hV'def, hderivU, hderivV]
    have hU'f : ∀ k : ℕ, 0 < k → k ≤ m → iteratedDerivWithin k U' (Set.Iic t₀) t₀ = 0 := by
      intro k _ hk
      rw [hU'def, iteratedDerivWithin_derivWithin k U (Set.Iic t₀)]
      exact hUf (k + 1) (Nat.succ_pos k) (by omega)
    have hV'f : ∀ k : ℕ, 0 < k → k ≤ m → iteratedDerivWithin k V' (Set.Ici t₀) t₀ = 0 := by
      intro k _ hk
      rw [hV'def, iteratedDerivWithin_derivWithin k V (Set.Ici t₀)]
      exact hVf (k + 1) (Nat.succ_pos k) (by omega)
    have hih : ContDiffAt ℝ ((m : ℕ) : WithTop ℕ∞) (flatGlue U' V' t₀) t₀ :=
      ih hU'c hV'c h0' hU'f hV'f
    have hderiv : ∀ s : ℝ, HasFDerivAt (flatGlue U V t₀)
        (ContinuousLinearMap.toSpanSingleton ℝ (flatGlue U' V' t₀ s)) s := by
      intro s
      rcases lt_trichotomy s t₀ with h | h | h
      · have hmem : Set.Iic t₀ ∈ 𝓝 s :=
          Filter.mem_of_superset (isOpen_Iio.mem_nhds h)
            (fun x hx => Set.mem_Iic.mpr (le_of_lt hx))
        have hdiff : DifferentiableAt ℝ U s :=
          (hU.differentiableOn hne).differentiableAt hmem
        have hder : HasDerivAt U (derivWithin U (Set.Iic t₀) s) s := by
          simpa [derivWithin_of_mem_nhds hmem] using hdiff.hasDerivAt
        have hF := hder.hasFDerivAt
        have hev : flatGlue U V t₀ =ᶠ[𝓝 s] U := by
          filter_upwards [isOpen_Iio.mem_nhds h] with t ht
          exact flatGlue_of_le (le_of_lt ht)
        simpa [hU'def, flatGlue_of_le (le_of_lt h)] using hF.congr_of_eventuallyEq hev
      · rw [h]
        have hUw : DifferentiableWithinAt ℝ U (Set.Iic t₀) t₀ :=
          (hU.differentiableOn hne) t₀ (Set.mem_Iic.mpr le_rfl)
        have hVw : DifferentiableWithinAt ℝ V (Set.Ici t₀) t₀ :=
          (hV.differentiableOn hne) t₀ (Set.mem_Ici.mpr le_rfl)
        have hF := (hasDerivAt_flatGlue_zero' hUw hVw h0 hderivU hderivV).hasFDerivAt
        simpa [hU'def, flatGlue_of_le le_rfl, hderivU] using hF
      · have hmem : Set.Ici t₀ ∈ 𝓝 s :=
          Filter.mem_of_superset (isOpen_Ioi.mem_nhds h)
            (fun x hx => Set.mem_Ici.mpr (le_of_lt hx))
        have hdiff : DifferentiableAt ℝ V s :=
          (hV.differentiableOn hne).differentiableAt hmem
        have hder : HasDerivAt V (derivWithin V (Set.Ici t₀) s) s := by
          simpa [derivWithin_of_mem_nhds hmem] using hdiff.hasDerivAt
        have hF := hder.hasFDerivAt
        have hev : flatGlue U V t₀ =ᶠ[𝓝 s] V := by
          filter_upwards [isOpen_Ioi.mem_nhds h] with t ht
          exact flatGlue_of_gt ht
        simpa [hV'def, flatGlue_of_gt h, h0] using hF.congr_of_eventuallyEq hev
    have key : ContDiffAt ℝ (((m : ℕ) : WithTop ℕ∞) + 1) (flatGlue U V t₀) t₀ := by
      rw [contDiffAt_succ_iff_hasFDerivAt]
      refine ⟨fun s => ContinuousLinearMap.toSpanSingleton ℝ (flatGlue U' V' t₀ s),
        ⟨Set.univ, Filter.univ_mem, fun s _ => hderiv s⟩, ?_⟩
      have hphi : ContDiff ℝ ∞ (fun x : F => (toSpanSingletonCLM x : ℝ →L[ℝ] F)) := by
        simpa using (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
          (toSpanSingletonCLM : F →L[ℝ] (ℝ →L[ℝ] F)))
      have hcomp : ContDiffAt ℝ ((m : ℕ) : WithTop ℕ∞)
          (fun s => ContinuousLinearMap.toSpanSingleton ℝ (flatGlue U' V' t₀ s)) t₀ := by
        have h1 := (hphi.contDiffAt (x := flatGlue U' V' t₀ t₀)).of_le (coe_nat_le_inf_withTop m)
        have h3 := h1.comp t₀ hih
        simpa [Function.comp_def, toSpanSingletonCLM_apply] using h3
      exact hcomp
    exact key

/-- **Gluing two smooth arcs of a manifold that are flat at the junction.**

Let `A B : ℝ → M` be `C^∞` maps into a `C^∞` manifold `M` with `A τ = B τ = q`, and suppose that
the chart expression of `A` at `q` has all one-sided derivatives of positive order vanishing at
`τ` on `(-∞,τ]`, and likewise for `B` on `[τ,∞)`.  Then the glued map
`t ↦ if t ≤ τ then A t else B t` is `C^∞` at `τ`. -/
theorem contMDiffAt_glue_flat {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] {A B : ℝ → M} {τ : ℝ} {q : M}
    (hA : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hB : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) B)
    (hAτ : A τ = q) (hBτ : B τ = q)
    (hAf : ∀ k : ℕ, 0 < k → iteratedDerivWithin k
      (fun t => extChartAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) q (A t))
      (Set.Iic τ) τ = 0)
    (hBf : ∀ k : ℕ, 0 < k → iteratedDerivWithin k
      (fun t => extChartAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) q (B t))
      (Set.Ici τ) τ = 0) :
    ContMDiffAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t => if t ≤ τ then A t else B t) τ := by
  set G : ℝ → M := fun t : ℝ => if t ≤ τ then A t else B t with hG
  have hGτ : G τ = q := by
    rw [hG]
    simp only [if_pos le_rfl]
    exact hAτ
  have hcont : ContinuousAt G τ := by
    rw [hG]
    have hgf : (fun t : ℝ => if t ≤ τ then A t else B t) τ = q := by
      simp only [if_pos le_rfl]
      exact hAτ
    change Tendsto (fun t : ℝ => if t ≤ τ then A t else B t) (𝓝 τ)
      (𝓝 ((fun t : ℝ => if t ≤ τ then A t else B t) τ))
    rw [hgf]
    have hleft : Tendsto (fun t : ℝ => if t ≤ τ then A t else B t) (𝓝[≤] τ) (𝓝 q) := by
      have h1 : Tendsto A (𝓝[≤] τ) (𝓝 q) := by
        rw [← hAτ]
        exact hA.continuous.continuousAt.mono_left (nhdsWithin_le_nhds : 𝓝[≤] τ ≤ 𝓝 τ)
      have h2 : A =ᶠ[𝓝[≤] τ] (fun t : ℝ => if t ≤ τ then A t else B t) :=
        eventually_mem_nhdsWithin.mono (fun t ht => by
          show A t = (if t ≤ τ then A t else B t)
          rw [if_pos (Set.mem_Iic.mp ht)])
      exact Filter.Tendsto.congr' h2 h1
    have hright : Tendsto (fun t : ℝ => if t ≤ τ then A t else B t) (𝓝[≥] τ) (𝓝 q) := by
      have h1 : Tendsto B (𝓝[≥] τ) (𝓝 q) := by
        rw [← hBτ]
        exact hB.continuous.continuousAt.mono_left (nhdsWithin_le_nhds : 𝓝[≥] τ ≤ 𝓝 τ)
      have h2 : B =ᶠ[𝓝[≥] τ] (fun t : ℝ => if t ≤ τ then A t else B t) :=
        eventually_mem_nhdsWithin.mono (fun t ht => by
          rcases eq_or_lt_of_le (Set.mem_Ici.mp ht) with h | h
          · rw [show t = τ from h.symm]
            show B τ = (if τ ≤ τ then A τ else B τ)
            rw [if_pos le_rfl]
            exact hBτ.trans hAτ.symm
          · show B t = (if t ≤ τ then A t else B t)
            rw [if_neg (not_le.mpr h)])
      exact Filter.Tendsto.congr' h2 h1
    rw [← nhdsLE_sup_nhdsGE]
    exact tendsto_sup.mpr ⟨hleft, hright⟩
  rw [contMDiffAt_iff_target]
  refine ⟨hcont, ?_⟩
  rw [hGτ]
  let e : M → EuclideanSpace ℝ (Fin n) :=
    extChartAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) q
  rw [contMDiffAt_infty]
  intro m
  rw [contMDiffAt_iff_contDiffAt]
  -- the chart expression of `A` is `C^{m+1}` at `τ`
  have hAe : ContDiffAt ℝ (((m + 1 : ℕ)) : WithTop ℕ∞) (fun s => e (A s)) τ := by
    have h1 : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) e (A τ) := by
      rw [hAτ]
      exact contMDiffAt_extChartAt
    have h2 : ContMDiffAt (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s => e (A s)) τ :=
      ContMDiffAt.comp τ h1 hA.contMDiffAt
    exact (contDiffAt_infty.mp h2.contDiffAt) (m + 1)
  have hBe : ContDiffAt ℝ (((m + 1 : ℕ)) : WithTop ℕ∞) (fun s => e (B s)) τ := by
    have h1 : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) e (B τ) := by
      rw [hBτ]
      exact contMDiffAt_extChartAt
    have h2 : ContMDiffAt (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s => e (B s)) τ :=
      ContMDiffAt.comp τ h1 hB.contMDiffAt
    exact (contDiffAt_infty.mp h2.contDiffAt) (m + 1)
  -- upgrade to `C^{m+1}` on a ball around `τ`
  obtain ⟨u, hu, hfu⟩ := hAe.contDiffOn le_rfl (fun h => by simp at h)
  obtain ⟨δ₁, hδ₁pos, hδ₁sub⟩ := Metric.mem_nhds_iff.mp hu
  obtain ⟨u', hu', hfu'⟩ := hBe.contDiffOn le_rfl (fun h => by simp at h)
  obtain ⟨δ₂, hδ₂pos, hδ₂sub⟩ := Metric.mem_nhds_iff.mp hu'
  have hf : ContDiffOn ℝ (((m + 1 : ℕ)) : WithTop ℕ∞) (fun s => e (A s))
      (Metric.ball τ (min δ₁ δ₂)) :=
    hfu.mono (fun x hx => hδ₁sub (Metric.ball_subset_ball (min_le_left _ _) hx))
  have hg : ContDiffOn ℝ (((m + 1 : ℕ)) : WithTop ℕ∞) (fun s => e (B s))
      (Metric.ball τ (min δ₁ δ₂)) :=
    hfu'.mono (fun x hx => hδ₂sub (Metric.ball_subset_ball (min_le_right _ _) hx))
  have hδpos : 0 < min δ₁ δ₂ := lt_min hδ₁pos hδ₂pos
  -- localise both germs to globally `C^{m+1}` functions
  obtain ⟨U, hUsm, hUeq, hUIic, hUIci⟩ :=
    exists_contDiff_localization_flat (f := fun s => e (A s)) hδpos hf
  obtain ⟨V, hVsm, hVeq, hVIic, hVIci⟩ :=
    exists_contDiff_localization_flat (f := fun s => e (B s)) hδpos hg
  have h0UV : U τ = V τ := by
    have h1 := hUeq.eq_of_nhds
    have h2 := hVeq.eq_of_nhds
    simp only [h1, h2, hAτ, hBτ]
  have hglue : ContDiffAt ℝ ((m : ℕ) : WithTop ℕ∞) (flatGlue U V τ) τ :=
    contDiffAt_flatGlue_finite m hUsm.contDiffOn hVsm.contDiffOn h0UV
      (fun k hk _ => by rw [hUIic k hk]; exact hAf k hk)
      (fun k hk _ => by rw [hVIci k hk]; exact hBf k hk)
  have hUVeq : flatGlue U V τ =ᶠ[𝓝 τ]
      (fun t => if t ≤ τ then e (A t) else e (B t)) := by
    filter_upwards [hUeq, hVeq] with t hUt hVt
    by_cases h : t ≤ τ
    · rw [flatGlue_of_le h, hUt, if_pos h]
    · rw [flatGlue_of_gt (not_le.mp h), hVt, if_neg h]
  have hglue2 : ContDiffAt ℝ ((m : ℕ) : WithTop ℕ∞)
      (fun t => if t ≤ τ then e (A t) else e (B t)) τ :=
    hglue.congr_of_eventuallyEq hUVeq.symm
  refine hglue2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  simp only [Function.comp_apply]
  show e (G t) = (if t ≤ τ then e (A t) else e (B t))
  rw [hG]
  by_cases h : t ≤ τ <;> simp [h]

end Work.Noncompact.ProperLine
