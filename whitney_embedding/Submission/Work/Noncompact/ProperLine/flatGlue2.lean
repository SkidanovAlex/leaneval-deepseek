import Mathlib
import Submission.Work.Noncompact.ProperLine.flatGlue

open Set Filter Asymptotics
open scoped Topology ContDiff

set_option maxHeartbeats 1000000

namespace Work.Noncompact.ProperLine

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The function obtained by gluing `U` on `(-∞, t₀]` to `V` on `[t₀, ∞)`. -/
noncomputable def flatGlue (U V : ℝ → F) (t₀ : ℝ) : ℝ → F := fun t => if t ≤ t₀ then U t else V t

theorem flatGlue_of_le {U V : ℝ → F} {t₀ t : ℝ} (h : t ≤ t₀) :
    flatGlue U V t₀ t = U t := if_pos h

theorem flatGlue_of_gt {U V : ℝ → F} {t₀ t : ℝ} (h : t₀ < t) :
    flatGlue U V t₀ t = V t := if_neg (not_le.mpr h)

theorem flatGlue_self {U V : ℝ → F} {t₀ : ℝ} (h0 : U t₀ = V t₀) :
    flatGlue U V t₀ t₀ = U t₀ := flatGlue_of_le le_rfl

theorem flatGlue_of_ge {U V : ℝ → F} {t₀ t : ℝ} (h0 : U t₀ = V t₀) (ht : t₀ ≤ t) :
    flatGlue U V t₀ t = V t := by
  rcases eq_or_lt_of_le ht with h | h
  · subst h; rw [flatGlue_self h0, h0]
  · exact flatGlue_of_gt h

/-- Continuity at the junction. -/
theorem continuousAt_flatGlue {U V : ℝ → F} {t₀ : ℝ}
    (hU : ContinuousOn U (Set.Iic t₀)) (hV : ContinuousOn V (Set.Ici t₀)) (h0 : U t₀ = V t₀) :
    ContinuousAt (flatGlue U V t₀) t₀ := by
  have hleft : Tendsto (flatGlue U V t₀) (𝓝[≤] t₀) (𝓝 (flatGlue U V t₀ t₀)) := by
    have h1 : Tendsto U (𝓝[≤] t₀) (𝓝 (U t₀)) :=
      hU.continuousWithinAt (Set.mem_Iic.mpr le_rfl)
    have h2 : flatGlue U V t₀ =ᶠ[𝓝[≤] t₀] U :=
      eventually_mem_nhdsWithin.mono (fun t ht => flatGlue_of_le (Set.mem_Iic.mp ht))
    rw [flatGlue_self h0]
    exact h1.congr' h2.symm
  have hright : Tendsto (flatGlue U V t₀) (𝓝[≥] t₀) (𝓝 (flatGlue U V t₀ t₀)) := by
    have h1 : Tendsto V (𝓝[≥] t₀) (𝓝 (V t₀)) :=
      hV.continuousWithinAt (Set.mem_Ici.mpr le_rfl)
    have h2 : flatGlue U V t₀ =ᶠ[𝓝[≥] t₀] V :=
      eventually_mem_nhdsWithin.mono (fun t ht => flatGlue_of_ge h0 (Set.mem_Ici.mp ht))
    rw [flatGlue_self h0, h0]
    exact h1.congr' h2.symm
  have hsup : Tendsto (flatGlue U V t₀) (𝓝[≤] t₀ ⊔ 𝓝[≥] t₀) (𝓝 (flatGlue U V t₀ t₀)) :=
    tendsto_sup.mpr ⟨hleft, hright⟩
  rwa [nhdsLE_sup_nhdsGE] at hsup

/-- The derivative of the glued function at the junction is `0`. -/
theorem hasDerivAt_flatGlue_zero {U V : ℝ → F} {t₀ : ℝ}
    (hU : ContDiffOn ℝ ∞ U (Set.Iic t₀)) (hV : ContDiffOn ℝ ∞ V (Set.Ici t₀))
    (h0 : U t₀ = V t₀)
    (hUd : derivWithin U (Set.Iic t₀) t₀ = 0) (hVd : derivWithin V (Set.Ici t₀) t₀ = 0) :
    HasDerivAt (flatGlue U V t₀) 0 t₀ := by
  have hUd' : HasDerivWithinAt U (0 : F) (Set.Iic t₀) t₀ := by
    have hd := (hU.contDiffWithinAt (Set.mem_Iic.mpr le_rfl)).differentiableWithinAt (by simp)
    simpa [hUd] using hd.hasDerivWithinAt
  have hVd' : HasDerivWithinAt V (0 : F) (Set.Ici t₀) t₀ := by
    have hd := (hV.contDiffWithinAt (Set.mem_Ici.mpr le_rfl)).differentiableWithinAt (by simp)
    simpa [hVd] using hd.hasDerivWithinAt
  have hleft : Tendsto (slope U t₀) (𝓝[<] t₀) (𝓝 (0 : F)) := by
    have h := (hasDerivWithinAt_iff_tendsto_slope).mp hUd'
    have h2 : (Set.Iic t₀ \ {t₀}) = Set.Iio t₀ := by
      ext t; simp only [Set.mem_diff, Set.mem_Iic, Set.mem_singleton_iff, Set.mem_Iio]
      constructor
      · rintro ⟨h1, h2⟩; exact lt_of_le_of_ne h1 h2
      · intro h1; exact ⟨le_of_lt h1, ne_of_lt h1⟩
    rw [h2] at h
    exact h
  have hright : Tendsto (slope V t₀) (𝓝[>] t₀) (𝓝 (0 : F)) := by
    have h := (hasDerivWithinAt_iff_tendsto_slope).mp hVd'
    have h2 : (Set.Ici t₀ \ {t₀}) = Set.Ioi t₀ := by
      ext t; simp only [Set.mem_diff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
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

theorem coe_nat_le_inf_withTop (n : ℕ) : ((n : ℕ∞) : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

theorem top_add_one_le_withTop : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := le_of_eq (by
  rw [← WithTop.coe_one (α := ℕ∞), ← WithTop.coe_add (a := (⊤ : ℕ∞)) (b := (1 : ℕ∞))]
  congr 1)

/-- The continuous linear map `x ↦ (c ↦ c • x)`, as a linear map. -/
noncomputable def toSpanSingletonLinearMap : F →ₗ[ℝ] (ℝ →L[ℝ] F) where
  toFun := fun x => ContinuousLinearMap.toSpanSingleton ℝ x
  map_add' := by
    intro x y
    ext c
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_add]
  map_smul' := by
    intro c x
    ext d
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.toSpanSingleton_apply]
    simp

/-- The continuous linear map `x ↦ (c ↦ c • x)`. -/
noncomputable def toSpanSingletonCLM : F →L[ℝ] (ℝ →L[ℝ] F) :=
  LinearMap.mkContinuous toSpanSingletonLinearMap 1 fun x => by
    rw [one_mul]
    exact le_of_eq (ContinuousLinearMap.norm_toSpanSingleton x)

theorem toSpanSingletonCLM_apply (x : F) :
    toSpanSingletonCLM x = ContinuousLinearMap.toSpanSingleton ℝ x := rfl

theorem iteratedDerivWithin_derivWithin (k : ℕ) (U : ℝ → F) (s : Set ℝ) :
    iteratedDerivWithin k (derivWithin U s) s = iteratedDerivWithin (k + 1) U s := by
  induction k with
  | zero => simp [iteratedDerivWithin_zero, iteratedDerivWithin_one]
  | succ k ih =>
    rw [iteratedDerivWithin_succ (n := k) (f := derivWithin U s), ih,
      iteratedDerivWithin_succ (n := k + 1) (f := U)]

/-- **Flat gluing.** If `U` is `C^∞` on `(-∞, t₀]` and `V` is `C^∞` on `[t₀, ∞)`, they agree
at `t₀`, and all the one-sided derivatives of order `≥ 1` of both vanish at `t₀`, then the glued
function is `C^n` at `t₀` for every `n`. -/
theorem contDiffAt_flatGlue_nat : ∀ (n : ℕ) {U V : ℝ → F} {t₀ : ℝ},
    ContDiffOn ℝ ∞ U (Set.Iic t₀) → ContDiffOn ℝ ∞ V (Set.Ici t₀) → U t₀ = V t₀ →
    (∀ k : ℕ, 0 < k → iteratedDerivWithin k U (Set.Iic t₀) t₀ = 0) →
    (∀ k : ℕ, 0 < k → iteratedDerivWithin k V (Set.Ici t₀) t₀ = 0) →
    ContDiffAt ℝ (n : WithTop ℕ∞) (flatGlue U V t₀) t₀ := by
  intro n
  induction n with
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
  | succ n ih =>
    intro U V t₀ hU hV h0 hUf hVf
    set U' : ℝ → F := derivWithin U (Set.Iic t₀) with hU'def
    set V' : ℝ → F := derivWithin V (Set.Ici t₀) with hV'def
    have hU'c : ContDiffOn ℝ ∞ U' (Set.Iic t₀) := by
      simpa [hU'def] using hU.derivWithin (uniqueDiffOn_Iic t₀) (top_add_one_le_withTop)
    have hV'c : ContDiffOn ℝ ∞ V' (Set.Ici t₀) := by
      simpa [hV'def] using hV.derivWithin (uniqueDiffOn_Ici t₀) (top_add_one_le_withTop)
    have hderivU : derivWithin U (Set.Iic t₀) t₀ = 0 := by
      simpa [iteratedDerivWithin_one] using hUf 1 one_pos
    have hderivV : derivWithin V (Set.Ici t₀) t₀ = 0 := by
      simpa [iteratedDerivWithin_one] using hVf 1 one_pos
    have h0' : U' t₀ = V' t₀ := by
      rw [hU'def, hV'def, hderivU, hderivV]
    have hU'f : ∀ k : ℕ, 0 < k → iteratedDerivWithin k U' (Set.Iic t₀) t₀ = 0 := by
      intro k _
      rw [hU'def, iteratedDerivWithin_derivWithin k U (Set.Iic t₀)]
      exact hUf (k + 1) (Nat.succ_pos k)
    have hV'f : ∀ k : ℕ, 0 < k → iteratedDerivWithin k V' (Set.Ici t₀) t₀ = 0 := by
      intro k _
      rw [hV'def, iteratedDerivWithin_derivWithin k V (Set.Ici t₀)]
      exact hVf (k + 1) (Nat.succ_pos k)
    have hderiv : ∀ s : ℝ, HasFDerivAt (flatGlue U V t₀)
        (ContinuousLinearMap.toSpanSingleton ℝ (flatGlue U' V' t₀ s)) s := by
      intro s
      rcases lt_trichotomy s t₀ with h | h | h
      · have hmem : Set.Iic t₀ ∈ 𝓝 s :=
          Filter.mem_of_superset (isOpen_Iio.mem_nhds h) (fun x hx => Set.mem_Iic.mpr (le_of_lt hx))
        have hdiff : DifferentiableAt ℝ U s :=
          (hU.differentiableOn (by simp)).differentiableAt hmem
        have hder : HasDerivAt U (derivWithin U (Set.Iic t₀) s) s := by
          simpa [derivWithin_of_mem_nhds hmem] using hdiff.hasDerivAt
        have hF := hder.hasFDerivAt
        have hev : flatGlue U V t₀ =ᶠ[𝓝 s] U := by
          filter_upwards [isOpen_Iio.mem_nhds h] with t ht
          exact flatGlue_of_le (le_of_lt ht)
        simpa [hU'def, flatGlue_of_le (le_of_lt h)] using hF.congr_of_eventuallyEq hev
      · subst h
        have hF := (hasDerivAt_flatGlue_zero hU hV h0 hderivU hderivV).hasFDerivAt
        simpa [hU'def, flatGlue_of_le le_rfl, hderivU] using hF
      · have hmem : Set.Ici t₀ ∈ 𝓝 s :=
          Filter.mem_of_superset (isOpen_Ioi.mem_nhds h) (fun x hx => Set.mem_Ici.mpr (le_of_lt hx))
        have hdiff : DifferentiableAt ℝ V s :=
          (hV.differentiableOn (by simp)).differentiableAt hmem
        have hder : HasDerivAt V (derivWithin V (Set.Ici t₀) s) s := by
          simpa [derivWithin_of_mem_nhds hmem] using hdiff.hasDerivAt
        have hF := hder.hasFDerivAt
        have hev : flatGlue U V t₀ =ᶠ[𝓝 s] V := by
          filter_upwards [isOpen_Ioi.mem_nhds h] with t ht
          exact flatGlue_of_gt ht
        simpa [hV'def, flatGlue_of_gt h, h0] using hF.congr_of_eventuallyEq hev
    have key : ContDiffAt ℝ (((n : ℕ) : WithTop ℕ∞) + 1) (flatGlue U V t₀) t₀ := by
      rw [contDiffAt_succ_iff_hasFDerivAt]
      refine ⟨fun s => ContinuousLinearMap.toSpanSingleton ℝ (flatGlue U' V' t₀ s),
        ⟨Set.univ, Filter.univ_mem, fun s _ => hderiv s⟩, ?_⟩
      have hphi : ContDiff ℝ ∞ (fun x : F => (toSpanSingletonCLM x : ℝ →L[ℝ] F)) := by
        simpa using (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
          (toSpanSingletonCLM : F →L[ℝ] (ℝ →L[ℝ] F)))
      have hcomp : ContDiffAt ℝ (((n : ℕ) : ℕ∞) : WithTop ℕ∞)
          (fun s => ContinuousLinearMap.toSpanSingleton ℝ (flatGlue U' V' t₀ s)) t₀ := by
        have h1 := (hphi.contDiffAt (x := flatGlue U' V' t₀ t₀)).of_le (coe_nat_le_inf_withTop n)
        have h2 : ContDiffAt ℝ (((n : ℕ) : ℕ∞) : WithTop ℕ∞) (flatGlue U' V' t₀) t₀ :=
          ih hU'c hV'c h0' hU'f hV'f
        have h3 := h1.comp t₀ h2
        simpa [Function.comp_def, toSpanSingletonCLM_apply] using h3
      exact hcomp
    convert key using 1
    simp [Nat.cast_add, Nat.cast_one]

/-- **The `C^∞` (top-level) form of the flat gluing.**

`contDiffAt_flatGlue_nat` produces only the *natural* levels `ContDiffAt ℝ (↑n)`; the manifold
arguments in this development live at the top level `((⊤ : ℕ∞) : WithTop ℕ∞)`, and definitional
equality does not bridge `↑n` and `⊤`.  Here the top level is obtained from the global
`contDiff_all_iff_nat` instantiated at `⊤`: away from the junction the glued function is
*eventually equal* to `U` resp. `V`, and at the junction `contDiffAt_flatGlue_nat` applies. -/
theorem contDiffAt_flatGlue_top {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U V : ℝ → F} {t₀ : ℝ}
    (hU : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (h0 : U t₀ = V t₀)
    (hUf : ∀ k : ℕ, 0 < k → iteratedDerivWithin k U (Set.Iic t₀) t₀ = 0)
    (hVf : ∀ k : ℕ, 0 < k → iteratedDerivWithin k V (Set.Ici t₀) t₀ = 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (flatGlue U V t₀) t₀ := by
  have hall : ∀ n : ℕ, ContDiff ℝ (↑n : WithTop ℕ∞) (flatGlue U V t₀) := by
    intro n
    rw [contDiff_iff_contDiffAt]
    intro x
    have hle : ((n : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
      WithTop.coe_le_coe.mpr le_top
    rcases lt_trichotomy x t₀ with h | h | h
    · refine (((hU.contDiffAt (x := x)).of_le hle)).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Iio.mem_nhds h] with y hy
      exact flatGlue_of_le (le_of_lt hy)
    · subst h
      exact contDiffAt_flatGlue_nat n hU.contDiffOn hV.contDiffOn h0 hUf hVf
    · refine (((hV.contDiffAt (x := x)).of_le hle)).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Ioi.mem_nhds h] with y hy
      exact flatGlue_of_gt hy
  exact ((contDiff_all_iff_nat.mpr hall) ⊤).contDiffAt

end Work.Noncompact.ProperLine
