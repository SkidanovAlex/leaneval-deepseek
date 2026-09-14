import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Commons.Analysis.ODE

open Filter Set
open scoped Topology

section Helpers
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The first coordinate of a curve `z : ℝ → X × X` with derivative `((z t).2, g (z t).1)`
has derivative `(z t).2`. -/
lemma tube_hasDerivAt_fst {z : ℝ → X × X} {g : X → X} {t : ℝ}
    (hz : HasDerivAt z ((z t).2, g (z t).1) t) :
    HasDerivAt (fun s => (z s).1) (z t).2 t := by
  have h : HasDerivAtFilter (fun s => (z s).1) (z t).2 (𝓝 t ×ˢ pure t) := by
    have h := (hz.hasFDerivAtFilter.fst).hasDerivAtFilter
    simpa [ContinuousLinearMap.toSpanSingleton_apply] using h
  exact h

/-- The second coordinate of a curve `z : ℝ → X × X` with derivative `((z t).2, g (z t).1)`
has derivative `g (z t).1`. -/
lemma tube_hasDerivAt_snd {z : ℝ → X × X} {g : X → X} {t : ℝ}
    (hz : HasDerivAt z ((z t).2, g (z t).1) t) :
    HasDerivAt (fun s => (z s).2) (g (z t).1) t := by
  have h : HasDerivAtFilter (fun s => (z s).2) (g (z t).1) (𝓝 t ×ˢ pure t) := by
    have h := (hz.hasFDerivAtFilter.snd).hasDerivAtFilter
    simpa [ContinuousLinearMap.toSpanSingleton_apply] using h
  exact h

/-- **Velocity estimate along a tube.**  If `z = (x, v)` solves `x' = v`, `v' = g x` on `Icc t₁ S`,
if `x` stays in the tube `dist (x s) (s • a) < s ρ` for `s ∈ [t₁, t)` and if on that tube the force
is bounded by `K / s ^ 2`, then `‖v t - a‖ ≤ ‖v t₁ - a‖ + K / t₁ - K / t`.

This is the (fencing-inequality form of the) statement that the velocity can only approach `a`
as fast as `∫ K/s² ds` allows. -/
lemma tube_velocity_bound
    {z : ℝ → X × X} {g : X → X} {a : X} {ρ K t₁ S t : ℝ} (ht₁ : 0 < t₁)
    (hz : ∀ s ∈ Set.Icc t₁ S, HasDerivAt z ((z s).2, g (z s).1) s)
    (htube : ∀ s ∈ Set.Ico t₁ t, dist (z s).1 (s • a) < s * ρ)
    (hb : ∀ s ∈ Set.Icc t₁ S, ∀ y : X, dist y (s • a) ≤ s * ρ → ‖g y‖ ≤ K / s ^ 2)
    (ht : t ∈ Set.Icc t₁ S) :
    ‖(z t).2 - a‖ ≤ ‖(z t₁).2 - a‖ + K / t₁ - K / t := by
  have hzcont : ContinuousOn z (Set.Icc t₁ S) :=
    fun x hx => (hz x hx).continuousAt.continuousWithinAt
  have hcontf : ContinuousOn (fun s => (z s).2 - a) (Set.Icc t₁ t) :=
    (((continuous_snd.comp_continuousOn hzcont).mono (Set.Icc_subset_Icc_right ht.2)).sub
      continuousOn_const)
  have hf' : ∀ x ∈ Set.Ico t₁ t,
      HasDerivWithinAt (fun s => (z s).2 - a) (g (z x).1) (Set.Ici x) x := by
    intro x hx
    exact ((tube_hasDerivAt_snd (hz x ⟨hx.1, le_trans (le_of_lt hx.2) ht.2⟩)).sub_const a).hasDerivWithinAt
  have hBcont : ContinuousOn (fun s : ℝ => ‖(z t₁).2 - a‖ + K / t₁ - K / s) (Set.Icc t₁ t) := by
    have h1 : ContinuousOn (fun s : ℝ => K / s) (Set.Icc t₁ t) := by
      have hinv : ContinuousOn (fun s : ℝ => s⁻¹) (Set.Icc t₁ t) :=
        ContinuousOn.inv₀ continuousOn_id (by intro x hx; exact ne_of_gt (lt_of_lt_of_le ht₁ hx.1))
      simpa [div_eq_mul_inv] using hinv.const_mul K
    exact (continuousOn_const.add continuousOn_const).sub h1
  have hB' : ∀ x ∈ Set.Ico t₁ t,
      HasDerivWithinAt (fun s : ℝ => ‖(z t₁).2 - a‖ + K / t₁ - K / s) (K / x ^ 2)
        (Set.Ici x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le ht₁ hx.1)
    have h2 : HasDerivAt (fun s : ℝ => K / s) (-(K / x^2)) x := by
      have h := (hasDerivAt_inv hx0).const_mul K
      simpa only [div_eq_mul_inv, mul_neg, neg_neg] using h
    have h3 := h2.const_sub ((‖(z t₁).2 - a‖ + K / t₁) : ℝ)
    exact (by simpa using h3 : HasDerivAt (fun s : ℝ => ‖(z t₁).2 - a‖ + K / t₁ - K / s) (K / x^2) x).hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico t₁ t, ‖g (z x).1‖ ≤ K / x ^ 2 := by
    intro x hx
    have hxS : x ∈ Set.Icc t₁ S := ⟨hx.1, le_trans (le_of_lt hx.2) ht.2⟩
    exact hb x hxS (z x).1 (le_of_lt (htube x hx))
  have H := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
      (f := fun s => (z s).2 - a) (f' := fun s => g (z s).1)
      (B := fun s => ‖(z t₁).2 - a‖ + K / t₁ - K / s) (B' := fun s => K / s ^ 2)
      hcontf hf' (by simp) hBcont hB' hbound
  exact H (show t ∈ Set.Icc t₁ t from ⟨ht.1, le_rfl⟩)

/-- **Position estimate along a tube.**  If `z = (x, v)` solves `x' = v`, `v' = g x` on `Icc t₁ S`
and if `‖v s - a‖ ≤ c` for all `s ∈ [t₁, t)`, then
`‖x t - t • a‖ ≤ ‖x t₁ - t₁ • a‖ + c * (t - t₁)`: the distance to the moving ray grows at most
linearly with slope `c`. -/
lemma tube_position_bound
    {z : ℝ → X × X} {g : X → X} {a : X} {c t₁ S t : ℝ}
    (hz : ∀ s ∈ Set.Icc t₁ S, HasDerivAt z ((z s).2, g (z s).1) s)
    (ht : t ∈ Set.Icc t₁ S)
    (hc : ∀ s ∈ Set.Ico t₁ t, ‖(z s).2 - a‖ ≤ c) :
    ‖(z t).1 - t • a‖ ≤ ‖(z t₁).1 - t₁ • a‖ + c * (t - t₁) := by
  have hzcont : ContinuousOn z (Set.Icc t₁ S) :=
    fun x hx => (hz x hx).continuousAt.continuousWithinAt
  have hcontf : ContinuousOn (fun s => (z s).1 - s • a) (Set.Icc t₁ t) :=
    (((continuous_fst.comp_continuousOn hzcont).mono (Set.Icc_subset_Icc_right ht.2)).sub
      (continuousOn_id.smul continuousOn_const))
  have hf' : ∀ x ∈ Set.Ico t₁ t,
      HasDerivWithinAt (fun s => (z s).1 - s • a) ((z x).2 - a) (Set.Ici x) x := by
    intro x hx
    have hd1 : HasDerivAt ((fun s => (z s).1) - (fun y => y • a)) ((z x).2 - a) x := by
      simpa using ((tube_hasDerivAt_fst (hz x ⟨hx.1, le_trans (le_of_lt hx.2) ht.2⟩)).sub
        ((hasDerivAt_id x).smul_const a))
    have hd2 : ((fun s => (z s).1) - (fun y => y • a)) = (fun s => (z s).1 - s • a) := rfl
    rw [hd2] at hd1
    exact hd1.hasDerivWithinAt
  have hBcont : ContinuousOn (fun s : ℝ => ‖(z t₁).1 - t₁ • a‖ + c * (s - t₁)) (Set.Icc t₁ t) := by
    fun_prop
  have hB' : ∀ x ∈ Set.Ico t₁ t,
      HasDerivWithinAt (fun s : ℝ => ‖(z t₁).1 - t₁ • a‖ + c * (s - t₁)) c (Set.Ici x) x := by
    intro x hx
    have h : HasDerivAt (fun s : ℝ => ‖(z t₁).1 - t₁ • a‖ + c * (s - t₁)) c x := by
      have h1 : HasDerivAt (fun s : ℝ => s - t₁) 1 x := (hasDerivAt_id x).sub_const t₁
      simpa using (h1.const_mul c).const_add (‖(z t₁).1 - t₁ • a‖)
    exact h.hasDerivWithinAt
  have H := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
      (f := fun s => (z s).1 - s • a) (f' := fun s => (z s).2 - a)
      (B := fun s => ‖(z t₁).1 - t₁ • a‖ + c * (s - t₁)) (B' := fun _ => c)
      hcontf hf' (by simp) hBcont hB' (fun x hx => hc x hx)
  exact H (show t ∈ Set.Icc t₁ t from ⟨ht.1, le_rfl⟩)

/-- **One step of the tube-invariance argument.**  If `z` stays in the tube
`dist (z s).1 (s • a) < s ρ` for `s ∈ [t₁, t)` and the initial data at `t₁` satisfy the inner
bounds `dist (z t₁).1 (t₁ • a) < t₁ ρ / 3`, `dist (z t₁).2 a < ρ / 3`, `K / t₁ < ρ / 3`, then the
endpoint `t` already satisfies the full tube bounds `dist (z t).1 (t • a) < t ρ`,
`dist (z t).2 a < 2 ρ / 3`. -/
lemma tube_step_Icc
    {z : ℝ → X × X} {g : X → X} {a : X} {ρ K t₁ S t : ℝ}
    (hρ : 0 < ρ) (ht₁ : 0 < t₁) (htK : K / t₁ < ρ / 3)
    (hz : ∀ s ∈ Set.Icc t₁ S, HasDerivAt z ((z s).2, g (z s).1) s)
    (hb : ∀ s ∈ Set.Icc t₁ S, ∀ y : X, dist y (s • a) ≤ s * ρ → ‖g y‖ ≤ K / s ^ 2)
    (hpos : dist (z t₁).1 (t₁ • a) < t₁ * ρ / 3) (hvel : dist (z t₁).2 a < ρ / 3)
    (ht : t ∈ Set.Icc t₁ S)
    (htube : ∀ s ∈ Set.Ico t₁ t, dist (z s).1 (s • a) < s * ρ) :
    dist (z t).1 (t • a) < t * ρ ∧ dist (z t).2 a < 2 * ρ / 3 := by
  have hK : 0 ≤ K := by
    have h1 : ‖g (t₁ • a)‖ ≤ K / t₁ ^ 2 :=
      hb t₁ ⟨le_rfl, le_trans ht.1 ht.2⟩ (t₁ • a) (by rw [dist_self]; positivity)
    have h2 : 0 ≤ K / t₁ ^ 2 := le_trans (norm_nonneg _) h1
    have h3 : (0 : ℝ) < t₁ ^ 2 := by positivity
    have h4 : 0 ≤ K / t₁ ^ 2 * t₁ ^ 2 := mul_nonneg h2 (le_of_lt h3)
    rwa [div_mul_cancel₀ _ (ne_of_gt h3)] at h4
  have hcs : ∀ s ∈ Set.Ico t₁ t, ‖(z s).2 - a‖ ≤ ‖(z t₁).2 - a‖ + K / t₁ := by
    intro s hs
    have hsS : s ∈ Set.Icc t₁ S := ⟨hs.1, le_trans (le_of_lt hs.2) ht.2⟩
    have htube' : ∀ u ∈ Set.Ico t₁ s, dist (z u).1 (u • a) < u * ρ :=
      fun u hu => htube u ⟨hu.1, lt_trans hu.2 hs.2⟩
    have hv := tube_velocity_bound ht₁ hz htube' hb hsS
    have hKs : 0 ≤ K / s := div_nonneg hK (le_of_lt (lt_of_lt_of_le ht₁ hs.1))
    linarith
  have hpb := tube_position_bound hz ht hcs
  have h1 : dist (z t).1 (t • a) < t * ρ := by
    have hdt : dist (z t).1 (t • a) = ‖(z t).1 - t • a‖ := dist_eq_norm _ _
    rw [hdt]
    have hd1 : dist (z t₁).1 (t₁ • a) = ‖(z t₁).1 - t₁ • a‖ := dist_eq_norm _ _
    have hdv : dist (z t₁).2 a = ‖(z t₁).2 - a‖ := dist_eq_norm _ _
    have hc_lt : ‖(z t₁).2 - a‖ + K / t₁ < 2 * ρ / 3 := by linarith
    have htm : 0 ≤ t - t₁ := sub_nonneg.mpr ht.1
    have h2' : (‖(z t₁).2 - a‖ + K / t₁) * (t - t₁) ≤ (2 * ρ / 3) * (t - t₁) :=
      mul_le_mul_of_nonneg_right (le_of_lt hc_lt) htm
    have h3' : t₁ * ρ / 3 + (2 * ρ / 3) * (t - t₁) < t * ρ := by
      nlinarith [ht.1, ht₁, hρ]
    linarith [hpos]
  have h2 : dist (z t).2 a < 2 * ρ / 3 := by
    have hv := tube_velocity_bound ht₁ hz htube hb ht
    have hdt : dist (z t).2 a = ‖(z t).2 - a‖ := dist_eq_norm _ _
    rw [hdt]
    have hdv : dist (z t₁).2 a = ‖(z t₁).2 - a‖ := dist_eq_norm _ _
    have hKs : 0 ≤ K / t := div_nonneg hK (le_of_lt (lt_of_lt_of_le ht₁ ht.1))
    linarith
  exact ⟨h1, h2⟩

end Helpers

/-- **The invariant tube, on a compact time interval.**

Let `z = (x, v)` solve `x' = v`, `v' = g x` on `Icc t₁ S`, and suppose that on the tube
`dist y (t • a) ≤ t ρ` around the ray `t ↦ t • a` the force is bounded by `K / t ^ 2`
(this is the standard situation for a homogeneous potential, where the force decays like `t⁻²`
along the ray).  If `z t₁` lies inside the inner tube
`dist x (t₁ • a) < t₁ ρ / 3`, `dist v a < ρ / 3` and `K / t₁ < ρ / 3`, then `z` stays in the tube
`dist (z t).1 (t • a) < t ρ`, `dist (z t).2 a < 2 ρ / 3` for all `t ∈ Icc t₁ S`. -/
theorem tube_invariant_Icc
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {g : X → X} {a : X} {ρ K t₁ S : ℝ} (hρ : 0 < ρ) (ht₁ : 0 < t₁) (htK : K / t₁ < ρ / 3)
    (hb : ∀ t ∈ Set.Icc t₁ S, ∀ y : X, dist y (t • a) ≤ t * ρ → ‖g y‖ ≤ K / t ^ 2)
    {z : ℝ → X × X}
    (hz : ∀ t ∈ Set.Icc t₁ S, HasDerivAt z ((z t).2, g (z t).1) t)
    (hpos : dist (z t₁).1 (t₁ • a) < t₁ * ρ / 3) (hvel : dist (z t₁).2 a < ρ / 3) :
    ∀ t ∈ Set.Icc t₁ S, dist (z t).1 (t • a) < t * ρ ∧ dist (z t).2 a < 2 * ρ / 3 := by
  intro t ht
  by_contra hcon
  set B : Set ℝ := {u | u ∈ Set.Icc t₁ S ∧
      ¬ (dist (z u).1 (u • a) < u * ρ ∧ dist (z u).2 a < 2 * ρ / 3)} with hB
  have hBne : B.Nonempty := ⟨t, ht, hcon⟩
  have hBdd : BddBelow B := by
    refine ⟨t₁, ?_⟩
    intro u hu
    rw [hB] at hu
    exact hu.1.1
  set τ := sInf B with hτ
  have hτcl : τ ∈ closure B := by rw [hτ]; exact csInf_mem_closure hBne hBdd
  have hsub : B ⊆ Set.Icc t₁ S := by
    intro u hu
    rw [hB] at hu
    exact hu.1
  have hτmem : τ ∈ Set.Icc t₁ S := closure_minimal hsub isClosed_Icc hτcl
  have hPs : ∀ s ∈ Set.Ico t₁ τ,
      dist (z s).1 (s • a) < s * ρ ∧ dist (z s).2 a < 2 * ρ / 3 := by
    intro s hs
    have hsIcc : s ∈ Set.Icc t₁ S := ⟨hs.1, le_trans (le_of_lt hs.2) hτmem.2⟩
    have hsnotB : s ∉ B := by
      intro hsB
      have hle : sInf B ≤ s := csInf_le hBdd hsB
      rw [← hτ] at hle
      linarith [hs.2]
    by_contra hP
    exact hsnotB (by rw [hB]; exact ⟨hsIcc, hP⟩)
  have hPτ : dist (z τ).1 (τ • a) < τ * ρ ∧ dist (z τ).2 a < 2 * ρ / 3 :=
    tube_step_Icc hρ ht₁ htK hz hb hpos hvel hτmem (fun s hs => (hPs s hs).1)
  have hτcont : ContinuousAt z τ := (hz τ hτmem).continuousAt
  have hc1 : ContinuousAt (fun s : ℝ => dist (z s).1 (s • a)) τ :=
    (continuous_fst.continuousAt.comp hτcont).dist
      ((continuous_id.smul continuous_const).continuousAt)
  have hc2 : ContinuousAt (fun s : ℝ => dist (z s).2 a) τ :=
    (continuous_snd.continuousAt.comp hτcont).dist continuousAt_const
  have hnhds1 : ∀ᶠ s in 𝓝 τ, dist (z s).1 (s • a) < s * ρ :=
    hc1.eventually_lt (continuousAt_id.mul continuousAt_const) hPτ.1
  have hnhds2 : ∀ᶠ s in 𝓝 τ, dist (z s).2 a < 2 * ρ / 3 :=
    hc2.eventually_lt continuousAt_const hPτ.2
  have hnhds : ∀ᶠ s in 𝓝 τ,
      (dist (z s).1 (s • a) < s * ρ ∧ dist (z s).2 a < 2 * ρ / 3) := hnhds1.and hnhds2
  obtain ⟨ε, hεpos, hball⟩ :=
    Metric.mem_nhds_iff.mp (show {s : ℝ | dist (z s).1 (s • a) < s * ρ ∧
      dist (z s).2 a < 2 * ρ / 3} ∈ 𝓝 τ from hnhds)
  have hτint : τ ∈ Set.Ioo (τ - ε) (τ + ε) := ⟨by linarith, by linarith⟩
  obtain ⟨b, hbU, hbB⟩ := mem_closure_iff.mp hτcl (Set.Ioo (τ - ε) (τ + ε)) isOpen_Ioo hτint
  have hbdist : dist b τ < ε := by
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [hbU.1], by linarith [hbU.2]⟩
  have hPb := hball hbdist
  rw [hB] at hbB
  exact hbB.2 hPb

end Commons.Analysis.ODE