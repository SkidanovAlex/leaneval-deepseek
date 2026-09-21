import Mathlib

/-!
# Differentiation under the integral sign on an interval, within a closed interval

The main result `Work.VolterraLong.C1.param_interval_deriv` states that if
`F : ℝ → ℝ → E` and `F' : ℝ → ℝ → E` are continuous on `Icc a b ×ˢ Icc c d`, and
`x ↦ F x t` has derivative `F' x t` at every `x ∈ Icc a b` for every `t ∈ Icc c d`,
then `x ↦ ∫ t in c..d, F x t` has derivative `∫ t in c..d, F' x₀ t` at `x₀` within
`Icc a b`.

Mathlib's parametric interval integral lemmas require differentiability on a genuine
neighbourhood of `x₀`, which is not available at the endpoints of `Icc a b`.  We
therefore extend `F` in its first argument linearly beyond `Icc a b` (and clamp the
second argument, which does not change interval integrals), differentiate the
extension with the Mathlib lemma, and transfer the result back by congruence.
-/

namespace Work.VolterraLong.C1

open MeasureTheory Set intervalIntegral Filter
open scoped Topology

/-- Clamp a real number to the interval `[a,b]`. -/
def clampTo (a b x : ℝ) : ℝ := max a (min b x)

lemma clampTo_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) : clampTo a b x ∈ Set.Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

lemma clampTo_eq_self {a b x : ℝ} (_hab : a ≤ b) (hx : x ∈ Set.Icc a b) :
    clampTo a b x = x := by
  rw [clampTo, min_eq_right hx.2, max_eq_right hx.1]

lemma clampTo_eq_left {a b x : ℝ} (hab : a ≤ b) (hx : x ≤ a) : clampTo a b x = a := by
  rw [clampTo, min_eq_right (le_trans hx hab), max_eq_left hx]

lemma clampTo_eq_right {a b x : ℝ} (hab : a ≤ b) (hx : b ≤ x) : clampTo a b x = b := by
  rw [clampTo, min_eq_left hx, max_eq_right hab]

lemma continuous_clampTo (a b : ℝ) : Continuous (clampTo a b) := by
  show Continuous (fun x : ℝ => max a (min b x))
  exact (continuous_const (y := a)).max ((continuous_const (y := b)).min continuous_id)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Extension of `F` in its first variable: affine beyond `[a,b]`; the second variable is
clamped to `[c,d]` (which does not change interval integrals over `c..d`). -/
def ext (a b c d : ℝ) (F F' : ℝ → ℝ → E) (x t : ℝ) : E :=
  F (clampTo a b x) (clampTo c d t) + (x - clampTo a b x) • F' (clampTo a b x) (clampTo c d t)

/-- The derivative of `ext` with respect to the first variable. -/
def extDeriv (a b c d : ℝ) (F' : ℝ → ℝ → E) (x t : ℝ) : E :=
  F' (clampTo a b x) (clampTo c d t)

lemma continuous_ext {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) {F F' : ℝ → ℝ → E}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Set.Icc a b ×ˢ Set.Icc c d))
    (hF' : ContinuousOn (fun p : ℝ × ℝ => F' p.1 p.2) (Set.Icc a b ×ˢ Set.Icc c d))
    (x : ℝ) : Continuous (fun t => ext a b c d F F' x t) := by
  have h1 : Continuous (fun t : ℝ => F (clampTo a b x) (clampTo c d t)) :=
    hF.comp_continuous (continuous_const.prodMk (continuous_clampTo c d))
      (fun t => ⟨clampTo_mem hab x, clampTo_mem hcd t⟩)
  have h2 : Continuous (fun t : ℝ => F' (clampTo a b x) (clampTo c d t)) :=
    hF'.comp_continuous (continuous_const.prodMk (continuous_clampTo c d))
      (fun t => ⟨clampTo_mem hab x, clampTo_mem hcd t⟩)
  show Continuous (fun t : ℝ => F (clampTo a b x) (clampTo c d t) +
    (x - clampTo a b x) • F' (clampTo a b x) (clampTo c d t))
  exact h1.add (h2.const_smul _)

omit [NormedSpace ℝ E] in
lemma continuous_extDeriv {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) {F' : ℝ → ℝ → E}
    (hF' : ContinuousOn (fun p : ℝ × ℝ => F' p.1 p.2) (Set.Icc a b ×ˢ Set.Icc c d))
    (x : ℝ) : Continuous (fun t => extDeriv a b c d F' x t) := by
  show Continuous (fun t : ℝ => F' (clampTo a b x) (clampTo c d t))
  exact hF'.comp_continuous (continuous_const.prodMk (continuous_clampTo c d))
      (fun t => ⟨clampTo_mem hab x, clampTo_mem hcd t⟩)

/-- An affine function of the form `y ↦ F a τ + (y - a) • F' a τ`. -/
lemma hasDerivAt_affine {F F' : ℝ → ℝ → E} (a τ x : ℝ) :
    HasDerivAt (fun y : ℝ => F a τ + (y - a) • F' a τ) (F' a τ) x := by
  have h : HasDerivAt (fun y : ℝ => (y - a) • F' a τ) (F' a τ) x := by
    have h1 : HasDerivAt (fun y : ℝ => y - a) (1 : ℝ) x := HasDerivAt.sub_const a (hasDerivAt_id x)
    simpa using h1.smul_const (F' a τ)
  simpa using HasDerivAt.const_add (F a τ) h

/-- The extension `ext` is differentiable in its first variable everywhere, with derivative
`extDeriv`, provided `a < b`. -/
lemma hasDerivAt_ext {a b c d : ℝ} (hab : a < b) (hcd : c ≤ d)
    {F F' : ℝ → ℝ → E}
    (hd : ∀ x ∈ Set.Icc a b, ∀ t ∈ Set.Icc c d, HasDerivAt (fun x => F x t) (F' x t) x)
    (t x : ℝ) :
    HasDerivAt (fun y => ext a b c d F F' y t) (extDeriv a b c d F' x t) x := by
  have hab' : a ≤ b := le_of_lt hab
  have hτ : clampTo c d t ∈ Set.Icc c d := clampTo_mem hcd t
  rcases lt_or_ge x a with hxa | hxa
  · -- x < a
    have hxc : clampTo a b x = a := clampTo_eq_left hab' (le_of_lt hxa)
    have hev : (fun y : ℝ => ext a b c d F F' y t) =ᶠ[𝓝 x]
        (fun y : ℝ => F a (clampTo c d t) + (y - a) • F' a (clampTo c d t)) := by
      filter_upwards [Iio_mem_nhds hxa] with y hy
      have hyc : clampTo a b y = a := clampTo_eq_left hab' (le_of_lt hy)
      simp only [ext, hyc]
    simpa only [extDeriv, hxc] using
      (hasDerivAt_affine (F := F) (F' := F') a (clampTo c d t) x).congr_of_eventuallyEq hev
  · rcases lt_or_ge b x with hbx | hbx
    · -- b < x
      have hxc : clampTo a b x = b := clampTo_eq_right hab' (le_of_lt hbx)
      have hev : (fun y : ℝ => ext a b c d F F' y t) =ᶠ[𝓝 x]
          (fun y : ℝ => F b (clampTo c d t) + (y - b) • F' b (clampTo c d t)) := by
        filter_upwards [Ioi_mem_nhds hbx] with y hy
        have hyc : clampTo a b y = b := clampTo_eq_right hab' (le_of_lt hy)
        simp only [ext, hyc]
      simpa only [extDeriv, hxc] using
        (hasDerivAt_affine (F := F) (F' := F') b (clampTo c d t) x).congr_of_eventuallyEq hev
    · rcases lt_or_ge a x with hax | hax
      · rcases lt_or_ge x b with hxb | hxb
        · -- a < x < b : interior
          have hxc : clampTo a b x = x := clampTo_eq_self hab' ⟨hax.le, hxb.le⟩
          have hev : (fun y : ℝ => ext a b c d F F' y t) =ᶠ[𝓝 x]
              (fun y : ℝ => F y (clampTo c d t)) := by
            filter_upwards [Ioo_mem_nhds hax hxb] with y hy
            have hyc : clampTo a b y = y := clampTo_eq_self hab' ⟨hy.1.le, hy.2.le⟩
            simp only [ext, hyc, sub_self, zero_smul, add_zero]
          simpa only [extDeriv, hxc] using
            (hd x ⟨hax.le, hxb.le⟩ (clampTo c d t) hτ).congr_of_eventuallyEq hev
        · -- x = b
          have hxbeq : x = b := le_antisymm hbx hxb
          rw [hxbeq]
          have hxc : clampTo a b b = b := clampTo_eq_right hab' le_rfl
          have h1 : HasDerivWithinAt (fun y : ℝ => ext a b c d F F' y t)
              (F' b (clampTo c d t)) (Set.Icc a b) b := by
            refine (hd b ⟨hab', le_rfl⟩ (clampTo c d t) hτ).hasDerivWithinAt.congr ?_ ?_
            · intro y hy
              simp only [ext, clampTo_eq_self hab' hy, sub_self, zero_smul, add_zero]
            · simp only [ext, clampTo_eq_self hab' ⟨hab', le_rfl⟩, sub_self, zero_smul, add_zero]
          have h2 : HasDerivWithinAt (fun y : ℝ => ext a b c d F F' y t)
              (F' b (clampTo c d t)) (Set.Ici b) b := by
            refine (hasDerivAt_affine (F := F) (F' := F') b (clampTo c d t) b).hasDerivWithinAt.congr
              ?_ ?_
            · intro y hy
              have hyc : clampTo a b y = b := clampTo_eq_right hab' hy
              simp only [ext, hyc]
            · simp only [ext, clampTo_eq_right hab' le_rfl]
          have hset : Set.Icc a b ∪ Set.Ici b = Set.Ici a := by
            ext y
            simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ici]
            constructor
            · rintro (⟨h, -⟩ | h) <;> linarith
            · intro h
              by_cases hy : b ≤ y
              · exact Or.inr hy
              · exact Or.inl ⟨h, le_of_lt (not_le.mp hy)⟩
          have h12 := h1.union h2
          rw [hset] at h12
          simpa only [extDeriv, hxc] using h12.hasDerivAt (Ici_mem_nhds hab)
      · -- x = a
        have hxaeq : x = a := le_antisymm hax hxa
        rw [hxaeq]
        have hxc : clampTo a b a = a := clampTo_eq_left hab' le_rfl
        have h1 : HasDerivWithinAt (fun y : ℝ => ext a b c d F F' y t)
            (F' a (clampTo c d t)) (Set.Iic a) a := by
          refine (hasDerivAt_affine (F := F) (F' := F') a (clampTo c d t) a).hasDerivWithinAt.congr
            ?_ ?_
          · intro y hy
            have hyc : clampTo a b y = a := clampTo_eq_left hab' hy
            simp only [ext, hyc]
          · simp only [ext, clampTo_eq_left hab' le_rfl]
        have h2 : HasDerivWithinAt (fun y : ℝ => ext a b c d F F' y t)
            (F' a (clampTo c d t)) (Set.Icc a b) a := by
          refine (hd a ⟨le_rfl, hab'⟩ (clampTo c d t) hτ).hasDerivWithinAt.congr ?_ ?_
          · intro y hy
            simp only [ext, clampTo_eq_self hab' hy, sub_self, zero_smul, add_zero]
          · simp only [ext, clampTo_eq_self hab' ⟨le_rfl, hab'⟩, sub_self, zero_smul, add_zero]
        have hset : Set.Iic a ∪ Set.Icc a b = Set.Iic b := by
          ext y
          simp only [Set.mem_union, Set.mem_Iic, Set.mem_Icc]
          constructor
          · rintro (h | ⟨-, h⟩) <;> linarith
          · intro h
            by_cases hy : y ≤ a
            · exact Or.inl hy
            · exact Or.inr ⟨le_of_lt (not_le.mp hy), h⟩
        have h12 := h1.union h2
        rw [hset] at h12
        simpa only [extDeriv, hxc] using h12.hasDerivAt (Iic_mem_nhds hab)

theorem param_interval_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b c d : ℝ} (hcd : c ≤ d) {F F' : ℝ → ℝ → E} {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b)
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Set.Icc a b ×ˢ Set.Icc c d))
    (hF' : ContinuousOn (fun p : ℝ × ℝ => F' p.1 p.2) (Set.Icc a b ×ˢ Set.Icc c d))
    (hd : ∀ x ∈ Set.Icc a b, ∀ t ∈ Set.Icc c d, HasDerivAt (fun x => F x t) (F' x t) x) :
    HasDerivWithinAt (fun x => ∫ t in c..d, F x t) (∫ t in c..d, F' x₀ t) (Set.Icc a b) x₀ := by
  have hab : a ≤ b := hx₀.1.trans hx₀.2
  rcases eq_or_lt_of_le hab with heq | hlt
  · -- degenerate case a = b : the interval is a singleton
    have hx₀eq : x₀ = a := by linarith [hx₀.1, hx₀.2, heq]
    have hset : Set.Icc a b = {x₀} := by
      rw [← heq, Set.Icc_self]
      exact Set.singleton_eq_singleton_iff.mpr hx₀eq.symm
    rw [hset]
    have hzero : HasDerivWithinAt (fun x => ∫ t in c..d, F x t) (∫ t in c..d, F' x₀ t)
        ({x₀} \ {x₀} : Set ℝ) x₀ := by
      rw [Set.sdiff_self (s := ({x₀} : Set ℝ)), hasDerivWithinAt_iff_tendsto, nhdsWithin_empty]
      exact Filter.tendsto_bot
    exact (hasDerivWithinAt_sdiff_singleton (s := {x₀}) (x := x₀)).mp hzero
  · have hab' : a ≤ b := le_of_lt hlt
    obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hF'
    have hbound : ∀ᵐ t ∂volume, t ∈ Set.uIoc c d → ∀ x ∈ (Set.univ : Set ℝ),
        ‖extDeriv a b c d F' x t‖ ≤ M := by
      refine Filter.Eventually.of_forall (fun t _ x _ => ?_)
      simp only [extDeriv]
      exact hM (clampTo a b x, clampTo c d t) ⟨clampTo_mem hab' x, clampTo_mem hcd t⟩
    have hmeas : ∀ᶠ x in 𝓝 x₀,
        AEStronglyMeasurable (fun t => ext a b c d F F' x t) (volume.restrict (Set.uIoc c d)) :=
      Filter.Eventually.of_forall (fun x => (continuous_ext hab' hcd hF hF' x).aestronglyMeasurable)
    have hint : IntervalIntegrable (fun t => ext a b c d F F' x₀ t) volume c d :=
      (continuous_ext hab' hcd hF hF' x₀).intervalIntegrable c d
    have hmeas' : AEStronglyMeasurable (fun t => extDeriv a b c d F' x₀ t)
        (volume.restrict (Set.uIoc c d)) :=
      (continuous_extDeriv hab' hcd hF' x₀).aestronglyMeasurable
    have hbounded : IntervalIntegrable (fun _ : ℝ => M) volume c d := intervalIntegrable_const
    have hderiv : ∀ᵐ t ∂volume, t ∈ Set.uIoc c d → ∀ x ∈ (Set.univ : Set ℝ),
        HasDerivAt (fun x => ext a b c d F F' x t) (extDeriv a b c d F' x t) x :=
      Filter.Eventually.of_forall (fun t _ x _ => hasDerivAt_ext hlt hcd hd t x)
    have h_ext := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := c) (b := d) (bound := fun _ : ℝ => M)
      (F := fun x t => ext a b c d F F' x t) (F' := fun x t => extDeriv a b c d F' x t)
      (x₀ := x₀) (s := Set.univ) Filter.univ_mem hmeas hint hmeas' hbound hbounded hderiv).2
    have hint_eq : ∀ x ∈ Set.Icc a b,
        (∫ t in c..d, ext a b c d F F' x t) = ∫ t in c..d, F x t := by
      intro x hx
      refine intervalIntegral.integral_congr ?_
      intro t ht
      rw [Set.uIcc_of_le hcd] at ht
      simp only [ext, clampTo_eq_self hab' hx, clampTo_eq_self hcd ht,
        sub_self, zero_smul, add_zero]
    have hderiv_eq : (∫ t in c..d, extDeriv a b c d F' x₀ t) = ∫ t in c..d, F' x₀ t := by
      refine intervalIntegral.integral_congr ?_
      intro t ht
      rw [Set.uIcc_of_le hcd] at ht
      simp only [extDeriv, clampTo_eq_self hab' hx₀, clampTo_eq_self hcd ht]
    rw [hderiv_eq] at h_ext
    exact h_ext.hasDerivWithinAt.congr (fun x hx => (hint_eq x hx).symm) (hint_eq x₀ hx₀).symm

end Work.VolterraLong.C1
