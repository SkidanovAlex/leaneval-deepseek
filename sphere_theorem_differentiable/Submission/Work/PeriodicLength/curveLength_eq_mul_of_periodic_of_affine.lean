import Mathlib
import Submission.Work.OddBound.LiftKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.PeriodicLength

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval

/-- **The speed of a `1`-periodic curve is `1`-periodic.**  If `f (r + 1) = f r` for every `r`,
then the Riemannian speed of `f` satisfies `curveSpeed f (t + 1) = curveSpeed f t` for every `t`.

The identity holds unconditionally, including at points where `f` is not differentiable: there the
velocity (and hence the speed) is the junk value `0` on both sides, and `f` is differentiable at
`t` if and only if it is differentiable at `t + 1` (compose with the translation, both ways). -/
private lemma curveSpeed_add_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {f : ℝ → M} (hper : ∀ r : ℝ, f (r + 1) = f r) (t : ℝ) :
    Submission.Length.curveSpeed (I := I) f (t + 1) = Submission.Length.curveSpeed (I := I) f t := by
  by_cases hd : MDifferentiableAt 𝓘(ℝ) I f t
  · -- `f` is differentiable at `t`: transport the velocity along the translation `r ↦ r - 1`.
    have hvel : Submission.Geodesic.curveVelocity (I := I) f (t + 1)
        = Submission.Geodesic.curveVelocity (I := I) f t := by
      have h1 := Submission.GeodesicGlobal2.curveVelocity_comp_sub (I := I) (σ := f) (t := t)
        (T := 1) hd
      have h2 : (fun s : ℝ => f (s - 1)) = f := by
        funext s
        simpa using (hper (s - 1)).symm
      have h3 := Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq (I := I)
        (t := t + 1) (γ := fun s : ℝ => f (s - 1)) (γ' := f) (Filter.EventuallyEq.of_eq h2)
      exact h3.symm.trans h1
    simp only [Submission.Length.curveSpeed_def]
    rw [hper t, hvel]
  · -- `f` is not differentiable at `t`: then neither at `t + 1`, and both speeds are `0`.
    have h0 : Submission.Geodesic.curveVelocity (I := I) f t = 0 := by
      show (mfderiv 𝓘(ℝ) I f t) (1 : ℝ) = 0
      rw [mfderiv_zero_of_not_mdifferentiableAt hd]
      exact zero_apply (1 : ℝ)
    have hnd : ¬ MDifferentiableAt 𝓘(ℝ) I f (t + 1) := by
      intro hf1
      have hadd : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ) (fun s : ℝ => s + 1) t := by
        rw [mdifferentiableAt_iff_differentiableAt]
        exact (differentiableAt_id (x := t)).add_const (1 : ℝ)
      have hcomp : MDifferentiableAt 𝓘(ℝ) I (f ∘ (fun s : ℝ => s + 1)) t := hf1.comp t hadd
      have heq : f ∘ (fun s : ℝ => s + 1) = f := by
        funext s; exact hper s
      exact hd (heq ▸ hcomp)
    have h0' : Submission.Geodesic.curveVelocity (I := I) f (t + 1) = 0 := by
      show (mfderiv 𝓘(ℝ) I f (t + 1)) (1 : ℝ) = 0
      rw [mfderiv_zero_of_not_mdifferentiableAt hnd]
      exact zero_apply (1 : ℝ)
    have hs0 : Submission.Length.curveSpeed (I := I) f t = 0 := by
      simp only [Submission.Length.curveSpeed_def]
      rw [h0, inner_zero_left, Real.sqrt_zero]
    have hs1 : Submission.Length.curveSpeed (I := I) f (t + 1) = 0 := by
      simp only [Submission.Length.curveSpeed_def]
      rw [h0', inner_zero_left, Real.sqrt_zero]
    rw [hs1, hs0]

/-- **The length of a `1`-periodic curve is affine in the upper endpoint.**  If every translate
`fun r => f (r + 1)` equals `f`, the speed of `f` is interval integrable on every interval, and the
length over `[0,u]` is `u * T` for every `u ∈ [0,1]`, then the length over `[0,s]` is `s * T` for
every real `s`.  (`curveLength` is `Submission.Length.curveLength` from the imported library.) -/
theorem curveLength_eq_mul_of_periodic_of_affine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {f : ℝ → M} {T : ℝ}
    (hper : ∀ r : ℝ, f (r + 1) = f r)
    (hint : ∀ a b : ℝ,
      IntervalIntegrable (Submission.Length.curveSpeed (I := I) f) MeasureTheory.volume a b)
    (haff : ∀ u ∈ Set.Icc (0:ℝ) 1, Submission.Length.curveLength (I := I) f 0 u = u * T) :
    ∀ s : ℝ, Submission.Length.curveLength (I := I) f 0 s = s * T := by
  -- The speed is `1`-periodic.
  have hgp : Function.Periodic (Submission.Length.curveSpeed (I := I) f) 1 :=
    fun t => curveSpeed_add_one (I := I) hper t
  -- The length of one period, starting at `0`.
  have hT1 : (∫ x in (0:ℝ)..0 + (1:ℝ), Submission.Length.curveSpeed (I := I) f x) = T := by
    have h := haff 1 (by norm_num)
    simpa [Submission.Length.curveLength_def] using h
  -- The length from `0` to an integer.
  have hInt : ∀ n : ℤ, Submission.Length.curveLength (I := I) f 0 (n : ℝ) = (n : ℝ) * T := by
    intro n
    have h := Function.Periodic.intervalIntegral_add_zsmul_eq hgp n 0 hint
    have hz : (0:ℝ) + n • (1:ℝ) = (n:ℝ) := by simp
    calc Submission.Length.curveLength (I := I) f 0 (n : ℝ)
        = ∫ x in (0:ℝ)..(n:ℝ), Submission.Length.curveSpeed (I := I) f x := rfl
      _ = ∫ x in (0:ℝ)..0 + n • (1:ℝ), Submission.Length.curveSpeed (I := I) f x := by rw [hz]
      _ = n • (∫ x in (0:ℝ)..0 + (1:ℝ), Submission.Length.curveSpeed (I := I) f x) := h
      _ = (n : ℝ) * T := by rw [hT1, zsmul_eq_mul]
  -- The length from an integer `k` to `k + u`, for `u ∈ [0,1]`.
  have hShift : ∀ (k : ℤ) (u : ℝ), u ∈ Set.Icc (0:ℝ) 1 →
      Submission.Length.curveLength (I := I) f (k:ℝ) ((k:ℝ) + u) = u * T := by
    intro k u hu
    have hperk : ∀ x : ℝ, Submission.Length.curveSpeed (I := I) f (x + (k:ℝ))
        = Submission.Length.curveSpeed (I := I) f x := by
      intro x
      have h := (hgp.zsmul k) x
      simpa using h
    have h1 : (∫ x in (k:ℝ)..(k:ℝ) + u, Submission.Length.curveSpeed (I := I) f x)
        = ∫ x in (0:ℝ)..u, Submission.Length.curveSpeed (I := I) f (x + (k:ℝ)) := by
      have h := intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := u)
        (Submission.Length.curveSpeed (I := I) f) ((k:ℝ))
      rw [zero_add, add_comm u ((k:ℝ))] at h
      exact h.symm
    have h2 : (∫ x in (0:ℝ)..u, Submission.Length.curveSpeed (I := I) f (x + (k:ℝ)))
        = ∫ x in (0:ℝ)..u, Submission.Length.curveSpeed (I := I) f x :=
      intervalIntegral.integral_congr (fun x _ => hperk x)
    have h3 : (∫ x in (0:ℝ)..u, Submission.Length.curveSpeed (I := I) f x) = u * T := by
      have h := haff u hu
      simpa [Submission.Length.curveLength_def] using h
    calc Submission.Length.curveLength (I := I) f (k:ℝ) ((k:ℝ) + u)
        = ∫ x in (k:ℝ)..(k:ℝ) + u, Submission.Length.curveSpeed (I := I) f x := rfl
      _ = ∫ x in (0:ℝ)..u, Submission.Length.curveSpeed (I := I) f (x + (k:ℝ)) := h1
      _ = ∫ x in (0:ℝ)..u, Submission.Length.curveSpeed (I := I) f x := h2
      _ = u * T := h3
  intro s
  -- Decompose `s = ⌊s⌋ + fract s` with an integer part and a fractional part in `[0,1]`.
  have hfrac : Int.fract s ∈ Set.Icc (0:ℝ) 1 :=
    ⟨Int.fract_nonneg s, le_of_lt (Int.fract_lt_one s)⟩
  have hs : ((⌊s⌋ : ℤ) : ℝ) + Int.fract s = s := by
    linarith [Int.self_sub_fract s]
  have hadd := Submission.Length.curveLength_add_of_integrable (I := I) (γ := f) (a := (0:ℝ))
      (b := ((⌊s⌋ : ℤ) : ℝ)) (c := s) (hint 0 _) (hint _ s)
  have hL : Submission.Length.curveLength (I := I) f ((⌊s⌋ : ℤ) : ℝ) s = Int.fract s * T := by
    have h := hShift ⌊s⌋ (Int.fract s) hfrac
    rwa [hs] at h
  have htot : Submission.Length.curveLength (I := I) f 0 s
      = ((⌊s⌋ : ℤ) : ℝ) * T + Int.fract s * T := by
    rw [← hadd, hInt ⌊s⌋, hL]
  calc Submission.Length.curveLength (I := I) f 0 s
      = ((⌊s⌋ : ℤ) : ℝ) * T + Int.fract s * T := htot
    _ = (((⌊s⌋ : ℤ) : ℝ) + Int.fract s) * T := (add_mul _ _ T).symm
    _ = s * T := by rw [hs]

end Work.PeriodicLength
