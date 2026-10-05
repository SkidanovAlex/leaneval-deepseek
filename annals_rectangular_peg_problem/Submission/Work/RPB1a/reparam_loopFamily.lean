import Mathlib
import Submission.Work.RPB1a.Defs
import Submission.Work.RPB1a.exists_monodromy_int
import Submission.Work.RPB1a.monodromy_eq_one_or_neg_one

/-!
# Node N9: `Work.RPB1a.reparam_loopFamily`

Let `v` be a smooth embedded immersed `2π`-periodic loop in `ℂ` and `σ` a `C^∞` reparametrisation
such that `v ∘ σ` is again a smooth embedded immersed loop.  Then `σ` is a smooth reparametrisation
of the circle `ℝ/2πℤ` of degree `±1`: there is `k : ℤ`, `k = ±1`, with
`σ (t + 2π) = σ t + 2π k`, and the straight-line interpolation of the reparametrisation realises
`v ∘ σ` as a loop family equivalent to `v (k ·)`:

`c s t = v ((1 - s) * σ t + s * k * t)`.

The two "data" lemmas about `σ` are proved (publicly) in the sibling modules

* `Work.RPB1a.exists_monodromy_int` — the monodromy of `σ` over one period is an integer `k`
  (a continuous integer-valued function on the connected line is constant),
* `Work.RPB1a.monodromy_eq_one_or_neg_one` — `σ` is strictly monotone and `|k| ≥ 2` would let the
  intermediate value theorem produce `t₁ ∈ (0, 2π)` with `σ t₁ = σ 0 ± 2π`, contradicting
  injectivity of `v ∘ σ` mod `2π`.

What remains here is the chain rule (`deriv σ ≠ 0`), the sign of `deriv σ`, and the construction
of the family: the interpolation `Θ_s = (1 - s) σ + s k · id` is strictly monotone (which gives
injectivity mod `2π` for each `s`) and immersed, and `v ∘ Θ_s` inherits these properties through
the chain rule.
-/

set_option autoImplicit false

open Complex Set Metric
open scoped ContDiff Real

noncomputable section

namespace Work.RPB1a

/-- `σ` with nowhere vanishing derivative is strictly monotone (in one of the two directions). -/
private lemma strictMono_or_strictAnti_of_deriv_ne_zero (σ : ℝ → ℝ) (hσ : ContDiff ℝ ∞ σ)
    (h : ∀ t, deriv σ t ≠ 0) : StrictMono σ ∨ StrictAnti σ := by
  have hcont : Continuous (deriv σ) := hσ.continuous_deriv (by simp)
  rcases (isPreconnected_univ).mapsTo_Ioi_or_Iio hcont.continuousOn (fun x _ => h x) with hp | hn
  · exact Or.inl (strictMono_of_deriv_pos fun t => hp (Set.mem_univ t))
  · exact Or.inr (strictAnti_of_deriv_neg fun t => hn (Set.mem_univ t))

/-- `0 < (1 - s) a + s` for `a > 0`, `0 ≤ s ≤ 1`. -/
private lemma pos_combo {a s : ℝ} (ha : 0 < a) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 < (1 - s) * a + s := by
  have h1 : 0 ≤ 1 - s := by linarith
  rcases eq_or_lt_of_le hs0 with h | h
  · rw [← h]; simpa using ha
  · nlinarith [mul_nonneg h1 (le_of_lt ha)]

/-- `(1 - s) a - s < 0` for `a < 0`, `0 ≤ s ≤ 1`. -/
private lemma neg_combo {a s : ℝ} (ha : a < 0) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 - s) * a - s < 0 := by
  have h1 : 0 ≤ 1 - s := by linarith
  rcases eq_or_lt_of_le hs0 with h | h
  · rw [← h]; simpa using ha
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos h1 (le_of_lt ha)]

/-- A convex combination, with nonnegative weights not both zero, of two strictly increasing
functions is strictly increasing. -/
private lemma strictMono_combo {f g : ℝ → ℝ} (hf : StrictMono f) (hg : StrictMono g)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) :
    StrictMono (fun x => a * f x + b * g x) := by
  intro x y hxy
  change a * f x + b * g x < a * f y + b * g y
  have hfx : f x < f y := hf hxy
  have hgx : g x < g y := hg hxy
  rcases eq_or_lt_of_le ha with h | h
  · have hb' : 0 < b := by linarith
    rw [← h]
    simpa using mul_lt_mul_of_pos_left hgx hb'
  · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hfx h)
      (mul_le_mul_of_nonneg_left (le_of_lt hgx) hb)

/-- A convex combination, with nonnegative weights not both zero, of two strictly decreasing
functions is strictly decreasing. -/
private lemma strictAnti_combo {f g : ℝ → ℝ} (hf : StrictAnti f) (hg : StrictAnti g)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) :
    StrictAnti (fun x => a * f x + b * g x) := by
  intro x y hxy
  change a * f y + b * g y < a * f x + b * g x
  have hfx : f y < f x := hf hxy
  have hgx : g y < g x := hg hxy
  rcases eq_or_lt_of_le ha with h | h
  · have hb' : 0 < b := by linarith
    rw [← h]
    simpa using mul_lt_mul_of_pos_left hgx hb'
  · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hfx h)
      (mul_le_mul_of_nonneg_left (le_of_lt hgx) hb)

/-- **N9.** A smooth reparametrisation of a smooth embedded loop is a degree-`±1` circle
reparametrisation, and the straight-line homotopy of the reparametrisation is a loop family. -/
theorem reparam_loopFamily (v : ℝ → ℂ) (hv : IsSmoothLoop v) (σ : ℝ → ℝ)
    (hσ : ContDiff ℝ ∞ σ) (hw : IsSmoothLoop (fun t => v (σ t))) :
    ∃ e : ℝ, (e = 1 ∨ e = -1) ∧ ∃ c : ℝ → ℝ → ℂ, IsLoopFamily c ∧
      (∀ t, c 0 t = v (σ t)) ∧ ∀ t, c 1 t = v (e * t) := by
  obtain ⟨k, hk⟩ := exists_monodromy_int v hv σ hσ.continuous hw
  -- the chain rule: `σ'` never vanishes
  have hderivσ : ∀ t, deriv σ t ≠ 0 := by
    intro t
    have hσd : HasDerivAt σ (deriv σ t) t :=
      (hσ.differentiable (by simp)).differentiableAt.hasDerivAt
    have hvd : HasDerivAt v (deriv v (σ t)) (σ t) :=
      (hv.1.differentiable (by simp)).differentiableAt.hasDerivAt
    have hcomp := HasDerivAt.scomp (𝕜' := ℝ) t hvd hσd
    have heq : deriv (fun t => v (σ t)) t = (deriv σ t) • (deriv v (σ t)) := by
      simpa [Function.comp_def] using hcomp.deriv
    have hne : (deriv σ t) • (deriv v (σ t)) ≠ 0 := by
      rw [← heq]
      exact hw.2.2.2 t
    intro h0
    rw [h0] at hne
    exact hne (zero_smul ℝ _)
  have hmono : StrictMono σ ∨ StrictAnti σ :=
    strictMono_or_strictAnti_of_deriv_ne_zero σ hσ hderivσ
  have hk12 : k = 1 ∨ k = -1 :=
    monodromy_eq_one_or_neg_one v hv σ hσ.continuous hw k hk hmono
  -- sign consistency between the monotonicity of `σ` and the sign of `k`
  have hksign : (StrictMono σ ∧ k = 1) ∨ (StrictAnti σ ∧ k = -1) := by
    have hpi : (0 : ℝ) < 2 * π := by positivity
    rcases hmono with hsm | hanti
    · left
      refine ⟨hsm, ?_⟩
      have hkpos : (0 : ℝ) < (k : ℝ) := by
        have hlt : σ 0 < σ (0 + 2 * π) := hsm (by linarith)
        rw [hk 0] at hlt
        have : (0 : ℝ) < (2 : ℝ) * π * (k : ℝ) := by linarith
        exact pos_of_mul_pos_right this (le_of_lt hpi)
      rcases hk12 with h | h
      · exact h
      · rw [h] at hkpos
        norm_num at hkpos
    · right
      refine ⟨hanti, ?_⟩
      have hkneg : (k : ℝ) < 0 := by
        have hlt : σ (0 + 2 * π) < σ 0 := hanti (by linarith)
        rw [hk 0] at hlt
        have : (2 : ℝ) * π * (k : ℝ) < 0 := by linarith
        exact neg_of_mul_neg_right this (le_of_lt hpi)
      rcases hk12 with h | h
      · rw [h] at hkneg
        norm_num at hkneg
      · exact h
  -- `v (x + 2π k) = v x` for the integer `k`
  have hvk : ∀ x : ℝ, v (x + (k : ℝ) * (2 * π)) = v x :=
    fun x => (Function.Periodic.int_mul hv.2.1 k) x
  -- the integer shift of the reparametrisation
  have hσsh : ∀ (j : ℤ) (x : ℝ), σ (x + (j : ℝ) * (2 * π)) =
      σ x + (k : ℝ) * ((j : ℝ) * (2 * π)) := by
    intro j x
    have hP : Function.Periodic (fun y : ℝ => σ y - (k : ℝ) * y) (2 * π) := by
      intro y
      show σ (y + 2 * π) - (k : ℝ) * (y + 2 * π) = σ y - (k : ℝ) * y
      rw [hk y]
      ring
    have h : σ (x + (j : ℝ) * (2 * π)) - (k : ℝ) * (x + (j : ℝ) * (2 * π))
        = σ x - (k : ℝ) * x := (hP.int_mul j) x
    ring_nf at h ⊢
    linarith
  -- `Θ_s x = (1 - s) σ x + s k x` is a strictly monotone circle map for `s ∈ [0,1]`
  have hstrict : ∀ s ∈ Icc (0 : ℝ) 1,
      StrictMono (fun x : ℝ => (1 - s) * σ x + s * (k : ℝ) * x) ∨
      StrictAnti (fun x : ℝ => (1 - s) * σ x + s * (k : ℝ) * x) := by
    intro s hs
    rcases hksign with ⟨hsm, hk1⟩ | ⟨hanti, hkneg⟩
    · left
      have hk1' : (k : ℝ) = 1 := by rw [hk1]; norm_num
      have hfun : (fun x : ℝ => (1 - s) * σ x + s * (k : ℝ) * x) =
          fun x : ℝ => (1 - s) * σ x + s * x := by
        funext x
        rw [hk1']
        ring
      rw [hfun]
      exact strictMono_combo hsm strictMono_id (by linarith [hs.2]) hs.1 (by linarith)
    · right
      have hkneg' : (k : ℝ) = -1 := by rw [hkneg]; norm_num
      have hfun : (fun x : ℝ => (1 - s) * σ x + s * (k : ℝ) * x) =
          fun x : ℝ => (1 - s) * σ x + s * (-x) := by
        funext x
        rw [hkneg']
        ring
      rw [hfun]
      exact strictAnti_combo hanti (fun x y hxy => by linarith) (by linarith [hs.2]) hs.1
        (by linarith)
  have hinj : ∀ s ∈ Icc (0 : ℝ) 1,
      Function.Injective (fun x : ℝ => (1 - s) * σ x + s * (k : ℝ) * x) := by
    intro s hs
    rcases hstrict s hs with h | h
    · exact h.injective
    · exact h.injective
  -- the intermediate reparametrisations are immersed
  have hderiv_ne : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t,
      deriv (fun x : ℝ => (1 - s) * σ x + s * (k : ℝ) * x) t ≠ 0 := by
    intro s hs t
    have hΘd : HasDerivAt (fun x : ℝ => (1 - s) * σ x + s * (k : ℝ) * x)
        ((1 - s) * deriv σ t + s * (k : ℝ)) t := by
      have h1 : HasDerivAt σ (deriv σ t) t :=
        (hσ.differentiable (by simp)).differentiableAt.hasDerivAt
      have h2 : HasDerivAt (fun x : ℝ => s * (k : ℝ) * x) (s * (k : ℝ)) t := by
        simpa using (hasDerivAt_id t).const_mul (s * (k : ℝ))
      exact (h1.const_mul (1 - s)).add h2
    rw [hΘd.deriv]
    rcases hksign with ⟨hsm, hk1⟩ | ⟨hanti, hkneg⟩
    · have hσpos : 0 < deriv σ t :=
        lt_of_le_of_ne (hsm.monotone.deriv_nonneg) (Ne.symm (hderivσ t))
      have hk1' : (k : ℝ) = 1 := by rw [hk1]; norm_num
      have heq : (1 - s) * deriv σ t + s * (k : ℝ) = (1 - s) * deriv σ t + s := by
        rw [hk1']; ring
      rw [heq]
      exact ne_of_gt (pos_combo hσpos hs.1 hs.2)
    · have hσneg : deriv σ t < 0 :=
        lt_of_le_of_ne (hanti.antitone.deriv_nonpos) (hderivσ t)
      have hkneg' : (k : ℝ) = -1 := by rw [hkneg]; norm_num
      have heq : (1 - s) * deriv σ t + s * (k : ℝ) = (1 - s) * deriv σ t - s := by
        rw [hkneg']; ring
      rw [heq]
      exact ne_of_lt (neg_combo hσneg hs.1 hs.2)
  refine ⟨(k : ℝ), ?_, fun s t => v ((1 - s) * σ t + s * (k : ℝ) * t), ?_, ?_, ?_⟩
  · rcases hk12 with h | h
    · left; rw [h]; norm_num
    · right; rw [h]; norm_num
  · -- `IsLoopFamily`
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- joint smoothness
      have hΘ : ContDiff ℝ ∞ (fun z : ℝ × ℝ => (1 - z.1) * σ z.2 + z.1 * (k : ℝ) * z.2) := by
        have h1 : ContDiff ℝ ∞ (fun z : ℝ × ℝ => 1 - z.1) := contDiff_const.sub contDiff_fst
        have h2 : ContDiff ℝ ∞ (fun z : ℝ × ℝ => σ z.2) := hσ.comp contDiff_snd
        have h3 : ContDiff ℝ ∞ (fun z : ℝ × ℝ => z.1 * (k : ℝ) * z.2) :=
          (contDiff_fst.mul contDiff_const).mul contDiff_snd
        exact (h1.mul h2).add h3
      exact hv.1.comp hΘ
    · -- periodicity
      intro s t
      show v ((1 - s) * σ (t + 2 * π) + s * (k : ℝ) * (t + 2 * π))
        = v ((1 - s) * σ t + s * (k : ℝ) * t)
      have h : (1 - s) * σ (t + 2 * π) + s * (k : ℝ) * (t + 2 * π)
          = ((1 - s) * σ t + s * (k : ℝ) * t) + (k : ℝ) * (2 * π) := by
        rw [hk t]
        ring
      rw [h]
      exact hvk _
    · -- injectivity mod `2π`
      intro s hs t t' hvv
      obtain ⟨m, hm⟩ := hv.2.2.1 ((1 - s) * σ t + s * (k : ℝ) * t)
        ((1 - s) * σ t' + s * (k : ℝ) * t') hvv
      have hΘsh : ∀ (j : ℤ) (x : ℝ),
          (1 - s) * σ (x + (j : ℝ) * (2 * π)) + s * (k : ℝ) * (x + (j : ℝ) * (2 * π))
            = ((1 - s) * σ x + s * (k : ℝ) * x) + (k : ℝ) * ((j : ℝ) * (2 * π)) := by
        intro j x
        rw [hσsh j x]
        ring
      have hkk : (k : ℝ) * (k : ℝ) = 1 := by
        rcases hk12 with h | h <;> rw [h] <;> norm_num
      have hab : (k : ℝ) * (((k * m : ℤ) : ℝ) * (2 * π)) = 2 * π * (m : ℝ) := by
        rw [Int.cast_mul]
        rw [show (k : ℝ) * ((k : ℝ) * (m : ℝ) * (2 * π))
            = ((k : ℝ) * (k : ℝ)) * ((m : ℝ) * (2 * π)) by ring]
        rw [hkk]
        ring
      refine ⟨k * m, ?_⟩
      have hkey : (1 - s) * σ (t + ((k * m : ℤ) : ℝ) * (2 * π))
          + s * (k : ℝ) * (t + ((k * m : ℤ) : ℝ) * (2 * π))
            = (1 - s) * σ t' + s * (k : ℝ) * t' := by
        rw [hΘsh (k * m) t, hm, hab]
      have := hinj s hs hkey
      rw [← this]
      ring
    · -- immersion
      intro s hs t
      show deriv (fun x : ℝ => v ((1 - s) * σ x + s * (k : ℝ) * x)) t ≠ 0
      have hvd : HasDerivAt v (deriv v ((1 - s) * σ t + s * (k : ℝ) * t))
          ((1 - s) * σ t + s * (k : ℝ) * t) :=
        (hv.1.differentiable (by simp)).differentiableAt.hasDerivAt
      have hΘd : HasDerivAt (fun x : ℝ => (1 - s) * σ x + s * (k : ℝ) * x)
          ((1 - s) * deriv σ t + s * (k : ℝ)) t := by
        have h1 : HasDerivAt σ (deriv σ t) t :=
          (hσ.differentiable (by simp)).differentiableAt.hasDerivAt
        have h2 : HasDerivAt (fun x : ℝ => s * (k : ℝ) * x) (s * (k : ℝ)) t := by
          simpa using (hasDerivAt_id t).const_mul (s * (k : ℝ))
        exact (h1.const_mul (1 - s)).add h2
      have hcomp := HasDerivAt.scomp (𝕜' := ℝ) t hvd hΘd
      have hder : deriv (fun x : ℝ => v ((1 - s) * σ x + s * (k : ℝ) * x)) t
          = ((1 - s) * deriv σ t + s * (k : ℝ))
              • (deriv v ((1 - s) * σ t + s * (k : ℝ) * t)) := hcomp.deriv
      rw [hder, hΘd.deriv.symm]
      exact smul_ne_zero (hderiv_ne s hs t) (hv.2.2.2 _)
  · -- left endpoint
    intro t
    simp
  · -- right endpoint
    intro t
    simp

end Work.RPB1a

end
