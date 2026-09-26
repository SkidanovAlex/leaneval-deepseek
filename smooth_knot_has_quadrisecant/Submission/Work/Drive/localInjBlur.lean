import Mathlib
import Submission.Work.Drive.cornerBlur

/-!
# The local injectivity of a parameter blur, from a *local* half-space condition

This is the correct (local) form of the "common direction" criterion of the chord sweep.

Let `b` be a smoothing kernel (continuous, nonnegative, of *positive* mass — no normalisation
is needed here: the mass only has to be positive), `δ > 0` the width, and let
`γ : ℝ → E` be a curve whose **secants** over an interval `[α, β]` all grow in a fixed direction:

    `c * (s₂ - s₁) ≤ ⟪n, γ s₂ - γ s₁⟫`   for `α ≤ s₁ ≤ s₂ ≤ β`, some `c > 0`.

Then the parameter blur

    blur b δ γ t = ∫ u in (-1)..1, b u • γ (t - δ*u)

is **strictly monotone** (hence injective) on the inner interval `[a, d]` of `[α, β]` — with
`α ≤ a - δ` and `d + δ ≤ β`, so that every blur window stays inside `[α, β]`.

Proof: for `t₁ < t₂`, `blur t₂ - blur t₁ = ∫ b u • (γ (t₂ - δu) - γ (t₁ - δu)) du`; pairing with `n`
and using the secant condition pointwise — with `s₁ = t₁ - δu ≤ s₂ = t₂ - δu` and
`s₂ - s₁ = t₂ - t₁` — gives

    ⟪n, blur t₂ - blur t₁⟫ = ∫ u, b u * ⟪n, γ (t₂ - δu) - γ (t₁ - δu)⟫ du
                            ≥ ∫ u, b u * c (t₂ - t₁) du = c (t₂ - t₁) > 0.

Two remarks.

* The **secant** form is the one that survives at a *corner*: for the wedge
  `wedge p q s = if s ≤ 0 then s • p else s • q` with `⟪n, p⟫ ≥ c`, `⟪n, q⟫ ≥ c`, the secant from
  `s₁ < 0` to `s₂ > 0` is `s₂ • q + (-s₁) • p`, and pairing with `n` gives
  `s₂⟪n,q⟫ + (-s₁)⟪n,p⟫ ≥ c (s₂ - s₁)`: the two branches only need to lie in one open half-plane.
  This is the positive half of `Submission/Work/Drive/cornerBlur.lean`, where the *antiparallel*
  case is shown to be non-injective for every width.  No differentiability is used.
* The derivative form `c ≤ ⟪n, γ' s⟫` implies the secant form wherever `γ` is differentiable
  (`secant_of_deriv_halfspace`, by the fundamental theorem of calculus applied to the scalar function
  `s ↦ ⟪n, γ s⟫`).

Why the *global* form of the criterion kept being refuted: the corner at which the retained arc meets
its chord is a *near-cusp* — the two branch directions are antiparallel up to the curvature
correction (`NOTES_cornerBlur_SESSION.md` §2-3) — so the criterion fails there for *every* `n`,
whether on a window or on the whole loop.  What the lemma above does supply is the criterion's honest
local reach: on the smooth pieces of the loop, over a window shorter than the curvature scale, the
derivative form holds and the local injectivity follows; and the far separation of the sweep is the
separate, already proved `Work.Drive.sweepFamFarSep`.  The corner itself is the razor's-edge case,
and the ambient twist does **not** remove it (see the warning in
`Submission/Work/Drive/cornerBlur.lean`).
-/

noncomputable section

namespace Work.Drive

open scoped Real Topology intervalIntegral
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **The parameter blur** of a curve `γ` with kernel `b` and width `δ`. -/
def blur (b : ℝ → ℝ) (δ : ℝ) (γ : ℝ → E) (t : ℝ) : E :=
  ∫ u in (-1 : ℝ)..1, b u • γ (t - δ * u)

/-- The inner product passes through an interval integral of a scalar multiple. -/
lemma inner_intervalIntegral_smul_eq {n : E} {b : ℝ → ℝ} {γ : ℝ → E} {a c : ℝ}
    (h : IntervalIntegrable (fun u => b u • γ u) volume a c) :
    inner ℝ n (∫ u in a..c, b u • γ u) = ∫ u in a..c, b u * inner ℝ n (γ u) := by
  change (innerSL ℝ n) (∫ u in a..c, b u • γ u) = ∫ u in a..c, b u * inner ℝ n (γ u)
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℝ n) h]
  exact intervalIntegral.integral_congr (fun u _ => by
    simp only [innerSL_apply_apply, real_inner_smul_right])

/-- **Strict monotonicity of a parameter blur from a local secant condition.**

If every secant of `γ` over `[α, β]` grows at rate `c > 0` in the direction `n`, then the pairing of
the blur of `γ` with `n` is strictly increasing on the inner interval `[a, d]` (so that every blur
window stays inside `[α, β]`). -/
theorem strictMonoOn_inner_blur_of_secant {b : ℝ → ℝ} (hb : Continuous b) (hnn : ∀ u : ℝ, 0 ≤ b u)
    (hmass : 0 < ∫ u in (-1 : ℝ)..1, b u) {δ c : ℝ} (hδ : 0 < δ)
    (hc : 0 < c) {n : E} {γ : ℝ → E} (hγ : Continuous γ) {α β a d : ℝ}
    (ha : α ≤ a - δ) (hd : d + δ ≤ β)
    (hsec : ∀ s₁ ∈ Set.Icc α β, ∀ s₂ ∈ Set.Icc α β, s₁ ≤ s₂ →
      c * (s₂ - s₁) ≤ inner ℝ n (γ s₂ - γ s₁)) :
    StrictMonoOn (fun t : ℝ => inner ℝ n (blur b δ γ t)) (Set.Icc a d) := by
  intro t₁ ht₁ t₂ ht₂ hlt
  have ht₁' : a ≤ t₁ := ht₁.1
  have ht₂' : t₂ ≤ d := ht₂.2
  have hc' : IntervalIntegrable (fun u : ℝ => b u • γ (t₁ - δ * u)) volume (-1) 1 :=
    ((hb).smul (hγ.comp (by fun_prop))).intervalIntegrable _ _
  have hc'' : IntervalIntegrable (fun u : ℝ => b u • γ (t₂ - δ * u)) volume (-1) 1 :=
    ((hb).smul (hγ.comp (by fun_prop))).intervalIntegrable _ _
  -- the two windows stay inside `[α, β]`
  have hs : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      t₁ - δ * u ∈ Set.Icc α β ∧ t₂ - δ * u ∈ Set.Icc α β := by
    intro u hu
    have h1 : δ * u ≤ δ := by nlinarith [hu.2, hδ]
    have h2 : -δ ≤ δ * u := by nlinarith [hu.1, hδ]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hbound : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      c * (t₂ - t₁) ≤ inner ℝ n (γ (t₂ - δ * u) - γ (t₁ - δ * u)) := by
    intro u hu
    obtain ⟨hs₁, hs₂⟩ := hs u hu
    have hle' : t₁ - δ * u ≤ t₂ - δ * u := by linarith
    have h := hsec (t₁ - δ * u) hs₁ (t₂ - δ * u) hs₂ hle'
    have hsub' : (t₂ - δ * u) - (t₁ - δ * u) = t₂ - t₁ := by ring
    rwa [hsub'] at h
  -- the difference of the blurs is the blur of the differences
  have hdiff : blur b δ γ t₂ - blur b δ γ t₁
      = ∫ u in (-1 : ℝ)..1, b u • (γ (t₂ - δ * u) - γ (t₁ - δ * u)) := by
    rw [blur, blur, ← intervalIntegral.integral_sub hc'' hc']
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    rw [smul_sub]
  have hcont₂ : Continuous (fun u : ℝ => γ (t₂ - δ * u) - γ (t₁ - δ * u)) :=
    (hγ.comp (by fun_prop)).sub (hγ.comp (by fun_prop))
  have hpair : inner ℝ n (∫ u in (-1 : ℝ)..1, b u • (γ (t₂ - δ * u) - γ (t₁ - δ * u)))
      = ∫ u in (-1 : ℝ)..1, b u * inner ℝ n (γ (t₂ - δ * u) - γ (t₁ - δ * u)) :=
    inner_intervalIntegral_smul_eq (n := n)
      (((hb).smul hcont₂).intervalIntegrable _ _)
  have hinner : Continuous (fun u : ℝ => inner ℝ n (γ (t₂ - δ * u) - γ (t₁ - δ * u))) :=
    continuous_const.inner hcont₂
  have hmono : ∫ u in (-1 : ℝ)..1, b u * (c * (t₂ - t₁))
      ≤ ∫ u in (-1 : ℝ)..1, b u * inner ℝ n (γ (t₂ - δ * u) - γ (t₁ - δ * u)) :=
    intervalIntegral.integral_mono_on (by norm_num)
      (((hb).mul continuous_const).intervalIntegrable _ _)
      (((hb).mul hinner).intervalIntegrable _ _)
      (fun u hu => mul_le_mul_of_nonneg_left (hbound u hu) (hnn u))
  have hconst : ∫ u in (-1 : ℝ)..1, b u * (c * (t₂ - t₁))
      = c * (t₂ - t₁) * ∫ u in (-1 : ℝ)..1, b u := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun u _ => by ring)
  have hval : c * (t₂ - t₁) * (∫ u in (-1 : ℝ)..1, b u)
      ≤ inner ℝ n (blur b δ γ t₂ - blur b δ γ t₁) := by
    rw [hdiff, hpair]
    rw [hconst] at hmono
    exact hmono
  have hpos : 0 < inner ℝ n (blur b δ γ t₂ - blur b δ γ t₁) :=
    lt_of_lt_of_le (mul_pos (mul_pos hc (by linarith)) hmass) hval
  rw [inner_sub_right] at hpos
  linarith

/-- **Local injectivity of a parameter blur from a local secant condition.** -/
theorem injOn_blur_of_secant {b : ℝ → ℝ} (hb : Continuous b) (hnn : ∀ u : ℝ, 0 ≤ b u)
    (hmass : 0 < ∫ u in (-1 : ℝ)..1, b u) {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    {n : E} {γ : ℝ → E} (hγ : Continuous γ) {α β a d : ℝ}
    (ha : α ≤ a - δ) (hd : d + δ ≤ β)
    (hsec : ∀ s₁ ∈ Set.Icc α β, ∀ s₂ ∈ Set.Icc α β, s₁ ≤ s₂ →
      c * (s₂ - s₁) ≤ inner ℝ n (γ s₂ - γ s₁)) :
    Set.InjOn (blur b δ γ) (Set.Icc a d) := by
  intro t₁ ht₁ t₂ ht₂ heq
  rcases lt_trichotomy t₁ t₂ with h | h | h
  · have hlt : inner ℝ n (blur b δ γ t₁) < inner ℝ n (blur b δ γ t₂) :=
      strictMonoOn_inner_blur_of_secant hb hnn hmass hδ hc hγ ha hd hsec ht₁ ht₂ h
    rw [heq] at hlt
    exact absurd hlt (lt_irrefl _)
  · exact h
  · have hlt : inner ℝ n (blur b δ γ t₂) < inner ℝ n (blur b δ γ t₁) :=
      strictMonoOn_inner_blur_of_secant hb hnn hmass hδ hc hγ ha hd hsec ht₂ ht₁ h
    rw [heq] at hlt
    exact absurd hlt (lt_irrefl _)

/-- **The derivative half-space condition implies the secant condition** (for increasing pairs), by
the fundamental theorem of calculus applied to the scalar function `s ↦ ⟪n, γ s⟫`. -/
theorem secant_of_deriv_halfspace {n : E} {γ γ' : ℝ → E} {c : ℝ}
    {α β : ℝ} (hαβ : α ≤ β) (hc : 0 ≤ c)
    (hder : ∀ s ∈ Set.Icc α β, HasDerivAt γ (γ' s) s)
    (hint : IntervalIntegrable (fun s => inner ℝ n (γ' s)) volume α β)
    (hpos : ∀ s ∈ Set.Icc α β, c ≤ inner ℝ n (γ' s)) :
    ∀ s₁ ∈ Set.Icc α β, ∀ s₂ ∈ Set.Icc α β, s₁ ≤ s₂ →
      c * (s₂ - s₁) ≤ inner ℝ n (γ s₂ - γ s₁) := by
  intro s₁ hs₁ s₂ hs₂ hle
  have hsubI : Set.uIcc s₁ s₂ ⊆ Set.Icc α β := by
    intro s hs
    rw [Set.uIcc_of_le hle] at hs
    exact ⟨le_trans hs₁.1 hs.1, le_trans hs.2 hs₂.2⟩
  have hconv : ∀ s : ℝ, s ∈ Set.Icc s₁ s₂ → s ∈ Set.uIcc s₁ s₂ := by
    intro s hs
    rwa [Set.uIcc_of_le hle]
  have hsubU : Set.uIcc s₁ s₂ ⊆ Set.uIcc α β := by
    intro s hs
    rw [Set.uIcc_of_le hαβ]
    exact hsubI hs
  have hder' : ∀ s ∈ Set.uIcc s₁ s₂, HasDerivAt (fun r => inner ℝ n (γ r))
      (inner ℝ n (γ' s)) s := by
    intro s hs
    exact (innerSL ℝ n).hasFDerivAt.comp_hasDerivAt s (hder s (hsubI hs))
  have hftc : ∫ s in s₁..s₂, inner ℝ n (γ' s) = inner ℝ n (γ s₂) - inner ℝ n (γ s₁) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hder' (hint.mono_set hsubU)
  have h1 : ∫ s in s₁..s₂, c ≤ ∫ s in s₁..s₂, inner ℝ n (γ' s) :=
    intervalIntegral.integral_mono_on hle (continuous_const.intervalIntegrable _ _)
      (hint.mono_set hsubU) (fun s hs => hpos s (hsubI (hconv s hs)))
  rw [intervalIntegral.integral_const, smul_eq_mul] at h1
  rw [inner_sub_right, ← hftc]
  linarith [h1]

/-- **Local strict monotonicity of the parameter blur from a local half-space condition on the
velocity** (`secant_of_deriv_halfspace` + `strictMonoOn_blur_of_secant`). -/
theorem strictMonoOn_inner_blur_of_halfspace {b : ℝ → ℝ} (hb : Continuous b)
    (hnn : ∀ u : ℝ, 0 ≤ b u) (hmass : 0 < ∫ u in (-1 : ℝ)..1, b u) {δ c : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) {n : E} {γ γ' : ℝ → E} (hγ : Continuous γ) {α β a d : ℝ}
    (hαβ : α ≤ β) (ha : α ≤ a - δ) (hd : d + δ ≤ β)
    (hder : ∀ s ∈ Set.Icc α β, HasDerivAt γ (γ' s) s)
    (hint : IntervalIntegrable (fun s => inner ℝ n (γ' s)) volume α β)
    (hpos : ∀ s ∈ Set.Icc α β, c ≤ inner ℝ n (γ' s)) :
    StrictMonoOn (fun t : ℝ => inner ℝ n (blur b δ γ t)) (Set.Icc a d) :=
  strictMonoOn_inner_blur_of_secant hb hnn hmass hδ hc hγ ha hd
    (secant_of_deriv_halfspace hαβ hc.le hder hint hpos)

/-- **Local injectivity of the parameter blur from a local half-space condition on the velocity.** -/
theorem injOn_blur_of_halfspace {b : ℝ → ℝ} (hb : Continuous b) (hnn : ∀ u : ℝ, 0 ≤ b u)
    (hmass : 0 < ∫ u in (-1 : ℝ)..1, b u) {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) {n : E} {γ γ' : ℝ → E} (hγ : Continuous γ) {α β a d : ℝ} (hαβ : α ≤ β)
    (ha : α ≤ a - δ) (hd : d + δ ≤ β)
    (hder : ∀ s ∈ Set.Icc α β, HasDerivAt γ (γ' s) s)
    (hint : IntervalIntegrable (fun s => inner ℝ n (γ' s)) volume α β)
    (hpos : ∀ s ∈ Set.Icc α β, c ≤ inner ℝ n (γ' s)) :
    Set.InjOn (blur b δ γ) (Set.Icc a d) :=
  injOn_blur_of_secant hb hnn hmass hδ hc hγ ha hd
    (secant_of_deriv_halfspace hαβ hc.le hder hint hpos)

end Work.Drive

end
