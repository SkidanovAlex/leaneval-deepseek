import Mathlib

namespace Work.EpsW

/-!
# The one-sided half of a level set at an isolated transverse crossing

Fix a continuous real function `f = L ∘ γ` on the line and a value `a`.  Suppose `t₀` is the only
point of a neighbourhood `(t₀ - δ₁, t₀ + δ₁)` at which `f = a`, and suppose `f` takes values both
above and below `a` arbitrarily close to `t₀`.  Then, on each closed half `[t₀ - δ, t₀ + δ]` with
`0 < δ < δ₁`, the sign of `f - a` is constant on each side of `t₀` and *opposite* on the two
sides: `a ≤ f t` holds exactly for the `t` on one chosen side, and this is encoded by a number `d`
with `|d| = δ` via `0 ≤ (t - t₀) * d`.

The mathematics is elementary.  A continuous function on an interval on which it never vanishes has
constant sign (intermediate value theorem); this gives the constancy on `[t₀ - δ, t₀)` and on
`(t₀, t₀ + δ]`, the endpoint being included because the endpoint is not a zero either.  The two
sides cannot carry the same sign, since then `a` would not be approached from the other side
arbitrarily closely.

The main workhorse is `sign_const_Icc`; the target statement is then obtained from the purely real
result `exists_half_level_param_real` applied to `f = L ∘ γ`.
-/

/-- A continuous real function which never takes the value `a` on a closed interval assumes values
all `< a` or all `> a` at its endpoints.  (Intermediate value theorem.) -/
private lemma sign_const_Icc {f : ℝ → ℝ} {a x y : ℝ} (hxy : x ≤ y)
    (hcont : ContinuousOn f (Set.Icc x y)) (hne : ∀ z ∈ Set.Icc x y, f z ≠ a) :
    (f x < a ↔ f y < a) := by
  constructor
  · intro hx
    by_contra hy
    push_neg at hy
    have hmem : a ∈ Set.Icc (f x) (f y) := ⟨le_of_lt hx, hy⟩
    obtain ⟨z, hz, hza⟩ := (intermediate_value_Icc hxy hcont) hmem
    exact hne z hz hza
  · intro hy
    by_contra hx
    push_neg at hx
    have hmem : a ∈ Set.Icc (f y) (f x) := ⟨le_of_lt hy, hx⟩
    obtain ⟨z, hz, hza⟩ := (intermediate_value_Icc' hxy hcont) hmem
    exact hne z hz hza

/-- **Constancy on the left half.**  If `f` is continuous, `t₀` is the only zero of `f - a` in
`(t₀ - δ₁, t₀ + δ₁)` and `δ < δ₁`, then for every `z ∈ [t₀ - δ, t₀)` the sign of `f z - a` is the
sign of `f (t₀ - δ) - a`; in particular the endpoint sign is the correct side sign. -/
private lemma sign_left {f : ℝ → ℝ} (hf : Continuous f) {a t₀ δ δ₁ : ℝ}
    (hδlt : δ < δ₁) (hiso : ∀ t, f t = a → |t - t₀| < δ₁ → t = t₀) :
    ∀ z ∈ Set.Ico (t₀ - δ) t₀, (f z < a ↔ f (t₀ - δ) < a) := by
  intro z hz
  have hno : ∀ w ∈ Set.Icc (t₀ - δ) z, f w ≠ a := by
    intro w hw hwa
    have hwlt : w < t₀ := lt_of_le_of_lt hw.2 hz.2
    have hwt : w = t₀ := by
      refine hiso w hwa ?_
      have habs : |w - t₀| = t₀ - w := by
        rw [abs_of_nonpos (by linarith)]; ring
      rw [habs]
      linarith [hw.1, hδlt]
    exact absurd hwt (ne_of_lt hwlt)
  exact (sign_const_Icc hz.1 hf.continuousOn hno).symm

/-- **Constancy on the right half.**  Dual to `sign_left`: for every `z ∈ (t₀, t₀ + δ]` the sign of
`f z - a` is the sign of `f (t₀ + δ) - a`. -/
private lemma sign_right {f : ℝ → ℝ} (hf : Continuous f) {a t₀ δ δ₁ : ℝ}
    (hδlt : δ < δ₁) (hiso : ∀ t, f t = a → |t - t₀| < δ₁ → t = t₀) :
    ∀ z ∈ Set.Ioc t₀ (t₀ + δ), (f z < a ↔ f (t₀ + δ) < a) := by
  intro z hz
  have hno : ∀ w ∈ Set.Icc z (t₀ + δ), f w ≠ a := by
    intro w hw hwa
    have hwgt : t₀ < w := lt_of_lt_of_le hz.1 hw.1
    have hwt : w = t₀ := by
      refine hiso w hwa ?_
      have habs : |w - t₀| = w - t₀ := abs_of_nonneg (by linarith)
      rw [habs]
      linarith [hw.2, hδlt]
    exact absurd hwt (ne_of_gt hwgt)
  exact sign_const_Icc hz.2 hf.continuousOn hno

/-- The purely real content of `exists_half_level_param`: for a continuous `f : ℝ → ℝ` whose only
zero of `f - a` in `(t₀ - δ₁, t₀ + δ₁)` is `t₀`, and which takes values on both sides of `a`
arbitrarily close to `t₀`, the level `a` splits the closed interval `[t₀ - δ, t₀ + δ]`,
`0 < δ < δ₁`, into a positive and a negative half. -/
private theorem exists_half_level_param_real {f : ℝ → ℝ} (hf : Continuous f) {a t₀ δ₁ δ : ℝ}
    (ht₀ : f t₀ = a)
    (hiso : ∀ t, f t = a → |t - t₀| < δ₁ → t = t₀)
    (hpos : ∀ ε > 0, ∃ t', |t' - t₀| < ε ∧ a < f t')
    (hneg : ∀ ε > 0, ∃ t', |t' - t₀| < ε ∧ f t' < a)
    (hδ : 0 < δ) (hδlt : δ < δ₁) :
    ∃ d : ℝ, |d| = δ ∧ ∀ t, |t - t₀| ≤ δ → (a ≤ f t ↔ 0 ≤ (t - t₀) * d) := by
  have hleft := sign_left hf hδlt hiso
  have hright := sign_right hf hδlt hiso
  -- Points above resp. below `a` inside `(t₀ - δ, t₀ + δ)`.
  obtain ⟨tp, htpabs, htppos⟩ := hpos δ hδ
  obtain ⟨tn, htnabs, htnneg⟩ := hneg δ hδ
  -- `tp` forces one of the two sides to be `≤ a`; `tn` forces one to be `< a`.
  have hpos_side : ¬ (f (t₀ - δ) < a) ∨ ¬ (f (t₀ + δ) < a) := by
    rcases lt_trichotomy tp t₀ with hlt | heq | hgt
    · left; intro hsL
      have htpmem : tp ∈ Set.Ico (t₀ - δ) t₀ :=
        ⟨by have := (abs_lt.mp htpabs).1; linarith, hlt⟩
      have := (hleft tp htpmem).mpr hsL
      linarith
    · exfalso; rw [heq] at htppos; rw [ht₀] at htppos; exact absurd htppos (lt_irrefl a)
    · right; intro hsR
      have htpmem : tp ∈ Set.Ioc t₀ (t₀ + δ) :=
        ⟨hgt, by have := (abs_lt.mp htpabs).2; linarith⟩
      have := (hright tp htpmem).mpr hsR
      linarith
  have hneg_side : f (t₀ - δ) < a ∨ f (t₀ + δ) < a := by
    rcases lt_trichotomy tn t₀ with hlt | heq | hgt
    · left
      have htnmem : tn ∈ Set.Ico (t₀ - δ) t₀ :=
        ⟨by have := (abs_lt.mp htnabs).1; linarith, hlt⟩
      exact (hleft tn htnmem).mp htnneg
    · exfalso; rw [heq] at htnneg; rw [ht₀] at htnneg; exact absurd htnneg (lt_irrefl a)
    · right
      have htnmem : tn ∈ Set.Ioc t₀ (t₀ + δ) :=
        ⟨hgt, by have := (abs_lt.mp htnabs).2; linarith⟩
      exact (hright tn htnmem).mp htnneg
  -- The two sides have opposite signs, encoded as `sR ↔ ¬ sL`, where
  -- `sL = (f (t₀ - δ) < a)` and `sR = (f (t₀ + δ) < a)`.
  have hnotboth : ¬ (f (t₀ - δ) < a ∧ f (t₀ + δ) < a) := by
    rintro ⟨h1, h2⟩
    rcases hpos_side with h | h
    · exact h h1
    · exact h h2
  have hsRiff : (f (t₀ + δ) < a) ↔ ¬ (f (t₀ - δ) < a) := by
    constructor
    · intro h1 h2; exact hnotboth ⟨h2, h1⟩
    · intro h
      rcases hneg_side with h1 | h2
      · exact absurd h1 h
      · exact h2
  -- The outer normal: `-δ` when the right side is negative, `+δ` otherwise.
  set d : ℝ := if f (t₀ + δ) < a then -δ else δ with hddef
  have hdabs : |d| = δ := by
    rw [hddef]; split_ifs with _
    · rw [abs_neg, abs_of_pos hδ]
    · rw [abs_of_pos hδ]
  have hdle : d ≤ 0 ↔ ¬ (f (t₀ - δ) < a) := by
    rw [hddef]; split_ifs with h
    · rw [hsRiff] at h
      exact ⟨fun _ => h, fun _ => by linarith⟩
    · exact ⟨fun h' => absurd h' (not_le.mpr hδ),
        fun h2 => absurd (hsRiff.mpr h2) h⟩
  have hdge : 0 ≤ d ↔ ¬ (f (t₀ + δ) < a) := by
    rw [hddef]; split_ifs with h
    · exact ⟨fun h' => absurd h' (not_le.mpr (by linarith)),
        fun h2 => absurd h h2⟩
    · exact ⟨fun _ => h, fun _ => by linarith⟩
  refine ⟨d, hdabs, ?_⟩
  intro t ht
  rcases eq_or_ne t t₀ with heq | hne
  · -- the centre: both sides are trivially true
    rw [heq, ht₀]; simp
  · -- off-centre: `f t ≠ a`, and the sign of `f t - a` matches the corresponding half
    have hft : f t ≠ a := fun hcon => hne (hiso t hcon (lt_of_le_of_lt ht hδlt))
    have htab : -δ ≤ t - t₀ ∧ t - t₀ ≤ δ := abs_le.mp ht
    rcases lt_trichotomy t t₀ with hlt | heq2 | hgt
    · -- `t` on the left
      have htmem : t ∈ Set.Ico (t₀ - δ) t₀ := ⟨by linarith [htab.1], hlt⟩
      have hlt' : f t < a ↔ f (t₀ - δ) < a := hleft t htmem
      have hle : a ≤ f t ↔ ¬ (f (t₀ - δ) < a) := by
        rw [← hlt']; simp only [not_lt]
      have hmul : 0 ≤ (t - t₀) * d ↔ d ≤ 0 := by
        have hx : t - t₀ < 0 := by linarith
        constructor
        · intro hh
          by_contra hc
          push_neg at hc
          have : (t - t₀) * d < 0 := mul_neg_of_neg_of_pos hx hc
          linarith
        · intro hh
          exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt hx) hh
      rw [hle, hmul]
      exact hdle.symm
    · exact absurd heq2 hne
    · -- `t` on the right
      have htmem : t ∈ Set.Ioc t₀ (t₀ + δ) := ⟨hgt, by linarith [htab.2]⟩
      have hrt : f t < a ↔ f (t₀ + δ) < a := hright t htmem
      have hle : a ≤ f t ↔ ¬ (f (t₀ + δ) < a) := by
        rw [← hrt]; simp only [not_lt]
      have hmul : 0 ≤ (t - t₀) * d ↔ 0 ≤ d := by
        have hx : 0 < t - t₀ := by linarith
        exact mul_nonneg_iff_of_pos_left hx
      rw [hle, hmul]
      exact hdge.symm

/-- **The up-half of a level set along a curve at an isolated transverse crossing.**  Let `γ : ℝ → X`
be continuous and `L : X → ℝ` continuous with `L (γ t₀) = a`.  Suppose `t₀` is an *isolated* point of
the level set `{t | L (γ t) = a}` at scale `δ₁ > 0`, and suppose the level `L ∘ γ` takes values both
above and below `a` in every neighbourhood of `t₀`.  Then the level set near `t₀` is one-sided: for
every `0 < δ < δ₁` there is `d` with `|d| = δ` such that, on `[t₀ - δ, t₀ + δ]`, the condition
`a ≤ L (γ t)` is equivalent to `t` lying on the `d`-side of `t₀`. -/
theorem exists_half_level_param {X : Type*} [TopologicalSpace X] {γ : ℝ → X} (hγ : Continuous γ)
    {L : X → ℝ} (hL : Continuous L) {a t₀ δ₁ δ : ℝ} (hδ₁ : 0 < δ₁)
    (ht₀ : L (γ t₀) = a)
    (hiso : ∀ t : ℝ, L (γ t) = a → |t - t₀| < δ₁ → t = t₀)
    (hpos : ∀ ε : ℝ, 0 < ε → ∃ t' : ℝ, |t' - t₀| < ε ∧ a < L (γ t'))
    (hneg : ∀ ε : ℝ, 0 < ε → ∃ t' : ℝ, |t' - t₀| < ε ∧ L (γ t') < a)
    (hδ : 0 < δ) (hδlt : δ < δ₁) :
    ∃ d : ℝ, |d| = δ ∧ ∀ t : ℝ, |t - t₀| ≤ δ → (a ≤ L (γ t) ↔ 0 ≤ (t - t₀) * d) := by
  exact exists_half_level_param_real (hL.comp hγ) ht₀ hiso hpos hneg hδ hδlt

end Work.EpsW
