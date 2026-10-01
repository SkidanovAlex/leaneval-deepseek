/-
# ZeroFreeTables — testFn71_defs

Definitions for the test function of Heath-Brown (1992), **Lemma 7.1** — the
`0 < k < 3` branch of the §7 variational problem, and the family from which
HB's Tables 2, 3, 9, 10, 11 are computed (the `θ → 0` limiting case is Lemma 7.2,
already constructed in `testFn72_defs`).

With parameters `0 < θ < π/2`, `λ > 0` put

* `ζ = λ tan θ` (`tf71ζ`),  `γ = θ/ζ` (`tf71γ`);
* `g(t) = λ(1+tan²θ)(cos(ζt) − cos θ)` on `[-γ,γ]`, `0` outside (`tf71g`);
* `f = g ⊛ g` (`tf71conv`), with HB's closed form on `[0,2γ]` (`tf71cf`, and
  `tf71f`, which is the closed form on `[0,2γ]` and `0` outside);
* `F(z) = ∫₀^{2γ} e^{−zt} f(t) dt` (`tf71Fc`).

HB Lemma 7.1 states `f 0 = λ(1+tan²θ)[θ tan θ + 3θ cot θ − 3]`,
`F 0 = 2(1+tan²θ)(1 − θ cot θ)²` and `F(−λ) = 2 tan²θ + 3 − 3θ tan θ − 3θ cot θ`
(all three verified numerically).  This module fixes the notations and proves the
elementary structural facts (positivity of `g`, continuity, support, `C²` and the
second-derivative bound, the value `f 0`), so that the crux (`f = g ⊛ g` on
`[0,2γ]`) and the transcendental value lemmas can be delegated.
-/
import Mathlib

noncomputable section
open scoped Real
namespace Work.ZeroFreeTables

/-- HB §7, Lemma 7.1: `ζ = λ tan θ`. -/
def tf71ζ (θ lam : ℝ) : ℝ := lam * Real.tan θ

/-- HB §7, Lemma 7.1: `γ = θ/ζ`. -/
def tf71γ (θ lam : ℝ) : ℝ := θ / tf71ζ θ lam

/-- The closed form for `f = g ⊛ g` of HB Lemma 7.1 (valid on `[0,2γ]`). -/
def tf71cf (θ lam : ℝ) (x : ℝ) : ℝ :=
  lam * (1 + Real.tan θ ^ 2) *
    ( lam * (1 + Real.tan θ ^ 2) * (tf71γ θ lam - x/2) * Real.cos (tf71ζ θ lam * x)
      + lam * (2 * tf71γ θ lam - x)
      + Real.sin (2*θ - tf71ζ θ lam * x) / Real.sin (2*θ)
      - 2 * (1 + Real.sin (θ - tf71ζ θ lam * x) / Real.sin θ) )

/-- HB Lemma 7.1's auxiliary `g`: `λ(1+tan²θ)(cos ζt − cos θ)` on `[-γ,γ]`, `0` outside. -/
def tf71g (θ lam : ℝ) (t : ℝ) : ℝ :=
  if |t| ≤ tf71γ θ lam then
    lam * (1 + Real.tan θ ^ 2) * (Real.cos (tf71ζ θ lam * t) - Real.cos θ)
  else 0

/-- HB Lemma 7.1's test function: the closed form on `[0,2γ]` (written through
`min · (2γ)`, so that it is manifestly continuous at the right end), `0` elsewhere. -/
def tf71f (θ lam : ℝ) (x : ℝ) : ℝ :=
  if 0 ≤ x then tf71cf θ lam (min x (2 * tf71γ θ lam)) else 0

/-- The convolution `g ⊛ g` over `ℝ`. -/
def tf71conv (θ lam : ℝ) (x : ℝ) : ℝ := ∫ s, tf71g θ lam s * tf71g θ lam (x - s)

/-- The Laplace transform of the test function, for complex arguments. -/
def tf71Fc (θ lam : ℝ) (z : ℂ) : ℂ :=
  ∫ t in (0:ℝ)..(2 * tf71γ θ lam), Complex.exp (-(z * (t:ℂ))) * ((tf71f θ lam t : ℝ) : ℂ)
/-! ## Elementary facts about `ζ`, `γ`, `g` -/

theorem tf71_tan_pos {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) : 0 < Real.tan θ :=
  Real.tan_pos_of_pos_of_lt_pi_div_two hθ0 hθ1

theorem tf71ζ_pos {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    0 < tf71ζ θ lam := mul_pos hlam (tf71_tan_pos hθ0 hθ1)

theorem tf71γ_pos {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    0 < tf71γ θ lam := div_pos hθ0 (tf71ζ_pos hθ0 hθ1 hlam)

theorem tf71ζ_mul_γ {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    tf71ζ θ lam * tf71γ θ lam = θ := by
  rw [tf71γ, mul_div_cancel₀ _ (ne_of_gt (tf71ζ_pos hθ0 hθ1 hlam))]

theorem tf71_lam_mul_γ {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    lam * tf71γ θ lam = θ / Real.tan θ := by
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  have ht : Real.tan θ ≠ 0 := ne_of_gt (tf71_tan_pos hθ0 hθ1)
  have hlt : lam * Real.tan θ ≠ 0 := mul_ne_zero hlam_ne ht
  rw [tf71γ, tf71ζ]
  field_simp [hlam_ne, ht, hlt]

theorem tf71_sinθ_ne {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) : Real.sin θ ≠ 0 :=
  ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos]))

theorem tf71_sin2θ_ne {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Real.sin (2 * θ) ≠ 0 := by
  apply ne_of_gt
  apply Real.sin_pos_of_pos_of_lt_pi (by linarith)
  linarith

theorem tf71g_nonneg {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    ∀ t : ℝ, 0 ≤ tf71g θ lam t := by
  intro t
  unfold tf71g
  by_cases h : |t| ≤ tf71γ θ lam
  · rw [if_pos h]
    have h1 : |tf71ζ θ lam * t| ≤ θ := by
      rw [abs_mul, abs_of_pos (tf71ζ_pos hθ0 hθ1 hlam)]
      calc tf71ζ θ lam * |t| ≤ tf71ζ θ lam * tf71γ θ lam :=
            mul_le_mul_of_nonneg_left h (le_of_lt (tf71ζ_pos hθ0 hθ1 hlam))
        _ = θ := tf71ζ_mul_γ hθ0 hθ1 hlam
    have h2 : Real.cos θ ≤ Real.cos (tf71ζ θ lam * t) := by
      have hh := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (tf71ζ θ lam * t))
        (by linarith [Real.pi_pos] : θ ≤ Real.pi) h1
      rwa [Real.cos_abs] at hh
    have h3 : 0 ≤ lam * (1 + Real.tan θ ^ 2) := by positivity
    exact mul_nonneg h3 (by linarith)
  · rw [if_neg h]

theorem tf71g_even (θ lam : ℝ) : ∀ t : ℝ, tf71g θ lam (-t) = tf71g θ lam t := by
  intro t
  unfold tf71g
  rw [abs_neg]
  congr 2
  rw [mul_neg, Real.cos_neg]

theorem tf71g_cont {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    Continuous (tf71g θ lam) := by
  have hE : Continuous
      (fun x => lam * (1 + Real.tan θ ^ 2) * (Real.cos (tf71ζ θ lam * x) - Real.cos θ)) := by
    fun_prop
  have hcomp : Continuous (fun t =>
      lam * (1 + Real.tan θ ^ 2) *
        (Real.cos (tf71ζ θ lam * (min |t| (tf71γ θ lam))) - Real.cos θ)) :=
    hE.comp (continuous_abs.min continuous_const)
  refine hcomp.congr ?_
  intro t
  unfold tf71g
  have hζγ : tf71ζ θ lam * tf71γ θ lam = θ := tf71ζ_mul_γ hθ0 hθ1 hlam
  by_cases h : |t| ≤ tf71γ θ lam
  · rw [if_pos h, min_eq_left h]
    have hkey : tf71ζ θ lam * |t| = |tf71ζ θ lam * t| := by
      rw [abs_mul, abs_of_pos (tf71ζ_pos hθ0 hθ1 hlam)]
    rw [hkey, Real.cos_abs]
  · rw [if_neg h, min_eq_right (le_of_lt (not_le.mp h))]
    rw [hζγ, sub_self, mul_zero]

theorem tf71g_supp {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    ∀ t : ℝ, tf71γ θ lam ≤ |t| → tf71g θ lam t = 0 := by
  intro t ht
  unfold tf71g
  have hζγ : tf71ζ θ lam * tf71γ θ lam = θ := tf71ζ_mul_γ hθ0 hθ1 hlam
  by_cases h : |t| ≤ tf71γ θ lam
  · have hte : |t| = tf71γ θ lam := le_antisymm h ht
    rw [if_pos h]
    have hcos : Real.cos (tf71ζ θ lam * t) = Real.cos θ := by
      have h1 : |tf71ζ θ lam * t| = θ := by
        rw [abs_mul, abs_of_pos (tf71ζ_pos hθ0 hθ1 hlam), hte, hζγ]
      rw [← Real.cos_abs (tf71ζ θ lam * t), h1]
    rw [hcos, sub_self, mul_zero]
  · rw [if_neg h]


/-! ## Elementary facts about `f` -/

theorem tf71cf_cont (θ lam : ℝ) : Continuous (tf71cf θ lam) := by
  unfold tf71cf; fun_prop

theorem tf71cf_diff (θ lam : ℝ) : ContDiff ℝ 2 (tf71cf θ lam) := by
  unfold tf71cf; fun_prop

theorem tf71cf_at_twoγ {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    tf71cf θ lam (2 * tf71γ θ lam) = 0 := by
  have hζγ : tf71ζ θ lam * tf71γ θ lam = θ := tf71ζ_mul_γ hθ0 hθ1 hlam
  have hz : tf71ζ θ lam * (2 * tf71γ θ lam) = 2 * θ := by
    rw [show tf71ζ θ lam * (2 * tf71γ θ lam)
          = 2 * (tf71ζ θ lam * tf71γ θ lam) from by ring, hζγ]
  have hsinθ : Real.sin θ ≠ 0 := tf71_sinθ_ne hθ0 hθ1
  simp only [tf71cf, hz]
  rw [show 2 * θ - 2 * θ = 0 from by ring, Real.sin_zero, zero_div,
      show θ - 2 * θ = -θ from by ring, Real.sin_neg,
      show tf71γ θ lam - 2 * tf71γ θ lam / 2 = 0 from by ring,
      show 2 * tf71γ θ lam - 2 * tf71γ θ lam = 0 from by ring]
  simp [hsinθ]

theorem tf71f_cont (θ lam : ℝ) : ContinuousOn (tf71f θ lam) (Set.Ici 0) := by
  have hh : Continuous (fun x => tf71cf θ lam (min x (2 * tf71γ θ lam))) :=
    (tf71cf_cont θ lam).comp (continuous_id.min continuous_const)
  refine hh.continuousOn.congr ?_
  intro x hx
  simp only [Set.mem_Ici] at hx
  unfold tf71f
  rw [if_pos hx]

theorem tf71f_supp {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    ∀ x : ℝ, 2 * tf71γ θ lam ≤ x → tf71f θ lam x = 0 := by
  intro x hx
  have hcf := tf71cf_at_twoγ hθ0 hθ1 hlam
  have hγ := tf71γ_pos hθ0 hθ1 hlam
  unfold tf71f
  rw [if_pos (le_trans (by linarith) hx), min_eq_right hx]
  exact hcf

theorem tf71f_diff (θ lam : ℝ) (hγ : 0 < tf71γ θ lam) :
    ContDiffOn ℝ 2 (tf71f θ lam) (Set.Ioo 0 (2 * tf71γ θ lam)) := by
  refine (tf71cf_diff θ lam).contDiffOn.congr (fun x hx => ?_)
  unfold tf71f
  rw [if_pos hx.1.le, min_eq_left hx.2.le]

theorem tf71f_bound (θ lam : ℝ) (hγ : 0 < tf71γ θ lam) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ Set.Ioo (0:ℝ) (2 * tf71γ θ lam),
      ‖iteratedDeriv 2 (tf71f θ lam) x‖ ≤ B := by
  have hcont : Continuous (iteratedDeriv 2 (tf71cf θ lam)) :=
    (tf71cf_diff θ lam).continuous_iteratedDeriv 2 le_rfl
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 2 * tf71γ θ lam))
    |>.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have hs : IsOpen (Set.Ioo (0:ℝ) (2 * tf71γ θ lam)) := isOpen_Ioo
  have hcg : Set.EqOn (tf71f θ lam) (tf71cf θ lam) (Set.Ioo (0:ℝ) (2 * tf71γ θ lam)) := by
    intro z hz
    unfold tf71f
    rw [if_pos hz.1.le, min_eq_left hz.2.le]
  have hEq : iteratedDeriv 2 (tf71f θ lam) x = iteratedDeriv 2 (tf71cf θ lam) x := by
    rw [← iteratedDerivWithin_of_isOpen (f := tf71f θ lam) (n := 2) hs hx,
        iteratedDerivWithin_congr hcg hx,
        iteratedDerivWithin_of_isOpen (n := 2) hs hx]
  rw [hEq]
  exact (hC x (Set.Ioo_subset_Icc_self hx)).trans (le_max_left _ _)

theorem tf71f_at_zero {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    tf71f θ lam 0 = lam * (1 + Real.tan θ ^ 2) *
      (θ * Real.tan θ + 3 * θ * (Real.tan θ)⁻¹ - 3) := by
  have hγ := tf71γ_pos hθ0 hθ1 hlam
  have hsinθ : Real.sin θ ≠ 0 := tf71_sinθ_ne hθ0 hθ1
  have hsin2θ : Real.sin (2*θ) ≠ 0 := tf71_sin2θ_ne hθ0 hθ1
  have hlt : lam * tf71γ θ lam = θ / Real.tan θ := tf71_lam_mul_γ hθ0 hθ1 hlam
  have ht : Real.tan θ ≠ 0 := ne_of_gt (tf71_tan_pos hθ0 hθ1)
  unfold tf71f
  rw [if_pos le_rfl, min_eq_left (by linarith : (0:ℝ) ≤ 2 * tf71γ θ lam)]
  unfold tf71cf
  simp only [mul_zero, sub_zero, Real.cos_zero, Real.sin_zero, zero_div, one_mul, mul_one]
  rw [div_self hsin2θ, div_self hsinθ]
  have h1 : lam * (1 + Real.tan θ ^ 2) * tf71γ θ lam
      = (1 + Real.tan θ ^ 2) * (θ / Real.tan θ) := by rw [← hlt]; ring
  have h2 : lam * (2 * tf71γ θ lam) = 2 * (θ / Real.tan θ) := by rw [← hlt]; ring
  rw [h1, h2]
  field_simp
  ring

end Work.ZeroFreeTables
