import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BoseB1Cube.chiFibreDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The one-dimensional wing comparison for the `chiSmall` fibre kernel

`chiFibreK M A B t = (ζ(A − t)·ζ(B − t))^M` with `ζ = zeta1d` the cosine profile
(`ζ(y) = cos (π y)` on `|y| ≤ 1/2` and `0` outside).  `ζ` is a function of `|y|`
and antitone in it.  On the wing `[ν − 2δ', ν]` — which lies entirely on the
increasing branch of both factors, by `|A|, |B| ≤ ν − 1/2` and `δ' ≤ 1/8` — the
kernel is therefore antitone, and so is its reflection `t ↦ chiFibreK M A B (−t)`.

Hence the two "inner" integrals of the statement (the wings of length `δ'` of the
sum `h := K + K ∘ (−·)`, written as the pair of wings at distance `δ'` from `0`)
are dominated by the two "outer" ones (the same sum on the wing one step further
out), which is exactly the claimed inequality.

The auxiliary facts are proved in the order

* `zeta1d_le_of_abs_le` — `ζ` is antitone in `|·|`;
* `antitoneOn_zeta1d_sub`, `antitoneOn_zeta1d_add` — the two one-sided shifted
  profiles are antitone on the wing;
* `antitoneOn_mul_of_nonneg`, `antitoneOn_pow_of_nonneg` — products and powers of
  nonnegative antitone functions are antitone;
* `antitoneOn_chiFibreK`, `antitoneOn_chiFibreK_neg` — the kernel and its
  reflection;
* `intervalIntegral_antitone_wing` — for antitone `h` on `[m − δ, m + δ]`,
  `∫_m^{m+δ} h ≤ ∫_{m−δ}^m h` (the right wing of length `δ` dominates the left one).

This is the `e_j ≤ d_j` step of `Submission/Work/BoseB1Cube/chiFibreGood.lean`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseB1Cube

open Submission.BoseGases

/-! ### `ζ` is antitone in the distance -/

/-- The cosine profile is antitone in `|·|`. -/
lemma zeta1d_le_of_abs_le {x y : ℝ} (h : |x| ≤ |y|) : zeta1d y ≤ zeta1d x := by
  by_cases hy : |y| ≤ 1 / 2
  · have hx : |x| ≤ 1 / 2 := le_trans h hy
    rw [zeta1d_of_abs_le hy, zeta1d_of_abs_le hx, cos_pi_mul_eq_cos_pi_abs y,
      cos_pi_mul_eq_cos_pi_abs x]
    refine Real.antitoneOn_cos ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_
    · positivity
    · have h1 : |x| ≤ 1 := by linarith [abs_nonneg x]
      nlinarith [Real.pi_pos]
    · positivity
    · have h1 : |y| ≤ 1 := by linarith [abs_nonneg y]
      nlinarith [Real.pi_pos]
    · exact mul_le_mul_of_nonneg_left h (le_of_lt Real.pi_pos)
  · rw [zeta1d_of_one_half_lt (lt_of_not_ge hy)]
    exact zeta1d_nonneg x

/-! ### The shifted profiles are antitone on the wing -/

/-- On the wing `[a − δ, a + δ]`, which for `|A| ≤ (a + δ) − 1/2` and `δ ≤ 1/8` lies on
the increasing branch of `ζ`, the shifted profile `t ↦ ζ(A − t)` is antitone. -/
lemma antitoneOn_zeta1d_sub {A a δ : ℝ} (hA : |A| ≤ (a + δ) - 1 / 2) (hδ : δ ≤ 1 / 8) :
    AntitoneOn (fun t : ℝ => zeta1d (A - t)) (Set.Icc (a - δ) (a + δ)) := by
  intro t₁ ht₁ t₂ ht₂ h12
  have hA' : A ≤ (a + δ) - 1 / 2 := (abs_le.mp hA).2
  have hneg₁ : A - t₁ < 0 := by
    obtain ⟨h1, _⟩ := ht₁
    linarith
  have hneg₂ : A - t₂ < 0 := by linarith
  have hle : |A - t₁| ≤ |A - t₂| := by
    rw [abs_of_neg hneg₁, abs_of_neg hneg₂]
    linarith
  exact zeta1d_le_of_abs_le hle

/-- On the wing `[a − δ, a + δ]`, the reflected shifted profile `t ↦ ζ(A + t)` is
antitone: the wing lies on the decreasing branch of `ζ`. -/
lemma antitoneOn_zeta1d_add {A a δ : ℝ} (hA : |A| ≤ (a + δ) - 1 / 2) (hδ : δ ≤ 1 / 8) :
    AntitoneOn (fun t : ℝ => zeta1d (A + t)) (Set.Icc (a - δ) (a + δ)) := by
  intro t₁ ht₁ t₂ ht₂ h12
  have hA' : -((a + δ) - 1 / 2) ≤ A := (abs_le.mp hA).1
  have hpos₁ : 0 < A + t₁ := by
    obtain ⟨h1, _⟩ := ht₁
    linarith
  have hpos₂ : 0 < A + t₂ := by
    obtain ⟨_, h2⟩ := ht₂
    linarith
  have hle : |A + t₁| ≤ |A + t₂| := by
    rw [abs_of_pos hpos₁, abs_of_pos hpos₂]
    linarith
  exact zeta1d_le_of_abs_le hle

/-! ### Products and powers of nonnegative antitone functions -/

/-- A product of two nonnegative antitone functions is antitone. -/
lemma antitoneOn_mul_of_nonneg {f g : ℝ → ℝ} {s : Set ℝ} (hf : AntitoneOn f s)
    (hg : AntitoneOn g s) (hf0 : ∀ x ∈ s, 0 ≤ f x) (hg0 : ∀ x ∈ s, 0 ≤ g x) :
    AntitoneOn (fun x => f x * g x) s := by
  intro x hx y hy hxy
  exact mul_le_mul (hf hx hy hxy) (hg hx hy hxy) (hg0 y hy) (hf0 x hx)

/-- A nonnegative power of a nonnegative antitone function is antitone. -/
lemma antitoneOn_pow_of_nonneg {f : ℝ → ℝ} {s : Set ℝ} (hf : AntitoneOn f s)
    (hf0 : ∀ x ∈ s, 0 ≤ f x) (n : ℕ) : AntitoneOn (fun x => f x ^ n) s := by
  intro x hx y hy hxy
  exact pow_le_pow_left₀ (hf0 y hy) (hf hx hy hxy) n

/-! ### The fibre kernel and its reflection -/

/-- The one-dimensional fibre kernel is antitone on the wing. -/
lemma antitoneOn_chiFibreK {M : ℕ} {A B a δ : ℝ} (hA : |A| ≤ (a + δ) - 1 / 2)
    (hB : |B| ≤ (a + δ) - 1 / 2) (hδ : δ ≤ 1 / 8) :
    AntitoneOn (fun t : ℝ => chiFibreK M A B t) (Set.Icc (a - δ) (a + δ)) := by
  have h1 := antitoneOn_zeta1d_sub (A := A) hA hδ
  have h2 := antitoneOn_zeta1d_sub (A := B) hB hδ
  have hmul := antitoneOn_mul_of_nonneg h1 h2 (fun t _ => zeta1d_nonneg (A - t))
    (fun t _ => zeta1d_nonneg (B - t))
  have hpow := antitoneOn_pow_of_nonneg hmul
    (fun t _ => mul_nonneg (zeta1d_nonneg (A - t)) (zeta1d_nonneg (B - t))) M
  simpa [chiFibreK] using hpow

/-- The reflection `t ↦ chiFibreK M A B (−t)` of the fibre kernel is antitone on the wing. -/
lemma antitoneOn_chiFibreK_neg {M : ℕ} {A B a δ : ℝ} (hA : |A| ≤ (a + δ) - 1 / 2)
    (hB : |B| ≤ (a + δ) - 1 / 2) (hδ : δ ≤ 1 / 8) :
    AntitoneOn (fun t : ℝ => chiFibreK M A B (-t)) (Set.Icc (a - δ) (a + δ)) := by
  have h1 := antitoneOn_zeta1d_add (A := A) hA hδ
  have h2 := antitoneOn_zeta1d_add (A := B) hB hδ
  have hmul := antitoneOn_mul_of_nonneg h1 h2 (fun t _ => zeta1d_nonneg (A + t))
    (fun t _ => zeta1d_nonneg (B + t))
  have hpow := antitoneOn_pow_of_nonneg hmul
    (fun t _ => mul_nonneg (zeta1d_nonneg (A + t)) (zeta1d_nonneg (B + t))) M
  simpa [chiFibreK] using hpow

/-! ### The integral comparison for an antitone function -/

/-- **Wing comparison.**  For a function antitone on `[m − δ, m + δ]` with `δ ≥ 0`,
the integral over the right wing `[m, m + δ]` is dominated by the integral over the
left wing `[m − δ, m]` — this is the shift `∫_{m−δ}^{m} h = ∫_{m}^{m+δ} h(· − δ)`
plus the pointwise bound `h x ≤ h (x − δ)`. -/
lemma intervalIntegral_antitone_wing {h : ℝ → ℝ} {m δ : ℝ} (hδ : 0 ≤ δ)
    (hm : AntitoneOn h (Set.Icc (m - δ) (m + δ))) :
    ∫ x in m..(m + δ), h x ≤ ∫ x in (m - δ)..m, h x := by
  have hmono₁ : AntitoneOn h (Set.Icc m (m + δ)) :=
    hm.mono (Set.Icc_subset_Icc_left (by linarith : m - δ ≤ m))
  have hmono₂ : AntitoneOn (fun x : ℝ => h (x - δ)) (Set.Icc m (m + δ)) := by
    intro x hx y hy hxy
    simp only [Set.mem_Icc] at hx hy
    exact hm ⟨by linarith [hx.1], by linarith [hx.2, hδ]⟩
      ⟨by linarith [hy.1], by linarith [hy.2, hδ]⟩ (by linarith)
  have hInt₁ : IntervalIntegrable h volume m (m + δ) := by
    have h' : AntitoneOn h (Set.uIcc m (m + δ)) := by
      rwa [Set.uIcc_of_le (by linarith : m ≤ m + δ)]
    exact h'.intervalIntegrable
  have hInt₂ : IntervalIntegrable (fun x : ℝ => h (x - δ)) volume m (m + δ) := by
    have h' : AntitoneOn (fun x : ℝ => h (x - δ)) (Set.uIcc m (m + δ)) := by
      rwa [Set.uIcc_of_le (by linarith : m ≤ m + δ)]
    exact h'.intervalIntegrable
  have hkey : ∫ x in m..(m + δ), h (x - δ) = ∫ x in (m - δ)..m, h x := by
    rw [intervalIntegral.integral_comp_sub_right h δ]
    simp
  rw [← hkey]
  refine intervalIntegral.integral_mono_on (by linarith : m ≤ m + δ) hInt₁ hInt₂ ?_
  intro x hx
  simp only [Set.mem_Icc] at hx
  exact hm ⟨by linarith [hx.1], by linarith [hx.2, hδ]⟩
    ⟨by linarith [hx.1], by linarith [hx.2, hδ]⟩ (by linarith)

/-! ### The target -/

theorem chiFibreWing {M : ℕ} {ν δ' A B : ℝ} (hν : 1 / 2 < ν) (hδ' : 0 < δ')
    (hδ'8 : δ' ≤ 1 / 8) (hA : |A| ≤ ν - 1 / 2) (hB : |B| ≤ ν - 1 / 2) :
    (∫ t in (ν - δ')..ν, Work.BoseB1Cube.chiFibreK M A B t)
        + (∫ t in (-ν)..(-(ν - δ')), Work.BoseB1Cube.chiFibreK M A B t)
      ≤ (∫ t in (ν - 2 * δ')..(ν - δ'), Work.BoseB1Cube.chiFibreK M A B t)
        + (∫ t in (-(ν - δ'))..(-(ν - 2 * δ')), Work.BoseB1Cube.chiFibreK M A B t) := by
  have hδ'0 : 0 ≤ δ' := le_of_lt hδ'
  -- hypotheses for the antitone lemmas with `a := ν - δ'`, `δ := δ'`
  have hA' : |A| ≤ (ν - δ') + δ' - 1 / 2 := by linarith
  have hB' : |B| ≤ (ν - δ') + δ' - 1 / 2 := by linarith
  have hanti₁ := antitoneOn_chiFibreK (M := M) (A := A) (B := B) (a := ν - δ') (δ := δ')
    hA' hB' hδ'8
  have hanti₂ := antitoneOn_chiFibreK_neg (M := M) (A := A) (B := B) (a := ν - δ') (δ := δ')
    hA' hB' hδ'8
  have hsum : AntitoneOn (fun t : ℝ => chiFibreK M A B t + chiFibreK M A B (-t))
      (Set.Icc ((ν - δ') - δ') ((ν - δ') + δ')) := hanti₁.add hanti₂
  have hwing := intervalIntegral_antitone_wing
    (h := fun t : ℝ => chiFibreK M A B t + chiFibreK M A B (-t))
    (m := ν - δ') (δ := δ') hδ'0 hsum
  rw [show (ν - δ') + δ' = ν by ring, show (ν - δ') - δ' = ν - 2 * δ' by ring] at hwing
  -- integrability (the kernel is continuous)
  have hcont : Continuous (fun t : ℝ => chiFibreK M A B t) := by
    unfold chiFibreK
    exact (((zeta1d_continuous.comp (continuous_const.sub continuous_id)).mul
      (zeta1d_continuous.comp (continuous_const.sub continuous_id))).pow M)
  have hInt₁ : IntervalIntegrable (fun t : ℝ => chiFibreK M A B t) volume (ν - δ') ν :=
    hcont.intervalIntegrable (ν - δ') ν
  have hInt₂ : IntervalIntegrable (fun t : ℝ => chiFibreK M A B (-t)) volume (ν - δ') ν :=
    (hcont.comp continuous_neg).intervalIntegrable (ν - δ') ν
  have hInt₃ : IntervalIntegrable (fun t : ℝ => chiFibreK M A B t) volume (ν - 2 * δ') (ν - δ') :=
    hcont.intervalIntegrable (ν - 2 * δ') (ν - δ')
  have hInt₄ : IntervalIntegrable (fun t : ℝ => chiFibreK M A B (-t)) volume (ν - 2 * δ') (ν - δ') :=
    (hcont.comp continuous_neg).intervalIntegrable (ν - 2 * δ') (ν - δ')
  -- reflection of the wings
  have hneg₁ : (∫ t in (-ν)..(-(ν - δ')), chiFibreK M A B t)
      = ∫ t in (ν - δ')..ν, chiFibreK M A B (-t) :=
    (intervalIntegral.integral_comp_neg (f := fun t : ℝ => chiFibreK M A B t)
      (a := ν - δ') (b := ν)).symm
  have hneg₂ : (∫ t in (-(ν - δ'))..(-(ν - 2 * δ')), chiFibreK M A B t)
      = ∫ t in (ν - 2 * δ')..(ν - δ'), chiFibreK M A B (-t) :=
    (intervalIntegral.integral_comp_neg (f := fun t : ℝ => chiFibreK M A B t)
      (a := ν - 2 * δ') (b := ν - δ')).symm
  have e₁ : (∫ t in (ν - δ')..ν, chiFibreK M A B t)
        + (∫ t in (-ν)..(-(ν - δ')), chiFibreK M A B t)
      = ∫ t in (ν - δ')..ν, (chiFibreK M A B t + chiFibreK M A B (-t)) := by
    rw [hneg₁]
    exact (intervalIntegral.integral_add hInt₁ hInt₂).symm
  have e₂ : (∫ t in (ν - 2 * δ')..(ν - δ'),
          (chiFibreK M A B t + chiFibreK M A B (-t)))
      = (∫ t in (ν - 2 * δ')..(ν - δ'), chiFibreK M A B t)
        + (∫ t in (-(ν - δ'))..(-(ν - 2 * δ')), chiFibreK M A B t) := by
    rw [intervalIntegral.integral_add hInt₃ hInt₄, hneg₂]
  calc (∫ t in (ν - δ')..ν, Work.BoseB1Cube.chiFibreK M A B t)
        + (∫ t in (-ν)..(-(ν - δ')), Work.BoseB1Cube.chiFibreK M A B t)
      = ∫ t in (ν - δ')..ν, (chiFibreK M A B t + chiFibreK M A B (-t)) := e₁
    _ ≤ ∫ t in (ν - 2 * δ')..(ν - δ'), (chiFibreK M A B t + chiFibreK M A B (-t)) := hwing
    _ = (∫ t in (ν - 2 * δ')..(ν - δ'), Work.BoseB1Cube.chiFibreK M A B t)
        + (∫ t in (-(ν - δ'))..(-(ν - 2 * δ')), Work.BoseB1Cube.chiFibreK M A B t) := e₂

end Work.BoseB1Cube
