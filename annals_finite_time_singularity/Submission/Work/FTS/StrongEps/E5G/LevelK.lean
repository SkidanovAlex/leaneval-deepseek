/-
Copyright: work module for the Elgindi finite-time singularity project.

# `E5G/LevelK.lean` — the `ℋ^k`-bookkeeping at an *arbitrary* level `k`

The two sibling files

* `Work.FTS.StrongEps.LocUnif.mixed_sq_le_HkIntegrand` (`(D_z^jD_θ^i F)² ≤ HkIntegrand α 6 F`), and
* `Work.FTS.StrongEps.LocUnif.rect_integral_le_of_pointwise`
  (`∫_rect g² ≤ K · HkSq α 6 F` from a pointwise bound),

are both stated with the level `6` hard-coded (they were built for the `ℋ⁶` chapter).  The
level-`4` Morrey estimate `morrey_four` needs the same two facts at level `4`, so this file
provides them at an arbitrary level `k`:

* `mixed_sq_le_HkIntegrand_level α k hα j i hji` — the square of a single mixed derivative of
  order `i + j ≤ k` is dominated pointwise by `HkIntegrand α k F` (the mechanism is the trivial
  one: `HkIntegrand` is a sum of squares and every weight occurring in it is `≥ 1` on
  `z > 0, sin(2θ) > 0`);
* `rect_integral_le_of_pointwise_level k` — if `g²` is dominated by `K · HkIntegrand α k F` on a
  rectangle inside the open quadrant, then the iterated integral of `g²` over the rectangle is
  dominated by `K · HkSq α k F`.

Both proofs are the verbatim transcription of the level-`6` originals with `6` replaced by `k`;
everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

set_option autoImplicit false

/-! ## The weights are `≥ 1` on the region `z > 0`, `sin(2θ) > 0` -/

private lemma one_le_w_of_pos {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  have hz2 : 0 < z ^ 2 := by positivity
  rw [Work.Spaces.w, one_le_div hz2]
  calc z ^ 2 ≤ (1 + z) ^ 2 := pow_le_pow_left₀ (le_of_lt hz) (by linarith) 2
    _ = (1 + z) ^ 2 := rfl

private lemma one_le_wTheta {α θ : ℝ} (hα : 0 < α) (hsin : 0 < Real.sin (2 * θ)) :
    1 ≤ Work.Spaces.wTheta α θ := by
  have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hexp : -(Work.Spaces.gam α / 2) ≤ 0 := by
    have h := Work.Spaces.gam_pos hα
    linarith
  have h := Real.rpow_le_rpow_of_exponent_ge hsin hsin1 hexp
  rwa [Real.rpow_zero] at h

private lemma one_le_Wt {α z θ : ℝ} (hα : 0 < α) (hz : 0 < z)
    (hsin : 0 < Real.sin (2 * θ)) : 1 ≤ Work.Spaces.Wt α z θ := by
  have h1 : 1 ≤ Work.Spaces.w z := one_le_w_of_pos hz
  have h2 : 1 ≤ Work.Spaces.wTheta α θ := one_le_wTheta hα hsin
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ Work.Spaces.w z * Work.Spaces.wTheta α θ :=
        mul_le_mul h1 h2 zero_le_one (le_trans zero_le_one h1)
    _ = Work.Spaces.Wt α z θ := rfl

private lemma one_le_w_div_sin_eta {z θ : ℝ} (hz : 0 < z) (hsin : 0 < Real.sin (2 * θ)) :
    1 ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hspos : 0 < Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hsin _
  have hsle : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one hsin.le hs1 (by norm_num [Work.Spaces.eta])
  rw [one_le_div hspos]
  have h1 : 1 ≤ Work.Spaces.w z := one_le_w_of_pos hz
  linarith

private lemma sq_le_sq_mul_of_one_le {A M : ℝ} (hM : 1 ≤ M) : A ^ 2 ≤ (A * M) ^ 2 := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have h : |A| ≤ |A * M| := by
    rw [abs_mul, abs_of_pos hMpos]
    nlinarith [abs_nonneg A]
  exact sq_le_sq.mpr h

/-! ## A single mixed derivative at level `k` -/

/-- The square of a single mixed derivative `D_z^jD_θ^i F` of order `i + j ≤ k` is dominated
pointwise by the `ℋ^k`-integrand of `F`, on the region `z > 0`, `0 < sin(2θ) ≤ 1`. -/
theorem mixed_sq_le_HkIntegrand_level (α : ℝ) (k : ℕ) (hα : 0 < α) (j i : ℕ) (hji : j + i ≤ k)
    {F : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z) (hsin : 0 < Real.sin (2 * θ)) :
    (Work.Spaces.mixed j i F z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k F z θ := by
  by_cases hi1 : 1 ≤ i
  · have h1 : 1 ≤ Work.Spaces.Wt α z θ := one_le_Wt hα hz hsin
    have h2 : (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α k F z θ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α k F z θ i j hi1 (by omega)
    exact le_trans (sq_le_sq_mul_of_one_le h1) h2
  · have hi0 : i = 0 := by omega
    have h3 : (Work.Spaces.DzIter j F z θ) ^ 2
        ≤ (Work.Spaces.DzIter j F z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 :=
      sq_le_sq_mul_of_one_le (one_le_w_div_sin_eta hz hsin)
    have h4 : (Work.Spaces.DzIter j F z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α k F z θ :=
      Work.Spaces.sq_le_HkIntegrand_z α k F z θ j (by omega)
    have h5 : Work.Spaces.mixed j i F = Work.Spaces.DzIter j F := by
      rw [hi0]
      simp
    rw [h5]
    exact le_trans h3 h4

/-! ## The rectangle integral comparison at level `k` -/

/-- If `g²` is dominated pointwise on the rectangle `[a,b] × [c,d]` (`⊆ (0,∞) × (0,π/2)`) by
`K` times the `ℋ^k`-integrand of `F`, then the iterated integral of `g²` over the rectangle is
dominated by `K` times the squared `ℋ^k`-norm of `F`. -/
theorem rect_integral_le_of_pointwise_level {a b c d K α : ℝ} (k : ℕ) (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c) (hd : d < Real.pi / 2) {F g : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k F) (hK : 0 ≤ K)
    (hpt : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      (g z θ) ^ 2 ≤ K * Work.Spaces.HkIntegrand α k F z θ) :
    (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (g z θ) ^ 2) ≤ K * Work.Spaces.HkSq α k F := by
  have hsubz : Set.Icc a b ⊆ Work.Spaces.Iz := fun z hz => le_trans ha.le hz.1
  have hsubθ : Set.Icc c d ⊆ Work.Spaces.Iθ :=
    fun θ hθ => ⟨le_trans hc.le hθ.1, le_trans hθ.2 hd.le⟩
  -- (1) the angular integral at a fixed `z ∈ [a,b]`
  have hinner : ∀ z ∈ Set.Icc a b,
      (∫ θ in Set.Icc c d, (g z θ) ^ 2)
        ≤ K * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ := by
    intro z hz
    have hzIz : z ∈ Work.Spaces.Iz := hsubz hz
    have hInt : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k F z θ) (Set.Icc c d) :=
      (hmem.1 z hzIz).mono_set hsubθ
    have hInt2 : IntegrableOn
        (fun θ => K * Work.Spaces.HkIntegrand α k F z θ) (Set.Icc c d) := hInt.const_mul _
    have hstep1 : (∫ θ in Set.Icc c d, (g z θ) ^ 2)
        ≤ ∫ θ in Set.Icc c d, K * Work.Spaces.HkIntegrand α k F z θ :=
      MeasureTheory.integral_mono_of_nonneg
        (Eventually.of_forall fun θ => sq_nonneg _) hInt2
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          fun θ hθ => hpt z hz θ hθ)
    have hstep2 : (∫ θ in Set.Icc c d, Work.Spaces.HkIntegrand α k F z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ :=
      setIntegral_mono_set (hmem.1 z hzIz)
        (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ)
        (Eventually.of_forall fun θ hθ => hsubθ hθ)
    calc (∫ θ in Set.Icc c d, (g z θ) ^ 2)
        ≤ ∫ θ in Set.Icc c d, K * Work.Spaces.HkIntegrand α k F z θ := hstep1
      _ = K * ∫ θ in Set.Icc c d, Work.Spaces.HkIntegrand α k F z θ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ K * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ :=
          mul_le_mul_of_nonneg_left hstep2 hK
  -- (2) the radial integral
  have houter : (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (g z θ) ^ 2)
      ≤ K * ∫ z in Set.Icc a b, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k F z θ := by
    have hInt : IntegrableOn
        (fun z => K * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
        (Set.Icc a b) := (hmem.2.mono_set hsubz).const_mul _
    calc (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (g z θ) ^ 2)
        ≤ ∫ z in Set.Icc a b, K * ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k F z θ :=
          MeasureTheory.integral_mono_of_nonneg
            (Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _) hInt
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
              fun z hz => hinner z hz)
      _ = K * ∫ z in Set.Icc a b, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k F z θ := MeasureTheory.integral_const_mul _ _
  -- (3) enlarging `[a,b]` to `Iz`
  have hlast : (∫ z in Set.Icc a b, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k F z θ) ≤ Work.Spaces.HkSq α k F := by
    rw [Work.Spaces.HkSq]
    exact setIntegral_mono_set hmem.2
      (Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ)
      (Eventually.of_forall fun z hz => hsubz hz)
  exact le_trans houter (mul_le_mul_of_nonneg_left hlast hK)

end Work.FTS.StrongEps.E5G
