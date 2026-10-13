import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.PhiStar.Honesty.rgB_int_Ioc
import Submission.Work.FTS.PhiStar.Honesty.rgB_int_Ioi
import Submission.Work.FTS.PhiStar.Honesty.rgB_near_le
import Submission.Work.FTS.PhiStar.Honesty.rgB_tail_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The value bound for the tail (growing) Green primitive `rgB`

`rgB α m c z = ∫_{t > z} c t · t^{-p-1} dt` with `p = rgP α m = 2m/α ≥ 8`.  We prove, for
`0 < z ≤ 1` and a source `c` which is controlled by `|c t| ≤ ε t^{3/2}` on `(0,δ]`
(`δ ≤ 1`), `L²`-integrable on `(1,∞)` and with `c t/t²` `L²`-integrable on `(0,1)`:

  `|rgB α m c z| ≤ ε·z^{3/2-p}/(p-3/2) + ½∫_{(0,1)} c²/t⁴ + ½∫_{(1,∞)} c² + δ^{-(2p+1)} + 1`,

which is the tail estimate needed in the honesty/regularity estimates for the radial Green
function.

The proof splits the tail `(z,∞)` at `δ` (near part: the smallness hypothesis; far part:
`(δ,1)` by AM–GM against `c²/t⁴`, `(1,∞)` by AM–GM against `c²` and the integrable weight
`t^{-2p-2}`).  The two value estimates and the two integrability facts are provided by the
sibling modules `rgB_tail_le`, `rgB_near_le`, `rgB_int_Ioi`, `rgB_int_Ioc`; the measurability
interface `aesm_abs_c_of` is proved here.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.PhiStar.Honesty

/-- **Measurability of `|c|`** from the two integrability hypotheses on `c`.  Note that
measurability of `c` itself does *not* follow from measurability of `c²`; only `|c|` is
recovered, and `|c|` is all that the norm of the tail integrand involves. -/
theorem aesm_abs_c_of {c : ℝ → ℝ}
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.AEStronglyMeasurable (fun t : ℝ => |c t|)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have h1 : AEStronglyMeasurable (fun t : ℝ => |c t|) (volume.restrict (Set.Ioo 0 1)) := by
    have h0 : AEStronglyMeasurable (fun t : ℝ => c t ^ 2 / t ^ 4)
        (volume.restrict (Set.Ioo 0 1)) := hnear.1
    have h2 : AEStronglyMeasurable (fun t : ℝ => c t ^ 2 / t ^ 4 * t ^ 4)
        (volume.restrict (Set.Ioo 0 1)) :=
      h0.mul (continuous_id.pow 4).aestronglyMeasurable
    have h3 : AEStronglyMeasurable (fun t : ℝ => c t ^ 2) (volume.restrict (Set.Ioo 0 1)) := by
      refine h2.congr ?_
      rw [Filter.EventuallyEq]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have ht0 : t ≠ 0 := ne_of_gt ht.1
      field_simp
    have h4 : AEStronglyMeasurable (fun t : ℝ => Real.sqrt (c t ^ 2))
        (volume.restrict (Set.Ioo 0 1)) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable h3
    refine h4.congr ?_
    rw [Filter.EventuallyEq]
    exact Eventually.of_forall (fun t => Real.sqrt_sq_eq_abs (c t))
  have h2 : AEStronglyMeasurable (fun t : ℝ => |c t|) (volume.restrict (Set.Ioi 1)) := by
    have h4 : AEStronglyMeasurable (fun t : ℝ => Real.sqrt (c t ^ 2))
        (volume.restrict (Set.Ioi 1)) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hfar.1
    refine h4.congr ?_
    rw [Filter.EventuallyEq]
    exact Eventually.of_forall (fun t => Real.sqrt_sq_eq_abs (c t))
  have hU : AEStronglyMeasurable (fun t : ℝ => |c t|)
      (volume.restrict (Set.Ioo 0 1 ∪ Set.Ioi 1)) :=
    aestronglyMeasurable_union_iff.mpr ⟨h1, h2⟩
  have hsingle : AEStronglyMeasurable (fun t : ℝ => |c t|) (volume.restrict ({1} : Set ℝ)) := by
    refine (stronglyMeasurable_const (b := |c 1|)).aestronglyMeasurable |>.congr ?_
    rw [Filter.EventuallyEq]
    filter_upwards [ae_restrict_mem (measurableSet_singleton 1)] with t ht
    have ht1 : t = 1 := by simpa using ht
    simp [ht1]
  have hfin : AEStronglyMeasurable (fun t : ℝ => |c t|)
      (volume.restrict (Set.Ioo 0 1 ∪ Set.Ioi 1 ∪ {1})) :=
    aestronglyMeasurable_union_iff.mpr ⟨hU, hsingle⟩
  have hset : (Set.Ioo 0 1 ∪ Set.Ioi 1 ∪ {1} : Set ℝ) = Set.Ioi 0 := by
    ext t
    simp only [Set.mem_union, Set.mem_Ioo, Set.mem_Ioi, Set.mem_singleton_iff]
    constructor
    · rintro ((⟨h1, _⟩ | h1) | rfl) <;> linarith
    · intro h
      rcases lt_trichotomy t 1 with hlt | heq | hgt
      · exact Or.inl (Or.inl ⟨h, hlt⟩)
      · exact Or.inr heq
      · exact Or.inl (Or.inr hgt)
  rwa [hset] at hfin

/-! ## The value bound -/

theorem rgB_value_bound {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {ε δ : ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε)
    (hvy : ∀ t : ℝ, 0 < t → t ≤ δ → |c t| ≤ ε * t ^ ((3 : ℝ) / 2))
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∀ z : ℝ, 0 < z → z ≤ 1 →
      |Work.FTS.EllExist.rgB α m c z|
        ≤ ε * z ^ (3 / 2 - Work.FTS.EllExist.rgP α m) / (Work.FTS.EllExist.rgP α m - 3 / 2)
          + (∫ x in Set.Ioo (0 : ℝ) 1, (c x) ^ 2 / x ^ 4) / 2
          + (∫ x in Set.Ioi (1 : ℝ), (c x) ^ 2) / 2
          + δ ^ (-(2 * Work.FTS.EllExist.rgP α m + 1)) + 1 := by
  intro z hz hz1
  have hp8 : 8 ≤ Work.FTS.EllExist.rgP α m := Work.FTS.EllExist.rgP_ge hα hα4 hm
  have hp2 : 2 ≤ Work.FTS.EllExist.rgP α m := by linarith
  have hp32 : 3 / 2 < Work.FTS.EllExist.rgP α m := by linarith
  have hp1 : 1 ≤ Work.FTS.EllExist.rgP α m := by linarith
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => |c t|)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := aesm_abs_c_of hnear hfar
  have hrgB : |Work.FTS.EllExist.rgB α m c z|
      = |∫ t in Set.Ioi z, c t * t ^ (-(Work.FTS.EllExist.rgP α m) - 1)| := by
    simp only [Work.FTS.EllExist.rgB, Work.FTS.EllExist.rgF2]
  have hfirst : |Work.FTS.EllExist.rgB α m c z|
      ≤ ∫ t in Set.Ioi z, ‖c t * t ^ (-(Work.FTS.EllExist.rgP α m) - 1)‖ := by
    rw [hrgB]
    have h := norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioi z))
      (f := fun t : ℝ => c t * t ^ (-(Work.FTS.EllExist.rgP α m) - 1))
    simpa only [Real.norm_eq_abs] using h
  have htail := rgB_tail_le (c := c) (p := Work.FTS.EllExist.rgP α m) (δ := δ)
    hp2 hδ hδ1 hmeas hnear hfar
  by_cases hzδ : z ≤ δ
  · have hnear' : ∫ t in Set.Ioc z δ, ‖c t * t ^ (-(Work.FTS.EllExist.rgP α m) - 1)‖
        ≤ ε * z ^ (3 / 2 - Work.FTS.EllExist.rgP α m)
            / (Work.FTS.EllExist.rgP α m - 3 / 2) :=
      rgB_near_le (c := c) (p := Work.FTS.EllExist.rgP α m) (ε := ε) (z := z) (δ := δ)
        hp32 hε hz hzδ hvy
    have hIoc := rgB_int_Ioc (c := c) (p := Work.FTS.EllExist.rgP α m) (ε := ε) (z := z)
      (δ := δ) hp32 hε hz hmeas hvy
    have hIoi := rgB_int_Ioi (c := c) (p := Work.FTS.EllExist.rgP α m) (δ := δ)
      hp1 hδ hmeas hnear hfar
    have hdisj : Disjoint (Set.Ioc z δ) (Set.Ioi δ) := by
      rw [Set.disjoint_left]
      intro t ht1 ht2
      exact absurd ht1.2 (not_le.mpr ht2)
    have hset : Set.Ioi z = Set.Ioc z δ ∪ Set.Ioi δ := by
      ext t
      simp only [Set.mem_Ioi, Set.mem_Ioc, Set.mem_union]
      constructor
      · intro h
        rcases lt_or_ge δ t with h' | h'
        · exact Or.inr h'
        · exact Or.inl ⟨h, h'⟩
      · rintro (⟨h, _⟩ | h) <;> linarith
    have hsplit : ∫ t in Set.Ioi z, ‖c t * t ^ (-(Work.FTS.EllExist.rgP α m) - 1)‖
        = (∫ t in Set.Ioc z δ, ‖c t * t ^ (-(Work.FTS.EllExist.rgP α m) - 1)‖)
          + (∫ t in Set.Ioi δ, ‖c t * t ^ (-(Work.FTS.EllExist.rgP α m) - 1)‖) := by
      rw [hset, setIntegral_union hdisj measurableSet_Ioi hIoc hIoi]
    calc |Work.FTS.EllExist.rgB α m c z|
        ≤ ∫ t in Set.Ioi z, ‖c t * t ^ (-(Work.FTS.EllExist.rgP α m) - 1)‖ := hfirst
      _ = (∫ t in Set.Ioc z δ, ‖c t * t ^ (-(Work.FTS.EllExist.rgP α m) - 1)‖)
            + (∫ t in Set.Ioi δ, ‖c t * t ^ (-(Work.FTS.EllExist.rgP α m) - 1)‖) := hsplit
      _ ≤ ε * z ^ (3 / 2 - Work.FTS.EllExist.rgP α m)
              / (Work.FTS.EllExist.rgP α m - 3 / 2)
            + ((∫ x in Set.Ioo (0 : ℝ) 1, (c x) ^ 2 / x ^ 4) / 2
              + (∫ x in Set.Ioi (1 : ℝ), (c x) ^ 2) / 2
              + δ ^ (-(2 * Work.FTS.EllExist.rgP α m + 1)) + 1) :=
          add_le_add hnear' htail
      _ = ε * z ^ (3 / 2 - Work.FTS.EllExist.rgP α m)
              / (Work.FTS.EllExist.rgP α m - 3 / 2)
            + (∫ x in Set.Ioo (0 : ℝ) 1, (c x) ^ 2 / x ^ 4) / 2
            + (∫ x in Set.Ioi (1 : ℝ), (c x) ^ 2) / 2
            + δ ^ (-(2 * Work.FTS.EllExist.rgP α m + 1)) + 1 := by ring
  · simp only [not_le] at hzδ
    have hIoi := rgB_int_Ioi (c := c) (p := Work.FTS.EllExist.rgP α m) (δ := δ)
      hp1 hδ hmeas hnear hfar
    have hmono : ∫ t in Set.Ioi z, ‖c t * t ^ (-(Work.FTS.EllExist.rgP α m) - 1)‖
        ≤ ∫ t in Set.Ioi δ, ‖c t * t ^ (-(Work.FTS.EllExist.rgP α m) - 1)‖ :=
      setIntegral_mono_set hIoi (Eventually.of_forall (fun t => norm_nonneg _))
        (Eventually.of_forall (fun t ht => lt_trans hzδ ht))
    have hnn : 0 ≤ ε * z ^ (3 / 2 - Work.FTS.EllExist.rgP α m)
        / (Work.FTS.EllExist.rgP α m - 3 / 2) :=
      div_nonneg (mul_nonneg hε (Real.rpow_nonneg hz.le _)) (by linarith)
    calc |Work.FTS.EllExist.rgB α m c z|
        ≤ ∫ t in Set.Ioi z, ‖c t * t ^ (-(Work.FTS.EllExist.rgP α m) - 1)‖ := hfirst
      _ ≤ ∫ t in Set.Ioi δ, ‖c t * t ^ (-(Work.FTS.EllExist.rgP α m) - 1)‖ := hmono
      _ ≤ (∫ x in Set.Ioo (0 : ℝ) 1, (c x) ^ 2 / x ^ 4) / 2
            + (∫ x in Set.Ioi (1 : ℝ), (c x) ^ 2) / 2
            + δ ^ (-(2 * Work.FTS.EllExist.rgP α m + 1)) + 1 := htail
      _ ≤ ε * z ^ (3 / 2 - Work.FTS.EllExist.rgP α m)
              / (Work.FTS.EllExist.rgP α m - 3 / 2)
            + (∫ x in Set.Ioo (0 : ℝ) 1, (c x) ^ 2 / x ^ 4) / 2
            + (∫ x in Set.Ioi (1 : ℝ), (c x) ^ 2) / 2
            + δ ^ (-(2 * Work.FTS.EllExist.rgP α m + 1)) + 1 := by linarith [hnn]

end Work.FTS.PhiStar.Honesty
