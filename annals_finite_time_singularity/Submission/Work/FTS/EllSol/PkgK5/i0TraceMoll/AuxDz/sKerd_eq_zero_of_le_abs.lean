import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.EllSol.PkgK5.i0TraceMoll.AuxDz.sKerd_eq_zero_of_le_abs`

The first derivative of the normalised bump `sKer ε` vanishes on the *closed* complement of
its support, `{t | ε ≤ |t|}`:

  `deriv (sKer ε) t = 0`  for `0 < ε` and `ε ≤ |t|`.

The strict version `ε < |t|` is immediate from the support containment
(`sKer_eq_zero_of_le_abs` from `MollDefs`, i.e. `sBump` is a genuine bump); at the two
boundary points `t = ±ε` it is *not* an eventual-equality statement, but it follows from
the flatness of `Real.smoothTransition` at `0`, packaged here as:

* `contDiff_two_sKer` — `sKer ε` is `C²`, hence `deriv (sKer ε)` is continuous, and
* `deriv_sKer_eq_zero_of_lt_abs` — the strict-support vanishing.

Indeed `deriv (sKer ε)` is continuous and vanishes on the *dense* subset `{|t| > ε}` of each
of `[ε, ∞)` and `(-∞, -ε]`; a continuous function vanishing on a dense set vanishes
everywhere.  (Equivalently: `{x | deriv (sKer ε) x = 0}` is closed and contains `Ioi ε`,
hence contains `closure (Ioi ε) = Ici ε`.)
-/

namespace Work.FTS.EllSol.PkgK5.i0TraceMoll.AuxDz

open scoped Real Topology
open MeasureTheory Set Filter

/-- `sKer ε = (ε * sMass)⁻¹ • sBump (· / ε)` is smooth; in particular it is `C²`. -/
theorem contDiff_two_sKer (ε : ℝ) :
    ContDiff ℝ (2 : ℕ∞) (Work.FTS.EllSol.PkgK5.K5c.sKer ε) := by
  have hinner : ContDiff ℝ (2 : ℕ∞) (fun t : ℝ => 1 - (t / ε) ^ 2) :=
    contDiff_const.sub ((contDiff_id.div_const ε).pow 2)
  have hcomp : ContDiff ℝ (2 : ℕ∞) (fun t : ℝ => Real.smoothTransition (1 - (t / ε) ^ 2)) :=
    (Real.smoothTransition.contDiff (n := 2)).comp hinner
  have hmul : ContDiff ℝ (2 : ℕ∞)
      (fun t : ℝ => (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
        * Real.smoothTransition (1 - (t / ε) ^ 2)) := contDiff_const.mul hcomp
  have hfun : Work.FTS.EllSol.PkgK5.K5c.sKer ε
      = fun t : ℝ => (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
          * Real.smoothTransition (1 - (t / ε) ^ 2) := rfl
  rw [hfun]
  exact hmul

/-- The derivative of `sKer ε` is continuous. -/
theorem continuous_deriv_sKer (ε : ℝ) :
    Continuous (deriv (Work.FTS.EllSol.PkgK5.K5c.sKer ε)) :=
  (contDiff_two_sKer ε).continuous_deriv (by norm_num)

/-- The first derivative of the bump vanishes off its support (strict version). -/
theorem deriv_sKer_eq_zero_of_lt_abs {ε t : ℝ} (hε : 0 < ε) (h : ε < |t|) :
    deriv (Work.FTS.EllSol.PkgK5.K5c.sKer ε) t = 0 := by
  have hev : Work.FTS.EllSol.PkgK5.K5c.sKer ε =ᶠ[𝓝 t] fun _ : ℝ => (0 : ℝ) := by
    rcases lt_or_ge (0 : ℝ) t with hpos | hnonpos
    · have htε : ε < t := by rwa [abs_of_pos hpos] at h
      filter_upwards [isOpen_Ioi.mem_nhds htε] with u hu
      have hu' : ε ≤ |u| := by
        rw [abs_of_pos (lt_trans hε hu)]
        exact le_of_lt hu
      exact Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε hu'
    · have htε : t < -ε := by
        rw [abs_of_nonpos hnonpos] at h; linarith
      filter_upwards [isOpen_Iio.mem_nhds htε] with u hu
      have hu2 : u < -ε := hu
      have hu0 : u < 0 := by linarith
      have hu' : ε ≤ |u| := by
        rw [abs_of_neg hu0]; linarith
      exact Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε hu'
  rw [Filter.EventuallyEq.deriv_eq hev]
  simp

theorem sKerd_eq_zero_of_le_abs {ε t : ℝ} (hε : 0 < ε) (ht : ε ≤ |t|) :
    deriv (Work.FTS.EllSol.PkgK5.K5c.sKer ε) t = 0 := by
  have hclosed : IsClosed {x : ℝ | deriv (Work.FTS.EllSol.PkgK5.K5c.sKer ε) x = 0} :=
    isClosed_eq (continuous_deriv_sKer ε) continuous_const
  rcases lt_or_eq_of_le ht with h | h
  · exact deriv_sKer_eq_zero_of_lt_abs hε h
  · rcases lt_or_ge t (0 : ℝ) with ht0 | ht0
    · -- `t = -ε`: the derivative vanishes on `Iio (-ε)`
      have htε : t = -ε := by rw [abs_of_neg ht0] at h; linarith
      rw [htε]
      have hsub : Set.Iio (-ε) ⊆ {x : ℝ | deriv (Work.FTS.EllSol.PkgK5.K5c.sKer ε) x = 0} := by
        intro u hu
        have hu2 : u < -ε := hu
        exact deriv_sKer_eq_zero_of_lt_abs hε (by
          have hu0 : u < 0 := by linarith
          rw [abs_of_neg hu0]
          linarith)
      have hsub' : closure (Set.Iio (-ε))
          ⊆ {x : ℝ | deriv (Work.FTS.EllSol.PkgK5.K5c.sKer ε) x = 0} :=
        hclosed.closure_subset_iff.mpr hsub
      have hmem : (-ε) ∈ closure (Set.Iio (-ε)) := by
        rw [closure_Iio]
        exact Set.mem_Iic.mpr le_rfl
      exact hsub' hmem
    · -- `t = ε`: the derivative vanishes on `Ioi ε`, whose closure contains `ε`
      have htε : t = ε := by rw [abs_of_nonneg ht0] at h; exact h.symm
      rw [htε]
      have hsub : Set.Ioi ε ⊆ {x : ℝ | deriv (Work.FTS.EllSol.PkgK5.K5c.sKer ε) x = 0} := by
        intro u hu
        exact deriv_sKer_eq_zero_of_lt_abs hε (by
          rw [abs_of_pos (lt_trans hε hu)]
          exact hu)
      have hsub' : closure (Set.Ioi ε)
          ⊆ {x : ℝ | deriv (Work.FTS.EllSol.PkgK5.K5c.sKer ε) x = 0} :=
        hclosed.closure_subset_iff.mpr hsub
      have hmem : ε ∈ closure (Set.Ioi ε) := by
        rw [closure_Ioi]
        exact Set.mem_Ici.mpr le_rfl
      exact hsub' hmem

end Work.FTS.EllSol.PkgK5.i0TraceMoll.AuxDz
