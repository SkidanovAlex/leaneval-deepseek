/-
# `hardyShrink_slice` — the shrinking region against the local Hardy inequality

`hardyShrink_slice` bounds the `thShrink`- (i.e. `Ω_n`-angular-) supported piece of the
singular weight `w²·(D_z^s F)²·sin(2θ)^{-γ}` by the `Ω_n`-part of the `ℋ^k`-integrand.

## Route

* `thShrink n θ = 1` exactly on `L ∪ R`, `L = θ < 2/n`, `R = π/2 - 2/n < θ`; on that set
  `(z,θ) ∈ Ω_n` for *every* `z`, so `omegaPart = HkIntegrand` there.
* Split the angular integral over `Iθ` into the two halves `(0, 2/n)` and `(π/2 - 2/n, π/2)`
  (the endpoints `0`, `π/2` are removed by `lintegral_union` against the singleton, whose
  `volume` is `0`).
* On each half apply the local weighted Hardy inequality `hardyLoc` / `hardyLocRight` with
  `c = γ ∈ (1, 3/2]` to the *scaled* slice `θ ↦ w z · D_z^s F z θ`; this converts
  `∫ sin^{-γ}(w u)²` into `∫ sin^{2-γ}(∂_θ(w u))²`, and the weight identity
  `sin(2θ)^{2-γ}·(∂_θ(D_z^sF)·w)² = (D_z^sD_θF·Wt)²` (`EstAux.sin_rpow_deriv_sq_eq`) turns the
  latter into the mixed slot `(s,1)` of the `ℋ^k`-integrand, which is legal because `s+1 ≤ k`.
* The vanishing of the trace at both endpoints (`u → 0` at `0⁺`, `π/2⁻`) is read off from the
  boundary hypothesis `PhiStar.ThetaTraces α k F` through `ClassC.tendsto_of_sin_rpow_sq`.

The constant is `8/(γ-1)²` with `γ = gam α = 1 + α/10` (so `γ - 1 = α/10 > 0`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstDefs
import Submission.Work.FTS.PhiStar.Honesty.CptApp.hardyLoc
import Submission.Work.FTS.PhiStar.Honesty.CptApp.hardyLocRight
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.sin_rpow_deriv_sq_eq
import Submission.Work.FTS.ClassC.tendsto_of_sin_rpow_sq
import Submission.Work.FTS.Vocab
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.PhiStar.ThetaTraces

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp.Est

set_option autoImplicit false

/-! ## An abstract slice inequality

The measure-theoretic skeleton of the estimate, with the two Hardy inputs and the two
pointwise majorants left as hypotheses. -/
private theorem shrink_slice_abstract {n : ℕ} (hn : 3 ≤ n) {γ : ℝ} (hγ1 : 1 < γ)
    (hγ32 : γ ≤ 3 / 2) {W : ℝ} {u G : ℝ → ℝ}
    (hsmL : ContDiffOn ℝ 1 (fun θ => W * u θ) (Set.Ioo 0 (2 / (n : ℝ))))
    (htrL : Filter.Tendsto (fun θ => W * u θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hsmR : ContDiffOn ℝ 1 (fun θ => W * u θ)
      (Set.Ioo (Real.pi / 2 - 2 / (n : ℝ)) (Real.pi / 2)))
    (htrR : Filter.Tendsto (fun θ => W * u θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hbdL : ∀ θ ∈ Set.Ioo 0 (2 / (n : ℝ)),
      (Real.sin (2 * θ)) ^ (2 - γ) * (deriv (fun θ' => W * u θ') θ) ^ 2 ≤ G θ)
    (hbdR : ∀ θ ∈ Set.Ioo (Real.pi / 2 - 2 / (n : ℝ)) (Real.pi / 2),
      (Real.sin (2 * θ)) ^ (2 - γ) * (deriv (fun θ' => W * u θ') θ) ^ 2 ≤ G θ) :
    (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (W ^ 2
        * (Work.FTS.PhiStar.Honesty.CptApp.thShrink n θ * (u θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-γ))))
      ≤ ENNReal.ofReal (8 / (γ - 1) ^ 2) * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (G θ)) := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h2n_pos : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have h2n_le : 2 / (n : ℝ) ≤ Real.pi / 4 := by
    rw [div_le_iff₀ hnR]
    have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [Real.pi_gt_three]
  have h2n_lt : 2 / (n : ℝ) < Real.pi / 2 := by linarith [h2n_le, Real.pi_pos]
  have hHL := Work.FTS.PhiStar.Honesty.CptApp.hardyLoc γ (2 / (n : ℝ)) hγ1 hγ32 h2n_pos h2n_le
    hsmL htrL
  have hHR := Work.FTS.PhiStar.Honesty.CptApp.hardyLocRight γ (Real.pi / 2 - 2 / (n : ℝ))
    hγ1 hγ32
    (by linarith : Real.pi / 2 - 2 / (n : ℝ) < Real.pi / 2)
    (by linarith : Real.pi / 4 ≤ Real.pi / 2 - 2 / (n : ℝ)) hsmR htrR
  -- the left half is contained in `(0, 2/n) ∪ {0}`, the right one in `(π/2-2/n, π/2) ∪ {π/2}`
  have hLsub : Work.Spaces.Iθ ∩ Set.Iio (2 / (n : ℝ))
      ⊆ Set.Ioo 0 (2 / (n : ℝ)) ∪ ({0} : Set ℝ) := by
    intro θ hθ
    obtain ⟨hθI, hθL⟩ := hθ
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθI
    rw [Set.mem_Iio] at hθL
    rcases eq_or_lt_of_le hθI.1 with h | h
    · exact Or.inr (by rw [← h]; exact Set.mem_singleton 0)
    · exact Or.inl ⟨h, hθL⟩
  have hRsub : Work.Spaces.Iθ ∩ Set.Ioi (Real.pi / 2 - 2 / (n : ℝ))
      ⊆ Set.Ioo (Real.pi / 2 - 2 / (n : ℝ)) (Real.pi / 2) ∪ ({Real.pi / 2} : Set ℝ) := by
    intro θ hθ
    obtain ⟨hθI, hθR⟩ := hθ
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθI
    rw [Set.mem_Ioi] at hθR
    rcases lt_or_eq_of_le hθI.2 with h | h
    · exact Or.inl ⟨hθR, h⟩
    · exact Or.inr (by rw [h]; exact Set.mem_singleton (Real.pi / 2))
  have hleft : (∫⁻ θ in Work.Spaces.Iθ ∩ Set.Iio (2 / (n : ℝ)),
        ENNReal.ofReal (W ^ 2 * (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)))
      ≤ ENNReal.ofReal (4 / (γ - 1) ^ 2) * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (G θ)) := by
    calc (∫⁻ θ in Work.Spaces.Iθ ∩ Set.Iio (2 / (n : ℝ)),
          ENNReal.ofReal (W ^ 2 * (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)))
        ≤ ∫⁻ θ in Set.Ioo 0 (2 / (n : ℝ)) ∪ ({0} : Set ℝ),
            ENNReal.ofReal (W ^ 2 * (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)) :=
          MeasureTheory.lintegral_mono_set hLsub
      _ = (∫⁻ θ in Set.Ioo 0 (2 / (n : ℝ)),
              ENNReal.ofReal (W ^ 2 * (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)))
            + (∫⁻ θ in ({0} : Set ℝ),
              ENNReal.ofReal (W ^ 2 * (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ))) :=
          MeasureTheory.lintegral_union (A := Set.Ioo 0 (2 / (n : ℝ))) (B := ({0} : Set ℝ))
            (measurableSet_singleton 0) (by rw [Set.disjoint_singleton_right]; simp)
      _ = ∫⁻ θ in Set.Ioo 0 (2 / (n : ℝ)),
            ENNReal.ofReal (W ^ 2 * (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)) := by
          rw [MeasureTheory.lintegral_singleton]; simp
      _ = ∫⁻ θ in Set.Ioo 0 (2 / (n : ℝ)),
            ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-γ) * (W * u θ) ^ 2) := by
          refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
          congr 1
          ring
      _ ≤ ENNReal.ofReal (4 / (γ - 1) ^ 2) * (∫⁻ θ in Set.Ioo 0 (2 / (n : ℝ)),
            ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - γ)
              * (deriv (fun θ' => W * u θ') θ) ^ 2)) := hHL
      _ ≤ ENNReal.ofReal (4 / (γ - 1) ^ 2) * (∫⁻ θ in Set.Ioo 0 (2 / (n : ℝ)),
            ENNReal.ofReal (G θ)) := by
          refine mul_le_mul_right ?_ _
          exact MeasureTheory.lintegral_mono_ae
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
              (fun θ hθ => ENNReal.ofReal_le_ofReal (hbdL θ hθ)))
      _ ≤ ENNReal.ofReal (4 / (γ - 1) ^ 2) * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (G θ)) := by
          refine mul_le_mul_right ?_ _
          refine MeasureTheory.lintegral_mono_set (fun θ hθ => ?_)
          exact ⟨hθ.1.le, by linarith [hθ.2, h2n_lt]⟩
  have hright : (∫⁻ θ in Work.Spaces.Iθ ∩ Set.Ioi (Real.pi / 2 - 2 / (n : ℝ)),
        ENNReal.ofReal (W ^ 2 * (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)))
      ≤ ENNReal.ofReal (4 / (γ - 1) ^ 2) * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (G θ)) := by
    calc (∫⁻ θ in Work.Spaces.Iθ ∩ Set.Ioi (Real.pi / 2 - 2 / (n : ℝ)),
          ENNReal.ofReal (W ^ 2 * (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)))
        ≤ ∫⁻ θ in Set.Ioo (Real.pi / 2 - 2 / (n : ℝ)) (Real.pi / 2) ∪ ({Real.pi / 2} : Set ℝ),
            ENNReal.ofReal (W ^ 2 * (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)) :=
          MeasureTheory.lintegral_mono_set hRsub
      _ = (∫⁻ θ in Set.Ioo (Real.pi / 2 - 2 / (n : ℝ)) (Real.pi / 2),
              ENNReal.ofReal (W ^ 2 * (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)))
            + (∫⁻ θ in ({Real.pi / 2} : Set ℝ),
              ENNReal.ofReal (W ^ 2 * (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ))) :=
          MeasureTheory.lintegral_union (A := Set.Ioo (Real.pi / 2 - 2 / (n : ℝ)) (Real.pi / 2))
            (B := ({Real.pi / 2} : Set ℝ)) (measurableSet_singleton _)
            (by rw [Set.disjoint_singleton_right]; simp)
      _ = ∫⁻ θ in Set.Ioo (Real.pi / 2 - 2 / (n : ℝ)) (Real.pi / 2),
            ENNReal.ofReal (W ^ 2 * (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)) := by
          rw [MeasureTheory.lintegral_singleton]; simp
      _ = ∫⁻ θ in Set.Ioo (Real.pi / 2 - 2 / (n : ℝ)) (Real.pi / 2),
            ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-γ) * (W * u θ) ^ 2) := by
          refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
          congr 1
          ring
      _ ≤ ENNReal.ofReal (4 / (γ - 1) ^ 2) * (∫⁻ θ in Set.Ioo (Real.pi / 2 - 2 / (n : ℝ))
            (Real.pi / 2), ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - γ)
              * (deriv (fun θ' => W * u θ') θ) ^ 2)) := hHR
      _ ≤ ENNReal.ofReal (4 / (γ - 1) ^ 2) * (∫⁻ θ in Set.Ioo (Real.pi / 2 - 2 / (n : ℝ))
            (Real.pi / 2), ENNReal.ofReal (G θ)) := by
          refine mul_le_mul_right ?_ _
          exact MeasureTheory.lintegral_mono_ae
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
              (fun θ hθ => ENNReal.ofReal_le_ofReal (hbdR θ hθ)))
      _ ≤ ENNReal.ofReal (4 / (γ - 1) ^ 2) * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (G θ)) := by
          refine mul_le_mul_right ?_ _
          refine MeasureTheory.lintegral_mono_set (fun θ hθ => ?_)
          exact ⟨by linarith [h2n_lt, hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  -- `thShrink` is exactly the indicator of `L ∪ R`
  have hstep1 : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (W ^ 2
        * (Work.FTS.PhiStar.Honesty.CptApp.thShrink n θ * (u θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-γ))))
      = ∫⁻ θ in Work.Spaces.Iθ,
          (Set.Iio (2 / (n : ℝ)) ∪ Set.Ioi (Real.pi / 2 - 2 / (n : ℝ))).indicator
            (fun θ => ENNReal.ofReal (W ^ 2 * (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ))) θ := by
    refine MeasureTheory.setLIntegral_congr_fun hIθ (fun θ _ => ?_)
    by_cases h : θ ∈ Set.Iio (2 / (n : ℝ)) ∪ Set.Ioi (Real.pi / 2 - 2 / (n : ℝ))
    · rw [Set.indicator_of_mem h]
      have hone : Work.FTS.PhiStar.Honesty.CptApp.thShrink n θ = 1 := by
        rw [Work.FTS.PhiStar.Honesty.CptApp.thShrink_eq_one_iff]
        simpa only [Set.mem_union, Set.mem_Iio, Set.mem_Ioi] using h
      rw [hone]
      congr 1
      ring
    · rw [Set.indicator_of_notMem h]
      have hzero : Work.FTS.PhiStar.Honesty.CptApp.thShrink n θ = 0 := by
        rcases Work.FTS.PhiStar.Honesty.CptApp.thShrink_eq_zero_or_one n θ with h0 | h1
        · exact h0
        · exact absurd (by
            rw [Work.FTS.PhiStar.Honesty.CptApp.thShrink_eq_one_iff] at h1
            simpa only [Set.mem_union, Set.mem_Iio, Set.mem_Ioi] using h1) h
      rw [hzero]
      simp
  have hunion : ((Set.Iio (2 / (n : ℝ)) ∩ Work.Spaces.Iθ)
        ∪ (Set.Ioi (Real.pi / 2 - 2 / (n : ℝ)) ∩ Work.Spaces.Iθ))
      = (Work.Spaces.Iθ ∩ Set.Iio (2 / (n : ℝ)))
        ∪ (Work.Spaces.Iθ ∩ Set.Ioi (Real.pi / 2 - 2 / (n : ℝ))) := by
    rw [Set.inter_comm (Set.Iio (2 / (n : ℝ))),
      Set.inter_comm (Set.Ioi (Real.pi / 2 - 2 / (n : ℝ)))]
  have hlast : ENNReal.ofReal (4 / (γ - 1) ^ 2) * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (G θ))
      + ENNReal.ofReal (4 / (γ - 1) ^ 2) * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (G θ))
      = ENNReal.ofReal (8 / (γ - 1) ^ 2) * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (G θ)) := by
    rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring_nf
  rw [hstep1]
  rw [MeasureTheory.setLIntegral_indicator
    (s := Set.Iio (2 / (n : ℝ)) ∪ Set.Ioi (Real.pi / 2 - 2 / (n : ℝ)))
    (t := Work.Spaces.Iθ)
    (f := fun θ => ENNReal.ofReal (W ^ 2 * (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)))
    (by measurability)]
  rw [Set.union_inter_distrib_right, hunion]
  refine le_trans (MeasureTheory.lintegral_union_le _ _ _) ?_
  exact le_trans (add_le_add hleft hright) (le_of_eq hlast)

/-! ## The requested estimate -/

theorem hardyShrink_slice (k : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (F : ℝ → ℝ → ℝ) (n s : ℕ), 3 ≤ n → s + 1 ≤ k →
      Work.FTS.EllipticEst.SmoothOpen F → Work.FTS.PhiStar.ThetaTraces α k F →
      ∀ z ∈ Set.Ioi (0 : ℝ),
        (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((Work.Spaces.w z) ^ 2
              * (Work.FTS.PhiStar.Honesty.CptApp.thShrink n θ
                * (Work.Spaces.DzIter s F z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))))
          ≤ ENNReal.ofReal C
            * (∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal (Work.FTS.PhiStar.Honesty.CptApp.omegaPart α k n F z θ)) := by
  have hgam1 : 1 < Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hgam32 : Work.Spaces.gam α ≤ 3 / 2 := by rw [Work.Spaces.gam]; linarith
  have hCpos : 0 < 8 / (Work.Spaces.gam α - 1) ^ 2 := by
    have h : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam]; linarith
    exact div_pos (by norm_num) (pow_pos h 2)
  refine ⟨8 / (Work.Spaces.gam α - 1) ^ 2, hCpos, ?_⟩
  intro F n s hn hs hF hB z hz
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h2n_lt : 2 / (n : ℝ) < Real.pi / 2 := by
    rw [div_lt_iff₀ hnR]
    have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [Real.pi_gt_three]
  -- ## the vanishing traces, from `ThetaTraces`
  have hBD := hB s hs z hz
  have htraceL : Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
      * (Work.Spaces.DzIter s F z θ) ^ 2) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa only [Work.Spaces.mixed_zero_right] using hBD.1
  have htraceR : Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
      * (Work.Spaces.DzIter s F z θ) ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    simpa only [Work.Spaces.mixed_zero_right] using hBD.2
  have hlL : ∀ᶠ θ : ℝ in nhdsWithin 0 (Set.Ioi 0), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    have hmem : ∀ᶠ θ : ℝ in nhds (0 : ℝ), θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2) :=
      isOpen_Ioo.mem_nhds ⟨by norm_num, by linarith [Real.pi_pos]⟩
    filter_upwards [hmem.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with θ h1 h2
    exact ⟨h2, h1.2⟩
  have hlR : ∀ᶠ θ : ℝ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    have hmem : ∀ᶠ θ : ℝ in nhds (Real.pi / 2), θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2 + 1) :=
      isOpen_Ioo.mem_nhds ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    filter_upwards [hmem.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with θ h1 h2
    exact ⟨h1.1, h2⟩
  have hsliceL := Work.FTS.ClassC.tendsto_of_sin_rpow_sq hgam1 hlL htraceL
  have hsliceR := Work.FTS.ClassC.tendsto_of_sin_rpow_sq hgam1 hlR htraceR
  -- ## smoothness of the scaled slices
  have hsm : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => Work.Spaces.DzIter s F z θ)
      (Set.Ioo 0 (Real.pi / 2)) := (hF.DzIter s).curry_θ hz
  have hsmvL : ContDiffOn ℝ 1 (fun θ => Work.Spaces.w z * Work.Spaces.DzIter s F z θ)
      (Set.Ioo 0 (2 / (n : ℝ))) := by
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun θ => Work.Spaces.w z * Work.Spaces.DzIter s F z θ) (Set.Ioo 0 (2 / (n : ℝ))) := by
      simpa only [smul_eq_mul] using
        (hsm.mono (Set.Ioo_subset_Ioo_right h2n_lt.le)).const_smul (Work.Spaces.w z)
    exact h1.of_le (by simp [Work.Stability.smoothOrder])
  have hsmvR : ContDiffOn ℝ 1 (fun θ => Work.Spaces.w z * Work.Spaces.DzIter s F z θ)
      (Set.Ioo (Real.pi / 2 - 2 / (n : ℝ)) (Real.pi / 2)) := by
    have hle : (0 : ℝ) ≤ Real.pi / 2 - 2 / (n : ℝ) := by linarith [h2n_lt]
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun θ => Work.Spaces.w z * Work.Spaces.DzIter s F z θ)
        (Set.Ioo (Real.pi / 2 - 2 / (n : ℝ)) (Real.pi / 2)) := by
      simpa only [smul_eq_mul] using
        (hsm.mono (Set.Ioo_subset_Ioo_left hle)).const_smul (Work.Spaces.w z)
    exact h1.of_le (by simp [Work.Stability.smoothOrder])
  have htrvL : Filter.Tendsto (fun θ => Work.Spaces.w z * Work.Spaces.DzIter s F z θ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using hsliceL.const_mul (Work.Spaces.w z)
  have htrvR : Filter.Tendsto (fun θ => Work.Spaces.w z * Work.Spaces.DzIter s F z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    simpa using hsliceR.const_mul (Work.Spaces.w z)
  -- ## the pointwise majorants
  have homegaL : ∀ θ ∈ Set.Ioo 0 (2 / (n : ℝ)),
      (Work.Spaces.mixed s 1 F z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.FTS.PhiStar.Honesty.CptApp.omegaPart α k n F z θ := by
    intro θ hθ
    have ho : Work.FTS.PhiStar.Honesty.CptApp.omegaPart α k n F z θ
        = Work.Spaces.HkIntegrand α k F z θ := by
      rw [Work.FTS.PhiStar.Honesty.CptApp.omegaPart,
        if_pos (Work.FTS.PhiStar.Honesty.CptApp.mem_Omega_of_lt_th hθ.2)]
    rw [ho]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α k F z θ 1 s le_rfl (by omega)
  have homegaR : ∀ θ ∈ Set.Ioo (Real.pi / 2 - 2 / (n : ℝ)) (Real.pi / 2),
      (Work.Spaces.mixed s 1 F z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.FTS.PhiStar.Honesty.CptApp.omegaPart α k n F z θ := by
    intro θ hθ
    have ho : Work.FTS.PhiStar.Honesty.CptApp.omegaPart α k n F z θ
        = Work.Spaces.HkIntegrand α k F z θ := by
      rw [Work.FTS.PhiStar.Honesty.CptApp.omegaPart,
        if_pos (Work.FTS.PhiStar.Honesty.CptApp.mem_Omega_of_gt_th hθ.1)]
    rw [ho]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α k F z θ 1 s le_rfl (by omega)
  have hbdL : ∀ θ ∈ Set.Ioo 0 (2 / (n : ℝ)),
      (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        * (deriv (fun θ' => Work.Spaces.w z * Work.Spaces.DzIter s F z θ') θ) ^ 2
        ≤ Work.FTS.PhiStar.Honesty.CptApp.omegaPart α k n F z θ := by
    intro θ hθ
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ.1, by linarith [hθ.2, h2n_lt]⟩
    rw [deriv_const_mul_field]
    rw [show (Work.Spaces.w z * deriv (fun θ' => Work.Spaces.DzIter s F z θ') θ) ^ 2
        = (deriv (fun θ' => Work.Spaces.DzIter s F z θ') θ * Work.Spaces.w z) ^ 2 by ring]
    rw [Work.FTS.PhiStar.Honesty.CptApp.EstAux.sin_rpow_deriv_sq_eq α F hF s hz hθ']
    exact homegaL θ hθ
  have hbdR : ∀ θ ∈ Set.Ioo (Real.pi / 2 - 2 / (n : ℝ)) (Real.pi / 2),
      (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        * (deriv (fun θ' => Work.Spaces.w z * Work.Spaces.DzIter s F z θ') θ) ^ 2
        ≤ Work.FTS.PhiStar.Honesty.CptApp.omegaPart α k n F z θ := by
    intro θ hθ
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [h2n_lt, hθ.1], hθ.2⟩
    rw [deriv_const_mul_field]
    rw [show (Work.Spaces.w z * deriv (fun θ' => Work.Spaces.DzIter s F z θ') θ) ^ 2
        = (deriv (fun θ' => Work.Spaces.DzIter s F z θ') θ * Work.Spaces.w z) ^ 2 by ring]
    rw [Work.FTS.PhiStar.Honesty.CptApp.EstAux.sin_rpow_deriv_sq_eq α F hF s hz hθ']
    exact homegaR θ hθ
  exact shrink_slice_abstract hn hgam1 hgam32 hsmvL htrvL hsmvR htrvR hbdL hbdR

end Work.FTS.PhiStar.Honesty.CptApp.Est
