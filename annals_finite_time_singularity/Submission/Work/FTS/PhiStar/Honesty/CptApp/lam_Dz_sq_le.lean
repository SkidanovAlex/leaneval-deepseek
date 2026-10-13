import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Defs
import Submission.Work.FTS.FinalClock.ZopIterLeibniz
import Submission.Work.FTS.LocData.DzIter_mul_smoothQuad
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.PhiStar.Honesty.CptApp.LamAux.chiR_dzIter_boundAux
import Submission.Work.FTS.PhiStar.Honesty.CptApp.LamEst.lamContDiffOn
import Submission.Work.FTS.PhiStar.Honesty.CptApp.LamEst.integrableOn_slice_L2
import Submission.Work.FTS.PhiStar.Honesty.CptApp.LamEst.lam_correction_sq_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `lam_Dz_sq_le`

The angular moment of the truncated source is `lam n F z = ∫_θ zetaR n θ · F z θ · sinθcos²θ`.
Because `F_*(F) = 0`, the radial derivative `D_z^s(lam n F)` differs from the *truncated*
moment integral only through the factor `zetaR n θ - 1`, which is supported where
`sin(2θ) ≤ 2·(2/n)`: this produces the smallness `(2/n)^(2+η)`.

`D_z^m (chiR n · lam n F)` is then expanded by the Leibniz rule; the multipliers `D_z^b(chiR n)`
are uniformly bounded in `n`, which gives the stated estimate.

The proof is split into elementary inputs (proved elsewhere) and the present assembly:
* `LamEst.lamContDiffOn` — `lam n F` is `C^m` on `(0,∞)`;
* `LamEst.chiR_dzIter_bound` — a uniform bound for `D_z^b (chiR n)`;
* `LamEst.lam_correction_sq_le` — the pointwise (a.e.) Cauchy–Schwarz bound on the correction
  `D_z^s(lam n F)`;
* `LamEst.integrableOn_slice_L2` — the `z`-integrability of the weighted `L²`-slice of `D_z^i F`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The radial cutoff `chiR n` is `C^m` on `(0,∞)` (indeed smooth on all of `ℝ`). -/
private theorem chiR_contDiffOn (n m : ℕ) : ContDiffOn ℝ m (chiR n) (Set.Ioi (0 : ℝ)) := by
  have hcut : ContDiff ℝ ((m : ℕ) : WithTop ℕ∞) cut01 :=
    Real.smoothTransition.contDiff (n := (m : ℕ∞))
  have h1 : ContDiff ℝ ((m : ℕ) : WithTop ℕ∞) (fun z : ℝ => cut01 ((n : ℝ) * z - 1)) :=
    hcut.comp (by fun_prop)
  have h2 : ContDiff ℝ ((m : ℕ) : WithTop ℕ∞) (fun z : ℝ => cut01 (2 - z / (n : ℝ))) :=
    hcut.comp (by fun_prop)
  have h3 : ContDiff ℝ ((m : ℕ) : WithTop ℕ∞)
      (fun z : ℝ => cut01 ((n : ℝ) * z - 1) * cut01 (2 - z / (n : ℝ))) := h1.mul h2
  change ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞)
    (fun z : ℝ => cut01 ((n : ℝ) * z - 1) * cut01 (2 - z / (n : ℝ))) (Set.Ioi (0 : ℝ))
  exact h3.contDiffOn

/-- The assembly of the estimate `lam_Dz_sq_le` from its four elementary inputs. -/
private theorem lam_Dz_sq_le_of_estimates {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α k F)
    {K : ℕ → ℝ} (hK0 : ∀ b, 0 ≤ K b)
    (hK : ∀ (n b : ℕ) (z θ : ℝ),
        |Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ| ≤ K b)
    (hLam : ∀ (n : ℕ), 1 ≤ n → ∀ m : ℕ,
        ContDiffOn ℝ m (fun z : ℝ => lam n F z) (Set.Ioi (0 : ℝ)))
    {Cmom : ℝ} (hCmom0 : 0 ≤ Cmom)
    (hcorr : ∀ (n : ℕ), 2 ≤ n → ∀ (s : ℕ), s ≤ k →
        ∀ᵐ z ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ))),
          (Work.Spaces.DzIter s (fun z _ => lam n F z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2
            ≤ Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
              * (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.DzIter s F z θ
                    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
    (hint : ∀ (i : ℕ), i ≤ k →
        MeasureTheory.IntegrableOn
          (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter i F z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          Work.Spaces.Iz) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 2 ≤ n → ∀ (m : ℕ), m ≤ k → ∀ θ₀ : ℝ,
      MeasureTheory.integral
        (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ)))
        (fun z => (Work.Spaces.DzIter m
            (fun z _ => chiR n z * lam n F z) z θ₀) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ C * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F := by
  set Ssum : ℝ := ∑ b ∈ Finset.range (k + 1), ((k.choose b : ℝ)) ^ 2 * (K b) ^ 2 with hSsum
  have hSsum0 : 0 ≤ Ssum := by
    rw [hSsum]
    exact Finset.sum_nonneg fun b _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hk1 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  have hC0 : 0 ≤ 1 + ((k : ℝ) + 1) * Ssum * Cmom * ((k : ℝ) + 1) := by
    have : 0 ≤ ((k : ℝ) + 1) * Ssum * Cmom * ((k : ℝ) + 1) :=
      mul_nonneg (mul_nonneg (mul_nonneg hk1 hSsum0) hCmom0) hk1
    linarith
  refine ⟨1 + ((k : ℝ) + 1) * Ssum * Cmom * ((k : ℝ) + 1), hC0, ?_⟩
  intro n hn m hm θ₀
  -- the a.e. statement of the correction bound, for all `b ≤ k`
  have hae : ∀ᵐ z ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ))),
      ∀ b ∈ Finset.range (k + 1),
        (Work.Spaces.w z) ^ 2
            * (Work.Spaces.DzIter b (fun z _ => lam n F z) z 0) ^ 2
          ≤ Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
            * (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.DzIter b F z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    rw [Finset.eventually_all]
    intro b hb
    filter_upwards [hcorr n hn b (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb))] with z hz
    calc (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter b (fun z _ => lam n F z) z 0) ^ 2
        = (Work.Spaces.DzIter b (fun z _ => lam n F z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2 := by
          ring
      _ ≤ _ := hz
  -- the Leibniz expansion
  have hchi : ContDiffOn ℝ m (chiR n) (Set.Ioi (0 : ℝ)) := chiR_contDiffOn n m
  have hlam : ContDiffOn ℝ m (fun z : ℝ => lam n F z) (Set.Ioi (0 : ℝ)) := hLam n (by omega) m
  have hZop_chi : ∀ (b : ℕ) (z : ℝ),
      Work.Spaces.Zop^[b] (chiR n) z = Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ₀ := by
    intro b z
    have h1 := congrFun (Work.FTS.LocData.Zop_iterate_slice b (fun z _ : ℝ => chiR n z) θ₀) z
    have h2 : (fun z : ℝ => (fun z _ : ℝ => chiR n z) z θ₀) = chiR n := by funext z; rfl
    rw [h2] at h1
    exact h1.symm
  have hZop_lam : ∀ (b : ℕ) (z : ℝ),
      Work.Spaces.Zop^[b] (lam n F) z = Work.Spaces.DzIter b (fun z _ : ℝ => lam n F z) z 0 := by
    intro b z
    have h1 := congrFun (Work.FTS.LocData.Zop_iterate_slice b (fun z _ : ℝ => lam n F z) 0) z
    have h2 : (fun z : ℝ => (fun z _ : ℝ => lam n F z) z 0) = lam n F := by funext z; rfl
    rw [h2] at h1
    exact h1.symm
  have hZop_prod : ∀ z : ℝ,
      Work.Spaces.Zop^[m] (chiR n * lam n F) z
        = Work.Spaces.DzIter m (fun z _ : ℝ => chiR n z * lam n F z) z θ₀ := by
    intro z
    have h1 := congrFun (Work.FTS.LocData.Zop_iterate_slice m
      (fun z _ : ℝ => chiR n z * lam n F z) θ₀) z
    have h2 : (fun z : ℝ => (fun z _ : ℝ => chiR n z * lam n F z) z θ₀) = chiR n * lam n F := by
      funext z
      rfl
    rw [h2] at h1
    exact h1.symm
  have hLeib : ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Spaces.DzIter m (fun z _ : ℝ => chiR n z * lam n F z) z θ₀
        = ∑ b ∈ Finset.range (m + 1), (m.choose b : ℝ)
            * (Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ₀
                * Work.Spaces.DzIter (m - b) (fun z _ : ℝ => lam n F z) z 0) := by
    intro z hz
    have hkey : Work.Spaces.Zop^[m] (chiR n * lam n F) z
        = ∑ b ∈ Finset.range (m + 1), (m.choose b : ℝ)
            * (Work.Spaces.Zop^[b] (chiR n) z * Work.Spaces.Zop^[m - b] (lam n F) z) :=
      Work.FTS.FinalClock.ZopIterLeibniz (N := m) (U := Set.Ioi (0 : ℝ)) isOpen_Ioi
        (u := chiR n) (v := lam n F) hchi hlam hz
    rw [← hZop_prod z, hkey]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hZop_chi b z, hZop_lam (m - b) z]
  -- the pointwise bound
  have hp2n0 : 0 ≤ (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) :=
    Real.rpow_nonneg (by positivity) _
  have hpoint :
      ∀ᵐ z ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ))),
      (Work.Spaces.w z) ^ 2
          * (Work.Spaces.DzIter m (fun z _ : ℝ => chiR n z * lam n F z) z θ₀) ^ 2
        ≤ ((k : ℝ) + 1) * Ssum * Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
            * ∑ i ∈ Finset.range (k + 1),
                (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.DzIter i F z θ
                    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    filter_upwards [hae, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
      with z hz_ae hz
    set Ab : ℕ → ℝ := fun b => (m.choose b : ℝ)
      * (Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ₀
          * Work.Spaces.DzIter (m - b) (fun z _ : ℝ => lam n F z) z 0) with hAb
    set hh : ℕ → ℝ := fun i => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.DzIter i F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 with hhh
    have hhh0 : ∀ i : ℕ, 0 ≤ hh i := by
      intro i
      rw [hhh]
      exact integral_nonneg fun θ => sq_nonneg _
    have hleib := hLeib z hz
    have hsq : (Work.Spaces.DzIter m (fun z _ : ℝ => chiR n z * lam n F z) z θ₀) ^ 2
        ≤ ((m : ℝ) + 1) * ∑ b ∈ Finset.range (m + 1), (Ab b) ^ 2 := by
      rw [hleib]
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (m + 1)) (f := Ab)
      simpa only [Finset.card_range, Nat.cast_add, Nat.cast_one] using h
    have hterm : ∀ b ∈ Finset.range (m + 1),
        (Work.Spaces.w z) ^ 2 * (Ab b) ^ 2
          ≤ Ssum * (Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * hh (m - b)) := by
      intro b hb
      have hb1 : b ≤ k := by
        have := Finset.mem_range.mp hb
        omega
      have hmbk : m - b ∈ Finset.range (k + 1) := by
        have := Finset.mem_range.mp hb
        exact Finset.mem_range.mpr (by omega)
      have hcb : ((m.choose b : ℝ)) ^ 2 ≤ ((k.choose b : ℝ)) ^ 2 := by
        have h1 : m.choose b ≤ k.choose b := Nat.choose_le_choose b hm
        have h2 : ((m.choose b : ℕ) : ℝ) ≤ ((k.choose b : ℕ) : ℝ) := by exact_mod_cast h1
        nlinarith [h2]
      have hkb : |Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ₀| ≤ K b := hK n b z θ₀
      have hsq2 : (Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ₀) ^ 2 ≤ (K b) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hkb 2
      have hcor := hz_ae (m - b) hmbk
      have hcor' : (Work.Spaces.DzIter (m - b) (fun z _ : ℝ => lam n F z) z 0) ^ 2
            * (Work.Spaces.w z) ^ 2
          ≤ Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * hh (m - b) := by
        rw [hhh]
        calc (Work.Spaces.DzIter (m - b) (fun z _ : ℝ => lam n F z) z 0) ^ 2
              * (Work.Spaces.w z) ^ 2
            = (Work.Spaces.w z) ^ 2
              * (Work.Spaces.DzIter (m - b) (fun z _ : ℝ => lam n F z) z 0) ^ 2 := by ring
          _ ≤ _ := hcor
      have hcK : ((m.choose b : ℝ)) ^ 2
            * (Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ₀) ^ 2
          ≤ ((k.choose b : ℝ)) ^ 2 * (K b) ^ 2 :=
        mul_le_mul hcb hsq2 (sq_nonneg _) (sq_nonneg _)
      have hmain := mul_le_mul hcK hcor'
        (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      have hSle : ((k.choose b : ℝ)) ^ 2 * (K b) ^ 2 ≤ Ssum := by
        rw [hSsum]
        exact Finset.single_le_sum (f := fun b => ((k.choose b : ℝ)) ^ 2 * (K b) ^ 2)
          (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
          (Finset.mem_range.mpr (by omega))
      have hC0 : 0 ≤ Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * hh (m - b) :=
        mul_nonneg (mul_nonneg hCmom0 hp2n0) (hhh0 _)
      calc (Work.Spaces.w z) ^ 2 * (Ab b) ^ 2
          = ((m.choose b : ℝ)) ^ 2
              * (Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ₀) ^ 2
              * ((Work.Spaces.DzIter (m - b) (fun z _ : ℝ => lam n F z) z 0) ^ 2
                * (Work.Spaces.w z) ^ 2) := by
            rw [hAb]
            ring
        _ ≤ ((k.choose b : ℝ)) ^ 2 * (K b) ^ 2
              * (Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * hh (m - b)) := hmain
        _ ≤ Ssum * (Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * hh (m - b)) :=
              mul_le_mul_of_nonneg_right hSle hC0
    have hsumprod : (∑ b ∈ Finset.range (m + 1),
          Ssum * (Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * hh (m - b)))
        = (Ssum * (Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)))
          * ∑ b ∈ Finset.range (m + 1), hh (m - b) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    calc (Work.Spaces.w z) ^ 2
          * (Work.Spaces.DzIter m (fun z _ : ℝ => chiR n z * lam n F z) z θ₀) ^ 2
        ≤ (Work.Spaces.w z) ^ 2 * (((m : ℝ) + 1) * ∑ b ∈ Finset.range (m + 1), (Ab b) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = ((m : ℝ) + 1) * ((Work.Spaces.w z) ^ 2
            * ∑ b ∈ Finset.range (m + 1), (Ab b) ^ 2) := by ring
      _ = ((m : ℝ) + 1) * ∑ b ∈ Finset.range (m + 1),
            (Work.Spaces.w z) ^ 2 * (Ab b) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ ((m : ℝ) + 1) * ∑ b ∈ Finset.range (m + 1),
            Ssum * (Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * hh (m - b)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
      _ = ((m : ℝ) + 1) * ((Ssum * (Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)))
            * ∑ b ∈ Finset.range (m + 1), hh (m - b)) := by rw [hsumprod]
      _ = ((m : ℝ) + 1) * ((Ssum * (Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)))
            * ∑ i ∈ Finset.range (m + 1), hh i) := by
          rw [show (∑ b ∈ Finset.range (m + 1), hh (m - b))
              = ∑ b ∈ Finset.range (m + 1), hh (m + 1 - 1 - b) from rfl,
            Finset.sum_range_reflect hh (m + 1)]
      _ ≤ ((m : ℝ) + 1) * ((Ssum * (Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)))
            * ∑ i ∈ Finset.range (k + 1), hh i) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ ?_)
            (by positivity)
          · exact Finset.sum_le_sum_of_subset_of_nonneg
              (fun i hi => Finset.mem_range.mpr (by
                have := Finset.mem_range.mp hi; omega))
              (fun i _ _ => hhh0 i)
          · exact mul_nonneg hSsum0 (mul_nonneg hCmom0 hp2n0)
      _ ≤ ((k : ℝ) + 1) * ((Ssum * (Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)))
            * ∑ i ∈ Finset.range (k + 1), hh i) :=
          mul_le_mul_of_nonneg_right (by
            have : m + 1 ≤ k + 1 := by omega
            exact_mod_cast this)
            (mul_nonneg (mul_nonneg hSsum0 (mul_nonneg hCmom0 hp2n0))
              (Finset.sum_nonneg fun i _ => hhh0 i))
      _ = ((k : ℝ) + 1) * Ssum * Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
            * ∑ i ∈ Finset.range (k + 1),
                (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.DzIter i F z θ
                    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
          rw [hhh]
          ring
  -- integrability of the majorant
  have hmeas : MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ))
      = MeasureTheory.Measure.restrict MeasureTheory.volume Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))
  have hmaj_int : MeasureTheory.Integrable
      (fun z => ((k : ℝ) + 1) * Ssum * Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
        * ∑ i ∈ Finset.range (k + 1),
            (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.DzIter i F z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ))) := by
    rw [hmeas]
    exact (integrable_finsetSum (Finset.range (k + 1))
      (fun i hi => hint i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))).const_mul _
  have hmain := MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hmaj_int hpoint
  -- compute the integral of the majorant
  have hInt : MeasureTheory.integral
      (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ)))
      (fun z => ∑ i ∈ Finset.range (k + 1),
        (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter i F z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
      = ∑ i ∈ Finset.range (k + 1),
          Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter i F z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) := by
    rw [hmeas]
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun i _ => rfl
    · intro i hi
      exact hint i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  have hL2 : ∀ i ∈ Finset.range (k + 1),
      Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter i F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
        ≤ Work.Spaces.HkSq α k F := fun i hi =>
    Work.Spaces.L2Sq_DzIter_le_HkSq α k F hF i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  have hsum_le : (∑ i ∈ Finset.range (k + 1),
      Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter i F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
      ≤ ((k : ℝ) + 1) * Work.Spaces.HkSq α k F := by
    calc (∑ i ∈ Finset.range (k + 1),
        Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter i F z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
        ≤ ∑ _i ∈ Finset.range (k + 1), Work.Spaces.HkSq α k F := Finset.sum_le_sum hL2
      _ = ((k : ℝ) + 1) * Work.Spaces.HkSq α k F := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hconst : 0 ≤ ((k : ℝ) + 1) * Ssum * Cmom :=
    mul_nonneg (mul_nonneg hk1 hSsum0) hCmom0
  have hmaj_val : MeasureTheory.integral
      (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ)))
      (fun z => ((k : ℝ) + 1) * Ssum * Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
        * ∑ i ∈ Finset.range (k + 1),
            (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.DzIter i F z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
      = ((k : ℝ) + 1) * Ssum * Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
        * (∑ i ∈ Finset.range (k + 1),
            Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter i F z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) := by
    rw [MeasureTheory.integral_const_mul, hInt]
  have hfinal : ((k : ℝ) + 1) * Ssum * Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
        * (∑ i ∈ Finset.range (k + 1),
            Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter i F z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
      ≤ (1 + ((k : ℝ) + 1) * Ssum * Cmom * ((k : ℝ) + 1))
          * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F := by
    have hHk := Work.Spaces.HkSq_nonneg α k F
    have hstep : ((k : ℝ) + 1) * Ssum * Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
          * (∑ i ∈ Finset.range (k + 1),
              Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter i F z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
        ≤ ((k : ℝ) + 1) * Ssum * Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
          * (((k : ℝ) + 1) * Work.Spaces.HkSq α k F) :=
      mul_le_mul_of_nonneg_left hsum_le
        (mul_nonneg (mul_nonneg (mul_nonneg hk1 hSsum0) hCmom0) hp2n0)
    have hstep2 : ((k : ℝ) + 1) * Ssum * Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
          * (((k : ℝ) + 1) * Work.Spaces.HkSq α k F)
        ≤ (1 + ((k : ℝ) + 1) * Ssum * Cmom * ((k : ℝ) + 1))
          * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F := by
      nlinarith [hconst, hp2n0, hHk, hk1]
    linarith [hstep, hstep2]
  have hgoal_eq : MeasureTheory.integral
        (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ)))
        (fun z => (Work.Spaces.DzIter m
            (fun z _ => chiR n z * lam n F z) z θ₀) ^ 2 * (Work.Spaces.w z) ^ 2)
      = MeasureTheory.integral
        (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ)))
        (fun z => (Work.Spaces.w z) ^ 2
          * (Work.Spaces.DzIter m (fun z _ => chiR n z * lam n F z) z θ₀) ^ 2) :=
    integral_congr_ae (Eventually.of_forall fun z => by ring)
  rw [hgoal_eq]
  calc MeasureTheory.integral
        (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ)))
        (fun z => (Work.Spaces.w z) ^ 2
          * (Work.Spaces.DzIter m (fun z _ => chiR n z * lam n F z) z θ₀) ^ 2)
      ≤ MeasureTheory.integral
          (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ)))
          (fun z => ((k : ℝ) + 1) * Ssum * Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
            * ∑ i ∈ Finset.range (k + 1),
                (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.DzIter i F z θ
                    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)) :=
        hmain
    _ = ((k : ℝ) + 1) * Ssum * Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
        * (∑ i ∈ Finset.range (k + 1),
            Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter i F z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) := hmaj_val
    _ ≤ (1 + ((k : ℝ) + 1) * Ssum * Cmom * ((k : ℝ) + 1))
          * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F := hfinal

theorem lam_Dz_sq_le {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α k F)
    (hFs : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 2 ≤ n → ∀ (m : ℕ), m ≤ k → ∀ θ₀ : ℝ,
      MeasureTheory.integral
        (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi 0))
        (fun z => (Work.Spaces.DzIter m
            (fun z _ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
              * Work.FTS.PhiStar.Honesty.CptApp.lam n F z) z θ₀)^2 * (Work.Spaces.w z)^2)
      ≤ C * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F := by
  obtain ⟨K, hK0, hK⟩ := Work.FTS.PhiStar.Honesty.CptApp.LamAux.chiR_dzIter_boundAux
  have hlam : ∀ (n : ℕ), 1 ≤ n → ∀ m : ℕ,
      ContDiffOn ℝ m (fun z : ℝ => lam n F z) (Set.Ioi (0 : ℝ)) :=
    fun n hn m => Work.FTS.PhiStar.Honesty.CptApp.LamEst.lamContDiffOn hsm hn m
  have hint : ∀ (i : ℕ), i ≤ k →
      MeasureTheory.IntegrableOn
        (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter i F z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        Work.Spaces.Iz :=
    fun i hi => Work.FTS.PhiStar.Honesty.CptApp.LamEst.integrableOn_slice_L2 hsm hF hi
  obtain ⟨Cmom, hCmom0, hcorr⟩ :=
    Work.FTS.PhiStar.Honesty.CptApp.LamEst.lam_correction_sq_le hsm hF hFs
  exact lam_Dz_sq_le_of_estimates hsm hF hK0 hK hlam hCmom0 hcorr hint

end Work.FTS.PhiStar.Honesty.CptApp
