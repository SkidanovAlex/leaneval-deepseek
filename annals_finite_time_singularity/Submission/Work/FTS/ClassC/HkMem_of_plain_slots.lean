import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.remov.Baux.dthIter_abs_le_pthIter_sum
import Submission.Work.FTS.H2.STQ.Basic
import Submission.Work.FTS.LocData.HkMem_of_majorant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Local helpers

The reduction `HkMem α k f` from the *plain* slots `D_z^j f` and `D_z^j ∂_θ^r f` rests on one
pointwise estimate: on the open quadrant the mixed derivative `D_z^j D_θ^i f` (`i ≥ 1`) is a
`θ`-dependent linear combination of the plain slots `D_z^j ∂_θ^r f`, `1 ≤ r ≤ i`, whose
coefficients satisfy `|a_{i,r}(θ)| ≤ K_r sin(2θ)^r`.  The conormal factor `sin(2θ)^r` with
`r ≥ 1` pays for the difference between the `γ`-weight of the mixed slot and the `η`-weight of
the plain slots: `sin(2θ)^{r-γ/2} ≤ sin(2θ)^{-η/2}` as soon as `r ≥ (γ-η)/2`, which holds
because `r ≥ 1` and `γ ≤ 3/2`.  This gives the required domination. -/

/-- The level-`0` `ℋ^k`-integrand collapses to the square of the `η`-weighted profile. -/
theorem HkIntegrand_zero_eq_classC (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [Work.Spaces.HkIntegrand]
  simp

/-- If the product weight `Wt α z θ` does not vanish at a point of `Iz × Iθ`, then that point
lies in the open quadrant. -/
theorem Wt_ne_zero_quadrant {α z θ : ℝ} (hα : 0 < α) (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Work.Spaces.Iθ) (h : Work.Spaces.Wt α z θ ≠ 0) :
    0 < z ∧ 0 < θ ∧ θ < Real.pi / 2 := by
  have hz0 : 0 ≤ z := hz
  have hθI : 0 ≤ θ ∧ θ ≤ Real.pi / 2 := hθ
  have hw : Work.Spaces.w z ≠ 0 := fun hw0 => h (by rw [Work.Spaces.Wt, hw0, zero_mul])
  have hwt : Work.Spaces.wTheta α θ ≠ 0 := fun h0 => h (by rw [Work.Spaces.Wt, h0, mul_zero])
  have hzpos : 0 < z := by
    rcases lt_or_eq_of_le hz0 with h' | h'
    · exact h'
    · exfalso; apply hw; rw [← h']; simp [Work.Spaces.w]
  have hsin : Real.sin (2 * θ) ≠ 0 := by
    intro hs0
    apply hwt
    rw [Work.Spaces.wTheta, hs0]
    refine Real.zero_rpow ?_
    have hγ : 0 < Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
    intro hc
    linarith
  refine ⟨hzpos, ?_, ?_⟩
  · rcases lt_or_eq_of_le hθI.1 with h' | h'
    · exact h'
    · exact absurd (by rw [← h']; simp) hsin
  · rcases lt_or_eq_of_le hθI.2 with h' | h'
    · exact h'
    · exact absurd (by rw [h', show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]) hsin

/-- `SmoothOpen` is preserved by the iterates of `∂_θ`. -/
theorem SmoothOpen_pthIter_classC {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (r : ℕ) : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter r f) := by
  induction r with
  | zero => simpa using hf
  | succ r ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

/-- The expansion of `D_θ^i f` in the plain angular basis, at each point of the open
quadrant, for `f` which is `C^∞` there. -/
theorem dthCoef_expansion_Q0 {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (i : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DthIter i f z θ
        = ∑ r ∈ Finset.range (i + 1),
            Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ
              * Work.Spaces.pthIter r f z θ := by
  intro z θ hz hθ0 hθ1
  refine Work.FTS.EllipticEst.remov.selfdth.DthIter_expansion_local i f z θ ?_
  intro n
  exact (hsm.forall n).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
    (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩))

/-- **The mixed derivative in the plain angular basis.**  On the open quadrant,
`D_z^j D_θ^{m+1} f = Σ_{1 ≤ r ≤ m+1} a_{m+1,r}(θ) · D_z^j ∂_θ^r f`, a linear combination of the
plain slots with `θ`-only coefficients (the `r = 0` term of the expansion of `D_θ^{m+1}`
vanishes). -/
theorem mixed_eq_sum_dthCoef_succ {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (m j : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed j (m + 1) f z θ
        = ∑ r ∈ Finset.Icc 1 (m + 1),
            Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) r θ
              * Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ := by
  intro z θ hz hθ0 hθ1
  have hexp := dthCoef_expansion_Q0 hsm (m + 1)
  have h1 : Work.Spaces.DzIter j (Work.Spaces.DthIter (m + 1) f) z θ
      = Work.Spaces.DzIter j (fun z θ => ∑ r ∈ Finset.range (m + 2),
          Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) r θ
            * Work.Spaces.pthIter r f z θ) z θ :=
    Work.FTS.EllipticEst.SmoothOpen.DzIter_congr
      (F := Work.Spaces.DthIter (m + 1) f)
      (G := fun z θ => ∑ r ∈ Finset.range (m + 2),
          Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) r θ
            * Work.Spaces.pthIter r f z θ)
      (fun z' θ' hz' hθ0' hθ1' => hexp z' θ' hz' hθ0' hθ1') j z θ hz hθ0 hθ1
  have h2 : Work.Spaces.DzIter j (fun z θ => ∑ r ∈ Finset.range (m + 2),
        Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) r θ
          * Work.Spaces.pthIter r f z θ) z θ
      = ∑ r ∈ Finset.range (m + 2),
          Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) r θ
            * Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ :=
    Work.FTS.H2.STQ.DzIter_sum_theta_coeff_eqOn (Finset.range (m + 2))
      (fun r θ => Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) r θ)
      (fun r => Work.Spaces.pthIter r f) Work.FTS.EllipticEst.isOpen_Q0
      (fun r _ => SmoothOpen_pthIter_classC hsm r) j
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩)
  have h3 : (∑ r ∈ Finset.range (m + 2),
        Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) r θ
          * Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ)
      = ∑ r ∈ Finset.Icc 1 (m + 1),
          Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) r θ
            * Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ :=
    Work.FTS.EllipticEst.remov.Baux.sum_range_succ_eq_sum_Icc m _ (by
      have h0 : Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) 0 θ = 0 := by
        have h := congrFun (Work.FTS.EllipticEst.remov.selfdth.dthCoef_succ_zero m) θ
        simpa using h
      show Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) 0 θ
          * Work.Spaces.DzIter j (Work.Spaces.pthIter 0 f) z θ = 0
      rw [h0, zero_mul])
  show Work.Spaces.DzIter j (Work.Spaces.DthIter (m + 1) f) z θ = _
  rw [h1, h2, h3]

/-- **The pointwise domination of a mixed slot by the plain slots.**  For `f` which is `C^∞` on
the open quadrant and `i ≥ 1`,

`(D_z^j D_θ^i f · W)² ≤ C · Σ_{r ∈ Icc 1 i} (D_z^j ∂_θ^r f · w/sin(2θ)^{η/2})²`

on `[0,∞) × [0,π/2]`, with `C > 0` independent of `(z,θ)`. -/
theorem plainSlot_domination_succ {α : ℝ} (hα : 0 < α) (hγ : Work.Spaces.gam α ≤ 3 / 2)
    {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f) (m j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.mixed j (m + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ C * ∑ r ∈ Finset.Icc 1 (m + 1),
            (Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  classical
  have hcoef : ∀ r : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ θ : ℝ,
      |Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) r θ|
        ≤ K * |Real.sin (2 * θ)| ^ r :=
    fun r => Work.FTS.EllipticEst.remov.selfdth.DthCoef_sin_pow_bound (m + 1) r
  let Kc : ℕ → ℝ := fun r => Classical.choose (hcoef r)
  have hKcpos : ∀ r : ℕ, 0 < Kc r := fun r => (Classical.choose_spec (hcoef r)).1
  have hKcle : ∀ (r : ℕ) (θ : ℝ),
      |Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) r θ|
        ≤ Kc r * |Real.sin (2 * θ)| ^ r :=
    fun r θ => (Classical.choose_spec (hcoef r)).2 θ
  refine ⟨∑ r ∈ Finset.Icc 1 (m + 1), (Kc r) ^ 2, ?_, ?_⟩
  · refine Finset.sum_pos' (fun r _ => sq_nonneg _) ⟨1, ?_, pow_pos (hKcpos 1) 2⟩
    simp [Finset.mem_Icc]
  · intro z hz θ hθ
    by_cases hW : Work.Spaces.Wt α z θ = 0
    · have hzero : (Work.Spaces.mixed j (m + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2 = 0 := by
        rw [hW, mul_zero]; simp
      rw [hzero]
      exact mul_nonneg (Finset.sum_nonneg fun r _ => sq_nonneg _)
        (Finset.sum_nonneg fun r _ => sq_nonneg _)
    · obtain ⟨hzpos, hθ0, hθ1⟩ := Wt_ne_zero_quadrant hα hz hθ hW
      have hs : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      have hw_nonneg : 0 ≤ Work.Spaces.w z := by
        rw [Work.Spaces.w]
        exact div_nonneg (sq_nonneg _) (sq_nonneg _)
      have hsn_gam : 0 < (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) :=
        Real.rpow_pos_of_pos hs _
      have hsn_eta : 0 < (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) :=
        Real.rpow_pos_of_pos hs _
      -- the expansion bound on `|mixed|`
      have hexp := mixed_eq_sum_dthCoef_succ hsm m j z θ hzpos hθ0 hθ1
      have hD_bound : |Work.Spaces.mixed j (m + 1) f z θ|
          ≤ ∑ r ∈ Finset.Icc 1 (m + 1), Kc r * (Real.sin (2 * θ)) ^ r
              * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ| := by
        have hsinabs : |Real.sin (2 * θ)| = Real.sin (2 * θ) := abs_of_pos hs
        rw [hexp]
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun r hr => ?_)
        calc |Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) r θ
              * Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ|
            = |Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) r θ|
              * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ| := abs_mul _ _
          _ ≤ (Kc r * |Real.sin (2 * θ)| ^ r)
              * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ| :=
              mul_le_mul_of_nonneg_right (hKcle r θ) (abs_nonneg _)
          _ = Kc r * (Real.sin (2 * θ)) ^ r
              * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ| := by
              rw [hsinabs]
      -- the weight of the mixed slot
      have hWt_abs : |Work.Spaces.Wt α z θ|
          = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
        rw [Work.Spaces.Wt, Work.Spaces.wTheta, abs_mul, abs_of_nonneg (le_of_lt hsn_gam),
          abs_of_nonneg hw_nonneg]
      -- the exponent comparison `sin(2θ)^{r-γ/2} ≤ sin(2θ)^{-η/2}`: here `r ≥ 1`, `γ ≤ 3/2`
      have hexp_le : ∀ r ∈ Finset.Icc 1 (m + 1),
          (Real.sin (2 * θ)) ^ ((r : ℝ) - Work.Spaces.gam α / 2)
            ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := by
        intro r hr
        have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
        refine Real.rpow_le_rpow_of_exponent_ge hs hsin1 ?_
        have hr1' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
        have hg : 1 + α / 10 ≤ 3 / 2 := by
          have h := hγ; rwa [Work.Spaces.gam] at h
        rw [Work.Spaces.eta]
        linarith
      have hrpow_split : ∀ r : ℕ,
          (Real.sin (2 * θ)) ^ r * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))
            = (Real.sin (2 * θ)) ^ ((r : ℝ) - Work.Spaces.gam α / 2) := by
        intro r
        rw [← Real.rpow_natCast, ← Real.rpow_add hs]
        congr 1
      have hwd_nonneg : 0 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
        div_nonneg hw_nonneg (le_of_lt (Real.rpow_pos_of_pos hs _))
      have hsn_eta_nn : 0 ≤ Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) :=
        mul_nonneg hw_nonneg (le_of_lt hsn_eta)
      have hsum_bound : |Work.Spaces.mixed j (m + 1) f z θ * Work.Spaces.Wt α z θ|
          ≤ ∑ r ∈ Finset.Icc 1 (m + 1), Kc r
              * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))| := by
        calc |Work.Spaces.mixed j (m + 1) f z θ * Work.Spaces.Wt α z θ|
            = |Work.Spaces.mixed j (m + 1) f z θ| * |Work.Spaces.Wt α z θ| := abs_mul _ _
          _ = |Work.Spaces.mixed j (m + 1) f z θ|
                * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) := by
              rw [hWt_abs]
          _ ≤ (∑ r ∈ Finset.Icc 1 (m + 1), Kc r * (Real.sin (2 * θ)) ^ r
                * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ|)
              * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) :=
              mul_le_mul_of_nonneg_right hD_bound (by positivity)
          _ = ∑ r ∈ Finset.Icc 1 (m + 1), Kc r * (Real.sin (2 * θ)) ^ r
                * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ|
                * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) :=
              Finset.sum_mul _ _ _
          _ = ∑ r ∈ Finset.Icc 1 (m + 1), Kc r
                * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ| * Work.Spaces.w z
                * ((Real.sin (2 * θ)) ^ r
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) := by
              refine Finset.sum_congr rfl fun r hr => by ring
          _ = ∑ r ∈ Finset.Icc 1 (m + 1), Kc r
                * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ| * Work.Spaces.w z
                * (Real.sin (2 * θ)) ^ ((r : ℝ) - Work.Spaces.gam α / 2) := by
              refine Finset.sum_congr rfl fun r hr => by rw [hrpow_split r]
          _ ≤ ∑ r ∈ Finset.Icc 1 (m + 1), Kc r
                * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ| * Work.Spaces.w z
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := by
              refine Finset.sum_le_sum fun r hr => mul_le_mul_of_nonneg_left (hexp_le r hr) ?_
              exact mul_nonneg (mul_nonneg (le_of_lt (hKcpos r)) (abs_nonneg _)) hw_nonneg
          _ = ∑ r ∈ Finset.Icc 1 (m + 1), Kc r
                * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ
                    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))| := by
              refine Finset.sum_congr rfl fun r hr => ?_
              have hwd : Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
                  = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := by
                rw [div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hs)]
              rw [hwd, abs_mul, abs_of_nonneg hsn_eta_nn]
              ring
      -- Cauchy–Schwarz in the sum
      calc (Work.Spaces.mixed j (m + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2
          = |Work.Spaces.mixed j (m + 1) f z θ * Work.Spaces.Wt α z θ| ^ 2 := by
            rw [sq_abs]
        _ ≤ (∑ r ∈ Finset.Icc 1 (m + 1), Kc r
              * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))|) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hsum_bound 2
        _ ≤ (∑ r ∈ Finset.Icc 1 (m + 1), (Kc r) ^ 2)
              * ∑ r ∈ Finset.Icc 1 (m + 1),
                  (|Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ
                    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))|) ^ 2 :=
            Finset.sum_mul_sq_le_sq_mul_sq _ _ _
        _ = (∑ r ∈ Finset.Icc 1 (m + 1), (Kc r) ^ 2)
              * ∑ r ∈ Finset.Icc 1 (m + 1),
                  (Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ
                    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
            rw [Finset.sum_congr rfl (fun r _ => sq_abs _)]

/-- **The pointwise domination of a mixed slot by the plain slots**, in the form needed by the
assembly (`i ≥ 1`). -/
theorem plainSlot_domination {α : ℝ} (hα : 0 < α) (hγ : Work.Spaces.gam α ≤ 3 / 2)
    {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f) (i j : ℕ) (hi : 1 ≤ i) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ C * ∑ r ∈ Finset.Icc 1 i,
            (Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  exact plainSlot_domination_succ hα hγ hsm m j

/-! ## The constant attached to a mixed slot -/

/-- The constant of the pointwise domination for the slot `(i,j)`; for `i = 0` no mixed slot
occurs in the integrand of level `≥ 1`, so the value is irrelevant and set to `1`. -/
noncomputable def plainSlotC (α : ℝ) (hα : 0 < α) (hγ : Work.Spaces.gam α ≤ 3 / 2)
    (f : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen f) (i j : ℕ) : ℝ :=
  if hi : 1 ≤ i then Classical.choose (plainSlot_domination hα hγ hsm i j hi) else 1

theorem plainSlotC_pos {α : ℝ} (hα : 0 < α) (hγ : Work.Spaces.gam α ≤ 3 / 2)
    {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f) {i j : ℕ} (hi : 1 ≤ i) :
    0 < plainSlotC α hα hγ f hsm i j := by
  rw [plainSlotC, dif_pos hi]
  exact (Classical.choose_spec (plainSlot_domination hα hγ hsm i j hi)).1

theorem plainSlotC_spec {α : ℝ} (hα : 0 < α) (hγ : Work.Spaces.gam α ≤ 3 / 2)
    {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f) {i j : ℕ} (hi : 1 ≤ i) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ plainSlotC α hα hγ f hsm i j * ∑ r ∈ Finset.Icc 1 i,
            (Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [plainSlotC, dif_pos hi]
  exact (Classical.choose_spec (plainSlot_domination hα hγ hsm i j hi)).2

/-! ## The assembly -/

/-- **The reduction of `ℋ^k`-membership to the plain slots.**  If `f` is `C^∞` on the open
quadrant and each plain slot `D_z^j f` (`j ≤ k`) and `D_z^j ∂_θ^r f` (`1 ≤ r`, `r + j ≤ k`) is
`ℋ^0`-honest, then `f ∈ ℋ^k`: the mixed slots of the `ℋ^k`-integrand are dominated by the plain
slots (`plainSlot_domination`), and the resulting finite sum of honest integrands is an honest
majorant. -/
theorem HkMem_of_plain_slots {α : ℝ} (hα : 0 < α) (hγ : Work.Spaces.gam α ≤ 3 / 2)
    {k : ℕ} {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hz : ∀ i ≤ k, Work.Spaces.HkMem α 0 (Work.Spaces.DzIter i f))
    (hp : ∀ j r : ℕ, 1 ≤ r → r + j ≤ k →
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter j (Work.Spaces.pthIter r f))) :
    Work.Spaces.HkMem α k f := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hsm.continuousOn_HkIntegrand α k
  set M : ℝ → ℝ → ℝ := fun z θ =>
      (∑ j ∈ Finset.range (k + 1), Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j f) z θ)
      + ∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.Icc 1 (k - j),
          plainSlotC α hα hγ f hsm i j *
            (∑ r ∈ Finset.Icc 1 i,
              Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j (Work.Spaces.pthIter r f))
                z θ) with hMdef
  have hA : ∀ z ∈ Work.Spaces.Iz, ∀ j ∈ Finset.range (k + 1),
      Integrable (fun θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j f) z θ)
        (volume.restrict Work.Spaces.Iθ) :=
    fun z hz' j hj => (hz j (by have h := Finset.mem_range.mp hj; omega)).1 z hz'
  have hB : ∀ z ∈ Work.Spaces.Iz, ∀ j ∈ Finset.range (k + 1),
      ∀ i ∈ Finset.Icc 1 (k - j), ∀ r ∈ Finset.Icc 1 i,
      Integrable (fun θ => Work.Spaces.HkIntegrand α 0
          (Work.Spaces.DzIter j (Work.Spaces.pthIter r f)) z θ)
        (volume.restrict Work.Spaces.Iθ) :=
    fun z hz' j hj i hi r hr =>
      (hp j r (Finset.mem_Icc.mp hr).1
        (by have h1 := (Finset.mem_Icc.mp hr).2
            have h2 := (Finset.mem_Icc.mp hi).2
            have h3 := Finset.mem_range.mp hj
            omega)).1 z hz'
  refine Work.FTS.LocData.HkMem_of_majorant (M := M) α k hcont ?_ ?_ ?_
  · intro z hz'
    rw [hMdef]
    refine Integrable.add ?_ ?_
    · exact integrable_finsetSum _ (hA z hz')
    · refine integrable_finsetSum _ fun j hj =>
        integrable_finsetSum _ fun i hi =>
          Integrable.const_mul (integrable_finsetSum _ (hB z hz' j hj i hi)) _
  · -- the `θ`-integral of the majorant is a finite sum of honest integrands
    set G : ℝ → ℝ := fun z =>
        (∑ j ∈ Finset.range (k + 1),
            ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j f) z θ)
        + ∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.Icc 1 (k - j),
            plainSlotC α hα hγ f hsm i j *
              (∑ r ∈ Finset.Icc 1 i,
                ∫ θ in Work.Spaces.Iθ,
                  Work.Spaces.HkIntegrand α 0
                    (Work.Spaces.DzIter j (Work.Spaces.pthIter r f)) z θ) with hGdef
    have hGint : IntegrableOn G Work.Spaces.Iz := by
      rw [hGdef]
      refine Integrable.add ?_ ?_
      · refine integrable_finsetSum _ fun j hj =>
          (hz j (by have h := Finset.mem_range.mp hj; omega)).2
      · refine integrable_finsetSum _ fun j hj =>
          integrable_finsetSum _ fun i hi =>
            Integrable.const_mul (integrable_finsetSum _ fun r hr =>
              (hp j r (Finset.mem_Icc.mp hr).1
                (by have h1 := (Finset.mem_Icc.mp hr).2
                    have h2 := (Finset.mem_Icc.mp hi).2
                    have h3 := Finset.mem_range.mp hj
                    omega)).2) _
    have hpoint : ∀ z ∈ Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, M z θ) = G z := by
      intro z hz'
      have hsingle : (∫ θ in Work.Spaces.Iθ, ∑ j ∈ Finset.range (k + 1),
            Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j f) z θ)
          = ∑ j ∈ Finset.range (k + 1),
              ∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j f) z θ :=
        MeasureTheory.integral_finsetSum _ (hA z hz')
      have hdouble : (∫ θ in Work.Spaces.Iθ, ∑ j ∈ Finset.range (k + 1),
            ∑ i ∈ Finset.Icc 1 (k - j), plainSlotC α hα hγ f hsm i j *
              (∑ r ∈ Finset.Icc 1 i, Work.Spaces.HkIntegrand α 0
                (Work.Spaces.DzIter j (Work.Spaces.pthIter r f)) z θ))
          = ∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.Icc 1 (k - j),
              plainSlotC α hα hγ f hsm i j *
                (∑ r ∈ Finset.Icc 1 i,
                  ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
                    (Work.Spaces.DzIter j (Work.Spaces.pthIter r f)) z θ) := by
        rw [MeasureTheory.integral_finsetSum _ fun j hj =>
          integrable_finsetSum _ fun i hi =>
            Integrable.const_mul (integrable_finsetSum _ (hB z hz' j hj i hi)) _]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [MeasureTheory.integral_finsetSum _ fun i hi =>
          Integrable.const_mul (integrable_finsetSum _ (hB z hz' j hj i hi)) _]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [MeasureTheory.integral_const_mul]
        congr 1
        exact MeasureTheory.integral_finsetSum _ (hB z hz' j hj i hi)
      have hInt1 : Integrable (fun θ => ∑ j ∈ Finset.range (k + 1),
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j f) z θ)
          (volume.restrict Work.Spaces.Iθ) := integrable_finsetSum _ (hA z hz')
      have hInt2 : Integrable (fun θ => ∑ j ∈ Finset.range (k + 1),
          ∑ i ∈ Finset.Icc 1 (k - j), plainSlotC α hα hγ f hsm i j *
            (∑ r ∈ Finset.Icc 1 i, Work.Spaces.HkIntegrand α 0
              (Work.Spaces.DzIter j (Work.Spaces.pthIter r f)) z θ))
          (volume.restrict Work.Spaces.Iθ) :=
        integrable_finsetSum _ fun j hj => integrable_finsetSum _ fun i hi =>
          Integrable.const_mul (integrable_finsetSum _ (hB z hz' j hj i hi)) _
      rw [hMdef, MeasureTheory.integral_add hInt1 hInt2, hsingle, hdouble, hGdef]
    exact hGint.congr_fun (fun z hz' => (hpoint z hz').symm) measurableSet_Ici
  · -- the pointwise domination of the integrand by the majorant
    intro z hz' θ hθ'
    rw [hMdef, Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum]
    refine le_trans (Finset.sum_le_sum fun j hj => ?_) (le_of_eq Finset.sum_add_distrib)
    rw [Work.FTS.EllipticEst.sliceGroup]
    refine add_le_add (le_of_eq ?_) (Finset.sum_le_sum fun i hi => ?_)
    · exact (HkIntegrand_zero_eq_classC α (Work.Spaces.DzIter j f) z θ).symm
    · have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      refine le_trans (plainSlotC_spec hα hγ hsm hi1 z hz' θ hθ') ?_
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (plainSlotC_pos hα hγ hsm hi1))
      exact le_of_eq (Finset.sum_congr rfl fun r hr =>
        (HkIntegrand_zero_eq_classC α (Work.Spaces.DzIter j (Work.Spaces.pthIter r f))
          z θ).symm)

end Work.FTS.ClassC
