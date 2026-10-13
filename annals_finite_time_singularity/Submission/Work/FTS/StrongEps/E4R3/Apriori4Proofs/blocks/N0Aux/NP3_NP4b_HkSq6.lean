import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.Maj6Split
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.N0row_defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup4
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.LocData.HkIntegrand_const_mul
import Submission.Work.FTS.StrongPersist.H6Aux.Facts
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.H2.L12HQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux

open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! ## Auxiliary lemmas

`HkSq` is homogeneous of degree two in the amplitude *unconditionally* (the version
`Work.FTS.LocData.HkSq_const_mul` carries an unused `HkMem` hypothesis, which we would have to
produce for the product `L₁₂(w)·w`; the identity itself needs none), and the two smallness
absorptions `α^{-2}·(c·|w|₄)² ≤ c²·(C₀')²` and `α^{-2}·HkSq α 2 w ≤ (C₀')²·α²` used at the end. -/

/-- **Homogeneity of `HkSq` in the amplitude, unconditionally.** -/
private theorem HkSq_const_mul_u (α : ℝ) (k : ℕ) (β : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α k (fun z θ => β * f z θ) = β ^ 2 * Work.Spaces.HkSq α k f := by
  have hpoint : ∀ z θ : ℝ,
      Work.Spaces.HkIntegrand α k (fun z θ => β * f z θ) z θ
        = β ^ 2 * Work.Spaces.HkIntegrand α k f z θ :=
    fun z θ => Work.FTS.LocData.HkIntegrand_const_mul α k β f z θ
  have hinner : ∀ z : ℝ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z θ => β * f z θ) z θ)
        = β ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
    intro z
    rw [funext (fun θ => hpoint z θ)]
    exact MeasureTheory.integral_const_mul (β ^ 2) _
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  simp only [hinner]
  exact MeasureTheory.integral_const_mul (β ^ 2) _

/-- **The absorption of the low `ℋ⁴`-jet of the radial factor.**  If `|ξ| ≤ C₀'·α²` with
`0 < α ≤ 1` then `α^{-2}·(c·ξ)² ≤ c²·C₀'²`. -/
private lemma scale_sq_le {α c ξ C₀' : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hc : 0 ≤ c) (_hC₀' : 0 ≤ C₀') (hξ0 : 0 ≤ ξ) (h : ξ ≤ C₀' * α ^ 2) :
    (1 / α) ^ 2 * (c * ξ) ^ 2 ≤ c ^ 2 * C₀' ^ 2 := by
  have hα2 : α ^ 2 ≤ 1 := by nlinarith [hα0, hα1]
  have h1 : ξ ^ 2 ≤ (C₀' * α ^ 2) ^ 2 := pow_le_pow_left₀ hξ0 h 2
  have h2 : (1 / α) ^ 2 * ξ ^ 2 ≤ (1 / α) ^ 2 * (C₀' * α ^ 2) ^ 2 :=
    mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  have heq : (1 / α) ^ 2 * (C₀' * α ^ 2) ^ 2 = C₀' ^ 2 * α ^ 2 := by field_simp
  have h3 : C₀' ^ 2 * α ^ 2 ≤ C₀' ^ 2 := by nlinarith [sq_nonneg C₀', hα2]
  calc (1 / α) ^ 2 * (c * ξ) ^ 2 = c ^ 2 * ((1 / α) ^ 2 * ξ ^ 2) := by ring
    _ ≤ c ^ 2 * (C₀' ^ 2 * α ^ 2) := by
        rw [← heq]; exact mul_le_mul_of_nonneg_left h2 (sq_nonneg c)
    _ ≤ c ^ 2 * C₀' ^ 2 := mul_le_mul_of_nonneg_left h3 (sq_nonneg c)

/-- **The absorption of the `ℋ²`-slot against the smallness.**  If `H2 ≤ C₀'²·α⁴`, `H6 ≥ 0` and
`0 < α ≤ 1` then `α^{-2}·c²·H6·H2 ≤ c²·C₀'²·H6`. -/
private lemma scale_Hsq_le {α c H6 H2 C₀' : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hc : 0 ≤ c) (_hC₀' : 0 ≤ C₀') (hH6 : 0 ≤ H6) (h2 : H2 ≤ C₀' ^ 2 * α ^ 4) :
    (1 / α) ^ 2 * (c ^ 2 * H6 * H2) ≤ c ^ 2 * C₀' ^ 2 * H6 := by
  have hα2 : α ^ 2 ≤ 1 := by nlinarith [hα0, hα1]
  have h1 : (1 / α) ^ 2 * H2 ≤ (1 / α) ^ 2 * (C₀' ^ 2 * α ^ 4) :=
    mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  have heq : (1 / α) ^ 2 * (C₀' ^ 2 * α ^ 4) = C₀' ^ 2 * α ^ 2 := by field_simp
  have h3 : C₀' ^ 2 * α ^ 2 ≤ C₀' ^ 2 := by nlinarith [sq_nonneg C₀', hα2]
  calc (1 / α) ^ 2 * (c ^ 2 * H6 * H2) = c ^ 2 * H6 * ((1 / α) ^ 2 * H2) := by ring
    _ ≤ c ^ 2 * H6 * (C₀' ^ 2 * α ^ 2) := by
        rw [← heq]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ c ^ 2 * H6 * C₀' ^ 2 := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = c ^ 2 * C₀' ^ 2 * H6 := by ring

/-
Route hint.  Write `NP3 α w = (1/α) • (Lᵢ · w)` and `NP4b α w = (3/(2α)) • (Lᵢ · Dth w)` with
the radial function `Lᵢ z := Work.Construction.L12 w z`, use
`Work.Spaces.HkSq_const_mul` to pull the scalar out, then the engine
`Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.radialMaj6_split` with `X := Lᵢ`,
`f := w` resp. `f := Work.Spaces.Dth w` (all hypotheses: `ContDiffOn ℝ 6 Lᵢ (Ioi 0)` from
`ClassC.reg` + `EllipticEst.UopHk.contDiffOn_L12_k`, `SmoothOpen f` from `ClassC.reg`+`Dth`,
`HkMem α 6 f` from `ClassC.mem` (`Dth`: `HkMem α 7 w` and `IPGen`/`HkMem_Dth_le`), and the jet
bounds `Blo := CL4 * Xn α w`, `Bhi := CL6 * HkNorm α 6 w` from
`H6Pair6Aux.L12Sup4` / `H6Pair6Aux.L12Sup6`).
The side bounds are `HkSq α 6 (Dth w) ≤ HkSq α 7 w` and `HkSq α 2 (Dth w) ≤ HkSq α 3 w`
(`StrongPersist.H6Aux.HkSq_Dth_le_succ'`), `HkSq α 2 w ≤ HkSq α 4 w = (Xn α w)² ≤ C₀²α⁴`
(`H6Aux.HkSq_mono_order`), so every `α`-power is absorbed by the smallness `Xn α w ≤ C₀α²`.
-/
theorem NP3_NP4b_HkSq6 : ∀ C₀ : ℝ, ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ w : Work.FTS.Galerkin.Fn,
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP3 α w)
        ≤ K * (1 + Work.Spaces.HkSq α 6 w) ∧
    Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP4b α w)
        ≤ K * (1 + Work.Spaces.HkSq α 7 w) := by
  intro C₀
  obtain ⟨C₄, hC₄pos, hC₄⟩ := Work.FTS.StrongPersist.H6Pair6Aux.L12Sup4
  obtain ⟨C₆, hC₆pos, hC₆⟩ := Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
  obtain ⟨CA, hCApos, hCA⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.radialMaj6_split
  set K : ℝ := CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2 * (9 / 4) + 1 with hK
  refine ⟨K, ?_, ?_⟩
  · have h1 : 0 ≤ CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2 * (9 / 4) := by positivity
    rw [hK]; linarith
  intro α hαIoc w hcls hXn
  have hα0 : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hα10 : -(1 / 10 : ℝ) ≤ α := by linarith
  have hreg : Work.FTS.EllipticEst.SmoothOpen w := hcls.reg
  have hmem7 : Work.Spaces.HkMem α 7 w := hcls.mem
  have hmem6 : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hreg 6 (by norm_num) hmem7
  have hmem4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hreg 4 (by norm_num) hmem7
  have hmem3 : Work.Spaces.HkMem α 3 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hreg 3 (by norm_num) hmem7
  have hl12 : Work.Construction.L12 w 0 = 0 := hcls.l12
  -- ## The smallness
  have hC₀'nn : (0 : ℝ) ≤ max C₀ 0 := le_max_right _ _
  have hXn' : Work.FTS.Nonlin.Xn α w ≤ max C₀ 0 * α ^ 2 :=
    le_trans hXn (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (sq_nonneg α))
  have hXn4sq : Work.Spaces.HkSq α 4 w ≤ (max C₀ 0) ^ 2 * α ^ 4 := by
    have h1 : (Work.Spaces.HkNorm α 4 w) ^ 2 ≤ (max C₀ 0 * α ^ 2) ^ 2 :=
      pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 w) hXn' 2
    have h2 : Work.Spaces.HkSq α 4 w ≤ (max C₀ 0 * α ^ 2) ^ 2 := by
      simpa only [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 w)] using h1
    calc Work.Spaces.HkSq α 4 w ≤ (max C₀ 0 * α ^ 2) ^ 2 := h2
      _ = (max C₀ 0) ^ 2 * α ^ 4 := by ring
  have hE6nn : 0 ≤ Work.Spaces.HkSq α 6 w := Work.Spaces.HkSq_nonneg α 6 w
  have hE7nn : 0 ≤ Work.Spaces.HkSq α 7 w := Work.Spaces.HkSq_nonneg α 7 w
  have hH2le : Work.Spaces.HkSq α 2 w ≤ (max C₀ 0) ^ 2 * α ^ 4 :=
    le_trans (Work.FTS.StrongPersist.H6Aux.HkSq_mono_order α (by norm_num) hmem4) hXn4sq
  have hH3le : Work.Spaces.HkSq α 3 w ≤ (max C₀ 0) ^ 2 * α ^ 4 :=
    le_trans (Work.FTS.StrongPersist.H6Aux.HkSq_mono_order α (by norm_num) hmem4) hXn4sq
  have hE6le7 : Work.Spaces.HkSq α 6 w ≤ Work.Spaces.HkSq α 7 w :=
    Work.FTS.StrongPersist.H6Aux.HkSq_mono_order α (by norm_num) hmem7
  -- ## The radial factor: smoothness and the two jet bounds
  have hXcd : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 w z) (Set.Ioi 0) := by
    have h := Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 6 w hα0 hα1 hreg hmem6
      (by norm_num : 2 ≤ 6)
    exact h.congr (fun x _ =>
      (congrFun (Work.FTS.H2.constructionL12_eq_ellipticL12 w) x).symm)
  have hLo : ∀ j : ℕ, j ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 w z) z|
        ≤ C₄ * Work.FTS.Nonlin.Xn α w :=
    fun j hj z hz => hC₄ α w hα0 hα1 hreg hmem6 hl12 j hj z hz
  have hHi : ∀ j : ℕ, j ≤ 6 → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 w z) z|
        ≤ C₆ * Work.Spaces.HkNorm α 6 w :=
    fun j hj z hz => hC₆ α w hα0 hα1 hreg hmem6 hmem7 hl12 j hj z hz
  -- ## The engine, for an arbitrary field `f`
  have hEng : ∀ (f : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.HkMem α 6 f →
      Work.Spaces.HkSq α 6 (fun z θ => Work.Construction.L12 w z * f z θ)
        ≤ CA * ((C₄ * Work.FTS.Nonlin.Xn α w) ^ 2 * Work.Spaces.HkSq α 6 f
            + (C₆ * Work.Spaces.HkNorm α 6 w) ^ 2 * Work.Spaces.HkSq α 2 f) := by
    intro f hf hm
    exact hCA α (fun z => Work.Construction.L12 w z) f (C₄ * Work.FTS.Nonlin.Xn α w)
      (C₆ * Work.Spaces.HkNorm α 6 w) hXcd hf hm
      (mul_nonneg hC₄pos.le (Work.Spaces.HkNorm_nonneg α 4 w))
      (mul_nonneg hC₆pos.le (Work.Spaces.HkNorm_nonneg α 6 w)) hLo hHi
  have heng3 := hEng w hreg hmem6
  have hDthMem : Work.Spaces.HkMem α 6 (Work.Spaces.Dth w) :=
    Work.FTS.IPGen.HkMem_Dth_le hα10 hreg hmem7
  have heng4 := hEng (Work.Spaces.Dth w) hreg.Dth hDthMem
  have hN6 : (C₆ * Work.Spaces.HkNorm α 6 w) ^ 2 = C₆ ^ 2 * Work.Spaces.HkSq α 6 w := by
    rw [mul_pow, Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 w)]
  have hs1 : (1 / α) ^ 2 * (C₄ * Work.FTS.Nonlin.Xn α w) ^ 2
      ≤ C₄ ^ 2 * (max C₀ 0) ^ 2 :=
    scale_sq_le hα0 hα1 hC₄pos.le hC₀'nn (Work.Spaces.HkNorm_nonneg α 4 w) hXn'
  -- ## `NP3`
  have hsc3 : Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP3 α w)
      = (1 / α) ^ 2 * Work.Spaces.HkSq α 6
          (fun z θ => Work.Construction.L12 w z * w z θ) := by
    change Work.Spaces.HkSq α 6 (fun z θ => (1 / α)
      * (Work.Construction.L12 w z * w z θ))
      = (1 / α) ^ 2 * Work.Spaces.HkSq α 6
          (fun z θ => Work.Construction.L12 w z * w z θ)
    exact HkSq_const_mul_u α 6 (1 / α) _
  have hs2 : (1 / α) ^ 2
      * (C₆ ^ 2 * Work.Spaces.HkSq α 6 w * Work.Spaces.HkSq α 2 w)
      ≤ C₆ ^ 2 * (max C₀ 0) ^ 2 * Work.Spaces.HkSq α 6 w :=
    scale_Hsq_le hα0 hα1 hC₆pos.le hC₀'nn hE6nn hH2le
  have hb3 : Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP3 α w)
      ≤ CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2
          * (1 + Work.Spaces.HkSq α 6 w) := by
    calc Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP3 α w)
        = (1 / α) ^ 2 * Work.Spaces.HkSq α 6
            (fun z θ => Work.Construction.L12 w z * w z θ) := hsc3
      _ ≤ (1 / α) ^ 2 * (CA * ((C₄ * Work.FTS.Nonlin.Xn α w) ^ 2
            * Work.Spaces.HkSq α 6 w + (C₆ * Work.Spaces.HkNorm α 6 w) ^ 2
            * Work.Spaces.HkSq α 2 w)) :=
          mul_le_mul_of_nonneg_left heng3 (by positivity)
      _ = CA * ((1 / α) ^ 2 * ((C₄ * Work.FTS.Nonlin.Xn α w) ^ 2
              * Work.Spaces.HkSq α 6 w)
            + (1 / α) ^ 2 * (C₆ ^ 2 * Work.Spaces.HkSq α 6 w
              * Work.Spaces.HkSq α 2 w)) := by
          rw [hN6]; ring
      _ = CA * (((1 / α) ^ 2 * (C₄ * Work.FTS.Nonlin.Xn α w) ^ 2)
              * Work.Spaces.HkSq α 6 w
            + (1 / α) ^ 2 * (C₆ ^ 2 * Work.Spaces.HkSq α 6 w
              * Work.Spaces.HkSq α 2 w)) := by ring
      _ ≤ CA * (C₄ ^ 2 * (max C₀ 0) ^ 2 * Work.Spaces.HkSq α 6 w
            + C₆ ^ 2 * (max C₀ 0) ^ 2 * Work.Spaces.HkSq α 6 w) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ hs2) hCApos.le
          exact mul_le_mul_of_nonneg_right hs1 hE6nn
      _ = CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2 * Work.Spaces.HkSq α 6 w := by ring
      _ ≤ CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2
            * (1 + Work.Spaces.HkSq α 6 w) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hb3K : CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2
        * (1 + Work.Spaces.HkSq α 6 w) ≤ K * (1 + Work.Spaces.HkSq α 6 w) := by
    rw [hK]
    have h1 : 0 ≤ CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2 := by positivity
    have h2 : CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2
        ≤ CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2 * (9 / 4) + 1 := by nlinarith
    have h3 : 0 ≤ 1 + Work.Spaces.HkSq α 6 w := by linarith
    exact mul_le_mul_of_nonneg_right h2 h3
  -- ## `NP4b`
  have hsc4 : Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP4b α w)
      = (3 / (2 * α)) ^ 2 * Work.Spaces.HkSq α 6
          (fun z θ => Work.Construction.L12 w z * Work.Spaces.Dth w z θ) := by
    change Work.Spaces.HkSq α 6 (fun z θ => (3 / (2 * α))
      * (Work.Construction.L12 w z * Work.Spaces.Dth w z θ))
      = (3 / (2 * α)) ^ 2 * Work.Spaces.HkSq α 6
          (fun z θ => Work.Construction.L12 w z * Work.Spaces.Dth w z θ)
    exact HkSq_const_mul_u α 6 (3 / (2 * α)) _
  have hDth6le : Work.Spaces.HkSq α 6 (Work.Spaces.Dth w) ≤ Work.Spaces.HkSq α 7 w :=
    Work.FTS.StrongPersist.H6Aux.HkSq_Dth_le_succ' α hα10 6 hmem7
  have hDth2le : Work.Spaces.HkSq α 2 (Work.Spaces.Dth w) ≤ Work.Spaces.HkSq α 3 w :=
    Work.FTS.StrongPersist.H6Aux.HkSq_Dth_le_succ' α hα10 2 hmem3
  have hs2' : (1 / α) ^ 2
      * (C₆ ^ 2 * Work.Spaces.HkSq α 6 w * Work.Spaces.HkSq α 3 w)
      ≤ C₆ ^ 2 * (max C₀ 0) ^ 2 * Work.Spaces.HkSq α 6 w :=
    scale_Hsq_le hα0 hα1 hC₆pos.le hC₀'nn hE6nn hH3le
  have hb4 : Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP4b α w)
      ≤ (9 / 4) * CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2
          * (1 + Work.Spaces.HkSq α 7 w) := by
    calc Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP4b α w)
        = (3 / (2 * α)) ^ 2 * Work.Spaces.HkSq α 6
            (fun z θ => Work.Construction.L12 w z * Work.Spaces.Dth w z θ) := hsc4
      _ ≤ (3 / (2 * α)) ^ 2 * (CA * ((C₄ * Work.FTS.Nonlin.Xn α w) ^ 2
            * Work.Spaces.HkSq α 6 (Work.Spaces.Dth w)
            + (C₆ * Work.Spaces.HkNorm α 6 w) ^ 2
              * Work.Spaces.HkSq α 2 (Work.Spaces.Dth w))) :=
          mul_le_mul_of_nonneg_left heng4 (by positivity)
      _ ≤ (3 / (2 * α)) ^ 2 * (CA * ((C₄ * Work.FTS.Nonlin.Xn α w) ^ 2
            * Work.Spaces.HkSq α 7 w
            + (C₆ * Work.Spaces.HkNorm α 6 w) ^ 2
              * Work.Spaces.HkSq α 3 w)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hCApos.le
          · exact mul_le_mul_of_nonneg_left hDth6le (sq_nonneg _)
          · exact mul_le_mul_of_nonneg_left hDth2le (sq_nonneg _)
      _ = (9 / 4) * (CA * ((1 / α) ^ 2 * ((C₄ * Work.FTS.Nonlin.Xn α w) ^ 2
              * Work.Spaces.HkSq α 7 w)
            + (1 / α) ^ 2 * (C₆ ^ 2 * Work.Spaces.HkSq α 6 w
              * Work.Spaces.HkSq α 3 w))) := by
          rw [hN6]; ring
      _ = (9 / 4) * (CA * (((1 / α) ^ 2 * (C₄ * Work.FTS.Nonlin.Xn α w) ^ 2)
              * Work.Spaces.HkSq α 7 w
            + (1 / α) ^ 2 * (C₆ ^ 2 * Work.Spaces.HkSq α 6 w
              * Work.Spaces.HkSq α 3 w))) := by ring
      _ ≤ (9 / 4) * (CA * (C₄ ^ 2 * (max C₀ 0) ^ 2 * Work.Spaces.HkSq α 7 w
            + C₆ ^ 2 * (max C₀ 0) ^ 2 * Work.Spaces.HkSq α 6 w)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ hs2') hCApos.le
          exact mul_le_mul_of_nonneg_right hs1 hE7nn
      _ ≤ (9 / 4) * (CA * (C₄ ^ 2 * (max C₀ 0) ^ 2 * Work.Spaces.HkSq α 7 w
            + C₆ ^ 2 * (max C₀ 0) ^ 2 * Work.Spaces.HkSq α 7 w)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hCApos.le
          exact mul_le_mul_of_nonneg_left hE6le7 (by positivity)
      _ = (9 / 4) * CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2
            * Work.Spaces.HkSq α 7 w := by ring
      _ ≤ (9 / 4) * CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2
            * (1 + Work.Spaces.HkSq α 7 w) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hb4K : (9 / 4) * CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2
        * (1 + Work.Spaces.HkSq α 7 w) ≤ K * (1 + Work.Spaces.HkSq α 7 w) := by
    rw [hK]
    have h1 : 0 ≤ (9 / 4) * CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2 := by positivity
    have h2 : (9 / 4) * CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2
        ≤ CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2 * (9 / 4) + 1 := by nlinarith
    have h3 : 0 ≤ 1 + Work.Spaces.HkSq α 7 w := by linarith
    exact mul_le_mul_of_nonneg_right h2 h3
  exact ⟨hb3.trans hb3K, hb4.trans hb4K⟩

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux
