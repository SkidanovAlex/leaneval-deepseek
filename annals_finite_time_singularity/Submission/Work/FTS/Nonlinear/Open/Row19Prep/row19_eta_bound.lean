import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.NonlinRows.sqm_pz_DthIter_mul_le_4_open
import Submission.Work.FTS.Nonlinear.Open.Row19Prep.Defs
import Submission.Work.FTS.Nonlinear.Open.Row19Prep.H2bBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Open.Row19Prep

open scoped Real Topology
open MeasureTheory Set Filter

set_option linter.unusedVariables false

/-! ## A `z`-independent factor passes through the radial derivatives

The two lemmas below isolate the factor `α·Γ(θ)` of the row-19 product (which does not depend on
`z`) from the Leibniz expansion of `∂_z^m (A·H₂)`.  They are the `pzIter`-counterpart of
`Work.FTS.H2.pzIter_const_mul`; the single `deriv`-step uses the *unconditional* field form
`deriv_const_mul_field`. -/

theorem pz_const_mul_pt (c : ℝ → ℝ) (K : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pz (fun z θ => c θ * K z θ) z θ = c θ * Work.Spaces.pz K z θ := by
  rw [Work.Spaces.pz, Work.Spaces.pz]
  exact deriv_const_mul_field _

theorem pzIter_const_mul_pt (c : ℝ → ℝ) (K : ℝ → ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter j (fun z θ => c θ * K z θ) z θ = c θ * Work.Spaces.pzIter j K z θ := by
  induction j generalizing z θ with
  | zero => rfl
  | succ j ih =>
    rw [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_succ]
    have heq : Work.Spaces.pzIter j (fun z θ => c θ * K z θ)
        = fun z θ => c θ * Work.Spaces.pzIter j K z θ :=
      funext fun z => funext fun θ => ih z θ
    rw [heq, pz_const_mul_pt]

/-- `∂_z^k` of a function of `z` alone is the `k`-th iterate of `deriv`. -/
theorem pzIter_zOnly (r : ℝ → ℝ) (k : ℕ) :
    Work.Spaces.pzIter k (fun z θ => r z) = fun z θ => deriv^[k] r z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Work.Spaces.pzIter_succ, ih]
    funext z θ
    exact (congrFun (Function.iterate_succ_apply' deriv k r) z).symm

/-! ## Smoothness of the radial factor -/

theorem contDiffOn_H2b_Ioi :
    ContDiffOn ℝ Work.Stability.smoothOrder H2b (Set.Ioi 0) := by
  have h : H2b = fun z : ℝ => 2 * z ^ 2 * (1 - z) / (1 + z) ^ 4 := rfl
  rw [h]
  refine ContDiffOn.div ?_ ?_ ?_
  · exact ((contDiffOn_const (c := (2 : ℝ)).mul (contDiffOn_id.pow 2)).mul
      (contDiffOn_const.sub contDiffOn_id))
  · exact (contDiffOn_const.add contDiffOn_id).pow 4
  · intro z hz
    have hz1 : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
    positivity

theorem smoothOpen_H2b : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => H2b z) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ : ℝ => H2b z)) Work.FTS.EllipticEst.Q0
  have hfun : Function.uncurry (fun z θ : ℝ => H2b z) = fun p : ℝ × ℝ => H2b p.1 := rfl
  rw [hfun]
  exact contDiffOn_H2b_Ioi.comp contDiffOn_fst (fun p hp => hp.1)

/-! ## The `j = 0` case of the mixed Leibniz bound -/

/-- The Leibniz bound `sqm_pz_DthIter_mul_le_4_open` in the case `j = 0` (no `D_θ`-derivative),
where the inner `range (j+1)`-sum has the single term `a = 0`. -/
theorem sqm_pz_mul_le_4_open (k : ℕ) (hk : k ≤ 4) (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Work.Spaces.pzIter k (fun z θ => f z θ * g z θ) z θ| ≤
        (257 : ℝ) * ∑ c ∈ Finset.range (k + 1),
          |Work.Spaces.pzIter c f z θ| * |Work.Spaces.pzIter (k - c) g z θ| := by
  intro z hz θ hθ
  have h := Work.FTS.NonlinRows.sqm_pz_DthIter_mul_le_4_open k 0 hk (by norm_num) f g hf hg
    z hz θ hθ
  have h2 : (∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (0 + 1),
        |Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ| *
          |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (0 - a) g) z θ|)
      = ∑ c ∈ Finset.range (k + 1),
          |Work.Spaces.pzIter c f z θ| * |Work.Spaces.pzIter (k - c) g z θ| := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single 0]
    · simp
    · intro a ha hne
      rw [Finset.mem_range] at ha
      omega
    · intro hmem
      exact absurd (Finset.mem_range.mpr (by omega : 0 < 0 + 1)) hmem
  rw [h2] at h
  simpa using h

/-- **Row 19, the `η`-family of pointwise bounds.** With `A` a coefficient in `𝒲^{4,∞}` of norm
`≤ Λ` (this is `StarPkgo2.VzW` for `A = ((z+1)/z)·V(Φ̃_*)`),

`|(1+z)·w(z)·z^m·∂_z^m (α·Γ(θ)·(A·H₂))| ≤ C·α·Λ`  for `m ≤ 4`, `z > 0`, `θ ∈ (0,π/2)`,

where `H₂(z) = 2z²(1-z)/(1+z)⁴` is the radial factor of `V(Φ̃_*)·D_zF_*` and `w(z) = (1+z)²/z²`.
These are exactly the `hA`-hypotheses of `Work.FTS.NonlinRows.wtoHQ_of_pointwise_open` for
`f = V(Φ̃_*)·D_zF_*` (up to the constant `1/c(α)`).

Suggested route (all ingredients exist):
* `Work.FTS.Nonlinear.Open.Row19Prep.pzIter_theta_only` pulls `α·Γ` out of `∂_z^m`;
* `Work.FTS.NonlinRows.sqm_pz_DthIter_mul_le_4_open` (with `j = 0`) is the Leibniz bound for
  `∂_z^m(A·H₂)`: `≤ 257·Σ_{c≤m}|∂_z^cA|·|∂_z^{m-c}H₂|`;
* `Work.Spaces.pz_sup_bound` gives `|∂_z^cA| ≤ Λ/(1+z)^c`;
* `Work.FTS.Nonlinear.Open.Row19Prep.H2b_weight_le` gives
  `(1+z)w(z)z^m/(1+z)^{m-c}|∂_z^{m-c}H₂| ≤ 10^7` for every `c ≤ m ≤ 4`.
(The same estimate is carried out for the concrete `A = ((z+1)/z)·V(Φ̃_*)` in
`Submission/Work/FTS/NonlinRows/NRow19T2.lean`, `Z19_eta_bound`.) -/
theorem row19_eta_bound : ∃ C : ℝ, 0 < C ∧ ∀ (α Λ : ℝ) (A : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 → 0 ≤ Λ → Work.Spaces.WlInf α 4 A ≤ Λ →
    Work.Spaces.WlInfMem α 4 A → Work.FTS.EllipticEst.SmoothOpen A →
    ∀ (m : ℕ), m ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
      |(1 + z) * Work.Spaces.w z * z ^ m * Work.Spaces.pzIter m
        (fun z θ => α * Work.Spaces.Gam α θ
          * (A z θ * Work.FTS.Nonlinear.Open.Row19Prep.H2b z)) z θ|
        ≤ C * (α * Λ) := by
  obtain ⟨CH, hCH0, hCH⟩ := H2b_weight_le
  refine ⟨257 * 5 * CH, by nlinarith [hCH0], ?_⟩
  intro α Λ A hα hα1 hΛ0 hWΛ hmem hAsm m hm z hz θ hθ
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := Gam_nonneg hα hθI
  have hαG : |α * Work.Spaces.Gam α θ| ≤ α := by
    rw [abs_of_nonneg (mul_nonneg hα.le hG0)]
    nlinarith [Gam_le_one hα hθI]
  -- (i) the `z`-independent factor `α·Γ(θ)` passes through `∂_z^m`
  have hZeq : Work.Spaces.pzIter m
        (fun z θ : ℝ => α * Work.Spaces.Gam α θ * (A z θ * H2b z)) z θ
      = (α * Work.Spaces.Gam α θ)
          * Work.Spaces.pzIter m (fun z θ : ℝ => A z θ * H2b z) z θ := by
    simpa using pzIter_const_mul_pt (fun θ => α * Work.Spaces.Gam α θ)
      (fun z θ => A z θ * H2b z) m z θ
  -- (ii) the Leibniz bound for `∂_z^m (A·H₂)`
  have hleib : |Work.Spaces.pzIter m (fun z θ : ℝ => A z θ * H2b z) z θ| ≤
      (257 : ℝ) * ∑ c ∈ Finset.range (m + 1),
        |Work.Spaces.pzIter c A z θ| * |deriv^[m - c] H2b z| := by
    refine (sqm_pz_mul_le_4_open m hm A (fun z θ : ℝ => H2b z) hAsm smoothOpen_H2b
      z hz θ hθ).trans ?_
    have hSeq : (∑ c ∈ Finset.range (m + 1),
          |Work.Spaces.pzIter c A z θ|
            * |Work.Spaces.pzIter (m - c) (fun z θ : ℝ => H2b z) z θ|)
        = ∑ c ∈ Finset.range (m + 1),
            |Work.Spaces.pzIter c A z θ| * |deriv^[m - c] H2b z| := by
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [pzIter_zOnly H2b (m - c)]
    rw [hSeq]
  -- (iii) the termwise weighted bound
  have hterm : ∀ c ∈ Finset.range (m + 1),
      ((1 + z) * Work.Spaces.w z * z ^ m)
        * (|Work.Spaces.pzIter c A z θ| * |deriv^[m - c] H2b z|) ≤ Λ * CH := by
    intro c hc
    have hc_le : c ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hc)
    have hc4 : c ≤ 4 := by omega
    have hsplit : (1 + z) * Work.Spaces.w z * z ^ m
        = (1 + z) ^ c * ((1 + z) * Work.Spaces.w z * z ^ m / (1 + z) ^ c) := by
      have h2 : (0 : ℝ) < (1 + z) ^ c := pow_pos hz1 c
      field_simp
    rw [hsplit]
    have h1 : (1 + z) ^ c * ((1 + z) * Work.Spaces.w z * z ^ m / (1 + z) ^ c)
          * (|Work.Spaces.pzIter c A z θ| * |deriv^[m - c] H2b z|)
        = ((1 + z) ^ c * |Work.Spaces.pzIter c A z θ|)
          * ((1 + z) * Work.Spaces.w z * z ^ m / (1 + z) ^ c
              * |deriv^[m - c] H2b z|) := by ring
    rw [h1]
    have hA' : (1 + z) ^ c * |Work.Spaces.pzIter c A z θ| ≤ Λ := by
      have h := Work.Spaces.WlInf_z_bound α 4 A hmem c hc4 z θ hzI hθI
      have h2 : (z + 1) ^ c = (1 + z) ^ c := by ring
      rw [h2] at h
      calc (1 + z) ^ c * |Work.Spaces.pzIter c A z θ|
          = |(1 + z) ^ c * Work.Spaces.pzIter c A z θ| := by
            rw [abs_mul, abs_of_pos (pow_pos hz1 c)]
        _ ≤ Λ := le_trans h hWΛ
    have hB : (1 + z) * Work.Spaces.w z * z ^ m / (1 + z) ^ c
          * |deriv^[m - c] H2b z| ≤ CH := by
      have h := hCH m (m - c) hm (by omega) z hz
      have hc' : m - (m - c) = c := by omega
      rwa [hc'] at h
    have hWnn : 0 ≤ (1 + z) * Work.Spaces.w z * z ^ m / (1 + z) ^ c := by
      rw [Work.Spaces.w]; positivity
    exact mul_le_mul hA' hB (mul_nonneg hWnn (abs_nonneg _)) hΛ0
  -- (iv) the sum of the weighted terms
  have hsum : (∑ c ∈ Finset.range (m + 1),
        ((1 + z) * Work.Spaces.w z * z ^ m)
          * (|Work.Spaces.pzIter c A z θ| * |deriv^[m - c] H2b z|))
      ≤ 5 * (Λ * CH) := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right (by exact_mod_cast (show m + 1 ≤ 5 by omega))
      (mul_nonneg hΛ0 hCH0.le)
  have hwpos : 0 < (1 + z) * Work.Spaces.w z * z ^ m := by
    rw [Work.Spaces.w]; positivity
  have hfac : (∑ c ∈ Finset.range (m + 1),
        ((1 + z) * Work.Spaces.w z * z ^ m)
          * (|Work.Spaces.pzIter c A z θ| * |deriv^[m - c] H2b z|))
      = ((1 + z) * Work.Spaces.w z * z ^ m)
        * (∑ c ∈ Finset.range (m + 1),
            |Work.Spaces.pzIter c A z θ| * |deriv^[m - c] H2b z|) :=
    (Finset.mul_sum (Finset.range (m + 1))
      (fun c => |Work.Spaces.pzIter c A z θ| * |deriv^[m - c] H2b z|)
      ((1 + z) * Work.Spaces.w z * z ^ m)).symm
  -- (v) assembly
  calc |(1 + z) * Work.Spaces.w z * z ^ m * Work.Spaces.pzIter m
          (fun z θ : ℝ => α * Work.Spaces.Gam α θ * (A z θ * H2b z)) z θ|
      = ((1 + z) * Work.Spaces.w z * z ^ m)
          * |Work.Spaces.pzIter m
              (fun z θ : ℝ => α * Work.Spaces.Gam α θ * (A z θ * H2b z)) z θ| := by
        rw [abs_mul, abs_of_pos hwpos]
    _ = ((1 + z) * Work.Spaces.w z * z ^ m)
          * (|α * Work.Spaces.Gam α θ|
              * |Work.Spaces.pzIter m (fun z θ : ℝ => A z θ * H2b z) z θ|) := by
        rw [hZeq, abs_mul]
    _ ≤ ((1 + z) * Work.Spaces.w z * z ^ m)
          * (α * ((257 : ℝ) * ∑ c ∈ Finset.range (m + 1),
              |Work.Spaces.pzIter c A z θ| * |deriv^[m - c] H2b z|)) := by
        refine mul_le_mul_of_nonneg_left ?_ hwpos.le
        exact mul_le_mul hαG hleib (abs_nonneg _) hα.le
    _ = α * 257 * (∑ c ∈ Finset.range (m + 1),
            ((1 + z) * Work.Spaces.w z * z ^ m)
              * (|Work.Spaces.pzIter c A z θ| * |deriv^[m - c] H2b z|)) := by
        rw [hfac]; ring
    _ ≤ 257 * 5 * CH * (α * Λ) := by
        have hαΛ : 0 ≤ α * Λ := mul_nonneg hα.le hΛ0
        calc α * 257 * (∑ c ∈ Finset.range (m + 1),
              ((1 + z) * Work.Spaces.w z * z ^ m)
                * (|Work.Spaces.pzIter c A z θ| * |deriv^[m - c] H2b z|))
            ≤ α * 257 * (5 * (Λ * CH)) :=
              mul_le_mul_of_nonneg_left hsum (mul_nonneg hα.le (by norm_num))
          _ = 257 * 5 * CH * (α * Λ) := by ring

end Work.FTS.Nonlinear.Open.Row19Prep
