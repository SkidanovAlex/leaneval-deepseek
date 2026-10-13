/-
Auxiliary material for the row-19 `γ`-family of pointwise bounds
(`Submission/Work/FTS/Nonlinear/Open/Row19Prep/row19_gam_bound.lean`).

It contains

* the two elementary bounding devices `PsiA` (the angular factor `1` for `b = 0` and `Φ(θ)`
  for `b ≥ 1`, attached to `∂_z^c D_θ^b A`) and `TB` (dominating `tBound (a-1) 0`, `a ≤ 4`);
* the smoothness helpers for `θ`-only / `z`-only factors, for `Γ` and for `H₂`;
* `DthIter_theta_only` / `pzIter_zOnly`, the two degenerate calculus rules;
* `Kaf_pz_Dth_le`, the `z`-only Leibniz bound for `K = A·H₂`: the `D_θ`-derivatives all land
  on `A`, the terms where one falls on the `z`-only `H₂` vanishing.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.NonlinRows.sqm_pz_DthIter_mul_le_4_open
import Submission.Work.FTS.Nonlinear.Open.Row19Prep.Defs
import Submission.Work.FTS.Nonlinear.Open.Row19Prep.H2bBound
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.Spaces.WlInf_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Open.Row19Prep

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- `Φ(θ)` for `b ≥ 1`, `1` for `b = 0`: the angular factor attached to `∂_z^c D_θ^b A`. -/
def PsiA (α : ℝ) (b : ℕ) (θ : ℝ) : ℝ := if b = 0 then 1 else PhiA α θ

/-- `TB = Σ_{j<5} tBound j 0`, a uniform bound for `tBound (a-1) 0`, `a ≤ 4`. -/
def TB : ℝ := ∑ j ∈ Finset.range 5, Work.Spaces.tBound j 0

theorem TB_nonneg : 0 ≤ TB :=
  Finset.sum_nonneg fun j _ => Work.Spaces.tBound_nonneg j 0

theorem tBound_le_TB {a : ℕ} (ha : 1 ≤ a) (ha4 : a ≤ 4) : Work.Spaces.tBound (a - 1) 0 ≤ TB := by
  refine Finset.single_le_sum (f := fun j : ℕ => Work.Spaces.tBound j 0)
    (fun j _ => Work.Spaces.tBound_nonneg j 0) ?_
  rw [Finset.mem_range]; omega

theorem PsiA_nonneg {α : ℝ} (hα : 0 < α) {b : ℕ} {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ PsiA α b θ := by
  rw [PsiA]
  split_ifs with h
  · norm_num
  · exact PhiA_nonneg hα hθ

theorem PsiA_eq {α : ℝ} {b : ℕ} {θ : ℝ} : PsiA α b θ = if b = 0 then 1 else PhiA α θ := rfl

/-! ## Smoothness helpers -/

theorem smoothOpen_theta_only {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ Work.Stability.smoothOrder a (Set.Ioo 0 (π / 2))) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ) :=
  ha.comp contDiffOn_snd (fun p hp => hp.2)

theorem smoothOpen_z_only {r : ℝ → ℝ}
    (hr : ContDiffOn ℝ Work.Stability.smoothOrder r (Set.Ioi 0)) :
    Work.FTS.EllipticEst.SmoothOpen (fun (z : ℝ) _ => r z) :=
  hr.comp contDiffOn_fst (fun p hp => hp.1)

theorem smoothOpen_mul {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) := by
  have h : Function.uncurry (fun z θ : ℝ => f z θ * g z θ)
      = Function.uncurry f * Function.uncurry g := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen]
  rw [h]
  exact hf.mul hg

/-- `Γ(θ) = (sinθcos²θ)^{α/3}` is `C^∞` on the open interval `(0,π/2)`. -/
theorem contDiffOn_Gam (α : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Work.Spaces.Gam α θ)
      (Set.Ioo 0 (π / 2)) := by
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.sin θ)
      (Set.Ioo 0 (π / 2)) := Real.contDiff_sin.contDiffOn
  have hcos : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.cos θ)
      (Set.Ioo 0 (π / 2)) := Real.contDiff_cos.contDiffOn
  have hbase : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) (Set.Ioo 0 (π / 2)) := hsin.mul (hcos.pow 2)
  have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), Real.sin θ * Real.cos θ ^ 2 ≠ 0 := by
    intro θ hθ
    have h1 : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have h2 : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity
  have h := hbase.rpow (contDiffOn_const (c := α / 3)) hne
  refine h.congr (fun θ hθ => ?_)
  simp only [Work.Spaces.Gam]

theorem smoothOpen_alpha_Gam (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => α * Work.Spaces.Gam α θ) :=
  smoothOpen_theta_only ((contDiffOn_const (c := α)).mul (contDiffOn_Gam α))

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

theorem smoothOpen_H2b : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => H2b z) :=
  smoothOpen_z_only contDiffOn_H2b_Ioi

/-! ## `θ`-only / `z`-only calculus -/

/-- For a `θ`-only function, `D_θ^j` is the `dthU`-iterate. -/
theorem DthIter_theta_only (g : ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DthIter j (fun _ (θ : ℝ) => g θ) = fun _ θ => Work.Spaces.dthU^[j] g θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      funext z θ
      show Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.dthU^[j] g θ') θ
        = Work.Spaces.dthU^[j + 1] g θ
      rw [Function.iterate_succ_apply' Work.Spaces.dthU j g, Work.Spaces.dthU]

/-- `∂_z^k` of a `z`-only function is the `k`-th iterate of `deriv`. -/
theorem pzIter_zOnly (r : ℝ → ℝ) (k : ℕ) :
    Work.Spaces.pzIter k (fun z θ => r z) = fun z θ => deriv^[k] r z := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pzIter_succ, ih]
      funext z θ
      exact (congrFun (Function.iterate_succ_apply' deriv k r) z).symm

theorem pzIter_zero_fun (k : ℕ) :
    Work.Spaces.pzIter k (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => (0 : ℝ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pzIter_succ, ih]
      funext z θ
      simp only [Work.Spaces.pz, deriv_const]

theorem WlInf_nonneg (α : ℝ) (l : ℕ) (f : ℝ → ℝ → ℝ) (hmem : Work.Spaces.WlInfMem α l f) :
    0 ≤ Work.Spaces.WlInf α l f := by
  rw [Work.Spaces.WlInf]
  exact add_nonneg (Work.Spaces.wlZSum_nonneg α l f hmem) (Work.Spaces.wlThSum_nonneg α l f hmem)

/-! ## The `z`-only Leibniz bound for `A·H₂`

The `D_θ`-derivatives all land on `A`; the terms where one falls on the `z`-only `H₂` vanish. -/

theorem Kaf_pz_Dth_le (A : ℝ → ℝ → ℝ) (hAsm : Work.FTS.EllipticEst.SmoothOpen A)
    (k b : ℕ) (hk : k ≤ 4) (hb : b ≤ 4) :
    ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
      |Work.Spaces.pzIter k (Work.Spaces.DthIter b (fun z θ => A z θ * H2b z)) z θ|
        ≤ 257 * ∑ c ∈ Finset.range (k + 1),
            |Work.Spaces.pzIter c (Work.Spaces.DthIter b A) z θ| * |deriv^[k - c] H2b z| := by
  intro z hz θ hθ
  have h := Work.FTS.NonlinRows.sqm_pz_DthIter_mul_le_4_open k b hk hb A
    (fun z θ : ℝ => H2b z) hAsm smoothOpen_H2b z hz θ hθ
  refine h.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine Finset.sum_le_sum fun c _ => ?_
  have hsingle : (∑ a ∈ Finset.range (b + 1),
        |Work.Spaces.pzIter c (Work.Spaces.DthIter a A) z θ|
          * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (b - a) (fun z θ : ℝ => H2b z)) z θ|)
      = |Work.Spaces.pzIter c (Work.Spaces.DthIter b A) z θ|
          * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (b - b) (fun z θ : ℝ => H2b z)) z θ| :=
    Finset.sum_eq_single b (fun a ha hne => by
      obtain ⟨n, hn⟩ : ∃ n, b - a = n + 1 := by
        rw [Finset.mem_range] at ha
        exact ⟨b - a - 1, by omega⟩
      have hz0 : Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (b - a)
          (fun z θ : ℝ => H2b z)) z θ = 0 := by
        rw [hn, DthIter_succ_z_only H2b n]
        exact congrFun (congrFun (pzIter_zero_fun (k - c)) z) θ
      rw [hz0, abs_zero, mul_zero]) (fun hmem => by
        rw [Finset.mem_range] at hmem
        omega)
  rw [hsingle]
  have hb0 : b - b = 0 := by omega
  rw [hb0, Work.Spaces.DthIter_zero, pzIter_zOnly]

end Work.FTS.Nonlinear.Open.Row19Prep
