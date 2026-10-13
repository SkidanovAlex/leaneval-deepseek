import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.c2m_L12Fstar_W6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `𝒲^{6,∞}`-membership and `α`-linear `𝒲^{6,∞}`-bound for `-(2α/(1+z))·c2m(θ)`

The transport coefficient of the `N₀`/`𝓛_Γ^T` rows is the angular coefficient
`c2m(θ) = cos 2θ − sin²θ` times the radial profile `2α/(1+z)`.  The sibling module
`Work.FTS.StrongPersist.c2m_L12Fstar_W6` treats `c2m·L₁₂(F_*) = c2m·2α/(1+z)`; the present
lemma is the *explicit* version of the same function with the two factors written in the
opposite order and with the overall sign `-`, which is the form in which the coefficient is
requested (`N0pair6Aux.N0coefA6_WlInf6`).

The two pointwise inputs are `c2mSix_inv_points` and `c2mSix_inv_mixed` of the sibling module,
applied to `Hn0 α = c2m(θ)·2α/(1+z)`; the sign `-` is transported through the iterated
derivatives with the elementary commutation lemmas `pzIter_neg_fun` / `DthIter_neg_fun`, and
`|−x| = |x|` makes the two functions have the same bounds.  The smoothness is
`SmoothOpen.sep_mul`-style: `C^∞` on `(0,∞)` in `z` times `C^∞` in `θ`.
-/

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

open Work.Spaces
open scoped Real Topology

noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-- The coefficient of the statement, with the factors in the statement's order. -/
def Fn0 (α : ℝ) : ℝ → ℝ → ℝ := fun z θ => -(2 * α / (1 + z)) * Work.Construction.c2m θ

/-- The same function with the `c2m` factor first; this is the shape treated by
`Work.FTS.StrongPersist.c2mSix_inv_points` / `c2mSix_inv_mixed`. -/
def Hn0 (α : ℝ) : ℝ → ℝ → ℝ := fun z θ => Work.Construction.c2m θ * (2 * α / (1 + z))

/-! ## Negation commutes with the iterated operators -/

/-- Negation commutes with the iterated plain `z`-derivative. -/
theorem pzIter_neg_fun (k : ℕ) (X : ℝ → ℝ → ℝ) :
    Work.Spaces.pzIter k (fun z θ => -(X z θ)) = fun z θ => -Work.Spaces.pzIter k X z θ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_succ, ih]
      funext z θ
      simp only [Work.Spaces.pz]
      rw [show (fun z' : ℝ => -(Work.Spaces.pzIter k X) z' θ)
            = -((fun z' : ℝ => Work.Spaces.pzIter k X z' θ)) from rfl,
        deriv.neg]

/-- Negation commutes with the iterated `D_θ`-derivative. -/
theorem DthIter_neg_fun (j : ℕ) (X : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter j (fun z θ => -(X z θ)) = fun z θ => -Work.Spaces.DthIter j X z θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ, ih]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [show (fun θ' : ℝ => -(Work.Spaces.DthIter j X) z θ')
            = -(fun θ' : ℝ => Work.Spaces.DthIter j X z θ') from rfl, deriv.neg]
      ring

/-! ## Smoothness on the open quadrant -/

/-- `-(2α/(1+z))·c2m(θ)` is `C^∞` on the open quadrant.  This is the `sep_mul` shape: a
product of a function of `z` which is `C^∞` on `(0,∞)` and a function of `θ` which is `C^∞`
everywhere. -/
theorem Fn0_smoothOpen (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -(2 * α / (1 + z)) * Work.Construction.c2m θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => -(2 * α / (1 + z)) * Work.Construction.c2m θ))
    Work.FTS.EllipticEst.Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (fun p : ℝ × ℝ => -(2 * α / (1 + p.1)) * Work.Construction.c2m p.2)
    Work.FTS.EllipticEst.Q0
  rw [show (fun p : ℝ × ℝ => -(2 * α / (1 + p.1)) * Work.Construction.c2m p.2)
      = (fun p : ℝ × ℝ => -(2 * α / (1 + p.1)))
        * (fun p : ℝ × ℝ => Work.Construction.c2m p.2) from rfl]
  have hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ => -(2 * α / (1 + z)))
      (Set.Ioi 0) := by
    apply contDiffOn_infty.mpr
    intro m
    have hone : ContDiffOn ℝ m (fun z : ℝ => 1 + z) (Set.Ioi 0) := by fun_prop
    have hd : ContDiffOn ℝ m (fun z : ℝ => (2 * α) / (1 + z)) (Set.Ioi 0) := by
      apply ContDiffOn.div
      · exact contDiffOn_const
      · exact hone
      · intro z hz
        simp only [Set.mem_Ioi] at hz
        linarith
    exact hd.neg
  have hχ : ContDiff ℝ ⊤ Work.Construction.c2m := by
    rw [show Work.Construction.c2m = fun θ : ℝ => Real.cos (2 * θ) - Real.sin θ ^ 2 from rfl]
    fun_prop
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => -(2 * α / (1 + p.1))) Work.FTS.EllipticEst.Q0 :=
    hg.comp contDiffOn_fst fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => Work.Construction.c2m p.2) Work.FTS.EllipticEst.Q0 := by
    change ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Construction.c2m ∘ Prod.snd)
      Work.FTS.EllipticEst.Q0
    exact (hχ.of_le le_top).comp_contDiffOn (s := Work.FTS.EllipticEst.Q0)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) contDiffOn_snd
  exact h1.mul h2

/-! ## The two pointwise bounds -/

/-- The weighted radial bound: `|(z+1)^k ∂_z^k (Fn0 α)| ≤ 4α k!` on the domain. -/
theorem Fn0_z_bound (α z θ : ℝ) (hα : 0 < α) (hz : z ∈ Iz) (k : ℕ) :
    |(z + 1) ^ k * Work.Spaces.pzIter k (Fn0 α) z θ| ≤ 4 * α * (k.factorial : ℝ) := by
  have hf : Fn0 α = fun z θ => -(Hn0 α z θ) := by
    funext z θ; simp only [Fn0, Hn0]; ring
  rw [hf, pzIter_neg_fun]
  rw [show (z + 1) ^ k * -Work.Spaces.pzIter k (Hn0 α) z θ
      = -((z + 1) ^ k * Work.Spaces.pzIter k (Hn0 α) z θ) by ring, abs_neg]
  exact Work.FTS.StrongPersist.c2mSix_inv_points α z θ hα hz k

/-- The weighted mixed bound: the angular summand of `WlInf` for `Fn0 α` is `≤ C α`,
uniformly in `0 < α ≤ 1`, `z ∈ Iz`, `θ ∈ Iθ` and the orders `1 ≤ j ≤ 6`, `k ≤ 6`. -/
theorem Fn0_mixed_bound : ∃ C : ℝ, 0 < C ∧ ∀ (α z θ : ℝ), 0 < α → α ≤ 1 → z ∈ Iz → θ ∈ Iθ →
    ∀ j k : ℕ, 1 ≤ j → j ≤ 6 → k ≤ 6 →
    |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j (Fn0 α)) z θ
      * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ C * α := by
  obtain ⟨K, hKpos, hK⟩ := Work.FTS.StrongPersist.c2mSix_inv_mixed
  refine ⟨K, hKpos, ?_⟩
  intro α z θ hα hα1 hz hθ j k hj1 hj6 hk
  have hz0 : (0 : ℝ) ≤ z := hz
  have hf : Fn0 α = fun z θ => -(Hn0 α z θ) := by
    funext z θ; simp only [Fn0, Hn0]; ring
  rw [hf, DthIter_neg_fun, pzIter_neg_fun]
  rw [show (z + 1) ^ k * -Work.Spaces.pzIter k (Work.Spaces.DthIter j (Hn0 α)) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))
      = -((z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j (Hn0 α)) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) by ring, abs_neg]
  exact hK α z θ hα hα1 hz0 hθ j k hj1 hj6 hk

/-! ## The `𝒲^{6,∞}`-membership and the norm estimate -/

/-- Every one of the finitely many suprema of `WlInf α 6 (Fn0 α)` is bounded. -/
theorem Fn0_WlInfMem (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.WlInfMem α 6 (Fn0 α) := by
  obtain ⟨K, hKpos, hK⟩ := Fn0_mixed_bound
  constructor
  · intro k hk
    exact ⟨4 * α * (k.factorial : ℝ), fun y hy => by
      rcases hy with ⟨z, hz, θ, hθ, rfl⟩
      exact Fn0_z_bound α z θ hα hz k⟩
  · intro j hj k hk hj1 hjk
    exact ⟨K * α, fun y hy => by
      rcases hy with ⟨z, hz, θ, hθ, rfl⟩
      exact hK α z θ hα hα1 hz hθ j k hj1 hj hk⟩

/-- The `𝒲^{6,∞}`-norm of `Fn0 α` is bounded by a universal constant times `α`. -/
theorem Fn0_WlInf_le : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    Work.Spaces.WlInf α 6 (Fn0 α) ≤ C * α := by
  obtain ⟨K, hKpos, hK⟩ := Fn0_mixed_bound
  refine ⟨Work.FTS.StrongPersist.c2mSixCW K,
    Work.FTS.StrongPersist.c2mSixCW_pos K hKpos, ?_⟩
  intro α hα hα1
  have hzsum : (∑ k ∈ Finset.range 7, Work.Spaces.supAbs (fun z θ =>
        (z + 1) ^ k * Work.Spaces.pzIter k (Fn0 α) z θ))
      ≤ ∑ k ∈ Finset.range 7, 4 * α * (k.factorial : ℝ) := by
    apply Finset.sum_le_sum
    intro k hk
    exact Work.Spaces.supAbs_le fun z hz θ _ => Fn0_z_bound α z θ hα hz k
  have hmsum : (∑ j ∈ Finset.range 7, ∑ k ∈ Finset.range 7,
        (if 1 ≤ j ∧ k + j ≤ 6 then Work.Spaces.supAbs (fun z θ =>
          (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j (Fn0 α)) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0))
      ≤ ∑ j ∈ Finset.range 7, ∑ k ∈ Finset.range 7, K * α := by
    apply Finset.sum_le_sum
    intro j hj
    apply Finset.sum_le_sum
    intro k hk
    by_cases hc : 1 ≤ j ∧ k + j ≤ 6
    · rw [ite_eq_left hc]
      exact Work.Spaces.supAbs_le fun z hz θ hθ =>
        hK α z θ hα hα1 hz hθ j k hc.1 (by omega) (by omega)
    · rw [ite_eq_right hc]
      exact mul_nonneg hKpos.le hα.le
  calc Work.Spaces.WlInf α 6 (Fn0 α)
      = (∑ k ∈ Finset.range 7, Work.Spaces.supAbs (fun z θ =>
            (z + 1) ^ k * Work.Spaces.pzIter k (Fn0 α) z θ))
        + ∑ j ∈ Finset.range 7, ∑ k ∈ Finset.range 7,
            (if 1 ≤ j ∧ k + j ≤ 6 then Work.Spaces.supAbs (fun z θ =>
              (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j (Fn0 α)) z θ
                * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0) := rfl
    _ ≤ (∑ k ∈ Finset.range 7, 4 * α * (k.factorial : ℝ))
        + ∑ j ∈ Finset.range 7, ∑ k ∈ Finset.range 7, K * α := add_le_add hzsum hmsum
    _ = (∑ k ∈ Finset.range 7, 4 * (k.factorial : ℝ)) * α + 49 * (K * α) := by
      rw [Work.FTS.StrongPersist.c2mSix_sum_fact_mul,
        Work.FTS.StrongPersist.c2mSix_sum_const_mul]
    _ ≤ Work.FTS.StrongPersist.c2mSixCW K * α := by
      rw [Work.FTS.StrongPersist.c2mSixCW]
      nlinarith [hα.le, hKpos.le]

/-! ## The requested statement -/

theorem N0coefA6_WlInf6 : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => -(2 * α / (1 + z)) * Work.Construction.c2m θ) ∧
    Work.Spaces.WlInfMem α 6 (fun z θ => -(2 * α / (1 + z)) * Work.Construction.c2m θ) ∧
    Work.Spaces.WlInf α 6 (fun z θ => -(2 * α / (1 + z)) * Work.Construction.c2m θ) ≤ C * α := by
  obtain ⟨C, hC, hCb⟩ := Fn0_WlInf_le
  refine ⟨C, hC, fun α hα hα1 => ⟨Fn0_smoothOpen α, ?_, hCb α hα hα1⟩⟩
  exact Fn0_WlInfMem α hα hα1

end

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
