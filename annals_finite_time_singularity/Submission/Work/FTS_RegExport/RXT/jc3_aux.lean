/-
# `Work.FTS_RegExport.RXT.jc3_aux` — auxiliary lemmas for the leaf S3

Slice derivatives at finite order (`pz`/`pth` of the slices, and the definitional relations
`mixed (k+1) i = z·∂_z (mixed k i)` and `mixed 0 (k+1) = D_θ (mixed 0 k)`), together with the
abstract Landau step on a compact time interval, which is the tool that upgrades the
time-Lipschitz bound for the order-≤2 slots to the time-continuity of the order-3 slots.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false

/-! ## §1 Slice derivatives at finite order -/

/-- For a function which is `C¹` on an open set, the `z`-slice is differentiable and its
derivative is `pz`. -/
lemma hasDerivAt_slice_fst_of_contDiffOn {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (h : ContDiffOn ℝ 1 (Function.uncurry g) V)
    {z θ : ℝ} (hz : (z, θ) ∈ V) :
    HasDerivAt (fun z' => g z' θ) (Work.Spaces.pz g z θ) z := by
  have hd : DifferentiableAt ℝ (Function.uncurry g) (z, θ) :=
    (h.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hz)
  have h2 : HasFDerivAt (fun z' : ℝ => (z', θ)) (ContinuousLinearMap.inl ℝ ℝ ℝ) z :=
    hasFDerivAt_prodMk_left z θ
  have h3 : HasDerivAt (fun z' : ℝ => Function.uncurry g (z', θ))
      ((fderiv ℝ (Function.uncurry g) (z, θ)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ) 1) z := by
    simpa only [Function.comp_def] using (hd.hasFDerivAt.comp z h2).hasDerivAt
  have hval : (fderiv ℝ (Function.uncurry g) (z, θ)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ) 1
      = Work.Spaces.pz g z θ := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
    exact (Work.Spaces.deriv_slice_fst (Function.uncurry g) z θ hd).symm
  rw [hval] at h3
  exact h3

/-- For a function which is `C¹` on an open set, the `θ`-slice is differentiable and its
derivative is `pth`. -/
lemma hasDerivAt_slice_snd_of_contDiffOn {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (h : ContDiffOn ℝ 1 (Function.uncurry g) V)
    {z θ : ℝ} (hz : (z, θ) ∈ V) :
    HasDerivAt (fun θ' => g z θ') (Work.Spaces.pth g z θ) θ := by
  have hd : DifferentiableAt ℝ (Function.uncurry g) (z, θ) :=
    (h.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hz)
  have h2 : HasFDerivAt (fun θ' : ℝ => (z, θ')) (ContinuousLinearMap.inr ℝ ℝ ℝ) θ :=
    hasFDerivAt_prodMk_right z θ
  have h3 : HasDerivAt (fun θ' : ℝ => Function.uncurry g (z, θ'))
      ((fderiv ℝ (Function.uncurry g) (z, θ)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ) 1) θ := by
    simpa only [Function.comp_def] using (hd.hasFDerivAt.comp θ h2).hasDerivAt
  have hval : (fderiv ℝ (Function.uncurry g) (z, θ)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ) 1
      = Work.Spaces.pth g z θ := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    exact (Work.Spaces.deriv_slice_snd (Function.uncurry g) z θ hd).symm
  rw [hval] at h3
  exact h3

/-- The definitional relation `mixed (k+1) i f (z,θ) = z · ∂_z (mixed k i f) (z,θ)`. -/
lemma mixed_succ_fst_eq (f : ℝ → ℝ → ℝ) (k i : ℕ) :
    Work.Spaces.mixed (k + 1) i f
      = fun z θ => z * Work.Spaces.pz (Work.Spaces.mixed k i f) z θ := by
  funext z θ
  simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.Dz]

/-- `D_z` picks out the `z`-derivative: `mixed k i f z θ = z · ∂_z (mixed (k-1) i f) z θ`
for `1 ≤ k`. -/
lemma mixed_fst_eq_mul_pz (f : ℝ → ℝ → ℝ) {k i : ℕ} (hk : 1 ≤ k) (z θ : ℝ) :
    Work.Spaces.mixed k i f z θ
      = z * Work.Spaces.pz (Work.Spaces.mixed (k - 1) i f) z θ := by
  conv_lhs => rw [← Nat.succ_pred_eq_of_pos hk]
  simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.Dz, Nat.pred_eq_sub_one]

/-- `D_θ` picks out the `θ`-derivative: `mixed 0 3 f z θ = sin(2θ) · ∂_θ (mixed 0 2 f) z θ`. -/
lemma mixed_zero_three_eq (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 0 3 f z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.mixed 0 2 f) z θ := by
  simp only [Work.Spaces.mixed, Work.Spaces.DthIter_succ, Work.Spaces.DzIter_zero,
    Work.Spaces.Dth]

/-- `C⁴` spatial regularity gives `C¹` regularity of the mixed slots of order `≤ 3`. -/
lemma contDiffOn_mixed_of_four {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0) {j i : ℕ} (hji : j + i ≤ 3) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.mixed j i f)) Work.FTS.EllipticEst.Q0 :=
  Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le (n := 4)
    Work.FTS.EllipticEst.isOpen_Q0 i j 1 (by omega) h4

/-- `C⁴` spatial regularity gives continuity of the mixed slots of order `≤ 4`. -/
lemma continuousOn_mixed_of_four {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0) {j i : ℕ} (hji : j + i ≤ 4) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
  (Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le (n := 4)
    Work.FTS.EllipticEst.isOpen_Q0 i j 0 (by omega) h4).continuousOn

/-! ## §2 The Landau step on `[0,T]` -/

/-- The abstract Landau step, with the time variable restricted to `[0,T]`.  The passage from
the halfline statement to the interval statement is by clamping `τ` at `T`: the hypotheses on
the primitive are pointwise in `τ` and are inherited by the clamp, while the Lipschitz
hypothesis survives because `|min τ T - min τ' T| ≤ |τ - τ'|`. -/
lemma tau_lip_sqrt_of_primitive_Icc {T : ℝ} (hT : 0 < T)
    (hLandau : ∀ {V W : ℝ → ℝ → ℝ} {x₀ δc L K : ℝ}, 0 < δc → 0 ≤ L → 0 ≤ K →
      (∀ τ τ' : ℝ, 0 ≤ τ → 0 ≤ τ' → ∀ x ∈ Set.Icc x₀ (x₀ + δc),
        |V x τ - V x τ'| ≤ L * |τ - τ'|) →
      (∀ τ : ℝ, 0 ≤ τ → ContinuousOn (fun x => W x τ) (Set.Icc x₀ (x₀ + δc))) →
      (∀ τ : ℝ, 0 ≤ τ → ∀ x ∈ Set.Icc x₀ (x₀ + δc),
        |W x τ - W x₀ τ| ≤ K * |x - x₀|) →
      (∀ τ : ℝ, 0 ≤ τ → ∀ x ∈ Set.Icc x₀ (x₀ + δc),
        HasDerivAt (fun x' => V x' τ) (W x τ) x) →
      ∀ τ τ' : ℝ, 0 ≤ τ → 0 ≤ τ' → |τ - τ'| ≤ δc ^ 2 →
        |W x₀ τ - W x₀ τ'| ≤ (2 * L + K) * Real.sqrt |τ - τ'|)
    {V W : ℝ → ℝ → ℝ} {x₀ δc L K : ℝ} (hδc : 0 < δc) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hV : ∀ τ ∈ Set.Icc (0:ℝ) T, ∀ τ' ∈ Set.Icc (0:ℝ) T, ∀ x ∈ Set.Icc x₀ (x₀ + δc),
      |V x τ - V x τ'| ≤ L * |τ - τ'|)
    (hcont : ∀ τ ∈ Set.Icc (0:ℝ) T, ContinuousOn (fun x => W x τ) (Set.Icc x₀ (x₀ + δc)))
    (hW : ∀ τ ∈ Set.Icc (0:ℝ) T, ∀ x ∈ Set.Icc x₀ (x₀ + δc),
      |W x τ - W x₀ τ| ≤ K * |x - x₀|)
    (hderiv : ∀ τ ∈ Set.Icc (0:ℝ) T, ∀ x ∈ Set.Icc x₀ (x₀ + δc),
      HasDerivAt (fun x' => V x' τ) (W x τ) x) :
    ∀ τ ∈ Set.Icc (0:ℝ) T, ∀ τ' ∈ Set.Icc (0:ℝ) T, |τ - τ'| ≤ δc ^ 2 →
      |W x₀ τ - W x₀ τ'| ≤ (2 * L + K) * Real.sqrt |τ - τ'| := by
  intro τ hτ τ' hτ' hdiff
  have hmm : ∀ σ : ℝ, 0 ≤ σ → min σ T ∈ Set.Icc (0:ℝ) T := fun σ hσ =>
    ⟨le_min hσ hT.le, min_le_right _ _⟩
  have hminτ : min τ T = τ := min_eq_left hτ.2
  have hminτ' : min τ' T = τ' := min_eq_left hτ'.2
  have hmin_lip : ∀ σ σ' : ℝ, |min σ T - min σ' T| ≤ |σ - σ'| := by
    intro σ σ'
    have h := abs_min_sub_min_le_max σ T σ' T
    rwa [sub_self, abs_zero, max_eq_left (abs_nonneg _)] at h
  have hLand := hLandau (V := fun x σ => V x (min σ T)) (W := fun x σ => W x (min σ T))
    hδc hL hK
    (fun σ σ' hσ hσ' x hx => by
      have h1 := hV (min σ T) (hmm σ hσ) (min σ' T) (hmm σ' hσ') x hx
      exact le_trans h1 (mul_le_mul_of_nonneg_left (hmin_lip σ σ') hL))
    (fun σ hσ => hcont (min σ T) (hmm σ hσ))
    (fun σ hσ x hx => hW (min σ T) (hmm σ hσ) x hx)
    (fun σ hσ x hx => hderiv (min σ T) (hmm σ hσ) x hx)
    τ τ' hτ.1 hτ'.1 hdiff
  simpa [hminτ, hminτ'] using hLand

end Work.FTS_RegExport.RXT
