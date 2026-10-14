import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.Regularity.profFullBounds
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongGlobal.Transfer
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.R1G.vecResid_eq_scalar_smul
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.DatumOdd
-- ===== merged: Submission.Work.FTS.Regularity.dzProfFullUniform =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.Regularity.dzProfFullUniform` — the uniform `z`-derivative of the full profile

For a regularity package `h : RegPkg α S A B g` and a radius `R ≥ 0`, the `z`-derivative of the
full self-similar profile `F = F_* + g` (`profFull α g`) enjoys, uniformly on `z ∈ [0,R]`,
`θ ∈ Iθ`, `τ ∈ [0,S]`:

1. the **splitting** `∂_z F = ∂_z F_* + ∂_z g` (plain additivity of `deriv`, available because
   `RegPkg.hcont` makes `(z,τ) ↦ g z θ τ` jointly `C¹` at each fixed `θ` while `F_*` is smooth);
2. a **uniform bound** `|∂_z F| ≤ M`;
3. a **joint `α`-Hölder estimate in `(z,τ)`**:
   `|∂_zF(z,θ,τ) - ∂_zF(z',θ,τ')| ≤ N * (|z-z'| + |τ-τ'|)^α`.

The sum is estimated on its two parts:

* the **static part** `∂_z F_*` is bounded and `α`-Hölder on `[0,R]`; this is the content of the
  sibling module `Submission.Work.FTS.Regularity.fstarDzUniform`
  (`Work.FTS.Regularity.fstarDzUniform`);
* the **perturbation part** `∂_z g` is bounded and jointly `α`-Hölder in `(z,θ,τ)` by the jet
  field `RegPkg.hpz` (restricted to `θ = θ'`).
-/

noncomputable section

open FiniteTimeSingularity Set Filter Topology
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.Regularity

/-- **The `z`-slices of the perturbation are differentiable.**  `RegPkg.hcont` states that
`(z,τ) ↦ g z θ τ` is `C¹` on `Ioi (-1) ×ˢ Ioo (-1) (S+1)` at each fixed `θ ∈ Iθ`; since
`z ≥ 0 > -1` and `τ ∈ [0,S] ⊂ (-1, S+1)`, composing with `z' ↦ (z',τ)` gives differentiability of
the `z`-slice `z' ↦ g z' θ τ` at `z`. -/
theorem gSlice_differentiableAt {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg α S A B g) :
    ∀ θ ∈ Work.Spaces.Iθ, ∀ z τ : ℝ, 0 ≤ z → τ ∈ Set.Icc 0 S →
      DifferentiableAt ℝ (fun z' => g z' θ τ) z := by
  intro θ hθ z τ hz hτ
  have hz1 : -1 < z := by linarith
  have hτ1 : -1 < τ := by linarith [hτ.1]
  have hτ2 : τ < S + 1 := by linarith [hτ.2, h.hS]
  have hmem : (z, τ) ∈ (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1) : Set (ℝ × ℝ)) :=
    ⟨hz1, hτ1, hτ2⟩
  have hopen : IsOpen (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1) : Set (ℝ × ℝ)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hcd : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => g q.1 θ q.2) (z, τ) :=
    (h.hcont θ hθ).contDiffAt (hopen.mem_nhds hmem)
  have hdiff : DifferentiableAt ℝ (fun q : ℝ × ℝ => g q.1 θ q.2) (z, τ) :=
    hcd.differentiableAt (by norm_num)
  have hg : DifferentiableAt ℝ (fun z' : ℝ => (z', τ)) z := by fun_prop
  exact hdiff.comp z hg

/-- **The `z`-slices of the fundamental profile are differentiable** on `z > -1`: `F_*` is a
constant (in `z`; the `θ`-dependence enters only through the factor `Γ(θ)/c`) multiple of
`Work.FM.Fstar z = 2z/(1+z)²`, whose derivative is explicit
(`Work.FM.hasDerivAt_Fstar`). -/
theorem fstarSlice_differentiableAt {α : ℝ} (z θ : ℝ) (hz : -1 < z) :
    DifferentiableAt ℝ (fun z' => Work.Construction.Fstar (pExp α) z' θ) z := by
  have hfun : (fun z' => Work.Construction.Fstar (pExp α) z' θ)
      = fun z' => (pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
          * Work.FM.Fstar z' := by
    funext z'
    rw [Work.Construction.Fstar]
  rw [hfun]
  exact (Work.FM.hasDerivAt_Fstar z hz).const_mul _ |>.differentiableAt

theorem dzProfFullUniform {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg α S A B g) (R : ℝ) (hR : 0 ≤ R) :
    (∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
        deriv (fun z' => profFull α g z' θ τ) z
          = deriv (fun z' => Work.Construction.Fstar (pExp α) z' θ) z
            + Work.Spaces.pz (gSlice g τ) z θ) ∧
      (∃ M : ℝ, 0 ≤ M ∧ ∀ z θ τ : ℝ, 0 ≤ z → z ≤ R → θ ∈ Work.Spaces.Iθ →
        τ ∈ Set.Icc 0 S → |deriv (fun z' => profFull α g z' θ τ) z| ≤ M) ∧
      (∃ N : ℝ, 0 ≤ N ∧ ∀ z z' θ τ τ' : ℝ, 0 ≤ z → z ≤ R → 0 ≤ z' → z' ≤ R →
        θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S → τ' ∈ Set.Icc 0 S →
        |deriv (fun z'' => profFull α g z'' θ τ) z
          - deriv (fun z'' => profFull α g z'' θ τ') z'| ≤ N * (|z - z'| + |τ - τ'|) ^ α) := by
  -- the static part: bounds for `∂_z F_*` on `[0,R]`
  obtain ⟨M0, N0, hM0, hN0, hM0b, hN0b⟩ := fstarDzUniform h.hα h.hα13 hR
  -- the perturbation part: the jet of `∂_z g`
  obtain ⟨Npz, hNpz⟩ := h.hpz
  have hNpz0 : 0 ≤ Npz := hNpz.1
  -- conjunct 1: `deriv` is additive on the sum `F_* + g`
  have hpart1 : ∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
      deriv (fun z' => profFull α g z' θ τ) z
        = deriv (fun z' => Work.Construction.Fstar (pExp α) z' θ) z
          + Work.Spaces.pz (gSlice g τ) z θ := by
    intro z θ τ hz hθ hτ
    have hFd : DifferentiableAt ℝ (fun z' => Work.Construction.Fstar (pExp α) z' θ) z :=
      fstarSlice_differentiableAt z θ (by linarith)
    have hGd : DifferentiableAt ℝ (fun z' => g z' θ τ) z :=
      gSlice_differentiableAt h θ hθ z τ hz hτ
    exact deriv_add hFd hGd
  refine ⟨hpart1, ?_, ?_⟩
  · -- conjunct 2: triangle inequality, `M = M0 + Npz`
    refine ⟨M0 + Npz, by linarith, ?_⟩
    intro z θ τ hz hzR hθ hτ
    rw [hpart1 z θ τ hz hθ hτ]
    have h1 := hM0b z θ hz hzR hθ
    have h2 := hNpz.abs_le hz hθ hτ
    calc |deriv (fun z' => Work.Construction.Fstar (pExp α) z' θ) z
            + Work.Spaces.pz (gSlice g τ) z θ|
        ≤ |deriv (fun z' => Work.Construction.Fstar (pExp α) z' θ) z|
          + |Work.Spaces.pz (gSlice g τ) z θ| := abs_add_le _ _
      _ ≤ M0 + Npz := add_le_add h1 h2
  · -- conjunct 3: triangle inequality; the static part is `α`-Hölder, the perturbation part is
    -- jointly `α`-Hölder by its jet (at `θ = θ'`), then `|z-z'|^α ≤ (|z-z'|+|τ-τ'|)^α`
    refine ⟨N0 + Npz, by linarith, ?_⟩
    intro z z' θ τ τ' hz hzR hz' hz'R hθ hτ hτ'
    rw [hpart1 z θ τ hz hθ hτ, hpart1 z' θ τ' hz' hθ hτ']
    have h1 := hN0b z z' θ hz hzR hz' hz'R hθ
    have h2 := hNpz.2.2 z z' θ θ τ τ' hz hz' hθ hθ hτ hτ'
    have h3 : |z - z'| ^ α ≤ (|z - z'| + |τ - τ'|) ^ α :=
      Real.rpow_le_rpow (abs_nonneg _) (le_add_of_nonneg_right (abs_nonneg _)) h.hα.le
    have h5 : (0 : ℝ) ≤ (|z - z'| + |τ - τ'|) ^ α := Real.rpow_nonneg (by positivity) _
    have h6 : (0 : ℝ) ≤ N0 := hN0
    calc |deriv (fun z'' => Work.Construction.Fstar (pExp α) z'' θ) z
            + Work.Spaces.pz (gSlice g τ) z θ
            - (deriv (fun z'' => Work.Construction.Fstar (pExp α) z'' θ) z'
              + Work.Spaces.pz (gSlice g τ') z' θ)|
        = |(deriv (fun z'' => Work.Construction.Fstar (pExp α) z'' θ) z
              - deriv (fun z'' => Work.Construction.Fstar (pExp α) z'' θ) z')
            + (Work.Spaces.pz (gSlice g τ) z θ - Work.Spaces.pz (gSlice g τ') z' θ)| := by
          ring_nf
      _ ≤ |deriv (fun z'' => Work.Construction.Fstar (pExp α) z'' θ) z
              - deriv (fun z'' => Work.Construction.Fstar (pExp α) z'' θ) z'|
            + |Work.Spaces.pz (gSlice g τ) z θ - Work.Spaces.pz (gSlice g τ') z' θ| :=
          abs_add_le _ _
      _ ≤ N0 * |z - z'| ^ α + Npz * (|z - z'| + |θ - θ| + |τ - τ'|) ^ α :=
          add_le_add h1 h2
      _ ≤ (N0 + Npz) * (|z - z'| + |τ - τ'|) ^ α := by
          simp only [sub_self, abs_zero, add_zero] at *
          nlinarith [mul_le_mul_of_nonneg_left h3 h6, h5]

end Work.FTS.Regularity
end
end
-- ===== merged: Submission.Work.FTS.Regularity.physVort_holder_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Regularity

/-! ## 1. The explicit Hölder constant of `x ↦ omegaS (3α) g x` -/

/-- The Hölder constant of `x ↦ omegaS (3α) g x` produced by the chain
"composite + frame vector" (`gCompConstNN` and `smulEThetaConst`), with the `F_*`-part constant
`Cω` supplied from outside (it depends on `α` only). -/
def omegaSHolderConst (α Cv Lg Lθ K : ℝ) (Cω : NNReal) : NNReal :=
  3 * (Cω * ‖(3 * α / Work.Spaces.c (3 * α))‖₊
      + smulEThetaConst ((gCompConstNN α Cv Lg Lθ K : ℝ)) (max K Cv))

/-! ## 2. The half-space/odd extension at an *explicit* constant

This is `Work.ConstructionInstance.holder_of_half_odd` with the existential constant of the
half-space part replaced by the explicit one, which is what makes the estimate uniform. -/

theorem holder_of_half_odd_const {ω Φ : R3 → R3} {α : ℝ} (hα : 0 < α) {C : NNReal}
    (hΦ : HolderWith C (⟨α, hα.le⟩ : NNReal) Φ)
    (hhalf : ∀ x : R3, 0 ≤ x 2 → ω x = Φ x)
    (hodd : ∀ x : R3, ω (Work.Cyl.reflZ x) = - ω x)
    (hplane : ∀ x : R3, x 2 = 0 → Φ x = 0) :
    HolderWith (3 * C) (⟨α, hα.le⟩ : NNReal) ω := by
  have hΦb : ∀ a b : R3, ‖Φ a - Φ b‖ ≤ (C : ℝ) * ‖a - b‖ ^ α := by
    intro a b
    have h := hΦ.dist_le a b
    rw [dist_eq_norm, dist_eq_norm] at h
    exact h
  have hCnn : (0 : ℝ) ≤ (C : ℝ) := C.coe_nonneg
  have key : ∀ x y : R3, ‖ω x - ω y‖ ≤ 3 * (C : ℝ) * ‖x - y‖ ^ α := by
    intro x y
    have hxy : (0 : ℝ) ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
    have refl2 : ∀ z : R3, (Work.Cyl.reflZ z) 2 = - z 2 := by
      intro z; simp [Work.Cyl.reflZ]
    rcases le_or_gt (0 : ℝ) (x 2) with hx | hx
    · rcases le_or_gt (0 : ℝ) (y 2) with hy | hy
      · rw [hhalf x hx, hhalf y hy]
        calc ‖Φ x - Φ y‖ ≤ (C : ℝ) * ‖x - y‖ ^ α := hΦb x y
          _ ≤ 3 * (C : ℝ) * ‖x - y‖ ^ α := by nlinarith
      · have hy2 : 0 ≤ (Work.Cyl.reflZ y) 2 := by rw [refl2]; linarith
        have hry : ω (Work.Cyl.reflZ y) = Φ (Work.Cyl.reflZ y) := hhalf _ hy2
        have hwx : ω x = Φ x := hhalf x hx
        have hwy : ω y = - Φ (Work.Cyl.reflZ y) := by
          have h := hodd y
          rw [hry] at h
          rw [h]; simp
        have hmid : Φ (!₂[y 0, y 1, (0:ℝ)]) = 0 := hplane _ (by simp)
        have h1 := (Work.Cyl.dist_mid_neg_le hx hy).1
        have h2 := (Work.Cyl.dist_mid_neg_le hx hy).2
        have hpb : ‖Φ x + Φ (Work.Cyl.reflZ y)‖ ≤ 2 * (C : ℝ) * ‖x - y‖ ^ α := by
          have hdec : Φ x + Φ (Work.Cyl.reflZ y)
              = (Φ x - Φ (!₂[y 0, y 1, (0:ℝ)]))
                + (Φ (Work.Cyl.reflZ y) - Φ (!₂[y 0, y 1, (0:ℝ)])) := by
            rw [hmid]; abel
          rw [hdec]
          have htri := norm_add_le (Φ x - Φ (!₂[y 0, y 1, (0:ℝ)]))
            (Φ (Work.Cyl.reflZ y) - Φ (!₂[y 0, y 1, (0:ℝ)]))
          have ha : ‖Φ x - Φ (!₂[y 0, y 1, (0:ℝ)])‖ ≤ (C : ℝ) * ‖x - y‖ ^ α := by
            calc ‖Φ x - Φ (!₂[y 0, y 1, (0:ℝ)])‖
                ≤ (C : ℝ) * ‖x - !₂[y 0, y 1, (0:ℝ)]‖ ^ α := hΦb x _
              _ ≤ (C : ℝ) * ‖x - y‖ ^ α := by
                  apply mul_le_mul_of_nonneg_left _ hCnn
                  apply Real.rpow_le_rpow (norm_nonneg _) _ hα.le
                  rw [← dist_eq_norm, ← dist_eq_norm]
                  exact h1
          have hb : ‖Φ (Work.Cyl.reflZ y) - Φ (!₂[y 0, y 1, (0:ℝ)])‖
              ≤ (C : ℝ) * ‖x - y‖ ^ α := by
            calc ‖Φ (Work.Cyl.reflZ y) - Φ (!₂[y 0, y 1, (0:ℝ)])‖
                ≤ (C : ℝ) * ‖Work.Cyl.reflZ y - !₂[y 0, y 1, (0:ℝ)]‖ ^ α := hΦb _ _
              _ ≤ (C : ℝ) * ‖x - y‖ ^ α := by
                  apply mul_le_mul_of_nonneg_left _ hCnn
                  apply Real.rpow_le_rpow (norm_nonneg _) _ hα.le
                  rw [← dist_eq_norm, ← dist_eq_norm]
                  exact h2
          calc ‖(Φ x - Φ (!₂[y 0, y 1, (0:ℝ)]))
                  + (Φ (Work.Cyl.reflZ y) - Φ (!₂[y 0, y 1, (0:ℝ)]))‖
              ≤ _ := htri
            _ ≤ (C : ℝ) * ‖x - y‖ ^ α + (C : ℝ) * ‖x - y‖ ^ α := add_le_add ha hb
            _ = 2 * (C : ℝ) * ‖x - y‖ ^ α := by ring
        have hsplit : ω x - ω y = Φ x + Φ (Work.Cyl.reflZ y) := by rw [hwx, hwy]; abel
        rw [hsplit]
        calc ‖Φ x + Φ (Work.Cyl.reflZ y)‖ ≤ 2 * (C : ℝ) * ‖x - y‖ ^ α := hpb
          _ ≤ 3 * (C : ℝ) * ‖x - y‖ ^ α := by nlinarith
    · rcases le_or_gt (0 : ℝ) (y 2) with hy | hy
      · have hx2 : 0 ≤ (Work.Cyl.reflZ x) 2 := by rw [refl2]; linarith
        have hrx : ω (Work.Cyl.reflZ x) = Φ (Work.Cyl.reflZ x) := hhalf _ hx2
        have hwx : ω x = - Φ (Work.Cyl.reflZ x) := by
          have h := hodd x
          rw [hrx] at h
          rw [h]; simp
        have hwy : ω y = Φ y := hhalf y hy
        have hmid : Φ (!₂[y 0, y 1, (0:ℝ)]) = 0 := hplane _ (by simp)
        have h1 := (Work.Cyl.dist_mid_pos_le hx hy).1
        have h2 := (Work.Cyl.dist_mid_pos_le hx hy).2
        have hpb : ‖Φ (Work.Cyl.reflZ x) + Φ y‖ ≤ 2 * (C : ℝ) * ‖x - y‖ ^ α := by
          have hdec : Φ (Work.Cyl.reflZ x) + Φ y
              = (Φ (Work.Cyl.reflZ x) - Φ (!₂[y 0, y 1, (0:ℝ)]))
                + (Φ y - Φ (!₂[y 0, y 1, (0:ℝ)])) := by
            rw [hmid]; abel
          rw [hdec]
          have htri := norm_add_le (Φ (Work.Cyl.reflZ x) - Φ (!₂[y 0, y 1, (0:ℝ)]))
            (Φ y - Φ (!₂[y 0, y 1, (0:ℝ)]))
          have ha : ‖Φ (Work.Cyl.reflZ x) - Φ (!₂[y 0, y 1, (0:ℝ)])‖
              ≤ (C : ℝ) * ‖x - y‖ ^ α := by
            calc ‖Φ (Work.Cyl.reflZ x) - Φ (!₂[y 0, y 1, (0:ℝ)])‖
                ≤ (C : ℝ) * ‖Work.Cyl.reflZ x - !₂[y 0, y 1, (0:ℝ)]‖ ^ α := hΦb _ _
              _ ≤ (C : ℝ) * ‖x - y‖ ^ α := by
                  apply mul_le_mul_of_nonneg_left _ hCnn
                  apply Real.rpow_le_rpow (norm_nonneg _) _ hα.le
                  rw [← dist_eq_norm, ← dist_eq_norm]
                  exact h1
          have hb : ‖Φ y - Φ (!₂[y 0, y 1, (0:ℝ)])‖ ≤ (C : ℝ) * ‖x - y‖ ^ α := by
            calc ‖Φ y - Φ (!₂[y 0, y 1, (0:ℝ)])‖
                ≤ (C : ℝ) * ‖y - !₂[y 0, y 1, (0:ℝ)]‖ ^ α := hΦb y _
              _ ≤ (C : ℝ) * ‖x - y‖ ^ α := by
                  apply mul_le_mul_of_nonneg_left _ hCnn
                  apply Real.rpow_le_rpow (norm_nonneg _) _ hα.le
                  rw [← dist_eq_norm, ← dist_eq_norm]
                  exact h2
          calc ‖(Φ (Work.Cyl.reflZ x) - Φ (!₂[y 0, y 1, (0:ℝ)]))
                  + (Φ y - Φ (!₂[y 0, y 1, (0:ℝ)]))‖
              ≤ _ := htri
            _ ≤ (C : ℝ) * ‖x - y‖ ^ α + (C : ℝ) * ‖x - y‖ ^ α := add_le_add ha hb
            _ = 2 * (C : ℝ) * ‖x - y‖ ^ α := by ring
        have hsplit : ω x - ω y = - (Φ (Work.Cyl.reflZ x) + Φ y) := by rw [hwx, hwy]; abel
        rw [hsplit, norm_neg]
        calc ‖Φ (Work.Cyl.reflZ x) + Φ y‖ ≤ 2 * (C : ℝ) * ‖x - y‖ ^ α := hpb
          _ ≤ 3 * (C : ℝ) * ‖x - y‖ ^ α := by nlinarith
      · have hx2 : 0 ≤ (Work.Cyl.reflZ x) 2 := by rw [refl2]; linarith
        have hy2 : 0 ≤ (Work.Cyl.reflZ y) 2 := by rw [refl2]; linarith
        have hrx : ω (Work.Cyl.reflZ x) = Φ (Work.Cyl.reflZ x) := hhalf _ hx2
        have hry : ω (Work.Cyl.reflZ y) = Φ (Work.Cyl.reflZ y) := hhalf _ hy2
        have hwx : ω x = - Φ (Work.Cyl.reflZ x) := by
          have h := hodd x
          rw [hrx] at h
          rw [h]; simp
        have hwy : ω y = - Φ (Work.Cyl.reflZ y) := by
          have h := hodd y
          rw [hry] at h
          rw [h]; simp
        have hsplit : ω x - ω y
            = - (Φ (Work.Cyl.reflZ x) - Φ (Work.Cyl.reflZ y)) := by rw [hwx, hwy]; abel
        rw [hsplit, norm_neg]
        calc ‖Φ (Work.Cyl.reflZ x) - Φ (Work.Cyl.reflZ y)‖
            ≤ (C : ℝ) * ‖Work.Cyl.reflZ x - Work.Cyl.reflZ y‖ ^ α := hΦb _ _
          _ ≤ (C : ℝ) * ‖x - y‖ ^ α := by
              apply mul_le_mul_of_nonneg_left _ hCnn
              apply Real.rpow_le_rpow (norm_nonneg _) _ hα.le
              rw [← dist_eq_norm, ← dist_eq_norm]
              exact Work.Cyl.dist_reflZ_le x y
          _ ≤ 3 * (C : ℝ) * ‖x - y‖ ^ α := by nlinarith
  refine Work.Stability.holderWith_of_dist_le (C := 3 * C) (r := ⟨α, hα.le⟩) ?_
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  have hco : ((3 * C : NNReal) : ℝ) = 3 * (C : ℝ) := by push_cast; ring
  rw [hco]
  exact key x y

/-! ## 3. The cylindrical coordinates under a positive dilation -/

lemma radial_smul_dev {c : ℝ} (hc : 0 ≤ c) (x : R3) :
    Work.Cyl.radial (c • x) = c * Work.Cyl.radial x := by
  rw [Work.Cyl.radial, Work.Cyl.radial,
    show Work.Cyl.radSq (c • x) = c ^ 2 * Work.Cyl.radSq x by
      simp only [Work.Cyl.radSq, PiLp.smul_apply, smul_eq_mul]; ring,
    Real.sqrt_mul (by positivity) (Work.Cyl.radSq x), Real.sqrt_sq_eq_abs, abs_of_nonneg hc]

lemma rho_smul_dev {c : ℝ} (hc : 0 ≤ c) (x : R3) :
    Work.Cyl.rho (c • x) = c * Work.Cyl.rho x := by
  rw [Work.Cyl.rho_eq_norm, Work.Cyl.rho_eq_norm, norm_smul, Real.norm_of_nonneg hc]

lemma angularVec_smul_dev (c : ℝ) (x : R3) :
    Work.Cyl.angularVec (c • x) = c • Work.Cyl.angularVec x := by
  ext i; fin_cases i <;> simp [Work.Cyl.angularVec]

lemma theta_smul_dev {c : ℝ} (hc : 0 < c) (x : R3) :
    Work.Cyl.theta (c • x) = Work.Cyl.theta x := by
  rw [Work.Cyl.theta, Work.Cyl.theta]
  congr 1
  rw [show Work.Cyl.axial (c • x) = c * Work.Cyl.axial x by
        simp only [Work.Cyl.axial, PiLp.smul_apply, smul_eq_mul], radial_smul_dev hc.le]
  field_simp

lemma eTheta_smul_dev {c : ℝ} (hc : 0 < c) (x : R3) :
    Work.Cyl.eTheta (c • x) = Work.Cyl.eTheta x := by
  rw [Work.Cyl.eTheta, Work.Cyl.eTheta, radial_smul_dev hc.le, angularVec_smul_dev, smul_smul]
  congr 1
  field_simp

/-! ## 4. The self-similar vorticity of a slice is `α`-Hölder, with an explicit constant -/

theorem omegaS_holder_dev {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : ℝ → ℝ → ℝ}
    {Cv Lg Lθ K : ℝ} (hCv : 0 ≤ Cv) (hLg : 0 ≤ Lg) (hLθ : 0 ≤ Lθ) (hK : 0 ≤ K)
    (hvt : Work.Spaces.VanishTheta g)
    (hquad0 : ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ → g 0 θ = 0)
    (hvan : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ| ≤ Cv * Gamma α θ)
    (hzk : ∀ z z' θ : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ →
      |g z θ - g z' θ| ≤ Lg * |z - z'| ^ α)
    (hzth : ∀ z θ θ' : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |g z θ - g z θ'| ≤ Lθ * |θ - θ'| ^ α)
    (hKquad : ∀ z θ : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ K * z ^ 2)
    (hKz : ∀ z z' θ : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 → θ ∈ Work.Spaces.Iθ →
      |g z θ - g z' θ| ≤ K * max z z' * |z - z'|)
    (hKth : ∀ z θ θ' : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |g z θ - g z θ'| ≤ K * z * |θ - θ'|)
    (hlin : ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ → ∀ z : ℝ, 0 ≤ z → z ≤ 1 → |g z θ| ≤ K * z)
    {Cω : NNReal}
    (hCω : HolderWith Cω (⟨α, hα.le⟩ : NNReal) (Work.ConstructionInstance.omegaStar α)) :
    HolderWith (omegaSHolderConst α Cv Lg Lθ K Cω) (⟨α, hα.le⟩ : NNReal)
      (Work.ConstructionInstance.omegaS (3 * α) g) := by
  classical
  have hα1 : α ≤ 1 := by linarith
  have hθI : ∀ x : R3, |Work.Cyl.theta x| ∈ Work.Spaces.Iθ := by
    intro x
    refine ⟨abs_nonneg _, ?_⟩
    rw [abs_le]
    exact ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _), le_of_lt (Real.arctan_lt_pi_div_two _)⟩
  -- Extend the slice off the angular interval `Iθ`, so that the vanishing at `z = 0` holds for
  -- *all* angles: this is the form of the Taylor datum consumed by the composite estimate.
  -- On `Iθ` (where the composite is evaluated, since `|θ x| ∈ Iθ`) nothing changes.
  set G : ℝ → ℝ → ℝ := fun z θ => if θ ∈ Work.Spaces.Iθ then g z θ else 0 with hG
  have hG_eq : ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ → G z θ = g z θ := by
    intro z θ hθ
    rw [hG]
    exact ite_eq_left hθ
  have hquad0G : ∀ θ : ℝ, G 0 θ = 0 := by
    intro θ
    by_cases hθ : θ ∈ Work.Spaces.Iθ
    · rw [hG_eq 0 θ hθ]; exact hquad0 θ hθ
    · rw [hG]; exact ite_eq_right hθ
  have hvanG : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |G z θ| ≤ Cv * Gamma α θ :=
    fun z θ hz hθ => by rw [hG_eq z θ hθ]; exact hvan z θ hz hθ
  have hzkG : ∀ z z' θ : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ →
      |G z θ - G z' θ| ≤ Lg * |z - z'| ^ α :=
    fun z z' θ hz hz' hθ => by
      rw [hG_eq z θ hθ, hG_eq z' θ hθ]; exact hzk z z' θ hz hz' hθ
  have hzthG : ∀ z θ θ' : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |G z θ - G z θ'| ≤ Lθ * |θ - θ'| ^ α :=
    fun z θ θ' hz hθ hθ' => by
      rw [hG_eq z θ hθ, hG_eq z θ' hθ']; exact hzth z θ θ' hz hθ hθ'
  have hKquadG : ∀ z θ : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ → |G z θ| ≤ K * z ^ 2 :=
    fun z θ hz hz2 hθ => by rw [hG_eq z θ hθ]; exact hKquad z θ hz hz2 hθ
  have hKzG : ∀ z z' θ : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 → θ ∈ Work.Spaces.Iθ →
      |G z θ - G z' θ| ≤ K * max z z' * |z - z'| :=
    fun z z' θ hz hz2 hz' hz'2 hθ => by
      rw [hG_eq z θ hθ, hG_eq z' θ hθ]; exact hKz z z' θ hz hz2 hz' hz'2 hθ
  have hKthG : ∀ z θ θ' : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |G z θ - G z θ'| ≤ K * z * |θ - θ'| :=
    fun z θ θ' hz hz2 hθ hθ' => by
      rw [hG_eq z θ hθ, hG_eq z θ' hθ']; exact hKth z θ θ' hz hz2 hθ hθ'
  have hvtG : Work.Spaces.VanishTheta G :=
    ⟨fun z => by rw [hG_eq z 0 Work.Spaces.zero_mem_Iθ]; exact hvt.1 z,
     fun z => by rw [hG_eq z (Real.pi / 2) Work.Spaces.pi_half_mem_Iθ]; exact hvt.2 z⟩
  set ĝ : R3 → ℝ := fun x => G (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|) with hĝ
  have hĝ_holder : HolderWith (gCompConstNN α Cv Lg Lθ K) (⟨α, hα.le⟩ : NNReal) ĝ :=
    gCompHolderQuant hα hα13 hCv hLg hLθ hK hvtG hquad0G hvanG hzkG hzthG hKquadG hKzG hKthG
  have hĝ_abs : ∀ x : R3, |ĝ x| ≤ max K Cv * (Work.Cyl.radial x) ^ α := by
    intro x
    have hx : ĝ x = g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|) := by
      simp only [hĝ]
      exact hG_eq _ _ (hθI x)
    rw [hx]
    exact gComp_abs_le_quant hα hα13 hCv hK hvt hvan hlin x
  have hE : HolderWith (smulEThetaConst ((gCompConstNN α Cv Lg Lθ K : ℝ)) (max K Cv))
      (⟨α, hα.le⟩ : NNReal) (fun x : R3 => ĝ x • Work.Cyl.eTheta x) :=
    smulEThetaHolder hα hα1 (gCompConstNN α Cv Lg Lθ K).coe_nonneg
      (le_trans hCv (le_max_right K Cv)) hĝ_holder hĝ_abs
  have hS : HolderWith (Cω * ‖(3 * α / Work.Spaces.c (3 * α))‖₊) (⟨α, hα.le⟩ : NNReal)
      (fun x : R3 =>
        (3 * α / Work.Spaces.c (3 * α)) • Work.ConstructionInstance.omegaStar α x) :=
    HolderWith.smul (3 * α / Work.Spaces.c (3 * α)) hCω
  have hΦ : HolderWith (Cω * ‖(3 * α / Work.Spaces.c (3 * α))‖₊
        + smulEThetaConst ((gCompConstNN α Cv Lg Lθ K : ℝ)) (max K Cv))
      (⟨α, hα.le⟩ : NNReal)
      (fun x : R3 =>
        (3 * α / Work.Spaces.c (3 * α)) • Work.ConstructionInstance.omegaStar α x
          + ĝ x • Work.Cyl.eTheta x) :=
    HolderWith.add hS hE
  have hhalf : ∀ x : R3, 0 ≤ x 2 → Work.ConstructionInstance.omegaS (3 * α) g x
      = (3 * α / Work.Spaces.c (3 * α)) • Work.ConstructionInstance.omegaStar α x
        + ĝ x • Work.Cyl.eTheta x := by
    intro x hx
    have hθ : 0 ≤ Work.Cyl.theta x := Work.ConstructionInstance.theta_nonneg_of_axial_nonneg hx
    have hAom : Work.ConstructionInstance.Aom α x = Work.ConstructionInstance.A0 α x := by
      rw [Work.ConstructionInstance.Aom, Work.ConstructionInstance.cSign,
        ite_eq_left hx, one_mul]
    have hGF : Gamma α (Work.Cyl.theta x) * Work.FM.Fstar (Work.Cyl.rho x ^ (3 * α))
        = Work.ConstructionInstance.A0 α x := by
      rw [← hAom, Work.ConstructionInstance.Gamma_mul_Fstar_eq_Aom α hα x]
    have hF : Work.Construction.Fstar (3 * α) (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.theta x)
        = (3 * α / Work.Spaces.c (3 * α)) * Work.ConstructionInstance.A0 α x := by
      have hGam : Work.Spaces.Gam (3 * α) (Work.Cyl.theta x)
          = Work.ConstructionInstance.Gamma α (Work.Cyl.theta x) := by
        rw [Work.Spaces.Gam, Work.ConstructionInstance.Gamma,
          show (3 * α) / 3 = α by ring]
      rw [Work.Construction.Fstar, hGam]
      conv_rhs => rw [← hGF]
      ring
    have hĝx : ĝ x = g (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.theta x) := by
      simp only [hĝ]
      rw [hG_eq _ _ (hθI x), abs_of_nonneg hθ]
    rw [Work.ConstructionInstance.omegaS_apply', Work.ConstructionInstance.profile_of_nonneg hθ,
      hF, hĝx, Work.ConstructionInstance.omegaStar_apply,
      Work.ConstructionInstance.Gamma_mul_Fstar_eq_Aom α hα x, hAom, smul_smul, ← add_smul]
  have hplane : ∀ x : R3, x 2 = 0 →
      (3 * α / Work.Spaces.c (3 * α)) • Work.ConstructionInstance.omegaStar α x
        + ĝ x • Work.Cyl.eTheta x = 0 := by
    intro x hx
    have hθ0 : Work.Cyl.theta x = 0 := by
      rw [Work.Cyl.theta, Work.Cyl.axial, hx]; simp
    have hA0 : Work.ConstructionInstance.A0 α x = 0 := by
      simp [Work.ConstructionInstance.A0, hx, Real.zero_rpow (ne_of_gt hα)]
    have hAom : Work.ConstructionInstance.Aom α x = 0 := by
      rw [Work.ConstructionInstance.Aom, Work.ConstructionInstance.cSign,
        ite_eq_left (le_of_eq hx.symm), one_mul, hA0]
    have hĝ0 : ĝ x = 0 := by
      simp only [hĝ]
      rw [hG_eq _ _ (hθI x), hθ0, abs_zero]
      exact hvt.1 _
    rw [Work.ConstructionInstance.omegaStar_apply,
      Work.ConstructionInstance.Gamma_mul_Fstar_eq_Aom α hα x, hAom, hĝ0]
    simp
  have hodd : ∀ x : R3,
      Work.ConstructionInstance.omegaS (3 * α) g (Work.Cyl.reflZ x)
        = - Work.ConstructionInstance.omegaS (3 * α) g x := by
    intro x
    have hrho : Work.Cyl.rho (Work.Cyl.reflZ x) = Work.Cyl.rho x := by
      simp [Work.Cyl.rho, Work.Cyl.radSq, Work.Cyl.axial, Work.Cyl.reflZ]
    have hth : Work.Cyl.theta (Work.Cyl.reflZ x) = - Work.Cyl.theta x := by
      simp [Work.Cyl.theta, Work.Cyl.radial, Work.Cyl.radSq, Work.Cyl.axial, Work.Cyl.reflZ,
        neg_div, Real.arctan_neg]
    have he : Work.Cyl.eTheta (Work.Cyl.reflZ x) = Work.Cyl.eTheta x := by
      simp [Work.Cyl.eTheta, Work.Cyl.radial, Work.Cyl.radSq, Work.Cyl.angularVec,
        Work.Cyl.reflZ]
    rw [Work.ConstructionInstance.omegaS_apply', Work.ConstructionInstance.omegaS_apply',
      hrho, hth, he,
      Work.ConstructionInstance.profile_odd (by positivity : (3:ℝ) * α ≠ 0)
        (fun z => hvt.1 z), neg_smul]
  exact holder_of_half_odd_const hα hΦ hhalf hodd hplane

/-! ## 5. The target: the physical vorticity slices are `α`-Hölder, uniformly on `[0,S]` -/

theorem physVort_holder_slice {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.Regularity.RegPkg α S A B g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc 0 S, ∀ x y : Work.FTS.Regularity.R3,
      ‖Work.FTS.Regularity.physVort α A B g x τ - Work.FTS.Regularity.physVort α A B g y τ‖
        ≤ C * ‖x - y‖ ^ α := by
  have hα : 0 < α := h.hα
  have hα13 : α ≤ 1 / 3 := h.hα13
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨Cv, hCv0, hvan⟩ := h.hvan
  obtain ⟨Ng, hJet⟩ := h.hg
  have hLg : 0 ≤ Ng := hJet.1
  obtain ⟨K, hK0, htay⟩ := h.htay
  obtain ⟨a₀, a₁, ha₀, hab⟩ := h.hAb
  obtain ⟨b₀, b₁, hb₀, hbb⟩ := h.hBb
  obtain ⟨Cω, hCω⟩ := Work.ConstructionInstance.holder_omegaStar (β := α) hα hα1
  set CωS := omegaSHolderConst α Cv Ng Ng K Cω with hCωS
  have hslice : ∀ τ ∈ Set.Icc 0 S, HolderWith CωS (⟨α, hα.le⟩ : NNReal)
      (Work.ConstructionInstance.omegaS (3 * α) (gSlice g τ)) := by
    intro τ hτ
    exact omegaS_holder_dev hα hα13 hCv0 hLg hLg hK0 (h.hvt τ hτ)
      (fun θ hθ => h.hquad0 τ hτ θ hθ)
      (fun z θ hz hθ => hvan τ hτ z θ hz hθ)
      (fun z z' θ hz hz' hθ => hJet.zmod hz hz' hθ hτ)
      (fun z θ θ' hz hθ hθ' => hJet.thmod hz hθ hθ' hτ)
      (fun z θ hz hz2 hθ => (htay τ hτ θ hθ).1 z hz hz2)
      (fun z z' θ hz hz2 hz' hz'2 hθ => (htay τ hτ θ hθ).2.1 z z' hz hz2 hz' hz'2)
      (fun z θ θ' hz hz2 hθ hθ' => (htay τ hτ θ hθ).2.2 z hz hz2 θ' hθ')
      (fun θ hθ z hz hz1 => by
        have h1 := (htay τ hτ θ hθ).1 z hz (le_trans hz1 (by norm_num))
        have h2 : z ^ 2 ≤ z := by nlinarith
        exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hK0))
      hCω
  set bmax : ℝ := (b₀⁻¹) ^ (1 / (3 * α)) with hbmax
  have hbmaxnn : 0 ≤ bmax := Real.rpow_nonneg (inv_nonneg.mpr hb₀.le) _
  refine ⟨a₀⁻¹ * (CωS : ℝ) * bmax ^ α, ?_, ?_⟩
  · have h1 : 0 ≤ a₀⁻¹ := inv_nonneg.mpr ha₀.le
    have h2 : 0 ≤ (CωS : ℝ) := CωS.coe_nonneg
    exact mul_nonneg (mul_nonneg h1 h2) (Real.rpow_nonneg hbmaxnn _)
  · intro τ hτ x y
    have hAτ : a₀ ≤ A τ := (hab τ hτ).1
    have hApos : 0 < A τ := lt_of_lt_of_le ha₀ hAτ
    have hBτ : b₀ ≤ B τ := (hbb τ hτ).1
    have hBpos : 0 < B τ := lt_of_lt_of_le hb₀ hBτ
    set b : ℝ := (B τ)⁻¹ ^ (1 / (3 * α)) with hb
    have hbpos : 0 < b := Real.rpow_pos_of_pos (inv_pos.mpr hBpos) _
    have hbp : b ^ (3 * α) = (B τ)⁻¹ := by
      rw [hb, ← Real.rpow_mul (inv_nonneg.mpr hBpos.le) (1 / (3 * α)) (3 * α),
        div_mul_cancel₀ 1 (by positivity : (3:ℝ) * α ≠ 0), Real.rpow_one]
    have hble : b ≤ bmax :=
      Real.rpow_le_rpow (inv_nonneg.mpr hBpos.le)
        ((inv_le_inv₀ hBpos hb₀).mpr hBτ) (by positivity)
    have hid : ∀ z : R3, Work.ConstructionInstance.omegaSz (3 * α) (gSlice g τ)
        (Work.Cyl.rho z ^ (3 * α) / B τ) z
        = Work.ConstructionInstance.omegaS (3 * α) (gSlice g τ) (b • z) := by
      intro z
      have hzb : Work.Cyl.rho (b • z) ^ (3 * α) = Work.Cyl.rho z ^ (3 * α) / B τ := by
        rw [rho_smul_dev hbpos.le z, Real.mul_rpow hbpos.le (Work.Cyl.rho_nonneg z), hbp,
          div_eq_mul_inv, mul_comm]
      rw [Work.ConstructionInstance.omegaS_apply', Work.ConstructionInstance.omegaSz_apply,
        theta_smul_dev hbpos z, eTheta_smul_dev hbpos z, hzb]
    have hH := (hslice τ hτ).dist_le (b • x) (b • y)
    rw [dist_eq_norm, dist_eq_norm] at hH
    have hH' : ‖Work.ConstructionInstance.omegaS (3 * α) (gSlice g τ) (b • x)
        - Work.ConstructionInstance.omegaS (3 * α) (gSlice g τ) (b • y)‖
        ≤ (CωS : ℝ) * ‖b • x - b • y‖ ^ α := hH
    have hbxy : ‖b • x - b • y‖ = b * ‖x - y‖ := by
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg hbpos.le]
    rw [hbxy, Real.mul_rpow hbpos.le (norm_nonneg (x - y))] at hH'
    have hbα : b ^ α ≤ bmax ^ α := Real.rpow_le_rpow hbpos.le hble hα.le
    have hCt : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
    have hcore : (CωS : ℝ) * b ^ α * ‖x - y‖ ^ α ≤ (CωS : ℝ) * bmax ^ α * ‖x - y‖ ^ α := by
      have h1 : (CωS : ℝ) * b ^ α ≤ (CωS : ℝ) * bmax ^ α :=
        mul_le_mul_of_nonneg_left hbα CωS.coe_nonneg
      exact mul_le_mul_of_nonneg_right h1 hCt
    have hinv : (A τ)⁻¹ ≤ a₀⁻¹ := (inv_le_inv₀ hApos ha₀).mpr hAτ
    have hAi : 0 ≤ (A τ)⁻¹ := inv_nonneg.mpr hApos.le
    calc ‖Work.FTS.Regularity.physVort α A B g x τ
            - Work.FTS.Regularity.physVort α A B g y τ‖
        = ‖(A τ)⁻¹ • (Work.ConstructionInstance.omegaSz (3 * α) (gSlice g τ)
              (Work.Cyl.rho x ^ (3 * α) / B τ) x)
            - (A τ)⁻¹ • (Work.ConstructionInstance.omegaSz (3 * α) (gSlice g τ)
              (Work.Cyl.rho y ^ (3 * α) / B τ) y)‖ := by
            rw [Work.FTS.Regularity.physVort_apply, Work.FTS.Regularity.physVort_apply,
              Work.FTS.Regularity.pExp_eq]
      _ = ‖(A τ)⁻¹ • (Work.ConstructionInstance.omegaSz (3 * α) (gSlice g τ)
              (Work.Cyl.rho x ^ (3 * α) / B τ) x
            - Work.ConstructionInstance.omegaSz (3 * α) (gSlice g τ)
              (Work.Cyl.rho y ^ (3 * α) / B τ) y)‖ := by
            rw [smul_sub]
      _ = |(A τ)⁻¹| * ‖Work.ConstructionInstance.omegaSz (3 * α) (gSlice g τ)
              (Work.Cyl.rho x ^ (3 * α) / B τ) x
            - Work.ConstructionInstance.omegaSz (3 * α) (gSlice g τ)
              (Work.Cyl.rho y ^ (3 * α) / B τ) y‖ := by
            rw [norm_smul, Real.norm_eq_abs]
      _ = (A τ)⁻¹ * ‖Work.ConstructionInstance.omegaSz (3 * α) (gSlice g τ)
              (Work.Cyl.rho x ^ (3 * α) / B τ) x
            - Work.ConstructionInstance.omegaSz (3 * α) (gSlice g τ)
              (Work.Cyl.rho y ^ (3 * α) / B τ) y‖ := by
            rw [abs_of_nonneg hAi]
      _ = (A τ)⁻¹ * ‖Work.ConstructionInstance.omegaS (3 * α) (gSlice g τ) (b • x)
            - Work.ConstructionInstance.omegaS (3 * α) (gSlice g τ) (b • y)‖ := by
            rw [hid x, hid y]
      _ ≤ (A τ)⁻¹ * ((CωS : ℝ) * b ^ α * ‖x - y‖ ^ α) := by
            apply mul_le_mul_of_nonneg_left _ hAi
            calc ‖Work.ConstructionInstance.omegaS (3 * α) (gSlice g τ) (b • x)
                  - Work.ConstructionInstance.omegaS (3 * α) (gSlice g τ) (b • y)‖
                ≤ (CωS : ℝ) * (b ^ α * ‖x - y‖ ^ α) := hH'
              _ = (CωS : ℝ) * b ^ α * ‖x - y‖ ^ α := by ring
      _ ≤ a₀⁻¹ * ((CωS : ℝ) * bmax ^ α * ‖x - y‖ ^ α) := by
            have hc0 : 0 ≤ (CωS : ℝ) * b ^ α * ‖x - y‖ ^ α :=
              mul_nonneg (mul_nonneg CωS.coe_nonneg (Real.rpow_nonneg hbpos.le _)) hCt
            exact mul_le_mul hinv hcore hc0 (inv_nonneg.mpr ha₀.le)
      _ = a₀⁻¹ * (CωS : ℝ) * bmax ^ α * ‖x - y‖ ^ α := by ring

end Work.FTS.Regularity
end
end
-- ===== merged: Submission.Work.FTS.Regularity.physVort_holder_time =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set

namespace Work.FTS.Regularity

/-! ## Elementary tools -/

/-- The triangle inequality for the absolute value, in the form used below (the `norm` version of
Mathlib, transported to `ℝ`). -/
theorem abs_add_le_aux {a b : ℝ} : |a + b| ≤ |a| + |b| := by
  simpa [Real.norm_eq_abs] using norm_add_le a b

/-- `|a - b| ≤ |a| + |b|`. -/
theorem abs_sub_le_aux {a b : ℝ} : |a - b| ≤ |a| + |b| := by
  simpa [Real.norm_eq_abs] using norm_sub_le a b

/-- **Mean value inequality on the strip.**  A function on `[0,S]` whose derivative (in the sense
of `deriv`, supplied by `HasDerivAt` at every point of the strip) is bounded by `C` is
`C`-Lipschitz there. -/
theorem abs_sub_le_of_deriv_bound {S : ℝ} {f : ℝ → ℝ}
    (hd : ∀ τ ∈ Set.Icc 0 S, HasDerivAt f (deriv f τ) τ) {C : ℝ}
    (hC : ∀ τ ∈ Set.Icc 0 S, |deriv f τ| ≤ C) :
    ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, |f τ - f τ'| ≤ C * |τ - τ'| := by
  intro τ hτ τ' hτ'
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := Set.Icc 0 S)
    (fun x hx => (hd x hx).differentiableAt)
    (fun x hx => by rw [Real.norm_eq_abs]; exact hC x hx) (convex_Icc 0 S) hτ hτ'
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  rw [abs_sub_comm (f τ') (f τ), abs_sub_comm τ' τ] at h
  exact h

/-- For `0 ≤ s ≤ 1` and `0 < α ≤ 1` one has `s ≤ s ^ α`. -/
theorem self_le_rpow {α s : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s ≤ s ^ α := by
  rcases eq_or_lt_of_le hs0 with h | h
  · rw [← h, Real.zero_rpow (ne_of_gt hα)]
  · have := Real.rpow_le_rpow_of_exponent_ge h hs1 hα1
    rwa [Real.rpow_one] at this

/-- The radial profile `F_*(z) = 2z/(1+z)²` of the fundamental model is `2`-Lipschitz on
`[0,∞)`: its derivative is `2(1-z)/(1+z)³`, whose absolute value is at most `2` there. -/
theorem FM_Fstar_abs_sub_le {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') :
    |Work.FM.Fstar z - Work.FM.Fstar z'| ≤ 2 * |z - z'| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (C := (2:ℝ))
    (f := Work.FM.Fstar) (s := Set.Ici (0:ℝ))
    (fun x hx => (Work.FM.hasDerivAt_Fstar x (by linarith [show (0:ℝ) ≤ x from hx])).differentiableAt)
    (fun x hx => ?_) (convex_Ici 0) hz hz'
  · rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
    rw [abs_sub_comm (Work.FM.Fstar z') (Work.FM.Fstar z), abs_sub_comm z' z] at h
    exact h
  · have hx0 : (0:ℝ) ≤ x := hx
    rw [Work.FM.deriv_Fstar x (by linarith), Real.norm_eq_abs]
    have hpos : (0:ℝ) < (1 + x) ^ 3 := by positivity
    rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_pos hpos]
    rw [div_le_iff₀ hpos]
    have h1 : |1 - x| ≤ 1 + x := by rw [abs_le]; constructor <;> linarith
    have h2 : (1:ℝ) ≤ 1 + x := by linarith
    nlinarith [h1, h2, sq_nonneg (1 + x), hx0]

/-- The profile `F_*(z,θ) = p·(Γ(θ)/c)·2z/(1+z)²` is `20p`-Lipschitz in `z` on `[0,∞)`. -/
theorem Fstar_abs_sub_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {z z' θ : ℝ}
    (hz : 0 ≤ z) (hz' : 0 ≤ z') (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar p z θ - Work.Construction.Fstar p z' θ| ≤ 20 * p * |z - z'| := by
  have hc := (Work.Spaces.c_bounds p hp hp1).1
  have hcpos : 0 < Work.Spaces.c p := by linarith
  have hG0 : 0 ≤ Work.Spaces.Gam p θ :=
    Work.ConstructionInstance.Gamma_nonneg (β := p / 3) hθ
  have hG1 : Work.Spaces.Gam p θ ≤ 1 := by
    rw [← Work.ConstructionInstance.Gamma_div_three]
    exact Work.ConstructionInstance.Gamma_le_one (by positivity) hθ
  have hcoef0 : 0 ≤ p * (Work.Spaces.Gam p θ / Work.Spaces.c p) := by positivity
  rw [Work.Construction.Fstar, Work.Construction.Fstar, ← mul_sub, abs_mul, abs_of_nonneg hcoef0]
  have hcoef : p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * 2 ≤ 20 * p := by
    have h2 : Work.Spaces.Gam p θ / Work.Spaces.c p ≤ 10 := by
      rw [div_le_iff₀ hcpos]; nlinarith
    nlinarith [hp.le, hG0]
  calc p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * |Work.FM.Fstar z - Work.FM.Fstar z'|
      ≤ p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * (2 * |z - z'|) :=
        mul_le_mul_of_nonneg_left (FM_Fstar_abs_sub_le hz hz') hcoef0
    _ = (p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * 2) * |z - z'| := by ring
    _ ≤ (20 * p) * |z - z'| := mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)

/-- The profile of a `τ`-slice is the *sign of the angle* times the full profile evaluated at the
absolute angle `|θ|` (the odd extension of the profile in `θ`). -/
theorem profile_eq_sign_profFull {α : ℝ} {g : ℝ → ℝ → ℝ → ℝ} (z τ θ : ℝ) :
    Work.ConstructionInstance.profile (pExp α) (gSlice g τ) z θ
      = (if 0 ≤ θ then (1:ℝ) else -1) * profFull α g z |θ| τ := by
  by_cases h : 0 ≤ θ
  · rw [ite_eq_left h, Work.ConstructionInstance.profile_of_nonneg h, abs_of_nonneg h]
    simp [profFull, one_mul]
  · rw [ite_eq_right h, Work.ConstructionInstance.profile_of_neg h, abs_of_neg (not_le.mp h)]
    simp [profFull]

/-! ## Joint `α`-Hölder continuity of the profile in `(z,τ)` -/

/-- **The full profile is jointly `α`-Hölder in `(z,τ)` at fixed angle.**  This is the quantitative
input from which the time-regularity of the physical vorticity is read off: the `g`-part is the
joint `α`-Hölder datum of `RegPkg.hg` in `(z,τ)` (the angular increment is `0`), and the
`F_*`-part is `Lipschitz` in `z` and bounded in `z`, so that the two regimes `t ≤ 1` and `t ≥ 1`
of the metric `t = |Δz| + |Δτ|` both give `C·t^α`. -/
theorem profFull_holder_ztau {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg α S A B g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z z' θ τ τ' : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ →
      τ ∈ Set.Icc 0 S → τ' ∈ Set.Icc 0 S →
      |profFull α g z θ τ - profFull α g z' θ τ'| ≤ C * (|z - z'| + |τ - τ'|) ^ α := by
  obtain ⟨Ng, hJet⟩ := h.hg
  have hNg0 : 0 ≤ Ng := hJet.1
  have hp0 : 0 < pExp α := pExp_pos h.hα
  have hp1 : pExp α ≤ 1 := pExp_le_one h.hα13
  have hα1 : α ≤ 1 := le_trans h.hα13 (by norm_num)
  refine ⟨40 * pExp α + Ng, by positivity, ?_⟩
  intro z z' θ τ τ' hz hz' hθ hτ hτ'
  have hsplit : profFull α g z θ τ - profFull α g z' θ τ'
      = (Work.Construction.Fstar (pExp α) z θ - Work.Construction.Fstar (pExp α) z' θ)
        + (g z θ τ - g z' θ τ') := by
    simp only [profFull]; ring
  have hF := Fstar_abs_sub_le hp0 hp1 hz hz' hθ
  have hJ : |g z θ τ - g z' θ τ'| ≤ Ng * (|z - z'| + |τ - τ'|) ^ α := by
    have h1 := hJet.2.2 z z' θ θ τ τ' hz hz' hθ hθ hτ hτ'
    simpa using h1
  have hT0 : 0 ≤ |z - z'| + |τ - τ'| := by positivity
  rcases le_total (|z - z'| + |τ - τ'|) 1 with hT1 | hT1
  · have hTp : |z - z'| + |τ - τ'| ≤ (|z - z'| + |τ - τ'|) ^ α :=
      self_le_rpow h.hα hα1 hT0 hT1
    have h20 : 0 ≤ 20 * pExp α := by positivity
    have hstep : 20 * pExp α * |z - z'| ≤ 20 * pExp α * (|z - z'| + |τ - τ'|) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (abs_nonneg _)) h20
    calc |profFull α g z θ τ - profFull α g z' θ τ'|
        ≤ |Work.Construction.Fstar (pExp α) z θ - Work.Construction.Fstar (pExp α) z' θ|
          + |g z θ τ - g z' θ τ'| := by rw [hsplit]; exact abs_add_le_aux
      _ ≤ 20 * pExp α * (|z - z'| + |τ - τ'|) + Ng * (|z - z'| + |τ - τ'|) ^ α :=
          add_le_add (le_trans hF hstep) hJ
      _ ≤ 20 * pExp α * (|z - z'| + |τ - τ'|) ^ α + Ng * (|z - z'| + |τ - τ'|) ^ α := by
          have h := mul_le_mul_of_nonneg_left hTp h20
          linarith
      _ = (20 * pExp α + Ng) * (|z - z'| + |τ - τ'|) ^ α := by ring
      _ ≤ (40 * pExp α + Ng) * (|z - z'| + |τ - τ'|) ^ α := by
          have h := Real.rpow_nonneg hT0 α
          nlinarith [h, hp0.le]
  · have hTp : (1:ℝ) ≤ (|z - z'| + |τ - τ'|) ^ α := Real.one_le_rpow hT1 h.hα.le
    have hF' : |Work.Construction.Fstar (pExp α) z θ - Work.Construction.Fstar (pExp α) z' θ|
        ≤ 40 * pExp α := by
      have h1 := Work.ConstructionInstance.Fstar_abs_le hp0 hp1 hz hθ
      have h2 := Work.ConstructionInstance.Fstar_abs_le hp0 hp1 hz' hθ
      have hG : Work.ConstructionInstance.Gamma (pExp α / 3) θ ≤ 1 :=
        Work.ConstructionInstance.Gamma_le_one (by positivity) hθ
      have hG0 : 0 ≤ Work.ConstructionInstance.Gamma (pExp α / 3) θ :=
        Work.ConstructionInstance.Gamma_nonneg hθ
      have e1 : |Work.Construction.Fstar (pExp α) z θ| ≤ 20 * pExp α := by
        refine le_trans h1 ?_
        have hm := mul_le_mul_of_nonneg_left hG (by positivity : (0:ℝ) ≤ pExp α)
        linarith
      have e2 : |Work.Construction.Fstar (pExp α) z' θ| ≤ 20 * pExp α := by
        refine le_trans h2 ?_
        have hm := mul_le_mul_of_nonneg_left hG (by positivity : (0:ℝ) ≤ pExp α)
        linarith
      calc |Work.Construction.Fstar (pExp α) z θ - Work.Construction.Fstar (pExp α) z' θ|
          ≤ |Work.Construction.Fstar (pExp α) z θ| + |Work.Construction.Fstar (pExp α) z' θ| :=
            abs_sub_le_aux
        _ ≤ 20 * pExp α + 20 * pExp α := add_le_add e1 e2
        _ = 40 * pExp α := by ring
    calc |profFull α g z θ τ - profFull α g z' θ τ'|
        ≤ |Work.Construction.Fstar (pExp α) z θ - Work.Construction.Fstar (pExp α) z' θ|
          + |g z θ τ - g z' θ τ'| := by rw [hsplit]; exact abs_add_le_aux
      _ ≤ 40 * pExp α + Ng * (|z - z'| + |τ - τ'|) ^ α := add_le_add hF' hJ
      _ ≤ 40 * pExp α * (|z - z'| + |τ - τ'|) ^ α + Ng * (|z - z'| + |τ - τ'|) ^ α := by
          have h1 : 40 * pExp α ≤ 40 * pExp α * (|z - z'| + |τ - τ'|) ^ α :=
            le_mul_of_one_le_right (by positivity) hTp
          linarith
      _ = (40 * pExp α + Ng) * (|z - z'| + |τ - τ'|) ^ α := by ring

/-! ## The time-Hölder continuity -/

theorem physVort_holder_time {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.Regularity.RegPkg α S A B g) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ x : Work.FTS.Regularity.R3, ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
      ‖Work.FTS.Regularity.physVort α A B g x τ - Work.FTS.Regularity.physVort α A B g x τ'‖
        ≤ N * |τ - τ'| ^ α := by
  obtain ⟨a₀, a₁, ha₀, hAb⟩ := h.hAb
  obtain ⟨b₀, b₁, hb₀, hBb⟩ := h.hBb
  obtain ⟨a₂, ha₂⟩ := h.hAd
  obtain ⟨b₂, hb₂⟩ := h.hBd
  obtain ⟨Ng, hJet⟩ := h.hg
  obtain ⟨L, hLpos, hLsupp⟩ := h.hsupp
  obtain ⟨C, hC0, hC⟩ := profFull_holder_ztau h
  have hS : 0 < S := h.hS
  have h0S : (0:ℝ) ∈ Set.Icc 0 S := ⟨le_rfl, hS.le⟩
  have ha₂0 : 0 ≤ a₂ := le_trans (abs_nonneg _) (ha₂ 0 h0S)
  have hb₂0 : 0 ≤ b₂ := le_trans (abs_nonneg _) (hb₂ 0 h0S)
  have hb₁0 : 0 < b₁ := lt_of_lt_of_le (lt_of_lt_of_le hb₀ (hBb 0 h0S).1) (hBb 0 h0S).2
  have hNg0 : 0 ≤ Ng := hJet.1
  have hα1 : α ≤ 1 := le_trans h.hα13 (by norm_num)
  have hAlip := abs_sub_le_of_deriv_bound h.hAdiff ha₂
  have hBlip := abs_sub_le_of_deriv_bound h.hBdiff hb₂
  set p : ℝ := pExp α with hpdef
  have hp0 : 0 < p := by rw [hpdef]; exact pExp_pos h.hα
  have hp1 : p ≤ 1 := by rw [hpdef]; exact pExp_le_one h.hα13
  set M : ℝ := 20 * p + Ng with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  set c : ℝ := L * b₁ * b₂ / b₀ ^ 2 with hcdef
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  have hc1 : 0 ≤ c + 1 := by linarith
  set K : ℝ := max ((1 / a₀) * (C * (c + 1) ^ α) + ((1 / a₀) * (20 * p * c) + (a₂ / a₀ ^ 2) * M))
    (2 * M / a₀) with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    refine le_trans ?_ (le_max_left _ _)
    have h1 : 0 ≤ (1 / a₀) * (C * (c + 1) ^ α) := by positivity
    have h2 : 0 ≤ (1 / a₀) * (20 * p * c) := by positivity
    have h3 : 0 ≤ (a₂ / a₀ ^ 2) * M := by positivity
    linarith
  refine ⟨K, hK0, ?_⟩
  intro x τ hτ τ' hτ'
  set θ : ℝ := Work.Cyl.theta x with hθdef
  set ϑ : ℝ := |θ| with hϑdef
  have hϑI : ϑ ∈ Work.Spaces.Iθ := by rw [hϑdef]; exact abs_theta_mem_Iθ x
  have hϑ0 : 0 ≤ ϑ := by rw [hϑdef]; exact abs_nonneg θ
  set ρ : ℝ := Work.Cyl.rho x with hρdef
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; exact Work.Cyl.rho_nonneg x
  set sgn : ℝ := if 0 ≤ θ then (1:ℝ) else -1 with hsgn
  have hsgn1 : |sgn| = 1 := by rw [hsgn]; split_ifs <;> simp
  have hZnn : ∀ s ∈ Set.Icc 0 S, 0 ≤ ρ ^ p / B s := fun s hs =>
    div_nonneg (Real.rpow_nonneg hρ0 p) (h.hB s hs).le
  have hQbound : ∀ s ∈ Set.Icc 0 S, |profFull α g (ρ ^ p / B s) ϑ s| ≤ M := by
    intro s hs
    have hz := hZnn s hs
    have h1 := Work.ConstructionInstance.Fstar_abs_le hp0 hp1 hz hϑI
    have hG : Work.ConstructionInstance.Gamma (p / 3) ϑ ≤ 1 :=
      Work.ConstructionInstance.Gamma_le_one (by positivity) hϑI
    have hG0 : 0 ≤ Work.ConstructionInstance.Gamma (p / 3) ϑ :=
      Work.ConstructionInstance.Gamma_nonneg hϑI
    have h2 := hJet.abs_le hz hϑI hs
    have h3 : |profFull α g (ρ ^ p / B s) ϑ s|
        ≤ 20 * p * Work.ConstructionInstance.Gamma (p / 3) ϑ + Ng := by
      have hprof : profFull α g (ρ ^ p / B s) ϑ s
          = Work.Construction.Fstar p (ρ ^ p / B s) ϑ + g (ρ ^ p / B s) ϑ s := rfl
      rw [hprof]
      exact le_trans abs_add_le_aux (add_le_add h1 h2)
    rw [hMdef]
    have hm := mul_le_mul_of_nonneg_left hG (by positivity : (0:ℝ) ≤ p)
    linarith
  have hrepr : ∀ s ∈ Set.Icc 0 S, physVort α A B g x s
      = (sgn * ((A s)⁻¹ * profFull α g (ρ ^ p / B s) ϑ s)) • Work.Cyl.eTheta x := by
    intro s hs
    rw [physVort_apply, Work.ConstructionInstance.omegaSz_apply, smul_smul]
    congr 1
    rw [profile_eq_sign_profFull (α := α) (g := g) (ρ ^ p / B s) s θ, ← hsgn, hϑdef]
    ring
  have hdiff : physVort α A B g x τ - physVort α A B g x τ'
      = (sgn * ((A τ)⁻¹ * profFull α g (ρ ^ p / B τ) ϑ τ)
          - sgn * ((A τ')⁻¹ * profFull α g (ρ ^ p / B τ') ϑ τ')) • Work.Cyl.eTheta x := by
    rw [hrepr τ hτ, hrepr τ' hτ', ← sub_smul]
  set X : ℝ := (A τ)⁻¹ * profFull α g (ρ ^ p / B τ) ϑ τ with hXdef
  set Y : ℝ := (A τ')⁻¹ * profFull α g (ρ ^ p / B τ') ϑ τ' with hYdef
  have hAτ0 : 0 < A τ := h.hA τ hτ
  have hAτ'0 : 0 < A τ' := h.hA τ' hτ'
  have hinvτ : (A τ)⁻¹ ≤ 1 / a₀ := by
    simpa using one_div_le_one_div_of_le ha₀ (hAb τ hτ).1
  have hinvτ' : (A τ')⁻¹ ≤ 1 / a₀ := by
    simpa using one_div_le_one_div_of_le ha₀ (hAb τ' hτ').1
  have hbX : |X| ≤ M / a₀ := by
    rw [hXdef, abs_mul, abs_of_pos (inv_pos.mpr hAτ0)]
    calc (A τ)⁻¹ * |profFull α g (ρ ^ p / B τ) ϑ τ| ≤ (1 / a₀) * M :=
          mul_le_mul hinvτ (hQbound τ hτ) (abs_nonneg _) (by positivity)
      _ = M / a₀ := by ring
  have hbY : |Y| ≤ M / a₀ := by
    rw [hYdef, abs_mul, abs_of_pos (inv_pos.mpr hAτ'0)]
    calc (A τ')⁻¹ * |profFull α g (ρ ^ p / B τ') ϑ τ'| ≤ (1 / a₀) * M :=
          mul_le_mul hinvτ' (hQbound τ' hτ') (abs_nonneg _) (by positivity)
      _ = M / a₀ := by ring
  have hcore : |X - Y| ≤ K * |τ - τ'| ^ α := by
    by_cases hcase : ρ ^ p ≤ L * b₁
    · have hZp : |ρ ^ p / B τ - ρ ^ p / B τ'| ≤ c * |τ - τ'| := by
        have hBτ : 0 < B τ := h.hB τ hτ
        have hBτ' : 0 < B τ' := h.hB τ' hτ'
        have hnum : |B τ' - B τ| ≤ b₂ * |τ - τ'| := by
          rw [abs_sub_comm]; exact hBlip τ hτ τ' hτ'
        have hden : b₀ ^ 2 ≤ B τ * B τ' := by
          have h1 := (hBb τ hτ).1
          have h2 := (hBb τ' hτ').1
          nlinarith [mul_le_mul h1 h2 hb₀.le hBτ.le]
        have hkey : |ρ ^ p / B τ - ρ ^ p / B τ'|
            = ρ ^ p * (|B τ' - B τ| / (B τ * B τ')) := by
          have hfac : ρ ^ p / B τ - ρ ^ p / B τ'
              = ρ ^ p * ((B τ' - B τ) / (B τ * B τ')) := by
            field_simp
          rw [hfac, abs_mul, abs_of_nonneg (Real.rpow_nonneg hρ0 p), abs_div,
            abs_of_pos (mul_pos hBτ hBτ')]
        rw [hkey, hcdef]
        have hstep : |B τ' - B τ| / (B τ * B τ') ≤ (b₂ / b₀ ^ 2) * |τ - τ'| := by
          calc |B τ' - B τ| / (B τ * B τ') ≤ b₂ * |τ - τ'| / (B τ * B τ') :=
                div_le_div_of_nonneg_right hnum (le_of_lt (mul_pos hBτ hBτ'))
            _ ≤ b₂ * |τ - τ'| / b₀ ^ 2 :=
                div_le_div_of_nonneg_left (mul_nonneg hb₂0 (abs_nonneg _)) (by positivity) hden
            _ = (b₂ / b₀ ^ 2) * |τ - τ'| := by ring
        calc ρ ^ p * (|B τ' - B τ| / (B τ * B τ'))
            ≤ ρ ^ p * ((b₂ / b₀ ^ 2) * |τ - τ'|) :=
              mul_le_mul_of_nonneg_left hstep (Real.rpow_nonneg hρ0 p)
          _ ≤ (L * b₁) * ((b₂ / b₀ ^ 2) * |τ - τ'|) :=
              mul_le_mul_of_nonneg_right hcase (by positivity)
          _ = L * b₁ * b₂ / b₀ ^ 2 * |τ - τ'| := by ring
      have hQh := hC (ρ ^ p / B τ) (ρ ^ p / B τ') ϑ τ τ' (hZnn τ hτ) (hZnn τ' hτ') hϑI hτ hτ'
      have hQh' : |profFull α g (ρ ^ p / B τ) ϑ τ - profFull α g (ρ ^ p / B τ') ϑ τ'|
          ≤ C * (c + 1) ^ α * |τ - τ'| ^ α := by
        have hT : |ρ ^ p / B τ - ρ ^ p / B τ'| + |τ - τ'| ≤ (c + 1) * |τ - τ'| := by
          linarith [hZp, abs_nonneg (τ - τ')]
        calc |profFull α g (ρ ^ p / B τ) ϑ τ - profFull α g (ρ ^ p / B τ') ϑ τ'|
            ≤ C * (|ρ ^ p / B τ - ρ ^ p / B τ'| + |τ - τ'|) ^ α := hQh
          _ ≤ C * ((c + 1) * |τ - τ'|) ^ α := by
              refine mul_le_mul_of_nonneg_left ?_ hC0
              exact Real.rpow_le_rpow (by positivity) hT h.hα.le
          _ = C * (c + 1) ^ α * |τ - τ'| ^ α := by
              rw [Real.mul_rpow hc1 (abs_nonneg _)]; ring
      have hinvdiff : |(A τ)⁻¹ - (A τ')⁻¹| ≤ a₂ * |τ - τ'| / a₀ ^ 2 := by
        have h1 : |A τ' - A τ| ≤ a₂ * |τ - τ'| := by
          rw [abs_sub_comm]; exact hAlip τ hτ τ' hτ'
        have hkey : |(A τ)⁻¹ - (A τ')⁻¹| = |A τ' - A τ| / (A τ * A τ') := by
          rw [inv_sub_inv (ne_of_gt hAτ0) (ne_of_gt hAτ'0), abs_div,
            abs_of_pos (mul_pos hAτ0 hAτ'0)]
        rw [hkey]
        have hden : a₀ ^ 2 ≤ A τ * A τ' := by
          have h1' := (hAb τ hτ).1
          have h2' := (hAb τ' hτ').1
          nlinarith [mul_le_mul h1' h2' ha₀.le hAτ0.le]
        calc |A τ' - A τ| / (A τ * A τ') ≤ a₂ * |τ - τ'| / (A τ * A τ') :=
              div_le_div_of_nonneg_right h1 (le_of_lt (mul_pos hAτ0 hAτ'0))
          _ ≤ a₂ * |τ - τ'| / a₀ ^ 2 :=
              div_le_div_of_nonneg_left (mul_nonneg ha₂0 (abs_nonneg _)) (by positivity) hden
      have hdecomp : X - Y = (A τ)⁻¹ * (profFull α g (ρ ^ p / B τ) ϑ τ
            - profFull α g (ρ ^ p / B τ') ϑ τ')
          + ((A τ)⁻¹ - (A τ')⁻¹) * profFull α g (ρ ^ p / B τ') ϑ τ' := by
        rw [hXdef, hYdef]; ring
      have hfirst : |(A τ)⁻¹ * (profFull α g (ρ ^ p / B τ) ϑ τ
            - profFull α g (ρ ^ p / B τ') ϑ τ')|
          ≤ (1 / a₀) * (C * (c + 1) ^ α * |τ - τ'| ^ α) := by
        rw [abs_mul, abs_of_pos (inv_pos.mpr hAτ0)]
        exact mul_le_mul hinvτ hQh' (abs_nonneg _) (by positivity)
      have hsecond : |((A τ)⁻¹ - (A τ')⁻¹) * profFull α g (ρ ^ p / B τ') ϑ τ'|
          ≤ (a₂ * |τ - τ'| / a₀ ^ 2) * M := by
        rw [abs_mul]
        exact mul_le_mul hinvdiff (hQbound τ' hτ') (abs_nonneg _)
          (div_nonneg (mul_nonneg ha₂0 (abs_nonneg _)) (by positivity))
      rcases le_total |τ - τ'| 1 with hsl | hsl
      · have hττ : |τ - τ'| ≤ |τ - τ'| ^ α :=
          self_le_rpow h.hα hα1 (abs_nonneg _) hsl
        have hfin : |X - Y| ≤ ((1 / a₀) * (C * (c + 1) ^ α) + ((1 / a₀) * (20 * p * c)
              + (a₂ / a₀ ^ 2) * M)) * |τ - τ'| ^ α := by
          rw [hdecomp]
          have e1 : |(A τ)⁻¹ * (profFull α g (ρ ^ p / B τ) ϑ τ
                - profFull α g (ρ ^ p / B τ') ϑ τ')
              + ((A τ)⁻¹ - (A τ')⁻¹) * profFull α g (ρ ^ p / B τ') ϑ τ'|
              ≤ (1 / a₀) * (C * (c + 1) ^ α * |τ - τ'| ^ α)
                + (a₂ * |τ - τ'| / a₀ ^ 2) * M :=
            le_trans abs_add_le_aux (add_le_add hfirst hsecond)
          have hAeq : (1 / a₀) * (C * (c + 1) ^ α * |τ - τ'| ^ α)
              = ((1 / a₀) * (C * (c + 1) ^ α)) * |τ - τ'| ^ α := by ring
          have h2 : (a₂ * |τ - τ'| / a₀ ^ 2) * M
              ≤ ((a₂ / a₀ ^ 2) * M) * |τ - τ'| ^ α := by
            rw [show (a₂ * |τ - τ'| / a₀ ^ 2) * M = ((a₂ / a₀ ^ 2) * M) * |τ - τ'| by ring]
            exact mul_le_mul_of_nonneg_left hττ (by positivity)
          have h3 : ((a₂ / a₀ ^ 2) * M) * |τ - τ'| ^ α
              ≤ ((1 / a₀) * (20 * p * c) + (a₂ / a₀ ^ 2) * M) * |τ - τ'| ^ α := by
            rw [add_mul]
            exact le_add_of_nonneg_left (by positivity)
          have hsum : (1 / a₀) * (C * (c + 1) ^ α * |τ - τ'| ^ α)
                + (a₂ * |τ - τ'| / a₀ ^ 2) * M
              ≤ ((1 / a₀) * (C * (c + 1) ^ α) + ((1 / a₀) * (20 * p * c)
                + (a₂ / a₀ ^ 2) * M)) * |τ - τ'| ^ α := by
            rw [hAeq]
            have hexp : ((1 / a₀) * (C * (c + 1) ^ α) + ((1 / a₀) * (20 * p * c)
                + (a₂ / a₀ ^ 2) * M)) * |τ - τ'| ^ α
                = ((1 / a₀) * (C * (c + 1) ^ α)) * |τ - τ'| ^ α
                  + ((1 / a₀) * (20 * p * c) + (a₂ / a₀ ^ 2) * M) * |τ - τ'| ^ α := by ring
            rw [hexp]
            exact add_le_add le_rfl (le_trans h2 h3)
          exact le_trans e1 hsum
        calc |X - Y| ≤ ((1 / a₀) * (C * (c + 1) ^ α) + ((1 / a₀) * (20 * p * c)
              + (a₂ / a₀ ^ 2) * M)) * |τ - τ'| ^ α := hfin
          _ ≤ K * |τ - τ'| ^ α := by
              refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (abs_nonneg _) α)
              rw [hKdef]
              exact le_max_left _ _
      · have hττ : (1:ℝ) ≤ |τ - τ'| ^ α := Real.one_le_rpow hsl h.hα.le
        have h2M : |X - Y| ≤ 2 * M / a₀ := by
          calc |X - Y| ≤ |X| + |Y| := abs_sub_le_aux
            _ ≤ M / a₀ + M / a₀ := add_le_add hbX hbY
            _ = 2 * M / a₀ := by ring
        calc |X - Y| ≤ 2 * M / a₀ := h2M
          _ ≤ K * |τ - τ'| ^ α := by
              have hmax : 2 * M / a₀ ≤ K := by rw [hKdef]; exact le_max_right _ _
              calc 2 * M / a₀ ≤ K := hmax
                _ = K * 1 := by ring
                _ ≤ K * |τ - τ'| ^ α := mul_le_mul_of_nonneg_left hττ hK0
    · have hfar : ρ ^ p > L * b₁ := lt_of_not_ge hcase
      have hZτ : L ≤ ρ ^ p / B τ := by
        rw [le_div_iff₀ (h.hB τ hτ)]
        calc L * B τ ≤ L * b₁ := mul_le_mul_of_nonneg_left (hBb τ hτ).2 hLpos.le
          _ ≤ ρ ^ p := hfar.le
      have hZτ' : L ≤ ρ ^ p / B τ' := by
        rw [le_div_iff₀ (h.hB τ' hτ')]
        calc L * B τ' ≤ L * b₁ := mul_le_mul_of_nonneg_left (hBb τ' hτ').2 hLpos.le
          _ ≤ ρ ^ p := hfar.le
      have h0τ : profFull α g (ρ ^ p / B τ) ϑ τ = 0 := hLsupp τ hτ _ _ hZτ
      have h0τ' : profFull α g (ρ ^ p / B τ') ϑ τ' = 0 := hLsupp τ' hτ' _ _ hZτ'
      have hzero : X - Y = 0 := by rw [hXdef, hYdef, h0τ, h0τ']; ring
      rw [hzero, abs_zero]
      exact mul_nonneg hK0 (Real.rpow_nonneg (abs_nonneg _) α)
  calc ‖physVort α A B g x τ - physVort α A B g x τ'‖
      = ‖(sgn * X - sgn * Y) • Work.Cyl.eTheta x‖ := by rw [hdiff]
    _ = |sgn * X - sgn * Y| * ‖Work.Cyl.eTheta x‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |sgn * X - sgn * Y| * 1 :=
        mul_le_mul_of_nonneg_left (norm_eTheta_le_one x) (abs_nonneg _)
    _ = |X - Y| := by
        rw [mul_one, show sgn * X - sgn * Y = sgn * (X - Y) by ring, abs_mul, hsgn1, one_mul]
    _ ≤ K * |τ - τ'| ^ α := hcore

end Work.FTS.Regularity
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLimitDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS gdot IsDynEqOn IsDynGSolWith)

set_option autoImplicit false

/-! ## The right-hand side of the limiting equation -/

/-- The right-hand side of the limiting equation at the fake time `τ`: the scheme's right-hand
side with the mollifier removed,
`dynLin α g τ + dynRHS α (PsiCan Φs E g) g τ`. -/
def rhsFun (α : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fam) (τ : ℝ) : Fn :=
  fun z θ => dynLin α g τ z θ + dynRHS α (Work.FTS.Nonlin.PsiCan Φs E g) g τ z θ

/-- `rhsFun` depends on the family only through its slice. -/
theorem rhsFun_congr {α : ℝ} {Φs : Fn} {E : Fn → Fn} {g g' : Fam} {τ : ℝ}
    (h : slice g τ = slice g' τ) : rhsFun α Φs E g τ = rhsFun α Φs E g' τ := by
  funext z θ
  simp only [rhsFun, congrFun (congrFun (Work.FTS.StrongGlobal.dynLin_congr h) z) θ,
    congrFun (congrFun (Work.FTS.StrongGlobal.dynRHS_congr h) z) θ]

/-! ## The limit package on `[0,T]` -/

/-- **The limit package on `[0,T]`** — the conclusion of E5, and the input of the assembly
(`E6`).  Every clause is the restriction to `[0,T]` of the corresponding clause of
`Work.FTS.StrongGlobal.RegPkgMin` or of `IsDynGSolWith`, except that the `ℋ⁶`-bound of the slices is
carried along (it is what makes the extraction work and what identifies the limit). -/
structure EpsLimPkg (α C₀ K Cd T : ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn) (g : Fam) : Prop where
  /-- the datum is attained at `τ = 0`. -/
  init : ∀ z θ, g z θ 0 = g₀ z θ
  /-- the positivised elliptic law at every `τ ∈ [0,T]`. -/
  law : ∀ τ, 0 ≤ τ → τ ≤ T →
    Work.FTS.StrongGlobal.IsBslSolPos α (Work.Construction.Ftau α g τ)
      (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ)
  /-- the limiting equation at every `τ ∈ [0,T]`, within `[0,T]`. -/
  eqT : ∀ τ, 0 ≤ τ → τ ≤ T → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    HasDerivWithinAt (fun s => g z θ s) (rhsFun α Φs E g τ z θ) (Set.Icc 0 T) τ
  /-- joint `C¹`-regularity on the interior of the quadrant, for every `τ ∈ (0,T)`.

  **Domain note (E5 assembly, session 18).**  The clause was originally stated for *all*
  `τ > 0` (`Set.Ioi 0` in the last slot).  That is not producible from the extraction: the
  limit curve `F` is an arbitrary `Classical.choose` of an existence statement, hence its values
  for `τ > T` are junk, and the extension of `F` past `T` would need the *spatial* `C¹` of the
  horizon value `rhsFun α Φs E g T` (i.e. elliptic regularity at the limit slice).  The
  horizon-restricted domain is exactly what the only consumer (`Assembly.lean`) uses: there the
  `c1`-clause is read at a point `p` with `0 < p.2.2 < Tn (pidx p.2.2)`, i.e. strictly inside the
  horizon of the covering piece.  Nothing is lost: `RegPkgMin.c1` (unbounded in `τ`) is obtained
  in `Assembly.global_strong2_of_lim` by glueing the per-piece clauses. -/
  c1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
    (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioo 0 T)
  /-- `C⁴` in space at every `τ ∈ [0,T]`. -/
  c4 : ∀ τ, 0 ≤ τ → τ ≤ T →
    ContDiffOn ℝ 4 (Function.uncurry (slice g τ)) Work.FTS.EllipticEst.Q0
  /-- continuity in the fake time up to `τ = 0`, on the open quadrant.

  **Domain note (E5 assembly, session 18).**  As for `c1`, the clause is restricted to the horizon
  `Icc 0 T`: the limit curve `F` is the arbitrary `Classical.choose` of an existence statement, so
  its values for `τ > T` are junk and nothing constrains them (the reviewer of
  `E5G/EpsLimPkg_of_horizon` produced an explicit counterexample).  Every producer
  (`E5Clauses.E5_cont`, via `EpsLimCont`) already concludes the `Icc 0 T`-form, and the only
  consumer (`Assembly.global_strong2_of_lim`) reads the clause at a point `τ ∈ Icc 0 (Tn (pidx τ))`
  and then extends the within-set by `ContinuousWithinAt.mono_of_mem_nhdsWithin`; the glued family's
  global continuity (needed for `RegPkgMin.cont`, which is on `Ici 0`) comes from that stitching. -/
  cont : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    ContinuousOn (fun τ => g z θ τ) (Set.Icc 0 T)
  /-- `ℋ⁴`-membership at every `τ ∈ [0,T]`. -/
  mem4 : ∀ τ, 0 ≤ τ → τ ≤ T → Work.Spaces.HkMem α 4 (slice g τ)
  /-- the uniform `ℋ⁴`-bound. -/
  bd4 : ∀ τ, 0 ≤ τ → τ ≤ T → Work.FTS.Nonlin.Xn α (slice g τ) ≤ C₀ * α ^ 2
  /-- a uniform `ℋ⁶`-bound *carried through from the `ε`-approximants* (for the construction it is
  `K e^{KT}`, the exponential shape of `EpsUniform`).  It is never *re-derived* on the limit slice
  (no `Xn6`/`IP6` energy estimate is applied to a limit); it is the bound of the approximating
  sequence, transferred to the limit by lower semicontinuity.  It is what makes the *uniqueness*
  clause of `EpsUniformMem.exists_lim` work (the `ℋ⁵`-term of the difference estimate is controlled
  by it), and `Assembly.lean` does not read it at all. -/
  bd6 : ∃ B, ∀ τ, 0 ≤ τ → τ ≤ T → Work.FTS.StrongGlobal.Xn6 α (slice g τ) ≤ B
  /-- vanishing on the two angular boundaries, for `z ≥ 0`. -/
  vanish : ∀ τ, 0 ≤ τ → τ ≤ T → ∀ z, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0
  /-- the uniform `ℋ³`-bound on the fake-time derivative, for `0 < τ < T`, with the constant
  `Cd` *shared* by all the pieces (this is what makes the glued family of `Assembly.lean` satisfy
  the `dbd`-clause of `RegPkgMin`).  The bound is stated for `τ < T` and not for `τ ≤ T`: at
  `τ = T` the within-`[0,T]` derivative of `eqT` does not determine the honest derivative
  `gdot g τ = deriv (fun s => g z θ s) τ` (which sees `s > T` as well), so the endpoint instance
  is *not* derivable from the other clauses.  Nothing is lost: `Assembly.lean` reads the clause
  only at fake times `τ < Tn (pidx τ)` (`lt_Tn_pidx`), i.e. strictly inside the covering piece. -/
  dbd : ∀ τ, 0 < τ → τ < T →
    Work.Spaces.HkMem α 3 (gdot g τ) ∧ Work.Spaces.HkNorm α 3 (gdot g τ) ≤ Cd
  /-- **The G2 approximation clause** (`FinalV2.LimApprox`, in the horizon-restricted form of
  `LimApproxSE.LimApproxOn`): on every sub-horizon `[0,T']` the family `g` is the limit of
  class-`C` families with matching `ℋ⁴`-bounds, a uniform `ℋ⁶`-bound, a uniform `ℋ⁴`-Lipschitz
  modulus in `τ`, `C⁴`-jet convergence on `Qd` and convergence of the modulation.  It is glued
  across the covering pieces of `Assembly.lean` exactly like `dbd` — but with *one* piece covering
  the whole of `[0,T]` (see `Assembly.LimApproxOn_glued`). -/
  limApprox : ∀ T', 0 < T' → T' ≤ T → LimApproxOn α C₀ T' Φs E g



/-- The package restricts to shorter intervals: the `C¹`-, `cont`- and `vanish`-clauses are
interval-independent, and the remaining ones restrict by `HasDerivWithinAt.mono` and monotonicity
of the bound. -/
theorem EpsLimPkg.mono {α C₀ K Cd T T' : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn} {g : Fam}
    (hT : T' ≤ T) (h : EpsLimPkg α C₀ K Cd T Φs E g₀ g) (hT0 : 0 ≤ T') :
    EpsLimPkg α C₀ K Cd T' Φs E g₀ g :=
  { init := h.init
    law := fun τ h1 h2 => h.law τ h1 (le_trans h2 hT)
    eqT := fun τ h1 h2 z θ hz =>
      (h.eqT τ h1 (le_trans h2 hT) z θ hz).mono (Set.Icc_subset_Icc le_rfl hT)
    c1 := h.c1.mono (by
      intro q hq
      simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hq ⊢
      exact ⟨hq.1, hq.2.1, hq.2.2.1, lt_of_lt_of_le hq.2.2.2 hT⟩)
    c4 := fun τ h1 h2 => h.c4 τ h1 (le_trans h2 hT)
    cont := fun z θ hz => (h.cont z θ hz).mono (Set.Icc_subset_Icc le_rfl hT)
    mem4 := fun τ h1 h2 => h.mem4 τ h1 (le_trans h2 hT)
    bd4 := fun τ h1 h2 => h.bd4 τ h1 (le_trans h2 hT)
    bd6 := by
      obtain ⟨B, hB⟩ := h.bd6
      exact ⟨B, fun τ h1 h2 => hB τ h1 (le_trans h2 hT)⟩
    vanish := fun τ h1 h2 => h.vanish τ h1 (le_trans h2 hT)
    dbd := fun τ h1 h2 => h.dbd τ h1 (lt_of_lt_of_le h2 hT)
    limApprox := fun T' h1 h2 => h.limApprox T' h1 (le_trans h2 hT) }

/-! ## E5 and the level-three estimate of the limiting right-hand side -/


/-- **`E` passes to limits of bounded class-C sequences** (ruling v2).  Off the class C a linear
`E` is unconstrained (Hamel extension), so `EpsLimPkg.law`/`eqT` at a limit slice — which is not
in class C — need this.  Producer: EllSol (construction A6, "E extends to limits by boundedness"). -/
def EllLimOK (α : ℝ) (E : Fn → Fn) : Prop :=
  ∀ (fn : ℕ → Fn) (f : Fn) (B : ℝ),
    (∀ n, Work.FTS.ClassC.ClassC α (fn n)) →
    (∀ n, Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ B) →
    ContDiffOn ℝ 4 (Function.uncurry f) Work.Construction.Qd →
    (∀ j i : ℕ, j + i ≤ 4 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Tendsto (fun n => Work.Spaces.mixed j i (fn n) z θ) atTop
        (𝓝 (Work.Spaces.mixed j i f z θ))) →
    Work.FTS.StrongGlobal.IsBslSolPos α f (E f) ∧
    ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Tendsto (fun n => Work.Spaces.mixed j i (E (fn n)) z θ) atTop
        (𝓝 (Work.Spaces.mixed j i (E f) z θ))

/-- **The modulation bounds on class-C profiles of small `ℋ⁴`-size** (the `hμ`/`hlam` inputs of
`EpsLimDbd_aux`, at the mollified slices).  Producer: CoercivityFix. -/
def MuLamOK (α C₀ : ℝ) (Φs : Fn) (E : Fn → Fn) : Prop :=
  ∀ f : Fn, Work.FTS.ClassC.ClassC α f → Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 →
    |Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E (fun z θ _ => f z θ))
        (fun z θ _ => f z θ) 0| ≤ 1 / 2 ∧
    |Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E (fun z θ _ => f z θ))
        (fun z θ _ => f z θ) 0| ≤ 1

end Work.FTS.StrongEps
end
end
