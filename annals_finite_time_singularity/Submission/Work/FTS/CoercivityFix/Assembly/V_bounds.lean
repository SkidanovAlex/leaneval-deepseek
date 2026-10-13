/-
# `Assembly/V_bounds.lean` — the three comparison clauses of `IP4`

`IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α` is the paper's recursion
`HkIPStep c₁'' c₂'' (HkIPStep c₁' c₂' (HkIPStep c₁ c₂ (H1IP α)))` (`Assembly/Defs.lean`),
i.e. the `ℋ⁴` inner product with *free* step coefficients.  This file proves the three
comparison clauses of `Work.FTS.Nonlin.UnifIP` that relate it to the honest `ℋ⁴`-norm on the
coercivity class `CoerAdm α`:

* `lo`  : `clo · HkSq α 4 f ≤ IP4 α f f`,
* `up`  : `IP4 α f f ≤ Cup · HkSq α 4 f`,
* `Dz_self` : `|IP4 α (D_z f) f| ≤ Cdz · HkSq α 4 f`,

with constants independent of `α ∈ (0, α₂]`.

## The two comparison chains

`HkIPStep c₁ c₂ IP v v = IP v v + c₁ IP (D_θv) (D_θv) + c₂ IP (D_zv) (D_zv)`, so a lower
(resp. upper) bound for `IP` at level `n` transfers to the level-`n+1` pairing of
`HkIPStep`, the loss being `min 1 (min c₁ c₂)` (resp. `3 max 1 (max c₁ c₂)`), because

* `HkSq α (n+1) v ≤ HkSq α n v + HkSq α n (D_θv) + HkSq α n (D_zv)` (`HkSq_succ_le_Q`), and
* each of the three level-`n` norms of the slots is dominated by `HkSq α (n+1) v`
  (the `normSub` field of `StepReg2_all`).

The bases are `H1IP_le_self_Q` (`lo`) and `H1IP_upper_Q2` below (`up`).

## The `D_z` clause

The three-level recursion `A_n = HkIPStep … (H1IP α)` produces, in the *first* slot,
`IP4 α (D_z f) f = Σ_w c_w H1IP α (w (D_z f)) (w f)`, and the terms of `H1IP` in this
pairing involve one order of differentiation *more* than the level-`4` integrand: e.g. the
word `w = D_θ³` gives the pairing `wip_η (D_z² D_θ³ f) (D_z D_θ³ f)`.  The saving identity is
the paper's `z`-integration by parts in its integrated form
`⟨𝓛 u, u⟩_{w²σ} = ½⟨u,u⟩_{w²σ}` (`Coer1.wip_L_self_Q`), which turns every pairing
`⟨D_z u, u⟩_{w²σ}` into `-½⟨u,u⟩_{w²σ} + 2⟨u/(1+z), u⟩_{w²σ}` and hence gives

  `|⟨D_z u, u⟩_{w²σ}| ≤ 5/2 ⟨u,u⟩_{w²σ}`.

Applying this once per slot (with `u = f, D_z f, D_θ f` and the three weights `ρ_η`, `ρ_γ`,
`w²`) gives the *base* estimate `|H1IP α (D_z v) v| ≤ D₀ HkSq α 1 v` on `RegQ α 2`, and the
same recursion as above then propagates it through the three `HkIPStep`s — one level of the
norm per level of the recursion, which is exactly the balance the class `CoerAdm ⊆ RegQ α 5`
allows.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.CoercivityFix.Assembly.Defs
import Submission.Work.FTS.CoercivityFix.Assembly.Comm2_levels
import Submission.Work.FTS.CoercivityFix.Assembly.H1IP_le_self_Q
import Submission.Work.FTS.CoercivityFix.Assembly.HkSq_succ_le_Q
import Submission.Work.FTS.CoercivityFix.Assembly.Instantiate
import Submission.Work.FTS.CoercivityFix.Coer1.Defs
import Submission.Work.FTS.CoercivityFix.Coer1.IntFacts
import Submission.Work.FTS.CoercivityFix.Coer1.zIBP
import Submission.Work.FTS.CoercivityFix.Coer1.HkSqOne
import Submission.Work.FTS.CoercivityFix.Coer1T.SlotsDzGam
import Submission.Work.FTS.CoercivityFix.QuadPorts.RegQ_dz
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_Dth_le
import Submission.Work.FTS.Vocab

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (RegQ)

set_option autoImplicit false

/-! ## A small helper -/

/-- `RegQ` is monotone in the regularity index. -/
theorem regQ_mono' {α : ℝ} {k k' : ℕ} {f : Fn} (hf : RegQ α k f) (h : k' ≤ k) :
    RegQ α k' f := Work.FTS.GalerkinFix.RegQ.regQ_mono hf h

/-! ## The one-sided norm comparison of the three slots with the next level

This is the `normSub` field of `Assembly.StepReg2` (`Assembly/StepReg2_all.lean`), repeated
here because that module pulls in the elliptic certificates of the a-priori chapter, whose
build is independent of the coercivity layer. -/

/-- `|D_z f|²_{ℋⁿ} ≤ |f|²_{ℋ^{n+1}}` in the interior class `SmoothQuad`: the pointwise
integrand domination is `QuadPorts.HkIntegrand_Dz_le_succ` and the transfer to the iterated
integrals is `integral_mono_of_nonneg`. -/
theorem HkSq_Dz_le_quad (α : ℝ) (n : ℕ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) (h : Work.Spaces.HkMem α (n + 1) f) :
    Work.Spaces.HkSq α n (Work.Spaces.Dz f) ≤ Work.Spaces.HkSq α (n + 1) f := by
  have hmesz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hmesθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α n (Work.Spaces.Dz f) z θ)
    h.2 ?_
  show ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n (Work.Spaces.Dz f) z θ)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (n + 1) f z θ
  exact MeasureTheory.ae_restrict_of_forall_mem hmesz fun z hz =>
    MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ =>
        Work.Spaces.HkIntegrand_nonneg α n (Work.Spaces.Dz f) z θ)
      (h.1 z hz)
      (MeasureTheory.ae_restrict_of_forall_mem hmesθ fun θ hθ =>
        Work.FTS.CoercivityFix.QuadPorts.HkIntegrand_Dz_le_succ α n hsm z θ hz hθ)

/-- **The one-sided comparison of the three level-`n` norms with the level-`(n+1)` norm**,
on the interior class `RegQ α (n+1)`. -/
theorem normSub_Q (α : ℝ) (hα : 0 < α) (n : ℕ) :
    ∀ f : Fn, RegQ α (n + 1) f →
      Work.Spaces.HkSq α n f ≤ Work.Spaces.HkSq α (n + 1) f
        ∧ Work.Spaces.HkSq α n (Work.Spaces.Dth f) ≤ Work.Spaces.HkSq α (n + 1) f
        ∧ Work.Spaces.HkSq α n (Work.Spaces.Dz f) ≤ Work.Spaces.HkSq α (n + 1) f := by
  intro f hf
  obtain ⟨hsm, hmem, -⟩ := hf
  exact ⟨Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.le_succ n) hmem,
    Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα n hmem,
    HkSq_Dz_le_quad α n hsm hmem⟩

/-! ## The lower bound (`lo`) -/

/-- **One step of the lower comparison.**  If the level-`n` pairing dominates
`cst·|v|²_{ℋⁿ}` on `RegQ α (n+1)`, then the level-`n+1` pairing `HkIPStep c₁ c₂ IP` dominates
`(cst·min 1 (min c₁ c₂))·|v|²_{ℋ^{n+1}}` on `RegQ α (n+2)`. -/
theorem lo_step {α : ℝ} (hα : 0 < α) {n : ℕ}
    {IP : Fn → Fn → ℝ} {c₁ c₂ cst : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hcst : 0 < cst)
    (h : ∀ v : Fn, RegQ α (n + 1) v →
      cst * Work.Spaces.HkSq α (n + 1) v ≤ IP v v) :
    ∀ v : Fn, RegQ α (n + 2) v →
      (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 2) v
        ≤ Work.Coercivity.HkIPStep c₁ c₂ IP v v := by
  intro v hv
  have hv1 : RegQ α (n + 1) v :=
    Work.FTS.GalerkinFix.RegQ.regQ_mono hv (by omega : n + 1 ≤ n + 2)
  have hd : RegQ α (n + 1) (Work.Spaces.Dth v) :=
    Work.FTS.CoercivityFix.QuadPorts.RegQ_dth α hα (n := n + 1) hv
  have hz : RegQ α (n + 1) (Work.Spaces.Dz v) :=
    Work.FTS.CoercivityFix.QuadPorts.RegQ_dz α (n := n + 1) hv
  have hsm : Work.FTS.LocData.SmoothQuad v := hv.1
  have hmem : Work.Spaces.HkMem α (n + 2) v := hv.2.1
  have h0 := h v hv1
  have h1 := h (Work.Spaces.Dth v) hd
  have h2 := h (Work.Spaces.Dz v) hz
  have hsucc := HkSq_succ_le_Q α hα (n + 1) (by omega) hsm hmem
  have hA0 := Work.Spaces.HkSq_nonneg α (n + 1) v
  have hA1 := Work.Spaces.HkSq_nonneg α (n + 1) (Work.Spaces.Dth v)
  have hA2 := Work.Spaces.HkSq_nonneg α (n + 1) (Work.Spaces.Dz v)
  have hm1 : min 1 (min c₁ c₂) ≤ 1 := min_le_left _ _
  have hm2 : min 1 (min c₁ c₂) ≤ c₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hm3 : min 1 (min c₁ c₂) ≤ c₂ := le_trans (min_le_right _ _) (min_le_right _ _)
  have hcm : 0 ≤ cst * min 1 (min c₁ c₂) :=
    (mul_pos hcst (lt_min one_pos (lt_min hc₁ hc₂))).le
  have e0 : (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 1) v ≤ IP v v := by
    calc (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 1) v
        ≤ (cst * 1) * Work.Spaces.HkSq α (n + 1) v :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm1 hcst.le) hA0
      _ = cst * Work.Spaces.HkSq α (n + 1) v := by ring
      _ ≤ IP v v := h0
  have e1 : (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dth v)
      ≤ c₁ * IP (Work.Spaces.Dth v) (Work.Spaces.Dth v) := by
    calc (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dth v)
        ≤ (cst * c₁) * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dth v) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm2 hcst.le) hA1
      _ = c₁ * (cst * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dth v)) := by ring
      _ ≤ c₁ * IP (Work.Spaces.Dth v) (Work.Spaces.Dth v) :=
          mul_le_mul_of_nonneg_left h1 hc₁.le
  have e2 : (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dz v)
      ≤ c₂ * IP (Work.Spaces.Dz v) (Work.Spaces.Dz v) := by
    calc (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dz v)
        ≤ (cst * c₂) * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dz v) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm3 hcst.le) hA2
      _ = c₂ * (cst * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dz v)) := by ring
      _ ≤ c₂ * IP (Work.Spaces.Dz v) (Work.Spaces.Dz v) :=
          mul_le_mul_of_nonneg_left h2 hc₂.le
  have hsum : (cst * min 1 (min c₁ c₂))
        * (Work.Spaces.HkSq α (n + 1) v + Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dth v)
          + Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dz v))
      = (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 1) v
        + (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dth v)
        + (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dz v) := by
    ring
  rw [Work.Coercivity.HkIPStep]
  have hmain : (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 2) v
      ≤ IP v v + c₁ * IP (Work.Spaces.Dth v) (Work.Spaces.Dth v)
        + c₂ * IP (Work.Spaces.Dz v) (Work.Spaces.Dz v) := by
    refine le_trans (mul_le_mul_of_nonneg_left hsucc hcm) ?_
    rw [hsum]; linarith [e0, e1, e2]
  exact hmain

/-! ## The upper bound (`up`) -/

/-- **The level-`1` upper comparison in the interior class.**  `H1IP α v v` is dominated by
`10²²·|v|²_{ℋ¹}` on `RegQ α 2`, with a constant independent of `α` (the only input beyond the
definitions is `Ef ≤ EfEta`, i.e. `sin(2θ)^{-η} ≥ 1`). -/
theorem H1IP_upper_Q2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → ∀ v : Fn, RegQ α 2 v →
      Work.Coercivity.H1IP α v v ≤ C * Work.Spaces.HkSq α 1 v := by
  refine ⟨(10 : ℝ) ^ 22, by norm_num, ?_⟩
  intro α hα v hv
  have hsm : Work.FTS.LocData.SmoothQuad v := hv.1
  have hmem : Work.Spaces.HkMem α 2 v := hv.2.1
  have hmem1 : Work.Spaces.HkMem α 1 v :=
    Work.GalerkinFix.RegQ.HkMem_mono_Q hsm hmem
  have hshape : Work.Spaces.HkSq α 1 v
      = Work.Coercivity.EDz v + Work.Coercivity.EfEta v + Work.Coercivity.EDth α v :=
    Work.FTS.CoercivityFix.Coer1.HkSq_one_eq α hsm hmem1
  have hEf : Work.Coercivity.Ef v ≤ Work.Coercivity.EfEta v :=
    Work.FTS.CoercivityFix.Coer1T.Ef_le_EfEta_Q α hα hsm hmem
  have hH : Work.Coercivity.H1IP α v v
      = 10 * Work.Coercivity.EDz v + (10 : ℝ) ^ 10 * Work.Coercivity.EfEta v
        + (10 : ℝ) ^ 17 * Work.Coercivity.Ef v + (10 : ℝ) ^ 21 * Work.Coercivity.EDth α v := by
    rw [Work.Coercivity.H1IP, Work.Coercivity.EDz_eq_wip, Work.Coercivity.EfEta_eq_wip,
      ← Work.Coercivity.Ef_eq_wip v, Work.Coercivity.EDth_eq_wip]
  have hsin : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := fun θ hθ =>
    Work.FTS.CoercivityFix.Coer1.sin_nonneg_of_mem_Iθ hθ
  have hnn : ∀ z θ, θ ∈ Work.Spaces.Iθ →
      0 ≤ (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) z θ :=
    fun z θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin θ hθ) _)
  have hnng : ∀ z θ, θ ∈ Work.Spaces.Iθ →
      0 ≤ (fun z θ => Work.Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) z θ :=
    fun z θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin θ hθ) _)
  have hA : 0 ≤ Work.Coercivity.EDz v := by
    rw [Work.Coercivity.EDz_eq_wip]; exact Work.Coercivity.wip_self_nonneg hnn
  have hB : 0 ≤ Work.Coercivity.EfEta v := by
    rw [Work.Coercivity.EfEta_eq_wip]; exact Work.Coercivity.wip_self_nonneg hnn
  have hC : 0 ≤ Work.Coercivity.EDth α v := by
    rw [Work.Coercivity.EDth_eq_wip]; exact Work.Coercivity.wip_self_nonneg hnng
  have hEfnn : 0 ≤ Work.Coercivity.Ef v := by
    rw [Work.Coercivity.Ef_eq_wip]
    exact Work.Coercivity.wip_self_nonneg (fun z _ _ => sq_nonneg _)
  rw [hH, hshape]
  nlinarith [hEf, hA, hB, hC, hEfnn]

/-- **One step of the upper comparison.**  If the level-`n` pairing is dominated by
`Cst·|v|²_{ℋⁿ}` on `RegQ α (n+1)`, then `HkIPStep c₁ c₂ IP` is dominated by
`(3·Cst·max 1 (max c₁ c₂))·|v|²_{ℋ^{n+1}}` on `RegQ α (n+2)`. -/
theorem up_step {α : ℝ} (hα : 0 < α) {n : ℕ}
    {IP : Fn → Fn → ℝ} {c₁ c₂ Cst : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hCst : 0 < Cst)
    (h : ∀ v : Fn, RegQ α (n + 1) v → IP v v ≤ Cst * Work.Spaces.HkSq α n v) :
    ∀ v : Fn, RegQ α (n + 2) v →
      Work.Coercivity.HkIPStep c₁ c₂ IP v v
        ≤ (3 * Cst * max 1 (max c₁ c₂)) * Work.Spaces.HkSq α (n + 1) v := by
  intro v hv
  have hv1 : RegQ α (n + 1) v :=
    Work.FTS.GalerkinFix.RegQ.regQ_mono hv (by omega : n + 1 ≤ n + 2)
  have hd : RegQ α (n + 1) (Work.Spaces.Dth v) :=
    Work.FTS.CoercivityFix.QuadPorts.RegQ_dth α hα (n := n + 1) hv
  have hz : RegQ α (n + 1) (Work.Spaces.Dz v) :=
    Work.FTS.CoercivityFix.QuadPorts.RegQ_dz α (n := n + 1) hv
  have h0 := h v hv1
  have h1 := h (Work.Spaces.Dth v) hd
  have h2 := h (Work.Spaces.Dz v) hz
  obtain ⟨hn0, hn1, hn2⟩ := normSub_Q α hα n v hv1
  have hB0 : 0 ≤ Work.Spaces.HkSq α n v := Work.Spaces.HkSq_nonneg α n v
  have hB1 : 0 ≤ Work.Spaces.HkSq α n (Work.Spaces.Dth v) := Work.Spaces.HkSq_nonneg α n _
  have hB2 : 0 ≤ Work.Spaces.HkSq α n (Work.Spaces.Dz v) := Work.Spaces.HkSq_nonneg α n _
  have hT : 0 ≤ Work.Spaces.HkSq α (n + 1) v := Work.Spaces.HkSq_nonneg α (n + 1) v
  have e0 : IP v v ≤ Cst * Work.Spaces.HkSq α (n + 1) v :=
    le_trans h0 (mul_le_mul_of_nonneg_left hn0 hCst.le)
  have e1 : IP (Work.Spaces.Dth v) (Work.Spaces.Dth v)
      ≤ Cst * Work.Spaces.HkSq α (n + 1) v :=
    le_trans h1 (mul_le_mul_of_nonneg_left hn1 hCst.le)
  have e2 : IP (Work.Spaces.Dz v) (Work.Spaces.Dz v)
      ≤ Cst * Work.Spaces.HkSq α (n + 1) v :=
    le_trans h2 (mul_le_mul_of_nonneg_left hn2 hCst.le)
  have hm1 : (1 : ℝ) ≤ max 1 (max c₁ c₂) := le_max_left _ _
  have hm2 : c₁ ≤ max 1 (max c₁ c₂) := le_trans (le_max_left _ _) (le_max_right _ _)
  have hm3 : c₂ ≤ max 1 (max c₁ c₂) := le_trans (le_max_right _ _) (le_max_right _ _)
  rw [Work.Coercivity.HkIPStep]
  have hcomb : IP v v + c₁ * IP (Work.Spaces.Dth v) (Work.Spaces.Dth v)
      + c₂ * IP (Work.Spaces.Dz v) (Work.Spaces.Dz v)
      ≤ (Cst * (1 + c₁ + c₂)) * Work.Spaces.HkSq α (n + 1) v := by
    have hc1 : c₁ * IP (Work.Spaces.Dth v) (Work.Spaces.Dth v)
        ≤ c₁ * (Cst * Work.Spaces.HkSq α (n + 1) v) :=
      mul_le_mul_of_nonneg_left e1 hc₁.le
    have hc2 : c₂ * IP (Work.Spaces.Dz v) (Work.Spaces.Dz v)
        ≤ c₂ * (Cst * Work.Spaces.HkSq α (n + 1) v) :=
      mul_le_mul_of_nonneg_left e2 hc₂.le
    nlinarith [e0, hc1, hc2, hT, hCst, hc₁, hc₂]
  refine le_trans hcomb ?_
  have hcoef : Cst * (1 + c₁ + c₂) ≤ 3 * Cst * max 1 (max c₁ c₂) := by
    nlinarith [hCst, hm1, hm2, hm3]
  exact mul_le_mul_of_nonneg_right hcoef hT

/-! ## The `D_z`-clause: auxiliary estimates

The two tools below turn the paper's `z`-integration by parts (in its integrated form
`Coer1.wip_L_self_Q`) into a bound for the pairing `⟨D_z u, u⟩` of a slot with itself. -/

/-- The triangle inequality for four real numbers. -/
theorem abs_lin4 (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le (a + b + c) d
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le a b
  linarith

/-- `wip` only depends on its weight through the pointwise values. -/
theorem wip_weight_congr {ρ ρ' A B : Fn} (h : ∀ z θ, ρ z θ = ρ' z θ) :
    Work.Coercivity.wip ρ A B = Work.Coercivity.wip ρ' A B := by
  rw [Work.Coercivity.wip, Work.Coercivity.wip]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  rw [h z θ]

/-- `|c₁ a + c₂ b + c₃ c + c₄ d| ≤ c₁|a| + c₂|b| + c₃|c| + c₄|d|` for positive
coefficients. -/
theorem abs_lin4_coef (c₁ c₂ c₃ c₄ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hc₄ : 0 < c₄) (a b c d : ℝ) :
    |c₁ * a + c₂ * b + c₃ * c + c₄ * d|
      ≤ c₁ * |a| + c₂ * |b| + c₃ * |c| + c₄ * |d| := by
  have h := abs_lin4 (c₁ * a) (c₂ * b) (c₃ * c) (c₄ * d)
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos hc₁, abs_of_pos hc₂, abs_of_pos hc₃,
    abs_of_pos hc₄] at h
  exact h

/-- The triangle inequality with positive coefficients, three terms. -/
theorem abs_lin3_coef (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (a b c : ℝ) :
    |a + c₁ * b + c₂ * c| ≤ |a| + c₁ * |b| + c₂ * |c| := by
  have h1 := abs_add_le (a + c₁ * b) (c₂ * c)
  have h2 := abs_add_le a (c₁ * b)
  have e1 : |c₁ * b| = c₁ * |b| := by rw [abs_mul, abs_of_pos hc₁]
  have e2 : |c₂ * c| = c₂ * |c| := by rw [abs_mul, abs_of_pos hc₂]
  rw [e1] at h2
  rw [e2] at h1
  linarith

/-- The `Rho`-weight written with the explicit angular power. -/
theorem wip_Rho_eq (β : ℝ) (A B : Fn) :
    Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-β)) A B
      = Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho β) A B := by
  refine wip_weight_congr (fun z θ => ?_)
  simp only [Work.FTS.CoercivityFix.Coer1.Rho, Work.FTS.CoercivityFix.Coer1.sig]

/-- `wip` is a congruence in both pairing arguments. -/
theorem wip_congr_pt {ρ : Fn} {A A' B B' : Fn} (hA : ∀ z θ, A z θ = A' z θ)
    (hB : ∀ z θ, B z θ = B' z θ) : Work.Coercivity.wip ρ A B = Work.Coercivity.wip ρ A' B' := by
  rw [Work.Coercivity.wip, Work.Coercivity.wip]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  rw [hA z θ, hB z θ]

/-- `D_θ` and `D_z` commute on the closed quadrant for a `SmoothQuad` function: in the
interior this is Clairaut's theorem, and on the boundary (`z = 0` or `sin 2θ = 0`) both
sides vanish identically. -/
theorem Dth_Dz_comm_mem {v : Fn} (hsq : Work.FTS.LocData.SmoothQuad v) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.Dth (Work.Spaces.Dz v) z θ = Work.Spaces.Dz (Work.Spaces.Dth v) z θ := by
  intro z hz θ hθ
  by_cases hz0 : z = 0
  · subst hz0
    have hpth : Work.Spaces.pth (Work.Spaces.Dz v) 0 θ = 0 := by
      have hfun : (fun θ' => Work.Spaces.Dz v 0 θ') = fun _ => (0 : ℝ) := by
        funext θ'; simp only [Work.Spaces.Dz, zero_mul]
      simp only [Work.Spaces.pth, hfun, deriv_const]
    simp only [Work.Spaces.Dth, hpth, mul_zero, Work.Spaces.Dz, zero_mul]
  · by_cases hsin : Real.sin (2 * θ) = 0
    · have hfun : (fun z' => Work.Spaces.Dth v z' θ) = fun _ => (0 : ℝ) := by
        funext z'; simp only [Work.Spaces.Dth, hsin, zero_mul]
      simp only [Work.Spaces.Dth, hsin, zero_mul, Work.Spaces.Dz, Work.Spaces.pz,
        hfun, deriv_const, mul_zero]
    · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
      have hsinpos : 0 < Real.sin (2 * θ) :=
        lt_of_le_of_ne (Work.FTS.CoercivityFix.Coer1.sin_nonneg_of_mem_Iθ hθ)
          (Ne.symm hsin)
      have hθ' : θ ∈ Set.Ioo 0 (π / 2) :=
        Work.FTS.CoercivityFix.Coer1.mem_Ioo_of_mem_Iθ_of_sin_pos hθ hsinpos
      have hcd := Work.FTS.CoercivityFix.Coer1.contDiffAt_smoothQuad_two hsq hzpos hθ'
      exact (Work.Spaces.Dz_Dth_comm hcd).symm

/-- `⟨u/(1+z), u⟩_{w²σ} ≤ ⟨u,u⟩_{w²σ}` for a nonnegative weight: the factor `1/(1+z) ≤ 1`
on `z ≥ 0`. -/
theorem wip_div_one_add_self_le {ρ u : Fn} (hρ : ∀ z θ, θ ∈ Work.Spaces.Iθ → 0 ≤ ρ z θ)
    (h : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => u z θ ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hd : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      u z θ ^ 2 * ρ z θ / (1 + z))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.Coercivity.wip ρ (fun z θ => u z θ / (1 + z)) u ≤ Work.Coercivity.wip ρ u u := by
  have hIsum : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      u z θ / (1 + z) * u z θ * ρ z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q hd (fun z θ => by ring)
  have hIu : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      u z θ * u z θ * ρ z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q h (fun z θ => by ring)
  have e1 : Work.Coercivity.wip ρ (fun z θ => u z θ / (1 + z)) u
      = ∫ p : ℝ × ℝ, u p.1 p.2 ^ 2 * ρ p.1 p.2 / (1 + p.1)
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.Coercivity.wip_eq_integral_prod ρ (fun z θ => u z θ / (1 + z)) u hIsum]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    ring
  have e2 : Work.Coercivity.wip ρ u u
      = ∫ p : ℝ × ℝ, u p.1 p.2 ^ 2 * ρ p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.Coercivity.wip_eq_integral_prod ρ u u hIu]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    ring
  rw [e1, e2]
  have hI1 : MeasureTheory.Integrable (fun p : ℝ × ℝ => u p.1 p.2 ^ 2 * ρ p.1 p.2 / (1 + p.1))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict]
    exact hd
  have hI2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => u p.1 p.2 ^ 2 * ρ p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict]
    exact h
  refine MeasureTheory.integral_mono_ae hI1 hI2 ?_
  filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_prod_fst_pos,
    Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem_Ioo] with p hp1 hp2
  have hρnn : 0 ≤ ρ p.1 p.2 := hρ p.1 p.2 ⟨le_of_lt hp2.1, le_of_lt hp2.2⟩
  have hz : 0 < 1 + p.1 := by linarith [hp1]
  have hle : 1 / (1 + p.1) ≤ 1 := by
    rw [div_le_one hz]; linarith
  have hsq : 0 ≤ u p.1 p.2 ^ 2 * ρ p.1 p.2 := mul_nonneg (sq_nonneg _) hρnn
  calc u p.1 p.2 ^ 2 * ρ p.1 p.2 / (1 + p.1)
      = (u p.1 p.2 ^ 2 * ρ p.1 p.2) * (1 / (1 + p.1)) := by ring
    _ ≤ (u p.1 p.2 ^ 2 * ρ p.1 p.2) * 1 := mul_le_mul_of_nonneg_left hle hsq
    _ = u p.1 p.2 ^ 2 * ρ p.1 p.2 := mul_one _

/-- **The pairing of a slot with itself is controlled by `En`.**  For `u` with the `z`-IBP
hypotheses (`ZIBP`), the honesty of `u²w²σ` and of `𝓛u·u·w²σ`, and `σ ≥ 0` on `Iθ`,

  `|⟨D_z u, u⟩_{w²σ}| ≤ (5/2)⟨u, u⟩_{w²σ}`.

Indeed `⟨𝓛u, u⟩_{w²σ} = ½⟨u,u⟩_{w²σ}` and `𝓛u = u + D_z u - 2u/(1+z)`, so
`⟨D_z u, u⟩_{w²σ} = 2⟨u/(1+z), u⟩_{w²σ} - ½⟨u,u⟩_{w²σ}` with
`0 ≤ ⟨u/(1+z), u⟩_{w²σ} ≤ ⟨u,u⟩_{w²σ}`. -/
theorem wip_Dz_self_le {u : Fn} (hu : Work.FTS.CoercivityFix.Coer1.ZIBP u)
    {σ : ℝ → ℝ} (hσ : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ σ θ)
    (h2 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      u z θ ^ 2 * Work.Spaces.w z ^ 2 * σ θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hL : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.L u z θ * u z θ * Work.Spaces.w z ^ 2 * σ θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    |Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) (Work.Spaces.Dz u) u|
      ≤ (5 / 2) * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u := by
  have h2' : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      u z θ * u z θ * (Work.Spaces.w z ^ 2 * σ θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q h2 (fun z θ => by ring)
  have hL' : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.L u z θ * u z θ * (Work.Spaces.w z ^ 2 * σ θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q hL (fun z θ => by ring)
  have h3 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      u z θ * u z θ * (Work.Spaces.w z ^ 2 * σ θ) / (1 + z)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_div_one_add_Q h2'
  have hLu : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Coercivity.L u z θ - u z θ) * u z θ * (Work.Spaces.w z ^ 2 * σ θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine (hL'.sub h2').congr (Filter.Eventually.of_forall fun p => ?_)
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Pi.sub_apply]
    ring
  have h2u : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (2 * (u z θ / (1 + z))) * u z θ * (Work.Spaces.w z ^ 2 * σ θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine (h3.const_mul 2).congr (Filter.Eventually.of_forall fun p => ?_)
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair]
    ring
  have hself := Work.FTS.CoercivityFix.Coer1.wip_L_self_Q u hu σ h2 hL
  have e0 : Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
        (Work.Spaces.Dz u) u
      = Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
          (fun z θ => (Work.Coercivity.L u z θ - u z θ) + 2 * (u z θ / (1 + z))) u := by
    refine wip_congr_pt (fun z θ => ?_) (fun z θ => rfl)
    simp only [Work.Coercivity.L, Work.Spaces.Dz]
    ring
  have e1 : Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
        (fun z θ => (Work.Coercivity.L u z θ - u z θ) + 2 * (u z θ / (1 + z))) u
      = Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
          (fun z θ => Work.Coercivity.L u z θ - u z θ) u
        + Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
          (fun z θ => 2 * (u z θ / (1 + z))) u :=
    Work.Coercivity.wip_add_left hLu h2u
  have e2 : Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
        (fun z θ => Work.Coercivity.L u z θ - u z θ) u
      = Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) (Work.Coercivity.L u) u
        - Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u :=
    Work.FTS.CoercivityFix.Coer1.wip_sub_left hL' h2'
  have e3 : Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
        (fun z θ => 2 * (u z θ / (1 + z))) u
      = 2 * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
          (fun z θ => u z θ / (1 + z)) u :=
    Work.Coercivity.wip_smul_left
  have hkey : Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
        (Work.Spaces.Dz u) u
      = 2 * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
            (fun z θ => u z θ / (1 + z)) u
        - (1 / 2) * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u := by
    rw [e0, e1, e2, e3, hself]
    ring
  have hρnn : ∀ z θ, θ ∈ Work.Spaces.Iθ → 0 ≤ (fun z θ => Work.Spaces.w z ^ 2 * σ θ) z θ :=
    fun z θ hθ => mul_nonneg (sq_nonneg _) (hσ θ hθ)
  have hA : 0 ≤ Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u :=
    Work.Coercivity.wip_self_nonneg hρnn
  have hT3nn : 0 ≤ Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
      (fun z θ => u z θ / (1 + z)) u := by
    rw [Work.Coercivity.wip]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ici (fun z hz => ?_)
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    have hρ : 0 ≤ Work.Spaces.w z ^ 2 * σ θ := mul_nonneg (sq_nonneg _) (hσ θ hθ)
    have hz0 : (0 : ℝ) ≤ z := hz
    have h1z : 0 < 1 + z := by linarith
    have : u z θ / (1 + z) * u z θ = u z θ ^ 2 / (1 + z) := by ring
    rw [this]
    exact mul_nonneg (div_nonneg (sq_nonneg _) h1z.le) hρ
  have hT3le : Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
        (fun z θ => u z θ / (1 + z)) u
      ≤ Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u :=
    wip_div_one_add_self_le hρnn
      (Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q h2 (fun z θ => by ring))
      (Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q h3 (fun z θ => by ring))
  rw [hkey]
  have habs : |2 * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
        (fun z θ => u z θ / (1 + z)) u
      - (1 / 2) * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u|
      ≤ 2 * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
          (fun z θ => u z θ / (1 + z)) u
        + (1 / 2) * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u := by
    have h := abs_sub (2 * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
          (fun z θ => u z θ / (1 + z)) u)
        ((1 / 2) * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u)
    have h1 : |2 * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
          (fun z θ => u z θ / (1 + z)) u|
        = 2 * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
            (fun z θ => u z θ / (1 + z)) u :=
      abs_of_nonneg (by linarith [hT3nn])
    have h2 : |(1 / 2) * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u|
        = (1 / 2) * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u :=
      abs_of_nonneg (by linarith [hA])
    rw [h1, h2] at h
    exact h
  linarith [habs, hA, hT3le]

/-- `wip` is a congruence in its first argument, almost everywhere. -/
theorem wip_congr_ae' {ρ g₁ g₁' g₂ : Fn}
    (h : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), g₁ z θ = g₁' z θ) :
    Work.Coercivity.wip ρ g₁ g₂ = Work.Coercivity.wip ρ g₁' g₂ := by
  rw [Work.Coercivity.wip, Work.Coercivity.wip]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [h] with z hz
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hz] with θ hθ
  rw [hθ]

/-- **The base estimate of the `D_z` clause.**  On `RegQ α 2` the pairing of the first slot
of `H1IP` with `D_z v` against `v` is dominated by the *level-`1`* norm of `v` — the
`z`-integration by parts `wip_Dz_self_le` converts each of the four pairings into a square of
a level-`1` slot. -/
theorem H1IP_Dz_le_one (α : ℝ) (hα : 0 < α) {v : Fn} (hv : RegQ α 2 v) :
    |Work.Coercivity.H1IP α (Work.Spaces.Dz v) v| ≤ (10 : ℝ) ^ 22 * Work.Spaces.HkSq α 1 v := by
  have hp := Work.FTS.CoercivityFix.Coer1.IntPkg_Q α hα hv
  have hsq : Work.FTS.LocData.SmoothQuad v := hv.1
  have hmem1 : Work.Spaces.HkMem α 1 v :=
    Work.GalerkinFix.RegQ.HkMem_mono_Q hv.1 hv.2.1
  have hηnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ :=
    fun θ hθ => Real.rpow_nonneg (Work.FTS.CoercivityFix.Coer1.sin_nonneg_of_mem_Iθ hθ) _
  have hγnn : ∀ θ ∈ Work.Spaces.Iθ,
      0 ≤ Work.FTS.CoercivityFix.Coer1.sig (Work.Spaces.gam α) θ :=
    fun θ hθ => Real.rpow_nonneg (Work.FTS.CoercivityFix.Coer1.sin_nonneg_of_mem_Iθ hθ) _
  have hcomm : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.Dth (Work.Spaces.Dz v) z θ = Work.Spaces.Dz (Work.Spaces.Dth v) z θ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact Dth_Dz_comm_mem hsq z hz θ hθ
  -- the four pairings, in the `Rho`-normalisation
  have b1 := wip_Dz_self_le hp.zibp_Dz hηnn
      (Work.FTS.CoercivityFix.Coer1.to_h1 (β := Work.Spaces.eta)
        (hp.sqDzEta 1 (by norm_num)))
      (Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q hp.intL_Dz_eta
        (fun z θ => by simp only [Work.FTS.CoercivityFix.Coer1.Rho]; ring))
  have b2 := wip_Dz_self_le hp.zibp_f hηnn
      (Work.FTS.CoercivityFix.Coer1.to_h1 (β := Work.Spaces.eta)
        (hp.sqDzEta 0 (by norm_num)))
      (Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q hp.intL_f_eta
        (fun z θ => by simp only [Work.FTS.CoercivityFix.Coer1.Rho]; ring))
  have hb3 := wip_Dz_self_le hp.zibp_f (σ := fun _ => (1 : ℝ)) (fun θ _ => zero_le_one)
      (Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q (hp.sqDzOne 0 (by norm_num))
        (fun z θ => by simp only [Work.Spaces.DzIter_zero]; ring))
      (Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q hp.intL_f_one (fun z θ => by ring))
  have b3 : |Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) (Work.Spaces.Dz v) v|
      ≤ (5 / 2) * Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) v v := by
    rw [← wip_weight_congr (ρ := fun z θ => Work.Spaces.w z ^ 2 * (fun _ => (1 : ℝ)) θ)
          (ρ' := fun z _ => Work.Spaces.w z ^ 2) (A := Work.Spaces.Dz v) (B := v)
          (fun z θ => by simp),
      ← wip_weight_congr (ρ := fun z θ => Work.Spaces.w z ^ 2 * (fun _ => (1 : ℝ)) θ)
          (ρ' := fun z _ => Work.Spaces.w z ^ 2) (A := v) (B := v) (fun z θ => by simp)]
    exact hb3
  have hb4 := wip_Dz_self_le hp.zibp_Dth hγnn
      (Work.FTS.CoercivityFix.Coer1.to_h1 (β := Work.Spaces.gam α)
        (hp.sqMixedGam 1 0 (by norm_num) (by norm_num)))
      (Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q hp.intL_Dth_gam
        (fun z θ => by simp only [Work.FTS.CoercivityFix.Coer1.Rho]; ring))
  have b4 : |Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α))
        (Work.Spaces.Dth (Work.Spaces.Dz v)) (Work.Spaces.Dth v)|
      ≤ (5 / 2) * Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α))
          (Work.Spaces.Dth v) (Work.Spaces.Dth v) := by
    have hEq : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α))
          (Work.Spaces.Dth (Work.Spaces.Dz v)) (Work.Spaces.Dth v)
        = Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α))
          (Work.Spaces.Dz (Work.Spaces.Dth v)) (Work.Spaces.Dth v) :=
      wip_congr_ae' (ρ := Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α))
        (g₁ := Work.Spaces.Dth (Work.Spaces.Dz v))
        (g₁' := Work.Spaces.Dz (Work.Spaces.Dth v)) (g₂ := Work.Spaces.Dth v) hcomm
    rw [hEq]
    exact hb4
  -- the four bounds in the weights and `En`-normalisation of `H1IP`
  have h1 : |Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        (Work.Spaces.Dz (Work.Spaces.Dz v)) (Work.Spaces.Dz v)|
      ≤ (5 / 2) * Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta (Work.Spaces.Dz v) := by
    rw [wip_Rho_eq Work.Spaces.eta (Work.Spaces.Dz (Work.Spaces.Dz v)) (Work.Spaces.Dz v),
      ← Work.FTS.CoercivityFix.Coer1.wip_Rho_self Work.Spaces.eta (Work.Spaces.Dz v)]
    exact b1
  have h2 : |Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        (Work.Spaces.Dz v) v|
      ≤ (5 / 2) * Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta v := by
    rw [wip_Rho_eq Work.Spaces.eta (Work.Spaces.Dz v) v,
      ← Work.FTS.CoercivityFix.Coer1.wip_Rho_self Work.Spaces.eta v]
    exact b2
  have h3 : |Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) (Work.Spaces.Dz v) v|
      ≤ (5 / 2) * Work.FTS.CoercivityFix.Coer1.EnOne v := by
    rw [← Work.FTS.CoercivityFix.Coer1.wip_one_self v]
    exact b3
  have h4 : |Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        (Work.Spaces.Dth (Work.Spaces.Dz v)) (Work.Spaces.Dth v)|
      ≤ (5 / 2) * Work.FTS.CoercivityFix.Coer1.En (Work.Spaces.gam α) (Work.Spaces.Dth v) := by
    rw [wip_Rho_eq (Work.Spaces.gam α) (Work.Spaces.Dth (Work.Spaces.Dz v)) (Work.Spaces.Dth v),
      ← Work.FTS.CoercivityFix.Coer1.wip_Rho_self (Work.Spaces.gam α) (Work.Spaces.Dth v)]
    exact b4
  -- the `ℋ¹`-norm in terms of the three `En`-energies
  have hshape : Work.Spaces.HkSq α 1 v
      = Work.Coercivity.EDz v + Work.Coercivity.EfEta v + Work.Coercivity.EDth α v :=
    Work.FTS.CoercivityFix.Coer1.HkSq_one_eq α hsq hmem1
  have hnorm : Work.Spaces.HkSq α 1 v
      = Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta (Work.Spaces.Dz v)
        + Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta v
        + Work.FTS.CoercivityFix.Coer1.En (Work.Spaces.gam α) (Work.Spaces.Dth v) := by
    rw [hshape, Work.FTS.CoercivityFix.Coer1.EDz_eq_En v,
      Work.FTS.CoercivityFix.Coer1.EfEta_eq_En v, Work.FTS.CoercivityFix.Coer1.EDth_eq_En α v]
  have hE3le : Work.FTS.CoercivityFix.Coer1.EnOne v
      ≤ Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta v :=
    Work.FTS.CoercivityFix.Coer1T.EnOne_le_En_eta (u := v)
      (Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q (hp.sqDzOne 0 (by norm_num))
        (fun z θ => by simp only [Work.Spaces.DzIter_zero]))
      (Work.FTS.CoercivityFix.Coer1.to_h1 (β := Work.Spaces.eta) (hp.sqDzEta 0 (by norm_num)))
  have hAnn1 : 0 ≤ Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta (Work.Spaces.Dz v) :=
    Work.FTS.CoercivityFix.Coer1.En_nonneg _ _
  have hAnn2 : 0 ≤ Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta v :=
    Work.FTS.CoercivityFix.Coer1.En_nonneg _ _
  have hAnn3 : 0 ≤ Work.FTS.CoercivityFix.Coer1.EnOne v :=
    Work.FTS.CoercivityFix.Coer1.EnOne_nonneg _
  have hAnn4 : 0 ≤ Work.FTS.CoercivityFix.Coer1.En (Work.Spaces.gam α)
      (Work.Spaces.Dth v) := Work.FTS.CoercivityFix.Coer1.En_nonneg _ _
  rw [Work.Coercivity.H1IP, hnorm]
  refine le_trans (abs_lin4_coef ((10 : ℝ)) ((10 : ℝ) ^ 10) ((10 : ℝ) ^ 17) ((10 : ℝ) ^ 21)
    (by norm_num) (by positivity) (by positivity) (by positivity) _ _ _ _) ?_
  nlinarith [h1, h2, h3, h4, hE3le, hAnn1, hAnn2, hAnn3, hAnn4]

/-- **One step of the `D_z`-clause recursion.**  If the *first slot* pairing
`⟨IP (D_z v), v⟩` is bounded by `D·|v|²_{ℋ^{n+1}}` on `RegQ α (n+2)`, then the corresponding
pairing of `HkIPStep c₁ c₂ IP` is bounded by `3·D·max 1 (max c₁ c₂)` times the level-`(n+2)`
norm on `RegQ α (n+3)`.

The only structural input is the commutation `D_θ(D_z v) = D_z(D_θ v)` on the open quadrant,
used through the a.e. congruence `hcongr` of `IP`. -/
theorem dz_step {α : ℝ} (hα : 0 < α) {n : ℕ}
    {IP : Fn → Fn → ℝ} {c₁ c₂ D : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hD : 0 < D)
    (hcongr : ∀ f f' g : Fn,
      (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) → IP f g = IP f' g)
    (h : ∀ v : Fn, RegQ α (n + 2) v →
      |IP (Work.Spaces.Dz v) v| ≤ D * Work.Spaces.HkSq α (n + 1) v) :
    ∀ v : Fn, RegQ α (n + 3) v →
      |Work.Coercivity.HkIPStep c₁ c₂ IP (Work.Spaces.Dz v) v|
        ≤ (3 * D * max 1 (max c₁ c₂)) * Work.Spaces.HkSq α (n + 2) v := by
  intro v hv
  have hv2 : RegQ α (n + 2) v := regQ_mono' hv (by omega)
  have hdth : RegQ α (n + 2) (Work.Spaces.Dth v) :=
    Work.FTS.CoercivityFix.QuadPorts.RegQ_dth α hα (n := n + 2) hv
  have hdz : RegQ α (n + 2) (Work.Spaces.Dz v) :=
    Work.FTS.CoercivityFix.QuadPorts.RegQ_dz α (n := n + 2) hv
  have h0 := h v hv2
  have h1 := h (Work.Spaces.Dth v) hdth
  have h2 := h (Work.Spaces.Dz v) hdz
  -- the commutation, transported to the congruence class of `IP`
  have hcomm : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dth (Work.Spaces.Dz v) z θ = Work.Spaces.Dz (Work.Spaces.Dth v) z θ := by
    intro z θ hzθ
    have hU : (z, θ) ∈ Work.Spaces.quadU := by
      simp only [Work.Construction.Qd, Work.Spaces.quadU, Set.mem_prod, Set.mem_Ioi,
        Set.mem_Ioo] at hzθ ⊢
      exact ⟨by linarith [hzθ.1], hzθ.2.1, hzθ.2.2⟩
    have hq := Work.FTS.CoercivityFix.QuadPorts.DzIter_DthIter_comm_quad hv.1 1 1 hU
    simpa only [Function.uncurry_apply_pair, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
      Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero] using hq.symm
  have hcg := hcongr (Work.Spaces.Dth (Work.Spaces.Dz v))
    (Work.Spaces.Dz (Work.Spaces.Dth v)) (Work.Spaces.Dth v) hcomm
  obtain ⟨hs0, hs1, hs2⟩ := normSub_Q α hα (n + 1) v hv2
  have hB : 0 ≤ Work.Spaces.HkSq α (n + 2) v := Work.Spaces.HkSq_nonneg α (n + 2) v
  have e0 : |IP (Work.Spaces.Dz v) v| ≤ D * Work.Spaces.HkSq α (n + 2) v :=
    le_trans h0 (mul_le_mul_of_nonneg_left hs0 hD.le)
  have e1 : |IP (Work.Spaces.Dz (Work.Spaces.Dth v)) (Work.Spaces.Dth v)|
      ≤ D * Work.Spaces.HkSq α (n + 2) v :=
    le_trans h1 (mul_le_mul_of_nonneg_left hs1 hD.le)
  have e2 : |IP (Work.Spaces.Dz (Work.Spaces.Dz v)) (Work.Spaces.Dz v)|
      ≤ D * Work.Spaces.HkSq α (n + 2) v :=
    le_trans h2 (mul_le_mul_of_nonneg_left hs2 hD.le)
  rw [Work.Coercivity.HkIPStep, hcg]
  have htri : |IP (Work.Spaces.Dz v) v
        + c₁ * IP (Work.Spaces.Dz (Work.Spaces.Dth v)) (Work.Spaces.Dth v)
        + c₂ * IP (Work.Spaces.Dz (Work.Spaces.Dz v)) (Work.Spaces.Dz v)|
      ≤ |IP (Work.Spaces.Dz v) v|
        + c₁ * |IP (Work.Spaces.Dz (Work.Spaces.Dth v)) (Work.Spaces.Dth v)|
        + c₂ * |IP (Work.Spaces.Dz (Work.Spaces.Dz v)) (Work.Spaces.Dz v)| :=
    abs_lin3_coef c₁ c₂ hc₁ hc₂ _ _ _
  refine le_trans htri ?_
  have hm1 : (1 : ℝ) ≤ max 1 (max c₁ c₂) := le_max_left _ _
  have hm2 : c₁ ≤ max 1 (max c₁ c₂) := le_trans (le_max_left _ _) (le_max_right _ _)
  have hm3 : c₂ ≤ max 1 (max c₁ c₂) := le_trans (le_max_right _ _) (le_max_right _ _)
  have hcomb : |IP (Work.Spaces.Dz v) v|
        + c₁ * |IP (Work.Spaces.Dz (Work.Spaces.Dth v)) (Work.Spaces.Dth v)|
        + c₂ * |IP (Work.Spaces.Dz (Work.Spaces.Dz v)) (Work.Spaces.Dz v)|
      ≤ (3 * D * max 1 (max c₁ c₂)) * Work.Spaces.HkSq α (n + 2) v := by
    have hc1 : c₁ * |IP (Work.Spaces.Dz (Work.Spaces.Dth v)) (Work.Spaces.Dth v)|
        ≤ c₁ * (D * Work.Spaces.HkSq α (n + 2) v) := mul_le_mul_of_nonneg_left e1 hc₁.le
    have hc2 : c₂ * |IP (Work.Spaces.Dz (Work.Spaces.Dz v)) (Work.Spaces.Dz v)|
        ≤ c₂ * (D * Work.Spaces.HkSq α (n + 2) v) := mul_le_mul_of_nonneg_left e2 hc₂.le
    have hsum : |IP (Work.Spaces.Dz v) v|
        + c₁ * |IP (Work.Spaces.Dz (Work.Spaces.Dth v)) (Work.Spaces.Dth v)|
        + c₂ * |IP (Work.Spaces.Dz (Work.Spaces.Dz v)) (Work.Spaces.Dz v)|
        ≤ D * Work.Spaces.HkSq α (n + 2) v
          + c₁ * (D * Work.Spaces.HkSq α (n + 2) v)
          + c₂ * (D * Work.Spaces.HkSq α (n + 2) v) := by
      linarith [e0, hc1, hc2]
    refine le_trans hsum ?_
    have hcoef : 1 + c₁ + c₂ ≤ 3 * max 1 (max c₁ c₂) := by linarith [hm1, hm2, hm3]
    have hDH : 0 ≤ D * Work.Spaces.HkSq α (n + 2) v := mul_nonneg hD.le hB
    calc D * Work.Spaces.HkSq α (n + 2) v
          + c₁ * (D * Work.Spaces.HkSq α (n + 2) v)
          + c₂ * (D * Work.Spaces.HkSq α (n + 2) v)
        = (1 + c₁ + c₂) * (D * Work.Spaces.HkSq α (n + 2) v) := by ring
      _ ≤ (3 * max 1 (max c₁ c₂)) * (D * Work.Spaces.HkSq α (n + 2) v) :=
          mul_le_mul_of_nonneg_right hcoef hDH
      _ = (3 * D * max 1 (max c₁ c₂)) * Work.Spaces.HkSq α (n + 2) v := by ring
  exact hcomb

/-- **The lower comparison for `IP4`.** -/
theorem lo_four {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ}
    (h₁ : 0 < c₁) (h₂ : 0 < c₂) (h₁' : 0 < c₁') (h₂' : 0 < c₂')
    (h₁'' : 0 < c₁'') (h₂'' : 0 < c₂'') :
    ∃ clo : ℝ, 0 < clo ∧ ∀ (α : ℝ), 0 < α → ∀ f : Fn, RegQ α 4 f →
      clo * Work.Spaces.HkSq α 4 f
        ≤ IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f f := by
  refine ⟨((1 * min 1 (min c₁ c₂)) * min 1 (min c₁' c₂')) * min 1 (min c₁'' c₂''),
    mul_pos (mul_pos (mul_pos one_pos (lt_min one_pos (lt_min h₁ h₂)))
      (lt_min one_pos (lt_min h₁' h₂'))) (lt_min one_pos (lt_min h₁'' h₂'')), ?_⟩
  intro α hα f hf
  have l2 : ∀ v : Fn, RegQ α 2 v →
      (1 * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α 2 v ≤ IP2 c₁ c₂ α v v :=
    lo_step (IP := Work.Coercivity.H1IP α) (n := 0) hα h₁ h₂ one_pos
      (fun v hv => by simpa using H1IP_le_self_Q α hv)
  have l3 : ∀ v : Fn, RegQ α 3 v →
      ((1 * min 1 (min c₁ c₂)) * min 1 (min c₁' c₂')) * Work.Spaces.HkSq α 3 v
        ≤ IP3 c₁ c₂ c₁' c₂' α v v :=
    lo_step (IP := IP2 c₁ c₂ α) (n := 1) hα h₁' h₂'
      (mul_pos one_pos (lt_min one_pos (lt_min h₁ h₂))) l2
  have l4 : ∀ v : Fn, RegQ α 4 v →
      (((1 * min 1 (min c₁ c₂)) * min 1 (min c₁' c₂')) * min 1 (min c₁'' c₂''))
          * Work.Spaces.HkSq α 4 v
        ≤ IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α v v :=
    lo_step (IP := IP3 c₁ c₂ c₁' c₂' α) (n := 2) hα h₁'' h₂''
      (mul_pos (mul_pos one_pos (lt_min one_pos (lt_min h₁ h₂)))
        (lt_min one_pos (lt_min h₁' h₂'))) l3
  exact l4 f hf

/-- **The upper comparison for `IP4`.** -/
theorem up_four {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ}
    (h₁ : 0 < c₁) (h₂ : 0 < c₂) (h₁' : 0 < c₁') (h₂' : 0 < c₂')
    (h₁'' : 0 < c₁'') (h₂'' : 0 < c₂'') :
    ∃ Cup : ℝ, 0 < Cup ∧ ∀ (α : ℝ), 0 < α → ∀ f : Fn, RegQ α 5 f →
      IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f f ≤ Cup * Work.Spaces.HkSq α 4 f := by
  obtain ⟨C₁, hC₁, hC₁b⟩ := H1IP_upper_Q2
  set D₁ : ℝ := 3 * C₁ * max 1 (max c₁ c₂) with hD₁
  set D₂ : ℝ := 3 * D₁ * max 1 (max c₁' c₂') with hD₂
  set D₃ : ℝ := 3 * D₂ * max 1 (max c₁'' c₂'') with hD₃
  have hm₁ : (1 : ℝ) ≤ max 1 (max c₁ c₂) := le_max_left _ _
  have hm₂ : (1 : ℝ) ≤ max 1 (max c₁' c₂') := le_max_left _ _
  have hm₃ : (1 : ℝ) ≤ max 1 (max c₁'' c₂'') := le_max_left _ _
  have hD₁pos : 0 < D₁ := by rw [hD₁]; nlinarith [hC₁, hm₁]
  have hD₂pos : 0 < D₂ := by rw [hD₂]; nlinarith [hD₁pos, hm₂]
  have hD₃pos : 0 < D₃ := by rw [hD₃]; nlinarith [hD₂pos, hm₃]
  refine ⟨D₃, hD₃pos, ?_⟩
  intro α hα f hf
  have u2 := up_step (IP := Work.Coercivity.H1IP α) (n := 1) hα h₁ h₂ hC₁
    (fun v hv => hC₁b α hα v hv)
  have u3 := up_step (IP := IP2 c₁ c₂ α) (n := 2) hα h₁' h₂' hD₁pos
    (by intro v hv; rw [hD₁]; exact u2 v hv)
  have u4 := up_step (IP := IP3 c₁ c₂ c₁' c₂' α) (n := 3) hα h₁'' h₂'' hD₂pos
    (by intro v hv; rw [hD₂]; exact u3 v hv)
  exact u4 f hf

/-- **The `D_z` comparison for `IP4`.** -/
theorem dz_four {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ}
    (h₁ : 0 < c₁) (h₂ : 0 < c₂) (h₁' : 0 < c₁') (h₂' : 0 < c₂')
    (h₁'' : 0 < c₁'') (h₂'' : 0 < c₂'') :
    ∃ Cdz : ℝ, 0 < Cdz ∧ ∀ (α : ℝ), 0 < α → ∀ f : Fn, RegQ α 5 f →
      |IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (Work.Spaces.Dz f) f|
        ≤ Cdz * Work.Spaces.HkSq α 4 f := by
  set E₁ : ℝ := 3 * (10 : ℝ) ^ 22 * max 1 (max c₁ c₂) with hE₁
  set E₂ : ℝ := 3 * E₁ * max 1 (max c₁' c₂') with hE₂
  set E₃ : ℝ := 3 * E₂ * max 1 (max c₁'' c₂'') with hE₃
  have hm₁ : (1 : ℝ) ≤ max 1 (max c₁ c₂) := le_max_left _ _
  have hm₂ : (1 : ℝ) ≤ max 1 (max c₁' c₂') := le_max_left _ _
  have hm₃ : (1 : ℝ) ≤ max 1 (max c₁'' c₂'') := le_max_left _ _
  have hE₁pos : 0 < E₁ := by rw [hE₁]; nlinarith [hm₁]
  have hE₂pos : 0 < E₂ := by rw [hE₂]; nlinarith [hE₁pos, hm₂]
  have hE₃pos : 0 < E₃ := by rw [hE₃]; nlinarith [hE₂pos, hm₃]
  refine ⟨E₃, hE₃pos, ?_⟩
  intro α hα f hf
  have hc2 := Comm2_levels α hα (c₁ := c₁) (c₂ := c₂) (c₁' := c₁') (c₂' := c₂')
    (c₁'' := c₁'') (c₂'' := c₂'')
  have v1 := dz_step (IP := Work.Coercivity.H1IP α) (n := 0) hα h₁ h₂
    (by norm_num : (0 : ℝ) < 10 ^ 22) (Comm2_L1 α hα).congr
    (fun v hv => H1IP_Dz_le_one α hα hv)
  have v2 := dz_step (IP := IP2 c₁ c₂ α) (n := 1) hα h₁' h₂' hE₁pos hc2.1.congr
    (by intro v hv; rw [hE₁]; exact v1 v hv)
  have v3 := dz_step (IP := IP3 c₁ c₂ c₁' c₂' α) (n := 2) hα h₁'' h₂'' hE₂pos
    hc2.2.1.congr (by intro v hv; rw [hE₂]; exact v2 v hv)
  exact v3 f hf

theorem V_bounds {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ}
    (h₁ : 0 < c₁) (h₂ : 0 < c₂) (h₁' : 0 < c₁') (h₂' : 0 < c₂')
    (h₁'' : 0 < c₁'') (h₂'' : 0 < c₂'') :
    ∃ α₂ clo Cup Cdz : ℝ, 0 < α₂ ∧ 0 < clo ∧ 0 < Cup ∧ 0 < Cdz ∧
      (∀ (α : ℝ), α ∈ Set.Ioc 0 α₂ → ∀ (f : ℝ → ℝ → ℝ), Work.FTS.Nonlin.CoerAdm α f →
        clo * Work.Spaces.HkSq α 4 f
          ≤ Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f f) ∧
      (∀ (α : ℝ), α ∈ Set.Ioc 0 α₂ → ∀ (f : ℝ → ℝ → ℝ), Work.FTS.Nonlin.CoerAdm α f →
        Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f f
          ≤ Cup * Work.Spaces.HkSq α 4 f) ∧
      (∀ (α : ℝ), α ∈ Set.Ioc 0 α₂ → ∀ (f : ℝ → ℝ → ℝ), Work.FTS.Nonlin.CoerAdm α f →
        |Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
            (Work.Spaces.Dz f) f| ≤ Cdz * Work.Spaces.HkSq α 4 f) := by
  obtain ⟨clo, hclo, hlo⟩ := lo_four h₁ h₂ h₁' h₂' h₁'' h₂''
  obtain ⟨Cup, hCup, hup⟩ := up_four h₁ h₂ h₁' h₂' h₁'' h₂''
  obtain ⟨Cdz, hCdz, hdz⟩ := dz_four h₁ h₂ h₁' h₂' h₁'' h₂''
  refine ⟨1, clo, Cup, Cdz, one_pos, hclo, hCup, hCdz, ?_, ?_, ?_⟩
  · intro α hα f hf
    exact hlo α hα.1 f (regQ_mono' hf.reg (by norm_num : 4 ≤ 5))
  · intro α hα f hf
    exact hup α hα.1 f hf.reg
  · intro α hα f hf
    exact hdz α hα.1 f hf.reg

end Work.FTS.CoercivityFix.Assembly
