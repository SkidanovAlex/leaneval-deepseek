import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.mixed_Jeps_kernel_partial
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## 1. The routed kernel derivatives and the density -/

/-- `∂₁^a ∂₂^b ρ`: the routed derivative of the kernel `ρ` itself (the `∂₁`-iterations outside,
as in `Work.FTS.StrongEps.Kd`). -/
abbrev Kdr (ρ : ℝ × ℝ → ℝ) (a b : ℕ) : ℝ × ℝ → ℝ := Work.FTS.StrongEps.Kd ρ a b

/-- `∂₁^a ∂₂^b (Jker ρ ε)`: the kernel that appears in the fully routed slot identity. -/
abbrev KdK (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (a b : ℕ) : ℝ × ℝ → ℝ :=
  Work.FTS.StrongEps.Kd (Work.FTS.StrongEps.Jker ρ ε) a b

/-- `Σ_{a,b ≤ M} |∂₁^a ∂₂^b ρ|`: the level-`M` kernel-side datum. -/
def sigKd (ρ : ℝ × ℝ → ℝ) (M : ℕ) : ℝ × ℝ → ℝ :=
  fun q => ∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (M + 1), |Kdr ρ a b q|

/-- The raw routed density: `Λ_raw = Jker (Σ_{a,b ≤ M} |∂₁^a ∂₂^b ρ|) ε`. -/
def LamK (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (M : ℕ) : ℝ × ℝ → ℝ :=
  Work.FTS.StrongEps.Jker (sigKd ρ M) ε

/-- The routed density, with the weight-shift factor `ε⁻¹^M · e^{4cε}` absorbed into the kernel
itself, so that `LamFull` is again a rescaled kernel `Jker Λsig ε` (this is what makes the
measurability, support and moment facts about it available from the generic `Jker` lemmas). -/
def LamFull (ρ : ℝ × ℝ → ℝ) (ε c : ℝ) (M : ℕ) : ℝ × ℝ → ℝ :=
  Work.FTS.StrongEps.Jker (fun q => ε⁻¹ ^ M * Real.exp (4 * c * ε) * sigKd ρ M q) ε

/-- The kernel-side datum of `LamFull`. -/
theorem LamFull_eq (ρ : ℝ × ℝ → ℝ) (ε c : ℝ) (M : ℕ) (p : ℝ × ℝ) :
    LamFull ρ ε c M p = ε⁻¹ ^ M * Real.exp (4 * c * ε) * LamK ρ ε M p := by
  simp only [LamFull, LamK, Work.FTS.StrongEps.Jker]
  ring

/-- The mass of all routed density kernels of order `≤ M`. -/
def Ksm (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (M : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (M + 1),
    ∫ p : ℝ × ℝ, |KdK ρ ε a b p|

/-- The mass constant of the gain: the mass of all routed kernels, times `2^{2M}` (the factor
paid by the `θ`-routing, which multiplies a `θ`-derivative by `2`; the routing of `i` of them
costs `2^{2i} ≤ 2^{2M}` after Cauchy–Schwarz). -/
def KgainBig (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (M : ℕ) : ℝ := Ksm ρ ε M * 2 ^ (2 * M)

/-- The constant of the pointwise gain estimate, after summing the `(M+1) + (M+1)²` slots of
`HkIntegrand α M`. -/
def Cgain (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (M : ℕ) : ℝ :=
  (((M + 1) + (M + 1) ^ 2 : ℕ) : ℝ) * KgainBig ρ ε M

/-! ## 2. The scaling identity for the partial derivatives of `Jker ρ ε` -/

/-- Pulling a constant out of `∂₁`. -/
theorem partFst_const_mul (c : ℝ) (F : ℝ × ℝ → ℝ) :
    Work.FTS.StrongEps.partFst (fun p => c * F p)
      = fun p => c * Work.FTS.StrongEps.partFst F p := by
  funext p
  change deriv (fun s : ℝ => c * F (s, p.2)) p.1
    = c * deriv (fun s : ℝ => F (s, p.2)) p.1
  rw [deriv_const_mul_field']

/-- Pulling a constant out of `∂₂`. -/
theorem partSnd_const_mul (c : ℝ) (F : ℝ × ℝ → ℝ) :
    Work.FTS.StrongEps.partSnd (fun p => c * F p)
      = fun p => c * Work.FTS.StrongEps.partSnd F p := by
  funext p
  change deriv (fun t : ℝ => c * F (p.1, t)) p.2
    = c * deriv (fun t : ℝ => F (p.1, t)) p.2
  rw [deriv_const_mul_field']

/-- The `∂₁`-scaling identity: differentiating the rescaled kernel in the first variable is
rescaling the kernel of the first partial derivative, at the price of one factor `ε⁻¹`. -/
theorem partFst_Jker (σ : ℝ × ℝ → ℝ) (hσ : ContDiff ℝ 1 σ) (ε : ℝ) (p : ℝ × ℝ) :
    Work.FTS.StrongEps.partFst (Work.FTS.StrongEps.Jker σ ε) p
      = ε⁻¹ * Work.FTS.StrongEps.Jker (Work.FTS.StrongEps.partFst σ) ε p := by
  have hsm : ContDiff ℝ 1 (fun u : ℝ => σ (u, ε⁻¹ * p.2)) :=
    hσ.comp (contDiff_id.prodMk (contDiff_const (c := ε⁻¹ * p.2)))
  have houter : HasDerivAt (fun u : ℝ => σ (u, ε⁻¹ * p.2))
      (deriv (fun u : ℝ => σ (u, ε⁻¹ * p.2)) (ε⁻¹ * p.1)) (ε⁻¹ * p.1) :=
    hsm.differentiable_one.differentiableAt.hasDerivAt
  have hinner : HasDerivAt (fun s : ℝ => ε⁻¹ * s) ε⁻¹ p.1 := by
    simpa using (hasDerivAt_id p.1).const_mul ε⁻¹
  have hcomp : HasDerivAt (fun s : ℝ => σ (ε⁻¹ * s, ε⁻¹ * p.2))
      (deriv (fun u : ℝ => σ (u, ε⁻¹ * p.2)) (ε⁻¹ * p.1) * ε⁻¹) p.1 := by
    simpa [Function.comp_def] using houter.comp p.1 hinner
  have hJ : ∀ s : ℝ, Work.FTS.StrongEps.Jker σ ε (s, p.2)
      = ε⁻¹ ^ 2 * σ (ε⁻¹ * s, ε⁻¹ * p.2) := by
    intro s
    simp only [Work.FTS.StrongEps.Jker, Prod.smul_mk, Prod.smul_fst, smul_eq_mul]
  have hder := (hcomp.const_mul (ε⁻¹ ^ 2)).deriv
  simp only [Work.FTS.StrongEps.partFst]
  rw [show (fun s : ℝ => Work.FTS.StrongEps.Jker σ ε (s, p.2))
      = fun s : ℝ => ε⁻¹ ^ 2 * σ (ε⁻¹ * s, ε⁻¹ * p.2) from funext hJ]
  rw [hder]
  simp only [Work.FTS.StrongEps.Jker, Work.FTS.StrongEps.partFst, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  ring

/-- The `∂₂`-scaling identity. -/
theorem partSnd_Jker (σ : ℝ × ℝ → ℝ) (hσ : ContDiff ℝ 1 σ) (ε : ℝ) (p : ℝ × ℝ) :
    Work.FTS.StrongEps.partSnd (Work.FTS.StrongEps.Jker σ ε) p
      = ε⁻¹ * Work.FTS.StrongEps.Jker (Work.FTS.StrongEps.partSnd σ) ε p := by
  have hsm : ContDiff ℝ 1 (fun u : ℝ => σ (ε⁻¹ * p.1, u)) :=
    hσ.comp ((contDiff_const (c := ε⁻¹ * p.1)).prodMk contDiff_id)
  have houter : HasDerivAt (fun u : ℝ => σ (ε⁻¹ * p.1, u))
      (deriv (fun u : ℝ => σ (ε⁻¹ * p.1, u)) (ε⁻¹ * p.2)) (ε⁻¹ * p.2) :=
    hsm.differentiable_one.differentiableAt.hasDerivAt
  have hinner : HasDerivAt (fun t : ℝ => ε⁻¹ * t) ε⁻¹ p.2 := by
    simpa using (hasDerivAt_id p.2).const_mul ε⁻¹
  have hcomp : HasDerivAt (fun t : ℝ => σ (ε⁻¹ * p.1, ε⁻¹ * t))
      (deriv (fun u : ℝ => σ (ε⁻¹ * p.1, u)) (ε⁻¹ * p.2) * ε⁻¹) p.2 := by
    simpa [Function.comp_def] using houter.comp p.2 hinner
  have hJ : ∀ t : ℝ, Work.FTS.StrongEps.Jker σ ε (p.1, t)
      = ε⁻¹ ^ 2 * σ (ε⁻¹ * p.1, ε⁻¹ * t) := by
    intro t
    simp only [Work.FTS.StrongEps.Jker, Prod.smul_mk, Prod.smul_snd, smul_eq_mul]
  have hder := (hcomp.const_mul (ε⁻¹ ^ 2)).deriv
  simp only [Work.FTS.StrongEps.partSnd]
  rw [show (fun t : ℝ => Work.FTS.StrongEps.Jker σ ε (p.1, t))
      = fun t : ℝ => ε⁻¹ ^ 2 * σ (ε⁻¹ * p.1, ε⁻¹ * t) from funext hJ]
  rw [hder]
  simp only [Work.FTS.StrongEps.Jker, Work.FTS.StrongEps.partSnd, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  ring

/-- **The routed scaling identity, as a function equality** (stated with the raw `Kd` so that
the induction can rewrite syntactically). -/
theorem Kd_Jker_scale_fn {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) (ε : ℝ) (a b : ℕ) :
    Work.FTS.StrongEps.Kd (Work.FTS.StrongEps.Jker ρ ε) a b
      = fun p => ε⁻¹ ^ (a + b) * Work.FTS.StrongEps.Jker (Work.FTS.StrongEps.Kd ρ a b) ε p := by
  have hb : ∀ b : ℕ, Work.FTS.StrongEps.Kd (Work.FTS.StrongEps.Jker ρ ε) 0 b
      = fun q => ε⁻¹ ^ b * Work.FTS.StrongEps.Jker (Work.FTS.StrongEps.Kd ρ 0 b) ε q := by
    intro b
    induction b with
    | zero =>
      funext q
      simp only [Work.FTS.StrongEps.Kd_zero_eq, Function.iterate_zero_apply, pow_zero, one_mul]
    | succ b ih =>
      have hsm : ContDiff ℝ 1 (Work.FTS.StrongEps.Kd ρ 0 b) :=
        Work.FTS.StrongEps.Kd_smooth ρ hρ.smooth 0 b 1
      rw [Work.FTS.StrongEps.Kd_zero_succ, ih, partSnd_const_mul]
      funext q
      rw [partSnd_Jker (Work.FTS.StrongEps.Kd ρ 0 b) hsm ε q]
      rw [Work.FTS.StrongEps.Kd_zero_succ, pow_succ]
      ring
  induction a with
  | zero => simpa only [Nat.zero_add] using hb b
  | succ a ih =>
    have hsm : ContDiff ℝ 1 (Work.FTS.StrongEps.Kd ρ a b) :=
      Work.FTS.StrongEps.Kd_smooth ρ hρ.smooth a b 1
    simp only [Work.FTS.StrongEps.Kd_succ_eq]
    rw [ih, partFst_const_mul]
    funext q
    rw [partFst_Jker (Work.FTS.StrongEps.Kd ρ a b) hsm ε q]
    rw [show (a + 1) + b = (a + b) + 1 from by ring, pow_succ]
    ring

/-- **The routed scaling identity**: `∂₁^a ∂₂^b (Jker ρ ε) = ε⁻¹^{a+b} · Jker (∂₁^a ∂₂^b ρ) ε`. -/
theorem Kd_Jker_scale {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) (ε : ℝ) (a b : ℕ) (p : ℝ × ℝ) :
    KdK ρ ε a b p = ε⁻¹ ^ (a + b) * Work.FTS.StrongEps.Jker (Kdr ρ a b) ε p :=
  congrFun (Kd_Jker_scale_fn hρ ε a b) p

/-! ## 3. Support of the partial derivatives of `ρ` -/

/-- A point at which `∂₁F` does not vanish lies in the topological support of `F`. -/
theorem mem_tsupport_of_partFst_ne_zero {F : ℝ × ℝ → ℝ} {q : ℝ × ℝ}
    (hq : Work.FTS.StrongEps.partFst F q ≠ 0) : q ∈ tsupport F := by
  by_contra hcon
  refine hq ?_
  simp only [Work.FTS.StrongEps.partFst]
  have h0 : F =ᶠ[nhds q] 0 := notMem_tsupport_iff_eventuallyEq.mp hcon
  have hcont : ContinuousAt (fun s : ℝ => (s, q.2)) q.1 :=
    continuousAt_id.prodMk continuousAt_const
  have hg : (fun s : ℝ => F (s, q.2)) =ᶠ[nhds q.1] (fun _ => 0) :=
    hcont.tendsto.eventually h0
  rw [hg.deriv_eq, deriv_const]

/-- A point at which `∂₂F` does not vanish lies in the topological support of `F`. -/
theorem mem_tsupport_of_partSnd_ne_zero {F : ℝ × ℝ → ℝ} {q : ℝ × ℝ}
    (hq : Work.FTS.StrongEps.partSnd F q ≠ 0) : q ∈ tsupport F := by
  by_contra hcon
  refine hq ?_
  simp only [Work.FTS.StrongEps.partSnd]
  have h0 : F =ᶠ[nhds q] 0 := notMem_tsupport_iff_eventuallyEq.mp hcon
  have hcont : ContinuousAt (fun t : ℝ => (q.1, t)) q.2 :=
    continuousAt_const.prodMk continuousAt_id
  have hg : (fun t : ℝ => F (q.1, t)) =ᶠ[nhds q.2] (fun _ => 0) :=
    hcont.tendsto.eventually h0
  rw [hg.deriv_eq, deriv_const]


/-- Every `∂₂`-iterate of an admissible kernel vanishes outside the closed unit ball. -/
theorem Kdr_zero_support {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) (b : ℕ) :
    ∀ q : ℝ × ℝ, Kdr ρ 0 b q ≠ 0 → q.1 ^ 2 + q.2 ^ 2 ≤ 1 := by
  induction b with
  | zero =>
    intro q hq
    exact hρ.moll.support q (by simpa only [Kdr, Work.FTS.StrongEps.Kd_zero_eq,
      Function.iterate_zero_apply] using hq)
  | succ b ih =>
    intro q hq
    have hq' : Work.FTS.StrongEps.partSnd (Kdr ρ 0 b) q ≠ 0 := by
      simpa only [Kdr, Work.FTS.StrongEps.Kd_zero_succ] using hq
    have hmem : q ∈ tsupport (Kdr ρ 0 b) := mem_tsupport_of_partSnd_ne_zero hq'
    have hsub : tsupport (Kdr ρ 0 b) ⊆ {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ 1} :=
      closure_minimal (fun r hr => ih r (by simpa only [Function.mem_support] using hr))
        (isClosed_le (by continuity) continuous_const)
    exact hsub hmem

/-- Every partial derivative of an admissible kernel vanishes outside the closed unit ball. -/
theorem Kdr_support {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) (a b : ℕ) :
    ∀ q : ℝ × ℝ, Kdr ρ a b q ≠ 0 → q.1 ^ 2 + q.2 ^ 2 ≤ 1 := by
  induction a with
  | zero => exact Kdr_zero_support hρ b
  | succ a ih =>
    intro q hq
    have hq' : Work.FTS.StrongEps.partFst (Kdr ρ a b) q ≠ 0 := by
      simpa only [Kdr, Work.FTS.StrongEps.Kd_succ_eq] using hq
    have hmem : q ∈ tsupport (Kdr ρ a b) := mem_tsupport_of_partFst_ne_zero hq'
    have hsub : tsupport (Kdr ρ a b) ⊆ {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ 1} :=
      closure_minimal (fun r hr => ih r (by simpa only [Function.mem_support] using hr))
        (isClosed_le (by continuity) continuous_const)
    exact hsub hmem

theorem sigKd_nonneg (ρ : ℝ × ℝ → ℝ) (M : ℕ) (q : ℝ × ℝ) : 0 ≤ sigKd ρ M q :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem sigKd_support {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) (M : ℕ) {q : ℝ × ℝ}
    (hq : sigKd ρ M q ≠ 0) : q.1 ^ 2 + q.2 ^ 2 ≤ 1 := by
  by_contra hcon
  have hlt : 1 < q.1 ^ 2 + q.2 ^ 2 := not_le.mp hcon
  refine hq ?_
  simp only [sigKd]
  refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
  rw [abs_eq_zero]
  by_contra hne
  exact absurd (Kdr_support hρ a b q hne) (not_le.mpr hlt)

theorem sigKd_continuous {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) (M : ℕ) :
    Continuous (sigKd ρ M) := by
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
  exact ((Work.FTS.StrongEps.Kd_smooth ρ hρ.smooth a b 0).continuous).abs

/-- Points where `Λ_raw` does not vanish lie in the closed ball of radius `ε`. -/
theorem LamK_support {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) (M : ℕ) {ε : ℝ} {p : ℝ × ℝ}
    (hp : LamK ρ ε M p ≠ 0) : p.1 ^ 2 + p.2 ^ 2 ≤ ε ^ 2 := by
  by_cases hε0 : ε = 0
  · subst hε0
    have h0 : LamK ρ 0 M p = 0 := by
      simp only [LamK, Work.FTS.StrongEps.Jker, inv_zero, zero_smul]
      ring
    exact absurd h0 hp
  · have hsig : sigKd ρ M (ε⁻¹ • p) ≠ 0 := by
      intro h
      refine hp ?_
      simp only [LamK, Work.FTS.StrongEps.Jker, h, mul_zero]
    have h1 := sigKd_support hρ M hsig
    rw [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, smul_eq_mul] at h1
    have hε2 : 0 < ε ^ 2 := sq_pos_of_ne_zero hε0
    have hkey : ε⁻¹ ^ 2 * (p.1 ^ 2 + p.2 ^ 2) ≤ 1 := by
      have hw : (ε⁻¹ * p.1) ^ 2 + (ε⁻¹ * p.2) ^ 2
          = ε⁻¹ ^ 2 * (p.1 ^ 2 + p.2 ^ 2) := by ring
      rw [hw] at h1
      exact h1
    have h2 : ε⁻¹ ^ 2 * (p.1 ^ 2 + p.2 ^ 2) * ε ^ 2 ≤ 1 * ε ^ 2 :=
      mul_le_mul_of_nonneg_right hkey hε2.le
    have heq : ε⁻¹ ^ 2 * (p.1 ^ 2 + p.2 ^ 2) * ε ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
      have h : ε⁻¹ ^ 2 * ε ^ 2 = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hε0, one_pow]
      calc ε⁻¹ ^ 2 * (p.1 ^ 2 + p.2 ^ 2) * ε ^ 2
          = (ε⁻¹ ^ 2 * ε ^ 2) * (p.1 ^ 2 + p.2 ^ 2) := by ring
        _ = 1 * (p.1 ^ 2 + p.2 ^ 2) := by rw [h]
        _ = p.1 ^ 2 + p.2 ^ 2 := one_mul _
    rwa [heq, one_mul] at h2

/-! ## 4. Continuity, integrability and the pointwise domination by `LamFull` -/

theorem KdK_continuous {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) (ε : ℝ) (a b : ℕ) :
    Continuous (KdK ρ ε a b) :=
  (Work.FTS.StrongEps.Kd_smooth (Work.FTS.StrongEps.Jker ρ ε)
    (fun n => Work.FTS.StrongEps.Jker_smooth hρ ε) a b 0).continuous

theorem KdK_hasCompactSupport {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    (a b : ℕ) : HasCompactSupport (KdK ρ ε a b) :=
  Work.FTS.StrongEps.Kd_compact (Work.FTS.StrongEps.Jker ρ ε)
    (Work.FTS.StrongEps.Jker_hasCompactSupport hρ.moll hε) a b

/-- `Λ_raw` is nonnegative. -/
theorem LamK_nonneg {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) (M : ℕ)
    (p : ℝ × ℝ) : 0 ≤ LamK ρ ε M p := by
  simp only [LamK, Work.FTS.StrongEps.Jker]
  exact mul_nonneg (by positivity) (sigKd_nonneg ρ M _)


theorem LamFull_nonneg {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {c : ℝ} (M : ℕ) (p : ℝ × ℝ) : 0 ≤ LamFull ρ ε c M p := by
  rw [LamFull_eq]
  exact mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) (LamK_nonneg hρ hε M p)

theorem LamFull_continuous {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) (ε c : ℝ) (M : ℕ) :
    Continuous (LamFull ρ ε c M) := by
  simp only [LamFull, Work.FTS.StrongEps.Jker]
  exact continuous_const.mul (continuous_const.mul
    ((sigKd_continuous hρ M).comp (continuous_const_smul ε⁻¹)))

/-- The support of `LamFull` sits in the closed ball of radius `ε`. -/
theorem LamFull_support {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {ε c : ℝ} (M : ℕ)
    {p : ℝ × ℝ} (hp : LamFull ρ ε c M p ≠ 0) : p.1 ^ 2 + p.2 ^ 2 ≤ ε ^ 2 := by
  rw [LamFull_eq] at hp
  refine LamK_support hρ M fun h => hp ?_
  rw [h, mul_zero]

/-- The mass of the routed kernel of order `(a,b)` is bounded by `KgainBig`. -/
theorem integral_abs_KdK_le_KgainBig {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {ε : ℝ}
    (hε : 0 < ε) {M : ℕ} {a b : ℕ} (ha : a ≤ M) (hb : b ≤ M) :
    (∫ p : ℝ × ℝ, |KdK ρ ε a b p|) ≤ KgainBig ρ ε M := by
  have hmem : ∫ p : ℝ × ℝ, |KdK ρ ε a b p|
      ≤ ∑ a' ∈ Finset.range (M + 1), ∑ b' ∈ Finset.range (M + 1),
          ∫ p : ℝ × ℝ, |KdK ρ ε a' b' p| := by
    have step1 : (∫ p : ℝ × ℝ, |KdK ρ ε a b p|)
        ≤ ∑ a' ∈ Finset.range (M + 1), ∫ p : ℝ × ℝ, |KdK ρ ε a' b p| :=
      Finset.single_le_sum (f := fun a' => ∫ p : ℝ × ℝ, |KdK ρ ε a' b p|)
        (fun _ _ => integral_nonneg fun p => abs_nonneg _)
        (show a ∈ Finset.range (M + 1) from Finset.mem_range.mpr (by omega))
    have step2 : (∑ a' ∈ Finset.range (M + 1), ∫ p : ℝ × ℝ, |KdK ρ ε a' b p|)
        ≤ ∑ a' ∈ Finset.range (M + 1), ∑ b' ∈ Finset.range (M + 1),
            ∫ p : ℝ × ℝ, |KdK ρ ε a' b' p| :=
      Finset.sum_le_sum fun a' _ => Finset.single_le_sum
        (f := fun b' => ∫ p : ℝ × ℝ, |KdK ρ ε a' b' p|)
        (fun _ _ => integral_nonneg fun p => abs_nonneg _)
        (show b ∈ Finset.range (M + 1) from Finset.mem_range.mpr (by omega))
    exact step1.trans step2
  refine hmem.trans ?_
  have h2 : (1 : ℝ) ≤ 2 ^ (2 * M) := one_le_pow₀ (by norm_num)
  calc (∑ a' ∈ Finset.range (M + 1), ∑ b' ∈ Finset.range (M + 1),
        ∫ p : ℝ × ℝ, |KdK ρ ε a' b' p|)
      = Ksm ρ ε M := rfl
    _ ≤ Ksm ρ ε M * 2 ^ (2 * M) := le_mul_of_one_le_right
        (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
          integral_nonneg fun p => abs_nonneg _) h2
    _ = KgainBig ρ ε M := rfl

theorem Ksm_nonneg {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) (ε : ℝ) (M : ℕ) :
    0 ≤ Ksm ρ ε M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    integral_nonneg fun p => abs_nonneg _

theorem KgainBig_nonneg {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) (ε : ℝ) (M : ℕ) :
    0 ≤ KgainBig ρ ε M :=
  mul_nonneg (Ksm_nonneg hρ ε M) (by positivity)


/-- **The pointwise domination of every routed kernel derivative by `LamFull`**: for
`a + b ≤ M`, the weight-shifted routed kernel is dominated by the single density `LamFull`. -/
theorem abs_KdK_mul_exp_le_LamFull {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) {c : ℝ} (hc : 0 ≤ c) {M a b : ℕ} (hab : a + b ≤ M) (p : ℝ × ℝ) :
    |KdK ρ ε a b p| * Real.exp (2 * c * (|p.1| + |p.2|)) ≤ LamFull ρ ε c M p := by
  have ha : a ≤ M := by omega
  have hb : b ≤ M := by omega
  rcases eq_or_ne (KdK ρ ε a b p) 0 with hzero | hne
  · rw [hzero, abs_zero, zero_mul]
    exact LamFull_nonneg hρ hε M p
  · have hscale := Kd_Jker_scale hρ ε a b p
    have hεinv : ε⁻¹ ^ (a + b) ≠ 0 := pow_ne_zero _ (inv_ne_zero hε.ne')
    have hJne : Work.FTS.StrongEps.Jker (Kdr ρ a b) ε p ≠ 0 := by
      intro h
      exact hne (by rw [hscale, h, mul_zero])
    have hkey : Kdr ρ a b (ε⁻¹ • p) ≠ 0 := by
      intro h
      refine hJne ?_
      simp only [Work.FTS.StrongEps.Jker, h, mul_zero]
    have hball := Kdr_support hρ a b (ε⁻¹ • p) hkey
    rw [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, smul_eq_mul] at hball
    have hsq1 : (ε⁻¹ * p.1) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (ε⁻¹ * p.2)]
    have hsq2 : (ε⁻¹ * p.2) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (ε⁻¹ * p.1)]
    have hb1 : ε⁻¹ * |p.1| ≤ 1 := by
      have h : |ε⁻¹ * p.1| ≤ 1 := abs_le.mpr ⟨by nlinarith [hsq1], by nlinarith [hsq1]⟩
      rwa [abs_mul, abs_of_nonneg (inv_nonneg.mpr hε.le)] at h
    have hb2 : ε⁻¹ * |p.2| ≤ 1 := by
      have h : |ε⁻¹ * p.2| ≤ 1 := abs_le.mpr ⟨by nlinarith [hsq2], by nlinarith [hsq2]⟩
      rwa [abs_mul, abs_of_nonneg (inv_nonneg.mpr hε.le)] at h
    have hmul1 : ε * (ε⁻¹ * |p.1|) = |p.1| := by
      rw [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul]
    have hmul2 : ε * (ε⁻¹ * |p.2|) = |p.2| := by
      rw [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul]
    have hp1 : |p.1| ≤ ε := by
      calc |p.1| = ε * (ε⁻¹ * |p.1|) := hmul1.symm
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hb1 hε.le
        _ = ε := mul_one ε
    have hp2 : |p.2| ≤ ε := by
      calc |p.2| = ε * (ε⁻¹ * |p.2|) := hmul2.symm
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hb2 hε.le
        _ = ε := mul_one ε
    have hexp : Real.exp (2 * c * (|p.1| + |p.2|)) ≤ Real.exp (4 * c * ε) := by
      rw [Real.exp_le_exp]
      nlinarith [hc]
    have habs : |Work.FTS.StrongEps.Jker (Kdr ρ a b) ε p|
        = Work.FTS.StrongEps.Jker (fun q => |Kdr ρ a b q|) ε p := by
      simp only [Work.FTS.StrongEps.Jker, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε⁻¹ ^ 2)]
    have hpt : ∀ q : ℝ × ℝ, |Kdr ρ a b q| ≤ sigKd ρ M q := by
      intro q
      have h1 : |Kdr ρ a b q| ≤ ∑ b' ∈ Finset.range (M + 1), |Kdr ρ a b' q| :=
        Finset.single_le_sum (f := fun b' => |Kdr ρ a b' q|) (fun _ _ => abs_nonneg _)
          (show b ∈ Finset.range (M + 1) from Finset.mem_range.mpr (by omega))
      have h2 : (∑ b' ∈ Finset.range (M + 1), |Kdr ρ a b' q|)
          ≤ ∑ a' ∈ Finset.range (M + 1), ∑ b' ∈ Finset.range (M + 1), |Kdr ρ a' b' q| :=
        Finset.single_le_sum (f := fun a' => ∑ b' ∈ Finset.range (M + 1), |Kdr ρ a' b' q|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (show a ∈ Finset.range (M + 1) from Finset.mem_range.mpr (by omega))
      exact h1.trans h2
    have hmono : Work.FTS.StrongEps.Jker (fun q => |Kdr ρ a b q|) ε p ≤ LamK ρ ε M p := by
      rw [LamK]
      exact mul_le_mul_of_nonneg_left (hpt (ε⁻¹ • p)) (by positivity)
    have hpow : ε⁻¹ ^ (a + b) ≤ ε⁻¹ ^ M :=
      pow_le_pow_right₀ ((one_le_inv₀ hε).mpr hε1) hab
    have hker : |KdK ρ ε a b p| ≤ ε⁻¹ ^ M * LamK ρ ε M p := by
      rw [hscale, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε⁻¹ ^ (a + b)), habs]
      exact mul_le_mul hpow hmono (by
        simp only [Work.FTS.StrongEps.Jker]
        positivity) (by positivity)
    calc |KdK ρ ε a b p| * Real.exp (2 * c * (|p.1| + |p.2|))
        ≤ |KdK ρ ε a b p| * Real.exp (4 * c * ε) :=
          mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
      _ ≤ (ε⁻¹ ^ M * LamK ρ ε M p) * Real.exp (4 * c * ε) :=
          mul_le_mul_of_nonneg_right hker (Real.exp_pos _).le
      _ = LamFull ρ ε c M p := by
          rw [LamFull_eq]; ring

end Work.FTS.StrongEps.EpsE4Thr
