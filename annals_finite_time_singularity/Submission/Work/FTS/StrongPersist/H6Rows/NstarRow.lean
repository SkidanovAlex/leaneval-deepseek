import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongPersist.IP6_cs_coeffs
import Submission.Work.FTS.StrongPersist.IP6Clauses
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.HkNorm_const_mul
import Submission.Work.FTS.StrongPersist.H6Rows.RowAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.ip6_dz_self

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn Fam slice dynRHS)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The `N_*`-row

`Construction.Nstar μ lam g = -μg - (μ+λ+μλ)·D_zg`, and the paper's `λ = lamfun μ` makes
`μ+λ+μλ = -μ`, so `N_* = μ(D_zg - g)`.  Its pairing against `g` is bounded by
`(|μ| + |μ+λ+μλ|)` times the two self-pairings; the `D_z`-self-pairing is the *proved*
`H6Pair6Aux.ip6_dz_self` (the lossless radial IBP), the other is Cauchy–Schwarz. -/

/-- **The `N_*`-row**: `|IP6 α (N_star μ λ f) f| ≤ C·(|μ| + |μ+λ+μλ|)·|f|²_{ℋ⁶}`.  No elliptic
data enters: only `HkMem α 7 f` (needed by the `D_z`-self-pairing, which must integrate by parts
across the order-seven slots) and the two bonding lemmas. -/
theorem nstar_pair_le : ∃ C α₂ : ℝ, 0 < C ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (μ lam : ℝ) (f : Fn),
      Work.FTS.VocabO.HQo α 6 f → Work.Spaces.HkMem α 7 f →
      |IP6 1 1 1 1 1 1 1 1 1 1 α
          (fun z θ => -μ * f z θ - (μ + lam + μ * lam) * Work.Spaces.Dz f z θ) f|
        ≤ C * (|μ| + |μ + lam + μ * lam|) * Work.Spaces.HkSq α 6 f := by
  obtain ⟨Cd, αd, hCd0, hαd0, hdz_self⟩ := H6Pair6Aux.ip6_dz_self
  obtain ⟨CC, hCC0, hCS⟩ := IP6_cs_coeffs 1 1 1 1 1 1 1 1 1 1 1 one_pos
  refine ⟨max Cd CC, min αd 1, lt_of_lt_of_le hCd0 (le_max_left Cd CC),
    lt_min hαd0 one_pos, ?_⟩
  intro α hα μ lam f hf h7
  have hα0 : 0 < α := hα.1
  have hαd : α ∈ Set.Ioc 0 αd := ⟨hα0, le_trans hα.2 (min_le_left _ _)⟩
  have hα1 : α ∈ Set.Ioc 0 1 := ⟨hα0, le_trans hα.2 (min_le_right _ _)⟩
  have h6 : Work.Spaces.HkMem α 6 f := hf.2
  have hsmf : Work.FTS.EllipticEst.SmoothOpen f := hf.1
  have hsm1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => -μ * f z θ) :=
    smoothOpen_const_mul' (-μ) hsmf
  have hsm2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -(μ + lam + μ * lam) * Work.Spaces.Dz f z θ) :=
    smoothOpen_const_mul' (-(μ + lam + μ * lam)) hsmf.Dz
  have hm1 : Work.Spaces.HkMem α 6 (fun z θ => -μ * f z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 6 (-μ) h6
  have hm2 : Work.Spaces.HkMem α 6 (fun z θ => -(μ + lam + μ * lam) * Work.Spaces.Dz f z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 6 (-(μ + lam + μ * lam))
      (Work.FTS.IPGen.HkMem_Dz_le hsmf h7)
  have hcongr : (fun z θ => -μ * f z θ - (μ + lam + μ * lam) * Work.Spaces.Dz f z θ)
      = fun z θ => (-μ * f z θ) + (-(μ + lam + μ * lam) * Work.Spaces.Dz f z θ) := by
    funext z θ
    ring
  rw [hcongr]
  rw [IP6_add 1 1 1 1 1 1 1 1 1 1 α hα0 hsm1 hsm2 hsmf hm1 hm2 h6]
  rw [IP6_smul 1 1 1 1 1 1 1 1 1 1 α (-μ) f f,
    IP6_smul 1 1 1 1 1 1 1 1 1 1 α (-(μ + lam + μ * lam)) (Work.Spaces.Dz f) f]
  have hA1 : |IP6 1 1 1 1 1 1 1 1 1 1 α f f| ≤ CC * Work.Spaces.HkSq α 6 f := by
    have h := hCS α hα1 f f hf hf
    have hs : Xn6 α f * Xn6 α f = Work.Spaces.HkSq α 6 f := by
      rw [← sq, Work.FTS.StrongPersist.Xn6_sq]
    calc |IP6 1 1 1 1 1 1 1 1 1 1 α f f| ≤ CC * Xn6 α f * Xn6 α f := h
      _ = CC * (Xn6 α f * Xn6 α f) := by ring
      _ = CC * Work.Spaces.HkSq α 6 f := by rw [hs]
  have hA2 : |IP6 1 1 1 1 1 1 1 1 1 1 α (Work.Spaces.Dz f) f|
      ≤ Cd * Work.Spaces.HkSq α 6 f := hdz_self α hαd f hf h7
  have hSq0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  set A1 := IP6 1 1 1 1 1 1 1 1 1 1 α f f with hA1def
  set A2 := IP6 1 1 1 1 1 1 1 1 1 1 α (Work.Spaces.Dz f) f with hA2def
  have h1 : |(-μ) * A1| ≤ |μ| * (CC * Work.Spaces.HkSq α 6 f) := by
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left hA1 (abs_nonneg μ)
  have h2 : |(-(μ + lam + μ * lam)) * A2| ≤ |μ + lam + μ * lam| * (Cd * Work.Spaces.HkSq α 6 f) := by
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left hA2 (abs_nonneg _)
  have h3 : |(-μ) * A1 + (-(μ + lam + μ * lam)) * A2|
      ≤ |μ| * (CC * Work.Spaces.HkSq α 6 f)
        + |μ + lam + μ * lam| * (Cd * Work.Spaces.HkSq α 6 f) :=
    le_trans (abs_add_le _ _) (add_le_add h1 h2)
  have hCdSq : 0 ≤ Cd * Work.Spaces.HkSq α 6 f := mul_nonneg hCd0.le hSq0
  have hCCSq : 0 ≤ CC * Work.Spaces.HkSq α 6 f := mul_nonneg hCC0.le hSq0
  have h4 : |μ| * (CC * Work.Spaces.HkSq α 6 f)
      + |μ + lam + μ * lam| * (Cd * Work.Spaces.HkSq α 6 f)
      ≤ max Cd CC * (|μ| + |μ + lam + μ * lam|) * Work.Spaces.HkSq α 6 f := by
    have ha : CC ≤ max Cd CC := le_max_right _ _
    have hb : Cd ≤ max Cd CC := le_max_left _ _
    have h5 : |μ| * (CC * Work.Spaces.HkSq α 6 f) ≤ |μ| * (max Cd CC * Work.Spaces.HkSq α 6 f) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha hSq0) (abs_nonneg μ)
    have h6' : |μ + lam + μ * lam| * (Cd * Work.Spaces.HkSq α 6 f)
        ≤ |μ + lam + μ * lam| * (max Cd CC * Work.Spaces.HkSq α 6 f) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb hSq0) (abs_nonneg _)
    have hsum : |μ| * (max Cd CC * Work.Spaces.HkSq α 6 f)
        + |μ + lam + μ * lam| * (max Cd CC * Work.Spaces.HkSq α 6 f)
        = max Cd CC * (|μ| + |μ + lam + μ * lam|) * Work.Spaces.HkSq α 6 f := by ring
    linarith [h5, h6', hsum.le, hsum.ge]
  simpa only [hA1def, hA2def] using le_trans h3 h4



end Work.FTS.StrongPersist
