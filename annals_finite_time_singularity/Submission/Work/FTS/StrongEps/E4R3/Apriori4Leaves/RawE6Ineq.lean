import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Defs
import Submission.Work.FTS.StrongPersist.H6Pair_ones3

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Leaves/RawE6Ineq.lean` — OPEN LEAF L-A (research-low given S1–S5, F6)

curric-46 install 2026-10-12 (`cbc/fts_apriori6_ruling.md` §3 L-A; REVIEW fix F1).
The raw energy inequality with an `ε`-small superlinear defect.  Write `X = epsWP`, `x = P₀Jg`,
`e = rawE6`:
`IP6(P₀JX, g) = IP6(X, x) + c(Jg)·IP6(X, bump) − c_X·IP6(bump, g) + O(ε|X|₆|g|₆)`;
with S2 and `HkSq_Jeps_step_le` the defect is `≤ C|g|₆² + Cε(1+e)^{3/2}`;
`IP6(X, x) ≤ CL·Sq6 x + |H6Pair|` (`H6Aux.H6Lin_IP6`, one-sided, + `H6Pair`).
`IP6_lo_coeffs` needs only `HQo 6`, so the raw slices qualify.  Inputs: S1 `Jeps_IP6_transfer`,
S2 `epsWP_semitame`, S3 `Jeps_gain_quant`, S5 `L6Ctx_JfamP`, F6 `rawSlice_L12_zero`,
`IP6_cs/lo_coeffs`, `hkNorm_Pz_le`, `HkSq_Jeps_sub_le`, `HkSq_JfamP_le`, `Pz_l12`.

The pairing estimate is the PROVED `StrongPersist.H6Pair_ones3` (REVIEW F1 — NOT the duplicate
node `H6Pair6`): `rawE6_ineq_ones3` below instantiates it (needs `0 < Ce`, from `core1_1a3`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R4

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongEps
open Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false

/-- **OPEN LEAF (L-A)** `2 IP6(epsRHSP, g) ≤ Λ(1+e) + ε C₁ (1+e)²` along ball-solutions, given a
level-six pairing estimate `H6Pair`. -/
theorem rawE6_ineq {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) (hρs : ∀ p : ℝ × ℝ, ρ (-p) = ρ p)
    {α₂ Ce Cp : ℝ}
    (hpair : Work.FTS.StrongPersist.H6Pair (IP6o) α₂ Ce Cp) :
    ∀ C₀ Cs : ℝ, ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α ∈ Ioc 0 α₀, ∃ Λ C₁ : ℝ, 0 ≤ Λ ∧ 0 ≤ C₁ ∧
    ∀ {K : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn},
    E4Data α C₀ K Ce Cs ρ Φs E g₀ → Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ T : ℝ, 0 < T → ∀ g : Fam,
      IsEpsSolP α ρ ε T Φs E g₀ g → EpsRegP α ρ ε T g →
      (∀ τ ∈ Icc 0 T, Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2) →
      ∀ τ ∈ Ioo 0 T,
        2 * IP6o α (epsRHSP α ρ ε Φs E g τ) (slice g τ)
          ≤ Λ * (1 + rawE6 α g τ) + ε * C₁ * (1 + rawE6 α g τ) ^ 2 := by
  sorry

/-- `rawE6_ineq` with the pairing estimate supplied by the PROVED `H6Pair_ones3` (PROVED modulo
the leaf `rawE6_ineq`).  This is the form the `ℋ⁶`-half (`sixthChapterB_leaf`) should use. -/
theorem rawE6_ineq_ones3 {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ)
    (hρs : ∀ p : ℝ × ℝ, ρ (-p) = ρ p) {Ce : ℝ} (hCe : 0 < Ce) :
    ∀ C₀ Cs : ℝ, ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α ∈ Ioc 0 α₀, ∃ Λ C₁ : ℝ, 0 ≤ Λ ∧ 0 ≤ C₁ ∧
    ∀ {K : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn},
    E4Data α C₀ K Ce Cs ρ Φs E g₀ → Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ T : ℝ, 0 < T → ∀ g : Fam,
      IsEpsSolP α ρ ε T Φs E g₀ g → EpsRegP α ρ ε T g →
      (∀ τ ∈ Icc 0 T, Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2) →
      ∀ τ ∈ Ioo 0 T,
        2 * IP6o α (epsRHSP α ρ ε Φs E g τ) (slice g τ)
          ≤ Λ * (1 + rawE6 α g τ) + ε * C₁ * (1 + rawE6 α g τ) ^ 2 := by
  obtain ⟨α₂, Cp, _hCp, _hα₂, hpair⟩ := Work.FTS.StrongPersist.H6Pair_ones3 Ce hCe
  exact rawE6_ineq hρ hρs hpair

end Work.FTS.StrongEps.EpsE4Thr.E4R4
