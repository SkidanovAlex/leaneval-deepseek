/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E5G/Xn_JfamP_lip.lean` — **mis-stated: the per-slice
regularity is missing** (and the repaired statement is proved below)

## The obstruction (why the listed hypotheses do not support the conclusion)

The conclusion is a Lipschitz bound in `τ` for `τ ↦ slice (JfamP ρ ε g) τ =
Pz (J_ε (slice g τ))`.  The listed hypotheses constrain **only the differences**
`slice g τ − slice g τ'` (smoothness `hsmD`, honest `ℋ⁴`-membership and the `Xn`-bound `hsl`) plus
the zero mode of each slice (`hl12`); they involve **no** regularity of the individual profiles
`slice g s`.  This is not an accident of the statement — the hypotheses are literally *invariant*
under adding one fixed arbitrary profile `ξ` to every slice:

* `hsmD` becomes `SmoothOpen ((ξ + ψ_τ) − (ξ + ψ_τ')) = SmoothOpen (ψ_τ − ψ_τ')`, unchanged;
* `hsl` likewise only sees the differences;
* `hl12` only constrains the single linear functional `L₁₂(·)(0)`.

Consequently `SmoothOpen (slice g s)` and `HkMem α 4 (slice g s)` are **not derivable**, and the only
bridge from the hypotheses to the conclusion is additivity of the log-coordinate mollifier,
`J_ε f − J_ε f' = J_ε (f − f')`.  In this workspace that additivity is available *only* for
arguments which are `ContinuousOn`/`SmoothOpen` on the quadrant
(`EpsRLX.Jeps_sub_eq`, `EpsEngine.Jeps_add`, `JepsSubApply`), and it **fails** at the level of the
listed hypotheses because of the junk-integral convention `integral_undef`
(`¬ Integrable f μ → ∫ a, f a ∂μ = 0`): take `f := fun z θ => 1/|z-1|`, `f' := 0`.  Then
`f − f' = f`, and at every `(z,θ)` whose log-ball meets `z = 1` the left side
`J_ε f − J_ε f'` is `0 − 0 = 0` (both `p`-integrands are non-integrable there, `1/|p₁ − log z|` being
non-`L¹` on a ball centred at the singular line), whereas `J_ε (f − f') = J_ε f` is the genuine,
non-zero integral of a positive function.  So the two sides differ on a set of positive measure.

Every brick the intended proof of this lemma uses is therefore inapplicable at the listed
hypotheses:

| brick | what it needs |
|---|---|
| `HkSq_Jeps_le` (E1) | `HkMem α 4` of the argument (an *individual* slice) |
| `HkMem_Jeps`, `smoothOpen_Jeps` | all-order `ContDiffOn` of the argument on `Quad` |
| `L12_lipschitz_field`, `L12_sub_HkMem` | `HQo α 4` of *both* arguments |
| `L12_Jeps_sub_le4` | `SmoothOpen` and `HkMem α 4` of its argument |
| `E5G.hkNorm_Pz_le_four` | `SmoothOpen` of its argument |

and these are precisely the bricks named in the lead's plan for this lemma
(`Submission/Work/FTS/StrongEps/NOTES_session20.md` §3, "**Then** the projected version follows with
`HkSq_Jeps_le` (E1), `hkNorm_Pz_le_four` … and the rank-one correction's τ-variation").

## The repair (proved in this file)

`Xn_JfamP_lip_of_reg` below adds exactly the per-slice regularity

  `hreg : ∀ s ∈ Icc 0 T, SmoothOpen (slice g s) ∧ HkMem α 4 (slice g s)`

and is proved by `EpsRLX.Jeps_sub_eq` + `EpsRLX.Pz_sub_eq` (the `L₁₂`-additivity coming from
`EComparison.L12_sub_HkMem`) + `HkSq_Jeps_le` (E1) + `hkNorm_Pz_le_four`, with the constant
`max 1 (A · e^{C/2} · max B 0)`.  Note `hl12` is **not** needed for it.  The intended consumer has
this hypothesis for free: the tower data carries `TowerAt.hsm` (`SmoothOpen (slice g τ)`) and
`TowerAt.hmem6` (`HkMem α 6 (slice g τ)`, which descends to `HkMem α 4` via
`OpenPkg.HkMem_mono_open`).

-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.PZero
import Submission.Work.FTS.StrongEps.PZeroAux.Pz_l12
import Submission.Work.FTS.StrongEps.HkSq_Jeps_le
import Submission.Work.FTS.StrongEps.L12_Jeps_sub_le4
import Submission.Work.FTS.StrongEps.LimApproxSE
import Submission.Work.FTS.StrongEps.EpsRLX.DeltaData
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.JepsSmoothOpen
import Submission.Work.FTS.StrongEps.HkMem_Jeps
import Submission.Work.FTS.StrongEps.E5G.hkNorm_Pz_le_four

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The repaired statement (per-slice regularity added) -/

/-- **The repaired `Xn_JfamP_lip`**: the projected-mollified family is `ℋ⁴`-Lipschitz in the fake
time, *assuming the per-slice regularity* `SmoothOpen (slice g s) ∧ HkMem α 4 (slice g s)`.

Chain: `slice (JfamP ρ ε g) τ = P₀ (J_ε (slice g τ))` (definitional),
`J_ε f − J_ε f' = J_ε (f − f')` (`EpsRLX.Jeps_sub_eq`), `P₀ F − P₀ G = P₀ (F − G)`
(`EpsRLX.Pz_sub_eq` with `L₁₂`-additivity `EComparison.L12_sub_HkMem`), then
`‖P₀ X‖_{ℋ⁴} ≤ A‖X‖_{ℋ⁴}` (`hkNorm_Pz_le_four`) and `‖J_ε D‖_{ℋ⁴} ≤ e^{C/2}‖D‖_{ℋ⁴}`
(`HkSq_Jeps_le`, E1), and finally the hypothesis on the slices' differences. -/
theorem Xn_JfamP_lip_of_reg {α T ε B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
    {E : Fn → Fn} {g : Fam}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc (0 : ℝ) 1)
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (hreg : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen (slice g s) ∧
        Work.Spaces.HkMem α 4 (slice g s))
    (hsmD : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ τ' ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => slice g τ z θ - slice g τ' z θ))
    (hsl : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ τ' ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 4 (fun z θ => slice g τ z θ - slice g τ' z θ) ∧
        Work.FTS.Nonlin.Xn α (fun z θ => slice g τ z θ - slice g τ' z θ)
          ≤ B * |τ - τ'|) :
    ∃ L : ℝ, 0 < L ∧ ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ τ' ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.Nonlin.Xn α (fun z θ =>
          slice (Work.FTS.StrongEps.JfamP ρ ε g) τ z θ
            - slice (Work.FTS.StrongEps.JfamP ρ ε g) τ' z θ)
        ≤ L * |τ - τ'| := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongEps.HkSq_Jeps_le ρ hρ.moll
  obtain ⟨A, hApos, hA⟩ := Work.FTS.StrongEps.E5G.hkNorm_Pz_le_four
  refine ⟨max 1 (A * Real.exp (C / 2) * max B 0),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro τ hτ τ' hτ'
  -- the three profiles
  set f : Fn := slice g τ with hfdef
  set f' : Fn := slice g τ' with hf'def
  set D : Fn := fun z θ => f z θ - f' z θ with hDdef
  have hf : Work.FTS.EllipticEst.SmoothOpen f := (hreg τ hτ).1
  have hf' : Work.FTS.EllipticEst.SmoothOpen f' := (hreg τ' hτ').1
  have hmf : Work.Spaces.HkMem α 4 f := (hreg τ hτ).2
  have hmf' : Work.Spaces.HkMem α 4 f' := (hreg τ' hτ').2
  have hDsm : Work.FTS.EllipticEst.SmoothOpen D := by
    rw [hDdef, hfdef, hf'def]; exact hsmD τ hτ τ' hτ'
  have hDmem : Work.Spaces.HkMem α 4 D := by
    rw [hDdef, hfdef, hf'def]; exact (hsl τ hτ τ' hτ').1
  have hDXn : Work.FTS.Nonlin.Xn α D ≤ B * |τ - τ'| := by
    rw [hDdef, hfdef, hf'def]; exact (hsl τ hτ τ' hτ').2
  -- the `∀n`-forms of smoothness, in the two shapes used by the library
  have hQ0 : ∀ {F : Fn}, Work.FTS.EllipticEst.SmoothOpen F →
      ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) Work.FTS.EllipticEst.Q0 :=
    fun hF n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hF n
  have hQuad : ∀ {F : Fn}, Work.FTS.EllipticEst.SmoothOpen F →
      ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) Work.FTS.StrongEps.Quad :=
    fun hF n => by
      simpa only [Work.FTS.StrongEps.Quad, Work.FTS.EllipticEst.Q0] using hQ0 hF n
  -- smoothness and honest membership of the mollified profiles
  have hJfSm : Work.FTS.EllipticEst.SmoothOpen (Jeps ρ ε f) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε.1 (hQ0 hf)
  have hJf'Sm : Work.FTS.EllipticEst.SmoothOpen (Jeps ρ ε f') :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε.1 (hQ0 hf')
  have hJfMem : Work.Spaces.HkMem α 4 (Jeps ρ ε f) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε.1 (hQuad hf) hmf
  have hJf'Mem : Work.Spaces.HkMem α 4 (Jeps ρ ε f') :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε.1 (hQuad hf') hmf'
  have hDMemJ : Work.Spaces.HkMem α 4 (Jeps ρ ε D) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε.1 (hQuad hDsm) hDmem
  have hDSmJ : Work.FTS.EllipticEst.SmoothOpen (Jeps ρ ε D) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε.1 (hQ0 hDsm)
  -- additivity of `J_ε` on the two slices
  have hJsub : Jeps ρ ε f - Jeps ρ ε f' = Jeps ρ ε D := by
    rw [hDdef]
    exact Work.FTS.StrongEps.EpsRLX.Jeps_sub_eq hρ.moll hε.1 hf hf'
  -- affinity of `P₀`
  have hL12 : Work.Construction.L12
        (fun z θ => Jeps ρ ε f z θ - Jeps ρ ε f' z θ) 0
      = Work.Construction.L12 (Jeps ρ ε f) 0
        - Work.Construction.L12 (Jeps ρ ε f') 0 :=
    Work.FTS.StrongEps.EComparison.L12_sub_HkMem hJfSm hJf'Sm hJfMem hJf'Mem 0
      (by simp [Work.Spaces.Iz])
  have hPz : Pz (Jeps ρ ε f) - Pz (Jeps ρ ε f') = Pz (Jeps ρ ε D) := by
    rw [← hJsub]
    exact Work.FTS.StrongEps.EpsRLX.Pz_sub_eq hL12
  -- the two norm bounds
  have hPzb : Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε D))
      ≤ A * Work.FTS.Nonlin.Xn α (Jeps ρ ε D) :=
    hA α hα (Jeps ρ ε D) hDSmJ hDMemJ
  have hJXn : Work.FTS.Nonlin.Xn α (Jeps ρ ε D)
      ≤ Real.exp (C / 2) * Work.FTS.Nonlin.Xn α D := by
    have hsq := hC α hα 4 ε hε.1 hε.2 D (hQ0 hDsm) hDmem hDMemJ
    calc Work.FTS.Nonlin.Xn α (Jeps ρ ε D)
        = Real.sqrt (Work.Spaces.HkSq α 4 (Jeps ρ ε D)) := rfl
      _ ≤ Real.sqrt (Real.exp (C * ε) * Work.Spaces.HkSq α 4 D) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (Real.exp (C * ε)) * Real.sqrt (Work.Spaces.HkSq α 4 D) :=
          Real.sqrt_mul (Real.exp_pos _).le _
      _ = Real.exp (C * ε / 2) * Work.FTS.Nonlin.Xn α D := by
          rw [Real.exp_half]; rfl
      _ ≤ Real.exp (C / 2) * Work.FTS.Nonlin.Xn α D := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          exact Real.exp_le_exp.mpr (by nlinarith [hε.2, hCpos])
  -- the `max B 0` upgrade
  have hDXn' : Work.FTS.Nonlin.Xn α D ≤ max B 0 * |τ - τ'| :=
    hDXn.trans (mul_le_mul_of_nonneg_right (le_max_left B 0) (abs_nonneg _))
  -- assembly
  have hmain : Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε f) - Pz (Jeps ρ ε f'))
      ≤ A * Real.exp (C / 2) * (max B 0 * |τ - τ'|) := by
    calc Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε f) - Pz (Jeps ρ ε f'))
        = Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε D)) := by rw [hPz]
      _ ≤ A * Work.FTS.Nonlin.Xn α (Jeps ρ ε D) := hPzb
      _ ≤ A * (Real.exp (C / 2) * Work.FTS.Nonlin.Xn α D) :=
          mul_le_mul_of_nonneg_left hJXn hApos.le
      _ ≤ A * (Real.exp (C / 2) * (max B 0 * |τ - τ'|)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hDXn' (Real.exp_pos _).le) hApos.le
      _ = A * Real.exp (C / 2) * (max B 0 * |τ - τ'|) := by ring
  have hfin : A * Real.exp (C / 2) * (max B 0 * |τ - τ'|)
      ≤ max 1 (A * Real.exp (C / 2) * max B 0) * |τ - τ'| := by
    rw [show A * Real.exp (C / 2) * (max B 0 * |τ - τ'|)
        = (A * Real.exp (C / 2) * max B 0) * |τ - τ'| from by ring]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)
  have hgoal : Work.FTS.Nonlin.Xn α (fun z θ =>
        slice (Work.FTS.StrongEps.JfamP ρ ε g) τ z θ
          - slice (Work.FTS.StrongEps.JfamP ρ ε g) τ' z θ)
      = Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε f) - Pz (Jeps ρ ε f')) := by
    rw [hfdef, hf'def]
    rfl
  rw [hgoal]
  exact hmain.trans hfin

/-! ## The requested statement (kept verbatim; see the header for why its hypotheses are
insufficient) -/

theorem Xn_JfamP_lip {α T ε B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc (0 : ℝ) 1)
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (hl12 : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.Construction.L12 (Work.FTS.Galerkin.slice g s) 0 = 0)
    (hsmD : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ τ' ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.FTS.Galerkin.slice g τ z θ - Work.FTS.Galerkin.slice g τ' z θ))
    (hsl : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ τ' ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 4 (fun z θ => Work.FTS.Galerkin.slice g τ z θ - Work.FTS.Galerkin.slice g τ' z θ) ∧
        Work.FTS.Nonlin.Xn α (fun z θ => Work.FTS.Galerkin.slice g τ z θ - Work.FTS.Galerkin.slice g τ' z θ)
          ≤ B * |τ - τ'|) :
    ∃ L : ℝ, 0 < L ∧ ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ τ' ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.Nonlin.Xn α (fun z θ =>
          Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ z θ
            - Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ' z θ)
        ≤ L * |τ - τ'| := by
  sorry

end Work.FTS.StrongEps.E5G
