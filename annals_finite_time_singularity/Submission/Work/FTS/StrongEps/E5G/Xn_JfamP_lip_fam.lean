import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Submission.Work.FTS.StrongEps.E5G.Xn_JfamP_lip

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

set_option linter.unusedVariables false

/-- **The family version of `Work.FTS.StrongEps.E5G.Xn_JfamP_lip_of_reg`:** the projected,
mollified families `JfamP ρ (ε k) (G k)` are `ℋ⁴`-Lipschitz in the fake time with a *single*
constant `L`, uniform in the family index `k`.

The proof is the proof of `Xn_JfamP_lip_of_reg` with the index `k` universally quantified
throughout: the chain
`slice (JfamP ρ ε g) τ − slice (JfamP ρ ε g) τ' = Pz (J_ε (slice g τ) − J_ε (slice g τ'))`
(`EpsRLX.Jeps_sub_eq` + `EpsRLX.Pz_sub_eq` + `EComparison.L12_sub_HkMem`), then
`‖Pz X‖_{ℋ⁴} ≤ A ‖X‖_{ℋ⁴}` (`hkNorm_Pz_le_four`) and `‖J_ε X‖_{ℋ⁴} ≤ e^{C/2} ‖X‖_{ℋ⁴}`
(`HkSq_Jeps_le`, the constant being independent of `ε ≤ 1`), so that
`L := max 1 (A · e^{C/2} · max B 0)` works for every `k`. -/
theorem Xn_JfamP_lip_fam {α T B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {G : ℕ → Work.FTS.Galerkin.Fam} {ε : ℕ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1)
    (hε : ∀ k : ℕ, ε k ∈ Set.Ioc (0 : ℝ) 1)
    (hreg : ∀ k : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Galerkin.slice (G k) s) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.Galerkin.slice (G k) s))
    (hsmD : ∀ k : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ τ' ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
        Work.FTS.Galerkin.slice (G k) τ z θ - Work.FTS.Galerkin.slice (G k) τ' z θ))
    (hsl : ∀ k : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ τ' ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 4 (fun z θ =>
          Work.FTS.Galerkin.slice (G k) τ z θ - Work.FTS.Galerkin.slice (G k) τ' z θ) ∧
        Work.FTS.Nonlin.Xn α (fun z θ =>
          Work.FTS.Galerkin.slice (G k) τ z θ - Work.FTS.Galerkin.slice (G k) τ' z θ)
          ≤ B * |τ - τ'|) :
    ∃ L : ℝ, 0 < L ∧ ∀ k : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ τ' ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.Nonlin.Xn α (fun z θ =>
          Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) τ z θ
            - Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) τ' z θ)
        ≤ L * |τ - τ'| := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongEps.HkSq_Jeps_le ρ hρ.moll
  obtain ⟨A, hApos, hA⟩ := Work.FTS.StrongEps.E5G.hkNorm_Pz_le_four
  refine ⟨max 1 (A * Real.exp (C / 2) * max B 0),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro k τ hτ τ' hτ'
  -- the three profiles
  set f : Fn := slice (G k) τ with hfdef
  set f' : Fn := slice (G k) τ' with hf'def
  set D : Fn := fun z θ => f z θ - f' z θ with hDdef
  have hf : Work.FTS.EllipticEst.SmoothOpen f := (hreg k τ hτ).1
  have hf' : Work.FTS.EllipticEst.SmoothOpen f' := (hreg k τ' hτ').1
  have hmf : Work.Spaces.HkMem α 4 f := (hreg k τ hτ).2
  have hmf' : Work.Spaces.HkMem α 4 f' := (hreg k τ' hτ').2
  have hDsm : Work.FTS.EllipticEst.SmoothOpen D := by
    rw [hDdef, hfdef, hf'def]; exact hsmD k τ hτ τ' hτ'
  have hDmem : Work.Spaces.HkMem α 4 D := by
    rw [hDdef, hfdef, hf'def]; exact (hsl k τ hτ τ' hτ').1
  have hDXn : Work.FTS.Nonlin.Xn α D ≤ B * |τ - τ'| := by
    rw [hDdef, hfdef, hf'def]; exact (hsl k τ hτ τ' hτ').2
  -- the `∀n`-forms of smoothness, in the two shapes used by the library
  have hQ0 : ∀ {F : Fn}, Work.FTS.EllipticEst.SmoothOpen F →
      ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) Work.FTS.EllipticEst.Q0 :=
    fun hF n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hF n
  have hQuad : ∀ {F : Fn}, Work.FTS.EllipticEst.SmoothOpen F →
      ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) Work.FTS.StrongEps.Quad :=
    fun hF n => by
      simpa only [Work.FTS.StrongEps.Quad, Work.FTS.EllipticEst.Q0] using hQ0 hF n
  -- smoothness and honest membership of the mollified profiles
  have hJfSm : Work.FTS.EllipticEst.SmoothOpen (Jeps ρ (ε k) f) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ (hε k).1 (hQ0 hf)
  have hJf'Sm : Work.FTS.EllipticEst.SmoothOpen (Jeps ρ (ε k) f') :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ (hε k).1 (hQ0 hf')
  have hJfMem : Work.Spaces.HkMem α 4 (Jeps ρ (ε k) f) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα (hε k).1 (hQuad hf) hmf
  have hJf'Mem : Work.Spaces.HkMem α 4 (Jeps ρ (ε k) f') :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα (hε k).1 (hQuad hf') hmf'
  have hDMemJ : Work.Spaces.HkMem α 4 (Jeps ρ (ε k) D) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα (hε k).1 (hQuad hDsm) hDmem
  have hDSmJ : Work.FTS.EllipticEst.SmoothOpen (Jeps ρ (ε k) D) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ (hε k).1 (hQ0 hDsm)
  -- additivity of `J_ε` on the two slices
  have hJsub : Jeps ρ (ε k) f - Jeps ρ (ε k) f' = Jeps ρ (ε k) D := by
    rw [hDdef]
    exact Work.FTS.StrongEps.EpsRLX.Jeps_sub_eq hρ.moll (hε k).1 hf hf'
  -- affinity of `P₀`
  have hL12 : Work.Construction.L12
        (fun z θ => Jeps ρ (ε k) f z θ - Jeps ρ (ε k) f' z θ) 0
      = Work.Construction.L12 (Jeps ρ (ε k) f) 0
        - Work.Construction.L12 (Jeps ρ (ε k) f') 0 :=
    Work.FTS.StrongEps.EComparison.L12_sub_HkMem hJfSm hJf'Sm hJfMem hJf'Mem 0
      (by simp [Work.Spaces.Iz])
  have hPz : Pz (Jeps ρ (ε k) f) - Pz (Jeps ρ (ε k) f') = Pz (Jeps ρ (ε k) D) := by
    rw [← hJsub]
    exact Work.FTS.StrongEps.EpsRLX.Pz_sub_eq hL12
  -- the two norm bounds
  have hPzb : Work.FTS.Nonlin.Xn α (Pz (Jeps ρ (ε k) D))
      ≤ A * Work.FTS.Nonlin.Xn α (Jeps ρ (ε k) D) :=
    hA α hα (Jeps ρ (ε k) D) hDSmJ hDMemJ
  have hJXn : Work.FTS.Nonlin.Xn α (Jeps ρ (ε k) D)
      ≤ Real.exp (C / 2) * Work.FTS.Nonlin.Xn α D := by
    have hsq := hC α hα 4 (ε k) (hε k).1 (hε k).2 D (hQ0 hDsm) hDmem hDMemJ
    calc Work.FTS.Nonlin.Xn α (Jeps ρ (ε k) D)
        = Real.sqrt (Work.Spaces.HkSq α 4 (Jeps ρ (ε k) D)) := rfl
      _ ≤ Real.sqrt (Real.exp (C * ε k) * Work.Spaces.HkSq α 4 D) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (Real.exp (C * ε k)) * Real.sqrt (Work.Spaces.HkSq α 4 D) :=
          Real.sqrt_mul (Real.exp_pos _).le _
      _ = Real.exp (C * ε k / 2) * Work.FTS.Nonlin.Xn α D := by
          rw [Real.exp_half]; rfl
      _ ≤ Real.exp (C / 2) * Work.FTS.Nonlin.Xn α D := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          exact Real.exp_le_exp.mpr (by nlinarith [(hε k).2, hCpos])
  -- the `max B 0` upgrade
  have hDXn' : Work.FTS.Nonlin.Xn α D ≤ max B 0 * |τ - τ'| :=
    hDXn.trans (mul_le_mul_of_nonneg_right (le_max_left B 0) (abs_nonneg _))
  -- assembly
  have hmain : Work.FTS.Nonlin.Xn α (Pz (Jeps ρ (ε k) f) - Pz (Jeps ρ (ε k) f'))
      ≤ A * Real.exp (C / 2) * (max B 0 * |τ - τ'|) := by
    calc Work.FTS.Nonlin.Xn α (Pz (Jeps ρ (ε k) f) - Pz (Jeps ρ (ε k) f'))
        = Work.FTS.Nonlin.Xn α (Pz (Jeps ρ (ε k) D)) := by rw [hPz]
      _ ≤ A * Work.FTS.Nonlin.Xn α (Jeps ρ (ε k) D) := hPzb
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
        slice (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) τ z θ
          - slice (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) τ' z θ)
      = Work.FTS.Nonlin.Xn α (Pz (Jeps ρ (ε k) f) - Pz (Jeps ρ (ε k) f')) := by
    rw [hfdef, hf'def]
    rfl
  rw [hgoal]
  exact hmain.trans hfin

end Work.FTS.StrongEps.E5G
