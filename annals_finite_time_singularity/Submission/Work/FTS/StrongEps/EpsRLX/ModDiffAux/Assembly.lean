import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Construction.MufunS
import Submission.Work.FTS.GalFields.Defs
import Submission.Work.FTS.GalFields.RHS.sharpN0_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ModDiffAux/Assembly` — the assembly of `ModDiffClassC` from the three `L₁₂`-differences

The two modulation constants are, by definition (`Construction/Defs.lean`,
`Construction/MufunS.lean`),

  `μ̄ = L₁₂(N₀)(0) + L₁₂(N)(0)`,
  `μ  = (1/(2α))·(L₁₂(N₀)(0) + L₁₂(N)(0) + L₁₂(3 D_θ g/(1+z))(0))`,

so the difference of the two constants at `W₁`, `W₂` is the explicit linear combination of the
three `L₁₂`-zero-mode differences `ΔN₀`, `ΔN`, `ΔT`.  `modDiff_of_L12_bounds` is the assembly: it
takes the three *bounds* (linear in `|W₁−W₂|_{ℋ⁵}`, with constants `K₀, K_N, K_T`) and produces the
two clauses of `ModDiffClassC` with the constant
`K := max ((1/(2α))·(K₀+K_N+K_T)) (K₀+K_N) + 1`.

The three bounds themselves are supplied by `ModDiffAux.L12N0DiffClassC`,
`ModDiffAux.L12NDiffClassC` and `ModDiffAux.L12_transport_diff_classC`. -/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.ModDiffAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **The assembly of the two modulation-difference bounds from the three `L₁₂`-difference
bounds** (all three of the shape `K·(1 + |W₁|_{ℋ⁵} + |W₂|_{ℋ⁵})·|W₁−W₂|_{ℋ⁵}`). -/
theorem modDiff_of_L12_bounds {α : ℝ} (hα : α ∈ Set.Ioc 0 1)
    {Ce Cs : ℝ} {Φs : Fn} {E : Fn → Fn}
    {K0 KN KT : ℝ} (hK0 : 0 < K0) (hKN : 0 < KN) (hKT : 0 < KT)
    (h0 : ∀ {W₁ W₂ : Fn}, Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ →
      |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁) 0
        - Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂) 0|
        ≤ K0 * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ))
    (hN : ∀ {W₁ W₂ : Fn}, Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ →
      |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₁)
          (fun z θ => Φs z θ + E W₁ z θ)) 0
        - Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₂)
          (fun z θ => Φs z θ + E W₂ z θ)) 0|
        ≤ KN * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ))
    (hT : ∀ {W₁ W₂ : Fn}, Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ →
      |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₁ z θ / (1 + z)) 0
        - Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₂ z θ / (1 + z)) 0|
        ≤ KT * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ {W₁ W₂ : Fn},
      Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ →
      |Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁)
          (Work.Construction.N α (Work.Construction.Ftot α W₁)
            (fun z θ => Φs z θ + E W₁ z θ)) W₁
        - Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂)
          (Work.Construction.N α (Work.Construction.Ftot α W₂)
            (fun z θ => Φs z θ + E W₂ z θ)) W₂|
        ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) ∧
      |Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁)
          (Work.Construction.N α (Work.Construction.Ftot α W₁)
            (fun z θ => Φs z θ + E W₁ z θ))
        - Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂)
          (Work.Construction.N α (Work.Construction.Ftot α W₂)
            (fun z θ => Φs z θ + E W₂ z θ))|
        ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
  have hα0 : 0 < α := hα.1
  have hfac : (0 : ℝ) < 1 / (2 * α) := by positivity
  refine ⟨max ((1 / (2 * α)) * (K0 + KN + KT)) (K0 + KN) + 1, by
    have h1 : 0 ≤ max ((1 / (2 * α)) * (K0 + KN + KT)) (K0 + KN) := by
      refine le_max_of_le_left ?_
      exact mul_nonneg hfac.le (by linarith)
    linarith, ?_⟩
  intro W₁ W₂ h₁ h₂
  have hb0 := h0 h₁ h₂
  have hbN := hN h₁ h₂
  have hbT := hT h₁ h₂
  set T : ℝ := (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
      * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) with hTdef
  have hT0 : 0 ≤ T := by
    rw [hTdef]
    refine mul_nonneg (by linarith [Work.Spaces.HkNorm_nonneg α 5 W₁,
      Work.Spaces.HkNorm_nonneg α 5 W₂]) ?_
    exact Work.Spaces.HkNorm_nonneg α 5 _
  have hb0' : |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁) 0
      - Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂) 0|
      ≤ K0 * T := by
    have h : K0 * T = K0 * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
        * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by rw [hTdef]; ring
    rw [h]; exact hb0
  have hbN' : |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₁)
        (fun z θ => Φs z θ + E W₁ z θ)) 0
      - Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₂)
        (fun z θ => Φs z θ + E W₂ z θ)) 0| ≤ KN * T := by
    have h : KN * T = KN * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
        * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by rw [hTdef]; ring
    rw [h]; exact hbN
  have hbT' : |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₁ z θ / (1 + z)) 0
      - Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₂ z θ / (1 + z)) 0|
      ≤ KT * T := by
    have h : KT * T = KT * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
        * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by rw [hTdef]; ring
    rw [h]; exact hbT
  have hbarid : Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁)
        (Work.Construction.N α (Work.Construction.Ftot α W₁)
          (fun z θ => Φs z θ + E W₁ z θ))
      - Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂)
        (Work.Construction.N α (Work.Construction.Ftot α W₂)
          (fun z θ => Φs z θ + E W₂ z θ))
      = (Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁) 0
          - Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂) 0)
        + (Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₁)
            (fun z θ => Φs z θ + E W₁ z θ)) 0
          - Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₂)
            (fun z θ => Φs z θ + E W₂ z θ)) 0) := by
    simp only [Work.Construction.mubar]
    ring
  have hmuid : Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁)
        (Work.Construction.N α (Work.Construction.Ftot α W₁)
          (fun z θ => Φs z θ + E W₁ z θ)) W₁
      - Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂)
        (Work.Construction.N α (Work.Construction.Ftot α W₂)
          (fun z θ => Φs z θ + E W₂ z θ)) W₂
      = (1 / (2 * α))
        * ((Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁) 0
            - Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂) 0)
          + (Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₁)
              (fun z θ => Φs z θ + E W₁ z θ)) 0
            - Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₂)
              (fun z θ => Φs z θ + E W₂ z θ)) 0)
          + (Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₁ z θ / (1 + z)) 0
            - Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₂ z θ / (1 + z)) 0)) := by
    simp only [Work.Construction.mufunS]
    ring
  have hsum0 : |(Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁) 0
        - Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂) 0)
      + (Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₁)
          (fun z θ => Φs z θ + E W₁ z θ)) 0
        - Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₂)
          (fun z θ => Φs z θ + E W₂ z θ)) 0)
      + (Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₁ z θ / (1 + z)) 0
        - Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₂ z θ / (1 + z)) 0)|
      ≤ (K0 + KN + KT) * T := by
    have h1 := abs_add_le
      ((Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁) 0
          - Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂) 0)
        + (Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₁)
          (fun z θ => Φs z θ + E W₁ z θ)) 0
          - Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₂)
            (fun z θ => Φs z θ + E W₂ z θ)) 0))
      (Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₁ z θ / (1 + z)) 0
        - Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₂ z θ / (1 + z)) 0)
    have h2 := abs_add_le
      (Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁) 0
        - Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂) 0)
      (Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₁)
        (fun z θ => Φs z θ + E W₁ z θ)) 0
        - Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₂)
          (fun z θ => Φs z θ + E W₂ z θ)) 0)
    linarith
  have hsumN : |(Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁) 0
        - Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂) 0)
      + (Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₁)
          (fun z θ => Φs z θ + E W₁ z θ)) 0
        - Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₂)
          (fun z θ => Φs z θ + E W₂ z θ)) 0)| ≤ (K0 + KN) * T := by
    have h2 := abs_add_le
      (Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁) 0
        - Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂) 0)
      (Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₁)
        (fun z θ => Φs z θ + E W₁ z θ)) 0
        - Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₂)
          (fun z θ => Φs z θ + E W₂ z θ)) 0)
    linarith
  have hKmu : (1 / (2 * α)) * ((K0 + KN + KT) * T)
      ≤ (max ((1 / (2 * α)) * (K0 + KN + KT)) (K0 + KN) + 1) * T := by
    have h1 : (1 / (2 * α)) * (K0 + KN + KT)
        ≤ max ((1 / (2 * α)) * (K0 + KN + KT)) (K0 + KN) + 1 := by
      linarith [le_max_left ((1 / (2 * α)) * (K0 + KN + KT)) (K0 + KN)]
    calc (1 / (2 * α)) * ((K0 + KN + KT) * T)
        = ((1 / (2 * α)) * (K0 + KN + KT)) * T := by ring
      _ ≤ (max ((1 / (2 * α)) * (K0 + KN + KT)) (K0 + KN) + 1) * T :=
          mul_le_mul_of_nonneg_right h1 hT0
  have hKbar : (K0 + KN) * T
      ≤ (max ((1 / (2 * α)) * (K0 + KN + KT)) (K0 + KN) + 1) * T := by
    have h1 : K0 + KN ≤ max ((1 / (2 * α)) * (K0 + KN + KT)) (K0 + KN) + 1 := by
      linarith [le_max_right ((1 / (2 * α)) * (K0 + KN + KT)) (K0 + KN)]
    exact mul_le_mul_of_nonneg_right h1 hT0
  constructor
  · rw [hmuid, abs_mul, abs_of_pos hfac]
    calc (1 / (2 * α)) * |(Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁) 0
          - Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂) 0)
        + (Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₁)
            (fun z θ => Φs z θ + E W₁ z θ)) 0
          - Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₂)
            (fun z θ => Φs z θ + E W₂ z θ)) 0)
        + (Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₁ z θ / (1 + z)) 0
          - Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₂ z θ / (1 + z)) 0)|
        ≤ (1 / (2 * α)) * ((K0 + KN + KT) * T) := mul_le_mul_of_nonneg_left hsum0 hfac.le
      _ ≤ (max ((1 / (2 * α)) * (K0 + KN + KT)) (K0 + KN) + 1) * T := hKmu
      _ = (max ((1 / (2 * α)) * (K0 + KN + KT)) (K0 + KN) + 1)
            * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
          rw [hTdef]; ring
  · rw [hbarid]
    calc |(Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁) 0
          - Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂) 0)
        + (Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₁)
            (fun z θ => Φs z θ + E W₁ z θ)) 0
          - Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₂)
            (fun z θ => Φs z θ + E W₂ z θ)) 0)|
        ≤ (K0 + KN) * T := hsumN
      _ ≤ (max ((1 / (2 * α)) * (K0 + KN + KT)) (K0 + KN) + 1) * T := hKbar
      _ = (max ((1 / (2 * α)) * (K0 + KN + KT)) (K0 + KN) + 1)
            * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
          rw [hTdef]; ring

end Work.FTS.StrongEps.EpsRLX.ModDiffAux
