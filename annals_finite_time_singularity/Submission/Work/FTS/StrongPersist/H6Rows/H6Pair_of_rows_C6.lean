import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.H6Rows.AK6Row
import Submission.Work.FTS.StrongPersist.H6Rows.NstarRow
import Submission.Work.FTS.StrongPersist.H6Rows.ScalarRows
import Submission.Work.FTS.StrongPersist.H6Rows.RowAux
import Submission.Work.FTS.StrongPersist.IP6AddFin
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.HkAddFin
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.assembly
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.assembly_core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows

open Work.FTS.Galerkin (Fn Fam slice dynRHS)
open Work.FTS.StrongPersist.H6Pair6Aux

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Elementary helpers for the constant bookkeeping -/

/-- `√x ≤ 1 + x` for `x ≥ 0`. -/
theorem sqrt_le_one_add_c6 {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ 1 + x := by
  have h1 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  have h2 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  nlinarith [h1, h2, sq_nonneg (Real.sqrt x - 1)]

/-- Inflate a product by a factor `≥ 1`: `a·b ≤ a·c·b`. -/
theorem mul_le_mul_insert_one_c6 {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 1 ≤ c) :
    a * b ≤ a * c * b := by
  have h := mul_le_mul_of_nonneg_right hc ha
  calc a * b = (1 * a) * b := by ring
    _ ≤ (c * a) * b := mul_le_mul_of_nonneg_right h hb
    _ = a * c * b := by ring

/-- The two scalar shapes of the row right-hand sides agree:
`ScalRHS · (1 + Sq6) = RowRHS`. -/
theorem ScalRHS_mul_eq_RowRHS_c6 (α M Ce Cs : ℝ) (f : Fn) :
    ScalRHS α M Ce Cs * (1 + Sq6 α f) = RowRHS α M Ce Cs f := by
  rw [ScalRHS, RowRHS]

/-- `(1 + |Ce| + |Cs|)^4 ≥ 1`. -/
theorem one_le_Cpow_c6 (Ce Cs : ℝ) : (1 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 :=
  one_le_pow₀ (by have h1 := abs_nonneg Ce; have h2 := abs_nonneg Cs; linarith)

/-- The row shape `K (1+|Ce|+|Cs|)^4 α^{-10} (1+M)^4` is `K · ScalRHS`. -/
theorem scalRow_eq_c6 (K α M Ce Cs : ℝ) :
    K * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4
      = K * ScalRHS α M Ce Cs := by
  rw [ScalRHS]; ring

/-- `α^{-10}` is nonnegative for `α > 0`. -/
theorem rpow_neg_ten_nonneg_c6 {α : ℝ} (hα : 0 < α) : (0 : ℝ) ≤ α ^ (-(10 : ℝ)) :=
  Real.rpow_nonneg hα.le _

/-! ## The finite-smoothness splitting of the pairing

`IP6_split4` of `H6Pair6Aux.assembly_core` splits the pairing over a four-fold sum, but asks for
`SmoothOpen` (i.e. `C^∞`) of the four summands.  The rows of the `C⁶` version of the assembly
supply only `ContDiffOn ℝ 6`, which is exactly what the finite-order additivity `IP6AddFin`
consumes; the only extra input is the `ℋ⁶`-membership of the *partial* sums, which is
`HkAddFin` (closure of `ℋ⁶` under addition at finite smoothness). -/

/-- **`IP6 1 … 1` splits over a four-fold sum, at finite smoothness.** -/
theorem IP6_split4_fin {α : ℝ} (hα : 0 < α) {u₁ u₂ u₃ u₄ v : Fn}
    (hs₁ : ContDiffOn ℝ 6 (Function.uncurry u₁) Work.FTS.EllipticEst.Q0)
    (hs₂ : ContDiffOn ℝ 6 (Function.uncurry u₂) Work.FTS.EllipticEst.Q0)
    (hs₃ : ContDiffOn ℝ 6 (Function.uncurry u₃) Work.FTS.EllipticEst.Q0)
    (hs₄ : ContDiffOn ℝ 6 (Function.uncurry u₄) Work.FTS.EllipticEst.Q0)
    (hv : ContDiffOn ℝ 6 (Function.uncurry v) Work.FTS.EllipticEst.Q0)
    (hm₁ : Work.Spaces.HkMem α 6 u₁) (hm₂ : Work.Spaces.HkMem α 6 u₂)
    (hm₃ : Work.Spaces.HkMem α 6 u₃) (hm₄ : Work.Spaces.HkMem α 6 u₄)
    (hmv : Work.Spaces.HkMem α 6 v) :
    Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
        (fun z θ => u₁ z θ + u₂ z θ + u₃ z θ + u₄ z θ) v
      = Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α u₁ v
        + Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α u₂ v
        + Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α u₃ v
        + Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α u₄ v := by
  have hs₁₂ : ContDiffOn ℝ 6 (Function.uncurry (fun z θ => u₁ z θ + u₂ z θ))
      Work.FTS.EllipticEst.Q0 := by
    have h : Function.uncurry (fun z θ => u₁ z θ + u₂ z θ)
        = fun p : ℝ × ℝ => Function.uncurry u₁ p + Function.uncurry u₂ p := rfl
    rw [h]
    exact hs₁.add hs₂
  have hs₁₂₃ : ContDiffOn ℝ 6 (Function.uncurry (fun z θ => (u₁ z θ + u₂ z θ) + u₃ z θ))
      Work.FTS.EllipticEst.Q0 := by
    have h : Function.uncurry (fun z θ => (u₁ z θ + u₂ z θ) + u₃ z θ)
        = fun p : ℝ × ℝ => Function.uncurry (fun z θ => u₁ z θ + u₂ z θ) p
            + Function.uncurry u₃ p := rfl
    rw [h]
    exact hs₁₂.add hs₃
  have hm₁₂ : Work.Spaces.HkMem α 6 (fun z θ => u₁ z θ + u₂ z θ) :=
    (HkAddFin (k := 6) hs₁ hs₂ hm₁ hm₂).1
  have hm₁₂₃ : Work.Spaces.HkMem α 6 (fun z θ => (u₁ z θ + u₂ z θ) + u₃ z θ) :=
    (HkAddFin (k := 6) hs₁₂ hs₃ hm₁₂ hm₃).1
  rw [IP6AddFin (u := fun z θ => (u₁ z θ + u₂ z θ) + u₃ z θ) (v := u₄) (w := v)
      hα hs₁₂₃ hs₄ hv hm₁₂₃ hm₄ hmv,
    IP6AddFin (u := fun z θ => u₁ z θ + u₂ z θ) (v := u₃) (w := v)
      hα hs₁₂ hs₃ hv hm₁₂ hm₃ hmv,
    IP6AddFin (u := u₁) (v := u₂) (w := v) hα hs₁ hs₂ hv hm₁ hm₂ hmv]

/-! ## The assembly of `H6Pair` from the four rows, with the `C⁶` hypothesis

`dynRHS = -μ̄·AK + N₀ + N + N_*`, and the rows bound each of the four summands.  The only
smoothness input that the argument needs beyond `L6Ctx` is `C⁶`-smoothness of `N₀` and of `N`
(the two pieces the elliptic solver produces, available from `HkMem α 7 f` by
`EllipticEst.UopHk.contDiffOn_L12_k`); the pieces `-μ̄·AK` and `N_*` are `C^∞` on the open
quadrant, and the profile `f = slice g τ` is `SmoothOpen` by `H6Adm`. -/
theorem H6Pair_of_rows_C6 {Ce : ℝ} (hCe : 0 < Ce)
    (hN0 : ∃ K α₂ : ℝ, 0 < K ∧ 0 < α₂ ∧ α₂ ≤ 1 ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
        Work.FTS.StrongPersist.H6Adm α f → Work.Spaces.HkMem α 7 f → Work.FTS.Nonlin.Xn α f ≤ M →
        Work.Spaces.HkMem α 6
            (Work.Construction.N0 α (fun z θ => Work.Construction.Fstar α z θ + f z θ) f) ∧
        |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
            (Work.Construction.N0 α (fun z θ => Work.Construction.Fstar α z θ + f z θ) f) f|
          ≤ K * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Work.FTS.StrongPersist.Sq6 α f))
    (hN : ∃ K α₂ : ℝ, 0 < K ∧ 0 < α₂ ∧ α₂ ≤ 1 ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ (g Φ : Work.FTS.Galerkin.Fam) (τ M Cs : ℝ) (E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn) (Φs : Work.FTS.Galerkin.Fn), 0 ≤ τ →
        Work.FTS.StrongPersist.L6Ctx (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1) α M Ce Cs E Φs g Φ τ →
        Work.Spaces.HkMem α 6
            (Work.Construction.N α (Work.Construction.Ftau α g τ)
              (Work.FTS.Galerkin.slice Φ τ)) ∧
        |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
            (Work.Construction.N α (Work.Construction.Ftau α g τ)
              (Work.FTS.Galerkin.slice Φ τ)) (Work.FTS.Galerkin.slice g τ)|
          ≤ K * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4
              * (1 + Work.FTS.StrongPersist.Sq6 α (Work.FTS.Galerkin.slice g τ)))
    (hS : ∃ K α₂ : ℝ, 0 < K ∧ 0 < α₂ ∧ α₂ ≤ 1 ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ (g Φ : Work.FTS.Galerkin.Fam) (τ M Cs : ℝ) (E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn) (Φs : Work.FTS.Galerkin.Fn), 0 ≤ τ →
        Work.FTS.StrongPersist.L6Ctx (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1) α M Ce Cs E Φs g Φ τ →
        |Work.FTS.Galerkin.muDyn α Φ g τ|
            ≤ K * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 ∧
        |Work.Construction.mubar
            (Work.Construction.N0 α (Work.Construction.Ftau α g τ)
              (Work.FTS.Galerkin.slice g τ))
            (Work.Construction.N α (Work.Construction.Ftau α g τ)
              (Work.FTS.Galerkin.slice Φ τ))|
          ≤ K * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4)
    (hN0c : ∃ α₂ : ℝ, 0 < α₂ ∧ α₂ ≤ 1 ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ (g Φ : Work.FTS.Galerkin.Fam) (τ M Cs : ℝ) (E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn) (Φs : Work.FTS.Galerkin.Fn), 0 ≤ τ →
        Work.FTS.StrongPersist.L6Ctx (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1) α M Ce Cs E Φs g Φ τ →
        ContDiffOn ℝ 6 (Function.uncurry
            (Work.Construction.N0 α (Work.Construction.Ftau α g τ)
              (Work.FTS.Galerkin.slice g τ))) Work.FTS.EllipticEst.Q0 ∧
        ContDiffOn ℝ 6 (Function.uncurry
            (Work.Construction.N α (Work.Construction.Ftau α g τ)
              (Work.FTS.Galerkin.slice Φ τ))) Work.FTS.EllipticEst.Q0) :
    ∃ α₂ Cp : ℝ, 0 < Cp ∧ 0 < α₂ ∧
      Work.FTS.StrongPersist.H6Pair (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1) α₂ Ce Cp := by
  obtain ⟨K0r, α0r, hK0r, hα0r, _hα0rle, hN0r⟩ := hN0
  obtain ⟨KNr, αNr, hKNr, hαNr, _hαNrle, hNr⟩ := hN
  obtain ⟨KSr, αSr, hKSr, hαSr, _hαSrle, hSr⟩ := hS
  obtain ⟨αSm, hαSm, _hαSmle, hSmr⟩ := hN0c
  obtain ⟨KAK6, hKAK60, hAK6b⟩ := Work.FTS.StrongPersist.AK6_mem_norm
  obtain ⟨CC6, hCC60, hCS6⟩ :=
    Work.FTS.StrongPersist.IP6_cs_coeffs 1 1 1 1 1 1 1 1 1 1 1 one_pos
  obtain ⟨Cns, αns, hCns0, hαns0, hnsb⟩ := Work.FTS.StrongPersist.nstar_pair_le
  -- the two output constants
  set A2 : ℝ := min (min (min (min α0r αNr) (min αSr αSm)) αns) 1 with hA2def
  set Cp : ℝ :=
    2 * ((CC6 * KAK6) * KSr + K0r + KNr + 2 * (Cns * KSr)) + 1 with hCpdef
  have hA20 : 0 < A2 := by
    rw [hA2def]
    exact lt_min (lt_min (lt_min (lt_min hα0r hαNr) (lt_min hαSr hαSm)) hαns0) one_pos
  have hA21 : A2 ≤ 1 := by rw [hA2def]; exact min_le_right _ _
  have hA2a : A2 ≤ min (min (min α0r αNr) (min αSr αSm)) αns := by
    rw [hA2def]; exact min_le_left _ _
  have hA2b : min (min (min α0r αNr) (min αSr αSm)) αns
      ≤ min (min α0r αNr) (min αSr αSm) := min_le_left _ _
  have hA2c : min (min α0r αNr) (min αSr αSm) ≤ min α0r αNr := min_le_left _ _
  have hA2d : min (min α0r αNr) (min αSr αSm) ≤ min αSr αSm := min_le_right _ _
  have hA2e : A2 ≤ αns := le_trans hA2a (min_le_right _ _)
  have hA2f : A2 ≤ α0r := le_trans hA2a (le_trans hA2b (le_trans hA2c (min_le_left _ _)))
  have hA2g : A2 ≤ αNr := le_trans hA2a (le_trans hA2b (le_trans hA2c (min_le_right _ _)))
  have hA2h : A2 ≤ αSr := le_trans hA2a (le_trans hA2b (le_trans hA2d (min_le_left _ _)))
  have hA2i : A2 ≤ αSm := le_trans hA2a (le_trans hA2b (le_trans hA2d (min_le_right _ _)))
  have hCp0 : 0 < Cp := by
    rw [hCpdef]
    have h1 : 0 < (CC6 * KAK6) * KSr := mul_pos (mul_pos hCC60 hKAK60) hKSr
    have h2 : 0 < Cns * KSr := mul_pos hCns0 hKSr
    linarith
  have hCs : (CC6 * KAK6) * KSr + K0r + KNr + 2 * (Cns * KSr) ≤ Cp := by
    rw [hCpdef]
    have h0 : 0 ≤ (CC6 * KAK6) * KSr + K0r + KNr + 2 * (Cns * KSr) := by
      have h1 : 0 < (CC6 * KAK6) * KSr := mul_pos (mul_pos hCC60 hKAK60) hKSr
      have h2 : 0 < Cns * KSr := mul_pos hCns0 hKSr
      linarith
    linarith
  refine ⟨A2, Cp, hCp0, hA20, ⟨⟨hCp0, hA20⟩, ?_⟩⟩
  rintro α hα g Φ τ M Cs E Φs hτ hctx
  have hαpos : 0 < α := hα.1
  have hαA2 : α ≤ A2 := hα.2
  have hα1' : α ≤ 1 := le_trans hαA2 hA21
  have hα0r' : α ∈ Set.Ioc 0 α0r := ⟨hαpos, le_trans hαA2 hA2f⟩
  have hαNr' : α ∈ Set.Ioc 0 αNr := ⟨hαpos, le_trans hαA2 hA2g⟩
  have hαSr' : α ∈ Set.Ioc 0 αSr := ⟨hαpos, le_trans hαA2 hA2h⟩
  have hαSm' : α ∈ Set.Ioc 0 αSm := ⟨hαpos, le_trans hαA2 hA2i⟩
  have hαns' : α ∈ Set.Ioc 0 αns := ⟨hαpos, le_trans hαA2 hA2e⟩
  -- the abbreviations of the statement
  set f : Fn := slice g τ with hf
  set Ψ : Fn := slice Φ τ with hΨ
  set F : Fn := Work.Construction.Ftau α g τ with hF
  set μbar : ℝ :=
    Work.Construction.mubar (Work.Construction.N0 α F f) (Work.Construction.N α F Ψ) with hμbar
  set μ : ℝ := Work.FTS.Galerkin.muDyn α Φ g τ with hμdef
  set lam : ℝ := Work.FTS.Galerkin.lamDyn α Φ g τ with hlamdef
  set p1 : Fn := Work.FTS.StrongPersist.H6Pair6Aux.P1 α g Φ τ with hp1
  set p2 : Fn := Work.FTS.StrongPersist.H6Pair6Aux.P2 α g τ with hp2
  set p3 : Fn := Work.FTS.StrongPersist.H6Pair6Aux.P3 α g Φ τ with hp3
  set p4 : Fn := Work.FTS.StrongPersist.H6Pair6Aux.P4 α Φ g τ with hp4
  -- the interface data
  have hreg : Work.FTS.StrongPersist.H6Adm α f := hctx.hreg
  have h7 : Work.Spaces.HkMem α 7 f := hctx.h7
  have hbdM : Work.FTS.Nonlin.Xn α f ≤ M := hctx.hbdd
  have h6 : Work.Spaces.HkMem α 6 f := hreg.reg.2
  have hsmf : Work.FTS.EllipticEst.SmoothOpen f := hreg.reg.1
  have hQof : Work.FTS.VocabO.HQo α 6 f := ⟨hsmf, h6⟩
  have hSq0 : 0 ≤ Sq6 α f := Work.FTS.StrongPersist.Sq6_nonneg α f
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hbdM
  -- smoothness and `ℋ⁶`-membership of the four summands
  have hsm23 := hSmr α hαSm' g Φ τ M Cs E Φs hτ hctx
  have hs1 : Work.FTS.EllipticEst.SmoothOpen p1 :=
    smoothOpen_const_mul_loc (-μbar) (Work.FTS.StrongPersist.AK_smoothO α)
  have hm1 : Work.Spaces.HkMem α 6 p1 :=
    Work.FTS.LocData.HkMem_const_mul α 6 (-μbar) (hAK6b α hαpos hα1').1
  have hs2 : ContDiffOn ℝ 6 (Function.uncurry p2) Work.FTS.EllipticEst.Q0 := hsm23.1
  have hm2 : Work.Spaces.HkMem α 6 p2 := (hN0r α hα0r' f M hreg h7 hbdM).1
  have hs3 : ContDiffOn ℝ 6 (Function.uncurry p3) Work.FTS.EllipticEst.Q0 := hsm23.2
  have hm3 : Work.Spaces.HkMem α 6 p3 := (hNr α hαNr' g Φ τ M Cs E Φs hτ hctx).1
  have hs4 : Work.FTS.EllipticEst.SmoothOpen p4 :=
    (P4_smooth_mem hsmf h6 h7).1
  have hm4 : Work.Spaces.HkMem α 6 p4 := (P4_smooth_mem hsmf h6 h7).2
  -- the decomposition `dynRHS = p1 + p2 + p3 + p4`
  have hdec : dynRHS α Φ g τ = fun z θ => p1 z θ + p2 z θ + p3 z θ + p4 z θ := by
    rw [dynRHS_eq_sum]
  have hsplit_eq : Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α (dynRHS α Φ g τ) f
      = Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p1 f
        + Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p2 f
        + Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p3 f
        + Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p4 f := by
    rw [hdec]
    exact IP6_split4_fin (α := α) (u₁ := p1) (u₂ := p2) (u₃ := p3) (u₄ := p4) (v := f)
      hαpos (hs1.forall 6) hs2 hs3 (hs4.forall 6) (hsmf.forall 6) hm1 hm2 hm3 hm4 h6
  have htri : |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α (dynRHS α Φ g τ) f|
      ≤ |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p1 f|
        + |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p2 f|
        + |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p3 f|
        + |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p4 f| := by
    rw [hsplit_eq]
    have h1 := abs_add_le
      (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p1 f
        + Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p2 f
        + Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p3 f)
      (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p4 f)
    have h2 := abs_add_le
      (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p1 f
        + Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p2 f)
      (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p3 f)
    have h3 := abs_add_le (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p1 f)
      (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p2 f)
    linarith
  -- the scalar bounds of the rows
  have hμbarbd : |μbar| ≤ KSr * ScalRHS α M Ce Cs := by
    have h := (hSr α hαSr' g Φ τ M Cs E Φs hτ hctx).2
    calc |μbar| ≤ KSr * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 := h
      _ = KSr * ScalRHS α M Ce Cs := scalRow_eq_c6 KSr α M Ce Cs
  have hμbd : |μ| ≤ KSr * ScalRHS α M Ce Cs := by
    have h := (hSr α hαSr' g Φ τ M Cs E Φs hτ hctx).1
    calc |μ| ≤ KSr * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 := h
      _ = KSr * ScalRHS α M Ce Cs := scalRow_eq_c6 KSr α M Ce Cs
  have hlamid : |μ + lam + μ * lam| = |μ| :=
    Work.FTS.StrongPersist.H6Pair6Aux.abs_add_lamfun μ
  have hbc : |μ| + |μ + lam + μ * lam| = 2 * |μ| := by
    rw [hlamid]; ring
  -- the four pairing bounds, all with the `RowRHS`-shape
  have hb1 : |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p1 f|
      ≤ (CC6 * KAK6 * KSr) * RowRHS α M Ce Cs f := by
    have hcs := hCS6 α ⟨hαpos, hα1'⟩ p1 f ⟨hs1, hm1⟩ hQof
    have hXn1 : Xn6 α p1 ≤ |μbar| * KAK6 := by
      have hk : Work.Spaces.HkNorm α 6 (fun z θ => -μbar * Work.Construction.AK α z θ)
          = |μbar| * Work.Spaces.HkNorm α 6 (Work.Construction.AK α) := by
        have h0 := Work.FTS.EllipticEst.HkNorm_const_mul α 6 (-μbar)
          (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall
            (fun z θ => Work.Construction.AK α z θ)).mp
              (Work.FTS.StrongPersist.AK_smoothO α) n)
        rw [abs_neg] at h0
        exact h0
      calc Xn6 α p1
          = Work.Spaces.HkNorm α 6 (fun z θ => -μbar * Work.Construction.AK α z θ) := rfl
        _ = |μbar| * Work.Spaces.HkNorm α 6 (Work.Construction.AK α) := hk
        _ ≤ |μbar| * KAK6 :=
            mul_le_mul_of_nonneg_left (hAK6b α hαpos hα1').2 (abs_nonneg μbar)
    have hXn6f : Xn6 α f ≤ 1 + Sq6 α f := sqrt_le_one_add_c6 hSq0
    have hstep1 : |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p1 f|
        ≤ CC6 * (|μbar| * KAK6) * (1 + Sq6 α f) := by
      calc |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p1 f|
          ≤ CC6 * Xn6 α p1 * Xn6 α f := hcs
        _ ≤ CC6 * (|μbar| * KAK6) * (1 + Sq6 α f) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hXn1 hCC60.le) hXn6f
              (Work.Spaces.HkNorm_nonneg α 6 f) ?_
            exact mul_nonneg hCC60.le (mul_nonneg (abs_nonneg μbar) hKAK60.le)
    have hmu : CC6 * (|μbar| * KAK6) ≤ (CC6 * KAK6 * KSr) * ScalRHS α M Ce Cs := by
      calc CC6 * (|μbar| * KAK6) ≤ CC6 * ((KSr * ScalRHS α M Ce Cs) * KAK6) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hμbarbd hKAK60.le) hCC60.le
        _ = (CC6 * KAK6 * KSr) * ScalRHS α M Ce Cs := by ring
    have hstep2 : CC6 * (|μbar| * KAK6) * (1 + Sq6 α f)
        ≤ (CC6 * KAK6 * KSr) * RowRHS α M Ce Cs f := by
      rw [← ScalRHS_mul_eq_RowRHS_c6]
      calc CC6 * (|μbar| * KAK6) * (1 + Sq6 α f)
          ≤ ((CC6 * KAK6 * KSr) * ScalRHS α M Ce Cs) * (1 + Sq6 α f) :=
            mul_le_mul_of_nonneg_right hmu (by linarith [hSq0])
        _ = (CC6 * KAK6 * KSr) * (ScalRHS α M Ce Cs * (1 + Sq6 α f)) := by ring
    exact le_trans hstep1 hstep2
  have hb2 : |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p2 f|
      ≤ K0r * RowRHS α M Ce Cs f := by
    have h' : |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p2 f|
        ≤ K0r * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f) :=
      (hN0r α hα0r' f M hreg h7 hbdM).2
    rw [← ScalRHS_mul_eq_RowRHS_c6]
    have hb : (0 : ℝ) ≤ α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f) :=
      mul_nonneg (mul_nonneg (rpow_neg_ten_nonneg_c6 hαpos) (by positivity)) (by linarith [hSq0])
    have h1 : K0r * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f)
        = K0r * (α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f)) := by ring
    have h1' : K0r * (α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f))
        ≤ K0r * (1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f)) :=
      mul_le_mul_insert_one_c6 hK0r.le hb (one_le_Cpow_c6 Ce Cs)
    have h2 : K0r * (1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f))
        = K0r * (ScalRHS α M Ce Cs * (1 + Sq6 α f)) := by
      rw [ScalRHS]; ring
    linarith [h', h1.le, h1.ge, h1', h2.le, h2.ge]
  have hb3 : |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p3 f|
      ≤ KNr * RowRHS α M Ce Cs f := by
    have h' : |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p3 f|
        ≤ KNr * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f) :=
      (hNr α hαNr' g Φ τ M Cs E Φs hτ hctx).2
    rw [← ScalRHS_mul_eq_RowRHS_c6]
    have h1 : KNr * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f)
        = KNr * (ScalRHS α M Ce Cs * (1 + Sq6 α f)) := by
      rw [ScalRHS]; ring
    rw [h1] at h'
    exact h'
  have hb4 : |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p4 f|
      ≤ (2 * (Cns * KSr)) * RowRHS α M Ce Cs f := by
    have h' : |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p4 f|
        ≤ Cns * (|μ| + |μ + lam + μ * lam|) * Sq6 α f :=
      hnsb α hαns' μ lam f hQof h7
    rw [hbc] at h'
    rw [← ScalRHS_mul_eq_RowRHS_c6]
    have hμ2 : 2 * |μ| ≤ 2 * (KSr * ScalRHS α M Ce Cs) :=
      mul_le_mul_of_nonneg_left hμbd (by norm_num)
    have hstep : Cns * (2 * |μ|) * Sq6 α f
        ≤ (2 * (Cns * KSr)) * (ScalRHS α M Ce Cs * (1 + Sq6 α f)) := by
      calc Cns * (2 * |μ|) * Sq6 α f
          ≤ Cns * (2 * (KSr * ScalRHS α M Ce Cs)) * Sq6 α f :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hμ2 hCns0.le) hSq0
        _ = (2 * (Cns * KSr)) * (ScalRHS α M Ce Cs * Sq6 α f) := by ring
        _ ≤ (2 * (Cns * KSr)) * (ScalRHS α M Ce Cs * (1 + Sq6 α f)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (by linarith [hSq0]) (ScalRHS_nonneg hαpos))
              (by have h := mul_pos hCns0 hKSr; linarith)
    exact le_trans h' hstep
  -- the four bounds combine
  have hsum : |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p1 f|
        + |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p2 f|
        + |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p3 f|
        + |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p4 f|
      ≤ ((CC6 * KAK6) * KSr + K0r + KNr + 2 * (Cns * KSr)) * RowRHS α M Ce Cs f := by
    have h12 := add_le_add hb1 hb2
    have h123 := add_le_add h12 hb3
    have h1234 := add_le_add h123 hb4
    calc |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p1 f|
          + |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p2 f|
          + |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p3 f|
          + |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p4 f|
        ≤ (CC6 * KAK6 * KSr) * RowRHS α M Ce Cs f + K0r * RowRHS α M Ce Cs f
          + KNr * RowRHS α M Ce Cs f + (2 * (Cns * KSr)) * RowRHS α M Ce Cs f := h1234
      _ = ((CC6 * KAK6) * KSr + K0r + KNr + 2 * (Cns * KSr)) * RowRHS α M Ce Cs f := by ring
  -- assemble
  calc |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α (dynRHS α Φ g τ) f|
      ≤ |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p1 f|
        + |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p2 f|
        + |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p3 f|
        + |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p4 f| := htri
    _ ≤ ((CC6 * KAK6) * KSr + K0r + KNr + 2 * (Cns * KSr)) * RowRHS α M Ce Cs f := hsum
    _ ≤ Cp * RowRHS α M Ce Cs f :=
        mul_le_mul_of_nonneg_right hCs (RowRHS_nonneg (f := f) hαpos)
    _ = Cp * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f) := by
        rw [← ScalRHS_mul_eq_RowRHS_c6, ScalRHS]; ring

end Work.FTS.StrongPersist.H6Rows
