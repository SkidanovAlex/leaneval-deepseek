import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.H6Row6.Lift
import Submission.Work.FTS.StrongPersist.ResidPtOfGo
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.coefData_pert
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.EllipticEst.HkNorm_const_mul
import Submission.Work.FTS.TransportS.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Row6

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open Work.FTS.StrongPersist.H6Pair6Aux.T6Coef (CoefData)

/-! ## Scaling the `CoefTh`/`supAbsO` vocabulary, and the `CoefData` structure

The three perturbed residual fields entering `row6PertData` are the scalar multiples
`2·Rop(Φ̃)`, `-2·(Uop(Φ̃)/sin 2θ)` and `-2α·Vop(Φ̃)` of the fields priced by the level-four
elliptic package `EllPkgGo`.  The lemmas below transport the `CoefData`/`CoefTh` data through
a scalar factor, and are the only place where the scalar bookkeeping happens. -/

/-- `∂_θ` commutes with multiplication by a constant (the unconditional form of `deriv`). -/
theorem r6_pth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pth f z θ := by
  funext z θ
  simp only [Work.Spaces.pth]
  exact deriv_const_mul_field c

/-- `SmoothOpen` is stable under multiplication by a constant. -/
theorem r6_smoothOpen_const_mul (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr (fun n => ?_)
  exact contDiffOn_const.mul ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hf n)

/-- `supAbsO` of a scalar multiple: bound the function pointwise first, then pull the scalar
out. -/
theorem r6_supAbsO_const_mul_le {c : ℝ} {g : ℝ → ℝ → ℝ} {K : ℝ}
    (hK : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |g z θ| ≤ K) :
    Work.FTS.H2.supAbsO (fun z θ => c * g z θ) ≤ |c| * Work.FTS.H2.supAbsO g := by
  refine Work.FTS.H2.supAbsO_le fun z θ hz hθ hθ' => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (Work.FTS.H2.le_supAbsO hz hθ hθ' hK) (abs_nonneg c)

/-- `CoefTh` is subadditive for scalar multiples. -/
theorem r6_coefTh_const_mul_le {l : ℕ} {c : ℝ} {g : ℝ → ℝ → ℝ}
    (hmem : Work.FTS.VocabO.CoefThMem l g) :
    Work.FTS.VocabO.CoefTh l (fun z θ => c * g z θ)
      ≤ |c| * Work.FTS.VocabO.CoefTh l g := by
  unfold Work.FTS.VocabO.CoefTh
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hbi : b + i ≤ l
  · rw [if_pos hbi, if_pos hbi]
    obtain ⟨K, hK⟩ := hmem b i hbi
    rw [r6_pth_const_mul c g,
      Work.FTS.LocData.mixed_const_mul c b i (Work.Spaces.pth g)]
    show Work.FTS.H2.supAbsO (fun z θ => c * Work.Spaces.mixed b i (Work.Spaces.pth g) z θ)
      ≤ |c| * Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth g))
    exact r6_supAbsO_const_mul_le hK
  · rw [if_neg hbi, if_neg hbi, mul_zero]

/-- `CoefThMem` is preserved by multiplication with a constant. -/
theorem r6_coefThMem_const_mul {l : ℕ} {c : ℝ} {g : ℝ → ℝ → ℝ}
    (hmem : Work.FTS.VocabO.CoefThMem l g) :
    Work.FTS.VocabO.CoefThMem l (fun z θ => c * g z θ) := by
  intro b i hbi
  obtain ⟨K, hK⟩ := hmem b i hbi
  refine ⟨|c| * K, fun z θ hz hθ hθ' => ?_⟩
  rw [r6_pth_const_mul c g, Work.FTS.LocData.mixed_const_mul c b i (Work.Spaces.pth g),
    abs_mul]
  exact mul_le_mul_of_nonneg_left (hK z θ hz hθ hθ') (abs_nonneg c)

/-- **`CoefData` of a scalar multiple**: all six fields scale with the factor `|c|`. -/
theorem r6_coefData_const_mul {α c : ℝ} {A : Work.FTS.Galerkin.Fn} {K0 K4 K6 : ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen A)
    (h4 : Work.Spaces.HkMem α 4 A) (h6 : Work.Spaces.HkMem α 6 A)
    (hval : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K0)
    (hn4 : Work.Spaces.HkNorm α 4 A ≤ K4) (hn6 : Work.Spaces.HkNorm α 6 A ≤ K6)
    (hK0 : 0 ≤ K0) (hK4 : 0 ≤ K4) (hK6 : 0 ≤ K6) :
    CoefData α (fun z θ => c * A z θ) (|c| * K0) (|c| * K4) (|c| * K6) := by
  have hc0 : 0 ≤ |c| := abs_nonneg c
  have hco : ∀ n : ℕ, ContDiffOn ℝ (↑n) (Function.uncurry A)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall A).mp hsm
  refine ⟨r6_smoothOpen_const_mul c hsm,
    Work.FTS.LocData.HkMem_const_mul α 4 c h4,
    Work.FTS.LocData.HkMem_const_mul α 6 c h6,
    fun z θ hz hθ hθ' => ?_, ?_, ?_⟩
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hval z θ hz hθ hθ') hc0
  · show Work.Spaces.HkNorm α 4 (fun z θ => c * A z θ) ≤ |c| * K4
    rw [Work.FTS.EllipticEst.HkNorm_const_mul α 4 c hco]
    exact mul_le_mul_of_nonneg_left hn4 hc0
  · show Work.Spaces.HkNorm α 6 (fun z θ => c * A z θ) ≤ |c| * K6
    rw [Work.FTS.EllipticEst.HkNorm_const_mul α 6 c hco]
    exact mul_le_mul_of_nonneg_left hn6 hc0

/-- `CoefData` is monotone in the three constants. -/
theorem r6_coefData_mono {α : ℝ} {A : Work.FTS.Galerkin.Fn} {K0 K4 K6 K0' K4' K6' : ℝ}
    (h : CoefData α A K0 K4 K6) (h0 : K0 ≤ K0') (h4 : K4 ≤ K4') (h6 : K6 ≤ K6') :
    CoefData α A K0' K4' K6' :=
  ⟨h.sm, h.h4, h.h6, fun z θ hz hθ hθ' => le_trans (h.val z θ hz hθ hθ') h0,
    le_trans h.n4 h4, le_trans h.n6 h6⟩

/-! ## The constant arithmetic -/

/-- The `K0`-arithmetic for the scaled slots: `2·a·C·r·Ce·M` is dominated by the flat
`(2C+1)·r·(1+Ce)·(1+M)`. -/
private lemma r6_flatK0 {C r Ce M a : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r) (hCe : 0 ≤ Ce)
    (hM : 0 ≤ M) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    2 * a * C * r * Ce * M ≤ (2 * C + 1) * r * (1 + Ce) * (1 + M) := by
  have hfac1 : 2 * a * C * r ≤ (2 * C + 1) * r := by
    have h2aC : 2 * a * C ≤ 2 * C := by
      have h2a : 2 * a ≤ 2 := by linarith
      exact mul_le_mul_of_nonneg_right h2a hC
    have h1 : (2 * C) * r ≤ (2 * C + 1) * r :=
      mul_le_mul_of_nonneg_right (by linarith) hr
    calc 2 * a * C * r = (2 * a * C) * r := by ring
      _ ≤ (2 * C) * r := mul_le_mul_of_nonneg_right h2aC hr
      _ ≤ (2 * C + 1) * r := h1
  have hfac2 : Ce * M ≤ (1 + Ce) * (1 + M) := by
    have h1 : Ce * M ≤ Ce * (1 + M) := mul_le_mul_of_nonneg_left (by linarith) hCe
    have h2 : Ce * (1 + M) ≤ (1 + Ce) * (1 + M) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  calc 2 * a * C * r * Ce * M = (2 * a * C * r) * (Ce * M) := by ring
    _ ≤ ((2 * C + 1) * r) * ((1 + Ce) * (1 + M)) :=
        mul_le_mul hfac1 hfac2 (mul_nonneg hCe hM) (mul_nonneg (by linarith) hr)
    _ = (2 * C + 1) * r * (1 + Ce) * (1 + M) := by ring

/-- The `K4`-arithmetic, with the `M`-slot. -/
private lemma r6_flatKM {Ce M : ℝ} (hM : 0 ≤ M) :
    2 * (|Ce| * M) ≤ 2 * (1 + |Ce|) * M := by
  have hle : |Ce| * M ≤ (1 + |Ce|) * M :=
    mul_le_mul_of_nonneg_right (by linarith [abs_nonneg Ce]) hM
  calc 2 * (|Ce| * M) ≤ 2 * ((1 + |Ce|) * M) :=
        mul_le_mul_of_nonneg_left hle (by norm_num)
    _ = 2 * (1 + |Ce|) * M := by ring

/-- The `K6`-arithmetic, with the `HkNorm`-slot. -/
private lemma r6_flatKx {Ce x : ℝ} (hx : 0 ≤ x) :
    2 * (|Ce| * x) ≤ 2 * (1 + |Ce|) * x := by
  have hle : |Ce| * x ≤ (1 + |Ce|) * x :=
    mul_le_mul_of_nonneg_right (by linarith [abs_nonneg Ce]) hx
  calc 2 * (|Ce| * x) ≤ 2 * ((1 + |Ce|) * x) :=
        mul_le_mul_of_nonneg_left hle (by norm_num)
    _ = 2 * (1 + |Ce|) * x := by ring

/-- The `CoefTh`-arithmetic for the `V`-slot. -/
private lemma r6_thArith {C r Ce M a : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r) (hCe : 0 ≤ Ce)
    (hM : 0 ≤ M) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    2 * a * (Ce * r * M) ≤ (2 * C + 2) * (1 + Ce) * r * M := by
  have h3 : 0 ≤ Ce * r * M := mul_nonneg (mul_nonneg hCe hr) hM
  have h2a : 2 * a ≤ 2 := by linarith
  have hstep : 2 * a * (Ce * r * M) ≤ 2 * (Ce * r * M) :=
    mul_le_mul_of_nonneg_right h2a h3
  have hrest : 2 * (Ce * r * M) ≤ (2 * C + 2) * (1 + Ce) * r * M := by
    have h1 : (2 : ℝ) * Ce ≤ (2 * C + 2) * (1 + Ce) := by
      have ha : (2 : ℝ) * Ce ≤ 2 * (1 + Ce) := by nlinarith [hCe]
      have hb : (2 : ℝ) * (1 + Ce) ≤ (2 * C + 2) * (1 + Ce) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      linarith
    calc 2 * (Ce * r * M) = (2 * Ce) * (r * M) := by ring
      _ ≤ ((2 * C + 2) * (1 + Ce)) * (r * M) :=
          mul_le_mul_of_nonneg_right h1 (mul_nonneg hr hM)
      _ = (2 * C + 2) * (1 + Ce) * r * M := by ring
  linarith

/-! ## The lemma -/

theorem row6PertData (Ce : ℝ) (hCe : 0 < Ce) : ∃ α₂ C0 C4 C6 C1 : ℝ,
    0 < α₂ ∧ α₂ ≤ 1 ∧ 0 ≤ C0 ∧ 0 ≤ C4 ∧ 0 ≤ C6 ∧ 0 ≤ C1 ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (g Φ : Work.FTS.Galerkin.Fam) (τ M Cs : ℝ)
      (E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn) (Φs : Work.FTS.Galerkin.Fn),
      0 ≤ τ →
      Work.FTS.StrongPersist.L6Ctx (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1)
        α M Ce Cs E Φs g Φ τ →
      (∃ K0 K4 K6 : ℝ, 0 ≤ K0 ∧ 0 ≤ K4 ∧ 0 ≤ K6 ∧
        K0 ≤ C0 * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M) ∧
        K4 ≤ C4 * (1 + |Ce|) * M ∧
        K6 ≤ C6 * (1 + |Ce|) * Work.Spaces.HkNorm α 6 (Work.FTS.Galerkin.slice g τ) ∧
        Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α
          (fun z θ => 2 * Work.Construction.Rop α (Work.Construction.PhiTil α
            (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) z θ) K0 K4 K6) ∧
      (∃ K0 K4 K6 : ℝ, 0 ≤ K0 ∧ 0 ≤ K4 ∧ 0 ≤ K6 ∧
        K0 ≤ C0 * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M) ∧
        K4 ≤ C4 * (1 + |Ce|) * M ∧
        K6 ≤ C6 * (1 + |Ce|) * Work.Spaces.HkNorm α 6 (Work.FTS.Galerkin.slice g τ) ∧
        Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α
          (fun z θ => -2 * (Work.Construction.Uop α (Work.Construction.PhiTil α
            (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) z θ
              / Work.Construction.s2 θ)) K0 K4 K6) ∧
      (∃ K0 K4 K6 : ℝ, 0 ≤ K0 ∧ 0 ≤ K4 ∧ 0 ≤ K6 ∧
        K0 ≤ C0 * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M) ∧
        K4 ≤ C4 * (1 + |Ce|) * M ∧
        K6 ≤ C6 * (1 + |Ce|) * Work.Spaces.HkNorm α 6 (Work.FTS.Galerkin.slice g τ) ∧
        Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α
          (fun z θ => -2 * α * Work.Construction.Vop (Work.Construction.PhiTil α
            (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) z θ) K0 K4 K6) ∧
      Work.FTS.VocabO.CoefThMem 1 (fun z θ => -2 * α * Work.Construction.Vop
        (Work.Construction.PhiTil α (Work.FTS.Galerkin.slice g τ)
          (E (Work.FTS.Galerkin.slice g τ))) z θ) ∧
      Work.FTS.VocabO.CoefTh 1 (fun z θ => -2 * α * Work.Construction.Vop
        (Work.Construction.PhiTil α (Work.FTS.Galerkin.slice g τ)
          (E (Work.FTS.Galerkin.slice g τ))) z θ)
        ≤ C1 * (1 + |Ce|) * α ^ (-(1 / 2 : ℝ)) * M := by
  obtain ⟨Cag, hCagpos, hresid⟩ := Work.FTS.StrongPersist.ResidPtOfGo
  refine ⟨1, 2 * Cag + 2, 2, 2, 2 * Cag + 2, one_pos, le_rfl, by linarith, by norm_num,
    by norm_num, by linarith, ?_⟩
  intro α hαI g Φ τ M Cs E Φs hτ hctx
  obtain ⟨hα0, hα1⟩ := hαI
  have hCe0 : 0 ≤ Ce := hCe.le
  have hCag0 : 0 ≤ Cag := hCagpos.le
  let f : Work.FTS.Galerkin.Fn := Work.FTS.Galerkin.slice g τ
  let F : Work.FTS.Galerkin.Fn := E f
  have hgo : Work.FTS.VocabO.EllPkgGo α Ce f F := hctx.hell.hgo
  have hK : Work.FTS.StrongPersist.EllPkgK α 6 Ce f F := hctx.hell.hell
  have hbdd : Work.FTS.Nonlin.Xn α f ≤ M := hctx.hbdd
  have hMnn : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hbdd
  have hr : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0.le _
  -- ## the pointwise pricing of the three residual fields
  have hres := hresid α Ce hα0 hα1 hCe0 f F hgo
  have hptR : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Rop α (Work.Construction.PhiTil α f F) z θ|
        ≤ Cag * α ^ (-(1 / 2 : ℝ)) * Ce * M := by
    intro z θ hz hθ hθ'
    have h1 := (hres z θ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ'⟩)).1
    have h2 : Work.Spaces.HkNorm α 4 f ≤ M := hbdd
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (mul_nonneg (mul_nonneg hCag0 hr) hCe0))
  have hptU : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Uop α (Work.Construction.PhiTil α f F) z θ / Work.Construction.s2 θ|
        ≤ Cag * α ^ (-(1 / 2 : ℝ)) * Ce * M := by
    intro z θ hz hθ hθ'
    have h1 := (hres z θ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ'⟩)).2.1
    have h2 : Work.Spaces.HkNorm α 4 f ≤ M := hbdd
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (mul_nonneg (mul_nonneg hCag0 hr) hCe0))
  have hptV : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Vop (Work.Construction.PhiTil α f F) z θ|
        ≤ Cag * α ^ (-(1 / 2 : ℝ)) * Ce * M := by
    intro z θ hz hθ hθ'
    have h1 := (hres z θ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ'⟩)).2.2
    have h2 : Work.Spaces.HkNorm α 4 f ≤ M := hbdd
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (mul_nonneg (mul_nonneg hCag0 hr) hCe0))
  -- ## the level-four/level-six norms of the three fields
  have hn4R : Work.Spaces.HkNorm α 4 (Work.Construction.Rop α (Work.Construction.PhiTil α f F))
      ≤ Ce * M := le_trans hgo.R.2 (mul_le_mul_of_nonneg_left hbdd hCe0)
  have hn4U : Work.Spaces.HkNorm α 4 (fun z θ =>
      Work.Construction.Uop α (Work.Construction.PhiTil α f F) z θ / Work.Construction.s2 θ)
      ≤ Ce * M := le_trans hgo.U.2 (mul_le_mul_of_nonneg_left hbdd hCe0)
  have hn4V : Work.Spaces.HkNorm α 4 (Work.Construction.Vop (Work.Construction.PhiTil α f F))
      ≤ Ce * M := le_trans hgo.V.2 (mul_le_mul_of_nonneg_left hbdd hCe0)
  have hn6R : Work.Spaces.HkNorm α 6 (Work.Construction.Rop α (Work.Construction.PhiTil α f F))
      ≤ Ce * Work.Spaces.HkNorm α 6 f := hK.R.2
  have hn6U : Work.Spaces.HkNorm α 6 (fun z θ =>
      Work.Construction.Uop α (Work.Construction.PhiTil α f F) z θ / Work.Construction.s2 θ)
      ≤ Ce * Work.Spaces.HkNorm α 6 f := hK.U.2
  have hn6V : Work.Spaces.HkNorm α 6 (Work.Construction.Vop (Work.Construction.PhiTil α f F))
      ≤ Ce * Work.Spaces.HkNorm α 6 f := hK.V.2
  -- ## nonnegativity of the three constants
  have hK0nn : 0 ≤ (2 * Cag + 1) * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hr) (by linarith [abs_nonneg Ce]))
      (by linarith)
  have hK4nn : 0 ≤ 2 * (|Ce| * M) :=
    mul_nonneg (by norm_num) (mul_nonneg (abs_nonneg Ce) hMnn)
  have hK6nn : 0 ≤ 2 * (|Ce| * Work.Spaces.HkNorm α 6 f) :=
    mul_nonneg (by norm_num)
      (mul_nonneg (abs_nonneg Ce) (Work.Spaces.HkNorm_nonneg α 6 f))
  -- ## the three `CoefData` fields, with the uniform constants
  have hK0R : 0 ≤ Cag * α ^ (-(1 / 2 : ℝ)) * Ce * M :=
    mul_nonneg (mul_nonneg (mul_nonneg hCag0 hr) hCe0) hMnn
  have hK4R : 0 ≤ Ce * M := mul_nonneg hCe0 hMnn
  have hK6R : 0 ≤ Ce * Work.Spaces.HkNorm α 6 f :=
    mul_nonneg hCe0 (Work.Spaces.HkNorm_nonneg α 6 f)
  have hRraw : CoefData α
      (fun z θ => 2 * Work.Construction.Rop α (Work.Construction.PhiTil α f F) z θ)
      (|(2 : ℝ)| * (Cag * α ^ (-(1 / 2 : ℝ)) * Ce * M))
      (|(2 : ℝ)| * (Ce * M)) (|(2 : ℝ)| * (Ce * Work.Spaces.HkNorm α 6 f)) :=
    r6_coefData_const_mul (α := α) (c := 2) hgo.R.1.1 hgo.R.1.2 hK.R.1.2 hptR hn4R hn6R
      hK0R hK4R hK6R
  have h2abs : |(2 : ℝ)| = 2 := by norm_num
  have lle0R : |(2 : ℝ)| * (Cag * α ^ (-(1 / 2 : ℝ)) * Ce * M)
      ≤ (2 * Cag + 1) * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M) := by
    rw [h2abs]
    calc 2 * (Cag * α ^ (-(1 / 2 : ℝ)) * Ce * M)
        = 2 * 1 * Cag * α ^ (-(1 / 2 : ℝ)) * Ce * M := by ring
      _ ≤ (2 * Cag + 1) * α ^ (-(1 / 2 : ℝ)) * (1 + Ce) * (1 + M) :=
          r6_flatK0 hCag0 hr hCe0 hMnn (by norm_num) (by norm_num)
      _ = (2 * Cag + 1) * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M) := by
          rw [abs_of_pos hCe]
  have lle4R : |(2 : ℝ)| * (Ce * M) ≤ 2 * (|Ce| * M) := by
    rw [h2abs]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self Ce) hMnn)
      (by norm_num)
  have lle6R : |(2 : ℝ)| * (Ce * Work.Spaces.HkNorm α 6 f)
      ≤ 2 * (|Ce| * Work.Spaces.HkNorm α 6 f) := by
    rw [h2abs]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (le_abs_self Ce) (Work.Spaces.HkNorm_nonneg α 6 f))
      (by norm_num)
  have hRdata : CoefData α
      (fun z θ => 2 * Work.Construction.Rop α (Work.Construction.PhiTil α f F) z θ)
      ((2 * Cag + 1) * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
      (2 * (|Ce| * M)) (2 * (|Ce| * Work.Spaces.HkNorm α 6 f)) :=
    r6_coefData_mono hRraw lle0R lle4R lle6R
  -- the `U`-slot
  have hUraw : CoefData α
      (fun z θ => -2 * (Work.Construction.Uop α (Work.Construction.PhiTil α f F) z θ
        / Work.Construction.s2 θ))
      (|(-2 : ℝ)| * (Cag * α ^ (-(1 / 2 : ℝ)) * Ce * M))
      (|(-2 : ℝ)| * (Ce * M)) (|(-2 : ℝ)| * (Ce * Work.Spaces.HkNorm α 6 f)) :=
    r6_coefData_const_mul (α := α) (c := -2)
      (A := fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f F) z θ
        / Work.Construction.s2 θ)
      hgo.U.1.1 hgo.U.1.2 hK.U.1.2 hptU hn4U hn6U hK0R hK4R hK6R
  have hm2abs : |(-2 : ℝ)| = 2 := by norm_num
  have lle4U : |(-2 : ℝ)| * (Ce * M) ≤ 2 * (|Ce| * M) := by
    rw [hm2abs]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self Ce) hMnn)
      (by norm_num)
  have lle6U : |(-2 : ℝ)| * (Ce * Work.Spaces.HkNorm α 6 f)
      ≤ 2 * (|Ce| * Work.Spaces.HkNorm α 6 f) := by
    rw [hm2abs]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (le_abs_self Ce) (Work.Spaces.HkNorm_nonneg α 6 f))
      (by norm_num)
  have lle0U : |(-2 : ℝ)| * (Cag * α ^ (-(1 / 2 : ℝ)) * Ce * M)
      ≤ (2 * Cag + 1) * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M) := by
    rw [hm2abs]
    calc 2 * (Cag * α ^ (-(1 / 2 : ℝ)) * Ce * M)
        = 2 * 1 * Cag * α ^ (-(1 / 2 : ℝ)) * Ce * M := by ring
      _ ≤ (2 * Cag + 1) * α ^ (-(1 / 2 : ℝ)) * (1 + Ce) * (1 + M) :=
          r6_flatK0 hCag0 hr hCe0 hMnn (by norm_num) (by norm_num)
      _ = (2 * Cag + 1) * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M) := by
          rw [abs_of_pos hCe]
  have hUdata : CoefData α
      (fun z θ => -2 * (Work.Construction.Uop α (Work.Construction.PhiTil α f F) z θ
        / Work.Construction.s2 θ))
      ((2 * Cag + 1) * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
      (2 * (|Ce| * M)) (2 * (|Ce| * Work.Spaces.HkNorm α 6 f)) :=
    r6_coefData_mono hUraw lle0U lle4U lle6U
  -- the `V`-slot
  have hVraw : CoefData α
      (fun z θ => -2 * α * Work.Construction.Vop (Work.Construction.PhiTil α f F) z θ)
      (|(-2 : ℝ) * α| * (Cag * α ^ (-(1 / 2 : ℝ)) * Ce * M))
      (|(-2 : ℝ) * α| * (Ce * M)) (|(-2 : ℝ) * α| * (Ce * Work.Spaces.HkNorm α 6 f)) :=
    r6_coefData_const_mul (α := α) (c := -2 * α)
      (A := Work.Construction.Vop (Work.Construction.PhiTil α f F))
      hgo.V.1.1 hgo.V.1.2 hK.V.1.2 hptV hn4V hn6V hK0R hK4R hK6R
  have hma : |(-2 : ℝ) * α| = 2 * α := by
    rw [abs_mul, abs_of_pos hα0]
    norm_num
  have lle0V : |(-2 : ℝ) * α| * (Cag * α ^ (-(1 / 2 : ℝ)) * Ce * M)
      ≤ (2 * Cag + 1) * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M) := by
    rw [hma]
    calc 2 * α * (Cag * α ^ (-(1 / 2 : ℝ)) * Ce * M)
        = 2 * α * Cag * α ^ (-(1 / 2 : ℝ)) * Ce * M := by ring
      _ ≤ (2 * Cag + 1) * α ^ (-(1 / 2 : ℝ)) * (1 + Ce) * (1 + M) :=
          r6_flatK0 hCag0 hr hCe0 hMnn hα0.le hα1
      _ = (2 * Cag + 1) * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M) := by
          rw [abs_of_pos hCe]
  have lle4V : |(-2 : ℝ) * α| * (Ce * M) ≤ 2 * (|Ce| * M) := by
    rw [hma]
    have h3 : 0 ≤ Ce * M := mul_nonneg hCe0 hMnn
    have h1 : 2 * α * (Ce * M) ≤ 2 * (Ce * M) := by
      have h2a : 2 * α ≤ 2 := by linarith
      exact mul_le_mul_of_nonneg_right h2a h3
    have h2 : 2 * (Ce * M) ≤ 2 * (|Ce| * M) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self Ce) hMnn)
        (by norm_num)
    linarith
  have lle6V : |(-2 : ℝ) * α| * (Ce * Work.Spaces.HkNorm α 6 f)
      ≤ 2 * (|Ce| * Work.Spaces.HkNorm α 6 f) := by
    rw [hma]
    have h3 : 0 ≤ Ce * Work.Spaces.HkNorm α 6 f :=
      mul_nonneg hCe0 (Work.Spaces.HkNorm_nonneg α 6 f)
    have h1 : 2 * α * (Ce * Work.Spaces.HkNorm α 6 f)
        ≤ 2 * (Ce * Work.Spaces.HkNorm α 6 f) := by
      have h2a : 2 * α ≤ 2 := by linarith
      exact mul_le_mul_of_nonneg_right h2a h3
    have h2 : 2 * (Ce * Work.Spaces.HkNorm α 6 f)
        ≤ 2 * (|Ce| * Work.Spaces.HkNorm α 6 f) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (le_abs_self Ce) (Work.Spaces.HkNorm_nonneg α 6 f))
        (by norm_num)
    linarith
  have hVdata : CoefData α
      (fun z θ => -2 * α * Work.Construction.Vop (Work.Construction.PhiTil α f F) z θ)
      ((2 * Cag + 1) * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
      (2 * (|Ce| * M)) (2 * (|Ce| * Work.Spaces.HkNorm α 6 f)) :=
    r6_coefData_mono hVraw lle0V lle4V lle6V
  -- ## the flat angular data of the `V`-slot
  have hVmem : Work.FTS.VocabO.CoefThMem 1
      (fun z θ => -2 * α * Work.Construction.Vop (Work.Construction.PhiTil α f F) z θ) :=
    r6_coefThMem_const_mul (l := 1) (c := -2 * α) hgo.Vth.1
  have hVth : Work.FTS.VocabO.CoefTh 1
      (fun z θ => -2 * α * Work.Construction.Vop (Work.Construction.PhiTil α f F) z θ)
      ≤ (2 * Cag + 2) * (1 + |Ce|) * α ^ (-(1 / 2 : ℝ)) * M := by
    have h1 := r6_coefTh_const_mul_le (l := 1) (c := -2 * α) hgo.Vth.1
    rw [hma] at h1
    have h3 : Work.FTS.VocabO.CoefTh 1
        (Work.Construction.Vop (Work.Construction.PhiTil α f F)) ≤ Ce * α ^ (-(1 / 2 : ℝ)) * M :=
      le_trans hgo.Vth.2 (mul_le_mul_of_nonneg_left hbdd (mul_nonneg hCe0 hr))
    have h4 : 2 * α * Work.FTS.VocabO.CoefTh 1
        (Work.Construction.Vop (Work.Construction.PhiTil α f F))
        ≤ 2 * α * (Ce * α ^ (-(1 / 2 : ℝ)) * M) :=
      mul_le_mul_of_nonneg_left h3 (mul_nonneg (by norm_num) hα0.le)
    have h5 : 2 * α * (Ce * α ^ (-(1 / 2 : ℝ)) * M)
        ≤ (2 * Cag + 2) * (1 + |Ce|) * α ^ (-(1 / 2 : ℝ)) * M := by
      calc 2 * α * (Ce * α ^ (-(1 / 2 : ℝ)) * M)
          ≤ (2 * Cag + 2) * (1 + Ce) * α ^ (-(1 / 2 : ℝ)) * M :=
            r6_thArith hCag0 hr hCe0 hMnn hα0.le hα1
        _ = (2 * Cag + 2) * (1 + |Ce|) * α ^ (-(1 / 2 : ℝ)) * M := by
            rw [abs_of_pos hCe]
    exact le_trans (le_trans h1 h4) h5
  -- ## assembly
  have leK0 : (2 * Cag + 1) * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)
      ≤ (2 * Cag + 2) * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M) := by
    have hz : 0 ≤ α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M) := by positivity
    have hmono := mul_le_mul_of_nonneg_right
      (show (2 * Cag + 1 : ℝ) ≤ 2 * Cag + 2 by linarith) hz
    calc (2 * Cag + 1) * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)
        = (2 * Cag + 1) * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) := by ring
      _ ≤ (2 * Cag + 2) * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) := hmono
      _ = (2 * Cag + 2) * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M) := by ring
  have leK4 : 2 * (|Ce| * M) ≤ 2 * (1 + |Ce|) * M := r6_flatKM hMnn
  have leK6 : 2 * (|Ce| * Work.Spaces.HkNorm α 6 f)
      ≤ 2 * (1 + |Ce|) * Work.Spaces.HkNorm α 6 f :=
    r6_flatKx (Work.Spaces.HkNorm_nonneg α 6 f)
  have hFirst : ∃ K0 K4 K6 : ℝ, 0 ≤ K0 ∧ 0 ≤ K4 ∧ 0 ≤ K6 ∧
      K0 ≤ (2 * Cag + 2) * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M) ∧
      K4 ≤ 2 * (1 + |Ce|) * M ∧
      K6 ≤ 2 * (1 + |Ce|) * Work.Spaces.HkNorm α 6 f ∧
      CoefData α (fun z θ => 2 * Work.Construction.Rop α
        (Work.Construction.PhiTil α f F) z θ) K0 K4 K6 :=
    ⟨_, _, _, hK0nn, hK4nn, hK6nn, leK0, leK4, leK6, hRdata⟩
  have hSecond : ∃ K0 K4 K6 : ℝ, 0 ≤ K0 ∧ 0 ≤ K4 ∧ 0 ≤ K6 ∧
      K0 ≤ (2 * Cag + 2) * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M) ∧
      K4 ≤ 2 * (1 + |Ce|) * M ∧
      K6 ≤ 2 * (1 + |Ce|) * Work.Spaces.HkNorm α 6 f ∧
      CoefData α (fun z θ => -2 * (Work.Construction.Uop α
        (Work.Construction.PhiTil α f F) z θ / Work.Construction.s2 θ)) K0 K4 K6 :=
    ⟨_, _, _, hK0nn, hK4nn, hK6nn, leK0, leK4, leK6, hUdata⟩
  have hThird : ∃ K0 K4 K6 : ℝ, 0 ≤ K0 ∧ 0 ≤ K4 ∧ 0 ≤ K6 ∧
      K0 ≤ (2 * Cag + 2) * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M) ∧
      K4 ≤ 2 * (1 + |Ce|) * M ∧
      K6 ≤ 2 * (1 + |Ce|) * Work.Spaces.HkNorm α 6 f ∧
      CoefData α (fun z θ => -2 * α * Work.Construction.Vop
        (Work.Construction.PhiTil α f F) z θ) K0 K4 K6 :=
    ⟨_, _, _, hK0nn, hK4nn, hK6nn, leK0, leK4, leK6, hVdata⟩
  exact ⟨hFirst, hSecond, hThird, hVmem, hVth⟩

end

end Work.FTS.StrongPersist.H6Row6
