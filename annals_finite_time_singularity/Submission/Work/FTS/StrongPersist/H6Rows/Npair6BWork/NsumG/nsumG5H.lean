import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkMomentJetSq
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkRowDthRepaired
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkRowDthTopRow
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkRowsAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_fk_mul
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.nsumData
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## helpers -/

/-- Scalar multiples pull out of the elementary slot pairing (the `SmoothOpen`-free version). -/
theorem slotPairing_const_mul_pure (ρ : ℝ → ℝ → ℝ) (a b : ℕ) (c : ℝ) (v f : ℝ → ℝ → ℝ) :
    Work.FTS.TransportS.slotPairing ρ a b (fun z θ => c * v z θ) f
      = c * Work.FTS.TransportS.slotPairing ρ a b v f := by
  unfold Work.FTS.TransportS.slotPairing
  rw [Work.FTS.StrongPersist.H6Pair6Aux.mixed_const_mul_pure c v b a]
  have hinner : ∀ z : ℝ,
      (∫ θ in Work.Spaces.Iθ,
          ρ z θ * (c * Work.Spaces.mixed b a v z θ) * Work.Spaces.mixed b a f z θ)
        = c * ∫ θ in Work.Spaces.Iθ,
            ρ z θ * Work.Spaces.mixed b a v z θ * Work.Spaces.mixed b a f z θ := by
    intro z
    rw [show (fun θ => ρ z θ * (c * Work.Spaces.mixed b a v z θ)
            * Work.Spaces.mixed b a f z θ)
          = fun θ => c * (ρ z θ * Work.Spaces.mixed b a v z θ
            * Work.Spaces.mixed b a f z θ) from funext fun θ => by ring]
    rw [MeasureTheory.integral_const_mul]
  rw [show (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        ρ z θ * (c * Work.Spaces.mixed b a v z θ) * Work.Spaces.mixed b a f z θ)
      = ∫ z in Work.Spaces.Iz, c * (∫ θ in Work.Spaces.Iθ,
          ρ z θ * Work.Spaces.mixed b a v z θ * Work.Spaces.mixed b a f z θ) from
    integral_congr_ae (Filter.Eventually.of_forall hinner)]
  rw [MeasureTheory.integral_const_mul]

/-- The absorption of a row price `K α^{-3}(1+M)²(1+S)` into the uniform shape
`C α^{-10}(1+|Ce|+|Cs|)⁴(1+M)⁴(1+S)`. -/
theorem row_shape_le {α Ce Cs M S K C X : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hM : 0 ≤ M) (hS : 0 ≤ S) (hC0 : 0 ≤ C) (hKC : K ≤ C)
    (h : X ≤ K * α ^ (-(3 : ℝ)) * (1 + M) * (1 + M) * (1 + S)) :
    X ≤ C * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 * (1 + S) := by
  have hA0 : (0 : ℝ) ≤ α ^ (-(3 : ℝ)) * (1 + M) * (1 + M) * (1 + S) := by positivity
  have hB0 : (0 : ℝ) ≤ α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
      * (1 + S) := by positivity
  have hα3 : α ^ (-(3 : ℝ)) ≤ α ^ (-(10 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (by norm_num)
  have hp10 : (0 : ℝ) ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα0.le _
  have h1S : (0 : ℝ) ≤ 1 + S := by linarith
  have hm : (1 + M) * (1 + M) ≤ (1 + M) ^ 4 := by
    have h1 : (1 : ℝ) ≤ (1 + M) * (1 + M) := by nlinarith [sq_nonneg M]
    calc (1 + M) * (1 + M) ≤ (1 + M) * (1 + M) * ((1 + M) * (1 + M)) :=
          le_mul_of_one_le_right (by positivity) h1
      _ = (1 + M) ^ 4 := by ring
  have hd4 : (1 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 := by
    have h1 : (1 : ℝ) ≤ 1 + |Ce| + |Cs| := by
      have h2 := abs_nonneg Ce; have h3 := abs_nonneg Cs; linarith
    exact one_le_pow₀ (n := 4) h1
  have hm4nn : (0 : ℝ) ≤ (1 + M) ^ 4 := by positivity
  have hAB : α ^ (-(3 : ℝ)) * (1 + M) * (1 + M) * (1 + S)
      ≤ α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 * (1 + S) := by
    calc α ^ (-(3 : ℝ)) * (1 + M) * (1 + M) * (1 + S)
        = α ^ (-(3 : ℝ)) * ((1 + M) * (1 + M)) * (1 + S) := by ring
      _ ≤ α ^ (-(10 : ℝ)) * ((1 + M) * (1 + M)) * (1 + S) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hα3 (by positivity)) h1S
      _ ≤ α ^ (-(10 : ℝ)) * ((1 + M) ^ 4) * (1 + S) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hp10) h1S
      _ ≤ α ^ (-(10 : ℝ)) * ((1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4) * (1 + S) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hm4nn hd4) hp10) h1S
      _ = α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 * (1 + S) := by ring
  calc X ≤ K * α ^ (-(3 : ℝ)) * (1 + M) * (1 + M) * (1 + S) := h
    _ = K * (α ^ (-(3 : ℝ)) * (1 + M) * (1 + M) * (1 + S)) := by ring
    _ ≤ C * (α ^ (-(3 : ℝ)) * (1 + M) * (1 + M) * (1 + S)) :=
        mul_le_mul_of_nonneg_right hKC hA0
    _ ≤ C * (α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 * (1 + S)) :=
        mul_le_mul_of_nonneg_left hAB hC0
    _ = C * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 * (1 + S) := by ring

/-! ## the two rows -/

/-- The `(FK f)·D_θf` row for **all** slots with `a + b ≤ 6`. -/
theorem fkDthRowAll : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Fn) (M : ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b
          (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) f|
        ≤ C * α ^ (-(3 : ℝ)) * (1 + M) * (1 + M)
            * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨C1, hC10, h1⟩ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkRowDthRepaired
  obtain ⟨Cg, hCg0, hg⟩ :=
    Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkRowDthTopRow
  refine ⟨C1 + Cg, by positivity, ?_⟩
  intro α hα f M a b ρ hD hab hρ
  have hX0 : (0 : ℝ) ≤ α ^ (-(3 : ℝ)) * (1 + M) * (1 + M)
      * (1 + Work.Spaces.HkSq α 6 f) := by
    have hp : (0 : ℝ) ≤ α ^ (-(3 : ℝ)) := Real.rpow_nonneg hα.1.le _
    have hM : (0 : ℝ) ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hD.bdd
    have hS : (0 : ℝ) ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
    positivity
  have hle1 : C1 ≤ C1 + Cg := le_add_of_nonneg_right hCg0.le
  have hle2 : Cg ≤ C1 + Cg := le_add_of_nonneg_left hC10.le
  have hstep : ∀ C C' : ℝ, C ≤ C' →
      C * α ^ (-(3 : ℝ)) * (1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)
        ≤ C' * α ^ (-(3 : ℝ)) * (1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by
    intro C C' hCC'
    have h := mul_le_mul_of_nonneg_right hCC' hX0
    convert h using 1 <;> ring
  by_cases hb : b ≤ 5
  · exact (h1 α hα f M a b ρ hD hab hb hρ).trans (hstep C1 (C1 + Cg) hle1)
  · have hb6 : b = 6 := by omega
    have ha0 : a = 0 := by omega
    subst hb6
    subst ha0
    exact (hg α hα f M ρ hD hρ).trans (hstep Cg (C1 + Cg) hle2)

/-- The `sin²θ·(FK f)·f` row for all slots with `a + b ≤ 6`. -/
theorem fkSinSqRowAll : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Fn) (M : ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b
          (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z * f z θ) f|
        ≤ C * α ^ (-(3 : ℝ)) * (1 + M) * (1 + M)
            * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨Css, hCss0, hss⟩ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSinSqHkSq
  refine ⟨Css + 1, by positivity, ?_⟩
  intro α hα f M a b ρ hD hab hρ
  have hS0 : (0 : ℝ) ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hM0 : (0 : ℝ) ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hD.bdd
  have hmemu : Work.Spaces.HkMem α 6
      (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z * f z θ) :=
    (Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_fk_mul α hα f M hD).2.2.2.2.1
  have hpair := Work.FTS.StrongPersist.H6Pair6Aux.SlotPairingHkSq
    (α := α) hα.1 hab hρ hmemu hD.h6
  have hen : Work.Spaces.HkSq α 6
      (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z * f z θ)
      ≤ Css * M ^ 2 * Work.Spaces.HkSq α 6 f := hss α hα f M hD
  have hB0 : (0 : ℝ) ≤ (1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by
    have h1 : (0:ℝ) ≤ 1 + M := by linarith
    positivity
  have hMS : M ^ 2 * Work.Spaces.HkSq α 6 f
      ≤ (1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by
    have h2 : M ^ 2 ≤ (1 + M) * (1 + M) := by nlinarith [hM0]
    have h3 : Work.Spaces.HkSq α 6 f ≤ 1 + Work.Spaces.HkSq α 6 f := by linarith
    exact mul_le_mul h2 h3 hS0 (by positivity)
  have hen' : Work.Spaces.HkSq α 6
        (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z * f z θ)
      ≤ Css * ((1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)) := by
    have h := mul_le_mul_of_nonneg_left hMS hCss0.le
    have he2 : Css * M ^ 2 * Work.Spaces.HkSq α 6 f
        = Css * (M ^ 2 * Work.Spaces.HkSq α 6 f) := by ring
    calc Work.Spaces.HkSq α 6
          (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z * f z θ)
        ≤ Css * M ^ 2 * Work.Spaces.HkSq α 6 f := hen
      _ = Css * (M ^ 2 * Work.Spaces.HkSq α 6 f) := he2
      _ ≤ Css * ((1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)) := h
  have hS' : Work.Spaces.HkSq α 6 f
      ≤ (1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by
    have h1 : (1:ℝ) ≤ (1 + M) * (1 + M) := by nlinarith [hM0]
    have h2 : Work.Spaces.HkSq α 6 f ≤ 1 + Work.Spaces.HkSq α 6 f := by linarith
    calc Work.Spaces.HkSq α 6 f ≤ 1 * (1 + Work.Spaces.HkSq α 6 f) := by simp
      _ ≤ (1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by
          refine mul_le_mul_of_nonneg_right h1 ?_
          linarith
  have hsum : (Work.Spaces.HkSq α 6
        (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z * f z θ)
        + Work.Spaces.HkSq α 6 f) / 2
      ≤ (Css + 1) * ((1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)) := by
    have h1 : Work.Spaces.HkSq α 6
          (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z * f z θ)
        + Work.Spaces.HkSq α 6 f
        ≤ (Css + 1) * ((1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)) := by
      have h2 : Css * ((1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f))
          + ((1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f))
          = (Css + 1) * ((1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)) := by ring
      linarith [hen', hS', h2.le]
    have h2 := div_le_div_of_nonneg_right h1 (by norm_num : (0:ℝ) ≤ 2)
    have h3 : (Css + 1) * ((1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)) / 2
        ≤ (Css + 1) * ((1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)) := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
      linarith [mul_nonneg (by positivity) hB0]
    linarith [h2, h3]
  refine hpair.trans (hsum.trans ?_)
  have hone : (1 : ℝ) ≤ α ^ (-(3 : ℝ)) :=
    Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.one_le_alpha_rpow hα.1 hα.2
  have hC1nn : (0 : ℝ) ≤ Css + 1 := by linarith
  calc (Css + 1) * ((1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f))
      = (Css + 1) * 1 * ((1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)) := by ring
    _ ≤ (Css + 1) * α ^ (-(3 : ℝ))
          * ((1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hone hC1nn) hB0
    _ = (Css + 1) * α ^ (-(3 : ℝ)) * (1 + M) * (1 + M)
          * (1 + Work.Spaces.HkSq α 6 f) := by ring

/-! ## the target -/

/-- The two *datum-slot* pieces of the angular-moment group (`Kf := FK f`, `f = slice g τ`):
`nsP15 = -(1/2)·Kf·D_θf` and `nsP19 = -sin²θ·Kf·f`.  These are the `fkRowsC6` conjuncts 2 and 5
with the budget `α^{-10}(1+|Ce|+|Cs|)^4(1+M)^4(1+HkSq α 6 f)`, i.e. one only needs the estimate
`C α^{-3}(1+M)²(1+HkSq α 6 f)`.

Route: the radial row for `(FK f)·X`: write `mixed b a (Kf·X) = Σ_{b₁ ≤ b} C(b,b₁)·(D_z^{b₁} Kf)·
mixed (b-b₁) a X`, bound `|D_z^{b₁} Kf|² ≤ Cdzd·HkSq α (b₁+1) f` a.e. (`FkAux.fkDzdIterSqLe`),
dominate the datum side by `HkIntegrand α 6 f` (the graded slice bounds `FkAux.fkSliceSup*`,
`HkSq_le_S`, `HkSq_le_Msq`), integrate (`FkAux.fkPairCS`, `slotPairing_abs_le`) and do the finite
arithmetic `(b+1)Σ_b₁ C(b,b₁)²·Cdzd·M² ≤ (7·7·4096·Cdzd)·(1+M)²` (`FkAux.fkArith`).  For `X = D_θf`
the slot order of the middle factor is `a+1`, so at `b = 6` the term needs the level-seven slot
(the `fkRowDth6`-style treatment, or an angular integration by parts); `X = f` at `b = 6` is
`FkAux.fkRowF6`.  The factor `sin²θ` of `nsP19` is handled by the Leibniz expansion in `θ`
(`|D_θ^r sin²θ| ≤ K_r σ² ≤ K_r`) against the `θ`-weights `σ^{-η}`/`σ^{-γ}` (`FkAux.fkSinPow`). -/
theorem nsumG5H (Ce : ℝ) : ∃ C : ℝ, 0 < C ∧
    ∀ α ∈ Set.Ioc 0 1, ∀ (g Φ : Work.FTS.Galerkin.Fam) (τ M Cs : ℝ)
      (E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn) (Φs : Work.FTS.Galerkin.Fn),
      0 ≤ τ →
      Work.FTS.StrongPersist.L6Ctx (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1)
        α M Ce Cs E Φs g Φ τ →
      ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      (|Work.FTS.TransportS.slotPairing ρ a b (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP15 α (Work.FTS.Galerkin.slice g τ)) (Work.FTS.Galerkin.slice g τ)|
          ≤ C * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
              * (1 + Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g τ)) ∧
       |Work.FTS.TransportS.slotPairing ρ a b (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP19 α (Work.FTS.Galerkin.slice g τ)) (Work.FTS.Galerkin.slice g τ)|
          ≤ C * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
              * (1 + Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g τ))) := by
  obtain ⟨Cdth, hCdth0, hDth⟩ := fkDthRowAll
  obtain ⟨Css, hCss0, hSin⟩ := fkSinSqRowAll
  refine ⟨Cdth + Css + 1, by positivity, ?_⟩
  intro α hα g Φ τ M Cs E Φs _hτ hctx a b ρ hab hleaf
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hdat :
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α (Work.FTS.Galerkin.slice g τ) M :=
    Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.datData_of_H6Adm hctx.hreg hctx.h7 hctx.hbdd
  set f : Fn := Work.FTS.Galerkin.slice g τ with hf
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hdat.bdd
  have hS0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hCtot1 : Cdth ≤ Cdth + Css + 1 := by
    have h1 : 0 ≤ Css := hCss0.le
    linarith
  have hCtot2 : Css ≤ Cdth + Css + 1 := by
    have h1 : 0 ≤ Cdth := hCdth0.le
    linarith
  have h15 : |Work.FTS.TransportS.slotPairing ρ a b
        (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP15 α f) f|
      ≤ Cdth * α ^ (-(3 : ℝ)) * (1 + M) * (1 + M)
          * (1 + Work.Spaces.HkSq α 6 f) := by
    have heq : Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP15 α f
        = fun z θ => (-(1 / 2)) * (Work.Construction.FK f z * Work.Spaces.Dth f z θ) := by
      funext z θ
      simp only [Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP15,
        Work.FTS.StrongPersist.H6Rows.Npair6SupAux.coefKf,
        Work.FTS.StrongPersist.H6Rows.Npair6SupAux.slotTf]
      ring
    have habs : |Work.FTS.TransportS.slotPairing ρ a b
          (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP15 α f) f|
        = (1 / 2) * |Work.FTS.TransportS.slotPairing ρ a b
            (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) f| := by
      rw [heq, slotPairing_const_mul_pure ρ a b (-(1 / 2))
        (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) f,
        abs_mul, abs_of_neg (by norm_num : (-(1 / 2) : ℝ) < 0), neg_neg]
    rw [habs]
    have hbase := hDth α hα f M a b ρ hdat hab hleaf
    linarith [hbase, abs_nonneg (Work.FTS.TransportS.slotPairing ρ a b
      (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) f)]
  have h19 : |Work.FTS.TransportS.slotPairing ρ a b
        (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP19 α f) f|
      ≤ Css * α ^ (-(3 : ℝ)) * (1 + M) * (1 + M)
          * (1 + Work.Spaces.HkSq α 6 f) := by
    have heq : Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP19 α f
        = fun z θ => (-1) * (Real.sin θ ^ 2 * Work.Construction.FK f z * f z θ) := by
      funext z θ
      simp only [Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP19,
        Work.FTS.StrongPersist.H6Rows.Npair6SupAux.angSin2,
        Work.FTS.StrongPersist.H6Rows.Npair6SupAux.coefKf]
      ring
    have habs : |Work.FTS.TransportS.slotPairing ρ a b
          (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP19 α f) f|
        = |Work.FTS.TransportS.slotPairing ρ a b
            (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z * f z θ) f| := by
      rw [heq, slotPairing_const_mul_pure ρ a b (-1)
        (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z * f z θ) f,
        abs_mul, abs_of_neg (by norm_num : ((-1 : ℝ)) < 0), neg_neg, one_mul]
    rw [habs]
    exact hSin α hα f M a b ρ hdat hab hleaf
  refine ⟨?_, ?_⟩
  · simpa only [hf] using row_shape_le hα0 hα1 hM0 hS0 (by positivity) hCtot1 h15
  · simpa only [hf] using row_shape_le hα0 hα1 hM0 hS0 (by positivity) hCtot2 h19

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG
