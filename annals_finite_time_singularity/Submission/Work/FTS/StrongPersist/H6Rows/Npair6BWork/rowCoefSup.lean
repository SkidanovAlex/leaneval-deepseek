import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkMomentJetSq
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkStarPieces
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_fk_mul
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.FKstarSlotPiece
import Submission.Work.FTS.StrongPersist.N6TransPriced
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG.nsumG5E =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Two elementary helpers

The scalar factors `-1/2` and `-1` of the two star-slot pieces are pulled out of the elementary
slot pairing (which is `ℝ`-homogeneous in its first argument, with no smoothness needed), and the
resulting price `(HkSq α 6 u + HkSq α 6 f)/2` with `HkSq α 6 u ≤ C α^{-2} HkSq α 6 f` is absorbed
into the uniform shape `C α^{-10} (1+|Ce|+|Cs|)⁴ (1+M)⁴ (1 + HkSq α 6 f)`. -/

/-- **Scalar multiples pull out of the elementary slot pairing.**

`slotPairing ρ a b (c·v) f = c · slotPairing ρ a b v f` for every constant `c`; this is
`H6Pair6Aux.SlotPairingConstMul` without its (unused) `SmoothOpen` hypothesis, which is not
available for the angular-moment products `FK f · D_θF_*` and `sin²θ · FK f · F_*`. -/
theorem slotPairing_smul_left (ρ : ℝ → ℝ → ℝ) (a b : ℕ) (c : ℝ) (v f : ℝ → ℝ → ℝ) :
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
          = (fun θ => c * (ρ z θ * Work.Spaces.mixed b a v z θ
            * Work.Spaces.mixed b a f z θ)) from funext fun θ => by ring]
    rw [MeasureTheory.integral_const_mul]
  rw [show (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        ρ z θ * (c * Work.Spaces.mixed b a v z θ) * Work.Spaces.mixed b a f z θ)
      = ∫ z in Work.Spaces.Iz, c * (∫ θ in Work.Spaces.Iθ,
          ρ z θ * Work.Spaces.mixed b a v z θ * Work.Spaces.mixed b a f z θ) from
    integral_congr_ae (Filter.Eventually.of_forall hinner)]
  rw [MeasureTheory.integral_const_mul]

/-- **The uniform shape of a star-slot price.**

If `K = HkSq α 6 u` is priced by `C α^{-2} H` (`H = HkSq α 6 f`) and `c ∈ [0,1]`, then
`c·(K + H)/2` is dominated by `(C+1) α^{-10} (1+|Ce|+|Cs|)⁴ (1+M)⁴ (1+H)`: the three factors
`α^{-2} ≤ α^{-10}`, `1 ≤ (1+|Ce|+|Cs|)⁴` and `1 ≤ (1+M)⁴` (for `M ≥ 0`) pay for the conversion. -/
theorem star_piece_shape {α Ce Cs M C K H c : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hK : 0 ≤ K) (hH : 0 ≤ H) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hKH : K ≤ C * α ^ (-(2 : ℝ)) * H) :
    c * ((K + H) / 2)
      ≤ (C + 1) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 * (1 + H) := by
  have hA1 : (1 : ℝ) ≤ α ^ (-(2 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (show (-(2 : ℝ)) ≤ 0 by norm_num)
    rwa [Real.rpow_zero] at h
  have hA2 : α ^ (-(2 : ℝ)) ≤ α ^ (-(10 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (by norm_num)
  have hAp2 : (0 : ℝ) ≤ α ^ (-(2 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hX : (1 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 := by
    have h1 : (1 : ℝ) ≤ 1 + |Ce| + |Cs| := by
      have h2 := abs_nonneg Ce
      have h3 := abs_nonneg Cs
      linarith
    exact one_le_pow₀ h1
  have hM4 : (1 : ℝ) ≤ (1 + M) ^ 4 := by
    have h1 : (1 : ℝ) ≤ 1 + M := by linarith
    exact one_le_pow₀ h1
  have h1 : c * ((K + H) / 2) ≤ (C * α ^ (-(2 : ℝ)) * H + H) / 2 := by
    have h2 : (K + H) / 2 ≤ (C * α ^ (-(2 : ℝ)) * H + H) / 2 :=
      div_le_div_of_nonneg_right (add_le_add hKH le_rfl) (by norm_num)
    have h3 : 0 ≤ (K + H) / 2 := by linarith
    calc c * ((K + H) / 2) ≤ 1 * ((K + H) / 2) := mul_le_mul_of_nonneg_right hc1 h3
      _ = (K + H) / 2 := one_mul _
      _ ≤ (C * α ^ (-(2 : ℝ)) * H + H) / 2 := h2
  have h2 : (C * α ^ (-(2 : ℝ)) * H + H) / 2 ≤ (C + 1) * α ^ (-(2 : ℝ)) * H := by
    have h4 : C * α ^ (-(2 : ℝ)) + 1 ≤ (C + 1) * α ^ (-(2 : ℝ)) := by nlinarith
    have h5 : 0 ≤ C * α ^ (-(2 : ℝ)) + 1 := by nlinarith
    have h6 : (C * α ^ (-(2 : ℝ)) * H + H) / 2
        = (C * α ^ (-(2 : ℝ)) + 1) * H / 2 := by ring
    have hpr : 0 ≤ (C * α ^ (-(2 : ℝ)) + 1) * H := mul_nonneg h5 hH
    have h7 : (C * α ^ (-(2 : ℝ)) + 1) * H / 2 ≤ (C * α ^ (-(2 : ℝ)) + 1) * H := by
      linarith
    have h8 : (C * α ^ (-(2 : ℝ)) + 1) * H ≤ (C + 1) * α ^ (-(2 : ℝ)) * H :=
      mul_le_mul_of_nonneg_right h4 hH
    rw [h6]
    exact le_trans h7 h8
  have h3 : (C + 1) * α ^ (-(2 : ℝ)) * H
      ≤ (C + 1) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 * (1 + H) := by
    have hC1 : 0 ≤ C + 1 := by linarith
    have hB : 0 ≤ (C + 1) * α ^ (-(10 : ℝ)) := mul_nonneg hC1 (Real.rpow_nonneg hα0.le _)
    have hstep1 : (C + 1) * α ^ (-(2 : ℝ)) * H ≤ (C + 1) * α ^ (-(10 : ℝ)) * H :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA2 hC1) hH
    have hstep2 : (C + 1) * α ^ (-(10 : ℝ)) * H
        ≤ (C + 1) * α ^ (-(10 : ℝ)) * (1 + H) :=
      mul_le_mul_of_nonneg_left (by linarith) hB
    have hstep3 : (C + 1) * α ^ (-(10 : ℝ)) * (1 + H)
        ≤ (C + 1) * α ^ (-(10 : ℝ)) * (1 + H) * (1 + |Ce| + |Cs|) ^ 4 :=
      le_mul_of_one_le_right (mul_nonneg hB (by linarith)) hX
    have hstep4 : (C + 1) * α ^ (-(10 : ℝ)) * (1 + H) * (1 + |Ce| + |Cs|) ^ 4
        ≤ (C + 1) * α ^ (-(10 : ℝ)) * (1 + H) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 :=
      le_mul_of_one_le_right
        (mul_nonneg (mul_nonneg hB (by linarith)) (by positivity)) hM4
    calc (C + 1) * α ^ (-(2 : ℝ)) * H
        ≤ (C + 1) * α ^ (-(10 : ℝ)) * H := hstep1
      _ ≤ (C + 1) * α ^ (-(10 : ℝ)) * (1 + H) := hstep2
      _ ≤ (C + 1) * α ^ (-(10 : ℝ)) * (1 + H) * (1 + |Ce| + |Cs|) ^ 4 := hstep3
      _ ≤ (C + 1) * α ^ (-(10 : ℝ)) * (1 + H) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 := hstep4
      _ = (C + 1) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 * (1 + H) := by ring
  linarith

/-- The two *star-slot* pieces of the angular-moment group (`Kf := FK f`, `f = slice g τ`):
`nsP14 = -(1/2)·Kf·D_θF_*` and `nsP18 = -sin²θ·Kf·F_*`.
Route: `hkMem_fk_mul` (conjuncts 4 and 7) gives `HkMem α 6` of `Kf·D_θF_*` and of
`sin²θ·Kf·F_*`; `FkAux.fkStarPieces` (conjuncts 3 and 4) gives `HkSq α 6 (·) ≤ C α^{-2} HkSq α 6 f`;
`H6Pair6Aux.SlotPairingHkSq` then bounds the pairing by `(HkSq α 6 (·) + HkSq α 6 f)/2`, and the
scalar factors `-1/2`, `-1` are pulled out (`mixed`/`slotPairing` are linear in the first
argument).  The datum data is `T6Coef.DatData α (slice g τ) M` from `L6Ctx`. -/
theorem nsumG5E (Ce : ℝ) : ∃ C : ℝ, 0 < C ∧
    ∀ α ∈ Set.Ioc 0 1, ∀ (g Φ : Work.FTS.Galerkin.Fam) (τ M Cs : ℝ)
      (E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn) (Φs : Work.FTS.Galerkin.Fn),
      0 ≤ τ →
      Work.FTS.StrongPersist.L6Ctx (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1)
        α M Ce Cs E Φs g Φ τ →
      ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      (|Work.FTS.TransportS.slotPairing ρ a b (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP14 α (Work.FTS.Galerkin.slice g τ)) (Work.FTS.Galerkin.slice g τ)|
          ≤ C * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
              * (1 + Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g τ)) ∧
       |Work.FTS.TransportS.slotPairing ρ a b (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP18 α (Work.FTS.Galerkin.slice g τ)) (Work.FTS.Galerkin.slice g τ)|
          ≤ C * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
              * (1 + Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g τ))) := by
  obtain ⟨C3, hC3pos, hpieces⟩ :=
    Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkStarPieces
  refine ⟨C3 + 1, by linarith, ?_⟩
  intro α hα g Φ τ M Cs E Φs hτ hctx a b ρ hab hleaf
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  set f : Fn := Work.FTS.Galerkin.slice g τ with hf
  have hdat : Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M := by
    simpa only [hf] using
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.datData_of_H6Adm hctx.hreg hctx.h7 hctx.hbdd)
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hdat.bdd
  have hH0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  -- the two price bounds of `fkStarPieces` (conjuncts 3 and 4) and the two memberships
  obtain ⟨-, -, hKdth, hKsin⟩ := hpieces α hα f M hdat
  obtain ⟨-, -, -, hmem4, -, -, hmem7⟩ :=
    Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_fk_mul α hα f M hdat
  -- the generic star-slot bound
  have hbound : ∀ (u : ℝ → ℝ → ℝ), Work.Spaces.HkMem α 6 u →
      Work.Spaces.HkSq α 6 u ≤ C3 * α ^ (-(2 : ℝ)) * Work.Spaces.HkSq α 6 f →
      ∀ c : ℝ, |c| ≤ 1 →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => c * u z θ) f|
        ≤ (C3 + 1) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f) := by
    intro u hmem hKu c hc
    rw [slotPairing_smul_left ρ a b c u f, abs_mul]
    have hcs : |Work.FTS.TransportS.slotPairing ρ a b u f|
        ≤ (Work.Spaces.HkSq α 6 u + Work.Spaces.HkSq α 6 f) / 2 :=
      Work.FTS.StrongPersist.H6Pair6Aux.SlotPairingHkSq hα0 hab hleaf hmem hdat.h6
    have hhalf : 0 ≤ (Work.Spaces.HkSq α 6 u + Work.Spaces.HkSq α 6 f) / 2 := by
      have h := Work.Spaces.HkSq_nonneg α 6 u
      linarith
    have h1 : |c| * |Work.FTS.TransportS.slotPairing ρ a b u f|
        ≤ (Work.Spaces.HkSq α 6 u + Work.Spaces.HkSq α 6 f) / 2 := by
      calc |c| * |Work.FTS.TransportS.slotPairing ρ a b u f|
          ≤ |c| * ((Work.Spaces.HkSq α 6 u + Work.Spaces.HkSq α 6 f) / 2) :=
            mul_le_mul_of_nonneg_left hcs (abs_nonneg c)
        _ ≤ 1 * ((Work.Spaces.HkSq α 6 u + Work.Spaces.HkSq α 6 f) / 2) :=
            mul_le_mul_of_nonneg_right hc hhalf
        _ = (Work.Spaces.HkSq α 6 u + Work.Spaces.HkSq α 6 f) / 2 := one_mul _
    exact le_trans h1 (by
      simpa using star_piece_shape (c := (1 : ℝ)) hα0 hα1 hC3pos.le hM0
        (Work.Spaces.HkSq_nonneg α 6 u) hH0 (by norm_num) (by norm_num) hKu)
  -- ## `nsP14 = -(1/2)·(FK f · D_θF_*)`
  have h14 : |Work.FTS.TransportS.slotPairing ρ a b
        (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP14 α f) f|
      ≤ (C3 + 1) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
          * (1 + Work.Spaces.HkSq α 6 f) := by
    have heq : Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP14 α f
        = fun z θ => (-(1 / 2)) * ((fun z θ => Work.Construction.FK f z
            * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) z θ) := by
      funext z θ
      simp only [Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP14,
        Work.FTS.StrongPersist.H6Rows.Npair6SupAux.coefKf,
        Work.FTS.StrongPersist.H6Rows.Npair6SupAux.slotTs]
      ring
    rw [heq]
    exact hbound (fun z θ => Work.Construction.FK f z
        * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) hmem4 hKdth (-(1 / 2))
      (by norm_num)
  -- ## `nsP18 = -sin²θ·(FK f · F_*)`
  have h18 : |Work.FTS.TransportS.slotPairing ρ a b
        (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP18 α f) f|
      ≤ (C3 + 1) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
          * (1 + Work.Spaces.HkSq α 6 f) := by
    have heq : Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP18 α f
        = fun z θ => (-1) * ((fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z
            * Work.Construction.Fstar α z θ) z θ) := by
      funext z θ
      simp only [Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP18,
        Work.FTS.StrongPersist.H6Rows.Npair6SupAux.angSin2,
        Work.FTS.StrongPersist.H6Rows.Npair6SupAux.coefKf,
        Work.FTS.StrongPersist.H6Rows.Npair6SupAux.slotFs]
      ring
    rw [heq]
    exact hbound (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z
        * Work.Construction.Fstar α z θ) hmem7 hKsin (-1) (by norm_num)
  exact ⟨by simpa only [hf] using h14, by simpa only [hf] using h18⟩

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowCoefSup =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open MeasureTheory

/-! ## `ℋ⁶`-scalar homogeneity of the squared norm

The squared `ℋ⁶`-integrand is a sum of squares of weighted slots, and every slot operator
(`D_z`, `D_θ` and their mixed iterates) commutes with scalar multiplication, so
`HkSq α k (c·f) = c² · HkSq α k f` (the squared-norm half of
`Work.FTS.EllipticEst.HkNorm_const_mul`). -/
private theorem hkSq_const_mul (α : ℝ) (k : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α k (fun z θ => c * f z θ) = c ^ 2 * Work.Spaces.HkSq α k f := by
  unfold Work.Spaces.HkSq
  have h1 : ∀ z : ℝ, (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ)
      = c ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
    intro z
    rw [show (fun θ => Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ)
        = fun θ => c ^ 2 * Work.Spaces.HkIntegrand α k f z θ from
      funext fun θ => Work.FTS.LocData.hkIntegrand_const_mul α k c f z θ]
    exact MeasureTheory.integral_const_mul _ _
  simp only [h1]
  exact MeasureTheory.integral_const_mul _ _

/-! ## Optimising the AM–GM slot bound

`Work.FTS.StrongPersist.H6Pair6Aux.SlotPairingHkSq` gives the *additive* bound
`|slotPairing ρ a b u f| ≤ (|u|²_{ℋ⁶} + |f|²_{ℋ⁶})/2`, which is quadratic in `|f|_{ℋ⁶}`.
Scaling the first argument (the pairing is `ℝ`-homogeneous in it) and optimising the scale turns
it into the *product* bound `≤ (1+|u|_{ℋ⁶})(1+|f|_{ℋ⁶})`: at scale `t > 0` the additive bound
reads `|P| ≤ (t n² + m²/t)/2`, and at `t = (m+1)/(n+1)` the two terms are `≤ (m+1)n` resp.
`≤ m(n+1)`. -/
private lemma amgm_opt {P n m : ℝ} (hn : 0 ≤ n) (hm : 0 ≤ m)
    (h : ∀ t : ℝ, 0 < t → |P| ≤ (t * n ^ 2 + m ^ 2 / t) / 2) :
    |P| ≤ (1 + n) * (1 + m) := by
  have hn1 : 0 < n + 1 := by linarith
  have hm1 : 0 < m + 1 := by linarith
  have ht : 0 < (m + 1) / (n + 1) := by positivity
  have h1 := h ((m + 1) / (n + 1)) ht
  have h2 : ((m + 1) / (n + 1)) * n ^ 2 ≤ (m + 1) * n := by
    have heq : ((m + 1) / (n + 1)) * n ^ 2 = (m + 1) * n ^ 2 / (n + 1) := by ring
    rw [heq, div_le_iff₀ hn1]
    nlinarith
  have h3 : m ^ 2 / ((m + 1) / (n + 1)) ≤ m * (n + 1) := by
    have heq : m ^ 2 / ((m + 1) / (n + 1)) = m ^ 2 * (n + 1) / (m + 1) := by
      field_simp
    rw [heq, div_le_iff₀ hm1]
    nlinarith
  refine h1.trans ?_
  have h4 : (m + 1) * n + m * (n + 1) ≤ 2 * ((1 + n) * (1 + m)) := by nlinarith
  linarith [add_le_add h2 h3, h4]

/-! ## The final arithmetic -/

private lemma arith_final {C₁ n KQ K0 K4 K6 M a3 : ℝ}
    (hC₁ : 0 ≤ C₁) (hKQ : 0 ≤ KQ) (hK0 : 0 ≤ K0) (hK4 : 0 ≤ K4) (hK6 : 0 ≤ K6)
    (hM : 0 ≤ M) (ha3 : 1 ≤ a3) (hn0 : 0 ≤ n)
    (hn : n ≤ C₁ * a3 * KQ * (1 + K0 + K4 + K6)) :
    (1 + n) ≤ (2 * C₁ + 2) * (a3 * (1 + KQ) * (1 + K0 + K4 + K6) * (1 + M)) := by
  have h2 : (1 : ℝ) ≤ 1 + KQ := by linarith
  have h3 : (1 : ℝ) ≤ 1 + K0 + K4 + K6 := by linarith
  have h4 : (1 : ℝ) ≤ 1 + M := by linarith
  have hA : (1 : ℝ) ≤ a3 * (1 + KQ) := by
    simpa using mul_le_mul ha3 h2 (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
  have hB : (1 : ℝ) ≤ a3 * (1 + KQ) * (1 + K0 + K4 + K6) := by
    simpa using mul_le_mul hA h3 (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
  have hD : (1 : ℝ) ≤ a3 * (1 + KQ) * (1 + K0 + K4 + K6) * (1 + M) := by
    simpa using mul_le_mul hB h4 (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
  have hD0 : (0 : ℝ) ≤ a3 * (1 + KQ) * (1 + K0 + K4 + K6) * (1 + M) := by linarith
  have hKQle : KQ ≤ 1 + KQ := by linarith
  have hM1 : (1 : ℝ) ≤ 1 + M := by linarith
  have hn' : n ≤ C₁ * (a3 * (1 + KQ) * (1 + K0 + K4 + K6) * (1 + M)) := by
    have e1 : C₁ * a3 * KQ * (1 + K0 + K4 + K6)
        ≤ C₁ * a3 * (1 + KQ) * (1 + K0 + K4 + K6) := by
      nlinarith [hKQle, hC₁, ha3, hK0, hK4, hK6]
    have e2 : C₁ * a3 * (1 + KQ) * (1 + K0 + K4 + K6)
        ≤ C₁ * a3 * (1 + KQ) * (1 + K0 + K4 + K6) * (1 + M) := by
      nlinarith [hM1, hC₁, ha3, hKQ, hK0, hK4, hK6]
    calc n ≤ C₁ * a3 * KQ * (1 + K0 + K4 + K6) := hn
      _ ≤ C₁ * a3 * (1 + KQ) * (1 + K0 + K4 + K6) := e1
      _ ≤ C₁ * a3 * (1 + KQ) * (1 + K0 + K4 + K6) * (1 + M) := e2
      _ = C₁ * (a3 * (1 + KQ) * (1 + K0 + K4 + K6) * (1 + M)) := by ring
  have hfin : (1 : ℝ) + n
      ≤ (C₁ + 1) * (a3 * (1 + KQ) * (1 + K0 + K4 + K6) * (1 + M)) := by
    nlinarith [hn', hD, hC₁]
  have hC1' : C₁ + 1 ≤ 2 * C₁ + 2 := by linarith
  nlinarith [hfin, mul_le_mul_of_nonneg_right hC1' hD0]

/-! ## The row

The slot pairing of the coefficient `A·Q` against the datum `f` — with `A` priced by its
`ℋ⁶`-norm (`CoefData`) and `Q` by its `𝒲^{6,∞}`-norm — is bounded by `α^{-3}` times the prices
`K0, K4, K6` of `A`, the price `KQ` of `Q`, the `ℋ⁴`-price `M` of `f` and the `ℋ⁶`-norm of `f`
— *linearly* in `HkNorm α 6 f`, which is what the level-six assembly needs.

Route: `Npair6SupAux.hknorm_mul_WlInf6_cd6'` (the `𝒲^{6,∞}`-priced product rule, applied with
`Q` as the `𝒲^{6,∞}`-factor and `A` as the `ℋ⁶`-factor) prices the coefficient `A·Q` in `ℋ⁶`
by `α^{-1/2} KQ K6`; the pointwise `AM–GM` slot estimate `SlotPairingHkSq` then bounds the
pairing by `(|A·Q|²_{ℋ⁶} + |f|²_{ℋ⁶})/2`, and optimising the scale (using the `ℝ`-homogeneity
of the pairing in its first slot, `SlotPairingConstMul`) converts this into the product bound
`(1+|A·Q|_{ℋ⁶})(1+|f|_{ℋ⁶})`, hence the linear-in-`HkNorm α 6 f` statement. -/
theorem rowCoefSup : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A Q f : Work.FTS.Galerkin.Fn) (K0 K4 K6 KQ M : ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      Work.FTS.EllipticEst.SmoothOpen Q → Work.Spaces.WlInfMem α 6 Q →
      Work.Spaces.WlInf α 6 Q ≤ KQ →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => A z θ * Q z θ) f|
        ≤ C * α ^ (-(3 : ℝ)) * (1 + KQ) * (1 + K0 + K4 + K6) * (1 + M)
            * (1 + Work.Spaces.HkNorm α 6 f) := by
  obtain ⟨C₁, hC₁pos, hProd⟩ :=
    Work.FTS.StrongPersist.H6Rows.Npair6SupAux.hknorm_mul_WlInf6_cd6'
  have hC₁0 : 0 ≤ C₁ := le_of_lt hC₁pos
  refine ⟨2 * C₁ + 2, by linarith, ?_⟩
  intro α hαI A Q f K0 K4 K6 KQ M a b ρ hcoef hdat hQsm hQm hQle hab hleaf
  have hα0 : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  -- the prices are nonnegative
  have hAn6 : Work.Spaces.HkNorm α 6 A ≤ K6 := hcoef.n6
  have hAn4 : Work.Spaces.HkNorm α 4 A ≤ K4 := hcoef.n4
  have hK6 : 0 ≤ K6 := le_trans (Work.Spaces.HkNorm_nonneg α 6 A) hAn6
  have hK4 : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hAn4
  have hKQ : 0 ≤ KQ :=
    le_trans (Work.FTS.StrongPersist.N6Trans.L6FBound.WlInf6_nonneg hQm) hQle
  have hM : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hdat.bdd
  have hK0 : 0 ≤ K0 := by
    have h := hcoef.val 1 (Real.pi / 4) (by norm_num) (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
    linarith [abs_nonneg (A 1 (Real.pi / 4))]
  have hα3 : 0 < α ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hα0 _
  set GU : ℝ → ℝ → ℝ := fun z θ => A z θ * Q z θ with hGU
  -- ## step 1: the product `A · Q` is `ℋ⁶`, priced by `KQ · K6 · α^{-1/2}`
  have hprod := hProd α Q A hα0 hα1 (hQsm.forall 6) hQm (hcoef.sm.forall 6) hcoef.h6
  have hfun : (fun z θ => Q z θ * A z θ) = GU := by
    funext z θ
    rw [hGU]
    ring
  rw [hfun] at hprod
  obtain ⟨hGmem, hGle⟩ := hprod
  have hn : Work.Spaces.HkNorm α 6 GU ≤ C₁ * α ^ (-(3 : ℝ)) * KQ * (1 + K0 + K4 + K6) := by
    refine hGle.trans ?_
    have hle13 : α ^ (-(1 / 2 : ℝ)) ≤ α ^ (-(3 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (by norm_num)
    have hW : 0 ≤ Work.Spaces.WlInf α 6 Q :=
      Work.FTS.StrongPersist.N6Trans.L6FBound.WlInf6_nonneg hQm
    have hAnn : 0 ≤ Work.Spaces.HkNorm α 6 A := Work.Spaces.HkNorm_nonneg α 6 A
    have hABC : C₁ * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 6 Q
        ≤ C₁ * α ^ (-(3 : ℝ)) * KQ :=
      mul_le_mul (mul_le_mul_of_nonneg_left hle13 hC₁0) hQle hW (by positivity)
    have hD : Work.Spaces.HkNorm α 6 A ≤ 1 + K0 + K4 + K6 := by linarith
    have hbig : (0 : ℝ) ≤ C₁ * α ^ (-(3 : ℝ)) * KQ :=
      mul_nonneg (mul_nonneg hC₁0 hα3.le) hKQ
    calc C₁ * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 6 Q * Work.Spaces.HkNorm α 6 A
        ≤ (C₁ * α ^ (-(3 : ℝ)) * KQ) * (1 + K0 + K4 + K6) := mul_le_mul hABC hD hAnn hbig
      _ = C₁ * α ^ (-(3 : ℝ)) * KQ * (1 + K0 + K4 + K6) := by ring
  -- ## step 2: the scaled `AM–GM` slot bound
  set n : ℝ := Work.Spaces.HkNorm α 6 GU with hn_def
  set m : ℝ := Work.Spaces.HkNorm α 6 f with hm_def
  have hn0 : 0 ≤ n := Work.Spaces.HkNorm_nonneg α 6 GU
  have hm0 : 0 ≤ m := Work.Spaces.HkNorm_nonneg α 6 f
  have hGsm : Work.FTS.EllipticEst.SmoothOpen GU :=
    Work.FTS.StrongPersist.N6TPPriced.SmoothOpen.mul hcoef.sm hQsm
  have hGUsq : Work.Spaces.HkSq α 6 GU = n ^ 2 := by
    rw [hn_def, Work.Spaces.HkNorm]
    exact (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 GU)).symm
  have hfsq : Work.Spaces.HkSq α 6 f = m ^ 2 := by
    rw [hm_def, Work.Spaces.HkNorm]
    exact (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 f)).symm
  have hPair : ∀ t : ℝ, 0 < t → |Work.FTS.TransportS.slotPairing ρ a b GU f|
      ≤ (t * n ^ 2 + m ^ 2 / t) / 2 := by
    intro t ht
    have htne : t ≠ 0 := ne_of_gt ht
    have hmem_t : Work.Spaces.HkMem α 6 (fun z θ => t * GU z θ) :=
      Work.FTS.LocData.HkMem_const_mul α 6 t hGmem
    have hsp := Work.FTS.StrongPersist.H6Pair6Aux.SlotPairingHkSq (α := α) (a := a)
      (b := b) (ρ := ρ) (u := fun z θ => t * GU z θ) (f := f) hα0 hab hleaf hmem_t hdat.h6
    have hcm := Work.FTS.StrongPersist.H6Pair6Aux.SlotPairingConstMul (ρ := ρ) a b t
      (v := GU) (f := f) hGsm
    rw [hcm, abs_mul, abs_of_pos ht] at hsp
    have hsq_t : Work.Spaces.HkSq α 6 (fun z θ => t * GU z θ)
        = t ^ 2 * Work.Spaces.HkSq α 6 GU := hkSq_const_mul α 6 t GU
    rw [hsq_t, hGUsq, hfsq] at hsp
    -- `hsp : t * |pairing| ≤ (t^2 * n^2 + m^2) / 2`
    have hXt : (t * n ^ 2 + m ^ 2 / t) * t = t ^ 2 * n ^ 2 + m ^ 2 := by
      rw [add_mul, div_mul_cancel₀ _ htne]
      ring
    have hgoal : |Work.FTS.TransportS.slotPairing ρ a b GU f| * 2
        ≤ t * n ^ 2 + m ^ 2 / t := by
      have h1 : |Work.FTS.TransportS.slotPairing ρ a b GU f| * 2 * t
          ≤ (t * n ^ 2 + m ^ 2 / t) * t := by
        rw [hXt, show |Work.FTS.TransportS.slotPairing ρ a b GU f| * 2 * t
            = 2 * (t * |Work.FTS.TransportS.slotPairing ρ a b GU f|) by ring]
        linarith
      exact le_of_mul_le_mul_right h1 ht
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    exact hgoal
  have hmain : |Work.FTS.TransportS.slotPairing ρ a b GU f| ≤ (1 + n) * (1 + m) :=
    amgm_opt hn0 hm0 hPair
  -- ## step 3: the arithmetic
  have ha3one : (1 : ℝ) ≤ α ^ (-(3 : ℝ)) := by
    rw [Real.rpow_neg hα0.le]
    exact (one_le_inv₀ (Real.rpow_pos_of_pos hα0 3)).mpr
      (Real.rpow_le_one hα0.le hα1 (by norm_num))
  have hkey := arith_final hC₁0 hKQ hK0 hK4 hK6 hM ha3one hn0 hn
  have hm1 : (0 : ℝ) ≤ 1 + m := by linarith
  refine hmain.trans ?_
  have hshape : (2 * C₁ + 2) * α ^ (-(3 : ℝ)) * (1 + KQ) * (1 + K0 + K4 + K6) * (1 + M)
        * (1 + m)
      = (2 * C₁ + 2) * (α ^ (-(3 : ℝ)) * (1 + KQ) * (1 + K0 + K4 + K6) * (1 + M))
        * (1 + m) := by ring
  rw [hshape]
  exact mul_le_mul_of_nonneg_right hkey hm1

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
