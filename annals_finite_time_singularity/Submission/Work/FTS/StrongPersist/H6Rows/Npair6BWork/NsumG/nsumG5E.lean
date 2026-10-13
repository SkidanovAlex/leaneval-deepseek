import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.NDefs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_fk_mul
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkStarPieces
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SlotPairingHkSq
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SlotPairingConstMul
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs

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
