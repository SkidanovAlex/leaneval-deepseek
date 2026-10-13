/-
Copyright: work module for the Elgindi finite-time singularity project.

# `H6N0Aux/N0row_defs` — the pieces of `N₀`, the `Q₀`-congruence of `slotPairing`, and the
small arithmetic helpers of the row `row_N0_pair`.

The seven pieces of `N₀ α (F_* + f) f` used by the level-six `N₀`-row are the seven
`slotPairing`-arguments

* `NA1` (the `F_*`-only combination `I^{N₀}_1 + I^{N₀}_2`, in the exact shape of
  `H6Rows.FstarI12H6`),
* `NA3 = (1/α)·(L₁₂(f)·f)`, `NA4a = (3/2α)·(L₁₂(f)·D_θF_*)`, `NA4b = (3/2α)·(L₁₂(f)·D_θf)`,
* `NA5a = (-1)·(L₁₂(f)·(c2m·D_zF_*))`, `NA5b = (-1)·(c2m·L₁₂(f)·D_zf)`,
* `NA6 = (-1)·(c2m·L₁₂(F_*)·D_zf)` (in the shape of `row_A_dz`).

Each is written in the *scaled / inner* shape that one of the proved rows
(`T3Row`, `T4bRowSlot`, `T45aRow`, `row_l12_dz`, `row_A_dz`) consumes.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SlotPairingConstMul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The coefficient functions of the `F_*`-pieces -/

/-- The coefficient `D_θ F_*` of the second half of `I^{N₀}_4`. -/
abbrev NA4 (α : ℝ) : ℝ → ℝ → ℝ := Work.Spaces.Dth (Work.Construction.Fstar α)

/-- The coefficient `c2m · D_zF_*` of the first half of `I^{N₀}_5`. -/
abbrev NA5 (α : ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  Work.Construction.c2m θ * Work.Spaces.Dz (Work.Construction.Fstar α) z θ

/-- The coefficient `c2m · L₁₂(F_*)` of `I^{N₀}_6`. -/
abbrev NA6 (α : ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z

/-! ## The seven pieces of `N₀` -/

/-- `I^{N₀}_1 + I^{N₀}_2` in the shape of `H6Rows.FstarI12H6`. -/
abbrev NA1 (α : ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  (3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.pth (Work.Construction.Fstar α) z θ
    - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ

/-- `I^{N₀}_3 = (1/α)·(L₁₂(f)·f)`. -/
abbrev NP3 (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (1 / α) * (Work.Construction.L12 f z * f z θ)

/-- `I^{N₀}_4` with the `F_*`-half of `∂_θF`, in the shape of `T45aRow`. -/
abbrev NP4a (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (3 / (2 * α)) * (Work.Construction.L12 f z * NA4 α z θ)

/-- `I^{N₀}_4` with the `f`-half of `∂_θF`, in the shape of `T4bRowSlot`. -/
abbrev NP4b (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (3 / (2 * α)) * (Work.Construction.L12 f z * Work.Spaces.Dth f z θ)

/-- `I^{N₀}_5` with the `F_*`-half of `D_zF`, in the shape of `T45aRow`. -/
abbrev NP5a (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (-1 : ℝ) * (Work.Construction.L12 f z * NA5 α z θ)

/-- `I^{N₀}_5` with the `f`-half of `D_zF`, in the shape of `T5bRow`/`row_l12_dz`. -/
abbrev NP5b (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (-1 : ℝ) * (Work.Construction.c2m θ * Work.Construction.L12 f z
    * Work.Spaces.Dz f z θ)

/-- `I^{N₀}_6`, in the shape of `row_A_dz`. -/
abbrev NP6 (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (-1 : ℝ) * (NA6 α z θ * Work.Spaces.Dz f z θ)

/-! ## The `Q₀`-congruence of the elementary slot pairing -/

/-- **The elementary slot pairing depends on its first argument only through its values on the
open quadrant.**  The derivatives `D_z^bD_θ^a` are local, so an equality of the two arguments
on the *open* quadrant `Q0` propagates to the slots there; the complement of `Q0` inside
`Iz × Iθ` is null. -/
theorem slotPairing_congr_Q0 (ρ : ℝ → ℝ → ℝ) (a b : ℕ) {u u' f : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry u) (Function.uncurry u') Work.FTS.EllipticEst.Q0) :
    Work.FTS.TransportS.slotPairing ρ a b u f
      = Work.FTS.TransportS.slotPairing ρ a b u' f := by
  unfold Work.FTS.TransportS.slotPairing
  refine Work.FTS.TransportS.setIntegral2_congr_Q0 (F := fun z θ =>
      ρ z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a f z θ)
    (G := fun z θ => ρ z θ * Work.Spaces.mixed b a u' z θ * Work.Spaces.mixed b a f z θ) ?_
  intro p hp
  have h1 := Work.FTS.TransportS.DthIter_congrOn Work.FTS.EllipticEst.isOpen_Q0 h a
  have h2 := Work.FTS.TransportS.DzIter_congrOn Work.FTS.EllipticEst.isOpen_Q0 h1 b
  have hm : Work.Spaces.mixed b a u p.1 p.2 = Work.Spaces.mixed b a u' p.1 p.2 := h2 hp
  simp only [Function.uncurry]
  rw [hm]

/-! ## Scaling a per-slot bound -/

/-- **A per-slot bound scales.**  If every leaf slot of `v` against `f` is bounded by `Bv`, then
the same holds for the scalar multiple `c·v`, with the constant `|c|·Bv` (by the homogeneity
`SlotPairingConstMul`). -/
theorem slot_bound_scale {α : ℝ} {f : ℝ → ℝ → ℝ} (c Bv : ℝ) {v : ℝ → ℝ → ℝ}
    (hv : Work.FTS.EllipticEst.SmoothOpen v)
    (hB : ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 →
      Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b v f| ≤ Bv) :
    ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => c * v z θ) f| ≤ |c| * Bv := by
  intro a b ρ hab hρ
  rw [SlotPairingConstMul (ρ := ρ) a b c hv, abs_mul]
  exact mul_le_mul_of_nonneg_left (hB a b ρ hab hρ) (abs_nonneg c)

/-! ## The elementary `α`-arithmetic -/

/-- `α ^ (-m) ≤ α ^ (-(10:ℝ))` for `0 < α ≤ 1` and `m ≤ 10`. -/
theorem rpow_neg_le_neg_ten {α m : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hm : m ≤ 10) :
    α ^ (-m) ≤ α ^ (-(10 : ℝ)) := by
  have h : α ^ (-m) = α ^ (10 - m) * α ^ (-(10 : ℝ)) := by
    rw [← Real.rpow_add hα0]
    ring_nf
  rw [h]
  have hle : α ^ (10 - m) ≤ 1 := Real.rpow_le_one hα0.le hα1 (by linarith)
  calc α ^ (10 - m) * α ^ (-(10 : ℝ)) ≤ 1 * α ^ (-(10 : ℝ)) :=
        mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hα0.le _)
    _ = α ^ (-(10 : ℝ)) := one_mul _

/-- `1 ≤ α ^ (-(10:ℝ))` for `0 < α ≤ 1`. -/
theorem one_le_rpow_neg_ten {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (1 : ℝ) ≤ α ^ (-(10 : ℝ)) := by
  rw [Real.rpow_neg hα0.le, show (10 : ℝ) = ((10 : ℕ) : ℝ) from by norm_num,
    Real.rpow_natCast]
  exact (one_le_inv₀ (by positivity : (0 : ℝ) < α ^ 10)).mpr (pow_le_one₀ hα0.le hα1)

/-- The natural power `α ^ 2` and the real power `α ^ (2:ℝ)` coincide. -/
theorem natPow_two_eq_rpow (α : ℝ) : α ^ 2 = α ^ (2 : ℝ) := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]

/-- `√t ≤ 1 + t` for `t ≥ 0`. -/
theorem sqrt_le_one_add {t : ℝ} (ht : 0 ≤ t) : Real.sqrt t ≤ 1 + t := by
  rw [Real.sqrt_le_iff]
  constructor
  · linarith
  · nlinarith

/-! ## Smoothness of the pieces -/

theorem smoothOpen_NA1 (α : ℝ) : Work.FTS.EllipticEst.SmoothOpen (NA1 α) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (3 / (2 * α))
      * Work.Construction.s2 θ * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.pth (Work.Construction.Fstar α) z θ) :=
    so_mul (so_mul (so_const_mul (3 / (2 * α)) (so_snd contDiff_s2))
      (smoothOpen_L12_Fstar α)) (smoothOpen_Fstar α).pth
  have h2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) :=
    so_mul (so_mul (so_snd contDiff_c2m) (smoothOpen_L12_Fstar α)) (smoothOpen_Fstar α).Dz
  have h12 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => ((3 / (2 * α))
      * Work.Construction.s2 θ * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.pth (Work.Construction.Fstar α) z θ)
      - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) :=
    so_sub h1 h2
  exact h12

theorem smoothOpen_NA4 (α : ℝ) : Work.FTS.EllipticEst.SmoothOpen (NA4 α) :=
  (smoothOpen_Fstar α).Dth

theorem smoothOpen_NA5 (α : ℝ) : Work.FTS.EllipticEst.SmoothOpen (NA5 α) :=
  so_mul (so_snd contDiff_c2m) (smoothOpen_Fstar α).Dz

theorem smoothOpen_NA6 (α : ℝ) : Work.FTS.EllipticEst.SmoothOpen (NA6 α) :=
  so_mul (so_snd contDiff_c2m) (smoothOpen_L12_Fstar α)

theorem smoothOpen_NP3 {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 f z)) :
    Work.FTS.EllipticEst.SmoothOpen (NP3 α f) :=
  so_const_mul (1 / α) (so_mul hL hf)

theorem smoothOpen_NP4a {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 f z)) :
    Work.FTS.EllipticEst.SmoothOpen (NP4a α f) :=
  so_const_mul (3 / (2 * α)) (so_mul hL (smoothOpen_NA4 α))

theorem smoothOpen_NP4b {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 f z)) :
    Work.FTS.EllipticEst.SmoothOpen (NP4b α f) :=
  so_const_mul (3 / (2 * α)) (so_mul hL hf.Dth)

theorem smoothOpen_NP5a {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 f z)) :
    Work.FTS.EllipticEst.SmoothOpen (NP5a α f) :=
  so_const_mul (-1) (so_mul hL (smoothOpen_NA5 α))

theorem smoothOpen_NP5b {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 f z)) :
    Work.FTS.EllipticEst.SmoothOpen (NP5b α f) :=
  so_const_mul (-1) (so_mul (so_mul (so_snd contDiff_c2m) hL) hf.Dz)

theorem smoothOpen_NP6 {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 f z)) :
    Work.FTS.EllipticEst.SmoothOpen (NP6 α f) :=
  so_const_mul (-1) (so_mul (smoothOpen_NA6 α) hf.Dz)


/-- `α ^ s ≤ α ^ (-(10:ℝ))` for `0 < α ≤ 1` and `s ≥ -10`. -/
theorem rpow_le_neg_ten_of {α s : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hs : -10 ≤ s) :
    α ^ s ≤ α ^ (-(10 : ℝ)) := by
  rw [show s = -(-s) from by ring]
  exact rpow_neg_le_neg_ten hα0 hα1 (by linarith)

/-- `c·(1+S) ≤ (c+1)·α^{-10}·(1+X)^4·(1+S)`. -/
theorem majorant_base {α X S c : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hX : 0 ≤ X) (hS : 0 ≤ S)
    (hc : 0 ≤ c) :
    c * (1 + S) ≤ (c + 1) * (α ^ (-(10 : ℝ)) * (1 + X) ^ 4 * (1 + S)) := by
  have hA10 : (1 : ℝ) ≤ α ^ (-(10 : ℝ)) := one_le_rpow_neg_ten hα0 hα1
  have hX1 : (1 : ℝ) ≤ (1 + X) ^ 4 := by
    calc (1 : ℝ) = 1 ^ 4 := by norm_num
      _ ≤ (1 + X) ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
  have hbase : (1 : ℝ) ≤ α ^ (-(10 : ℝ)) * (1 + X) ^ 4 := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ α ^ (-(10 : ℝ)) * (1 + X) ^ 4 :=
          mul_le_mul hA10 hX1 (by norm_num) (Real.rpow_nonneg hα0.le _)
  have hS1 : (0 : ℝ) ≤ 1 + S := by linarith
  calc c * (1 + S) ≤ (c + 1) * (1 + S) := mul_le_mul_of_nonneg_right (by linarith) hS1
    _ ≤ (c + 1) * ((α ^ (-(10 : ℝ)) * (1 + X) ^ 4) * (1 + S)) := by
        calc (c + 1) * (1 + S) = (c + 1) * (1 * (1 + S)) := by ring
          _ ≤ (c + 1) * ((α ^ (-(10 : ℝ)) * (1 + X) ^ 4) * (1 + S)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbase hS1) (by linarith)
    _ = (c + 1) * (α ^ (-(10 : ℝ)) * (1 + X) ^ 4 * (1 + S)) := by ring

/-- `c·α^m·(1+X)^4·(1+S) ≤ (c+1)·α^{-10}·(1+X)^4·(1+S)` for `m ≥ -10`. -/
theorem majorant_rpow {α X S c m : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hX : 0 ≤ X)
    (hS : 0 ≤ S) (hc : 0 ≤ c) (hm : -10 ≤ m) :
    c * α ^ m * (1 + X) ^ 4 * (1 + S)
      ≤ (c + 1) * (α ^ (-(10 : ℝ)) * (1 + X) ^ 4 * (1 + S)) := by
  have hpow : α ^ m ≤ α ^ (-(10 : ℝ)) := rpow_le_neg_ten_of hα0 hα1 hm
  have hA : 0 ≤ (1 + X) ^ 4 * (1 + S) := mul_nonneg (by positivity) (by linarith)
  have hm10 : 0 ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα0.le _
  calc c * α ^ m * (1 + X) ^ 4 * (1 + S)
      = c * (α ^ m * ((1 + X) ^ 4 * (1 + S))) := by ring
    _ ≤ c * (α ^ (-(10 : ℝ)) * ((1 + X) ^ 4 * (1 + S))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hA) hc
    _ ≤ (c + 1) * (α ^ (-(10 : ℝ)) * ((1 + X) ^ 4 * (1 + S))) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hm10 hA)
    _ = (c + 1) * (α ^ (-(10 : ℝ)) * (1 + X) ^ 4 * (1 + S)) := by ring

/-- `(1/α)·c·α^{-3}·A ≤ (c+1)·(α^{-10}·A)`. -/
theorem inv_three {α c A : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hc : 0 ≤ c) (hA : 0 ≤ A) :
    (1 / α) * c * α ^ (-(3 : ℝ)) * A ≤ (c + 1) * (α ^ (-(10 : ℝ)) * A) := by
  have hpow : α ^ (-(1 : ℝ)) * α ^ (-(3 : ℝ)) = α ^ (-(4 : ℝ)) := by
    rw [← Real.rpow_add hα0]; norm_num
  have h4 : α ^ (-(4 : ℝ)) ≤ α ^ (-(10 : ℝ)) := rpow_le_neg_ten_of hα0 hα1 (by norm_num)
  have h10 : 0 ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα0.le _
  calc (1 / α) * c * α ^ (-(3 : ℝ)) * A
      = c * (α ^ (-(1 : ℝ)) * α ^ (-(3 : ℝ))) * A := by
        rw [show (1 : ℝ) / α = α ^ (-(1 : ℝ)) from by rw [Real.rpow_neg_one, one_div]]
        ring
    _ = c * α ^ (-(4 : ℝ)) * A := by rw [hpow]
    _ ≤ c * α ^ (-(10 : ℝ)) * A :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hc) hA
    _ ≤ (c + 1) * (α ^ (-(10 : ℝ)) * A) := by
        have hle : c * α ^ (-(10 : ℝ)) ≤ (c + 1) * α ^ (-(10 : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith) h10
        calc c * α ^ (-(10 : ℝ)) * A = (c * α ^ (-(10 : ℝ))) * A := rfl
          _ ≤ ((c + 1) * α ^ (-(10 : ℝ))) * A := mul_le_mul_of_nonneg_right hle hA
          _ = (c + 1) * (α ^ (-(10 : ℝ)) * A) := by ring

/-- `(1/α)·(c·W)·α^{-3}·A ≤ (c·Cd+1)·(α^{-10}·A)` for `W ≤ Cd·α^e`, `e ≥ 0`. -/
theorem inv_W_three {α c W Cd A e : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hW0 : 0 ≤ W)
    (hW : W ≤ Cd * α ^ e) (hCd : 0 ≤ Cd) (he : 0 ≤ e) (hc : 0 ≤ c) (hA : 0 ≤ A) :
    (1 / α) * (c * W) * α ^ (-(3 : ℝ)) * A ≤ (c * Cd + 1) * (α ^ (-(10 : ℝ)) * A) := by
  have hpow : α ^ (-(1 : ℝ)) * α ^ (-(3 : ℝ)) = α ^ (-(4 : ℝ)) := by
    rw [← Real.rpow_add hα0]; norm_num
  have hm4 : -10 ≤ e - 4 := by linarith
  have hW4 : W * α ^ (-(4 : ℝ)) ≤ Cd * α ^ (-(10 : ℝ)) := by
    have h1 : W * α ^ (-(4 : ℝ)) ≤ (Cd * α ^ e) * α ^ (-(4 : ℝ)) :=
      mul_le_mul_of_nonneg_right hW (Real.rpow_nonneg hα0.le _)
    have h2 : (Cd * α ^ e) * α ^ (-(4 : ℝ)) = Cd * α ^ (e - 4) := by
      rw [mul_assoc, ← Real.rpow_add hα0]
      ring_nf
    rw [h2] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_left (rpow_le_neg_ten_of hα0 hα1 hm4) hCd)
  have h10 : 0 ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα0.le _
  calc (1 / α) * (c * W) * α ^ (-(3 : ℝ)) * A
      = c * (W * (α ^ (-(1 : ℝ)) * α ^ (-(3 : ℝ)))) * A := by
        rw [show (1 : ℝ) / α = α ^ (-(1 : ℝ)) from by rw [Real.rpow_neg_one, one_div]]
        ring
    _ = c * (W * α ^ (-(4 : ℝ))) * A := by rw [hpow]
    _ ≤ c * (Cd * α ^ (-(10 : ℝ))) * A :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW4 hc) hA
    _ ≤ (c * Cd + 1) * (α ^ (-(10 : ℝ)) * A) := by
        have hle : c * (Cd * α ^ (-(10 : ℝ))) ≤ (c * Cd + 1) * α ^ (-(10 : ℝ)) :=
          calc c * (Cd * α ^ (-(10 : ℝ))) = (c * Cd) * α ^ (-(10 : ℝ)) := by ring
            _ ≤ (c * Cd + 1) * α ^ (-(10 : ℝ)) :=
                mul_le_mul_of_nonneg_right (by linarith) h10
        calc c * (Cd * α ^ (-(10 : ℝ))) * A
            = (c * (Cd * α ^ (-(10 : ℝ)))) * A := rfl
          _ ≤ ((c * Cd + 1) * α ^ (-(10 : ℝ))) * A := mul_le_mul_of_nonneg_right hle hA
          _ = (c * Cd + 1) * (α ^ (-(10 : ℝ)) * A) := by ring

/-- `c·W·α^{-3}·A ≤ (c·Cd+1)·(α^{-10}·A)` for `W ≤ Cd·α^e`, `e ≥ 0`. -/
theorem W_three {α c W Cd A e : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hW0 : 0 ≤ W)
    (hW : W ≤ Cd * α ^ e) (hCd : 0 ≤ Cd) (he : 0 ≤ e) (hc : 0 ≤ c) (hA : 0 ≤ A) :
    c * W * α ^ (-(3 : ℝ)) * A ≤ (c * Cd + 1) * (α ^ (-(10 : ℝ)) * A) := by
  have hm3 : -10 ≤ e - 3 := by linarith
  have hW3 : W * α ^ (-(3 : ℝ)) ≤ Cd * α ^ (-(10 : ℝ)) := by
    have h1 : W * α ^ (-(3 : ℝ)) ≤ (Cd * α ^ e) * α ^ (-(3 : ℝ)) :=
      mul_le_mul_of_nonneg_right hW (Real.rpow_nonneg hα0.le _)
    have h2 : (Cd * α ^ e) * α ^ (-(3 : ℝ)) = Cd * α ^ (e - 3) := by
      rw [mul_assoc, ← Real.rpow_add hα0]
      ring_nf
    rw [h2] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_left (rpow_le_neg_ten_of hα0 hα1 hm3) hCd)
  have h10 : 0 ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα0.le _
  calc c * W * α ^ (-(3 : ℝ)) * A = c * (W * α ^ (-(3 : ℝ))) * A := by ring
    _ ≤ c * (Cd * α ^ (-(10 : ℝ))) * A :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW3 hc) hA
    _ ≤ (c * Cd + 1) * (α ^ (-(10 : ℝ)) * A) := by
        have hle : c * (Cd * α ^ (-(10 : ℝ))) ≤ (c * Cd + 1) * α ^ (-(10 : ℝ)) :=
          calc c * (Cd * α ^ (-(10 : ℝ))) = (c * Cd) * α ^ (-(10 : ℝ)) := by ring
            _ ≤ (c * Cd + 1) * α ^ (-(10 : ℝ)) :=
                mul_le_mul_of_nonneg_right (by linarith) h10
        calc c * (Cd * α ^ (-(10 : ℝ))) * A
            = (c * (Cd * α ^ (-(10 : ℝ)))) * A := rfl
          _ ≤ ((c * Cd + 1) * α ^ (-(10 : ℝ))) * A := mul_le_mul_of_nonneg_right hle hA
          _ = (c * Cd + 1) * (α ^ (-(10 : ℝ)) * A) := by ring


/-- The standard majorant `α^{-10}·(1+|f|_{ℋ⁴})⁴·(1+|f|²_{ℋ⁶})` of the row. -/
abbrev NFact (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ :=
  α ^ (-(10 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)

/-- The triangle inequality for a seven-fold sum. -/
theorem abs_sum7_le (x1 x2 x3 x4 x5 x6 x7 : ℝ) :
    |x1 + x2 + x3 + x4 + x5 + x6 + x7|
      ≤ |x1| + |x2| + |x3| + |x4| + |x5| + |x6| + |x7| := by
  have h1 := abs_add_le (x1 + x2 + x3 + x4 + x5 + x6) x7
  have h2 := abs_add_le (x1 + x2 + x3 + x4 + x5) x6
  have h3 := abs_add_le (x1 + x2 + x3 + x4) x5
  have h4 := abs_add_le (x1 + x2 + x3) x4
  have h5 := abs_add_le (x1 + x2) x3
  have h6 := abs_add_le x1 x2
  linarith [abs_nonneg x1, abs_nonneg x2, abs_nonneg x3, abs_nonneg x4, abs_nonneg x5,
    abs_nonneg x6, abs_nonneg x7]

end Work.FTS.StrongPersist.H6Pair6Aux
