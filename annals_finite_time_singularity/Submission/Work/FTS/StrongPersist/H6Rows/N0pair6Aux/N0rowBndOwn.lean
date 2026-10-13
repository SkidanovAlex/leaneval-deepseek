/-
Copyright: work module for the Elgindi finite-time singularity project.

# `N0pair6Aux/N0rowBndOwn` — the per-slot bound for the `N₀`-row at the bare-`f` interface

This is `H6Pair6Aux.H6N0Aux.N0row_bounds` re-proved at the interface of
`Work.FTS.StrongPersist.H6Rows.N0pair6` (bare `f`, `H6Adm α f` + `HkMem α 7 f`).  Two changes
are needed there:

* the individual pieces of `N₀` are only known to be `C⁶` on the open quadrant (their
  coefficient `L₁₂(f)` is `ContDiffOn ℝ 7 (·) (Ioi 0)` by `UopHk.contDiffOn_L12_k`, and
  `SmoothOpen (fun z _ => L₁₂ f z)` is *not* available), so the pairing splits use
  `SlotPairingSplit6` (finite-order smoothness) and the scaling rule
  `slotPairing_const_mul_free` (which needs no smoothness at all);
* the `A·D_z f` slot row takes the σ-decay hypothesis of `N0pair6Aux.RowAdz` (satisfied by
  `c₂ₘ(θ)·L₁₂(F_*)(z)`, `N0pair6Aux.NA6sig`), instead of the too-weak pointwise bound of
  `H6Pair6Aux.H6N0Aux.row_A_dz`.

Everything else — the seven pieces of `N0row_defs`, the row `T3Row`/`T4bRowSlot`/`T45aRow`/
`row_l12_dz`, the `𝒲^{6,∞}`-data of `NA4`/`NA5`, and the arithmetic `inv_three`/`W_three`/
`inv_W_three`/`majorant_rpow`/`abs_sum7_le` of `N0row_defs` — is reused verbatim.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.N0row_defs
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.SlotPairingSplit6
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45AslotLe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

open Work.FTS.StrongPersist.H6Pair6Aux (NA1 NA4 NA5 NA6 NP3 NP4a NP4b NP5a NP5b NP6 NFact)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

/-- `D_z^bD_θ^a(c·v) = c·D_z^bD_θ^a v`, unconditionally. -/
theorem mixed_const_mul_free' (c : ℝ) (v : ℝ → ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.mixed j i (fun z θ => c * v z θ)
      = fun z θ => c * Work.Spaces.mixed j i v z θ :=
  Work.FTS.StrongPersist.H6Pair6Aux.mixed_const_mul_pure c v j i

/-- **The elementary slot pairing is `ℝ`-homogeneous in its first slot** — with no
smoothness hypothesis (the existing `SlotPairingConstMul` carries an unused `SmoothOpen v`). -/
theorem slotPairingConstMulFree {ρ : ℝ → ℝ → ℝ} (a b : ℕ) (c : ℝ) {v f : ℝ → ℝ → ℝ} :
    Work.FTS.TransportS.slotPairing ρ a b (fun z θ => c * v z θ) f
      = c * Work.FTS.TransportS.slotPairing ρ a b v f := by
  unfold Work.FTS.TransportS.slotPairing
  rw [mixed_const_mul_free' c v b a]
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

/-- **A per-slot bound scales** (no smoothness needed). -/
theorem slotBoundScaleFree {α : ℝ} {f : ℝ → ℝ → ℝ} (c Bv : ℝ) {v : ℝ → ℝ → ℝ}
    (hB : ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 →
      Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b v f| ≤ Bv) :
    ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => c * v z θ) f| ≤ |c| * Bv := by
  intro a b ρ hab hρ
  rw [slotPairingConstMulFree a b c, abs_mul]
  exact mul_le_mul_of_nonneg_left (hB a b ρ hab hρ) (abs_nonneg c)


/-- The sum of two `C⁶` functions on the open quadrant is `C⁶` there. -/
theorem contDiffOnAdd6 {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ 6 (Function.uncurry (fun z θ => f z θ + g z θ))
      Work.FTS.EllipticEst.Q0 := by
  have h : Function.uncurry (fun z θ => f z θ + g z θ)
      = Function.uncurry f + Function.uncurry g := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [h]; exact hf.add hg

/-- **The per-slot bound for the seven-fold sum of the pieces of `N₀`** at the bare-`f`
interface.  The seven rows are supplied as hypotheses (they are the conclusions of
`slot_cs6`, `T3Row`, `T45aRow`, `T4bRowSlot`, `row_l12_dz` and `RowAdz` instantiated at `α`),
and the conclusion is the level-six per-slot bound by
`KS · α^{-10}(1+|f|_{ℋ⁴})⁴(1+|f|²_{ℋ⁶})`. -/
theorem N0rowBounds6 {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf6 : ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hm6 : Work.Spaces.HkMem α 6 f)
    (C3 C4b C5b C45 C6 K12 Cd1 Cd2 CN : ℝ)
    (hC3 : 0 ≤ C3) (hC4b : 0 ≤ C4b) (hC5b : 0 ≤ C5b) (hC45 : 0 ≤ C45) (hC6 : 0 ≤ C6)
    (hK12 : 0 ≤ K12) (hCd1 : 0 ≤ Cd1) (hCd2 : 0 ≤ Cd2) (hCN : 0 ≤ CN)
    (rowcs : ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
        |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => NA1 α z θ) f|
          ≤ Work.Spaces.HkNorm α 6 (NA1 α) * Work.Spaces.HkNorm α 6 f)
    (h12bd : Work.Spaces.HkNorm α 6 (NA1 α) ≤ K12 * α ^ (2 : ℝ))
    (row3 : ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
        |Work.FTS.TransportS.slotPairing ρ a b
          (fun z θ => Work.Construction.L12 f z * f z θ) f|
          ≤ C3 * α ^ (-(3 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f))
    (row4b : ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
        |Work.FTS.TransportS.slotPairing ρ a b
          (fun z θ => Work.Construction.L12 f z * Work.Spaces.Dth f z θ) f|
          ≤ C4b * α ^ (-(3 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f))
    (row45 : ∀ (A : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ) (K : ℝ),
        Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.WlInfMem α 6 A →
        Work.Spaces.WlInf α 6 A ≤ K → a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
        |Work.FTS.TransportS.slotPairing ρ a b
          (fun z θ => Work.Construction.L12 f z * A z θ) f|
          ≤ C45 * K * α ^ (-(3 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f))
    (row5b : ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
        |Work.FTS.TransportS.slotPairing ρ a b
          (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 f z
            * Work.Spaces.Dz f z θ) f|
          ≤ C5b * α ^ (-(3 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f))
    (row6 : ∀ (A : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ) (K : ℝ),
        Work.FTS.EllipticEst.SmoothOpen A → 0 ≤ K →
        (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ j i : ℕ, i + j ≤ 6 →
          |Work.Spaces.mixed j i A z θ| ≤ K * (if i = 0 then 1 else Real.sin (2 * θ))) →
        a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
        |Work.FTS.TransportS.slotPairing ρ a b
          (fun z θ => A z θ * Work.Spaces.Dz f z θ) f|
          ≤ C6 * K * α ^ (-(3 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f))
    (hm3 : Work.Spaces.HkMem α 6 (NP3 α f)) (hm4a : Work.Spaces.HkMem α 6 (NP4a α f))
    (hm4b : Work.Spaces.HkMem α 6 (NP4b α f)) (hm5a : Work.Spaces.HkMem α 6 (NP5a α f))
    (hm5b : Work.Spaces.HkMem α 6 (NP5b α f)) (hm6' : Work.Spaces.HkMem α 6 (NP6 α f))
    (hsm3 : ContDiffOn ℝ 6 (Function.uncurry (NP3 α f)) Work.FTS.EllipticEst.Q0)
    (hsm4a : ContDiffOn ℝ 6 (Function.uncurry (NP4a α f)) Work.FTS.EllipticEst.Q0)
    (hsm4b : ContDiffOn ℝ 6 (Function.uncurry (NP4b α f)) Work.FTS.EllipticEst.Q0)
    (hsm5a : ContDiffOn ℝ 6 (Function.uncurry (NP5a α f)) Work.FTS.EllipticEst.Q0)
    (hsm5b : ContDiffOn ℝ 6 (Function.uncurry (NP5b α f)) Work.FTS.EllipticEst.Q0)
    (hsm6' : ContDiffOn ℝ 6 (Function.uncurry (NP6 α f)) Work.FTS.EllipticEst.Q0)
    (hWl4mem : Work.Spaces.WlInfMem α 6 (NA4 α))
    (hWl5mem : Work.Spaces.WlInfMem α 6 (NA5 α))
    (hWl4 : Work.Spaces.WlInf α 6 (NA4 α) ≤ Cd1 * α ^ (2 : ℝ))
    (hWl5 : Work.Spaces.WlInf α 6 (NA5 α) ≤ Cd2 * α)
    (h12mem : Work.Spaces.HkMem α 6 (fun z θ => NA1 α z θ))
    (hNA6 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ j i : ℕ, i + j ≤ 6 →
        |Work.Spaces.mixed j i (NA6 α) z θ| ≤ CN * (if i = 0 then 1 else Real.sin (2 * θ))) :
    ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => NA1 α z θ + NP3 α f z θ
        + NP4a α f z θ + NP4b α f z θ + NP5a α f z θ + NP5b α f z θ + NP6 α f z θ) f|
        ≤ ((K12 + 1) + (C3 + 1) + ((3 / 2) * (C45 * Cd1 + 1)) + ((3 / 2) * (C4b + 1))
            + (C45 * Cd2 + 1) + (C5b + 1) + (C6 * CN + 1))
          * NFact α f := by
  have hXnn : 0 ≤ Work.FTS.Nonlin.Xn α f := Real.sqrt_nonneg _
  have hSqnn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hSleFact : (1 + Work.Spaces.HkSq α 6 f) ≤ NFact α f := by
    simp only [NFact]
    have hA10 : (1 : ℝ) ≤ α ^ (-(10 : ℝ)) :=
      Work.FTS.StrongPersist.H6Pair6Aux.one_le_rpow_neg_ten hα0 hα1
    have hX1 : (1 : ℝ) ≤ (1 + Work.FTS.Nonlin.Xn α f) ^ 4 := by
      calc (1 : ℝ) = 1 ^ 4 := by norm_num
        _ ≤ (1 + Work.FTS.Nonlin.Xn α f) ^ 4 :=
            pow_le_pow_left₀ (by norm_num) (by linarith) 4
    have hbase : (1 : ℝ) ≤ α ^ (-(10 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4 := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ α ^ (-(10 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4 :=
            mul_le_mul hA10 hX1 (by norm_num) (Real.rpow_nonneg hα0.le _)
    calc (1 + Work.Spaces.HkSq α 6 f)
        = 1 * (1 + Work.Spaces.HkSq α 6 f) := by ring
      _ ≤ (α ^ (-(10 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4)
            * (1 + Work.Spaces.HkSq α 6 f) :=
          mul_le_mul_of_nonneg_right hbase (by linarith)
      _ = α ^ (-(10 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f) := by ring
  -- ## the smoothness of the pieces
  have hP12sm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => NA1 α z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NA1 α
  have hA4 : Work.FTS.EllipticEst.SmoothOpen (NA4 α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NA4 α
  have hA5 : Work.FTS.EllipticEst.SmoothOpen (NA5 α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NA5 α
  have hA6 : Work.FTS.EllipticEst.SmoothOpen (NA6 α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NA6 α
  -- ## the bound for `NA1`
  have hb1 : ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => NA1 α z θ) f| ≤ (K12 + 1) * NFact α f := by
    intro a b ρ hab hρ
    have h1 := rowcs a b ρ hab hρ
    have hsq : Work.Spaces.HkNorm α 6 f ≤ 1 + Work.Spaces.HkSq α 6 f :=
      Work.FTS.StrongPersist.H6Pair6Aux.sqrt_le_one_add hSqnn
    have ha2 : α ^ (2 : ℝ) ≤ 1 := Real.rpow_le_one hα0.le hα1 (by norm_num)
    have hstep : K12 * α ^ (2 : ℝ) ≤ K12 := by
      calc K12 * α ^ (2 : ℝ) ≤ K12 * 1 := mul_le_mul_of_nonneg_left ha2 hK12
        _ = K12 := by ring
    have h2 : Work.Spaces.HkNorm α 6 (NA1 α) * Work.Spaces.HkNorm α 6 f
        ≤ K12 * (1 + Work.Spaces.HkSq α 6 f) := by
      calc Work.Spaces.HkNorm α 6 (NA1 α) * Work.Spaces.HkNorm α 6 f
          ≤ (K12 * α ^ (2 : ℝ)) * (1 + Work.Spaces.HkSq α 6 f) :=
            mul_le_mul h12bd hsq (Real.sqrt_nonneg _) (by positivity)
        _ ≤ K12 * (1 + Work.Spaces.HkSq α 6 f) :=
            mul_le_mul_of_nonneg_right hstep (by linarith)
    refine le_trans (le_trans h1 h2) ?_
    calc K12 * (1 + Work.Spaces.HkSq α 6 f)
        ≤ (K12 + 1) * (1 + Work.Spaces.HkSq α 6 f) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ ≤ (K12 + 1) * NFact α f := mul_le_mul_of_nonneg_left hSleFact (by linarith)
  -- ## `NP3`
  have hb3 : ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (NP3 α f) f| ≤ (C3 + 1) * NFact α f := by
    intro a b ρ hab hρ
    have h := slotBoundScaleFree (α := α) (f := f) (1 / α)
      (C3 * α ^ (-(3 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
        * (1 + Work.Spaces.HkSq α 6 f))
      (fun a b ρ hab hρ => row3 a b ρ hab hρ)
    have h2 := h a b ρ hab hρ
    rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / α)] at h2
    refine le_trans h2 ?_
    have key := Work.FTS.StrongPersist.H6Pair6Aux.inv_three (α := α) (c := C3)
      (A := (1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f))
      hα0 hα1 hC3 (by positivity)
    calc (1 / α) * (C3 * α ^ (-(3 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
          * (1 + Work.Spaces.HkSq α 6 f))
        = (1 / α) * C3 * α ^ (-(3 : ℝ))
            * ((1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)) := by ring
      _ ≤ (C3 + 1) * (α ^ (-(10 : ℝ))
            * ((1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f))) := key
      _ = (C3 + 1) * NFact α f := by simp only [NFact]; ring
  -- ## `NP4b`
  have hb4b : ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (NP4b α f) f| ≤ ((3 / 2) * (C4b + 1)) * NFact α f := by
    intro a b ρ hab hρ
    have h := slotBoundScaleFree (α := α) (f := f) (3 / (2 * α))
      (C4b * α ^ (-(3 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
        * (1 + Work.Spaces.HkSq α 6 f))
      (fun a b ρ hab hρ => row4b a b ρ hab hρ)
    have h2 := h a b ρ hab hρ
    rw [abs_of_pos (by positivity : (0 : ℝ) < 3 / (2 * α))] at h2
    refine le_trans h2 ?_
    have key := Work.FTS.StrongPersist.H6Pair6Aux.inv_three (α := α) (c := C4b)
      (A := (1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f))
      hα0 hα1 hC4b (by positivity)
    calc (3 / (2 * α)) * (C4b * α ^ (-(3 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
          * (1 + Work.Spaces.HkSq α 6 f))
        = (3 / 2) * ((1 / α) * C4b * α ^ (-(3 : ℝ))
            * ((1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f))) := by ring
      _ ≤ (3 / 2) * ((C4b + 1) * (α ^ (-(10 : ℝ))
            * ((1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)))) :=
          mul_le_mul_of_nonneg_left key (by norm_num)
      _ = ((3 / 2) * (C4b + 1)) * NFact α f := by simp only [NFact]; ring
  -- ## `NP4a`
  have hb4a : ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (NP4a α f) f|
        ≤ ((3 / 2) * (C45 * Cd1 + 1)) * NFact α f := by
    intro a b ρ hab hρ
    have h := slotBoundScaleFree (α := α) (f := f) (3 / (2 * α))
      (C45 * (Work.Spaces.WlInf α 6 (NA4 α)) * α ^ (-(3 : ℝ))
        * (1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f))
      (fun a b ρ hab hρ => row45 (NA4 α) a b ρ (Work.Spaces.WlInf α 6 (NA4 α)) hA4
        hWl4mem le_rfl hab hρ)
    have h2 := h a b ρ hab hρ
    rw [abs_of_pos (by positivity : (0 : ℝ) < 3 / (2 * α))] at h2
    refine le_trans h2 ?_
    have hW0 : 0 ≤ Work.Spaces.WlInf α 6 (NA4 α) :=
      Work.FTS.StrongPersist.H6Pair6Aux.WlInf_nonneg α 6 (NA4 α) hWl4mem
    have key := Work.FTS.StrongPersist.H6Pair6Aux.inv_W_three (α := α) (c := C45)
      (W := Work.Spaces.WlInf α 6 (NA4 α)) (Cd := Cd1)
      (A := (1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)) (e := 2)
      hα0 hα1 hW0 hWl4 hCd1 (by norm_num) hC45 (by positivity)
    calc (3 / (2 * α)) * (C45 * (Work.Spaces.WlInf α 6 (NA4 α)) * α ^ (-(3 : ℝ))
          * (1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f))
        = (3 / 2) * ((1 / α) * (C45 * (Work.Spaces.WlInf α 6 (NA4 α))) * α ^ (-(3 : ℝ))
            * ((1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f))) := by ring
      _ ≤ (3 / 2) * ((C45 * Cd1 + 1) * (α ^ (-(10 : ℝ))
            * ((1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)))) :=
          mul_le_mul_of_nonneg_left key (by norm_num)
      _ = ((3 / 2) * (C45 * Cd1 + 1)) * NFact α f := by simp only [NFact]; ring
  -- ## `NP5a`
  have hb5a : ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (NP5a α f) f| ≤ (C45 * Cd2 + 1) * NFact α f := by
    intro a b ρ hab hρ
    have h := slotBoundScaleFree (α := α) (f := f) (-1 : ℝ)
      (C45 * (Work.Spaces.WlInf α 6 (NA5 α)) * α ^ (-(3 : ℝ))
        * (1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f))
      (fun a b ρ hab hρ => row45 (NA5 α) a b ρ (Work.Spaces.WlInf α 6 (NA5 α)) hA5
        hWl5mem le_rfl hab hρ)
    have h2 := h a b ρ hab hρ
    rw [show |(-1 : ℝ)| = 1 by norm_num, one_mul] at h2
    refine le_trans h2 ?_
    have hW0 : 0 ≤ Work.Spaces.WlInf α 6 (NA5 α) :=
      Work.FTS.StrongPersist.H6Pair6Aux.WlInf_nonneg α 6 (NA5 α) hWl5mem
    have key := Work.FTS.StrongPersist.H6Pair6Aux.W_three (α := α) (c := C45)
      (W := Work.Spaces.WlInf α 6 (NA5 α)) (Cd := Cd2)
      (A := (1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)) (e := 1)
      hα0 hα1 hW0 (by rw [Real.rpow_one]; exact hWl5) hCd2 (by norm_num) hC45 (by positivity)
    calc C45 * (Work.Spaces.WlInf α 6 (NA5 α)) * α ^ (-(3 : ℝ))
          * (1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)
        = C45 * (Work.Spaces.WlInf α 6 (NA5 α)) * α ^ (-(3 : ℝ))
            * ((1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)) := by ring
      _ ≤ (C45 * Cd2 + 1) * (α ^ (-(10 : ℝ))
            * ((1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f))) := key
      _ = (C45 * Cd2 + 1) * NFact α f := by simp only [NFact]; ring
  -- ## `NP5b`
  have hb5b : ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (NP5b α f) f| ≤ (C5b + 1) * NFact α f := by
    intro a b ρ hab hρ
    have h := slotBoundScaleFree (α := α) (f := f) (-1 : ℝ)
      (C5b * α ^ (-(3 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
        * (1 + Work.Spaces.HkSq α 6 f))
      (fun a b ρ hab hρ => row5b a b ρ hab hρ)
    have h2 := h a b ρ hab hρ
    rw [show |(-1 : ℝ)| = 1 by norm_num, one_mul] at h2
    refine le_trans h2 ?_
    have key := Work.FTS.StrongPersist.H6Pair6Aux.majorant_rpow (α := α)
      (X := Work.FTS.Nonlin.Xn α f) (S := Work.Spaces.HkSq α 6 f) (c := C5b) (m := -(3 : ℝ))
      hα0 hα1 hXnn hSqnn hC5b (by norm_num : (-10 : ℝ) ≤ -(3 : ℝ))
    calc C5b * α ^ (-(3 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
          * (1 + Work.Spaces.HkSq α 6 f)
        ≤ (C5b + 1) * (α ^ (-(10 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f)) := key
      _ = (C5b + 1) * NFact α f := by simp only [NFact] <;> ring
  -- ## `NP6`
  have hb6 : ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (NP6 α f) f| ≤ (C6 * CN + 1) * NFact α f := by
    intro a b ρ hab hρ
    have h := slotBoundScaleFree (α := α) (f := f) (-1 : ℝ)
      (v := fun z θ => NA6 α z θ * Work.Spaces.Dz f z θ)
      (C6 * CN * α ^ (-(3 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
        * (1 + Work.Spaces.HkSq α 6 f))
      (fun a b ρ hab hρ => row6 (NA6 α) a b ρ CN hA6 hCN hNA6 hab hρ)
    have h2 := h a b ρ hab hρ
    rw [show |(-1 : ℝ)| = 1 by norm_num, one_mul] at h2
    refine le_trans h2 ?_
    have key := Work.FTS.StrongPersist.H6Pair6Aux.majorant_rpow (α := α)
      (X := Work.FTS.Nonlin.Xn α f) (S := Work.Spaces.HkSq α 6 f) (c := C6 * CN)
      (m := -(3 : ℝ)) hα0 hα1 hXnn hSqnn (by positivity)
      (by norm_num : (-10 : ℝ) ≤ -(3 : ℝ))
    calc C6 * CN * α ^ (-(3 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
          * (1 + Work.Spaces.HkSq α 6 f)
        ≤ (C6 * CN + 1) * (α ^ (-(10 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f)) := key
      _ = (C6 * CN + 1) * NFact α f := by simp only [NFact] <;> ring
  -- ## the memberships of the partial sums
  have hA1c : ContDiffOn ℝ 6 (Function.uncurry (fun z θ => NA1 α z θ))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall (fun z θ => NA1 α z θ)).mp hP12sm 6
  have hc3 : ContDiffOn ℝ 6 (Function.uncurry (fun z θ => NP3 α f z θ))
      Work.FTS.EllipticEst.Q0 := hsm3
  have hc4a : ContDiffOn ℝ 6 (Function.uncurry (fun z θ => NP4a α f z θ))
      Work.FTS.EllipticEst.Q0 := hsm4a
  have hc4b : ContDiffOn ℝ 6 (Function.uncurry (fun z θ => NP4b α f z θ))
      Work.FTS.EllipticEst.Q0 := hsm4b
  have hc5a : ContDiffOn ℝ 6 (Function.uncurry (fun z θ => NP5a α f z θ))
      Work.FTS.EllipticEst.Q0 := hsm5a
  have hc5b : ContDiffOn ℝ 6 (Function.uncurry (fun z θ => NP5b α f z θ))
      Work.FTS.EllipticEst.Q0 := hsm5b
  have hc6 : ContDiffOn ℝ 6 (Function.uncurry (fun z θ => NP6 α f z θ))
      Work.FTS.EllipticEst.Q0 := hsm6'
  have hc13 : ContDiffOn ℝ 6 (Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ))
      Work.FTS.EllipticEst.Q0 := contDiffOnAdd6 hA1c hc3
  have hc134a : ContDiffOn ℝ 6
      (Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ))
      Work.FTS.EllipticEst.Q0 := contDiffOnAdd6 hc13 hc4a
  have hc134ab : ContDiffOn ℝ 6
      (Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ + NP4b α f z θ))
      Work.FTS.EllipticEst.Q0 := contDiffOnAdd6 hc134a hc4b
  have hc134ab5a : ContDiffOn ℝ 6
      (Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ + NP4b α f z θ
        + NP5a α f z θ)) Work.FTS.EllipticEst.Q0 := contDiffOnAdd6 hc134ab hc5a
  have hc134ab5ab : ContDiffOn ℝ 6
      (Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ + NP4b α f z θ
        + NP5a α f z θ + NP5b α f z θ)) Work.FTS.EllipticEst.Q0 :=
    contDiffOnAdd6 hc134ab5a hc5b
  have hm13 : Work.Spaces.HkMem α 6 (fun z θ => NA1 α z θ + NP3 α f z θ) :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.hkMem_add_of_contDiffOn α 6 hA1c hc3 h12mem hm3
  have hm134a : Work.Spaces.HkMem α 6
      (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ) :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.hkMem_add_of_contDiffOn α 6 hc13 hc4a hm13 hm4a
  have hm134ab : Work.Spaces.HkMem α 6
      (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ + NP4b α f z θ) :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.hkMem_add_of_contDiffOn α 6 hc134a hc4b hm134a hm4b
  have hm134ab5a : Work.Spaces.HkMem α 6
      (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ + NP4b α f z θ + NP5a α f z θ) :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.hkMem_add_of_contDiffOn α 6 hc134ab hc5a
      hm134ab hm5a
  have hm134ab5ab : Work.Spaces.HkMem α 6
      (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ + NP4b α f z θ + NP5a α f z θ
        + NP5b α f z θ) :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.hkMem_add_of_contDiffOn α 6 hc134ab5a hc5b
      hm134ab5a hm5b
  -- ## the split and the triangle inequality
  intro a b ρ hab hρ
  rw [SlotPairingSplit6 (α := α) hα0 hab hρ
    (u₁ := fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ + NP4b α f z θ
      + NP5a α f z θ + NP5b α f z θ) (u₂ := fun z θ => NP6 α f z θ)
    hc134ab5ab hc6 hf6 hm134ab5ab hm6' hm6]
  rw [SlotPairingSplit6 (α := α) hα0 hab hρ
    (u₁ := fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ + NP4b α f z θ
      + NP5a α f z θ) (u₂ := fun z θ => NP5b α f z θ)
    hc134ab5a hc5b hf6 hm134ab5a hm5b hm6]
  rw [SlotPairingSplit6 (α := α) hα0 hab hρ
    (u₁ := fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ + NP4b α f z θ)
    (u₂ := fun z θ => NP5a α f z θ)
    hc134ab hc5a hf6 hm134ab hm5a hm6]
  rw [SlotPairingSplit6 (α := α) hα0 hab hρ
    (u₁ := fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ) (u₂ := fun z θ => NP4b α f z θ)
    hc134a hc4b hf6 hm134a hm4b hm6]
  rw [SlotPairingSplit6 (α := α) hα0 hab hρ
    (u₁ := fun z θ => NA1 α z θ + NP3 α f z θ) (u₂ := fun z θ => NP4a α f z θ)
    hc13 hc4a hf6 hm13 hm4a hm6]
  rw [SlotPairingSplit6 (α := α) hα0 hab hρ
    (u₁ := fun z θ => NA1 α z θ) (u₂ := fun z θ => NP3 α f z θ)
    hA1c hc3 hf6 h12mem hm3 hm6]
  have h1 := hb1 a b ρ hab hρ
  have h2 := hb3 a b ρ hab hρ
  have h3 := hb4a a b ρ hab hρ
  have h4 := hb4b a b ρ hab hρ
  have h5 := hb5a a b ρ hab hρ
  have h6 := hb5b a b ρ hab hρ
  have h7 := hb6 a b ρ hab hρ
  have htri := Work.FTS.StrongPersist.H6Pair6Aux.abs_sum7_le
    (Work.FTS.TransportS.slotPairing ρ a b (fun z θ => NA1 α z θ) f)
    (Work.FTS.TransportS.slotPairing ρ a b (NP3 α f) f)
    (Work.FTS.TransportS.slotPairing ρ a b (NP4a α f) f)
    (Work.FTS.TransportS.slotPairing ρ a b (NP4b α f) f)
    (Work.FTS.TransportS.slotPairing ρ a b (NP5a α f) f)
    (Work.FTS.TransportS.slotPairing ρ a b (NP5b α f) f)
    (Work.FTS.TransportS.slotPairing ρ a b (NP6 α f) f)
  refine le_trans htri ?_
  have hF0 : (0 : ℝ) ≤ NFact α f := by
    simp only [NFact]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hα0.le _) (by positivity)) (by linarith)
  have hc1 : (0 : ℝ) ≤ (K12 + 1) * NFact α f := by positivity
  have hc3 : (0 : ℝ) ≤ (C3 + 1) * NFact α f := by positivity
  have hc4a : (0 : ℝ) ≤ ((3 / 2) * (C45 * Cd1 + 1)) * NFact α f := by positivity
  have hc4b : (0 : ℝ) ≤ ((3 / 2) * (C4b + 1)) * NFact α f := by positivity
  have hc5a : (0 : ℝ) ≤ (C45 * Cd2 + 1) * NFact α f := by positivity
  have hc5b : (0 : ℝ) ≤ (C5b + 1) * NFact α f := by positivity
  have hc6 : (0 : ℝ) ≤ (C6 * CN + 1) * NFact α f := by positivity
  nlinarith [h1, h2, h3, h4, h5, h6, h7, hc1, hc3, hc4a, hc4b, hc5a, hc5b, hc6]

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
