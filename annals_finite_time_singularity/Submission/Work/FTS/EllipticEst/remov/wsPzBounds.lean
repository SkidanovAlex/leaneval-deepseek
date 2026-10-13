/-
Copyright: work module for the Elgindi finite-time singularity project.

# `remov.wsPzBounds`: affine `θ`-energy bounds for `Ψ` and `∂_zΨ` on a compact radial interval

For a datum of the weak class `EllWeakPos α k F Ψ` with `k ≥ 1`, the `θ`-energies
`thetaE X s = ∫_θ X(s,θ)² sin(2θ)^{-η} dθ` of the slices `Ψ` and `∂_zΨ` are dominated, on every
compact radial interval `[a,b] ⊂ (0,∞)`, by the corresponding energies of their second
`θ`-derivatives:

* `thetaE Ψ s ≤ K (1 + thetaE (∂_θ²Ψ) s)`,
* `thetaE (∂_zΨ) s ≤ K (1 + thetaE (D_z ∂_θ²Ψ) s)`,

with a constant `K` depending only on `(a,b)`.

Both are instances of the pointwise slice bound `ws_slice_pointwise_le` — interior oscillation
control of `v` and `v'` by `v''` on `(0,π/2)` — applied to `v = Ψ(s,·)` and to `v = ∂_zΨ(s,·)`.
The first needs, in addition, only the smoothness of `Ψ` on the open quadrant and the
`ℋ^k`-membership of `∂_θ²Ψ` (`h.memB`, with `k ≥ 1`); the second also uses the Clairaut identity
`∂_θ²∂_zΨ = ∂_z∂_θ²Ψ` on the open quadrant (`ws_pthIter_two_DzIter`) in order to identify
`∂_θ²(∂_zΨ)` with `D_z(∂_θ²Ψ)`, and the `ℋ^k`-membership of `∂_θ²Ψ` at slot `D_z^1`
(again `h.memB`, via `ws_slot_slice`, which is where `1 ≤ k` is consumed).

The remaining inputs are elementary: the value bounds at the interior point `π/4` of the four
functions `Ψ`, `∂_θΨ`, `∂_zΨ`, `∂_θ∂_zΨ` on the compact set `[a,b] × {π/4}` (the shared lemma
`Work.FTS.EllipticEst.remov.wsAbsBound`), and the arithmetic converting the shape produced by
`ws_thetaE_self_le` into an affine bound in the relevant energy (the shared lemma
`Work.FTS.EllipticEst.remov.wsThetaEConvert`).  The integral form of the Clairaut identity is the
shared lemma `Work.FTS.EllipticEst.remov.wsPzPthIterThetaE`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.remov.wsAbsBound
import Submission.Work.FTS.EllipticEst.remov.wsThetaEConvert
import Submission.Work.FTS.EllipticEst.remov.wsPzPthIterThetaE

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθ" => Work.Spaces.Iθ
local notation "SS" => Work.FTS.EllipticEst.sEta

/-! ## Tools -/

/-- The iterated `∂_θ`-derivatives of a function smooth on the open quadrant are again smooth
on the open quadrant. -/
private theorem smoothOpen_pthIter {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.SmoothOpen G) (n : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter n G) := by
  induction n with
  | zero => simpa using hG
  | succ n ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

/-- The `θ`-slice of a function smooth on the open quadrant is `C²` on the open interval. -/
private theorem contDiffOn_two_theta_slice {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.SmoothOpen G) {s : ℝ} (hs : 0 < s) :
    ContDiffOn ℝ 2 (fun θ => G s θ) (Set.Ioo 0 (Real.pi / 2)) :=
  contDiffOn_iff_forall_nat_le.mp (hG.curry_θ hs) 2 le_top

/-- The `θ`-derivative of a function multiplied by a constant in `z`: `∂_θ(z f) = z ∂_θf`. -/
private theorem pth_smul_left (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => z * f z θ) = fun z θ => z * Work.Spaces.pth f z θ := by
  funext z θ
  show deriv (fun θ' => z * f z θ') θ = z * deriv (fun θ' => f z θ') θ
  rw [deriv_const_mul_field]

/-- The iterated form of `pth_smul_left`: `∂_θ²(z f) = z ∂_θ²f`. -/
private theorem pthIter_two_smul (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter 2 (fun z θ => z * f z θ)
      = fun z θ => z * Work.Spaces.pthIter 2 f z θ := by
  have h1 : Work.Spaces.pthIter 2 (fun z θ => z * f z θ)
      = Work.Spaces.pth (fun z θ => z * Work.Spaces.pth f z θ) := by
    rw [show Work.Spaces.pthIter 2 (fun z θ => z * f z θ)
        = Work.Spaces.pth (Work.Spaces.pth (fun z θ => z * f z θ)) from rfl]
    rw [pth_smul_left f]
  rw [h1, pth_smul_left (Work.Spaces.pth f)]
  rfl

/-- **Clairaut for `∂_z` and `∂_θ²` on the open quadrant**, in the form in which the `∂_z`-slice
consumes it: `∂_θ²∂_zΨ = D_z∂_θ²Ψ / z`.  (`D_z = z∂_z` and `∂_θ²(z ∂_zΨ) = z ∂_θ²∂_zΨ`, so
this is `ws_pthIter_two_DzIter` at `i = 1` divided by `z`.) -/
private theorem ws_pthIter_two_pz_eq {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.SmoothOpen G) {s θ : ℝ} (hs : 0 < s)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pthIter 2 (Work.Spaces.pz G) s θ
      = Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 G) s θ / s := by
  have h1 : Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 G) s θ
      = s * Work.Spaces.pthIter 2 (Work.Spaces.pz G) s θ := by
    change Work.Spaces.pthIter 2 (fun z θ => z * Work.Spaces.pz G z θ) s θ = _
    exact congrFun (congrFun (pthIter_two_smul (Work.Spaces.pz G)) s) θ
  have h2 := ws_pthIter_two_DzIter hG 1 hs hθ
  rw [h2] at h1
  rw [eq_div_iff (ne_of_gt hs)]
  linarith

/-- Integrability of the weighted square of `∂_θ²∂_zΨ` on the angular slice, from the
`ℋ^k`-membership of `∂_θ²Ψ` at the slot `D_z^1` (so from `1 ≤ k`). -/
private theorem ws_integrable_pz {α : ℝ} {k : ℕ} {G : ℝ → ℝ → ℝ} (hk : 1 ≤ k)
    (hG : Work.FTS.EllipticEst.SmoothOpen G)
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 G)) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun θ => (Work.Spaces.pthIter 2 (Work.Spaces.pz G) s θ) ^ 2 * SS θ) Iθ := by
  have hbase : IntegrableOn
      (fun θ => (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 G) s θ) ^ 2 * SS θ) Iθ :=
    ws_slot_slice (smoothOpen_pthIter hG 2) hmem 1 hk hs
  refine (hbase.const_mul ((s ^ 2)⁻¹)).congr ?_
  filter_upwards [ws_ae_mem_Ioo] with θ hθ
  rw [ws_pthIter_two_pz_eq hG hs hθ, div_pow]
  ring

/-! ## The target -/

theorem wsPzBounds (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hk : 1 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ a b : ℝ, 0 < a → a < b → ∃ K : ℝ, 0 ≤ K ∧
      (∀ s ∈ Set.Icc a b, Work.FTS.EllipticEst.remov.thetaE Ψ s
        ≤ K * (1 + Work.FTS.EllipticEst.remov.thetaE (Work.Spaces.pthIter 2 Ψ) s)) ∧
      (∀ s ∈ Set.Icc a b, Work.FTS.EllipticEst.remov.thetaE (Work.Spaces.pz Ψ) s
        ≤ K * (1 + Work.FTS.EllipticEst.remov.thetaE
            (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s)) := by
  intro a b ha hab
  have hS : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hq : Real.pi / 4 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hab' : a ≤ b := le_of_lt hab
  obtain ⟨C₁, hC₁0, hC₁⟩ := wsAbsBound (g := Ψ) hS.continuousOn ha hab' hq
  obtain ⟨C₂, hC₂0, hC₂⟩ := wsAbsBound (g := Work.Spaces.pth Ψ) hS.pth.continuousOn ha hab' hq
  obtain ⟨C₃, hC₃0, hC₃⟩ := wsAbsBound (g := Work.Spaces.pz Ψ) hS.pz.continuousOn ha hab' hq
  obtain ⟨C₄, hC₄0, hC₄⟩ :=
    wsAbsBound (g := Work.Spaces.pth (Work.Spaces.pz Ψ)) hS.pz.pth.continuousOn ha hab' hq
  set P : ℝ := ∫ θ in Iθ, SS θ with hPdef
  have hP0 : 0 ≤ P := by rw [hPdef]; exact ws_sEta_integral_nonneg
  set A₁ : ℝ := C₁ ^ 2 with hA₁def
  set B₁ : ℝ := C₂ ^ 2 with hB₁def
  set A₂ : ℝ := C₃ ^ 2 with hA₂def
  set B₂ : ℝ := C₄ ^ 2 with hB₂def
  have hA₁0 : 0 ≤ A₁ := by rw [hA₁def]; positivity
  have hB₁0 : 0 ≤ B₁ := by rw [hB₁def]; positivity
  have hA₂0 : 0 ≤ A₂ := by rw [hA₂def]; positivity
  have hB₂0 : 0 ≤ B₂ := by rw [hB₂def]; positivity
  set M : ℝ := max 1 (1 + P) with hMdef
  have hM1 : 1 ≤ M := by rw [hMdef]; exact le_max_left _ _
  have hMP : 1 + P ≤ M := by rw [hMdef]; exact le_max_right _ _
  have hM0 : 0 ≤ M := le_trans zero_le_one hM1
  set K₁ : ℝ := M * (2 * A₁ + 4 * Real.pi ^ 2 * M * (1 + B₁)) with hK₁def
  set K₂ : ℝ := M * (2 * A₂ + 4 * Real.pi ^ 2 * M * (1 + B₂)) with hK₂def
  have hK₁0 : 0 ≤ K₁ := by
    rw [hK₁def]
    have hb : (0 : ℝ) ≤ 1 + B₁ := by linarith
    have hterm : 0 ≤ 4 * Real.pi ^ 2 * M * (1 + B₁) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg Real.pi)) hM0) hb
    have hterm2 : 0 ≤ 2 * A₁ := by linarith
    exact mul_nonneg hM0 (by linarith)
  have hK₂0 : 0 ≤ K₂ := by
    rw [hK₂def]
    have hb : (0 : ℝ) ≤ 1 + B₂ := by linarith
    have hterm : 0 ≤ 4 * Real.pi ^ 2 * M * (1 + B₂) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg Real.pi)) hM0) hb
    have hterm2 : 0 ≤ 2 * A₂ := by linarith
    exact mul_nonneg hM0 (by linarith)
  set L : ℝ := max 1 ((a ^ 2)⁻¹) with hLdef
  have hL1 : 1 ≤ L := by rw [hLdef]; exact le_max_left _ _
  have hLinv : (a ^ 2)⁻¹ ≤ L := by rw [hLdef]; exact le_max_right _ _
  set K : ℝ := max K₁ (K₂ * L) with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact le_trans hK₁0 (le_max_left _ _)
  refine ⟨K, hK0, ?_, ?_⟩
  · -- the `Ψ`-bound
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    have h2s := contDiffOn_two_theta_slice hS hs0
    have hEine : IntegrableOn (fun θ => (Work.Spaces.pthIter 2 Ψ s θ) ^ 2 * SS θ) Iθ :=
      ws_slot_slice (smoothOpen_pthIter hS 2) h.memB 0 (Nat.zero_le k) hs0
    have hA : (Ψ s (Real.pi / 4)) ^ 2 ≤ A₁ := by
      have h1 : |Ψ s (Real.pi / 4)| ≤ C₁ := hC₁ s hs
      have h2 : |Ψ s (Real.pi / 4)| ^ 2 ≤ C₁ ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
      simpa only [hA₁def, sq_abs] using h2
    have hB : (deriv (fun θ => Ψ s θ) (Real.pi / 4)) ^ 2 ≤ B₁ := by
      have h1 : |Work.Spaces.pth Ψ s (Real.pi / 4)| ≤ C₂ := hC₂ s hs
      have h2 : |Work.Spaces.pth Ψ s (Real.pi / 4)| ^ 2 ≤ C₂ ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
      simpa only [hB₁def, sq_abs, Work.Spaces.pth] using h2
    have hmain := ws_thetaE_self_le (Ψ := Ψ) (s := s) (A := A₁) (B := B₁) h2s hEine hA hB
    rw [← hPdef] at hmain
    have hconv := wsThetaEConvert (A := A₁) (B := B₁) (E := thetaE (Work.Spaces.pthIter 2 Ψ) s)
      (P := P) (M := M) hA₁0 hB₁0 (thetaE_nonneg _ _) hP0 hMP hmain
    calc thetaE Ψ s ≤ K₁ * (1 + thetaE (Work.Spaces.pthIter 2 Ψ) s) := by
          rw [hK₁def]; exact hconv
      _ ≤ K * (1 + thetaE (Work.Spaces.pthIter 2 Ψ) s) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _)
            (by linarith [thetaE_nonneg (Work.Spaces.pthIter 2 Ψ) s])
  · -- the `∂_zΨ`-bound
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    have hsa : a ≤ s := hs.1
    have h2s := contDiffOn_two_theta_slice hS.pz hs0
    have hEine : IntegrableOn
        (fun θ => (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) s θ) ^ 2 * SS θ) Iθ :=
      ws_integrable_pz hk hS h.memB hs0
    have hA : (Work.Spaces.pz Ψ s (Real.pi / 4)) ^ 2 ≤ A₂ := by
      have h1 : |Work.Spaces.pz Ψ s (Real.pi / 4)| ≤ C₃ := hC₃ s hs
      have h2 : |Work.Spaces.pz Ψ s (Real.pi / 4)| ^ 2 ≤ C₃ ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
      simpa only [hA₂def, sq_abs] using h2
    have hB : (deriv (fun θ => Work.Spaces.pz Ψ s θ) (Real.pi / 4)) ^ 2 ≤ B₂ := by
      have h1 : |Work.Spaces.pth (Work.Spaces.pz Ψ) s (Real.pi / 4)| ≤ C₄ := hC₄ s hs
      have h2 : |Work.Spaces.pth (Work.Spaces.pz Ψ) s (Real.pi / 4)| ^ 2 ≤ C₄ ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
      simpa only [hB₂def, sq_abs, Work.Spaces.pth] using h2
    have hmain := ws_thetaE_self_le (Ψ := Work.Spaces.pz Ψ) (s := s) (A := A₂) (B := B₂)
      h2s hEine hA hB
    rw [← hPdef] at hmain
    have hK2 := wsThetaEConvert (A := A₂) (B := B₂)
      (E := thetaE (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ)) s) (P := P) (M := M)
      hA₂0 hB₂0 (thetaE_nonneg _ _) hP0 hMP hmain
    -- the second `θ`-derivative of `∂_zΨ` is `D_z∂_θ²Ψ / s`
    have hF0 : 0 ≤ thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s :=
      thetaE_nonneg _ _
    have hE2 : thetaE (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ)) s
        ≤ L * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s := by
      rw [wsPzPthIterThetaE hS hs0]
      have hinv : (s ^ 2)⁻¹ ≤ (a ^ 2)⁻¹ := by
        refine (inv_le_inv₀ (by positivity) (by positivity)).mpr ?_
        exact pow_le_pow_left₀ ha.le hsa 2
      calc (s ^ 2)⁻¹ * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s
          ≤ (a ^ 2)⁻¹ * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s :=
            mul_le_mul_of_nonneg_right hinv hF0
        _ ≤ L * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s :=
            mul_le_mul_of_nonneg_right hLinv hF0
    have hmax : thetaE (Work.Spaces.pz Ψ) s
        ≤ (K₂ * L) * (1 + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s) := by
      have h1 : 1 + thetaE (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ)) s
          ≤ L * (1 + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s) := by
        have h2 : 1 + thetaE (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ)) s
            ≤ 1 + L * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s := by
          linarith [hE2]
        have h3 : 1 + L * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s
            ≤ L * (1 + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s) := by
          nlinarith [hL1, hF0]
        linarith
      calc thetaE (Work.Spaces.pz Ψ) s
          ≤ K₂ * (1 + thetaE (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ)) s) := by
            rw [hK₂def]; exact hK2
        _ ≤ K₂ * (L * (1 + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s)) :=
            mul_le_mul_of_nonneg_left h1 hK₂0
        _ = (K₂ * L) * (1 + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s) := by
            ring
    exact le_trans hmax (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (by linarith [thetaE_nonneg (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s]))

end Work.FTS.EllipticEst.remov
