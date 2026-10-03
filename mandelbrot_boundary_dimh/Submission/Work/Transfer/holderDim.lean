import Mathlib
import Submission.Work.Transfer.Setup
import Submission.Work.Transfer.dimH_image_le_div_of_dist_le

/-!
# Step 5 of the area-transfer argument: from the Hölder map to `dimH ∂M`

This file proves `Work.Transfer.holderDim`, the final (dimension) step of the area-transfer
argument of Shishikura's theorem (see `Submission/Work/Transfer/transfer.lean` for the overall
blueprint; this is "Step 5" there, replacing MSS Lemma III.2 / Shishikura Lemma 3.2).

Situation: `c₀` is a parameter where `Tc c₀` carries a conformal IFS with `N` branches and
expansion bounded by `K` (`IsConformalIFS N τ p r K`), and `π = phi` is a `MotionData` motion of
the coding map of that IFS, bi-Hölder between parameters with exponent `a ∈ (0,1)`
(`MotionData.holder`).  For the parameter `c₁` of the motion we are given

* a surjection of the code cylinder `cylinder l` onto the hit set `Y = HitSet m c₁ ρ₁ phi W`
  (`hsurj`), through the map `c ↦ codeOf m phi c`;
* `Y ⊆ ∂M` (`hfront`);
* the Hölder regularity of `Psi c = phi c₁ (codeOf m phi c)` on `Y` with exponent `a` (`hholder`).

The dimension count is then

  `dimH ∂M ≥ dimH Y ≥ a · dimH (Psi '' Y) ≥ a · dimH (phi c₁ '' cylinder l)`
  `≥ a · a · dimH (phi c₀ '' cylinder l) = a² · dimH (codingPt τ p '' cylinder l) ≥ a² · log N / log K`,

where the two "`a ·`" factors come from the two Hölder maps: `Psi` (with constant `K'`) on `Y`, and
the comparison of the motion at the two parameters `c₀`, `c₁` on the code cylinder.  Both Hölder
estimates are converted to dimension bounds by `dimH_image_le_div_of_dist_le`
(`HolderOnWith.dimH_image_le` for a Hölder relation), and all inequalities are combined in `ℝ≥0∞`.
-/

open LeanEval.Dynamics.MandelbrotBoundary
open Set Metric Filter Topology
open Classical
open scoped NNReal ENNReal

noncomputable section

namespace Work.Transfer

theorem holderDim (hD : MandelDim.DimStatement) {c₀ : ℂ} {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    {τ : Fin N → ℂ → ℂ} {n : Fin N → ℕ} {p : ℂ} {r K ρ a : ℝ}
    {phi : ℂ → (ℕ → Fin N) → ℂ} (hρ : 0 < ρ) (hifs : MandelDim.IsConformalIFS N τ p r K)
    (hMD : Work.Transfer.MotionData c₀ N τ n p ρ a phi) (ha0 : 0 < a) (ha1 : a < 1)
    (m : ℕ) {c₁ : ℂ} (hc₁ : c₁ ∈ Metric.ball c₀ ρ) {ρ₁ : ℝ} {l : List (Fin N)}
    {W : Set (ℕ → Fin N)} (hcylW : MandelDim.cylinder l ⊆ W)
    (hfront : Work.Transfer.HitSet m c₁ ρ₁ phi W ⊆
      frontier LeanEval.Dynamics.MandelbrotBoundary.Mandelbrot)
    (hsurj : ∀ ω ∈ MandelDim.cylinder l,
        ∃ c ∈ Work.Transfer.HitSet m c₁ ρ₁ phi W, Work.Transfer.codeOf m phi c = ω)
    {K' : NNReal} (hholder : HolderOnWith K' (Real.toNNReal a)
        (fun c => phi c₁ (Work.Transfer.codeOf m phi c)) (Work.Transfer.HitSet m c₁ ρ₁ phi W)) :
    ENNReal.ofReal (a ^ 2 * (Real.log N / Real.log K)) ≤
      dimH (frontier LeanEval.Dynamics.MandelbrotBoundary.Mandelbrot) := by
  -- `DimStatement` at the base parameter `c₀`, where `phi c₀ = codingPt τ p`.
  have hD0 : ENNReal.ofReal (Real.log N / Real.log K) ≤
      dimH (MandelDim.codingPt τ p '' MandelDim.cylinder l) := hD N τ p r K hN hifs l
  have hbase : phi c₀ = MandelDim.codingPt τ p := funext hMD.base
  -- The Hölder relation of the motion between the two parameters, as a norm inequality.
  obtain ⟨C, hC⟩ := hMD.holder
  let Cn : NNReal := ⟨max C 0, le_max_right C 0⟩
  have hCrel : ∀ x ∈ MandelDim.cylinder l, ∀ y ∈ MandelDim.cylinder l,
      ‖phi c₀ x - phi c₀ y‖ ≤ (Cn : ℝ) * ‖phi c₁ x - phi c₁ y‖ ^ a := by
    have hCnv : (Cn : ℝ) = max C 0 := rfl
    intro x _ y _
    rw [hCnv]
    rcases le_total 0 C with h | h
    · exact (hC c₀ (Metric.mem_ball_self hρ) c₁ hc₁ x y).trans
        (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg (norm_nonneg _) a))
    · rw [max_eq_right h, zero_mul]
      exact (hC c₀ (Metric.mem_ball_self hρ) c₁ hc₁ x y).trans
        (mul_nonpos_of_nonpos_of_nonneg h
          (Real.rpow_nonneg (norm_nonneg (phi c₁ x - phi c₁ y)) a))
  -- First Hölder factor: the picture at `c₀` is an `a`-Hölder image of the picture at `c₁`.
  have hA2 : (Real.toNNReal a : ENNReal) * dimH (phi c₀ '' MandelDim.cylinder l) ≤
      dimH (phi c₁ '' MandelDim.cylinder l) := by
    have hstep := dimH_image_le_div_of_dist_le (S := MandelDim.cylinder l) (F := phi c₀)
      (G := phi c₁) (C := Cn) ha0 hCrel
    have hA0 : (Real.toNNReal a : ENNReal) ≠ 0 :=
      ENNReal.coe_ne_zero.mpr (Real.toNNReal_pos.mpr ha0).ne'
    have hAt : (Real.toNNReal a : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have h2 := (ENNReal.le_div_iff_mul_le (Or.inl hA0) (Or.inl hAt)).1 hstep
    rw [mul_comm] at h2
    exact h2
  -- The code surjectivity: the whole cylinder is realised inside the hit set.
  have himage : phi c₁ '' MandelDim.cylinder l ⊆
      (fun c => phi c₁ (Work.Transfer.codeOf m phi c)) '' (Work.Transfer.HitSet m c₁ ρ₁ phi W) := by
    rintro _ ⟨ω, hω, rfl⟩
    obtain ⟨c, hc, hcode⟩ := hsurj ω hω
    exact ⟨c, hc, by simp only [hcode]⟩
  -- Second Hölder factor: `Psi` on the hit set, with the constant `K'`.
  have hPsi : (Real.toNNReal a : ENNReal) *
      dimH ((fun c => phi c₁ (Work.Transfer.codeOf m phi c)) ''
        (Work.Transfer.HitSet m c₁ ρ₁ phi W)) ≤
      dimH (Work.Transfer.HitSet m c₁ ρ₁ phi W) := by
    have h1 := hholder.dimH_image_le (Real.toNNReal_pos.mpr ha0)
    have hA0 : (Real.toNNReal a : ENNReal) ≠ 0 :=
      ENNReal.coe_ne_zero.mpr (Real.toNNReal_pos.mpr ha0).ne'
    have hAt : (Real.toNNReal a : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have h2 := (ENNReal.le_div_iff_mul_le (Or.inl hA0) (Or.inl hAt)).1 h1
    rw [mul_comm] at h2
    exact h2
  -- `a^2 * L = a * (a * L)`, so that the two Hölder factors can be applied in sequence.
  have hkey : ENNReal.ofReal (a ^ 2 * (Real.log N / Real.log K)) =
      (Real.toNNReal a : ENNReal) *
        ((Real.toNNReal a : ENNReal) * ENNReal.ofReal (Real.log N / Real.log K)) := by
    have hcoe : (Real.toNNReal a : ENNReal) = ENNReal.ofReal a := by
      rw [ENNReal.ofReal_eq_coe_nnreal ha0.le, Real.toNNReal_of_nonneg ha0.le]
    rw [hcoe, ← mul_assoc, ← pow_two, ← ENNReal.ofReal_pow ha0.le 2,
      ← ENNReal.ofReal_mul (sq_nonneg a)]
  calc ENNReal.ofReal (a ^ 2 * (Real.log N / Real.log K))
      = (Real.toNNReal a : ENNReal) *
          ((Real.toNNReal a : ENNReal) * ENNReal.ofReal (Real.log N / Real.log K)) := hkey
    _ ≤ (Real.toNNReal a : ENNReal) *
          ((Real.toNNReal a : ENNReal) *
            dimH (MandelDim.codingPt τ p '' MandelDim.cylinder l)) :=
        mul_le_mul_right (mul_le_mul_right hD0 _) _
    _ = (Real.toNNReal a : ENNReal) *
          ((Real.toNNReal a : ENNReal) * dimH (phi c₀ '' MandelDim.cylinder l)) := by
        rw [hbase]
    _ ≤ (Real.toNNReal a : ENNReal) * dimH (phi c₁ '' MandelDim.cylinder l) :=
        mul_le_mul_right hA2 _
    _ ≤ (Real.toNNReal a : ENNReal) *
          dimH ((fun c => phi c₁ (Work.Transfer.codeOf m phi c)) ''
            (Work.Transfer.HitSet m c₁ ρ₁ phi W)) :=
        mul_le_mul_right (dimH_mono himage) _
    _ ≤ dimH (Work.Transfer.HitSet m c₁ ρ₁ phi W) := hPsi
    _ ≤ dimH (frontier LeanEval.Dynamics.MandelbrotBoundary.Mandelbrot) := dimH_mono hfront

end Work.Transfer
