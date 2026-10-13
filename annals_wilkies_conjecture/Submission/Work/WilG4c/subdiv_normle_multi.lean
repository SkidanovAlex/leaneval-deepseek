/-
  WilG4c — `subdiv_normle_multi`: the diagonal subdivision estimate of BNZ §5.4 with a
  multiindex-indexed family of near-maximising curves.

  This is `Work.WilkG4c.subdiv_normle` with the single curve `γ : ℝ → Fin n → ℝ` replaced by a
  family `γ : (m : ℕ) → (Fin m → Fin (n + 1)) → ℝ → Fin n → ℝ` attached to each multiindex
  `(m, v)`.  The proof is split into two independent parts:

  * `pt_jet_le_multi` (sibling module `Submission.Work.WilG4c.pt_jet_le_multi`) — the pointwise
    transfer of the mixed-derivative bounds from the curve of the matching multiindex to the
    cube point `pt x y`: `‖D^m G (pt x y)‖ ≤ 2 (e (r (1 + n e))^m) (n + 1)^m`;
  * `subdiv_normle_of_pt_bound` (below) — the analytic chain of BNZ §5.4, which only needs such
    a pointwise bound at every `C^m`-point of the cube to conclude the operator-norm bound
    `≤ 1` after pulling back along the diagonal subdivision.

  The requested statement `subdiv_normle_multi` is the two of them glued together.
-/
import Mathlib
import Submission.Work.WilG4c.StepHigherDefs
import Submission.Work.WilG4c.subdiv_normle
import Submission.Work.WilG4c.norm_iteratedFDeriv_le_of_dirs
import Submission.Work.WilG4c.affine_iteratedFDeriv_norm_le
import Submission.Work.WilG4c.pt_jet_le_multi

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- If `f ∘ (b + A ·)` is `C^r` at `x` and `B` is a right inverse of `A` (`A (B u) = u`) as well
as a left inverse (`B (A u) = u`), then `f` is `C^r` at `b + A x`: `f` is the composite of
`f ∘ (b + A ·)` with the affine map `w ↦ B (w - b)`, which inverts `y ↦ b + A y`. -/
private lemma contDiffAt_of_contDiffAt_comp_affine {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {r : ℕ} {f : E → ℝ} (A B : E →L[ℝ] E) (hAB : ∀ u, A (B u) = u)
    (hBA : ∀ u, B (A u) = u) (b : E) {x : E}
    (h : ContDiffAt ℝ r (fun y => f (b + A y)) x) : ContDiffAt ℝ r f (b + A x) := by
  have hψ : ContDiffAt ℝ r (fun w : E => B (w - b)) (b + A x) :=
    (B.contDiff.contDiffAt).comp (b + A x) (contDiffAt_id.sub contDiffAt_const)
  have h' : ContDiffAt ℝ r (fun y => f (b + A y)) (B ((b + A x) - b)) := by
    rw [add_sub_cancel_left, hBA]; exact h
  have hcomp := h'.comp (b + A x) hψ
  have hfun : (fun y => f (b + A y)) ∘ (fun w : E => B (w - b)) = f := by
    funext w
    simp only [Function.comp_apply]
    rw [hAB, add_sub_cancel]
  rwa [hfun] at hcomp

/-- **The analytic core of `subdiv_normle`.**  If `G` is bounded by `1` on the cube and its
`m`-th iterated derivative is bounded by `2 (e (r (1 + n e))^m) (n + 1)^m` at every `C^m`-point
of the cube (a bound of exactly the shape supplied by `pt_jet_le`/`pt_jet_le_multi`), then the
pullback of `G` along the diagonal subdivision of BNZ §5.4 has operator norms of all orders
`≤ r` bounded by `1`. -/
theorem subdiv_normle_of_pt_bound {n r : ℕ} (hr : 1 ≤ r) (G : (Fin (n + 1) → ℝ) → ℝ)
    (h0 : ∀ z ∈ WilkiesDesign.openCube (n + 1), |G z| ≤ 1)
    (hpt : ∀ (m : ℕ) (x : ℝ) (y : Fin n → ℝ), m ≤ r → x ∈ Work.WilkG4c.I →
      y ∈ WilkiesDesign.openCube n → ContDiffAt ℝ m G (Work.WilkG4c.pt x y) →
      ‖iteratedFDeriv ℝ m G (Work.WilkG4c.pt x y)‖ ≤
        2 * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) * ((n : ℝ) + 1) ^ m) :
    ∀ (s : Fin (n + 1) → Fin (3 * (Work.WilkG4c.subdivN n r - 1) + 1)) (m : ℕ), m ≤ r →
      ∀ t ∈ WilkiesDesign.openCube (n + 1),
        ContDiffAt ℝ r (fun t : Fin (n + 1) → ℝ =>
          G (Work.WilkG4c.subdivMap (Work.WilkG4c.subdivN n r) s t)) t →
        ‖iteratedFDeriv ℝ m (fun t : Fin (n + 1) → ℝ =>
          G (Work.WilkG4c.subdivMap (Work.WilkG4c.subdivN n r) s t)) t‖ ≤ 1 := by
  intro s m hm t ht hcd
  have hN : 1 ≤ Work.WilkG4c.subdivN n r := Work.WilkG4c.subdivN_pos hr
  set A : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
    ((Work.WilkG4c.subdivN n r : ℕ) : ℝ)⁻¹ • 1 with hA
  set B : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
    ((Work.WilkG4c.subdivN n r : ℕ) : ℝ) • 1 with hB
  set b : Fin (n + 1) → ℝ := Work.WilkG4c.subdivBase (Work.WilkG4c.subdivN n r) s with hb
  have hNe : (((Work.WilkG4c.subdivN n r : ℕ)) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < ((Work.WilkG4c.subdivN n r : ℕ) : ℝ) := by exact_mod_cast hN
    exact ne_of_gt this
  have hS : ∀ u, Work.WilkG4c.subdivMap (Work.WilkG4c.subdivN n r) s u = b + A u := by
    intro u
    rw [Work.WilkG4c.subdivMap_eq, hb, hA]
    simp
  have hAB : ∀ u, A (B u) = u := by
    intro u
    simp [hA, hB, smul_smul, mul_inv_cancel₀ hNe]
  have hBA : ∀ u, B (A u) = u := by
    intro u
    simp [hA, hB, smul_smul, inv_mul_cancel₀ hNe]
  have hLft : (fun t : Fin (n + 1) → ℝ =>
        G (Work.WilkG4c.subdivMap (Work.WilkG4c.subdivN n r) s t)) = fun u => G (b + A u) := by
    funext u
    rw [hS u]
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · rw [hm0, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    exact h0 _ (Work.WilkG4c.subdivMap_mem_openCube hN s ht)
  · have hcd' : ContDiffAt ℝ r (fun u => G (b + A u)) t := by
      rw [← hLft]; exact hcd
    -- `G` is `C^r` at the image point: `G` is the composite of `G ∘ (b + A ·)` with the
    -- smooth inverse `w ↦ B (w - b)` of `u ↦ b + A u`.
    have hG : ContDiffAt ℝ r G (b + A t) :=
      contDiffAt_of_contDiffAt_comp_affine A B hAB hBA b hcd'
    have hGm : ContDiffAt ℝ m G (b + A t) := hG.of_le (by exact_mod_cast hm)
    have hzmem : b + A t ∈ WilkiesDesign.openCube (n + 1) := by
      rw [← hS t]; exact Work.WilkG4c.subdivMap_mem_openCube hN s ht
    have hxI : (b + A t) 0 ∈ Work.WilkG4c.I := hzmem 0
    have hy : Fin.tail (b + A t) ∈ WilkiesDesign.openCube n := by
      intro i
      show (b + A t) i.succ ∈ Set.Ioo (0 : ℝ) 1
      exact hzmem i.succ
    have hpt_eq : Work.WilkG4c.pt ((b + A t) 0) (Fin.tail (b + A t)) = b + A t :=
      Work.WilkG4c.pt_eta _
    have hbound := hpt m ((b + A t) 0) (Fin.tail (b + A t)) hm hxI hy (by rw [hpt_eq]; exact hGm)
    rw [hpt_eq] at hbound
    have haff := Work.WilG4c.affine_iteratedFDeriv_norm_le r m hm G b t A hG
    have hnormA : ‖A‖ ≤ (((Work.WilkG4c.subdivN n r : ℕ)) : ℝ)⁻¹ := by
      have hc : (0 : ℝ) ≤ (((Work.WilkG4c.subdivN n r : ℕ)) : ℝ)⁻¹ := by positivity
      refine ContinuousLinearMap.opNorm_le_bound A hc (fun u => ?_)
      have hAu : A u = (((Work.WilkG4c.subdivN n r : ℕ)) : ℝ)⁻¹ • u := by
        rw [hA]; simp
      exact le_of_eq (by rw [hAu, norm_smul, Real.norm_of_nonneg hc])
    have hnonneg : (0 : ℝ) ≤
        2 * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) * ((n : ℝ) + 1) ^ m := by positivity
    have harith := Work.WilG4c.subdiv_rescale_bound (n := n) (r := r) (m := m)
      (N := Work.WilkG4c.subdivN n r) hr hmpos (Work.WilkG4c.subdivN_ge n r)
    calc ‖iteratedFDeriv ℝ m (fun t : Fin (n + 1) → ℝ =>
            G (Work.WilkG4c.subdivMap (Work.WilkG4c.subdivN n r) s t)) t‖
        = ‖iteratedFDeriv ℝ m (fun u : Fin (n + 1) → ℝ => G (b + A u)) t‖ := by rw [hLft]
      _ ≤ ‖iteratedFDeriv ℝ m G (b + A t)‖ * ‖A‖ ^ m := haff
      _ ≤ (2 * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) * ((n : ℝ) + 1) ^ m) *
            ‖A‖ ^ m :=
          mul_le_mul_of_nonneg_right hbound (pow_nonneg (norm_nonneg A) m)
      _ ≤ (2 * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) * ((n : ℝ) + 1) ^ m) *
            (((Work.WilkG4c.subdivN n r : ℕ) : ℝ)⁻¹) ^ m :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg A) hnormA m) hnonneg
      _ ≤ 1 := harith

theorem subdiv_normle_multi {n r : ℕ} (hr : 1 ≤ r) (G : (Fin (n + 1) → ℝ) → ℝ)
    (h0 : ∀ z ∈ WilkiesDesign.openCube (n + 1), |G z| ≤ 1)
    (γ : (m : ℕ) → (Fin m → Fin (n + 1)) → ℝ → Fin n → ℝ)
    (hmax : ∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ) (y : Fin n → ℝ), m ≤ r →
      x ∈ Work.WilkG4c.I → y ∈ WilkiesDesign.openCube n → ContDiffAt ℝ m G (Work.WilkG4c.pt x y) →
      |iteratedFDeriv ℝ m G (Work.WilkG4c.pt x y) (fun k => Pi.single (v k) 1)| ≤
        2 * |iteratedFDeriv ℝ m G (Work.WilkG4c.curveFun (γ m v) x) (fun k => Pi.single (v k) 1)|)
    (hcurve : ∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ), m ≤ r → x ∈ Work.WilkG4c.I →
      |iteratedFDeriv ℝ m G (Work.WilkG4c.curveFun (γ m v) x) (fun k => Pi.single (v k) 1)| ≤
        Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) :
    ∀ (s : Fin (n + 1) → Fin (3 * (Work.WilkG4c.subdivN n r - 1) + 1)) (m : ℕ), m ≤ r →
      ∀ t ∈ WilkiesDesign.openCube (n + 1),
        ContDiffAt ℝ r (fun t : Fin (n + 1) → ℝ => G (Work.WilkG4c.subdivMap (Work.WilkG4c.subdivN n r) s t)) t →
        ‖iteratedFDeriv ℝ m (fun t : Fin (n + 1) → ℝ => G (Work.WilkG4c.subdivMap (Work.WilkG4c.subdivN n r) s t)) t‖ ≤ 1 :=
  subdiv_normle_of_pt_bound (n := n) (r := r) hr G h0
    (fun _ _ _ hm hx hy hG => pt_jet_le_multi G γ hmax hcurve hm hx hy hG)

end Work.WilG4c
