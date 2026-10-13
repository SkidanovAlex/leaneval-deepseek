/-
  WilG4c — the final diagonal subdivision estimate of BNZ §5.4 (`subdiv_normle`).

  Given a function `G` on the cube which is bounded by `1` in absolute value and whose mixed
  derivatives `∂^α G` at every point `pt x y` of the cube are bounded by twice their value on the
  curve `x ↦ curveFun γ x`, and whose mixed derivatives on the curve are bounded by
  `e · (r(1+ne))^{|α|}`, the pulled-back function `t ↦ G (subdivMap N s t)` of the *diagonal*
  subdivision with `N = subdivN n r` has operator norms of all derivatives of order `≤ r` bounded
  by `1`.

  The proof is the chain of inequalities of BNZ §5.4:

      ‖D^m (G ∘ subdivMap)(t)‖ = ‖D^m G (subdivMap t) ∘ (A, …, A)‖         (A = N⁻¹ • 1)
                       ≤ ‖D^m G (subdivMap t)‖ · ‖A‖^m                     (`affine_…_norm_le`)
                       ≤ 2·e·(r(1+ne))^m · (n+1)^m · N^{-m}                (`pt_jet_le`)
                       ≤ 1,                                                 (`subdiv_rescale_bound`)

  where the `(n+1)^m` comes from expanding the multilinear form `D^m G` in the coordinate basis
  (`norm_iteratedFDeriv_le_of_dirs`) and is absorbed by the `+1` in the constant of `subdivN`.
  The case `m = 0` is the bound `|G| ≤ 1` on the cube.
-/
import Mathlib
import Submission.Work.WilG4c.StepHigherDefs
import Submission.Work.WilG4c.norm_iteratedFDeriv_le_of_dirs
import Submission.Work.WilG4c.affine_iteratedFDeriv_norm_le
import Submission.Work.WilG4c.pt_jet_le
import Submission.Work.WilG4c.subdiv_rescale_bound

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- If `f ∘ (b + A ·)` is `C^r` at `x` and `B` is a right inverse of `A` (`A (B u) = u`) as well as
a left inverse (`B (A u) = u`), then `f` is `C^r` at `b + A x`: `f` is the composite of
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

theorem subdiv_normle {n r : ℕ} (hr : 1 ≤ r) (G : (Fin (n + 1) → ℝ) → ℝ) (γ : ℝ → Fin n → ℝ)
    (h0 : ∀ z ∈ WilkiesDesign.openCube (n + 1), |G z| ≤ 1)
    (hmax : ∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ) (y : Fin n → ℝ), m ≤ r →
      x ∈ Work.WilkG4c.I → y ∈ WilkiesDesign.openCube n → ContDiffAt ℝ m G (Work.WilkG4c.pt x y) →
      |iteratedFDeriv ℝ m G (Work.WilkG4c.pt x y) (fun k => Pi.single (v k) 1)| ≤
        2 * |iteratedFDeriv ℝ m G (Work.WilkG4c.curveFun γ x) (fun k => Pi.single (v k) 1)|)
    (hcurve : ∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ), m ≤ r → x ∈ Work.WilkG4c.I →
      |iteratedFDeriv ℝ m G (Work.WilkG4c.curveFun γ x) (fun k => Pi.single (v k) 1)| ≤
        Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) :
    ∀ (s : Fin (n + 1) → Fin (3 * (Work.WilkG4c.subdivN n r - 1) + 1)) (m : ℕ), m ≤ r →
      ∀ t ∈ WilkiesDesign.openCube (n + 1),
        ContDiffAt ℝ r (fun t : Fin (n + 1) → ℝ =>
          G (Work.WilkG4c.subdivMap (Work.WilkG4c.subdivN n r) s t)) t →
        ‖iteratedFDeriv ℝ m (fun t : Fin (n + 1) → ℝ =>
          G (Work.WilkG4c.subdivMap (Work.WilkG4c.subdivN n r) s t)) t‖ ≤ 1 := by
  intro s m hm t ht hcd
  have hN : 1 ≤ subdivN n r := subdivN_pos hr
  -- the subdivision chart as an affine map `u ↦ b + A u`
  set A : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) := ((subdivN n r : ℕ) : ℝ)⁻¹ • 1 with hA
  set B : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) := ((subdivN n r : ℕ) : ℝ) • 1 with hB
  set b : Fin (n + 1) → ℝ := subdivBase (subdivN n r) s with hb
  have hNe : (((subdivN n r : ℕ)) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < ((subdivN n r : ℕ) : ℝ) := by exact_mod_cast hN
    exact ne_of_gt this
  have hS : ∀ u, subdivMap (subdivN n r) s u = b + A u := by
    intro u
    rw [subdivMap_eq, hb, hA]
    simp
  have hAB : ∀ u, A (B u) = u := by
    intro u
    simp [hA, hB, smul_smul, mul_inv_cancel₀ hNe, inv_mul_cancel₀ hNe]
  have hBA : ∀ u, B (A u) = u := by
    intro u
    simp [hA, hB, smul_smul, inv_mul_cancel₀ hNe, mul_inv_cancel₀ hNe]
  have hLft : (fun t : Fin (n + 1) → ℝ => G (subdivMap (subdivN n r) s t))
      = fun u => G (b + A u) := by
    funext u
    rw [hS u]
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- order `0`: the bound `|G| ≤ 1` on the cube
    rw [hm0, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    exact h0 _ (subdivMap_mem_openCube hN s ht)
  · -- order `m ≥ 1`
    have hcd' : ContDiffAt ℝ r (fun u => G (b + A u)) t := by
      rw [← hLft]; exact hcd
    -- the subdivision chart is invertible, so `G` is `C^r` at the image point
    have hG : ContDiffAt ℝ r G (b + A t) :=
      contDiffAt_of_contDiffAt_comp_affine A B hAB hBA b hcd'
    have hGm : ContDiffAt ℝ m G (b + A t) := hG.of_le (by exact_mod_cast hm)
    have hzmem : b + A t ∈ openCube (n + 1) := by
      rw [← hS t]; exact subdivMap_mem_openCube hN s ht
    have hxI : (b + A t) 0 ∈ I := hzmem 0
    have hy : Fin.tail (b + A t) ∈ openCube n := by
      intro i
      show (b + A t) i.succ ∈ Set.Ioo (0 : ℝ) 1
      exact hzmem i.succ
    have hpt : pt ((b + A t) 0) (Fin.tail (b + A t)) = b + A t := pt_eta _
    -- transfer of the curve bound to the point `b + A t`
    have hbound := Work.WilG4c.pt_jet_le G γ hmax hcurve hm hxI hy (by rw [hpt]; exact hGm)
    rw [hpt] at hbound
    -- the affine chain rule for the subdivision
    have haff := Work.WilG4c.affine_iteratedFDeriv_norm_le r m hm G b t A hG
    have hnormA : ‖A‖ ≤ ((subdivN n r : ℕ) : ℝ)⁻¹ := by
      have hc : (0 : ℝ) ≤ ((subdivN n r : ℕ) : ℝ)⁻¹ := by positivity
      refine ContinuousLinearMap.opNorm_le_bound A hc (fun u => ?_)
      have hAu : A u = ((subdivN n r : ℕ) : ℝ)⁻¹ • u := by
        rw [hA]; simp
      exact le_of_eq (by rw [hAu, norm_smul, Real.norm_of_nonneg hc])
    have hnonneg : (0 : ℝ) ≤
        2 * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) * ((n : ℝ) + 1) ^ m := by
      positivity
    have harith := Work.WilG4c.subdiv_rescale_bound (n := n) (r := r) (m := m)
      (N := subdivN n r) hr hmpos (subdivN_ge n r)
    calc ‖iteratedFDeriv ℝ m (fun t : Fin (n + 1) → ℝ => G (subdivMap (subdivN n r) s t)) t‖
        = ‖iteratedFDeriv ℝ m (fun u : Fin (n + 1) → ℝ => G (b + A u)) t‖ := by rw [hLft]
      _ ≤ ‖iteratedFDeriv ℝ m G (b + A t)‖ * ‖A‖ ^ m := haff
      _ ≤ (2 * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) * ((n : ℝ) + 1) ^ m) * ‖A‖ ^ m :=
          mul_le_mul_of_nonneg_right hbound (pow_nonneg (norm_nonneg A) m)
      _ ≤ (2 * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) * ((n : ℝ) + 1) ^ m) *
            (((subdivN n r : ℕ) : ℝ)⁻¹) ^ m :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg A) hnormA m) hnonneg
      _ ≤ 1 := harith

end Work.WilkG4c

/-- The same statement as `Work.WilkG4c.subdiv_normle`, under the namespace of the file's module
path (`Submission.Work.WilG4c.subdiv_normle`), so that the lemma is reachable under either spelling
of the area's namespace. -/
theorem Work.WilG4c.subdiv_normle {n r : ℕ} (hr : 1 ≤ r) (G : (Fin (n + 1) → ℝ) → ℝ)
    (γ : ℝ → Fin n → ℝ)
    (h0 : ∀ z ∈ WilkiesDesign.openCube (n + 1), |G z| ≤ 1)
    (hmax : ∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ) (y : Fin n → ℝ), m ≤ r →
      x ∈ Work.WilkG4c.I → y ∈ WilkiesDesign.openCube n → ContDiffAt ℝ m G (Work.WilkG4c.pt x y) →
      |iteratedFDeriv ℝ m G (Work.WilkG4c.pt x y) (fun k => Pi.single (v k) 1)| ≤
        2 * |iteratedFDeriv ℝ m G (Work.WilkG4c.curveFun γ x) (fun k => Pi.single (v k) 1)|)
    (hcurve : ∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ), m ≤ r → x ∈ Work.WilkG4c.I →
      |iteratedFDeriv ℝ m G (Work.WilkG4c.curveFun γ x) (fun k => Pi.single (v k) 1)| ≤
        Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) :
    ∀ (s : Fin (n + 1) → Fin (3 * (Work.WilkG4c.subdivN n r - 1) + 1)) (m : ℕ), m ≤ r →
      ∀ t ∈ WilkiesDesign.openCube (n + 1),
        ContDiffAt ℝ r (fun t : Fin (n + 1) → ℝ =>
          G (Work.WilkG4c.subdivMap (Work.WilkG4c.subdivN n r) s t)) t →
        ‖iteratedFDeriv ℝ m (fun t : Fin (n + 1) → ℝ =>
          G (Work.WilkG4c.subdivMap (Work.WilkG4c.subdivN n r) s t)) t‖ ≤ 1 :=
  Work.WilkG4c.subdiv_normle hr G γ h0 hmax hcurve
