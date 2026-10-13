import Mathlib
import Submission.Work.WilG4c.subdiv_normle_multi
import Submission.Work.WilG4c.pt_jet_le_multi_bad_offBC

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

theorem subdiv_normle_multi_badBC {n r : ℕ} (hr : 1 ≤ r) (G : (Fin (n + 1) → ℝ) → ℝ)
    (h0 : ∀ z ∈ WilkiesDesign.openCube (n + 1), |G z| ≤ 1)
    (γ : (m : ℕ) → (Fin m → Fin (n + 1)) → ℝ → Fin n → ℝ)
    (B : Finset ℝ)
    (hmax : ∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ) (y : Fin n → ℝ), m ≤ r →
      x ∈ Work.WilkG4c.I → x ∉ (B : Set ℝ) → y ∈ WilkiesDesign.openCube n →
      ContDiffAt ℝ m G (Work.WilkG4c.pt x y) →
      |iteratedFDeriv ℝ m G (Work.WilkG4c.pt x y) (fun k => Pi.single (v k) 1)| ≤
        2 * |iteratedFDeriv ℝ m G (Work.WilkG4c.curveFun (γ m v) x)
          (fun k => Pi.single (v k) 1)|)
    (hcurve : ∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ) (y : Fin n → ℝ), m ≤ r →
      x ∈ Work.WilkG4c.I → x ∉ (B : Set ℝ) → y ∈ WilkiesDesign.openCube n →
      ContDiffAt ℝ m G (Work.WilkG4c.pt x y) →
      |iteratedFDeriv ℝ m G (Work.WilkG4c.curveFun (γ m v) x) (fun k => Pi.single (v k) 1)| ≤
        Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) :
    ∀ (s : Fin (n + 1) → Fin (3 * (Work.WilkG4c.subdivN n r - 1) + 1)) (m : ℕ), m ≤ r →
      ∀ t ∈ WilkiesDesign.openCube (n + 1),
        ContDiffAt ℝ r (fun t : Fin (n + 1) → ℝ =>
          G (Work.WilkG4c.subdivMap (Work.WilkG4c.subdivN n r) s t)) t →
        ‖iteratedFDeriv ℝ m (fun t : Fin (n + 1) → ℝ =>
          G (Work.WilkG4c.subdivMap (Work.WilkG4c.subdivN n r) s t)) t‖ ≤ 1 := by
  refine subdiv_normle_of_pt_bound (n := n) (r := r) hr G h0 (fun m x y hm hx hy hG => ?_)
  exact Work.WilkG4c.pt_jet_le_multi_bad_offBC G γ B hmax hcurve hm hx hy hG

end Work.WilG4c
