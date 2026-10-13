import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.Engine
import Submission.Work.WilG4c.norm_iteratedFDeriv_le_of_dirs
import Submission.Work.Wilkies.Defs

namespace Work.WilG4c

theorem pt_jet_le {n r : ℕ} (G : (Fin (n + 1) → ℝ) → ℝ) (γ : ℝ → Fin n → ℝ)
    (hmax : ∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ) (y : Fin n → ℝ), m ≤ r →
      x ∈ Work.WilkG4c.I → y ∈ WilkiesDesign.openCube n → ContDiffAt ℝ m G (Work.WilkG4c.pt x y) →
      |iteratedFDeriv ℝ m G (Work.WilkG4c.pt x y) (fun k => Pi.single (v k) 1)| ≤
        2 * |iteratedFDeriv ℝ m G (Work.WilkG4c.curveFun γ x) (fun k => Pi.single (v k) 1)|)
    (hcurve : ∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ), m ≤ r → x ∈ Work.WilkG4c.I →
      |iteratedFDeriv ℝ m G (Work.WilkG4c.curveFun γ x) (fun k => Pi.single (v k) 1)| ≤
        Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m)
    {m : ℕ} (hm : m ≤ r) {x : ℝ} {y : Fin n → ℝ} (hx : x ∈ Work.WilkG4c.I)
    (hy : y ∈ WilkiesDesign.openCube n) (hG : ContDiffAt ℝ m G (Work.WilkG4c.pt x y)) :
    ‖iteratedFDeriv ℝ m G (Work.WilkG4c.pt x y)‖ ≤
      2 * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) * ((n : ℝ) + 1) ^ m := by
  have hC : ∀ v : Fin m → Fin (n + 1),
      |iteratedFDeriv ℝ m G (Work.WilkG4c.pt x y) (fun k => Pi.single (v k) 1)| ≤
        2 * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) := by
    intro v
    calc |iteratedFDeriv ℝ m G (Work.WilkG4c.pt x y) (fun k => Pi.single (v k) 1)|
        ≤ 2 * |iteratedFDeriv ℝ m G (Work.WilkG4c.curveFun γ x) (fun k => Pi.single (v k) 1)| :=
          hmax m v x y hm hx hy hG
      _ ≤ 2 * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) :=
          mul_le_mul_of_nonneg_left (hcurve m v x hm hx) (by norm_num)
  have hbound := norm_iteratedFDeriv_le_of_dirs G (Work.WilkG4c.pt x y)
    (2 * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m)) hC
  calc ‖iteratedFDeriv ℝ m G (Work.WilkG4c.pt x y)‖
      ≤ (2 * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m)) * ((n + 1 : ℕ) : ℝ) ^ m := hbound
    _ = 2 * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) * ((n : ℝ) + 1) ^ m := by
        rw [Nat.cast_add, Nat.cast_one]

end Work.WilG4c
