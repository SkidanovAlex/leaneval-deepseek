import Mathlib
import Submission.Work.WilG4c.subdiv_normle_multi
import Submission.Work.WilG4c.pt_jet_le_multi
import Submission.Work.WilG4c.StepHigherDefs
import Submission.Work.WilG4c.abs_le_of_continuousAt_of_mem_closure
import Submission.Work.WilG4c.continuousAt_pt_jet
import Submission.Work.WilG4c.mem_closure_good_pts

set_option autoImplicit false
noncomputable section
open Classical
open scoped Topology

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- **Pointwise jet bound away from a finite bad set.**  This is `pt_jet_le_multi` with the
near-maximality hypothesis required only off a finite set `B` of `x`-coordinates.

The two hypotheses alone give the bound `2 (e (r (1 + n e))^m)` on every fixed tuple of
coordinate directions at the *good* points `x ∉ B`.  At a bad point `x ∈ B` the bound is
recovered by continuity: the function `x' ↦ D^m G (pt x' y) (e_{v})` is continuous at `x`
(`continuousAt_pt_jet`, using `C^m` of `G` at `pt x y`), it is bounded by `2 (e (r(1+ne))^m)`
on the "good" set `{x' ∈ I : x' ∉ B, pt x' y ∈ U}` (a neighbourhood of `x` minus a finite set,
hence accumulating at `x`, `mem_closure_good_pts`), and a bound that holds on a set accumulating
at a continuity point passes to the limit (`abs_le_of_continuousAt_of_mem_closure`). -/
theorem pt_jet_le_multi_bad {n r : ℕ} (G : (Fin (n + 1) → ℝ) → ℝ)
    (γ : (m : ℕ) → (Fin m → Fin (n + 1)) → ℝ → Fin n → ℝ)
    (B : Finset ℝ)
    (hmax : ∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ) (y : Fin n → ℝ), m ≤ r →
      x ∈ Work.WilkG4c.I → x ∉ (B : Set ℝ) → y ∈ WilkiesDesign.openCube n →
      ContDiffAt ℝ m G (Work.WilkG4c.pt x y) →
      |iteratedFDeriv ℝ m G (Work.WilkG4c.pt x y) (fun k => Pi.single (v k) 1)| ≤
        2 * |iteratedFDeriv ℝ m G (Work.WilkG4c.curveFun (γ m v) x)
          (fun k => Pi.single (v k) 1)|)
    (hcurve : ∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ), m ≤ r →
      x ∈ Work.WilkG4c.I →
      |iteratedFDeriv ℝ m G (Work.WilkG4c.curveFun (γ m v) x) (fun k => Pi.single (v k) 1)| ≤
        Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m)
    {m : ℕ} (hm : m ≤ r) {x : ℝ} {y : Fin n → ℝ} (hx : x ∈ Work.WilkG4c.I)
    (hy : y ∈ WilkiesDesign.openCube n) (hG : ContDiffAt ℝ m G (Work.WilkG4c.pt x y)) :
    ‖iteratedFDeriv ℝ m G (Work.WilkG4c.pt x y)‖ ≤
      2 * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) * ((n : ℝ) + 1) ^ m := by
  -- Bound the jet at `pt x y` on every tuple of coordinate directions.
  have hC : ∀ v : Fin m → Fin (n + 1),
      |iteratedFDeriv ℝ m G (Work.WilkG4c.pt x y) (fun k => Pi.single (v k) 1)| ≤
        2 * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) := by
    intro v
    -- `G` is `C^m` on a neighbourhood of `pt x y`; take its interior as the open `U`.
    obtain ⟨U, hUnhds, hUcd⟩ := hG.contDiffOn le_rfl (fun h => absurd h (by simp))
    -- The set of good `x`-coordinates (inside `I`, outside `B`, with `pt · y` in `U`).
    refine abs_le_of_continuousAt_of_mem_closure
      (f := fun x' : ℝ => iteratedFDeriv ℝ m G (Work.WilkG4c.pt x' y) (fun k => Pi.single (v k) 1))
      (x₀ := x) (C := 2 * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m))
      (s := {x' : ℝ | x' ∈ Work.WilkG4c.I ∧ x' ∉ (B : Set ℝ) ∧
        Work.WilkG4c.pt x' y ∈ interior U})
      ?_ (continuousAt_pt_jet hG) ?_
    · -- the good coordinates accumulate at `x`
      exact mem_closure_good_pts (B := B) (y := y) (U := interior U) isOpen_interior
        (mem_interior_iff_mem_nhds.mpr hUnhds) hx
    · -- and the bound holds at every good coordinate
      intro x' hx'
      obtain ⟨hx'I, hx'B, hx'U⟩ := hx'
      have hcd : ContDiffAt ℝ m G (Work.WilkG4c.pt x' y) :=
        hUcd.contDiffAt (Filter.mem_of_superset (isOpen_interior.mem_nhds hx'U) interior_subset)
      calc |iteratedFDeriv ℝ m G (Work.WilkG4c.pt x' y) (fun k => Pi.single (v k) 1)|
          ≤ 2 * |iteratedFDeriv ℝ m G (Work.WilkG4c.curveFun (γ m v) x')
                (fun k => Pi.single (v k) 1)| := hmax m v x' y hm hx'I hx'B hy hcd
        _ ≤ 2 * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) :=
            mul_le_mul_of_nonneg_left (hcurve m v x' hm hx'I) (by norm_num)
  -- Multilinear expansion: `(n+1)^m` coordinate tuples.
  have hbound := Work.WilG4c.norm_iteratedFDeriv_le_of_dirs G (Work.WilkG4c.pt x y)
    (2 * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m)) hC
  calc ‖iteratedFDeriv ℝ m G (Work.WilkG4c.pt x y)‖
      ≤ (2 * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m)) * ((n + 1 : ℕ) : ℝ) ^ m := hbound
    _ = 2 * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) * ((n : ℝ) + 1) ^ m := by
        rw [Nat.cast_add, Nat.cast_one]

/-- `Work.WilkG4c.subdiv_normle_multi` with the near-maximality hypothesis `hmax` required only
off a finite ("bad") set `B` of `x`-coordinates.  At the bad points the bound is recovered by
continuity of `iteratedFDeriv ℝ m (G ∘ subdivMap)` there (which holds because the composite is
`C^r` at the point and `m ≤ r`). -/
theorem subdiv_normle_multi_bad {n r : ℕ} (hr : 1 ≤ r) (G : (Fin (n + 1) → ℝ) → ℝ)
    (h0 : ∀ z ∈ WilkiesDesign.openCube (n + 1), |G z| ≤ 1)
    (γ : (m : ℕ) → (Fin m → Fin (n + 1)) → ℝ → Fin n → ℝ)
    (B : Finset ℝ)
    (hmax : ∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ) (y : Fin n → ℝ), m ≤ r →
      x ∈ Work.WilkG4c.I → x ∉ (B : Set ℝ) → y ∈ WilkiesDesign.openCube n →
      ContDiffAt ℝ m G (Work.WilkG4c.pt x y) →
      |iteratedFDeriv ℝ m G (Work.WilkG4c.pt x y) (fun k => Pi.single (v k) 1)| ≤
        2 * |iteratedFDeriv ℝ m G (Work.WilkG4c.curveFun (γ m v) x)
          (fun k => Pi.single (v k) 1)|)
    (hcurve : ∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ), m ≤ r →
      x ∈ Work.WilkG4c.I →
      |iteratedFDeriv ℝ m G (Work.WilkG4c.curveFun (γ m v) x) (fun k => Pi.single (v k) 1)| ≤
        Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) :
    ∀ (s : Fin (n + 1) → Fin (3 * (Work.WilkG4c.subdivN n r - 1) + 1)) (m : ℕ), m ≤ r →
      ∀ t ∈ WilkiesDesign.openCube (n + 1),
        ContDiffAt ℝ r (fun t : Fin (n + 1) → ℝ =>
          G (Work.WilkG4c.subdivMap (Work.WilkG4c.subdivN n r) s t)) t →
        ‖iteratedFDeriv ℝ m (fun t : Fin (n + 1) → ℝ =>
          G (Work.WilkG4c.subdivMap (Work.WilkG4c.subdivN n r) s t)) t‖ ≤ 1 := by
  -- The analytic core of `subdiv_normle_multi` needs only the pointwise jet bound, which
  -- `pt_jet_le_multi_bad` supplies everywhere, bad `x`-coordinates included.
  refine subdiv_normle_of_pt_bound (n := n) (r := r) hr G h0 (fun m x y hm hx hy hG => ?_)
  exact pt_jet_le_multi_bad G γ B hmax hcurve hm hx hy hG

end Work.WilG4c
