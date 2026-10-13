/-
  WilG4c — BNZ §5.4, the last step of the reduction `FLemP PYLipDef → FLemP PYLip`.

  Given a family `F` on `ℝ^{n+1}` with `YBound F r` and `LipOnCube F 1`, whose members admit
  near-maximising curves `γ = γ_{i,l}` (a curve through the fibre of the member, along which the
  mixed derivatives of order `≤ r` dominate, up to the factor `2`, their values at every interior
  point of the fibre, and are bounded by `e·(r(1+ne))^m` on the curve), the family pulled back
  along the diagonal subdivision chart `subdivMap (subdivN n r) s` satisfies `PYLipDef`:

  * `YBound`: the chart is the affine substitution `z ↦ q + z/N` with `q = subdivBase N s`, and
    `RescalePredicates` shows that a rescaling of the coordinates by `1/N` with `N ≥ 1` and a
    displacement by a point `q` whose unit cube `q + [0,1/N]` stays in the cube preserves
    `YBound` and `LipOnCube 1`;
  * `NormLeOneDef`: this is exactly `subdiv_normle`, the chain of inequalities of BNZ §5.4, whose
    inputs are the sup bound `|F| ≤ 1` on the cube (read off from `YBound` at order `0`), the
    near-maximality of `γ` and the curve bound.
-/
import Mathlib
import Submission.Work.WilG4c.StepHigherDefs
import Submission.Work.WilG4c.subdiv_normle
import Submission.Work.WilG4c.RescalePredicates
import Submission.Work.WilG4c.ScaledLip

set_option autoImplicit false
noncomputable section

open Classical
open Work.WilkG4c WilkiesDesign WilkiesDesign.CG

namespace Work.WilG4c

/-! ## Auxiliary facts about the diagonal subdivision -/

/-- The base point of the `s`-th subdivision cube stays a full `1/N` away from the far face of
the unit cube: `subdivBase N s j + 1/N ≤ 1` for `1 ≤ N`.  (Each `subdivBase N s j` is a multiple
of `1/(3N)` and `s j ≤ 3(N-1)`.) -/
theorem subdivBase_add_inv_le_one {n N : ℕ} (hN : 1 ≤ N)
    (s : Fin (n + 1) → Fin (3 * (N - 1) + 1)) (j : Fin (n + 1)) :
    Work.WilkG4c.subdivBase N s j + (N : ℝ)⁻¹ ≤ 1 := by
  have h3N : (0 : ℝ) < 3 * (N : ℝ) := by
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    linarith
  have hsj : (s j : ℕ) ≤ 3 * (N - 1) := by have := (s j).2; omega
  have hcast : (((s j : ℕ)) : ℝ) ≤ 3 * ((N : ℝ) - 1) := by
    have h : (((s j : ℕ)) : ℝ) ≤ ((3 * (N - 1) : ℕ) : ℝ) := by exact_mod_cast hsj
    rw [Nat.cast_mul, Nat.cast_sub hN, Nat.cast_one] at h
    simpa using h
  have key : Work.WilkG4c.subdivBase N s j + (N : ℝ)⁻¹
      = ((((s j : ℕ)) : ℝ) + 3) / (3 * (N : ℝ)) := by
    rw [Work.WilkG4c.subdivBase,
      show (N : ℝ)⁻¹ = 3 / (3 * (N : ℝ)) by field_simp, ← add_div]
  rw [key, div_le_one h3N]
  linarith

/-- The subdivision chart is the affine substitution `z ↦ subdivBase N s + z/N`. -/
theorem subdivMap_eq_div {n : ℕ} (N : ℕ) (s : Fin (n + 1) → Fin (3 * (N - 1) + 1))
    (t : Fin (n + 1) → ℝ) :
    Work.WilkG4c.subdivMap N s t = fun j => Work.WilkG4c.subdivBase N s j + t j / (N : ℝ) := by
  funext j
  rw [Work.WilkG4c.subdivMap_eq]
  simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- `YBound` bounds each member of the family by `1` in absolute value on the cube: order `0` of
the derivative bound of the `x`-slices. -/
theorem abs_le_one_of_YBound {k p n r : ℕ} {F : Work.WilkG4c.Family k p (n + 1)}
    (hY : Work.WilkG4c.YBound F r) (i : Fin k) (l : Fin p → ℝ) :
    ∀ z ∈ openCube (n + 1), |F i l z| ≤ 1 := by
  intro w hw
  have hb := hY i l (w 0) (hw 0) 0 (Nat.zero_le r) (Fin.tail w) (fun j => hw j.succ)
  rw [norm_iteratedFDeriv_zero] at hb
  have hw' : Work.WilkG4c.slice (F i l) (w 0) (Fin.tail w) = F i l w := by
    rw [Work.WilkG4c.slice_apply, Work.WilkG4c.pt_eta]
  rwa [hw', Real.norm_eq_abs] at hb

/-! ## The pullback satisfies `PYLipDef` -/

theorem pullback_pylipdef {k p n r : ℕ} (hr : 1 ≤ r) :
    ∀ (F : Work.WilkG4c.Family k p (n + 1))
      (s : Fin (n + 1) → Fin (3 * (Work.WilkG4c.subdivN n r - 1) + 1)),
      Work.WilkG4c.YBound F r → Work.WilkG4c.LipOnCube F 1 →
      (∀ (i : Fin k) (l : Fin p → ℝ),
        ∃ γ : ℝ → Fin n → ℝ, ∀ x ∈ Work.WilkG4c.I, γ x ∈ WilkiesDesign.openCube n ∧
          (∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (y : Fin n → ℝ), m ≤ r →
            y ∈ WilkiesDesign.openCube n → ContDiffAt ℝ m (F i l) (Work.WilkG4c.pt x y) →
            |iteratedFDeriv ℝ m (F i l) (Work.WilkG4c.pt x y) (fun t => Pi.single (v t) 1)| ≤
              2 * |iteratedFDeriv ℝ m (F i l) (Work.WilkG4c.curveFun γ x)
                    (fun t => Pi.single (v t) 1)|) ∧
          (∀ (m : ℕ) (v : Fin m → Fin (n + 1)), m ≤ r →
            |iteratedFDeriv ℝ m (F i l) (Work.WilkG4c.curveFun γ x)
                (fun t => Pi.single (v t) 1)| ≤
              Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m)) →
      Work.WilkG4c.PYLipDef p n r k
        (fun i l t => F i l (Work.WilkG4c.subdivMap (Work.WilkG4c.subdivN n r) s t)) := by
  intro F s hY hLip hγ
  -- the base point of the subdivision cube, and the family in the "div" form
  set q : Fin (n + 1) → ℝ := Work.WilkG4c.subdivBase (Work.WilkG4c.subdivN n r) s with hqdef
  have hN : 1 ≤ Work.WilkG4c.subdivN n r := Work.WilkG4c.subdivN_pos hr
  have hfam : (fun (i : Fin k) (l : Fin p → ℝ) (z : Fin (n + 1) → ℝ) =>
        F i l (fun j => q j + z j / ((Work.WilkG4c.subdivN n r : ℕ) : ℝ)))
      = (fun (i : Fin k) (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) =>
        F i l (Work.WilkG4c.subdivMap (Work.WilkG4c.subdivN n r) s t)) := by
    funext i l t
    congr 1
    funext j
    rw [Work.WilG4c.subdivMap_eq_div, hqdef]
  -- the rescaled family is `YBound` and `1`-Lipschitz: `RescalePredicates`
  have hRP := Work.WilkG4c.RescalePredicates n p (Work.WilkG4c.subdivN n r) hN q
    (fun j => by rw [hqdef]; exact Work.WilkG4c.subdivBase_nonneg (Work.WilkG4c.subdivN n r) s j)
    (fun j => by
      rw [hqdef]
      simpa [one_div] using
        Work.WilG4c.subdivBase_add_inv_le_one (N := Work.WilkG4c.subdivN n r) hN s j)
    F r 1 le_rfl (by exact_mod_cast hN) (∅ : Set (Fin p → ℝ)) hY hLip
    (fun i l hl => absurd hl (by simp))
  refine ⟨hfam ▸ hRP.1, hfam ▸ hRP.2.1, ?_⟩
  -- `NormLeOneDef`: the diagonal subdivision estimate `subdiv_normle`, member by member
  intro i l z hz hcd m hm
  obtain ⟨γ, hγspec⟩ := hγ i l
  exact Work.WilkG4c.subdiv_normle (n := n) (r := r) hr (F i l) γ
    (Work.WilG4c.abs_le_one_of_YBound hY i l)
    (fun m v x y hm hx hy hcd' => (hγspec x hx).2.1 m v y hm hy hcd')
    (fun m v x hm hx => (hγspec x hx).2.2 m v hm)
    s m hm z hz hcd

end Work.WilG4c
