import Mathlib
import Submission.Work.GM.S2.pair_sum_defs

/-!
# Basic regularity and size bounds for `PolySum`

`PolySum Y σ = Σ_{1 ≤ m ≤ ⌊Y⌋} m^{iσ}` is the short Dirichlet polynomial appearing in
the reflected sum of Guth–Maynard §6.  We record the two facts the surrounding
arguments use freely:

* it is a continuous function of the frequency `ξ ↦ PolySum Y (t + 2πξ)`
  (the phase is affine in `ξ`);
* each of its `⌊Y⌋` summands is unimodular, so `‖PolySum Y σ‖ ≤ ⌊Y⌋` uniformly in `σ`.
-/

open Complex Finset
open scoped BigOperators Topology

set_option autoImplicit false

namespace Work.GM.S2

/-- `PolySum Y` is continuous, hence so is the parametrised family
`ξ ↦ PolySum Y (t + 2πξ)`. -/
theorem continuous_polysum_affine (Y t : ℝ) :
    Continuous (fun ξ : ℝ => PolySum Y (t + 2 * Real.pi * ξ)) := by
  unfold PolySum
  apply continuous_finsetSum
  intro m hm
  have hm0 : (m : ℂ) ≠ 0 := by
    have h1 : (1 : ℕ) ≤ m := (Finset.mem_Icc.mp hm).1
    exact_mod_cast (by omega : m ≠ 0)
  exact Continuous.const_cpow (by fun_prop) (Or.inl hm0)

/-- Each summand `m^{iσ}` (`m ≥ 1`) is unimodular. -/
theorem norm_cpow_unimodular {m : ℕ} (hm : 0 < m) (σ : ℝ) :
    ‖(m : ℂ) ^ (Complex.I * (σ : ℂ))‖ = 1 := by
  rw [Complex.norm_natCast_cpow_of_pos hm]
  simp [Complex.mul_re]

/-- `‖PolySum Y σ‖ ≤ ⌊Y⌋` uniformly in `σ`. -/
theorem norm_polysum_le (Y σ : ℝ) :
    ‖PolySum Y σ‖ ≤ (Nat.floor Y : ℝ) := by
  unfold PolySum
  calc ‖∑ m ∈ Finset.Icc 1 (Nat.floor Y), (m : ℂ) ^ (Complex.I * (σ : ℂ))‖
      ≤ ∑ m ∈ Finset.Icc 1 (Nat.floor Y), ‖(m : ℂ) ^ (Complex.I * (σ : ℂ))‖ :=
        norm_sum_le _ _
    _ = ∑ _m ∈ Finset.Icc 1 (Nat.floor Y), (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro m hm
        have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
        exact norm_cpow_unimodular hmpos σ
    _ = ((Finset.Icc 1 (Nat.floor Y)).card : ℝ) := by simp
    _ = (Nat.floor Y : ℝ) := by
        rw [Nat.card_Icc, Nat.add_sub_cancel]

theorem polysum_basic (Y t : ℝ) :
    Continuous (fun ξ : ℝ => Work.GM.S2.PolySum Y (t + 2 * Real.pi * ξ)) ∧
      (∀ σ : ℝ, ‖Work.GM.S2.PolySum Y σ‖ ≤ (Nat.floor Y : ℝ)) :=
  ⟨continuous_polysum_affine Y t, norm_polysum_le Y⟩

end Work.GM.S2
