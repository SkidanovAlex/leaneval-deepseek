import Mathlib
import Submission.Work.WilG5.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilG5.Rel

open WilkiesDesign WilkiesConjecture

variable {n d μ : ℕ}

/-! ## Padding a parametrisation

`padRel h R` forgets the last `μ - d` coordinates of the parameter of `R`, so
membership of an appended point only depends on the first `d` coordinates of the
parameter.  The two helper maps below are the truncation `Fin μ → Fin d` and the
padding `Fin d → Fin μ` (filled with the constant `1/2`, which lies in the open
cube). -/

/-- Truncate a point of the `μ`-cube to its first `d` coordinates. -/
def padTrunc (h : d ≤ μ) (u : Fin μ → ℝ) : Fin d → ℝ := fun i => u (Fin.castLE h i)

theorem padTrunc_apply (h : d ≤ μ) (u : Fin μ → ℝ) (i : Fin d) :
    padTrunc h u i = u (Fin.castLE h i) := rfl

/-- The key computation: appending `x` to `u` lands in `padRel h R` exactly when
appending `x` to the truncation of `u` lands in `R`. -/
theorem padRel_append {h : d ≤ μ} {R : Set (Fin (d + n) → ℝ)} (u : Fin μ → ℝ)
    (x : Fin n → ℝ) :
    Fin.append u x ∈ Work.WilG5.padRel h R ↔ Fin.append (padTrunc h u) x ∈ R := by
  unfold Work.WilG5.padRel padTrunc
  simp only [Set.mem_ofPred_eq, Fin.append_left, Fin.append_right]

theorem padTrunc_mem_openCube {h : d ≤ μ} {u : Fin μ → ℝ} (hu : u ∈ openCube μ) :
    padTrunc h u ∈ openCube d := fun i => hu (Fin.castLE h i)

/-- Pad a point of the `d`-cube to a point of the `μ`-cube with the constant `1/2`
(on the first `d` coordinates it agrees with the original point). -/
def padExtLE (h : d ≤ μ) (u : Fin d → ℝ) : Fin μ → ℝ :=
  fun k => if hk : ∃ i : Fin d, Fin.castLE h i = k then u (Classical.choose hk) else 1 / 2

theorem padExtLE_castLE (h : d ≤ μ) (u : Fin d → ℝ) (i : Fin d) :
    padExtLE h u (Fin.castLE h i) = u i := by
  have hk : ∃ j : Fin d, Fin.castLE h j = Fin.castLE h i := ⟨i, rfl⟩
  unfold padExtLE
  rw [dite_eq_left hk]
  exact congrArg u (Fin.castLE_injective h (Classical.choose_spec hk))

theorem padExtLE_mem_openCube {h : d ≤ μ} {u : Fin d → ℝ} (hu : u ∈ openCube d) :
    padExtLE h u ∈ openCube μ := by
  intro k
  unfold padExtLE
  by_cases hk : ∃ i : Fin d, Fin.castLE h i = k
  · rw [dite_eq_left hk]; exact hu (Classical.choose hk)
  · rw [dite_eq_right hk]; norm_num

theorem padTrunc_padExtLE (h : d ≤ μ) (u : Fin d → ℝ) : padTrunc h (padExtLE h u) = u :=
  funext fun i => padExtLE_castLE h u i

theorem pad_par {n d μ : ℕ} (h : d ≤ μ) {κ : Set (Fin n → ℝ)} {e : Fin d → Fin n} {R : Set (Fin (d + n) → ℝ)} (hpar : Work.WilG5.CellPar n κ d e R) :
    (∀ u ∈ WilkiesDesign.openCube μ, ∀ x : Fin n → ℝ, Fin.append u x ∈ Work.WilG5.padRel h R → x ∈ κ) ∧
    (∀ u ∈ WilkiesDesign.openCube μ, ∀ x y : Fin n → ℝ,
        Fin.append u x ∈ Work.WilG5.padRel h R → Fin.append u y ∈ Work.WilG5.padRel h R → x = y) ∧
    (∀ u ∈ WilkiesDesign.openCube μ, ∃ x : Fin n → ℝ, Fin.append u x ∈ Work.WilG5.padRel h R) ∧
    (∀ x ∈ κ, ∃ u ∈ WilkiesDesign.openCube μ, Fin.append u x ∈ Work.WilG5.padRel h R) ∧
    (∀ u ∈ WilkiesDesign.openCube μ,
        Work.WilG5.RelSel (Work.WilG5.padRel h R) u = Work.WilG5.RelSel R (fun i : Fin d => u (Fin.castLE h i))) := by
  have hC1 := hpar.1
  have hC2 := hpar.2.1
  have hC3 := hpar.2.2.1
  have hC4 := hpar.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u hu x hx
    exact hC1 (padTrunc h u) (padTrunc_mem_openCube hu) x ((padRel_append u x).1 hx)
  · intro u hu x y hx hy
    exact hC2 (padTrunc h u) (padTrunc_mem_openCube hu) x y
      ((padRel_append u x).1 hx) ((padRel_append u y).1 hy)
  · intro u hu
    obtain ⟨x, hx⟩ := hC3 (padTrunc h u) (padTrunc_mem_openCube hu)
    exact ⟨x, (padRel_append u x).2 hx⟩
  · intro x hx
    obtain ⟨u, hu, huR⟩ := hC4 x hx
    refine ⟨padExtLE h u, padExtLE_mem_openCube hu, ?_⟩
    rw [padRel_append, padTrunc_padExtLE]
    exact huR
  · intro u hu
    have hu' : padTrunc h u ∈ openCube d := padTrunc_mem_openCube hu
    obtain ⟨x, hx⟩ := hC3 (padTrunc h u) hu'
    have hex : ∃ y : Fin n → ℝ, Fin.append u y ∈ Work.WilG5.padRel h R :=
      ⟨x, (padRel_append u x).2 hx⟩
    have h1 : Fin.append (padTrunc h u) (Work.WilG5.RelSel (Work.WilG5.padRel h R) u) ∈ R :=
      (padRel_append u _).1 (Work.WilG5.RelSel_spec (R := Work.WilG5.padRel h R) hex)
    have hexR : ∃ y : Fin n → ℝ, Fin.append (padTrunc h u) y ∈ R := ⟨x, hx⟩
    have h2 : Fin.append (padTrunc h u) (Work.WilG5.RelSel R (padTrunc h u)) ∈ R :=
      Work.WilG5.RelSel_spec (R := R) hexR
    exact hC2 (padTrunc h u) hu' _ _ h1 h2

end Work.WilG5.Rel
