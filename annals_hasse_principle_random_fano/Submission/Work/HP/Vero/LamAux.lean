import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Vero.SigmaDefs
import Submission.Work.HP.Lat.detLAux

/-!
# Auxiliary lemmas for `lamR_dual_Gam_two`

* `le_lamR_one`: to prove `c ≤ lamR L 1` it suffices to bound the norm of every nonzero element of
  `L` from below by `c`, provided `L` has a nonzero element.
* `sigma_mem_Gam`: the paper's `σ(u,v)` lies in `Γ = Λ_{ν₂x} ∩ Λ_{ν₂y}` as soon as `u ⊥ x` and
  `v ⊥ y`.
* `canU`, `canV`: the test vectors `‖x‖²y - ⟨x,y⟩x` and `‖y‖²x - ⟨x,y⟩y` of the first case, with
  their basic pairing properties.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP.Vero

open Work.HP

/-- The Euclidean norm is nonnegative. -/
lemma rNorm_nonneg' {ι : Type*} [Fintype ι] (v : ι → ℝ) : 0 ≤ rNorm v := Real.sqrt_nonneg _

/-- If every nonzero element of `L` has norm at least `c`, and `L` has a nonzero element, then
`c ≤ lamR L 1`. -/
theorem le_lamR_one {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℝ)) {c : ℝ}
    (hne : ∃ v ∈ L, v ≠ 0) (h : ∀ v ∈ L, v ≠ 0 → c ≤ rNorm v) : c ≤ lamR L 1 := by
  rw [lamR]
  refine le_csInf ?_ ?_
  · obtain ⟨v, hv, hv0⟩ := hne
    exact ⟨rNorm v, rNorm_nonneg' v, fun _ : Fin 1 => v, fun _ => hv,
      linearIndependent_unique_iff.mpr hv0, fun _ => le_rfl⟩
  · rintro r ⟨hr, f, hfL, hfLI, hfr⟩
    have h0 : f 0 ∈ L := hfL 0
    have h0' : f 0 ≠ 0 := hfLI.ne_zero 0
    exact (h (f 0) h0 h0').trans (hfr 0)

variable {n : ℕ}

/-- `σ(u,v) ∈ Γ` when `u ⊥ x` and `v ⊥ y`. -/
theorem sigma_mem_Gam (x y u v : Fin (n + 1) → ℤ)
    (hu : ∑ i, u i * x i = 0) (hv : ∑ i, v i * y i = 0) :
    sigma n u v ∈ Gam 2 n x y := by
  rw [Gam, Submodule.mem_inf, mem_latOrth, mem_latOrth, pdot, pdot]
  constructor
  · have h := dot_veronese_sigma n x u v
    rw [Finset.sum_congr rfl (fun i _ => mul_comm (x i) (u i)), hu, zero_mul] at h
    rw [show dotZ (sigma n u v) (veronese 2 n x)
          = ∑ m, veronese 2 n x m * sigma n u v m from
        Finset.sum_congr rfl (fun i _ => mul_comm _ _), h]
  · have h := dot_veronese_sigma n y u v
    rw [Finset.sum_congr rfl (fun j _ => mul_comm (y j) (v j)), hv, mul_zero] at h
    rw [show dotZ (sigma n u v) (veronese 2 n y)
          = ∑ m, veronese 2 n y m * sigma n u v m from
        Finset.sum_congr rfl (fun i _ => mul_comm _ _), h]

/-- The first test vector `‖x‖² • y - ⟨x,y⟩ • x` of the first case. -/
def canU (n : ℕ) (x y : Fin (n + 1) → ℤ) : Fin (n + 1) → ℤ :=
  (∑ i, x i * x i) • y - (∑ i, x i * y i) • x

/-- The second test vector `‖y‖² • x - ⟨x,y⟩ • y` of the first case. -/
def canV (n : ℕ) (x y : Fin (n + 1) → ℤ) : Fin (n + 1) → ℤ :=
  (∑ i, y i * y i) • x - (∑ i, x i * y i) • y

end Work.HP.Vero
