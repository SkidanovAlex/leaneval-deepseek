import Mathlib
import Submission.Work.WilE9.Deriv.contMultilinear_eq_sum_basis
import Submission.Work.WilE9.Deriv.continuousOn_iff_comp_injective
import Submission.Work.WilE9.Deriv.differentiableOn_iff_comp_injective

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators ContDiff
open Topology Filter

namespace Work.WilE9.Deriv

/-! ## The evaluation map on basis tuples, as a continuous linear map

The scalar functions `y ↦ iteratedFDeriv ℝ m f y (fun j => Pi.single (v j) 1)` appearing in the
statement are the coordinates of the *multilinear-map-valued* function
`y ↦ iteratedFDeriv ℝ m f y` under the evaluation map

`evalBasisCLM n m : ((Fin n → ℝ) [×m]→L[ℝ] ℝ) →L[ℝ] ((Fin m → Fin n) → ℝ)`.

That map is injective (the standard basis tuples determine a multilinear map), and because its
target is finite dimensional it has a continuous linear one-sided inverse; hence continuity and
differentiability `On U` transfer both ways. -/

/-- Evaluation of a continuous multilinear map on `(Fin n → ℝ)^m` at tuples of standard basis
vectors, as a continuous linear map. -/
noncomputable def evalBasisCLM (n m : ℕ) :
    ((Fin n → ℝ) [×m]→L[ℝ] ℝ) →L[ℝ] ((Fin m → Fin n) → ℝ) :=
  ContinuousLinearMap.pi (fun v : Fin m → Fin n =>
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => (Fin n → ℝ)) ℝ
      (fun j => Pi.single (v j) (1:ℝ)))

lemma evalBasisCLM_apply (n m : ℕ) (M : (Fin n → ℝ) [×m]→L[ℝ] ℝ) :
    evalBasisCLM n m M
      = fun v : Fin m → Fin n => M (fun j => Pi.single (v j) (1:ℝ)) := rfl

/-- The evaluation map on standard-basis tuples is injective on continuous multilinear maps. -/
lemma evalBasisCLM_injective (n m : ℕ) : Function.Injective (evalBasisCLM n m) := by
  intro M M' h
  ext x
  rw [contMultilinear_eq_sum_basis M x, contMultilinear_eq_sum_basis M' x]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  congr 1
  exact congr_fun h v

/-! ## Coordinate characterisations of the multilinear-valued iterated derivative -/

/-- On any set `U`, the `m`-th iterated derivative `y ↦ iteratedFDeriv ℝ m f y` is continuous
iff all of its evaluations at tuples of standard basis vectors are. -/
lemma continuousOn_iteratedFDeriv_iff {n m : ℕ} (f : (Fin n → ℝ) → ℝ) (U : Set (Fin n → ℝ)) :
    ContinuousOn (fun y => iteratedFDeriv ℝ m f y) U ↔
      ∀ v : Fin m → Fin n,
        ContinuousOn (fun y => iteratedFDeriv ℝ m f y (fun j => Pi.single (v j) 1)) U := by
  rw [← continuousOn_iff_comp_injective (evalBasisCLM n m) (evalBasisCLM_injective n m)]
  rw [continuousOn_pi]
  simp only [evalBasisCLM_apply]

/-- On any set `U`, the `m`-th iterated derivative `y ↦ iteratedFDeriv ℝ m f y` is differentiable
iff all of its evaluations at tuples of standard basis vectors are. -/
lemma differentiableOn_iteratedFDeriv_iff {n m : ℕ} (f : (Fin n → ℝ) → ℝ) (U : Set (Fin n → ℝ)) :
    DifferentiableOn ℝ (fun y => iteratedFDeriv ℝ m f y) U ↔
      ∀ v : Fin m → Fin n,
        DifferentiableOn ℝ (fun y => iteratedFDeriv ℝ m f y (fun j => Pi.single (v j) 1)) U := by
  rw [← differentiableOn_iff_comp_injective (evalBasisCLM n m) (evalBasisCLM_injective n m)]
  rw [differentiableOn_pi]
  simp only [evalBasisCLM_apply]

/-! ## The `ContDiffOn` characterisation on an open set -/

/-- On an **open** set `U`, `f` is `C^k` iff each iterated derivative `iteratedFDeriv ℝ m f` is
continuous for `m ≤ k` and differentiable for `m < k`. This is Mathlib's
`contDiffOn_nat_iff_continuousOn_differentiableOn`, transported from `iteratedFDerivWithin` to
`iteratedFDeriv` using `iteratedFDerivWithin_of_isOpen`. -/
lemma contDiffOn_iff_multilinear {n k : ℕ} (f : (Fin n → ℝ) → ℝ) (U : Set (Fin n → ℝ))
    (hU : IsOpen U) :
    ContDiffOn ℝ k f U ↔
      (∀ m, m ≤ k → ContinuousOn (fun y => iteratedFDeriv ℝ m f y) U) ∧
      (∀ m, m < k → DifferentiableOn ℝ (fun y => iteratedFDeriv ℝ m f y) U) := by
  rw [contDiffOn_nat_iff_continuousOn_differentiableOn hU.uniqueDiffOn]
  constructor
  · rintro ⟨hc, hd⟩
    exact ⟨fun m hm => (hc m hm).congr
              (fun y hy => (iteratedFDerivWithin_of_isOpen m hU hy).symm),
           fun m hm => (hd m hm).congr
              (fun y hy => (iteratedFDerivWithin_of_isOpen m hU hy).symm)⟩
  · rintro ⟨hc, hd⟩
    exact ⟨fun m hm => (hc m hm).congr
              (fun y hy => (iteratedFDerivWithin_of_isOpen m hU hy)),
           fun m hm => (hd m hm).congr
              (fun y hy => (iteratedFDerivWithin_of_isOpen m hU hy))⟩

/-- On an **open** set `U`, `f` is `C^k` iff all the *evaluated* iterated derivatives in the
coordinate directions are continuous for `m ≤ k` and differentiable for `m < k`. -/
lemma contDiffOn_iff_partials {n k : ℕ} (f : (Fin n → ℝ) → ℝ) (U : Set (Fin n → ℝ))
    (hU : IsOpen U) :
    ContDiffOn ℝ k f U ↔
      ((∀ m, m ≤ k → ∀ v : Fin m → Fin n,
          ContinuousOn (fun y => iteratedFDeriv ℝ m f y (fun j => Pi.single (v j) 1)) U) ∧
       (∀ m, m < k → ∀ v : Fin m → Fin n,
          DifferentiableOn ℝ (fun y => iteratedFDeriv ℝ m f y (fun j => Pi.single (v j) 1)) U)) := by
  rw [contDiffOn_iff_multilinear f U hU]
  constructor
  · rintro ⟨hc, hd⟩
    exact ⟨fun m hm v => (continuousOn_iteratedFDeriv_iff f U).mp (hc m hm) v,
           fun m hm v => (differentiableOn_iteratedFDeriv_iff f U).mp (hd m hm) v⟩
  · rintro ⟨hc, hd⟩
    exact ⟨fun m hm => (continuousOn_iteratedFDeriv_iff f U).mpr (fun v => hc m hm v),
           fun m hm => (differentiableOn_iteratedFDeriv_iff f U).mpr (fun v => hd m hm v)⟩

/-! ## The main theorem -/

/-- **The `C^k` characterisation used by `int {ContDiffAt ℝ k f}`.** `f` is `C^k` at `x` iff,
on a neighbourhood, all the *evaluated* iterated derivatives in the coordinate directions
`iteratedFDeriv ℝ m f y (fun j => Pi.single (v j) 1)`, `m < k`, exist and are continuous, i.e.
satisfy `ContinuousOn`/`DifferentiableOn` (the `C^{m+1}` condition on the `m`-th derivative).
This replaces the multilinear-map-valued `iteratedFDerivWithin` of Mathlib's
`contDiffOn_nat_iff_continuousOn_differentiableOn` by its evaluations at basis tuples, using
that the sups over the standard basis tuples control the operator norm on a finite-dimensional
space. -/
theorem contDiffAt_iff_partials {n k : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    ContDiffAt ℝ k f x ↔
      ∃ U : Set (Fin n → ℝ), U ∈ nhds x ∧ IsOpen U ∧
        (∀ (m : ℕ), m ≤ k → ∀ v : Fin m → Fin n,
          ContinuousOn (fun y => iteratedFDeriv ℝ m f y (fun j => Pi.single (v j) 1)) U) ∧
        (∀ (m : ℕ), m < k → ∀ v : Fin m → Fin n,
          DifferentiableOn ℝ (fun y => iteratedFDeriv ℝ m f y (fun j => Pi.single (v j) 1)) U) := by
  constructor
  · intro hf
    obtain ⟨u, hu, hcdu⟩ := hf.contDiffOn le_rfl (by simp)
    obtain ⟨U, hUu, hUo, hxU⟩ := mem_nhds_iff.mp hu
    exact ⟨U, mem_nhds_iff.mpr ⟨U, subset_rfl, hUo, hxU⟩, hUo,
      (contDiffOn_iff_partials f U hUo).mp (hcdu.mono hUu)⟩
  · rintro ⟨U, hU, hUo, hAB⟩
    exact ((contDiffOn_iff_partials f U hUo).mpr hAB).contDiffAt hU

end Work.WilE9.Deriv
