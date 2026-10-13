/-
  WilE10 — `E10_rexp_to_subpf`, assembly.

  The two directions (the point of the forward direction lies in the semi-Pfaffian set `W`, and
  every point of `W` over a compactified parameter gives a solution of the `rexp` equation) are
  `mkPt_mem_W` and `exists_rexp_of_mem_W`; here we assemble them into the frozen statement.
-/
import Submission.Work.WilE10.RexpSubDefs
import Submission.Work.WilE10.RexpSub.mkPt_mem_W
import Submission.Work.WilE10.RexpSub.exists_rexp_of_mem_W

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE10

open WilkiesDesign WilkiesDesign.E

/-- The core of `E10_rexp_to_subpf`, for a single rexp-polynomial. -/
theorem rexp_to_subpf_core (n m : ℕ) (P : MvPolynomial (Fin (n + m) ⊕ Fin (n + m)) ℝ) :
    ∃ Z : Set (Fin n → ℝ), SubPf n Z ∧
      psiV ⁻¹' Z = {x : Fin n → ℝ | ∃ y : Fin m → ℝ, rexpPolyEval P (Fin.append x y) = 0} := by
  refine ⟨projFirst n (rd n m) '' (W n m P).set, ⟨rd n m, W n m P, rfl⟩, ?_⟩
  ext t
  rw [Set.mem_preimage, mem_projFirst_iff]
  constructor
  · rintro ⟨v, hv⟩
    exact RexpSub.exists_rexp_of_mem_W n m P t v hv
  · rintro ⟨y, hy⟩
    refine ⟨fun j => mkPt n m t (fun i => decide (|Fin.append t y i| ≤ 1)) (Fin.append t y)
        (Fin.natAdd n j), ?_⟩
    rw [append_mkPt n m t (fun i => decide (|Fin.append t y i| ≤ 1)) (Fin.append t y)]
    exact RexpSub.mkPt_mem_W n m P t y hy

end Work.WilE10

namespace WilkiesDesign.E

open WilkiesDesign

/-- **E10a.** Every `rexp`-existential set is, up to the compactification `psiV`, sub-Pfaffian. -/
theorem E10_rexp_to_subpf_proved {n : ℕ} (X : Set (Fin n → ℝ)) (h : RExpExist X) :
    ∃ Z : Set (Fin n → ℝ), SubPf n Z ∧ X = psiV ⁻¹' Z := by
  obtain ⟨m, P, rfl⟩ := h
  obtain ⟨Z, hZ, hEq⟩ := Work.WilE10.rexp_to_subpf_core n m P
  exact ⟨Z, hZ, hEq.symm⟩

end WilkiesDesign.E
