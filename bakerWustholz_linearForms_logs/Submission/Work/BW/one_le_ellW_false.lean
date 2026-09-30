import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.ellW_eq_rank

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- For `ε = false` the Lie algebra `lieSub` is contained in the hyperplane `x 0 = 0`, hence
the first basis vector `e₀` of the ambient space is never an element of it. -/
private lemma not_mem_lieSub_false {r ρ : ℕ} (M : Fin ρ → Fin r → ℤ) :
    (Pi.single (0 : Fin (r + 1)) (1 : ℂ) : Fin (r + 1) → ℂ) ∉ lieSub r ρ false M := by
  have hker : (Pi.single (0 : Fin (r + 1)) (1 : ℂ) : Fin (r + 1) → ℂ) ∉
      LinearMap.ker (LinearMap.proj (R := ℂ) (φ := fun _ : Fin (r + 1) => ℂ) 0) := by
    rw [LinearMap.mem_ker]
    simp
  have hle : lieSub r ρ false M ≤
      LinearMap.ker (LinearMap.proj (R := ℂ) (φ := fun _ : Fin (r + 1) => ℂ) 0) := by
    simp only [lieSub, Bool.false_eq_true, ite_false]
    exact inf_le_left
  exact fun h => hker (hle h)

/-- If a vector of a finite-dimensional space lies in a submodule `U` but not in a submodule
`L`, then the codimension of `U ⊓ L` in `U` is at least `1`. -/
private lemma one_le_finrank_sub_finrank {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (U L : Submodule ℂ V) (x : V)
    (hxU : x ∈ U) (hxL : x ∉ L) :
    1 ≤ Module.finrank ℂ U - Module.finrank ℂ (U ⊓ L : Submodule ℂ V) := by
  have hle : U ⊓ L ≤ U := inf_le_left
  have hne : U ⊓ L ≠ U := by
    intro h
    have hxUL : x ∈ U ⊓ L := by
      rw [h]
      exact hxU
    exact hxL hxUL.2
  have hlt : Module.finrank ℂ (U ⊓ L : Submodule ℂ V) < Module.finrank ℂ U := by
    by_contra h
    rw [not_lt] at h
    exact hne (Submodule.eq_of_le_of_finrank_le hle h)
  omega

theorem one_le_ellW_false {r : ℕ} (c : Fin (r - 1) → Fin r → ℚ) (ρ : ℕ)
    (M : Fin ρ → Fin r → ℤ) :
    1 ≤ ellW (N := r) (q := r - 1 + 1)
      (Fin.cons (Pi.single (0 : Fin (r + 1)) (1 : ℂ))
        (fun m : Fin (r - 1) => Fin.cons 0 (fun i : Fin r => ((c m i : ℚ) : ℂ))))
      false M := by
  let w : Fin (r - 1 + 1) → Fin (r + 1) → ℂ := Fin.cons (Pi.single (0 : Fin (r + 1)) (1 : ℂ))
      (fun m : Fin (r - 1) => Fin.cons 0 (fun i : Fin r => ((c m i : ℚ) : ℂ)))
  change 1 ≤ ellW w false M
  have he0V : (Pi.single (0 : Fin (r + 1)) (1 : ℂ) : Fin (r + 1) → ℂ) ∈
      Submodule.span ℂ (Set.range w) := by
    apply Submodule.subset_span
    refine ⟨(0 : Fin (r - 1 + 1)), ?_⟩
    rw [show w 0 = Pi.single (0 : Fin (r + 1)) (1 : ℂ) from Fin.cons_zero _ _]
  have he0L : (Pi.single (0 : Fin (r + 1)) (1 : ℂ) : Fin (r + 1) → ℂ) ∉ lieSub r ρ false M :=
    not_mem_lieSub_false M
  have hell : ellW w false M =
      Module.finrank ℂ (Submodule.span ℂ (Set.range w)) -
        Module.finrank ℂ ((Submodule.span ℂ (Set.range w) ⊓ lieSub r ρ false M :
          Submodule ℂ (Fin (r + 1) → ℂ))) := rfl
  rw [hell]
  exact one_le_finrank_sub_finrank _ _ _ he0V he0L

end Work.BW
