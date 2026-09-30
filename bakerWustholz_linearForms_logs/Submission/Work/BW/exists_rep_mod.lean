import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- If `d > 0` and the subgroup `L ⊆ ℤ^ρ` contains `d • ℤ^ρ`, then every coset of `L` has a
representative all of whose coordinates lie in `[0, d)`: take any lift and reduce each coordinate
modulo `d` (`L ∋ d • k = lift - reduction`). -/
theorem exists_rep_mod {ρ : ℕ} (L : Submodule ℤ (Fin ρ → ℤ)) (d : ℕ) (hd : 0 < d)
    (hmem : ∀ y : Fin ρ → ℤ, ((d : ℤ) • y) ∈ L) :
    ∃ rep : (Fin ρ → ℤ) ⧸ L → (Fin ρ → ℤ),
      (∀ c, Submodule.Quotient.mk (rep c) = c) ∧
        ∀ c i, 0 ≤ rep c i ∧ rep c i < (d : ℤ) := by
  -- Reduce every coordinate of the canonical lift `Quotient.out c` modulo `d`.
  refine ⟨fun c i => Quotient.out c i % (d : ℤ), ?_, ?_⟩
  · intro c
    -- It suffices that the difference `lift - reduction` lies in `L`.
    have hmem' : Quotient.out c - (fun i => Quotient.out c i % (d : ℤ)) ∈ L := by
      have hcoord : Quotient.out c - (fun i => Quotient.out c i % (d : ℤ)) =
          (d : ℤ) • (fun i => Quotient.out c i / (d : ℤ)) := by
        ext i
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        have h := Int.mul_ediv_add_emod (Quotient.out c i) (d : ℤ)
        linarith
      rw [hcoord]
      exact hmem _
    have h2 : Submodule.Quotient.mk (Quotient.out c) =
        Submodule.Quotient.mk (fun i => Quotient.out c i % (d : ℤ)) :=
      (Submodule.Quotient.eq L).mpr hmem'
    rw [Submodule.Quotient.mk_out c] at h2
    exact h2.symm
  · intro c i
    exact ⟨Int.emod_nonneg _ (by exact_mod_cast hd.ne'),
      Int.emod_lt_of_pos _ (by exact_mod_cast hd)⟩

end Work.BW
