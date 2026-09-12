import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

namespace Commons.LinearAlgebra.Basis

open scoped BigOperators

/-- A non-dependent version of `Fin.snoc_castSucc`:
`Fin.snoc` keeps the entries of the original family on the `castSucc` indices. -/
lemma snoc_castSucc_const {α : Type*} {n : ℕ} (p : Fin n → α) (x : α) (i : Fin n) :
    Fin.snoc (α := fun _ => α) p x i.castSucc = p i := by
  exact Fin.snoc_castSucc (α := fun _ => α) x p i

/-- Any ℝ-linearly independent family of `k` vectors in `Fin (n + 1) → ℝ` with
`k ≤ n + 1` can be extended to a linearly independent family of `n + 1` vectors
whose first `k` entries (in index order) are the original vectors. -/
theorem exists_linearIndependent_extend (n k : ℕ) (hk : k ≤ n + 1)
    {w : Fin k → (Fin (n + 1) → ℝ)} (hli : LinearIndependent ℝ w) :
    ∃ E : Fin (n + 1) → (Fin (n + 1) → ℝ),
      LinearIndependent ℝ E ∧ ∀ j : Fin k, E ((Fin.castLE hk) j) = w j := by
  classical
  let V : Type := Fin (n + 1) → ℝ
  let m : ℕ := n + 1 - k
  have hfin : Module.finrank ℝ V = n + 1 := by
    dsimp [V]
    rw [Module.finrank_pi]
    simp
  -- Repeatedly append a vector that is linearly independent of the current family,
  -- `m` times in total; after `t` steps the family has length `k + t` and still
  -- agrees with `w` on its first `k` entries.
  have ind : ∀ t, t ≤ m → ∃ v : Fin (k + t) → V,
      LinearIndependent ℝ v ∧ ∀ j : Fin k, v (Fin.castLE (by omega : k ≤ k + t) j) = w j := by
    intro t
    induction t with
    | zero =>
        intro ht
        refine ⟨w, hli, ?_⟩
        intro j
        rfl
    | succ t ih =>
        intro htm
        have ht' : t ≤ m := by omega
        rcases ih ht' with ⟨v, hv, hvw⟩
        have hlt : k + t < Module.finrank ℝ V := by
          rw [hfin]
          omega
        rcases exists_linearIndependent_snoc_of_lt_finrank (R := ℝ) (M := V) (v := v) hv hlt with
          ⟨x, hx⟩
        let v' : Fin (k + (t + 1)) → V := Fin.snoc (α := fun _ => V) v x
        refine ⟨v', ?_, ?_⟩
        · simpa [v'] using hx
        · intro j
          have hstep : Fin.castLE (by omega : k ≤ k + (t + 1)) j =
              Fin.castSucc (Fin.castLE (by omega : k ≤ k + t) j) := by
            apply Fin.ext
            simp
          calc
            v' (Fin.castLE (by omega : k ≤ k + (t + 1)) j)
                = Fin.snoc (α := fun _ => V) v x (Fin.castLE (by omega : k ≤ k + (t + 1)) j) := by
                    rfl
            _ = Fin.snoc (α := fun _ => V) v x
                  (Fin.castSucc (Fin.castLE (by omega : k ≤ k + t) j)) := by
                    exact congrArg
                      (fun i : Fin (k + (t + 1)) => Fin.snoc (α := fun _ => V) v x i) hstep
            _ = v (Fin.castLE (by omega : k ≤ k + t) j) := by
                    exact snoc_castSucc_const v x (Fin.castLE (by omega : k ≤ k + t) j)
            _ = w j := hvw j
  have hm : k + m = n + 1 := by
    dsimp [m]
    omega
  rcases ind m (by omega) with ⟨v, hv, hvw⟩
  refine ⟨fun i => v (Fin.cast hm.symm i), ?_, ?_⟩
  · exact LinearIndependent.comp hv (Fin.cast hm.symm) (Fin.cast_injective hm.symm)
  · intro j
    change v (Fin.cast hm.symm (Fin.castLE hk j)) = w j
    have hidx : Fin.cast hm.symm (Fin.castLE hk j) = Fin.castLE (by omega : k ≤ k + m) j := by
      apply Fin.ext
      simp
    rw [hidx]
    exact hvw j

end Commons.LinearAlgebra.Basis