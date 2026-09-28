import Mathlib
import Submission.Work.HP.Q44Child.SuperDefs
import Submission.Work.HP.lam_basic
import Submission.Work.HP.Q44Child.lam_attained
import Submission.Work.HP.BCS.small_basis_clean

/-!
# Covering radius of a rank-`2` lattice for the `lam · 2` bound

If `N ⊆ ℤ^5` has rank `2`, then every point `p` of the real span `Lℝ N` is within
`lam N 2` of an integral lattice point of `N`.

The argument is the elementary "rounding of coordinates" bound for the covering radius
of a lattice of rank `k`: taking `k = rk N = 2` linearly independent lattice vectors
`f 0, f 1` of norms bounded by the two successive minima (which exist by
`Q44Child.lam_attained`), any real combination `p = c 0 • f 0 + c 1 • f 1` is within
`(‖f 0‖ + ‖f 1‖)/2 ≤ lam N 2` of the lattice point obtained by rounding the coefficients
`c i` to the nearest integer.

The two ingredients are the existing lemmas `Work.HP.BCS.spanE_eq_span_f` (the real span
of `N` is spanned by the `f i`) and `Work.HP.BCS.close_span` (the rounding step).
-/

namespace Work.Q44Geom

/-- Every point `p` of the real span of a rank-`2` lattice `N ⊆ ℤ^5` is within `lam N 2`
of a lattice point of `N`. -/
theorem exists_close_lam_two (N : Submodule ℤ (Fin 5 → ℤ)) (hrk : Work.HP.rk N = 2)
    (p : Work.HP.Q44Child.E5) (hp : p ∈ Work.HP.Q44Child.Lℝ N) :
    ∃ n : Fin 5 → ℤ, n ∈ N ∧ ‖p - Work.HP.Q44Child.toE n‖ ≤ Work.HP.lam N 2 := by
  -- Two linearly independent lattice vectors respecting the first two successive minima.
  obtain ⟨f, hfN, hfI, hfb⟩ := Work.HP.Q44Child.lam_attained N 2 (by norm_num) (by omega)
  -- Their Euclidean images span the real span of `N`.
  have hspan : Work.HP.spanE N = Submodule.span ℝ (Set.range fun j => Work.HP.toEr (f j)) := by
    set g : Fin (Work.HP.rk N) → Fin 5 → ℤ := fun i => f (finCongr hrk i) with hgdef
    have hgN : ∀ i, g i ∈ N := fun i => hfN _
    have hgI : LinearIndependent ℤ g := hfI.comp (finCongr hrk) (finCongr hrk).injective
    have hrange : Set.range (fun i : Fin (Work.HP.rk N) => Work.HP.toEr (g i))
        = Set.range (fun j : Fin 2 => Work.HP.toEr (f j)) := by
      have h1 : (fun i : Fin (Work.HP.rk N) => Work.HP.toEr (g i))
          = (fun j : Fin 2 => Work.HP.toEr (f j)) ∘ (finCongr hrk) := rfl
      rw [h1, Set.range_comp, Set.range_eq_univ.mpr (finCongr hrk).surjective]
      simp
    rw [Work.HP.BCS.spanE_eq_span_f N g hgN hgI, hrange]
  -- Rounding the two coefficients.
  obtain ⟨n, hnN, hnbd⟩ := Work.HP.BCS.close_span N f hfN hspan p hp
  -- The successive-minima bound on the two lengths.
  have hsum : ∑ j : Fin 2, Work.HP.eNorm (f j) ≤ 2 * Work.HP.lam N 2 := by
    have h0 : Work.HP.eNorm (f 0) ≤ Work.HP.lam N 1 := by
      have := hfb (0 : Fin 2); simpa using this
    have h1 : Work.HP.eNorm (f 1) ≤ Work.HP.lam N 2 := by
      have := hfb (1 : Fin 2); simpa using this
    have hmono : Work.HP.lam N 1 ≤ Work.HP.lam N 2 :=
      Work.HP.lam_mono N (by norm_num) (by omega)
    rw [Fin.sum_univ_two]
    linarith
  have hbound : (1 / 2 : ℝ) * ∑ j : Fin 2, Work.HP.eNorm (f j) ≤ Work.HP.lam N 2 := by
    linarith
  exact ⟨n, hnN, le_trans hnbd hbound⟩

end Work.Q44Geom
