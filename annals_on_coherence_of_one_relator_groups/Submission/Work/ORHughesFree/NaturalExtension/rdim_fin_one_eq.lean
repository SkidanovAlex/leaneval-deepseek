import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.DualityDefs
import Submission.Work.ORHughesFree.NaturalExtension.DualityAPI

namespace Work.ORHughesFree.NaturalExtension

open Matrix

universe u

/-- A `1 × m`-indexed matrix has only one column, so each of its rows is the constant function
with value the entry in column `0`. -/
private lemma fin_one_fun_eq {R : Type*} [Ring R] {m : ℕ} (A : Matrix (Fin m) (Fin 1) R) (i : Fin m) :
    (fun j : Fin 1 => A i j) = (fun _ : Fin 1 => A i 0) := by
  funext j; fin_cases j; rfl

/-- `rdim` of a submodule of `R^1` is the supremum of the ranks of its elements.  Route:
`≥` is immediate (`c ↦ oneByOne c` is the case `m = 1`); for `≤`, given an `m × 1` matrix `A`
whose rows (i.e. entries `A i 0`) lie in `K`, use
`Work.ORHughesFree.DivisionRank.regular_leftIdeal_idempotent` on the finite set of entries to
get an idempotent `e` in the span of the entries with `x * e = x` for all `x` in that span;
then `A = A * oneByOne e` and `rk A ≤ rk (oneByOne e)` by `SylvesterRank.rk_mul_le_right`,
while `e ∈ K` since the entries lie in `K`. -/
theorem rdim_fin_one_eq {R : Type u} [Ring R] [VonNeumannRegularRing R] (rk : SylvesterRank R)
    (K : Submodule R (Fin 1 → R)) :
    rdim rk K = sSup {x : ℝ | ∃ c : R, (fun _ : Fin 1 => c) ∈ K ∧ x = rk.rk 1 1 (oneByOne c)} := by
  classical
  have hT_nemp : ({x : ℝ | ∃ c : R, (fun _ : Fin 1 => c) ∈ K ∧
      x = rk.rk 1 1 (oneByOne c)} : Set ℝ).Nonempty :=
    ⟨0, 0, K.zero_mem, (rk.rk_zero 1 1).symm⟩
  have hT_bdd : BddAbove ({x : ℝ | ∃ c : R, (fun _ : Fin 1 => c) ∈ K ∧
      x = rk.rk 1 1 (oneByOne c)} : Set ℝ) := by
    refine ⟨1, ?_⟩
    rintro x ⟨c, -, rfl⟩
    have h := rk.rk_mul_le_right (oneByOne c) (1 : Matrix (Fin 1) (Fin 1) R)
    rwa [Matrix.mul_one, rk.rk_one] at h
  refine le_antisymm ?_ ?_
  · -- `rdim rk K ≤ sup`: reduce an arbitrary `m × 1` matrix `A` with entries in `K`
    -- to the `1 × 1` matrix `oneByOne e`, where `e` is an idempotent generator of the left
    -- ideal spanned by the entries of `A`.
    rw [rdim]
    refine csSup_le (rdim_nonempty rk K) ?_
    rintro x ⟨m, A, hA, rfl⟩
    let s : Finset R := Finset.univ.image (fun i : Fin m => A i 0)
    obtain ⟨e, he, heprop⟩ :=
      Work.ORHughesFree.DivisionRank.regular_leftIdeal_idempotent (U := R) s
    have hmem : ∀ i : Fin m, A i 0 ∈ Submodule.span R (↑s : Set R) := by
      intro i
      exact Submodule.subset_span (show A i 0 ∈ (s : Set R) from
        Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    have hAe : ∀ i : Fin m, A i 0 * e = A i 0 := fun i => (heprop (A i 0)).mp (hmem i)
    have hAe' : A * oneByOne e = A := by
      ext i j
      fin_cases j
      simp [Matrix.mul_apply, oneByOne, hAe i]
    -- the "constant functions" copy of `R` inside `R^1`, restricted to `K`
    let φ : R →ₗ[R] (Fin 1 → R) :=
      { toFun := fun c _ => c
        map_add' := fun a b => by ext i; rfl
        map_smul' := fun a b => by ext i; rfl }
    have hsL : (↑s : Set R) ⊆ (K.comap φ : Set R) := by
      intro c hc
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hc
      show (fun _ : Fin 1 => A i 0) ∈ K
      rw [← fin_one_fun_eq A i]
      exact hA i
    have hspan_le : Submodule.span R (↑s : Set R) ≤ K.comap φ :=
      Submodule.span_le.mpr hsL
    have heL : e ∈ K.comap φ := hspan_le ((heprop e).mpr he)
    have heK : (fun _ : Fin 1 => e) ∈ K := heL
    calc rk.rk m 1 A = rk.rk m 1 (A * oneByOne e) := by rw [hAe']
      _ ≤ rk.rk 1 1 (oneByOne e) := rk.rk_mul_le_right A (oneByOne e)
      _ ≤ sSup {x : ℝ | ∃ c : R, (fun _ : Fin 1 => c) ∈ K ∧
            x = rk.rk 1 1 (oneByOne c)} := le_csSup hT_bdd ⟨e, heK, rfl⟩
  · -- `sup ≤ rdim rk K`: `oneByOne c` is the case `m = 1`.
    rw [rdim]
    refine csSup_le hT_nemp ?_
    rintro x ⟨c, hc, rfl⟩
    exact le_csSup (rdim_bddAbove rk K)
      ⟨1, oneByOne c, fun i => by simpa [oneByOne] using hc, rfl⟩

end Work.ORHughesFree.NaturalExtension
