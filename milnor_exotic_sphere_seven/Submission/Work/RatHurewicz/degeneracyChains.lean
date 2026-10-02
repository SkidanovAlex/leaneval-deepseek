import Mathlib
import Submission.Work.RatHurewicz.degenFaces
import Submission.Work.RatHurewicz.CubicalDefs
import Submission.Work.RatHurewicz.Bridge.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The degenerate cubical chains as the span of the degeneracy operators

`Work.RatHurewicz.Deg n X` (`CubicalDefs.lean`) is the submodule of the cubical `n`-chains spanned by
the cubes which are *independent of* one coordinate.  This file records the two facts that make
`Deg` usable in chain manipulations:

* `Dlin n k` — the `ℤ`-linear extension of the degeneracy operator `D_k χ = χ ∘ delG k`
  (`degenFaces.lean`) to chains, and the identification

  **`Deg (n+1) X = ⨆ k : Fin (n+1), LinearMap.range (Dlin n k)`**,

  i.e. a chain is degenerate exactly when it is a `ℤ`-linear combination of `D_k`-images of
  `n`-chains;
* the usable form `exists_decomposition_of_mem_Deg`: every `d ∈ Deg (n+1) X` can be *written*
  `d = ∑ k, Dlin n k (e k)`.

This is the bridge needed to feed the hypothesis `d ∈ Deg (m+2) X` of
`Work.RatHurewicz.DegenCycleKilled` into any argument that works on the generators `D_k c`.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The `ℤ`-linear extension of the degeneracy operator `D_k` to cubical `n`-chains. -/
def Dlin (n : ℕ) (k : Fin (n + 1)) : Cub n X →ₗ[ℤ] Cub (n + 1) X :=
  Finsupp.linearCombination ℤ fun s : C(IC n, X) => Finsupp.single (degenOp k s) (1 : ℤ)

@[simp] theorem Dlin_single (n : ℕ) (k : Fin (n + 1)) (s : C(IC n, X)) :
    Dlin (X := X) n k (Finsupp.single s (1 : ℤ)) = Finsupp.single (degenOp k s) (1 : ℤ) := by
  rw [Dlin, Finsupp.linearCombination_single, one_smul]

theorem Dlin_single_smul (n : ℕ) (k : Fin (n + 1)) (s : C(IC n, X)) (a : ℤ) :
    Dlin (X := X) n k (Finsupp.single s a) = a • Finsupp.single (degenOp k s) (1 : ℤ) := by
  rw [Dlin, Finsupp.linearCombination_single]

/-- `D_k χ` is independent of the coordinate `k`. -/
theorem degenOp_indep {n : ℕ} (k : Fin (n + 1)) (s : C(IC n, X)) :
    ∀ t t' : IC (n + 1), (∀ j : Fin (n + 1), j ≠ k → t j = t' j) →
      degenOp k s t = degenOp k s t' := by
  intro t t' ht
  simp only [degenOp_apply]
  congr 1
  funext j
  exact ht (k.succAbove j) (Fin.succAbove_ne k j)

/-- The points `faceCM i b (delG i t)` and `t` agree away from the coordinate `i`. -/
theorem faceCM_delG_apply_of_ne {n : ℕ} (i : Fin (n + 1)) (b : unitInterval) (t : IC (n + 1))
    {j : Fin (n + 1)} (hj : j ≠ i) : faceCM i b (delG n i t) j = t j := by
  have hmem : j ∈ Set.range i.succAbove := by
    rw [Fin.range_succAbove]
    simpa using hj
  obtain ⟨k, hk⟩ := hmem
  rw [← hk, faceCM_apply_succAbove, delG_apply]

/-- **The `D_k`-images of the `n`-chains span the degenerate `(n+1)`-chains.** -/
theorem Deg_le_iSup_range_Dlin (n : ℕ) :
    Deg (n + 1) X ≤ ⨆ k : Fin (n + 1), LinearMap.range (Dlin (X := X) n k) := by
  rw [Deg]
  refine iSup_le fun i => Submodule.span_le.mpr ?_
  rintro x ⟨f, hf, rfl⟩
  refine Submodule.mem_iSup_of_mem i ⟨Finsupp.single (f.comp (faceCM i (cval 0))) (1 : ℤ), ?_⟩
  rw [Dlin_single]
  congr 1
  ext t
  simp only [ContinuousMap.comp_apply, degenOp_apply]
  exact hf _ _ fun j hj => faceCM_delG_apply_of_ne i (cval 0) t hj

theorem Dlin_mem_Deg (n : ℕ) (k : Fin (n + 1)) (c : Cub n X) :
    Dlin (X := X) n k c ∈ Deg (n + 1) X := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  | single s a =>
      rw [Dlin_single_smul]
      exact Submodule.smul_mem _ _ (Bridge.Deg_of_indep k (degenOp_indep k s))

theorem iSup_range_Dlin_le_Deg (n : ℕ) :
    (⨆ k : Fin (n + 1), LinearMap.range (Dlin (X := X) n k)) ≤ Deg (n + 1) X :=
  iSup_le fun k => by rintro c ⟨e, rfl⟩; exact Dlin_mem_Deg n k e

/-- **The degenerate `(n+1)`-chains are exactly the span of the degeneracy operators.** -/
theorem Deg_eq_iSup_range_Dlin (n : ℕ) :
    Deg (n + 1) X = ⨆ k : Fin (n + 1), LinearMap.range (Dlin (X := X) n k) :=
  le_antisymm (Deg_le_iSup_range_Dlin n) (iSup_range_Dlin_le_Deg n)

/-- The linear map `e ↦ ∑ k, D_k (e k)`. -/
def Dall (n : ℕ) : (Fin (n + 1) → Cub n X) →ₗ[ℤ] Cub (n + 1) X :=
  ∑ k : Fin (n + 1),
    (Dlin (X := X) n k).comp (LinearMap.proj (R := ℤ) (φ := fun _ : Fin (n + 1) => Cub n X) k)

theorem Dall_apply (n : ℕ) (e : Fin (n + 1) → Cub n X) :
    Dall (X := X) n e = ∑ k, Dlin (X := X) n k (e k) := by
  simp only [Dall, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Finset.sum_apply]

theorem Deg_le_range_Dall (n : ℕ) : Deg (n + 1) X ≤ LinearMap.range (Dall (X := X) n) := by
  refine le_trans (Deg_le_iSup_range_Dlin n) (iSup_le fun i => ?_)
  rintro c ⟨e, rfl⟩
  exact ⟨fun k => if k = i then e else 0, by
    rw [Dall_apply, Finset.sum_eq_single i]
    · simp
    · intro k _ hk; simp [hk]
    · intro h; exact absurd (Finset.mem_univ i) h⟩

/-- **Usable form.**  Every degenerate `(n+1)`-chain is a finite `ℤ`-linear combination of
`D_k`-images of `n`-chains. -/
theorem exists_decomposition_of_mem_Deg {n : ℕ} {d : Cub (n + 1) X}
    (hd : d ∈ Deg (n + 1) X) :
    ∃ e : Fin (n + 1) → Cub n X, d = ∑ k, Dlin (X := X) n k (e k) := by
  obtain ⟨e, he⟩ := Deg_le_range_Dall n hd
  exact ⟨e, by rw [← he, Dall_apply]⟩

end

end Work.RatHurewicz
