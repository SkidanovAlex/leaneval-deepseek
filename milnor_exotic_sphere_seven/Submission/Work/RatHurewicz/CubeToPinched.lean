import Mathlib
import Submission.Work.RatHurewicz.pinchedMap_nullHomotopic
import Submission.Work.RatHurewicz.RelPiPathDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The pinched map of pairs associated with a based cube in the homotopy fibre

Area **RATHUREWICZ**.  Let `A ⊆ Y`, `i = setIncl A`, `a₀ : ↥A` and let
`E = homotopyFibre i a₀` be the homotopy fibre of the inclusion, with base point `bp = (a₀, const)`
(the space of pairs `(a, γ)` with `γ` a path in `Y` from `i a₀` to `i a`).

A based cube `p : Ω^(Fin j) E bp` — i.e. a continuous `p : I^j → E` sending `∂I^j` to `bp` — is
the "pinched model" of a map of pairs `(I^{j+1}, ∂I^{j+1}) → (Y,A)`: its *pinched map*
`cubeToPinched a₀ j p : C(I^{j+1}, Y)` is the uncurried evaluation

  `x ↦ fibreCM (p (Fin.init x)) (x (Fin.last j))`,

so that on the slice `x = Fin.snoc u s` it is `s ↦ (p u).1.2.1 s`: the path attached to `p u`,
evaluated at `s`.  On the bottom face `s = 0` it is the constant `i a₀`, on the top face `s = 1` it
is `i ((p u).1.1) ∈ A`, and on the side faces it is constant `i a₀` because `p` is based.

The main use (`Work.RatHurewicz.subsingleton_relPi_of_compressRel_range`) is the converse of
`Work.RatHurewicz.pinchedMap_nullHomotopic`: a compression homotopy of `cubeToPinched a₀ j p`
*relative to the boundary* curries back to a homotopy of based cubes.

## Main names

* `mem_boundary_succ_iff` — the boundary of `I^{j+1}` via the last coordinate and `∂I^j`;
* `cubeToPinched` — the pinched map of pairs of a based cube;
* `cubeToPinched_snoc`, `cubeToPinched_snoc_zero`, `cubeToPinched_snoc_one`,
  `cubeToPinched_snoc_of_mem_boundary`, `cubeToPinched_bdry_mem`.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {Y : Type} [TopologicalSpace Y] {A : Set Y}

/-- **The boundary of `I^{j+1}`** in terms of the last coordinate and the boundary of `I^j`: a
point of `I^{j+1}` is on the boundary iff its last coordinate is `0` or `1`, or its first `j`
coordinates form a point of `∂I^j`. -/
theorem mem_boundary_succ_iff {j : ℕ} (x : ICube (j + 1)) :
    x ∈ Cube.boundary (Fin (j + 1)) ↔
      x (Fin.last j) = 0 ∨ x (Fin.last j) = 1 ∨ Fin.init x ∈ Cube.boundary (Fin j) := by
  constructor
  · rintro ⟨i, hi⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl
    · exact Or.inr (Or.inr ⟨k, hi⟩)
    · rcases hi with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  · rintro (h | h | ⟨k, hk⟩)
    · exact ⟨Fin.last j, Or.inl h⟩
    · exact ⟨Fin.last j, Or.inr h⟩
    · exact ⟨Fin.castSucc k, hk⟩

/-- **The pinched map of pairs associated with a based cube in the homotopy fibre of `A ↪ Y`.** -/
def cubeToPinched (a₀ : ↥A) (j : ℕ)
    (p : Ω^ (Fin j) (homotopyFibre (setIncl A) a₀) (homotopyFibreBasepoint (setIncl A) a₀)) :
    C(ICube (j + 1), Y) where
  toFun x := fibreCM (p (Fin.init x)) (x (Fin.last j))
  continuous_toFun :=
    continuous_apply_comp
      ((fibreCMFamily a₀).continuous.comp (p.1.continuous.comp (continuous_init j)))
      (continuous_apply (Fin.last j))

@[simp]
theorem cubeToPinched_apply (a₀ : ↥A) (j : ℕ)
    (p : Ω^ (Fin j) (homotopyFibre (setIncl A) a₀) (homotopyFibreBasepoint (setIncl A) a₀))
    (x : ICube (j + 1)) :
    cubeToPinched a₀ j p x = fibreCM (p (Fin.init x)) (x (Fin.last j)) := rfl

/-- On the slice `Fin.snoc u s`, the pinched map is the path attached to `p u`, evaluated at `s`. -/
theorem cubeToPinched_snoc (a₀ : ↥A) (j : ℕ)
    (p : Ω^ (Fin j) (homotopyFibre (setIncl A) a₀) (homotopyFibreBasepoint (setIncl A) a₀))
    (u : ICube j) (s : unitInterval) :
    cubeToPinched a₀ j p (Fin.snoc u s) = fibreCM (p u) s := by
  rw [cubeToPinched_apply, Fin.init_snoc, Fin.snoc_last]

/-- The bottom face of the pinched map is the constant `i a₀`. -/
theorem cubeToPinched_snoc_zero (a₀ : ↥A) (j : ℕ)
    (p : Ω^ (Fin j) (homotopyFibre (setIncl A) a₀) (homotopyFibreBasepoint (setIncl A) a₀))
    (u : ICube j) :
    cubeToPinched a₀ j p (Fin.snoc u 0) = setIncl A a₀ := by
  rw [cubeToPinched_snoc, fibreCM_zero]

/-- The top face of the pinched map lands in `A`. -/
theorem cubeToPinched_snoc_one (a₀ : ↥A) (j : ℕ)
    (p : Ω^ (Fin j) (homotopyFibre (setIncl A) a₀) (homotopyFibreBasepoint (setIncl A) a₀))
    (u : ICube j) :
    cubeToPinched a₀ j p (Fin.snoc u 1) = setIncl A (p u).1.1 := by
  rw [cubeToPinched_snoc, fibreCM_one]

/-- The side faces of the pinched map are the constant `i a₀` (because `p` is based). -/
theorem cubeToPinched_snoc_of_mem_boundary (a₀ : ↥A) (j : ℕ)
    (p : Ω^ (Fin j) (homotopyFibre (setIncl A) a₀) (homotopyFibreBasepoint (setIncl A) a₀))
    {u : ICube j} (hu : u ∈ Cube.boundary (Fin j)) (s : unitInterval) :
    cubeToPinched a₀ j p (Fin.snoc u s) = setIncl A a₀ := by
  rw [cubeToPinched_snoc, show p u = homotopyFibreBasepoint (setIncl A) a₀ from p.2 u hu]
  rfl

/-- **The boundary of the cube lands in `A`**: the pinched map is a map of pairs
`(I^{j+1}, ∂I^{j+1}) → (Y, A)`. -/
theorem cubeToPinched_bdry_mem (a₀ : ↥A) (j : ℕ)
    (p : Ω^ (Fin j) (homotopyFibre (setIncl A) a₀) (homotopyFibreBasepoint (setIncl A) a₀)) :
    ∀ x, x ∈ Cube.boundary (Fin (j + 1)) → cubeToPinched a₀ j p x ∈ A := by
  intro x hx
  rcases (mem_boundary_succ_iff x).mp hx with h0 | h1 | hinit
  · rw [cubeToPinched_apply, h0, fibreCM_zero]
    exact a₀.2
  · rw [cubeToPinched_apply, h1, fibreCM_one]
    exact (p (Fin.init x)).1.1.2
  · rw [cubeToPinched_apply, show p (Fin.init x) = homotopyFibreBasepoint (setIncl A) a₀
      from p.2 (Fin.init x) hinit]
    show (setIncl A a₀ : Y) ∈ A
    exact a₀.2

end

end Work.RatHurewicz
