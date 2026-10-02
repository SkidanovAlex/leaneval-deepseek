import Mathlib
import Submission.Work.StemsB.fibrationLES_of_serre
import Submission.Work.StemsB.exists_lift_rel
import Submission.Work.RatHurewicz.Excision
import Submission.Work.Stems.subsingleton_homotopyGroup_change_basepoint

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Connectivity of the total space, from the fibration long exact sequence

For a Hurewicz fibration `p : E → B` with `k`-connected fibre over `p e₀` (`k ≥ 2`) and vanishing
`π_j(B)` for `j ≤ k-1`, the total space has vanishing `π_J` for `1 ≤ J ≤ k-1` — at the base point
`e₀` (the exactness at `π_J(E)` of the fibration sequence), and at every point of the fibre over
`p e₀` (the fibre is path connected by `π_0 = 0`, and triviality transfers along paths).

This is the input `π_J E = 0` that `Cofibre/BMInstantiate.lean` needs in order to instantiate the
Blakers–Massey hypotheses (A) and (B) at arbitrary base points of `cofibreU ι`.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **The fibre over `p e₀` is path connected** when `π_0` of it vanishes. -/
theorem joined_fibre_of_subsingleton (p : C(E, B)) (e₀ : E)
    (h0 : Subsingleton (HomotopyGroup (Fin 0) (↥(p ⁻¹' {p e₀})) ⟨e₀, rfl⟩)) :
    ∀ x : ↥(p ⁻¹' {p e₀}), Nonempty (Path x ⟨e₀, rfl⟩) := by
  have hZ : Subsingleton (ZerothHomotopy (↥(p ⁻¹' {p e₀}))) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := (HomotopyGroup.pi0EquivZerothHomotopy
      (X := ↥(p ⁻¹' {p e₀})) (x := ⟨e₀, rfl⟩)).surjective a
    obtain ⟨b', rfl⟩ := (HomotopyGroup.pi0EquivZerothHomotopy
      (X := ↥(p ⁻¹' {p e₀})) (x := ⟨e₀, rfl⟩)).surjective b
    exact congrArg _ (h0.elim a' b')
  intro x
  exact Quotient.exact (hZ.elim (ZerothHomotopy.mk x) (ZerothHomotopy.mk ⟨e₀, rfl⟩))

/-- **`π_J` of the fibre is trivial at every base point**, for `J ≤ k`: triviality at `⟨e₀, rfl⟩`
transfers along a path, and the fibre is path connected because `π_0` of it vanishes. -/
theorem subsingleton_pi_fibre_of_mem (p : C(E, B)) (e₀ : E) (k : ℕ)
    (hconn : ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j) (↥(p ⁻¹' {p e₀})) ⟨e₀, rfl⟩))
    (J : ℕ) (hJ : J ≤ k) (x : ↥(p ⁻¹' {p e₀})) :
    Subsingleton (HomotopyGroup (Fin J) ↥(p ⁻¹' {p e₀}) x) := by
  obtain ⟨γ⟩ := joined_fibre_of_subsingleton p e₀ (hconn 0 (by omega)) x
  exact Work.Stems.subsingleton_homotopyGroup_change_basepoint (N := Fin J) γ.symm (hconn J hJ)

/-- **`π_J E` is trivial at the base point**, for `2 ≤ J ≤ k-1`.

Exactness at `π_J(E)` of the fibration sequence is `Work.StemsB.les_exact_E` at index `J-2` (note
`πmap f n` lands in `π_{n+1}` — `Submission/Work/StemsB/PiMap.lean` — so the middle space of the
relation at index `n` is `π_{n+2}(E)`): every `a : π_J(E)` has `π_{J-1}(p) a = 1` by `hmodel`, hence
`a = π_{J-1}(fibreIncl) x`, and all such `x` are equal by `hconn`. -/
theorem subsingleton_pi_E_basepoint (p : C(E, B)) (hp : Work.StemsB.IsHurewiczFibration p) (e₀ : E)
    (k : ℕ) (J : ℕ) (hJ : 2 ≤ J) (hJk : J ≤ k - 1)
    (hconn : ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j) (↥(p ⁻¹' {p e₀})) ⟨e₀, rfl⟩))
    (hmodel : ∀ j : ℕ, j ≤ 2 * k - 1 → j ≠ k →
      Subsingleton (HomotopyGroup (Fin j) B (p e₀))) :
    Subsingleton (HomotopyGroup (Fin J) E e₀) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, J = m + 2 := ⟨J - 2, by omega⟩
  have hex := Work.StemsB.les_exact_E p e₀
    (fun k => Work.StemsB.exists_lift_rel p
      (Work.StemsB.IsHurewiczFibration.isSerreFibration hp) k) m
  have hmod : Subsingleton (HomotopyGroup (Fin (m + 2)) B (p e₀)) :=
    hmodel (m + 2) (by omega) (by omega)
  have hfib : Subsingleton (HomotopyGroup (Fin (m + 2)) (↥(p ⁻¹' {p e₀}))
      (Work.StemsB.fibrePoint p e₀)) := hconn (m + 2) (by omega)
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, hx⟩ := (hex a).mp (hmod.elim _ _)
  obtain ⟨y, hy⟩ := (hex b).mp (hmod.elim _ _)
  rw [← hx, ← hy]
  exact congrArg _ (hfib.elim x y)

/-- **`π_J E` is trivial at every point of the fibre over `p e₀`**, for `2 ≤ J ≤ k-1`.

The fibre is path connected by `joined_fibre_of_subsingleton`; reversing the path gives a path in `E`
from `e₀` to `x.1` (the reversal is `γ (unitInterval.symm ·)`), and triviality transfers along it to
`subsingleton_pi_E_basepoint`. -/
theorem subsingleton_pi_E_of_mem_fibre (p : C(E, B)) (hp : Work.StemsB.IsHurewiczFibration p)
    (e₀ : E) (k : ℕ) (m : ℕ) (hm : m + 2 ≤ k - 1)
    (hconn : ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j) (↥(p ⁻¹' {p e₀})) ⟨e₀, rfl⟩))
    (hmodel : ∀ j : ℕ, j ≤ 2 * k - 1 → j ≠ k →
      Subsingleton (HomotopyGroup (Fin j) B (p e₀)))
    (x : ↥(p ⁻¹' {p e₀})) :
    Subsingleton (HomotopyGroup (Fin (m + 2)) E x.1) := by
  obtain ⟨γ⟩ := joined_fibre_of_subsingleton p e₀ (hconn 0 (by omega)) x
  have hγ : Path e₀ x.1 :=
    ⟨⟨fun t => (γ (unitInterval.symm t)).1,
        continuous_subtype_val.comp (γ.continuous.comp unitInterval.continuous_symm)⟩, by
      show (γ (unitInterval.symm 0)).1 = e₀
      rw [unitInterval.symm_zero]
      exact congrArg Subtype.val γ.target,
      by
      show (γ (unitInterval.symm 1)).1 = x.1
      rw [unitInterval.symm_one]
      exact congrArg Subtype.val γ.source⟩
  exact Work.Stems.subsingleton_homotopyGroup_change_basepoint (N := Fin (m + 2)) hγ
    (subsingleton_pi_E_basepoint p hp e₀ k (m + 2) (by omega) hm hconn hmodel)

end

end Work.RatHurewicz
