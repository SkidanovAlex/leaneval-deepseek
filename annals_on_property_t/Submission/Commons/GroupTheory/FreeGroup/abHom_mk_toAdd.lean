import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.GroupTheory.FreeGroup.Basic

namespace Commons.GroupTheory.FreeGroup

/-- The abelianisation of `FreeGroup (Fin n)` onto `Multiplicative (Fin n → ℤ)`,
sending the `j`-th standard generator to the `j`-th coordinate vector. -/
noncomputable def abHom (n : ℕ) : FreeGroup (Fin n) →* Multiplicative (Fin n → ℤ) :=
  FreeGroup.lift (fun j : Fin n => Multiplicative.ofAdd (Pi.single j 1))

/-- A coordinate of a product in `Multiplicative` is the sum of the coordinates. -/
theorem toAdd_prod_apply {n : ℕ} (u : Fin n) (l : List (Multiplicative (Fin n → ℤ))) :
    (l.prod).toAdd u = (l.map (fun y => y.toAdd u)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.prod_cons, toAdd_mul, Pi.add_apply, ih, List.map_cons, List.sum_cons]

/-- **Exponent sums along a word.**  For a word `L` over `Fin n × Bool` (with
`(j, true) = a_j` and `(j, false) = a_j⁻¹`) and a coordinate `u`, the `u`-th
coordinate of the abelianisation of `FreeGroup.mk L` is the sum of `±1` over
the letters of `L` whose generator part is `u`. -/
theorem abHom_mk_toAdd (n : ℕ) (u : Fin n) (L : List (Fin n × Bool)) :
    (abHom n (FreeGroup.mk L)).toAdd u
      = (L.map (fun l => if l.1 = u then (if l.2 then (1 : ℤ) else -1) else 0)).sum := by
  rw [abHom, FreeGroup.lift_mk]
  rw [toAdd_prod_apply]
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro x _
  obtain ⟨j, b⟩ := x
  cases b <;> simp [Pi.single_apply, neg_ite, @eq_comm _ j u]

end Commons.GroupTheory.FreeGroup