import Submission.Work.Stems.HomAdd.assemblyNull
import Submission.Work.RatHurewicz.psiDefs
import Submission.Work.RatHurewicz.PsiKillsAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Hutchings' `(2.5)`: `Psi` kills boundaries

This is the second geometric brick of the elementary (cubical) proof of the Hurewicz isomorphism
theorem -- blueprint step **S1** of `Submission/Work/Drive/SERRE_BLUEPRINT.md`
(`Work.RatHurewicz.hurewiczKerTorsionFirstDegree`, on which the rational Hurewicz statement in the
stable range, and hence the drive's contract and this area's target, ultimately rest).

For the based-ification `Psi N m K hN` of `Work.RatHurewicz.psiDefs`, and every `(m+3)`-cube `τ`,
the alternating product of the classes of the based-ifications of the faces of `τ` is `1`.  This is
`Work.RatHurewicz.Psi_kills_boundary` (`Submission/Work/RatHurewicz/Psi_kills_boundary.lean`),
proved here from the ingredients that are now available:

* `Work.RatHurewicz.assembly_class` — the class of the assembly of the layers is the alternating
  product of the classes of the pieces, and
* `Work.Stems.HomAdd.assemblyNull` — the assembly is null-homotopic (the geometric core, proved
  from the general cubical homotopy-addition statement `Work.RatHurewicz.PinchAll`).

The two versions (this file and the RATHUREWICZ file just quoted) have the same statement; the
RATHUREWICZ `Psi_kills_boundary` still quotes `assembly_null`, whose only `sorry` this module
closes, so it can be replaced by the one line

```
theorem Psi_kills_boundary ... := Work.Stems.HomAdd.PsiKillsBoundary ...
```
-/

open scoped unitInterval Topology
open Work.Stems.Cubical
open Work.RatHurewicz

namespace Work.Stems.HomAdd

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- **Hutchings (2.5)**: for every `(m+3)`-cube `τ`, the alternating product of the classes of the
based-ifications of its faces is trivial. -/
theorem PsiKillsBoundary (N m : ℕ) {x₀ : X} (K : Tower x₀ N) (hN : m + 1 ≤ N)
    [Nontrivial (Fin (m + 2))] (τ : C(IC (m + 3), X)) :
    (∏ i : Fin (m + 3), ∏ b : Fin 2,
      ((show HomotopyGroup (Fin (m + 2)) X x₀ from
        Quotient.mk _ (Psi N m K hN (τ.comp (faceCM i (cval b))))) :
          HomotopyGroup (Fin (m + 2)) X x₀) ^ ((-1 : ℤ) ^ ((i : ℕ) + (b : ℕ)))) = 1 := by
  have hclass := assembly_class N m K hN τ
  have hnull : cl (m + 2) X x₀ (assembly N m K hN τ) = 1 := by
    have h : (⟦assembly N m K hN τ⟧ :
        Quotient (GenLoop.Homotopic.setoid (Fin (m + 2)) x₀)) = ⟦GenLoop.const⟧ :=
      Quotient.sound (assemblyNull N m K hN τ)
    exact h
  have hprod : (∏ i : Fin (m + 3), ∏ b : Fin 2,
      ((show HomotopyGroup (Fin (m + 2)) X x₀ from
        Quotient.mk _ (Psi N m K hN (τ.comp (faceCM i (cval b))))) :
          HomotopyGroup (Fin (m + 2)) X x₀) ^ ((-1 : ℤ) ^ ((i : ℕ) + (b : ℕ))))
      = ∏ i : Fin (m + 3), ∏ b : Fin 2,
          (cl (m + 2) X x₀ (piece N m K hN τ (i, b))) ^ (esign m i b) := by
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun b _ => ?_
    rfl
  rw [hprod, ← hclass, hnull]

/-- **The packaged form** (`Work.RatHurewicz.psiKillsBoundary`): for `n ≥ 2` and a filling family
up to level `N ≥ n - 1` there is a based-ification `Ψ : C(Iⁿ,X) → GenLoop (Fin n) X x₀` that is the
identity on based cubes, sends the constant cube to the constant loop, and kills the boundary of
every `(n+1)`-cube. -/
theorem psiKillsBoundary (n : ℕ) (hn : 2 ≤ n) [Nontrivial (Fin n)] (N : ℕ) (hN : n - 1 ≤ N)
    {x₀ : X} (K : Tower x₀ N) :
    ∃ Ψ : C(IC n, X) → GenLoop (Fin n) X x₀,
      (∀ p : GenLoop (Fin n) X x₀, GenLoop.Homotopic (Ψ p.1) p) ∧
      Ψ (cconst n x₀) = GenLoop.const ∧
      (∀ τ : C(IC (n + 1), X),
        (∏ i : Fin (n + 1), ∏ b : Fin 2,
          ((show HomotopyGroup (Fin n) X x₀ from
            Quotient.mk _ (Ψ (τ.comp (faceCM i (cval b))))) :
              HomotopyGroup (Fin n) X x₀) ^ ((-1 : ℤ) ^ ((i : ℕ) + (b : ℕ)))) = 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hN' : m + 1 ≤ N := by omega
  exact ⟨Psi N m K hN', fun p => Psi_section N m K hN' p, Psi_const N m K hN',
    fun τ => PsiKillsBoundary N m K hN' τ⟩

end

end Work.Stems.HomAdd
