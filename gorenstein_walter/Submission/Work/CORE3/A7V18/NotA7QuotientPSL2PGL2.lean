import Mathlib
import Submission.Work.ASM.Defs
import Submission.Work.CORE3.MData.NoA7SectionPSL2
import Submission.Work.DSTR.layerShape
import Submission.Work.A7.Defs
import Submission.Work.CORE3.A7V18.Prelim
import Submission.Work.CORE3.A7V18.CommutatorIsoPSL2
import Submission.Work.CORE3.A7V18.QuotientCenterIsoPSL2

/-!
# CORE3 / A7V18: no `A₇`-quotient quasisimple subgroup above a normal `PSL₂(q)` / `PGL₂(q)`

Deliverable `Work.CORE3.A7V18.NotA7QuotientPSL2PGL2`.

Let `Q` be a finite group, `L ◁ Q` a normal subgroup of **odd index** isomorphic to
`PSL(2, p^k)` or to `PGL(2, p^k)`, with `p` an odd prime and `p^k ≥ 5`, and let `E ≤ Q` be
quasisimple (`⁅E,E⁆ = E` and `E/Z(E)` simple) with `E/Z(E) ≅ A₇`.  Then `Q` is impossible.

The proof has three mathematical inputs.

1. **`E ≤ L`.**  `Q/L` has odd order (`Odd L.index` and `Subgroup.index_eq_card`), so by the
   odd order theorem (`hFT`) it is solvable.  The image of the perfect group `E` in the solvable
   group `Q ⧸ L` is perfect and solvable, hence trivial
   (`Work.CORE3.A7V18.le_ker_of_isSolvable_of_perfect`, a formalisation of
   `Group.IsPerfect.not_isSolvable`).  Thus `E ≤ L`.

2. **The `PSL₂` case.**  If `L ≅ PSL(2,q)`, then `L/Z(L) ≅ PSL(2,q)`
   (`Work.CORE3.A7V18.QuotientCenterIsoPSL2`: `PSL(2,q)` is simple, hence has trivial centre),
   and `Work.CORE3.MData.NoA7SectionPSL2` gives the contradiction.

3. **The `PGL₂` case.**  If `L ≅ PGL(2,q)`, then `⁅L,L⁆ ≅ ⁅PGL₂(q), PGL₂(q)⁆ = L₂(q) ≅ PSL(2,q)`
   (`Work.CORE3.A7V18.commutator_top_eq_Lsub`: `L₂(q) ⊴ PGL₂(q)` has index `2`, so contains the
   commutator subgroup, and is perfect so is contained in it), and `E = ⁅E,E⁆ ≤ ⁅L,L⁆`.  The
   quotient `⁅L,L⁆ ◁ Q` is normal in `Q` (commutator of a normal subgroup), so part 2 applies.
-/

open scoped MatrixGroups

namespace Work.CORE3.A7V18

/-- **`Q` has no quasisimple `A₇`-quotient above a normal `PSL₂`- or `PGL₂`-subgroup of odd
index.**  (Gorenstein–Walter, 1965: the `A₇` configuration is incompatible with the `L₂(q)`
layer of a group with dihedral Sylow 2-subgroups.) -/
theorem NotA7QuotientPSL2PGL2 {Q : Type} [Group Q] [Finite Q] (hFT : Work.GW2.FeitThompsonProp) (L : Subgroup Q) (hLn : L.Normal) (hLodd : Odd L.index) (p k : ℕ) [Fact p.Prime] (hpodd : Odd p) (hq : 5 ≤ p ^ k) (hLiso : Nonempty (L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) ∨ Nonempty (L ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k))) (E : Subgroup Q) (hEq : Work.GW2.IsQuasisimple E) (hA7 : Nonempty ((↥E ⧸ Subgroup.center ↥E) ≃* alternatingGroup (Fin 7))) : False := by
  -- Step 1: `Q ⧸ L` has odd order, hence is solvable by Feit–Thompson; `E` is perfect with
  -- trivial image there, so `E ≤ L`.
  have hodd : Odd (Nat.card (Q ⧸ L)) := by rw [← Subgroup.index_eq_card]; exact hLodd
  have hsol : Group.IsSolvable (Q ⧸ L) := hFT (Q ⧸ L) hodd
  have hEL : E ≤ L := by
    have h := le_ker_of_isSolvable_of_perfect (QuotientGroup.mk' L) hsol E hEq.1
    rwa [QuotientGroup.ker_mk' L] at h
  rcases hLiso with hpsl | hpgl
  · -- Case `L ≅ PSL(2, q)`.
    obtain ⟨e⟩ := hpsl
    have hq' : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :=
      QuotientCenterIsoPSL2 p k hq ⟨e⟩
    exact Work.CORE3.MData.NoA7SectionPSL2 p k hpodd hq Q L hLn hq' E hEq hEL hA7
  · -- Case `L ≅ PGL(2, q)`: `⁅L,L⁆ ≅ PSL(2,q)` is normal in `Q` and contains `E`.
    obtain ⟨e⟩ := hpgl
    have hL0n : (⁅L, L⁆ : Subgroup Q).Normal :=
      Subgroup.commutator_normal L L (h₁ := hLn) (h₂ := hLn)
    have hE0 : E ≤ ⁅L, L⁆ := by
      rw [← hEq.1]
      exact Subgroup.commutator_mono hEL hEL
    have hiso : Nonempty (↥(⁅L, L⁆ : Subgroup Q) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :=
      CommutatorIsoPSL2 L p k hpodd hq ⟨e⟩
    have hq' : Nonempty ((↥(⁅L, L⁆ : Subgroup Q) ⧸
        Subgroup.center ↥(⁅L, L⁆ : Subgroup Q)) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :=
      QuotientCenterIsoPSL2 p k hq hiso
    exact Work.CORE3.MData.NoA7SectionPSL2 p k hpodd hq Q ⁅L, L⁆ hL0n hq' E hEq hE0 hA7

end Work.CORE3.A7V18
