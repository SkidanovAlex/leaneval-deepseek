import Mathlib
import Submission.Work.RatHurewicz.cubicalBridgeDeg
import Submission.Work.RatHurewicz.fillingFamilyConst
import Submission.Work.RatHurewicz.cubD_comp_cubD
import Submission.Work.Stems.Hur2c.PsiLinGen
import Submission.Work.Stems.Hur2c.PsiLinGenCubD
import Submission.Work.Stems.Hur2c.BasedCubeCycle
import Submission.Work.Stems.HurewiczNeutral

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The first-degree Hurewicz lemma modulo torsion, reduced to the crux `DegenCycleKilled`

`Work.RatHurewicz.hurewiczKerTorsionFirstDegree` (the target of the area RATHUREWICZ, step **S1**
of `Submission/Work/Drive/SERRE_BLUEPRINT.md`) is proved here from the single input

* **`DegenCycleKilled`** — `ΨLin` kills degenerate `(m+2)`-cycles: for `X` with `π_i(X,x₀) = 0` for
  `i < m+2`, a filling family `K : Tower x₀ N` with `N ≥ m+1` and a degenerate `(m+2)`-chain `d`
  (`d ∈ Deg (m+2) X`) which is a cycle (`cubD (m+1) X d = 0`) one has
  `psiLinGen N m K hN d = 0`.

Everything else is in place: the filling family (`fillingFamilyConst`), the based-ification `Ψ` and
its linearisation (`psiLinGen`, with `(Z) psiLinGen_single_based`), Hutchings' `(2.5)` in additive
form (`psiLinGen_cubD_eq_zero`), the chain-level bridge (`cubicalBridgeDeg`) and the fact that a
based cube is a cycle (`cubD_single_based`).

The mathematical content of `DegenCycleKilled` is `Submission/Work/Stems/PSI_DEG_NOTES.md`'s
statement (E): `Ψ` does *not* kill every degenerate cube (the naive statement is unprovable for an
arbitrary filling family), but it does kill degenerate *cycles*; the degree-`2` case is
`Work.Stems.Hur2c.PsiLin_eq_zero_of_degen_cycle`.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- **The crux.**  `ΨLin` kills degenerate `(m+2)`-cycles. -/
def DegenCycleKilled : Prop :=
  ∀ (N m : ℕ) [Nontrivial (Fin (m + 2))] (X : Type) [TopologicalSpace X] (x₀ : X),
    (∀ i : ℕ, i < m + 2 → Subsingleton (HomotopyGroup (Fin i) X x₀)) →
      ∀ (K : Tower x₀ N) (hN : m + 1 ≤ N) (d : Cub (m + 2) X),
        d ∈ Deg (m + 2) X → cubD (m + 1) X d = 0 →
          Work.Stems.Hur2c.psiLinGen N m K hN d = 0

/-- **The assembly.**  The crux implies the first-degree Hurewicz lemma modulo torsion: for `X`
with `π_i(X,x₀) = 0` for `i < m+1`, a class in `π_{m+1}` whose Hurewicz class vanishes is trivial
(a fortiori torsion). -/
theorem hurewiczKerTorsionFirstDegree_of_degenCycle (H : DegenCycleKilled) :
    ∀ (m : ℕ), 1 ≤ m → ∀ (X : Type) [TopologicalSpace X] (x₀ : X),
      (∀ i < m + 1, Subsingleton (HomotopyGroup (Fin i) X x₀)) →
        ∀ a : HomotopyGroup (Fin (m + 1)) X x₀,
          Work.Stems.hurewiczMapN (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) x₀ a = 0 →
            ∃ N : ℕ, 0 < N ∧ a ^ N = 1 := by
  intro m hm X _ x₀ hconn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  intro a ha
  haveI : Nontrivial (Fin (k + 2)) :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  letI : CommGroup (Quotient (GenLoop.Homotopic.setoid (Fin (k + 2)) x₀)) :=
    HomotopyGroup.commGroup
  -- the filling family at level `k+1`
  obtain ⟨Kf, hα, hβ, hγ⟩ :=
    fillingFamilyConst (k + 1) x₀ (fun i hi => hconn i (by omega))
  let K : Tower x₀ (k + 1) := ⟨Kf, hα, hβ, hγ⟩
  -- the linearised based-ification at level `k+2`
  set Ψ := Work.Stems.Hur2c.psiLinGen (k + 1) k K (le_refl (k + 1)) with hΨ
  -- a representative of the class
  set p : GenLoop (Fin (k + 2)) X x₀ :=
    Quotient.out (a : Quotient (GenLoop.Homotopic.setoid (Fin (k + 2)) x₀)) with hp
  have hp_eq : (Quotient.mk (GenLoop.Homotopic.setoid (Fin (k + 2)) x₀) p
      : HomotopyGroup (Fin (k + 2)) X x₀) = a := Quotient.out_eq _
  have hp : Work.Stems.hurewiczMapN (k + 2) (by omega) x₀
      (show HomotopyGroup (Fin (k + 2)) X x₀ from Quotient.mk _ p) = 0 := by
    rw [hp_eq]
    exact ha
  -- the chain-level bridge
  obtain ⟨c, hc | hc⟩ := cubicalBridgeDeg (k + 2) (by omega) x₀ p hp
  · -- `cubD (k+2) c - single p.1 1 ∈ Deg (k+2) X`
    have hd : cubD (k + 1) X (cubD (k + 2) X c - Finsupp.single p.1 1) = 0 := by
      rw [map_sub, cubD_comp_cubD (k + 1) c,
        Work.Stems.Hur2c.cubD_single_based (n := k + 1) x₀ p, sub_zero]
    have hE := H (k + 1) k X x₀ (fun i hi => hconn i (by omega)) K (le_refl (k + 1))
      (cubD (k + 2) X c - Finsupp.single p.1 1) hc hd
    have key : Ψ (Finsupp.single p.1 1) = 0 := by
      have hsplit : Finsupp.single p.1 1
          = cubD (k + 2) X c - (cubD (k + 2) X c - Finsupp.single p.1 1) :=
        (sub_sub_cancel _ _).symm
      rw [hsplit, map_sub, Work.Stems.Hur2c.psiLinGen_cubD_eq_zero (k + 1) k K (le_refl (k + 1)) c,
        hE, sub_zero]
    have hZ : Ψ (Finsupp.single p.1 1) = Additive.ofMul (⟦p⟧ : HomotopyGroup (Fin (k + 2)) X x₀) :=
      Work.Stems.Hur2c.psiLinGen_single_based (k + 1) k K (le_refl (k + 1)) p
    have hp1 : (Quotient.mk (GenLoop.Homotopic.setoid (Fin (k + 2)) x₀) p
        : HomotopyGroup (Fin (k + 2)) X x₀) = 1 := by
      have h0 : Additive.ofMul (⟦p⟧ : HomotopyGroup (Fin (k + 2)) X x₀) = 0 := hZ ▸ key
      simpa using h0
    have ha1 : a = 1 := hp_eq ▸ hp1
    exact ⟨1, one_pos, by rw [ha1, one_pow]⟩
  · -- `cubD (k+2) c + single p.1 1 ∈ Deg (k+2) X`
    have hd : cubD (k + 1) X (cubD (k + 2) X c + Finsupp.single p.1 1) = 0 := by
      rw [map_add, cubD_comp_cubD (k + 1) c,
        Work.Stems.Hur2c.cubD_single_based (n := k + 1) x₀ p, zero_add]
    have hE := H (k + 1) k X x₀ (fun i hi => hconn i (by omega)) K (le_refl (k + 1))
      (cubD (k + 2) X c + Finsupp.single p.1 1) hc hd
    have key : Ψ (Finsupp.single p.1 1) = 0 := by
      have hsplit : Finsupp.single p.1 1
          = (cubD (k + 2) X c + Finsupp.single p.1 1) - cubD (k + 2) X c := by
        rw [add_sub_cancel_left]
      rw [hsplit, map_sub, hE,
        Work.Stems.Hur2c.psiLinGen_cubD_eq_zero (k + 1) k K (le_refl (k + 1)) c]
      simp
    have hZ : Ψ (Finsupp.single p.1 1) = Additive.ofMul (⟦p⟧ : HomotopyGroup (Fin (k + 2)) X x₀) :=
      Work.Stems.Hur2c.psiLinGen_single_based (k + 1) k K (le_refl (k + 1)) p
    have hp1 : (Quotient.mk (GenLoop.Homotopic.setoid (Fin (k + 2)) x₀) p
        : HomotopyGroup (Fin (k + 2)) X x₀) = 1 := by
      have h0 : Additive.ofMul (⟦p⟧ : HomotopyGroup (Fin (k + 2)) X x₀) = 0 := hZ ▸ key
      simpa using h0
    have ha1 : a = 1 := hp_eq ▸ hp1
    exact ⟨1, one_pos, by rw [ha1, one_pow]⟩

end

end Work.RatHurewicz
