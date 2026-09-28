import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.lam_basic
import Submission.Work.HP.rk_le_card
import Submission.Work.HP.phiOf_injective
import Submission.Work.HP.Sig2.Recursion

/-!
# Schmidt's bound for lattice points in a ball (`Work.HP.Sig2.schmidt_bound`)

For every sublattice `L ⊆ ℤ^ι` and every `T ≥ 1`,

`#(L ∩ B(T)) ≤ K(ι) · ∏_{i=1}^{rk L} (T / λ_i(L) + 1)`,

where `λ_1 ≤ λ_2 ≤ ⋯` are the successive minima of `L` for the Euclidean unit ball and the
constant `K(ι)` depends only on the ambient type `ι`.

The proof transports `L` to its coefficient presentation `phiOf (vb b)` for a `ℤ`-basis `b` of `L`
(this identifies `ballCount L` with `latCount` and `lam L i` with `latMin`), applies the rank
induction `Work.HP.Sig2Rec.recursion_count` in coefficient space, and enlarges the induction
constant to one depending only on `Fintype.card ι` using `rk_le_card`.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP.Sig2

open Work.HP.Sig2Rec

theorem schmidt_bound {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (T : ℝ), 1 ≤ T →
      (ballCount L T : ℝ) ≤ K * ∏ i ∈ Finset.range (rk L), (T / lam L (i + 1) + 1) := by
  classical
  refine ⟨Kcb (Fintype.card ι), Kcb_pos _, ?_⟩
  intro L T hT
  obtain ⟨n, b0⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ι) L
  have hn : n = Work.HP.rk L := by
    show n = Module.finrank ℤ L
    rw [Module.finrank_eq_card_basis b0, Fintype.card_fin]
  let b : Module.Basis (Fin (Work.HP.rk L)) ℤ L := b0.reindex (finCongr hn)
  have hv : LinearIndependent ℤ (vb (L := L) b) :=
    b.linearIndependent.map' (Submodule.subtype L) (LinearMap.ker_eq_bot.mpr Subtype.coe_injective)
  have hΦ : Function.Injective (phiOf (vb (L := L) b)) := phiOf_injective _ hv
  have hbound := recursion_count (Work.HP.rk L) (phiOf (vb (L := L) b)) hΦ T hT
  have hbc : (ballCount L T : ℝ) = (latCount (phiOf (vb (L := L) b)) T : ℝ) := by
    rw [ballCount_eq_latCount b T]
  rw [hbc]
  have hLprod : ∏ i ∈ Finset.range (Work.HP.rk L), (T / lam L (i + 1) + 1)
      = ∏ i ∈ Finset.range (Work.HP.rk L),
          (T / latMin (phiOf (vb (L := L) b)) (i + 1) + 1) := by
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [lam_eq_latMin b (i + 1)]
  rw [hLprod]
  calc (latCount (phiOf (vb (L := L) b)) T : ℝ)
      ≤ Kcb (Work.HP.rk L) * ∏ i ∈ Finset.range (Work.HP.rk L),
          (T / latMin (phiOf (vb (L := L) b)) (i + 1) + 1) := hbound
    _ ≤ Kcb (Fintype.card ι) * ∏ i ∈ Finset.range (Work.HP.rk L),
          (T / latMin (phiOf (vb (L := L) b)) (i + 1) + 1) := by
        refine mul_le_mul_of_nonneg_right (Kcb_mono (rk_le_card L)) ?_
        exact Finset.prod_nonneg (fun i hi => by
          have hi' : i < Work.HP.rk L := Finset.mem_range.mp hi
          have hpos : 0 < latMin (phiOf (vb (L := L) b)) (i + 1) :=
            latMin_pos _ hΦ (by omega) (by omega)
          exact add_nonneg (div_nonneg (by linarith) hpos.le) zero_le_one)

end Work.HP.Sig2
