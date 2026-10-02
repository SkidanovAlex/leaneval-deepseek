import Mathlib
import Submission.Work.Stems.stableStemsTorsion_of_stable3
import Submission.Work.RatHurewicz.SphereSuspDefs
import Submission.Work.RatHurewicz.homotopyExcision
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.StemsB.pi_contractible
import Submission.Work.StemsB.basepoint_transport

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Auxiliary lemmas for Freudenthal's suspension theorem

This module collects the lemmas used by `Work.RatHurewicz.freudenthalTorsionTransfer`.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

/-- The upper thickened hemisphere is open. -/
theorem isOpen_upperHem (n : ℕ) : IsOpen (upperHem n) :=
  isOpen_lt continuous_const
    ((continuous_lastC (n + 1)).comp continuous_subtype_val)

/-- The lower thickened hemisphere is open. -/
theorem isOpen_lowerHem (n : ℕ) : IsOpen (lowerHem n) :=
  isOpen_lt ((continuous_lastC (n + 1)).comp continuous_subtype_val) continuous_const

/-- The two thickened hemispheres cover the sphere. -/
theorem upperHem_union_lowerHem (n : ℕ) : upperHem n ∪ lowerHem n = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  rcases lt_or_ge (-(1 / 2 : ℝ)) (lastC (n + 1) x) with h | h
  · exact Or.inl h
  · exact Or.inr (lt_of_le_of_lt h (by norm_num))

/-- **A section is surjective on homotopy groups.**  If `incl` is a continuous section of `proj`
(`proj (incl y) = y`), then `πmap proj` is surjective (up to the transport of the base point). -/
theorem piMap_surjective_of_section {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (incl : ContinuousMap X Y) (proj : ContinuousMap Y X) (h : ∀ y : X, proj (incl y) = y)
    (m : ℕ) (x : X) :
    Function.Surjective (Work.StemsB.πmap proj m (incl x)) := by
  intro a
  have hcomp : proj.comp incl = ContinuousMap.id X := ContinuousMap.ext h
  have key := Work.StemsB.πmap_congr (f := proj.comp incl) (g := ContinuousMap.id X) hcomp m x
    (Work.StemsB.homotopyGroupCast (h x) m a)
  rw [Work.StemsB.πmap_id_apply] at key
  rw [show congrArg (fun k : C(X, X) => k x) hcomp = h x from Subsingleton.elim _ _] at key
  refine ⟨Work.StemsB.πmap incl m x (Work.StemsB.homotopyGroupCast (h x) m a), ?_⟩
  rw [← Work.StemsB.πmap_comp_apply incl proj m x]
  exact (Work.StemsB.homotopyGroupCast (h x) m).injective key

/-- **A space with a point and a connector is contractible.** -/
theorem contractibleSpace_of_connector {Y : Type*} [TopologicalSpace Y] (hc : Connector Y)
    (y₀ : Y) : ContractibleSpace Y := by
  rw [contractible_iff_id_nullhomotopic]
  have H : ContinuousMap.Homotopy (ContinuousMap.const Y y₀) (ContinuousMap.id Y) :=
    { toContinuousMap := ⟨fun p : I × Y => hc.c (y₀, p.2, p.1),
        hc.c.continuous.comp (continuous_const.prodMk
          (continuous_snd.prodMk continuous_fst))⟩
      map_zero_left := fun x => hc.zero y₀ x
      map_one_left := fun x => hc.one y₀ x }
  exact ⟨y₀, ⟨H.symm⟩⟩

/-- **The two degenerate consequences of the long exact sequence of a pair** (see
`Work.RatHurewicz.freudenthalTorsionTransfer` for the use). -/
theorem pairLES_surjective {X : Type} [TopologicalSpace X] {A : Type} [TopologicalSpace A]
    (i : ContinuousMap A X) (a₀ : A) (k : ℕ) (hk : 1 ≤ k)
    (hA : Subsingleton (HomotopyGroup (Fin (k + 1)) A a₀))
    (hX : Subsingleton (HomotopyGroup (Fin (k + 2)) X (i a₀))) :
    (∃ d : HomotopyGroup (Fin (k + 2)) X (i a₀) →*
        RelHomotopyGroup i a₀ (k + 1), Function.Surjective d) ∧
      Function.Surjective (Work.StemsB.πmap (homotopyFibreFst i a₀) (k + 1)
        (homotopyFibreBasepoint i a₀)) := by
  obtain ⟨del, d, h1, h2, h3, h4⟩ := pair_les i a₀ k hk
  refine ⟨⟨d, ?_⟩, ?_⟩
  · intro y
    have hy : Work.StemsB.πmap (homotopyFibreFst i a₀) k
        (homotopyFibreBasepoint i a₀) y = 1 := hA.elim _ 1
    obtain ⟨x, hx⟩ := (h4 y).mp hy
    exact ⟨x, hx⟩
  · intro y
    have hy : Work.StemsB.πmap i (k + 1) a₀ y = 1 := hX.elim _ 1
    obtain ⟨x, hx⟩ := (h2 y).mp hy
    exact ⟨x, hx⟩

end

end Work.RatHurewicz
