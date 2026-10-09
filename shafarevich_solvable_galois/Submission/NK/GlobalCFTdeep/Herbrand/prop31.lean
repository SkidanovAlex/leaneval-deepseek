import Mathlib
import Submission.NK.GlobalCFTdeep.Shared
import Submission.NK.GlobalCFTdeep.Herbrand.LogDefs
import Submission.NK.GlobalCFTdeep.Herbrand.StableRep
import Submission.NK.GlobalCFTdeep.Herbrand.DescentSetup
import Submission.NK.GlobalCFTdeep.LogLattice.LogLatticeMain
import Submission.NK.GlobalCFTdeep.LogLattice.logVec_smul_apply
import Submission.NK.GlobalCFTdeep.LogLattice.sum_logVec_eq_zero
import Submission.NK.GlobalCFTdeep.LogLattice.finite_ker_logVecLin
import Submission.NK.GlobalCFTdeep.LogLattice.span_logVecLin_oneVec
import Submission.NK.GlobalCFTdeep.LogLattice.finrank_lattices
import Submission.NK.GlobalCFTdeep.LogLattice.herbrandEq_divisorLatticeRep_iff
import Submission.NK.GlobalCFTdeep.LogLattice.herbrandEq_iff_of_span_eq_top
import Submission.NK.GlobalCFTdeep.LogLattice.hZero_mul_hOne_logLattice
import Submission.NK.GlobalCFTdeep.LogLattice.hZero_mul_hOne_unitLattice
import Submission.NK.GlobalCFTdeep.PlacePerm.herbrandEq_placeFunRep
import Submission.NK.GlobalCFTdeep.Herbrand.finite_tateCohomology_of_moduleFinite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFT

/-! ## The arithmetic core of Milne's Proposition 3.1

Given the two relations

* `h(U(T)) = h(M')`        (`hZero U * hOne M' = hZero M' * hOne U`),
* `h(M) = n · h(M')`       (`hZero M * hOne M' = n * hZero M' * hOne M`),

together with `h(M) = P` (`hZero M = P * hOne M`, i.e. `HerbrandEq M P`), where `M = M' + ℤ·e`,
the `S`-unit computation `n · h(U(T)) = P` follows by cancellation. -/

/-- **The numerical heart of Milne, *CFT*, Proposition 3.1.** -/
theorem prop31_arith {n P A B C D E F : ℕ}
    (hi : A * D = C * B) (hii : E * D = n * C * F) (hiii : E = P * F)
    (hD : 0 < D) (hF : 0 < F) : n * A = P * B := by
  have key : P * D = n * C := by
    have h := hii
    rw [hiii] at h
    have h2 : (P * D) * F = (n * C) * F := by
      rw [← h]
      ring
    exact Nat.mul_right_cancel hF h2
  have h3 : (n * A) * D = (P * B) * D := by
    calc (n * A) * D = n * (A * D) := by ring
      _ = n * (C * B) := by rw [hi]
      _ = (n * C) * B := by ring
      _ = (P * D) * B := by rw [key]
      _ = (P * B) * D := by ring
  exact Nat.mul_right_cancel hD h3

end NK.GlobalCFTdeep.Herbrand

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFT

/-- **Milne, *Class Field Theory*, Proposition 3.1** (the `S`-unit computation): for a cyclic
extension `L/K`, a finite set `S` of places of `K` containing all infinite places and `T` the set
of places of `L` above `S`,

  `[L:K] · h(U(T)) = (∏_{v ∈ S} [L_w : K_v])`,

in the cross-multiplied `Nat.card` form `n · hZero U = P · hOne U`.

The proof assembles the pieces of the `LogLattice` chapter:

* `HerbrandEq (placeFunRep T hT) P` — the permutation module `Hom(T, ℤ)` has Herbrand quotient the
  product of the local degrees (`PlacePerm/herbrandEq_placeFunRep`);
* `HerbrandEq (divisorLatticeRep T hT) P` — the divisor lattice inside `∏_{w ∈ T} ℝ`
  (`LogLattice/herbrandEq_divisorLatticeRep_iff`);
* `HerbrandEq (unitLatticeRep T hT) P` — Milne's lattice `M = M' + ℤ·e`, by the comparison of two
  full lattices in the same real representation
  (`LogLattice/herbrandEq_iff_of_span_eq_top`, which uses the descent
  `Herbrand/Descent/exists_det_ne_zero_of_map_solution` and the ranks
  `LogLattice/finrank_lattices`);
* the two relations `h(U(T)) = h(M')` and `h(M) = n·h(M')`
  (`LogLattice/hZero_mul_hOne_logLattice`, `LogLattice/hZero_mul_hOne_unitLattice`);
* the cancellation `prop31_arith`. -/
theorem prop31 {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (S : Finset (NK.GlobalCFT.Place K)) (T : Set (NK.GlobalCFT.Place L)) [Finite T]
    (hTinf : ∀ w : NK.GlobalCFT.Place L, w.IsInfinite → w ∈ T)
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : NK.GlobalCFT.Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : NK.GlobalCFT.Place L, w ∈ T ↔ ∃ v ∈ S, NK.GlobalCFT.Place.LiesOver w v)
    (w : (v : NK.GlobalCFT.Place K) → v ∈ S → NK.GlobalCFT.Place L)
    (hw : ∀ (v : NK.GlobalCFT.Place K) (hv : v ∈ S),
      NK.GlobalCFT.Place.LiesOver (w v hv) v) :
    Nat.card (L ≃ₐ[K] L) * NK.GlobalCFTdeep.hZero (NK.GlobalCFTdeep.tUnitsRep (L := L) T hT)
      = (Finset.prod S.attach (fun v => Nat.card
          (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) (w v.1 v.2))))
        * NK.GlobalCFTdeep.hOne (NK.GlobalCFTdeep.tUnitsRep (L := L) T hT) := by
  classical
  haveI : Fintype ↥T := Fintype.ofFinite _
  set P : ℕ := Finset.prod S.attach (fun v => Nat.card
    (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) (w v.1 v.2))) with hP
  -- the permutation module side (Milne's Proposition 2.7 bookkeeping)
  have hperm : HerbrandEq (placeFunRep (L := L) T hT) P :=
    NK.GlobalCFTdeep.PlacePerm.herbrandEq_placeFunRep (K := K) (L := L) S T hT hTS w hw
  -- the divisor lattice
  have hdiv : HerbrandEq (divisorLatticeRep (L := L) T hT) P :=
    (NK.GlobalCFTdeep.LogLattice.herbrandEq_divisorLatticeRep_iff (L := L) T hT P).mpr hperm
  -- finiteness of the two lattices
  haveI hfinLog : Module.Finite ℤ ↥(logLattice T) := finite_logLattice T hTinf
  haveI hfreeLog : Module.Free ℤ ↥(logLattice T) := free_logLattice T hTinf
  haveI hfinUnit : Module.Finite ℤ ↥(unitLattice T) := finite_unitLattice T hTinf
  haveI hfreeUnit : Module.Free ℤ ↥(unitLattice T) := free_unitLattice T hTinf
  haveI hfinDiv : Module.Finite ℤ ↥(divisorLattice T) := finite_divisorLattice T
  haveI hfreeDiv : Module.Free ℤ ↥(divisorLattice T) := free_divisorLattice T
  obtain ⟨hrankLog, hrankUnit, hrankDiv⟩ := NK.GlobalCFTdeep.LogLattice.finrank_lattices (K := K) (L := L) T hTinf
  -- the comparison of the two full lattices in `↥T → ℝ`
  have hspanUnit : Submodule.span ℝ ((unitLattice T : Set (↥T → ℝ))) = ⊤ := by
    rw [eq_top_iff, ← NK.GlobalCFTdeep.LogLattice.span_logVecLin_oneVec (K := K) (L := L) T hTinf]
    refine Submodule.span_le.2 ?_
    rintro x (hx | hx)
    · obtain ⟨a, rfl⟩ := hx
      exact Submodule.subset_span (logLattice_le_unitLattice T (mem_logLattice.mpr ⟨a, rfl⟩))
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact Submodule.subset_span (oneVec_mem_unitLattice T)
  have hspanDiv : Submodule.span ℝ ((divisorLattice T : Set (↥T → ℝ))) = ⊤ :=
    span_divisorLattice T
  letI := permAction T hT ℝ
  haveI : SMulCommClass (L ≃ₐ[K] L) ℝ (↥T → ℝ) :=
    ⟨fun g c f => by funext w; rfl⟩
  have hcmp : HerbrandEq (unitLatticeRep (L := L) T hT) P ↔
      HerbrandEq (divisorLatticeRep (L := L) T hT) P :=
    NK.GlobalCFTdeep.LogLattice.herbrandEq_iff_of_span_eq_top (G := L ≃ₐ[K] L) (V := ↥T → ℝ)
      (unitLattice T) (divisorLattice T)
      (fun g x hx => smul_mem_unitLattice T hT g hx)
      (fun g x hx => smul_mem_divisorLattice T hT g hx)
      hspanUnit hspanDiv hrankUnit hrankDiv P
  have hM : HerbrandEq (unitLatticeRep (L := L) T hT) P := hcmp.mpr hdiv
  -- the two exact-sequence relations
  have hi := NK.GlobalCFTdeep.LogLattice.hZero_mul_hOne_logLattice (K := K) (L := L) T hT hTinf
  have hii := NK.GlobalCFTdeep.LogLattice.hZero_mul_hOne_unitLattice (K := K) (L := L) T hT hTinf
  -- positivity of the two `hOne`
  haveI hfL : Module.Finite ℤ (logLatticeRep (L := L) T hT).V := finite_logLattice T hTinf
  haveI hfU : Module.Finite ℤ (unitLatticeRep (L := L) T hT).V := finite_unitLattice T hTinf
  haveI : Finite ↥(tateCohomology (logLatticeRep (L := L) T hT) 1) :=
    (finite_tateCohomology_of_moduleFinite (logLatticeRep (L := L) T hT)).2
  haveI : Finite ↥(tateCohomology (unitLatticeRep (L := L) T hT) 1) :=
    (finite_tateCohomology_of_moduleFinite (unitLatticeRep (L := L) T hT)).2
  have hD : 0 < hOne (logLatticeRep (L := L) T hT) := by
    haveI : Nonempty ↥(tateCohomology (logLatticeRep (L := L) T hT) 1) := ⟨0⟩
    rw [hOne_def]
    exact Nat.card_pos
  have hF : 0 < hOne (unitLatticeRep (L := L) T hT) := by
    haveI : Nonempty ↥(tateCohomology (unitLatticeRep (L := L) T hT) 1) := ⟨0⟩
    rw [hOne_def]
    exact Nat.card_pos
  exact prop31_arith (n := Nat.card (L ≃ₐ[K] L)) (P := P)
    (A := hZero (tUnitsRep (L := L) T hT)) (B := hOne (tUnitsRep (L := L) T hT))
    (C := hZero (logLatticeRep (L := L) T hT)) (D := hOne (logLatticeRep (L := L) T hT))
    (E := hZero (unitLatticeRep (L := L) T hT)) (F := hOne (unitLatticeRep (L := L) T hT))
    hi hii hM hD hF

end NK.GlobalCFTdeep.Herbrand
