import Mathlib
import Submission.Work.Lattice.MaxEuclidData
import Submission.Work.Lattice.LatticePolygon

/-!
# The intrinsic max-norm rank data of a lattice, and its identification with the flow data

The paper's Grayson polygon is built with the **sup norm** `cnorm` on `⋀^j ℝᵈ`, and the §3 flow
data `FlowDataMax.flowMaxData Λ₀ ℓ t j` is the infimum of `log cnorm (⋀^j a_t(⋀v))` over
`ℝ`-independent families `v : Fin j → Λ₀`.  For the flag/Prop-5 layer (which lives on the
*subgroups* of a lattice) one needs the same quantity attached to a lattice alone:

* `maxRankDataSet Λ j` / `maxRankData Λ j` — the infimum of `log (cnorm (⋀^j v))` over
  `ℝ`-independent families `v : Fin j → Λ`; the rank-`0` case is `0` (`maxRankData_zero`);
* **`flowMaxDataSet_eq_maxRankDataSet`** / **`flowMaxData_eq_maxRankData`** — the identification of
  the flow data with the intrinsic max-norm data of the flowed lattice `a_t Λ₀`
  (`flowMaxData Λ₀ ℓ t j = maxRankData (Λ₀.map a_t) j`), proved from the injectivity of `a_t`
  (`FlowDataMax.eFlow_injective`) and `exteriorPower.map_apply_ιMulti`.

Module `Submission.Work.Lattice.MaxRankData`, namespace `Submission.MaxRankData`.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Submission.MaxRankData

open Submission.GraysonLattice
open Submission.GraysonData
open Submission.ExteriorCoordinates
open Submission.MaxNorm
open Submission.MaxNormFlow
open Submission.FlowDataMax
open Submission.DiagonalFlow

variable {d : ℕ}

/-- The intrinsic max-norm rank-`j` data set of a lattice `Λ ≤ ℝᵈ`: the `log cnorm` values of
the wedges of `ℝ`-independent families in `Λ`. -/
def maxRankDataSet {d : ℕ} (Λ : Submodule ℤ (E d)) (j : ℕ) (hjd : j ≤ d) : Set ℝ :=
  {r | ∃ v : Fin j → E d, (∀ i, v i ∈ Λ) ∧ LinearIndependent ℝ v ∧
    r = Real.log (cnorm hjd (exteriorPower.ιMulti ℝ j v))}

/-- The intrinsic max-norm rank-`j` data of `Λ`. -/
def maxRankData {d : ℕ} (Λ : Submodule ℤ (E d)) (j : ℕ) (hjd : j ≤ d) : ℝ :=
  sInf (maxRankDataSet Λ j hjd)

/-- **The identification of the flow data with the intrinsic data of the flowed lattice.** -/
theorem flowMaxDataSet_eq_maxRankDataSet {Λ₀ : Submodule ℤ (RD d)} (ℓ : ℕ) (t : ℝ) (j : ℕ)
    (hjd : j ≤ d) :
    flowMaxDataSet (d := d) Λ₀ ℓ t j hjd =
      maxRankDataSet (d := d) (Λ₀.map ((eFlow (d := d) ℓ t).restrictScalars ℤ)) j hjd := by
  ext r
  constructor
  · rintro ⟨v, hvmem, hvli, rfl⟩
    have hmem : ∀ i, eFlow (d := d) ℓ t (v i) ∈
        Λ₀.map ((eFlow (d := d) ℓ t).restrictScalars ℤ) := fun i =>
      Submodule.mem_map.mpr ⟨v i, hvmem i, rfl⟩
    have hli : LinearIndependent ℝ (fun i => eFlow (d := d) ℓ t (v i)) := by
      have hker : LinearMap.ker (eFlow (d := d) ℓ t) = ⊥ :=
        LinearMap.ker_eq_bot.mpr (eFlow_injective (d := d) ℓ t)
      have hmap := hvli.map' (eFlow (d := d) ℓ t) hker
      simpa [Function.comp_def] using hmap
    refine ⟨fun i => eFlow (d := d) ℓ t (v i), hmem, hli, ?_⟩
    rw [exteriorPower.map_apply_ιMulti]
    simp only [Function.comp_def]
  · rintro ⟨u, humem, huli, rfl⟩
    choose w hwmem hwu using fun i => Submodule.mem_map.mp (humem i)
    have hwli : LinearIndependent ℝ w := by
      refine LinearIndependent.of_comp (eFlow (d := d) ℓ t) ?_
      rw [show (⇑(eFlow (d := d) ℓ t) ∘ w) = fun i => eFlow (d := d) ℓ t (w i) from rfl,
        show (fun i => eFlow (d := d) ℓ t (w i)) = u from funext hwu]
      exact huli
    refine ⟨w, hwmem, hwli, ?_⟩
    rw [show u = fun i => eFlow (d := d) ℓ t (w i) from (funext hwu).symm,
      exteriorPower.map_apply_ιMulti]
    simp only [Function.comp_def]

/-- **The flow data is the intrinsic max-norm data of the flowed lattice.** -/
theorem flowMaxData_eq_maxRankData {Λ₀ : Submodule ℤ (RD d)} (ℓ : ℕ) (t : ℝ) (j : ℕ)
    (hjd : j ≤ d) :
    flowMaxData (d := d) Λ₀ ℓ t j hjd =
      maxRankData (d := d) (Λ₀.map ((eFlow (d := d) ℓ t).restrictScalars ℤ)) j hjd := by
  rw [flowMaxData, maxRankData, flowMaxDataSet_eq_maxRankDataSet]

/-- The sup norm of the wedge of the empty family is `1`. -/
lemma cnorm_iMulti_zero (d : ℕ) (v : Fin 0 → RD d) :
    cnorm (d := d) (Nat.zero_le d) (exteriorPower.ιMulti ℝ 0 v) = 1 := by
  have hw : ∀ I : IDX d 0, wcoord (d := d) (k := 0) (exteriorPower.ιMulti ℝ 0 v) I = 1 := by
    intro I
    rw [wcoord_eq_inner, basisWedge_eq_enumWedge (d := d) (k := 0) I,
      exteriorPower.inner_ιMulti_ιMulti]
    simp
  refine le_antisymm ?_ ?_
  · refine cnorm_le_of_forall (d := d) (Nat.zero_le d) _ (fun I => ?_)
    rw [hw I, abs_one]
  · obtain ⟨I, -⟩ := idx_nonempty (d := d) (k := 0) (Nat.zero_le d)
    calc (1 : ℝ) = |wcoord (d := d) (k := 0) (exteriorPower.ιMulti ℝ 0 v) I| := by
          rw [hw I, abs_one]
      _ ≤ cnorm (d := d) (Nat.zero_le d) _ := le_cnorm _ _ I

/-- The max-norm rank-`0` data set is the singleton `{0}`. -/
lemma maxRankDataSet_eq_zero {Λ : Submodule ℤ (E d)} {hjd : 0 ≤ d} :
    maxRankDataSet (d := d) Λ 0 hjd = {0} := by
  rw [Subsingleton.elim hjd (Nat.zero_le d)]
  ext r
  constructor
  · rintro ⟨v, _, _, rfl⟩
    rw [cnorm_iMulti_zero, Real.log_one]
    exact rfl
  · intro hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨Fin.elim0, fun i => i.elim0, linearIndependent_empty_type, by
      rw [cnorm_iMulti_zero, Real.log_one]⟩

/-- The max-norm rank-`0` data set is bounded below. -/
lemma bddBelow_maxRankDataSet_zero (Λ : Submodule ℤ (E d)) (hjd : 0 ≤ d) :
    BddBelow (maxRankDataSet (d := d) Λ 0 hjd) := by
  rw [maxRankDataSet_eq_zero]
  exact ⟨0, by intro x hx; rw [Set.mem_singleton_iff] at hx; rw [hx]⟩

/-- The max-norm data at rank `0` is `0`. -/
lemma maxRankData_zero (Λ : Submodule ℤ (E d)) :
    maxRankData Λ 0 (Nat.zero_le d) = 0 := by
  have hset : maxRankDataSet Λ 0 (Nat.zero_le d) = {0} := by
    ext r
    constructor
    · rintro ⟨v, _, _, rfl⟩
      rw [cnorm_iMulti_zero, Real.log_one]
      exact rfl
    · intro hr
      rw [Set.mem_singleton_iff] at hr
      subst hr
      exact ⟨Fin.elim0, fun i => i.elim0, linearIndependent_empty_type, by
        rw [cnorm_iMulti_zero, Real.log_one]⟩
  rw [maxRankData, hset, csInf_singleton]

/-- A variant of `maxRankData_zero` for an arbitrary proof of `j ≤ d`. -/
lemma maxRankData_eq_zero {Λ : Submodule ℤ (E d)} {j : ℕ} (hjd : j ≤ d) (hj : j = 0) :
    maxRankData Λ j hjd = 0 := by
  subst hj
  exact maxRankData_zero Λ

end Submission.MaxRankData

end
