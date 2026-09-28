import Mathlib
import Submission.Work.Serre.RangeEMVanFinDefs
import Submission.Work.Serre.serreRangeEMVanOne
import Submission.Work.Rat.U.C3
import Submission.Work.Serre.RangeOne.colimModel

/-!
# `RangeEMVanOneFin` from `SerreC0` and `SerreC3Finite`

`Work.Serre.RangeEMVanOneFin` is the range form of the acyclicity of `K(A,1)` for a **finite**
coefficient group `A` (see `RangeEMVanFinDefs.lean`).  The proof is the one of
`Work.Serre.serreRangeEMVanOne` with the *finite* statement `Work.Serre.SerreC3Finite` in place of
the torsion statement `Work.Serre.SerreC3`: compare a range model `W` with a genuine model `Z` of
`K(π₁W,1)` (`Work.Serre.RangeOne.colimModel`, which needs only that `π₁W` be torsion — supplied
here by its finiteness) and apply C3 to `Z`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

/-- A finite group is a torsion group (in the form used by `Work.Serre.RangeOne.colimModel`). -/
theorem torsion_of_nonempty_fintype {G : Type*} [Group G] (h : Nonempty (Fintype G)) :
    ∀ α : G, ∃ K : ℕ, 0 < K ∧ α ^ K = 1 := by
  haveI := h.some
  intro α
  exact ⟨orderOf α, orderOf_pos α, pow_orderOf_eq_one α⟩

/-- **The `1`-type range form of C3 for a finite coefficient group**, from `SerreC0` and
`SerreC3Finite` — unconditionally. -/
theorem serreRangeEMVanOneFin (hC0 : Work.Serre.SerreC0) (hC3 : Work.Serre.SerreC3Finite) :
    Work.Serre.RangeEMVanOneFin := by
  intro N W _ w₀ h0 hcomm hfin hvan t ht htN
  have hN : 2 ≤ N := by omega
  haveI : Nonempty W := ⟨w₀⟩
  obtain ⟨Z, tZ, pt, f, hgen, hbij⟩ :=
    Work.Serre.RangeOne.colimModel N W w₀ h0 hcomm
      (torsion_of_nonempty_fintype hfin) hvan
  rcases hgen with ⟨hne, hhigh⟩
  obtain ⟨e⟩ := hne
  letI : TopologicalSpace Z := tZ
  -- the additive commutative group structure required by `SerreC3Finite`
  letI hGr : Group (HomotopyGroup (Fin 1) W w₀) := HomotopyGroup.group (Fin 1)
  letI : CommGroup (HomotopyGroup (Fin 1) W w₀) := { hGr with mul_comm := hcomm }
  haveI : Fintype (Additive (HomotopyGroup (Fin 1) W w₀)) := by
    haveI := hfin.some
    exact inferInstance
  have hIsEM : IsEMSpace (Additive (HomotopyGroup (Fin 1) W w₀)) 1 (by norm_num) Z pt :=
    ⟨⟨e⟩, hhigh⟩
  have hacyc : RatAcyclic Z := hC3 _ 1 (by norm_num) Z pt hIsEM
  have hiso : IsIso (ratHomologyMap f t) :=
    Work.Serre.RangeOne.rangeWhitehead W Z w₀ f N (fun i hi x => hbij i hi x) t (by omega)
  exact IsZero.of_iso (hacyc.isZero_ratH ht) (asIso (ratHomologyMap f t))

end

end Work.Serre

namespace Work.Serre

noncomputable section

/-- **`RangeEMVanOneFin` from `SerreC3Finite` alone.**  `Work.Serre.serreRangeEMVanOneFin` carries
an unused `SerreC0` hypothesis; this is the same proof with it removed. -/
theorem serreRangeEMVanOneFin_noC0 (hC3 : Work.Serre.SerreC3Finite) :
    Work.Serre.RangeEMVanOneFin := by
  intro N W _ w₀ h0 hcomm hfin hvan t ht htN
  have hN : 2 ≤ N := by omega
  haveI : Nonempty W := ⟨w₀⟩
  obtain ⟨Z, tZ, pt, f, hgen, hbij⟩ :=
    Work.Serre.RangeOne.colimModel N W w₀ h0 hcomm
      (Work.Serre.torsion_of_nonempty_fintype hfin) hvan
  rcases hgen with ⟨hne, hhigh⟩
  obtain ⟨e⟩ := hne
  letI : TopologicalSpace Z := tZ
  letI hGr : Group (HomotopyGroup (Fin 1) W w₀) := HomotopyGroup.group (Fin 1)
  letI : CommGroup (HomotopyGroup (Fin 1) W w₀) := { hGr with mul_comm := hcomm }
  haveI : Fintype (Additive (HomotopyGroup (Fin 1) W w₀)) := by
    haveI := hfin.some
    exact inferInstance
  have hIsEM : IsEMSpace (Additive (HomotopyGroup (Fin 1) W w₀)) 1 (by norm_num) Z pt :=
    ⟨⟨e⟩, hhigh⟩
  have hacyc : RatAcyclic Z := hC3 _ 1 (by norm_num) Z pt hIsEM
  have hiso : IsIso (ratHomologyMap f t) :=
    Work.Serre.RangeOne.rangeWhitehead W Z w₀ f N (fun i hi x => hbij i hi x) t (by omega)
  exact IsZero.of_iso (hacyc.isZero_ratH ht) (asIso (ratHomologyMap f t))

end

end Work.Serre
