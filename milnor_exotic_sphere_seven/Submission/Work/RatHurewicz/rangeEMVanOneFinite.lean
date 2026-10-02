import Mathlib
import Submission.Work.Serre.RangeEMVanDefs
import Submission.Work.Serre.serreRangeEMVanOne
import Submission.Work.Serre.RangeOne.colimModel
import Submission.Work.StemsB.serreC3_of_two_le

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `RangeEMVanOne` with a **finite** fundamental group

`Work.Serre.RangeEMVanOne` is the range form of C3 at `n = 1`: a connected space `W` with
*abelian torsion* `π₁` and vanishing `πᵢ` (`2 ≤ i ≤ N`) has `H_t(W;ℚ) = 0` for `0 < t ≤ N-1`.

The purpose of this file is to separate out the **finite** case of that statement,

* `Work.RatHurewicz.RangeEMVanOneFinite` — the same statement with `π₁(W)` assumed `Finite`,
* `Work.RatHurewicz.rangeEMVanOneFinite_of_C3FiniteOne` — it follows from C3 at `n = 1` for
  *finite* coefficient groups (`Work.Serre.serreC3FiniteOne`), by comparing a range model with the
  genuine model `Work.Serre.RangeOne.colimModel` (`Work.Serre.rangeEMVanOne_of_comparison`),

together with the reduction of the general case to the finite one
(`Work.RatHurewicz.rangeEMVanOne_of_finite`, in the sibling module): an arbitrary torsion `π₁(W)` is
reduced by the compactness argument of `SERRE_BLUEPRINT.md` ADDENDUM 3 (A) — a rational homology
class is carried by a *finite* subcomplex, whose fundamental group is finitely generated, hence
(being torsion) finite.

This is the split that the target `Work.RatHurewicz.exists_killTower` needs: its chain goes through
`RangeEMVanOne`, and only the *finite* case of C3 is provided by the transfer/lens-space argument
(`Work.Serre.serreC3FiniteOne`).
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

/-- **`RangeEMVanOne` with a finite `π₁`.**  A connected space whose `π₁` is a *finite* abelian
group and whose homotopy groups vanish in degrees `2 ≤ i ≤ N` has vanishing rational homology in
degrees `0 < t ≤ N-1`. -/
def RangeEMVanOneFinite : Prop :=
  ∀ (N : ℕ) (W : Type) [TopologicalSpace W] (w₀ : W),
    Subsingleton (HomotopyGroup (Fin 0) W w₀) →
    (∀ a b : HomotopyGroup (Fin 1) W w₀, a * b = b * a) →
    Finite (HomotopyGroup (Fin 1) W w₀) →
    (∀ i : ℕ, 2 ≤ i → i ≤ N → Subsingleton (HomotopyGroup (Fin i) W w₀)) →
    ∀ t : ℕ, 0 < t → t ≤ N - 1 → IsZero (Work.Serre.ratH (TopCat.of W) t)

/-- **A finite group is a torsion group**, in the form needed by `RangeEMVanOne`. -/
theorem torsion_of_finite_piOne {W : Type} [TopologicalSpace W] (w₀ : W)
    [Finite (HomotopyGroup (Fin 1) W w₀)] :
    ∀ α : HomotopyGroup (Fin 1) W w₀, ∃ K : ℕ, 0 < K ∧ α ^ K = 1 := by
  intro α
  exact ⟨Nat.card (HomotopyGroup (Fin 1) W w₀),
    Nat.card_pos_iff.mpr ⟨⟨1⟩, inferInstance⟩, pow_card_eq_one' (x := α)⟩

/-- **The finite-`π₁` case of `RangeEMVanOne`, from C3 at `n = 1` for finite groups.**

The genuine model of `K(π₁W,1)` is the colimit of the truncation tower
(`Work.Serre.RangeOne.colimModel`); C3 for the finite group `π₁W` makes it rationally acyclic, and
the range Whitehead theorem (`Work.Serre.RangeOne.rangeWhitehead`) transports the vanishing of the
rational homology back to `W`. -/
theorem rangeEMVanOneFinite_of_C3FiniteOne
    (hC3 : ∀ (A : Type) [AddCommGroup A] [Fintype A] (X : Type) [TopologicalSpace X] (pt : X),
      Work.Serre.IsEMSpace A 1 (by norm_num) X pt → Work.Serre.RatAcyclic X) :
    RangeEMVanOneFinite := by
  intro N W _ w₀ h0 hcomm hfin hvan t ht htN
  haveI : Nonempty W := ⟨w₀⟩
  letI hGr : Group (HomotopyGroup (Fin 1) W w₀) := HomotopyGroup.group (Fin 1)
  letI hCG : CommGroup (HomotopyGroup (Fin 1) W w₀) := { hGr with mul_comm := hcomm }
  haveI hFint : Finite (HomotopyGroup (Fin 1) W w₀) := hfin
  haveI hFt : Fintype (HomotopyGroup (Fin 1) W w₀) := Fintype.ofFinite _
  have htors : ∀ α : HomotopyGroup (Fin 1) W w₀, ∃ K : ℕ, 0 < K ∧ α ^ K = 1 :=
    torsion_of_finite_piOne w₀
  obtain ⟨Z, tZ, pt, f, hgen, hbij⟩ :=
    Work.Serre.RangeOne.colimModel N W w₀ h0 hcomm htors hvan
  rcases hgen with ⟨hne, hhigh⟩
  obtain ⟨e⟩ := hne
  letI : TopologicalSpace Z := tZ
  have hIsEM : Work.Serre.IsEMSpace (Additive (HomotopyGroup (Fin 1) W w₀)) 1 (by norm_num)
      Z pt :=
    ⟨⟨e⟩, hhigh⟩
  have hacyc : Work.Serre.RatAcyclic Z := hC3 _ Z pt hIsEM
  have hiso : IsIso (Work.Serre.ratHomologyMap f t) :=
    Work.Serre.RangeOne.rangeWhitehead W Z w₀ f N (fun i hi x => hbij i hi x) t (by omega)
  exact IsZero.of_iso (hacyc.isZero_ratH ht) (asIso (Work.Serre.ratHomologyMap f t))

end

end Work.RatHurewicz

namespace Work.RatHurewicz

noncomputable section

/-- **The range form of C3 at `n = 1`, from C3 at `n = 1` for finite coefficient groups.**

This replaces the hypothesis `Work.Serre.SerreC3` (arbitrary torsion `A`) of
`Work.Serre.rangeEMVanOne_of_comparison` by the *finite* case only — which is what the
transfer/lens-space argument (`Work.Serre.serreC3FiniteOne`) provides — together with the
finite-to-torsion reduction `Work.RatHurewicz.rangeEMVanOne_of_finite` (the compactness argument of
SERRE_BLUEPRINT.md ADDENDUM 3 (A): a rational homology class of `W` is carried by a *finite*
subcomplex, whose fundamental group is finitely generated and torsion, hence finite). -/
theorem rangeEMVanOne_of_C3FiniteOne
    (hC3 : ∀ (A : Type) [AddCommGroup A] [Fintype A] (X : Type) [TopologicalSpace X] (pt : X),
      Work.Serre.IsEMSpace A 1 (by norm_num) X pt → Work.Serre.RatAcyclic X)
    (hbridge : RangeEMVanOneFinite → Work.Serre.RangeEMVanOne) :
    Work.Serre.RangeEMVanOne :=
  hbridge (rangeEMVanOneFinite_of_C3FiniteOne hC3)

end

end Work.RatHurewicz
