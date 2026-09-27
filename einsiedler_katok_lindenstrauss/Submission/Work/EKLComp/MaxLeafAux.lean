import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLContract.Lemmas.Uij_range
import Submission.Work.EKLContract.Lemmas.Box1_Uij
import Submission.Work.EKLComp.MaxLeafDefs

/-!
# C11a — elementary API used by the maximal inequality
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

noncomputable section

namespace Work.EKLComp

/-- `s ↦ uij h s` is injective. -/
theorem uij_injective {i j : Fin 3} (h : i ≠ j) : Function.Injective (fun s : ℝ => uij h s) := by
  intro s t hst
  have h2 := congrArg (fun g : SL3 => (g : Matrix (Fin 3) (Fin 3) ℝ) i j) hst
  rwa [Work.EKLContract.Lemmas.uij_apply_self h s,
    Work.EKLContract.Lemmas.uij_apply_self h t] at h2

/-- An element of `Uij h` is `uij h s` for the unique `s`, namely its `(i,j)`-entry. -/
theorem eq_uij_entry {i j : Fin 3} (h : i ≠ j) {g : SL3} (hg : g ∈ Uij h) :
    g = uij h ((g : Matrix (Fin 3) (Fin 3) ℝ) i j) := by
  obtain ⟨s, hs⟩ := (Work.EKLContract.Lemmas.mem_Uij_iff h g).mp hg
  rw [← hs, Work.EKLContract.Lemmas.uij_apply_self h s]

/-- Membership in the leaf. -/
theorem mem_leaf_iff {i j : Fin 3} (hij : i ≠ j) (x y : X3) :
    y ∈ leaf i j hij x ↔ ∃ u ∈ Uij hij, u • x = y := Iff.rfl

/-- The leaf of `x` is the orbit of `x`. -/
theorem leaf_smul {i j : Fin 3} (hij : i ≠ j) (x : X3) (u : SL3) (hu : u ∈ Uij hij) :
    u • x ∈ leaf i j hij x := ⟨u, hu, rfl⟩

/-- Points of an atom have the same atom: `atom m` is constant on its atoms. -/
theorem atom_eq_of_mem__MaxLeafAux {m : MeasurableSpace X3} {x y : X3} (hy : y ∈ atom m x) :
    atom m y = atom m x := by
  have hy' : ∀ s : Set X3, MeasurableSet[m] s → x ∈ s → y ∈ s := by
    intro s hs hxs
    rw [atom, Set.mem_sInter] at hy
    exact hy s ⟨hs, hxs⟩
  have hx' : ∀ s : Set X3, MeasurableSet[m] s → y ∈ s → x ∈ s := by
    intro s hs hys
    by_contra hxs
    exact (hy' sᶜ hs.compl hxs) hys
  refine le_antisymm ?_ ?_
  · intro z hz
    rw [atom, Set.mem_sInter] at hz ⊢
    intro s hs
    exact hz s ⟨hs.1, hy' s hs.1 hs.2⟩
  · intro z hz
    rw [atom, Set.mem_sInter] at hz ⊢
    intro s hs
    exact hz s ⟨hs.1, hx' s hs.1 hs.2⟩

end Work.EKLComp

namespace Work.EKLComp

/-- The coordinate of a matrix in the root group `U_ij`: its `(i,j)`-entry. -/
def leafCoord (i j : Fin 3) : SL3 → ℝ := fun g => (g : Matrix (Fin 3) (Fin 3) ℝ) i j

/-- The leafwise measure `ν x` read in the coordinate `t ↦ uij hij t • x`: a measure on `ℝ`. -/
def leafPush (i j : Fin 3) (ν : X3 → Measure SL3) (x : X3) : Measure ℝ :=
  (ν x).map (leafCoord i j)

/-- The point `uij hij t • x` of the leaf. -/
def leafPoint (i j : Fin 3) (hij : i ≠ j) (x : X3) (t : ℝ) : X3 := uij hij t • x

/-- Freeness is transported along the leaf. -/
theorem free_of_smul {i j : Fin 3} (hij : i ≠ j) {x y : X3} {u : SL3} (hu : u ∈ Uij hij)
    (hy : y = u • x) (hx : x ∈ Free i j hij) : y ∈ Free i j hij := by
  subst hy
  intro v hv hvy
  have hfix : (u⁻¹ * v * u) • x = x := by
    rw [mul_smul, mul_smul, hvy, ← mul_smul, inv_mul_cancel, one_smul]
  have hone : u⁻¹ * v * u = 1 := hx _ (mul_mem (mul_mem ((Uij hij).inv_mem hu) hv) hu) hfix
  have h2 : v = 1 := by
    have h3 := congrArg (fun w : SL3 => u * w * u⁻¹) hone
    simpa [mul_assoc] using h3
  exact h2

end Work.EKLComp
