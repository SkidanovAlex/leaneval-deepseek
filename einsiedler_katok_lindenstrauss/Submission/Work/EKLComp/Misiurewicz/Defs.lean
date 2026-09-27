import Mathlib
import Submission.Work.EKLContract.Interfaces

/-!
# C4a (Misiurewicz) — shared definitions

The material below is the vocabulary of the Misiurewicz construction
(`Submission/Work/EKLComp/prove_Misiurewicz.lean`): the neighbourhoods `V δ` and their closures,
the displacement function `vMove`, the uniform measure on a finite set and the Misiurewicz
averaged measure, and the "window joins" used to compute entropies of shifted time windows.
-/

namespace Work.EKLComp

open MeasureTheory Filter Topology
open Work.EKLContract
open scoped ENNReal

noncomputable section

/-! ## Neighbourhoods of the identity and "fine" sets -/

/-- The closed `δ`-neighbourhood of the identity, i.e. `V δ` with `≤` instead of `<`.
It is compact (for `δ > 0`), and contains `closure (V δ)`. -/
def Vbar (δ : ℝ) : Set SL3 :=
  {g | ∀ i j, |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ δ}

theorem V_subset_Vbar (δ : ℝ) : V δ ⊆ Vbar δ := fun g hg i j => le_of_lt (hg i j)

/-- The translate `V δ • z = {u • z | u ∈ V δ}`. -/
def Vball (δ : ℝ) (z : X3) : Set X3 := (fun u : SL3 => u • z) '' V δ

theorem mem_Vball {δ : ℝ} {z x : X3} : x ∈ Vball δ z ↔ ∃ u ∈ V δ, u • z = x := Iff.rfl

theorem Vball_subset_Vbar_ball (δ : ℝ) (z : X3) : Vball δ z ⊆ (fun u : SL3 => u • z) '' Vbar δ :=
  Set.image_mono (V_subset_Vbar δ)

/-- A subset of `X₃` is `ε`-fine if any two of its points are related by `V ε`, i.e. `y = u • x`
with `u ∈ V ε`.  Such sets are exactly what the separated sets of `PosEnt` can distinguish. -/
def Fine (ε : ℝ) (S : Set X3) : Prop := ∀ x ∈ S, ∀ y ∈ S, CloseBy ε x y

theorem Fine.mono {ε ε' : ℝ} (h : ε ≤ ε') {S : Set X3} (hS : Fine ε S) : Fine ε' S :=
  fun x hx y hy => let ⟨u, hu, huy⟩ := hS x hx y hy
    ⟨u, fun i j => lt_of_lt_of_le (hu i j) h, huy⟩

/-- The `V`-displacement from `x` to `y`: the infimum of the `δ > 0` such that `y = u • x`
for some `u ∈ V δ`.  (The action of `SL₃(ℝ)` on `X₃` is transitive, so the set is nonempty and
the infimum is a nonnegative real.) -/
def vMove (x y : X3) : ℝ := sInf {δ : ℝ | 0 < δ ∧ CloseBy δ x y}

/-- The translate `V η • z` is `ε`-fine as soon as `V η · (V η)⁻¹ ⊆ V ε`. -/
theorem fine_Vball (ε η : ℝ) (hη : ∀ u v : SL3, u ∈ V η → v ∈ V η → v * u⁻¹ ∈ V ε)
    (z : X3) : Fine ε (Vball η z) := by
  rintro x ⟨u, hu, rfl⟩ y ⟨v, hv, rfl⟩
  refine ⟨v * u⁻¹, hη u v hu hv, ?_⟩
  show v • z = (v * u⁻¹) • (u • z)
  rw [← mul_smul]
  congr 1
  group

/-! ## The maps `x ↦ g • x` -/

/-- `smulMap g` is the homeomorphism `x ↦ g • x` of `X₃`. -/
def smulMap (g : SL3) : X3 → X3 := fun x => g • x

@[simp] theorem smulMap_apply (g : SL3) (x : X3) : smulMap g x = g • x := rfl

theorem smulMap_iterate (g : SL3) (k : ℕ) : (smulMap g)^[k] = smulMap (g ^ k) := by
  ext x
  simp only [smulMap_apply]
  induction k with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, smulMap_apply, pow_succ', mul_smul]

@[simp] theorem smulMap_iterate_apply (g : SL3) (k : ℕ) (x : X3) :
    (smulMap g)^[k] x = (g ^ k) • x := by
  rw [smulMap_iterate]; rfl

theorem continuous_smulMap (g : SL3) : Continuous (smulMap g) := continuous_const_smul g

/-! ## Averaging measures -/

/-- The uniform probability measure on a nonempty finite set. -/
def unifMeasure (E : Finset X3) : Measure X3 :=
  (E.card : ℝ≥0∞)⁻¹ • ∑ x ∈ E, Measure.dirac x

/-- The Misiurewicz average of `σ` along the first `N` iterates of `x ↦ g • x`. -/
def misAvgMeasure (g : SL3) (N : ℕ) (σ : Measure X3) : Measure X3 :=
  (N : ℝ≥0∞)⁻¹ • ∑ k ∈ Finset.range N, Measure.map (smulMap (g ^ k)) σ

/-- The Misiurewicz average associated to a finite set `E`: average the uniform measure on `E`
over the first `N` iterates. -/
def misAvg (g : SL3) (N : ℕ) (E : Finset X3) : Measure X3 :=
  misAvgMeasure g N (unifMeasure E)

/-! ## Window joins -/

/-- The join of the first `N` iterates of `P` along the time window `[k, k+N)`. -/
def winJoin (T : X3 → X3) (P : FinPart X3) (k N : ℕ) : (Fin N → Fin P.n) → Set X3 :=
  fun w => ⋂ j : Fin N, T^[(j : ℕ) + k] ⁻¹' P.parts (w j)

theorem winJoin_zero (T : X3 → X3) (P : FinPart X3) (N : ℕ) :
    winJoin T P 0 N = joinSets T P N := by
  funext w
  ext x
  simp only [winJoin, joinSets, Set.mem_iInter, Set.mem_preimage, Nat.add_zero]

theorem winJoin_eq_preimage (T : X3 → X3) (P : FinPart X3) (k N : ℕ) (w : Fin N → Fin P.n) :
    winJoin T P k N w = T^[k] ⁻¹' (joinSets T P N w) := by
  ext x
  simp only [winJoin, joinSets, Set.mem_iInter, Set.mem_preimage]
  constructor
  · intro h j
    have h' := h j
    rw [Function.iterate_add_apply] at h'
    exact h'
  · intro h j
    have h' := h j
    rw [← Function.iterate_add_apply] at h'
    exact h'

/-- The join of a finite partition over `N` time steps is a partition. -/
theorem joinSets_pairwise (T : X3 → X3) (P : FinPart X3) (N : ℕ) :
    Pairwise (fun w w' : Fin N → Fin P.n =>
      Disjoint (joinSets T P N w) (joinSets T P N w')) := by
  intro w w' hne
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  exact Disjoint.mono (Set.iInter_subset _ j) (Set.iInter_subset _ j)
    ((P.disjoint hj).preimage (T^[j]))

theorem joinSets_iUnion (T : X3 → X3) (P : FinPart X3) (N : ℕ) :
    (⋃ w, joinSets T P N w) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  rw [Set.mem_iUnion]
  choose w hw using fun j : Fin N =>
    Set.mem_iUnion.mp (P.cover ▸ Set.mem_univ ((T^[(j : ℕ)]) x))
  exact ⟨w, by rw [joinSets]; exact Set.mem_iInter.mpr hw⟩

theorem winJoin_isPartition (T : X3 → X3) (P : FinPart X3) (k N : ℕ) :
    (⋃ w, winJoin T P k N w) = Set.univ ∧
      Pairwise (fun w w' : Fin N → Fin P.n =>
        Disjoint (winJoin T P k N w) (winJoin T P k N w')) := by
  constructor
  · rw [Set.eq_univ_iff_forall]
    intro x
    rw [Set.mem_iUnion]
    choose w hw using fun j : Fin N =>
      Set.mem_iUnion.mp (P.cover ▸ Set.mem_univ ((T^[(j : ℕ) + k]) x))
    exact ⟨w, by rw [winJoin]; exact Set.mem_iInter.mpr hw⟩
  · intro w w' hne
    rw [winJoin_eq_preimage T P k N w, winJoin_eq_preimage T P k N w']
    exact (joinSets_pairwise T P N hne).preimage (T^[k])

end

end Work.EKLComp
