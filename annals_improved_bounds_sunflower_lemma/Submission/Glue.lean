import Mathlib
import ChallengeDeps
import Submission.Upper
import Submission.FinalFit
import Submission.SunBasic

/-!
# Top-level assembly: from Finset sunflowers to `Set (Set X)` sunflowers

This module connects the finite-combinatorics chain (in `Submission.Sun`, over
`Finset α`) to the theorem statement over `Set (Set X)` (see `ChallengeDeps.lean`).
The last step: a `w`-set system `ℱ` with `|ℱ| ≥ lowerBound r C w` contains an
`r`-sunflower.
-/
open Finset
open scoped BigOperators
open scoped Classical
open Real

noncomputable section

namespace Submission.Glue

open _root_.ImprovedBoundsSunflowerLemma
open _root_.Set

/-- Final constant `C` in Theorem 1.4 (2^82, matching `FinalFit.Cf`). -/
noncomputable def Cfinal : ℝ := 2 ^ 82

lemma Ksf_eq_KsfF : Sun.Ksf = FinalFit.KsfF := by
  unfold Sun.Ksf FinalFit.KsfF
  norm_num

/-- fitting: (w+r+1)·(Ksf·r·log(2w))^w ≤ lowerBound r (2^82) w -/
lemma fit_lowerBound {r w : ℕ} (hr : 3 ≤ r) (hw : 2 ≤ w) :
    ((w : ℝ) + (r : ℝ) + 1) * (Sun.Ksf * (r : ℝ) * Real.log (2 * (w : ℝ))) ^ w
      ≤ lowerBound r Cfinal w := by
  unfold lowerBound
  calc
    ((w : ℝ) + (r : ℝ) + 1) * (Sun.Ksf * (r : ℝ) * Real.log (2 * (w : ℝ))) ^ w
        = ((w : ℝ) + (r : ℝ) + 1) * (FinalFit.KsfF * (r : ℝ) * Real.log (2 * (w : ℝ))) ^ w := by
            rw [Ksf_eq_KsfF]
    _ ≤ (FinalFit.Cf * (r : ℝ) ^ 3 * Real.logb (1.9 : ℝ) (w : ℝ) *
          Real.logb (1.9 : ℝ) (Real.logb (1.9 : ℝ) (w : ℝ))) ^ w := by
            exact FinalFit.fit_main (r := r) (w := w) hr hw
    _ = (Cfinal * (r : ℝ) ^ 3 * Real.logb (1.9 : ℝ) (w : ℝ) *
          Real.logb (1.9 : ℝ) (Real.logb (1.9 : ℝ) (w : ℝ))) ^ w := by
          unfold Cfinal FinalFit.Cf
          ring

namespace SetLevel

variable {X : Type*} [Fintype X]

/-- the Finset-family associated with a set system ℱ -/
def finsetFamily (ℱ : Set (Set X)) : Finset (Finset X) :=
  (ℱ.toFinset).image (fun A : Set X => A.toFinset)

lemma toFinset_injective : Function.Injective (fun A : Set X => A.toFinset) := by
  intro A B h
  have hc : (↑(A.toFinset) : Set X) = (↑(B.toFinset) : Set X) := by
    exact congrArg (fun s : Finset X => (↑s : Set X)) h
  simpa using hc

lemma mem_finsetFamily {ℱ : Set (Set X)} {f : Finset X} :
    f ∈ finsetFamily ℱ ↔ ∃ A ∈ ℱ, A.toFinset = f := by
  unfold finsetFamily
  rw [Finset.mem_image]
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, Set.mem_toFinset.mp hA, rfl⟩
  · rintro ⟨A, hA, hEq⟩
    refine ⟨A, ?_, hEq⟩
    exact Set.mem_toFinset.mpr hA

lemma card_finsetFamily (ℱ : Set (Set X)) : (finsetFamily ℱ).card = ℱ.ncard := by
  unfold finsetFamily
  rw [Finset.card_image_of_injective _ (toFinset_injective (X := X))]
  rw [Set.ncard_eq_toFinset_card']

lemma member_card {ℱ : Set (Set X)} {A : Set X} (hA : A ∈ ℱ) :
    (A.toFinset : Finset X).card = A.ncard := by
  rw [Set.ncard_eq_toFinset_card']

lemma of_mem_finsetFamily {ℱ : Set (Set X)} {f : Finset X}
    (hf : f ∈ finsetFamily ℱ) : ((f : Set X) ∈ ℱ) := by
  rcases (mem_finsetFamily (ℱ := ℱ)).1 hf with ⟨A, hA, hEq⟩
  have : A = (f : Set X) := by
    calc
      A = (↑(A.toFinset) : Set X) := (Set.coe_toFinset A).symm
      _ = (f : Set X) := by rw [hEq]
  simpa [this] using hA

/-- the set-level family from a Finset sunflower -/
def liftSunflowerSet (G' : Finset (Finset X)) : Set (Set X) :=
  {A : Set X | A.toFinset ∈ G'}

lemma mem_liftSunflowerSet {G' : Finset (Finset X)} {A : Set X} :
    A ∈ liftSunflowerSet G' ↔ A.toFinset ∈ G' := by rfl

def finEquiv : Set X ≃ Finset X where
  toFun := fun A => A.toFinset
  invFun := fun s => (↑s : Set X)
  left_inv := by intro A; exact Set.coe_toFinset A
  right_inv := by intro s; ext x; simp

lemma liftSunflowerSet_card {G' : Finset (Finset X)} :
    (liftSunflowerSet G').ncard = G'.card := by
  classical
  let e : Set X ≃ Finset X := finEquiv
  have himg : e '' liftSunflowerSet G' = (G' : Set (Finset X)) := by
    ext f
    constructor
    · intro h
      rcases h with ⟨A, hA, hEq⟩
      have hA' : A.toFinset ∈ G' := (mem_liftSunflowerSet (G' := G')).1 hA
      rw [← hEq]
      exact hA'
    · intro hf
      refine ⟨(f : Set X), ?_, ?_⟩
      · unfold liftSunflowerSet
        simpa using hf
      · dsimp [e, finEquiv]
        ext x
        simp
  calc
    (liftSunflowerSet G').ncard = (e '' liftSunflowerSet G').ncard := by
      exact (Set.ncard_image_of_injective (liftSunflowerSet G') e.injective).symm
    _ = (G' : Set (Finset X)).ncard := by rw [himg]
    _ = G'.card := by
      rw [Set.ncard_eq_toFinset_card']
      congr 1
      ext f
      simp

/-- set-level sInter of the lifted family equals the Finset `interAll`. -/
lemma sInter_liftSunflowerSet {G' : Finset (Finset X)}
    (hG : G'.Nonempty) :
    (⋂₀ liftSunflowerSet G' : Set X) = (↑(Sun.interAll G') : Set X) := by
  ext x
  rw [Finset.mem_coe]
  rw [Sun.mem_interAll hG]
  constructor
  · intro hx C hC
    have hmem : (C : Set X) ∈ liftSunflowerSet G' := by
      rw [mem_liftSunflowerSet]
      simpa using hC
    have hxCset : x ∈ (C : Set X) := hx (C : Set X) hmem
    simpa using hxCset
  · intro hx C0 hC0
    have hC : C0.toFinset ∈ G' := (mem_liftSunflowerSet (G' := G')).1 hC0
    have hxC : x ∈ C0.toFinset := hx C0.toFinset hC
    have hxC0 : x ∈ C0 := by simpa using hxC
    exact hxC0

/-- IsSunflower (Set-level) from the Finset-level one -/
theorem lift_sunflower {G' : Finset (Finset X)} {r : ℕ} (hr : 1 ≤ r)
    (hG' : Sun.IsSunflower G' r) : _root_.Set.IsSunflower r (liftSunflowerSet G') := by
  constructor
  · rw [liftSunflowerSet_card, hG'.1]
  · intro A hA B hB hAB
    have hA' : A.toFinset ∈ G' := (mem_liftSunflowerSet (G' := G')).1 hA
    have hB' : B.toFinset ∈ G' := (mem_liftSunflowerSet (G' := G')).1 hB
    have hne : A.toFinset ≠ B.toFinset := by
      intro h
      exact hAB (toFinset_injective h)
    have hInter : A.toFinset ∩ B.toFinset = Sun.interAll G' :=
      hG'.2 A.toFinset hA' B.toFinset hB' hne
    have hGnon : G'.Nonempty := by
      apply Finset.card_pos.mp
      rw [hG'.1]
      exact hr
    have hAB' : A ∩ B = (↑(Sun.interAll G') : Set X) := by
      ext x
      simp
      rw [← hInter]
      simp
    rw [hAB']
    exact (sInter_liftSunflowerSet (G' := G') hGnon).symm

theorem sunflower_of_set {ℱ : Set (Set X)} {r : ℕ} (hr : 1 ≤ r)
    (h : Sun.HasSunflower (finsetFamily ℱ) r) :
    ∃ S ⊆ ℱ, _root_.Set.IsSunflower r S := by
  rcases h with ⟨G', hG'F, hSun⟩
  refine ⟨liftSunflowerSet G', ?_, lift_sunflower (G' := G') hr hSun⟩
  intro A hA
  have hA' : A.toFinset ∈ G' := (mem_liftSunflowerSet (G' := G')).1 hA
  have hmem : (A.toFinset : Set X) ∈ ℱ := of_mem_finsetFamily (ℱ := ℱ) (f := A.toFinset) (hG'F hA')
  simpa [Set.coe_toFinset] using hmem

end SetLevel

/-- ℱ with |ℱ| ≥ lowerBound contains an r-sunflower (the Set-level core). -/
theorem glue_sunflower {X : Type*} [Fintype X] {r w : ℕ}
    (hr : 3 ≤ r) (hw : 2 ≤ w) (ℱ : Set (Set X))
    (hsize : ∀ A ∈ ℱ, A.ncard ≤ w)
    (hcard : (ℱ.ncard : ℝ) ≥ lowerBound r Cfinal w) :
    ∃ S ⊆ ℱ, _root_.Set.IsSunflower r S := by
  classical
  let F : Finset (Finset X) := SetLevel.finsetFamily ℱ
  have hS : ∀ A ∈ F, A ⊆ Finset.univ := by
    intro A hA
    simp
  have huni : ∀ A ∈ F, A.card ≤ w := by
    intro A hA
    rcases (SetLevel.mem_finsetFamily (ℱ := ℱ)).1 hA with ⟨A0, hA0, hEq⟩
    have hc : A0.ncard ≤ w := hsize A0 hA0
    rw [← hEq]
    simpa [SetLevel.member_card hA0] using hc
  have hB : ((w : ℝ) + (r : ℝ) + 1) * (Sun.Ksf * (r : ℝ) * Real.log (2 * (w : ℝ))) ^ w
      ≤ lowerBound r Cfinal w := fit_lowerBound hr hw
  have hFcard : (F.card : ℝ) ≥ lowerBound r Cfinal w := by
    rw [SetLevel.card_finsetFamily]
    exact hcard
  have hsun := Sun.sunflower_of_large (X := (Finset.univ : Finset X)) (F := F) (p := r) (w := w)
    (B := lowerBound r Cfinal w) (by omega) hw hS huni hB hFcard
  exact SetLevel.sunflower_of_set (ℱ := ℱ) (by omega) hsun

end Submission.Glue

end
