import Mathlib.GroupTheory.Nilpotent
import Mathlib.Topology.Order
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.Work.SSGRoute.PT.pt_fun_vanishing_relaxation_offRam
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

open scoped RestrictedProduct

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **The relaxation step with the annihilator condition required only off `Ram`.**

This is `Work.SSGRoute.PT.restrictedProduct_relaxation_of_dualPair` with the condition

  `hU : ∀ i, ∀ y : Y i, y ∈ U' i ↔ ∀ x : X i, x ∈ U i → β i x y = 0`

weakened to the indices `i ∉ Ram`.  The proof is that of
`Work.SSGRoute.PT.restrictedProduct_relaxation_of_dualPair` with the only `hU`-consuming call
(`Work.SSGRoute.PT.pt_fun_vanishing_relaxation`) replaced by the off-`Ram` version
`Work.SSGRoute.PT.pt_fun_vanishing_relaxation_offRam`. -/
theorem restrictedProduct_relaxation_offRam
    (p : ℕ) [Fact p.Prime]
    {ι : Type*} {X Y : ι → Type*}
    [∀ i, AddCommGroup (X i)] [∀ i, Module (ZMod p) (X i)] [∀ i, Finite (X i)]
    [∀ i, TopologicalSpace (X i)] [∀ i, DiscreteTopology (X i)]
    [∀ i, AddCommGroup (Y i)] [∀ i, Module (ZMod p) (Y i)] [∀ i, Finite (Y i)]
    [∀ i, TopologicalSpace (Y i)] [∀ i, DiscreteTopology (Y i)]
    (U : ∀ i, Submodule (ZMod p) (X i)) (U' : ∀ i, Submodule (ZMod p) (Y i))
    (β : ∀ i, X i →ₗ[ZMod p] Y i →ₗ[ZMod p] ZMod p)
    (hβL : ∀ i, ∀ x : X i, (∀ y : Y i, β i x y = 0) → x = 0)
    (hβR : ∀ i, ∀ y : Y i, (∀ x : X i, β i x y = 0) → y = 0)
    (hβ0 : ∀ i, ∀ x ∈ U i, ∀ y ∈ U' i, β i x y = 0)
    (Ram : Set ι) (T : Finset ι) (hTRam : ∀ i ∈ T, i ∈ Ram)
    (hU : ∀ i, i ∉ Ram → ∀ y : Y i, y ∈ U' i ↔ ∀ x : X i, x ∈ U i → β i x y = 0)
    (A : Submodule (ZMod p) (Πʳ i, [X i, U i]))
    (B : Submodule (ZMod p) (Πʳ i, [Y i, U' i]))
    (hBcl : ∀ y : Πʳ i, [Y i, U' i],
      (∀ a : Πʳ i, [X i, U i], a ∈ A → restrictedPairing U U' β a y = 0) → y ∈ B)
    (hAB : ∀ a : Πʳ i, [X i, U i],
      a ∈ A ↔ ∀ b : Πʳ i, [Y i, U' i], b ∈ B → restrictedPairing U U' β a b = 0)
    (x : (i : T) → X i)
    (hx : ∀ b : Πʳ i, [Y i, U' i], b ∈ B →
      (∀ i, i ∉ Ram → (b i : Y i) ∈ U' i) → (∀ i, i ∈ Ram → i ∉ T → (b i : Y i) = 0) →
      ∑ i : T, β i (x i) (b (i : ι)) = 0) :
    ∃ a : Πʳ i, [X i, U i], a ∈ A ∧ (∀ i, i ∉ Ram → (a i : X i) ∈ U i) ∧
      (∀ i : T, a (i : ι) = x i) := by
  classical
  -- the relaxation subgroup
  let W : Submodule (ZMod p) (Πʳ i, [X i, U i]) :=
    { carrier := {w | (∀ i ∈ T, (w i : X i) = 0) ∧ (∀ i, i ∉ Ram → (w i : X i) ∈ U i)}
      zero_mem' := by
        constructor
        · intro i _; rfl
        · intro i _; exact (U i).zero_mem
      add_mem' := by
        intro a b ha hb
        constructor
        · intro i hi
          change (a i : X i) + b i = 0
          rw [ha.1 i hi, hb.1 i hi, add_zero]
        · intro i hi
          change (a i : X i) + b i ∈ U i
          exact (U i).add_mem (ha.2 i hi) (hb.2 i hi)
      smul_mem' := by
        intro c a ha
        constructor
        · intro i hi
          change c • (a i : X i) = 0
          rw [ha.1 i hi, smul_zero]
        · intro i hi
          change c • (a i : X i) ∈ U i
          exact (U i).smul_mem c (ha.2 i hi) }
  -- the test element `z`
  set fz : ∀ i, X i := fun i => if h : i ∈ T then x ⟨i, h⟩ else 0 with hfzdef
  set z : Πʳ i, [X i, U i] := piSingle U T fz with hzdef
  have hfz : ∀ j (hj : j ∈ T), fz j = x ⟨j, hj⟩ := by
    intro j hj
    rw [hfzdef]
    simp only [dif_pos hj]
  have hzT : ∀ j (hj : j ∈ T), ((z : Πʳ i, [X i, U i]) : ∀ i, X i) j = x ⟨j, hj⟩ := by
    intro j hj
    rw [hzdef, piSingle_apply_of_mem U hj]
    exact hfz j hj
  have hzN : ∀ j, j ∉ T → ((z : Πʳ i, [X i, U i]) : ∀ i, X i) j = 0 := by
    intro j hj
    rw [hzdef, piSingle_apply_of_notMem U hj]
  -- the pairing of `z` against any element of the dual restricted product
  have hzsum : ∀ b : Πʳ i, [Y i, U' i],
      restrictedPairing U U' β z b = ∑ i : T, β i (x i) (b (i : ι)) := by
    intro b
    rw [hzdef, restrictedPairing_piSingle_left U U' β hβ0 T fz b]
    rw [sum_piSingle_bridge U U' β T x fz hfz b]
    rw [← sum_attach_eq_sum T (fun j => β j.1 (x j) (b j.1))]
  -- the annihilator of `A` is `B`: this is *exactly* the hypothesis `hBcl`
  have hAann : ∀ y : Πʳ i, [Y i, U' i],
      (∀ a ∈ A, restrictedPairing U U' β a y = 0) → y ∈ B := hBcl
  -- the main step: `z` lies in `A + W`
  have hz : z ∈ A ⊔ W := by
    by_contra hzin
    have hcl : W.mkQ z ∉ A.map W.mkQ := by
      rw [Submodule.mem_map]
      rintro ⟨a, ha, haz⟩
      apply hzin
      refine Submodule.mem_sup.mpr ⟨a, ha, z - a, ?_, ?_⟩
      · have h1 : a - z ∈ W := by
          rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at haz
          exact (Submodule.Quotient.eq W).mp haz
        simpa using W.neg_mem h1
      · abel
    obtain ⟨g, hgker, hgz⟩ := LinearMap.exists_extend_of_notMem (p := A.map W.mkQ)
      (0 : ↥(A.map W.mkQ) →ₗ[ZMod p] ZMod p) hcl 1
    set L : (Πʳ i, [X i, U i]) →ₗ[ZMod p] ZMod p := g.comp W.mkQ with hLdef
    have hker : ∀ a ∈ A, L a = 0 := by
      intro a ha
      have h2 := LinearMap.congr_fun hgker
        (⟨W.mkQ a, Submodule.mem_map_of_mem ha⟩ : ↥(A.map W.mkQ))
      simpa [hLdef] using h2
    have hLW : ∀ w : Πʳ i, [X i, U i],
        (∀ i ∈ T, (w i : X i) = 0) → (∀ i, i ∉ Ram → (w i : X i) ∈ U i) → L w = 0 := by
      intro w h1 h2
      have hw : w ∈ W := ⟨h1, h2⟩
      have h0 : W.mkQ w = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hw
      rw [hLdef, LinearMap.comp_apply, h0, map_zero]
    obtain ⟨b, hbU, hbR0, hbL⟩ :=
      pt_fun_vanishing_relaxation_offRam p U U' β hβL hβR hβ0 Ram T hTRam hU L hLW
    have hbB : b ∈ B := by
      apply hAann
      intro a ha
      rw [← hbL a]
      exact hker a ha
    have h1 : (∑ i : T, β i (x i) (b (i : ι))) = 0 := hx b hbB hbU hbR0
    have h3 : restrictedPairing U U' β z b = 1 := by
      rw [← hbL z, hLdef, LinearMap.comp_apply, hgz]
    have h4 : restrictedPairing U U' β z b = 0 := by rw [hzsum b, h1]
    rw [h4] at h3
    exact absurd h3 (by simp)
  -- conclusion
  obtain ⟨a, ha, w, hw, haw⟩ := Submodule.mem_sup.mp hz
  refine ⟨a, ha, ?_, ?_⟩
  · intro i hiRam
    have hiT : i ∉ T := fun h => hiRam (hTRam i h)
    have h1 : ((z : Πʳ i, [X i, U i]) : ∀ i, X i) i = 0 := hzN i hiT
    have h2 : (w i : X i) ∈ U i := hw.2 i hiRam
    have h3 : (a i : X i) + w i = (z i : X i) := by
      have hh := congrArg (fun t : Πʳ i, [X i, U i] => (t : ∀ i, X i) i) haw
      simpa using hh
    rw [h1] at h3
    have h4 : (a i : X i) = -w i := (add_eq_zero_iff_eq_neg.mp h3)
    rw [h4]
    exact (U i).neg_mem h2
  · intro i
    have h1 : ((z : Πʳ i, [X i, U i]) : ∀ i, X i) (i : ι) = x i := hzT (i : ι) i.2
    have h2 : (w (i : ι) : X i) = 0 := hw.1 (i : ι) i.2
    have h3 : (a (i : ι) : X i) + w (i : ι) = (z (i : ι) : X i) := by
      have hh := congrArg (fun t : Πʳ i, [X i, U i] => (t : ∀ i, X i) (i : ι)) haw
      simpa using hh
    rw [h2, add_zero] at h3
    rw [h3, h1]

end Work.SSGRoute.PT
