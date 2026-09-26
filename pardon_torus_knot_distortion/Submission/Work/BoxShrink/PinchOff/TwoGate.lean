import Submission.Work.BoxShrink.PinchOff.ClosedPairing
import Submission.Work.BoxShrink.PinchOff.SliceConnected
import Submission.Work.BoxShrink.PinchOff.RankOne
import Submission.Work.BoxShrink.PinchOff.alternatingPartitionDataWeak_of_finite_crossing
import Submission.Work.BoxShrink.PinchOff.winding_psi_eq_zero_of_two_component_inter_of_weakPartition
import Submission.Work.PinchLemma3.ClosedDiscA.potential_helpers

/-!
# The pinch for a slice with two components: the two-gate rank bound

The alternating-partition datum of `PairingData.lean` needs the *connectors* — paths inside the
slice joining the endpoints of each upper arc — and these exist automatically only when the slice
is path connected (`alternatingPartitionData_of_finite_crossing_of_isPathConnected_slice`).  For a
slice with **two** components the connectors may be missing, but the *gate* argument of
`winding_psi_eq_zero_of_two_component_inter_of_weakPartition` (delegated, proved) needs no
connectors: with the **connector-free** datum
(`AlternatingPartitionDataWeak`, available from the crossing finiteness alone,
`alternatingPartitionDataWeak_of_finite_crossing`, with no connectivity hypothesis) and the two
gates `A ∩ B = K₁ ∪ K₂`, a functional killing the test loop through the gates kills *every*
winding realised in `A ∪ B`.

This module applies that to the two closed halves of the pinch (`A = UpperSide`,
`B = LowerSide`, `A ∩ B = Σ`), and turns it into the dimension bound the residual needs:

* `exists_killing_functional` — a nonzero functional killing a prescribed displacement vector;
* `psiDisp_eq_apply_psiDisp_id` — `psiDisp ψ u = ψ (psiDisp id u)`;
* `two_gate_rank_le_one` — `finrank W(A ∪ B) ≤ 1` from the weak partition, the two gates and the
  test loop (the linear algebra of `RankOne.lean`);
* `finrank_Omega_le_one_of_two_gate` — the same for `Ω` and the two closed halves, with
  `W(UpperSide) = W(LowerSide) = ⊥` supplied by `TransverseSlice` + `W(Ω⁺ ∪ Ω⁻) = ⊥`;
* `TwoGateDatum` and `dropCase_of_twoGateDatum`, `keyTameClosed_of_twoGateDatum`,
  `bubbleHalf_of_twoGateDatum` — the residual from the two-gate datum at every configuration;
* `twoGateDatum_of_finiteCrossing_of_two_gates` — the datum from `FiniteCrossing`, two
  path-connected gates and path-connected closed halves.

So `DropCase` holds for a slice which is the union of **at most two** path-connected components
(the genuinely *arc* case: one or two embedded arcs), under `FiniteCrossing` and the
path-connectedness of the two closed halves.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-! ## A functional killing a prescribed displacement -/

/-- The linear functional `(x, y) ↦ d₂ x − d₁ y` of the plane, vanishing at `d`. -/
def killFunctional (d : ℝ × ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℝ where
  toFun v := d.2 * v.1 - d.1 * v.2
  map_add' := by
    intro a b
    simp only [Prod.fst_add, Prod.snd_add, RingHom.id_apply]
    ring
  map_smul' := by
    intro a b
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
    ring

theorem killFunctional_apply_self (d : ℝ × ℝ) : killFunctional d d = 0 := by
  simp only [killFunctional, LinearMap.coe_mk, AddHom.coe_mk]
  ring

/-- **A nonzero functional killing a prescribed vector of the plane.** -/
theorem exists_killing_functional (d : ℝ × ℝ) :
    ∃ ψ' : (ℝ × ℝ) →ₗ[ℝ] ℝ, ψ' d = 0 ∧ ψ' ≠ 0 := by
  by_cases hd : d = 0
  · subst hd
    refine ⟨LinearMap.fst ℝ ℝ ℝ, rfl, ?_⟩
    intro h
    have h1 := congrArg (fun f : (ℝ × ℝ) →ₗ[ℝ] ℝ => f ((1 : ℝ), (0 : ℝ))) h
    simp at h1
  · refine ⟨killFunctional d, killFunctional_apply_self d, ?_⟩
    intro hzero
    apply hd
    have h1 : d.2 = 0 := by
      have := congrArg (fun f : (ℝ × ℝ) →ₗ[ℝ] ℝ => f ((1 : ℝ), (0 : ℝ))) hzero
      simpa [killFunctional] using this
    have h2 : d.1 = 0 := by
      have := congrArg (fun f : (ℝ × ℝ) →ₗ[ℝ] ℝ => f ((0 : ℝ), (1 : ℝ))) hzero
      simpa [killFunctional] using this
    exact Prod.ext h2 h1

/-! ## The displacement of `ψ` is `ψ` of the displacement -/

/-- **`psiDisp ψ u = ψ (psiDisp id u)`**: the displacement of a path under a linear map is the
linear map applied to the displacement. -/
theorem psiDisp_eq_apply_psiDisp_id {P : Work.CoreTopology.ParamTorus} {W : Type*}
    [AddCommGroup W] [Module ℝ W] (ψ : (ℝ × ℝ) →ₗ[ℝ] W) {x y : P.carrier} (u : Path x y) :
    Work.PinchLemma3.ClosedDiscA.psiDisp ψ u =
      ψ (Work.PinchLemma3.ClosedDiscA.psiDisp
        (LinearMap.id : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) u) := by
  rw [Work.PinchLemma3.ClosedDiscA.psiDisp, Work.PinchLemma3.ClosedDiscA.psiDisp, map_sub]
  rfl

/-! ## The spans of the two closed halves -/

theorem windingSpan_upperSide_eq_bot_of_transverseSlice
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (hbot : Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) = ⊥) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (UpperSide ψ s c σ u) = ⊥ := by
  rw [upperSide_eq_closedHalfUp, windingSpan_closedHalfUp_eq_halfUp_holds hT]
  exact le_bot_iff.mp (le_trans (Work.SurgeryInvariance.WindingSpan_mono (surface ψ)
    (Set.subset_union_left : HalfUp ψ s c σ u ⊆ Halves ψ s c σ u)) (le_of_eq hbot))

theorem windingSpan_lowerSide_eq_bot_of_transverseSlice
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (hbot : Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) = ⊥) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (LowerSide ψ s c σ u) = ⊥ := by
  rw [lowerSide_eq_closedHalfDown, windingSpan_closedHalfDown_eq_halfDown_holds hT]
  exact le_bot_iff.mp (le_trans (Work.SurgeryInvariance.WindingSpan_mono (surface ψ)
    (Set.subset_union_right : HalfDown ψ s c σ u ⊆ Halves ψ s c σ u)) (le_of_eq hbot))

/-! ## The rank bound from the two gates -/

/-- **The two-gate rank bound**: two sets `A`, `B` carrying the connector-free datum, inessential,
with a two-piece intersection, and a functional killing the test loop through the gates, span at
most one dimension. -/
theorem two_gate_rank_le_one {P : Work.CoreTopology.ParamTorus} {A B : Set R3}
    (hAc : A ⊆ P.carrier) (hBc : B ⊆ P.carrier)
    (hApc : IsPathConnected A) (hBpc : IsPathConnected B)
    (hpart : AlternatingPartitionDataWeak P A B)
    (hVA : Work.SurgeryInvariance.WindingSpan P A = ⊥)
    (hVB : Work.SurgeryInvariance.WindingSpan P B = ⊥)
    {K₁ K₂ : Set R3} (hK₁c : K₁ ⊆ P.carrier) (hK₂c : K₂ ⊆ P.carrier)
    (hK₁pc : IsPathConnected K₁) (hK₂pc : IsPathConnected K₂)
    (hinter : A ∩ B = K₁ ∪ K₂)
    {a b : P.carrier} (ha : (a : R3) ∈ K₁) (hb : (b : R3) ∈ K₂)
    (cA : Path a b) (hcA : ∀ t : unitInterval, ((cA t) : R3) ∈ A)
    (cB : Path a b) (hcB : ∀ t : unitInterval, ((cB t) : R3) ∈ B) :
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (A ∪ B)) ≤ 1 := by
  obtain ⟨ψ', hψ'disp, hψ'ne⟩ := exists_killing_functional
    (Work.PinchLemma3.ClosedDiscA.psiDisp (LinearMap.id : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))
      (cA.trans cB.symm))
  have hψ'w : Work.PinchLemma3.ClosedDiscA.psiDisp ψ' (cA.trans cB.symm) = 0 := by
    rw [psiDisp_eq_apply_psiDisp_id]
    exact hψ'disp
  refine finrank_windingSpan_le_one_of_forall_psi_eq_zero hψ'ne fun γ hγ => ?_
  exact winding_psi_eq_zero_of_two_component_inter_of_weakPartition hAc hBc hApc hBpc hpart
    hVA hVB hK₁c hK₂c hK₁pc hK₂pc hinter ha hb cA hcA cB hcB ψ' hψ'w γ hγ

/-! ## The rank bound at a two-gate configuration of the pinch -/

/-- **The box region is at most one-dimensional when the slice has two gates.**  This is
`DropCase`'s conclusion at a `TransverseSlice` configuration: the two closed halves are inessential
(`TransverseSlice` + `W(Ω⁺ ∪ Ω⁻) = ⊥`), the connector-free datum is available (either directly or
through `FiniteCrossing`), and the two gates carry a test loop. -/
theorem finrank_Omega_le_one_of_two_gate
    (hApc : IsPathConnected (UpperSide ψ s c σ u)) (hBpc : IsPathConnected (LowerSide ψ s c σ u))
    (hpart : AlternatingPartitionDataWeak (surface ψ) (UpperSide ψ s c σ u)
      (LowerSide ψ s c σ u))
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (hbot : Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) = ⊥)
    {K₁ K₂ : Set R3} (hK₁c : K₁ ⊆ (surface ψ).carrier) (hK₂c : K₂ ⊆ (surface ψ).carrier)
    (hK₁pc : IsPathConnected K₁) (hK₂pc : IsPathConnected K₂)
    {a b : (surface ψ).carrier} (ha : (a : R3) ∈ K₁) (hb : (b : R3) ∈ K₂)
    (hinter : UpperSide ψ s c σ u ∩ LowerSide ψ s c σ u = K₁ ∪ K₂) :
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ)) ≤ 1 := by
  have hVA := windingSpan_upperSide_eq_bot_of_transverseSlice hT hbot
  have hVB := windingSpan_lowerSide_eq_bot_of_transverseSlice hT hbot
  have haAB : (a : R3) ∈ UpperSide ψ s c σ u ∩ LowerSide ψ s c σ u := by
    rw [hinter]; exact Or.inl ha
  have hbAB : (b : R3) ∈ UpperSide ψ s c σ u ∩ LowerSide ψ s c σ u := by
    rw [hinter]; exact Or.inr hb
  obtain ⟨cA, hcA⟩ := Work.PinchLemma3.ClosedDiscA.exists_carrierPath
    (P := surface ψ) (X := UpperSide ψ s c σ u)
    (upperSide_subset_carrier (ψ := ψ) (s := s) (c := c) (σ := σ) (u := u))
    (hApc.joinedIn (a : R3) haAB.1 (b : R3) hbAB.1)
  obtain ⟨cB, hcB⟩ := Work.PinchLemma3.ClosedDiscA.exists_carrierPath
    (P := surface ψ) (X := LowerSide ψ s c σ u)
    (lowerSide_subset_carrier (ψ := ψ) (s := s) (c := c) (σ := σ) (u := u))
    (hBpc.joinedIn (a : R3) haAB.2 (b : R3) hbAB.2)
  have hfr := two_gate_rank_le_one
    (upperSide_subset_carrier (ψ := ψ) (s := s) (c := c) (σ := σ) (u := u))
    (lowerSide_subset_carrier (ψ := ψ) (s := s) (c := c) (σ := σ) (u := u))
    hApc hBpc hpart hVA hVB hK₁c hK₂c hK₁pc hK₂pc hinter ha hb cA hcA cB hcB
  rwa [← Omega_eq_upperSide_union_lowerSide] at hfr

/-! ## The two-gate datum, and the residual -/

/-- **The two-gate datum of the pinch**: the slice is the union of two path-connected gates, the
two closed halves are path-connected, and the closed halves carry the connector-free
alternating-partition datum. -/
def TwoGateDatum (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Prop :=
  ∃ (K₁ K₂ : Set R3) (a b : (surface ψ).carrier),
    K₁ ⊆ (surface ψ).carrier ∧ K₂ ⊆ (surface ψ).carrier ∧
    IsPathConnected K₁ ∧ IsPathConnected K₂ ∧ (a : R3) ∈ K₁ ∧ (b : R3) ∈ K₂ ∧
    UpperSide ψ s c σ u ∩ LowerSide ψ s c σ u = K₁ ∪ K₂ ∧
    IsPathConnected (UpperSide ψ s c σ u) ∧ IsPathConnected (LowerSide ψ s c σ u) ∧
    AlternatingPartitionDataWeak (surface ψ) (UpperSide ψ s c σ u) (LowerSide ψ s c σ u)

/-- **`DropCase` from the two-gate datum.** -/
theorem dropCase_of_twoGateDatum
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → TwoGateDatum ψ s c σ u) :
    DropCase := by
  intro ψ s c σ u hT _hTa _hS _hZ hbot
  obtain ⟨K₁, K₂, a, b, hK₁c, hK₂c, hK₁pc, hK₂pc, ha, hb, hinter, hApc, hBpc, hpart⟩ :=
    h ψ s c σ u hT
  exact finrank_Omega_le_one_of_two_gate hApc hBpc hpart hT hbot hK₁c hK₂c hK₁pc hK₂pc
    ha hb hinter

/-- The same, in the vocabulary of the honest residual `KeyTameClosed`. -/
theorem keyTameClosed_of_twoGateDatum
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → TwoGateDatum ψ s c σ u) :
    KeyTameClosed :=
  keyTameClosed_of_dropCase (dropCase_of_twoGateDatum h)

/-- Pardon's Lemma 3 at the closed-tame configurations from the two-gate datum. -/
theorem bubbleHalf_of_twoGateDatum (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → TwoGateDatum ψ s c σ u) :
    ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → TameClosedSlice ψ s c σ u →
      ¬ (surface ψ).ContainsEssentialLoop (SphereTrace s c σ) →
      ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
      Work.BoxShrink.Bubble.BubbleHalf (surface ψ) s c σ u :=
  bubbleHalf_of_keyTameClosed hnice (keyTameClosed_of_twoGateDatum h)

/-- **The two-gate datum from the crossing data**: the connector-free datum is free from
`FiniteCrossing` (`alternatingPartitionDataWeak_of_finite_crossing`), and the gates are read off the
slice through `UpperSide ∩ LowerSide = Σ`. -/
theorem twoGateDatum_of_finiteCrossing_of_two_gates
    (hfin : FiniteCrossing ψ s c σ u)
    (hApc : IsPathConnected (UpperSide ψ s c σ u)) (hBpc : IsPathConnected (LowerSide ψ s c σ u))
    {K₁ K₂ : Set R3} (hK₁c : K₁ ⊆ (surface ψ).carrier) (hK₂c : K₂ ⊆ (surface ψ).carrier)
    (hK₁pc : IsPathConnected K₁) (hK₂pc : IsPathConnected K₂)
    (hinter : Sigma ψ s c σ u = K₁ ∪ K₂) :
    TwoGateDatum ψ s c σ u := by
  obtain ⟨a₀, ha₀⟩ := hK₁pc.nonempty
  obtain ⟨b₀, hb₀⟩ := hK₂pc.nonempty
  have ha : ((⟨a₀, hK₁c ha₀⟩ : (surface ψ).carrier) : R3) ∈ K₁ := ha₀
  have hb : ((⟨b₀, hK₂c hb₀⟩ : (surface ψ).carrier) : R3) ∈ K₂ := hb₀
  exact ⟨K₁, K₂, ⟨a₀, hK₁c ha₀⟩, ⟨b₀, hK₂c hb₀⟩, hK₁c, hK₂c, hK₁pc, hK₂pc, ha, hb,
    by rw [upperSide_inter_lowerSide]; exact hinter,
    hApc, hBpc, alternatingPartitionDataWeak_of_finite_crossing hfin⟩

/-- **`DropCase` from `FiniteCrossing` and a two-gate slice.** -/
theorem dropCase_of_finiteCrossing_of_two_gates
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u →
      FiniteCrossing ψ s c σ u ∧
      IsPathConnected (UpperSide ψ s c σ u) ∧ IsPathConnected (LowerSide ψ s c σ u) ∧
      ∃ (K₁ K₂ : Set R3), K₁ ⊆ (surface ψ).carrier ∧ K₂ ⊆ (surface ψ).carrier ∧
        IsPathConnected K₁ ∧ IsPathConnected K₂ ∧ Sigma ψ s c σ u = K₁ ∪ K₂) :
    DropCase :=
  dropCase_of_twoGateDatum fun ψ s c σ u hT => by
    obtain ⟨hfin, hApc, hBpc, K₁, K₂, hK₁c, hK₂c, hK₁pc, hK₂pc, hinter⟩ := h ψ s c σ u hT
    exact twoGateDatum_of_finiteCrossing_of_two_gates hfin hApc hBpc hK₁c hK₂c hK₁pc hK₂pc
      hinter

end

end Work.BoxShrink.PinchOff
