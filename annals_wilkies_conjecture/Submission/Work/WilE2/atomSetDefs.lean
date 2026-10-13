import Mathlib
import Submission.Work.WilE2.ComponentsDefs
import Submission.Work.WilE2.level_hitting
import Submission.Work.WilE2.posComps_finite
import Submission.Work.WilE2.VcbTopology

namespace Work.WilE2

open Classical
open WilkiesDesign WilkiesDesign.E

/-!
  ## The sign-assignment step (Gabrielov–Vorobjov Thm 3.4 / Thm 3.7): the single-atom set

  Given `VarietyBound F` (a polynomial bound on the number of components of the zero sets of
  families of EA functions, cut by the cube), one wants a polynomial bound on the number of
  components of a *basic* set

      `Z = cubeC k ∩ {f = 0 (f ∈ B.eqs)} ∩ {g > 0 (g ∈ B.pos)}`.

  This module builds the reduction: on the set where the *product* `G := ∏_{g ∈ B.pos} g` is
  positive, every positivity atom is non-zero, and its sign is constant on every connected
  component.  Hence `Z` is a union of connected components of the *single-atom* set
  `atomSet c B = cubeC k ∩ {B.eqs = 0} ∩ {G > 0}`, and a hitting set of the components of
  `atomSet c B` that is contained in `Z` is a hitting set of the components of `Z`
  (`hits_of_atomSet_hits`).
-/

noncomputable section

/-- The product `∏_{g ∈ B.pos} g` of the positivity atoms of a basic set. -/
noncomputable def posProd {k r : ℕ} (B : Basic k r) : EAPoly k r := B.pos.prod

@[simp] theorem posProd_nil {k r : ℕ} : posProd (⟨[], []⟩ : Basic k r) = 1 := by
  simp [posProd]

/-- Evaluation of the product of the positivity atoms. -/
theorem eaEval_posProd {k r : ℕ} (c : EAChain k r) (B : Basic k r) (x : Fin k → ℝ) :
    eaEval c (posProd B) x = (B.pos.map (fun g => eaEval c g x)).prod := by
  have h : eaEval c B.pos.prod x = (B.pos.map (fun g => eaEval c g x)).prod := by
    change MvPolynomial.eval (Sum.elim x (fun j => Real.exp (c.ell j x))) B.pos.prod = _
    rw [map_list_prod]
    rfl
  simpa [posProd] using h

/-- On a point where all positivity atoms are positive, their product is positive. -/
theorem posProd_pos_of_holds {k r : ℕ} (c : EAChain k r) (B : Basic k r) {x : Fin k → ℝ}
    (h : Basic.holds c B x) : 0 < eaEval c (posProd B) x := by
  rw [eaEval_posProd]
  exact List.prod_pos fun a ha => by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ha
    exact h.2 g hg

/-- If a positivity atom vanishes somewhere, the product vanishes there. -/
theorem posProd_eq_zero_of_mem {k r : ℕ} (c : EAChain k r) (B : Basic k r) {x : Fin k → ℝ}
    {g : EAPoly k r} (hg : g ∈ B.pos) (hx : eaEval c g x = 0) :
    eaEval c (posProd B) x = 0 := by
  rw [eaEval_posProd]
  refine List.prod_eq_zero ?_
  rw [← hx]
  exact List.mem_map_of_mem (f := fun g => eaEval c g x) hg

/-! ## §1.  Small evaluation lemmas -/

theorem eaEval_sub {k r : ℕ} (c : EAChain k r) (P Q : EAPoly k r) (x : Fin k → ℝ) :
    eaEval c (P - Q) x = eaEval c P x - eaEval c Q x := by
  simp only [eaEval, map_sub]

theorem eaEval_C {k r : ℕ} (c : EAChain k r) (a : ℝ) (x : Fin k → ℝ) :
    eaEval c (MvPolynomial.C a) x = a := by
  simp only [eaEval, MvPolynomial.eval_C]

theorem eaEval_one {k r : ℕ} (c : EAChain k r) (x : Fin k → ℝ) :
    eaEval c (1 : EAPoly k r) x = 1 := by
  simp only [eaEval, map_one]

/-! ## §2.  The single-atom set -/

/-- The "single atom" basic set: the cube, the equations and the single strict inequality
`∏ pos > 0`.  Its components are (essentially) the components of the basic set. -/
def atomSet {k r : ℕ} (c : EAChain k r) (B : Basic k r) : Set (Fin k → ℝ) :=
  cubeC k ∩ {x | (∀ f ∈ B.eqs, eaEval c f x = 0) ∧ 0 < eaEval c (posProd B) x}

theorem mem_atomSet {k r : ℕ} {c : EAChain k r} {B : Basic k r} {x : Fin k → ℝ} :
    x ∈ atomSet c B ↔
      x ∈ cubeC k ∧ (∀ f ∈ B.eqs, eaEval c f x = 0) ∧ 0 < eaEval c (posProd B) x :=
  Iff.rfl

/-- The basic set is contained in the single-atom set. -/
theorem holds_subset_atomSet {k r : ℕ} (c : EAChain k r) (B : Basic k r) :
    cubeC k ∩ {x | Basic.holds c B x} ⊆ atomSet c B := by
  rintro x ⟨hxc, hxe, hxp⟩
  exact ⟨hxc, hxe, posProd_pos_of_holds c B ⟨hxe, hxp⟩⟩

/-- On the single-atom set no positivity atom vanishes. -/
theorem atom_ne_zero_of_mem_atomSet {k r : ℕ} {c : EAChain k r} {B : Basic k r}
    {x : Fin k → ℝ} (hx : x ∈ atomSet c B) {g : EAPoly k r} (hg : g ∈ B.pos) :
    eaEval c g x ≠ 0 := by
  intro h0
  have h := hx.2.2
  rw [posProd_eq_zero_of_mem c B hg h0] at h
  exact lt_irrefl 0 h

/-- **The sign of a positivity atom is constant on the components of the single-atom set.** -/
theorem atom_positive_of_mem_component {k r : ℕ} (c : EAChain k r) (B : Basic k r)
    {x y : Fin k → ℝ} (hx : x ∈ cubeC k ∩ {x | Basic.holds c B x})
    (hy : y ∈ connectedComponentIn (atomSet c B) x) {g : EAPoly k r} (hg : g ∈ B.pos) :
    0 < eaEval c g y := by
  have hxA : x ∈ atomSet c B := holds_subset_atomSet c B hx
  have hD : connectedComponentIn (atomSet c B) x ⊆ atomSet c B :=
    connectedComponentIn_subset _ _
  have hDpc : IsPreconnected (connectedComponentIn (atomSet c B) x) :=
    isPreconnected_connectedComponentIn
  have hcont : ContinuousOn (fun w : Fin k → ℝ => eaEval c g w)
      (connectedComponentIn (atomSet c B) x) :=
    (Work.WilE5.Flat.continuous_eaEval c g).continuousOn
  by_contra hneg
  push Not at hneg
  have hxpos : 0 < eaEval c g x := hx.2.2 g hg
  have hIVT := hDpc.intermediate_value hy (mem_connectedComponentIn hxA) hcont
  have h0mem : (0 : ℝ) ∈ Set.Icc (eaEval c g y) (eaEval c g x) :=
    ⟨hneg, le_of_lt hxpos⟩
  obtain ⟨w, hw, hw0⟩ := hIVT h0mem
  exact atom_ne_zero_of_mem_atomSet (hD hw) hg hw0

/-- **The reduction.**  A hitting set of the components of the single-atom set `atomSet c B` yields
a hitting set of the components of the basic set, contained in the basic set. -/
theorem hits_of_atomSet_hits {k r : ℕ} (c : EAChain k r) (B : Basic k r)
    (s : Finset (Fin k → ℝ)) (hs : (↑s : Set (Fin k → ℝ)) ⊆ atomSet c B)
    (hhits : ∀ x ∈ atomSet c B, ∃ y ∈ s,
      connectedComponentIn (atomSet c B) x = connectedComponentIn (atomSet c B) y) :
    ∃ s' : Finset (Fin k → ℝ), s'.card ≤ s.card ∧
      (↑s' : Set (Fin k → ℝ)) ⊆ cubeC k ∩ {x | Basic.holds c B x} ∧
      ∀ x ∈ cubeC k ∩ {x | Basic.holds c B x}, ∃ y ∈ s',
        connectedComponentIn (cubeC k ∩ {x | Basic.holds c B x}) x =
        connectedComponentIn (cubeC k ∩ {x | Basic.holds c B x}) y := by
  classical
  set Z : Set (Fin k → ℝ) := cubeC k ∩ {x | Basic.holds c B x} with hZ
  refine ⟨s.filter (fun y => y ∈ Z), Finset.card_filter_le _ _, ?_, ?_⟩
  · intro y hy
    exact (Finset.mem_filter.mp hy).2
  · intro x hx
    have hxA : x ∈ atomSet c B := holds_subset_atomSet c B hx
    obtain ⟨y, hys, hyc⟩ := hhits x hxA
    have hyA : y ∈ atomSet c B := hs hys
    have hyx : y ∈ connectedComponentIn (atomSet c B) x := by
      rw [hyc]; exact mem_connectedComponentIn hyA
    have hcomp : connectedComponentIn (atomSet c B) x ⊆ Z := by
      intro w hw
      obtain ⟨hwc, hwe, _⟩ := mem_atomSet.mp (connectedComponentIn_subset (atomSet c B) x hw)
      refine ⟨hwc, hwe, fun g hg => atom_positive_of_mem_component c B hx hw hg⟩
    have hyZ : y ∈ Z := hcomp hyx
    refine ⟨y, Finset.mem_filter.mpr ⟨hys, hyZ⟩, ?_⟩
    have hxZ : x ∈ Z := hx
    have hZA : Z ⊆ atomSet c B := holds_subset_atomSet c B
    have hcompY : connectedComponentIn (atomSet c B) y ⊆ Z := hyc ▸ hcomp
    have eqx : connectedComponentIn Z x = connectedComponentIn (atomSet c B) x :=
      Set.Subset.antisymm
        ((isPreconnected_connectedComponentIn (F := Z) (x := x)).subset_connectedComponentIn
          (mem_connectedComponentIn hxZ) ((connectedComponentIn_subset Z x).trans hZA))
        ((isPreconnected_connectedComponentIn (F := atomSet c B) (x := x)).subset_connectedComponentIn
          (mem_connectedComponentIn hxA) hcomp)
    have eqy : connectedComponentIn Z y = connectedComponentIn (atomSet c B) y :=
      Set.Subset.antisymm
        ((isPreconnected_connectedComponentIn (F := Z) (x := y)).subset_connectedComponentIn
          (mem_connectedComponentIn hyZ) ((connectedComponentIn_subset Z y).trans hZA))
        ((isPreconnected_connectedComponentIn (F := atomSet c B) (x := y)).subset_connectedComponentIn
          (mem_connectedComponentIn hyA) hcompY)
    rw [eqx, eqy, hyc]

end

end Work.WilE2
