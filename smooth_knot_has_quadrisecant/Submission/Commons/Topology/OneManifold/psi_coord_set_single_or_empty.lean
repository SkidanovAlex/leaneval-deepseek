import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Analysis.Normed.Order.Lattice
import Submission.Commons.Topology.ConnectedReal.preconnected_inter_of_homeoUnit
import Submission.Commons.Analysis.RealIntervals.open_preconnected_nonempty_subset_unit_Ioo_shape

open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

noncomputable section

namespace Commons.Topology.OneManifold

/-- The open unit interval `(0,1)`, as a subtype of ℝ, is a connected space. -/
private lemma unit_interval_connected : ConnectedSpace {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} := by
  change ConnectedSpace (Set.Ioo (0 : ℝ) 1 : Set ℝ)
  exact Subtype.connectedSpace
    (isConnected_Ioo (a := (0 : ℝ)) (b := 1) (by norm_num : (0 : ℝ) < 1))

/-- A set `s : Set X` that is the image of the connected space `{x : X // x ∈ s}`
under the subtype inclusion is preconnected (as a subset of `X`). -/
private lemma isPreconnected_of_connected_subtype {X : Type*} [TopologicalSpace X]
    (s : Set X) (hconn : ConnectedSpace {x : X // x ∈ s}) : IsPreconnected s := by
  letI : ConnectedSpace {x : X // x ∈ s} := hconn
  have hrng : IsConnected (Set.range (fun u : {x : X // x ∈ s} => (u : X))) :=
    isConnected_range continuous_subtype_val
  have hrng_eq : Set.range (fun u : {x : X // x ∈ s} => (u : X)) = s := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact u.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hIs : IsConnected s := by
    rw [← hrng_eq]
    exact hrng
  exact hIs.isPreconnected

theorem psi_coord_set_single_or_empty {X : Type*} [TopologicalSpace X]
    (e : ({t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1}) ≃ₜ X)
    (P U : Set X) (κ : ({t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1}) ≃ₜ {x : X // x ∈ P})
    (ψ : ({t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1}) ≃ₜ {x : X // x ∈ U})
    (hPopen : IsOpen P) (hUopen : IsOpen U)
    (hPne : P.Nonempty) (hUne : U.Nonempty) :
    (((↑) : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} → ℝ) ''
      {t : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} | ((ψ t : {x : X // x ∈ U}) : X) ∈ P}) = ∅ ∨
      ∃ a b : ℝ, a < b ∧
        (((↑) : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} → ℝ) ''
          {t : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} | ((ψ t : {x : X // x ∈ U}) : X) ∈ P}) =
          Set.Ioo a b := by
  classical
  let S : Set {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} :=
    {t : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} | ((ψ t : {x : X // x ∈ U}) : X) ∈ P}
  let V : Set ℝ :=
    (((↑) : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} → ℝ) '' S)
  change V = ∅ ∨ ∃ a b : ℝ, a < b ∧ V = Set.Ioo a b
  by_cases hPU : (P ∩ U).Nonempty
  · right
    -- The unit interval type is connected, so P and U (homeomorphic images) are
    -- preconnected subsets of X; being open arcs in the interval-ambient X, their
    -- overlap is preconnected (and nonempty), hence connected.
    haveI hIconn : ConnectedSpace {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} := unit_interval_connected
    have hPconn : ConnectedSpace {x : X // x ∈ P} := (κ.connectedSpace_iff).mp hIconn
    have hUpconn : ConnectedSpace {x : X // x ∈ U} := (ψ.connectedSpace_iff).mp hIconn
    have hPpc : IsPreconnected P := isPreconnected_of_connected_subtype P hPconn
    have hUpc : IsPreconnected U := isPreconnected_of_connected_subtype U hUpconn
    have hPre : IsPreconnected (P ∩ U) := by
      exact Commons.Topology.ConnectedReal.preconnected_inter_of_homeoUnit
        (X := X) (Ω := (Set.univ : Set X))
        ((Homeomorph.Set.univ X).trans e.symm)
        (s := P) (t := U) hPopen hUopen (by intro x hx; trivial) (by intro x hx; trivial)
        hPpc hUpc hPU
    have hconn : ConnectedSpace {x : X // x ∈ P ∩ U} := Subtype.connectedSpace ⟨hPU, hPre⟩
    -- S (the ψ-coordinates of the overlap) is open, nonempty and preconnected
    have hSopen : IsOpen S := by
      have hfcont : Continuous
          (fun t : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} => ((ψ t : {x : X // x ∈ U}) : X)) :=
        continuous_subtype_val.comp ψ.continuous
      have hSdef : S = ((fun t : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} =>
            ((ψ t : {x : X // x ∈ U}) : X)) ⁻¹' P) := by
        ext t
        simp [S]
      rw [hSdef]
      exact hPopen.preimage hfcont
    have hSne : S.Nonempty := by
      rcases hPU with ⟨x, hxP, hxU⟩
      refine ⟨ψ.symm ⟨x, hxU⟩, ?_⟩
      have hxeq : ((ψ (ψ.symm ⟨x, hxU⟩) : {x : X // x ∈ U}) : X) = x := by
        rw [ψ.apply_symm_apply]
      simpa [S, hxeq] using hxP
    have hA_pc : IsPreconnected
        ({a : {x : X // x ∈ U} | (a : X) ∈ P} : Set {x : X // x ∈ U}) := by
      letI : ConnectedSpace {x : X // x ∈ P ∩ U} := hconn
      let g : {x : X // x ∈ P ∩ U} → X := fun c => (c : X)
      let h : {x : X // x ∈ P ∩ U} → {x : X // x ∈ U} :=
        Set.codRestrict g U (fun c => c.2.2)
      have hgcont : Continuous g := by
        simpa [g] using
          (continuous_subtype_val : Continuous
            (fun c : {x : X // x ∈ P ∩ U} => (c : X)))
      have hhcont : Continuous h := hgcont.codRestrict (fun c => c.2.2)
      have hrng : IsPreconnected (Set.range h) := isPreconnected_range hhcont
      have hrng_eq : Set.range h = {a : {x : X // x ∈ U} | (a : X) ∈ P} := by
        ext a
        constructor
        · rintro ⟨c, rfl⟩
          simpa [h, g] using c.2.1
        · intro ha
          refine ⟨⟨(a : X), ⟨ha, a.2⟩⟩, ?_⟩
          apply Subtype.ext
          simp [h, g]
      rw [← hrng_eq]
      exact hrng
    have hSpc : IsPreconnected S := by
      have hS_eq : S = ψ.symm '' ({a : {x : X // x ∈ U} | (a : X) ∈ P} : Set {x : X // x ∈ U}) := by
        ext t
        constructor
        · intro ht
          refine ⟨ψ t, ?_, ?_⟩
          · simpa [S] using ht
          · exact ψ.symm_apply_apply t
        · rintro ⟨a, haA, ht⟩
          have hψt : ψ t = a := by
            calc
              ψ t = ψ (ψ.symm a) := by rw [ht]
              _ = a := ψ.apply_symm_apply a
          simpa [S, hψt] using haA
      rw [hS_eq]
      exact hA_pc.image ψ.symm (ψ.symm.continuous.continuousOn)
    -- Push S to ℝ through the coordinate; classify.
    have hV01 : V ⊆ Set.Ioo (0 : ℝ) 1 := by
      rintro y ⟨t, htS, rfl⟩
      exact t.2
    have hVopen : IsOpen V := by
      have hOpenMap : IsOpenMap ((↑) : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} → ℝ) :=
        (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) 1)).isOpenMap_subtype_val
      have : IsOpen (((↑) : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} → ℝ) '' S) :=
        hOpenMap S hSopen
      simpa [V] using this
    have hVne : V.Nonempty := by
      have : (((↑) : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} → ℝ) '' S).Nonempty :=
        hSne.image ((↑) : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} → ℝ)
      simpa [V] using this
    have hVpc : IsPreconnected V := by
      have : IsPreconnected (((↑) : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} → ℝ) '' S) :=
        hSpc.image ((↑) : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} → ℝ)
          (continuous_subtype_val.continuousOn)
      simpa [V] using this
    rcases Commons.Analysis.RealIntervals.open_preconnected_nonempty_subset_unit_Ioo_shape
        hV01 hVopen hVne hVpc with ⟨a, b, hab, hVeq⟩
    exact ⟨a, b, hab, hVeq⟩
  · left
    have hPUeq : P ∩ U = ∅ := Set.not_nonempty_iff_eq_empty.mp hPU
    have hSempty : S = ∅ := by
      ext t
      constructor
      · intro ht
        have htP : ((ψ t : {x : X // x ∈ U}) : X) ∈ P := by simpa [S] using ht
        have htU : ((ψ t : {x : X // x ∈ U}) : X) ∈ U := (ψ t).2
        have hmem : ((ψ t : {x : X // x ∈ U}) : X) ∈ P ∩ U := ⟨htP, htU⟩
        rw [hPUeq] at hmem
        exact False.elim hmem
      · intro ht
        exact False.elim ht
    have hVempty : V = ∅ := by
      dsimp [V]
      rw [hSempty]
      exact Set.image_empty ((↑) : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} → ℝ)
    exact hVempty

end Commons.Topology.OneManifold
