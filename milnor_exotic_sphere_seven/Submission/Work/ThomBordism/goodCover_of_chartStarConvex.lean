import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.ThomBordism

theorem goodCover_of_chartStarConvex {X : Type*} [TopologicalSpace X]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (B : Fin m → Set X)
    (hdata : ∀ S : Finset (Fin m), S.Nonempty → (⋂ i ∈ S, B i).Nonempty →
      ∃ (φ : OpenPartialHomeomorph X E) (c : E),
        (∀ i ∈ S, B i ⊆ φ.source) ∧ (∀ i ∈ S, StarConvex ℝ c (φ '' B i))) :
    ∀ S : Finset (Fin m), S.Nonempty → (⋂ i ∈ S, B i).Nonempty →
      ContractibleSpace ↥(⋂ i ∈ S, B i) := by
  intro S hS hne
  obtain ⟨φ, c, hsub, hsc⟩ := hdata S hS hne
  obtain ⟨i₀, hi₀⟩ := hS
  set s : Set X := ⋂ i ∈ S, B i with hs
  set t : Set E := ⋂ i ∈ S, φ '' B i with ht
  have hs_sub : s ⊆ φ.source := by
    intro x hx
    rw [hs] at hx
    rw [Set.mem_iInter₂] at hx
    exact hsub i₀ hi₀ (hx i₀ hi₀)
  have ht_sub : t ⊆ φ.target := by
    intro y hy
    rw [ht] at hy
    rw [Set.mem_iInter₂] at hy
    obtain ⟨z, hz, hzy⟩ := hy i₀ hi₀
    rw [← hzy]
    exact φ.map_source (hsub i₀ hi₀ hz)
  have hsc_t : StarConvex ℝ c t := by
    rw [ht]
    apply starConvex_iInter
    intro i
    apply starConvex_iInter
    intro hi
    exact hsc i hi
  have mem_t_of : ∀ x : X, x ∈ s → φ x ∈ t := by
    intro x hx
    rw [hs] at hx
    rw [Set.mem_iInter₂] at hx
    rw [ht]
    rw [Set.mem_iInter₂]
    intro i hi
    exact ⟨x, hx i hi, rfl⟩
  have mem_s_of : ∀ y : E, y ∈ t → φ.symm y ∈ s := by
    intro y hy
    rw [ht] at hy
    rw [Set.mem_iInter₂] at hy
    rw [hs]
    rw [Set.mem_iInter₂]
    intro i hi
    obtain ⟨z, hz, hzy⟩ := hy i hi
    have hzsrc : z ∈ φ.source := hsub i hi hz
    rw [← hzy, φ.left_inv hzsrc]
    exact hz
  have ht_ne : t.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨φ x, mem_t_of x hx⟩
  have hφcont : Continuous (fun x : ↥s => φ (x : X)) :=
    φ.continuousOn.comp_continuous continuous_subtype_val (fun x => hs_sub x.2)
  have hφsymmcont : Continuous (fun y : ↥t => φ.symm (y : E)) :=
    φ.symm.continuousOn.comp_continuous continuous_subtype_val (fun y => ht_sub y.2)
  have hf : Continuous (fun x : ↥s => (⟨φ (x : X), mem_t_of x x.2⟩ : ↥t)) :=
    Continuous.subtype_mk hφcont (fun x => mem_t_of x x.2)
  have hg : Continuous (fun y : ↥t => (⟨φ.symm (y : E), mem_s_of y y.2⟩ : ↥s)) :=
    Continuous.subtype_mk hφsymmcont (fun y => mem_s_of y y.2)
  have hleft : Function.LeftInverse (fun y : ↥t => (⟨φ.symm (y : E), mem_s_of y y.2⟩ : ↥s))
      (fun x : ↥s => (⟨φ (x : X), mem_t_of x x.2⟩ : ↥t)) := by
    intro x
    apply Subtype.ext
    change φ.symm (φ (x : X)) = (x : X)
    exact φ.left_inv (hs_sub x.2)
  have hright : Function.RightInverse (fun y : ↥t => (⟨φ.symm (y : E), mem_s_of y y.2⟩ : ↥s))
      (fun x : ↥s => (⟨φ (x : X), mem_t_of x x.2⟩ : ↥t)) := by
    intro y
    apply Subtype.ext
    change φ (φ.symm (y : E)) = (y : E)
    exact φ.right_inv (ht_sub y.2)
  let e : ↥s ≃ ↥t :=
    { toFun := fun x => ⟨φ (x : X), mem_t_of x x.2⟩
      invFun := fun y => ⟨φ.symm (y : E), mem_s_of y y.2⟩
      left_inv := hleft
      right_inv := hright }
  let eH : ↥s ≃ₜ ↥t := Homeomorph.mk e hf hg
  exact (Homeomorph.contractibleSpace_iff eH).mpr (hsc_t.contractibleSpace ht_ne)

end Work.ThomBordism
