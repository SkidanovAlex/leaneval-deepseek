import Submission.Work.EQ.UnivCover.Defs

/-!
# The sheets of the universal cover are graphs over disc-like sets

Over a disc-like set `V`, the sheet through a point `e` meets every fibre exactly once: it is the
graph of a section `V → UC x₀`.  In particular distinct sheets over `V` are disjoint.
-/

set_option autoImplicit false
open _root_.Topology
open scoped Topology
open Work.EQ.UnivCover

namespace Work.EQ.UnivCover

variable {X : Type*} [TopologicalSpace X] {x₀ : X}

/-- Two paths in a disc-like set with the same endpoints have the same class. -/
theorem mk_eq_mk_of_isDiscLike {V : Set X} (hV : IsDiscLike V) {a b : X}
    (γ₁ γ₂ : Path a b) (h₁ : ∀ t, γ₁ t ∈ V) (h₂ : ∀ t, γ₂ t ∈ V) :
    Path.Homotopic.Quotient.mk γ₁ = Path.Homotopic.Quotient.mk γ₂ := by
  have haV : a ∈ V := by have := h₁ 0; simpa using this
  have hloop : (γ₁.trans γ₂.symm).Homotopic (Path.refl a) := by
    refine hV.simply_connected haV _ fun t => ?_
    have ht : (γ₁.trans γ₂.symm) t ∈ Set.range (γ₁.trans γ₂.symm) := ⟨t, rfl⟩
    rw [Path.trans_range, Path.symm_range, Set.mem_union] at ht
    rcases ht with ⟨s, hs⟩ | ⟨s, hs⟩
    · rw [← hs]; exact h₁ s
    · rw [← hs]; exact h₂ s
  have hq : Path.Homotopic.Quotient.mk (γ₁.trans γ₂.symm)
      = Path.Homotopic.Quotient.mk (Path.refl a) := Quotient.sound hloop
  rw [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.mk_refl] at hq
  have h := congrArg (fun q => q.trans (Path.Homotopic.Quotient.mk γ₂)) hq
  simp only [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans, Path.Homotopic.Quotient.trans_refl] at h
  exact h

/-- **Uniqueness in a sheet.** Over a disc-like set, a sheet meets every fibre at most once, and
distinct sheets over it are disjoint. -/
theorem UC_sheet_unique {V : Set X} (hV : IsDiscLike V) :
    (∀ {e e₁ e₂ : UC x₀}, e₁ ∈ UC.sheet e V → e₂ ∈ UC.sheet e V → e₁.pt = e₂.pt → e₁ = e₂) ∧
    (∀ {e₁ e₂ e' : UC x₀}, e' ∈ UC.sheet e₁ V → e' ∈ UC.sheet e₂ V → e₁.pt = e₂.pt → e₁ = e₂) := by
  constructor
  · intro e e₁ e₂ h₁ h₂ hpt
    obtain ⟨p₁, c₁⟩ := e₁
    obtain ⟨p₂, c₂⟩ := e₂
    simp only [UC.mem_sheet_iff] at h₁ h₂ ⊢
    obtain ⟨-, δ₁, hδ₁, hc₁⟩ := h₁
    obtain ⟨-, δ₂, hδ₂, hc₂⟩ := h₂
    have hpt' : p₁ = p₂ := hpt
    subst hpt'
    rw [hc₁, hc₂, mk_eq_mk_of_isDiscLike hV δ₁ δ₂ hδ₁ hδ₂]
  · intro e₁ e₂ e' h₁ h₂ he
    obtain ⟨p₁, c₁⟩ := e₁
    obtain ⟨p₂, c₂⟩ := e₂
    simp only [UC.mem_sheet_iff] at h₁ h₂
    obtain ⟨-, δ₁, hδ₁, hc₁⟩ := h₁
    obtain ⟨-, δ₂, hδ₂, hc₂⟩ := h₂
    have he' : p₁ = p₂ := he
    subst he'
    have hδ : Path.Homotopic.Quotient.mk δ₁ = Path.Homotopic.Quotient.mk δ₂ :=
      mk_eq_mk_of_isDiscLike hV δ₁ δ₂ hδ₁ hδ₂
    have hce : c₁.trans (Path.Homotopic.Quotient.mk δ₁)
        = c₂.trans (Path.Homotopic.Quotient.mk δ₂) := by rw [← hc₁, ← hc₂]
    have hcl : c₁ = c₂ := by
      have hthis := congrArg (fun q => q.trans ((Path.Homotopic.Quotient.mk δ₂).symm)) hce
      rw [hδ] at hthis
      simpa only [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
        Path.Homotopic.Quotient.trans_refl] using hthis
    rw [hcl]

/-- **Existence in a sheet.** Over a disc-like set, a sheet through a point over `V` meets every
fibre over `V`. -/
theorem UC_sheet_exists {V : Set X} (hV : IsDiscLike V) {e : UC x₀} (heV : e.pt ∈ V) {y : X}
    (hy : y ∈ V) : ∃ e' : UC x₀, e' ∈ UC.sheet e V ∧ e'.pt = y := by
  obtain ⟨δ, hδ⟩ := hV.path_connected heV hy
  exact ⟨⟨y, e.cls.trans (Path.Homotopic.Quotient.mk δ)⟩, ⟨hy, δ, hδ, rfl⟩, rfl⟩

end Work.EQ.UnivCover
