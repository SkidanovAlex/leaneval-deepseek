import Mathlib
import Submission.Work.Mostow.geodSetup

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

set_option linter.style.haveILetI false

/-- **The set of `Λ`-elements sending `z` into `F` is finite, of size at most `geodPtCard m Λ`.**

If every `γ ∈ Λ` with `γ • z ∈ F` has `γ γ₂⁻¹` in the setwise stabiliser of the standard geodesic
with trivial restriction to it, and if the pointwise stabiliser (inside `Λ`) of that geodesic is
finite, then the set of such `γ` is finite with at most `geodPtCard m Λ` elements: the map
`γ ↦ γ γ₂⁻¹` (right multiplication by `γ₂⁻¹` followed by the injection into `PO (1+m) 1`) is
injective into the pointwise stabiliser. -/
theorem geodPtFinset (m : ℕ) (hA : Submission.Mostow.POActionProp (1 + m))
    (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1)) (z : Submission.Mostow.E (1 + m))
    (F : Set (Submission.Mostow.E (1 + m))) (γ₂ : Λ)
    (hP : Finite {c : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1 //
      c ∈ Λ ∧ c ∈ Submission.Mostow.SetStabStd 1 m ∧ Submission.Mostow.resStd 1 m c = 1})
    (h : ∀ γ : Λ, (γ : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1) • z ∈ F →
          ((γ : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1) *
              (γ₂ : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1)⁻¹) ∈ Work.Mostow.geodStab m hA Λ ∧
          Submission.Mostow.resStd 1 m ((γ : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1) *
              (γ₂ : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1)⁻¹) = 1) :
    ∃ s : Finset Λ, s.card ≤ Work.Mostow.geodPtCard m Λ ∧
      ∀ γ : Λ, (γ : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1) • z ∈ F → γ ∈ s := by
  classical
  -- the pointwise stabiliser of the standard geodesic inside `Λ`, as a finite type
  haveI hPfin : Finite {c : PO (1 + m) 1 // c ∈ Λ ∧ c ∈ SetStabStd 1 m ∧ resStd 1 m c = 1} := hP
  haveI hPft : Fintype {c : PO (1 + m) 1 // c ∈ Λ ∧ c ∈ SetStabStd 1 m ∧ resStd 1 m c = 1} :=
    Fintype.ofFinite _
  -- the set of elements of `Λ` whose translate of `z` lands in `F`
  set Δs : Set Λ := {γ | (γ : PO (1 + m) 1) • z ∈ F} with hΔsdef
  have hφ : ∀ γ ∈ Δs, ((γ * γ₂⁻¹ : Λ) : PO (1 + m) 1) ∈
      {c : PO (1 + m) 1 | c ∈ Λ ∧ c ∈ SetStabStd 1 m ∧ resStd 1 m c = 1} := by
    intro γ hγ
    obtain ⟨h1, h2⟩ := h γ hγ
    have hcoe : ((γ * γ₂⁻¹ : Λ) : PO (1 + m) 1)
        = (γ : PO (1 + m) 1) * (γ₂ : PO (1 + m) 1)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
    have hin : ((γ * γ₂⁻¹ : Λ) : PO (1 + m) 1) ∈ Work.Mostow.geodStab m hA Λ := by
      rw [hcoe]; exact h1
    exact ⟨(γ * γ₂⁻¹ : Λ).2, (Subgroup.mem_inf.mp hin).2, by rw [hcoe]; exact h2⟩
  -- the injection `γ ↦ γ γ₂⁻¹` into the pointwise stabiliser
  let φ : Δs → {c : PO (1 + m) 1 // c ∈ Λ ∧ c ∈ SetStabStd 1 m ∧ resStd 1 m c = 1} :=
    fun γ => ⟨((γ.1 * γ₂⁻¹ : Λ) : PO (1 + m) 1), hφ γ.1 γ.2⟩
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h1 : ((a.1 * γ₂⁻¹ : Λ) : PO (1 + m) 1) = ((b.1 * γ₂⁻¹ : Λ) : PO (1 + m) 1) := by
      have hh := congrArg (fun t : {c : PO (1 + m) 1 // c ∈ Λ ∧ c ∈ SetStabStd 1 m ∧
          resStd 1 m c = 1} => (t : PO (1 + m) 1)) hab
      simpa only [φ] using hh
    have h2 : (((a.1 * γ₂⁻¹ : Λ)) : PO (1 + m) 1)
        = (a.1 : PO (1 + m) 1) * (γ₂ : PO (1 + m) 1)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
    have h3 : (((b.1 * γ₂⁻¹ : Λ)) : PO (1 + m) 1)
        = (b.1 : PO (1 + m) 1) * (γ₂ : PO (1 + m) 1)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
    have h4 : (a.1 : PO (1 + m) 1) = (b.1 : PO (1 + m) 1) := by
      have hh := h1
      rw [h2, h3] at hh
      calc (a.1 : PO (1 + m) 1)
          = (a.1 : PO (1 + m) 1) * 1 := (mul_one _).symm
        _ = (a.1 : PO (1 + m) 1) * ((γ₂ : PO (1 + m) 1)⁻¹ * (γ₂ : PO (1 + m) 1)) := by
              rw [inv_mul_cancel, mul_one]
        _ = ((a.1 : PO (1 + m) 1) * (γ₂ : PO (1 + m) 1)⁻¹) * (γ₂ : PO (1 + m) 1) :=
              (mul_assoc _ _ _).symm
        _ = ((b.1 : PO (1 + m) 1) * (γ₂ : PO (1 + m) 1)⁻¹) * (γ₂ : PO (1 + m) 1) := by rw [hh]
        _ = (b.1 : PO (1 + m) 1) := by rw [mul_assoc, inv_mul_cancel, mul_one]
    exact Subtype.ext (Subtype.ext h4)
  haveI hΔsFin : Finite Δs := Finite.of_injective φ hφinj
  haveI hΔsFt : Fintype Δs := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun γ : Δs => γ.1), ?_, ?_⟩
  · -- the cardinality bound
    have hcard : Nat.card Δs ≤ Nat.card
        {c : PO (1 + m) 1 // c ∈ Λ ∧ c ∈ SetStabStd 1 m ∧ resStd 1 m c = 1} :=
      Nat.card_le_card_of_injective φ hφinj
    have h1 : (Finset.univ.image (fun γ : Δs => γ.1)).card ≤ Nat.card Δs := by
      calc (Finset.univ.image (fun γ : Δs => γ.1)).card
          ≤ (Finset.univ : Finset Δs).card := Finset.card_image_le
        _ = Fintype.card Δs := Finset.card_univ
        _ = Nat.card Δs := Nat.card_eq_fintype_card.symm
    calc (Finset.univ.image (fun γ : Δs => γ.1)).card ≤ Nat.card Δs := h1
      _ ≤ Nat.card {c : PO (1 + m) 1 // c ∈ Λ ∧ c ∈ SetStabStd 1 m ∧ resStd 1 m c = 1} := hcard
      _ = Work.Mostow.geodPtCard m Λ := rfl
  · -- every element with `γ • z ∈ F` lies in the finset
    intro γ hγ
    exact Finset.mem_image.mpr ⟨⟨γ, hγ⟩, Finset.mem_univ _, rfl⟩

end Work.Mostow
