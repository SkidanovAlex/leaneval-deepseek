import Mathlib
import Submission.Work.Mostow.thickDefs
import Submission.Work.Mostow.QIDefs

/-!
# Basic properties of the injectivity radius `thick`

`thick Γ u = ⨅ {γ : Γ // γ ≠ 1}, hdist u (γ • u)` is the injectivity radius of the
subgroup `Γ` at `u`.  This file proves the four elementary facts used everywhere:

* it is a lower bound for every nontrivial displacement (`thick_le_hdist`);
* it is the *greatest* such lower bound (`le_thick`);
* it is `Γ`-invariant (`thick_smul`);
* it is `2`-Lipschitz (`abs_thick_sub_le`).

The only hypothesis needed is that `Γ` is nontrivial (otherwise the infimum is `sInf ∅ = 0` and
the second and fourth statements can fail).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-- The index set of the infimum defining `thick` is nonempty for a nontrivial subgroup. -/
lemma thick_nonempty {Γ : Subgroup (PO n 1)} (hnt : ∃ γ : Γ, γ ≠ 1) :
    Nonempty {γ : Γ // γ ≠ 1} :=
  ⟨⟨hnt.choose, hnt.choose_spec⟩⟩

/-- `thick Γ u` is bounded below: every displacement is nonnegative. -/
lemma thick_bddBelow {Γ : Subgroup (PO n 1)} (hI : HypIsometryProp n) (u : E n) :
    BddBelow (Set.range (fun γ : {γ : Γ // γ ≠ 1} => hdist u ((γ : PO n 1) • u))) := by
  refine ⟨0, ?_⟩
  intro x hx
  obtain ⟨γ, rfl⟩ := hx
  exact hI.1 u _

/-- `thick Γ u` is a lower bound for the displacement of every nontrivial element. -/
lemma thick_le_hdist {Γ : Subgroup (PO n 1)} (hI : HypIsometryProp n) (u : E n)
    (γ : Γ) (hγ : γ ≠ 1) : thick Γ u ≤ hdist u ((γ : PO n 1) • u) :=
  ciInf_le (thick_bddBelow (n := n) hI u) ⟨γ, hγ⟩

/-- `thick Γ u` is the greatest lower bound of the nontrivial displacements. -/
lemma le_thick {Γ : Subgroup (PO n 1)} (hnt : ∃ γ : Γ, γ ≠ 1) (u : E n) (c : ℝ)
    (hc : ∀ (γ : Γ), γ ≠ 1 → c ≤ hdist u ((γ : PO n 1) • u)) : c ≤ thick Γ u := by
  haveI : Nonempty {γ : Γ // γ ≠ 1} := thick_nonempty hnt
  exact le_ciInf (fun x => hc x.1 x.2)

/-- Conjugation acts on `γ • u` in the expected way. -/
lemma conj_smul (hA : POActionProp n) {Γ : Subgroup (PO n 1)} (γ δ : Γ) (u : E n) :
    ((γ * δ * γ⁻¹ : Γ) : PO n 1) • ((γ : PO n 1) • u) = (γ : PO n 1) • ((δ : PO n 1) • u) := by
  have hA' : POBasic n := POBasic.ofProp hA
  have hcoe : (((γ * δ * γ⁻¹ : Γ)) : PO n 1) =
      (γ : PO n 1) * (δ : PO n 1) * (γ : PO n 1)⁻¹ := by
    simp [Subgroup.coe_mul, Subgroup.coe_inv]
  have h3 : (γ : PO n 1)⁻¹ • ((γ : PO n 1) • u) = u := by
    rw [← hA'.mul_smul, inv_mul_cancel, hA'.one_smul]
  rw [hcoe]
  simp only [hA'.mul_smul, h3]

/-- The displacement of `δ` is the displacement of the conjugate `γ δ γ⁻¹` at `γ • u`. -/
lemma hdist_conj_thick_basic (hA : POActionProp n) (hI : HypIsometryProp n) {Γ : Subgroup (PO n 1)}
    (γ δ : Γ) (u : E n) :
    hdist u ((δ : PO n 1) • u) =
      hdist ((γ : PO n 1) • u) (((γ * δ * γ⁻¹ : Γ) : PO n 1) • ((γ : PO n 1) • u)) := by
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  calc hdist u ((δ : PO n 1) • u)
      = hdist ((γ : PO n 1) • u) ((γ : PO n 1) • ((δ : PO n 1) • u)) :=
        (hI'.isom_smul (γ : PO n 1) u ((δ : PO n 1) • u)).symm
    _ = hdist ((γ : PO n 1) • u) (((γ * δ * γ⁻¹ : Γ) : PO n 1) • ((γ : PO n 1) • u)) := by
        rw [conj_smul hA γ δ u]

/-- The displacement at `γ • u` of `δ` is the displacement at `u` of the conjugate
`γ⁻¹ δ γ`. -/
lemma hdist_conj_inv (hA : POActionProp n) (hI : HypIsometryProp n) {Γ : Subgroup (PO n 1)}
    (γ δ : Γ) (u : E n) :
    hdist ((γ : PO n 1) • u) ((δ : PO n 1) • ((γ : PO n 1) • u))
      = hdist u (((γ⁻¹ * δ * γ : Γ) : PO n 1) • u) := by
  have hA' : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  have h3 : (γ : PO n 1)⁻¹ • ((γ : PO n 1) • u) = u := by
    rw [← hA'.mul_smul, inv_mul_cancel, hA'.one_smul]
  have h4 : (γ : PO n 1)⁻¹ • ((δ : PO n 1) • ((γ : PO n 1) • u))
      = ((γ⁻¹ * δ * γ : Γ) : PO n 1) • u := by
    have hcoe : (((γ⁻¹ * δ * γ : Γ)) : PO n 1) =
        (γ : PO n 1)⁻¹ * (δ : PO n 1) * (γ : PO n 1) := by
      simp [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcoe]
    simp only [hA'.mul_smul]
  calc hdist ((γ : PO n 1) • u) ((δ : PO n 1) • ((γ : PO n 1) • u))
      = hdist ((γ : PO n 1)⁻¹ • ((γ : PO n 1) • u))
          ((γ : PO n 1)⁻¹ • ((δ : PO n 1) • ((γ : PO n 1) • u))) :=
        (hI'.isom_smul (γ : PO n 1)⁻¹ ((γ : PO n 1) • u)
          ((δ : PO n 1) • ((γ : PO n 1) • u))).symm
    _ = hdist u (((γ⁻¹ * δ * γ : Γ) : PO n 1) • u) := by rw [h3, h4]

/-- `thick` is invariant under the action of `Γ`. -/
lemma thick_smul (hA : POActionProp n) (hI : HypIsometryProp n) {Γ : Subgroup (PO n 1)}
    (hnt : ∃ γ : Γ, γ ≠ 1) (γ : Γ) (u : E n) :
    thick Γ ((γ : PO n 1) • u) = thick Γ u := by
  haveI : Nonempty {γ : Γ // γ ≠ 1} := thick_nonempty hnt
  refine le_antisymm ?_ ?_
  · refine le_ciInf (fun δ => ?_)
    have hne : γ * δ * γ⁻¹ ≠ 1 := by
      intro hc
      refine δ.2 ?_
      have h1 : γ⁻¹ * (γ * (δ : Γ) * γ⁻¹) * γ = (δ : Γ) := by group
      have h2 := congrArg (fun x : Γ => γ⁻¹ * x * γ) hc
      rw [h1] at h2
      simpa using h2
    calc thick Γ ((γ : PO n 1) • u)
        ≤ hdist ((γ : PO n 1) • u) (((γ * δ * γ⁻¹ : Γ) : PO n 1) • ((γ : PO n 1) • u)) :=
          thick_le_hdist hI _ _ hne
      _ = hdist u ((δ : PO n 1) • u) := (hdist_conj_thick_basic hA hI γ δ u).symm
  · refine le_ciInf (fun δ => ?_)
    have hne : γ⁻¹ * δ * γ ≠ 1 := by
      intro hc
      refine δ.2 ?_
      have h1 : γ * (γ⁻¹ * (δ : Γ) * γ) * γ⁻¹ = (δ : Γ) := by group
      have h2 := congrArg (fun x : Γ => γ * x * γ⁻¹) hc
      rw [h1] at h2
      simpa using h2
    calc thick Γ u
        ≤ hdist u (((γ⁻¹ * δ * γ : Γ) : PO n 1) • u) := thick_le_hdist hI _ _ hne
      _ = hdist ((γ : PO n 1) • u) ((δ : PO n 1) • ((γ : PO n 1) • u)) :=
          (hdist_conj_inv hA hI γ δ u).symm

/-- `thick` is `2`-Lipschitz in the point. -/
lemma abs_thick_sub_le (_hA : POActionProp n) (hI : HypIsometryProp n) {Γ : Subgroup (PO n 1)}
    (hnt : ∃ γ : Γ, γ ≠ 1) (u v : E n) :
    |thick Γ u - thick Γ v| ≤ 2 * hdist u v := by
  haveI : Nonempty {γ : Γ // γ ≠ 1} := thick_nonempty hnt
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  have key : ∀ u v : E n, thick Γ u ≤ thick Γ v + 2 * hdist u v := by
    intro u v
    have h1 : thick Γ u - 2 * hdist u v ≤ thick Γ v := by
      refine le_ciInf (fun δ => ?_)
      have hδ : hdist u ((δ : PO n 1) • u) ≤ hdist v ((δ : PO n 1) • v) + 2 * hdist u v := by
        have ht1 := hI'.triangle u v ((δ : PO n 1) • u)
        have ht2 := hI'.triangle v ((δ : PO n 1) • v) ((δ : PO n 1) • u)
        have hiso := hI'.isom_smul (δ : PO n 1) v u
        have hsym := hI'.symm u v
        linarith
      have h2 := thick_le_hdist hI u δ.1 δ.2
      linarith
    linarith
  have hu := key u v
  have hv := key v u
  have hsv := hI'.symm u v
  rw [abs_le]
  constructor <;> linarith

theorem thick_basic {n : ℕ} (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    {Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)} (hnt : ∃ γ : Γ, γ ≠ 1) :
    (∀ (u : Submission.Mostow.E n) (γ : Γ), γ ≠ 1 →
        Work.Mostow.thick Γ u ≤ Submission.Mostow.hdist u
          ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u)) ∧
    (∀ (u : Submission.Mostow.E n) (c : ℝ),
        (∀ (γ : Γ), γ ≠ 1 → c ≤ Submission.Mostow.hdist u
          ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u)) →
        c ≤ Work.Mostow.thick Γ u) ∧
    (∀ (γ : Γ) (u : Submission.Mostow.E n),
        Work.Mostow.thick Γ ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u)
          = Work.Mostow.thick Γ u) ∧
    (∀ u v : Submission.Mostow.E n,
        |Work.Mostow.thick Γ u - Work.Mostow.thick Γ v|
          ≤ 2 * Submission.Mostow.hdist u v) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u γ hγ
    exact thick_le_hdist hI u γ hγ
  · intro u c hc
    exact le_thick hnt u c hc
  · intro γ u
    exact thick_smul hA hI hnt γ u
  · intro u v
    exact abs_thick_sub_le hA hI hnt u v

end

end Work.Mostow
