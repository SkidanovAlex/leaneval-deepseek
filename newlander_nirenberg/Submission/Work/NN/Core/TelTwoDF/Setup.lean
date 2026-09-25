/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The geometric setup of the parameterised `(0,2)`-telescoping

This file fixes the geometry of the parameterised telescoping used for the lemma
`Work.NN.Core.exists_telTwoDF`: from the two multi-radii `ρ' < ρ` it produces

* a `Geom n` structure with radii `e < a < b ≤ r/2` chosen as explicit fractions of the gap
  `ρ - ρ'`,
* a *data* multi-radius `C` with `b < C < ρ`, and
* a smooth bump `χ` which equals `1` on the open polydisc `polydisc 0 C` and whose topological
  support is contained in `polydisc 0 ρ`.

It also defines the linear map `chiMul χ` (multiplication of a family of functions by `χ`), so
that the solution operator of `exists_telTwoDF` can be written as `S2 G ∘ chiMul χ`.
-/
import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.sharpCut
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.TelTwoDF.Defs
import Submission.Work.NN.Core.TelTwoDF.Solves
import Submission.Work.NN.Core.TelTwoDF.S2Bound
import Submission.Work.NN.Core.TelTwoDF.dbarTransform_Eset_le
import Submission.Work.NN.Core.TelTwoDF.holderNorm_bump_mul_le
import Submission.Work.NN.Core.TelTwoDF.contDiff_mul_of_contDiffOn_of_tsupport_subset
import Submission.Work.NN.Core.exists_contDiff_bump_of_isCompact_subset

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Core.TelTwoDF

open Work.NN.Core (Cn)

variable {n : ℕ}

/-! ## Multiplication by a bump -/

/-- Multiplication of a family of functions on `ℂⁿ` by a fixed bump `χ`, as a linear map. -/
def chiMul (χ : Cn n → ℂ) : (Fin n → Fin n → Cn n → ℂ) →ₗ[ℝ] (Fin n → Fin n → Cn n → ℂ) where
  toFun η := fun i l z => χ z * η i l z
  map_add' η η' := by
    funext i l z
    simp only [Pi.add_apply]
    ring
  map_smul' c η := by
    funext i l z
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [Complex.real_smul, Complex.real_smul]
    ring

@[simp] lemma chiMul_apply (χ : Cn n → ℂ) (η : Fin n → Fin n → Cn n → ℂ) (i l : Fin n)
    (z : Cn n) : chiMul χ η i l z = χ z * η i l z := rfl

/-- The closed polydisc `{z | ∀ k, ‖z k‖ ≤ C k}` is compact. -/
lemma isCompact_closedPolydisc (C : Fin n → ℝ) :
    IsCompact {z : Cn n | ∀ k, ‖z k‖ ≤ C k} := by
  have h1 : {z : Cn n | ∀ k, ‖z k‖ ≤ C k}
      = Set.pi univ (fun k => Metric.closedBall (0 : ℂ) (C k)) := by
    ext z; simp [Metric.mem_closedBall, dist_eq_norm]
  rw [h1]
  exact isCompact_univ_pi (fun k => isCompact_closedBall 0 (C k))

/-! ## The geometric setup -/

/-- From multi-radii `0 < ρ' < ρ` produce the geometry `e < a < b ≤ r/2` of the parameterised
telescoping, a data radius `b < C < ρ`, and a bump `χ` which is `1` on the open polydisc
`polydisc 0 C` and whose topological support is contained in `polydisc 0 ρ`. -/
theorem exists_setup {n : ℕ} {ρ ρ' : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hρ' : ∀ j, 0 < ρ' j)
    (hlt : ∀ j, ρ' j < ρ j) :
    ∃ (G : Geom n) (C : Fin n → ℝ) (χ : Cn n → ℂ),
      (∀ j, ρ' j < G.e j) ∧ (∀ j, G.b j < C j) ∧ (∀ j, C j < ρ j) ∧
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Work.CR.Flat.polydisc (0 : Cn n) ρ ∧
      (∀ z : Cn n, (∀ j, ‖z j‖ < C j) → χ z = 1) := by
  have hu : ∀ k, 0 < ρ k - ρ' k := fun k => sub_pos.mpr (hlt k)
  -- the radii of the telescoping
  set e : Fin n → ℝ := fun k => ρ' k + (ρ k - ρ' k) / 8 with hedef
  set a : Fin n → ℝ := fun k => ρ' k + (ρ k - ρ' k) / 4 with hadef
  set b : Fin n → ℝ := fun k => ρ' k + 3 * (ρ k - ρ' k) / 8 with hbdef
  set r : Fin n → ℝ := fun k => 2 * b k with hrdef
  set C : Fin n → ℝ := fun k => ρ' k + 7 * (ρ k - ρ' k) / 8 with hCdef
  have hratio : ∀ k, 0 < ρ k - ρ' k := hu
  have e_form : ∀ k, e k = ρ' k + (ρ k - ρ' k) / 8 := fun k => by simp only [hedef]
  have a_form : ∀ k, a k = ρ' k + (ρ k - ρ' k) / 4 := fun k => by simp only [hadef]
  have b_form : ∀ k, b k = ρ' k + 3 * (ρ k - ρ' k) / 8 := fun k => by simp only [hbdef]
  have r_form : ∀ k, r k = 2 * b k := fun k => by simp only [hrdef]
  have C_form : ∀ k, C k = ρ' k + 7 * (ρ k - ρ' k) / 8 := fun k => by simp only [hCdef]
  have he_pos : ∀ k, 0 < e k := fun k => by rw [e_form k]; nlinarith [hρ' k, hu k]
  have ha_pos : ∀ k, 0 < a k := fun k => by rw [a_form k]; nlinarith [hρ' k, hu k]
  have hea : ∀ k, e k < a k := fun k => by
    rw [e_form k, a_form k]; nlinarith [hu k]
  have hab : ∀ k, a k < b k := fun k => by
    rw [a_form k, b_form k]; nlinarith [hu k]
  have hr_pos : ∀ k, 0 < r k := fun k => by
    rw [r_form k, b_form k]; nlinarith [hρ' k, hu k]
  have hbr : ∀ k, b k ≤ r k / 2 := fun k => by rw [r_form k]; linarith
  -- the data radius
  have hbC : ∀ k, b k < C k := fun k => by
    rw [b_form k, C_form k]; nlinarith [hu k]
  have hCρ : ∀ k, C k < ρ k := fun k => by
    rw [C_form k]; nlinarith [hρ' k, hlt k]
  have hCpos : ∀ k, 0 < C k := fun k => by
    rw [C_form k]; nlinarith [hρ' k, hu k]
  -- the bump
  have hKU : {z : Cn n | ∀ k, ‖z k‖ ≤ C k} ⊆ Work.CR.Flat.polydisc (0 : Cn n) ρ := by
    intro z hz
    rw [Work.CR.Flat.mem_polydisc]
    intro k
    simp only [Pi.zero_apply, sub_zero]
    exact lt_of_le_of_lt (hz k) (hCρ k)
  obtain ⟨χ, V, hχdiff, hχcpt, hχts, hVo, hKV, hχone⟩ :=
    Work.NN.Core.exists_contDiff_bump_of_isCompact_subset
      (K := {z : Cn n | ∀ k, ‖z k‖ ≤ C k}) (U := Work.CR.Flat.polydisc (0 : Cn n) ρ)
      (isCompact_closedPolydisc C) (Work.CR.Flat.isOpen_polydisc (0 : Cn n) ρ) hKU
  refine ⟨⟨e, a, b, r, he_pos, hea, ha_pos, hab, hr_pos, hbr⟩, C, χ,
    fun k => by show ρ' k < e k; rw [e_form k]; nlinarith [hu k],
    hbC, hCρ, hχdiff, hχcpt, hχts, fun z hz => hχone z (hKV (fun k => le_of_lt (hz k)))⟩

/-! ## The solution operator -/

/-- The solution operator `T := S2 G ∘ chiMul χ` of the parameterised telescoping, as a linear
map.  All the data that `exists_telTwoDF` prescribes only on the polydisc `polydisc 0 ρ` are fed
to the recursion through the bump-multiplied family `chiMul χ η`, which is globally smooth as soon
as `η` is smooth on a neighbourhood of the topological support of `χ`. -/
def TtwoDF (G : Geom n) (χ : Cn n → ℂ) :
    (Fin n → Fin n → Cn n → ℂ) →ₗ[ℝ] (Fin n → Cn n → ℂ) where
  toFun η := S2 G (chiMul χ η)
  map_add' η η' := by rw [LinearMap.map_add, S2_add]
  map_smul' c η := by simp only [LinearMap.map_smul, S2_smul, RingHom.id_apply]

@[simp] lemma TtwoDF_apply (G : Geom n) (χ : Cn n → ℂ) (η : Fin n → Fin n → Cn n → ℂ) :
    TtwoDF G χ η = S2 G (chiMul χ η) := rfl

end Work.NN.Core.TelTwoDF
