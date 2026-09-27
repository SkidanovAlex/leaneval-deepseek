import Mathlib
import Submission.Work.Mostow.bridge_core

/-!
# The Dirichlet domain is a fundamental domain

For a subgroup `Γ ≤ PO n 1`, a base point `o` with trivial `Γ`-stabiliser and the property that
every point of `ℍⁿ` has a nearest point of the orbit `Γ • o`, the Dirichlet domain

`D = {x | ∀ γ : Γ, hdist x o ≤ hdist x (γ • o)}`

is a `volH`-fundamental domain for the action of `Γ`.

* `D` is closed (`Work.Mostow.isClosed_dirichletSet`), hence null-measurable.
* Every `x` lies in some translate of `D`: take `γ` closest to `x`, then `γ⁻¹ • x ∈ D` (this is
  where `hmin` is used).
* Distinct translates are a.e. disjoint: if `a ≠ b` and `x ∈ a • D ∩ b • D` then applying the
  isometry `a` (resp. `b`) to the inequalities defining the two membership statements shows
  `hdist x (a • o) = hdist x (b • o)`; the bisector between the two distinct points `a • o ≠ b • o`
  is `volH`-null (`Work.Mostow.dirichlet_bisector_null`).

No discreteness of `Γ`, no compactness and no explicit counting argument is needed: the
bisector-nullity computation replaces the usual local finiteness.
-/

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped Pointwise

namespace Work.Mostow

theorem dirichletSet_isFundamentalDomain (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) [Countable Γ]
    (o : Submission.Mostow.E n) (ho : ∀ γ : Γ, γ • o = o → γ = 1)
    (hmin : ∀ x : Submission.Mostow.E n, ∃ γ : Γ,
      ∀ γ' : Γ, Submission.Mostow.hdist x (γ • o) ≤ Submission.Mostow.hdist x (γ' • o)) :
    MeasureTheory.IsFundamentalDomain Γ (Work.Mostow.dirichletSet Γ o)
      (Submission.Mostow.volH n) := by
  obtain ⟨-, -, -, hone, hmul, -, -, -, -, -, -, -⟩ := hA
  obtain ⟨-, -, -, -, -, -, hiso, -, -, -, -, -, -⟩ := hI
  -- The action laws of `PO n 1`, transported to `Γ`.
  have honeΓ : ∀ y : E n, (1 : Γ) • y = y := by
    intro y
    calc (1 : Γ) • y = (1 : PO n 1) • y := rfl
      _ = y := hone y
  have hsm_mul_Γ : ∀ (g h : Γ) (y : E n), (g * h : Γ) • y = g • (h • y) := by
    intro g h y
    calc (g * h : Γ) • y = ((g : PO n 1) * (h : PO n 1)) • y := rfl
      _ = (g : PO n 1) • ((h : PO n 1) • y) := hmul (g : PO n 1) (h : PO n 1) y
      _ = g • (h • y) := rfl
  have hisoΓ : ∀ (g : Γ) (u v : E n), hdist (g • u) (g • v) = hdist u v := by
    intro g u v
    calc hdist (g • u) (g • v) = hdist ((g : PO n 1) • u) ((g : PO n 1) • v) := rfl
      _ = hdist u v := hiso (g : PO n 1) u v
  have hinv_smul : ∀ (g : Γ) (y : E n), g • ((g⁻¹ : Γ) • y) = y := by
    intro g y
    calc g • ((g⁻¹ : Γ) • y) = (g : PO n 1) • ((g : PO n 1)⁻¹ • y) := rfl
      _ = ((g : PO n 1) * (g : PO n 1)⁻¹) • y :=
          (hmul (g : PO n 1) ((g : PO n 1))⁻¹ y).symm
      _ = y := by rw [mul_inv_cancel, hone]
  have hinv_smul' : ∀ (g : Γ) (y : E n), (g⁻¹ : Γ) • (g • y) = y := by
    intro g y
    calc (g⁻¹ : Γ) • (g • y) = (g : PO n 1)⁻¹ • ((g : PO n 1) • y) := rfl
      _ = ((g : PO n 1)⁻¹ * (g : PO n 1)) • y :=
          (hmul ((g : PO n 1))⁻¹ (g : PO n 1) y).symm
      _ = y := by rw [inv_mul_cancel, hone]
  refine ⟨?_, ?_, ?_⟩
  · -- null-measurability: `D` is closed
    exact (isClosed_dirichletSet Γ o).measurableSet.nullMeasurableSet
  · -- covering: the nearest orbit point of `x` translates `x` into `D`
    refine Filter.Eventually.of_forall fun x => ?_
    obtain ⟨γ, hγ⟩ := hmin x
    refine ⟨γ⁻¹, ?_⟩
    intro δ
    have h1 : hdist ((γ⁻¹ : Γ) • x) o = hdist x (γ • o) := by
      rw [← hisoΓ γ ((γ⁻¹ : Γ) • x) o, hinv_smul γ x]
    have h2 : hdist ((γ⁻¹ : Γ) • x) (δ • o) = hdist x ((γ * δ : Γ) • o) := by
      rw [← hisoΓ γ ((γ⁻¹ : Γ) • x) (δ • o), hinv_smul γ x, ← hsm_mul_Γ γ δ o]
    rw [h1, h2]
    exact hγ (γ * δ)
  · -- pairwise a.e. disjointness: points of `a • D ∩ b • D` lie on the bisector `(a • o, b • o)`
    intro a b hab
    show volH n ((a • dirichletSet Γ o) ∩ (b • dirichletSet Γ o)) = 0
    have hne : ((a : PO n 1) • o) ≠ ((b : PO n 1) • o) := by
      intro h
      have hab_eq : a • o = b • o := by
        calc a • o = (a : PO n 1) • o := rfl
          _ = (b : PO n 1) • o := h
          _ = b • o := rfl
      have h2 : (b⁻¹ * a : Γ) • o = o := by
        rw [hsm_mul_Γ b⁻¹ a o, hab_eq, hinv_smul' b o]
      have hba : b⁻¹ * a = 1 := ho _ h2
      have hab' : a = b := by
        have hb : b * (b⁻¹ * a) = b := by rw [hba, mul_one]
        rwa [mul_inv_cancel_left] at hb
      exact hab hab'
    have hnull : volH n {u : E n | hdist u ((a : PO n 1) • o) = hdist u ((b : PO n 1) • o)} = 0 :=
      dirichlet_bisector_null n hne
    refine measure_mono_null ?_ hnull
    intro x hx
    rw [Set.mem_inter_iff, Set.mem_smul_set, Set.mem_smul_set] at hx
    obtain ⟨⟨y, hy, hyx⟩, ⟨z, hz, hzx⟩⟩ := hx
    subst hyx
    have hle1 : hdist (a • y) (a • o) ≤ hdist (a • y) (b • o) := by
      have h := hy (a⁻¹ * b : Γ)
      rw [← hisoΓ a y o, ← hisoΓ a y ((a⁻¹ * b : Γ) • o)] at h
      rw [← hsm_mul_Γ a (a⁻¹ * b) o] at h
      rw [show (a * (a⁻¹ * b) : Γ) = b from mul_inv_cancel_left a b] at h
      exact h
    have hle2 : hdist (a • y) (b • o) ≤ hdist (a • y) (a • o) := by
      have h := hz (b⁻¹ * a : Γ)
      rw [← hisoΓ b z o, ← hisoΓ b z ((b⁻¹ * a : Γ) • o)] at h
      rw [← hsm_mul_Γ b (b⁻¹ * a) o] at h
      rw [show (b * (b⁻¹ * a) : Γ) = a from mul_inv_cancel_left b a] at h
      rw [hzx] at h
      exact h
    exact le_antisymm hle1 hle2

end Work.Mostow
