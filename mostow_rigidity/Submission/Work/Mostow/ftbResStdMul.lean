import Mathlib
import Submission.Work.Mostow.blk_smul_fermi

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

/-! ## Helpers for `ftbResStdMul`

The hypotheses `hAj`, `hA` are the action axioms of `POActionProp`.  Only two of them are
used: `(g * h) • u = g • (h • u)` and faithfulness `(∀ u, g • u = u) → g = 1`.  The block
description `hblk` records that every `c` in `centralizer {blk j m 1 R} ⊓ Λ` acts on the
Fermi coordinates as `(resStd c, nrmStd c)`; on the stratum (`w = 0`) it therefore reads
`c • coordEmb v = coordEmb (resStd c • v)`, which determines `resStd c` through its action.
Multiplicativity of `resStd` on this set is then the multiplicativity of that action. -/

/-- `fermi k m v 0 = coordEmb k m v`: Fermi coordinates with vanishing normal part. -/
private lemma fer0 (k m : ℕ) (v : E k) : fermi k m v 0 = coordEmb k m v := by
  simp [fermi, coordEmb, sinhc]

/-- `tanC` is a left inverse of `coordEmb`. -/
private lemma tanCe (k m : ℕ) (v : E k) : tanC k m (coordEmb k m v) = v := by
  ext i; simp [tanC, coordEmb]

/-- `coordEmb k m` is injective. -/
private lemma cEmbInj (k m : ℕ) : Function.Injective (coordEmb k m) := by
  intro a b h
  have hh := congrArg (tanC k m) h
  rwa [tanCe, tanCe] at hh

/-- Two elements of `PO n 1` with the same action on `E n` are equal (from the action
axioms alone). -/
private lemma eq_of_smul_eq {n : ℕ} (hOne : ∀ u : E n, (1 : PO n 1) • u = u)
    (hMul : ∀ (g h : PO n 1) (u : E n), (g * h) • u = g • (h • u))
    (hFaith : ∀ g : PO n 1, (∀ u : E n, g • u = u) → g = 1) {g h : PO n 1}
    (H : ∀ u : E n, g • u = h • u) : g = h := by
  have h1 : g⁻¹ * h = 1 := hFaith (g⁻¹ * h) (fun u => by
    rw [hMul, ← H u, ← hMul, inv_mul_cancel, hOne])
  have h2 : g * (g⁻¹ * h) = g * 1 := by rw [h1]
  rw [← mul_assoc, mul_inv_cancel, one_mul, mul_one] at h2
  exact h2.symm

theorem ftbResStdMul (j m : ℕ) (hAj : Submission.Mostow.POActionProp j)
    (hA : Submission.Mostow.POActionProp (j + m))
    (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (j + m) 1))
    (R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
    (hblk : ∀ c ∈ (Subgroup.centralizer {Submission.Mostow.blk j m 1 R} ⊓ Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (j + m) 1)),
      ∀ (v : Submission.Mostow.E j) (w : Submission.Mostow.E m),
        (c : LeanEval.Geometry.MostowRigidity.PO (j + m) 1) • Submission.Mostow.fermi j m v w =
          Submission.Mostow.fermi j m
            (Submission.Mostow.resStd j m (c : LeanEval.Geometry.MostowRigidity.PO (j + m) 1) • v)
            (Submission.Mostow.nrmStd j m (c : LeanEval.Geometry.MostowRigidity.PO (j + m) 1) w)) :
    ∀ c₁ c₂ : LeanEval.Geometry.MostowRigidity.PO (j + m) 1,
      c₁ ∈ (Subgroup.centralizer {Submission.Mostow.blk j m 1 R} ⊓ Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (j + m) 1)) →
      c₂ ∈ (Subgroup.centralizer {Submission.Mostow.blk j m 1 R} ⊓ Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (j + m) 1)) →
      Submission.Mostow.resStd j m (c₁ * c₂) = Submission.Mostow.resStd j m c₁ * Submission.Mostow.resStd j m c₂ := by
  obtain ⟨-, -, -, hOneA, hMulA, hFaithA, -⟩ := hA
  obtain ⟨-, -, -, hOnej, hMulj, hFaithj, -⟩ := hAj
  intro c₁ c₂ hc₁ hc₂
  have hmem : c₁ * c₂ ∈
      (Subgroup.centralizer {Submission.Mostow.blk j m 1 R} ⊓ Λ : Subgroup (PO (j + m) 1)) :=
    mul_mem hc₁ hc₂
  -- on the stratum the action of `resStd c` is determined by that of `c`
  have hcoord : ∀ (c : PO (j + m) 1),
      c ∈ (Subgroup.centralizer {Submission.Mostow.blk j m 1 R} ⊓ Λ : Subgroup (PO (j + m) 1)) →
      ∀ v : E j, c • Submission.Mostow.coordEmb j m v =
        Submission.Mostow.coordEmb j m (Submission.Mostow.resStd j m c • v) := by
    intro c hc v
    have h := hblk c hc v 0
    rw [fer0 j m v, map_zero, fer0 j m (Submission.Mostow.resStd j m c • v)] at h
    exact h
  have key : ∀ v : E j,
      Submission.Mostow.resStd j m (c₁ * c₂) • v =
        (Submission.Mostow.resStd j m c₁ * Submission.Mostow.resStd j m c₂) • v := by
    intro v
    apply cEmbInj j m
    calc Submission.Mostow.coordEmb j m (Submission.Mostow.resStd j m (c₁ * c₂) • v)
        = (c₁ * c₂) • Submission.Mostow.coordEmb j m v := (hcoord (c₁ * c₂) hmem v).symm
      _ = c₁ • (c₂ • Submission.Mostow.coordEmb j m v) := hMulA c₁ c₂ _
      _ = c₁ • Submission.Mostow.coordEmb j m (Submission.Mostow.resStd j m c₂ • v) := by
            rw [hcoord c₂ hc₂ v]
      _ = Submission.Mostow.coordEmb j m
            (Submission.Mostow.resStd j m c₁ • (Submission.Mostow.resStd j m c₂ • v)) :=
            hcoord c₁ hc₁ _
      _ = Submission.Mostow.coordEmb j m
            ((Submission.Mostow.resStd j m c₁ * Submission.Mostow.resStd j m c₂) • v) := by
            rw [hMulj]
  exact eq_of_smul_eq hOnej hMulj hFaithj key

end Work.Mostow
