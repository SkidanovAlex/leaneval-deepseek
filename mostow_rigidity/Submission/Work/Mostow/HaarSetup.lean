import Mathlib
import Submission.Mostow.Interfaces
import Submission.Work.Mostow.HaarBase
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.VolDefs

/-!
# Set-up for the Haar-to-volume bridge (`Work.Mostow.haar_map_eq_smul_volH`)

`Work.Mostow.Ksub n hA` is the stabiliser of the origin in `PO n 1`.  Given a *section*
`s : E n → PO n 1` of the orbit map `g ↦ g • 0` (i.e. `s u • 0 = u`), the map

`Theta n hA s : E n × ↥(Ksub n hA) → PO n 1`,  `(u, k) ↦ s u * k`

is a bijection.  This file collects the elementary algebra of `Theta`, of the "defect"
`psi g u ∈ Ksub` with `g * s u = s (g • u) * psi g u`, and the measurability facts needed to
push measures forward along `Theta` and along the maps `p ↦ (g • p.1, psi g p.1 * p.2)`.

Nothing here depends on the existence of `s`: existence of a *continuous* section is the
separate statement `Work.Mostow.exists_continuous_section` (module
`Submission.Work.Mostow.continuousSection`).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal

noncomputable section

variable {n : ℕ}

/-- The parametrisation `(u, k) ↦ s u * k` of `PO n 1` by `E n × ↥(Ksub n hA)`. -/
def Theta (n : ℕ) (hA : POActionProp n) (s : E n → PO n 1) :
    E n × ↥(Ksub n hA) → PO n 1 :=
  fun p => s p.1 * (p.2 : PO n 1)

@[simp] theorem Theta_apply (n : ℕ) (hA : POActionProp n) (s : E n → PO n 1)
    (p : E n × ↥(Ksub n hA)) : Theta n hA s p = s p.1 * (p.2 : PO n 1) := rfl


/-- If `a • 0 = b • 0` then `(a⁻¹ * b) • 0 = 0`. -/
theorem inv_mul_smul_zero (n : ℕ) (hA : POActionProp n) {a b : PO n 1}
    (h : a • (0 : E n) = b • (0 : E n)) : (a⁻¹ * b) • (0 : E n) = 0 := by
  calc (a⁻¹ * b) • (0 : E n) = a⁻¹ • (b • (0 : E n)) := hA.2.2.2.2.1 _ _ _
    _ = a⁻¹ • (a • (0 : E n)) := by rw [h.symm]
    _ = (a⁻¹ * a) • (0 : E n) := (hA.2.2.2.2.1 _ _ _).symm
    _ = (0 : E n) := by rw [inv_mul_cancel, hA.2.2.2.1]

/-- The `Ksub`-coordinate of `g ∈ PO n 1` relative to the section `s`. -/
def kPart (n : ℕ) (hA : POActionProp n) (s : E n → PO n 1)
    (hs : ∀ u : E n, s u • (0 : E n) = u) (g : PO n 1) : ↥(Ksub n hA) :=
  ⟨(s (g • (0 : E n)))⁻¹ * g, mem_Ksub.2 (inv_mul_smul_zero n hA (hs (g • (0 : E n))))⟩

@[simp] theorem kPart_coe (n : ℕ) (hA : POActionProp n) (s : E n → PO n 1)
    (hs : ∀ u : E n, s u • (0 : E n) = u) (g : PO n 1) :
    (kPart n hA s hs g : PO n 1) = (s (g • (0 : E n)))⁻¹ * g := rfl

/-- The defect `psi g u ∈ Ksub` with `g * s u = s (g • u) * psi g u`. -/
def psi (n : ℕ) (hA : POActionProp n) (s : E n → PO n 1)
    (hs : ∀ u : E n, s u • (0 : E n) = u) (g : PO n 1) (u : E n) : ↥(Ksub n hA) :=
  ⟨(s (g • u))⁻¹ * (g * s u), mem_Ksub.2 (inv_mul_smul_zero n hA (by
    rw [hA.2.2.2.2.1, hs u, hs (g • u)]))⟩

@[simp] theorem psi_coe (n : ℕ) (hA : POActionProp n) (s : E n → PO n 1)
    (hs : ∀ u : E n, s u • (0 : E n) = u) (g : PO n 1) (u : E n) :
    (psi n hA s hs g u : PO n 1) = (s (g • u))⁻¹ * (g * s u) := rfl

/-- `Theta` is a section of the orbit map in the first coordinate. -/
theorem Theta_fst (n : ℕ) (hA : POActionProp n) (s : E n → PO n 1)
    (hs : ∀ u : E n, s u • (0 : E n) = u) (u : E n) (k : ↥(Ksub n hA)) :
    Theta n hA s (u, k) • (0 : E n) = u := by
  calc Theta n hA s (u, k) • (0 : E n) = (s u * (k : PO n 1)) • (0 : E n) := rfl
    _ = s u • ((k : PO n 1) • (0 : E n)) := hA.2.2.2.2.1 _ _ _
    _ = s u • (0 : E n) := by rw [k.2]
    _ = u := hs u

/-- The key identity: left multiplication by `g` on `PO n 1` corresponds, under `Theta`, to
`(u, k) ↦ (g • u, psi g u * k)`. -/
theorem Theta_mul (n : ℕ) (hA : POActionProp n) (s : E n → PO n 1)
    (hs : ∀ u : E n, s u • (0 : E n) = u) (g : PO n 1) (u : E n) (k : ↥(Ksub n hA)) :
    g * Theta n hA s (u, k) = Theta n hA s (g • u, psi n hA s hs g u * k) := by
  have hcoe : ((psi n hA s hs g u * k : ↥(Ksub n hA)) : PO n 1)
      = (psi n hA s hs g u : PO n 1) * (k : PO n 1) := Submonoid.coe_mul _ _ _
  show g * (s u * (k : PO n 1)) = s (g • u) * ↑(psi n hA s hs g u * k)
  rw [hcoe, psi_coe]
  group

/-- `Theta` is surjective, with explicit inverse given by `kPart`. -/
theorem Theta_surjective (n : ℕ) (hA : POActionProp n) (s : E n → PO n 1)
    (hs : ∀ u : E n, s u • (0 : E n) = u) :
    Function.Surjective (Theta n hA s) := by
  intro g
  refine ⟨(g • (0 : E n), kPart n hA s hs g), ?_⟩
  show s (g • (0 : E n)) * ↑(kPart n hA s hs g) = g
  rw [kPart_coe]
  group

/-- `Theta` is injective (given that `s` is a section). -/
theorem Theta_injective (n : ℕ) (hA : POActionProp n) (s : E n → PO n 1)
    (hs : ∀ u : E n, s u • (0 : E n) = u) :
    Function.Injective (Theta n hA s) := by
  intro p q hpq
  obtain ⟨u, k⟩ := p
  obtain ⟨u', k'⟩ := q
  simp only [Prod.mk.injEq] at hpq ⊢
  have h1 : u = u' := by
    rw [← Theta_fst n hA s hs u k, ← Theta_fst n hA s hs u' k', hpq]
  refine ⟨h1, ?_⟩
  have h2 : (k : PO n 1) = (k' : PO n 1) := by
    have h := hpq
    simp only [Theta] at h
    rw [h1] at h
    exact mul_left_cancel h
  exact Subtype.ext h2

/-- Continuity of `Theta` for a continuous section. -/
theorem continuous_Theta (n : ℕ) (hA : POActionProp n) (s : E n → PO n 1)
    (hsc : Continuous s) : Continuous (Theta n hA s) := by
  have h1 : Continuous fun p : E n × ↥(Ksub n hA) => s p.1 := hsc.comp continuous_fst
  have h2 : Continuous fun p : E n × ↥(Ksub n hA) => (p.2 : PO n 1) :=
    continuous_subtype_val.comp continuous_snd
  exact h1.mul h2

/-- Joint continuity of `(g, u) ↦ g • u` for a fixed `g`. -/
theorem continuous_smul_const (n : ℕ) (hA : POActionProp n) (g : PO n 1) :
    Continuous fun u : E n => g • u :=
  hA.2.2.2.2.2.2.1.comp (continuous_const.prodMk continuous_id)

/-- Continuity of `u ↦ psi g u`. -/
theorem continuous_psi (n : ℕ) (hA : POActionProp n) (s : E n → PO n 1)
    (hs : ∀ u : E n, s u • (0 : E n) = u) (hsc : Continuous s) (g : PO n 1) :
    Continuous fun u : E n => psi n hA s hs g u := by
  apply Continuous.subtype_mk
  have hact : Continuous fun u : E n => g • u := continuous_smul_const n hA g
  have h1 : Continuous fun u : E n => s (g • u) := hsc.comp hact
  have h2 : Continuous fun u : E n => (g : PO n 1) * s u := Continuous.mul continuous_const hsc
  show Continuous fun u : E n => ((s (g • u))⁻¹ * (g * s u) : PO n 1)
  exact Continuous.mul h1.inv h2

/-- Continuity of the "conjugation" map `p ↦ (g • p.1, psi g p.1 * p.2)`. -/
theorem continuous_Phi (n : ℕ) (hA : POActionProp n) (s : E n → PO n 1)
    (hs : ∀ u : E n, s u • (0 : E n) = u) (hsc : Continuous s) (g : PO n 1) :
    Continuous fun p : E n × ↥(Ksub n hA) => (g • p.1, psi n hA s hs g p.1 * p.2) :=
  (((continuous_smul_const n hA g).comp continuous_fst)).prodMk
    (((continuous_psi n hA s hs hsc g).comp continuous_fst).mul continuous_snd)

/-- Measurability of the "conjugation" map `p ↦ (g • p.1, psi g p.1 * p.2)`. -/
theorem measurable_Phi (n : ℕ) (hA : POActionProp n) (s : E n → PO n 1)
    (hs : ∀ u : E n, s u • (0 : E n) = u) (hsc : Continuous s) (g : PO n 1) :
    Measurable fun p : E n × ↥(Ksub n hA) => (g • p.1, psi n hA s hs g p.1 * p.2) :=
  (continuous_Phi n hA s hs hsc g).measurable

end
end Work.Mostow
