import Mathlib
import Submission.Work.Mostow.mlDefs

/-!
# Bookkeeping for two-point sets on the boundary sphere

`Pres2 g z w` (from `Submission.Work.Mostow.mlDefs`) says that `g` permutes the two-point set
`{z, w}`.  This file records that `Pres2` is multiplicative, stable under inversion and conjugation,
and that it can be divided on the left; plus injectivity of `bd` on the boundary sphere.
-/

namespace Work.Mostow.ML

open Submission.Mostow Work.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-- `bd g` is injective on the boundary sphere. -/
lemma bd_inj_sph (hA : POActionProp n) (g : PO n 1) {ξ η : E n} (hξ : ξ ∈ Sph n)
    (hη : η ∈ Sph n) (h : bd g ξ = bd g η) : ξ = η := by
  have hbd1 : ∀ ξ : E n, ξ ∈ Sph n → bd (1 : PO n 1) ξ = ξ := hA.2.2.2.2.2.2.2.2.1
  have hbdmul : ∀ (g h : PO n 1) (ξ : E n), ξ ∈ Sph n → bd (g * h) ξ = bd g (bd h ξ) :=
    hA.2.2.2.2.2.2.2.2.2.1
  calc ξ = bd (1 : PO n 1) ξ := (hbd1 ξ hξ).symm
    _ = bd (g⁻¹ * g) ξ := by rw [inv_mul_cancel]
    _ = bd g⁻¹ (bd g ξ) := hbdmul g⁻¹ g ξ hξ
    _ = bd g⁻¹ (bd g η) := by rw [h]
    _ = bd (g⁻¹ * g) η := (hbdmul g⁻¹ g η hη).symm
    _ = bd (1 : PO n 1) η := by rw [inv_mul_cancel]
    _ = η := hbd1 η hη

/-- Membership for the image of `z` under a `Pres2` element. -/
lemma mem_z_of_pres2 {g : PO n 1} {z w : E n} (hg : Pres2 g z w) :
    bd g z = z ∨ bd g z = w := by
  rcases hg with ⟨a, -⟩ | ⟨a, -⟩
  · exact Or.inl a
  · exact Or.inr a

/-- Membership for the image of `w` under a `Pres2` element. -/
lemma mem_w_of_pres2 {g : PO n 1} {z w : E n} (hg : Pres2 g z w) :
    bd g w = z ∨ bd g w = w := by
  rcases hg with ⟨-, a⟩ | ⟨-, a⟩
  · exact Or.inr a
  · exact Or.inl a

/-- Membership in `{z, w}` of the images of `z` and `w` implies `Pres2`. -/
lemma pres2_of_mem {z w : E n} (hA : POActionProp n) (hz : z ∈ Sph n) (hw : w ∈ Sph n)
    {g : PO n 1} (m1 : bd g z = z ∨ bd g z = w) (m2 : bd g w = z ∨ bd g w = w) :
    Pres2 g z w := by
  have hinj : ∀ {ξ η : E n}, ξ ∈ Sph n → η ∈ Sph n → bd g ξ = bd g η → ξ = η :=
    fun hξ hη h => bd_inj_sph hA g hξ hη h
  unfold Pres2
  rcases m1 with m1 | m1
  · rcases m2 with m2 | m2
    · exact Or.inl ⟨m1, by rw [m2]; exact hinj hz hw (m1.trans m2.symm)⟩
    · exact Or.inl ⟨m1, m2⟩
  · rcases m2 with m2 | m2
    · exact Or.inr ⟨m1, m2⟩
    · exact Or.inr ⟨m1, by rw [m2]; exact (hinj hz hw (m1.trans m2.symm)).symm⟩

/-- `Pres2` is multiplicative. -/
lemma pres2_mul {z w : E n} (hA : POActionProp n) (hz : z ∈ Sph n) (hw : w ∈ Sph n)
    {g h : PO n 1} (hg : Pres2 g z w) (hh : Pres2 h z w) : Pres2 (g * h) z w := by
  have hbdmul : ∀ (g h : PO n 1) (ξ : E n), ξ ∈ Sph n → bd (g * h) ξ = bd g (bd h ξ) :=
    hA.2.2.2.2.2.2.2.2.2.1
  unfold Pres2
  rcases hg with ⟨hgz, hgw⟩ | ⟨hgz, hgw⟩
  · rcases hh with ⟨hhz, hhw⟩ | ⟨hhz, hhw⟩
    · refine Or.inl ⟨by rw [hbdmul g h z hz, hhz, hgz],
                      by rw [hbdmul g h w hw, hhw, hgw]⟩
    · refine Or.inr ⟨by rw [hbdmul g h z hz, hhz, hgw],
                      by rw [hbdmul g h w hw, hhw, hgz]⟩
  · rcases hh with ⟨hhz, hhw⟩ | ⟨hhz, hhw⟩
    · refine Or.inr ⟨by rw [hbdmul g h z hz, hhz, hgz],
                      by rw [hbdmul g h w hw, hhw, hgw]⟩
    · refine Or.inl ⟨by rw [hbdmul g h z hz, hhz, hgw],
                      by rw [hbdmul g h w hw, hhw, hgz]⟩

/-- `Pres2` is stable under inversion. -/
lemma pres2_inv {z w : E n} (hA : POActionProp n) (hz : z ∈ Sph n) (hw : w ∈ Sph n)
    {g : PO n 1} (hg : Pres2 g z w) : Pres2 g⁻¹ z w := by
  have hbd1 : ∀ ξ : E n, ξ ∈ Sph n → bd (1 : PO n 1) ξ = ξ := hA.2.2.2.2.2.2.2.2.1
  have hbdmul : ∀ (g h : PO n 1) (ξ : E n), ξ ∈ Sph n → bd (g * h) ξ = bd g (bd h ξ) :=
    hA.2.2.2.2.2.2.2.2.2.1
  have hginv : ∀ y ∈ Sph n, bd g⁻¹ (bd g y) = y := by
    intro y hy
    calc bd g⁻¹ (bd g y) = bd (g⁻¹ * g) y := (hbdmul g⁻¹ g y hy).symm
      _ = bd (1 : PO n 1) y := by rw [inv_mul_cancel]
      _ = y := hbd1 y hy
  unfold Pres2
  rcases hg with ⟨hgz, hgw⟩ | ⟨hgz, hgw⟩
  · refine Or.inl ⟨?_, ?_⟩
    · nth_rewrite 1 [← hgz]; exact hginv z hz
    · nth_rewrite 1 [← hgw]; exact hginv w hw
  · refine Or.inr ⟨?_, ?_⟩
    · nth_rewrite 1 [← hgw]; exact hginv w hw
    · nth_rewrite 1 [← hgz]; exact hginv z hz

/-- `Pres2` is stable under conjugation, the two-point set being moved by `bd t⁻¹`. -/
lemma pres2_conj {z w : E n} (hA : POActionProp n) (hz : z ∈ Sph n) (hw : w ∈ Sph n)
    {g t : PO n 1} (hg : Pres2 g z w) : Pres2 (t⁻¹ * g * t) (bd t⁻¹ z) (bd t⁻¹ w) := by
  have hbd1 : ∀ ξ : E n, ξ ∈ Sph n → bd (1 : PO n 1) ξ = ξ := hA.2.2.2.2.2.2.2.2.1
  have hbdmul : ∀ (g h : PO n 1) (ξ : E n), ξ ∈ Sph n → bd (g * h) ξ = bd g (bd h ξ) :=
    hA.2.2.2.2.2.2.2.2.2.1
  have hmem : ∀ (g : PO n 1) (ξ : E n), ξ ∈ Sph n → bd g ξ ∈ Sph n := hA.2.2.2.2.2.2.2.1
  have htinv : ∀ y ∈ Sph n, bd t (bd t⁻¹ y) = y := by
    intro y hy
    calc bd t (bd t⁻¹ y) = bd (t * t⁻¹) y := (hbdmul t t⁻¹ y hy).symm
      _ = bd (1 : PO n 1) y := by rw [mul_inv_cancel]
      _ = y := hbd1 y hy
  have key : ∀ y ∈ Sph n, bd (t⁻¹ * g * t) (bd t⁻¹ y) = bd t⁻¹ (bd g y) := by
    intro y hy
    calc bd (t⁻¹ * g * t) (bd t⁻¹ y)
        = bd (t⁻¹ * g) (bd t (bd t⁻¹ y)) := hbdmul (t⁻¹ * g) t (bd t⁻¹ y) (hmem t⁻¹ y hy)
      _ = bd (t⁻¹ * g) y := by rw [htinv y hy]
      _ = bd t⁻¹ (bd g y) := hbdmul t⁻¹ g y hy
  unfold Pres2
  rcases hg with ⟨hgz, hgw⟩ | ⟨hgz, hgw⟩
  · refine Or.inl ⟨by rw [key z hz, hgz], by rw [key w hw, hgw]⟩
  · refine Or.inr ⟨by rw [key z hz, hgz], by rw [key w hw, hgw]⟩

/-- Division on the left for `Pres2`. -/
lemma pres2_of_mul_left {z w : E n} (hA : POActionProp n) (hz : z ∈ Sph n) (hw : w ∈ Sph n)
    {g h : PO n 1} (hgh : Pres2 (g * h) z w) (hg : Pres2 g z w) : Pres2 h z w := by
  have hbd1 : ∀ ξ : E n, ξ ∈ Sph n → bd (1 : PO n 1) ξ = ξ := hA.2.2.2.2.2.2.2.2.1
  have hbdmul : ∀ (g h : PO n 1) (ξ : E n), ξ ∈ Sph n → bd (g * h) ξ = bd g (bd h ξ) :=
    hA.2.2.2.2.2.2.2.2.2.1
  have hmem : ∀ (g : PO n 1) (ξ : E n), ξ ∈ Sph n → bd g ξ ∈ Sph n := hA.2.2.2.2.2.2.2.1
  have hgi : Pres2 g⁻¹ z w := pres2_inv hA hz hw hg
  have hginv : ∀ y ∈ Sph n, bd g⁻¹ (bd g y) = y := by
    intro y hy
    calc bd g⁻¹ (bd g y) = bd (g⁻¹ * g) y := (hbdmul g⁻¹ g y hy).symm
      _ = bd (1 : PO n 1) y := by rw [inv_mul_cancel]
      _ = y := hbd1 y hy
  have keyz : bd h z = bd g⁻¹ (bd (g * h) z) := by
    rw [hbdmul g h z hz, hginv (bd h z) (hmem h z hz)]
  have keyw : bd h w = bd g⁻¹ (bd (g * h) w) := by
    rw [hbdmul g h w hw, hginv (bd h w) (hmem h w hw)]
  rcases hgh with ⟨hz1, hw1⟩ | ⟨hz1, hw1⟩
  · rcases hgi with ⟨hz2, hw2⟩ | ⟨hz2, hw2⟩
    · refine pres2_of_mem hA hz hw (Or.inl ?_) (Or.inr ?_)
      · rw [keyz, hz1, hz2]
      · rw [keyw, hw1, hw2]
    · refine pres2_of_mem hA hz hw (Or.inr ?_) (Or.inl ?_)
      · rw [keyz, hz1, hz2]
      · rw [keyw, hw1, hw2]
  · rcases hgi with ⟨hz2, hw2⟩ | ⟨hz2, hw2⟩
    · refine pres2_of_mem hA hz hw (Or.inr ?_) (Or.inl ?_)
      · rw [keyz, hz1, hw2]
      · rw [keyw, hw1, hz2]
    · refine pres2_of_mem hA hz hw (Or.inl ?_) (Or.inr ?_)
      · rw [keyz, hz1, hw2]
      · rw [keyw, hw1, hz2]

/-! ### Sanity checks for the order of alternatives -/

example (P Q : Prop) (h : P ∨ Q) : True := by
  rcases h with hp | hq
  · have : P := hp
    trivial
  · have : Q := hq
    trivial

example (P Q R S : Prop) (h : (P ∧ Q) ∨ (R ∧ S)) : True := by
  rcases h with ⟨hp, hq⟩ | ⟨hr, hs⟩
  · have : P := hp
    trivial
  · have : R := hr
    trivial

end

end Work.Mostow.ML
