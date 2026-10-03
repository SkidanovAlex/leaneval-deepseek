/-
# The bridge `LinnellDatum → TorsionData`: shared definitions

This file fixes the vocabulary used by the construction of `Work.ORTorsion.TorsionData` from a
`Work.ORLinnell.LinnellDatum`:

* `Dsub L H` — the `K`-subalgebra of `U` whose carrier is the division closure `L.D H`;
* `Nsub φ` — for `φ : H →* Multiplicative ℤ`, the subgroup `φ.ker.map H.subtype` of `G` (the
  `N` of the Laurent datum, transported to `G`);
* `TorsionR L N H` — the subring `⟨D N ∪ gen H⟩` of `U` (the `R` of the Laurent datum);
* `TorsionRsub L N H` — the same set as a `K`-subalgebra;
* `rightMulU L N H s j` — right multiplication by `gen s ^ j` on `R`.

Everything here is definitional bookkeeping; the mathematical content is delegated.
-/
import Mathlib
import Submission.Work.ORLinnell.Main
import Submission.Work.ORLocInd.Basic
import Submission.Work.ORLocInd.Core
import Submission.Work.ORTorsion.Defs

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORFinal.TorsionData

open Work.ORLinnell

variable {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U] [Nontrivial U]
  [Algebra K U]

noncomputable section

/-! ## The division closure as a `K`-subalgebra -/

/-- The division closure `L.D H` of `K[H]` in `U`, as a `K`-subalgebra of `U`. -/
def Dsub (L : LinnellDatum K G U) (H : Subgroup G) : Subalgebra K U :=
  Subalgebra.mk (Subring.toSubsemiring (L.D H)) (fun k => L.algebraMap_mem H k)

@[simp] theorem mem_Dsub (L : LinnellDatum K G U) (H : Subgroup G) (x : U) :
    x ∈ Dsub L H ↔ x ∈ L.D H := Iff.rfl

@[simp] theorem coe_Dsub (L : LinnellDatum K G U) (H : Subgroup G) :
    ((Dsub L H : Subalgebra K U) : Set U) = (L.D H : Set U) := rfl

theorem Dsub_mono (L : LinnellDatum K G U) {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂) :
    Dsub L H₁ ≤ Dsub L H₂ := fun _ hx => L.D_mono h hx

theorem Dsub_isDivisionClosed (L : LinnellDatum K G U) (H : Subgroup G) :
    IsDivisionClosed (Dsub L H).toSubring :=
  L.isDivisionClosed H

/-- The image of `h : H` in `↥(Dsub L H)`. -/
def genDsub (L : LinnellDatum K G U) (H : Subgroup G) (h : H) : ↥(Dsub L H) :=
  ⟨(L.gen (h : G) : U), L.gen_mem H h⟩

@[simp] theorem genDsub_coe (L : LinnellDatum K G U) (H : Subgroup G) (h : H) :
    ((genDsub L H h : ↥(Dsub L H)) : U) = (L.gen (h : G) : U) := rfl

/-! ## The subgroup `N = ker φ` -/

/-- The kernel of `φ : H →* Multiplicative ℤ`, transported to `G` along `H.subtype`. -/
def Nsub {H : Subgroup G} (φ : H →* Multiplicative ℤ) : Subgroup G := φ.ker.map H.subtype

theorem Nsub_le {H : Subgroup G} (φ : H →* Multiplicative ℤ) : Nsub φ ≤ H := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

theorem subgroupOf_Nsub {H : Subgroup G} (φ : H →* Multiplicative ℤ) :
    (Nsub φ).subgroupOf H = φ.ker := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have : y = x := Subtype.ext hyx
    rwa [← this]
  · intro hx
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩

/-- `Nsub φ` is normal in `H`. -/
theorem normal_subgroupOf_Nsub {H : Subgroup G} (φ : H →* Multiplicative ℤ) :
    ((Nsub φ).subgroupOf H).Normal := by
  rw [subgroupOf_Nsub]
  exact MonoidHom.normal_ker φ

/-! ## The Laurent subring `R = ⟨D N ∪ gen H⟩` -/

/-- The subring `R = ⟨D N ∪ gen H⟩` of `U`. -/
def TorsionR (L : LinnellDatum K G U) (N H : Subgroup G) : Subring U :=
  Subring.closure ((L.D N : Set U) ∪ Set.range (fun h : H => (L.gen (h : G) : U)))

/-- The subalgebra with the same carrier as `TorsionR`. -/
def TorsionRsub (L : LinnellDatum K G U) (N H : Subgroup G) : Subalgebra K U :=
  Algebra.adjoin K ((L.D N : Set U) ∪ Set.range (fun h : H => (L.gen (h : G) : U)))

theorem TorsionRsub_toSubring (L : LinnellDatum K G U) (N H : Subgroup G) :
    (TorsionRsub L N H).toSubring = TorsionR L N H := by
  have hmono : Subring.closure ((L.D N : Set U) ∪ Set.range (fun h : H => (L.gen (h : G) : U)))
      ≤ Subring.closure (Set.range (algebraMap K U) ∪
          ((L.D N : Set U) ∪ Set.range (fun h : H => (L.gen (h : G) : U)))) :=
    Subring.closure_mono Set.subset_union_right
  have hmono' : Subring.closure (Set.range (algebraMap K U) ∪
        ((L.D N : Set U) ∪ Set.range (fun h : H => (L.gen (h : G) : U))))
      ≤ Subring.closure ((L.D N : Set U) ∪ Set.range (fun h : H => (L.gen (h : G) : U))) := by
    rw [Subring.closure_le]
    rintro x (hx | hx)
    · obtain ⟨k, rfl⟩ := hx
      exact Subring.subset_closure (Set.mem_union_left _ (L.algebraMap_mem N k))
    · exact Subring.subset_closure hx
  rw [TorsionRsub, TorsionR, Algebra.adjoin_eq_ring_closure]
  exact le_antisymm hmono' hmono

theorem mem_TorsionRsub_iff (L : LinnellDatum K G U) (N H : Subgroup G) (x : U) :
    x ∈ TorsionRsub L N H ↔ x ∈ TorsionR L N H := by
  show x ∈ (TorsionRsub L N H).toSubring ↔ x ∈ TorsionR L N H
  rw [TorsionRsub_toSubring L N H]

theorem mem_TorsionR (L : LinnellDatum K G U) (N H : Subgroup G) (x : U) :
    x ∈ TorsionR L N H ↔ x ∈ TorsionRsub L N H := (mem_TorsionRsub_iff L N H x).symm

theorem Dsub_le_TorsionRsub (L : LinnellDatum K G U) (N H : Subgroup G) :
    Dsub L N ≤ TorsionRsub L N H := by
  intro x hx
  rw [mem_TorsionRsub_iff]
  exact Subring.subset_closure (Set.mem_union_left _ hx)

theorem gen_mem_TorsionRsub (L : LinnellDatum K G U) (N H : Subgroup G) (h : H) :
    (L.gen (h : G) : U) ∈ TorsionRsub L N H := by
  rw [mem_TorsionRsub_iff]
  exact Subring.subset_closure (Set.mem_union_right _ ⟨h, rfl⟩)

theorem TorsionRsub_le_Dsub (L : LinnellDatum K G U) {N H : Subgroup G} (hNH : N ≤ H) :
    TorsionRsub L N H ≤ Dsub L H := by
  rw [TorsionRsub, Algebra.adjoin_le_iff]
  rintro x (hx | hx)
  · exact L.D_mono hNH hx
  · obtain ⟨h, rfl⟩ := hx
    exact L.gen_mem H h

theorem TorsionR_le_D (L : LinnellDatum K G U) {N H : Subgroup G} (hNH : N ≤ H) :
    TorsionR L N H ≤ L.D H := by
  rw [TorsionR, Subring.closure_le]
  rintro x (hx | hx)
  · exact L.D_mono hNH hx
  · obtain ⟨h, rfl⟩ := hx
    exact L.gen_mem H h

theorem TorsionR_mono (L : LinnellDatum K G U) {N₁ N₂ H₁ H₂ : Subgroup G} (hN : N₁ ≤ N₂)
    (hH : H₁ ≤ H₂) : TorsionR L N₁ H₁ ≤ TorsionR L N₂ H₂ := by
  rw [TorsionR, Subring.closure_le]
  rintro x (hx | hx)
  · exact Subring.subset_closure (Set.mem_union_left _ (L.D_mono hN hx))
  · obtain ⟨h, rfl⟩ := hx
    exact Subring.subset_closure (Set.mem_union_right _ ⟨⟨h, hH h.2⟩, rfl⟩)

/-- A nonzero element of a smaller division closure is a unit of a larger one. -/
theorem isUnit_of_mem_D_of_le (L : LinnellDatum K G U) {H₀ H : Subgroup G} (h : H₀ ≤ H)
    (hdivH₀ : ∀ x : ↥(L.D H₀), x ≠ 0 → IsUnit x) {t : U} (ht : t ∈ L.D H₀) (hne : t ≠ 0) :
    IsUnit (⟨t, L.D_mono h ht⟩ : ↥(L.D H)) := by
  have hne' : (⟨t, ht⟩ : ↥(L.D H₀)) ≠ 0 := by
    intro h0
    exact hne (congrArg Subtype.val h0)
  exact (hdivH₀ ⟨t, ht⟩ hne').map (Subring.inclusion (L.D_mono h))

/-- The `IsUnit` statement transported to the subalgebra `Dsub L H`. -/
theorem isUnit_of_mem_Dsub_of_le (L : LinnellDatum K G U) {H₀ H : Subgroup G} (h : H₀ ≤ H)
    (hdivH₀ : ∀ x : ↥(L.D H₀), x ≠ 0 → IsUnit x) {t : U} (ht : t ∈ L.D H₀) (hne : t ≠ 0) :
    IsUnit (⟨t, L.D_mono h ht⟩ : ↥(Dsub L H)) :=
  isUnit_of_mem_D_of_le L h hdivH₀ ht hne

/-- A subgroup of a torsion-free group, intersected with it, is torsion free. -/
theorem isTorsionFree_inf {G : Type*} [Group G] (G' : Subgroup G)
    (hG'tf : Work.ORLocInd.IsTorsionFree G') (H : Subgroup G) :
    Work.ORLocInd.IsTorsionFree ↥(H ⊓ G') :=
  Work.ORLocInd.IsTorsionFree.of_injective (Subgroup.inclusion inf_le_right)
    (Subgroup.inclusion_injective inf_le_right) hG'tf

/-- `gen g ^ j`, as an element of `U`. -/
def genZPow (L : LinnellDatum K G U) (g : G) (j : ℤ) : U := ↑((L.gen g) ^ j)

@[simp] theorem genZPow_zero (L : LinnellDatum K G U) (g : G) : genZPow L g 0 = 1 := by
  simp [genZPow]

theorem genZPow_add (L : LinnellDatum K G U) (g : G) (j k : ℤ) :
    genZPow L g (j + k) = genZPow L g j * genZPow L g k := by
  simp [genZPow, zpow_add]

theorem genZPow_eq_gen (L : LinnellDatum K G U) (H : Subgroup G) (s : H) (j : ℤ) :
    genZPow L (s : G) j = (L.gen (((s ^ j : H) : G)) : U) := by
  have h : (((s ^ j : H) : G)) = (s : G) ^ j := Subgroup.coe_zpow H s j
  show (↑((L.gen (s : G)) ^ j) : U) = (L.gen (((s ^ j : H) : G)) : U)
  rw [h, ← map_zpow]

/-- A power of `gen s` lies in `R`. -/
theorem zpow_gen_mem_TorsionRsub (L : LinnellDatum K G U) (N H : Subgroup G) (s : H) (j : ℤ) :
    genZPow L (s : G) j ∈ TorsionRsub L N H := by
  rw [genZPow_eq_gen L H s j]
  exact gen_mem_TorsionRsub L N H (s ^ j)

/-! ## Right multiplication by `gen s ^ j` on `R` -/

/-- Right multiplication by `gen s ^ j` on `R`, as a `K`-linear map. -/
def rightMulU (L : LinnellDatum K G U) (N H : Subgroup G) (s : H) (j : ℤ) :
    ↥(TorsionRsub L N H) →ₗ[K] ↥(TorsionRsub L N H) where
  toFun y := ⟨(y : U) * genZPow L (s : G) j,
    (TorsionRsub L N H).mul_mem y.2 (zpow_gen_mem_TorsionRsub L N H s j)⟩
  map_add' a b := by
    apply Subtype.ext
    show (((a : U) + (b : U)) * genZPow L (s : G) j)
      = (a : U) * genZPow L (s : G) j + (b : U) * genZPow L (s : G) j
    rw [add_mul]
  map_smul' k a := by
    apply Subtype.ext
    show ((k • (a : U)) * genZPow L (s : G) j) = k • ((a : U) * genZPow L (s : G) j)
    rw [Algebra.smul_def, Algebra.smul_def, mul_assoc]

@[simp] theorem rightMulU_coe (L : LinnellDatum K G U) (N H : Subgroup G) (s : H) (j : ℤ)
    (y : ↥(TorsionRsub L N H)) :
    ((rightMulU L N H s j y : ↥(TorsionRsub L N H)) : U)
      = (y : U) * genZPow L (s : G) j := rfl

theorem rightMulU_add (L : LinnellDatum K G U) (N H : Subgroup G) (s : H) (j k : ℤ)
    (y : ↥(TorsionRsub L N H)) :
    rightMulU L N H s j (rightMulU L N H s k y) = rightMulU L N H s (k + j) y := by
  apply Subtype.ext
  rw [rightMulU_coe, rightMulU_coe, rightMulU_coe, mul_assoc, ← genZPow_add]

theorem rightMulU_neg (L : LinnellDatum K G U) (N H : Subgroup G) (s : H) (j : ℤ)
    (y : ↥(TorsionRsub L N H)) :
    rightMulU L N H s (-j) (rightMulU L N H s j y) = y := by
  apply Subtype.ext
  rw [rightMulU_coe, rightMulU_coe]
  rw [mul_assoc, ← genZPow_add, add_neg_cancel, genZPow_zero, mul_one]

end

end Work.ORFinal.TorsionData
