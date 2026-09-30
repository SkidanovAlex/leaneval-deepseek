import Mathlib
import Submission.Work.BW.DefsB

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary definitions for B2c (`closedSub_structure`)

Characters on the torus `G_m^N`, the group-law helpers, the character lattice of a subgroup,
its saturation, and the kernel of a lattice of characters.
-/

namespace Work.BW

open Finset

/-- Torus points of `G_m^N`: all coordinates are nonzero. -/
def Tor (N : ℕ) : Set (Fin N → ℂ) := {y | ∀ i, y i ≠ 0}

/-- The monomial character `χ_z(y) = ∏ i, y i ^ (z i)`. -/
noncomputable def torChar {N : ℕ} (z : Fin N → ℤ) (y : Fin N → ℂ) : ℂ := ∏ i, (y i) ^ (z i)

/-- Pointwise product of torus points (the group law of `G_m^N`). -/
def tmul {N : ℕ} (x y : Fin N → ℂ) : Fin N → ℂ := fun i => x i * y i

/-- Pointwise inverse of a torus point. -/
noncomputable def tInv {N : ℕ} (x : Fin N → ℂ) : Fin N → ℂ := fun i => (x i)⁻¹

/-- One of the torus `G_m^N`. -/
def tOne (N : ℕ) : Fin N → ℂ := fun _ => 1

theorem torChar_zero {N : ℕ} (y : Fin N → ℂ) : torChar 0 y = 1 := by
  simp [torChar]

theorem torChar_add {N : ℕ} (z w : Fin N → ℤ) {y : Fin N → ℂ} (hy : ∀ i, y i ≠ 0) :
    torChar (z + w) y = torChar z y * torChar w y := by
  have h1 : (∏ i, y i ^ (z i + w i)) = ∏ i, (y i ^ (z i) * y i ^ (w i)) :=
    Finset.prod_congr rfl (fun i _ => zpow_add₀ (hy i) (z i) (w i))
  simp only [torChar, Pi.add_apply]
  rw [h1, Finset.prod_mul_distrib]

theorem torChar_smul {N : ℕ} (c : ℤ) (z : Fin N → ℤ) {y : Fin N → ℂ} (hy : ∀ i, y i ≠ 0) :
    torChar (c • z) y = (torChar z y) ^ c := by
  have h1 : (∏ i, y i ^ (c * z i)) = ∏ i, (y i ^ (z i)) ^ c :=
    Finset.prod_congr rfl (fun i _ => by rw [mul_comm]; exact zpow_mul (y i) (z i) c)
  simp only [torChar, Pi.smul_apply, smul_eq_mul]
  rw [h1, Finset.prod_zpow]

theorem torChar_tmul {N : ℕ} (z : Fin N → ℤ) (x y : Fin N → ℂ) :
    torChar z (tmul x y) = torChar z x * torChar z y := by
  have h1 : (∏ i, (x i * y i) ^ (z i)) = ∏ i, (x i ^ (z i) * y i ^ (z i)) :=
    Finset.prod_congr rfl (fun i _ => mul_zpow (x i) (y i) (z i))
  simp only [torChar, tmul]
  rw [h1, Finset.prod_mul_distrib]

theorem torChar_tInv {N : ℕ} (z : Fin N → ℤ) (x : Fin N → ℂ) :
    torChar z (tInv x) = (torChar z x)⁻¹ := by
  have h1 : (∏ i, (x i)⁻¹ ^ (z i)) = ∏ i, ((x i) ^ (z i))⁻¹ :=
    Finset.prod_congr rfl (fun i _ => inv_zpow (x i) (z i))
  simp only [torChar, tInv]
  rw [h1, Finset.prod_inv_distrib]

/-- A subgroup of the torus `G_m^N`. -/
def IsTorSub {N : ℕ} (K : Set (Fin N → ℂ)) : Prop :=
  K ⊆ Tor N ∧ (∀ x ∈ K, ∀ y ∈ K, tmul x y ∈ K) ∧ tOne N ∈ K ∧ (∀ x ∈ K, tInv x ∈ K)

/-- The character lattice of `K`: integer vectors `z` with `χ_z ≡ 1` on the torus points of `K`. -/
noncomputable def charLat {N : ℕ} (K : Set (Fin N → ℂ)) : Submodule ℤ (Fin N → ℤ) where
  carrier := {z | ∀ y ∈ K, (∀ i, y i ≠ 0) → torChar z y = 1}
  zero_mem' := by intro y _ _; exact torChar_zero y
  add_mem' := by
    intro z w hz hw y hy h
    rw [torChar_add z w h, hz y hy h, hw y hy h, one_mul]
  smul_mem' := by
    intro c z hz y hy h
    rw [torChar_smul c z h, hz y hy h, one_zpow]

/-- The saturation of a sublattice of `ℤ^N`. -/
noncomputable def satLat {N : ℕ} (L : Submodule ℤ (Fin N → ℤ)) : Submodule ℤ (Fin N → ℤ) where
  carrier := {z | ∃ m : ℤ, m ≠ 0 ∧ m • z ∈ L}
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  add_mem' := by
    intro z w ⟨m, hm, hz⟩ ⟨n, hn, hw⟩
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    have h1 : n • (m • z) ∈ L := L.smul_mem n hz
    have h2 : m • (n • w) ∈ L := L.smul_mem m hw
    have e1 : (m * n) • z = n • (m • z) := by rw [mul_comm m n, mul_smul]
    have e2 : (m * n) • w = m • (n • w) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact L.add_mem h1 h2
  smul_mem' := by
    intro c z ⟨m, hm, hz⟩
    refine ⟨m, hm, ?_⟩
    rw [smul_comm]
    exact L.smul_mem c hz

/-- The kernel of a lattice of characters, as a set of torus points. -/
def kerLat {N : ℕ} (L : Submodule ℤ (Fin N → ℤ)) : Set (Fin N → ℂ) :=
  {y | (∀ i, y i ≠ 0) ∧ ∀ z ∈ L, torChar z y = 1}

theorem mem_charLat_iff {N : ℕ} {K : Set (Fin N → ℂ)} {z : Fin N → ℤ} :
    z ∈ charLat K ↔ ∀ y ∈ K, (∀ i, y i ≠ 0) → torChar z y = 1 := Iff.rfl

theorem charLat_anti {N : ℕ} {K K' : Set (Fin N → ℂ)} (hKK : K ⊆ K') :
    charLat K' ≤ charLat K := by
  intro z hz y hy hne
  exact hz y (hKK hy) hne

theorem le_satLat {N : ℕ} (L : Submodule ℤ (Fin N → ℤ)) : L ≤ satLat L := by
  intro z hz
  exact ⟨1, one_ne_zero, by simpa using hz⟩

theorem satLat_sat {N : ℕ} (L : Submodule ℤ (Fin N → ℤ)) {z : Fin N → ℤ} {m : ℤ}
    (hm : m ≠ 0) (hz : m • z ∈ satLat L) : z ∈ satLat L := by
  obtain ⟨n, hn, hnz⟩ := hz
  refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
  have e : (m * n) • z = n • (m • z) := by rw [mul_comm m n, mul_smul]
  rw [e]
  exact hnz

theorem charLat_le_satLat {N : ℕ} (K : Set (Fin N → ℂ)) :
    charLat K ≤ satLat (charLat K) := le_satLat _

theorem kerLat_mono {N : ℕ} {L L' : Submodule ℤ (Fin N → ℤ)} (h : L ≤ L') :
    kerLat L' ⊆ kerLat L := by
  intro y ⟨hy, hyl⟩
  exact ⟨hy, fun z hz => hyl z (h hz)⟩

theorem kerLat_tmul {N : ℕ} (L : Submodule ℤ (Fin N → ℤ)) {x y : Fin N → ℂ}
    (hx : x ∈ kerLat L) (hy : y ∈ kerLat L) : tmul x y ∈ kerLat L := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  refine ⟨fun i => mul_ne_zero (hx1 i) (hy1 i), ?_⟩
  intro z hz
  rw [torChar_tmul, hx2 z hz, hy2 z hz, one_mul]

theorem kerLat_tInv {N : ℕ} (L : Submodule ℤ (Fin N → ℤ)) {x : Fin N → ℂ}
    (hx : x ∈ kerLat L) : tInv x ∈ kerLat L := by
  obtain ⟨hx1, hx2⟩ := hx
  refine ⟨fun i => inv_ne_zero (hx1 i), ?_⟩
  intro z hz
  rw [torChar_tInv, hx2 z hz, inv_one]

theorem kerLat_one {N : ℕ} (L : Submodule ℤ (Fin N → ℤ)) : tOne N ∈ kerLat L := by
  refine ⟨fun i => one_ne_zero, ?_⟩
  intro z hz
  simp [torChar, tOne]

theorem kerLat_sub {N : ℕ} (L : Submodule ℤ (Fin N → ℤ)) {x y : Fin N → ℂ}
    (hx : x ∈ kerLat L) (hy : y ∈ kerLat L) : tmul (tInv x) y ∈ kerLat L :=
  kerLat_tmul L (kerLat_tInv L hx) hy

/-- `InG (cons 0 t)` is exactly `t ∈ Tor N`. -/
theorem inG_cons_iff {N : ℕ} {t : Fin N → ℂ} : InG (Fin.cons (0 : ℂ) t) ↔ t ∈ Tor N := by
  constructor <;> intro h i
  · simpa using h i
  · simpa [InG] using h i

end Work.BW
