import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

namespace Work.ThmF.ChV3.Prove

theorem conj_coset_injective {G : Type} [Group G] {P R Y : Subgroup G} {u : G}
    (hYP : Y ≤ Subgroup.centralizer (P : Set G))
    (hu : u ∈ R) (huP : u ∉ P)
    (hfpf : ∀ y ∈ Y, y ≠ 1 → y * u * y⁻¹ * u⁻¹ ∉ P) :
    Function.Injective (fun w : ↥Y × ↥P => (w.2 : G) * ((w.1 : G) * u * (w.1 : G)⁻¹)) := by
  rintro ⟨⟨y1, hy1⟩, ⟨p1, hp1⟩⟩ ⟨⟨y2, hy2⟩, ⟨p2, hp2⟩⟩ heq
  simp only at heq
  -- Elements of `Y` commute with elements of `P`.
  have hcomm : ∀ (y : G), y ∈ Y → ∀ p ∈ P, p * y = y * p := by
    intro y hy p hp
    have h : y ∈ Subgroup.centralizer (P : Set G) := hYP hy
    rw [Subgroup.mem_centralizer_iff] at h
    exact h p hp
  -- Hence conjugation by an element of `Y` preserves `P`.
  have hconj : ∀ (y : G), y ∈ Y → ∀ x ∈ P, y⁻¹ * x * y ∈ P := by
    intro y hy x hx
    have hc : x * y = y * x := hcomm y hy x hx
    have hxy : y⁻¹ * x * y = x := by
      calc y⁻¹ * x * y = y⁻¹ * (x * y) := by group
        _ = y⁻¹ * (y * x) := by rw [hc]
        _ = x := by group
    rw [hxy]; exact hx
  -- From `p1 * (y1 u y1⁻¹) = p2 * (y2 u y2⁻¹)` we get that
  -- `(y1 u y1⁻¹) * (y2 u y2⁻¹)⁻¹ ∈ P`.
  have hab : (y1 * u * y1⁻¹) * (y2 * u * y2⁻¹)⁻¹ ∈ P := by
    have h1 : (y1 * u * y1⁻¹) * (y2 * u * y2⁻¹)⁻¹ = p1⁻¹ * p2 := by
      have h := congrArg (fun t => p1⁻¹ * t) heq
      have ha : y1 * u * y1⁻¹ = p1⁻¹ * (p2 * (y2 * u * y2⁻¹)) := by simpa using h
      rw [ha]; group
    rw [h1]; exact P.mul_mem (P.inv_mem hp1) hp2
  set z := y1⁻¹ * y2 with hz
  have key : (y1 * u * y1⁻¹) * (y2 * u * y2⁻¹)⁻¹ = y2 * (z⁻¹ * u * z * u⁻¹) * y2⁻¹ := by
    simp only [hz]; group
  -- Conjugating back by `y2 ∈ Y` (which preserves `P`) yields `z⁻¹ u z u⁻¹ ∈ P`.
  have hq : z⁻¹ * u * z * u⁻¹ ∈ P := by
    have hmem : y2 * (z⁻¹ * u * z * u⁻¹) * y2⁻¹ ∈ P := by rw [← key]; exact hab
    have hc := hconj y2 hy2 (y2 * (z⁻¹ * u * z * u⁻¹) * y2⁻¹) hmem
    rwa [show y2⁻¹ * (y2 * (z⁻¹ * u * z * u⁻¹) * y2⁻¹) * y2 = z⁻¹ * u * z * u⁻¹ by group] at hc
  have hzY : z ∈ Y := by rw [hz]; exact Y.mul_mem (Y.inv_mem hy1) hy2
  -- The fixed-point-free hypothesis forces `z = 1`.
  have hz1 : z = 1 := by
    by_contra hz'
    have hzinv : z⁻¹ ≠ 1 := fun h => hz' (by rw [← inv_inv z, h, inv_one])
    have hq' : z⁻¹ * u * (z⁻¹)⁻¹ * u⁻¹ ∈ P := by simpa using hq
    exact (hfpf z⁻¹ (Y.inv_mem hzY) hzinv) hq'
  -- Consequently `y2 = y1` and then `p1 = p2`.
  have hy_eq : y2 = y1 := by
    calc y2 = y1 * (y1⁻¹ * y2) := by group
      _ = y1 * z := by rw [hz]
      _ = y1 * 1 := by rw [hz1]
      _ = y1 := by rw [mul_one]
  have hp_eq : p1 = p2 := by
    apply mul_right_cancel (b := y1 * u * y1⁻¹)
    rw [heq, show y2 * u * y2⁻¹ = y1 * u * y1⁻¹ by rw [hy_eq]]
  exact Prod.ext (Subtype.ext hy_eq.symm) (Subtype.ext hp_eq)

end Work.ThmF.ChV3.Prove
