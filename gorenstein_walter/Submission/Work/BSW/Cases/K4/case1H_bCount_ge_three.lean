import Mathlib
import Submission.Work.BSW.Cases.K4.case1Aux

namespace Work.BSW.Cases.K4

open Work.GW2

/-- For an involution `u`, the involutions lying in the left coset `u H` are exactly the
involutions lying in the right coset `H u`: an involution equals its own inverse, and inversion
swaps the two cosets. -/
private lemma involutions_coe_mul_eq_mul_coe {G : Type} [Group G] (H : Subgroup G) {u : G}
    (hu : orderOf u = 2) :
    ({y : G | orderOf y = 2 ∧ u⁻¹ * y ∈ H} : Set G) =
      {y : G | orderOf y = 2 ∧ ∃ h ∈ H, y = h * u} := by
  have huu : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu, pow_two] at this
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  ext y
  constructor
  · rintro ⟨hy2, hyh⟩
    have hyy : y⁻¹ = y := by
      have hyy2 : y * y = 1 := by
        have := pow_orderOf_eq_one y
        rwa [hy2, pow_two] at this
      exact inv_eq_of_mul_eq_one_right hyy2
    refine ⟨hy2, (u⁻¹ * y)⁻¹, H.inv_mem hyh, ?_⟩
    calc y = y⁻¹ := hyy.symm
      _ = (u * (u⁻¹ * y))⁻¹ := by rw [mul_inv_cancel_left]
      _ = (u⁻¹ * y)⁻¹ * u⁻¹ := by rw [mul_inv_rev]
      _ = (u⁻¹ * y)⁻¹ * u := by rw [huinv]
  · rintro ⟨hy2, h, hhH, rfl⟩
    refine ⟨hy2, ?_⟩
    have hyy : (h * u)⁻¹ = h * u := by
      have hyy2 : (h * u) * (h * u) = 1 := by
        have := pow_orderOf_eq_one (h * u)
        rwa [hy2, pow_two] at this
      exact inv_eq_of_mul_eq_one_right hyy2
    have hkey : u⁻¹ * (h * u) = h⁻¹ := by
      calc u⁻¹ * (h * u) = u⁻¹ * (h * u)⁻¹ := by rw [hyy]
        _ = u⁻¹ * (u⁻¹ * h⁻¹) := by rw [mul_inv_rev, huinv]
        _ = (u⁻¹ * u⁻¹) * h⁻¹ := by group
        _ = h⁻¹ := by rw [← mul_inv_rev, huu, inv_one, one_mul]
    rw [hkey]
    exact H.inv_mem hhH

/-- Two elements of the same left coset of `H` give the same involution count:
`g⁻¹ x ∈ H` implies that `y ↦ g⁻¹ y ∈ H` and `y ↦ x⁻¹ y ∈ H` define the same set of `y`. -/
private lemma cosetInvCount_eq_of_mem_leftCoset {G : Type} [Group G] (H : Subgroup G) {g x : G}
    (hxg : g⁻¹ * x ∈ H) :
    cosetInvCount H g = cosetInvCount H x := by
  rw [cosetInvCount, cosetInvCount]
  refine congrArg Set.ncard ?_
  ext y
  constructor
  · rintro ⟨hy2, hyg⟩
    refine ⟨hy2, ?_⟩
    have hx_eq : x = g * (g⁻¹ * x) := by group
    have hsplit : x⁻¹ * y = (g⁻¹ * x)⁻¹ * (g⁻¹ * y) := by rw [hx_eq]; group
    rw [hsplit]
    exact H.mul_mem (H.inv_mem hxg) hyg
  · rintro ⟨hy2, hyx⟩
    refine ⟨hy2, ?_⟩
    have hsplit : g⁻¹ * y = (g⁻¹ * x) * (x⁻¹ * y) := by group
    rw [hsplit]
    exact H.mul_mem hxg hyx

/-- Every nontrivial coset of `H` contains at most two involutions, under the two counting
hypotheses of the `|K| = 4`, Case 1 setting. -/
private lemma cosetInvCount_le_two {G : Type} [Group G] [Finite G] (H : Subgroup G)
    (hle2 : ∀ u : G, u ∉ H → orderOf u = 2 →
      Nat.card ↥(Subgroup.centralizer ({u} : Set G) ⊓ H) ≤ 2)
    (hcoset : ∀ u : G, orderOf u = 2 → u ∉ H →
      ({y : G | orderOf y = 2 ∧ ∃ h ∈ H, y = h * u} : Set G).ncard =
        Nat.card ↥(Subgroup.centralizer ({u} : Set G) ⊓ H))
    {g : G} (hg : g ∉ H) : cosetInvCount H g ≤ 2 := by
  by_cases h0 : cosetInvCount H g = 0
  · omega
  · have hpos : 0 < cosetInvCount H g := Nat.pos_of_ne_zero h0
    rw [cosetInvCount] at hpos
    obtain ⟨x, hx2, hxg⟩ :=
      (Set.ncard_pos (Set.toFinite ({x : G | orderOf x = 2 ∧ g⁻¹ * x ∈ H} : Set G))).mp hpos
    have hxH : x ∉ H := by
      intro hx
      apply hg
      have hg_inv : g⁻¹ ∈ H := by
        have hgg : g⁻¹ = (g⁻¹ * x) * x⁻¹ := by group
        rw [hgg]
        exact H.mul_mem hxg (H.inv_mem hx)
      exact inv_mem_iff.mp hg_inv
    calc cosetInvCount H g = cosetInvCount H x := cosetInvCount_eq_of_mem_leftCoset H hxg
      _ = ({y : G | orderOf y = 2 ∧ ∃ h ∈ H, y = h * x} : Set G).ncard := by
            rw [cosetInvCount, involutions_coe_mul_eq_mul_coe H hx2]
      _ = Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ H) := hcoset x hx2 hxH
      _ ≤ 2 := hle2 x hxH hx2

theorem case1H_bCount_ge_three {G : Type} [Group G] [Finite G] (H : Subgroup G)
    (hle2 : ∀ u : G, u ∉ H → orderOf u = 2 →
      Nat.card ↥(Subgroup.centralizer ({u} : Set G) ⊓ H) ≤ 2)
    (hcoset : ∀ u : G, orderOf u = 2 → u ∉ H →
      ({y : G | orderOf y = 2 ∧ ∃ h ∈ H, y = h * u} : Set G).ncard =
        Nat.card ↥(Subgroup.centralizer ({u} : Set G) ⊓ H)) :
    ∀ n : ℕ, 3 ≤ n → Work.GW2.bCount H n = 0 := by
  classical
  have hkey : ∀ g : G, g ∉ H → cosetInvCount H g ≤ 2 :=
    fun g hg => cosetInvCount_le_two H hle2 hcoset hg
  intro n hn
  have hempty :
      {c : G ⧸ H | c ≠ ((1 : G) : G ⧸ H) ∧ cosetInvCount H (Quotient.out c) = n} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro c ⟨hc1, hc2⟩
    have hgH : Quotient.out c ∉ H := by
      intro hmem
      apply hc1
      rw [← Quotient.out_eq c]
      refine QuotientGroup.eq.mpr ?_
      simpa using H.inv_mem hmem
    have hle := hkey (Quotient.out c) hgH
    omega
  rw [Work.GW2.bCount, hempty, Set.ncard_empty]

end Work.BSW.Cases.K4
