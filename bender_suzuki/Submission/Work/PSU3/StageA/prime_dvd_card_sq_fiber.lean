import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageA

open MulAction

/-- If a group of prime order `p` acts on a set `X` with no fixed points, then
`p` divides the cardinality of `X`. -/
theorem isPGroup_dvd_card_of_no_fixedPoints {p : ℕ} [hpp : Fact p.Prime] {P : Type} [Group P]
    (hPg : IsPGroup p P) (X : Type) [MulAction P X]
    (hno : ¬ (fixedPoints P X).Nonempty) : p ∣ Nat.card X := by
  by_contra hcon
  exact hno (hPg.nonempty_fixed_point_of_prime_not_dvd_card X hcon)

/-- **Bender–Suzuki, Stage A fibre divisibility.**  Let `P` be a subgroup of prime order
which normalises a subgroup `Q` and centralises `s ∈ Q`.  If the fibre of the squaring map on
`Q` over `s` has no point centralising `P`, then the order of `P` divides the cardinality of
that fibre. -/
theorem prime_dvd_card_sq_fiber {G : Type} [Group G] [Finite G] {Q P : Subgroup G} {s : G}
    (hs : s ∈ Q) (hp : (Nat.card P).Prime) (hs2 : orderOf s = 2)
    (hPQ : ∀ g ∈ P, ∀ x ∈ Q, g * x * g⁻¹ ∈ Q)
    (hPs : ∀ g ∈ P, g * s * g⁻¹ = s)
    (hfix : ∀ x ∈ Q, x * x = s → x ∈ Subgroup.centralizer (P : Set G) → False) :
    Nat.card P ∣ Nat.card {x : ↥Q // x ^ 2 = (⟨s, hs⟩ : ↥Q)} := by
  classical
  haveI : Fact (Nat.card P).Prime := ⟨hp⟩
  -- the fibre of the squaring map
  set X := {x : ↥Q // x ^ 2 = (⟨s, hs⟩ : ↥Q)} with hX
  -- `P` acts on `X` by conjugation
  letI : MulAction ↥P X :=
    { smul := fun g x => ⟨⟨g.1 * x.1.1 * g.1⁻¹, hPQ g.1 g.2 x.1.1 x.1.2⟩, by
        apply Subtype.ext
        rw [Subgroup.coe_pow]
        have hx : x.1.1 ^ 2 = s := by
          have h := congrArg Subtype.val x.2
          simpa using h
        calc (g.1 * x.1.1 * g.1⁻¹) ^ 2
            = g.1 * (x.1.1 ^ 2) * g.1⁻¹ := by rw [pow_two, pow_two]; group
          _ = g.1 * s * g.1⁻¹ := by rw [hx]
          _ = s := hPs g.1 g.2⟩
      one_smul := fun x => by
        apply Subtype.ext
        apply Subtype.ext
        show (1 : ↥P).1 * x.1.1 * (1 : ↥P).1⁻¹ = x.1.1
        simp
      mul_smul := fun g h x => by
        apply Subtype.ext
        apply Subtype.ext
        show ((g * h : ↥P).1) * x.1.1 * ((g * h : ↥P).1)⁻¹
              = g.1 * (h.1 * x.1.1 * h.1⁻¹) * g.1⁻¹
        simp only [Subgroup.coe_mul]
        group }
  have hpgroup : IsPGroup (Nat.card P) ↥P := IsPGroup.of_card (n := 1) (by simp)
  -- the action has no fixed point, by `hfix`
  apply isPGroup_dvd_card_of_no_fixedPoints hpgroup X
  rintro ⟨x, hx⟩
  rw [mem_fixedPoints] at hx
  apply hfix x.1.1 x.1.2
  · -- `x.1.1 * x.1.1 = s`
    have h := congrArg Subtype.val x.2
    have h2 : x.1.1 ^ 2 = s := by simpa using h
    rwa [pow_two] at h2
  · -- `x.1.1` centralises `P`
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h1 : (⟨g, hg⟩ : ↥P) • x = x := hx ⟨g, hg⟩
    have h2 := congrArg (fun y : X => y.1.1) h1
    have h3 : g * x.1.1 * g⁻¹ = x.1.1 := h2
    calc g * x.1.1 = g * x.1.1 * g⁻¹ * g := by group
      _ = x.1.1 * g := by rw [h3]

end Work.PSU3.StageA
