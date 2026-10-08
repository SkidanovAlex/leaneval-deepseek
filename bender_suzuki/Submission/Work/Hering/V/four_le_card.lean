import Mathlib
import Submission.Work.Hering.InvSubgroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `V = Inv(G) ∪ {1}` has at least four elements

If `G` is a finite group with `DTInv G` (double transitivity on involutions) and `HasFourGroup G`
(two distinct commuting involutions), then `V = Inv(G) ∪ {1} = invSubgroup hDT h4` contains the two
distinct involutions `a`, `b` supplied by `h4`, together with `1`: three distinct elements. Since
`a` is an element of order `2` of `V`, Lagrange's theorem gives `2 ∣ |V|`, and `|V| ≥ 3`, whence
`4 ≤ |V|`.
-/

namespace Work.Hering.V

theorem four_le_card {G : Type*} [Group G] (hDT : DTInv G) (h4 : HasFourGroup G) [Finite G] :
    4 ≤ Nat.card ↥(invSubgroup hDT h4) := by
  classical
  -- keep a copy of `h4` under a fresh name so that it survives the destruction below
  have h4' := h4
  obtain ⟨a, b, ha2, hb2, hab, hcomm⟩ := h4
  have haI : a ∈ involutions G := ha2
  have hbI : b ∈ involutions G := hb2
  let H : Subgroup G := invSubgroup hDT h4'
  have haS : a ∈ H := involutions_subset_invSubgroup hDT h4' haI
  have hbS : b ∈ H := involutions_subset_invSubgroup hDT h4' hbI
  have h1S : (1 : G) ∈ H := H.one_mem
  have ha1 : a ≠ 1 := ne_one_of_mem_involutions haI
  have hb1 : b ≠ 1 := ne_one_of_mem_involutions hbI
  -- `a`, viewed in `H`, has order `2`
  have hord : orderOf (⟨a, haS⟩ : ↥H) = 2 := by
    apply orderOf_eq_prime
    · have h : (a : G) ^ 2 = 1 := by
        simpa [pow_two] using sq_eq_one_of_orderOf_eq_two haI
      ext
      simpa using h
    · intro hcon
      exact ha1 (congrArg Subtype.val hcon)
  -- Lagrange: the order of `a` divides `|H|`
  have hdvd : 2 ∣ Nat.card ↥H := by
    simpa [hord] using orderOf_dvd_natCard (⟨a, haS⟩ : ↥H)
  -- `1`, `a`, `b` are three distinct elements of `H`
  have hge3 : 3 ≤ Nat.card ↥H := by
    have hinj : Function.Injective (![(⟨1, h1S⟩ : ↥H), ⟨a, haS⟩, ⟨b, hbS⟩]) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [Subtype.ext_iff]
    have h := Nat.card_le_card_of_injective _ hinj
    simpa using h
  have hmain : 4 ≤ Nat.card ↥H := by
    obtain ⟨k, hk⟩ := hdvd
    omega
  exact hmain

end Work.Hering.V
