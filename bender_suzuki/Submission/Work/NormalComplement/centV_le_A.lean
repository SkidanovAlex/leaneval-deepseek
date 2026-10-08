import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise

namespace Work.NormalComplement

/-- If `V` normalizes `A`, `V = A ⊔ P`, `|P|` and `|A|` are coprime, and `P` meets the
centralizer of `A` trivially, then the centralizer of `A` inside `V` is contained in `A`.

The proof: the conjugation action of `V` on `A` is a homomorphism `φ : V →* Aut A` whose
kernel is `V ∩ C_G(A)`.  For `x ∈ V ∩ C_G(A)` write `x = a * p` with `a ∈ A`, `p ∈ P`
(possible since `P` normalizes `A`).  Then `φ p = (φ a)⁻¹`, so `orderOf (φ p) = orderOf (φ a)`
divides both `|P|` (through `p ∈ P`) and `|A|` (through `a ∈ A`).  Coprimality forces
`φ p = 1`, i.e. `p ∈ C_G(A)`, hence `p ∈ P ∩ C_G(A) = ⊥`, so `p = 1` and `x = a ∈ A`. -/
theorem centV_le_A {G : Type} [Group G] [Finite G] {A V P : Subgroup G}
    (hAV : V ≤ Subgroup.normalizer (A : Set G))
    (hsup : A ⊔ P = V)
    (hcop : Nat.Coprime (Nat.card ↥P) (Nat.card ↥A))
    (hCP : P ⊓ Subgroup.centralizer (A : Set G) = ⊥) :
    V ⊓ Subgroup.centralizer (A : Set G) ≤ A := by
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxV, hxC⟩ := hx
  -- `A ≤ V`, `P ≤ V`, and `P ≤ N_G(A)`
  have hA_le_V : A ≤ V := le_sup_left.trans_eq hsup
  have hP_le_V : P ≤ V := le_sup_right.trans_eq hsup
  have hPV : P ≤ Subgroup.normalizer (A : Set G) := hP_le_V.trans hAV
  -- since `P` normalizes `A`, `V = A ⊔ P = A * P` pointwise
  have hVmul : (↑V : Set G) = (↑A : Set G) * (↑P : Set G) := by
    rw [← hsup]; exact Subgroup.coe_mul_of_right_le_normalizer_left A P hPV
  have hxmul : x ∈ ((↑A : Set G) * (↑P : Set G)) := by rw [← hVmul]; exact hxV
  obtain ⟨a, ha, p, hp, hap⟩ := hxmul
  -- the conjugation action of `V` on `A`
  let φ : ↥V →* MulAut ↥A := (Subgroup.normalizerMonoidHom A).comp (Subgroup.inclusion hAV)
  let x' : ↥V := ⟨x, hxV⟩
  let a' : ↥V := ⟨a, hA_le_V ha⟩
  let p' : ↥V := ⟨p, hP_le_V hp⟩
  -- `x` centralizes `A`, so it acts trivially
  have hφx : φ x' = 1 := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [MulAut.one_apply]
    show (↑x * ↑b * (↑x)⁻¹ : G) = ↑b
    have hcomm : (↑b : G) * x = x * ↑b :=
      (Subgroup.mem_centralizer_iff.mp hxC) (↑b) b.2
    rw [← hcomm]
    group
  -- `x' = a' * p'` in `V`
  have hx'_eq : x' = a' * p' := by
    apply Subtype.ext
    show x = a * p
    exact hap.symm
  have hφ1 : φ a' * φ p' = 1 := by
    rw [← map_mul, ← hx'_eq, hφx]
  have hp'_eq : φ p' = (φ a')⁻¹ := eq_inv_of_mul_eq_one_right hφ1
  -- order divisibility: `orderOf (φ p')` divides `|P|` and `|A|`
  have hmP : orderOf (φ p') ∣ Nat.card ↥P := by
    refine (orderOf_map_dvd φ p').trans ?_
    rw [← Subgroup.orderOf_coe p']
    exact Subgroup.orderOf_dvd_natCard P hp
  have hmA : orderOf (φ p') ∣ Nat.card ↥A := by
    rw [hp'_eq, orderOf_inv]
    refine (orderOf_map_dvd φ a').trans ?_
    rw [← Subgroup.orderOf_coe a']
    exact Subgroup.orderOf_dvd_natCard A ha
  have hm1 : orderOf (φ p') = 1 := by
    have hdvd : orderOf (φ p') ∣ Nat.gcd (Nat.card ↥P) (Nat.card ↥A) := Nat.dvd_gcd hmP hmA
    rw [hcop.gcd_eq_one] at hdvd
    exact Nat.dvd_one.mp hdvd
  have hφp : φ p' = 1 := orderOf_eq_one_iff.mp hm1
  -- hence `p` centralizes `A`
  have hpC : p ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hval : (↑(φ p' ⟨b, hb⟩) : G) = b := by
      have h2 : φ p' ⟨b, hb⟩ = (1 : MulAut ↥A) ⟨b, hb⟩ := by rw [hφp]
      rw [MulAut.one_apply] at h2
      exact congrArg (fun y : ↥A => (y : G)) h2
    have hcoe : (↑(φ p' ⟨b, hb⟩) : G) = p * b * p⁻¹ := rfl
    rw [hcoe] at hval
    have h1 : p * b * p⁻¹ = b := hval
    calc b * p = (p * b * p⁻¹) * p := by rw [h1]
         _ = p * b := by group
  have hp1 : p = 1 := by
    have : p ∈ P ⊓ Subgroup.centralizer (A : Set G) := ⟨hp, hpC⟩
    rw [hCP] at this
    exact Subgroup.mem_bot.mp this
  have hxa : x = a := by
    rw [← hap, hp1]
    group
  rw [hxa]
  exact ha

end Work.NormalComplement
