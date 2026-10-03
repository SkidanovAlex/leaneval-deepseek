import Mathlib
import Submission.Work.OROneRel.conjugateHnnSubgroups

namespace Work.OROneRel

universe u

/-- Given a homomorphism `θ : H →* G` and an element `t : G`, this is the "`ℤ`-invariant part"
of `θ.range`: the set of `g : G` all of whose conjugates `t^n * g * t^(-n)` (`n : ℤ`) lie in
`θ.range`.  It is a subgroup of `G` on which conjugation by `t` acts by an automorphism. -/
theorem conjugateHnnSubgroups_zInvariant {H G : Type u} [Group H] [Group G] (θ : H →* G) (t : G)
    (hθ : Function.Injective θ) :
    ∃ (A : Subgroup H) (φ : A ≃* A),
      (∀ a : H, a ∈ A ↔ ∀ n : ℤ, t ^ n * θ a * t ^ (-n) ∈ θ.range) ∧
      (∀ a : A, θ (((φ a : A) : H)) = t⁻¹ * θ ((a : H)) * t) := by
  classical
  -- `S : Subgroup G` is the subgroup of elements all of whose `t`-conjugates lie in `θ.range`.
  let S : Subgroup G :=
    { carrier := {g | ∀ n : ℤ, t ^ n * g * t ^ (-n) ∈ θ.range}
      one_mem' := by intro n; simp
      mul_mem' := by
        intro g h hg hh n
        rw [show t ^ n * (g * h) * t ^ (-n) = (t^n * g * t^(-n)) * (t^n * h * t^(-n)) by group]
        exact mul_mem (hg n) (hh n)
      inv_mem' := by
        intro g hg n
        rw [show t^n * g⁻¹ * t^(-n) = (t^n * g * t^(-n))⁻¹ by group]
        exact inv_mem (hg n) }
  have hSmem : ∀ g : G, g ∈ S ↔ ∀ n : ℤ, t^n * g * t^(-n) ∈ θ.range := fun g => Iff.rfl
  -- `S` is invariant under conjugation by `t` (both directions).
  have hS_conj : ∀ g : G, g ∈ S ↔ t⁻¹ * g * t ∈ S := by
    intro g
    rw [hSmem g, hSmem (t⁻¹ * g * t)]
    constructor
    · intro hg n
      rw [show t^n * (t⁻¹ * g * t) * t^(-n) = t^(n-1) * g * t^(-(n-1)) by group]
      exact hg (n-1)
    · intro hg n
      have := hg (n+1)
      rwa [show t^(n+1) * (t⁻¹ * g * t) * t^(-(n+1)) = t^n * g * t^(-n) by group] at this
  have hS_conj' : ∀ g : G, g ∈ S ↔ t * g * t⁻¹ ∈ S := by
    intro g
    rw [hSmem g, hSmem (t * g * t⁻¹)]
    constructor
    · intro hg n
      rw [show t^n * (t * g * t⁻¹) * t^(-n) = t^(n+1) * g * t^(-(n+1)) by group]
      exact hg (n+1)
    · intro hg n
      have := hg (n-1)
      rwa [show t^(n-1) * (t * g * t⁻¹) * t^(-(n-1)) = t^n * g * t^(-n) by group] at this
  have hS_le : S ≤ θ.range := by
    intro g hg
    have h := (hSmem g).mp hg 0
    simpa using h
  -- `A = θ⁻¹(S)`; its membership condition is exactly the one in the statement.
  let A : Subgroup H := S.comap θ
  have hAmem : ∀ a : H, a ∈ A ↔ ∀ n : ℤ, t^n * θ a * t^(-n) ∈ θ.range := by
    intro a
    show a ∈ S.comap θ ↔ _
    rw [Subgroup.mem_comap]
    exact hSmem (θ a)
  -- For `a ∈ A`, the element `t⁻¹ θ(a) t` lies in `S`, hence in `θ.range`, so has a unique
  -- preimage under `θ`; that preimage is again in `A`.
  have hmain : ∀ a : A, ∃ b : H, b ∈ A ∧ θ b = t⁻¹ * θ (a : H) * t := by
    intro a
    have hSa : θ (a : H) ∈ S := Subgroup.mem_comap.mp a.2
    have h1 : t⁻¹ * θ (a : H) * t ∈ S := (hS_conj (θ (a:H))).mp hSa
    have h2 : t⁻¹ * θ (a : H) * t ∈ θ.range := hS_le h1
    refine ⟨Function.invFun θ (t⁻¹ * θ (a : H) * t), ?_, Function.invFun_eq h2⟩
    rw [Subgroup.mem_comap, Function.invFun_eq h2]
    exact h1
  -- The same with `t` replaced by `t⁻¹`, giving the inverse map.
  have hmain' : ∀ b : A, ∃ a : H, a ∈ A ∧ θ a = t * θ (b : H) * t⁻¹ := by
    intro b
    have hSb : θ (b : H) ∈ S := Subgroup.mem_comap.mp b.2
    have h1 : t * θ (b : H) * t⁻¹ ∈ S := (hS_conj' (θ (b:H))).mp hSb
    have h2 : t * θ (b : H) * t⁻¹ ∈ θ.range := hS_le h1
    refine ⟨Function.invFun θ (t * θ (b : H) * t⁻¹), ?_, Function.invFun_eq h2⟩
    rw [Subgroup.mem_comap, Function.invFun_eq h2]
    exact h1
  -- The map `φ` and its inverse, and the defining intertwining identity.
  let φto : A → A := fun a => ⟨Classical.choose (hmain a), (Classical.choose_spec (hmain a)).1⟩
  have hφto : ∀ a : A, θ ((φto a : A) : H) = t⁻¹ * θ (a : H) * t := fun a =>
    (Classical.choose_spec (hmain a)).2
  let φinv : A → A := fun b => ⟨Classical.choose (hmain' b), (Classical.choose_spec (hmain' b)).1⟩
  have hφinv : ∀ b : A, θ ((φinv b : A) : H) = t * θ (b : H) * t⁻¹ := fun b =>
    (Classical.choose_spec (hmain' b)).2
  have hleft : ∀ a : A, φinv (φto a) = a := by
    intro a
    apply Subtype.ext
    apply hθ
    rw [hφinv (φto a), hφto a]
    group
  have hright : ∀ b : A, φto (φinv b) = b := by
    intro b
    apply Subtype.ext
    apply hθ
    rw [hφto (φinv b), hφinv b]
    group
  have hmul : ∀ a b : A, φto (a * b) = φto a * φto b := by
    intro a b
    apply Subtype.ext
    apply hθ
    rw [Subgroup.coe_mul, map_mul, hφto a, hφto b]
    rw [hφto (a * b), Subgroup.coe_mul, map_mul]
    group
  let φ : A ≃* A :=
    { toFun := φto
      invFun := φinv
      left_inv := hleft
      right_inv := hright
      map_mul' := hmul }
  exact ⟨A, φ, hAmem, fun a => hφto a⟩

end Work.OROneRel
