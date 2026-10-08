import Mathlib

namespace Work.BSW.Cases.K4

/-- **Gorenstein–Walter, auxiliary (K4).** Let `A` be a finite group on which an involution `t`
acts (via conjugation, `t` normalizing `A`) with trivial fixed points. Then `A` is abelian and
`t` inverts every element of `A`.

Proof: conjugation by `t` defines an order-two automorphism `c` of `A`. The map
`f : a ↦ a * (c a)⁻¹` satisfies `c (f a) = (f a)⁻¹`, i.e. `f a` is inverted by `c`; and `f` is
injective because `f a = f b` forces `b⁻¹ a = c (b⁻¹ a)`, so `b⁻¹ a = 1`. Since `A` is finite,
`f` is surjective, so every element of `A` is inverted by `c`, i.e. `t * a * t⁻¹ = a⁻¹`. Then
`(a * b)⁻¹ = a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹`, whence `A` is abelian. -/
theorem inverts_of_fixedPointFree_involution {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) (t : G) (ht2 : t * t = 1) (hnorm : t ∈ Subgroup.normalizer (A : Set G))
    (hfix : ∀ a ∈ A, t * a * t⁻¹ = a → a = 1) :
    (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ ∀ a ∈ A, t * a * t⁻¹ = a⁻¹ := by
  -- `t` normalizes `A`, so conjugation by `t` sends `A` to itself.
  have hnorm_iff : ∀ x : G, x ∈ A ↔ t * x * t⁻¹ ∈ A := Subgroup.mem_normalizer_iff.mp hnorm
  -- the conjugation automorphism of `A` induced by `t`.
  let c : A → A := fun a => ⟨t * (a : G) * t⁻¹, (hnorm_iff (a : G)).mp a.2⟩
  have hc : ∀ a : A, ((c a : A) : G) = t * (a : G) * t⁻¹ := fun a => rfl
  have hc_one : c 1 = 1 := by ext; simp [hc]
  have hc_mul : ∀ a b : A, c (a * b) = c a * c b := by
    intro a b
    ext
    simp only [hc, Subgroup.coe_mul]
    group
  have htinvt : t⁻¹ * t⁻¹ = (1 : G) := by rw [← mul_inv_rev, ht2, inv_one]
  have hc_invol : ∀ a : A, c (c a) = a := by
    intro a
    ext
    rw [hc, hc]
    simp only [mul_assoc]
    rw [htinvt, mul_one, ← mul_assoc, ht2, one_mul]
  have hc_inv : ∀ a : A, c a⁻¹ = (c a)⁻¹ := by
    intro a
    have h : c a * c a⁻¹ = 1 := by rw [← hc_mul, mul_inv_cancel, hc_one]
    exact eq_inv_of_mul_eq_one_right h
  -- every value of `a ↦ a * (c a)⁻¹` is inverted by `c`.
  have hcf : ∀ a : A, c (a * (c a)⁻¹) = (a * (c a)⁻¹)⁻¹ := by
    intro a
    rw [hc_mul, hc_inv, hc_invol, mul_inv_rev, inv_inv]
  have hinj : Function.Injective (fun a : A => a * (c a)⁻¹) := by
    intro a b hab
    have h3 : b⁻¹ * a = (c b)⁻¹ * c a := by
      have h := congrArg (fun x : A => b⁻¹ * x * c a) hab
      simpa [mul_assoc] using h
    have h4 : c (b⁻¹ * a) = (c b)⁻¹ * c a := by rw [hc_mul, hc_inv]
    have h1 : b⁻¹ * a = c (b⁻¹ * a) := h3.trans h4.symm
    -- so `b⁻¹ * a` is a fixed point of `c`, hence trivial by hypothesis.
    have hfix' : ((b⁻¹ * a : A) : G) = 1 := by
      apply hfix ((b⁻¹ * a : A) : G) (b⁻¹ * a).2
      have hh := congrArg (fun y : A => (y : G)) h1
      simpa [hc] using hh.symm
    have h2 : (b⁻¹ * a : A) = 1 := Subtype.ext hfix'
    have hb : b * (b⁻¹ * a) = a := by group
    rw [← hb, h2, mul_one]
  have hsurj : Function.Surjective (fun a : A => a * (c a)⁻¹) :=
    Finite.surjective_of_injective hinj
  have hinv : ∀ a : A, c a = a⁻¹ := by
    intro a
    obtain ⟨b, hb⟩ := hsurj a
    rw [← hb, hcf]
  have hmain : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹ := by
    intro a ha
    have h := congrArg (fun x : A => (x : G)) (hinv ⟨a, ha⟩)
    simpa [hc] using h
  refine ⟨?_, hmain⟩
  -- abelian: `(x * y)⁻¹ = x⁻¹ * y⁻¹` shows inverses commute, then replace `x, y` by `x⁻¹, y⁻¹`.
  have key : ∀ x ∈ A, ∀ y ∈ A, x⁻¹ * y⁻¹ = y⁻¹ * x⁻¹ := by
    intro x hx y hy
    have h1 : (x * y)⁻¹ = x⁻¹ * y⁻¹ := by
      rw [← hmain (x * y) (A.mul_mem hx hy), ← hmain x hx, ← hmain y hy]; group
    have h2 : (x * y)⁻¹ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    rw [h1] at h2
    exact h2
  intro a ha b hb
  simpa using key a⁻¹ (A.inv_mem ha) b⁻¹ (A.inv_mem hb)

end Work.BSW.Cases.K4
