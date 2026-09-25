import Mathlib

set_option linter.style.haveILetI false

/-!
# Vanishing of `H²` for free groups: every 2-cocycle is a coboundary

Let `k` be a commutative ring, `α` a type, `F = FreeGroup α` the free group on `α`, and
`M : Rep k F` a `k`-linear representation of `F`.  The main result of this file is
`Work.ShafarevichKoch.freeGroup_twoCocycle_is_coboundary`: every function
`f : F × F → M.V` satisfying the cocycle identity

`f (g * h, j) + f (g, h) = ρ g (f (h, j)) + f (g, h * j)`

is the coboundary of a `1`-cochain `x : F → M.V`, i.e.

`ρ g (x h) - x (g * h) + x g = f (g, h)`.

Equivalently: `H²(F, M) = 0` for a free group `F` and arbitrary coefficients `M`.

The mathematical content is the classical fact that a free group has cohomological
dimension one; the proof below makes it explicit.  After normalizing the cocycle,
`c (g, h) = f (g, h) - ρ g (f (1, 1))`, the identity above is exactly the associativity
of the multiplication

`(a, g) * (b, h) = (a + ρ g b + c (g, h), g * h)`

on `M.V × F`, which turns `M.V × F` into a group `T` (a non-split extension of `F` by
the module `M.V`), with `(0, 1)` as identity — the cocycle identity *is* associativity,
and the normalized nature of `c` supplies the identity.  The projection `T → F` has a
section because `F` is free, and the first coordinate of that section is the required
`1`-cochain.
-/

namespace Work.ShafarevichKoch

open Rep

/-- Normalized form of the vanishing of `H²`: if a `2`-cocycle `c` satisfies `c (1, h) = 0`
then it is a coboundary. -/
theorem freeGroup_twoCocycle_is_coboundary_aux {α : Type} {k : Type} [CommRing k]
    (M : Rep k (FreeGroup α)) (c : FreeGroup α × FreeGroup α → M.V)
    (hc : ∀ g h j : FreeGroup α, c (g * h, j) + c (g, h) = M.ρ g (c (h, j)) + c (g, h * j))
    (h1 : ∀ h : FreeGroup α, c (1, h) = 0) :
    ∃ x : FreeGroup α → M.V, ∀ g h : FreeGroup α, M.ρ g (x h) - x (g * h) + x g = c (g, h) := by
  -- `c (g, 1) = 0` follows from the cocycle identity and `c (1, ·) = 0`.
  have hg1 : ∀ g : FreeGroup α, c (g, 1) = 0 := by
    intro g
    have h := hc g 1 1
    simp only [mul_one, h1, map_zero] at h
    exact add_right_cancel h
  -- the inverse-consistency relation, used to produce inverses in the twisted product
  have hkey : ∀ g : FreeGroup α, M.ρ g⁻¹ (c (g, g⁻¹)) = c (g⁻¹, g) := by
    intro g
    have h := hc g g⁻¹ g
    simp only [mul_inv_cancel, inv_mul_cancel, h1, hg1, zero_add, add_zero] at h
    rw [h, Representation.inv_self_apply]
  -- the twisted product on `M.V × FreeGroup α`
  let mul : M.V × FreeGroup α → M.V × FreeGroup α → M.V × FreeGroup α :=
    fun p q => (p.1 + M.ρ p.2 q.1 + c (p.2, q.2), p.2 * q.2)
  let one : M.V × FreeGroup α := (0, 1)
  let inv : M.V × FreeGroup α → M.V × FreeGroup α :=
    fun p => (-(M.ρ p.2⁻¹ (p.1 + c (p.2, p.2⁻¹))), p.2⁻¹)
  letI : Mul (M.V × FreeGroup α) := ⟨mul⟩
  letI : One (M.V × FreeGroup α) := ⟨one⟩
  letI : Inv (M.V × FreeGroup α) := ⟨inv⟩
  have hmul_fst : ∀ p q : M.V × FreeGroup α,
      (p * q).1 = p.1 + M.ρ p.2 q.1 + c (p.2, q.2) := fun p q => rfl
  have hmul_snd : ∀ p q : M.V × FreeGroup α, (p * q).2 = p.2 * q.2 := fun p q => rfl
  have hone_fst : (1 : M.V × FreeGroup α).1 = 0 := rfl
  have hone_snd : (1 : M.V × FreeGroup α).2 = 1 := rfl
  have hinv_fst : ∀ p : M.V × FreeGroup α,
      (p⁻¹).1 = -(M.ρ p.2⁻¹ (p.1 + c (p.2, p.2⁻¹))) := fun p => rfl
  have hinv_snd : ∀ p : M.V × FreeGroup α, (p⁻¹).2 = p.2⁻¹ := fun p => rfl
  -- associativity is exactly the cocycle identity
  have hmul_assoc : ∀ p q r : M.V × FreeGroup α, (p * q) * r = p * (q * r) := by
    rintro ⟨a, g⟩ ⟨b, h⟩ ⟨d, j⟩
    refine Prod.ext ?_ ?_
    · simp only [hmul_fst, hmul_snd, map_add, map_mul, Module.End.mul_apply]
      have key : c (g, h) + c (g * h, j) = M.ρ g (c (h, j)) + c (g, h * j) := by
        rw [add_comm, hc g h j]
      calc a + M.ρ g b + c (g, h) + M.ρ g (M.ρ h d) + c (g * h, j)
          = (a + M.ρ g b + M.ρ g (M.ρ h d)) + (c (g, h) + c (g * h, j)) := by abel
        _ = (a + M.ρ g b + M.ρ g (M.ρ h d)) + (M.ρ g (c (h, j)) + c (g, h * j)) := by
              rw [key]
        _ = a + (M.ρ g b + M.ρ g (M.ρ h d) + M.ρ g (c (h, j))) + c (g, h * j) := by abel
    · simp only [hmul_snd]
      exact mul_assoc g h j
  have hone_mul : ∀ p : M.V × FreeGroup α, 1 * p = p := by
    rintro ⟨a, g⟩
    refine Prod.ext ?_ ?_
    · simp only [hmul_fst, hone_fst, hone_snd, h1, map_one, Module.End.one_apply, zero_add]
      abel
    · simp only [hmul_snd, hone_snd]
      exact one_mul g
  have hinv_mul : ∀ p : M.V × FreeGroup α, p⁻¹ * p = 1 := by
    rintro ⟨a, g⟩
    refine Prod.ext ?_ ?_
    · simp only [hmul_fst, hinv_fst, hinv_snd, hone_fst, map_add]
      rw [hkey g]
      abel
    · simp only [hmul_snd, hinv_snd, hone_snd]
      exact inv_mul_cancel g
  -- the twisted product is a group
  letI : Group (M.V × FreeGroup α) := Group.ofLeftAxioms hmul_assoc hone_mul hinv_mul
  -- the projection onto the second factor
  let π : M.V × FreeGroup α →* FreeGroup α :=
    { toFun := Prod.snd
      map_one' := by simp only [hone_snd]
      map_mul' := by intro p q; simp only [hmul_snd] }
  -- the section supplied by freeness of `FreeGroup α`
  let φ : α → M.V × FreeGroup α := fun i => (0, FreeGroup.of i)
  let s : FreeGroup α →* (M.V × FreeGroup α) := FreeGroup.lift φ
  have hs : ∀ g : FreeGroup α, (s g).2 = g := by
    intro g
    have h := FreeGroup.lift_unique (f := FreeGroup.of) ((π.comp s)) (fun i => rfl) (x := g)
    simpa [π, MonoidHom.comp_apply, FreeGroup.lift_of_apply] using h
  refine ⟨fun g => -(s g).1, fun g h => ?_⟩
  have hm : (s (g * h)).1 = (s g).1 + M.ρ g (s h).1 + c (g, h) := by
    have hh := congrArg Prod.fst (map_mul s g h)
    rw [hmul_fst, hs g, hs h] at hh
    exact hh
  change M.ρ g (-(s h).1) - -(s (g * h)).1 + -(s g).1 = c (g, h)
  rw [map_neg, hm]
  abel

theorem freeGroup_twoCocycle_is_coboundary (α : Type) (k : Type) [CommRing k]
    (M : Rep k (FreeGroup α)) (f : FreeGroup α × FreeGroup α → M.V)
    (hf : ∀ g h j : FreeGroup α, f (g * h, j) + f (g, h) = M.ρ g (f (h, j)) + f (g, h * j)) :
    ∃ x : FreeGroup α → M.V, ∀ g h : FreeGroup α, M.ρ g (x h) - x (g * h) + x g = f (g, h) := by
  -- `f` depends on its second argument only through the product `g * h` at `g = 1`
  have hf1 : ∀ h : FreeGroup α, f (1, h) = f (1, 1) := by
    intro h
    have h' := hf 1 1 h
    simp only [one_mul, map_one, Module.End.one_apply] at h'
    exact (add_left_cancel h').symm
  have hfg1 : ∀ g : FreeGroup α, f (g, 1) = M.ρ g (f (1, 1)) := by
    intro g
    have h' := hf g 1 1
    simp only [mul_one] at h'
    exact add_right_cancel h'
  -- normalization of `f`
  let F : FreeGroup α × FreeGroup α → M.V := fun p => f p - M.ρ p.1 (f (1, 1))
  have hFc : ∀ g h j : FreeGroup α, F (g * h, j) + F (g, h) = M.ρ g (F (h, j)) + F (g, h * j) := by
    intro g h j
    simp only [F, map_sub, map_mul, Module.End.mul_apply]
    calc f (g * h, j) - M.ρ g (M.ρ h (f (1, 1))) + (f (g, h) - M.ρ g (f (1, 1)))
        = (f (g * h, j) + f (g, h))
            - (M.ρ g (M.ρ h (f (1, 1))) + M.ρ g (f (1, 1))) := by abel
      _ = (M.ρ g (f (h, j)) + f (g, h * j))
            - (M.ρ g (M.ρ h (f (1, 1))) + M.ρ g (f (1, 1))) := by rw [hf g h j]
      _ = M.ρ g (f (h, j)) - M.ρ g (M.ρ h (f (1, 1)))
            + (f (g, h * j) - M.ρ g (f (1, 1))) := by abel
  have hF1 : ∀ h : FreeGroup α, F (1, h) = 0 := by
    intro h
    simp only [F, hf1, map_one, Module.End.one_apply, sub_self]
  obtain ⟨x, hx⟩ := freeGroup_twoCocycle_is_coboundary_aux M F hFc hF1
  refine ⟨fun g => x g + f (1, 1), fun g h => ?_⟩
  have hshift : M.ρ g (x h + f (1, 1)) - (x (g * h) + f (1, 1)) + (x g + f (1, 1))
      = (M.ρ g (x h) - x (g * h) + x g) + M.ρ g (f (1, 1)) := by
    rw [map_add]
    abel
  change M.ρ g (x h + f (1, 1)) - (x (g * h) + f (1, 1)) + (x g + f (1, 1)) = f (g, h)
  rw [hshift, hx g h]
  simp only [F]
  abel

end Work.ShafarevichKoch
