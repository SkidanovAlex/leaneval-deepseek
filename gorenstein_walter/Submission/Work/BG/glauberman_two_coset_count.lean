import Mathlib
import Submission.Work.BG.Defs

/-!
# The two-coset count of Glauberman's lemma

Let `U` be a finite group of **odd** order, `σ` an involutive automorphism of `U` and
`u ∈ U`.  Writing `C_U(σ) = {x : σ x = x}` for the fixed-point subgroup, the present
lemma counts the `σ`-twisted conjugates of `u` that lie in `C_U(σ)`:

`Nat.card {v : U // σ v * u * v⁻¹ ∈ C_U(σ)} = Nat.card C_U(σ)`.

This is the combinatorial heart of Glauberman's coset-sum identity
(`Work.BG.glauberman_two_coset_sum`): the set of admissible `v` is a *single* left coset
of `C_U(σ)`, namely `C_U(σ) · v₀` for the element `v₀` with `v₀⁻¹ σ v₀ = a₀`.

## The argument

Set `a(v) := v⁻¹ σ v`.  A direct computation gives

`σ v * u * v⁻¹ ∈ C_U(σ) ↔ a(v) * u * a(v) = σ u`,

and the map `a : U → U` has as fibres exactly the left cosets of `C_U(σ)` (if
`a(v) = a(w)` then `w v⁻¹ = σ (w v⁻¹)`, so `w v⁻¹ ∈ C_U(σ)`).  Hence it suffices to show
that the equation `a * u * a = σ u` has **exactly one** solution, which we do in two
steps:

* *Uniqueness.*  If `a * u * a = σ u` then `(a u)² = σ u * u`, so `a u` is the unique
  square root of `σ u * u` (squaring is injective on a finite group of odd order);
  since `u ↦ u²` is a bijection, `a u` — and therefore `a = (a u) u⁻¹` — is determined.
* *Existence.*  The element `a₀ := (σ u * u)^{(n+1)/2} · u⁻¹` (where `n = |U|`) satisfies
  `a₀ * u * a₀ = σ u`; moreover `σ a₀ = a₀⁻¹`, because `σ a₀ = u · ((σ u * u)^{(n+1)/2})⁻¹
  · σ u`, and both sides square to `u * σ u`.

Finally `v₀ := a₀^{(n-1)/2}` satisfies `v₀⁻¹ σ v₀ = a₀`, and
`v⁻¹ σ v = a₀ ↔ v v₀⁻¹ ∈ C_U(σ)`, so multiplication by `v₀` is a bijection
`C_U(σ) ≃ {v : U // σ v * u * v⁻¹ ∈ C_U(σ)}`.
-/

namespace Work.BG

/-- In a finite group of odd order, `x ↦ x ^ 2` is injective. -/
theorem sq_injective_of_odd {G : Type*} [Group G] [Fintype G] (hG : Odd (Nat.card G))
    {x y : G} (h : x ^ 2 = y ^ 2) : x = y := by
  obtain ⟨t, ht⟩ := hG
  have key : ∀ z : G, (z ^ 2) ^ (t + 1) = z := by
    intro z
    rw [← pow_mul, show 2 * (t + 1) = Nat.card G + 1 by omega, pow_succ,
      pow_card_eq_one', one_mul]
  rw [← key x, h, key y]

theorem glauberman_two_coset_count {U : Type} [Group U] [Fintype U]
    (hU : Odd (Nat.card U)) (σ : MulAut U) (hσ : σ * σ = 1) (u : U) :
    Nat.card {v : U // σ v * u * v⁻¹ ∈ Work.BG.fixedSubgroup σ}
      = Nat.card ↥(Work.BG.fixedSubgroup σ) := by
  classical
  -- `σ` is an involution
  have hσ2 : ∀ x : U, σ (σ x) = x := by
    intro x
    have h := DFunLike.congr_fun hσ x
    simpa [MulAut.mul_apply] using h
  -- **Step 1.** `σ v * u * v⁻¹ ∈ C_U(σ)` iff `a * u * a = σ u` with `a = v⁻¹ * σ v`.
  have hkeyeq : ∀ v : U, (σ v * u * v⁻¹ ∈ fixedSubgroup σ) ↔
      (v⁻¹ * σ v) * u * (v⁻¹ * σ v) = σ u := by
    intro v
    rw [mem_fixedSubgroup]
    constructor
    · intro h
      have h' : v * σ u * (σ v)⁻¹ = σ v * u * v⁻¹ := by
        rw [map_mul, map_mul, map_inv, hσ2 v] at h
        exact h
      have := congrArg (fun t => v⁻¹ * t * (σ v)) h'
      simpa [mul_assoc] using this.symm
    · intro h
      have := congrArg (fun t => v * t * (σ v)⁻¹) h
      rw [map_mul, map_mul, map_inv, hσ2 v]
      simpa [mul_assoc] using this.symm
  -- We work with `n = |U| = 2 * t + 1` and the element `a₀ = (σ u * u)^(t+1) * u⁻¹`.
  obtain ⟨t, ht⟩ := hU
  have hUodd : Odd (Nat.card U) := ⟨t, ht⟩
  set X := (σ u * u) ^ (t + 1) with hXdef
  set a₀ := X * u⁻¹ with ha₀def
  have hm : (t + 1) * 2 = Nat.card U + 1 := by omega
  -- **Step 2.** `X * X = σ u * u`, whence `a₀ * u * a₀ = σ u`.
  have hy : X * X = σ u * u := by
    rw [hXdef, ← pow_two, ← pow_mul, hm, pow_succ, pow_card_eq_one', one_mul]
  have ha0 : a₀ * u * a₀ = σ u := by
    rw [ha₀def]
    have h : (X * u⁻¹) * u * (X * u⁻¹) = (X * X) * u⁻¹ := by group
    rw [h, hy]; group
  -- **Step 3.** `σ a₀ = a₀⁻¹`: `σ X` and `u * X⁻¹ * σ u` both square to `u * σ u`.
  have hsq1 : (σ X) ^ 2 = u * σ u := by
    rw [← map_pow, pow_two, hy, map_mul, hσ2 u]
  have hsq2 : (u * X⁻¹ * σ u) ^ 2 = u * σ u := by
    have h1 : u * X⁻¹ * σ u * (u * X⁻¹ * σ u)
        = u * (X⁻¹ * (σ u * u) * X⁻¹) * σ u := by group
    have hX1 : X⁻¹ * (X * X) * X⁻¹ = 1 := by group
    rw [pow_two, h1, ← hy, hX1]; simp
  have hsigy : σ X = u * X⁻¹ * σ u := sq_injective_of_odd hUodd (by rw [hsq1, hsq2])
  have hsig : σ a₀ = a₀⁻¹ := by
    rw [ha₀def, map_mul, map_inv, hsigy]; group
  -- **Step 4.** The equation `a * u * a = σ u` has the unique solution `a = a₀`.
  have huniq : ∀ a : U, a * u * a = σ u → a = a₀ := by
    intro a ha
    have h1 : (a * u) ^ 2 = (a * u * a) * u := by rw [pow_two]; group
    have h2 : (a * u) ^ 2 = X ^ 2 := by rw [h1, ha, ← hy, pow_two]
    have h3 := sq_injective_of_odd hUodd h2
    rw [ha₀def, ← h3]; group
  have hkey : ∀ v : U, (σ v * u * v⁻¹ ∈ fixedSubgroup σ) ↔ v⁻¹ * σ v = a₀ := by
    intro v
    rw [hkeyeq v]
    constructor
    · intro h; exact huniq (v⁻¹ * σ v) h
    · intro h; rw [h]; exact ha0
  -- **Step 5.** `v₀ = a₀^t` satisfies `v₀⁻¹ * σ v₀ = a₀`; hence `σ v₀ = v₀ * a₀`.
  set v₀ := a₀ ^ t with hv₀def
  have h2t : 2 * t + 1 = Nat.card U := by omega
  have ha2t : a₀ ^ (2 * t) = a₀⁻¹ := by
    have hh : a₀ ^ (2 * t) * a₀ = 1 := by rw [← pow_succ, h2t, pow_card_eq_one']
    exact eq_inv_of_mul_eq_one_left hh
  have hv₀ : v₀⁻¹ * σ v₀ = a₀ := by
    rw [hv₀def, map_pow, hsig, inv_pow]
    rw [← mul_inv_rev, ← pow_add, show t + t = 2 * t by omega, ha2t, inv_inv]
  have hv0σ : σ v₀ = v₀ * a₀ := by
    have hh := congrArg (fun x => v₀ * x) hv₀
    rw [← mul_assoc, mul_inv_cancel, one_mul] at hh
    exact hh
  -- **Step 6.** `v⁻¹ σ v = a₀` iff `v * v₀⁻¹ ∈ C_U(σ)`.
  have heq : ∀ v : U, (σ v * u * v⁻¹ ∈ fixedSubgroup σ) ↔
      v * v₀⁻¹ ∈ fixedSubgroup σ := by
    intro v
    rw [hkey v]
    constructor
    · intro h
      have e1 : σ v = v * a₀ := by
        have hh := congrArg (fun x => v * x) h
        simpa [mul_assoc] using hh
      rw [mem_fixedSubgroup, map_mul, map_inv, hv0σ, e1]; group
    · intro h
      rw [mem_fixedSubgroup] at h
      have e1 : σ v = v * a₀ := by
        have h' : σ v * (v₀ * a₀)⁻¹ = v * v₀⁻¹ := by
          have hh := h
          rw [map_mul, map_inv, hv0σ] at hh
          exact hh
        have h4 := congrArg (fun x => x * (v₀ * a₀)) h'
        simpa [mul_assoc] using h4
      rw [e1]; group
  -- **Step 7.** Multiplication by `v₀` is a bijection `C_U(σ) ≃ {v // σ v * u * v⁻¹ ∈ C_U(σ)}`.
  let e : ↥(fixedSubgroup σ) ≃ {v : U // σ v * u * v⁻¹ ∈ fixedSubgroup σ} :=
    { toFun := fun c => ⟨c.val * v₀,
        (heq (c.val * v₀)).mpr (by rw [mul_assoc, mul_inv_cancel, mul_one]; exact c.property)⟩
      invFun := fun v => ⟨v.val * v₀⁻¹, (heq v.val).mp v.property⟩
      left_inv := by intro c; exact Subtype.ext (by group)
      right_inv := by intro v; exact Subtype.ext (by group) }
  exact (Nat.card_congr e).symm

end Work.BG
