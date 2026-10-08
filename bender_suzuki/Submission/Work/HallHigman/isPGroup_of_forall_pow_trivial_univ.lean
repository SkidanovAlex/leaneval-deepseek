import Mathlib
import Submission.Work.HallHigman.FT71

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman

/-- Universe-general form of `Work.HallHigman.isPGroup_of_forall_pow_trivial` (the final step of
Feit--Thompson's Lemma 7.1): if `P ≤ H` preserves a subspace `Z ≤ V` and every `y ∈ P` has *some*
`p`-power acting trivially on `Z` and *some* `p`-power acting trivially on `V ⧸ Z`, then `P` is a
`p`-group.

Here `H` and `V` live in independent universes. -/
theorem isPGroup_of_forall_pow_trivial_univ {p : ℕ} [Fact p.Prime] {H : Type*} [Group H] [Finite H]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] (ρ : Representation (ZMod p) H V)
    (hfaith : Function.Injective ρ) {Z : Submodule (ZMod p) V} {P : Subgroup H}
    (hZinv : ∀ y ∈ P, ∀ v ∈ Z, ρ y v ∈ Z)
    (hZ : ∀ y ∈ P, ∃ k : ℕ, ∀ v ∈ Z, ρ (y ^ p ^ k) v = v)
    (hQ : ∀ y ∈ P, ∃ k : ℕ, ∀ v : V, ρ (y ^ p ^ k) v - v ∈ Z) :
    IsPGroup p P := by
  rw [IsPGroup.iff_orderOf]
  intro y
  obtain ⟨kZ, hkZ⟩ := hZ y y.2
  obtain ⟨kQ, hkQ⟩ := hQ y y.2
  -- the two triviality properties are preserved when passing to powers
  have hpowZ : ∀ (g : P) (m : ℕ), (∀ v ∈ Z, ρ (g : H) v = v) →
      ∀ v ∈ Z, ρ ((g : H) ^ m) v = v := by
    intro g m
    induction m with
    | zero => intro _ v _; simp
    | succ j ih =>
      intro hg v hv
      rw [pow_succ', map_mul, Module.End.mul_apply, ih hg v hv]
      exact hg v hv
  have hpowQ : ∀ (g : P) (m : ℕ), (∀ v : V, ρ (g : H) v - v ∈ Z) →
      ∀ v : V, ρ ((g : H) ^ m) v - v ∈ Z := by
    intro g m
    induction m with
    | zero => intro _ v; simp
    | succ j ih =>
      intro hg v
      have h1 : ρ (g : H) (ρ ((g : H) ^ j) v) - ρ (g : H) v ∈ Z := by
        have := hZinv g g.2 (ρ ((g : H) ^ j) v - v) (ih hg v)
        simpa [map_sub] using this
      have h2 : ρ (g : H) v - v ∈ Z := hg v
      have hsum := Z.add_mem h1 h2
      rw [pow_succ', map_mul, Module.End.mul_apply]
      convert hsum using 1
      abel
  -- take the maximal exponent
  obtain ⟨k, hk⟩ : ∃ k, kZ ≤ k ∧ kQ ≤ k := ⟨max kZ kQ, le_max_left _ _, le_max_right _ _⟩
  have hgf : (y : H) ^ p ^ k = ((y : H) ^ p ^ kZ) ^ p ^ (k - kZ) := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hk.1]
  have hgq : (y : H) ^ p ^ k = ((y : H) ^ p ^ kQ) ^ p ^ (k - kQ) := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hk.2]
  have hZtriv : ∀ v ∈ Z, ρ ((y : H) ^ p ^ k) v = v := by
    intro v hv
    rw [hgf]
    exact hpowZ ⟨(y : H) ^ p ^ kZ, P.pow_mem y.2 _⟩ (p ^ (k - kZ))
      (fun w hw => hkZ w hw) v hv
  have hQtriv : ∀ v : V, ρ ((y : H) ^ p ^ k) v - v ∈ Z := by
    intro v
    rw [hgq]
    exact hpowQ ⟨(y : H) ^ p ^ kQ, P.pow_mem y.2 _⟩ (p ^ (k - kQ)) (fun w => hkQ w) v
  -- such an element is unipotent of index two on `V`, hence has `p`-power order
  have hunip : ((ρ.comp P.subtype) ⟨(y : H) ^ p ^ k, P.pow_mem y.2 _⟩ - 1) ^ 2 = 0 := by
    rw [pow_two]
    change ((ρ ((y : H) ^ p ^ k) - 1) * (ρ ((y : H) ^ p ^ k) - 1)) = 0
    refine LinearMap.ext fun v => ?_
    have h1 : ρ ((y : H) ^ p ^ k) v - v ∈ Z := hQtriv v
    have h2 : ρ ((y : H) ^ p ^ k) (ρ ((y : H) ^ p ^ k) v - v)
        = ρ ((y : H) ^ p ^ k) v - v := hZtriv _ h1
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, LinearMap.zero_apply]
    rw [h2, sub_self]
  have hfaith' : Function.Injective (ρ.comp P.subtype) :=
    fun a b hab => Subtype.coe_injective (hfaith hab)
  obtain ⟨n, hn⟩ := orderOf_eq_prime_pow_of_sq_sub_one_eq_zero (ρ.comp P.subtype) hfaith' hunip
  -- conclude that `orderOf y` itself is a prime power
  have hge : (⟨(y : H) ^ p ^ k, P.pow_mem y.2 _⟩ : P) = y ^ p ^ k := rfl
  rw [hge, orderOf_pow] at hn
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Fact.out).mp (Nat.gcd_dvd_right (orderOf y) (p ^ k))
  refine ⟨n + j, ?_⟩
  have hdiv := Nat.div_mul_cancel (Nat.gcd_dvd_left (orderOf y) (p ^ k))
  rw [hn, hj] at hdiv
  rw [← hdiv, pow_add]

end Work.HallHigman
