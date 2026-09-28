import Mathlib
import Submission.Work.Drive.Interfaces

/-!
# The rational-to-torsion bridge for the stable stems (area STEMS, route B)

This file isolates the *group-theoretic* half of Serre's theorem on the stable stems: a
(homotopy) group whose rationalisation is trivial is a torsion group, i.e. every element has
finite order — which is exactly the conclusion of `Work.Drive.StableStemsTorsion`.

The mathematical content is one line: for a `ℤ`-module `A`, if `A ⊗[ℤ] ℚ = 0` then every element
of `A` is torsion (if `a` had infinite order, the injective map `ℤ → A`, `1 ↦ a` would stay
injective after tensoring with the flat module `ℚ`, so `a ⊗ 1 ≠ 0`).  Consequently the *whole*
mathematical content of route B lies in the rational vanishing statement
`Work.StemsB.RatVanishesStems` (see `Submission/Work/StemsB/RatVanishing.lean`), and the present
file is the (proved) bridge from that statement to the contract.

## Main results

* `Work.StemsB.exists_nat_smul_eq_zero_of_subsingleton_tensorRat` — additive form.
* `Work.StemsB.exists_pow_eq_one_of_subsingleton_tensorRat` — multiplicative form, the form
  needed for `HomotopyGroup` (whose elements are written multiplicatively).
-/

set_option linter.style.haveILetI false

open scoped Topology TensorProduct

namespace Work.StemsB

noncomputable section

variable {A : Type*} [AddCommGroup A]

/-- **The rational-to-torsion bridge (additive form).**  A `ℤ`-module whose tensor product with
`ℚ` is a subsingleton is a torsion module: every element has a non-zero integer multiple equal to
zero.

Proof: if `a` has infinite order then `f : ℤ →ₗ[ℤ] A`, `f z = z • a`, is injective; since `ℚ` is
flat over the Dedekind domain `ℤ`, `f.rTensor ℚ` is injective as well, so `a ⊗ 1 = f 1 ⊗ 1` is
non-zero in `A ⊗[ℤ] ℚ` (and `1 ⊗ 1` is non-zero because `TensorProduct.lid` is an isomorphism),
contradicting `Subsingleton (A ⊗[ℤ] ℚ)`. -/
theorem exists_nat_smul_eq_zero_of_subsingleton_tensorRat
    (h : Subsingleton (A ⊗[ℤ] ℚ)) (a : A) : ∃ n : ℕ, 0 < n ∧ n • a = 0 := by
  by_contra hc
  push Not at hc
  -- if `a` has infinite order, then `z ↦ z • a` is injective
  have key : ∀ z : ℤ, z • a = 0 → z = 0 := by
    intro z hz
    obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg z
    · rw [hn] at hz
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · omega
      · exact absurd (by simpa using hz) (hc n hpos)
    · rw [hn, neg_smul, neg_eq_zero] at hz
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · omega
      · exact absurd (by simpa using hz) (hc n hpos)
  set f : ℤ →ₗ[ℤ] A := LinearMap.toSpanSingleton ℤ A a with hf_def
  have hf_apply : ∀ z : ℤ, f z = z • a := by intro z; simp [hf_def]
  have hf : Function.Injective f := by
    intro m n hmn
    have h1 : (m - n) • a = 0 := by rw [sub_smul, ← hf_apply, ← hf_apply, hmn, sub_self]
    have h2 := key (m - n) h1
    omega
  have hinj : Function.Injective (f.rTensor ℚ) :=
    Module.Flat.rTensor_preserves_injective_linearMap f hf
  have hone : ((1 : ℤ) ⊗ₜ[ℤ] (1 : ℚ)) ≠ 0 := by
    intro hz
    have := congrArg (TensorProduct.lid ℤ ℚ) hz
    simp [TensorProduct.lid_tmul] at this
  have hzero : (f.rTensor ℚ) ((1 : ℤ) ⊗ₜ[ℤ] (1 : ℚ)) = 0 := by
    rw [LinearMap.rTensor_tmul, hf_apply]
    simp only [one_zsmul]
    exact Subsingleton.elim _ _
  exact hone (hinj (by rw [hzero, map_zero]))

/-- **The rational-to-torsion bridge (multiplicative form).**  A commutative group whose
`ℤ`-module rationalisation is trivial is a torsion group: every element has finite order.

This is the form used for `HomotopyGroup`, whose composition is written multiplicatively. -/
theorem exists_pow_eq_one_of_subsingleton_tensorRat {G : Type*} [CommGroup G]
    (h : Subsingleton (Additive G ⊗[ℤ] ℚ)) (g : G) : ∃ n : ℕ, 0 < n ∧ g ^ n = 1 := by
  obtain ⟨n, hpos, hn⟩ := exists_nat_smul_eq_zero_of_subsingleton_tensorRat h (Additive.ofMul g)
  refine ⟨n, hpos, ?_⟩
  have h2 : Additive.ofMul (g ^ n) = Additive.ofMul (1 : G) := by
    change n • Additive.ofMul g = 0
    exact hn
  exact Additive.ofMul.injective h2

/-- A `ℤ`-module whose rationalisation is trivial is a torsion module, in the language of
`Module.IsTorsion`. -/
theorem isTorsion_of_subsingleton_tensorRat (h : Subsingleton (A ⊗[ℤ] ℚ)) :
    Module.IsTorsion ℤ A := by
  intro x
  obtain ⟨n, hn0, hn⟩ := exists_nat_smul_eq_zero_of_subsingleton_tensorRat h x
  exact ⟨⟨(n : ℤ), by simp [hn0.ne']⟩, by simpa using hn⟩

end

end Work.StemsB
