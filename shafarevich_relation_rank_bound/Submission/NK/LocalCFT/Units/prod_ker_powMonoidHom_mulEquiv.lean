import Mathlib

/-!
# Coprime power-map decomposition

If `M` is a commutative group of exponent dividing `a * b` with `a` and `b`
coprime, then `M` is (multiplicatively) the direct product of the kernels of
the `a`-th and `b`-th power maps:

`M ≃* ker (powMonoidHom a) × ker (powMonoidHom b)`.

This is the group-theoretic "Chinese remainder" statement used in the
local/global class field theory input for Neukirch–Uchida.  The isomorphism
sends `x` to `(x ^ b, x ^ a)`; the inverse is given by Bézout exponents.
-/

namespace NK.LocalCFT.Units

variable {M : Type*} [CommGroup M]

/-- For `k : ℤ` and `n : ℕ`, `(x ^ k) ^ n = x ^ (k * n)`. -/
lemma pow_zpow_eq (x : M) (k : ℤ) (n : ℕ) : (x ^ k) ^ n = x ^ (k * (n : ℤ)) := by
  rw [← zpow_natCast (x ^ k) n, ← zpow_mul]

/-- If `x ^ (m * n) = 1`, then raising `x ^ m` to any integer power and then to
the `n`-th power gives `1`. -/
lemma pow_zpow_pow_eq_one {x : M} {m n : ℕ} (h : x ^ (m * n) = 1) (k : ℤ) :
    ((x ^ m : M) ^ k) ^ n = 1 := by
  have h1 : ((x ^ m : M) ^ k) ^ n = x ^ (((m : ℤ) * k) * (n : ℤ)) := by
    rw [← zpow_natCast x m, ← zpow_mul, pow_zpow_eq]
  rw [h1]
  have h2 : ((m : ℤ) * k) * (n : ℤ) = ((m * n : ℕ) : ℤ) * k := by
    push_cast; ring
  rw [h2, zpow_mul, zpow_natCast x (m * n), h, one_zpow]

theorem prod_ker_powMonoidHom_mulEquiv {M : Type*} [CommGroup M] {a b : ℕ}
    (hab : a.Coprime b) (hexp : ∀ x : M, x ^ (a * b) = 1) :
    Nonempty (↥(MonoidHom.ker (powMonoidHom a : M →* M)) ×
      ↥(MonoidHom.ker (powMonoidHom b : M →* M)) ≃* M) := by
  have hgcd : a.gcd b = 1 := Nat.coprime_iff_gcd_eq_one.mp hab
  -- Bezout: `1 = a * gcdA b + b * gcdB b` in `ℤ`
  have hbez : (1 : ℤ) = (a : ℤ) * a.gcdA b + (b : ℤ) * a.gcdB b := by
    have h := Nat.gcd_eq_gcd_ab a b
    rw [hgcd] at h
    simpa using h
  -- Every element is the product of an `a`-power and a `b`-power
  have key : ∀ x : M, (x ^ a : M) ^ (a.gcdA b) * (x ^ b : M) ^ (a.gcdB b) = x := by
    intro x
    have h1 : (x ^ a : M) ^ (a.gcdA b) = x ^ ((a : ℤ) * a.gcdA b) := by
      rw [← zpow_natCast x a, ← zpow_mul]
    have h2 : (x ^ b : M) ^ (a.gcdB b) = x ^ ((b : ℤ) * a.gcdB b) := by
      rw [← zpow_natCast x b, ← zpow_mul]
    rw [h1, h2, ← zpow_add, ← hbez, zpow_one]
  -- The two kernels meet trivially
  have hbot : ∀ w : M, w ∈ MonoidHom.ker (powMonoidHom a : M →* M) →
      w ∈ MonoidHom.ker (powMonoidHom b : M →* M) → w = 1 := by
    intro w hwa hwb
    have ha : w ^ a = 1 := by simpa [MonoidHom.mem_ker, powMonoidHom_apply] using hwa
    have hb : w ^ b = 1 := by simpa [MonoidHom.mem_ker, powMonoidHom_apply] using hwb
    have hk := key w
    rw [ha, hb] at hk
    simpa using hk.symm
  have memKa : ∀ x : M,
      (x ^ b : M) ^ (a.gcdB b) ∈ MonoidHom.ker (powMonoidHom a : M →* M) := by
    intro x
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    exact pow_zpow_pow_eq_one (m := b) (n := a)
      (by rw [Nat.mul_comm b a]; exact hexp x) (a.gcdB b)
  have memKb : ∀ x : M,
      (x ^ a : M) ^ (a.gcdA b) ∈ MonoidHom.ker (powMonoidHom b : M →* M) := by
    intro x
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    exact pow_zpow_pow_eq_one (m := a) (n := b) (hexp x) (a.gcdA b)
  -- Multiplication `ker a × ker b → M`
  let μ : (↥(MonoidHom.ker (powMonoidHom a : M →* M)) ×
      ↥(MonoidHom.ker (powMonoidHom b : M →* M))) →* M :=
    MonoidHom.mk' (fun p => (p.1 : M) * (p.2 : M)) (by
      intro p q
      simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
      ac_rfl)
  have μ_apply : ∀ p : (↥(MonoidHom.ker (powMonoidHom a : M →* M)) ×
      ↥(MonoidHom.ker (powMonoidHom b : M →* M))), μ p = (p.1 : M) * (p.2 : M) := by
    intro p
    rfl
  have hinj : Function.Injective μ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [Subgroup.eq_bot_iff_forall]
    rintro ⟨y, z⟩ hp
    rw [MonoidHom.mem_ker] at hp
    have hpy : (y : M) * (z : M) = 1 := by simpa only [μ_apply] using hp
    have hzy : (z : M) * (y : M) = 1 := by rw [mul_comm]; exact hpy
    have hyz : (y : M) = (z : M)⁻¹ := eq_inv_of_mul_eq_one_right hzy
    have hyKb : (y : M) ∈ MonoidHom.ker (powMonoidHom b : M →* M) := by
      rw [hyz]
      exact (MonoidHom.ker (powMonoidHom b : M →* M)).inv_mem z.2
    have hy1 : (y : M) = 1 := hbot (y : M) y.2 hyKb
    have hz1 : (z : M) = 1 := by rw [hy1, one_mul] at hpy; exact hpy
    refine Prod.ext ?_ ?_
    · exact Subtype.ext (by simpa using hy1)
    · exact Subtype.ext (by simpa using hz1)
  have hsurj : Function.Surjective μ := by
    intro x
    refine ⟨(⟨(x ^ b : M) ^ (a.gcdB b), memKa x⟩,
      ⟨(x ^ a : M) ^ (a.gcdA b), memKb x⟩), ?_⟩
    rw [μ_apply]
    rw [mul_comm]
    exact key x
  exact ⟨MulEquiv.ofBijective μ ⟨hinj, hsurj⟩⟩

end NK.LocalCFT.Units
