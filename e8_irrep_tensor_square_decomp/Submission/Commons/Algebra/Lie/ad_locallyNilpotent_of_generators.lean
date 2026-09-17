import Mathlib.Algebra.Lie.OfAssociative

namespace Commons.Algebra.Lie

variable {R : Type*}

/-- If `(ad x)^m y = 0` then `(ad x)^k y = 0` for every `k ≥ m`. -/
lemma ad_pow_apply_eq_zero_of_le {L : Type*} [Field R] [LieRing L] [LieAlgebra R L]
    (x : L) {y : L} {m k : ℕ} (h : ((LieAlgebra.ad R L x)^m) y = 0) (hk : m ≤ k) :
    ((LieAlgebra.ad R L x)^k) y = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_comm m d, pow_add, Module.End.mul_apply, h, map_zero]

/-- The Leibniz rule iterated: `(ad x)^(m+n) ⁅y,z⁆ = 0` whenever `(ad x)^m y = 0` and
`(ad x)^n z = 0`. -/
lemma ad_pow_lie_eq_zero {L : Type*} [Field R] [LieRing L] [LieAlgebra R L]
    (x y z : L) {m n : ℕ} (hm : ((LieAlgebra.ad R L x)^m) y = 0)
    (hn : ((LieAlgebra.ad R L x)^n) z = 0) :
    ((LieAlgebra.ad R L x)^(m+n)) ⁅y, z⁆ = 0 := by
  rw [LieAlgebra.ad_pow_lie]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  have hij' : i + j = m + n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  have hb : ⁅((LieAlgebra.ad R L x)^i) y, ((LieAlgebra.ad R L x)^j) z⁆ = 0 := by
    by_cases hi : m ≤ i
    · rw [ad_pow_apply_eq_zero_of_le x hm hi, zero_lie]
    · have hj : n ≤ j := by omega
      rw [ad_pow_apply_eq_zero_of_le x hn hj, lie_zero]
  rw [hb, smul_zero]

/-- If `x` is such that `⁅x,x⁆ = 0` and `ad x` is locally nilpotent on a generating set `S` of a Lie
algebra `L`, then `ad x` is locally nilpotent on `L`.  (The set of elements annihilated by some power
of `ad x` is a Lie subalgebra, by the Leibniz rule for derivations.)

This is the abstract form of the fact that for the Serre-constructed algebra the adjoint action of
each `eᵢ` (resp. `fᵢ`) is locally nilpotent, since the defining Serre relations give
`(ad eᵢ)ⁿ eⱼ = 0` for a suitable `n` depending on `i,j` and `(ad eᵢ) eᵢ = 0`, while `hⱼ` and `fⱼ`
are annihilated by a small power too. -/
theorem ad_locallyNilpotent_of_generators {R L : Type*} [Field R] [LieRing L] [LieAlgebra R L]
    {x : L} (hx : ⁅x, x⁆ = 0) {S : Set L} (hS : LieSubalgebra.lieSpan R L S = ⊤)
    (hloc : ∀ y ∈ S, ∃ n : ℕ, ((LieAlgebra.ad R L x)^n) y = 0) :
    ∀ y : L, ∃ n : ℕ, ((LieAlgebra.ad R L x)^n) y = 0 := by
  let A : Set L := {y | ∃ n : ℕ, ((LieAlgebra.ad R L x)^n) y = 0}
  have hxA : x ∈ A := ⟨1, by rw [pow_one, LieAlgebra.ad_apply, hx]⟩
  have hzero : (0 : L) ∈ A := ⟨1, by rw [pow_one, map_zero]⟩
  have hadd : ∀ y ∈ A, ∀ z ∈ A, y + z ∈ A := by
    rintro y ⟨m, hm⟩ z ⟨n, hn⟩
    refine ⟨max m n, ?_⟩
    rw [map_add, ad_pow_apply_eq_zero_of_le x hm (le_max_left m n),
      ad_pow_apply_eq_zero_of_le x hn (le_max_right m n), add_zero]
  have hsmul : ∀ (r : R) (y : L), y ∈ A → r • y ∈ A := by
    rintro r y ⟨n, hn⟩
    exact ⟨n, by rw [map_smul, hn, smul_zero]⟩
  have hlie : ∀ y ∈ A, ∀ z ∈ A, ⁅y, z⁆ ∈ A := by
    rintro y ⟨m, hm⟩ z ⟨n, hn⟩
    exact ⟨m + n, ad_pow_lie_eq_zero x y z hm hn⟩
  let K : LieSubalgebra R L :=
    { carrier := A
      add_mem' := fun {_ _} hy hz => hadd _ hy _ hz
      zero_mem' := hzero
      smul_mem' := fun r _ hy => hsmul r _ hy
      lie_mem' := fun {_ _} hy hz => hlie _ hy _ hz }
  have hSK : S ⊆ K := fun y hy => hloc y hy
  have htop : (⊤ : LieSubalgebra R L) ≤ K := by
    rw [← hS]
    exact LieSubalgebra.lieSpan_le.mpr hSK
  intro y
  exact htop (show y ∈ (⊤ : LieSubalgebra R L) by trivial)

end Commons.Algebra.Lie