import Mathlib

namespace Work.DSM2p

theorem pow_torsion_factorPow {E : Type*} [CommRing E] {p : ℕ}
    (hp : IsSMulRegular E (p : E)) (m : ℕ)
    (x : E ⧸ (Ideal.span {(p : E)} ^ (m + 1) • ⊤ : Submodule E E))
    (hx : (p : E ⧸ (Ideal.span {(p : E)} ^ (m + 1) • ⊤ : Submodule E E)) * x = 0) :
    Submodule.factorPow (Ideal.span {(p : E)}) E (Nat.le_succ m) x = 0 := by
  -- Write `x` as the class of some `a : E`.
  obtain ⟨a, rfl⟩ :=
    Submodule.Quotient.mk_surjective (Ideal.span {(p : E)} ^ (m + 1) • ⊤ : Submodule E E) x
  -- `hx` says `p * mk a = 0` in `E ⧸ (p)^{m+1}`, hence `p * a ∈ (p)^{m+1}`.
  have hpa : (p : E) * a ∈ (Ideal.span {(p : E)} ^ (m + 1) • ⊤ : Submodule E E) := by
    refine (Submodule.Quotient.mk_eq_zero _).mp ?_
    rw [← hx]
    rfl
  -- Identify `(p)^{m+1} • ⊤` with the principal ideal `(p^{m+1})`.
  have hpow : (p : E) ^ (m + 1) ∣ (p : E) * a := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] at hpa
    exact Ideal.mem_span_singleton.mp hpa
  obtain ⟨b, hb⟩ := hpow
  -- Cancelling the regular element `p` gives `a = b * p^m ∈ (p^m)`.
  have hba : a = b * (p : E) ^ m := by
    apply hp
    dsimp only
    rw [smul_eq_mul, smul_eq_mul, hb]
    ring
  have hmem : a ∈ Ideal.span {(p : E) ^ m} := by
    rw [hba]
    exact Ideal.mem_span_singleton'.mpr ⟨b, rfl⟩
  -- The transition map sends the class of `a` to the class of `a`.
  have hkey : (Submodule.factorPow (Ideal.span {(p : E)}) E (Nat.le_succ m))
      (Submodule.Quotient.mk a) = Submodule.Quotient.mk a :=
    Submodule.factor_mk (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ m))) a
  rw [hkey, Submodule.Quotient.mk_eq_zero]
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  exact hmem

end Work.DSM2p
