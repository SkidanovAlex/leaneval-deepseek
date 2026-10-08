import Mathlib
import Submission.Work.Higman.Layers.Defs
import Submission.Work.Higman.Layers.dvd_finrank
import Submission.Work.Higman.Layers.pow_le_card

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.Higman.Layers

/-- Every non-zero, proper `σ`-invariant subspace of `V` has `𝔽₂`-dimension `n`.

`Work.Higman.Layers.dvd_finrank` gives `n ∣ finrank U` for `U ≠ ⊥`, while `hcard` forces
`finrank V = 2 * n`; since `U ≠ ⊤` the dimension is not `2 * n`, so it is `n`. -/
theorem finrank_eq_n_of_isInv_ne {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {σ : V →ₗ[ZMod 2] V} {n : ℕ} (hn : 1 ≤ n) (hcard : Nat.card V = 2 ^ (2 * n))
    (horder : orderOf σ = 2 ^ n - 1) (hsr : Work.Higman.Layers.Semiregular σ)
    {U : Submodule (ZMod 2) V} (hU : Work.Higman.Layers.IsInv σ U) (hne : U ≠ ⊥)
    (htop : U ≠ ⊤) : Module.finrank (ZMod 2) U = n := by
  classical
  haveI : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  -- `hcard` pins down `finrank V = 2 * n`
  have hfinV : Module.finrank (ZMod 2) V = 2 * n := by
    have hv : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)]; norm_num
    have h : 2 ^ (2 * n) = 2 ^ Module.finrank (ZMod 2) V := by rw [← hv, hcard]
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  -- a proper invariant subspace has strictly smaller dimension
  have hlt : Module.finrank (ZMod 2) U < 2 * n := by
    rw [← hfinV]; exact Submodule.finrank_lt htop
  -- semiregularity forces `2 ^ n ≤ |U|`, hence `n ≤ finrank U`
  have hge : n ≤ Module.finrank (ZMod 2) U := by
    have hle := Work.Higman.Layers.pow_le_card horder hn hsr hU hne
    have hcardU : Nat.card U = 2 ^ Module.finrank (ZMod 2) U := by
      haveI : Module.Finite (ZMod 2) ↥U := Module.Finite.of_finite
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥U)]; norm_num
    rw [hcardU] at hle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  -- and `n ∣ finrank U`, so `finrank U` is a multiple of `n` in `[n, 2 * n)`
  have hdvd : n ∣ Module.finrank (ZMod 2) U :=
    Work.Higman.Layers.dvd_finrank horder hn hsr hU hne
  obtain ⟨k, hk⟩ := hdvd
  rw [hk] at hlt hge ⊢
  have hklt2 : k < 2 := by
    have : n * k < n * 2 := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  have hkge1 : 1 ≤ k := by
    have : n * 1 ≤ n * k := by simpa using hge
    exact Nat.le_of_mul_le_mul_left this (by omega)
  have hk1 : k = 1 := by omega
  subst hk1
  simp

end Work.Higman.Layers
