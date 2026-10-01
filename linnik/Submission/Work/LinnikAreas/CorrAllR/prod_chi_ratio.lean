import Mathlib
import Submission.Work.LinnikAreas.CorrAllR.DefsSq
import Submission.Commons.NumberTheory.DirichletCharacter.primesq_weil_bound

namespace Work.LinnikAreas.CorrAllR

open scoped BigOperators

variable {p : ℕ}

/-- Adding a natural number to the digit decomposition, in explicit digits. -/
theorem zmod_sq_add_digit [NeZero p] (a : ℕ) (r y : ZMod p) :
    ((r.val : ℕ) : ZMod (p^2)) + (p : ZMod (p^2)) * ((y.val : ℕ) : ZMod (p^2))
      + ((a : ℕ) : ZMod (p^2))
      = ((((r.val + a % p) % p) + p * ((r.val + a % p) / p + a % (p^2) / p + y.val) : ℕ)
          : ZMod (p^2)) := by
  have hcast : ((a : ℕ) : ZMod (p^2)) = ((a % p^2 : ℕ) : ZMod (p^2)) := by
    rw [← ZMod.natCast_zmod_val (a : ZMod (p^2))]
    rw [ZMod.val_natCast]
  rw [hcast]
  have h1 : a % p^2 % p = a % p := Nat.mod_mod_of_dvd a (⟨p, by ring⟩ : p ∣ p ^ 2)
  have hL : a % p^2 = p * ((a % p^2) / p) + a % p := by
    rw [← h1, Nat.div_add_mod]
  have hR : r.val + a % p = p * ((r.val + a % p) / p) + (r.val + a % p) % p :=
    (Nat.div_add_mod _ _).symm
  have hkey : r.val + p * y.val + a % p^2
      = (r.val + a % p) % p + p * ((r.val + a % p) / p + a % (p^2) / p + y.val) := by
    calc r.val + p * y.val + a % p^2
        = r.val + p * y.val + (p * ((a % p^2) / p) + a % p) := by
            conv_lhs => rw [hL]
      _ = (r.val + a % p) + p * (y.val + (a % p^2) / p) := by ring
      _ = (p * ((r.val + a % p) / p) + (r.val + a % p) % p)
            + p * (y.val + (a % p^2) / p) := by
            conv_lhs => rw [hR]
      _ = (r.val + a % p) % p + p * ((r.val + a % p) / p + a % (p^2) / p + y.val) := by ring
  have hfinal : (((r.val + p * y.val + a % (p^2)) : ℕ) : ZMod (p^2))
      = ((((r.val + a % p) % p
          + p * ((r.val + a % p) / p + a % (p^2) / p + y.val)) : ℕ) : ZMod (p^2)) := by
    rw [hkey]
  rw [← hfinal]
  push_cast
  ring

/-- Adding a natural number to `zmd p r y`. -/
theorem zmd_add_natCast [NeZero p] (a : ℕ) (r y : ZMod p) :
    zmd p r y + ((a : ℕ) : ZMod (p^2))
      = ((((r.val + a % p) % p)
          + p * ((r.val + a % p) / p + a % (p^2) / p + y.val) : ℕ) : ZMod (p^2)) := by
  simpa only [zmd] using zmod_sq_add_digit (p := p) a r y

/-- Reduction of `zmd p r y` back to `ZMod p` gives `r`. -/
theorem zmd_castHom (hp : p.Prime) [NeZero p] (r y : ZMod p) :
    ZMod.castHom (show p ∣ p^2 from ⟨p, by ring⟩) (ZMod p) (zmd p r y) = r := by
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.pos.ne'⟩
  have hd : p ∣ p ^ 2 := ⟨p, by ring⟩
  have h1 : ZMod.castHom hd (ZMod p) ((r.val : ℕ) : ZMod (p^2)) = (r.val : ZMod p) := by
    rw [ZMod.castHom_apply, ZMod.cast_natCast hd]
  have h2 : ZMod.castHom hd (ZMod p) ((p : ℕ) : ZMod (p^2)) = 0 := by
    rw [ZMod.castHom_apply, ZMod.cast_natCast hd, ZMod.natCast_self]
  have h3 : ZMod.castHom hd (ZMod p) ((y.val : ℕ) : ZMod (p^2)) = (y.val : ZMod p) := by
    rw [ZMod.castHom_apply, ZMod.cast_natCast hd]
  unfold zmd
  rw [map_add, map_mul, h1, h2, h3, zero_mul, add_zero, ZMod.natCast_zmod_val]

/-- The `1 + p`-kernel shift for a character modulo `p ^ 2`. -/
theorem chi_shift [Fact p.Prime] (χ : DirichletCharacter ℂ (p^2))
    {m K δ : ℕ} (hm : m < p) (hδ : (δ : ZMod p) * (m : ZMod p) = 1) :
    χ (((m + p * K : ℕ)) : ZMod (p^2))
      = χ (((m : ℕ)) : ZMod (p^2)) * (χ (((1 + p : ℕ)) : ZMod (p^2))) ^ (K * δ) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.pos.ne'⟩
  have hδm : ((δ * m : ℕ) : ZMod p) = 1 := by
    have h : ((δ : ZMod p) * (m : ZMod p)) = ((δ * m : ℕ) : ZMod p) := by push_cast; ring
    rw [← h]; exact hδ
  have hmδ : ((m * δ : ℕ) : ZMod p) = 1 := by rw [Nat.mul_comm]; exact hδm
  have hmul : (((K * (m * δ) : ℕ)) : ZMod p) = ((K : ℕ) : ZMod p) := by
    rw [Nat.cast_mul, hmδ, mul_one]
  have hprime : (p : ZMod (p^2)) * (((K * (m * δ) : ℕ)) : ZMod (p^2))
      = (p : ZMod (p^2)) * ((K : ℕ) : ZMod (p^2)) :=
    Commons.NumberTheory.DirichletCharacter.mul_prime_eq_of_cast_eq _ _ (by simpa [ZMod.castHom_apply] using hmul)
  have hkey : (m : ZMod (p^2)) * (1 + (p : ZMod (p^2)) * ((K * δ : ℕ) : ZMod (p^2)))
      = (((m + p * K : ℕ)) : ZMod (p^2)) := by
    have h1 : (m : ZMod (p^2)) * ((p : ZMod (p^2)) * ((K * δ : ℕ) : ZMod (p^2)))
        = (p : ZMod (p^2)) * (((K * (m * δ) : ℕ)) : ZMod (p^2)) := by
      push_cast
      ring
    rw [mul_add, mul_one, h1, hprime]
    push_cast
    ring
  rw [← hkey, map_mul]
  congr 1
  have h2 : (1 : ZMod (p^2)) + (p : ZMod (p^2)) * ((K * δ : ℕ) : ZMod (p^2))
      = (1 + (p : ZMod (p^2))) ^ (K * δ) := by
    rw [Commons.NumberTheory.DirichletCharacter.pow_one_add_prime_eq]
    ring
  rw [h2, map_pow]
  congr 1
  push_cast
  ring

/-- Single-factor ratio: the `y`-dependence of `χ (zmd p r y + c)` is a `p`-th root of unity
raised to the power `y`. -/
theorem chi_factor_ratio [Fact p.Prime] (χ : DirichletCharacter ℂ (p^2)) (c : ℕ) (r : ZMod p)
    (hc : r + (c : ZMod p) ≠ 0) (y : ZMod p) :
    χ (zmd p r y + ((c : ℕ) : ZMod (p^2)))
      = χ (zmd p r 0 + ((c : ℕ) : ZMod (p^2)))
        * (χ (((1 + p : ℕ)) : ZMod (p^2))) ^ (y.val * ((r + (c : ZMod p))⁻¹).val) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hm_val : (r + (c : ZMod p)).val = (r.val + c % p) % p := by
    rw [ZMod.val_add, ZMod.val_natCast]
  have hm_eq : (((r.val + c % p) % p : ℕ) : ZMod p) = r + (c : ZMod p) := by
    rw [← hm_val, ZMod.natCast_zmod_val]
  have hδ : ((((r + (c : ZMod p))⁻¹).val : ℕ) : ZMod p)
      * (((r.val + c % p) % p : ℕ) : ZMod p) = 1 := by
    rw [hm_eq, ZMod.natCast_zmod_val]
    exact inv_mul_cancel₀ hc
  have hmlt : (r.val + c % p) % p < p := Nat.mod_lt _ hp.pos
  have hd : ∀ y : ZMod p, zmd p r y + ((c : ℕ) : ZMod (p^2))
      = (((r.val + c % p) % p
          + p * ((r.val + c % p) / p + c % (p^2) / p + y.val) : ℕ) : ZMod (p^2)) :=
    fun y => zmd_add_natCast (p := p) c r y
  have h1 : χ (zmd p r y + ((c : ℕ) : ZMod (p^2)))
      = χ ((((r.val + c % p) % p : ℕ)) : ZMod (p^2))
        * (χ (((1 + p : ℕ)) : ZMod (p^2)))
            ^ (((r.val + c % p) / p + c % (p^2) / p + y.val)
                * (((r + (c : ZMod p))⁻¹).val)) := by
    rw [hd y]; exact chi_shift χ hmlt hδ
  have h0 : χ (zmd p r 0 + ((c : ℕ) : ZMod (p^2)))
      = χ ((((r.val + c % p) % p : ℕ)) : ZMod (p^2))
        * (χ (((1 + p : ℕ)) : ZMod (p^2)))
            ^ (((r.val + c % p) / p + c % (p^2) / p + (0 : ZMod p).val)
                * (((r + (c : ZMod p))⁻¹).val)) := by
    rw [hd 0]; exact chi_shift χ hmlt hδ
  rw [h1, h0]
  rw [ZMod.val_zero]
  have hexp : ((r.val + c % p) / p + c % (p^2) / p + y.val)
      * (((r + (c : ZMod p))⁻¹).val)
      = ((r.val + c % p) / p + c % (p^2) / p + 0) * (((r + (c : ZMod p))⁻¹).val)
        + y.val * (((r + (c : ZMod p))⁻¹).val) := by ring
  rw [hexp, pow_add]
  ring

/-- **Ratio formula for a product of shifted linear factors modulo `p ^ 2`.**

For a prime `p`, a Dirichlet character `χ` mod `p ^ 2`, a residue `ρ : ZMod p` and `n` shifts
`c l` whose reductions `ρ + c l` are all non-zero, the `y`-dependence of the product
`∏ l, χ (zmd p ρ y + c l)` is a pure power of `χ (1 + p)`; here `zmd p r y = r.val + p * y.val`
is the digit decomposition of `ZMod (p^2)` defined in
`Submission/Work/LinnikAreas/CorrAllR/DefsSq.lean` (import it via the `depends_on` module).
This is the general-`n` version of the `n = 3` private lemma `prod_chi_ratio` of
`Submission/Commons/NumberTheory/DirichletCharacter/charCorrelation6_primeSq.lean`, whose
supporting private lemmas (`chi_factor_ratio`, `chi_shift`, `zmd`, `zmd_add_natCast`,
`zmod_sq_add_digit`, `zmd_castHom`) are all independent of `n` and can be copied verbatim
into the new file (making them public). -/
theorem prod_chi_ratio (p : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ (p ^ 2)) {n : ℕ}
    (c : Fin n → ℕ) (ρ : ZMod p) (h : ∀ l : Fin n, ρ + (c l : ZMod p) ≠ 0) (y : ZMod p) :
    (∏ l : Fin n, χ (zmd p ρ y + ((c l : ℕ) : ZMod (p ^ 2))))
      = (∏ l : Fin n, χ (zmd p ρ 0 + ((c l : ℕ) : ZMod (p ^ 2))))
        * ((χ (((1 + p : ℕ)) : ZMod (p ^ 2)))
            ^ (∑ l : Fin n, ((ρ + (c l : ZMod p))⁻¹).val)) ^ y.val := by
  have hterm : ∀ l : Fin n, χ (zmd p ρ y + ((c l : ℕ) : ZMod (p^2)))
      = χ (zmd p ρ 0 + ((c l : ℕ) : ZMod (p^2)))
        * (χ (((1 + p : ℕ)) : ZMod (p^2))) ^ (y.val * ((ρ + (c l : ZMod p))⁻¹).val) :=
    fun l => chi_factor_ratio χ (c l) ρ (h l) y
  rw [Finset.prod_congr rfl (fun l _ => hterm l), Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_pow_eq_pow_sum, ← pow_mul]
  congr 1
  rw [Nat.mul_comm (∑ l : Fin n, ((ρ + (c l : ZMod p))⁻¹).val) y.val, Finset.mul_sum]

end Work.LinnikAreas.CorrAllR
