import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The height of a maximal ideal of a polynomial ring

For a field `k` and a maximal ideal `𝔪` of `k[X₁, …, Xₙ]`, the height of `𝔪` equals `n`.

This is the equidimensionality of affine space: `k[X₁, …, Xₙ]` has Krull dimension `n`, and every
maximal ideal has height equal to the (Krull) dimension of the ring.  Equivalently, each maximal
ideal is generated up to radical by `n` "independent" elements.

## Proof

Induction on `n`.

* `n = 0`: `MvPolynomial (Fin 0) k` has Krull dimension `0`
  (`MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite` and `ringKrullDim_eq_zero_of_field`),
  so the height of every proper ideal — in particular the maximal ideal `𝔪` — is `0`
  (`Ideal.height_le_ringKrullDim_of_ne_top`).

* `n + 1`: identify `MvPolynomial (Fin (n+1)) k` with `Polynomial (MvPolynomial (Fin n) k)` via
  `MvPolynomial.finSuccEquiv` and transport `𝔪` to a maximal ideal `P` of `R[X]`, `R = k[X₁,…,Xₙ]`.
  Its contraction `p = P ∩ R` is maximal: this is Zariski's lemma for the Jacobson (hence
  Hilbert-Jacobson) ring `R`, packaged as `Polynomial.isMaximal_comap_C_of_isJacobsonRing`.
  Since `P` lies over `p`, `Polynomial.height_eq_height_add_one` gives `ht P = ht p + 1`, and the
  induction hypothesis gives `ht p = n`, whence `ht P = n + 1`.  Finally heights are preserved by
  ring equivalences (`RingEquiv.height_map`).
-/

set_option linter.style.haveILetI false

namespace Work.BW.RB

theorem poly_max_ideal_height {k : Type*} [Field k] (n : ℕ)
    (m : Ideal (MvPolynomial (Fin n) k)) [m.IsMaximal] : m.height = n := by
  induction n with
  | zero =>
    -- `MvPolynomial (Fin 0) k` has Krull dimension `0`, so every proper ideal has height `0`.
    have hm : m.IsMaximal := inferInstance
    have h := Ideal.height_le_ringKrullDim_of_ne_top (I := m) hm.ne_top
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
        ringKrullDim_eq_zero_of_field k, Nat.card_eq_fintype_card, Fintype.card_fin,
        Nat.cast_zero, add_zero] at h
    exact le_bot_iff.mp (WithBot.coe_le_coe.mp h)
  | succ n ih =>
    haveI : IsJacobsonRing (MvPolynomial (Fin n) k) := inferInstance
    -- Identify `k[X₀,…,Xₙ]` with `k[X₁,…,Xₙ][X₀]`.
    let e : MvPolynomial (Fin (n + 1)) k ≃ₐ[k] Polynomial (MvPolynomial (Fin n) k) :=
      MvPolynomial.finSuccEquiv k n
    let P : Ideal (Polynomial (MvPolynomial (Fin n) k)) :=
      m.map (e.toRingEquiv :
        MvPolynomial (Fin (n + 1)) k →+* Polynomial (MvPolynomial (Fin n) k))
    have hPmax : P.IsMaximal := Ideal.map_isMaximal_of_equiv e.toRingEquiv
    haveI := hPmax
    -- The contraction of `P` to the base ring, a maximal ideal by Zariski's lemma.
    let p : Ideal (MvPolynomial (Fin n) k) := P.comap Polynomial.C
    have hpmax : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    haveI := hpmax
    -- `P` lies over `p`.
    have hlie : P.LiesOver p := ⟨by rw [Ideal.under_def, Polynomial.algebraMap_eq]⟩
    haveI := hlie
    have hstep : P.height = p.height + 1 := Polynomial.height_eq_height_add_one p P
    have hpht : p.height = ((n : ℕ) : ℕ∞) := ih p
    have hPht : P.height = ((n + 1 : ℕ) : ℕ∞) := by
      rw [hstep, hpht, Nat.cast_add, Nat.cast_one]
    have hmap : P.height = m.height := RingEquiv.height_map e.toRingEquiv m
    rw [← hmap]
    exact hPht

end Work.BW.RB
