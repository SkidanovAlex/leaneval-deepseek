import Mathlib
import Submission.Work.LinnikBurgess.card_hensel_le_sf

namespace Work.LinnikBurgess

open Polynomial

/-- **Fiber bound, zero `p`-adic level case.**

Let `Q ∈ ℤ[X]` have degree `≤ 4` and be nonzero modulo the prime `p`.  Among the `y < p^M`
with `p^A ∣ Q(y)` and `p ∤ Q'(y)` (i.e. `y` is a *simple* root of `Q` modulo `p^A`), there
are at most `4 · p^(M - min A M)`.

The argument: the `y` with `p^A ∣ Q(y)` and `p ∤ Q'(y)` reduce modulo `p^A` to residues that
are simple roots of `Q` modulo `p^A`; by Hensel such a residue is determined by its class
modulo `p`, and a nonzero polynomial of degree `≤ 4` over the field `ZMod p` has at most `4`
roots.  Hence there are at most `4` admissible residues `r ∈ [0, p^A)`, and each residue class
modulo `p^A` meets `[0, p^M)` in at most `p^(M-A)` points. -/
theorem capContent_fiber_zero {p : ℕ} [Fact p.Prime] (Q : Polynomial ℤ)
    (hdeg : Q.natDegree ≤ 4) (hQ : Q.map (Int.castRingHom (ZMod p)) ≠ 0)
    {A M : ℕ} (hA : 1 ≤ A) (S : Finset ℕ)
    (hS : ∀ y ∈ S, ((p ^ A : ℕ) : ℤ) ∣ Q.eval (y : ℤ)
        ∧ ¬ ((p : ℤ) ∣ (Polynomial.derivative Q).eval (y : ℤ)) ∧ y < p ^ M) :
    S.card ≤ 4 * p ^ (M - min A M) := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : 0 < p := hp.pos
  have hpowA : 0 < p ^ A := pow_pos hp0 A
  have hAne : A ≠ 0 := by omega
  have hQne : Q ≠ 0 := fun h => hQ (by rw [h, Polynomial.map_zero])
  -- The residues modulo `p^A` that are simple roots of `Q`.
  set R : Finset ℕ := (Finset.range (p ^ A)).filter (fun r : ℕ =>
      ((p ^ A : ℕ) : ℤ) ∣ Q.eval (r : ℤ)
        ∧ ¬ ((p : ℤ) ∣ (Polynomial.derivative Q).eval (r : ℤ))) with hRdef
  -- Hensel: at most `natDegree Q ≤ 4` such residues.
  have hRle : R.card ≤ 4 := by
    have hsub : R ⊆ henselSet p Q A := by
      intro r hr
      rw [hRdef, Finset.mem_filter] at hr
      obtain ⟨hrrange, hr1, hr2⟩ := hr
      rw [henselSet, Finset.mem_filter]
      refine ⟨hrrange, 0, ?_, ?_, ?_⟩
      · simp
      · simpa using hr2
      · have hmax : max (2 * 0 + 1) (A + 0) = A := by omega
        rw [hmax]; exact hr1
    calc R.card ≤ (henselSet p Q A).card := Finset.card_le_card hsub
      _ ≤ Q.natDegree := card_hensel_le_sf Q hQne A hA
      _ ≤ 4 := hdeg
  -- The quotient `y / p^A` is bounded by `p^(M - A)`.
  have hdivlt : ∀ y : ℕ, y < p ^ M → y / p ^ A < p ^ (M - A) := by
    intro y hy
    rw [Nat.div_lt_iff_lt_mul hpowA]
    rcases lt_or_ge M A with hMA | hAM
    · have h1 : M - A = 0 := Nat.sub_eq_zero_of_le (le_of_lt hMA)
      have h2 : p ^ M ≤ p ^ A := Nat.pow_le_pow_right hp0 (le_of_lt hMA)
      calc y < p ^ M := hy
        _ ≤ p ^ A := h2
        _ = p ^ (M - A) * p ^ A := by rw [h1, pow_zero, one_mul]
    · have h1 : M - A + A = M := Nat.sub_add_cancel hAM
      calc y < p ^ M := hy
        _ = p ^ (M - A + A) := by rw [h1]
        _ = p ^ (M - A) * p ^ A := pow_add p (M - A) A
  -- The reduction `y ↦ (y % p^A, y / p^A)` maps `S` into `R × {0,…,p^(M-A)-1}`.
  have hmaps : Set.MapsTo (fun y : ℕ => (y % p ^ A, y / p ^ A)) (↑S)
      (↑(R ×ˢ Finset.range (p ^ (M - A)))) := by
    intro y hyS
    obtain ⟨hy1, hy2, hy3⟩ := hS y hyS
    show (y % p ^ A, y / p ^ A) ∈ R ×ˢ Finset.range (p ^ (M - A))
    rw [Finset.mem_product]
    refine ⟨?_, Finset.mem_range.mpr (hdivlt y hy3)⟩
    rw [hRdef, Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr (Nat.mod_lt y hpowA), ?_, ?_⟩
    · -- `p^A ∣ Q (y % p^A)`, since `y ≡ y % p^A (mod p^A)`.
      have hmod : ((p ^ A : ℕ) : ℤ) ∣ (y : ℤ) - ((y % p ^ A : ℕ) : ℤ) :=
        (Nat.modEq_iff_dvd (n := p ^ A) (a := y % p ^ A) (b := y)).mp
          (Nat.mod_modEq y (p ^ A))
      have hdiff : ((p ^ A : ℕ) : ℤ) ∣ Q.eval (y : ℤ) - Q.eval ((y % p ^ A : ℕ) : ℤ) :=
        dvd_trans hmod (sub_dvd_eval_sub (y : ℤ) ((y % p ^ A : ℕ) : ℤ) Q)
      have h2 : ((p ^ A : ℕ) : ℤ) ∣ Q.eval (y : ℤ) - (Q.eval (y : ℤ) - Q.eval ((y % p ^ A : ℕ) : ℤ)) :=
        dvd_sub hy1 hdiff
      rwa [sub_sub_cancel] at h2
    · -- `p ∤ Q' (y % p^A)`, since `p ∣ y - y % p^A`.
      have hp_dvd : (p : ℤ) ∣ ((p ^ A : ℕ) : ℤ) := by
        rw [Nat.cast_pow]
        exact dvd_pow_self (p : ℤ) hAne
      have hmod : ((p ^ A : ℕ) : ℤ) ∣ (y : ℤ) - ((y % p ^ A : ℕ) : ℤ) :=
        (Nat.modEq_iff_dvd (n := p ^ A) (a := y % p ^ A) (b := y)).mp
          (Nat.mod_modEq y (p ^ A))
      have hpdvd : (p : ℤ) ∣ (y : ℤ) - ((y % p ^ A : ℕ) : ℤ) := dvd_trans hp_dvd hmod
      intro hbad
      exact hy2 (by
        have hdiff' : (p : ℤ) ∣ (Polynomial.derivative Q).eval (y : ℤ)
            - (Polynomial.derivative Q).eval ((y % p ^ A : ℕ) : ℤ) :=
          dvd_trans hpdvd
            (sub_dvd_eval_sub (y : ℤ) ((y % p ^ A : ℕ) : ℤ) (Polynomial.derivative Q))
        have hsum : (Polynomial.derivative Q).eval (y : ℤ)
            = ((Polynomial.derivative Q).eval (y : ℤ)
                - (Polynomial.derivative Q).eval ((y % p ^ A : ℕ) : ℤ))
              + (Polynomial.derivative Q).eval ((y % p ^ A : ℕ) : ℤ) := by ring
        rw [hsum]
        exact dvd_add hdiff' hbad)
  -- The reduction is injective on `[0, p^M)` (indeed on all of `ℕ`).
  have hinj : Set.InjOn (fun y : ℕ => (y % p ^ A, y / p ^ A)) (↑S) := by
    intro y _ y' _ heq
    have h1 : y % p ^ A = y' % p ^ A := congrArg Prod.fst heq
    have h2 : y / p ^ A = y' / p ^ A := congrArg Prod.snd heq
    calc y = p ^ A * (y / p ^ A) + y % p ^ A := (Nat.div_add_mod y (p ^ A)).symm
      _ = p ^ A * (y' / p ^ A) + y' % p ^ A := by rw [h1, h2]
      _ = y' := Nat.div_add_mod y' (p ^ A)
  have hcard := Finset.card_le_card_of_injOn (fun y : ℕ => (y % p ^ A, y / p ^ A)) hmaps hinj
  have hmin : M - min A M = M - A := by omega
  calc S.card ≤ (R ×ˢ Finset.range (p ^ (M - A))).card := hcard
    _ = R.card * p ^ (M - A) := by rw [Finset.card_product, Finset.card_range]
    _ ≤ 4 * p ^ (M - A) := Nat.mul_le_mul_right _ hRle
    _ = 4 * p ^ (M - min A M) := by rw [hmin]

end Work.LinnikBurgess
