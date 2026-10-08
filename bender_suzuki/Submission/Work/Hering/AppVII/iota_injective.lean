import Mathlib
import Submission.Work.Hering.AppVII.brauer_setup
import Submission.Work.CharCore.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.AppVII

open Polynomial

/-- If `q ∈ ℤ[X]` vanishes at a primitive `n`-th root of unity `x`, then `q` is divisible by
`cyclotomic n ℤ`.  Indeed `cyclotomic n ℤ` is the minimal polynomial of `x` over `ℤ`
(`Polynomial.cyclotomic_eq_minpoly`), so it divides every polynomial killing `x`. -/
theorem cyclotomic_dvd_of_eval₂_eq_zero {n : ℕ} (hn : 0 < n) {x : ℂ} (hx : IsPrimitiveRoot x n)
    {q : Polynomial ℤ} (hq : Polynomial.eval₂ (Int.castRingHom ℂ) x q = 0) :
    Polynomial.cyclotomic n ℤ ∣ q := by
  have haeval : (Polynomial.aeval x) q = 0 := by
    rw [Polynomial.aeval_def,
      show (algebraMap ℤ ℂ : ℤ →+* ℂ) = Int.castRingHom ℂ from rfl]
    exact hq
  have hmin : Polynomial.cyclotomic n ℤ = minpoly ℤ x := Polynomial.cyclotomic_eq_minpoly hx hn
  have hint : IsIntegral ℤ x := hx.isIntegral hn
  have hdvd : minpoly ℤ x ∣ q := minpoly.isIntegrallyClosed_dvd hint haeval
  rwa [← hmin] at hdvd

/-- The value of `iota n` on the class of a polynomial `q ∈ ℤ[X]`. -/
theorem iota_mk {n : ℕ} [NeZero n] (q : Polynomial ℤ) :
    Work.Hering.AppVII.iota n (AdjoinRoot.mk (Polynomial.cyclotomic n ℤ) q)
      = Polynomial.eval₂ (Int.castRingHom ℂ)
          (Complex.exp (2 * Real.pi * Complex.I / n)) q :=
  AdjoinRoot.lift_mk _ q

theorem iota_injective {A : Type*} [Group A] [Fintype A] :
    Function.Injective (Work.Hering.AppVII.iota (Nat.card A)) := by
  intro x y hxy
  obtain ⟨q, hq⟩ := AdjoinRoot.mk_surjective x
  obtain ⟨r, hr⟩ := AdjoinRoot.mk_surjective y
  rw [← hq, ← hr] at hxy ⊢
  rw [iota_mk, iota_mk] at hxy
  rw [AdjoinRoot.mk_eq_mk]
  have h1 : Polynomial.eval₂ (Int.castRingHom ℂ)
      (Complex.exp (2 * Real.pi * Complex.I / (Nat.card A : ℂ))) (q - r) = 0 := by
    rw [Polynomial.eval₂_sub, hxy, sub_self]
  exact cyclotomic_dvd_of_eval₂_eq_zero (NeZero.pos (Nat.card A))
    (Complex.isPrimitiveRoot_exp (Nat.card A) (NeZero.ne (Nat.card A))) h1

end Work.Hering.AppVII
