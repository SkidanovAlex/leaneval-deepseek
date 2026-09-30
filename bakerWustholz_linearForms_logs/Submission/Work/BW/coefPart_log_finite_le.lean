import Mathlib
import Submission.Work.BW.est15defs
import Submission.Work.BW.tijdeman_rat
import Submission.Work.BW.piRat_int
import Submission.Work.BW.thetaJ_int_cast
import Submission.Work.BW.finitePlace_basic
import Submission.Work.BW.log_le_neg_log_pow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Kummer/2-adic integrality at a finite place `w`: the `Π`-, `u`- and `Θ`-factors of `coefKJ` contribute at most the Kummer term `2Jh(λ₀+1)·(−log w(2))`. Indeed `piRat` is an integer (`deltaRat x k = C(x+k,k)`), `ulcm h` is an integer, and `tijdeman_rat` gives `2^{2Jh(λ₀+1)} u(h)^{t₀} Θ(s/2^J+λ₋₁; h, λ₀+1, t₀) ∈ ℤ`, so `w(u^{t₀}Θ) ≤ w(2)^{-2Jh(λ₀+1)}`; all three logged factors are `≤ 1` (and `Real.log 0 = 0` covers vanishing cases). Requires `import Submission.Work.BW.tijdeman_rat`. -/
theorem coefPart_log_finite_le {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (t0 : ℕ) (t : Fin (r - 1) → ℕ) (s : ℤ)
    (lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ))
    (w : NumberField.FinitePlace K) :
    Real.log (w (coefPart b k L ι (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) J t0 t s lm))
      ≤ (2 * J * (acH K b v) * (((lm.2.1 : ℕ) + 1)) : ℝ) * (- Real.log (w 2)) := by
  classical
  -- basic facts about the finite place
  obtain ⟨h2pos, h2le, hnn, hnat, hint⟩ := finitePlace_basic (K := K) w
  -- integrality of the `Π`-factor
  obtain ⟨Np, hNp⟩ :=
    piRat_int b k L ι (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) t lm
  -- integrality of `2^{2Jh(λ₀+1)} · u(h)^{t₀} · Θ` (Kummer/Tijdeman)
  obtain ⟨Nt, hNt⟩ :=
    thetaJ_int_cast (K := K) (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) J t0 s lm
  -- `w` of the `Π`-factor is `≤ 1`
  have hA : w (((piRat b k L ι (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) t lm : ℚ) : K))
      ≤ 1 := by
    rw [hNp]
    simpa using hint Np
  -- `w` of `u(h)` is `≤ 1`
  have hB : w ((((ulcm (acH K b v) : ℚ) : K))) ≤ 1 := by
    simpa using hnat (ulcm (acH K b v))
  -- push the integrality identity through `w`
  have hkey : (w (2 : K) ^ (J * (2 * (acH K b v) * ((lm.2.1 : ℕ) + 1)))
        * w ((((ulcm (acH K b v) : ℚ) : K))) ^ t0)
        * w (((thetaJ (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) J t0 s lm : ℚ) : K))
      = w (((Nt : ℤ) : K)) := by
    have h := congrArg w hNt
    simp only [map_mul, map_pow] at h
    exact h
  -- main bound: `w(2)^{2Jh(λ₀+1)} · w(coefPart) ≤ 1`
  have hmain : w (2 : K) ^ (J * (2 * (acH K b v) * ((lm.2.1 : ℕ) + 1)))
      * w (coefPart b k L ι (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) J t0 t s lm)
      ≤ 1 := by
    have hwcp : w (coefPart b k L ι (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)
          J t0 t s lm)
        = w (((piRat b k L ι (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) t lm : ℚ) : K))
          * w ((((ulcm (acH K b v) : ℚ) : K))) ^ t0
          * w (((thetaJ (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) J t0 s lm : ℚ) : K)) := by
      rw [coefPart]
      simp only [map_mul, map_pow]
    rw [hwcp]
    have hstep : (w (2 : K) ^ (J * (2 * (acH K b v) * ((lm.2.1 : ℕ) + 1)))
            * w (((piRat b k L ι (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) t lm : ℚ) : K)))
          * (w ((((ulcm (acH K b v) : ℚ) : K))) ^ t0
            * w (((thetaJ (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) J t0 s lm : ℚ) : K)))
        ≤ (w (2 : K) ^ (J * (2 * (acH K b v) * ((lm.2.1 : ℕ) + 1))) * 1)
          * (w ((((ulcm (acH K b v) : ℚ) : K))) ^ t0
            * w (((thetaJ (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) J t0 s lm : ℚ) : K))) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hA (pow_nonneg (hnn (2 : K)) _))
        (mul_nonneg (pow_nonneg (hnn _) t0) (hnn _))
    calc w (2 : K) ^ (J * (2 * (acH K b v) * ((lm.2.1 : ℕ) + 1)))
          * (w (((piRat b k L ι (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) t lm : ℚ) : K))
            * w ((((ulcm (acH K b v) : ℚ) : K))) ^ t0
            * w (((thetaJ (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) J t0 s lm : ℚ) : K)))
        = (w (2 : K) ^ (J * (2 * (acH K b v) * ((lm.2.1 : ℕ) + 1)))
            * w (((piRat b k L ι (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) t lm : ℚ) : K)))
          * (w ((((ulcm (acH K b v) : ℚ) : K))) ^ t0
            * w (((thetaJ (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) J t0 s lm : ℚ) : K))) := by
          ring
      _ ≤ _ := hstep
      _ = w (((Nt : ℤ) : K)) := by
          rw [mul_one, ← mul_assoc]
          exact hkey
      _ ≤ 1 := hint Nt
  -- conclude by taking logarithms
  have hn_eq : (2 * J * (acH K b v) * (((lm.2.1 : ℕ) + 1)) : ℝ)
      = ((J * (2 * (acH K b v) * ((lm.2.1 : ℕ) + 1)) : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hn_eq]
  exact log_le_neg_log_pow (a := w (2 : K))
    (x := w (coefPart b k L ι (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) J t0 t s lm))
    (n := J * (2 * (acH K b v) * ((lm.2.1 : ℕ) + 1)))
    h2pos h2le
    (hnn (coefPart b k L ι (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) J t0 t s lm))
    hmain

end Work.BW
