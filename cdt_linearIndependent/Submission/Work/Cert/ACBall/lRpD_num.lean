import Mathlib
import Submission.Work.Cert.ACBall.LuneShadow
import Submission.Work.Cert.ACBall.LuneChain

namespace Work.Cert.ACBall

/-- Numeric face of the `lRpD` radius: writing `P = w.rpU + (lRp st).r`, `Q = lRpp = 2·LB2`,
`ρ = st.rho`, `D = lRpD st w = P + ⌈ρQ/S⌉ + 1`, and `S` for the certificate scale, the
first-order data `P, Q` dominate the second-order ball term at `ρ`:

* `(P/S)·(ρ/S) + (Q/S)·(ρ/S)² ≤ ⌈ρD/S⌉/S`, and
* `P/S + (Q/S)·(ρ/S) ≤ D/S`.

Both are immediate from `mu_ge` (`⌈x/S⌉ ≥ x/S`): the second says `Qρ/S ≤ ⌈ρQ/S⌉ + 1`, and the
first is the second multiplied by `ρ/S ≥ 0` and combined with `⌈ρD/S⌉ ≥ ρD/S`. -/
theorem lRpD_num (st : Work.Cert.St) (w : Work.Cert.LuneW) (hrho : 0 ≤ st.rho) :
    (((w.rpU + (Work.Cert.ACBall.lRp st).r : ℤ) : ℝ) / (Work.Cert.S : ℝ)) * ((st.rho : ℝ) / (Work.Cert.S : ℝ))
        + (((Work.Cert.ACBall.lRpp : ℤ) : ℝ) / (Work.Cert.S : ℝ)) * ((st.rho : ℝ) / (Work.Cert.S : ℝ)) ^ 2
      ≤ ((Work.Cert.mu st.rho (Work.Cert.ACBall.lRpD st w) : ℤ) : ℝ) / (Work.Cert.S : ℝ) ∧
      (((w.rpU + (Work.Cert.ACBall.lRp st).r : ℤ) : ℝ) / (Work.Cert.S : ℝ))
        + (((Work.Cert.ACBall.lRpp : ℤ) : ℝ) / (Work.Cert.S : ℝ)) * ((st.rho : ℝ) / (Work.Cert.S : ℝ))
      ≤ ((Work.Cert.ACBall.lRpD st w : ℤ) : ℝ) / (Work.Cert.S : ℝ) := by
  have hS : (0 : ℝ) < ((Work.Cert.S : ℤ) : ℝ) := by exact_mod_cast Work.Cert.ACBall.S_pos
  -- `mu` dominates from below
  have key := Work.Cert.ACBall.mu_ge st.rho Work.Cert.ACBall.lRpp
  have hd := Work.Cert.ACBall.mu_ge st.rho (Work.Cert.ACBall.lRpD st w)
  have hD : ((Work.Cert.ACBall.lRpD st w : ℤ) : ℝ)
      = ((w.rpU + (Work.Cert.ACBall.lRp st).r : ℤ) : ℝ)
        + ((Work.Cert.mu st.rho Work.Cert.ACBall.lRpp : ℤ) : ℝ) + 1 := by
    simp [Work.Cert.ACBall.lRpD]
  have hr : (0 : ℝ) ≤ ((st.rho : ℤ) : ℝ) := by exact_mod_cast hrho
  -- cleared form of `Qρ/S ≤ ⌈ρQ/S⌉ + 1`
  have hkey : ((Work.Cert.ACBall.lRpp : ℤ) : ℝ) * ((st.rho : ℤ) : ℝ)
      ≤ (((Work.Cert.mu st.rho Work.Cert.ACBall.lRpp : ℤ) : ℝ) + 1) * (Work.Cert.S : ℝ) := by
    rw [div_le_iff₀ hS] at key
    linarith
  rw [hD] at hd
  rw [div_le_iff₀ hS] at hd
  constructor
  · field_simp
    nlinarith [hkey, hd, hr, hS]
  · rw [hD]
    field_simp
    nlinarith [hkey, hS]

end Work.Cert.ACBall
