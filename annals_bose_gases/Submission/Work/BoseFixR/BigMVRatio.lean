import ChallengeDeps
import Submission.Work.BoseFixR.RB5FSDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/BigMVRatio.lean` — the window `𝓜` as a power of `X`

The far leg works with FS's matrix-localisation window

`𝓜 = K_𝓜 (μa³)^{-1/4}`  (FS `eq:DefM`, `Work.BoseBox.bigM` at the honest
parameters, recorded as `Work.BoseFixR.bigMV`),

`K_𝓜 = X^{-1}`, `X = (μa³)^{1/323}`, while the box side is
`ℓ = K_ℓ(μa)^{-1/2}`, `K_ℓ = X^{-3/2}`.  FS write the window in the *box*
variables as

`𝓜 = X^{337/4}·μℓ³`,

the form in which `𝓜` is compared with the density scale `μℓ³` of the box
(Session-287 rung: the `𝓜`-window has to be a monomial in `X` times `μℓ³`).
The identity is pure monomial arithmetic in `t = μa³`:

  `𝓜 = X^{-1}(μa³)^{-1/4} = (μa³)^{-1/323 - 1/4}`,
  `X^{337/4}·μℓ³ = X^{337/4}·X^{-9/2}·(μa³)^{-1/2} = (μa³)^{319/1292 - 1/2}`,

and `-1/323 - 1/4 = 319/1292 - 1/2 = -327/1292`.

Here it is proved as an exact identity (`X^{337/4}` *is* the compensating power
of `X` — the exponent `337/4` is forced, up to the free constant `K_𝓜`), so that
every consumer can rewrite `bigMV` into the `X`-monomial calculus
(`fsXp_mul`, `fsXp_pow`, `fsXp_rpow`) rather than carrying `rpow` bookkeeping.
-/

namespace Work.BoseFixR

open Work.BoseBox

/-- `t ^ c = fsXp t (323 * c)`: a plain real power of the diluteness is the
`X`-monomial with exponent `323c`. -/
private lemma rpow_eq_fsXp {t c : ℝ} : t ^ c = fsXp t (323 * c) := by
  rw [fsXp, mul_div_cancel_left₀ c (by norm_num : (323:ℝ) ≠ 0)]

/-- `(x ^ a) ^ n = x ^ (a * n)` for `x ≥ 0` (the exponent of a real power is
multiplied by a natural power). -/
private lemma rpow_pow_natCast {x : ℝ} (hx : 0 ≤ x) (a : ℝ) (n : ℕ) :
    (x ^ a) ^ n = x ^ (a * n) := by
  rw [← Real.rpow_natCast (x ^ a) n, ← Real.rpow_mul hx a (n:ℝ)]

/-- The healing-length arithmetic `M(M A)^{-3/2} = (M A³)^{-1/2}`
(`M = μ`, `A = a v`): the density `M` and the square of the box side
`(μ a)^{-1/2}` combine into the diluteness `(μa³)^{-1/2}`. -/
private lemma mu_mul_rpow (M A : ℝ) (hM : 0 < M) (hA : 0 < A) :
    M * (M * A) ^ (-(3/2 : ℝ)) = (M * A ^ 3) ^ (-(1/2 : ℝ)) := by
  rw [show A ^ 3 = A ^ (3:ℝ) by simp]
  calc M * (M * A) ^ (-(3/2 : ℝ))
      = M * (M ^ (-(3/2:ℝ)) * A ^ (-(3/2:ℝ))) := by rw [Real.mul_rpow hM.le hA.le]
    _ = M ^ (1:ℝ) * M ^ (-(3/2:ℝ)) * A ^ (-(3/2:ℝ)) := by rw [Real.rpow_one M]; ring
    _ = M ^ ((1:ℝ) + -(3/2)) * A ^ (-(3/2:ℝ)) := by rw [Real.rpow_add hM]
    _ = M ^ (-(1/2:ℝ)) * A ^ (-(3/2:ℝ)) := by
          rw [show (1:ℝ) + -(3/2) = -(1/2) by norm_num]
    _ = M ^ (-(1/2:ℝ)) * (A ^ (3:ℝ)) ^ (-(1/2:ℝ)) := by
          rw [show A ^ (-(3/2:ℝ)) = (A ^ (3:ℝ)) ^ (-(1/2:ℝ)) from by
            rw [← Real.rpow_mul hA.le 3 (-(1/2)), show (3:ℝ)*(-(1/2)) = -(3/2) by norm_num]]
    _ = (M * A ^ (3:ℝ)) ^ (-(1/2:ℝ)) := (Real.mul_rpow hM.le (Real.rpow_nonneg hA.le 3)).symm

/-- **FS's window in the box variables**: `𝓜 = K_𝓜(μa³)^{-1/4} = X^{337/4}·μℓ³`
at the honest parameters (`X = (μa³)^{1/323}`, `ℓ = K_ℓ(μa)^{-1/2}`,
`K_ℓ = X^{-3/2}`).  The exponent `337/4` is exactly
`323·(-1/4) + 1 + (3/2)·323·(1/2)` in units of `1/323`. -/
theorem BigMVRatio {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (hav : 0 < BoseGases.a v) (hμ : 0 < μ) :
    Work.BoseFixR.bigMV v μ = (Work.BoseFixR.fsX v μ) ^ (337 / 4 : ℝ) * (μ * Work.BoseFixR.ell v μ ^ 3) := by
  have hT : 0 < dil v μ := by rw [dil]; positivity
  have hT0 : (0:ℝ) ≤ dil v μ := hT.le
  have hB : (0:ℝ) ≤ μ * BoseGases.a v := le_of_lt (mul_pos hμ hav)
  -- `μ·(μa)^{-3/2} = (μa³)^{-1/2}`
  have hM1 : μ * (μ * BoseGases.a v) ^ (-(3/2:ℝ)) = (dil v μ) ^ (-(1/2:ℝ)) := by
    rw [dil]; exact mu_mul_rpow μ (BoseGases.a v) hμ hav
  -- left-hand side: `𝓜 = K_𝓜(μa³)^{-1/4} = X^{-327/4}`
  have hL : bigMV v μ = fsXp (dil v μ) (-(327/4)) := by
    show fsXp (dil v μ) (-1) * (dil v μ) ^ (-(1/4:ℝ)) = fsXp (dil v μ) (-(327/4))
    rw [rpow_eq_fsXp (t := dil v μ) (c := -(1/4:ℝ)),
        show (323:ℝ) * (-(1/4)) = -(323/4) by norm_num, fsXp_mul hT]
    rw [show (-1:ℝ) + -(323/4) = -(327/4) by norm_num]
  -- `X^{337/4}` as a monomial
  have hX : (fsX v μ) ^ (337/4:ℝ) = fsXp (dil v μ) (337/4) := by
    have h1 : (fsXp (dil v μ) 1) ^ (337/4:ℝ) = fsXp (dil v μ) (1 * (337/4)) :=
      fsXp_rpow hT0 1 (337/4)
    show (fsXp (dil v μ) 1) ^ (337/4:ℝ) = fsXp (dil v μ) (337/4)
    rw [h1, show (1:ℝ) * (337/4) = 337/4 by norm_num]
  -- `ℓ³ = X^{-9/2}(μa)^{-3/2}`
  have hpow : ell v μ ^ 3 = fsXp (dil v μ) (-(9/2)) * (μ * BoseGases.a v) ^ (-(3/2:ℝ)) := by
    have hell : ell v μ = fsXp (dil v μ) (-(3/2:ℝ)) * (μ * BoseGases.a v) ^ (-(1/2:ℝ)) := rfl
    have hA3 : (fsXp (dil v μ) (-(3/2:ℝ))) ^ 3 = fsXp (dil v μ) (-(9/2)) := by
      rw [fsXp_pow hT0]; congr 1; push_cast; norm_num
    have hB3 : ((μ * BoseGases.a v) ^ (-(1/2:ℝ))) ^ 3 = (μ * BoseGases.a v) ^ (-(3/2:ℝ)) := by
      rw [rpow_pow_natCast hB]; congr 1; push_cast; norm_num
    rw [hell, mul_pow, hA3, hB3]
  -- `μℓ³ = X^{-9/2}(μa³)^{-1/2}`
  have hell3 : μ * ell v μ ^ 3 = fsXp (dil v μ) (-(9/2)) * (dil v μ) ^ (-(1/2:ℝ)) := by
    have hr : μ * (fsXp (dil v μ) (-(9/2:ℝ)) * (μ * BoseGases.a v) ^ (-(3/2:ℝ)))
        = fsXp (dil v μ) (-(9/2:ℝ)) * (μ * (μ * BoseGases.a v) ^ (-(3/2:ℝ))) := by ring
    rw [hpow, hr, hM1]
  -- `X^{337/4}·μℓ³ = X^{337/4 - 9/2 - 323/2} = X^{-327/4}`: expand the two monomials
  have hR : (fsX v μ) ^ (337/4:ℝ) * (μ * ell v μ ^ 3) = fsXp (dil v μ) (-(327/4)) := by
    rw [hX, hell3, ← mul_assoc, rpow_eq_fsXp (t := dil v μ) (c := -(1/2:ℝ)),
        show (323:ℝ) * (-(1/2)) = -(323/2) by norm_num, fsXp_mul hT, fsXp_mul hT]
    rw [show (337/4:ℝ) + -(9/2) + -(323/2) = -(327/4) by norm_num]
  exact hL.trans hR.symm

end Work.BoseFixR
