import Mathlib

namespace Work.SynFFT

/-- Arithmetic core of the fold-combination cost bound: with `W = 1000 * K * X`
(a lower bound for the working size `V`), the four contributions
`a*W` (outer pre-phase), `n*(b*W + d*(S+1))` (the fold steps), `d` (tail) and
`c*W` (outer post-phase) fit inside `1000 * K * C * ((n+1)*X) + 1000 * K * C`
where `C = a + b + 3*d + c`.  The only input about `S` is `S + 1 ≤ 2*W`. -/
private lemma foldCostAux (a b c d K n S X : ℕ) (hK : 1 ≤ K)
    (hS : S + 1 ≤ 2 * (1000 * K * X)) :
    (a * (1000 * K * X) + (n * (b * (1000 * K * X) + d * (S + 1)) + d)) + c * (1000 * K * X) ≤
      1000 * K * (a + b + 3 * d + c) * ((n + 1) * X) + 1000 * K * (a + b + 3 * d + c) := by
  set W := 1000 * K * X with hW
  set C := a + b + 3 * d + c with hC
  -- the fold term, using `S + 1 ≤ 2*W`
  have hS2 : n * d * (S + 1) ≤ n * d * (2 * W) := by
    rw [hW]; exact Nat.mul_le_mul_left _ hS
  -- the coefficients of `W` fit into `C * (n+1)`
  have hscalar : a + n * b + 2 * n * d + c ≤ C * (n + 1) := by rw [hC]; nlinarith
  have hmain : (a + n * b + 2 * n * d + c) * W ≤ C * (n + 1) * W :=
    Nat.mul_le_mul_right W hscalar
  -- the additive tail `d` is absorbed by the constant `1000 * K * C`
  have hconst : d ≤ 1000 * K * C := by rw [hC]; nlinarith [hK]
  have hkey : 1000 * K * C * ((n + 1) * X) = C * (n + 1) * W := by rw [hW]; ring
  rw [hkey]
  nlinarith [hS2, hmain, hconst]

theorem axFoldCost (KCpre KCstep KCpost Kfold Km Kt Ka n S V X : ℕ)
    (hV : V = 1000 * (Km + Kt + Ka + 1) * X) (hS : S + 1 ≤ 2 * V) :
    (KCpre * V + (n * (KCstep * V + Kfold * (S + 1)) + Kfold)) + KCpost * V ≤
      1000 * (Km + Kt + Ka + 1) * (KCpre + KCstep + 3 * Kfold + KCpost) * ((n + 1) * X) +
        1000 * (Km + Kt + Ka + 1) * (KCpre + KCstep + 3 * Kfold + KCpost) := by
  subst hV
  exact foldCostAux KCpre KCstep KCpost Kfold (Km + Kt + Ka + 1) n S X (by omega) hS

end Work.SynFFT
