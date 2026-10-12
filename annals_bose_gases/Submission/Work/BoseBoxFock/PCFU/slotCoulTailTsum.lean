import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.W1funDecay_momentsAbs
import Submission.Work.BoseBoxFock.L1Tails.kernelTail
import Submission.Work.BoseBoxFock.PCFU.windowPartialSumLe
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.slotCoulTailTsum` — the lattice Coulomb tail as an infinite series

The finite-set lattice Coulomb tail of the scattering weight `W₁ = W1fun v h ℓ`
(`Work.BoseBoxFock.PCFU.coulTail_W1fun`) is upgraded here to the **infinite lattice series**
truncated at the box cut-off `Λ = uvRad ℓ N`:

    Σ'_n 1_{Λ ≤ ‖κ_n‖} · ‖Ŵ₁(κ_n)‖² / ‖κ_n‖²  ≤  C (1 + R)⁶ ℓ³ / Λ ,      κ_n = kappaL ℓ n ,

together with the **summability** of the summand (which is what makes the `tsum` an honest limit
rather than `0`).  This is the `hτ` input of the `L¹Tails` chapter in its infinite-series shape,
consumed e.g. by `Submission/Work/BoseBoxFock/PCFU/_slotScratch2.lean` (`slotMain`).

**Proof.**  Three ingredients, all already available:

* the momentum decay `‖Ŵ₁(q)‖ ≤ K (1+R)³/(1+‖q‖)` (`Work.BoseBogFS.W1funDecay_momentsAbs`, `m = 0`);
* the finite partial-sum estimate `Work.BoseBoxFock.PCFU.windowPartialSumLe`: for an abstract weight
  `W` with decay `‖kinFT W q‖ ≤ K/(1+‖q‖)` the windowed partial sums over *every* finite set are
  bounded by `C K² ℓ³/Λ`;
* the passage from a uniform bound on the finite partial sums of a **nonnegative** sequence to the
  infinite sum: `summable_of_sum_le` and `Real.tsum_le_of_sum_le`.

Substituting the decay constant `K(1+R)³` gives the constant `C K²` and the factor `(1+R)⁶`.
-/

namespace Work.BoseBoxFock.PCFU

open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

theorem slotCoulTailTsum : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ} {N : ℕ},
      0 < R → 0 < ℓ → (∀ x, 0 ≤ v x) → _root_.BoseGases.IsRadial v →
      tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R →
      R ≤ ℓ * Submission.BoseGases.chiR0 → 1 ≤ N →
      Summable (fun n : Fin 3 → ℤ =>
        (if Work.BoseBoxFock.uvRad ℓ N ≤ ‖Work.BoseBoxFock.kappaL ℓ n‖ then (1 : ℝ) else 0)
          * (‖Submission.BoseGases.kinFT
                (fun y => ((Work.BoseFixR.W1fun v h ℓ y : ℝ) : ℂ))
                (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2
              / ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2))
      ∧ (∑' n : Fin 3 → ℤ,
        (if Work.BoseBoxFock.uvRad ℓ N ≤ ‖Work.BoseBoxFock.kappaL ℓ n‖ then (1 : ℝ) else 0)
          * (‖Submission.BoseGases.kinFT
                (fun y => ((Work.BoseFixR.W1fun v h ℓ y : ℝ) : ℂ))
                (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2
              / ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2))
        ≤ C * (1 + R) ^ 6 * ℓ ^ 3 / Work.BoseBoxFock.uvRad ℓ N := by
  -- the decay constant of `Ŵ₁` and the constant of the finite partial-sum estimate
  obtain ⟨K, hK0, hKdec⟩ := Work.BoseBogFS.W1funDecay_momentsAbs
  obtain ⟨C₀, hC₀0, hC₀⟩ := windowPartialSumLe
  refine ⟨C₀ * K ^ 2, mul_nonneg hC₀0 (sq_nonneg K), ?_⟩
  intro v hsci R ℓ N hR hℓ hv hvrad hsupp hRℓ hN
  -- the cut-off `uvRad ℓ N` is positive
  have hΛ : 0 < Work.BoseBoxFock.uvRad ℓ N := by
    rw [Work.BoseBoxFock.uvRad]
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    positivity
  -- the decay of `Ŵ₁` in the exact shape required by `windowPartialSumLe`
  have hdec : ∀ q : E3, ‖Submission.BoseGases.kinFT
        (fun y => ((Work.BoseFixR.W1fun v hsci ℓ y : ℝ) : ℂ)) q‖
      ≤ K * (1 + R) ^ 3 / (1 + ‖q‖) := by
    intro q
    have hgo := hKdec (v := v) (h := hsci) hR hℓ hv hvrad hsupp hRℓ 0 (by norm_num)
      (0 : Fin 3) q
    have hfun : (fun y : E3 => ((((y.ofLp (0 : Fin 3) : ℝ)) ^ 0)
          * Work.BoseFixR.W1fun v hsci ℓ y : ℂ))
        = fun y : E3 => ((Work.BoseFixR.W1fun v hsci ℓ y : ℝ) : ℂ) := by
      funext y
      simp
    rwa [hfun] at hgo
  -- the summand is nonnegative
  have hGnn : ∀ n : Fin 3 → ℤ,
      0 ≤ (if Work.BoseBoxFock.uvRad ℓ N ≤ ‖Work.BoseBoxFock.kappaL ℓ n‖
            then (1 : ℝ) else 0)
        * (‖Submission.BoseGases.kinFT
              (fun y => ((Work.BoseFixR.W1fun v hsci ℓ y : ℝ) : ℂ))
              (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2
            / ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2) := by
    intro n
    by_cases h : Work.BoseBoxFock.uvRad ℓ N ≤ ‖Work.BoseBoxFock.kappaL ℓ n‖
    · rw [if_pos h, one_mul]
      positivity
    · rw [if_neg h, zero_mul]
  -- the uniform bound on the finite partial sums
  have hb : ∀ u : Finset (Fin 3 → ℤ),
      (∑ n ∈ u,
        (if Work.BoseBoxFock.uvRad ℓ N ≤ ‖Work.BoseBoxFock.kappaL ℓ n‖ then (1 : ℝ) else 0)
          * (‖Submission.BoseGases.kinFT
                (fun y => ((Work.BoseFixR.W1fun v hsci ℓ y : ℝ) : ℂ))
                (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2
              / ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2))
        ≤ C₀ * K ^ 2 * (1 + R) ^ 6 * ℓ ^ 3 / Work.BoseBoxFock.uvRad ℓ N := by
    intro u
    have hchild := hC₀ hℓ hΛ (show (0 : ℝ) ≤ K * (1 + R) ^ 3 by positivity) hdec u
    calc (∑ n ∈ u,
        (if Work.BoseBoxFock.uvRad ℓ N ≤ ‖Work.BoseBoxFock.kappaL ℓ n‖ then (1 : ℝ) else 0)
          * (‖Submission.BoseGases.kinFT
                (fun y => ((Work.BoseFixR.W1fun v hsci ℓ y : ℝ) : ℂ))
                (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2
              / ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2))
        ≤ C₀ * (K * (1 + R) ^ 3) ^ 2 * ℓ ^ 3 / Work.BoseBoxFock.uvRad ℓ N := hchild
      _ = C₀ * K ^ 2 * (1 + R) ^ 6 * ℓ ^ 3 / Work.BoseBoxFock.uvRad ℓ N := by ring
  exact ⟨summable_of_sum_le hGnn hb, Real.tsum_le_of_sum_le hGnn hb⟩

end Work.BoseBoxFock.PCFU
