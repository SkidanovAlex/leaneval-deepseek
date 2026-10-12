import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseBoxFock.KafzHonest
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.kf_Q3b` — the second half of the `Q̃₃` row of `H2ndF`

The `Q̃₃` row of FS `eq:HLambdaSecond` is

    `ℓ⁻³ Σ_s Σ_k f_L(s) Ŵ₁(k) a₀† ã_s† a_{s−k} a_k + h.c.`

The `h.c.` half is `a_k† a_{s−k}† ã_s a₀`; the dictionary lemma here transports its
spectator word to `Work.BoseBoxFock`, picking up the anti-normal monomial
`monoOp 1 0 B = a₀ ∘ lift B` (`a₀` on the outside because the spectator operators
commute with the condensate `a₀`).

The proof is the `a₀`-version of `Work.BoseBoxFock.split_weighted_number`: the
dictionary lemmas `split_creOf`/`split_annOf` transport the three spectator factors,
`split_ann_zero_apply` transports `ann m 0`, and `lift_comm_a0` moves the condensate
annihilation to the front.
-/

noncomputable section

open Work.BoseB4

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {m : ℕ} [NeZero m]

/-- `monoOp 1 0 B = a₀ ∘ lift B` (`B ↦ monoOp p q B` is `a₀^p ∘ (a₀†)^q ∘ lift B`). -/
lemma kf_Q3b_monoOp_one_zero (B : cfock (Excited m) →ₗ[ℂ] cfock (Excited m)) :
    monoOp 1 0 B = a0.comp (lift B) := by
  simp [monoOp, a0pow_succ, a0dpow_zero]

/-- `lift A (lift B (lift C z)) = lift (A ∘ B ∘ C) z`. -/
lemma kf_Q3b_lift3 (A B C : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (z : FockCore (cfock (Excited m))) :
    lift A (lift B (lift C z)) = lift (A.comp (B.comp C)) z := by
  rw [Work.BoseB4.lift_comp_apply, Work.BoseB4.lift_comp_apply]
  rfl

theorem kf_Q3b {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (S Ks : Finset Mode) (γ : Mode → Mode → ℝ) (g f : Mode → Fin m → ℝ)
    (hg : ∀ s ∈ S, g s 0 = 0) (hf : ∀ k : Mode, f k 0 = 0) (x : Work.BoseB4.RealFock m) :
    Work.BoseB4.split ((∑ s ∈ S, ∑ k ∈ Ks, γ s k •
        (((Work.BoseB4.creOf m (f k)) ∘ₗ (Work.BoseB4.creOf m (f (s - k))) ∘ₗ (Work.BoseB4.annOf m (g s)) ∘ₗ (Work.BoseB4.ann m 0)) x)))
      = (Work.BoseB4.monoOp 1 0 (∑ s ∈ S, ∑ k ∈ Ks, ((γ s k : ℝ) : ℂ) •
              ((Work.BoseBoxFock.creOfE (f k)) ∘ₗ (Work.BoseBoxFock.creOfE (f (s - k))) ∘ₗ (Work.BoseBoxFock.annOfE (g s))))) (Work.BoseB4.split x) := by
  -- the per-(s,k) transport of one word `creOf k ∘ creOf (s-k) ∘ annOf s ∘ ann 0`
  have hterm : ∀ s ∈ S, ∀ k ∈ Ks, ∀ y : RealFock m,
      split ((((creOf m (f k)) ∘ₗ (creOf m (f (s - k))) ∘ₗ (annOf m (g s)) ∘ₗ (ann m 0)) y))
        = (monoOp 1 0 ((creOfE (f k)) ∘ₗ (creOfE (f (s - k))) ∘ₗ (annOfE (g s)))) (split y) := by
    intro s hs k hk y
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    rw [split_creOf _ (hf k), split_creOf _ (hf (s - k)), split_annOf _ (hg s hs),
      Work.BoseB4.split_ann_zero_apply]
    rw [kf_Q3b_monoOp_one_zero, LinearMap.comp_apply]
    rw [Work.BoseB4.lift_a0_apply, Work.BoseB4.lift_a0_apply, Work.BoseB4.lift_a0_apply]
    rw [kf_Q3b_lift3]
  -- `split` of the sum of the terms
  have hA : split ((∑ s ∈ S, ∑ k ∈ Ks, γ s k •
        (((creOf m (f k)) ∘ₗ (creOf m (f (s - k))) ∘ₗ (annOf m (g s)) ∘ₗ (ann m 0)) x)))
      = ∑ s ∈ S, ∑ k ∈ Ks, ((γ s k : ℝ) : ℂ) •
          (monoOp 1 0 ((creOfE (f k)) ∘ₗ (creOfE (f (s - k))) ∘ₗ (annOfE (g s)))) (split x) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [map_smul, hterm s hs k hk]
    exact (Complex.coe_smul (γ s k)
      ((monoOp 1 0 ((creOfE (f k)) ∘ₗ (creOfE (f (s - k))) ∘ₗ (annOfE (g s)))) (split x))).symm
  -- the anti-normal monomial of the summed spectator operator
  have hC1 : monoOp 1 0 (∑ s ∈ S, ∑ k ∈ Ks, ((γ s k : ℝ) : ℂ) •
        ((creOfE (f k)) ∘ₗ (creOfE (f (s - k))) ∘ₗ (annOfE (g s))))
      = ∑ s ∈ S, ∑ k ∈ Ks, ((γ s k : ℝ) : ℂ) •
          monoOp 1 0 ((creOfE (f k)) ∘ₗ (creOfE (f (s - k))) ∘ₗ (annOfE (g s))) := by
    rw [show (∑ s ∈ S, ∑ k ∈ Ks, ((γ s k : ℝ) : ℂ) •
          ((creOfE (f k)) ∘ₗ (creOfE (f (s - k))) ∘ₗ (annOfE (g s))))
        = ∑ s ∈ S, (1 : ℂ) • (∑ k ∈ Ks, ((γ s k : ℝ) : ℂ) •
          ((creOfE (f k)) ∘ₗ (creOfE (f (s - k))) ∘ₗ (annOfE (g s)))) from
      Finset.sum_congr rfl (fun s _ => (one_smul ℂ _).symm)]
    rw [monoOp_sum_smul]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    rw [one_smul, monoOp_sum_smul]
  have hC : (monoOp 1 0 (∑ s ∈ S, ∑ k ∈ Ks, ((γ s k : ℝ) : ℂ) •
        ((creOfE (f k)) ∘ₗ (creOfE (f (s - k))) ∘ₗ (annOfE (g s))))) (split x)
      = ∑ s ∈ S, ∑ k ∈ Ks, ((γ s k : ℝ) : ℂ) •
          (monoOp 1 0 ((creOfE (f k)) ∘ₗ (creOfE (f (s - k))) ∘ₗ (annOfE (g s)))) (split x) := by
    rw [hC1, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun k hk => by rw [LinearMap.smul_apply])
  exact hA.trans hC.symm

end Work.BoseBoxFock
