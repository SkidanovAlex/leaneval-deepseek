import ChallengeDeps
import Submission.Work.BoseFixR.FarResidAdm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `epsSplitEqB` — FS `eq:ChoiceEpsilon`'s `ε`-split of the residual Bogoliubov word, re-summed

The `ε`-split correction of `Work.BoseFixR.KzBogFS_epsSplit` is

`Σ_k ½(τ_k − τ'_k)⟨(n_k + n_{-k})f,f⟩`,  `τ'_k = (1−ε)τ_k + ρε^{-1/2}a`.

Since `τ_k − τ'_k = ετ_k − ρε^{-1/2}a`, and `⟨(n_k+n_{-k})f,f⟩ = ⟨n_kf,f⟩ + ⟨n_{-k}f,f⟩`,
the correction splits into an `ετ`-reserve and an `ε^{-1/2}`-diagonal.  When `τ` is *even*
(`τ_{-k} = τ_k`) the `k ↦ −k` reindexing identifies the two halves of the `ετ`-reserve, so the
correction collapses to

`(Σ_k ετ_k⟨n_kf,f⟩) − ρε^{-1/2}a·Σ_k ½⟨(n_k+n_{-k})f,f⟩`.

This is the bookkeeping identity consumed by the far-leg `B`-form of FS `lem:Roughbounds`
(`Work.BoseFixR.FarResidB`) and its auxiliary copy (`Work.BoseFixR.FarResidAdm`).
-/

namespace Work.BoseFixR.FarResidBaux

/-- Reindexing a finite sum over `Mode` by the negation of the summation index
(`Equiv.neg`, the `k ↦ −k` bijection of the mode group). -/
lemma sum_neg_index {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] (g : Mode → ℝ) :
    (∑ k : Mode, g (-k)) = ∑ k : Mode, g k := by
  have h := Equiv.sum_comp (Equiv.neg Mode) g
  have hneg : ∀ i : Mode, (Equiv.neg Mode) i = -i := fun i => rfl
  simpa only [hneg, neg_neg] using h

theorem epsSplitEqB {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode)
    (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ ρ : ℝ) (f : F.H)
    (hτ : ∀ k : Mode, E.tau (-k) = E.tau k) :
    (∑ k : Mode, (1 / 2 : ℝ) * ((E.tau k - (Work.BoseFixR.farEnv E v μ ρ).tau k)
        * F.qw f (F.nOp k + F.nOp (-k))))
      = (∑ k : Mode, (Work.BoseFixR.epsFar v μ ρ * E.tau k) * F.qw f (F.nOp k))
        - ρ * (Work.BoseFixR.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v
            * (∑ k : Mode, (1 / 2 : ℝ) * F.qw f (F.nOp k + F.nOp (-k))) := by
  -- the diagonal correction `τ_k − τ'_k = ετ_k − ρε^{-1/2}a`
  have hsplit : ∀ k : Mode, E.tau k - (Work.BoseFixR.farEnv E v μ ρ).tau k
      = Work.BoseFixR.epsFar v μ ρ * E.tau k
        - ρ * (Work.BoseFixR.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v := by
    intro k
    rw [Work.BoseFixR.farEnv_tau]
    ring
  -- additivity of the Fock form in the operator
  have hQ : ∀ k : Mode, F.qw f (F.nOp k + F.nOp (-k))
      = F.qw f (F.nOp k) + F.qw f (F.nOp (-k)) := fun k => F.qw_add f _ _
  -- the `k ↦ −k` reindexing identifies the two halves of the `ετ`-reserve
  have hB' : (∑ k : Mode,
        (1 / 2 : ℝ) * ((Work.BoseFixR.epsFar v μ ρ * E.tau k) * F.qw f (F.nOp (-k))))
      = ∑ k : Mode,
        (1 / 2 : ℝ) * ((Work.BoseFixR.epsFar v μ ρ * E.tau k) * F.qw f (F.nOp k)) := by
    have h := Equiv.sum_comp (Equiv.neg Mode)
      (fun k : Mode =>
        (1 / 2 : ℝ) * ((Work.BoseFixR.epsFar v μ ρ * E.tau (-k)) * F.qw f (F.nOp k)))
    have hneg : ∀ i : Mode, (Equiv.neg Mode) i = -i := fun i => rfl
    simp only [hneg, neg_neg] at h
    rw [h]
    exact Finset.sum_congr rfl fun k _ => by rw [hτ k]
  have hA : (∑ k : Mode,
        (1 / 2 : ℝ) * ((Work.BoseFixR.epsFar v μ ρ * E.tau k) * F.qw f (F.nOp k)))
      = (1 / 2 : ℝ)
        * ∑ k : Mode, (Work.BoseFixR.epsFar v μ ρ * E.tau k) * F.qw f (F.nOp k) :=
    (Finset.mul_sum Finset.univ
      (fun k : Mode => (Work.BoseFixR.epsFar v μ ρ * E.tau k) * F.qw f (F.nOp k))
      (1 / 2)).symm
  have hB2 : (∑ k : Mode,
        (1 / 2 : ℝ) * ((Work.BoseFixR.epsFar v μ ρ * E.tau k) * F.qw f (F.nOp (-k))))
      = (1 / 2 : ℝ)
        * ∑ k : Mode, (Work.BoseFixR.epsFar v μ ρ * E.tau k) * F.qw f (F.nOp k) :=
    hB'.trans hA
  -- the `ε^{-1/2}`-diagonal
  have hC : (∑ k : Mode, (1 / 2 : ℝ)
        * ((ρ * (Work.BoseFixR.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v)
            * F.qw f (F.nOp k + F.nOp (-k))))
      = ρ * (Work.BoseFixR.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v
          * (∑ k : Mode, (1 / 2 : ℝ) * F.qw f (F.nOp k + F.nOp (-k))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  -- per-mode expansion of the corrected summand
  have hcongr : ∀ k : Mode, (1 / 2 : ℝ)
        * ((E.tau k - (Work.BoseFixR.farEnv E v μ ρ).tau k) * F.qw f (F.nOp k + F.nOp (-k)))
      = (1 / 2 : ℝ) * ((Work.BoseFixR.epsFar v μ ρ * E.tau k) * F.qw f (F.nOp k))
        + (1 / 2 : ℝ) * ((Work.BoseFixR.epsFar v μ ρ * E.tau k) * F.qw f (F.nOp (-k)))
        - (1 / 2 : ℝ)
          * ((ρ * (Work.BoseFixR.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v)
              * F.qw f (F.nOp k + F.nOp (-k))) := by
    intro k
    rw [hsplit k, hQ k]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hcongr k), Finset.sum_sub_distrib,
    Finset.sum_add_distrib, hA, hB2, hC]
  ring

end Work.BoseFixR.FarResidBaux
