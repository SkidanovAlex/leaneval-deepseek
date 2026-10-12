import ChallengeDeps
import Submission.Work.SecondOrder.Reduce.Decompose
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Work.SecondOrder.Reduce

open Submission.BoseGases
open _root_.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

/-- Finite double sum–integral interchange over the box: the analogue of
`integral_sum_sum` for a summand that already carries the whole integrand. -/
private lemma integral_sum_sum_mul {N : ℕ} {ℓ : ℝ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (F : ι → ι → X N → ℝ)
    (h : ∀ p ∈ s, ∀ q ∈ s, Integrable (F p q) (volume.restrict (abox N ℓ))) :
    (∫ x in abox N ℓ, ∑ p ∈ s, ∑ q ∈ s, F p q x)
      = ∑ p ∈ s, ∑ q ∈ s, ∫ x in abox N ℓ, F p q x := by
  have h1 : (∫ x in abox N ℓ, ∑ p ∈ s, ∑ q ∈ s, F p q x)
      = ∑ p ∈ s, ∫ x in abox N ℓ, ∑ q ∈ s, F p q x :=
    integral_finsetSum (s := s) (f := fun p => fun x => ∑ q ∈ s, F p q x)
      (fun p hp => integrable_finsetSum (s := s) (f := fun q => F p q)
        (fun q hq => h p hp q hq))
  rw [h1]
  exact Finset.sum_congr rfl (fun p hp =>
    integral_finsetSum (s := s) (f := fun q => F p q) (fun q hq => h p hp q hq))

/-- **The `qLHSword` double-sum expansion** (general kernels).  For arbitrary
potentials `w`, `w1`, the potential word `qLHSword` of the pair-excited state
`pairState N ψ wt G` is the weighted double sum over partial matchings of the
configuration integrals of the matching components against the potential
density

`−μ Σᵢ w1Fibre ℓ w1 (xᵢ) + ½ Σ_{r ∈ pairSet N} w (x r.1) (x r.2)`. -/
theorem qLHSword_pairState_eq_doubleSum_gen {N : ℕ} {ℓ μ : ℝ}
    {w w1 : ℝ³ → ℝ³ → ℝ} {psi : ℝ³ → ℝ} {wt : ℕ → ℝ} {G : ℝ³ → ℝ³ → ℝ}
    (hpot : ∀ p ∈ pmatch N, ∀ q ∈ pmatch N,
      IntegrableOn (fun x : X N => pairComp N psi G p x * pairComp N psi G q x *
        (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i))
          + (1 / 2) * (∑ r ∈ pairSet N, w (x r.1) (x r.2))))
        (abox N ℓ)) :
    qLHSword (N := N) ℓ μ w w1 (pairState N psi wt G)
      = ∑ p ∈ pmatch N, ∑ q ∈ pmatch N,
          wt (nPair p) * wt (nPair q)
            * ∫ x in abox N ℓ,
                pairComp N psi G p x * pairComp N psi G q x *
                  (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i))
                    + (1 / 2) * (∑ r ∈ pairSet N, w (x r.1) (x r.2))) := by
  -- the full integrand of one `(p,q)` term
  set F : (Fin N → Fin N) → (Fin N → Fin N) → X N → ℝ :=
    fun p q x => ((wt (nPair p) * pairComp N psi G p x) * (wt (nPair q) * pairComp N psi G q x)) *
      (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i))
        + (1 / 2) * (∑ r ∈ pairSet N, w (x r.1) (x r.2))) with hF
  -- pointwise square expansion
  have hsq : ∀ x : X N,
      (pairState N psi wt G x) ^ 2 *
        (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i))
          + (1 / 2) * (∑ r ∈ pairSet N, w (x r.1) (x r.2)))
      = ∑ p ∈ pmatch N, ∑ q ∈ pmatch N, F p q x := by
    intro x
    rw [pairState_eq_sum_components (x := x)]
    rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.sum_mul]
  -- integrability of every `F p q`
  have hInt : ∀ p ∈ pmatch N, ∀ q ∈ pmatch N,
      Integrable (F p q) (volume.restrict (abox N ℓ)) := by
    intro p hp q hq
    have hbase : Integrable (fun x : X N => pairComp N psi G p x * pairComp N psi G q x *
        (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i))
          + (1 / 2) * (∑ r ∈ pairSet N, w (x r.1) (x r.2))))
        (volume.restrict (abox N ℓ)) := hpot p hp q hq
    refine (hbase.const_mul (wt (nPair p) * wt (nPair q))).congr
      (Eventually.of_forall (fun x => ?_))
    simp only [hF]
    ring
  unfold qLHSword
  have hfun : (fun x : X N => (pairState N psi wt G x) ^ 2 *
        (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i))
          + (1 / 2) * (∑ r ∈ pairSet N, w (x r.1) (x r.2))))
      = fun x : X N => ∑ p ∈ pmatch N, ∑ q ∈ pmatch N, F p q x :=
    funext hsq
  rw [hfun]
  rw [integral_sum_sum_mul (pmatch N) F hInt]
  refine Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun q hq => ?_))
  rw [show (fun x : X N => F p q x)
      = fun x : X N => (wt (nPair p) * wt (nPair q)) *
          (pairComp N psi G p x * pairComp N psi G q x *
            (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i))
              + (1 / 2) * (∑ r ∈ pairSet N, w (x r.1) (x r.2)))) by
      funext x; simp only [hF]; ring]
  rw [integral_const_mul]

theorem qLHSword_pairState_eq_doubleSum {N : ℕ} {ℓ μ : ℝ} {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, _root_.BoseGases.IsRadial w ∧
      _root_.BoseGases.IsScatteringSolution w v)
    {psi : EuclideanSpace ℝ (Fin 3) → ℝ} {wt : ℕ → ℝ}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hpot : ∀ p ∈ Work.SecondOrder.pmatch N, ∀ q ∈ Work.SecondOrder.pmatch N,
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.SecondOrder.pairComp N psi G p x * Work.SecondOrder.pairComp N psi G q x *
          (- μ * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ
              (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h)) (x i))
            + (1 / 2) * (∑ r ∈ Submission.BoseGases.pairSet N,
                Submission.BoseGases.wPairC ℓ v (x r.1) (x r.2))))
        (Submission.BoseGases.abox N ℓ)) :
    Submission.BoseGases.qLHSword (N := N) ℓ μ (Submission.BoseGases.wPairC ℓ v)
        (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h))
        (Work.SecondOrder.pairState N psi wt G)
      = ∑ p ∈ Work.SecondOrder.pmatch N, ∑ q ∈ Work.SecondOrder.pmatch N,
          wt (Work.SecondOrder.nPair p) * wt (Work.SecondOrder.nPair q)
            * ∫ x in Submission.BoseGases.abox N ℓ,
                Work.SecondOrder.pairComp N psi G p x * Work.SecondOrder.pairComp N psi G q x *
                  (- μ * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ
                      (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h)) (x i))
                    + (1 / 2) * (∑ r ∈ Submission.BoseGases.pairSet N,
                        Submission.BoseGases.wPairC ℓ v (x r.1) (x r.2))) := by
  exact qLHSword_pairState_eq_doubleSum_gen (w := wPairC ℓ v)
    (w1 := wPairC ℓ (g0 v h)) (psi := psi) (wt := wt) (G := G) hpot

end Work.SecondOrder.Reduce
