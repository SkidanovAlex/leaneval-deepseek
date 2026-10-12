import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.exclFunOpAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.exclFunOpPropsB1` — the operator algebra of `exclFunOp`

`exclFunOp volA A i g Ψ = Σ_S g (|S| − 1_{i∈S}) · (n0ProjOp volA A S Ψ)` is the slot-`i`-excluded
functional calculus `g(n₀ − P_i)` (`n0ExclFunOp`).  This file proves the four algebraic properties
the sharp completion of squares needs:

1. **fibre commutation**: `fib (· i)` survives the operator, `exclFunOp g (fib_i · Ψ) = fib (· i) ·
   exclFunOp g Ψ`.  Note that the slot-`i` projection itself does *not* commute with the fibre
   weight: the proof regroups the defining sum into the pairs `{T, T ∪ {i}}` (`powersetErasePairSum`)
   and observes that the two halves of a pair cancel the slot-`i` step
   (`n0IterFibPair`);
2. **multiplicativity**: `exclFunOp g ∘ exclFunOp h = exclFunOp (g · h)` (the `n0ProjOp` are
   orthogonal idempotents, `n0ProjOpEigenOrth`, and the iteration is linear over finite sums,
   `n0IterFinsetSum`);
3. **self-adjointness**: `⟨exclFunOp g Φ, Ψ⟩ = ⟨Φ, exclFunOp g Ψ⟩` on `L²(abox N ℓ)`
   (`n0IterSelfAdj`);
4. **the eigen-property on the idempotents**: `exclFunOp g (n0ProjOp S Ψ) = g (|S| − 1_{i∈S}) ·
   n0ProjOp S Ψ`, i.e. `n0ProjOp S` projects onto the eigenspace of `n₀ − P_i` for the eigenvalue
   `|S| − 1_{i∈S}`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000

theorem exclFunOpPropsB1 {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (i : Fin N) :
    (∀ (g : ℝ → ℝ) {fib : EuclideanSpace ℝ (Fin 3) → ℝ} (hfibm : Measurable fib) {Cf : ℝ}
        (hfibb : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ Cf)
        {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : Work.BoseFixB1S.GoodState ℓ Ψ),
        (fun x => Work.BoseFixB1S.exclFunOp volA A i g (fun y => fib (y i) * Ψ y) x)
          =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)]
          fun x => fib (x i) * Work.BoseFixB1S.exclFunOp volA A i g Ψ x)
    ∧ (∀ (g h : ℝ → ℝ) {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : Work.BoseFixB1S.GoodState ℓ Ψ),
        (fun x => Work.BoseFixB1S.exclFunOp volA A i g (Work.BoseFixB1S.exclFunOp volA A i h Ψ) x)
          =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)]
          fun x => Work.BoseFixB1S.exclFunOp volA A i (fun r => g r * h r) Ψ x)
    ∧ (∀ (g : ℝ → ℝ) {Φ Ψ : Submission.BoseGases.X N → ℝ}
        (hΦ : Work.BoseFixB1S.GoodState ℓ Φ) (hΨ : Work.BoseFixB1S.GoodState ℓ Ψ),
        ∫ x in Submission.BoseGases.abox N ℓ, Work.BoseFixB1S.exclFunOp volA A i g Φ x * Ψ x
          = ∫ x in Submission.BoseGases.abox N ℓ, Φ x * Work.BoseFixB1S.exclFunOp volA A i g Ψ x)
    ∧ (∀ (g : ℝ → ℝ) (S : Finset (Fin N)) {Ψ : Submission.BoseGases.X N → ℝ}
        (hΨ : Work.BoseFixB1S.GoodState ℓ Ψ) (x : Submission.BoseGases.X N)
        (hx : x ∈ Submission.BoseGases.abox N ℓ),
        Work.BoseFixB1S.exclFunOp volA A i g (Work.BoseFixB1S.n0ProjOp volA A S Ψ) x
          = g ((S.card : ℝ) - (if i ∈ S then 1 else 0)) *
              ((Work.BoseFixB1S.n0ProjOp volA A S) Ψ x)) := by
  classical
  have hnd : (List.ofFn (fun j : Fin N => j)).Nodup := List.nodup_ofFn.mpr (fun _ _ h => h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (1) the fibre weight `fib (· i)` passes through the operator
    intro g fib hfibm Cf hfibb Ψ hΨ
    filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
    have hpair : ∀ T ∈ (Finset.univ.erase i).powerset,
        (Work.BoseFixB1S.n0ProjOp volA A T (fun y => fib (y i) * Ψ y) x
            + Work.BoseFixB1S.n0ProjOp volA A (insert i T) (fun y => fib (y i) * Ψ y) x)
          = fib (x i) * (Work.BoseFixB1S.n0ProjOp volA A T Ψ x
              + Work.BoseFixB1S.n0ProjOp volA A (insert i T) Ψ x) := by
      intro T hT
      have hiT : i ∉ T := fun h => Finset.notMem_erase i _ ((Finset.mem_powerset.mp hT) h)
      have hagr : ∀ j ∈ List.ofFn (fun j : Fin N => j), j ≠ i →
          decide (j ∈ T) = decide (j ∈ insert i T) := by
        intro j _ hji
        refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => ?_⟩
        · rw [Finset.mem_insert]; exact Or.inr h
        · rcases Finset.mem_insert.mp h with h' | h'
          · exact absurd h' hji
          · exact h'
      have h0 : (fun j : Fin N => decide (j ∈ T)) i = false := by simp [hiT]
      have h1 : (fun j : Fin N => decide (j ∈ insert i T)) i = true := by simp
      exact n0IterFibPair hℓ hvol hA hvolA hAc hfibm hfibb i h0 h1
        (List.ofFn (fun j : Fin N => j)) hnd hagr Ψ hΨ x hx
    calc Work.BoseFixB1S.exclFunOp volA A i g (fun y => fib (y i) * Ψ y) x
        = ∑ S : Finset (Fin N),
            g ((S.card : ℝ) - (if i ∈ S then 1 else 0))
              * Work.BoseFixB1S.n0ProjOp volA A S (fun y => fib (y i) * Ψ y) x := rfl
      _ = ∑ T ∈ (Finset.univ.erase i).powerset, g ((T.card : ℝ))
            * (Work.BoseFixB1S.n0ProjOp volA A T (fun y => fib (y i) * Ψ y) x
              + Work.BoseFixB1S.n0ProjOp volA A (insert i T) (fun y => fib (y i) * Ψ y) x) :=
          powersetErasePairSum i g
            (fun S => Work.BoseFixB1S.n0ProjOp volA A S (fun y => fib (y i) * Ψ y) x)
      _ = ∑ T ∈ (Finset.univ.erase i).powerset, g ((T.card : ℝ))
            * (fib (x i) * (Work.BoseFixB1S.n0ProjOp volA A T Ψ x
              + Work.BoseFixB1S.n0ProjOp volA A (insert i T) Ψ x)) := by
          apply Finset.sum_congr rfl
          intro T hT
          rw [hpair T hT]
      _ = fib (x i) * ∑ T ∈ (Finset.univ.erase i).powerset, g ((T.card : ℝ))
            * (Work.BoseFixB1S.n0ProjOp volA A T Ψ x
              + Work.BoseFixB1S.n0ProjOp volA A (insert i T) Ψ x) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro T _
          ring
      _ = fib (x i) * Work.BoseFixB1S.exclFunOp volA A i g Ψ x := by
          rw [show Work.BoseFixB1S.exclFunOp volA A i g Ψ x
              = ∑ S : Finset (Fin N),
                  g ((S.card : ℝ) - (if i ∈ S then 1 else 0))
                    * Work.BoseFixB1S.n0ProjOp volA A S Ψ x from rfl,
            ← powersetErasePairSum i g (fun S => Work.BoseFixB1S.n0ProjOp volA A S Ψ x)]
  · -- (2) multiplicativity of the functional calculus
    intro g h Ψ hΨ
    filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
    have hS : ∀ S : Finset (Fin N), GoodState ℓ (Work.BoseFixB1S.n0ProjOp volA A S Ψ) :=
      fun S => goodState_n0Iter hℓ hvol hA hvolA hAc (fun j => decide (j ∈ S))
        (List.ofFn (fun j : Fin N => j)) hΨ
    have hstep : ∀ T : Finset (Fin N),
        Work.BoseFixB1S.n0ProjOp volA A T (Work.BoseFixB1S.exclFunOp volA A i h Ψ) x
          = h ((T.card : ℝ) - (if i ∈ T then 1 else 0))
              * Work.BoseFixB1S.n0ProjOp volA A T Ψ x := by
      intro T
      have hlin := n0IterFinsetSum hℓ hvol hA hvolA hAc (Finset.univ : Finset (Finset (Fin N)))
        (fun S => h ((S.card : ℝ) - (if i ∈ S then 1 else 0))) (fun j => decide (j ∈ T))
        (List.ofFn (fun j : Fin N => j)) (fun S => Work.BoseFixB1S.n0ProjOp volA A S Ψ)
        (fun S _ => hS S) x hx
      calc Work.BoseFixB1S.n0ProjOp volA A T (Work.BoseFixB1S.exclFunOp volA A i h Ψ) x
          = n0Iter volA A (fun j => decide (j ∈ T)) (List.ofFn (fun j : Fin N => j))
              (fun y => ∑ S : Finset (Fin N),
                h ((S.card : ℝ) - (if i ∈ S then 1 else 0))
                  * Work.BoseFixB1S.n0ProjOp volA A S Ψ y) x := rfl
        _ = ∑ S : Finset (Fin N), h ((S.card : ℝ) - (if i ∈ S then 1 else 0))
              * n0Iter volA A (fun j => decide (j ∈ T)) (List.ofFn (fun j : Fin N => j))
                  (Work.BoseFixB1S.n0ProjOp volA A S Ψ) x := hlin
        _ = ∑ S : Finset (Fin N), h ((S.card : ℝ) - (if i ∈ S then 1 else 0))
              * (if T = S then Work.BoseFixB1S.n0ProjOp volA A S Ψ x else 0) := by
            apply Finset.sum_congr rfl
            intro S _
            rw [show n0Iter volA A (fun j => decide (j ∈ T)) (List.ofFn (fun j : Fin N => j))
                  (Work.BoseFixB1S.n0ProjOp volA A S Ψ) x
                = Work.BoseFixB1S.n0ProjOp volA A T (Work.BoseFixB1S.n0ProjOp volA A S Ψ) x
                from rfl,
              n0ProjOpEigenOrth hℓ hvol hA hvolA hAc hΨ S T x hx]
        _ = h ((T.card : ℝ) - (if i ∈ T then 1 else 0))
              * Work.BoseFixB1S.n0ProjOp volA A T Ψ x := by
            rw [Finset.sum_eq_single T]
            · rw [if_pos rfl]
            · intro S _ hST
              rw [if_neg (Ne.symm hST), mul_zero]
            · intro hT
              exact absurd (Finset.mem_univ T) hT
    calc Work.BoseFixB1S.exclFunOp volA A i g (Work.BoseFixB1S.exclFunOp volA A i h Ψ) x
        = ∑ T : Finset (Fin N), g ((T.card : ℝ) - (if i ∈ T then 1 else 0))
            * Work.BoseFixB1S.n0ProjOp volA A T (Work.BoseFixB1S.exclFunOp volA A i h Ψ) x := rfl
      _ = ∑ T : Finset (Fin N), g ((T.card : ℝ) - (if i ∈ T then 1 else 0))
            * (h ((T.card : ℝ) - (if i ∈ T then 1 else 0))
                * Work.BoseFixB1S.n0ProjOp volA A T Ψ x) := by
          apply Finset.sum_congr rfl
          intro T _
          rw [hstep T]
      _ = ∑ T : Finset (Fin N),
            (g ((T.card : ℝ) - (if i ∈ T then 1 else 0))
              * h ((T.card : ℝ) - (if i ∈ T then 1 else 0)))
              * Work.BoseFixB1S.n0ProjOp volA A T Ψ x := by
          apply Finset.sum_congr rfl
          intro T _
          ring
      _ = Work.BoseFixB1S.exclFunOp volA A i (fun r => g r * h r) Ψ x := rfl
  · -- (3) self-adjointness on `L²(abox N ℓ)`
    intro g Φ Ψ hΦ hΨ
    have hG : ∀ S : Finset (Fin N), GoodState ℓ (Work.BoseFixB1S.n0ProjOp volA A S Ψ) :=
      fun S => goodState_n0Iter hℓ hvol hA hvolA hAc (fun j => decide (j ∈ S))
        (List.ofFn (fun j : Fin N => j)) hΨ
    have hP : ∀ S : Finset (Fin N), GoodState ℓ (Work.BoseFixB1S.n0ProjOp volA A S Φ) :=
      fun S => goodState_n0Iter hℓ hvol hA hvolA hAc (fun j => decide (j ∈ S))
        (List.ofFn (fun j : Fin N => j)) hΦ
    have hI : ∀ S : Finset (Fin N),
        IntegrableOn (fun x => Work.BoseFixB1S.n0ProjOp volA A S Φ x * Ψ x)
          (abox N ℓ) volume :=
      fun S => integrableOn_mul_goodState hℓ (hP S) hΨ
    have hJ : ∀ S : Finset (Fin N),
        IntegrableOn (fun x => Φ x * Work.BoseFixB1S.n0ProjOp volA A S Ψ x)
          (abox N ℓ) volume :=
      fun S => integrableOn_mul_goodState hℓ hΦ (hG S)
    have hL1 : (∫ x in abox N ℓ, Work.BoseFixB1S.exclFunOp volA A i g Φ x * Ψ x)
        = ∑ S : Finset (Fin N), g ((S.card : ℝ) - (if i ∈ S then 1 else 0))
            * ∫ x in abox N ℓ, Work.BoseFixB1S.n0ProjOp volA A S Φ x * Ψ x := by
      rw [show (∫ x in abox N ℓ, Work.BoseFixB1S.exclFunOp volA A i g Φ x * Ψ x)
          = ∫ x in abox N ℓ, ∑ S : Finset (Fin N),
              g ((S.card : ℝ) - (if i ∈ S then 1 else 0))
                * (Work.BoseFixB1S.n0ProjOp volA A S Φ x * Ψ x) from by
        apply setIntegral_congr_fun (abox_measurable N ℓ)
        intro x _
        show (∑ S : Finset (Fin N), g ((S.card : ℝ) - (if i ∈ S then 1 else 0))
              * Work.BoseFixB1S.n0ProjOp volA A S Φ x) * Ψ x
            = ∑ S : Finset (Fin N), g ((S.card : ℝ) - (if i ∈ S then 1 else 0))
              * (Work.BoseFixB1S.n0ProjOp volA A S Φ x * Ψ x)
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro S _
        ring]
      rw [MeasureTheory.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro S _
        rw [MeasureTheory.integral_const_mul]
      · intro S _
        exact (hI S).const_mul _
    have hL2 : (∑ S : Finset (Fin N), g ((S.card : ℝ) - (if i ∈ S then 1 else 0))
            * ∫ x in abox N ℓ, Work.BoseFixB1S.n0ProjOp volA A S Φ x * Ψ x)
        = ∑ S : Finset (Fin N), g ((S.card : ℝ) - (if i ∈ S then 1 else 0))
            * ∫ x in abox N ℓ, Φ x * Work.BoseFixB1S.n0ProjOp volA A S Ψ x := by
      apply Finset.sum_congr rfl
      intro S _
      rw [show (∫ x in abox N ℓ, Work.BoseFixB1S.n0ProjOp volA A S Φ x * Ψ x)
            = ∫ x in abox N ℓ, n0Iter volA A (fun j => decide (j ∈ S))
                (List.ofFn (fun j : Fin N => j)) Φ x * Ψ x from rfl,
          n0IterSelfAdj hℓ hvol hA hvolA hAc (fun j => decide (j ∈ S))
            (List.ofFn (fun j : Fin N => j)) hnd Φ Ψ hΦ hΨ,
          show (∫ x in abox N ℓ, Φ x * n0Iter volA A (fun j => decide (j ∈ S))
                (List.ofFn (fun j : Fin N => j)) Ψ x)
            = ∫ x in abox N ℓ, Φ x * Work.BoseFixB1S.n0ProjOp volA A S Ψ x from rfl]
    have hL3 : (∑ S : Finset (Fin N), g ((S.card : ℝ) - (if i ∈ S then 1 else 0))
            * ∫ x in abox N ℓ, Φ x * Work.BoseFixB1S.n0ProjOp volA A S Ψ x)
        = ∫ x in abox N ℓ, Φ x * Work.BoseFixB1S.exclFunOp volA A i g Ψ x := by
      rw [show (∫ x in abox N ℓ, Φ x * Work.BoseFixB1S.exclFunOp volA A i g Ψ x)
          = ∫ x in abox N ℓ, ∑ S : Finset (Fin N),
              g ((S.card : ℝ) - (if i ∈ S then 1 else 0))
                * (Φ x * Work.BoseFixB1S.n0ProjOp volA A S Ψ x) from by
        apply setIntegral_congr_fun (abox_measurable N ℓ)
        intro x _
        show Φ x * (∑ S : Finset (Fin N), g ((S.card : ℝ) - (if i ∈ S then 1 else 0))
              * Work.BoseFixB1S.n0ProjOp volA A S Ψ x)
            = ∑ S : Finset (Fin N), g ((S.card : ℝ) - (if i ∈ S then 1 else 0))
              * (Φ x * Work.BoseFixB1S.n0ProjOp volA A S Ψ x)
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S _
        ring]
      rw [MeasureTheory.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro S _
        rw [MeasureTheory.integral_const_mul]
      · intro S _
        exact (hJ S).const_mul _
    rw [hL1, hL2, hL3]
  · -- (4) the eigen-property on the subset idempotents
    intro g S Ψ hΨ x hx
    calc Work.BoseFixB1S.exclFunOp volA A i g (Work.BoseFixB1S.n0ProjOp volA A S Ψ) x
        = ∑ T : Finset (Fin N), g ((T.card : ℝ) - (if i ∈ T then 1 else 0))
            * Work.BoseFixB1S.n0ProjOp volA A T (Work.BoseFixB1S.n0ProjOp volA A S Ψ) x := rfl
      _ = ∑ T : Finset (Fin N), g ((T.card : ℝ) - (if i ∈ T then 1 else 0))
            * (if T = S then Work.BoseFixB1S.n0ProjOp volA A S Ψ x else 0) := by
          apply Finset.sum_congr rfl
          intro T _
          rw [n0ProjOpEigenOrth hℓ hvol hA hvolA hAc hΨ S T x hx]
      _ = g ((S.card : ℝ) - (if i ∈ S then 1 else 0))
            * ((Work.BoseFixB1S.n0ProjOp volA A S) Ψ x) := by
          rw [Finset.sum_eq_single S]
          · rw [if_pos rfl]
          · intro T _ hTS
            rw [if_neg hTS, mul_zero]
          · intro hS
            exact absurd (Finset.mem_univ S) hS

end Work.BoseFixB1S
