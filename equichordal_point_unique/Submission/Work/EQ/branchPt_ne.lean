import Mathlib
import Submission.Work.EQ.bp_aux
import Submission.Work.EQ.backward_puiseux
import Submission.Work.EQ.paramLambda_ne_neg

namespace Work.EQ

open Filter _root_.Topology
open Complex Metric

noncomputable section

/-! ### Auxiliary facts for the comparison of two branches -/

/-- `O₁` is the zero of the radicand `ρ'`. -/
private lemma rhoPrimeSq_O1_eq_zero (a : ℝ) : rhoPrimeSq a (O1 a) = 0 := by
  simp [rhoPrimeSq, O1]

/-- `ρ'(Q)² ≠ 0` forces `Q ≠ O₁`. -/
private lemma ne_O1_of_rhoPrimeSq_ne_zero {a : ℝ} {Q : ℂ × ℂ} (h : rhoPrimeSq a Q ≠ 0) :
    Q ≠ O1 a := by
  intro hQ
  exact h (by rw [hQ]; exact rhoPrimeSq_O1_eq_zero a)

/-- For *different* signs, `sgn` flips. -/
private lemma sgn_eq_neg_sgn {b b' : Bool} (h : b ≠ b') : sgn b' = - sgn b := by
  cases b <;> cases b' <;> simp_all [sgn]

/-- **Two F3 branches with different sign sequences differ pointwise.**

`Work.EQ.branchPt a c u₀ R σ t j` is the `j`-th point of the backward `EqRelC`-chain of length
`N` ending at `c (u₀ + t ^ (2^N))` with sign sequence `σ`.  At the first level `m₀` where `σ` and
`σ'` disagree, the level-`m₀` functions agree (`Work.EQ.Xf` at level `m` depends only on
`σ 0 … σ (m-1)`) and the two level-`(m₀+1)` values are `paramΛ a (Y (w²)) (± lam w)`, which differ
because `paramΛ a Q lam - paramΛ a Q (-lam) = (2/lam) • (Q - O₁) ≠ 0` whenever `lam ≠ 0` and
`Q ≠ O₁` (both hold on the punctured disc by `Work.EQ.StepOut.hlam_ne` and
`lam² = rhoPrimeSq a Q ≠ 0`).

Note `j : Fin (N+1)` is an explicit last argument, so the conclusion compares the two partial
applications `branchPt a c u₀ R σ t` and `branchPt a c u₀ R σ' t` as functions
`Fin (N+1) → ℂ × ℂ` — this is the function-level statement, and it is the shape
`Work.Topology.eventually_index_const` needs (the separating level depends on the pair).

Hence `σ ≠ σ'` forces `branchPt a c u₀ R σ t ≠ branchPt a c u₀ R σ' t` for every `t` in the
punctured disc, and in particular the two branches are separated near `0`. -/
theorem branchPt_ne {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ} (hR : 0 < R)
    (hc : AnalyticOnNhd ℂ c (Metric.ball u₀ R)) {σ σ' : Fin N → Bool}
    (hσ : Work.EQ.Adm a c u₀ R σ) (hσ' : Work.EQ.Adm a c u₀ R σ') (hne : σ ≠ σ') :
    ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < Work.EQ.rhoFin' a c u₀ R N →
      Work.EQ.branchPt a c u₀ R σ t ≠ Work.EQ.branchPt a c u₀ R σ' t := by
  classical
  -- the first level at which the two extended sign sequences disagree
  have hexk : ∃ k : Fin N, σ k ≠ σ' k := by
    by_contra h
    exact hne (funext (fun k => by by_contra hh; exact h ⟨k, hh⟩))
  obtain ⟨k, hk⟩ := hexk
  have hk' : sigmaExtN σ (k : ℕ) ≠ sigmaExtN σ' (k : ℕ) := by
    rw [sigmaExtN_apply σ (k : ℕ) k.isLt, sigmaExtN_apply σ' (k : ℕ) k.isLt]
    exact hk
  have hex : ∃ m : ℕ, m < N ∧ sigmaExtN σ m ≠ sigmaExtN σ' m := ⟨k, k.isLt, hk'⟩
  let m₀ : ℕ := Nat.find hex
  have hm₀N : m₀ < N := (Nat.find_spec hex).1
  have hne₀ : sigmaExtN σ m₀ ≠ sigmaExtN σ' m₀ := (Nat.find_spec hex).2
  have hagree : ∀ i < m₀, sigmaExtN σ i = sigmaExtN σ' i := by
    intro i hi
    by_contra h
    exact Nat.find_min hex hi ⟨lt_trans hi hm₀N, h⟩
  -- the two branches agree at level `m₀`
  have hXfeq : Xf a c u₀ R (sigmaExtN σ) m₀ = Xf a c u₀ R (sigmaExtN σ') m₀ :=
    Xf_congr (fun i hi => hagree i hi)
  have hLfeq : Lf a c u₀ R (sigmaExtN σ) m₀ = Lf a c u₀ R (sigmaExtN σ') m₀ :=
    Lf_congr (fun i hi => hagree i hi)
  have hG : Good a c u₀ R (sigmaExtN σ) (m₀ + 1) :=
    hasGood_of_adm hσ (m₀ + 1) (by omega)
  have hex1 : ∃ S : StepOut a (Xf a c u₀ R (sigmaExtN σ) m₀)
      (seqRho a c u₀ R (sigmaExtN σ) m₀), True :=
    stepOut_exists_of_good
      (XProps_of_good hR hc (sigmaExtN σ) m₀ (hasGood_of_adm hσ m₀ (le_of_lt hm₀N)))
      (hσ.1 m₀ hm₀N)
  have hex2 : ∃ S : StepOut a (Xf a c u₀ R (sigmaExtN σ') m₀)
      (seqRho a c u₀ R (sigmaExtN σ') m₀), True :=
    stepOut_exists_of_good
      (XProps_of_good hR hc (sigmaExtN σ') m₀ (hasGood_of_adm hσ' m₀ (le_of_lt hm₀N)))
      (hσ'.1 m₀ hm₀N)
  have hxsucc1 := Xf_succ (σ := sigmaExtN σ) (m := m₀) hex1
  have hxsucc2 := Xf_succ (σ := sigmaExtN σ') (m := m₀) hex2
  intro t ht0 htρ hfun
  -- separating index and evaluation point
  let j : Fin (N + 1) := ⟨N - 1 - m₀, by omega⟩
  let j₂ : Fin (N + 1) := ⟨N - m₀, by omega⟩
  let w : ℂ := t ^ (2 ^ (N - 1 - m₀))
  have hdiff : branchPt a c u₀ R σ t j = branchPt a c u₀ R σ' t j := congrFun hfun j
  have htne : t ≠ 0 := by intro h; rw [h] at ht0; simp at ht0
  have hw0 : 0 < ‖w‖ := by
    simp only [w, norm_pow]
    exact pow_pos (norm_pos_iff.mpr htne) _
  have hwraw : ‖w‖ < rawRho a c u₀ R (sigmaExtN σ) m₀ := by
    have h := tmem_rawRho hR hc htρ (⟨m₀, hm₀N⟩ : Fin N) hG
    simpa only [w, Fin.val_mk] using h
  have hLfne : Lf a c u₀ R (sigmaExtN σ) m₀ w ≠ 0 := Lf_ne hex1 w hw0 hwraw
  have hlamne : sgn (sigmaExtN σ m₀) * Lf a c u₀ R (sigmaExtN σ) m₀ w ≠ 0 :=
    mul_ne_zero (sgn_ne_zero _) hLfne
  have hrho : rhoPrimeSq a (Xf a c u₀ R (sigmaExtN σ) m₀ (w ^ 2)) ≠ 0 := by
    rw [← Lf_sq hex1 w hw0 hwraw]
    exact pow_ne_zero 2 hLfne
  have hQne : Xf a c u₀ R (sigmaExtN σ) m₀ (w ^ 2) ≠ O1 a :=
    ne_O1_of_rhoPrimeSq_ne_zero hrho
  -- `w ^ 2 = t ^ (2 ^ (N - m₀))`
  have hw2 : w ^ 2 = t ^ (2 ^ (N - m₀)) := by
    have h2 : 2 ^ (N - 1 - m₀) * 2 = 2 ^ (N - m₀) := by
      rw [← pow_succ]
      congr 1
      omega
    simp only [w, ← pow_mul, h2]
  -- the two evaluations, written over the common level `m₀`
  have hlev : N - (j : ℕ) = m₀ + 1 := by
    simp only [j]
    omega
  have hj2v : (j₂ : ℕ) = N - m₀ := by simp only [j₂]
  have key1 : branchPt a c u₀ R σ t j = Xf a c u₀ R (sigmaExtN σ) (m₀ + 1) w := by
    rw [branchPt]
    simp only [j, w, hlev]
  have key1' : branchPt a c u₀ R σ' t j = Xf a c u₀ R (sigmaExtN σ') (m₀ + 1) w := by
    rw [branchPt]
    simp only [j, w, hlev]
  have key2 : branchPt a c u₀ R σ t j₂ = Xf a c u₀ R (sigmaExtN σ) m₀ (w ^ 2) := by
    have hj2 : N - (j₂ : ℕ) = m₀ := by omega
    have hj3 : 2 ^ (j₂ : ℕ) = 2 ^ (N - m₀) := by rw [hj2v]
    rw [hw2, branchPt]
    simp only [hj2, hj3]
  have hQne' : branchPt a c u₀ R σ t j₂ ≠ O1 a :=
    fun h => hQne (key2.symm.trans h)
  have hval1 : branchPt a c u₀ R σ t j
      = paramΛ a (branchPt a c u₀ R σ t j₂)
          (sgn (sigmaExtN σ m₀) * Lf a c u₀ R (sigmaExtN σ) m₀ w) := by
    rw [key1, congrFun hxsucc1 w, ← key2]
  have hsign : sgn (sigmaExtN σ' m₀) * Lf a c u₀ R (sigmaExtN σ') m₀ w
      = - (sgn (sigmaExtN σ m₀) * Lf a c u₀ R (sigmaExtN σ) m₀ w) := by
    rw [sgn_eq_neg_sgn hne₀, ← hLfeq, neg_mul]
  have hval2 : branchPt a c u₀ R σ' t j
      = paramΛ a (branchPt a c u₀ R σ t j₂)
          (- (sgn (sigmaExtN σ m₀) * Lf a c u₀ R (sigmaExtN σ) m₀ w)) := by
    rw [key1', congrFun hxsucc2 w, ← hXfeq, hsign, ← key2]
  have hparam := paramLambda_ne_neg (a := a)
    (Q := branchPt a c u₀ R σ t j₂) hlamne hQne'
  exact hparam (by rw [hval1, hval2] at hdiff; exact hdiff)

end

end Work.EQ
