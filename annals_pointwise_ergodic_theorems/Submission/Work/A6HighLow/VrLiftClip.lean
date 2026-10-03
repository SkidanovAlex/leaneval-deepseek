import Mathlib
import Submission.Work.KMTPlan.A6.MdlAdelicProb
import Submission.Work.KMTAreas.A7.variationalNorm_clip_le
import Submission.Work.KMTAreas.A7Hi2.supDeepLe
import Submission.Port.Aesm

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.A6HighLow

open MeasureTheory
open scoped ENNReal BigOperators

/-! ## Clipping a packet family at an upward-closed set of indices

`Work.KMTPlan.A6.VrLiftDataP R Q u` is

`(⨆ n, eLpNorm (u n) 2 (zmodProb Q)) + (⨆ chains, (∑_i (eLpNorm (u (k i.succ) - u (k i.castSucc)) 2 (zmodProb Q))^R)^(1/R))`.

For an *upward closed* `γ : ℕ → Prop` (i.e. `n ≤ m → γ n → γ m`) we show that replacing `u` by
`w = u · 1_γ` (the clip) costs at most a factor `2`:

`VrLiftDataP R Q w ≤ VrLiftDataP R Q u + VrLiftDataP R Q u`.

The proof splits the two summands of `VrLiftDataP`:

* the **sup part** is pointwise (`w n` is either `u n` or `0`), so it only decreases;
* for the **chain part**, fix a monotone chain `k : Fin (J+1) → ℕ`.  An increment
  `w (k i.succ) - w (k i.castSucc)` can differ from `u (k i.succ) - u (k i.castSucc)` only when the
  chain *crosses* the boundary of `γ`, i.e. `¬γ (k i.castSucc) ∧ γ (k i.succ)`.  Upward closedness
  makes the crossing set a subsingleton (at most one index), and at a crossing the increment is
  exactly `u (k i.succ)`, bounded by the sup part.  The `ℓ^R` triangle inequality (Minkowski in
  `ℝ≥0∞`, two terms) then gives the chain inequality. -/

/-- A sum of a constant over a finset of cardinality at most one is at most the constant. -/
private lemma sum_const_le_of_card_le_one {α : Type*} (s : Finset α) (x : ℝ≥0∞)
    (h : s.card ≤ 1) : (∑ _ ∈ s, x) ≤ x := by
  rw [Finset.sum_const]
  obtain h0 | h1 := Nat.le_one_iff_eq_zero_or_eq_one.mp h
  · rw [h0]; simp
  · rw [h1]; simp

/-- `(x ^ R) ^ (1 / R) = x` for `R ≥ 1`. -/
private lemma rpow_rpow_inv {R : ℝ} (hR : 1 ≤ R) (x : ℝ≥0∞) :
    (x ^ R) ^ (1 / R) = x := by
  have hne : R ≠ 0 := by linarith
  rw [← ENNReal.rpow_mul, mul_one_div_cancel hne, ENNReal.rpow_one]

/-- **The sup part of `VrLiftDataP` only decreases under a clip.** -/
private lemma sup_le_of_clip {Q : ℕ} [NeZero Q] (γ : ℕ → Prop) [DecidablePred γ]
    (u w : ℕ → ZMod Q → ℂ) (hw : ∀ n θ, w n θ = if γ n then u n θ else 0) :
    (⨆ n : ℕ, eLpNorm (w n) 2 (Work.KMTPlan.A6.zmodProb Q))
      ≤ (⨆ n : ℕ, eLpNorm (u n) 2 (Work.KMTPlan.A6.zmodProb Q)) := by
  refine iSup_le fun n => ?_
  refine (eLpNorm_mono_enorm (hf := by pw_aesm) ?_).trans
    (le_iSup (fun n : ℕ => eLpNorm (u n) 2 (Work.KMTPlan.A6.zmodProb Q)) n)
  intro θ
  rw [hw n θ]
  by_cases h : γ n
  · simp [h]
  · simp [h]

/-- **The chain part of `VrLiftDataP` under a clip**: clipping costs the sup part at most. -/
private lemma chain_le_of_clip {Q : ℕ} [NeZero Q] (R : ℝ) (hR : 1 ≤ R)
    (γ : ℕ → Prop) [DecidablePred γ]
    (hγ : ∀ ⦃n m : ℕ⦄, n ≤ m → γ n → γ m)
    (u w : ℕ → ZMod Q → ℂ) (hw : ∀ n θ, w n θ = if γ n then u n θ else 0) :
    (⨆ (J : ℕ) (k : Fin (J + 1) → ℕ) (_ : Monotone k),
        ENNReal.rpow (Finset.univ.sum fun i : Fin J =>
          ENNReal.rpow
            (eLpNorm (w (k i.succ) - w (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q)) R)
          (1 / R))
      ≤ (⨆ (J : ℕ) (k : Fin (J + 1) → ℕ) (_ : Monotone k),
          ENNReal.rpow (Finset.univ.sum fun i : Fin J =>
            ENNReal.rpow
              (eLpNorm (u (k i.succ) - u (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q)) R)
            (1 / R))
        + (⨆ n : ℕ, eLpNorm (u n) 2 (Work.KMTPlan.A6.zmodProb Q)) := by
  classical
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  have hnn : (0 : ℝ) ≤ 1 / R := by positivity
  have hle1 : (1 : ℝ) / R ≤ 1 := by
    rw [div_le_one hRpos]; exact hR
  refine iSup_le fun J => iSup_le fun k => iSup_le fun hk => ?_
  set A : ℝ≥0∞ := ⨆ n : ℕ, eLpNorm (u n) 2 (Work.KMTPlan.A6.zmodProb Q) with hA
  set B : ℝ≥0∞ := (⨆ (J : ℕ) (k : Fin (J + 1) → ℕ) (_ : Monotone k),
      ENNReal.rpow (Finset.univ.sum fun i : Fin J =>
        ENNReal.rpow
          (eLpNorm (u (k i.succ) - u (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q)) R)
        (1 / R)) with hB
  set S : Finset (Fin J) :=
    Finset.univ.filter (fun i : Fin J => ¬ γ (k i.castSucc) ∧ γ (k i.succ)) with hS
  -- the crossing set has at most one element
  have hScard : S.card ≤ 1 := by
    rw [hS, Finset.card_le_one]
    intro i hi j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    by_contra hij
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have hval : ((i.succ : Fin (J + 1)) : ℕ) ≤ ((j.castSucc : Fin (J + 1)) : ℕ) := by
        rw [Fin.val_succ, Fin.val_castSucc]
        have h' : (i : ℕ) < (j : ℕ) := Fin.lt_def.mp hlt
        omega
      have hkle : k i.succ ≤ k j.castSucc := hk (Fin.le_def.mpr hval)
      exact hj.1 (hγ hkle hi.2)
    · have hval : ((j.succ : Fin (J + 1)) : ℕ) ≤ ((i.castSucc : Fin (J + 1)) : ℕ) := by
        rw [Fin.val_succ, Fin.val_castSucc]
        have h' : (j : ℕ) < (i : ℕ) := Fin.lt_def.mp hlt
        omega
      have hkle : k j.succ ≤ k i.castSucc := hk (Fin.le_def.mpr hval)
      exact hi.1 (hγ hkle hj.2)
  -- at a crossing the increment is `u (k i.succ)`, bounded by the sup part
  have hzS : ∀ i : Fin J, i ∈ S →
      eLpNorm (w (k i.succ) - w (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q) ≤ A := by
    intro i hi
    rw [hS] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨hi1, hi2⟩ := hi
    have hws : w (k i.succ) = u (k i.succ) := by
      funext θ; rw [hw (k i.succ) θ, if_pos hi2]
    have hwc : w (k i.castSucc) = 0 := by
      funext θ; rw [hw (k i.castSucc) θ, if_neg hi1]; rfl
    have hz : eLpNorm (w (k i.succ) - w (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q)
        = eLpNorm (u (k i.succ)) 2 (Work.KMTPlan.A6.zmodProb Q) := by
      rw [hws, hwc, sub_zero]
    rw [hz, hA]
    exact le_iSup (fun n : ℕ => eLpNorm (u n) 2 (Work.KMTPlan.A6.zmodProb Q)) (k i.succ)
  -- away from a crossing the increment only decreases
  have hzc : ∀ i : Fin J, i ∉ S →
      eLpNorm (w (k i.succ) - w (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q)
        ≤ eLpNorm (u (k i.succ) - u (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q) := by
    intro i hi
    by_cases h1 : γ (k i.castSucc)
    · have h2 : γ (k i.succ) := hγ (hk (Fin.castSucc_le_succ i)) h1
      have hws : w (k i.succ) = u (k i.succ) := by
        funext θ; rw [hw (k i.succ) θ, if_pos h2]
      have hwc : w (k i.castSucc) = u (k i.castSucc) := by
        funext θ; rw [hw (k i.castSucc) θ, if_pos h1]
      rw [hws, hwc]
    · have h2 : ¬ γ (k i.succ) := by
        intro h2
        exact hi (by
          rw [hS]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨h1, h2⟩)
      have hws : w (k i.succ) = 0 := by
        funext θ; rw [hw (k i.succ) θ, if_neg h2]; rfl
      have hwc : w (k i.castSucc) = 0 := by
        funext θ; rw [hw (k i.castSucc) θ, if_neg h1]; rfl
      rw [hws, hwc, sub_self, eLpNorm_zero]
      exact zero_le
  -- the crossing terms: at most one increment, each bounded by `A`
  have h1 : (∑ i ∈ S, ENNReal.rpow
        (eLpNorm (w (k i.succ) - w (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q)) R)
      ≤ ENNReal.rpow A R :=
    (Finset.sum_le_sum fun i hi => ENNReal.rpow_le_rpow (hzS i hi) hRpos.le).trans
      (sum_const_le_of_card_le_one S _ hScard)
  -- the remaining terms are bounded by the chain terms of `u`
  have h2 : (∑ i ∈ Sᶜ, ENNReal.rpow
        (eLpNorm (w (k i.succ) - w (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q)) R)
      ≤ ∑ i : Fin J, ENNReal.rpow
          (eLpNorm (u (k i.succ) - u (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q)) R :=
    (Finset.sum_le_sum fun i hi =>
        ENNReal.rpow_le_rpow (hzc i (Finset.mem_compl.mp hi)) hRpos.le).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Sᶜ) (fun i _ _ => zero_le))
  -- the `ℓ^R`-sum bound: one crossing term plus the remaining increments
  have hsum : (∑ i : Fin J, ENNReal.rpow
          (eLpNorm (w (k i.succ) - w (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q)) R)
      ≤ (∑ i : Fin J, ENNReal.rpow
          (eLpNorm (u (k i.succ) - u (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q)) R)
        + ENNReal.rpow A R := by
    calc (∑ i : Fin J, ENNReal.rpow
            (eLpNorm (w (k i.succ) - w (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q)) R)
        = (∑ i ∈ S, ENNReal.rpow
              (eLpNorm (w (k i.succ) - w (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q)) R)
            + ∑ i ∈ Sᶜ, ENNReal.rpow
              (eLpNorm (w (k i.succ) - w (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q)) R :=
          (Finset.sum_add_sum_compl S _).symm
      _ ≤ ENNReal.rpow A R + ∑ i : Fin J, ENNReal.rpow
              (eLpNorm (u (k i.succ) - u (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q)) R :=
          add_le_add h1 h2
      _ = (∑ i : Fin J, ENNReal.rpow
              (eLpNorm (u (k i.succ) - u (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q)) R)
            + ENNReal.rpow A R := add_comm _ _
  -- Minkowski in `ℝ≥0∞` and the identification `(A^R)^(1/R) = A`
  have hfin : ENNReal.rpow (∑ i : Fin J, ENNReal.rpow
        (eLpNorm (w (k i.succ) - w (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q)) R) (1 / R)
      ≤ B + A := by
    have h1' := ENNReal.rpow_le_rpow hsum hnn
    have h2' := ENNReal.rpow_add_le_add_rpow
      (∑ i : Fin J, ENNReal.rpow
        (eLpNorm (u (k i.succ) - u (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q)) R)
      (ENNReal.rpow A R) hnn hle1
    have h3 : ENNReal.rpow (ENNReal.rpow A R) (1 / R) = A := rpow_rpow_inv hR A
    have h4 : ENNReal.rpow (∑ i : Fin J, ENNReal.rpow
          (eLpNorm (u (k i.succ) - u (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q)) R) (1 / R)
        ≤ B := by
      rw [hB]
      exact le_iSup_of_le J (le_iSup_of_le k (le_iSup_of_le hk le_rfl))
    calc ENNReal.rpow (∑ i : Fin J, ENNReal.rpow
            (eLpNorm (w (k i.succ) - w (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q)) R) (1 / R)
        ≤ ENNReal.rpow ((∑ i : Fin J, ENNReal.rpow
              (eLpNorm (u (k i.succ) - u (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q)) R)
              + ENNReal.rpow A R) (1 / R) := h1'
      _ ≤ ENNReal.rpow (∑ i : Fin J, ENNReal.rpow
              (eLpNorm (u (k i.succ) - u (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q)) R) (1 / R)
            + ENNReal.rpow (ENNReal.rpow A R) (1 / R) := h2'
      _ = ENNReal.rpow (∑ i : Fin J, ENNReal.rpow
              (eLpNorm (u (k i.succ) - u (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q)) R) (1 / R)
            + A := by rw [h3]
      _ ≤ B + A := add_le_add h4 le_rfl
  exact hfin

theorem VrLiftClip {Q : ℕ} [NeZero Q] (R : ℝ) (hR : 1 ≤ R)
    (γ : ℕ → Prop) [DecidablePred γ] (hγ : ∀ ⦃n m : ℕ⦄, n ≤ m → γ n → γ m)
    (u : ℕ → ZMod Q → ℂ) :
    Work.KMTPlan.A6.VrLiftDataP R Q (fun n θ => if γ n then u n θ else 0)
      ≤ Work.KMTPlan.A6.VrLiftDataP R Q u + Work.KMTPlan.A6.VrLiftDataP R Q u := by
  classical
  set w : ℕ → ZMod Q → ℂ := fun n θ => if γ n then u n θ else 0 with hw
  have hw' : ∀ n θ, w n θ = if γ n then u n θ else 0 := fun n θ => by rw [hw]
  unfold Work.KMTPlan.A6.VrLiftDataP
  refine (add_le_add (sup_le_of_clip γ u w hw')
    (chain_le_of_clip R hR γ hγ u w hw')).trans ?_
  -- `supU + (chainU + supU) ≤ (supU + chainU) + (supU + chainU)`
  conv_lhs => rw [← add_assoc]
  exact add_le_add le_rfl le_self_add

end Work.A6HighLow
