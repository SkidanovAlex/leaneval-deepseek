import Mathlib
import Submission.Work.BMF.recursion.Defs
import Submission.Work.BMF.recursion.I1I2Defs
import Submission.Work.BMF.recursion.MomVec
import Submission.Work.BMF.recursion.I2aux
import Submission.Work.BMF.recursion.I2linnik

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.BMF.recursion

open Finset
open scoped BigOperators

noncomputable section

open LeanEval.NumberTheory.VinogradovMeanValue

/-! ## The quadruple sets of the Linnik step -/

/-- The quadruples `(m, n, U, V)` of head pairs `(m,n)` with pairwise distinct residues
modulo `p` and `U`-pairs whose shifted head moments are linked by
`p^(j+1)·(momVec V - momVec U)_j = (hMom m - hMom n)_j`. -/
def QMset (S k Q p y : ℕ) (hkS : k ≤ S) :
    Finset ((Tup k Q × Tup k Q) × (UTup (S - k) (Q / p) × UTup (S - k) (Q / p))) := by
  classical
  exact ((Hset p k Q ×ˢ Hset p k Q) ×ˢ
      ((Finset.univ : Finset (UTup (S - k) (Q / p))) ×ˢ Finset.univ)).filter (fun q =>
        ∀ j : Fin k, (p : ℤ) ^ (j.1 + 1) * (momVec k q.2.2 j - momVec k q.2.1 j)
          = hMom k y q.1.1 j - hMom k y q.1.2 j)

/-- The head pairs satisfying the Linnik congruence conditions. -/
def CongSet (S k Q p y : ℕ) : Finset (Tup k Q × Tup k Q) := by
  classical
  exact (Hset p k Q ×ˢ Hset p k Q).filter (fun q =>
    ∀ j : Fin k, (p : ℤ) ^ (j.1 + 1) ∣ hMom k y q.1 j - hMom k y q.2 j)

/-- The diagonal pairs of `U`-tuples (equal moment vectors). -/
def DiagSet (S k Q p : ℕ) : Finset (UTup (S - k) (Q / p) × UTup (S - k) (Q / p)) := by
  classical
  exact Finset.univ.filter (fun q => momVec k q.1 = momVec k q.2)

lemma mem_QMset {S k Q p y : ℕ} {hkS : k ≤ S} {q : (Tup k Q × Tup k Q) ×
    (UTup (S - k) (Q / p) × UTup (S - k) (Q / p))} :
    q ∈ QMset S k Q p y hkS ↔
      q.1.1 ∈ Hset p k Q ∧ q.1.2 ∈ Hset p k Q ∧
      (∀ j : Fin k, (p : ℤ) ^ (j.1 + 1) * (momVec k q.2.2 j - momVec k q.2.1 j)
        = hMom k y q.1.1 j - hMom k y q.1.2 j) := by
  classical
  simp only [QMset, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
  tauto

lemma mem_CongSet {S k Q p y : ℕ} {q : Tup k Q × Tup k Q} :
    q ∈ CongSet S k Q p y ↔ q.1 ∈ Hset p k Q ∧ q.2 ∈ Hset p k Q ∧
      (∀ j : Fin k, (p : ℤ) ^ (j.1 + 1) ∣ hMom k y q.1 j - hMom k y q.2 j) := by
  classical
  simp only [CongSet, Finset.mem_filter, Finset.mem_product]
  tauto

lemma mem_pairMomSet' {S k Q : ℕ} {s : Finset (Tup S Q)} {q : Tup S Q × Tup S Q} :
    q ∈ pairMomSet S k Q s ↔ q.1 ∈ s ∧ q.2 ∈ s ∧
      Submission.Vinogradov.powerSums k q.1 = Submission.Vinogradov.powerSums k q.2 := by
  classical
  constructor
  · intro hq
    rw [pairMomSet, Finset.mem_filter] at hq
    exact ⟨(Finset.mem_product.mp hq.1).1, (Finset.mem_product.mp hq.1).2, hq.2⟩
  · rintro ⟨h1, h2, h3⟩
    rw [pairMomSet, Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr ⟨h1, h2⟩, h3⟩

lemma card_univ_tup (k Q : ℕ) : (Finset.univ : Finset (Tup k Q)).card = Q ^ k := by
  have hcoe : Fintype.card (Finset.Icc 1 Q) = Q := by
    rw [Fintype.card_coe, Nat.card_Icc]
    omega
  rw [Finset.card_univ]
  show Fintype.card (Fin k → Finset.Icc 1 Q) = Q ^ k
  rw [Fintype.card_fun, hcoe, Fintype.card_fin]

lemma Hset_card (p k Q : ℕ) : (Hset p k Q).card ≤ Q ^ k := by
  classical
  have h1 : (Hset p k Q).card ≤ (Finset.univ : Finset (Tup k Q)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  rw [card_univ_tup] at h1
  exact h1

/-! ## The three counting steps -/

/-- `I2` is bounded by the `(m,n,U,V)`-quadruples. -/
lemma pairMomSet_le_QMset (S k Q p y : ℕ) (hkS : k ≤ S) (hy : y < p) :
    (pairMomSet S k Q (i2Set S k Q p y hkS)).card ≤ (QMset S k Q p y hkS).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun q : Tup S Q × Tup S Q => ((hdT hkS q.1, hdT hkS q.2),
      (uTupOf p hkS q.1, uTupOf p hkS q.2))) ?_ ?_
  · intro q hq
    rw [Finset.mem_coe, mem_pairMomSet'] at hq
    rw [Finset.mem_coe, mem_QMset]
    refine ⟨(mem_i2Set_iff hkS q.1).mp hq.1 |>.1, (mem_i2Set_iff hkS q.2).mp hq.2.1 |>.1, ?_⟩
    intro j
    exact key_identity hkS hy hq.1 hq.2.1 hq.2.2 j
  · intro a ha b hb hab
    rw [Finset.mem_coe, mem_pairMomSet'] at ha hb
    have e1 : hdT hkS a.1 = hdT hkS b.1 := congrArg (fun z => z.1.1) hab
    have e2 : hdT hkS a.2 = hdT hkS b.2 := congrArg (fun z => z.1.2) hab
    have e3 : uTupOf p hkS a.1 = uTupOf p hkS b.1 := congrArg (fun z => z.2.1) hab
    have e4 : uTupOf p hkS a.2 = uTupOf p hkS b.2 := congrArg (fun z => z.2.2) hab
    exact Prod.ext (uTupOf_injOn hkS hy a.1 ha.1 b.1 hb.1 e1 e3)
      (uTupOf_injOn hkS hy a.2 ha.2.1 b.2 hb.2.1 e2 e4)

/-- The quadruble count is bounded by the congruence-pair count times the diagonal count. -/
lemma QMset_bound (S k Q p y : ℕ) (hkS : k ≤ S) (hp : p.Prime) :
    (QMset S k Q p y hkS).card ≤ (CongSet S k Q p y).card * (DiagSet S k Q p).card := by
  classical
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hmap : Set.MapsTo (fun q : (Tup k Q × Tup k Q) ×
      (UTup (S - k) (Q / p) × UTup (S - k) (Q / p)) => q.1)
      (↑(QMset S k Q p y hkS)) (↑(Hset p k Q ×ˢ Hset p k Q)) := by
    intro q hq
    rw [Finset.mem_coe, mem_QMset] at hq
    rw [Finset.mem_coe, Finset.mem_product]
    exact ⟨hq.1, hq.2.1⟩
  have hfiber_le : ∀ p' ∈ CongSet S k Q p y,
      ((QMset S k Q p y hkS).filter (fun q => q.1 = p')).card ≤ (DiagSet S k Q p).card := by
    intro p' hp'
    by_cases hne : ((QMset S k Q p y hkS).filter (fun q => q.1 = p')).Nonempty
    · obtain ⟨w, hw⟩ := hne
      have hwmem : w ∈ QMset S k Q p y hkS := (Finset.mem_filter.mp hw).1
      have hw1 : w.1 = p' := (Finset.mem_filter.mp hw).2
      have hC2w := (mem_QMset.mp hwmem).2.2
      refine le_trans (Finset.card_le_card_of_injOn (fun q => q.2) ?_ ?_)
        (momVec_fiber_le_diag (S - k) k (Q / p) (momVec k w.2.2 - momVec k w.2.1))
      · intro q hq
        rw [Finset.mem_coe, Finset.mem_filter] at hq
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
        have hqmem := hq.1
        have hq1 : q.1 = p' := hq.2
        have hC2q := (mem_QMset.mp hqmem).2.2
        funext j
        simp only [Pi.sub_apply]
        have h1 := hC2q j
        have h2 := hC2w j
        rw [hq1] at h1
        rw [hw1] at h2
        exact mul_left_cancel₀ (pow_ne_zero _ hp0) (by rw [h1, h2])
      · intro a ha b hb hab
        rw [Finset.mem_coe, Finset.mem_filter] at ha hb
        exact Prod.ext (by rw [ha.2, hb.2]) hab
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      simp
  have hsubset : CongSet S k Q p y ⊆ Hset p k Q ×ˢ Hset p k Q := by
    intro x hx
    exact Finset.mem_product.mpr ⟨(mem_CongSet.mp hx).1, (mem_CongSet.mp hx).2.1⟩
  have hzero : ∀ p' ∈ Hset p k Q ×ˢ Hset p k Q, p' ∉ CongSet S k Q p y →
      ((QMset S k Q p y hkS).filter (fun q => q.1 = p')).card = 0 := by
    intro p' hp' hpn
    apply Finset.card_eq_zero.mpr
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨q, hq⟩
    have hqmem : q ∈ QMset S k Q p y hkS := (Finset.mem_filter.mp hq).1
    have hq1 : q.1 = p' := (Finset.mem_filter.mp hq).2
    refine hpn (mem_CongSet.mpr ⟨?_, ?_, ?_⟩)
    · have h := (mem_QMset.mp hqmem).1
      rwa [hq1] at h
    · have h := (mem_QMset.mp hqmem).2.1
      rwa [hq1] at h
    · intro j
      have h := (mem_QMset.mp hqmem).2.2 j
      rw [hq1] at h
      exact ⟨momVec k q.2.2 j - momVec k q.2.1 j, h.symm⟩
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := fun q : (Tup k Q × Tup k Q) × (UTup (S - k) (Q / p) × UTup (S - k) (Q / p)) => q.1)
    (s := QMset S k Q p y hkS) (t := Hset p k Q ×ˢ Hset p k Q) hmap
  calc (QMset S k Q p y hkS).card
      = ∑ p' ∈ Hset p k Q ×ˢ Hset p k Q,
          ((QMset S k Q p y hkS).filter (fun q => q.1 = p')).card := hfib
    _ = ∑ p' ∈ CongSet S k Q p y,
          ((QMset S k Q p y hkS).filter (fun q => q.1 = p')).card :=
        (Finset.sum_subset hsubset hzero).symm
    _ ≤ ∑ p' ∈ CongSet S k Q p y, (DiagSet S k Q p).card := Finset.sum_le_sum hfiber_le
    _ = (CongSet S k Q p y).card * (DiagSet S k Q p).card := by
        rw [Finset.sum_const, smul_eq_mul]

/-- The Linnik bound for one fixed head tuple on the other side. -/
lemma CongSet_fiber_le (S k Q p y : ℕ) (hp : p.Prime) (hkp : k < p) (hQp : Q < p ^ k)
    (n : Tup k Q) :
    ((Hset p k Q).filter (fun m => ∀ j : Fin k,
        (p : ℤ) ^ (j.1 + 1) ∣ hMom k y m j - hMom k y n j)).card
      ≤ k.factorial * p ^ (k * (k - 1) / 2) := by
  classical
  set H : ℕ → ℕ := fun j =>
    ((∑ i, (((n i).1 : ℤ) - (y : ℤ)) ^ j) % ((p : ℤ) ^ j)).toNat with hH
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hsub : ((Hset p k Q).filter (fun m => ∀ j : Fin k,
        (p : ℤ) ^ (j.1 + 1) ∣ hMom k y m j - hMom k y n j))
      ⊆ ((Finset.univ : Finset (Tup k Q)).filter (fun a =>
        (∀ i j : Fin k, i ≠ j → ¬ (p : ℤ) ∣ (((a i).1 : ℤ) - ((a j).1 : ℤ))) ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ k →
          ((p : ℤ) ^ j) ∣ ((∑ i, (((a i).1 : ℤ) - (y : ℤ)) ^ j) - (H j : ℤ))))) := by
    intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨hmHset, hmc⟩ := hm
    have hmHDp : HDp p k (le_refl k) m := by
      rw [Hset, Finset.mem_filter] at hmHset
      exact hmHset.2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ m, ?_, ?_⟩
    · intro i j hij
      have h := hmHDp i j hij
      have e1 : m (hIdx (le_refl k) i) = m i := congrArg m (Fin.ext rfl)
      have e2 : m (hIdx (le_refl k) j) = m j := congrArg m (Fin.ext rfl)
      rwa [e1, e2] at h
    · intro j hj1 hjk
      have hjk1 : j - 1 < k := by omega
      have hjj : (⟨j - 1, hjk1⟩ : Fin k).1 + 1 = j := by simp; omega
      have hmval : hMom k y m ⟨j - 1, hjk1⟩ = ∑ i, (((m i).1 : ℤ) - (y : ℤ)) ^ j := by
        rw [hMom]
        exact Finset.sum_congr rfl (fun i _ => by rw [hjj])
      have hnval : hMom k y n ⟨j - 1, hjk1⟩ = ∑ i, (((n i).1 : ℤ) - (y : ℤ)) ^ j := by
        rw [hMom]
        exact Finset.sum_congr rfl (fun i _ => by rw [hjj])
      have hHval : ((H j : ℕ) : ℤ) = (∑ i, (((n i).1 : ℤ) - (y : ℤ)) ^ j) % ((p : ℤ) ^ j) := by
        rw [hH]
        exact Int.toNat_of_nonneg (Int.emod_nonneg _ (pow_ne_zero _ hp0))
      have hdiv : ((p : ℤ) ^ j) ∣ hMom k y m ⟨j - 1, hjk1⟩ - hMom k y n ⟨j - 1, hjk1⟩ := by
        have h := hmc ⟨j - 1, hjk1⟩
        rwa [hjj] at h
      have h3 : ((p : ℤ) ^ j) ∣ hMom k y n ⟨j - 1, hjk1⟩ - ((H j : ℕ) : ℤ) := by
        rw [hHval, hnval]
        refine ⟨(∑ i, (((n i).1 : ℤ) - (y : ℤ)) ^ j) / (p : ℤ) ^ j, ?_⟩
        have h := Int.mul_ediv_add_emod (∑ i, (((n i).1 : ℤ) - (y : ℤ)) ^ j) ((p : ℤ) ^ j)
        linarith [h]
      have h4 : ((p : ℤ) ^ j) ∣ (∑ i, (((m i).1 : ℤ) - (y : ℤ)) ^ j) - (H j : ℤ) := by
        rw [← hmval]
        have := dvd_add hdiv h3
        convert this using 1
        ring
      exact h4
  exact le_trans (Finset.card_le_card hsub) (linnik_count p k Q y hp hkp hQp H)

/-- The head-pair count obeys the Linnik bound. -/
lemma CongSet_bound (S k Q p y : ℕ) (hp : p.Prime) (hkp : k < p) (hQp : Q < p ^ k) :
    (CongSet S k Q p y).card ≤ Q ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) := by
  classical
  have hmap : Set.MapsTo (fun q : Tup k Q × Tup k Q => q.2)
      (↑(CongSet S k Q p y)) (↑(Hset p k Q)) := by
    intro q hq
    exact (mem_CongSet.mp hq).2.1
  have hfiber_le : ∀ n ∈ Hset p k Q,
      ((CongSet S k Q p y).filter (fun q => q.2 = n)).card
        ≤ k.factorial * p ^ (k * (k - 1) / 2) := by
    intro n hn
    refine le_trans (Finset.card_le_card_of_injOn (fun q => q.1) ?_ ?_)
      (CongSet_fiber_le S k Q p y hp hkp hQp n)
    · intro q hq
      rw [Finset.mem_coe, Finset.mem_filter] at hq
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨(mem_CongSet.mp hq.1).1, ?_⟩
      intro j
      have h := (mem_CongSet.mp hq.1).2.2 j
      rw [hq.2] at h
      exact h
    · intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_filter] at ha hb
      exact Prod.ext hab (by rw [ha.2, hb.2])
  have hfib := Finset.card_eq_sum_card_fiberwise (f := fun q : Tup k Q × Tup k Q => q.2)
    (s := CongSet S k Q p y) (t := Hset p k Q) hmap
  calc (CongSet S k Q p y).card
      = ∑ n ∈ Hset p k Q, ((CongSet S k Q p y).filter (fun q => q.2 = n)).card := hfib
    _ ≤ ∑ n ∈ Hset p k Q, (k.factorial * p ^ (k * (k - 1) / 2)) := Finset.sum_le_sum hfiber_le
    _ = (Hset p k Q).card * (k.factorial * p ^ (k * (k - 1) / 2)) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ Q ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) :=
        Nat.mul_le_mul_right _ (Hset_card p k Q)

/-- The diagonal `U`-pair count is bounded by the mean value `J`. -/
lemma DiagSet_bound (S k Q M p : ℕ) (hM : 1 ≤ M) (hMp : M ≤ p) :
    ((DiagSet S k Q p).card : ℝ) ≤ J (S - k) k (1 + Q / M) := by
  refine le_trans (momVec_diag_le_J (S - k) k (Q / p)) ?_
  refine J_mono_range ?_
  have hdiv : Q / p ≤ Q / M := Nat.div_le_div_left hMp (by omega)
  omega

theorem I2_bound (S k Q M p y : ℕ) (hk : 2 ≤ k) (hkS : k ≤ S) (hp : p.Prime) (hkp : k < p)
    (hQp : Q < p ^ k) (hM : 1 ≤ M) (hMp : M ≤ p) (hy : y < p) :
    (I2 S k Q p y hkS : ℝ) ≤ (Q : ℝ) ^ k * ((k.factorial : ℕ) : ℝ) *
      (p : ℝ) ^ (k * (k - 1) / 2) * LeanEval.NumberTheory.VinogradovMeanValue.J (S - k) k (1 + Q / M)
    := by
  classical
  have h1 : ((I2 S k Q p y hkS : ℕ) : ℝ) ≤ ((QMset S k Q p y hkS).card : ℝ) := by
    rw [I2_eq_pairCard]
    exact_mod_cast pairMomSet_le_QMset S k Q p y hkS hy
  have h2 : ((QMset S k Q p y hkS).card : ℝ)
      ≤ ((CongSet S k Q p y).card : ℝ) * ((DiagSet S k Q p).card : ℝ) := by
    exact_mod_cast QMset_bound S k Q p y hkS hp
  have h3 : ((CongSet S k Q p y).card : ℝ)
      ≤ (((Q ^ k * (k.factorial * p ^ (k * (k - 1) / 2))) : ℕ) : ℝ) := by
    exact_mod_cast CongSet_bound S k Q p y hp hkp hQp
  have h4 : ((DiagSet S k Q p).card : ℝ) ≤ J (S - k) k (1 + Q / M) :=
    DiagSet_bound S k Q M p hM hMp
  have hJ : (0 : ℝ) ≤ J (S - k) k (1 + Q / M) := Submission.Vinogradov.J_nonneg _ _ _
  have hb : (0 : ℝ) ≤ (((Q ^ k * (k.factorial * p ^ (k * (k - 1) / 2))) : ℕ) : ℝ) := by
    positivity
  calc (I2 S k Q p y hkS : ℝ)
      ≤ ((QMset S k Q p y hkS).card : ℝ) := h1
    _ ≤ ((CongSet S k Q p y).card : ℝ) * ((DiagSet S k Q p).card : ℝ) := h2
    _ ≤ (((Q ^ k * (k.factorial * p ^ (k * (k - 1) / 2))) : ℕ) : ℝ) * J (S - k) k (1 + Q / M) :=
        mul_le_mul h3 h4 (by positivity) hb
    _ = (Q : ℝ) ^ k * ((k.factorial : ℕ) : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2) *
        J (S - k) k (1 + Q / M) := by
        push_cast
        ring

end

end Work.BMF.recursion
