import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.keptEvidencePair

#check @Finset.sum_erase_add
#check @Finset.card_erase_of_mem
#check @Finset.sum_filter
#check @Finset.sum_mul_sum
#check @Finset.mem_erase
#check @Work.Deep.Conc.expect_add
#check @Work.Deep.Conc.expect_sub
#check @Work.Deep.Conc.expect_const
#check @Work.Deep.Conc.expect_const_mul

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Finset

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

noncomputable section

/-- For events `A`, `B` of a finite probability space with nonempty carrier,
`P (A ∩ B) = P A + P B - 1 + P (Aᶜ ∩ Bᶜ)`. -/
lemma prob_inter_eq {Ω : Type*} [Fintype Ω] [Nonempty Ω] (A B : Set Ω) :
    Work.Deep.Conc.prob (A ∩ B)
      = Work.Deep.Conc.prob A + Work.Deep.Conc.prob B - 1
        + Work.Deep.Conc.prob (Aᶜ ∩ Bᶜ) := by
  have hpt : (A ∩ B).indicator (fun _ => (1 : ℝ))
      = (A.indicator (fun _ => (1 : ℝ)) + B.indicator (fun _ => (1 : ℝ))
          - (fun _ => (1 : ℝ))) + (Aᶜ ∩ Bᶜ).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, ha, hb]
  rw [Work.Deep.Conc.prob, hpt, Work.Deep.Conc.prob, Work.Deep.Conc.prob,
    Work.Deep.Conc.prob, Work.Deep.Conc.expect_add, Work.Deep.Conc.expect_sub,
    Work.Deep.Conc.expect_add, Work.Deep.Conc.expect_const]

variable {n c : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗]
  {L : 𝓗 → Finset (Fin c)} {K : ℕ} [NeZero K]

/-- **The law of `#keptEvidence`.**  Its mean is at most the retention bound, and its variance
is at most its mean. -/
theorem keptEvidenceMeanVarAlt {C D Λ : ℕ}
    (hΛ1 : 1 ≤ Λ)
    (hlin : 𝓗.IsLinear)
    (hsize : ∀ e : 𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) = C)
    (hdeg : ∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
      Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} = D)
    (hlist : ∀ e : 𝓗, (L e).card = Λ) (e : 𝓗) :
    Work.Deep.Conc.expect (fun ω : Round.Space K 𝓗 L =>
        ((keptEvidence K e ω).card : ℝ))
      ≤ (Λ : ℝ) * (1 - retention Λ C D K) ∧
    Work.Deep.Conc.expect (fun ω : Round.Space K 𝓗 L =>
        (((keptEvidence K e ω).card : ℝ) -
          Work.Deep.Conc.expect (fun ω : Round.Space K 𝓗 L =>
            ((keptEvidence K e ω).card : ℝ))) ^ 2)
      ≤ Work.Deep.Conc.expect (fun ω : Round.Space K 𝓗 L =>
        ((keptEvidence K e ω).card : ℝ)) := by
  classical
  have hΛpos : 0 < Λ := lt_of_lt_of_le Nat.zero_lt_one hΛ1
  have hne : ∀ f : 𝓗, Nonempty (Round.Coord K 𝓗 L f) := fun f =>
    ⟨(0, ⟨0, by rw [hlist f]; exact hΛpos⟩)⟩
  haveI : Nonempty (Round.Space K 𝓗 L) := ⟨fun f => Classical.choice (hne f)⟩
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne K)
  have hΛ1R : (1 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast hΛ1
  set q : ℝ := 1 / ((K : ℝ) * (Λ : ℝ)) with hqdef
  set s : ℝ := (1 - q) ^ (C * (D - 1)) with hsdef
  have hq0 : 0 ≤ q := by rw [hqdef]; positivity
  have hq1 : q ≤ 1 := by
    rw [hqdef, div_le_one (by positivity)]
    nlinarith
  have hqr : retention Λ C D K = (1 - q) ^ (C * D) := by
    rw [retention, hqdef, div_div]
  -- the indicator variables
  set Y : Fin c → Round.Space K 𝓗 L → ℝ :=
    fun γ ω => if γ ∈ keptEvidence K e ω then (1 : ℝ) else 0 with hYdef
  have hexpY : ∀ γ : Fin c, Work.Deep.Conc.expect (Y γ)
      = Work.Deep.Conc.prob {ω : Round.Space K 𝓗 L | γ ∈ keptEvidence K e ω} := by
    intro γ
    have hYind : Y γ
        = ({ω : Round.Space K 𝓗 L | γ ∈ keptEvidence K e ω}).indicator (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases h : γ ∈ keptEvidence K e ω <;>
        simp [hYdef, Set.indicator_of_mem, Set.indicator_of_notMem, h]
    rw [hYind]
    rfl
  -- the sum decomposition of the cardinality
  have hcard : ∀ ω : Round.Space K 𝓗 L,
      ((keptEvidence K e ω).card : ℝ) = ∑ γ ∈ (L e), Y γ ω := by
    intro ω
    have hsub : keptEvidence K e ω ⊆ L e := fun γ hγ => (mem_classEvidence.mp hγ).1
    have h1 : (∑ γ ∈ (L e), Y γ ω) = ∑ _γ ∈ (keptEvidence K e ω), (1 : ℝ) := by
      rw [← Finset.sum_filter (s := L e) (f := fun _ : Fin c => (1 : ℝ))
        (p := fun γ => γ ∈ keptEvidence K e ω)]
      congr 1
      rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub]
    rw [h1, Finset.sum_const]
    simp
  -- the probability of a single colour
  have hprob : ∀ γ ∈ (L e), Work.Deep.Conc.prob
      {ω : Round.Space K 𝓗 L | γ ∈ keptEvidence K e ω} = 1 - s := by
    intro γ hγ
    rw [prob_mem_keptEvidence (K := K) (L := L) (𝓗 := 𝓗) hlin hsize hdeg hlist hγ, ← hsdef]
  -- pairwise negative correlation
  have hpair : ∀ γ ∈ (L e), ∀ γ' ∈ (L e), γ ≠ γ' → Work.Deep.Conc.prob
      {ω : Round.Space K 𝓗 L | γ ∈ keptEvidence K e ω ∧ γ' ∈ keptEvidence K e ω}
        ≤ (1 - s) * (1 - s) := by
    intro γ hγ γ' hγ' hne'
    have h1 := hprob γ hγ
    have h2 := hprob γ' hγ'
    have h3 : Work.Deep.Conc.prob {ω : Round.Space K 𝓗 L |
        γ ∉ keptEvidence K e ω ∧ γ' ∉ keptEvidence K e ω} ≤ s * s := by
      refine le_trans (prob_notMem_pair (K := K) (L := L) (𝓗 := 𝓗) hlin hsize hdeg hlist
        hne' hγ hγ') ?_
      rw [← hsdef]
    have h4 := prob_inter_eq {ω : Round.Space K 𝓗 L | γ ∈ keptEvidence K e ω}
      {ω : Round.Space K 𝓗 L | γ' ∈ keptEvidence K e ω}
    rw [Set.compl_ofPred, Set.compl_ofPred] at h4
    have h4' : Work.Deep.Conc.prob {ω : Round.Space K 𝓗 L |
          γ ∈ keptEvidence K e ω ∧ γ' ∈ keptEvidence K e ω}
        = Work.Deep.Conc.prob {ω : Round.Space K 𝓗 L | γ ∈ keptEvidence K e ω}
          + Work.Deep.Conc.prob {ω : Round.Space K 𝓗 L | γ' ∈ keptEvidence K e ω} - 1
          + Work.Deep.Conc.prob {ω : Round.Space K 𝓗 L |
              γ ∉ keptEvidence K e ω ∧ γ' ∉ keptEvidence K e ω} := h4
    rw [h4', h1, h2]
    nlinarith [h3]
  -- the mean
  have hmean : Work.Deep.Conc.expect (fun ω : Round.Space K 𝓗 L =>
      ((keptEvidence K e ω).card : ℝ)) = (Λ : ℝ) * (1 - s) := by
    calc Work.Deep.Conc.expect (fun ω : Round.Space K 𝓗 L =>
            ((keptEvidence K e ω).card : ℝ))
        = Work.Deep.Conc.expect (fun ω => ∑ γ ∈ (L e), Y γ ω) :=
          Work.Deep.Conc.expect_congr hcard
      _ = ∑ γ ∈ (L e), Work.Deep.Conc.expect (Y γ) := Work.Deep.Conc.expect_sum _ _
      _ = ∑ γ ∈ (L e), Work.Deep.Conc.prob
            {ω : Round.Space K 𝓗 L | γ ∈ keptEvidence K e ω} :=
          Finset.sum_congr rfl (fun γ _ => hexpY γ)
      _ = ∑ _γ ∈ (L e), (1 - s) := Finset.sum_congr rfl hprob
      _ = ((L e).card : ℝ) * (1 - s) := by simp [Finset.sum_const]; ring
      _ = (Λ : ℝ) * (1 - s) := by rw [hlist e]
  -- the second moment
  have hYY : ∀ γ ∈ (L e), ∀ γ' ∈ (L e),
      Work.Deep.Conc.expect (fun ω => Y γ ω * Y γ' ω)
        = Work.Deep.Conc.prob
            {ω : Round.Space K 𝓗 L | γ ∈ keptEvidence K e ω ∧ γ' ∈ keptEvidence K e ω} := by
    intro γ hγ γ' hγ'
    have hpt : (fun ω : Round.Space K 𝓗 L => Y γ ω * Y γ' ω)
        = ({ω : Round.Space K 𝓗 L |
              γ ∈ keptEvidence K e ω ∧ γ' ∈ keptEvidence K e ω}).indicator (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases h1 : γ ∈ keptEvidence K e ω <;> by_cases h2 : γ' ∈ keptEvidence K e ω <;>
        simp [hYdef, Set.indicator_of_mem, Set.indicator_of_notMem, h1, h2]
    rw [hpt]
    rfl
  have hEX2 : Work.Deep.Conc.expect
      (fun ω : Round.Space K 𝓗 L => ((keptEvidence K e ω).card : ℝ) ^ 2)
      ≤ (Λ : ℝ) * (1 - s) + ((Λ : ℝ) * (1 - s)) ^ 2 := by
    have hX2 : ∀ ω : Round.Space K 𝓗 L,
        ((keptEvidence K e ω).card : ℝ) ^ 2
          = ∑ γ ∈ (L e), ∑ γ' ∈ (L e), Y γ ω * Y γ' ω := by
      intro ω
      rw [hcard ω, sq, Finset.sum_mul_sum]
    rw [Work.Deep.Conc.expect_congr hX2, Work.Deep.Conc.expect_sum]
    have hstep : ∀ γ ∈ (L e),
        Work.Deep.Conc.expect (fun ω => ∑ γ' ∈ (L e), Y γ ω * Y γ' ω)
          ≤ (1 - s) + ((Λ : ℝ) - 1) * ((1 - s) * (1 - s)) := by
      intro γ hγ
      rw [Work.Deep.Conc.expect_sum]
      rw [show (∑ γ' ∈ (L e), Work.Deep.Conc.expect (fun ω => Y γ ω * Y γ' ω))
          = Work.Deep.Conc.expect (fun ω => Y γ ω * Y γ ω)
            + ∑ γ' ∈ (L e).erase γ, Work.Deep.Conc.expect (fun ω => Y γ ω * Y γ' ω) from by
        rw [(Finset.sum_erase_add _ _ hγ).symm, add_comm]]
      have hdiag : Work.Deep.Conc.expect (fun ω => Y γ ω * Y γ ω)
          = Work.Deep.Conc.prob {ω : Round.Space K 𝓗 L | γ ∈ keptEvidence K e ω} := by
        rw [hYY γ hγ γ hγ]
        congr 1
        ext ω; simp
      rw [hdiag, hprob γ hγ]
      have hsub : ∀ γ' ∈ (L e).erase γ,
          Work.Deep.Conc.expect (fun ω => Y γ ω * Y γ' ω) ≤ (1 - s) * (1 - s) := by
        intro γ' hγ'
        obtain ⟨hne', hmem'⟩ := Finset.mem_erase.mp hγ'
        exact le_trans (le_of_eq (hYY γ hγ γ' hmem')) (hpair γ hγ γ' hmem' (Ne.symm hne'))
      refine add_le_add (le_refl (1 - s)) ?_
      refine le_trans (Finset.sum_le_sum hsub) ?_
      rw [Finset.sum_const, Finset.card_erase_of_mem hγ, hlist e, nsmul_eq_mul]
      have hc : ((Λ - 1 : ℕ) : ℝ) = (Λ : ℝ) - 1 := by rw [Nat.cast_sub hΛ1, Nat.cast_one]
      rw [hc]
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [Finset.sum_const, nsmul_eq_mul, hlist e]
    nlinarith [sq_nonneg (1 - s), sq_nonneg ((Λ : ℝ) * (1 - s)), (by positivity : (0:ℝ) ≤ (Λ:ℝ))]
  -- the variance identity
  have hsq : Work.Deep.Conc.expect (fun ω : Round.Space K 𝓗 L =>
        (((keptEvidence K e ω).card : ℝ)
          - Work.Deep.Conc.expect (fun ω : Round.Space K 𝓗 L =>
            ((keptEvidence K e ω).card : ℝ))) ^ 2)
      = Work.Deep.Conc.expect (fun ω : Round.Space K 𝓗 L =>
            ((keptEvidence K e ω).card : ℝ) ^ 2)
        - (Work.Deep.Conc.expect (fun ω : Round.Space K 𝓗 L =>
            ((keptEvidence K e ω).card : ℝ))) ^ 2 := by
    have h1 : (fun ω : Round.Space K 𝓗 L =>
          (((keptEvidence K e ω).card : ℝ)
            - Work.Deep.Conc.expect (fun ω : Round.Space K 𝓗 L =>
              ((keptEvidence K e ω).card : ℝ))) ^ 2)
        = (fun ω : Round.Space K 𝓗 L => ((keptEvidence K e ω).card : ℝ) ^ 2)
          - (fun ω : Round.Space K 𝓗 L =>
              2 * (Work.Deep.Conc.expect (fun ω : Round.Space K 𝓗 L =>
                ((keptEvidence K e ω).card : ℝ))) * ((keptEvidence K e ω).card : ℝ))
          + (fun _ => (Work.Deep.Conc.expect (fun ω : Round.Space K 𝓗 L =>
                ((keptEvidence K e ω).card : ℝ))) ^ 2) := by
      funext ω
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [h1, Work.Deep.Conc.expect_add, Work.Deep.Conc.expect_sub,
      Work.Deep.Conc.expect_const_mul, Work.Deep.Conc.expect_const, hmean]
    ring
  constructor
  · -- the mean bound
    rw [hmean]
    have hp_le : 1 - s ≤ 1 - retention Λ C D K := by
      have hmono := pow_le_pow_of_le_one (by linarith : (0:ℝ) ≤ 1 - q) (by linarith : 1 - q ≤ 1)
        (Nat.mul_le_mul_left C (Nat.sub_le D 1))
      rw [hqr, hsdef]
      linarith
    exact mul_le_mul_of_nonneg_left hp_le (by positivity : (0:ℝ) ≤ (Λ:ℝ))
  · -- the variance bound
    rw [hsq, hmean]
    nlinarith [hEX2, sq_nonneg (1 - s), (by positivity : (0:ℝ) ≤ (Λ:ℝ))]

end

end Work.Deep.Kahn
