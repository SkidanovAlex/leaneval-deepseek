import Submission.Work.Deep.Nibble.FamCongr
import Submission.Work.Deep.Nibble.FamChernoff
import Submission.Work.Deep.Nibble.WfamTail
import Submission.Work.Deep.Nibble.r2_Wv_mean
import Submission.Work.Deep.Nibble.r2_Y_mean
import Submission.Work.Deep.Nibble.r2_S_mean

/-!
# One wasteful round of the family nibble, with the estimates discharged

`nibble_round2_fam_asm` (`FamRound.lean`) is the round lemma of the "wasteful"
Rödl nibble with the per-set clauses `RoundGoodFamW`: it takes the five mean
estimates and the two per-set tails as *hypotheses*.  This module discharges all
of them from a single, explicit largeness condition on the members of the family
(`FamLarge`), producing the round lemma in the form the iteration consumes:

    nibble_round2_fam : ∃ Dmin, ∀ 𝓖 D 𝓕, Dmin ≤ D → … → FamLarge r θ δ D 𝓕 →
      (n·4qV ≤ 1/4) → (room) → ∃ ω, RoundGood … ∧ RoundGoodFamW …

The means are `r2_Wv_mean`, `r2_Y_mean`, `r2_S_mean`, `r2_Yfam_mean`,
`r2_Wfam_mean`; the tails are `r2_Yfam_tail` (at `t = δ|S|/2`) and
`r2_Wfam_tail` (with the exceptional probability `exc := exp(-θ³δ²|S|/(2048r²))`,
which is `≤ 1/(2D|S|+1)²` by the `log`-clause of `FamLarge` and dominates the
Chernoff bound for `{Zsum > 4θ|S|}` by the `2r ≤ θ|S|`-clause).
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.Deep.Nibble

open Work.Deep.Reed

/-- **The per-set largeness condition of one round.**  For every member `S` of the
family: `θ|S| ≥ 2r` (so that the Chernoff bound for the exceptional event of the
waste is dominated by the per-set tail), `θ³δ²|S| ≥ 10⁶r²` (`r2_Wfam_tail`'s
largeness hypothesis), `50r√|S| < δ|S|/2` (`r2_Yfam_tail`'s), and
`4096 log(2D|S|+1) r² ≤ θ³δ²|S|` (so that the exceptional probability
`exp(-θ³δ²|S|/(2048r²))` is `≤ 1/M²` for `M = 2D|S|+1`). -/
def FamLarge {V : Type*} (r : ℕ) (θ δ : ℝ) (D : ℕ) (𝓕 : Finset (Finset V)) : Prop :=
  ∀ S ∈ 𝓕,
    2 * (r : ℝ) ≤ θ * (S.card : ℝ)
    ∧ 10 ^ 6 * (r : ℝ) ^ 2 ≤ θ ^ 3 * δ ^ 2 * (S.card : ℝ)
    ∧ 50 * (r : ℝ) * Real.sqrt (S.card : ℝ) < δ * (S.card : ℝ) / 2
    ∧ 4096 * Real.log (2 * (D : ℝ) * (S.card : ℝ) + 1) * (r : ℝ) ^ 2
        ≤ θ ^ 3 * δ ^ 2 * (S.card : ℝ)

/-- **One round of the family nibble with all estimates discharged.**  From the
per-set largeness `FamLarge`, the LLL budget `n·4qV ≤ 1/4` and the room condition
(the sum of the two per-set tail bounds over the family), `nibble_round2_fam_asm`
supplies an outcome satisfying `RoundGood` and the per-set clauses
`RoundGoodFamW`.  The unused `hWfammean`-type input of `_asm` is not needed: the
means are derived here from `r2_Wv_mean`, `r2_Y_mean`, `r2_S_mean`,
`r2_Yfam_mean` and `r2_Wfam_mean`, and the two per-set tails from `r2_Yfam_tail`
and `r2_Wfam_tail` (with the exceptional probability
`exp(-θ³δ²|S|/(2048r²))`, dominated by the `weighted_chernoff_up` bound for
`{Zsum > 4θ|S|}` thanks to the `2r ≤ θ|S|`-clause of `FamLarge`). -/
theorem nibble_round2_fam {r : ℕ} (hr : 2 ≤ r) {θ δ ε' ε : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 100) (hδ0 : 0 < δ) (hδ1 : δ ≤ θ / 100)
    (hε'0 : 0 < ε') (hε'1 : ε' ≤ 1 / 2) (hε'2 : 100 * (ε + ε * (r : ℝ) * θ) ≤ ε')
    (hε0 : 0 < ε) (hε1 : ε ≤ θ / 100) (hεδ : 4 * ε ≤ δ) :
    ∃ Dmin : ℕ, 1 ≤ Dmin ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (𝓖 : Set (Set V)) (D : ℕ)
        (𝓕 : Finset (Finset V)),
        Dmin ≤ D → D ≤ Fintype.card V → HLin 𝓖 → HUnif 𝓖 r →
        (∀ v : V, |((hd 𝓖 v : ℝ)) - (D : ℝ)| ≤ ε * (D : ℝ)) →
        FamLarge r θ δ D 𝓕 →
        ((Fintype.card V : ℝ) * (4 * qV r ε' θ D) ≤ 1 / 4) →
        (∑ S ∈ 𝓕, (4 * Real.exp (- δ ^ 2 * (S.card : ℝ) / (64 * (r : ℝ) ^ 2))
          + 16 * Real.exp (-(θ ^ 3 * δ ^ 2 * (S.card : ℝ)) / (2048 * (r : ℝ) ^ 2))))
            ≤ 1 / 16 →
        ∃ ω : 𝓖 → Bool, RoundGood 𝓖 r D θ δ ε' (Dlev r θ D) ω
          ∧ RoundGoodFamW 𝓖 r θ δ 𝓕 ω := by
  classical
  obtain ⟨Dmin0, hDmin0pos, hassm⟩ :=
    nibble_round2_fam_asm hr hθ0 hθ1 hδ0 hδ1 hε'0 hε'1 hε'2 hε0 hε1 hεδ
  refine ⟨max (max Dmin0 8) (⌈8 * θ ^ 2 / δ⌉₊ + 2),
    le_trans (by norm_num : 1 ≤ 8) (le_trans (le_max_right Dmin0 8) (le_max_left _ _)), ?_⟩
  intro V _ _ 𝓖 D 𝓕 hD hDV hl hu hdeg hlarge hLLL hroom
  have hD0 : Dmin0 ≤ D :=
    le_trans (le_trans (le_max_left Dmin0 8) (le_max_left _ _)) hD
  have hD8 : 8 ≤ D := le_trans (le_trans (le_max_right Dmin0 8) (le_max_left _ _)) hD
  have hDle : ⌈8 * θ ^ 2 / δ⌉₊ + 2 ≤ D := le_trans (le_max_right _ _) hD
  have hD2 : 2 ≤ D := le_trans (by norm_num) hD8
  have hD1 : 1 ≤ D := le_trans (by norm_num) hD8
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hD8R : (8 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD8
  have hD1R : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hr2R : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hθle1 : θ ≤ 1 := by linarith
  have hδle1 : δ ≤ 1 := by linarith
  have hεle1 : ε ≤ 1 := by linarith
  have hθδle : θ ^ 2 * δ ^ 2 ≤ 1 := by
    have ha : θ ^ 2 ≤ 1 := by nlinarith [hθ0, hθle1]
    have hb : δ ^ 2 ≤ 1 := by nlinarith [hδ0, hδle1]
    nlinarith [ha, hb]
  have hbig : 8 * θ ^ 2 ≤ δ * (D : ℝ) := by
    have h1 : 8 * θ ^ 2 / δ ≤ (⌈8 * θ ^ 2 / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈8 * θ ^ 2 / δ⌉₊ : ℝ) + 2 ≤ (D : ℝ) := by exact_mod_cast hDle
    have h3 : (8 * θ ^ 2 / δ) * δ = 8 * θ ^ 2 := div_mul_cancel₀ _ (ne_of_gt hδ0)
    have h4 : (8 * θ ^ 2 / δ) * δ ≤ (D : ℝ) * δ := by
      have h5 : 8 * θ ^ 2 / δ ≤ (D : ℝ) := by linarith
      exact mul_le_mul_of_nonneg_right h5 (le_of_lt hδ0)
    linarith [h3, h4]
  have hθD : θ / (D : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hDpos]
    linarith [hD8R, hθ1]
  have hp0c : 0 ≤ θ / (D : ℝ) := by positivity
  have hp1c' : θ / (D : ℝ) < 1 := by
    rw [div_lt_one hDpos]
    linarith [hD1R, hθle1]
  have hp1c : θ / (D : ℝ) ≤ 1 := hp1c'.le
  -- the five means
  have hWvmean : ∀ (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) ≤ 1) (v : V),
      |(edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (fun ω => ((Wv 𝓖 ω v : ℕ) : ℝ))
        - Dlev r θ D| ≤ ε' * Dlev r θ D / 2 := by
    intro hp0 hp1 v
    rw [edgeMeasure_exp_congr 𝓖 hp0 hp1 hp0c hp1c]
    exact r2_Wv_mean (δ := δ) 𝓖 hr hθ0 hθ1 hε'0 hε'1 hε'2 hD2 hp0c hp1c hθD hl hu hdeg v
  have hYmean : ∀ (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) ≤ 1),
      |(edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (fun ω => ((uncovF 𝓖 ω).card : ℝ))
        - Real.exp (-θ) * (Fintype.card V : ℝ)| ≤ δ * (Fintype.card V : ℝ) / 2 := by
    intro hp0 hp1
    rw [edgeMeasure_exp_congr 𝓖 hp0 hp1 hp0c hp1c]
    exact r2_Y_mean 𝓖 hθ0 hθ1 hδ0 hε0 hεδ hD8 hp0c hp1c hθD hbig hdeg
  have hSmean : ∀ (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) ≤ 1),
      (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (fun ω => ((collMult 𝓖 ω : ℕ) : ℝ))
        ≤ (1 + δ / 2) * (θ - θ * Real.exp (-θ)) * (Fintype.card V : ℝ) := by
    intro hp0 hp1
    rw [edgeMeasure_exp_congr 𝓖 hp0 hp1 hp0c hp1c]
    exact r2_S_mean 𝓖 hθ0 hθ1 hδ0 hδ1 hε0 hε1 hεδ hD8 hp0c hp1c hθD hbig hdeg
  have hYfammean : ∀ (S : Finset V) (hS : S ∈ 𝓕)
      (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) ≤ 1),
      |(edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (fun ω => ((uncovFam 𝓖 ω S : ℕ) : ℝ))
        - Real.exp (-θ) * (S.card : ℝ)| ≤ δ * (S.card : ℝ) / 2 := by
    intro S hS hp0 hp1
    rw [edgeMeasure_exp_congr 𝓖 hp0 hp1 hp0c hp1c]
    exact r2_Yfam_mean hθ0 hθ1 hδ0 hε0 hεδ hD8 hp0c hp1c hθD hbig hdeg S
  have hWfammean : ∀ (S : Finset V) (hS : S ∈ 𝓕)
      (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) ≤ 1),
      (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (fun ω => ((badSum 𝓖 ω S : ℕ) : ℝ))
        ≤ 2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ) := by
    intro S hS hp0 hp1
    rw [edgeMeasure_exp_congr 𝓖 hp0 hp1 hp0c hp1c]
    exact r2_Wfam_mean hr hu hθ0 hε0 (by linarith : ε ≤ 1 / 100) hD8 hp0c hp1c hdeg S
  -- the uncovered tail
  have hYfamtail : ∀ (S : Finset V) (hS : S ∈ 𝓕)
      (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) ≤ 1),
      (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).prob
        {ω : 𝓖 → Bool | δ / 2 * (S.card : ℝ) ≤ ((uncovFam 𝓖 ω S : ℕ) : ℝ)
          - (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp
              (fun ω => ((uncovFam 𝓖 ω S : ℕ) : ℝ))}
        ≤ 4 * Real.exp (- δ ^ 2 * (S.card : ℝ) / (64 * (r : ℝ) ^ 2)) := by
    intro S hS hp0 hp1
    obtain ⟨h1, h2, h3, h4⟩ := hlarge S hS
    have hSpos : 0 < (S.card : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) S.card
      nlinarith [h3, hθ0, hrR, this]
    have hset : {ω : 𝓖 → Bool | δ / 2 * (S.card : ℝ) ≤ ((uncovFam 𝓖 ω S : ℕ) : ℝ)
          - (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp
              (fun ω => ((uncovFam 𝓖 ω S : ℕ) : ℝ))}
        = {ω : 𝓖 → Bool | δ / 2 * (S.card : ℝ) ≤ ((uncovFam 𝓖 ω S : ℕ) : ℝ)
          - (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0c hp1c).exp
              (fun ω => ((uncovFam 𝓖 ω S : ℕ) : ℝ))} := by
      rw [edgeMeasure_exp_congr 𝓖 hp0 hp1 hp0c hp1c]
    rw [edgeMeasure_prob_congr 𝓖 hp0 hp1 hp0c hp1c, hset]
    have htail := r2_Yfam_tail 𝓖 hr hu hθ0 hD1 hp0c hp1c' S h3
    have heq : - (δ * (S.card : ℝ) / 2) ^ 2 / (16 * (r : ℝ) ^ 2 * (S.card : ℝ))
        = - δ ^ 2 * (S.card : ℝ) / (64 * (r : ℝ) ^ 2) := by
      field_simp
      ring
    rw [heq] at htail
    have hsub : {ω : 𝓖 → Bool | δ / 2 * (S.card : ℝ) ≤ ((uncovFam 𝓖 ω S : ℕ) : ℝ)
          - (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0c hp1c).exp
              (fun ω => ((uncovFam 𝓖 ω S : ℕ) : ℝ))}
        ⊆ {ω : 𝓖 → Bool | δ * (S.card : ℝ) / 2
          ≤ |((uncovFam 𝓖 ω S : ℕ) : ℝ)
            - (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0c hp1c).exp
                (fun ω => ((uncovFam 𝓖 ω S : ℕ) : ℝ))|} := by
      intro ω hω
      rw [Set.mem_ofPred_eq] at hω ⊢
      have h2' : δ / 2 * (S.card : ℝ) = δ * (S.card : ℝ) / 2 := by ring
      rw [h2'] at hω
      exact le_trans hω (le_abs_self _)
    exact le_trans (FinProb.prob_mono _ hsub) htail
  -- the waste tail
  have hWfamtail : ∀ (S : Finset V) (hS : S ∈ 𝓕)
      (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) ≤ 1),
      (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).prob
        {ω : 𝓖 → Bool | (1 + δ) * (2 * (r : ℝ) * θ ^ 2) * (S.card : ℝ)
          < ((badSum 𝓖 ω S : ℕ) : ℝ)}
        ≤ 16 * Real.exp (-(θ ^ 3 * δ ^ 2 * (S.card : ℝ)) / (2048 * (r : ℝ) ^ 2)) := by
    intro S hS hp0 hp1
    obtain ⟨h1, h2, h3, h4⟩ := hlarge S hS
    rw [edgeMeasure_prob_congr 𝓖 hp0 hp1 hp0c hp1c]
    set A : ℝ := θ ^ 3 * δ ^ 2 * (S.card : ℝ) / (2048 * (r : ℝ) ^ 2) with hA
    have hw0 : ∀ e : 𝓖, 0 ≤ (((e : Set V) ∩ (S : Set V)).ncard : ℝ) :=
      fun e => Nat.cast_nonneg _
    have hwr : ∀ e : 𝓖, (((e : Set V) ∩ (S : Set V)).ncard : ℝ) ≤ (r : ℝ) := by
      intro e
      have h5 : ((e : Set V) ∩ (S : Set V)).ncard ≤ (e : Set V).ncard :=
        Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _)
      have h6 : (e : Set V).ncard = r := hu (e : Set V) e.2
      exact_mod_cast (by omega : ((e : Set V) ∩ (S : Set V)).ncard ≤ r)
    have hZcast : ∀ ω : 𝓖 → Bool, ((Zsum 𝓖 ω S : ℕ) : ℝ)
        = ∑ e : 𝓖, (if ω e then (((e : Set V) ∩ (S : Set V)).ncard : ℝ) else 0) := by
      intro ω
      rw [Zsum, Nat.cast_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases h : ω e <;> simp [h]
    have hmu : (∑ e : 𝓖, (θ / (D : ℝ)) * (((e : Set V) ∩ (S : Set V)).ncard : ℝ))
        ≤ 2 * θ * (S.card : ℝ) := by
      have hsum : (∑ e : 𝓖, (((e : Set V) ∩ (S : Set V)).ncard : ℝ))
          = ∑ v ∈ S, (hd 𝓖 v : ℝ) := sum_ncard_inter_eq_sum_hd 𝓖 S
      have hle : ∑ v ∈ S, (hd 𝓖 v : ℝ) ≤ ∑ _v ∈ S, ((1 + ε) * (D : ℝ)) := by
        refine Finset.sum_le_sum fun v _ => ?_
        have h := hdeg v
        rw [abs_le] at h
        linarith [h.2]
      have hcard : ∑ _v ∈ S, ((1 + ε) * (D : ℝ)) = (S.card : ℝ) * ((1 + ε) * (D : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      have hpD : (θ / (D : ℝ)) * (D : ℝ) = θ := div_mul_cancel₀ θ (ne_of_gt hDpos)
      calc (∑ e : 𝓖, (θ / (D : ℝ)) * (((e : Set V) ∩ (S : Set V)).ncard : ℝ))
          = (θ / (D : ℝ)) * ∑ e : 𝓖, (((e : Set V) ∩ (S : Set V)).ncard : ℝ) := by
            rw [Finset.mul_sum]
        _ = (θ / (D : ℝ)) * ∑ v ∈ S, (hd 𝓖 v : ℝ) := by rw [hsum]
        _ ≤ (θ / (D : ℝ)) * ((S.card : ℝ) * ((1 + ε) * (D : ℝ))) :=
              mul_le_mul_of_nonneg_left (le_trans hle (le_of_eq hcard)) (by positivity)
        _ = θ * (1 + ε) * (S.card : ℝ) := by
              field_simp
        _ ≤ 2 * θ * (S.card : ℝ) := by
              have := Nat.cast_nonneg (α := ℝ) S.card
              nlinarith [hθ0, hεle1]
    have hexc : (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0c hp1c).prob
        {ω : 𝓖 → Bool | 4 * θ * (S.card : ℝ) < ((Zsum 𝓖 ω S : ℕ) : ℝ)}
        ≤ Real.exp (-A) := by
      have hZ := weighted_chernoff_up 𝓖 hp0c hp1c (le_of_lt hrR)
        (fun e : 𝓖 => (((e : Set V) ∩ (S : Set V)).ncard : ℝ)) hw0 hwr
        (t := 2 * θ * (S.card : ℝ)) (by positivity)
      have hsub : {ω : 𝓖 → Bool | 4 * θ * (S.card : ℝ) < ((Zsum 𝓖 ω S : ℕ) : ℝ)}
          ⊆ {ω : 𝓖 → Bool | 2 * θ * (S.card : ℝ)
              ≤ (∑ e : 𝓖, (if ω e then (((e : Set V) ∩ (S : Set V)).ncard : ℝ) else 0))
                - ∑ e : 𝓖, (θ / (D : ℝ)) * (((e : Set V) ∩ (S : Set V)).ncard : ℝ)} := by
        intro ω hω
        rw [Set.mem_ofPred_eq] at hω ⊢
        rw [hZcast ω] at hω
        linarith [hω, hmu]
      have hY1 : 2 * (r : ℝ) * ((∑ e : 𝓖,
              (θ / (D : ℝ)) * (((e : Set V) ∩ (S : Set V)).ncard : ℝ))
            + 2 * θ * (S.card : ℝ) / 3)
          ≤ 2 * (r : ℝ) * (2 * θ * (S.card : ℝ) + 2 * θ * (S.card : ℝ) / 3) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith [hmu]
      have hY2 : (2 * θ * (S.card : ℝ)) ^ 2
            / (2 * (r : ℝ) * (2 * θ * (S.card : ℝ) + 2 * θ * (S.card : ℝ) / 3))
          = 3 * θ * (S.card : ℝ) / (4 * (r : ℝ)) := by
        have hSn : θ * (S.card : ℝ) ≠ 0 := by
          have := Nat.cast_nonneg (α := ℝ) S.card
          nlinarith [hθ0, h1]
        field_simp
        ring
      have hkey : A + Real.log 2 ≤ 3 * θ * (S.card : ℝ) / (4 * (r : ℝ)) := by
        rw [hA]
        have hlog2 : Real.log 2 ≤ 3 / 4 := by
          have := Real.log_two_lt_d9
          linarith
        have hA2 : θ ^ 3 * δ ^ 2 * (S.card : ℝ) / (2048 * (r : ℝ) ^ 2)
            ≤ 3 * θ * (S.card : ℝ) / (8 * (r : ℝ)) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hSc : 0 < (S.card : ℝ) := by
            rcases Nat.eq_zero_or_pos S.card with h0 | h0
            · exfalso
              have hz : (S.card : ℝ) = 0 := by exact_mod_cast h0
              rw [hz] at h3
              simp at h3
            · exact_mod_cast h0
          have hSn : 0 < θ * (S.card : ℝ) := mul_pos hθ0 hSc
          have hfac : 8 * θ ^ 2 * δ ^ 2 * (r : ℝ) ≤ 6144 * (r : ℝ) ^ 2 := by
            have h1' : 8 * θ ^ 2 * δ ^ 2 ≤ 6144 * (r : ℝ) := by
              have h2' : (8 : ℝ) ≤ 6144 * (r : ℝ) := by nlinarith [hr2R]
              nlinarith [hθδle, h2']
            have h3' := mul_le_mul_of_nonneg_right h1' (le_of_lt hrR)
            nlinarith [h3']
          have hmul' := mul_le_mul_of_nonneg_left hfac (le_of_lt hSn)
          nlinarith [hmul']
        have h3' : 3 / 4 ≤ 3 * θ * (S.card : ℝ) / (8 * (r : ℝ)) := by
          rw [le_div_iff₀ (by positivity)]
          nlinarith [h1, hrR]
        have hsum'' : 3 * θ * (S.card : ℝ) / (8 * (r : ℝ))
              + 3 * θ * (S.card : ℝ) / (8 * (r : ℝ))
            = 3 * θ * (S.card : ℝ) / (4 * (r : ℝ)) := by ring
        linarith [hA2, h3', hlog2, hsum'']
      have hY3 : (2 * θ * (S.card : ℝ)) ^ 2
            / (2 * (r : ℝ) * (2 * θ * (S.card : ℝ) + 2 * θ * (S.card : ℝ) / 3))
          = 3 * θ * (S.card : ℝ) / (4 * (r : ℝ)) := hY2
      have hpos : 0 < 2 * (r : ℝ) * ((∑ e : 𝓖,
            (θ / (D : ℝ)) * (((e : Set V) ∩ (S : Set V)).ncard : ℝ))
          + 2 * θ * (S.card : ℝ) / 3) := by
        have hSn : 0 ≤ θ * (S.card : ℝ) := by
          have := Nat.cast_nonneg (α := ℝ) S.card
          positivity
        have hsum0 : 0 ≤ ∑ e : 𝓖, (θ / (D : ℝ)) * (((e : Set V) ∩ (S : Set V)).ncard : ℝ) := by
          refine Finset.sum_nonneg fun e _ => ?_
          exact mul_nonneg (by positivity) (Nat.cast_nonneg _)
        nlinarith [hrR, hSn, hsum0, hθ0]
      have hmono : (2 * θ * (S.card : ℝ)) ^ 2
            / (2 * (r : ℝ) * ((∑ e : 𝓖,
                (θ / (D : ℝ)) * (((e : Set V) ∩ (S : Set V)).ncard : ℝ))
              + 2 * θ * (S.card : ℝ) / 3))
          ≥ 3 * θ * (S.card : ℝ) / (4 * (r : ℝ)) := by
        rw [ge_iff_le, div_le_div_iff₀ (by positivity) hpos]
        nlinarith [(2 * θ * (S.card : ℝ)) ^ 2, hY1, hY2]
      have hexp2 : 2 * Real.exp (- (2 * θ * (S.card : ℝ)) ^ 2
            / (2 * (r : ℝ) * ((∑ e : 𝓖,
                (θ / (D : ℝ)) * (((e : Set V) ∩ (S : Set V)).ncard : ℝ))
              + 2 * θ * (S.card : ℝ) / 3)))
          ≤ Real.exp (-A) := by
        have hmono' : 3 * θ * (S.card : ℝ) / (4 * (r : ℝ))
            ≤ (2 * θ * (S.card : ℝ)) ^ 2
              / (2 * (r : ℝ) * ((∑ e : 𝓖,
                  (θ / (D : ℝ)) * (((e : Set V) ∩ (S : Set V)).ncard : ℝ))
                + 2 * θ * (S.card : ℝ) / 3)) := hmono
        have key : Real.log 2 + (-(2 * θ * (S.card : ℝ)) ^ 2
              / (2 * (r : ℝ) * ((∑ e : 𝓖,
                  (θ / (D : ℝ)) * (((e : Set V) ∩ (S : Set V)).ncard : ℝ))
                + 2 * θ * (S.card : ℝ) / 3))) ≤ -A := by
          have hneg : (-(2 * θ * (S.card : ℝ)) ^ 2
                / (2 * (r : ℝ) * ((∑ e : 𝓖,
                    (θ / (D : ℝ)) * (((e : Set V) ∩ (S : Set V)).ncard : ℝ))
                  + 2 * θ * (S.card : ℝ) / 3)))
              = -((2 * θ * (S.card : ℝ)) ^ 2
                / (2 * (r : ℝ) * ((∑ e : 𝓖,
                    (θ / (D : ℝ)) * (((e : Set V) ∩ (S : Set V)).ncard : ℝ))
                  + 2 * θ * (S.card : ℝ) / 3))) := by ring
          rw [hneg]
          linarith [le_trans hkey hmono']
        calc 2 * Real.exp (-(2 * θ * (S.card : ℝ)) ^ 2
              / (2 * (r : ℝ) * ((∑ e : 𝓖,
                  (θ / (D : ℝ)) * (((e : Set V) ∩ (S : Set V)).ncard : ℝ))
                + 2 * θ * (S.card : ℝ) / 3)))
            = Real.exp (Real.log 2 + (-(2 * θ * (S.card : ℝ)) ^ 2
              / (2 * (r : ℝ) * ((∑ e : 𝓖,
                  (θ / (D : ℝ)) * (((e : Set V) ∩ (S : Set V)).ncard : ℝ))
                + 2 * θ * (S.card : ℝ) / 3)))) := by
              rw [Real.exp_add, Real.exp_log (by norm_num)]
          _ ≤ Real.exp (-A) := Real.exp_le_exp.mpr key
      calc (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0c hp1c).prob
            {ω : 𝓖 → Bool | 4 * θ * (S.card : ℝ) < ((Zsum 𝓖 ω S : ℕ) : ℝ)}
          ≤ (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0c hp1c).prob
              {ω : 𝓖 → Bool | 2 * θ * (S.card : ℝ)
                ≤ (∑ e : 𝓖, (if ω e then (((e : Set V) ∩ (S : Set V)).ncard : ℝ) else 0))
                  - ∑ e : 𝓖, (θ / (D : ℝ)) * (((e : Set V) ∩ (S : Set V)).ncard : ℝ)} :=
            FinProb.prob_mono _ hsub
        _ ≤ 2 * Real.exp (- (2 * θ * (S.card : ℝ)) ^ 2
              / (2 * (r : ℝ) * ((∑ e : 𝓖,
                  (θ / (D : ℝ)) * (((e : Set V) ∩ (S : Set V)).ncard : ℝ))
                + 2 * θ * (S.card : ℝ) / 3))) := hZ
        _ ≤ Real.exp (-A) := hexp2
    have hexcM : Real.exp (-A) ≤ 1 / (2 * (D : ℝ) * (S.card : ℝ) + 1) ^ 2 := by
      have hM : (0 : ℝ) < 2 * (D : ℝ) * (S.card : ℝ) + 1 := by positivity
      have h4' : 2 * Real.log (2 * (D : ℝ) * (S.card : ℝ) + 1)
          ≤ θ ^ 3 * δ ^ 2 * (S.card : ℝ) / (2048 * (r : ℝ) ^ 2) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [h4]
      have h5 : -A ≤ -(2 * Real.log (2 * (D : ℝ) * (S.card : ℝ) + 1)) := by
        rw [hA]
        linarith [h4']
      have h6 : Real.exp (2 * Real.log (2 * (D : ℝ) * (S.card : ℝ) + 1))
          = (2 * (D : ℝ) * (S.card : ℝ) + 1) ^ 2 := by
        rw [show (2 : ℝ) * Real.log (2 * (D : ℝ) * (S.card : ℝ) + 1)
            = ((2 : ℕ) : ℝ) * Real.log (2 * (D : ℝ) * (S.card : ℝ) + 1) by norm_num]
        rw [Real.exp_nat_mul, Real.exp_log hM]
      calc Real.exp (-A) ≤ Real.exp (-(2 * Real.log (2 * (D : ℝ) * (S.card : ℝ) + 1))) :=
            Real.exp_le_exp.mpr h5
        _ = 1 / (2 * (D : ℝ) * (S.card : ℝ) + 1) ^ 2 := by
            rw [Real.exp_neg, h6]
            ring
    have htail := r2_Wfam_tail 𝓖 (by omega : 1 ≤ r) hu hθ0 hθle1 hδ0 hδle1 hε0 hεle1 hD1 hp0c hp1c'
      hdeg S (hWfammean S hS hp0c hp1c) (exc := Real.exp (-A)) hexc hexcM h2
    have hA0 : 0 ≤ A := by
      rw [hA]
      have := Nat.cast_nonneg (α := ℝ) S.card
      positivity
    have hfin : 4 * Real.exp (-(θ ^ 3 * δ ^ 2 * (S.card : ℝ)) / (512 * (r : ℝ) ^ 2))
          + 4 * Real.exp (-A)
        ≤ 16 * Real.exp (-A) := by
      have h1' : - (θ ^ 3 * δ ^ 2 * (S.card : ℝ)) / (512 * (r : ℝ) ^ 2) = -4 * A := by
        rw [hA]; ring
      rw [h1']
      have h2' : Real.exp (-4 * A) ≤ Real.exp (-A) := by
        refine Real.exp_le_exp.mpr ?_
        linarith
      have h3'' : (0:ℝ) ≤ Real.exp (-A) := Real.exp_nonneg _
      linarith [h2', h3'']
    have hthis : -(θ ^ 3 * δ ^ 2 * (S.card : ℝ)) / (2048 * (r : ℝ) ^ 2) = -A := by
      rw [hA]; ring
    rw [hthis]
    exact le_trans htail hfin
  exact hassm (V := V) 𝓖 D 𝓕 hD0 hDV hl hu hdeg hWvmean hYmean hSmean hYfammean
    hYfamtail hWfamtail (fun _ _ => hLLL) (fun _ _ => hroom)


end Work.Deep.Nibble
