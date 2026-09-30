import Mathlib
import Submission.Work.BMF.SD.sd3_defs
import Submission.Work.BMF.SD.tk_bad_weight
import Submission.Work.BMF.SD.sum_inv_primesIn_ge
import Submission.Work.BMF.Defs
import Submission.Work.BMF.SD.window_helpers
import Submission.Work.BMF.SD.geo_window_mass_lower2
import Submission.Work.BMF.SD.window_sums_le_two
import Submission.Work.BMF.SD.goodPairs_card_eq_sum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 4000000

namespace Work.BMF.SD

open Classical Polynomial Finset Real Complex
open BoundedMultiplicativeFunctions

/-- **The prime-window counting step of scaling down.**  There are constants `c₁ > 0` and `A` such
that for every `1`-bounded multiplicative `f`, every admissible datum `(X,H,P,Q)` with
`A ≤ log Q / log P`, and every `(X,H)`-phase family `F` of constant `c₀`, one can find a *narrow*
prime window `[a,b]` (`a ≥ P`, `a ≤ b`, `5b ≤ 7a`, `b ≤ Q`) carrying `≥ c₁ (X/H) π₀(a)` *good
pairs*: pairs `(y,p) ∈ F.fam × [a,b]`, `p` prime, whose rescaled phase correlates at level `c₀/2`:
`(c₀/2)(H/p) ≤ ‖corr f (p_* φ_y) (y/p) (H/p)‖`.

Route (all ingredients already in the workspace):
* `Work.BMF.SD.tk_bad_weight` gives `Σ_{p ∈ primesIn P Q} (1/p) · #{y ∈ F.fam : y bad at p} ≤ K·#F.fam`
  with `K ≤ 3200/c₀² + 64/c₀ + 8`, where `bad` is the negation of the displayed correlation bound;
* partition `[P, 5Q/7]` by the geometric windows `W_j = primesIn (P r^j) (P r^(j+1))`, `r = 7/5`
  (so `5·(P r^(j+1)) = 7·(P r^j)`); every prime of `[P,5Q/7]` lies in such a window, its index is
  unique up to the endpoints, and the upper ends satisfy `P r^(j+1) ≤ Q`;
* restrict to the windows with `a_j := P r^j ≥ 10¹⁰`, so that `Work.BMF.window_weights` supplies
  `β/log a_j ≤ Σ_{p∈W_j} 1/p` and `β' π₀(a_j) ≤ #(primesIn a_j (7a_j/5))`; use Mertens
  (`Work.BMF.SD.sum_inv_primesIn_ge`) to lower-bound the total mass of that restricted range by
  `log A − C`;
* call a window *bad* if its bad mass exceeds half of its mass; the bad windows have total mass
  `< 4K·#F.fam`, so the good ones retain `≥ #F.fam·(log A/2) > 0` of the mass, in particular one
  good window `W_{j₀}` of the restricted range exists, and every window of that range has mass
  `≥ β/log a_j`;
* for that window, `Σ_{p∈W} #good(p) ≥ (5/7)·a·(mass of W)·(1/2) ≥ (7β/20)·#F.fam·π₀(a)`, and
  `#F.fam ≥ c₀ X/H`.
Take `c₁ = c₀/100` and `A = exp(10 K)`.

## The constants actually produced by the proof below

## The constants actually produced by the proof below

With `K` from `Work.BMF.SD.tk_bad_weight`, `(β, β', A_w)` from `Work.BMF.window_weights` and
`C_M` from `Work.BMF.SD.sum_inv_primesIn_ge`, the proof takes `c₁ = β c₀ / 4` and
`A = exp (10K + C_M + 100) + ((log T + 2) exp (4K + C_M + 1) + 2)/log 2`, where `T = max A_w 1`; the
window threshold `A_w` of the prime-number-theorem-in-windows lemma enters `A` only through the
factor `log T`, so no explicit bound on `A_w` is needed.  The geometric range produced by
`Work.BMF.SD.geo_window_mass_lower2` starts at `a_{j₀} = P (7/5)^{j₀} ≥ T ≥ A_w` and ends at
`a_N = P (7/5)^N ≤ Q`, and the total reciprocal-prime mass of its windows is at least `4K`.

The good window is then produced by a weighted pigeonhole: a window is *bad* when its bad mass (the
`1/p`-weighted mass of the sources that fail the correlation bound at `p`) exceeds half of its total
mass `m_j = Σ_{p ∈ W_j} 1/p`.  Since every prime lies in at most two of the windows
(`Work.BMF.SD.window_sums_le_two`) and `Σ_{p ∈ [P,Q]} (1/p)·#{bad sources at p} ≤ K·#F.fam`
(`Work.BMF.SD.tk_bad_weight`), the bad windows carry at most `2K·#F.fam` of bad mass, while
`Σ_j m_j ≥ 4K`; hence some window is good, and for it
`Σ_{p ∈ W_j} #good(p) ≥ a_j · (1/2)·#F.fam · m_j ≥ (β/2)·#F.fam·π₀(a_j) ≥ (β c₀/2)(X/H)π₀(a_j)`,
using `m_j ≥ β/log a_j` (`Work.BMF.window_weights`, applicable since `a_j ≥ A_w`) and
`#F.fam ≥ c₀ X/H`.
-/

theorem good_window_pairs (k : ℕ) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ c₁ A : ℝ, 0 < c₁ ∧ 0 < A ∧
      ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) →
      ∀ (hmul : ∀ m n, Nat.Coprime m n → f (m * n) = f m * f n),
      ∀ (X H P Q : ℝ), 2 ≤ P → P ≤ Q → Q ^ 3 ≤ H → H ≤ X →
        A ≤ Real.log Q / Real.log P →
      ∀ (F : Work.BMF.PhaseFamily k f c₀ X H),
      ∃ a b : ℝ, P ≤ a ∧ a ≤ b ∧ 5 * b ≤ 7 * a ∧ b ≤ Q ∧
        c₁ * (X / H) * Work.BMF.pi0 a ≤
          ((Work.BMF.goodPairs f F.pol (c₀ / 2) H a b F.fam).card : ℝ) := by
  obtain ⟨K, hKpos, hKle, hTK⟩ := tk_bad_weight k c₀ hc₀
  obtain ⟨β, β', Aw, hβpos, hβ'pos, hAwpos, hww⟩ := window_weights
  obtain ⟨CM, hCM0, hMert⟩ := sum_inv_primesIn_ge
  set T : ℝ := max Aw 1 with hTdef
  have hT1 : 1 ≤ T := le_max_right _ _
  have hAwT : Aw ≤ T := le_max_left _ _
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hEpos : 0 < Real.exp (4 * K + CM + 1) := Real.exp_pos _
  set A₀ : ℝ := Real.exp (10 * K + CM + 100) with hA₀def
  set A₂ : ℝ := ((Real.log T + 2) * Real.exp (4 * K + CM + 1) + 2) / Real.log 2 with hA₂def
  have hA₂pos : 0 < A₂ := by
    rw [hA₂def]
    exact div_pos (by nlinarith [hEpos, hlogT0]) hlog2pos
  refine ⟨β * c₀ / 4, A₀ + A₂, by positivity, by positivity, ?_⟩
  intro f hf hmul X H P Q h2P hPQ hQ3 hHX hA F
  have hQ2 : (2 : ℝ) ≤ Q := le_trans h2P hPQ
  have hQpos : 0 < Q := by linarith
  have hPpos : 0 < P := by linarith
  have hP1 : 1 < P := by linarith
  have hlogPpos : 0 < Real.log P := Real.log_pos hP1
  have hlogQpos : 0 < Real.log Q := Real.log_pos (by linarith)
  have hlogPge : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) h2P
  have h8 : (8 : ℝ) ≤ Q ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hQ2 3
    norm_num at h
    exact h
  have hHpos : 0 < H := lt_of_lt_of_le (by norm_num) (le_trans h8 hQ3)
  have hXpos : 0 < X := lt_of_lt_of_le hHpos hHX
  have hTpos : 0 < X / H := div_pos hXpos hHpos
  have hAle : A₀ + A₂ ≤ Real.log Q / Real.log P := hA
  have hAlogP : (A₀ + A₂) * Real.log P ≤ Real.log Q := by
    have h := mul_le_mul_of_nonneg_right hAle hlogPpos.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hlogPpos)] at h
  have hE_le_A₀ : Real.exp (4 * K + CM + 1) ≤ A₀ := by
    rw [hA₀def]
    apply Real.exp_le_exp.mpr
    linarith
  have hA₂eq : A₂ * Real.log 2 = (Real.log T + 2) * Real.exp (4 * K + CM + 1) + 2 := by
    rw [hA₂def]
    field_simp
  -- the hypothesis of the window-mass lemma
  have hHyp : Real.exp (4 * K + CM + 1) * (Real.log P + Real.log T + 2) + 2 ≤ Real.log Q := by
    have h1 : Real.exp (4 * K + CM + 1) * Real.log P ≤ A₀ * Real.log P :=
      mul_le_mul_of_nonneg_right hE_le_A₀ hlogPpos.le
    have h2 : (Real.log T + 2) * Real.exp (4 * K + CM + 1) + 2 ≤ A₂ * Real.log P := by
      rw [← hA₂eq]
      exact mul_le_mul_of_nonneg_left hlogPge hA₂pos.le
    have h3 : Real.exp (4 * K + CM + 1) * (Real.log P + Real.log T + 2) + 2
        = Real.exp (4 * K + CM + 1) * Real.log P
          + ((Real.log T + 2) * Real.exp (4 * K + CM + 1) + 2) := by ring
    rw [h3]
    calc Real.exp (4 * K + CM + 1) * Real.log P
          + ((Real.log T + 2) * Real.exp (4 * K + CM + 1) + 2)
        ≤ A₀ * Real.log P + A₂ * Real.log P := add_le_add h1 h2
      _ = (A₀ + A₂) * Real.log P := by ring
      _ ≤ Real.log Q := hAlogP
  -- the datum is admissible for the geometric windows
  have hA2le : (2 : ℝ) ≤ A₀ + A₂ := by
    have h2 : (2 : ℝ) ≤ A₀ := by
      rw [hA₀def]
      have hlog2 : Real.log 2 ≤ 10 * K + CM + 100 := by
        have := Real.log_two_lt_d9
        linarith
      exact (Real.log_le_iff_le_exp (x := 2) (y := 10 * K + CM + 100) (by norm_num)).mp hlog2
    linarith [h2, hA₂pos.le]
  have hlogQ2 : 2 * Real.log P ≤ Real.log Q := by
    have h := mul_le_mul_of_nonneg_right hA2le hlogPpos.le
    have h' : 2 * Real.log P ≤ (A₀ + A₂) * Real.log P := by linarith
    linarith [h, h', hAlogP]
  have hP2Q : P ^ 2 ≤ Q := by
    have h : Real.log (P ^ 2) ≤ Real.log Q := by
      rw [Real.log_pow]
      push_cast
      linarith
    exact (Real.log_le_log_iff (by positivity) hQpos).mp h
  have hPQ2 : 7 * P ≤ 5 * Q := by nlinarith [hP2Q, h2P]
  obtain ⟨N, j₀, hjN, hTle, hPle, hbQ, hmass⟩ :=
    geo_window_mass_lower2 P Q T K CM h2P hPQ hPQ2 hT1 hKpos hMert hHyp
  -- the family is nonempty
  have hNge : c₀ * (X / H) ≤ (F.fam.card : ℝ) := F.card_ge
  have hNpos : 0 < (F.fam.card : ℝ) := lt_of_lt_of_le (mul_pos hc₀ hTpos) hNge
  -- the good/bad sets
  let Good : ℕ → Finset ℝ := fun p =>
    F.fam.filter (fun y => (c₀ / 2) * (H / (p : ℝ)) ≤
      ‖corr f (dil (p : ℝ) (F.pol y)) (y / (p : ℝ)) (H / (p : ℝ))‖)
  let Bad : ℕ → Finset ℝ := fun p =>
    F.fam.filter (fun y => ¬ ((c₀ / 2) * (H / (p : ℝ)) ≤
      ‖corr f (dil (p : ℝ) (F.pol y)) (y / (p : ℝ)) (H / (p : ℝ))‖))
  let W : ℕ → Finset ℕ := fun j => primesIn (P * (7 / 5) ^ j) (P * (7 / 5) ^ (j + 1))
  let m : ℕ → ℝ := fun j => ∑ p ∈ W j, (1 : ℝ) / (p : ℝ)
  let gd : ℕ → ℝ := fun j => ∑ p ∈ W j, (1 / (p : ℝ)) * ((Good p).card : ℝ)
  let bd : ℕ → ℝ := fun j => ∑ p ∈ W j, (1 / (p : ℝ)) * ((Bad p).card : ℝ)
  set J : Finset ℕ := Finset.Icc j₀ (N - 1) with hJdef
  have hj₀mem : j₀ ∈ J := by
    rw [hJdef]
    exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hJne : J.Nonempty := ⟨j₀, hj₀mem⟩
  -- (1) each window carries at least `β / log a_j`
  have hF1 : ∀ j ∈ J, β / Real.log (P * (7 / 5) ^ j) ≤ m j := by
    intro j hj
    have haj : Aw ≤ P * (7 / 5) ^ j := le_trans hAwT (hTle j hj)
    have hwin := (hww (P * (7 / 5) ^ j) haj).1
    have heq : 7 * (P * (7 / 5) ^ j) / 5 = P * (7 / 5) ^ (j + 1) := by
      rw [pow_succ]
      ring
    rw [heq] at hwin
    exact hwin
  -- (2) the two mass identities, prime by prime
  have hcardGb : ∀ p : ℕ, ((Good p).card : ℝ) + ((Bad p).card : ℝ) = (F.fam.card : ℝ) := by
    intro p
    have h := Finset.card_filter_add_card_filter_not (s := F.fam)
      (p := fun y => (c₀ / 2) * (H / (p : ℝ)) ≤
        ‖corr f (dil (p : ℝ) (F.pol y)) (y / (p : ℝ)) (H / (p : ℝ))‖)
    simp only [Good, Bad]
    exact_mod_cast h
  have hF2 : ∀ j : ℕ, gd j + bd j = (F.fam.card : ℝ) * m j := by
    intro j
    simp only [gd, bd, m]
    rw [← Finset.sum_add_distrib]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have h := hcardGb p
    rw [← h]
    ring
  -- (3) the bad mass is at most `2 K #fam`
  have hF3 : ∑ j ∈ J, bd j ≤ 2 * K * (F.fam.card : ℝ) := by
    have hsub : ∀ j ∈ J,
        primesIn (P * (7 / 5) ^ j) (P * (7 / 5) ^ (j + 1)) ⊆ primesIn P Q := by
      intro j hj
      exact primesIn_mono (hPle j hj) (hbQ j hj)
    have hws := window_sums_le_two P hPpos J (primesIn P Q)
      (fun p => (1 / (p : ℝ)) * ((Bad p).card : ℝ))
      (fun p => by positivity) hsub
    have hTK' : ∑ p ∈ primesIn P Q, (1 / (p : ℝ)) * ((Bad p).card : ℝ)
        ≤ K * (F.fam.card : ℝ) := by
      refine le_trans (le_of_eq ?_) (hTK f hf hmul X H P Q h2P hPQ hQ3 hHX F)
      apply Finset.sum_congr rfl
      intro p hp
      congr 1
    simp only [bd] at hws ⊢
    linarith [hws, hTK']
  -- (4) the windows carry `4K` of mass
  have hF4 : 4 * K ≤ ∑ j ∈ J, m j := by
    rw [hJdef]
    simp only [m]
    exact hmass
  -- (5) pigeonhole: some window is good
  have hF5 : ∃ j ∈ J, (1 / 2) * (F.fam.card : ℝ) * m j ≤ gd j := by
    by_contra hcon
    push_neg at hcon
    have hlt : (1 / 2) * (F.fam.card : ℝ) * ∑ j ∈ J, m j < ∑ j ∈ J, bd j := by
      rw [Finset.mul_sum]
      apply Finset.sum_lt_sum_of_nonempty hJne
      intro j hj
      have h2 := hF2 j
      have h3 := hcon j hj
      linarith
    have hge : 2 * K * (F.fam.card : ℝ) ≤ (1 / 2) * (F.fam.card : ℝ) * ∑ j ∈ J, m j := by
      have h := mul_le_mul_of_nonneg_left hF4 (by positivity : (0 : ℝ) ≤ (1 / 2) * (F.fam.card : ℝ))
      linarith
    linarith [hF3, hlt, hge]
  obtain ⟨j, hjJ, hgood⟩ := hF5
  -- the extraction
  have haP : P ≤ P * (7 / 5) ^ j := hPle j hjJ
  have hbQj : P * (7 / 5) ^ (j + 1) ≤ Q := hbQ j hjJ
  have hapos : 0 < P * (7 / 5) ^ j := by positivity
  have ha1 : 1 < P * (7 / 5) ^ j := by
    have h := mul_le_mul_of_nonneg_left (one_le_seven_fifths_pow j) hPpos.le
    linarith [hP1]
  have hlogapos : 0 < Real.log (P * (7 / 5) ^ j) := Real.log_pos ha1
  have hab : P * (7 / 5) ^ j ≤ P * (7 / 5) ^ (j + 1) := by
    have hpow : (7 / 5 : ℝ) ^ j ≤ (7 / 5) ^ (j + 1) :=
      pow_le_pow_right₀ (by norm_num) (Nat.le_succ j)
    exact mul_le_mul_of_nonneg_left hpow hPpos.le
  have h57 : 5 * (P * (7 / 5) ^ (j + 1)) ≤ 7 * (P * (7 / 5) ^ j) := by
    have heq : 5 * (P * (7 / 5) ^ (j + 1)) = 7 * (P * (7 / 5) ^ j) := by
      rw [pow_succ]
      ring
    linarith
  -- the pairs of the window, counted prime by prime
  have hcard : ((goodPairs f F.pol (c₀ / 2) H (P * (7 / 5) ^ j) (P * (7 / 5) ^ (j + 1))
        F.fam).card : ℝ) = ∑ p ∈ W j, ((Good p).card : ℝ) := by
    rw [goodPairs_card_eq_sum]
    push_cast
    rfl
  -- each prime of the window contributes at least `1/a` times its good count
  have hstep2 : (P * (7 / 5) ^ j) * gd j ≤ ∑ p ∈ W j, ((Good p).card : ℝ) := by
    have hpt : ∀ p ∈ W j, (1 / (p : ℝ)) * ((Good p).card : ℝ)
        ≤ (1 / (P * (7 / 5) ^ j)) * ((Good p).card : ℝ) := by
      intro p hp
      have hle : P * (7 / 5) ^ j ≤ (p : ℝ) := primesIn_lower hapos hp
      have h := one_div_le_one_div_of_le hapos hle
      exact mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)
    have h1 : gd j ≤ (1 / (P * (7 / 5) ^ j)) * ∑ p ∈ W j, ((Good p).card : ℝ) := by
      simp only [gd]
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hpt
    have h2 : (P * (7 / 5) ^ j) * ((1 / (P * (7 / 5) ^ j)) *
        ∑ p ∈ W j, ((Good p).card : ℝ)) = ∑ p ∈ W j, ((Good p).card : ℝ) := by
      rw [← mul_assoc, mul_one_div_cancel (ne_of_gt hapos), one_mul]
    have h3 := mul_le_mul_of_nonneg_left h1 hapos.le
    linarith [h2 ▸ h3]
  -- the good window carries `≥ (β/2) #fam π₀(a)`
  have hgd_low : (β / 2) * (F.fam.card : ℝ) * ((P * (7 / 5) ^ j) / Real.log (P * (7 / 5) ^ j))
      ≤ (P * (7 / 5) ^ j) * gd j := by
    have hmj : β / Real.log (P * (7 / 5) ^ j) ≤ m j := hF1 j hjJ
    have h1 : (1 / 2) * (F.fam.card : ℝ) * (β / Real.log (P * (7 / 5) ^ j)) ≤ gd j := by
      have h := mul_le_mul_of_nonneg_left hmj (by positivity : (0 : ℝ) ≤ (1 / 2) * (F.fam.card : ℝ))
      linarith [hgood, h]
    have h2 : (β / 2) * (F.fam.card : ℝ) * ((P * (7 / 5) ^ j) / Real.log (P * (7 / 5) ^ j))
        = (P * (7 / 5) ^ j) *
          ((1 / 2) * (F.fam.card : ℝ) * (β / Real.log (P * (7 / 5) ^ j))) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 hapos.le
  -- the constant comparison
  have hfin : (β * c₀ / 4) * (X / H) * pi0 (P * (7 / 5) ^ j)
      ≤ (β / 2) * (F.fam.card : ℝ) * ((P * (7 / 5) ^ j) / Real.log (P * (7 / 5) ^ j)) := by
    have hpio : pi0 (P * (7 / 5) ^ j) = (P * (7 / 5) ^ j) / Real.log (P * (7 / 5) ^ j) := rfl
    rw [hpio]
    have hnonneg : 0 ≤ (P * (7 / 5) ^ j) / Real.log (P * (7 / 5) ^ j) := by positivity
    have hc : (β * c₀ / 4) * (X / H) ≤ (β / 2) * (F.fam.card : ℝ) := by
      nlinarith [hNge, hβpos, hc₀, hTpos]
    exact mul_le_mul_of_nonneg_right hc hnonneg
  refine ⟨P * (7 / 5) ^ j, P * (7 / 5) ^ (j + 1), haP, hab, h57, hbQj, ?_⟩
  calc (β * c₀ / 4) * (X / H) * pi0 (P * (7 / 5) ^ j)
      ≤ (β / 2) * (F.fam.card : ℝ) * ((P * (7 / 5) ^ j) / Real.log (P * (7 / 5) ^ j)) := hfin
    _ ≤ (P * (7 / 5) ^ j) * gd j := hgd_low
    _ ≤ ∑ p ∈ W j, ((Good p).card : ℝ) := hstep2
    _ = ((goodPairs f F.pol (c₀ / 2) H (P * (7 / 5) ^ j) (P * (7 / 5) ^ (j + 1))
          F.fam).card : ℝ) := hcard.symm

end Work.BMF.SD
