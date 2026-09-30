import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.SD.sd3_defs
import Submission.Work.BMF.SD.good_window_pairs
import Submission.Work.BMF.SD.geo_window_mass_lower2
import Submission.Work.BMF.SD.window_sums_le_two
import Submission.Work.BMF.SD.tk_bad_weight_sub

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 4000000

namespace Work.BMF.SD

/-- The prime-window count for an arbitrary sub-family `S ⊆ F.fam`, with the correlation level taken
from the ambient constant `c₀` and the cardinality from the sub-family.

If `S ⊆ F.fam` carries at least `c'' · (X/H)` sources (`c'' > 0`), then some window `[a,b]`
(`P ≤ a ≤ b ≤ Q`, `5b ≤ 7a`) carries at least `c₁ · c'' · (X/H) · π₀(a)` pairs `(y,p) ∈ S × [a,b]`
`p` prime, whose rescaled correlation is at level `c₀/2`:
`(c₀/2)(H/p) ≤ ‖corr f (dil p (F.pol y)) (y/p) (H/p)‖`.

The bad-mass bound `Σ_{p ∈ primesIn P Q} (1/p) · #{y ∈ S : y bad at p} ≤ K · #S` is an explicit
hypothesis with the constant `K > 0` a parameter (it is provided by
`Work.BMF.SD.tk_bad_weight_sub` with `K ≤ 3200/c₀² + 64/c₀ + 8`).

Route: this is `Work.BMF.SD.good_window_pairs` with `F.fam` replaced by `S` throughout and the
family's own cardinality bound replaced by `c'' (X/H) ≤ #S`.  Concretely, the geometric windows
`W_j = [P(7/5)^j, P(7/5)^{j+1}]` (mass ladder: `Work.BMF.SD.geo_window_mass_lower2` gives a range
with `Σ_j mass_j ≥ 4K` once `A₀ ≥ exp (4K + C)`; `Work.BMF.window_weights` gives
`mass_j ≥ β/log a_j`), the bad windows satisfy `Σ_j badmass_j ≤ 2K·#S`
(`Work.BMF.SD.window_sums_le_two`), so some window has `goodmass_j ≥ (1/2)·#S·mass_j`, whence
`#(good pairs over S in W_j) ≥ a_j·goodmass_j ≥ (β/2)·#S·π₀(a_j) ≥ (β c''/4)(X/H)π₀(a_j)`.
So the conclusion holds with `c₁ = β/4`, a constant independent of `c''` and `K`; `A` needs to be
`e^{4K + C}`-large, again a constant once `K` is fixed. -/
theorem good_window_pairs_sub (k : ℕ) (c₀ K : ℝ) (hc₀ : 0 < c₀) (hK : 0 < K) :
    ∃ c₁ A : ℝ, 0 < c₁ ∧ 0 < A ∧
      ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) →
      ∀ (hmul : ∀ m n, Nat.Coprime m n → f (m * n) = f m * f n),
      ∀ (X H P Q c'' : ℝ), 0 < c'' → 2 ≤ P → P ≤ Q → Q ^ 3 ≤ H → H ≤ X →
        A ≤ Real.log Q / Real.log P →
      ∀ (F : Work.BMF.PhaseFamily k f c₀ X H) (S : Finset ℝ), S ⊆ F.fam →
        c'' * (X / H) ≤ (S.card : ℝ) →
        (∑ p ∈ Work.BMF.primesIn P Q, (1 / (p : ℝ)) *
          (((S.filter (fun (y : ℝ) => ¬ ((c₀ / 2) * (H / (p : ℝ)) ≤
            ‖Work.BMF.corr f (Work.BMF.dil (p : ℝ) (F.pol y)) (y / (p : ℝ)) (H / (p : ℝ))‖))).card : ℝ)))
          ≤ K * (S.card : ℝ) →
        ∃ a b : ℝ, P ≤ a ∧ a ≤ b ∧ 5 * b ≤ 7 * a ∧ b ≤ Q ∧
          c₁ * c'' * (X / H) * Work.BMF.pi0 a ≤
            ((Work.BMF.goodPairs f F.pol (c₀ / 2) H a b S).card : ℝ) := by
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
  refine ⟨β / 4, A₀ + A₂, by positivity, by positivity, ?_⟩
  intro f hf hmul X H P Q c'' hc'' h2P hPQ hQ3 hHX hA F S hS hcard hbad
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
    geo_window_mass_lower2 P Q T K CM h2P hPQ hPQ2 hT1 hK hMert hHyp
  -- the sub-family is nonempty
  have hNge : c'' * (X / H) ≤ (S.card : ℝ) := hcard
  have hNpos : 0 < (S.card : ℝ) := lt_of_lt_of_le (mul_pos hc'' hTpos) hNge
  -- the good/bad sets
  let Good : ℕ → Finset ℝ := fun p =>
    S.filter (fun y => (c₀ / 2) * (H / (p : ℝ)) ≤
      ‖corr f (dil (p : ℝ) (F.pol y)) (y / (p : ℝ)) (H / (p : ℝ))‖)
  let Bad : ℕ → Finset ℝ := fun p =>
    S.filter (fun y => ¬ ((c₀ / 2) * (H / (p : ℝ)) ≤
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
  have hcardGb : ∀ p : ℕ, ((Good p).card : ℝ) + ((Bad p).card : ℝ) = (S.card : ℝ) := by
    intro p
    have h := Finset.card_filter_add_card_filter_not (s := S)
      (p := fun y => (c₀ / 2) * (H / (p : ℝ)) ≤
        ‖corr f (dil (p : ℝ) (F.pol y)) (y / (p : ℝ)) (H / (p : ℝ))‖)
    simp only [Good, Bad]
    exact_mod_cast h
  have hF2 : ∀ j : ℕ, gd j + bd j = (S.card : ℝ) * m j := by
    intro j
    simp only [gd, bd, m]
    rw [← Finset.sum_add_distrib]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have h := hcardGb p
    rw [← h]
    ring
  -- (3) the bad mass is at most `2 K #S`
  have hF3 : ∑ j ∈ J, bd j ≤ 2 * K * (S.card : ℝ) := by
    have hsub : ∀ j ∈ J,
        primesIn (P * (7 / 5) ^ j) (P * (7 / 5) ^ (j + 1)) ⊆ primesIn P Q := by
      intro j hj
      exact primesIn_mono (hPle j hj) (hbQ j hj)
    have hws := window_sums_le_two P hPpos J (primesIn P Q)
      (fun p => (1 / (p : ℝ)) * ((Bad p).card : ℝ))
      (fun p => by positivity) hsub
    have hTK' : ∑ p ∈ primesIn P Q, (1 / (p : ℝ)) * ((Bad p).card : ℝ)
        ≤ K * (S.card : ℝ) := by
      simp only [Bad]
      exact hbad
    simp only [bd] at hws ⊢
    linarith [hws, hTK']
  -- (4) the windows carry `4K` of mass
  have hF4 : 4 * K ≤ ∑ j ∈ J, m j := by
    rw [hJdef]
    simp only [m]
    exact hmass
  -- (5) pigeonhole: some window is good
  have hF5 : ∃ j ∈ J, (1 / 2) * (S.card : ℝ) * m j ≤ gd j := by
    by_contra hcon
    push_neg at hcon
    have hlt : (1 / 2) * (S.card : ℝ) * ∑ j ∈ J, m j < ∑ j ∈ J, bd j := by
      rw [Finset.mul_sum]
      apply Finset.sum_lt_sum_of_nonempty hJne
      intro j hj
      have h2 := hF2 j
      have h3 := hcon j hj
      linarith
    have hge : 2 * K * (S.card : ℝ) ≤ (1 / 2) * (S.card : ℝ) * ∑ j ∈ J, m j := by
      have h := mul_le_mul_of_nonneg_left hF4 (by positivity : (0 : ℝ) ≤ (1 / 2) * (S.card : ℝ))
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
  have hcard' : ((goodPairs f F.pol (c₀ / 2) H (P * (7 / 5) ^ j) (P * (7 / 5) ^ (j + 1))
        S).card : ℝ) = ∑ p ∈ W j, ((Good p).card : ℝ) := by
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
  -- the good window carries `≥ (β/2) #S π₀(a)`
  have hgd_low : (β / 2) * (S.card : ℝ) * ((P * (7 / 5) ^ j) / Real.log (P * (7 / 5) ^ j))
      ≤ (P * (7 / 5) ^ j) * gd j := by
    have hmj : β / Real.log (P * (7 / 5) ^ j) ≤ m j := hF1 j hjJ
    have h1 : (1 / 2) * (S.card : ℝ) * (β / Real.log (P * (7 / 5) ^ j)) ≤ gd j := by
      have h := mul_le_mul_of_nonneg_left hmj (by positivity : (0 : ℝ) ≤ (1 / 2) * (S.card : ℝ))
      linarith [hgood, h]
    have h2 : (β / 2) * (S.card : ℝ) * ((P * (7 / 5) ^ j) / Real.log (P * (7 / 5) ^ j))
        = (P * (7 / 5) ^ j) *
          ((1 / 2) * (S.card : ℝ) * (β / Real.log (P * (7 / 5) ^ j))) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 hapos.le
  -- the constant comparison
  have hfin : (β / 4) * c'' * (X / H) * pi0 (P * (7 / 5) ^ j)
      ≤ (β / 2) * (S.card : ℝ) * ((P * (7 / 5) ^ j) / Real.log (P * (7 / 5) ^ j)) := by
    have hpio : pi0 (P * (7 / 5) ^ j) = (P * (7 / 5) ^ j) / Real.log (P * (7 / 5) ^ j) := rfl
    rw [hpio]
    have hnonneg : 0 ≤ (P * (7 / 5) ^ j) / Real.log (P * (7 / 5) ^ j) := by positivity
    have hcnn : 0 ≤ c'' * (X / H) := le_of_lt (mul_pos hc'' hTpos)
    have hc : (β / 4) * c'' * (X / H) ≤ (β / 2) * (S.card : ℝ) := by
      have hA' : (β / 2) * (c'' * (X / H)) ≤ (β / 2) * (S.card : ℝ) :=
        mul_le_mul_of_nonneg_left hcard (by linarith [hβpos])
      have hB' : (β / 4) * c'' * (X / H) ≤ (β / 2) * (c'' * (X / H)) := by
        nlinarith [hcnn, hβpos]
      linarith
    exact mul_le_mul_of_nonneg_right hc hnonneg
  refine ⟨P * (7 / 5) ^ j, P * (7 / 5) ^ (j + 1), haP, hab, h57, hbQj, ?_⟩
  calc (β / 4) * c'' * (X / H) * pi0 (P * (7 / 5) ^ j)
      ≤ (β / 2) * (S.card : ℝ) * ((P * (7 / 5) ^ j) / Real.log (P * (7 / 5) ^ j)) := hfin
    _ ≤ (P * (7 / 5) ^ j) * gd j := hgd_low
    _ ≤ ∑ p ∈ W j, ((Good p).card : ℝ) := hstep2
    _ = ((goodPairs f F.pol (c₀ / 2) H (P * (7 / 5) ^ j) (P * (7 / 5) ^ (j + 1))
          S).card : ℝ) := hcard'.symm

end Work.BMF.SD
