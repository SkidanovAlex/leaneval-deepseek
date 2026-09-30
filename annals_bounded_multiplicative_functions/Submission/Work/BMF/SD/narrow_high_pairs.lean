import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.SD.sd3_defs
import Submission.Work.BMF.SD.tk_bad_weight_sub
import Submission.Work.BMF.SD.good_window_pairs_sub
import Submission.Work.BMF.SD.low_sources_card_le
import Submission.Work.BMF.SD.goodPairs_narrow_admissible
import Submission.Work.BMF.fam_card_le
import Submission.Work.BMF.SD.goodPairs_narrow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD 09-30: new scale_down decomposition (read _NOTE_BMF_SD_0930_VERDICT.md at the workspace root; your node's route and constants are in its docstring). Narrow the prime window AFTER counting (pigeonhole into sub-windows of ratio 1+ρ), then split on T = X/H at a threshold T₁ depending only on c₀. No new analytic number theory is needed.
Assembly over proved lemmas (tk_bad_weight_sub, good_window_pairs_sub, fam_card_le). When the sibling node lands, add import Submission.Work.BMF.SD.goodPairs_narrow.
-/

open Classical Polynomial Finset Real Complex
open BoundedMultiplicativeFunctions

namespace Work.BMF.SD

/-- Admissible good pairs at positions `≥ X/(10a)`, for EVERY `c₀ > 0`, in the regime
`X/H ≥ 4/c₀`.  This replaces `admissible_good_pairs` (which needed `c₀ ≥ 10⁻³`): the window is
narrowed AFTER the pigeonhole, so the thin-window obstruction never arises.

Route (all inputs proved except the sibling `Work.BMF.SD.goodPairs_narrow`; add its import).
Write `T := X/H`, `N := #F.fam ≥ c₀ T`, `ρ := min (2/5) c₀`.
1. High sub-family `S := F.fam.filter (fun y => (1+ρ) * X / 10 ≤ y)`.  The low sources lie in
   `[X/10, (1+ρ)X/10)` and are `500H`-separated, so (`Work.BMF.card_le_of_sep`) there are at most
   `ρT/5000 + 1 ≤ c₀T/5000 + c₀T/4` of them (`1 ≤ c₀T/4` by `4/c₀ ≤ T`).  Hence
   `#S ≥ (c₀/2) T`.
2. `Work.BMF.SD.tk_bad_weight_sub k c₀` gives `K` and the bad weight `≤ K #S` for `S`.
3. `Work.BMF.SD.good_window_pairs_sub k c₀ K` with `c'' := c₀/2` gives a thick window `[a,b]`
   (`P ≤ a`, `5b ≤ 7a`, `b ≤ Q`) with `#goodPairs f F.pol (c₀/2) H a b S ≥ c₁₂ (c₀/2) T π₀(a)`.
4. `Work.BMF.SD.goodPairs_narrow ρ` with `κ := c₁₂ (c₀/2) T` gives `[a',b'] ⊆ [a,b]`,
   `b' ≤ (1+ρ)a'`, with `≥ c_ρ c₁₂ (c₀/2) T π₀(a')` good pairs of `S`.
5. Every such pair `(y,p)` has `y ≥ (1+ρ)X/10` and `p ≤ b' ≤ (1+ρ)a'`, so `y/p ≥ X/(10a')`; and
   `goodPairs .. S ⊆ goodPairs .. F.fam`.  Take `κ := c_ρ c₁₂ c₀ / 2`, `A := A₁₂`; output `a', b'`
   (`P ≤ a ≤ a'`, `b' ≤ b ≤ Q`, `5b' ≤ 7a'` from `ρ ≤ 2/5`). -/
theorem narrow_high_pairs (k : ℕ) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ κ A : ℝ, 0 < κ ∧ 0 < A ∧
      ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) →
      ∀ (hmul : ∀ m n, Nat.Coprime m n → f (m * n) = f m * f n),
      ∀ (X H P Q : ℝ), 2 ≤ P → P ≤ Q → Q ^ 3 ≤ H → H ≤ X →
        A ≤ Real.log Q / Real.log P → 4 / c₀ ≤ X / H →
      ∀ (F : Work.BMF.PhaseFamily k f c₀ X H),
      ∃ a b : ℝ, P ≤ a ∧ a ≤ b ∧ 5 * b ≤ 7 * a ∧ b ≤ Q ∧
        κ * (X / H) * Work.BMF.pi0 a ≤
          (((Work.BMF.goodPairs f F.pol (c₀ / 2) H a b F.fam).filter
            (fun q => X / (10 * a) ≤ q.1 / (q.2 : ℝ))).card : ℝ) := by
  obtain ⟨K, hKpos, _hKbd, hK⟩ := tk_bad_weight_sub k c₀ hc₀
  obtain ⟨c₁, A₁, hc₁pos, hA₁pos, hgw⟩ := good_window_pairs_sub k c₀ K hc₀ hKpos
  set ρ : ℝ := min (2 / 5) c₀ with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; exact lt_min (by norm_num) hc₀
  have hρle2 : ρ ≤ 2 / 5 := by rw [hρdef]; exact min_le_left _ _
  have hρlec : ρ ≤ c₀ := by rw [hρdef]; exact min_le_right _ _
  obtain ⟨cρ, hcρpos, hnarrow⟩ := goodPairs_narrow ρ hρpos hρle2
  refine ⟨cρ * c₁ * (c₀ / 2), A₁, by positivity, hA₁pos, ?_⟩
  intro f hf hmul X H P Q h2P hPQ hQ3 hHX hA hT F
  have h2Q : (2 : ℝ) ≤ Q := le_trans h2P hPQ
  have hQpos : 0 < Q := by linarith
  have h8 : (8 : ℝ) ≤ Q ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2Q 3
    norm_num at h
    linarith
  have hHpos : 0 < H := by linarith
  have hXpos : 0 < X := lt_of_lt_of_le hHpos hHX
  have hTpos : 0 < X / H := div_pos hXpos hHpos
  -- `1 ≤ c₀ (X/H) / 4`, i.e. `4 / c₀ ≤ X / H`
  have hcT : (1 : ℝ) ≤ c₀ * (X / H) / 4 := by
    have h4' : 4 ≤ c₀ * (X / H) := by
      have h := mul_le_mul_of_nonneg_left hT hc₀.le
      have hc : c₀ * (4 / c₀) = 4 := by field_simp
      linarith [h, hc]
    linarith
  -- step 1: the high sub-family
  set S : Finset ℝ := F.fam.filter (fun y => (1 + ρ) * X / 10 ≤ y) with hSdef
  set L : Finset ℝ := F.fam.filter (fun y => ¬ ((1 + ρ) * X / 10 ≤ y)) with hLdef
  have hSsub : S ⊆ F.fam := by rw [hSdef]; exact Finset.filter_subset _ _
  have hSlow : ∀ y ∈ S, (1 + ρ) * X / 10 ≤ y := by
    intro y hy
    rw [hSdef, Finset.mem_filter] at hy
    exact hy.2
  have hlow : (L.card : ℝ) ≤ ρ * (X / H) / 5000 + 1 :=
    low_sources_card_le hXpos hHpos hρpos F.isFam
  have hcardSplit : (S.card : ℝ) + (L.card : ℝ) = (F.fam.card : ℝ) := by
    have h := Finset.card_filter_add_card_filter_not (s := F.fam)
      (p := fun y : ℝ => (1 + ρ) * X / 10 ≤ y)
    simp only [hSdef, hLdef]
    exact_mod_cast h
  have hcardS : c₀ / 2 * (X / H) ≤ (S.card : ℝ) := by
    have hge : c₀ * (X / H) ≤ (F.fam.card : ℝ) := F.card_ge
    have h2 : ρ * (X / H) / 5000 ≤ c₀ * (X / H) / 5000 := by
      have h := mul_le_mul_of_nonneg_right hρlec hTpos.le
      linarith
    linarith [hge, hlow, h2, hcT, hcardSplit]
  -- step 2: the bad weight bound for `S`
  have hbad : (∑ p ∈ Work.BMF.primesIn P Q, (1 / (p : ℝ)) *
      (((S.filter (fun (y : ℝ) => ¬ ((c₀ / 2) * (H / (p : ℝ)) ≤
        ‖Work.BMF.corr f (Work.BMF.dil (p : ℝ) (F.pol y)) (y / (p : ℝ)) (H / (p : ℝ))‖))).card
        : ℝ))) ≤ K * (S.card : ℝ) := hK f hf hmul X H P Q h2P hPQ hQ3 hHX F S hSsub
  -- step 3: the thick window
  obtain ⟨a, b, hPa, hab, h57, hbQ, hcnt⟩ :=
    hgw f hf hmul X H P Q (c₀ / 2) (by positivity) h2P hPQ hQ3 hHX hA F S hSsub hcardS hbad
  -- step 4: the pigeonhole narrowing
  obtain ⟨a', b', haa', ha'b', hb'b, hb'ρ, hcnt'⟩ :=
    hnarrow f F.pol (c₀ / 2) H a b (c₁ * (c₀ / 2) * (X / H)) S
      (le_trans h2P hPa) hab h57 (by positivity) hcnt
  have ha'pos : 0 < a' := by linarith
  -- step 5: every pair of `S` in the narrow window is admissible
  have hsub := goodPairs_narrow_admissible (f := f) (pol := F.pol) (η := c₀ / 2) (H := H)
    (X := X) (ρ := ρ) (a' := a') (b' := b') (S := S) (T := F.fam)
    hSsub hρpos hXpos ha'pos hb'ρ hSlow
  refine ⟨a', b', le_trans hPa haa', ha'b', ?_, le_trans hb'b hbQ, ?_⟩
  · have h1 : 5 * b' ≤ 5 * ((1 + ρ) * a') := mul_le_mul_of_nonneg_left hb'ρ (by norm_num)
    nlinarith [h1, hρle2, ha'pos]
  · have hκeq : cρ * c₁ * (c₀ / 2) * (X / H) * Work.BMF.pi0 a'
        = cρ * (c₁ * (c₀ / 2) * (X / H)) * Work.BMF.pi0 a' := by ring
    rw [hκeq]
    refine le_trans hcnt' ?_
    have hcard := Finset.card_le_card hsub
    exact_mod_cast hcard

end Work.BMF.SD
