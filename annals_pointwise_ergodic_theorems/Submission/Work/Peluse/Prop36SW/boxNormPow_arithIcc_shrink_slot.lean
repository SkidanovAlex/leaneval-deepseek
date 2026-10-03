import Mathlib
import Submission.Work.Peluse.Prop36SW.boxNormPow_arithIcc_shrink

/-!
# Shrinking the direction family `q i [L'' i]` to `q i [L i]`, with a *slot-dependent* length

The sibling statement `Work.Peluse.Prop36SW.boxNormPow_arithIcc_shrink` shrinks a *common* length
`L'` down to a *common* length `L`.  Here the two lengths may vary from coordinate to coordinate:
for each `i` the direction set `arithIcc (q i) (L'' i)` is shrunk to `arithIcc (q i) (L i)`, with
`1 ≤ L i ≤ L'' i`.

The proof is the coordinatewise version of the constant-length argument.  For each `i` put

`B i := if q i = 0 then 1 else L'' i / L i + 1`,   `M i := B i * L i`.

Then `L'' i ≤ M i ≤ 2 L'' i` (for `q i ≠ 0` this is `mul_div_succ_bounds`, and for `q i = 0` both
direction sets are the singleton `{0}`, so `B i = 1` and `M i = L i`), and `M i = B i * L i`, so the
block-decomposition comparison `Work.Peluse.Prop36SW.shrink_dvd_zero_dir` gives `B(M) ≤ B(L)`.
Monotonicity of the raw box quantity (`Work.Peluse.TransferUp.rawPow_mono_of_two_le`, valid at every
level `t ≥ 2`) upgrades `arithIcc (q i) (L'' i) ⊆ arithIcc (q i) (M i)` to
`(∏ |arithIcc (q i) (L'' i)|²) B(L'') ≤ (∏ |arithIcc (q i) (M i)|²) B(M)`, and the cardinality
comparison `|arithIcc (q i) (M i)| ≤ 2 |arithIcc (q i) (L'' i)|` turns the prefix into `4^t` times
the same product.  Cancelling the positive factor `∏ |arithIcc (q i) (L'' i)|²` yields the statement
with `C = 4^{-t}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Work.Peluse.Prop36SW

noncomputable section

open Work.Peluse

theorem boxNormPow_arithIcc_shrink_slot {t : ℕ} (ht : 2 ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : Fin t → ℤ) (L L'' : Fin t → ℕ), (∀ i, 1 ≤ L i) → (∀ i, L i ≤ L'' i) →
      ∀ (S : Finset ℤ) (f : ℤ → ℂ), Work.Peluse.FinSuppZ f →
        C * Work.Peluse.boxNormPow t (fun i => Work.Peluse.arithIcc (q i) (L'' i)) S f
          ≤ Work.Peluse.boxNormPow t (fun i => Work.Peluse.arithIcc (q i) (L i)) S f := by
  refine ⟨(4 : ℝ) ^ (-(t : ℤ)), by positivity, ?_⟩
  intro q L L'' hL hLL S f hf
  have hL'' : ∀ i, 1 ≤ L'' i := fun i => le_trans (hL i) (hLL i)
  set B : Fin t → ℕ := fun i => if q i = 0 then 1 else L'' i / L i + 1 with hBdef
  have hB1 : ∀ i, 1 ≤ B i := by
    intro i
    by_cases hq : q i = 0
    · rw [show B i = 1 from by rw [hBdef]; exact if_pos hq]
    · rw [show B i = L'' i / L i + 1 from by rw [hBdef]; exact if_neg hq]
      simp
  have hz : ∀ i, q i = 0 → B i = 1 := by
    intro i hq
    rw [show B i = 1 from by rw [hBdef]; exact if_pos hq]
  -- the per-coordinate size comparison `B i * L i ≤ 2 * L'' i`
  have hMbound : ∀ i, B i * L i ≤ 2 * L'' i := by
    intro i
    by_cases hq : q i = 0
    · rw [hz i hq, one_mul]
      exact le_trans (hLL i) (by omega)
    · have hBi : B i = L'' i / L i + 1 := by rw [hBdef]; exact if_neg hq
      rw [hBi]
      exact (mul_div_succ_bounds (hL i) (hLL i)).2
  -- the per-coordinate inclusion `arithIcc (q i) (L'' i) ⊆ arithIcc (q i) (B i * L i)`
  have hsub : ∀ i, arithIcc (q i) (L'' i) ⊆ arithIcc (q i) (B i * L i) := by
    intro i
    by_cases hq : q i = 0
    · rw [hz i hq, one_mul, hq, arithIcc_zero_eq (hL'' i), arithIcc_zero_eq (hL i)]
    · have hBi : B i = L'' i / L i + 1 := by rw [hBdef]; exact if_neg hq
      rw [hBi]
      exact arithIcc_subset_of_le (q i) (mul_div_succ_bounds (hL i) (hLL i)).1
  have hraw : Work.Peluse.TransferUp.rawPow t (fun i => arithIcc (q i) (L'' i)) S f
      ≤ Work.Peluse.TransferUp.rawPow t (fun i => arithIcc (q i) (B i * L i)) S f :=
    Work.Peluse.TransferUp.rawPow_mono_of_two_le ht S hf hsub
  rw [Work.Peluse.TransferUp.rawPow, Work.Peluse.TransferUp.rawPow] at hraw
  set BL'' : ℝ := boxNormPow t (fun i => arithIcc (q i) (L'' i)) S f with hBL''def
  set BM : ℝ := boxNormPow t (fun i => arithIcc (q i) (B i * L i)) S f with hBMdef
  set BL : ℝ := boxNormPow t (fun i => arithIcc (q i) (L i)) S f with hBLdef
  set PL : ℝ := ∏ i : Fin t, (((arithIcc (q i) (L'' i)).card : ℝ)) ^ 2 with hPLdef
  set PM : ℝ := ∏ i : Fin t, (((arithIcc (q i) (B i * L i)).card : ℝ)) ^ 2 with hPMdef
  have hBMnn : 0 ≤ BM := by rw [hBMdef]; exact norm_nonneg _
  have hBLnn : 0 ≤ BL := by rw [hBLdef]; exact norm_nonneg _
  have hPLpos : 0 < PL := by
    rw [hPLdef]
    refine Finset.prod_pos (fun i _ => ?_)
    have h := arithIcc_card_pos (q i) (hL'' i)
    have h' : (0 : ℝ) < ((arithIcc (q i) (L'' i)).card : ℝ) := by exact_mod_cast h
    positivity
  have hPLnn : 0 ≤ PL := le_of_lt hPLpos
  have hPMle : PM ≤ (4 : ℝ) ^ t * PL := by
    have h1 : ∀ i : Fin t, (((arithIcc (q i) (B i * L i)).card : ℝ)) ^ 2
        ≤ 4 * (((arithIcc (q i) (L'' i)).card : ℝ)) ^ 2 := by
      intro i
      have h2 : ((arithIcc (q i) (B i * L i)).card : ℝ)
          ≤ 2 * ((arithIcc (q i) (L'' i)).card : ℝ) := by
        have h3 := arithIcc_card_le_two (q i) (hL'' i) (hMbound i)
        exact_mod_cast h3
      have h4 : (0 : ℝ) ≤ ((arithIcc (q i) (B i * L i)).card : ℝ) := by positivity
      have h5 : (0 : ℝ) ≤ ((arithIcc (q i) (L'' i)).card : ℝ) := by positivity
      nlinarith [h2, h4, h5]
    have hprod : PM ≤ ∏ i : Fin t, 4 * (((arithIcc (q i) (L'' i)).card : ℝ)) ^ 2 := by
      rw [hPMdef]
      exact Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => h1 i)
    have hfac : (∏ i : Fin t, 4 * (((arithIcc (q i) (L'' i)).card : ℝ)) ^ 2)
        = (4 : ℝ) ^ t * PL := by
      have e1 : (∏ i : Fin t, 4 * (((arithIcc (q i) (L'' i)).card : ℝ)) ^ 2)
          = (∏ _ : Fin t, (4 : ℝ))
            * ∏ i : Fin t, (((arithIcc (q i) (L'' i)).card : ℝ)) ^ 2 :=
        Finset.prod_mul_distrib
      rw [e1, hPLdef, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact le_trans hprod (le_of_eq hfac)
  -- the block-decomposition comparison `B(M) ≤ B(L)`
  have hPB : BM ≤ BL :=
    shrink_dvd_zero_dir (t := t) (by omega) q B L hB1 hz hL S hf
  have hstep : PL * BL'' ≤ PL * ((4 : ℝ) ^ t * BL) := by
    calc PL * BL'' ≤ PM * BM := hraw
      _ ≤ ((4 : ℝ) ^ t * PL) * BM := mul_le_mul_of_nonneg_right hPMle hBMnn
      _ ≤ ((4 : ℝ) ^ t * PL) * BL :=
          mul_le_mul_of_nonneg_left hPB (mul_nonneg (by positivity) hPLnn)
      _ = PL * ((4 : ℝ) ^ t * BL) := by rw [mul_comm ((4 : ℝ) ^ t) PL, mul_assoc]
  have hBL'' : BL'' ≤ (4 : ℝ) ^ t * BL := (mul_le_mul_iff_of_pos_left hPLpos).mp hstep
  have h4pos : (0 : ℝ) < (4 : ℝ) ^ t := by positivity
  have h4invnn : 0 ≤ (((4 : ℝ) ^ t)⁻¹) := by positivity
  calc (4 : ℝ) ^ (-(t : ℤ)) * BL''
      = (((4 : ℝ) ^ t)⁻¹) * BL'' := by rw [zpow_neg, zpow_natCast]
    _ ≤ (((4 : ℝ) ^ t)⁻¹) * ((4 : ℝ) ^ t * BL) := mul_le_mul_of_nonneg_left hBL'' h4invnn
    _ = BL := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt h4pos), one_mul]

end

end Work.Peluse.Prop36SW
