import Mathlib
import Submission.Work.Peluse.TransferUp.boxNormPow_arithIcc_raw_mono
import Submission.Work.Peluse.Prop36SW.shrink_dvd_zero_dir

/-!
# Shrinking the direction family `q i · [L']` to `q i · [L]`

The target `Work.Peluse.Prop36SW.boxNormPow_arithIcc_shrink` states that for every `t ≥ 2` there is
`C > 0` such that for all `q : Fin t → ℤ`, all `1 ≤ L ≤ L'`, every window `S` and every finitely
supported `f`,

`C * ‖f‖^{2^t}_{□^t_{(q i)[L']}(S)} ≤ ‖f‖^{2^t}_{□^t_{(q i)[L]}(S)}`,

i.e. the box-norm power of level `t` is (up to a constant) decreasing in the length of the
arithmetic-progression direction sets.  Unlike the sibling statements
(`Work.Peluse.Concat.arithIcc_shrink_ge_two`, `Work.Peluse.TransferUp.boxNormPow_arithIcc_shrink_coord`)
the direction coefficients `q i` are *arbitrary* integers: they may be negative and, crucially, they
may vanish, in which case `arithIcc 0 L = {0}` for every `L ≥ 1` is a singleton.

## The proof

Put `M := (L' / L + 1) * L`.  Since `L ≤ L'`, one has `L' ≤ M ≤ 2 L'`, and `L ∣ M`.

* **Raw monotonicity** (`Work.Peluse.TransferUp.rawPow_mono_of_two_le`, with
  `rawPow t Q S f = (∏_i |Q i|²) * boxNormPow t Q S f`): the direction sets
  `arithIcc (q i) L'` are contained in `arithIcc (q i) M`, so

  `(∏_i c_i²) * B(L') ≤ (∏_i C_i²) * B(M)`, where `c_i = |arithIcc (q i) L'|` and
  `C_i = |arithIcc (q i) M|`.

* **Cardinalities**: `c_i = 1 = C_i` when `q i = 0`, and `(c_i, C_i) = (L', M)` otherwise; in both
  cases `C_i ≤ 2 c_i` (by `M ≤ 2 L'`).  Hence `∏_i C_i² ≤ 4^t ∏_i c_i²`.

* **Shrinking** (`Work.Peluse.Prop36SW.shrink_dvd_zero_dir`): with `B i := 1` for the vanishing
  directions and `B i := L' / L + 1` otherwise, one has `B i * L = M` (a true identity of the
  direction sets also in the vanishing case, where both sides are `{0}`), so the block-decomposition
  comparison gives `B(M) ≤ B(L)`.

Combining: `(∏ c_i²) B(L') ≤ 4^t (∏ c_i²) B(L)`, and cancelling the positive factor `∏ c_i² > 0`
yields `B(L') ≤ 4^t B(L)`, i.e. the statement with `C = 4^{-t}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Work.Peluse.Prop36SW

noncomputable section

open Work.Peluse

/-! ## Elementary facts about the arithmetic progressions `arithIcc q L` -/

/-- The arithmetic progression with vanishing step is the singleton `{0}` (for positive length). -/
lemma arithIcc_zero_eq {L : ℕ} (hL : 1 ≤ L) : arithIcc 0 L = ({0} : Finset ℤ) := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨n, -, hn⟩
    rw [← hn]
    simp
  · intro hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact Finset.mem_image.mpr ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hL⟩, by simp⟩

/-- The cardinality of the degenerate progression `arithIcc 0 L`. -/
lemma arithIcc_card_zero {L : ℕ} (hL : 1 ≤ L) : (arithIcc 0 L).card = 1 := by
  rw [arithIcc_zero_eq hL]
  simp

/-- `arithIcc q L` is non-empty for `L ≥ 1`. -/
lemma arithIcc_card_pos (q : ℤ) {L : ℕ} (hL : 1 ≤ L) : 1 ≤ (arithIcc q L).card := by
  have h : q ∈ arithIcc q L :=
    Finset.mem_image.mpr ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hL⟩, by simp⟩
  exact Finset.card_pos.mpr ⟨q, h⟩

/-- The cardinality of `arithIcc q M` is at most twice the cardinality of `arithIcc q L` as soon as
`1 ≤ L` and `M ≤ 2L`: for a non-vanishing step this is `M ≤ 2L`, and for a vanishing step both sets
are (possibly empty) singletons. -/
lemma arithIcc_card_le_two (q : ℤ) {L M : ℕ} (hL : 1 ≤ L) (hM : M ≤ 2 * L) :
    (arithIcc q M).card ≤ 2 * (arithIcc q L).card := by
  rcases eq_or_ne q 0 with hq | hq
  · subst hq
    rcases Nat.eq_zero_or_pos M with hM0 | hMpos
    · subst hM0
      rw [arithIcc_card_zero hL]
      simp [Work.Peluse.arithIcc]
    · rw [arithIcc_card_zero hMpos, arithIcc_card_zero hL]
      norm_num
  · rw [Work.Peluse.BoxNormDilation.card_arithIcc hq M,
      Work.Peluse.BoxNormDilation.card_arithIcc hq L]
    omega

/-- The arithmetic progressions are monotone in the length. -/
lemma arithIcc_subset_of_le (q : ℤ) {L M : ℕ} (h : L ≤ M) :
    arithIcc q L ⊆ arithIcc q M :=
  Finset.image_subset_image (Finset.Icc_subset_Icc_right h)

/-- The arithmetic of the auxiliary length `M = (L'/L + 1) * L`: for `1 ≤ L ≤ L'` it is a length
between `L'` and `2 L'`. -/
lemma mul_div_succ_bounds {L L' : ℕ} (hL : 1 ≤ L) (hLL' : L ≤ L') :
    L' ≤ (L' / L + 1) * L ∧ (L' / L + 1) * L ≤ 2 * L' := by
  constructor
  · have h1 : L' / L * L + L' % L = L' := by
      rw [mul_comm]
      exact Nat.div_add_mod L' L
    have h2 : L' % L < L := Nat.mod_lt _ (by omega)
    calc L' = L' / L * L + L' % L := h1.symm
      _ ≤ L' / L * L + L := by omega
      _ = (L' / L + 1) * L := by ring
  · have h1 : L' / L * L ≤ L' := Nat.div_mul_le_self L' L
    calc (L' / L + 1) * L = L' / L * L + L := by ring
      _ ≤ L' + L' := by omega
      _ = 2 * L' := by ring

/-! ## The target -/

theorem boxNormPow_arithIcc_shrink {t : ℕ} (ht : 2 ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : Fin t → ℤ) (L L' : ℕ), 1 ≤ L → L ≤ L' →
      ∀ (S : Finset ℤ) (f : ℤ → ℂ), Work.Peluse.FinSuppZ f →
        C * Work.Peluse.boxNormPow t (fun i => Work.Peluse.arithIcc (q i) L') S f
          ≤ Work.Peluse.boxNormPow t (fun i => Work.Peluse.arithIcc (q i) L) S f := by
  refine ⟨(4 : ℝ) ^ (-(t : ℤ)), by positivity, ?_⟩
  intro q L L' hL hLL S f hf
  have hL' : 1 ≤ L' := le_trans hL hLL
  have hM1 : L' ≤ (L' / L + 1) * L := (mul_div_succ_bounds hL hLL).1
  have hM2 : (L' / L + 1) * L ≤ 2 * L' := (mul_div_succ_bounds hL hLL).2
  set M : ℕ := (L' / L + 1) * L with hMdef
  have hMpos : 1 ≤ M := le_trans hL (le_trans hLL hM1)
  set Bf : Fin t → ℕ := fun i => if q i = 0 then 1 else L' / L + 1 with hBfdef
  -- the raw box quantity is monotone in the direction sets
  have hraw : Work.Peluse.TransferUp.rawPow t (fun i => Work.Peluse.arithIcc (q i) L') S f
      ≤ Work.Peluse.TransferUp.rawPow t (fun i => Work.Peluse.arithIcc (q i) M) S f :=
    Work.Peluse.TransferUp.rawPow_mono_of_two_le ht S hf
      (fun i => arithIcc_subset_of_le (q i) hM1)
  rw [Work.Peluse.TransferUp.rawPow, Work.Peluse.TransferUp.rawPow] at hraw
  -- name the three box-norm powers and the two cardinality products
  set BL' : ℝ := Work.Peluse.boxNormPow t (fun i => Work.Peluse.arithIcc (q i) L') S f
    with hBL'def
  set BM : ℝ := Work.Peluse.boxNormPow t (fun i => Work.Peluse.arithIcc (q i) M) S f
    with hBMdef
  set BL : ℝ := Work.Peluse.boxNormPow t (fun i => Work.Peluse.arithIcc (q i) L) S f
    with hBLdef
  set PL : ℝ := ∏ i : Fin t, (((arithIcc (q i) L').card : ℝ)) ^ 2 with hPLdef
  set PM : ℝ := ∏ i : Fin t, (((arithIcc (q i) M).card : ℝ)) ^ 2 with hPMdef
  have hBMnn : 0 ≤ BM := by rw [hBMdef]; exact norm_nonneg _
  have hBLnn : 0 ≤ BL := by rw [hBLdef]; exact norm_nonneg _
  have hPLpos : 0 < PL := by
    rw [hPLdef]
    refine Finset.prod_pos (fun i _ => ?_)
    have h := arithIcc_card_pos (q i) hL'
    have h' : (0:ℝ) < ((arithIcc (q i) L').card : ℝ) := by exact_mod_cast h
    positivity
  have hPLnn : 0 ≤ PL := le_of_lt hPLpos
  have hPMle : PM ≤ (4:ℝ) ^ t * PL := by
    have h1 : ∀ i : Fin t, (((arithIcc (q i) M).card : ℝ)) ^ 2
        ≤ 4 * (((arithIcc (q i) L').card : ℝ)) ^ 2 := by
      intro i
      have h2 : ((arithIcc (q i) M).card : ℝ) ≤ 2 * ((arithIcc (q i) L').card : ℝ) := by
        have h3 := arithIcc_card_le_two (q i) hL' hM2
        exact_mod_cast h3
      have h4 : (0:ℝ) ≤ ((arithIcc (q i) M).card : ℝ) := by positivity
      have h5 : (0:ℝ) ≤ ((arithIcc (q i) L').card : ℝ) := by positivity
      nlinarith [h2, h4, h5]
    have hprod : PM ≤ ∏ i : Fin t, 4 * (((arithIcc (q i) L').card : ℝ)) ^ 2 := by
      rw [hPMdef]
      exact Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => h1 i)
    have hfac : (∏ i : Fin t, 4 * (((arithIcc (q i) L').card : ℝ)) ^ 2)
        = (4:ℝ) ^ t * PL := by
      have e1 : (∏ i : Fin t, 4 * (((arithIcc (q i) L').card : ℝ)) ^ 2)
          = (∏ _ : Fin t, (4:ℝ))
            * ∏ i : Fin t, (((arithIcc (q i) L').card : ℝ)) ^ 2 :=
        Finset.prod_mul_distrib
      rw [e1, hPLdef, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact le_trans hprod (le_of_eq hfac)
  have hBf1 : ∀ i, 1 ≤ Bf i := by
    intro i
    by_cases hq : q i = 0
    · rw [show Bf i = 1 from by rw [hBfdef]; exact if_pos hq]
    · rw [show Bf i = L' / L + 1 from by rw [hBfdef]; exact if_neg hq]
      simp
  have hz : ∀ i, q i = 0 → Bf i = 1 := by
    intro i hq
    rw [show Bf i = 1 from by rw [hBfdef]; exact if_pos hq]
  have hsets : ∀ i, arithIcc (q i) (Bf i * L) = arithIcc (q i) M := by
    intro i
    by_cases hq : q i = 0
    · rw [hz i hq, one_mul, hq, arithIcc_zero_eq hL, arithIcc_zero_eq hMpos]
    · have hBfi : Bf i = L' / L + 1 := by rw [hBfdef]; exact if_neg hq
      rw [hBfi, hMdef]
  -- the block-decomposition comparison, with the vanishing directions left untouched
  have hPB : BM ≤ BL := by
    have h := shrink_dvd_zero_dir (t := t) (by omega) q Bf (fun _ => L) hBf1 hz
      (fun _ => hL) S hf
    rw [show (fun i : Fin t => Work.Peluse.arithIcc (q i) (Bf i * L))
          = (fun i : Fin t => Work.Peluse.arithIcc (q i) M) from funext hsets] at h
    exact h
  have hstep : PL * BL' ≤ PL * ((4:ℝ) ^ t * BL) := by
    calc PL * BL' ≤ PM * BM := hraw
      _ ≤ ((4:ℝ)^t * PL) * BM := mul_le_mul_of_nonneg_right hPMle hBMnn
      _ ≤ ((4:ℝ)^t * PL) * BL :=
          mul_le_mul_of_nonneg_left hPB (mul_nonneg (by positivity) hPLnn)
      _ = PL * ((4:ℝ)^t * BL) := by rw [mul_comm ((4:ℝ)^t) PL, mul_assoc]
  have hBL' : BL' ≤ (4:ℝ) ^ t * BL := (mul_le_mul_iff_of_pos_left hPLpos).mp hstep
  have h4pos : (0:ℝ) < (4:ℝ) ^ t := by positivity
  have h4invnn : 0 ≤ (((4:ℝ) ^ t)⁻¹) := by positivity
  calc (4:ℝ) ^ (-(t : ℤ)) * BL'
      = (((4:ℝ) ^ t)⁻¹) * BL' := by rw [zpow_neg, zpow_natCast]
    _ ≤ (((4:ℝ) ^ t)⁻¹) * ((4:ℝ)^t * BL) := mul_le_mul_of_nonneg_left hBL' h4invnn
    _ = BL := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt h4pos), one_mul]

end

end Work.Peluse.Prop36SW
