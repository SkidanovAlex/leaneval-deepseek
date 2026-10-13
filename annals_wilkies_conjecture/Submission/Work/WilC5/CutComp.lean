import Mathlib
import Submission.Work.WilC5.Values
import Submission.Work.WilC5.ValueOrder
import Submission.Work.WilC5.ValuesLemmas
import Submission.Work.WilC5.ValArith
import Submission.Work.WilC5.CutCompAux.CutComp_log_prod
import Submission.Work.WilC5.CutCompAux.CutComp_VLe_add_intCast_mul

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC5

/-! ## Support lemmas for `CutComp`

These are elementary facts about the additive logarithm axioms and about the value order `VLe`
that the min-rule computation consumes. -/

/-- `log 1 = 0`, from multiplicativity at `1 * 1 = 1`. -/
private theorem cc_log_one {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (log : F → F)
    (hlog_mul : ∀ {x y : F}, 0 < x → 0 < y → log (x * y) = log x + log y) :
    log 1 = 0 := by
  have h := hlog_mul (show (0 : F) < 1 by norm_num) (show (0 : F) < 1 by norm_num)
  rw [mul_one] at h
  linarith

/-- The logarithm is positive exactly on the elements above `1`. -/
private theorem cc_one_lt_iff_log_pos {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (log : F → F)
    (hlog_lt : ∀ {x y : F}, 0 < x → 0 < y → (log x < log y ↔ x < y))
    (hlog_mul : ∀ {x y : F}, 0 < x → 0 < y → log (x * y) = log x + log y)
    {x : F} (hx : 0 < x) : (1 < x ↔ 0 < log x) := by
  have h := hlog_lt (show (0 : F) < 1 by norm_num) hx
  rw [cc_log_one log hlog_mul] at h
  exact h.symm

/-- **Sign dichotomy.** If `S` and `Z` are both dominated by `T` by a factor `> 2`, then
`Z < T + S` holds exactly when `T > 0`.  (The hypothesis rules out `T = 0`, and then `T + S` has
the sign of `T` while `|Z| < |T|/2 < |T + S|`.) -/
private theorem cc_order_step {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {T S Z : F} (hS : 2 * |S| < |T|) (hZ : 2 * |Z| < |T|) : (Z < T + S ↔ 0 < T) := by
  have hTnz : T ≠ 0 := by
    intro h
    rw [h, abs_zero] at hS
    linarith [abs_nonneg S]
  constructor
  · intro hcon
    by_contra hle
    have hneg : T < 0 := lt_of_le_of_ne (le_of_not_gt hle) hTnz
    have hTa : |T| = -T := abs_of_neg hneg
    rw [hTa] at hS hZ
    have h1 : T + S < T / 2 := by
      have := le_abs_self S
      linarith
    have h2 : T / 2 < Z := by
      have := neg_abs_le Z
      linarith
    linarith
  · intro hpos
    have hTa : |T| = T := abs_of_pos hpos
    rw [hTa] at hS hZ
    have h1 : Z < T / 2 := by
      have := le_abs_self Z
      linarith
    have h2 : T / 2 < T + S := by
      have := neg_abs_le S
      linarith
    linarith

/-- Transitivity of `VLe`, contraposed: an element strictly dominated by `a` is strictly dominated
by everything that `a` dominates. -/
private theorem cc_not_VLe_of_not_VLe_of_VLe {K : Type} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {a S T : K} (hS : ¬ VLe S a) (hT : VLe T a) : ¬ VLe S T :=
  fun h => hS (VLe_trans h hT)

/-- An integer multiple does not change the value: if `u` is strictly dominated by `a` then so is
`k * u`. -/
private theorem cc_not_VLe_intCast_mul {K : Type} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {a u : K} (k : ℤ) (h : ¬ VLe u a) : ¬ VLe ((k : K) * u) a :=
  fun hc => h (VLe_trans (VLe_intCast_mul k u) hc)

/-- The min-rule computation of vdDMM Lemma 4.4 Claim 4. In an ordered field, if
`w^Q = z * (∏_{i<n} X i ^ (N i)) * (1+eps)` with all `X i > 0`, `w > 0`, `z > 0`, `Q > 0`,
`1 + eps > 0`, and `m` is the *least* index with `N m ≠ 0`, and if moreover
* `log (X m) = β ± X (m+1)`,
* `log (X j)` is archimedean-strictly-smaller than `X (m+1)` for `m < j ≤ n`,
* `log (1+eps)` is archimedean-strictly-smaller than `X (m+1)`,
* `log z + (N m) * β` is not in the archimedean class of `X (m+1)`,
then `X n < w` iff `1 < z * X m ^ (N m)`, and `w < X n` iff `z * X m ^ (N m) < 1`. -/
theorem CutComp {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (log : F → F)
    (hlog_lt : ∀ {x y : F}, 0 < x → 0 < y → (log x < log y ↔ x < y))
    (hlog_mul : ∀ {x y : F}, 0 < x → 0 < y → log (x * y) = log x + log y)
    (hlog_zpow : ∀ {x : F}, 0 < x → ∀ k : ℤ, log (x ^ k) = (k : F) * log x)
    {n : ℕ} (X : ℕ → F) (hXpos : ∀ i : ℕ, 0 < X i)
    {w z eps : F} (hw : 0 < w) (hz : 0 < z) (heps : 0 < 1 + eps)
    {Q : ℤ} (hQ : 0 < Q) (N : Fin n → ℤ)
    (hdec : w ^ Q = z * (∏ i : Fin n, X (i : ℕ) ^ (N i)) * (1 + eps))
    {m : Fin n} (hm : N m ≠ 0) (hmin : ∀ i : Fin n, (i : ℕ) < (m : ℕ) → N i = 0)
    {β : F}
    (hrel : log (X (m : ℕ)) = β + X ((m : ℕ) + 1) ∨ log (X (m : ℕ)) = β - X ((m : ℕ) + 1))
    (hsmall : ∀ j : ℕ, (m : ℕ) < j → j ≤ n →
      Work.WilC5.VLe (X ((m : ℕ) + 1)) (log (X j)) ∧ ¬ Work.WilC5.VLe (log (X j)) (X ((m : ℕ) + 1)))
    (heps_small : Work.WilC5.VLe (X ((m : ℕ) + 1)) (log (1 + eps)) ∧
      ¬ Work.WilC5.VLe (log (1 + eps)) (X ((m : ℕ) + 1)))
    (hrho : ¬ Work.WilC5.SameArch (log z + (N m : F) * β) (X ((m : ℕ) + 1))) :
    ((X n < w ↔ 1 < z * X (m : ℕ) ^ (N m)) ∧
      (w < X n ↔ z * X (m : ℕ) ^ (N m) < 1)) := by
  classical
  -- Abbreviate the "dominant" element `a = X (m+1)`; `set` also folds it in the hypotheses.
  set a : F := X ((m : ℕ) + 1) with ha
  have ha_pos : 0 < a := by rw [ha]; exact hXpos _
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  -- ## The logarithm of the decomposition
  have hPpos : 0 < ∏ i : Fin n, X (i : ℕ) ^ (N i) :=
    Finset.prod_pos (fun i _ => zpow_pos (hXpos (i : ℕ)) (N i))
  have hlogP : log (∏ i : Fin n, X (i : ℕ) ^ (N i))
      = ∑ i : Fin n, (N i : F) * log (X (i : ℕ)) := by
    have h1 := CutCompAux.CutComp_log_prod log hlog_mul (Finset.univ : Finset (Fin n))
      (fun i => X (i : ℕ) ^ (N i)) (fun i _ => zpow_pos (hXpos (i : ℕ)) (N i))
    have h2 : (∑ i ∈ (Finset.univ : Finset (Fin n)), log (X (i : ℕ) ^ (N i)))
        = ∑ i : Fin n, (N i : F) * log (X (i : ℕ)) :=
      Finset.sum_congr rfl (fun i _ => hlog_zpow (hXpos (i : ℕ)) (N i))
    exact h1.trans h2
  have hlogR : log (z * (∏ i : Fin n, X (i : ℕ) ^ (N i)) * (1 + eps))
      = log z + (∑ i : Fin n, (N i : F) * log (X (i : ℕ))) + log (1 + eps) := by
    rw [hlog_mul (mul_pos hz hPpos) heps, hlog_mul hz hPpos, hlogP]
  have hlogw : (Q : F) * log w
      = log z + (∑ i : Fin n, (N i : F) * log (X (i : ℕ))) + log (1 + eps) := by
    rw [← hlog_zpow hw Q, hdec]
    exact hlogR
  -- ## Split off the `m`-th term
  have hsplit : (∑ i : Fin n, (N i : F) * log (X (i : ℕ)))
      = (N m : F) * log (X (m : ℕ))
        + ∑ i ∈ (Finset.univ.erase m), (N i : F) * log (X (i : ℕ)) := by
    have h := Finset.add_sum_erase (Finset.univ : Finset (Fin n))
      (fun i => (N i : F) * log (X (i : ℕ))) (Finset.mem_univ m)
    exact h.symm
  -- The "main term" `T = log (z * X m ^ (N m))`, the "small" part `S`, and `Z = Q * log (X n)`.
  set T : F := log z + (N m : F) * log (X (m : ℕ)) with hT
  set S : F := (∑ i ∈ (Finset.univ.erase m), (N i : F) * log (X (i : ℕ))) + log (1 + eps) with hS
  set Z : F := (Q : F) * log (X n) with hZ
  have hTS : (Q : F) * log w = T + S := by
    rw [hlogw, hsplit, hT, hS]; ring
  -- ## `log (X n)`, the tail sum and `log (1+eps)` are strictly dominated by `a`
  have hsmall_n : VLe a (log (X n)) ∧ ¬ VLe (log (X n)) a := hsmall n m.isLt le_rfl
  have htail : VLe a (∑ i ∈ (Finset.univ.erase m), (N i : F) * log (X (i : ℕ))) ∧
      ¬ VLe (∑ i ∈ (Finset.univ.erase m), (N i : F) * log (X (i : ℕ))) a := by
    refine VLe_sum_strict (Finset.univ.erase m) ha_ne _ ?_ ?_
    · intro i hi
      have him : i ≠ m := (Finset.mem_erase.mp hi).1
      rcases lt_trichotomy (i : ℕ) (m : ℕ) with hlt | heq | hgt
      · rw [hmin i hlt]; simp only [Int.cast_zero, zero_mul]; exact VLe_zero_right a
      · exact absurd (Fin.ext heq) him
      · exact VLe_intCast_mul_left (N i) (hsmall (i : ℕ) hgt (le_of_lt i.isLt)).1
    · intro i hi
      have him : i ≠ m := (Finset.mem_erase.mp hi).1
      rcases lt_trichotomy (i : ℕ) (m : ℕ) with hlt | heq | hgt
      · rw [hmin i hlt]; simp only [Int.cast_zero, zero_mul]; exact not_VLe_zero_left ha_ne
      · exact absurd (Fin.ext heq) him
      · exact cc_not_VLe_intCast_mul (N i) (hsmall (i : ℕ) hgt (le_of_lt i.isLt)).2
  have hS_small : ¬ VLe S a := by
    rw [hS]
    exact VLe_add_strict htail.1 heps_small.1 htail.2 heps_small.2
  -- ## `T` is not smaller than `a`: `L = log z + (N m) * β` is bigger *or* smaller than `a`
  have hT_dom : VLe T a := by
    rw [hT]
    have hL : ¬ SameArch (log z + (N m : F) * β) a := hrho
    rcases hrel with hrel | hrel
    · have heq : log z + (N m : F) * log (X (m : ℕ))
          = (log z + (N m : F) * β) + (N m : F) * a := by rw [hrel]; ring
      rw [heq]
      exact CutCompAux.CutComp_VLe_add_intCast_mul hm hL
    · have heq : log z + (N m : F) * log (X (m : ℕ))
          = (log z + (N m : F) * β) + ((-(N m) : ℤ) : F) * a := by
        rw [hrel]; push_cast; ring
      rw [heq]
      exact CutCompAux.CutComp_VLe_add_intCast_mul (neg_ne_zero.mpr hm) hL
  -- ## The three "small" quantities are infinitesimal relative to `T`
  have hun_small : ¬ VLe (log (X n)) T := cc_not_VLe_of_not_VLe_of_VLe hsmall_n.2 hT_dom
  have hST : ¬ VLe S T := cc_not_VLe_of_not_VLe_of_VLe hS_small hT_dom
  have hZT : ¬ VLe Z T := by
    rw [hZ]; exact cc_not_VLe_intCast_mul Q hun_small
  have h2S : 2 * |S| < |T| := by
    simp only [VLe, not_exists, not_le] at hST
    have h := hST 1
    norm_num at h
    exact h
  have h2Z : 2 * |Z| < |T| := by
    simp only [VLe, not_exists, not_le] at hZT
    have h := hZT 1
    norm_num at h
    exact h
  -- ## The sign dichotomy, in both orientations
  have hstep1 : Z < T + S ↔ 0 < T := cc_order_step h2S h2Z
  have hstep2 : T + S < Z ↔ T < 0 := by
    have h := cc_order_step (T := -T) (S := -S) (Z := -Z)
      (by simpa using h2S) (by simpa using h2Z)
    rw [show -T + -S = -(T + S) from by ring, neg_lt_neg_iff, neg_pos] at h
    exact h
  -- ## Translating the two signs of `T`
  have hQpos : (0 : F) < (Q : F) := Int.cast_pos.mpr hQ
  have hlogiff : log (X n) < log w ↔ X n < w := hlog_lt (hXpos n) hw
  have hmuliff : (Q : F) * log (X n) < (Q : F) * log w ↔ log (X n) < log w :=
    mul_lt_mul_iff_of_pos_left hQpos
  have hZTS : Z < T + S ↔ (Q : F) * log (X n) < (Q : F) * log w := by rw [hZ, ← hTS]
  have hZTS2 : (Q : F) * log w < (Q : F) * log (X n) ↔ T + S < Z := by rw [hTS, hZ]
  have hzm_pos : 0 < z * X (m : ℕ) ^ (N m) := mul_pos hz (zpow_pos (hXpos (m : ℕ)) (N m))
  have hlogzm : log (z * X (m : ℕ) ^ (N m)) = log z + (N m : F) * log (X (m : ℕ)) := by
    rw [hlog_mul hz (zpow_pos (hXpos (m : ℕ)) (N m)), hlog_zpow (hXpos (m : ℕ)) (N m)]
  have hTpos : 0 < T ↔ 1 < z * X (m : ℕ) ^ (N m) := by
    have h1 : (1 < z * X (m : ℕ) ^ (N m) ↔ 0 < log (z * X (m : ℕ) ^ (N m))) :=
      cc_one_lt_iff_log_pos log hlog_lt hlog_mul hzm_pos
    rw [h1, hlogzm, hT]
  have hTneg : T < 0 ↔ log (z * X (m : ℕ) ^ (N m)) < 0 := by rw [hlogzm, ← hT]
  have hzlt : log (z * X (m : ℕ) ^ (N m)) < 0 ↔ z * X (m : ℕ) ^ (N m) < 1 := by
    have h := hlog_lt hzm_pos (show (0 : F) < 1 by norm_num)
    rw [cc_log_one log hlog_mul] at h
    exact h
  refine ⟨?_, ?_⟩
  · exact hlogiff.symm.trans (hmuliff.symm.trans (hZTS.symm.trans (hstep1.trans hTpos)))
  · have hlogiff2 : w < X n ↔ log w < log (X n) := (hlog_lt hw (hXpos n)).symm
    exact hlogiff2.trans ((mul_lt_mul_iff_of_pos_left hQpos).symm.trans
      (hZTS2.trans (hstep2.trans (hTneg.trans hzlt))))

end Work.WilC5
