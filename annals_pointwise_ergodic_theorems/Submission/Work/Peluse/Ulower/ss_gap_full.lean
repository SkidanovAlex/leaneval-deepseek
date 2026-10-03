import Mathlib
import Submission.Work.Peluse.Ulower.gap_transfer
import Submission.Work.Peluse.Ulower.ss_gap_peel_many
import Submission.Work.Peluse.Ulower.ssA.GapLocalBlock
import Submission.Work.Peluse.Ulower.ssA.MassBound
import Submission.Work.Peluse.Ulower.ssA.GapBalCore
import Submission.Work.Peluse.Ulower.ssGapQArith
import Submission.Work.Peluse.Ulower.ssGapNArith
import Submission.Work.Peluse.Ulower.ssGapProgArith
import Submission.Work.Peluse.Ulower.ss_gap_Pv_le_prog

/-!
# The gap regime of `Work.Peluse.ulowering_of`, with the full shift range `D ≤ N ^ P.natDegree`

This file is a copy of `Submission/Work/Peluse/Ulower/ss_gap_case.lean` with the shift bound
relaxed from `D ≤ N ^ d / 2` to `D ≤ N ^ d`: in the original proof that hypothesis is used
**only** to deduce `D ≤ N ^ P.natDegree` (the line
`have hDN : (D : ℝ) ≤ (N : ℝ) ^ P.natDegree := by linarith [hDle]`), and everything downstream
uses `hDN`.  Hence the same proof closes the gap case of `Work.Peluse.ulowering_of` for the
whole shift range `1 ≤ D ≤ N ^ d`, which is what the top-level assembly needs (the `D`-small
case `D ≤ N^d/2` is `Ulower/small_shift`, the non-gap case is `Ulower/ss_nongap`).

## Original header (for the account of the proof)

See `NOTES_small_shift_GAP_SESSION.md` for the account.  The gap regime (`2 N^d < N₀`, `N < 2N₀`)
is closed here from the *`D`-lossy* balanced core `Work.Peluse.Ulower.ssGapBalCore` (proved from
`PeluseU2Inverse` + `PeluseMajorArc` alone), the localisation `SsA.gap_local_block`, and the
transfer `gap_transfer`; no `D`-free core (hence no Peluse Theorem 3.3) is needed.

The two points which make the assembly work are

* the localisation produces a *balanced* instance (`N^d ≤ A₀·Ns ≤ A₀·N^d`) with a **data-free**
  constant `A₀`, so the core's exponent is data-free (in particular independent of `A'`);
* the core needs `D ≤ Ns`, while the localisation only gives `D ≤ N^d ≤ A₀·Ns`; replacing the
  localised scale `Ns` by `Ns' := max Ns D` repairs this: `D ≤ Ns'`, while `N^d ≤ A₀·Ns'` and
  `Ns' ≤ A₀·N^d` still hold.  The many-shift data transfers from the box `symIcc (dSup P Ns N)` to
  `symIcc (dSup P Ns' N)` at the cost of the box ratio (a data-free loss), by
  `boxNormPow_eq_mul_card`.

The remaining input is the pure real arithmetic of `ssGapQArith`, `ssGapNArith`, `ssGapProgArith`
and `ss_gap_Pv_le_prog`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

open scoped BigOperators
open Polynomial

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-- `progAvgSum 1 1 f = ∑' x, ‖f x‖`. -/
theorem ss_progAvgSum_one_one' (f : ℤ → ℂ) :
    Work.Peluse.progAvgSum 1 ((1 : ℕ) : ℤ) f = ∑' x : ℤ, ‖f x‖ := by
  rw [Work.Peluse.progAvgSum]
  have h1 : (∑' x : ℤ, ‖Work.Peluse.progAvg 1 ((1 : ℕ) : ℤ) f x‖)
      = ∑' x : ℤ, ‖f (x + 1)‖ := by
    apply tsum_congr
    intro x
    have hpt : Work.Peluse.progAvg 1 ((1 : ℕ) : ℤ) f x = f (x + 1) := by
      rw [Work.Peluse.progAvg, Finset.Icc_self, Finset.sum_singleton]
      norm_num
    rw [hpt]
  rw [h1]
  exact Equiv.tsum_eq (Equiv.addRight (1 : ℤ)) (fun z : ℤ => ‖f z‖)

/-- **The many-shift hypothesis transfers to a larger support box** at the cost of the ratio of the
two box cardinalities: the box norm depends on the box only through its normalising factor. -/
theorem ss_manyShifts_box_transfer' {P : Polynomial ℤ} {s Ns Ns' N D : ℕ} {f₀ f₁ : ℤ → ℂ}
    {δ γ : ℝ} (h : ManyShiftsHypDensity P s Ns N D f₀ f₁ δ γ) :
    ManyShiftsHypDensity P s Ns' N D f₀ f₁
      (δ * (((symIcc (dSup P Ns N)).card : ℝ) / ((symIcc (dSup P Ns' N)).card : ℝ))) γ := by
  obtain ⟨H, hmem, hcard, hlev⟩ := h
  refine ⟨H, hmem, hcard, fun sh hsh => ?_⟩
  have hSne : (symIcc (dSup P Ns N)).Nonempty := by
    rw [symIcc]; exact Finset.nonempty_Icc.mpr (by omega)
  have hkey := boxNormPow_eq_mul_card 2 (fun _ : Fin 2 => arithIcc P.leadingCoeff D)
      (symIcc (dSup P Ns' N)) (symIcc (dSup P Ns N))
      (iterDelta (s - 2) sh (dualFn N P f₀ f₁)) hSne
  rw [hkey]
  have hnonneg : (0 : ℝ) ≤
      ((symIcc (dSup P Ns N)).card : ℝ) / ((symIcc (dSup P Ns' N)).card : ℝ) := by positivity
  exact le_trans (mul_le_mul_of_nonneg_right (hlev sh hsh) hnonneg) (le_of_eq (mul_comm _ _))

/-! ## Elementary real arithmetic for the assembly -/

/-- `symIcc L` has `2L+1` elements. -/
private lemma ss_card_symIcc (L : ℕ) : (symIcc L).card = 2 * L + 1 := by
  rw [symIcc, Int.card_Icc]
  have h : ((L : ℤ) + 1 - (-(L : ℤ))) = ((2 * L + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

/-- `u * a ≤ t` with `u * v = 1` and `u > 0` is equivalent to `a ≤ t * v`. -/
private lemma ss_mul_le_iff {a t u v : ℝ} (hu : 0 < u) (huv : u * v = 1) :
    (u * a ≤ t) ↔ (a ≤ t * v) := by
  have hv0 : 0 < v := by
    by_contra hcon
    push_neg at hcon
    nlinarith [huv, hu, hcon]
  constructor
  · intro h
    have h1 : u * a * v ≤ t * v := mul_le_mul_of_nonneg_right h (le_of_lt hv0)
    calc a = a * (u * v) := by rw [huv, mul_one]
      _ = u * a * v := by ring
      _ ≤ t * v := h1
  · intro h
    have h1 : a * u ≤ t * v * u := mul_le_mul_of_nonneg_right h (le_of_lt hu)
    have h2 : t * v * u = t := by rw [mul_assoc, mul_comm v u, huv, mul_one]
    calc u * a = a * u := by ring
      _ ≤ t * v * u := h1
      _ = t := h2

/-- `(δ^{3k}(D/M)^{3k}) · ((M/D)^{3k}(δ⁻¹)^{3k}) = 1`. -/
private lemma ss_pow_inv_mul {k : ℕ} {D M del : ℝ} (hD0 : 0 < D) (hM0 : 0 < M)
    (hdel0 : 0 < del) :
    (del ^ (3 * k) * (D / M) ^ (3 * k)) * ((M / D) ^ (3 * k) * (del⁻¹) ^ (3 * k)) = 1 := by
  have h1 : (D / M) ^ (3 * k) * (M / D) ^ (3 * k) = 1 := by
    rw [← mul_pow]
    have h2 : (D / M) * (M / D) = 1 := by field_simp
    rw [h2, one_pow]
  have h2 : del ^ (3 * k) * (del⁻¹) ^ (3 * k) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hdel0), one_pow]
  calc (del ^ (3 * k) * (D / M) ^ (3 * k)) * ((M / D) ^ (3 * k) * (del⁻¹) ^ (3 * k))
      = (del ^ (3 * k) * (del⁻¹) ^ (3 * k)) * ((D / M) ^ (3 * k) * (M / D) ^ (3 * k)) := by ring
    _ = 1 := by rw [h2, h1, mul_one]

/-- **The cleared form of the display.**  If the three clauses hold in the "cleared" normalisation
(multiplied through by `δ^{3k}(D/M)^{3k} > 0`), then they hold in the form of `Display`. -/
private lemma ss_display_of_cleared {P : Polynomial ℤ} {k C : ℕ} {A' : ℝ} {N N₀ D : ℕ}
    {f₁ : ℤ → ℂ} {δ : ℝ} {q N' : ℕ}
    (hδ0 : 0 < δ) (hD0 : (0 : ℝ) < (D : ℝ)) (hN0 : (0 : ℝ) < (N : ℝ))
    (hq1 : 1 ≤ q) (hN'1 : 1 ≤ N') (hN'le : N' ≤ N)
    (hc1 : (q : ℝ) * (δ ^ (3 * k) * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ (3 * k))
        ≤ (C : ℝ) * A' ^ (3 * k))
    (hc2 : δ ^ (6 * k) * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ (6 * k) * (N : ℝ)
        ≤ (C : ℝ) * A' ^ (3 * k) * (N' : ℝ))
    (hc3 : δ ^ (6 * k) * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ (6 * k) * (N₀ : ℝ)
        ≤ (C : ℝ) * A' ^ (3 * k) * (progAvgSum N' (q : ℤ) f₁)) :
    Display P C (3 * k) A' N N₀ D f₁ δ := by
  have hM0 : (0 : ℝ) < (N : ℝ) ^ P.natDegree := pow_pos hN0 _
  have hu0 : 0 < δ ^ (3 * k) * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ (3 * k) := by positivity
  have huv := ss_pow_inv_mul (k := k) (D := (D : ℝ)) (M := (N : ℝ) ^ P.natDegree) hD0 hM0 hδ0
  have h6 : δ ^ (6 * k) * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ (6 * k)
      = (δ ^ (3 * k) * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ (3 * k))
        * (δ ^ (3 * k) * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ (3 * k)) := by
    rw [show 6 * k = 3 * k + 3 * k by ring, pow_add, pow_add]; ring
  refine ⟨q, N', hq1, ?_, hN'1, hN'le, ?_, ?_⟩
  · have h1 : (δ ^ (3 * k) * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ (3 * k)) * (q : ℝ)
        ≤ (C : ℝ) * A' ^ (3 * k) := by rw [mul_comm]; exact hc1
    have h := (ss_mul_le_iff (u := δ ^ (3 * k) * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ (3 * k))
      (v := ((N : ℝ) ^ P.natDegree / (D : ℝ)) ^ (3 * k) * (δ⁻¹) ^ (3 * k)) hu0 huv).mp h1
    refine le_trans h (le_of_eq ?_)
    ring
  · have h1 : (δ ^ (3 * k) * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ (3 * k))
        * ((δ ^ (3 * k) * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ (3 * k)) * (N : ℝ))
        ≤ (C : ℝ) * A' ^ (3 * k) * (N' : ℝ) := by
      rw [← mul_assoc, ← h6]; exact hc2
    have h := (ss_mul_le_iff (u := δ ^ (3 * k) * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ (3 * k))
      (v := ((N : ℝ) ^ P.natDegree / (D : ℝ)) ^ (3 * k) * (δ⁻¹) ^ (3 * k)) hu0 huv).mp h1
    refine le_trans h (le_of_eq ?_)
    ring
  · have h1 : (δ ^ (3 * k) * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ (3 * k))
        * ((δ ^ (3 * k) * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ (3 * k)) * (N₀ : ℝ))
        ≤ (C : ℝ) * A' ^ (3 * k) * (progAvgSum N' (q : ℤ) f₁) := by
      rw [← mul_assoc, ← h6]; exact hc3
    have h := (ss_mul_le_iff (u := δ ^ (3 * k) * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ (3 * k))
      (v := ((N : ℝ) ^ P.natDegree / (D : ℝ)) ^ (3 * k) * (δ⁻¹) ^ (3 * k)) hu0 huv).mp h1
    refine le_trans h (le_of_eq ?_)
    ring

/-- **The branch-A arithmetic (cleared form)**: if the target's own `N' = 1` clause holds, the
display's clauses with `q = N' = 1` follow from the `ℓ¹`-mass bound `δ·N₀ ≤ 4·S`. -/
private lemma ss_gap_branchA_cleared {k : ℕ} {D M N N₀ C A' del S : ℝ}
    (hk : 1 ≤ k) (hdel0 : 0 < del) (hdel1 : del ≤ 1) (hD0 : 0 < D) (hDM : D ≤ M)
    (hA1 : 1 ≤ A') (hC4 : 4 ≤ C) (hN₀0 : 0 ≤ N₀) (hS0 : 0 ≤ S)
    (hbrA : del ^ (6 * k) * (D / M) ^ (6 * k) * N ≤ C * A' ^ (3 * k))
    (hmass : del * N₀ ≤ 4 * S) :
    (1 : ℝ) * (del ^ (3 * k) * (D / M) ^ (3 * k)) ≤ C * A' ^ (3 * k) ∧
      del ^ (6 * k) * (D / M) ^ (6 * k) * N ≤ C * A' ^ (3 * k) * 1 ∧
      del ^ (6 * k) * (D / M) ^ (6 * k) * N₀ ≤ C * A' ^ (3 * k) * S := by
  have hM0 : 0 < M := lt_of_lt_of_le hD0 hDM
  have hDMnn : 0 ≤ D / M := by positivity
  have hDM1 : D / M ≤ 1 := by rw [div_le_one hM0]; exact hDM
  have hCA : 4 ≤ C * A' ^ (3 * k) := by
    have hA : (1 : ℝ) ≤ A' ^ (3 * k) := one_le_pow₀ hA1
    nlinarith [hC4, hA]
  refine ⟨?_, ?_, ?_⟩
  · have h1 : del ^ (3 * k) * (D / M) ^ (3 * k) ≤ 1 := by
      have ha : del ^ (3 * k) ≤ 1 := pow_le_one₀ (le_of_lt hdel0) hdel1
      have hb : (D / M) ^ (3 * k) ≤ 1 := pow_le_one₀ hDMnn hDM1
      calc del ^ (3 * k) * (D / M) ^ (3 * k) ≤ 1 * 1 :=
            mul_le_mul ha hb (by positivity) (by norm_num)
        _ = 1 := by norm_num
    calc (1 : ℝ) * (del ^ (3 * k) * (D / M) ^ (3 * k))
        = del ^ (3 * k) * (D / M) ^ (3 * k) := one_mul _
      _ ≤ 1 := h1
      _ ≤ C * A' ^ (3 * k) := by linarith [hCA]
  · simpa using hbrA
  · have h6 : del ^ (6 * k) ≤ del := by
      have h := pow_le_pow_of_le_one (le_of_lt hdel0) hdel1 (show 1 ≤ 6 * k by omega)
      simpa using h
    have hDM6 : (D / M) ^ (6 * k) ≤ 1 := pow_le_one₀ hDMnn hDM1
    have h3 : del ^ (6 * k) * (D / M) ^ (6 * k) ≤ C * A' ^ (3 * k) * del / 4 := by
      have h4 : del ^ (6 * k) * (D / M) ^ (6 * k) ≤ del * 1 :=
        mul_le_mul h6 hDM6 (by positivity) (le_of_lt hdel0)
      rw [mul_one] at h4
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
      nlinarith [h4, hCA, hdel0]
    calc del ^ (6 * k) * (D / M) ^ (6 * k) * N₀
        ≤ (C * A' ^ (3 * k) * del / 4) * N₀ := mul_le_mul_of_nonneg_right h3 hN₀0
      _ = C * A' ^ (3 * k) * (del * N₀ / 4) := by ring
      _ ≤ C * A' ^ (3 * k) * S := by
          have h5 : del * N₀ / 4 ≤ S := by linarith [hmass]
          exact mul_le_mul_of_nonneg_left h5 (by nlinarith [hCA])


/-! ## The gap case -/

/-- **The gap case of `PeluseULowering`** (`2 N^d < N₀`, `N < 2N₀`). -/
theorem ss_gap_case_full {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree)
    (h1 : Work.Peluse.PeluseU2Inverse) (h2 : Work.Peluse.PeluseMajorArc P) :
    ∀ s : ℕ, 2 ≤ s → ∃ C K : ℕ, 1 ≤ C ∧ 1 ≤ K ∧
      ∀ (A' : ℝ) (N N₀ D : ℕ) (f₀ f₁ : ℤ → ℂ) (δ : ℝ),
        2 ≤ P.natDegree → 1 ≤ A' → 1 ≤ N → 1 ≤ N₀ →
        (N₀ : ℝ) ≤ A' * (N : ℝ) ^ P.natDegree →
        (N : ℝ) ^ P.natDegree ≤ A' * (δ⁻¹) * (N₀ : ℝ) →
        2 * (N : ℝ) ^ P.natDegree < (N₀ : ℝ) → (N : ℝ) < 2 * (N₀ : ℝ) →
        0 < δ → δ ≤ 1 → 1 ≤ D → (D : ℝ) ≤ (N : ℝ) ^ P.natDegree →
        Work.Peluse.SupportIn f₀ N₀ → Work.Peluse.SupportIn f₁ N₀ →
        (∀ x : ℤ, ‖f₀ x‖ ≤ 1) → (∀ x : ℤ, ‖f₁ x‖ ≤ 1) →
        δ ≤ Work.Peluse.uNormPow s (Work.Peluse.arithIcc P.leadingCoeff D)
          (Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N)) (Work.Peluse.dualFn N P f₀ f₁) →
        Display P C K A' N N₀ D f₁ δ := by
  intro s hs
  obtain ⟨A₀, hA₀1, hloc⟩ := SsA.gap_local_block (P := P) hd s hs
  obtain ⟨C₀, k, hC₀1, hk1, hcore⟩ := ssGapBalCore (P := P) hd h1 h2 s hs A₀ hA₀1
  have hA₀R1 : (1 : ℝ) ≤ (A₀ : ℝ) := by exact_mod_cast hA₀1
  have hA₀R0 : (0 : ℝ) < (A₀ : ℝ) := lt_of_lt_of_le zero_lt_one hA₀R1
  have hC₀R1 : (1 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀1
  have hC₀R0 : (0 : ℝ) < (C₀ : ℝ) := lt_of_lt_of_le zero_lt_one hC₀R1
  set Δn : ℕ := 3 + 2 * (A₀ * (1 + coeffSum P)) with hΔdef
  have hΔn1 : 1 ≤ Δn := by rw [hΔdef]; omega
  have hΔR1 : (1 : ℝ) ≤ (Δn : ℝ) := by exact_mod_cast hΔn1
  set lc : ℝ := |(((P.leadingCoeff : ℤ)) : ℝ)| with hlcle
  have hlc0 : (0 : ℝ) ≤ lc := by rw [hlcle]; exact abs_nonneg _
  set c₀ : ℝ := 64 * (A₀ : ℝ) ^ 2 * (Δn : ℝ) * (1 + (s : ℝ) + lc) with hc₀def
  have hc₀0 : 0 < c₀ := by rw [hc₀def]; positivity
  set T1 : ℝ := (C₀ : ℝ) * c₀ ^ k * (A₀ : ℝ) ^ k with hT1def
  set T2 : ℝ := 4 * (C₀ : ℝ) ^ 2 * (c₀ * (A₀ : ℝ)) ^ (2 * k) * (A₀ : ℝ) with hT2def
  set T3 : ℝ := (c₀ * (A₀ : ℝ)) ^ k * (A₀ : ℝ) * (C₀ : ℝ) with hT3def
  set CR : ℝ := max 4 (max T1 (max T2 T3)) with hCRdef
  have hT1le : T1 ≤ CR := le_trans (le_max_left _ _) (le_max_right _ _)
  have hT2le : T2 ≤ CR := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hT3le : T3 ≤ CR :=
    le_trans (le_trans (le_max_right T2 T3) (le_max_right T1 (max T2 T3)))
      (le_max_right 4 (max T1 (max T2 T3)))
  have h4le : (4 : ℝ) ≤ CR := le_max_left _ _
  have hCR1 : (1 : ℝ) ≤ CR := le_trans (by norm_num : (1 : ℝ) ≤ 4) h4le
  have hCRpos : 0 < CR := lt_of_lt_of_le zero_lt_one hCR1
  have hT1leC : T1 ≤ (⌈CR⌉₊ : ℝ) := le_trans hT1le (Nat.le_ceil CR)
  have hT2leC : T2 ≤ (⌈CR⌉₊ : ℝ) := le_trans hT2le (Nat.le_ceil CR)
  have hT3leC : T3 ≤ (⌈CR⌉₊ : ℝ) := le_trans hT3le (Nat.le_ceil CR)
  have h4leC : (4 : ℝ) ≤ (⌈CR⌉₊ : ℝ) := le_trans h4le (Nat.le_ceil CR)
  have hCCCpos : (0 : ℝ) < (⌈CR⌉₊ : ℝ) :=
    lt_of_lt_of_le zero_lt_one (le_trans hCR1 (Nat.le_ceil CR))
  refine ⟨⌈CR⌉₊, 3 * k, Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hCRpos).ne', by omega, ?_⟩
  intro A' N N₀ D f₀ f₁ δ hd2 hA'1 hN hN₀ hsc1 hsc2 hgap hNlt hδ0 hδ1 hD1 hDle hf0 hf1 hb0 hb1 hhyp
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD1)
  have hDN : (D : ℝ) ≤ (N : ℝ) ^ P.natDegree := by linarith [hDle]
  have hNdpos : (0 : ℝ) < (N : ℝ) ^ P.natDegree := pow_pos hNpos _
  -- ## the peel and the mass bound
  obtain ⟨Hp, hHp1, hHp2, hHp3⟩ :=
    ss_gap_peel_many (P := P) hs hd2 hN hN₀ hD1 hDN hgap hδ0 hδ1 hf0 hf1 hb0 hb1 hhyp
  have hmanyδ : ManyShiftsHypδ P s N₀ N D f₀ f₁ δ := ⟨Hp, hHp1, hHp2, hHp3⟩
  have hmass := SsA.ss_mass_bound_of_manyShifts (P := P) hd2 hN hN₀ hD1 hDN hgap hδ0 hδ1 hf0 hf1
    hb0 hb1 hmanyδ
  have hmass4 : δ * (N₀ : ℝ) ≤ 4 * (∑' x : ℤ, ‖f₁ x‖) := by
    have hle : (N₀ : ℝ) ≤ ((2 * dSup P N₀ N + 1 : ℕ) : ℝ) := by
      have h2 : N₀ ≤ 2 * dSup P N₀ N + 1 := by rw [dSup]; omega
      exact_mod_cast h2
    nlinarith [hmass, hle]
  have hSnn : (0 : ℝ) ≤ ∑' x : ℤ, ‖f₁ x‖ := tsum_nonneg (fun x => norm_nonneg _)
  -- ## the localisation
  set γd : ℝ := δ / 4 / (1 + (s : ℝ) + lc) with hγddef
  have hγd0 : 0 < γd := by rw [hγddef]; positivity
  have hγd1 : γd ≤ 1 := by
    rw [hγddef, div_le_one (by positivity)]
    have h1 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    linarith [hlc0, hδ1]
  have hmanyD : ManyShiftsHypDensity P s N₀ N D f₀ f₁ (δ / 4) γd := by
    have h := manyShiftsHypDensity_of_hypδ (P := P) hmanyδ
    rw [hγddef]; exact h
  obtain ⟨a, Ns, δ', γ', hNs1, hNNs, hMdNs, hNsMd, ha, hδ'0, hγ'0, hδle, hγδle, hmanyD'⟩ :=
    hloc N N₀ D f₀ f₁ (δ / 4) γd hN hN₀ hD1 hDN hgap (by linarith [hδ0]) (by linarith [hδ1])
      hγd0 hγd1 hf0 hf1 hb0 hb1 hmanyD
  -- ## the enlarged scale `Ns' := max Ns D`
  set Ns' : ℕ := max Ns D with hNs'def
  have hNs'1 : 1 ≤ Ns' := le_trans hNs1 (le_max_left _ _)
  have hNNs' : N ≤ Ns' := by
    have h : (N : ℝ) ≤ (Ns' : ℝ) := le_trans hNNs (by exact_mod_cast (le_max_left Ns D))
    exact_mod_cast h
  have hDNs' : D ≤ Ns' := le_max_right _ _
  have hNs'R0 : (0 : ℝ) < (Ns' : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hNs'1)
  have hNs'le : (Ns' : ℝ) ≤ (A₀ : ℝ) * (N : ℝ) ^ P.natDegree := by
    rw [hNs'def, Nat.cast_max]
    refine max_le ?_ ?_
    · exact le_trans hNsMd (by nlinarith [hA₀R1])
    · exact le_trans hDN (by nlinarith [hA₀R1])
  have hNs'ge : (N : ℝ) ^ P.natDegree ≤ (A₀ : ℝ) * (Ns' : ℝ) := by
    have h2 : (Ns : ℝ) ≤ (Ns' : ℝ) := by exact_mod_cast (le_max_left Ns D)
    nlinarith [hMdNs, h2, hA₀R1]
  have hDNs'R : (D : ℝ) ≤ (Ns' : ℝ) := by exact_mod_cast hDNs'
  -- ## the box ratio
  have hMdNsN : N ^ P.natDegree ≤ A₀ * Ns := by exact_mod_cast hMdNs
  have hdSup_small : Ns ≤ dSup P Ns N := by rw [dSup]; exact Nat.le_add_right _ _
  have hdSup_big : dSup P Ns' N ≤ (1 + A₀ + coeffSum P * A₀) * Ns := by
    have h1 : Ns' ≤ Ns + D := by
      rw [hNs'def]; exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    have h2 : D ≤ N ^ P.natDegree := by exact_mod_cast hDN
    have h3 : D ≤ A₀ * Ns := le_trans h2 hMdNsN
    have h4 : polySup P N ≤ coeffSum P * A₀ * Ns := by
      refine le_trans (Work.Peluse.UlowerA.polySup_le_coeffSum_mul_pow P hN) ?_
      rw [mul_assoc]
      exact Nat.mul_le_mul_left (coeffSum P) hMdNsN
    rw [dSup]
    have h5 : Ns' + polySup P N ≤ (Ns + D) + coeffSum P * A₀ * Ns := Nat.add_le_add h1 h4
    have h6 : (Ns + D) + coeffSum P * A₀ * Ns ≤ (1 + A₀ + coeffSum P * A₀) * Ns := by
      nlinarith [h3]
    omega
  have hcard_big : ((symIcc (dSup P Ns' N)).card : ℝ) ≤ (Δn : ℝ) * (Ns : ℝ) := by
    rw [ss_card_symIcc]
    have h1 : 2 * dSup P Ns' N + 1 ≤ Δn * Ns := by
      have h2 : 2 * dSup P Ns' N + 1 ≤ 2 * ((1 + A₀ + coeffSum P * A₀) * Ns) + 1 := by
        omega
      have h3 : 2 * ((1 + A₀ + coeffSum P * A₀) * Ns) + 1
          ≤ (2 * (1 + A₀ + coeffSum P * A₀) + 1) * Ns := by
        rw [show (2 * (1 + A₀ + coeffSum P * A₀) + 1) * Ns
            = 2 * ((1 + A₀ + coeffSum P * A₀) * Ns) + Ns by ring]
        omega
      have h4 : Δn = 2 * (1 + A₀ + coeffSum P * A₀) + 1 := by rw [hΔdef]; ring
      rw [h4]
      exact le_trans h2 h3
    exact_mod_cast h1
  have hcard_small : (Ns : ℝ) ≤ ((symIcc (dSup P Ns N)).card : ℝ) := by
    rw [ss_card_symIcc]
    have h1 : Ns ≤ 2 * dSup P Ns N + 1 := by omega
    exact_mod_cast h1
  have hΔρ : (1 : ℝ) ≤
      (Δn : ℝ) * (((symIcc (dSup P Ns N)).card : ℝ) / ((symIcc (dSup P Ns' N)).card : ℝ)) := by
    have hBpos : (0 : ℝ) < ((symIcc (dSup P Ns' N)).card : ℝ) := by rw [ss_card_symIcc]; positivity
    have h1 : ((symIcc (dSup P Ns' N)).card : ℝ) ≤ (Δn : ℝ) * ((symIcc (dSup P Ns N)).card : ℝ) := by
      calc ((symIcc (dSup P Ns' N)).card : ℝ) ≤ (Δn : ℝ) * (Ns : ℝ) := hcard_big
        _ ≤ (Δn : ℝ) * ((symIcc (dSup P Ns N)).card : ℝ) :=
            mul_le_mul_of_nonneg_left hcard_small (by positivity)
    have h2 : (1 : ℝ) ≤
        ((Δn : ℝ) * ((symIcc (dSup P Ns N)).card : ℝ)) / ((symIcc (dSup P Ns' N)).card : ℝ) := by
      rw [le_div_iff₀ hBpos, one_mul]; exact h1
    have h3 : ((Δn : ℝ) * ((symIcc (dSup P Ns N)).card : ℝ)) / ((symIcc (dSup P Ns' N)).card : ℝ)
        = (Δn : ℝ) * (((symIcc (dSup P Ns N)).card : ℝ) / ((symIcc (dSup P Ns' N)).card : ℝ)) :=
      mul_div_assoc _ _ _
    linarith [h2, h3.le, h3.ge]
  set ρ' : ℝ := ((symIcc (dSup P Ns N)).card : ℝ) / ((symIcc (dSup P Ns' N)).card : ℝ) with hρ'def
  have hρ'0 : 0 < ρ' := by
    rw [hρ'def]
    apply div_pos <;> rw [ss_card_symIcc] <;> positivity
  have hΔρ' : (1 : ℝ) ≤ (Δn : ℝ) * ρ' := by rw [hρ'def]; exact hΔρ
  have htrans : ManyShiftsHypDensity P s Ns' N D (gapLocalise f₀ a Ns) (gapLocalise f₁ a Ns)
      (δ' * ρ') γ' := by
    have h := ss_manyShifts_box_transfer' (P := P) (Ns' := Ns') hmanyD'
    rw [hρ'def]; exact h
  set δc : ℝ := min 1 (δ' * ρ') with hδcdef
  set γc : ℝ := min 1 γ' with hγcdef
  have hδc0 : 0 < δc := by rw [hδcdef]; exact lt_min one_pos (mul_pos hδ'0 hρ'0)
  have hδc1 : δc ≤ 1 := by rw [hδcdef]; exact min_le_left _ _
  have hγc0 : 0 < γc := by rw [hγcdef]; exact lt_min one_pos hγ'0
  have hγc1 : γc ≤ 1 := by rw [hγcdef]; exact min_le_left _ _
  have hmanyD'' : ManyShiftsHypDensity P s Ns' N D (gapLocalise f₀ a Ns) (gapLocalise f₁ a Ns)
      δc γc := by
    obtain ⟨H, hmem, hcard, hlev⟩ := htrans
    refine ⟨H, hmem, ?_, ?_⟩
    · refine le_trans (mul_le_mul_of_nonneg_right ?_ (by positivity)) hcard
      rw [hγcdef]; exact min_le_right _ _
    · intro sh hsh
      exact le_trans (by rw [hδcdef]; exact min_le_right _ _) (hlev sh hsh)
  have hsup0' : Work.Peluse.SupportIn (gapLocalise f₀ a Ns) Ns' :=
    (supportIn_gapLocalise_self f₀ a Ns).mono (le_max_left _ _)
  have hsup1' : Work.Peluse.SupportIn (gapLocalise f₁ a Ns) Ns' :=
    (supportIn_gapLocalise_self f₁ a Ns).mono (le_max_left _ _)
  have hbd0' : ∀ x : ℤ, ‖gapLocalise f₀ a Ns x‖ ≤ 1 := norm_gapLocalise_le_one hb0 a Ns
  have hbd1' : ∀ x : ℤ, ‖gapLocalise f₁ a Ns x‖ ≤ 1 := norm_gapLocalise_le_one hb1 a Ns
  -- ## the core
  obtain ⟨q, N', hq1, hN'1, hN'le, hqbound, hN'bound, hprog⟩ :=
    hcore Ns' N D (gapLocalise f₀ a Ns) (gapLocalise f₁ a Ns) δc γc hd2 hN hNs'1 hD1
      (by exact_mod_cast hNNs') hNs'ge hNs'le hDNs'R hsup0' hsup1' hbd0' hbd1'
      hδc0 hδc1 hγc0 hγc1 hmanyD''
  -- ## the lower bounds on the level and the density
  have hδc_low : δ / (4 * (A₀ : ℝ) * (Δn : ℝ)) ≤ δc := by
    have h1 : δ / (4 * (A₀ : ℝ)) ≤ δ' := by
      rw [div_le_iff₀ (by positivity)] at hδle ⊢
      linarith [hδle]
    have hρ'' : 1 / (Δn : ℝ) ≤ ρ' := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < (Δn : ℝ))]
      linarith [hΔρ']
    have h2 : δ / (4 * (A₀ : ℝ)) * (1 / (Δn : ℝ)) ≤ δ' * ρ' :=
      mul_le_mul h1 hρ'' (by positivity) (by positivity)
    have h3 : δ / (4 * (A₀ : ℝ)) * (1 / (Δn : ℝ)) = δ / (4 * (A₀ : ℝ) * (Δn : ℝ)) := by
      field_simp; try ring
    have h4 : δ / (4 * (A₀ : ℝ) * (Δn : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [hδ1, hA₀R1, hΔR1]
    have h2' : δ / (4 * (A₀ : ℝ) * (Δn : ℝ)) ≤ δ' * ρ' := by rw [← h3]; exact h2
    rw [hδcdef]
    exact le_min h4 h2'
  have hγc_low : δ ^ 2 / (16 * (A₀ : ℝ) * (1 + (s : ℝ) + lc)) ≤ γc := by
    have h1 : γd * (δ / 4) / (A₀ : ℝ) ≤ γ' := by
      rw [div_le_iff₀ hA₀R0]
      linarith [hγδle]
    have h2 : δ ^ 2 / (16 * (A₀ : ℝ) * (1 + (s : ℝ) + lc)) = γd * (δ / 4) / (A₀ : ℝ) := by
      rw [hγddef]; field_simp; ring
    have h3 : δ ^ 2 / (16 * (A₀ : ℝ) * (1 + (s : ℝ) + lc)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [hδ1, hA₀R1, hlc0, (Nat.cast_nonneg s : (0 : ℝ) ≤ (s : ℝ))]
    rw [hγcdef]
    exact le_min h3 (le_trans (le_of_eq h2) h1)
  have hlam : δ ^ 3 / c₀ ≤ δc * γc := by
    have h1 : δ ^ 3 / c₀ =
        (δ / (4 * (A₀ : ℝ) * (Δn : ℝ))) * (δ ^ 2 / (16 * (A₀ : ℝ) * (1 + (s : ℝ) + lc))) := by
      rw [hc₀def]; field_simp; ring
    rw [h1]
    exact mul_le_mul hδc_low hγc_low (by positivity) (by positivity)
  have hA'2lt : 2 < A' := by
    have hlt : 2 * ((N : ℝ) ^ P.natDegree) < A' * ((N : ℝ) ^ P.natDegree) :=
      lt_of_lt_of_le hgap hsc1
    nlinarith [hlt, hNdpos]
  have hA'2 : (2 : ℝ) ≤ A' := le_of_lt hA'2lt
  have hNsq : (N : ℝ) * (N : ℝ) ≤ (N : ℝ) ^ P.natDegree := by
    have h2 : (N : ℝ) * (N : ℝ) = (N : ℝ) ^ 2 := by ring
    rw [h2]
    exact pow_le_pow_right₀ (by exact_mod_cast hN : (1 : ℝ) ≤ (N : ℝ)) hd2
  by_cases hbr : (⌈CR⌉₊ : ℝ) * A' ^ (3 * k)
      < δ ^ (6 * k) * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ (6 * k) * (N : ℝ)
  · -- ## the branch in which the core supplies `q, N'`
    have hqsh : (q : ℝ) ≤ (C₀ : ℝ) * c₀ ^ k * (A₀ : ℝ) ^ k * (δ⁻¹) ^ (3 * k)
        * (((N : ℝ) ^ P.natDegree) / (D : ℝ)) ^ k :=
      ss_gap_q_arith_sharp (k := k) (c0 := c₀) (C0 := (C₀ : ℝ)) (A0 := (A₀ : ℝ))
        (D := (D : ℝ)) (M := (N : ℝ) ^ P.natDegree) (Ns := (Ns' : ℝ)) (del := δ) (delc := δc)
        (gac := γc) (q := (q : ℝ)) hc₀0 hδ0 hδ1 hγc0 hδc0 hDR hDN hNs'R0.le hNs'le (le_of_lt hA₀R0) (le_of_lt hC₀R0)
        hlam hqbound
    have hqfull : (q : ℝ) ≤ T1 * (A' ^ (3 * k)
        * (((N : ℝ) ^ P.natDegree) / (D : ℝ)) ^ (3 * k) * (δ⁻¹) ^ (3 * k)) := by
      rw [hT1def]
      exact ss_gap_q_arith (k := k) (c0 := c₀) (C0 := (C₀ : ℝ)) (A0 := (A₀ : ℝ))
        (D := (D : ℝ)) (M := (N : ℝ) ^ P.natDegree) (Ns := (Ns' : ℝ)) (del := δ) (delc := δc)
        (gac := γc) (q := (q : ℝ)) hc₀0 hδ0 hδ1 hγc0 hδc0 hDR hDN hNs'R0.le hNs'le (le_of_lt hA₀R0) (le_of_lt hC₀R0)
        hA'1 hlam hqbound
    have hN'ge : δ ^ (6 * k) * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ (6 * k) * (N : ℝ)
        / ((⌈CR⌉₊ : ℝ) * A' ^ (3 * k)) ≤ (N' : ℝ) :=
      ss_gap_N'_arith (k := k) (c0 := c₀) (C0 := (C₀ : ℝ)) (A0 := (A₀ : ℝ)) (D := (D : ℝ))
        (M := (N : ℝ) ^ P.natDegree) (Ns := (Ns' : ℝ)) (del := δ) (delc := δc) (gac := γc)
        (A' := A') (N := (N : ℝ)) (C := (⌈CR⌉₊ : ℝ)) (N' := (N' : ℝ))
        hc₀0 hδ0 hδ1 hDR hDN hNdpos hNs'R0 hNs'le hA₀R0 hA'1 hC₀R0 hδc0 hγc0 hNpos hCCCpos
        hT1leC hlam hN'bound
    have hPv : δ ^ (3 * k) * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ k * ((N : ℝ) ^ P.natDegree)
        / ((c₀ * (A₀ : ℝ)) ^ k * (A₀ : ℝ) * (C₀ : ℝ))
        ≤ Work.Peluse.progAvgSum N' (q : ℤ) (gapLocalise f₁ a Ns) :=
      ss_gap_Pv_le_prog (k := k) (c0 := c₀) (C0 := (C₀ : ℝ)) (A0 := (A₀ : ℝ)) (D := (D : ℝ))
        (M := (N : ℝ) ^ P.natDegree) (Ns := (Ns' : ℝ)) (del := δ) (delc := δc) (gac := γc)
        (P := Work.Peluse.progAvgSum N' (q : ℤ) (gapLocalise f₁ a Ns))
        hk1 hc₀0 hC₀R0 hA₀R1 hδ0 hDR hNdpos hNs'R0 hlam hNs'le hprog
    have htr := gap_transfer (f := f₁) (N₀ := N₀) hf1 hb1 (N' := N') (q := (q : ℤ))
      (by exact_mod_cast hq1) a Ns
    rw [Int.natAbs_natCast] at htr
    have htr' : Work.Peluse.progAvgSum N' (q : ℤ) (gapLocalise f₁ a Ns)
        ≤ Work.Peluse.progAvgSum N' (q : ℤ) f₁ + 2 * ((N' : ℝ) * (q : ℝ)) := by
      have h := htr
      push_cast at h
      linarith [h]
    have hi := ss_gap_i (k := k) (c0 := c₀) (C0 := (C₀ : ℝ)) (A0 := (A₀ : ℝ)) (D := (D : ℝ))
      (M := (N : ℝ) ^ P.natDegree) (N0 := (N₀ : ℝ)) (C := (⌈CR⌉₊ : ℝ)) (A' := A') (del := δ)
      hk1 hc₀0 hA₀R1 hC₀R0 hδ0 hδ1 hDR hDN hNdpos hsc1 hA'2 hCCCpos hT3leC
    have hii := ss_gap_ii (k := k) (c0 := c₀) (C0 := (C₀ : ℝ)) (A0 := (A₀ : ℝ)) (D := (D : ℝ))
      (M := (N : ℝ) ^ P.natDegree) (N := (N : ℝ)) (C := (⌈CR⌉₊ : ℝ)) (A' := A') (del := δ)
      (Nprime := (N' : ℝ)) (q := (q : ℝ))
      hk1 hc₀0 hA₀R1 hC₀R0 hδ0 hδ1 hDR hDN hNdpos hNpos hA'1 hCCCpos hNsq hT2leC hbr hqsh
      (by positivity) (by exact_mod_cast hN'le)
    have hZpos : 0 < (c₀ * (A₀ : ℝ)) ^ k * (A₀ : ℝ) * (C₀ : ℝ) := by positivity
    have hD3 : δ ^ (6 * k) * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ (6 * k) * (N₀ : ℝ)
        / ((⌈CR⌉₊ : ℝ) * A' ^ (3 * k)) ≤ Work.Peluse.progAvgSum N' (q : ℤ) f₁ := by
      have h2 : 4 * (N' : ℝ) * (q : ℝ) ≤ δ ^ (3 * k)
          * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ k * ((N : ℝ) ^ P.natDegree)
          / ((c₀ * (A₀ : ℝ)) ^ k * (A₀ : ℝ) * (C₀ : ℝ)) := by
        rw [le_div_iff₀ hZpos]
        linarith [hii]
      linarith [hPv, htr', hi, h2]
    -- ## the cleared clauses
    have hcl : (q : ℝ) * (δ ^ (3 * k) * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ (3 * k))
        ≤ (⌈CR⌉₊ : ℝ) * A' ^ (3 * k) := by
      have hu0 : 0 < δ ^ (3 * k) * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ (3 * k) := by positivity
      have hu1 : (((N : ℝ) ^ P.natDegree / (D : ℝ)) ^ (3 * k) * (δ⁻¹) ^ (3 * k))
          * (δ ^ (3 * k) * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ (3 * k)) = 1 := by
        rw [mul_comm]
        exact ss_pow_inv_mul (k := k) (D := (D : ℝ)) (M := (N : ℝ) ^ P.natDegree) hDR hNdpos hδ0
      have h1 := mul_le_mul_of_nonneg_right hqfull (le_of_lt hu0)
      have h2 : T1 * (A' ^ (3 * k)
            * (((N : ℝ) ^ P.natDegree / (D : ℝ)) ^ (3 * k) * (δ⁻¹) ^ (3 * k)))
          * (δ ^ (3 * k) * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ (3 * k)) = T1 * A' ^ (3 * k) := by
        rw [show T1 * (A' ^ (3 * k)
              * (((N : ℝ) ^ P.natDegree / (D : ℝ)) ^ (3 * k) * (δ⁻¹) ^ (3 * k)))
            * (δ ^ (3 * k) * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ (3 * k))
            = T1 * A' ^ (3 * k) * ((((N : ℝ) ^ P.natDegree / (D : ℝ)) ^ (3 * k) * (δ⁻¹) ^ (3 * k))
              * (δ ^ (3 * k) * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ (3 * k))) by ring,
          hu1, mul_one]
      exact le_trans (by linarith [h1, h2.le, h2.ge]) (mul_le_mul_of_nonneg_right hT1leC (by positivity))
    refine ss_display_of_cleared (P := P) (k := k) (C := ⌈CR⌉₊) (A' := A') (N := N) (N₀ := N₀)
      (D := D) (f₁ := f₁) (δ := δ) (q := q) (N' := N') hδ0 hDR hNpos hq1 hN'1 hN'le hcl ?_ ?_
    · have h := (div_le_iff₀ (by positivity : (0 : ℝ) < (⌈CR⌉₊ : ℝ) * A' ^ (3 * k))).mp hN'ge
      calc δ ^ (6 * k) * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ (6 * k) * (N : ℝ)
          ≤ (N' : ℝ) * ((⌈CR⌉₊ : ℝ) * A' ^ (3 * k)) := h
        _ = (⌈CR⌉₊ : ℝ) * A' ^ (3 * k) * (N' : ℝ) := by ring
    · have h := (div_le_iff₀ (by positivity : (0 : ℝ) < (⌈CR⌉₊ : ℝ) * A' ^ (3 * k))).mp hD3
      calc δ ^ (6 * k) * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ (6 * k) * (N₀ : ℝ)
          ≤ Work.Peluse.progAvgSum N' (q : ℤ) f₁ * ((⌈CR⌉₊ : ℝ) * A' ^ (3 * k)) := h
        _ = (⌈CR⌉₊ : ℝ) * A' ^ (3 * k) * (Work.Peluse.progAvgSum N' (q : ℤ) f₁) := by ring
  · -- ## the branch in which `q = N' = 1` works
    push_neg at hbr
    obtain ⟨hb1, hb2, hb3⟩ := ss_gap_branchA_cleared (k := k) (D := (D : ℝ))
      (M := (N : ℝ) ^ P.natDegree) (N := (N : ℝ)) (N₀ := (N₀ : ℝ)) (C := (⌈CR⌉₊ : ℝ))
      (A' := A') (del := δ) (S := ∑' x : ℤ, ‖f₁ x‖)
      hk1 hδ0 hδ1 hDR hDN hA'1 h4leC (Nat.cast_nonneg N₀) hSnn hbr hmass4
    have hprogone : Work.Peluse.progAvgSum 1 ((1 : ℕ) : ℤ) f₁ = ∑' x : ℤ, ‖f₁ x‖ :=
      ss_progAvgSum_one_one' f₁
    refine ss_display_of_cleared (P := P) (k := k) (C := ⌈CR⌉₊) (A' := A') (N := N) (N₀ := N₀)
      (D := D) (f₁ := f₁) (δ := δ) (q := 1) (N' := 1) hδ0 hDR hNpos le_rfl le_rfl hN ?_ ?_ ?_
    · simpa using hb1
    · simpa using hb2
    · rw [hprogone]; exact hb3

end

end Work.Peluse.Ulower
