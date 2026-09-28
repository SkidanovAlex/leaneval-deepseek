import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.bigW_le_pow
import Submission.Work.HP.MM2.Sk2_loc_ell
import Submission.Work.HP.MM2.moebius_gcd_zeta
import Submission.Work.HP.MM2.gcd_div_gcd_eq
import Submission.Work.HP.MM2.loc_arith
import Submission.Work.HP.MM2.Sstar2_loc_tail
import Submission.Work.HP.SstarMobiusLoc
import Submission.Work.HP.DeltaXY_gcd_detL
import Submission.Work.HP.Sig2.omega_li
import Submission.Work.HP.six_le_NN
import Submission.Work.HP.Lat.detL_ge_one
import Submission.Work.HP.MDEstimates.zeta_tail_C
import Submission.Work.HP.MDEstimates.sumIccInvSq
import Submission.Work.HP.MDEstimates.Sigma1_estimate
import Submission.Work.HP.MDEstimates.veronese_linIndep

set_option maxHeartbeats 4000000

noncomputable section

open Filter Finset MeasureTheory

namespace Work.HP.MM2

open Work.HP

/-! ## Auxiliary lemmas (private) -/

private lemma int_finset_gcd_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℤ) :
    0 ≤ s.gcd f := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.gcd_insert]; exact Int.gcd_nonneg _ _

/-- `1 ≤ bigW w` as a real inequality. -/
private lemma one_le_bigW_real (w : ℝ) : (1 : ℝ) ≤ (bigW w : ℝ) := by
  have h := one_le_bigW w
  exact_mod_cast h

private lemma bigW_pos_real (w : ℝ) : 0 < (bigW w : ℝ) :=
  lt_of_lt_of_le zero_lt_one (one_le_bigW_real w)

private lemma natAbs_cast_of_nonneg (m : ℤ) (hm : 0 ≤ m) :
    (((m.natAbs : ℕ)) : ℝ) = (m : ℝ) := by
  rw [Nat.cast_natAbs, abs_of_nonneg (by exact_mod_cast hm)]

private lemma isPrim_ne_zero' {ι : Type*} [Fintype ι] {a : ι → ℤ} (h : IsPrim a) : a ≠ 0 := by
  intro h0
  have h1 : Finset.univ.gcd a = 0 :=
    Finset.gcd_eq_zero_iff.mpr (fun i _ => by rw [h0]; rfl)
  rw [IsPrim] at h
  rw [h] at h1
  exact one_ne_zero h1

private lemma eNorm_pos_of_ne_zero {ι : Type*} [Fintype ι] {v : ι → ℤ} (hv : v ≠ 0) :
    0 < eNorm v := by
  rw [eNorm, Real.sqrt_pos]
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hv (funext hcon)
  exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ i, by
    have h : ((v i : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hi
    positivity⟩

private lemma ne_of_linIndep_pair {n : ℕ} {x y : Fin (n + 1) → ℤ}
    (h : LinearIndependent ℤ ![x, y]) : x ≠ y := by
  intro hxy
  have hc := (LinearIndependent.pair_iff.mp h) 1 (-1) (by simp [hxy])
  norm_num at hc

private lemma ne_neg_of_linIndep_pair {n : ℕ} {x y : Fin (n + 1) → ℤ}
    (h : LinearIndependent ℤ ![x, y]) : x ≠ -y := by
  intro hxy
  have hc := (LinearIndependent.pair_iff.mp h) 1 1 (by simp [hxy])
  norm_num at hc

/-- The covolume `wedgeNorm (ν(x)) (ν(y))` is positive for linearly independent primitive `x,y`. -/
private lemma wedgeNorm_veronese_pos (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hn : 1 ≤ n)
    (x y : Fin (n + 1) → ℤ) (hx : IsPrim x) (hy : IsPrim y)
    (hxy : LinearIndependent ℤ ![x, y]) :
    0 < wedgeNorm (veronese d n x) (veronese d n y) := by
  have hD := DeltaXY_gcd_detL d n hd hn x y hx hy hxy
  have hEx : 0 < eNorm (veronese d n x) :=
    eNorm_pos_of_ne_zero (MDEstimates.veronese_ne_zero (isPrim_ne_zero' hx))
  have hEy : 0 < eNorm (veronese d n y) :=
    eNorm_pos_of_ne_zero (MDEstimates.veronese_ne_zero (isPrim_ne_zero' hy))
  have hdet : 0 < detL (Gam d n x y) := by
    have h := Lat.detL_ge_one (Gam d n x y); linarith
  have hGne : (gcdMinors2 x y : ℝ) ≠ 0 := by
    have h := DGG.gcdMinors2_ne_zero x y hxy
    exact_mod_cast h
  have hwne : wedgeNorm (veronese d n x) (veronese d n y) ≠ 0 := by
    intro h0
    have h2 : DeltaXY d n x y = 0 := by rw [DeltaXY, h0, div_zero]
    have h3 : DeltaXY d n x y * (gcdMinors2 x y : ℝ) = 0 := by rw [h2, zero_mul]
    rw [h3] at hD
    have h1 : 0 < eNorm (veronese d n x) * eNorm (veronese d n y) / detL (Gam d n x y) :=
      div_pos (mul_pos hEx hEy) hdet
    linarith
  exact lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hwne)

private lemma wedgeNorm_le_mul_own {ι : Type*} [Fintype ι] (v w : ι → ℤ) :
    wedgeNorm v w ≤ eNorm v * eNorm w := by
  have h1 : eNorm v ^ 2 * eNorm w ^ 2 - (dotR (toR v) (toR w)) ^ 2
      ≤ (eNorm v * eNorm w) ^ 2 := by
    rw [mul_pow]; linarith [sq_nonneg (dotR (toR v) (toR w))]
  calc wedgeNorm v w
      = Real.sqrt (eNorm v ^ 2 * eNorm w ^ 2 - (dotR (toR v) (toR w)) ^ 2) := rfl
    _ ≤ Real.sqrt ((eNorm v * eNorm w) ^ 2) := Real.sqrt_le_sqrt h1
    _ = eNorm v * eNorm w := Real.sqrt_sq (mul_nonneg (eNorm_nonneg v) (eNorm_nonneg w))

private lemma deltaXY_pos (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hn : 1 ≤ n)
    (x y : Fin (n + 1) → ℤ) (hx : IsPrim x) (hy : IsPrim y)
    (hxy : LinearIndependent ℤ ![x, y]) :
    0 < DeltaXY d n x y := by
  have hwp := wedgeNorm_veronese_pos d n hd hn x y hx hy hxy
  have hEx : 0 < eNorm (veronese d n x) :=
    eNorm_pos_of_ne_zero (MDEstimates.veronese_ne_zero (isPrim_ne_zero' hx))
  have hEy : 0 < eNorm (veronese d n y) :=
    eNorm_pos_of_ne_zero (MDEstimates.veronese_ne_zero (isPrim_ne_zero' hy))
  rw [DeltaXY]
  exact div_pos (mul_pos hEx hEy) hwp

private lemma one_le_deltaXY (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hn : 1 ≤ n)
    (x y : Fin (n + 1) → ℤ) (hx : IsPrim x) (hy : IsPrim y)
    (hxy : LinearIndependent ℤ ![x, y]) :
    1 ≤ DeltaXY d n x y := by
  have hwp := wedgeNorm_veronese_pos d n hd hn x y hx hy hxy
  rw [DeltaXY, le_div_iff₀ hwp]
  have h := wedgeNorm_le_mul_own (veronese d n x) (veronese d n y)
  linarith

private lemma loc_per_ell_main_eq (A al W Q g h V D l : ℝ) (N : ℕ) (hN : 2 ≤ N)
    (hl : l ≠ 0) (hal : al ≠ 0) (hW : W ≠ 0) (hQ : Q = W / g) (hg : g ≠ 0) :
    (1 / l ^ 2) * ((A / l) ^ (N - 2) * V * D * h / (al ^ 2 * Q ^ 2))
      = (A ^ (N - 2) * V * D / (al ^ 2 * W ^ 2)) * (h * g ^ 2 / l ^ N) := by
  subst hQ
  have hpow : l ^ N = l ^ (N - 2) * l ^ 2 := by
    rw [← pow_add]; congr 1; omega
  rw [div_pow, hpow]
  field_simp
  try ring

private lemma finsum_mem_subset_le {α : Type*} {S S' : Set α} (h : S ⊆ S') (hfin : S'.Finite)
    {f : α → ℝ} (hf : ∀ i, 0 ≤ f i) : (∑ᶠ i ∈ S, f i) ≤ ∑ᶠ i ∈ S', f i := by
  classical
  have h1 : (∑ᶠ i ∈ S, f i) = ∑ i ∈ hfin.toFinset, S.indicator f i := by
    rw [finsum_mem_def, finsum_eq_finsetSum_of_support_subset (s := hfin.toFinset)]
    intro i hi
    rw [Function.mem_support] at hi
    by_contra hc
    have hmem : i ∈ S := by
      by_contra hns
      exact hi (Set.indicator_of_notMem hns f)
    exact hc (by simpa using h hmem)
  have h2 : (∑ᶠ i ∈ S', f i) = ∑ i ∈ hfin.toFinset, S'.indicator f i := by
    rw [finsum_mem_def, finsum_eq_finsetSum_of_support_subset (s := hfin.toFinset)]
    intro i hi
    rw [Function.mem_support] at hi
    by_contra hc
    have hmem : i ∉ S' := fun hs => hc (by simpa using hs)
    exact hi (Set.indicator_of_notMem hmem f)
  rw [h1, h2]
  refine Finset.sum_le_sum (fun i _ => ?_)
  by_cases hmem : i ∈ S
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (h hmem)]
  · rw [Set.indicator_of_notMem hmem]
    by_cases h2 : i ∈ S'
    · rw [Set.indicator_of_mem h2]; exact hf i
    · rw [Set.indicator_of_notMem h2]

private lemma Sk_mono_le {d n : ℕ} [DecidableEq (Mon d n)] (k : ℕ)
    {L L' : Submodule ℤ (Mon d n → ℤ)} {R R' : Set (Mon d n → ℤ)}
    (hL : L ≤ L') (hR : R ⊆ R')
    (hfin : ({a : Mon d n → ℤ | a ∈ L' ∧ a ≠ 0 ∧ a ∈ R'}).Finite) :
    Sk d n k L R ≤ Sk d n k L' R' := by
  rw [Sk, Sk]
  refine finsum_mem_subset_le
    (S := {a : Mon d n → ℤ | a ∈ L ∧ a ≠ 0 ∧ a ∈ R})
    (S' := {a : Mon d n → ℤ | a ∈ L' ∧ a ≠ 0 ∧ a ∈ R'}) ?_ hfin ?_
  · rintro a ⟨h1, h2, h3⟩
    exact ⟨hL h1, h2, hR h3⟩
  · intro a
    exact div_nonneg zero_le_one (pow_nonneg (eNorm_nonneg a) k)

private lemma sum_Icc_split_one {f : ℕ → ℝ} {c b : ℕ} (hcb : c ≤ b) :
    (∑ l ∈ Finset.Icc 1 b, f l)
      = (∑ l ∈ Finset.Icc 1 c, f l) + ∑ l ∈ Finset.Icc (c + 1) b, f l := by
  have hunion : Finset.Icc 1 b = Finset.Icc 1 c ∪ Finset.Icc (c + 1) b := by
    ext l
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 c) (Finset.Icc (c + 1) b) :=
    Finset.disjoint_left.mpr (fun x hx hx' => by
      simp only [Finset.mem_Icc] at hx hx'
      omega)
  rw [hunion, Finset.sum_union hdisj]

private lemma abs_sum_sub_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    |(∑ i ∈ s, f i) - ∑ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

private lemma zetaR_pos_of (m : ℕ) (hm : 1 < m) : 0 < zetaR m := by
  have hsum : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ m) := by
    have h2 : Summable (fun j : ℕ => 1 / ((j : ℕ) : ℝ) ^ m) :=
      Real.summable_one_div_nat_pow.mpr hm
    have h3 := (summable_nat_add_iff (f := fun j : ℕ => 1 / ((j : ℕ) : ℝ) ^ m) 1).mpr h2
    refine h3.congr (fun k => ?_)
    simp only [Nat.cast_add, Nat.cast_one]
  rw [zetaR]
  exact Summable.tsum_pos hsum (fun k => by positivity) 0 (by norm_num)

private lemma sum_Icc_inv_pow_le_two (m : ℕ) (hm : 2 ≤ m) (K : ℕ) :
    (∑ l ∈ Finset.Icc 1 K, 1 / (l : ℝ) ^ m) ≤ 2 := by
  refine le_trans (Finset.sum_le_sum (fun l hl => ?_)) (MDEstimates.sumIccInvSq K)
  have h1 : 1 ≤ l := (Finset.mem_Icc.mp hl).1
  refine one_div_le_one_div_of_le (by positivity) ?_
  exact pow_le_pow_right₀ (by exact_mod_cast h1) hm

private lemma iotaDN_pos' (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) : 0 < iotaDN d n := by
  have h6 : 6 ≤ NN d n := six_le_NN d n hd hdn
  have h1 : 1 ≤ NN d n - 2 := by omega
  have h2 : 1 < NN d n - 2 := by omega
  rw [iotaDN]
  have hV := MDEstimates.ballVol_pos (NN d n - 2) h1
  have hz := zetaR_pos_of (NN d n - 2) h2
  positivity

/-- The per-`ℓ` main term of `Sk2_loc_ell` at `Q = bigW (wOf B)/gcd ℓ (bigW (wOf B))`,
`α = log B`, `T = A/ℓ`. -/
private abbrev locH (d n : ℕ) (B : ℝ) (x y : Fin (n + 1) → ℤ) (ℓ : ℕ) : ℝ :=
  ((Nat.gcd (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))) (gcdMinors2 x y).natAbs : ℕ) : ℝ)

private abbrev locg (d n : ℕ) (B : ℝ) (ℓ : ℕ) : ℝ := ((Nat.gcd ℓ (bigW (wOf B)) : ℕ) : ℝ)

private abbrev locQ (d n : ℕ) (B : ℝ) (ℓ : ℕ) : ℝ :=
  (((bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B)) : ℕ) : ℝ))

private abbrev locPerMain (d n : ℕ) (A B : ℝ) (x y : Fin (n + 1) → ℤ) (ℓ : ℕ) : ℝ :=
  (A / (ℓ : ℝ)) ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y *
    locH d n B x y ℓ / ((Real.log B) ^ 2 * (locQ d n B ℓ) ^ 2)

private abbrev locE1 (d n : ℕ) (C A B : ℝ) (x y : Fin (n + 1) → ℤ) (ℓ : ℕ) : ℝ :=
  C * locPerMain d n A B x y ℓ * min 1 (DeltaXY d n x y ^ 2 / (Real.log B) ^ 2)

private abbrev locE2 (d n : ℕ) (C A B : ℝ) (x y : Fin (n + 1) → ℤ) (ℓ : ℕ) : ℝ :=
  C * (A / (ℓ : ℝ)) ^ (NN d n - 3) * locH d n B x y ℓ / locQ d n B ℓ

private abbrev locE3 (d n : ℕ) (C A B : ℝ) (x y : Fin (n + 1) → ℤ) (ℓ : ℕ) : ℝ :=
  C * (locQ d n B ℓ) ^ (NN d n - 2)

private abbrev locPerErr (d n : ℕ) (C A B : ℝ) (x y : Fin (n + 1) → ℤ) (ℓ : ℕ) : ℝ :=
  locE1 d n C A B x y ℓ + locE2 d n C A B x y ℓ + locE3 d n C A B x y ℓ

/-- `A^{N-2} V Δ/(α²W²)`. -/
private abbrev locK (d n : ℕ) (A B : ℝ) (x y : Fin (n + 1) → ℤ) : ℝ :=
  A ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y /
    ((Real.log B) ^ 2 * (bigW (wOf B) : ℝ) ^ 2)

/-- `𝒢(x,y)` as a real. -/
private abbrev locG (d n : ℕ) (x y : Fin (n + 1) → ℤ) : ℝ :=
  (((gcdMinors2 x y).natAbs : ℕ) : ℝ)

/-- The predicted main term of the small-`ℓ` sum. -/
private abbrev locL (d n : ℕ) (A B : ℝ) (x y : Fin (n + 1) → ℤ) : ℝ :=
  locK d n A B x y * locG d n x y / zetaR (NN d n - 2)

private lemma locMain_pos' (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hdn : d ≤ n)
    (A B : ℝ) (x y : Fin (n + 1) → ℤ) (hx : IsPrim x) (hy : IsPrim y)
    (hxy : LinearIndependent ℤ ![x, y]) (hA : 0 < A) (hB : 1 < B) :
    0 < locMain d n A B (x, y) := by
  have hi : 0 < iotaDN d n := iotaDN_pos' d n hd hdn
  have hA2 : 0 < A ^ (NN d n - 2) := pow_pos hA _
  have hEx : 0 < eNorm (veronese d n x) :=
    eNorm_pos_of_ne_zero (MDEstimates.veronese_ne_zero (isPrim_ne_zero' hx))
  have hEy : 0 < eNorm (veronese d n y) :=
    eNorm_pos_of_ne_zero (MDEstimates.veronese_ne_zero (isPrim_ne_zero' hy))
  have hlogB : 0 < Real.log B := Real.log_pos hB
  have hW : 0 < (bigW (wOf B) : ℝ) := bigW_pos_real (wOf B)
  have hdet : 0 < detL (Gam d n x y) := lt_of_lt_of_le zero_lt_one (Lat.detL_ge_one _)
  have hnum : 0 < 8 * iotaDN d n * A ^ (NN d n - 2) *
      (eNorm (veronese d n x) * eNorm (veronese d n y)) := by positivity
  have hden : 0 < (Real.log B * (bigW (wOf B) : ℝ)) ^ 2 * detL (Gam d n x y) := by positivity
  rw [locMain]
  exact div_pos hnum hden

/-! ## The small-`ℓ` estimate -/

private theorem loc_small (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hdn : d ≤ n)
    (h22 : (d, n) ≠ (2, 2)) :
    ∃ C B₀ : ℝ, 0 < C ∧ ∀ A B : ℝ, B₀ ≤ B → B ^ ((5 : ℝ) / 6) ≤ A → A ≤ B ^ 2 →
      ∀ x y : Fin (n + 1) → ℤ, IsPrim x → IsPrim y → LinearIndependent ℤ ![x, y] →
      |(∑ ℓ ∈ Finset.Icc 1 ⌊A / (bigW (wOf B) : ℝ)⌋₊,
          ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) *
            Sk d n 2 (GamLoc d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
              (TlocSet d n x y (A / (ℓ : ℝ)) (Real.log B)))
        - locMain d n A B (x, y)|
        ≤ C * locMain d n A B (x, y) * (errXY d n B x y + 1 / Real.log A) := by
  classical
  obtain ⟨Csk, hCskpos, hSk⟩ := Sk2_loc_ell d n hd hdn h22
  obtain ⟨Cz, hCzpos, hZ⟩ := moebius_gcd_zeta (NN d n - 2) 2 (by have h := six_le_NN d n hd hdn; omega)
  have hVpos : 0 < ballVol (NN d n - 2) := MDEstimates.ballVol_pos _ (by have h := six_le_NN d n hd hdn; omega)
  have hzzpos : 0 < zetaR (NN d n - 2) := zetaR_pos_of _ (by have h := six_le_NN d n hd hdn; omega)
  set P0 : ℝ := 2 * Csk * zetaR (NN d n - 2) / ballVol (NN d n - 2) with hP0def
  set Q0 : ℝ := zetaR (NN d n - 2) * Cz * 2 ^ (NN d n) with hQ0def
  have hP0nn : 0 ≤ P0 := by rw [hP0def]; positivity
  have hQ0nn : 0 ≤ Q0 := by rw [hQ0def]; positivity
  set K0 : ℝ := 100 * P0 + Q0 + 1 with hK0def
  have hK0pos : 0 < K0 := by rw [hK0def]; linarith
  have hK0ge1 : 1 ≤ K0 := by rw [hK0def]; linarith
  have hK0geA : P0 ≤ K0 := by rw [hK0def]; linarith
  have hK0geB : 100 * P0 ≤ K0 := by rw [hK0def]; linarith
  have hK0geZ : Q0 ≤ K0 := by rw [hK0def]; linarith
  obtain ⟨Bar, har⟩ := loc_arith d n hd hdn h22 K0
  refine ⟨2 * Csk * zetaR (NN d n - 2) + 3 * zetaR (NN d n - 2) + 2 * K0 + 1,
      max Bar 100, by positivity, ?_⟩
  intro A B hB hBA hAB2 x y hx hy hxy
  have hBar : Bar ≤ B := le_trans (le_max_left _ _) hB
  obtain ⟨hA1, hlogA, hw1, hAW1, hW1, hWA, har1, har2, har3⟩ := har B hBar A hBA hAB2
  have hK0ex : K0 = 100 * (2 * Csk * zetaR (NN d n - 2) / ballVol (NN d n - 2))
      + zetaR (NN d n - 2) * Cz * 2 ^ (NN d n) + 1 := by
    rw [hK0def, hP0def, hQ0def]
  have hApos : 0 < A := by linarith
  have hB100 : 100 ≤ B := le_trans (le_max_right _ _) hB
  have hBpos : 0 < B := by linarith
  have hB1 : 1 < B := by linarith
  have hWpos : 0 < (bigW (wOf B) : ℝ) := by
    have h := one_le_bigW (wOf B); linarith
  have hWne : (bigW (wOf B) : ℝ) ≠ 0 := ne_of_gt hWpos
  have hlog2 : Real.log A ≤ 2 * Real.log B := by
    have h := Real.log_le_log hApos hAB2
    rwa [Real.log_pow] at h
  have halpos : 0 < Real.log B := by linarith
  have hlb : (1 / 2 : ℝ) ≤ Real.log B := by linarith
  have halne : Real.log B ≠ 0 := ne_of_gt halpos
  have hlogApos : 0 < Real.log A := by linarith
  have hlogAne : Real.log A ≠ 0 := ne_of_gt hlogApos
  have hN2 : 2 ≤ NN d n := by have h := six_le_NN d n hd hdn; omega
  have hN3 : 3 ≤ NN d n := by have h := six_le_NN d n hd hdn; omega
  have hNA : (NN d n - 2) + 2 = NN d n := by omega
  have hNB : (NN d n - 2) - 1 = NN d n - 3 := by omega
  have hn1 : 1 ≤ n := by omega
  have hDpos : 0 < DeltaXY d n x y := deltaXY_pos d n hd hn1 x y hx hy hxy
  have hD1 : 1 ≤ DeltaXY d n x y := one_le_deltaXY d n hd hn1 x y hx hy hxy
  have hG0pos : 0 < (gcdMinors2 x y).natAbs := by
    have h : 0 < gcdMinors2 x y := DGG.gcdMinors2_pos x y hxy
    omega
  have hG1 : 1 ≤ locG d n x y := by
    rw [locG]; exact_mod_cast hG0pos
  have hGpos : 0 < locG d n x y := lt_of_lt_of_le zero_lt_one hG1
  have hKpos : 0 < locK d n A B x y := by
    rw [locK]
    have h1 : 0 < A ^ (NN d n - 2) := pow_pos hApos _
    have h2 : 0 < (Real.log B) ^ 2 * (bigW (wOf B) : ℝ) ^ 2 := by positivity
    exact div_pos (by positivity) h2
  have hLpos : 0 < locL d n A B x y := by
    rw [locL]; exact div_pos (mul_pos hKpos hGpos) hzzpos
  have hLnn : 0 ≤ locL d n A B x y := le_of_lt hLpos
  have hLexpr : locL d n A B x y = A ^ (NN d n - 2) * ballVol (NN d n - 2)
      * DeltaXY d n x y * locG d n x y
      / ((Real.log B) ^ 2 * (bigW (wOf B) : ℝ) ^ 2 * zetaR (NN d n - 2)) := by
    rw [show locL d n A B x y = (locK d n A B x y) * (locG d n x y / zetaR (NN d n - 2))
        from by rw [locL]; ring]
    rw [show locK d n A B x y * (locG d n x y / zetaR (NN d n - 2))
        = A ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y * locG d n x y
          / ((Real.log B) ^ 2 * (bigW (wOf B) : ℝ) ^ 2 * zetaR (NN d n - 2))
        from by rw [locK, div_mul_div_comm]]
  set L0 : ℕ := ⌊A / (bigW (wOf B) : ℝ)⌋₊ with hL0
  have hAWleA : A / (bigW (wOf B) : ℝ) ≤ A := by
    rw [div_le_iff₀ hWpos]
    nlinarith [hApos, hW1]
  have hL0M : L0 ≤ ⌊A⌋₊ := by
    rw [hL0]; exact Nat.floor_mono hAWleA
  -- elementary bounds for the summands
  have hHle : ∀ ℓ : ℕ, locH d n B x y ℓ ≤ locG d n x y := by
    intro ℓ
    rw [locH, locG]
    exact_mod_cast (Nat.le_of_dvd hG0pos
      (Nat.gcd_dvd_right (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))) ((gcdMinors2 x y).natAbs)))
  have hHnn : ∀ ℓ : ℕ, 0 ≤ locH d n B x y ℓ := by
    intro ℓ; rw [locH]; exact_mod_cast Nat.zero_le _
  have hgle : ∀ ℓ : ℕ, 1 ≤ ℓ → locg d n B ℓ ≤ (ℓ : ℝ) := by
    intro ℓ hℓ1
    rw [locg]
    exact_mod_cast (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left ℓ (bigW (wOf B))))
  have hgnn : ∀ ℓ : ℕ, 0 ≤ locg d n B ℓ := by
    intro ℓ; rw [locg]; exact_mod_cast Nat.zero_le _
  have hQle : ∀ ℓ : ℕ, locQ d n B ℓ ≤ (bigW (wOf B) : ℝ) := by
    intro ℓ; rw [locQ]; exact_mod_cast Nat.div_le_self _ _
  have hQnn : ∀ ℓ : ℕ, 0 ≤ locQ d n B ℓ := by
    intro ℓ; rw [locQ]; exact_mod_cast Nat.zero_le _
  have hQcast : ∀ ℓ : ℕ, locQ d n B ℓ = (bigW (wOf B) : ℝ) / locg d n B ℓ := by
    intro ℓ
    have hgne : ((Nat.gcd ℓ (bigW (wOf B)) : ℕ) : ℝ) ≠ 0 := by
      have h1 : 0 < Nat.gcd ℓ (bigW (wOf B)) :=
        Nat.gcd_pos_of_pos_right ℓ (by have h := one_le_bigW (wOf B); omega)
      exact_mod_cast (show Nat.gcd ℓ (bigW (wOf B)) ≠ 0 by omega)
    rw [locQ, locg, Nat.cast_div (Nat.gcd_dvd_right ℓ (bigW (wOf B))) hgne]
  -- (1) the per-`ℓ` estimate
  have hper : ∀ ℓ ∈ Finset.Icc 1 L0,
      |Sk d n 2 (GamLoc d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
          (TlocSet d n x y (A / (ℓ : ℝ)) (Real.log B)) - locPerMain d n A B x y ℓ|
        ≤ locPerErr d n Csk A B x y ℓ := by
    intro ℓ hℓmem
    obtain ⟨hℓ1, hℓL0⟩ := Finset.mem_Icc.mp hℓmem
    have hℓpos : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ1
    have hℓL0R : (ℓ : ℝ) ≤ L0 := by exact_mod_cast hℓL0
    have hℓAW : (ℓ : ℝ) ≤ A / (bigW (wOf B) : ℝ) := by
      rw [hL0] at hℓL0R
      exact le_trans hℓL0R (Nat.floor_le (by positivity))
    have hQ1 : 1 ≤ bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B)) := by
      rw [Nat.le_div_iff_mul_le (Nat.gcd_pos_of_pos_right ℓ
        (by have h := one_le_bigW (wOf B); omega))]
      simpa using Nat.le_of_dvd (by have h := one_le_bigW (wOf B); omega)
        (Nat.gcd_dvd_right ℓ (bigW (wOf B)))
    have hQT : ((bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B)) : ℕ) : ℝ) ≤ A / (ℓ : ℝ) := by
      have h1 : ((bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B)) : ℕ) : ℝ)
          ≤ (bigW (wOf B) : ℝ) := by exact_mod_cast Nat.div_le_self _ _
      have h2 : (bigW (wOf B) : ℝ) ≤ A / (ℓ : ℝ) := by
        rw [le_div_iff₀ hℓpos]
        have h3 : (ℓ : ℝ) * (bigW (wOf B) : ℝ) ≤ A := (le_div_iff₀ hWpos).mp hℓAW
        linarith
      linarith
    have hres := hSk x y hx hy hxy (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B)))
      (Real.log B) (A / (ℓ : ℝ)) hQ1 halpos hQT
    simpa only [locPerMain, locPerErr, locE1, locE2, locE3, locH, locQ]
      using hres
  -- (2) the exact per-`ℓ` main-term identity
  have hid : ∀ ℓ : ℕ, 1 ≤ ℓ →
      (1 / (ℓ : ℝ) ^ 2) * locPerMain d n A B x y ℓ
        = locK d n A B x y *
            (locH d n B x y ℓ * (locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n)) := by
    intro ℓ hℓ1
    have hℓpos : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ1
    have hℓne : (ℓ : ℝ) ≠ 0 := ne_of_gt hℓpos
    have hgne : locg d n B ℓ ≠ 0 := by
      rw [locg]
      have h1 : 0 < Nat.gcd ℓ (bigW (wOf B)) :=
        Nat.gcd_pos_of_pos_right ℓ (by have h := one_le_bigW (wOf B); omega)
      exact_mod_cast (show Nat.gcd ℓ (bigW (wOf B)) ≠ 0 by omega)
    rw [locPerMain, locK, locH]
    exact loc_per_ell_main_eq A (Real.log B) (bigW (wOf B) : ℝ)
      (locQ d n B ℓ) (locg d n B ℓ) (locH d n B x y ℓ) (ballVol (NN d n - 2))
      (DeltaXY d n x y) (ℓ : ℝ) (NN d n) hN2 hℓne halne hWne (hQcast ℓ) hgne
  -- (3) sum identities and bounds
  have hsumId : (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ) ^ 2) * locPerMain d n A B x y ℓ)
      = locK d n A B x y * (∑ ℓ ∈ Finset.Icc 1 L0,
          locH d n B x y ℓ * (locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ℓ hℓ => ?_)
    exact hid ℓ (Finset.mem_Icc.mp hℓ).1
  have hsumBnd : (∑ ℓ ∈ Finset.Icc 1 L0,
        locH d n B x y ℓ * (locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n)) ≤ 2 * locG d n x y := by
    have hpt : ∀ ℓ ∈ Finset.Icc 1 L0,
        locH d n B x y ℓ * (locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n)
          ≤ locG d n x y / (ℓ : ℝ) ^ (NN d n - 2) := by
      intro ℓ hℓ
      have hℓ1 : 1 ≤ ℓ := (Finset.mem_Icc.mp hℓ).1
      have hℓpos : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ1
      have hg2 : (locg d n B ℓ) ^ 2 ≤ (ℓ : ℝ) ^ 2 := by
        have h := hgle ℓ hℓ1
        nlinarith [hgnn ℓ, h]
      have hsplit : (ℓ : ℝ) ^ (NN d n) = (ℓ : ℝ) ^ (NN d n - 2) * (ℓ : ℝ) ^ 2 := by
        rw [← pow_add, hNA]
      have hd2 : 0 < (ℓ : ℝ) ^ (NN d n - 2) := by positivity
      have h2 : (locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]; exact hg2
      calc locH d n B x y ℓ * (locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n)
          = (locH d n B x y ℓ / (ℓ : ℝ) ^ (NN d n - 2))
              * ((locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ 2) := by
            rw [hsplit]; field_simp; try ring
        _ ≤ (locG d n x y / (ℓ : ℝ) ^ (NN d n - 2)) * 1 := by
            refine mul_le_mul (div_le_div_of_nonneg_right (hHle ℓ) (le_of_lt hd2)) h2
              (by positivity) (by positivity)
        _ = locG d n x y / (ℓ : ℝ) ^ (NN d n - 2) := by ring
    calc (∑ ℓ ∈ Finset.Icc 1 L0,
          locH d n B x y ℓ * (locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n))
        ≤ ∑ ℓ ∈ Finset.Icc 1 L0, locG d n x y / (ℓ : ℝ) ^ (NN d n - 2) :=
          Finset.sum_le_sum hpt
      _ = locG d n x y * (∑ ℓ ∈ Finset.Icc 1 L0, 1 / (ℓ : ℝ) ^ (NN d n - 2)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun ℓ _ => by ring)
      _ ≤ locG d n x y * 2 :=
          mul_le_mul_of_nonneg_left (sum_Icc_inv_pow_le_two _ (by have h := six_le_NN d n hd hdn; omega) L0) (le_of_lt hGpos)
      _ = 2 * locG d n x y := by ring
  have hS1 : (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ) ^ 2) * locE1 d n Csk A B x y ℓ)
      ≤ 2 * Csk * zetaR (NN d n - 2) * locL d n A B x y
          * min 1 (DeltaXY d n x y ^ 2 / (Real.log B) ^ 2) := by
    have hstep : (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ) ^ 2) * locE1 d n Csk A B x y ℓ)
        = Csk * min 1 (DeltaXY d n x y ^ 2 / (Real.log B) ^ 2)
            * (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ) ^ 2) * locPerMain d n A B x y ℓ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ℓ _ => ?_)
      rw [locE1]; ring
    rw [hstep, hsumId]
    have hminnn : 0 ≤ min 1 (DeltaXY d n x y ^ 2 / (Real.log B) ^ 2) :=
      le_min zero_le_one (by positivity)
    have hkey : Csk * min 1 (DeltaXY d n x y ^ 2 / (Real.log B) ^ 2)
          * (locK d n A B x y * (2 * locG d n x y))
        = 2 * Csk * zetaR (NN d n - 2) * locL d n A B x y
          * min 1 (DeltaXY d n x y ^ 2 / (Real.log B) ^ 2) := by
      have hzzn : zetaR (NN d n - 2) ≠ 0 := ne_of_gt hzzpos
      rw [locL]; field_simp; try ring
    rw [← hkey]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (le_of_lt hCskpos) hminnn)
    exact mul_le_mul_of_nonneg_left hsumBnd (le_of_lt hKpos)
  have hlog4 : (Real.log B) ^ 2 ≤ 4 * (Real.log B) ^ 4 := by
    have h1 : 1 ≤ 4 * (Real.log B) ^ 2 := by nlinarith [hlb]
    calc (Real.log B) ^ 2 = (Real.log B) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (Real.log B) ^ 2 * (4 * (Real.log B) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 4 * (Real.log B) ^ 4 := by ring
  have hWpow : ∀ j : ℕ, j ≤ NN d n + 4 → (bigW (wOf B) : ℝ) ^ j
      ≤ (bigW (wOf B) : ℝ) ^ (NN d n + 4) := fun j hj =>
    pow_le_pow_right₀ (one_le_bigW_real (wOf B)) hj
  have har1' : K0 * (Real.log B) ^ 4 * (bigW (wOf B) : ℝ) ^ (NN d n + 4) * Real.log A ≤ A := by
    calc K0 * (Real.log B) ^ 4 * (bigW (wOf B) : ℝ) ^ (NN d n + 4) * Real.log A
        = K0 * (Real.log B) ^ 4 * (bigW (wOf B) : ℝ) ^ (NN d n + 4) / A
          * (A * Real.log A) := by field_simp; try ring
      _ ≤ (1 / Real.log A) * (A * Real.log A) :=
          mul_le_mul_of_nonneg_right har1 (by positivity)
      _ = A := by field_simp; try ring
  have har2' : K0 * (Real.log B) ^ 4 * (bigW (wOf B) : ℝ) ^ (NN d n + 4) * Real.log A
      ≤ A ^ (NN d n - 2) := by
    calc K0 * (Real.log B) ^ 4 * (bigW (wOf B) : ℝ) ^ (NN d n + 4) * Real.log A
        = K0 * (Real.log B) ^ 4 * (bigW (wOf B) : ℝ) ^ (NN d n + 4) / A ^ (NN d n - 2)
          * (A ^ (NN d n - 2) * Real.log A) := by field_simp; try ring
      _ ≤ (1 / Real.log A) * (A ^ (NN d n - 2) * Real.log A) :=
          mul_le_mul_of_nonneg_right har2 (by positivity)
      _ = A ^ (NN d n - 2) := by field_simp; try ring
  have hS2 : (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ) ^ 2) * locE2 d n Csk A B x y ℓ)
      ≤ K0 * locL d n A B x y / Real.log A := by
    have hbase : 2 * Csk * zetaR (NN d n - 2) * (Real.log B) ^ 2
        * (bigW (wOf B) : ℝ) * Real.log A ≤ A * ballVol (NN d n - 2) := by
      have hstep1 : (2 * Csk * zetaR (NN d n - 2) / ballVol (NN d n - 2))
          * (Real.log B) ^ 4 * (bigW (wOf B) : ℝ) ^ (NN d n + 4) * Real.log A
          ≤ A / 100 := by
        have hcoef : 2 * Csk * zetaR (NN d n - 2) / ballVol (NN d n - 2) ≤ K0 / 100 := by
          have hh := hK0geB
          rw [hP0def] at hh
          rw [le_div_iff₀ (by norm_num : (0:ℝ) < 100)]
          linarith [hh]
        calc (2 * Csk * zetaR (NN d n - 2) / ballVol (NN d n - 2))
              * (Real.log B) ^ 4 * (bigW (wOf B) : ℝ) ^ (NN d n + 4) * Real.log A
            ≤ (K0 / 100) * (Real.log B) ^ 4 * (bigW (wOf B) : ℝ) ^ (NN d n + 4)
                * Real.log A := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hcoef (by positivity)) (by positivity))
                (by positivity)
          _ = K0 * (Real.log B) ^ 4 * (bigW (wOf B) : ℝ) ^ (NN d n + 4) * Real.log A
                / 100 := by ring
          _ ≤ A / 100 := div_le_div_of_nonneg_right har1' (by norm_num)
      have h4 : (Real.log B) ^ 2 * (bigW (wOf B) : ℝ)
          ≤ 4 * (Real.log B) ^ 4 * (bigW (wOf B) : ℝ) ^ (NN d n + 4) := by
        calc (Real.log B) ^ 2 * (bigW (wOf B) : ℝ)
            = (Real.log B) ^ 2 * (bigW (wOf B) : ℝ) ^ 1 := by rw [pow_one]
          _ ≤ (4 * (Real.log B) ^ 4) * (bigW (wOf B) : ℝ) ^ (NN d n + 4) :=
              mul_le_mul hlog4 (hWpow 1 (by omega)) (by positivity) (by positivity)
          _ = 4 * (Real.log B) ^ 4 * (bigW (wOf B) : ℝ) ^ (NN d n + 4) := by ring
      calc 2 * Csk * zetaR (NN d n - 2) * (Real.log B) ^ 2
            * (bigW (wOf B) : ℝ) * Real.log A
          = 2 * Csk * zetaR (NN d n - 2) * Real.log A
              * ((Real.log B) ^ 2 * (bigW (wOf B) : ℝ)) := by ring
        _ ≤ 2 * Csk * zetaR (NN d n - 2) * Real.log A
              * (4 * (Real.log B) ^ 4 * (bigW (wOf B) : ℝ) ^ (NN d n + 4)) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = 4 * ((2 * Csk * zetaR (NN d n - 2) / ballVol (NN d n - 2))
              * (Real.log B) ^ 4 * (bigW (wOf B) : ℝ) ^ (NN d n + 4) * Real.log A)
              * ballVol (NN d n - 2) := by
            field_simp; try ring
        _ ≤ 4 * (A / 100) * ballVol (NN d n - 2) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hstep1 (by norm_num)) (le_of_lt hVpos)
        _ ≤ A * ballVol (NN d n - 2) := by nlinarith [hApos, hVpos]
    have hpt : ∀ ℓ ∈ Finset.Icc 1 L0,
        (1 / (ℓ : ℝ) ^ 2) * locE2 d n Csk A B x y ℓ
          ≤ Csk * A ^ (NN d n - 3) * locG d n x y
              / ((bigW (wOf B) : ℝ) * (ℓ : ℝ) ^ (NN d n - 2)) := by
      intro ℓ hℓ
      have hℓ1 : 1 ≤ ℓ := (Finset.mem_Icc.mp hℓ).1
      have hℓpos : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ1
      have hgpos : 0 < locg d n B ℓ := by
        rw [locg]
        have h1 : 0 < Nat.gcd ℓ (bigW (wOf B)) :=
          Nat.gcd_pos_of_pos_right ℓ (by have h := one_le_bigW (wOf B); omega)
        exact_mod_cast h1
      have hsplit : (ℓ : ℝ) ^ (NN d n - 1) = (ℓ : ℝ) ^ (NN d n - 2) * (ℓ : ℝ) := by
        rw [show NN d n - 1 = (NN d n - 2) + 1 by omega, pow_add, pow_one]
      have hnum : locH d n B x y ℓ * locg d n B ℓ ≤ locG d n x y * (ℓ : ℝ) := by
        have h1 := hHle ℓ
        have h2 := hgle ℓ hℓ1
        nlinarith [hHnn ℓ, hgnn ℓ, hGpos]
      have hQpos : 0 < locQ d n B ℓ := by
        rw [hQcast ℓ]; positivity
      have key : (1 / (ℓ : ℝ) ^ 2) * (Csk * (A ^ (NN d n - 3) / (ℓ : ℝ) ^ (NN d n - 3))
            * locH d n B x y ℓ / ((bigW (wOf B) : ℝ) / locg d n B ℓ))
          = Csk * A ^ (NN d n - 3) * (locH d n B x y ℓ * locg d n B ℓ)
              / ((bigW (wOf B) : ℝ) * (ℓ : ℝ) ^ (NN d n - 1)) := by
        rw [show (ℓ : ℝ) ^ (NN d n - 1) = (ℓ : ℝ) ^ (NN d n - 3) * (ℓ : ℝ) ^ 2 by
          rw [← pow_add]; congr 1; omega]
        field_simp
        try ring
      rw [locE2, hQcast ℓ, div_pow, key]
      rw [div_le_div_iff₀ (by positivity) (by positivity), hsplit]
      have h4 : 0 < A ^ (NN d n - 3) := pow_pos hApos _
      have hle1 : (ℓ : ℝ) ^ (NN d n - 2) ≤ (ℓ : ℝ) ^ (NN d n - 2) * (ℓ : ℝ) := by
        calc (ℓ : ℝ) ^ (NN d n - 2) = (ℓ : ℝ) ^ (NN d n - 2) * 1 := (mul_one _).symm
          _ ≤ (ℓ : ℝ) ^ (NN d n - 2) * (ℓ : ℝ) :=
              mul_le_mul_of_nonneg_left (by exact_mod_cast hℓ1) (by positivity)
      calc Csk * A ^ (NN d n - 3) * (locH d n B x y ℓ * locg d n B ℓ)
            * ((bigW (wOf B) : ℝ) * (ℓ : ℝ) ^ (NN d n - 2))
          ≤ Csk * A ^ (NN d n - 3) * (locG d n x y * (ℓ : ℝ))
            * ((bigW (wOf B) : ℝ) * (ℓ : ℝ) ^ (NN d n - 2)) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnum (by positivity))
              (by positivity)
        _ = Csk * A ^ (NN d n - 3) * locG d n x y
            * ((bigW (wOf B) : ℝ) * ((ℓ : ℝ) ^ (NN d n - 2) * (ℓ : ℝ))) := by ac_rfl
    calc (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ) ^ 2) * locE2 d n Csk A B x y ℓ)
        ≤ ∑ ℓ ∈ Finset.Icc 1 L0, Csk * A ^ (NN d n - 3) * locG d n x y
            / ((bigW (wOf B) : ℝ) * (ℓ : ℝ) ^ (NN d n - 2)) := Finset.sum_le_sum hpt
      _ = Csk * A ^ (NN d n - 3) * locG d n x y / (bigW (wOf B) : ℝ)
            * (∑ ℓ ∈ Finset.Icc 1 L0, 1 / (ℓ : ℝ) ^ (NN d n - 2)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun ℓ _ => ?_)
          field_simp
          try ring
      _ ≤ Csk * A ^ (NN d n - 3) * locG d n x y / (bigW (wOf B) : ℝ) * 2 := by
          refine mul_le_mul_of_nonneg_left (sum_Icc_inv_pow_le_two _ (by have h := six_le_NN d n hd hdn; omega) L0) ?_
          positivity
      _ = 2 * Csk * A ^ (NN d n - 3) * locG d n x y / (bigW (wOf B) : ℝ) := by ring
      _ ≤ K0 * locL d n A B x y / Real.log A := by
        rw [le_div_iff₀ hlogApos]
        have hXnn : 0 ≤ A ^ (NN d n - 3) * DeltaXY d n x y * locG d n x y
            / ((Real.log B) ^ 2 * (bigW (wOf B) : ℝ) ^ 2 * zetaR (NN d n - 2)) := by positivity
        have hmul := mul_le_mul_of_nonneg_right hbase hXnn
        have hh1 : (2 * Csk * zetaR (NN d n - 2) * (Real.log B) ^ 2 * (bigW (wOf B) : ℝ)
              * Real.log A) * (A ^ (NN d n - 3) * DeltaXY d n x y * locG d n x y
                / ((Real.log B) ^ 2 * (bigW (wOf B) : ℝ) ^ 2 * zetaR (NN d n - 2)))
            = 2 * Csk * A ^ (NN d n - 3) * DeltaXY d n x y * locG d n x y * Real.log A
              / (bigW (wOf B) : ℝ) := by
          field_simp
          try ring
        have hh2 : (A * ballVol (NN d n - 2)) * (A ^ (NN d n - 3) * DeltaXY d n x y
                * locG d n x y
                / ((Real.log B) ^ 2 * (bigW (wOf B) : ℝ) ^ 2 * zetaR (NN d n - 2)))
            = locL d n A B x y := by
          rw [hLexpr]
          rw [show (A * ballVol (NN d n - 2)) * (A ^ (NN d n - 3) * DeltaXY d n x y
                * locG d n x y
                / ((Real.log B) ^ 2 * (bigW (wOf B) : ℝ) ^ 2 * zetaR (NN d n - 2)))
              = A ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y * locG d n x y
                / ((Real.log B) ^ 2 * (bigW (wOf B) : ℝ) ^ 2 * zetaR (NN d n - 2)) by
            rw [show A ^ (NN d n - 2) = A * A ^ (NN d n - 3) by
              rw [show NN d n - 2 = (NN d n - 3) + 1 by omega, pow_add, pow_one]
              ring]
            ring]
          try ring
        have hmul2 : 2 * Csk * A ^ (NN d n - 3) * DeltaXY d n x y * locG d n x y * Real.log A
              / (bigW (wOf B) : ℝ) ≤ locL d n A B x y := by
          rw [hh1] at hmul
          rw [hh2] at hmul
          exact hmul
        have hstep : 2 * Csk * A ^ (NN d n - 3) * locG d n x y * Real.log A
            / (bigW (wOf B) : ℝ)
            ≤ 2 * Csk * A ^ (NN d n - 3) * DeltaXY d n x y * locG d n x y * Real.log A
              / (bigW (wOf B) : ℝ) := by
          refine div_le_div_of_nonneg_right ?_ (le_of_lt hWpos)
          have h1 : 2 * Csk * A ^ (NN d n - 3) * locG d n x y
              ≤ 2 * Csk * A ^ (NN d n - 3) * DeltaXY d n x y * locG d n x y := by
            calc 2 * Csk * A ^ (NN d n - 3) * locG d n x y
                = 2 * Csk * A ^ (NN d n - 3) * 1 * locG d n x y := by ring
              _ ≤ 2 * Csk * A ^ (NN d n - 3) * DeltaXY d n x y * locG d n x y :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hD1 (by positivity)) (le_of_lt hGpos)
          exact mul_le_mul_of_nonneg_right h1 (le_of_lt hlogApos)
        rw [show 2 * Csk * A ^ (NN d n - 3) * locG d n x y / (bigW (wOf B) : ℝ)
              * Real.log A
            = 2 * Csk * A ^ (NN d n - 3) * locG d n x y * Real.log A
              / (bigW (wOf B) : ℝ) from by ring]
        calc 2 * Csk * A ^ (NN d n - 3) * locG d n x y * Real.log A / (bigW (wOf B) : ℝ)
            ≤ 2 * Csk * A ^ (NN d n - 3) * DeltaXY d n x y * locG d n x y * Real.log A
              / (bigW (wOf B) : ℝ) := hstep
          _ ≤ locL d n A B x y := hmul2
          _ ≤ K0 * locL d n A B x y := by nlinarith [hLnn, hK0ge1]
  have hS3 : (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ) ^ 2) * locE3 d n Csk A B x y ℓ)
      ≤ K0 * locL d n A B x y / Real.log A := by
    have hbase : 2 * Csk * zetaR (NN d n - 2) * (Real.log B) ^ 2
        * (bigW (wOf B) : ℝ) ^ (NN d n) * Real.log A
        ≤ A ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y * locG d n x y := by
      have hstep1 : (2 * Csk * zetaR (NN d n - 2) / ballVol (NN d n - 2))
          * (Real.log B) ^ 4 * (bigW (wOf B) : ℝ) ^ (NN d n + 4) * Real.log A
          ≤ A ^ (NN d n - 2) / 100 := by
        have hcoef : 2 * Csk * zetaR (NN d n - 2) / ballVol (NN d n - 2) ≤ K0 / 100 := by
          rw [le_div_iff₀ (by norm_num : (0:ℝ) < 100)]
          linarith [hK0geB]
        calc (2 * Csk * zetaR (NN d n - 2) / ballVol (NN d n - 2))
              * (Real.log B) ^ 4 * (bigW (wOf B) : ℝ) ^ (NN d n + 4) * Real.log A
            ≤ (K0 / 100) * (Real.log B) ^ 4 * (bigW (wOf B) : ℝ) ^ (NN d n + 4)
                * Real.log A := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hcoef (by positivity)) (by positivity))
                (by positivity)
          _ = K0 * (Real.log B) ^ 4 * (bigW (wOf B) : ℝ) ^ (NN d n + 4) * Real.log A
                / 100 := by ring
          _ ≤ A ^ (NN d n - 2) / 100 :=
              div_le_div_of_nonneg_right har2' (by norm_num)
      have h4 : (Real.log B) ^ 2 * (bigW (wOf B) : ℝ) ^ (NN d n)
          ≤ 4 * (Real.log B) ^ 4 * (bigW (wOf B) : ℝ) ^ (NN d n + 4) :=
        mul_le_mul hlog4 (hWpow _ (by omega)) (by positivity) (by positivity)
      calc 2 * Csk * zetaR (NN d n - 2) * (Real.log B) ^ 2
            * (bigW (wOf B) : ℝ) ^ (NN d n) * Real.log A
          = 2 * Csk * zetaR (NN d n - 2) * Real.log A
              * ((Real.log B) ^ 2 * (bigW (wOf B) : ℝ) ^ (NN d n)) := by ring
        _ ≤ 2 * Csk * zetaR (NN d n - 2) * Real.log A
              * (4 * (Real.log B) ^ 4 * (bigW (wOf B) : ℝ) ^ (NN d n + 4)) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = 4 * ((2 * Csk * zetaR (NN d n - 2) / ballVol (NN d n - 2))
              * (Real.log B) ^ 4 * (bigW (wOf B) : ℝ) ^ (NN d n + 4) * Real.log A)
              * ballVol (NN d n - 2) := by
            field_simp; try ring
        _ ≤ 4 * (A ^ (NN d n - 2) / 100) * ballVol (NN d n - 2) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hstep1 (by norm_num)) (le_of_lt hVpos)
        _ ≤ A ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y * locG d n x y := by
            have h1 : 4 * (A ^ (NN d n - 2) / 100) * ballVol (NN d n - 2)
                ≤ A ^ (NN d n - 2) * ballVol (NN d n - 2) := by
              nlinarith [hApos, hVpos, pow_pos hApos (NN d n - 2)]
            have h2 : A ^ (NN d n - 2) * ballVol (NN d n - 2)
                ≤ A ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y := by
              calc A ^ (NN d n - 2) * ballVol (NN d n - 2)
                  = A ^ (NN d n - 2) * ballVol (NN d n - 2) * 1 := (mul_one _).symm
                _ ≤ A ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y :=
                    mul_le_mul_of_nonneg_left hD1 (by positivity)
            have h3 : A ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y
                ≤ A ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y
                  * locG d n x y := by
              calc A ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y
                  = A ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y * 1 :=
                    (mul_one _).symm
                _ ≤ A ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y
                      * locG d n x y := mul_le_mul_of_nonneg_left hG1 (by positivity)
            linarith [h1, h2, h3]
    have hpt : ∀ ℓ ∈ Finset.Icc 1 L0,
        (1 / (ℓ : ℝ) ^ 2) * locE3 d n Csk A B x y ℓ
          ≤ Csk * (bigW (wOf B) : ℝ) ^ (NN d n - 2) / (ℓ : ℝ) ^ 2 := by
      intro ℓ hℓ
      have hQle' := hQle ℓ
      have hpow : (locQ d n B ℓ) ^ (NN d n - 2) ≤ (bigW (wOf B) : ℝ) ^ (NN d n - 2) :=
        pow_le_pow_left₀ (hQnn ℓ) hQle' _
      have h3 : 0 < (ℓ : ℝ) ^ 2 := by
        have hℓ1 : 1 ≤ ℓ := (Finset.mem_Icc.mp hℓ).1
        positivity
      rw [locE3]
      have hnorm : (1 / (ℓ : ℝ) ^ 2) * (Csk * (locQ d n B ℓ) ^ (NN d n - 2))
          = Csk * (locQ d n B ℓ) ^ (NN d n - 2) / (ℓ : ℝ) ^ 2 := by ring
      rw [hnorm, div_le_div_iff₀ h3 (by positivity)]
      calc Csk * (locQ d n B ℓ) ^ (NN d n - 2) * (ℓ : ℝ) ^ 2
          ≤ Csk * (bigW (wOf B) : ℝ) ^ (NN d n - 2) * (ℓ : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (le_of_lt hCskpos))
              (by positivity)
        _ = Csk * (bigW (wOf B) : ℝ) ^ (NN d n - 2) * (ℓ : ℝ) ^ 2 := rfl
    calc (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ) ^ 2) * locE3 d n Csk A B x y ℓ)
        ≤ ∑ ℓ ∈ Finset.Icc 1 L0, Csk * (bigW (wOf B) : ℝ) ^ (NN d n - 2) / (ℓ : ℝ) ^ 2 :=
          Finset.sum_le_sum hpt
      _ = Csk * (bigW (wOf B) : ℝ) ^ (NN d n - 2)
            * (∑ ℓ ∈ Finset.Icc 1 L0, 1 / (ℓ : ℝ) ^ 2) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun ℓ _ => by ring)
      _ ≤ Csk * (bigW (wOf B) : ℝ) ^ (NN d n - 2) * 2 :=
          mul_le_mul_of_nonneg_left (MDEstimates.sumIccInvSq L0) (by positivity)
      _ = 2 * Csk * (bigW (wOf B) : ℝ) ^ (NN d n - 2) := by ring
      _ ≤ K0 * locL d n A B x y / Real.log A := by
        rw [le_div_iff₀ hlogApos]
        have hXnn : 0 ≤ (1 : ℝ) / ((Real.log B) ^ 2 * (bigW (wOf B) : ℝ) ^ 2
            * zetaR (NN d n - 2)) := by positivity
        have hmul := mul_le_mul_of_nonneg_right hbase hXnn
        have hh1 : (2 * Csk * zetaR (NN d n - 2) * (Real.log B) ^ 2
              * (bigW (wOf B) : ℝ) ^ (NN d n) * Real.log A)
              * (1 / ((Real.log B) ^ 2 * (bigW (wOf B) : ℝ) ^ 2 * zetaR (NN d n - 2)))
            = 2 * Csk * (bigW (wOf B) : ℝ) ^ (NN d n - 2) * Real.log A := by
          rw [show (bigW (wOf B) : ℝ) ^ (NN d n)
              = (bigW (wOf B) : ℝ) ^ (NN d n - 2) * (bigW (wOf B) : ℝ) ^ 2 by
            rw [← pow_add, hNA]]
          field_simp
          try ring
        have hh2 : (A ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y
              * locG d n x y)
              * (1 / ((Real.log B) ^ 2 * (bigW (wOf B) : ℝ) ^ 2 * zetaR (NN d n - 2)))
            = locL d n A B x y := by
          rw [hLexpr]
          ring
        rw [hh1, hh2] at hmul
        calc 2 * Csk * (bigW (wOf B) : ℝ) ^ (NN d n - 2) * Real.log A
            ≤ locL d n A B x y := hmul
          _ ≤ K0 * locL d n A B x y := by nlinarith [hLnn, hK0ge1]
  -- (4) the main Möbius sum
  have hTEq : (∑ ℓ ∈ Finset.Icc 1 L0,
        ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) * locPerMain d n A B x y ℓ)
      = locK d n A B x y * (∑ ℓ ∈ Finset.Icc 1 L0,
          (ArithmeticFunction.moebius ℓ : ℝ)
            * (locH d n B x y ℓ * (locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ℓ hℓ => ?_)
    rw [show (ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2 * locPerMain d n A B x y ℓ
        = (ArithmeticFunction.moebius ℓ : ℝ) * ((1 / (ℓ : ℝ) ^ 2)
          * locPerMain d n A B x y ℓ) from by ring,
      hid ℓ (Finset.mem_Icc.mp hℓ).1]
    ring
  have hzz1 : 1 ≤ zetaR (NN d n - 2) := by
    have hsum : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ (NN d n - 2)) := by
      have h2 : Summable (fun j : ℕ => 1 / ((j : ℕ) : ℝ) ^ (NN d n - 2)) :=
        Real.summable_one_div_nat_pow.mpr (by have h := six_le_NN d n hd hdn; omega)
      have h3 := (summable_nat_add_iff (f := fun j : ℕ => 1 / ((j : ℕ) : ℝ) ^ (NN d n - 2))
        1).mpr h2
      refine h3.congr (fun k => ?_)
      simp only [Nat.cast_add, Nat.cast_one]
    have hle := Summable.le_tsum hsum 0 (fun j _ => by positivity :
      ∀ j : ℕ, j ≠ 0 → 0 ≤ 1 / ((j : ℝ) + 1) ^ (NN d n - 2))
    rw [zetaR]
    refine le_trans ?_ hle
    norm_num
  have hT1bd : ¬ ((gcdMinors2 x y) ∣ ((bigW (wOf B) / radW (wOf B) : ℕ) : ℤ)) →
      |(∑ ℓ ∈ Finset.Icc 1 L0, (ArithmeticFunction.moebius ℓ : ℝ)
            * (locH d n B x y ℓ * (locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n)))
          - locG d n x y / zetaR (NN d n - 2)| ≤ 3 * locG d n x y := by
    intro hbad
    have h1 : |(∑ ℓ ∈ Finset.Icc 1 L0, (ArithmeticFunction.moebius ℓ : ℝ)
            * (locH d n B x y ℓ * (locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n)))|
        ≤ 2 * locG d n x y := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hpt : ∀ ℓ ∈ Finset.Icc 1 L0,
          |(ArithmeticFunction.moebius ℓ : ℝ)
              * (locH d n B x y ℓ * (locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n))|
            ≤ locG d n x y / (ℓ : ℝ) ^ (NN d n - 2) := by
        intro ℓ hℓ
        have hℓ1 : 1 ≤ ℓ := (Finset.mem_Icc.mp hℓ).1
        have hℓpos : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ1
        have hmu1 : |(ArithmeticFunction.moebius ℓ : ℝ)| ≤ 1 :=
          MDEstimates.moebius_abs_cast_le_one ℓ
        have hg2 : (locg d n B ℓ) ^ 2 ≤ (ℓ : ℝ) ^ 2 := by
          nlinarith [hgle ℓ hℓ1, hgnn ℓ]
        have hsplit : (ℓ : ℝ) ^ (NN d n) = (ℓ : ℝ) ^ (NN d n - 2) * (ℓ : ℝ) ^ 2 := by
          rw [← pow_add, hNA]
        have hd2 : 0 < (ℓ : ℝ) ^ (NN d n - 2) := by positivity
        have h2 : (locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ 2 ≤ 1 := by
          rw [div_le_one (by positivity)]; exact hg2
        have hZabs : |locH d n B x y ℓ * (locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n)|
            ≤ locG d n x y / (ℓ : ℝ) ^ (NN d n - 2) := by
          rw [hsplit, abs_div, abs_mul, abs_of_nonneg (hHnn ℓ),
            abs_of_nonneg (by positivity : (0:ℝ) ≤ (locg d n B ℓ) ^ 2),
            abs_of_nonneg (by positivity : (0:ℝ) ≤ (ℓ : ℝ) ^ (NN d n - 2) * (ℓ : ℝ) ^ 2)]
          rw [div_le_div_iff₀ (by positivity) hd2]
          calc locH d n B x y ℓ * (locg d n B ℓ) ^ 2 * (ℓ : ℝ) ^ (NN d n - 2)
              ≤ locG d n x y * (ℓ : ℝ) ^ 2 * (ℓ : ℝ) ^ (NN d n - 2) :=
                mul_le_mul_of_nonneg_right (by
                  calc locH d n B x y ℓ * (locg d n B ℓ) ^ 2
                      ≤ locH d n B x y ℓ * (ℓ : ℝ) ^ 2 :=
                        mul_le_mul_of_nonneg_left
                          (by nlinarith [hgle ℓ hℓ1, hgnn ℓ]) (hHnn ℓ)
                    _ ≤ locG d n x y * (ℓ : ℝ) ^ 2 :=
                        mul_le_mul_of_nonneg_right (hHle ℓ) (by positivity)) (by positivity)
            _ = locG d n x y * ((ℓ : ℝ) ^ (NN d n - 2) * (ℓ : ℝ) ^ 2) := by ring
        calc |(ArithmeticFunction.moebius ℓ : ℝ)
              * (locH d n B x y ℓ * (locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n))|
            = |(ArithmeticFunction.moebius ℓ : ℝ)|
              * |locH d n B x y ℓ * (locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n)| := by rw [abs_mul]
          _ ≤ 1 * (locG d n x y / (ℓ : ℝ) ^ (NN d n - 2)) :=
              mul_le_mul hmu1 hZabs (abs_nonneg _) zero_le_one
          _ = locG d n x y / (ℓ : ℝ) ^ (NN d n - 2) := by ring
      calc (∑ ℓ ∈ Finset.Icc 1 L0,
            |(ArithmeticFunction.moebius ℓ : ℝ)
              * (locH d n B x y ℓ * (locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n))|)
          ≤ ∑ ℓ ∈ Finset.Icc 1 L0, locG d n x y / (ℓ : ℝ) ^ (NN d n - 2) :=
            Finset.sum_le_sum hpt
        _ = locG d n x y * (∑ ℓ ∈ Finset.Icc 1 L0, 1 / (ℓ : ℝ) ^ (NN d n - 2)) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun ℓ _ => by ring)
        _ ≤ locG d n x y * 2 :=
            mul_le_mul_of_nonneg_left (sum_Icc_inv_pow_le_two _ (by have h := six_le_NN d n hd hdn; omega) L0) (le_of_lt hGpos)
        _ = 2 * locG d n x y := by ring
    have h2 : locG d n x y / zetaR (NN d n - 2) ≤ locG d n x y := by
      rw [div_le_iff₀ hzzpos]
      nlinarith [hGpos, hzz1]
    calc |(∑ ℓ ∈ Finset.Icc 1 L0, (ArithmeticFunction.moebius ℓ : ℝ)
          * (locH d n B x y ℓ * (locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n)))
          - locG d n x y / zetaR (NN d n - 2)|
        ≤ |(∑ ℓ ∈ Finset.Icc 1 L0, (ArithmeticFunction.moebius ℓ : ℝ)
            * (locH d n B x y ℓ * (locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n)))|
          + |locG d n x y / zetaR (NN d n - 2)| := by
            rw [sub_eq_add_neg]
            calc |(∑ ℓ ∈ Finset.Icc 1 L0, (ArithmeticFunction.moebius ℓ : ℝ)
                  * (locH d n B x y ℓ * (locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n)))
                  + -(locG d n x y / zetaR (NN d n - 2))|
                ≤ |(∑ ℓ ∈ Finset.Icc 1 L0, (ArithmeticFunction.moebius ℓ : ℝ)
                    * (locH d n B x y ℓ * (locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n)))|
                  + |-(locG d n x y / zetaR (NN d n - 2))| := abs_add_le _ _
              _ = |(∑ ℓ ∈ Finset.Icc 1 L0, (ArithmeticFunction.moebius ℓ : ℝ)
                    * (locH d n B x y ℓ * (locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n)))|
                  + |locG d n x y / zetaR (NN d n - 2)| := by rw [abs_neg]
      _ = |(∑ ℓ ∈ Finset.Icc 1 L0, (ArithmeticFunction.moebius ℓ : ℝ)
            * (locH d n B x y ℓ * (locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n)))|
          + locG d n x y / zetaR (NN d n - 2) := by
          rw [abs_of_nonneg (by positivity : 0 ≤ locG d n x y / zetaR (NN d n - 2))]
      _ ≤ 2 * locG d n x y + locG d n x y := by linarith
      _ ≤ 3 * locG d n x y := by linarith
  have herrXYnn : 0 ≤ errXY d n B x y := by
    rw [errXY]
    by_cases h : (gcdMinors2 x y) ∣ ((bigW (wOf B) / radW (wOf B) : ℕ) : ℤ)
    · rw [if_pos h]
      linarith [le_min zero_le_one
        (by positivity : (0:ℝ) ≤ DeltaXY d n x y ^ 2 / (Real.log B) ^ 2)]
    · rw [if_neg h]
      linarith [le_min zero_le_one
        (by positivity : (0:ℝ) ≤ DeltaXY d n x y ^ 2 / (Real.log B) ^ 2)]
  have hmain : |(∑ ℓ ∈ Finset.Icc 1 L0,
          ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) * locPerMain d n A B x y ℓ)
        - locL d n A B x y|
      ≤ locL d n A B x y / Real.log A + 3 * zetaR (NN d n - 2) * locL d n A B x y
          * errXY d n B x y := by
    by_cases hgood : (gcdMinors2 x y) ∣ ((bigW (wOf B) / radW (wOf B) : ℕ) : ℤ)
    · have hgoodG : (gcdMinors2 x y).natAbs ∣ (bigW (wOf B) / radW (wOf B)) := by
        exact Int.ofNat_dvd.mp (Int.natAbs_dvd.mpr hgood)
      have hT2 : (∑ ℓ ∈ Finset.Icc 1 L0,
            (ArithmeticFunction.moebius ℓ : ℝ)
              * (locH d n B x y ℓ * (locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n)))
          = locG d n x y * (∑ ℓ ∈ Finset.Icc 1 L0,
              (ArithmeticFunction.moebius ℓ : ℝ)
                * ((locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun ℓ hℓ => ?_)
        by_cases hmu : ArithmeticFunction.moebius ℓ = 0
        · rw [hmu]; ring
        · have hsq : Squarefree ℓ := (ArithmeticFunction.moebius_ne_zero_iff_squarefree).mp hmu
          have hgcd := gcd_div_gcd_eq (wOf B) ℓ ((gcdMinors2 x y).natAbs) hsq hgoodG
          rw [locH, locG, hgcd]
          ring
      have hZapp := hZ (wOf B) (A / (bigW (wOf B) : ℝ)) hw1 hAW1
      rw [← hL0, hNA, hNB] at hZapp
      have hT2b : |(∑ ℓ ∈ Finset.Icc 1 L0,
            (ArithmeticFunction.moebius ℓ : ℝ) * ((locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n)))
            - 1 / zetaR (NN d n - 2)|
          ≤ Cz / (min (A / (bigW (wOf B) : ℝ)) (wOf B)) ^ (NN d n - 3) := by
        rw [show (∑ ℓ ∈ Finset.Icc 1 L0,
              (ArithmeticFunction.moebius ℓ : ℝ) * ((locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n)))
            = (∑ ℓ ∈ Finset.Icc 1 L0, (ArithmeticFunction.moebius ℓ : ℝ)
                * ((Nat.gcd ℓ (bigW (wOf B)) : ℕ) : ℝ) ^ 2 / (ℓ : ℝ) ^ (NN d n)) from by
          refine Finset.sum_congr rfl (fun ℓ _ => by rw [locg]; ring)]
        exact hZapp
      have hmin1 : 1 ≤ min (A / (bigW (wOf B) : ℝ)) (wOf B) :=
        le_min (by linarith [hAW1]) hw1
      have hminpos : 0 < min (A / (bigW (wOf B) : ℝ)) (wOf B) :=
        lt_of_lt_of_le zero_lt_one hmin1
      have hbound : |locK d n A B x y * (locG d n x y
            * (∑ ℓ ∈ Finset.Icc 1 L0, (ArithmeticFunction.moebius ℓ : ℝ)
                * ((locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n)))) - locL d n A B x y|
          ≤ zetaR (NN d n - 2) * Cz * locL d n A B x y
              / (min (A / (bigW (wOf B) : ℝ)) (wOf B)) ^ (NN d n - 3) := by
        rw [locL]
        rw [show locK d n A B x y * (locG d n x y * (∑ ℓ ∈ Finset.Icc 1 L0,
              (ArithmeticFunction.moebius ℓ : ℝ)
                * ((locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n))))
            - locK d n A B x y * locG d n x y / zetaR (NN d n - 2)
            = locK d n A B x y * locG d n x y
              * ((∑ ℓ ∈ Finset.Icc 1 L0, (ArithmeticFunction.moebius ℓ : ℝ)
                  * ((locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n))) - 1 / zetaR (NN d n - 2))
            from by ring]
        rw [abs_mul, abs_mul, abs_of_pos hKpos, abs_of_pos hGpos]
        calc locK d n A B x y * locG d n x y
              * |(∑ ℓ ∈ Finset.Icc 1 L0, (ArithmeticFunction.moebius ℓ : ℝ)
                  * ((locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n))) - 1 / zetaR (NN d n - 2)|
            ≤ locK d n A B x y * locG d n x y
                * (Cz / (min (A / (bigW (wOf B) : ℝ)) (wOf B)) ^ (NN d n - 3)) :=
              mul_le_mul_of_nonneg_left hT2b (mul_nonneg (le_of_lt hKpos) (le_of_lt hGpos))
          _ = zetaR (NN d n - 2) * Cz * locL d n A B x y
                / (min (A / (bigW (wOf B) : ℝ)) (wOf B)) ^ (NN d n - 3) := by
              have hzzn : zetaR (NN d n - 2) ≠ 0 := ne_of_gt hzzpos
              have hminn : (min (A / (bigW (wOf B) : ℝ)) (wOf B)) ^ (NN d n - 3) ≠ 0 :=
                ne_of_gt (pow_pos (lt_of_lt_of_le zero_lt_one hmin1) _)
              rw [show locL d n A B x y = locK d n A B x y * locG d n x y
                  / zetaR (NN d n - 2) from rfl]
              field_simp
              try ring
      have h4 : Real.log A ≤ (min (A / (bigW (wOf B) : ℝ)) (wOf B)) ^ (NN d n - 3) := by
        calc Real.log A = 1 * Real.log A := (one_mul _).symm
          _ ≤ K0 * Real.log A := mul_le_mul_of_nonneg_right hK0ge1 (le_of_lt hlogApos)
          _ ≤ _ := har3
      have h5 : zetaR (NN d n - 2) * Cz * locL d n A B x y
            / (min (A / (bigW (wOf B) : ℝ)) (wOf B)) ^ (NN d n - 3)
          ≤ locL d n A B x y / Real.log A := by
        have hkey : zetaR (NN d n - 2) * Cz * Real.log A
            ≤ (min (A / (bigW (wOf B) : ℝ)) (wOf B)) ^ (NN d n - 3) := by
          have h2 : zetaR (NN d n - 2) * Cz * Real.log A ≤ K0 * Real.log A :=
            mul_le_mul_of_nonneg_right (by
              have hh := hK0geZ
              rw [hQ0def] at hh
              exact le_trans (le_mul_of_one_le_right
                (mul_nonneg (le_of_lt hzzpos) (le_of_lt hCzpos))
                (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))) hh) (le_of_lt hlogApos)
          linarith [har3]
        rw [div_le_div_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one hmin1) _) hlogApos]
        calc (zetaR (NN d n - 2) * Cz * locL d n A B x y) * Real.log A
            = (zetaR (NN d n - 2) * Cz * Real.log A) * locL d n A B x y := by ring
          _ ≤ (min (A / (bigW (wOf B) : ℝ)) (wOf B)) ^ (NN d n - 3)
                * locL d n A B x y := mul_le_mul_of_nonneg_right hkey hLnn
          _ = locL d n A B x y
                * (min (A / (bigW (wOf B) : ℝ)) (wOf B)) ^ (NN d n - 3) := by ring
      calc |(∑ ℓ ∈ Finset.Icc 1 L0,
            ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) * locPerMain d n A B x y ℓ)
          - locL d n A B x y|
          = |locK d n A B x y * (locG d n x y * (∑ ℓ ∈ Finset.Icc 1 L0,
              (ArithmeticFunction.moebius ℓ : ℝ)
                * ((locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n)))) - locL d n A B x y| := by
            rw [hTEq, hT2]
        _ ≤ zetaR (NN d n - 2) * Cz * locL d n A B x y
              / (min (A / (bigW (wOf B) : ℝ)) (wOf B)) ^ (NN d n - 3) := hbound
        _ ≤ locL d n A B x y / Real.log A := h5
        _ ≤ locL d n A B x y / Real.log A + 3 * zetaR (NN d n - 2) * locL d n A B x y
              * errXY d n B x y := by
            have h2 : 0 ≤ errXY d n B x y := by
              rw [errXY, if_pos hgood]
              linarith [le_min zero_le_one
                (by positivity : (0:ℝ) ≤ DeltaXY d n x y ^ 2 / (Real.log B) ^ 2)]
            have h3 : 0 ≤ 3 * zetaR (NN d n - 2) * locL d n A B x y * errXY d n B x y := by
              positivity
            linarith
    · have herr1 : 1 ≤ errXY d n B x y := by
        rw [errXY, if_neg hgood]
        have h1 : 0 ≤ min 1 (DeltaXY d n x y ^ 2 / (Real.log B) ^ 2) :=
          le_min zero_le_one (by positivity)
        linarith
      have hfinal : |locK d n A B x y * (∑ ℓ ∈ Finset.Icc 1 L0,
            (ArithmeticFunction.moebius ℓ : ℝ)
              * (locH d n B x y ℓ * (locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n)))
            - locL d n A B x y| ≤ 3 * zetaR (NN d n - 2) * locL d n A B x y := by
        rw [locL]
        rw [show locK d n A B x y * (∑ ℓ ∈ Finset.Icc 1 L0,
              (ArithmeticFunction.moebius ℓ : ℝ)
                * (locH d n B x y ℓ * (locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n)))
            - locK d n A B x y * locG d n x y / zetaR (NN d n - 2)
            = locK d n A B x y * ((∑ ℓ ∈ Finset.Icc 1 L0,
                (ArithmeticFunction.moebius ℓ : ℝ)
                  * (locH d n B x y ℓ * (locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n)))
                - locG d n x y / zetaR (NN d n - 2)) from by ring]
        rw [abs_mul, abs_of_pos hKpos]
        calc locK d n A B x y * |(∑ ℓ ∈ Finset.Icc 1 L0,
              (ArithmeticFunction.moebius ℓ : ℝ)
                * (locH d n B x y ℓ * (locg d n B ℓ) ^ 2 / (ℓ : ℝ) ^ (NN d n)))
              - locG d n x y / zetaR (NN d n - 2)|
            ≤ locK d n A B x y * (3 * locG d n x y) :=
              mul_le_mul_of_nonneg_left (hT1bd hgood) (le_of_lt hKpos)
          _ = 3 * zetaR (NN d n - 2) * (locK d n A B x y * locG d n x y
                / zetaR (NN d n - 2)) := by
              have hzzn : zetaR (NN d n - 2) ≠ 0 := ne_of_gt hzzpos
              field_simp
              try ring
      calc |(∑ ℓ ∈ Finset.Icc 1 L0,
            ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) * locPerMain d n A B x y ℓ)
          - locL d n A B x y| = _ := by rw [hTEq]
        _ ≤ 3 * zetaR (NN d n - 2) * locL d n A B x y := hfinal
        _ ≤ locL d n A B x y / Real.log A + 3 * zetaR (NN d n - 2) * locL d n A B x y
              * errXY d n B x y := by
            have h1 : 0 ≤ locL d n A B x y / Real.log A := div_nonneg hLnn (le_of_lt hlogApos)
            have h2 : 0 ≤ 3 * zetaR (NN d n - 2) * locL d n A B x y := by positivity
            nlinarith [h1, h2, herr1, mul_nonneg h2 (sub_nonneg.mpr herr1)]
  -- (5) final assembly
  have hloc : locL d n A B x y = locMain d n A B (x, y) := by
    have hGcast : (((gcdMinors2 x y).natAbs : ℕ) : ℝ) = (gcdMinors2 x y : ℝ) :=
      natAbs_cast_of_nonneg (gcdMinors2 x y) (int_finset_gcd_nonneg Finset.univ _)
    have hD := DeltaXY_gcd_detL d n hd hn1 x y hx hy hxy
    have hdet : detL (Gam d n x y) ≠ 0 := by
      have h := Lat.detL_ge_one (Gam d n x y); linarith
    have hAB : eNorm (veronese d n x) * eNorm (veronese d n y)
        = DeltaXY d n x y * (gcdMinors2 x y : ℝ) * detL (Gam d n x y) := by
      rw [hD]
      field_simp
    simp only [locL, locK, locG, locMain, iotaDN, zetaR]
    rw [hGcast, hAB]
    field_simp
    try ring
  have hstep1 : |(∑ ℓ ∈ Finset.Icc 1 L0,
        ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) *
          Sk d n 2 (GamLoc d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
            (TlocSet d n x y (A / (ℓ : ℝ)) (Real.log B)))
        - (∑ ℓ ∈ Finset.Icc 1 L0,
          ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) * locPerMain d n A B x y ℓ)|
      ≤ ∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ) ^ 2) * locPerErr d n Csk A B x y ℓ := by
    refine le_trans (abs_sum_sub_le (Finset.Icc 1 L0)
      (fun ℓ => ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) *
        Sk d n 2 (GamLoc d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
          (TlocSet d n x y (A / (ℓ : ℝ)) (Real.log B)))
      (fun ℓ => ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2)
        * locPerMain d n A B x y ℓ)) ?_
    refine Finset.sum_le_sum (fun ℓ hℓ => ?_)
    have hℓ1 : 1 ≤ ℓ := (Finset.mem_Icc.mp hℓ).1
    have hℓpos : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ1
    have hmu1 : |(ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2| ≤ 1 / (ℓ : ℝ) ^ 2 := by
      rw [abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ (ℓ : ℝ) ^ 2)]
      exact div_le_div_of_nonneg_right (MDEstimates.moebius_abs_cast_le_one ℓ) (by positivity)
    rw [show ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) *
          Sk d n 2 (GamLoc d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
            (TlocSet d n x y (A / (ℓ : ℝ)) (Real.log B))
        - ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) * locPerMain d n A B x y ℓ
        = ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2)
          * (Sk d n 2 (GamLoc d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
              (TlocSet d n x y (A / (ℓ : ℝ)) (Real.log B))
            - locPerMain d n A B x y ℓ) from by ring]
    rw [abs_mul]
    exact mul_le_mul hmu1 (hper ℓ hℓ) (abs_nonneg _) (by positivity)
  have hAbsS : (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ) ^ 2) * locPerErr d n Csk A B x y ℓ)
      = (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ) ^ 2) * locE1 d n Csk A B x y ℓ)
        + (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ) ^ 2) * locE2 d n Csk A B x y ℓ)
        + (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ) ^ 2) * locE3 d n Csk A B x y ℓ) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    rw [locPerErr]; ring
  have herrmin : min 1 (DeltaXY d n x y ^ 2 / (Real.log B) ^ 2) ≤ errXY d n B x y := by
    rw [errXY]
    by_cases h : (gcdMinors2 x y) ∣ ((bigW (wOf B) / radW (wOf B) : ℕ) : ℤ)
    · rw [if_pos h]; linarith
    · rw [if_neg h]; linarith
  have hlog1 : 0 ≤ 1 / Real.log A := by positivity
  have hstep1 : |(∑ ℓ ∈ Finset.Icc 1 L0,
        ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) *
          Sk d n 2 (GamLoc d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
            (TlocSet d n x y (A / (ℓ : ℝ)) (Real.log B)))
        - (∑ ℓ ∈ Finset.Icc 1 L0,
          ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) * locPerMain d n A B x y ℓ)|
      ≤ ∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ) ^ 2) * locPerErr d n Csk A B x y ℓ := by
    refine le_trans (abs_sum_sub_le (Finset.Icc 1 L0)
      (fun ℓ => ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) *
        Sk d n 2 (GamLoc d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
          (TlocSet d n x y (A / (ℓ : ℝ)) (Real.log B)))
      (fun ℓ => ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2)
        * locPerMain d n A B x y ℓ)) ?_
    refine Finset.sum_le_sum (fun ℓ hℓ => ?_)
    have hℓ1 : 1 ≤ ℓ := (Finset.mem_Icc.mp hℓ).1
    have hℓpos : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ1
    have hmu1 : |(ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2| ≤ 1 / (ℓ : ℝ) ^ 2 := by
      rw [abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ (ℓ : ℝ) ^ 2)]
      exact div_le_div_of_nonneg_right (MDEstimates.moebius_abs_cast_le_one ℓ) (by positivity)
    rw [show ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) *
          Sk d n 2 (GamLoc d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
            (TlocSet d n x y (A / (ℓ : ℝ)) (Real.log B))
        - ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) * locPerMain d n A B x y ℓ
        = ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2)
          * (Sk d n 2 (GamLoc d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
              (TlocSet d n x y (A / (ℓ : ℝ)) (Real.log B))
            - locPerMain d n A B x y ℓ) from by ring]
    rw [abs_mul]
    exact mul_le_mul hmu1 (hper ℓ hℓ) (abs_nonneg _) (by positivity)
  have hAbsS : (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ) ^ 2) * locPerErr d n Csk A B x y ℓ)
      = (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ) ^ 2) * locE1 d n Csk A B x y ℓ)
        + (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ) ^ 2) * locE2 d n Csk A B x y ℓ)
        + (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ) ^ 2) * locE3 d n Csk A B x y ℓ) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    rw [locPerErr]; ring
  have herrmin : min 1 (DeltaXY d n x y ^ 2 / (Real.log B) ^ 2) ≤ errXY d n B x y := by
    rw [errXY]
    by_cases h : (gcdMinors2 x y) ∣ ((bigW (wOf B) / radW (wOf B) : ℕ) : ℤ)
    · rw [if_pos h]; linarith
    · rw [if_neg h]; linarith
  have hlog1 : 0 ≤ 1 / Real.log A := by positivity
  have hAbsBd : (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ) ^ 2) * locPerErr d n Csk A B x y ℓ)
      ≤ 2 * Csk * zetaR (NN d n - 2) * locL d n A B x y * errXY d n B x y
        + 2 * K0 * locL d n A B x y / Real.log A := by
    rw [hAbsS]
    have h1 := le_trans hS1 (mul_le_mul_of_nonneg_left herrmin (by positivity))
    have h23 : (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ) ^ 2) * locE2 d n Csk A B x y ℓ)
        + (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ) ^ 2) * locE3 d n Csk A B x y ℓ)
        ≤ K0 * locL d n A B x y / Real.log A + K0 * locL d n A B x y / Real.log A :=
      add_le_add hS2 hS3
    calc (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ) ^ 2) * locE1 d n Csk A B x y ℓ)
          + (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ) ^ 2) * locE2 d n Csk A B x y ℓ)
          + (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ) ^ 2) * locE3 d n Csk A B x y ℓ)
        = (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ) ^ 2) * locE1 d n Csk A B x y ℓ)
          + ((∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ) ^ 2) * locE2 d n Csk A B x y ℓ)
            + (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ) ^ 2) * locE3 d n Csk A B x y ℓ)) := by ring
      _ ≤ 2 * Csk * zetaR (NN d n - 2) * locL d n A B x y * errXY d n B x y
            + (K0 * locL d n A B x y / Real.log A
              + K0 * locL d n A B x y / Real.log A) := add_le_add h1 h23
      _ = 2 * Csk * zetaR (NN d n - 2) * locL d n A B x y * errXY d n B x y
            + 2 * K0 * locL d n A B x y / Real.log A := by ring
  have hAD : 2 * Csk * zetaR (NN d n - 2) * locL d n A B x y * errXY d n B x y
      + 3 * zetaR (NN d n - 2) * locL d n A B x y * errXY d n B x y
      ≤ (2 * Csk * zetaR (NN d n - 2) + 3 * zetaR (NN d n - 2) + 2 * K0 + 1)
        * locL d n A B x y * errXY d n B x y := by
    have hcoef : 2 * Csk * zetaR (NN d n - 2) + 3 * zetaR (NN d n - 2)
        ≤ (2 * Csk * zetaR (NN d n - 2) + 3 * zetaR (NN d n - 2) + 2 * K0 + 1) := by
      linarith [hK0pos]
    calc 2 * Csk * zetaR (NN d n - 2) * locL d n A B x y * errXY d n B x y
          + 3 * zetaR (NN d n - 2) * locL d n A B x y * errXY d n B x y
        = (2 * Csk * zetaR (NN d n - 2) + 3 * zetaR (NN d n - 2))
          * (locL d n A B x y * errXY d n B x y) := by ring
      _ ≤ (2 * Csk * zetaR (NN d n - 2) + 3 * zetaR (NN d n - 2) + 2 * K0 + 1)
          * (locL d n A B x y * errXY d n B x y) :=
          mul_le_mul_of_nonneg_right hcoef (mul_nonneg hLnn herrXYnn)
      _ = (2 * Csk * zetaR (NN d n - 2) + 3 * zetaR (NN d n - 2) + 2 * K0 + 1)
          * locL d n A B x y * errXY d n B x y := by ring
  have hBC : 2 * K0 * locL d n A B x y / Real.log A + locL d n A B x y / Real.log A
      ≤ (2 * Csk * zetaR (NN d n - 2) + 3 * zetaR (NN d n - 2) + 2 * K0 + 1)
        * locL d n A B x y * (1 / Real.log A) := by
    have hcoef : 2 * K0 + 1
        ≤ (2 * Csk * zetaR (NN d n - 2) + 3 * zetaR (NN d n - 2) + 2 * K0 + 1) := by
      nlinarith [hCskpos, hzzpos]
    calc 2 * K0 * locL d n A B x y / Real.log A + locL d n A B x y / Real.log A
        = (2 * K0 + 1) * (locL d n A B x y * (1 / Real.log A)) := by ring
      _ ≤ (2 * Csk * zetaR (NN d n - 2) + 3 * zetaR (NN d n - 2) + 2 * K0 + 1)
          * (locL d n A B x y * (1 / Real.log A)) :=
          mul_le_mul_of_nonneg_right hcoef (mul_nonneg hLnn hlog1)
      _ = (2 * Csk * zetaR (NN d n - 2) + 3 * zetaR (NN d n - 2) + 2 * K0 + 1)
          * locL d n A B x y * (1 / Real.log A) := by ring
  have hfinal : |(∑ ℓ ∈ Finset.Icc 1 L0,
        ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) *
          Sk d n 2 (GamLoc d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
            (TlocSet d n x y (A / (ℓ : ℝ)) (Real.log B)))
        - locMain d n A B (x, y)|
      ≤ (2 * Csk * zetaR (NN d n - 2) + 3 * zetaR (NN d n - 2) + 2 * K0 + 1)
        * locMain d n A B (x, y) * (errXY d n B x y + 1 / Real.log A) := by
    have htri : |(∑ ℓ ∈ Finset.Icc 1 L0,
          ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) *
            Sk d n 2 (GamLoc d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
              (TlocSet d n x y (A / (ℓ : ℝ)) (Real.log B)))
          - locMain d n A B (x, y)|
        ≤ |(∑ ℓ ∈ Finset.Icc 1 L0,
            ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) *
              Sk d n 2 (GamLoc d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
                (TlocSet d n x y (A / (ℓ : ℝ)) (Real.log B)))
            - (∑ ℓ ∈ Finset.Icc 1 L0,
              ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) * locPerMain d n A B x y ℓ)|
          + |(∑ ℓ ∈ Finset.Icc 1 L0,
              ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) * locPerMain d n A B x y ℓ)
            - locMain d n A B (x, y)| := by
      rw [show (∑ ℓ ∈ Finset.Icc 1 L0,
            ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) *
              Sk d n 2 (GamLoc d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
                (TlocSet d n x y (A / (ℓ : ℝ)) (Real.log B))) - locMain d n A B (x, y)
          = ((∑ ℓ ∈ Finset.Icc 1 L0,
              ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) *
                Sk d n 2 (GamLoc d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
                  (TlocSet d n x y (A / (ℓ : ℝ)) (Real.log B)))
              - (∑ ℓ ∈ Finset.Icc 1 L0,
                ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) * locPerMain d n A B x y ℓ))
            + ((∑ ℓ ∈ Finset.Icc 1 L0,
                ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) * locPerMain d n A B x y ℓ)
              - locMain d n A B (x, y)) from by ring]
      exact abs_add_le _ _
    have hmain' : |(∑ ℓ ∈ Finset.Icc 1 L0,
          ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) * locPerMain d n A B x y ℓ)
          - locMain d n A B (x, y)|
        ≤ locL d n A B x y / Real.log A
          + 3 * zetaR (NN d n - 2) * locL d n A B x y * errXY d n B x y := by
      rw [← hloc]; exact hmain
    calc |(∑ ℓ ∈ Finset.Icc 1 L0,
          ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) *
            Sk d n 2 (GamLoc d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
              (TlocSet d n x y (A / (ℓ : ℝ)) (Real.log B)))
          - locMain d n A B (x, y)|
        ≤ |(∑ ℓ ∈ Finset.Icc 1 L0,
            ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) *
              Sk d n 2 (GamLoc d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
                (TlocSet d n x y (A / (ℓ : ℝ)) (Real.log B)))
            - (∑ ℓ ∈ Finset.Icc 1 L0,
              ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) * locPerMain d n A B x y ℓ)|
          + |(∑ ℓ ∈ Finset.Icc 1 L0,
              ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) * locPerMain d n A B x y ℓ)
            - locMain d n A B (x, y)| := htri
      _ ≤ (∑ ℓ ∈ Finset.Icc 1 L0, (1 / (ℓ : ℝ) ^ 2) * locPerErr d n Csk A B x y ℓ)
          + (locL d n A B x y / Real.log A
            + 3 * zetaR (NN d n - 2) * locL d n A B x y * errXY d n B x y) :=
          add_le_add hstep1 hmain'
      _ ≤ (2 * Csk * zetaR (NN d n - 2) * locL d n A B x y * errXY d n B x y
            + 2 * K0 * locL d n A B x y / Real.log A)
          + (locL d n A B x y / Real.log A
            + 3 * zetaR (NN d n - 2) * locL d n A B x y * errXY d n B x y) :=
          add_le_add hAbsBd le_rfl
      _ = (2 * Csk * zetaR (NN d n - 2) * locL d n A B x y * errXY d n B x y
            + 3 * zetaR (NN d n - 2) * locL d n A B x y * errXY d n B x y)
          + (2 * K0 * locL d n A B x y / Real.log A
            + locL d n A B x y / Real.log A) := by ring
      _ ≤ (2 * Csk * zetaR (NN d n - 2) + 3 * zetaR (NN d n - 2) + 2 * K0 + 1)
          * locL d n A B x y * errXY d n B x y
          + (2 * Csk * zetaR (NN d n - 2) + 3 * zetaR (NN d n - 2) + 2 * K0 + 1)
          * locL d n A B x y * (1 / Real.log A) := add_le_add hAD hBC
      _ = (2 * Csk * zetaR (NN d n - 2) + 3 * zetaR (NN d n - 2) + 2 * K0 + 1)
          * locL d n A B x y * (errXY d n B x y + 1 / Real.log A) := by ring
      _ = (2 * Csk * zetaR (NN d n - 2) + 3 * zetaR (NN d n - 2) + 2 * K0 + 1)
          * locMain d n A B (x, y) * (errXY d n B x y + 1 / Real.log A) := by rw [hloc]
  exact hfinal

/-- (L2b) All pairs, local. Same scheme with `Sk2_loc_ell`, `Y = W`, `ℓ ≤ A/W`. -/
theorem Sstar2_loc_pair (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hdn : d ≤ n)
    (h22 : (d, n) ≠ (2, 2)) :
    ∃ C B₀ : ℝ, 0 < C ∧ ∀ A B : ℝ, B₀ ≤ B → B ^ ((5 : ℝ) / 6) ≤ A → A ≤ B ^ 2 →
      ∀ p ∈ Omega d n B,
      |Sstar d n 2 (GamLoc d n p.1 p.2 (bigW (wOf B))) (TlocSet d n p.1 p.2 A (Real.log B)) -
          locMain d n A B p|
        ≤ C * locMain d n A B p * (errXY d n B p.1 p.2 + 1 / Real.log A) := by
  classical
  obtain ⟨Csm, Bsm, hCsmpos, hSmall⟩ := loc_small d n hd hdn h22
  obtain ⟨Ctl, Btl, hCtlpos, hTail⟩ := Sstar2_loc_tail d n hd hdn h22
  obtain ⟨Bar0, har0⟩ := loc_arith d n hd hdn h22 0
  refine ⟨Csm + Ctl + 1, max (max Bsm Btl) (max Bar0 100), by positivity, ?_⟩
  intro A B hB hBA hAB2 p hp
  have hBsm : Bsm ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hB
  have hBtl : Btl ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hB
  have hBar0 : Bar0 ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hB
  have hB100 : 100 ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hB
  have hpx : IsPrim p.1 := hp.1.1
  have hpy : IsPrim p.2 := hp.2.1.1
  have hne : p.1 ≠ p.2 := hp.2.2.1
  have hne' : p.1 ≠ -p.2 := hp.2.2.2
  have hLI : LinearIndependent ℤ ![p.1, p.2] := Sig2.li_of_prim_ne_pm p.1 p.2 hpx hpy hne hne'
  obtain ⟨hA1, hlogA, hw1, hAW1, hW1r, hWA, -, -, -⟩ := har0 B hBar0 A hBA hAB2
  have hlogApos : 0 < Real.log A := by linarith
  have hlog1 : 0 ≤ 1 / Real.log A := by positivity
  have hW1n : 1 ≤ bigW (wOf B) := one_le_bigW (wOf B)
  have hmob := SstarMobiusLoc d n p.1 p.2 2 A (Real.log B) (bigW (wOf B)) hW1n hA1
  have hL0M : ⌊A / (bigW (wOf B) : ℝ)⌋₊ ≤ ⌊A⌋₊ := by
    refine Nat.floor_mono ?_
    rw [div_le_iff₀ (by have h := one_le_bigW (wOf B); linarith :
      (0 : ℝ) < (bigW (wOf B) : ℝ))]
    nlinarith [hA1, hW1r]
  have hs := hSmall A B hBsm hBA hAB2 p.1 p.2 hpx hpy hLI
  have ht := hTail A B hBtl hBA hAB2 p.1 p.2 hpx hpy hLI
  rw [hmob]
  set S : ℕ → ℝ := fun ℓ => ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) *
      Sk d n 2 (GamLoc d n p.1 p.2 (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
        (TlocSet d n p.1 p.2 (A / (ℓ : ℝ)) (Real.log B)) with hS
  have hs' : |(∑ ℓ ∈ Finset.Icc 1 ⌊A / (bigW (wOf B) : ℝ)⌋₊, S ℓ)
        - locMain d n A B (p.1, p.2)|
      ≤ Csm * locMain d n A B (p.1, p.2) * (errXY d n B p.1 p.2 + 1 / Real.log A) := by
    simpa only [hS] using hs
  have ht' : |(∑ ℓ ∈ Finset.Icc (⌊A / (bigW (wOf B) : ℝ)⌋₊ + 1) ⌊A⌋₊, S ℓ)|
      ≤ Ctl * locMain d n A B (p.1, p.2) / Real.log A := by
    simpa only [hS] using ht
  have hsplit := sum_Icc_split_one (f := S) hL0M
  rw [hsplit]
  have htri : |(∑ ℓ ∈ Finset.Icc 1 ⌊A / (bigW (wOf B) : ℝ)⌋₊, S ℓ)
        + (∑ ℓ ∈ Finset.Icc (⌊A / (bigW (wOf B) : ℝ)⌋₊ + 1) ⌊A⌋₊, S ℓ)
        - locMain d n A B p|
      ≤ |(∑ ℓ ∈ Finset.Icc 1 ⌊A / (bigW (wOf B) : ℝ)⌋₊, S ℓ) - locMain d n A B p|
        + |∑ ℓ ∈ Finset.Icc (⌊A / (bigW (wOf B) : ℝ)⌋₊ + 1) ⌊A⌋₊, S ℓ| := by
    rw [show (∑ ℓ ∈ Finset.Icc 1 ⌊A / (bigW (wOf B) : ℝ)⌋₊, S ℓ)
          + (∑ ℓ ∈ Finset.Icc (⌊A / (bigW (wOf B) : ℝ)⌋₊ + 1) ⌊A⌋₊, S ℓ)
          - locMain d n A B p
        = ((∑ ℓ ∈ Finset.Icc 1 ⌊A / (bigW (wOf B) : ℝ)⌋₊, S ℓ) - locMain d n A B p)
          + (∑ ℓ ∈ Finset.Icc (⌊A / (bigW (wOf B) : ℝ)⌋₊ + 1) ⌊A⌋₊, S ℓ) from by ring]
    exact abs_add_le _ _
  have hLMpos : 0 < locMain d n A B p :=
    locMain_pos' d n hd hdn A B p.1 p.2 hpx hpy hLI (by linarith) (by linarith)
  have hLMnn : 0 ≤ locMain d n A B p := le_of_lt hLMpos
  have herrnn : 0 ≤ errXY d n B p.1 p.2 := by
    rw [errXY]
    by_cases h : (gcdMinors2 p.1 p.2) ∣ ((bigW (wOf B) / radW (wOf B) : ℕ) : ℤ)
    · rw [if_pos h]
      linarith [le_min zero_le_one
        (by positivity : (0 : ℝ) ≤ DeltaXY d n p.1 p.2 ^ 2 / (Real.log B) ^ 2)]
    · rw [if_neg h]
      linarith [le_min zero_le_one
        (by positivity : (0 : ℝ) ≤ DeltaXY d n p.1 p.2 ^ 2 / (Real.log B) ^ 2)]
  calc |(∑ ℓ ∈ Finset.Icc 1 ⌊A / (bigW (wOf B) : ℝ)⌋₊, S ℓ)
        + (∑ ℓ ∈ Finset.Icc (⌊A / (bigW (wOf B) : ℝ)⌋₊ + 1) ⌊A⌋₊, S ℓ)
        - locMain d n A B p|
      ≤ |(∑ ℓ ∈ Finset.Icc 1 ⌊A / (bigW (wOf B) : ℝ)⌋₊, S ℓ) - locMain d n A B p|
        + |∑ ℓ ∈ Finset.Icc (⌊A / (bigW (wOf B) : ℝ)⌋₊ + 1) ⌊A⌋₊, S ℓ| := htri
    _ ≤ Csm * locMain d n A B (p.1, p.2) * (errXY d n B p.1 p.2 + 1 / Real.log A)
        + Ctl * locMain d n A B (p.1, p.2) / Real.log A := add_le_add hs' ht'
    _ ≤ (Csm + Ctl + 1) * locMain d n A B p
        * (errXY d n B p.1 p.2 + 1 / Real.log A) := by
        have hy : 0 ≤ errXY d n B p.1 p.2 + 1 / Real.log A := by linarith
        have hyle : 1 / Real.log A ≤ errXY d n B p.1 p.2 + 1 / Real.log A := by linarith
        have h1 : Ctl * locMain d n A B p / Real.log A
            ≤ Ctl * locMain d n A B p * (errXY d n B p.1 p.2 + 1 / Real.log A) := by
          calc Ctl * locMain d n A B p / Real.log A
              = Ctl * locMain d n A B p * (1 / Real.log A) := by ring
            _ ≤ Ctl * locMain d n A B p
                  * (errXY d n B p.1 p.2 + 1 / Real.log A) :=
                mul_le_mul_of_nonneg_left hyle (by positivity)
        have h2 : Csm * locMain d n A B p * (errXY d n B p.1 p.2 + 1 / Real.log A)
            + Ctl * locMain d n A B p * (errXY d n B p.1 p.2 + 1 / Real.log A)
            ≤ (Csm + Ctl + 1) * locMain d n A B p
              * (errXY d n B p.1 p.2 + 1 / Real.log A) := by
          nlinarith [hLMnn, hy, hCsmpos, hCtlpos]
        linarith [h1, h2]

end Work.HP.MM2

