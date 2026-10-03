/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team.

# The analytic core of the gap-regime localisation

The heart of `Submission/Work/Peluse/Ulower/gap_local_block.lean`: the level-two box norm of the
iterated difference of the *windowed* dual function dominates the (shifted) interior mass of the
mass function of the original data (`boxNorm_gapLocalise_ge`), the levels are bounded
(`boxNorm_gapLocalise_le_two`), and the two elementary counting lemmas used for the pigeonhole.
-/
import Mathlib
import Submission.Work.Peluse.Ulower.gap_local_aux
import Submission.Work.Peluse.BoxNormDilation.boxNormPow_two_eq
import Submission.Work.Peluse.Ulower.boxNormPow_le_mass
import Submission.Work.Peluse.Tools.dualFn_supportIn

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Work.Peluse.Ulower.SsA

noncomputable section

open Work.Peluse

variable {P : Polynomial ℤ}

/-! ## Elementary bounds -/

/-- `N ≤ gapNs P s N` as soon as `P` has positive degree. -/
theorem le_gapNs {s N : ℕ} (hd : 1 ≤ P.natDegree) (hN : 1 ≤ N) : N ≤ gapNs P s N := by
  have hNd : N ≤ N ^ P.natDegree := by
    calc N = N ^ 1 := (pow_one N).symm
      _ ≤ N ^ P.natDegree := Nat.pow_le_pow_right hN hd
  have h1 : 1 ≤ gapC2 P s := by rw [gapC2]; omega
  calc N ≤ 1 * N ^ P.natDegree := by rw [one_mul]; exact hNd
    _ ≤ gapC2 P s * N ^ P.natDegree := Nat.mul_le_mul_right _ h1
    _ = gapNs P s N := rfl

/-- The dual function of two `1`-bounded functions is `1`-bounded. -/
theorem dualFn_norm_le_one (N : ℕ) (P : Polynomial ℤ) {f₀ f₁ : ℤ → ℂ}
    (h0 : ∀ x : ℤ, ‖f₀ x‖ ≤ 1) (h1 : ∀ x : ℤ, ‖f₁ x‖ ≤ 1) :
    ∀ x : ℤ, ‖dualFn N P f₀ f₁ x‖ ≤ 1 := by
  intro x
  rcases Nat.eq_zero_or_pos N with hN | hN
  · simp [dualFn, hN]
  · have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hcard : ((Finset.Icc 1 N).card : ℝ) = (N : ℝ) := by
      rw [Nat.card_Icc]; norm_num
    rw [dualFn]
    calc ‖((N : ℂ))⁻¹ * ∑ y ∈ Finset.Icc 1 N,
            f₀ (x - P.eval (y : ℤ)) * f₁ (x + (y : ℤ) - P.eval (y : ℤ))‖
        = ((N : ℝ))⁻¹ * ‖∑ y ∈ Finset.Icc 1 N,
            f₀ (x - P.eval (y : ℤ)) * f₁ (x + (y : ℤ) - P.eval (y : ℤ))‖ := by
          rw [norm_mul, norm_inv, Complex.norm_natCast]
      _ ≤ ((N : ℝ))⁻¹ * ∑ y ∈ Finset.Icc 1 N,
            ‖f₀ (x - P.eval (y : ℤ)) * f₁ (x + (y : ℤ) - P.eval (y : ℤ))‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ ((N : ℝ))⁻¹ * ∑ _y ∈ Finset.Icc 1 N, (1 : ℝ) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun y _ => ?_)) (by positivity)
          rw [norm_mul]
          exact mul_le_one₀ (h0 _) (norm_nonneg _) (h1 _)
      _ = ((N : ℝ))⁻¹ * (N : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
      _ = 1 := by field_simp

/-! ## Supports -/

/-- The shift entries of a tuple drawn from `arithIcc (lc P) D` are bounded by `D |lc P|`. -/
theorem shift_entries_le {D : ℕ} {k : ℕ} {sh : Fin k → ℤ × ℤ}
    (hsh : ∀ i, (sh i).1 ∈ arithIcc P.leadingCoeff D ∧
      (sh i).2 ∈ arithIcc P.leadingCoeff D) :
    ∀ i : Fin k, (sh i).1.natAbs ≤ D * P.leadingCoeff.natAbs ∧
      (sh i).2.natAbs ≤ D * P.leadingCoeff.natAbs :=
  fun i => ⟨mem_arithIcc_le (hsh i).1, mem_arithIcc_le (hsh i).2⟩

/-- The iterated difference of the *windowed* dual function is supported in the corresponding box. -/
theorem supportIn_iterDelta_gapLocalise {s N D : ℕ} (hN : 1 ≤ N) (hNs : N ≤ gapNs P s N)
    {f₀ f₁ : ℤ → ℂ} {sh : Fin (s - 2) → ℤ × ℤ}
    (hsh : ∀ i, (sh i).1 ∈ arithIcc P.leadingCoeff D ∧
      (sh i).2 ∈ arithIcc P.leadingCoeff D) (a : ℤ) :
    SupportIn (iterDelta (s - 2) sh
        (dualFn N P (gapLocalise f₀ a (gapNs P s N)) (gapLocalise f₁ a (gapNs P s N))))
      (dSup P (gapNs P s N) N + gapSig P s D) := by
  have hdual : SupportIn (dualFn N P (gapLocalise f₀ a (gapNs P s N))
      (gapLocalise f₁ a (gapNs P s N))) (dSup P (gapNs P s N) N) :=
    Work.Peluse.Tools.dualFn_supportIn (N := gapNs P s N) (M := N) (by omega) P _ _
      (supportIn_gapLocalise_self f₀ a _) (supportIn_gapLocalise_self f₁ a _) hNs
  refine (iterDelta_supportIn sh (shift_entries_le hsh) hdual).mono ?_
  have h : (s - 2) * (D * P.leadingCoeff.natAbs) ≤ gapSig P s D := by
    rw [gapSig]
    calc (s - 2) * (D * P.leadingCoeff.natAbs) ≤ s * (D * P.leadingCoeff.natAbs) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = s * D * P.leadingCoeff.natAbs := by ring
  omega

/-- The iterated difference of the original dual function is supported in the big box. -/
theorem supportIn_iterDelta_dual {s N N₀ D : ℕ} (hN : 1 ≤ N) (hNle : N ≤ N₀)
    {f₀ f₁ : ℤ → ℂ} (hs0 : SupportIn f₀ N₀) (hs1 : SupportIn f₁ N₀)
    {sh : Fin (s - 2) → ℤ × ℤ}
    (hsh : ∀ i, (sh i).1 ∈ arithIcc P.leadingCoeff D ∧
      (sh i).2 ∈ arithIcc P.leadingCoeff D) :
    SupportIn (iterDelta (s - 2) sh (dualFn N P f₀ f₁)) (dSup P N₀ N + gapSig P s D) := by
  have hdual : SupportIn (dualFn N P f₀ f₁) (dSup P N₀ N) :=
    Work.Peluse.Tools.dualFn_supportIn (N := N₀) (M := N) (by omega) P _ _ hs0 hs1 hNle
  refine (iterDelta_supportIn sh (shift_entries_le hsh) hdual).mono ?_
  have h : (s - 2) * (D * P.leadingCoeff.natAbs) ≤ gapSig P s D := by
    rw [gapSig]
    calc (s - 2) * (D * P.leadingCoeff.natAbs) ≤ s * (D * P.leadingCoeff.natAbs) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = s * D * P.leadingCoeff.natAbs := by ring
  omega

/-- The inner window sum of a function supported in `symIcc B` over `Q = c[D]` is supported in
`symIcc (B + 2 D |c|)`. -/
theorem inner_support {B c : ℕ} {F : ℤ → ℂ} (hF : SupportIn F B) {Q : Finset ℤ}
    (hQ : ∀ z ∈ Q, z.natAbs ≤ c) {a' b' : ℤ} (ha' : a' ∈ Q) (hb' : b' ∈ Q) :
    SupportIn (fun x : ℤ => ∑ k ∈ Q, F (x + a' + k) * star (F (x + b' + k))) (B + 2 * c) := by
  intro x hx
  refine Finset.sum_eq_zero (fun k hk => ?_)
  have h4 : (a' + k).natAbs ≤ 2 * c := by
    have h5 : (a' + k).natAbs ≤ a'.natAbs + k.natAbs := Int.natAbs_add_le _ _
    have := hQ a' ha'; have := hQ k hk; omega
  have h3 : x.natAbs ≤ (x + a' + k).natAbs + (a' + k).natAbs := by
    calc x.natAbs = ((x + a' + k) + (-(a' + k))).natAbs := by ring_nf
      _ ≤ (x + a' + k).natAbs + (-(a' + k)).natAbs := Int.natAbs_add_le _ _
      _ = (x + a' + k).natAbs + (a' + k).natAbs := by rw [Int.natAbs_neg]
  have h1 : B < (x + a' + k).natAbs := by omega
  rw [hF (x + a' + k) h1, zero_mul]

/-! ## The interior identity for the inner window sums -/

/-- **The interior identity.**  On the interior `symIcc (gapHalf P s N)` of the window, the inner
window sum of the iterated difference of the *windowed* dual function is the corresponding inner
window sum of the original one, shifted by `a`. -/
theorem inner_eq_of_gapR {s N N₀ D : ℕ} (hs : 2 ≤ s)
    (hNsGap : gapK0 P N + gapSig P s D ≤ gapHalf P s N)
    {f₀ f₁ : ℤ → ℂ} (a : ℤ) {sh : Fin (s - 2) → ℤ × ℤ}
    (hsh : ∀ i, (sh i).1 ∈ arithIcc P.leadingCoeff D ∧
      (sh i).2 ∈ arithIcc P.leadingCoeff D)
    {a' b' : ℤ} (ha' : a' ∈ arithIcc P.leadingCoeff D)
    (hb' : b' ∈ arithIcc P.leadingCoeff D) {x : ℤ} (hx : x ∈ symIcc (gapHalf P s N)) :
    (∑ k ∈ arithIcc P.leadingCoeff D,
        iterDelta (s - 2) sh (dualFn N P (gapLocalise f₀ a (gapNs P s N))
          (gapLocalise f₁ a (gapNs P s N))) (x + a' + k) *
        star (iterDelta (s - 2) sh (dualFn N P (gapLocalise f₀ a (gapNs P s N))
          (gapLocalise f₁ a (gapNs P s N))) (x + b' + k)))
      = (∑ k ∈ arithIcc P.leadingCoeff D,
        iterDelta (s - 2) sh (dualFn N P f₀ f₁) ((x + a) + a' + k) *
        star (iterDelta (s - 2) sh (dualFn N P f₀ f₁) ((x + a) + b' + k))) := by
  have hNs2 : gapNs P s N = 2 * gapHalf P s N := gapNs_eq_two_gapHalf P s N
  have hK0Ns : gapK0 P N + gapSig P s D ≤ gapNs P s N := by rw [hNs2]; omega
  have hK0le : gapK0 P N ≤ gapNs P s N := le_trans (Nat.le_add_right _ _) hK0Ns
  have hdual : ∀ u : ℤ, u ∈ gapGoodSet P N (gapNs P s N) →
      dualFn N P (gapLocalise f₀ a (gapNs P s N)) (gapLocalise f₁ a (gapNs P s N)) u
        = dualFn N P f₀ f₁ (u + a) :=
    fun u hu => dualFn_gapLocalise_eq hK0le f₀ f₁ a hu
  have hreach : ∀ ζ ∈ reach (s - 2) sh, ζ.natAbs ≤ (s - 2) * (D * P.leadingCoeff.natAbs) :=
    reach_natAbs_le _ sh (shift_entries_le hsh)
  have hsig : (s - 2) * (D * P.leadingCoeff.natAbs) + 2 * (D * P.leadingCoeff.natAbs)
      ≤ gapSig P s D := by
    rw [gapSig]
    have h : (s - 2) * (D * P.leadingCoeff.natAbs) + 2 * (D * P.leadingCoeff.natAbs)
        = s * (D * P.leadingCoeff.natAbs) := by rw [← add_mul]; congr 1; omega
    rw [h, mul_assoc]
  have hmain : ∀ y : ℤ, y.natAbs ≤ gapHalf P s N + 2 * (D * P.leadingCoeff.natAbs) →
      (iterDelta (s - 2) sh (dualFn N P (gapLocalise f₀ a (gapNs P s N))
        (gapLocalise f₁ a (gapNs P s N)))) y
        = (iterDelta (s - 2) sh (dualFn N P f₀ f₁)) (y + a) := by
    intro y hy
    refine iterDelta_congr (s - 2) sh _ _ _ a hdual y (fun ζ hζ => ?_)
    have hζle := hreach ζ hζ
    have h1 : (y + ζ).natAbs ≤ gapHalf P s N + gapSig P s D := by
      have h2 : (y + ζ).natAbs ≤ y.natAbs + ζ.natAbs := Int.natAbs_add_le _ _
      omega
    rw [gapGoodSet, mem_symIcc_iff, ← gapK0]
    omega
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hkD : k.natAbs ≤ D * P.leadingCoeff.natAbs := mem_arithIcc_le hk
  have ha'D : a'.natAbs ≤ D * P.leadingCoeff.natAbs := mem_arithIcc_le ha'
  have hb'D : b'.natAbs ≤ D * P.leadingCoeff.natAbs := mem_arithIcc_le hb'
  have hxl : x.natAbs ≤ gapHalf P s N := mem_symIcc_iff.mp hx
  have hxa : (x + a' + k).natAbs ≤ gapHalf P s N + 2 * (D * P.leadingCoeff.natAbs) := by
    have h1 : (x + a' + k).natAbs ≤ x.natAbs + a'.natAbs + k.natAbs := by
      calc (x + a' + k).natAbs ≤ (x + a').natAbs + k.natAbs := Int.natAbs_add_le _ _
        _ ≤ x.natAbs + a'.natAbs + k.natAbs := by
            have h2 := Int.natAbs_add_le x a'; omega
    omega
  have hxb : (x + b' + k).natAbs ≤ gapHalf P s N + 2 * (D * P.leadingCoeff.natAbs) := by
    have h1 : (x + b' + k).natAbs ≤ x.natAbs + b'.natAbs + k.natAbs := by
      calc (x + b' + k).natAbs ≤ (x + b').natAbs + k.natAbs := Int.natAbs_add_le _ _
        _ ≤ x.natAbs + b'.natAbs + k.natAbs := by
            have h2 := Int.natAbs_add_le x b'; omega
    omega
  rw [hmain _ hxa, hmain _ hxb]
  rw [show (x + a' + k) + a = (x + a) + a' + k by ring,
      show (x + b' + k) + a = (x + a) + b' + k by ring]

/-! ## The level bound for the windowed function -/

/-- The inner window sum over the direction set `Q`. -/
def gapInner (Q : Finset ℤ) (F : ℤ → ℂ) (a' b' : ℤ) : ℤ → ℂ :=
  fun x => ∑ k ∈ Q, F (x + a' + k) * star (F (x + b' + k))

/-- The interior mass of `F` over the window `symIcc l`, shifted by `a`. -/
def gapMass (Q : Finset ℤ) (F : ℤ → ℂ) (l : ℕ) (a : ℤ) : ℝ :=
  ∑ a' ∈ Q, ∑ b' ∈ Q, ∑ x ∈ symIcc l, ‖gapInner Q F a' b' (x + a)‖ ^ 2

/-- The total mass of `F`. -/
def gapTot (Q : Finset ℤ) (F : ℤ → ℂ) : ℝ :=
  ∑ a' ∈ Q, ∑ b' ∈ Q, ∑' x : ℤ, ‖gapInner Q F a' b' x‖ ^ 2

/-- The level-two box-norm power as a sum of the squares of the inner window sums. -/
theorem boxNormPow_two_eq_gapInner {Q S : Finset ℤ} {F : ℤ → ℂ} (hF : FinSuppZ F) :
    boxNormPow 2 (fun _ : Fin 2 => Q) S F
      = ((S.card : ℝ))⁻¹ * ((Q.card : ℝ))⁻¹ ^ 4 * gapTot Q F := by
  rw [Work.Peluse.BoxNormDilation.boxNormPow_two_eq Q S hF]
  rw [gapTot]
  simp only [gapInner]

/-- The arithmetic-progression set `arithIcc (lc P) D` is nonempty when `D ≥ 1`. -/
theorem arithIcc_card_pos {P : Polynomial ℤ} {D : ℕ} (hD : 1 ≤ D) :
    0 < (arithIcc P.leadingCoeff D).card :=
  Finset.card_pos.mpr ⟨P.leadingCoeff * 1, by
    rw [arithIcc]
    exact Finset.mem_image.mpr ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hD⟩, by ring⟩⟩

/-- **The interior mass is dominated by the total mass.** -/
theorem interior_le_total {Q : Finset ℤ} {c l : ℕ} {F G : ℤ → ℂ} {B' : ℕ}
    (hG : SupportIn G B') (hQ : ∀ z ∈ Q, z.natAbs ≤ c) (hl : l ≤ B' + 2 * c) (a : ℤ)
    (hint : ∀ a' ∈ Q, ∀ b' ∈ Q, ∀ x ∈ symIcc l,
      gapInner Q G a' b' x = gapInner Q F a' b' (x + a)) :
    gapMass Q F l a ≤ gapTot Q G := by
  rw [gapMass, gapTot]
  refine Finset.sum_le_sum (fun a' ha' => Finset.sum_le_sum (fun b' hb' => ?_))
  rw [Finset.sum_congr rfl (fun x hx => by rw [← hint a' ha' b' hb' x hx])]
  rw [tsum_eq_sum (s := symIcc (B' + 2 * c)) (fun x hx => by
    rw [mem_symIcc_iff] at hx
    have h0 : gapInner Q G a' b' x = 0 :=
      inner_support hG hQ ha' hb' x (not_le.mp hx)
    rw [h0, norm_zero]
    ring)]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity)
  intro z hz
  rw [mem_symIcc_iff] at hz ⊢
  omega

/-- **The windowed level dominates the interior mass of the mass function, shifted by `a`.** -/
theorem boxNorm_gapLocalise_ge {s N N₀ D : ℕ} (hs : 2 ≤ s)
    (hN : 1 ≤ N) (hD : 1 ≤ D) (hNs : N ≤ gapNs P s N)
    (hNsGap : gapK0 P N + gapSig P s D ≤ gapHalf P s N)
    {f₀ f₁ : ℤ → ℂ} (a : ℤ) {sh : Fin (s - 2) → ℤ × ℤ}
    (hsh : ∀ i, (sh i).1 ∈ arithIcc P.leadingCoeff D ∧
      (sh i).2 ∈ arithIcc P.leadingCoeff D) :
    (((arithIcc P.leadingCoeff D).card : ℝ))⁻¹ ^ 4 *
        gapMass (arithIcc P.leadingCoeff D) (iterDelta (s - 2) sh (dualFn N P f₀ f₁))
          (gapHalf P s N) a
      ≤ ((symIcc (dSup P (gapNs P s N) N)).card : ℝ) *
        boxNormPow 2 (fun _ : Fin 2 => arithIcc P.leadingCoeff D)
          (symIcc (dSup P (gapNs P s N) N))
          (iterDelta (s - 2) sh (dualFn N P (gapLocalise f₀ a (gapNs P s N))
            (gapLocalise f₁ a (gapNs P s N)))) := by
  have hfloc : FinSuppZ (iterDelta (s - 2) sh (dualFn N P (gapLocalise f₀ a (gapNs P s N))
      (gapLocalise f₁ a (gapNs P s N)))) :=
    FinSuppZ.of_supportIn (supportIn_iterDelta_gapLocalise (P := P) (s := s) (N := N) (D := D)
      hN hNs hsh a)
  have hB := boxNormPow_two_eq_gapInner
    (Q := arithIcc P.leadingCoeff D) (S := symIcc (dSup P (gapNs P s N) N))
    (F := iterDelta (s - 2) sh (dualFn N P (gapLocalise f₀ a (gapNs P s N))
      (gapLocalise f₁ a (gapNs P s N)))) hfloc
  have hSpos : (0 : ℝ) < ((symIcc (dSup P (gapNs P s N) N)).card : ℝ) := by
    rw [symIcc_card']; positivity
  have h1 : gapMass (arithIcc P.leadingCoeff D) (iterDelta (s - 2) sh (dualFn N P f₀ f₁))
        (gapHalf P s N) a
      ≤ gapTot (arithIcc P.leadingCoeff D)
        (iterDelta (s - 2) sh (dualFn N P (gapLocalise f₀ a (gapNs P s N))
          (gapLocalise f₁ a (gapNs P s N)))) := by
    refine interior_le_total (c := D * P.leadingCoeff.natAbs)
      (B' := dSup P (gapNs P s N) N + gapSig P s D)
      (supportIn_iterDelta_gapLocalise (P := P) (s := s) (N := N) (D := D) hN hNs hsh a)
      (fun z hz => mem_arithIcc_le hz) ?_ a (fun a' ha' b' hb' x hx => ?_)
    · have h2 : gapHalf P s N ≤ dSup P (gapNs P s N) N + gapSig P s D := by
        have h3 := gapNs_eq_two_gapHalf P s N
        rw [dSup]
        omega
      omega
    · have hA' : a' ∈ arithIcc P.leadingCoeff D := ha'
      have hB' : b' ∈ arithIcc P.leadingCoeff D := hb'
      exact inner_eq_of_gapR (P := P) (s := s) (N := N) (N₀ := N₀) (D := D)
        (f₀ := f₀) (f₁ := f₁) (sh := sh) (a' := a') (b' := b') (x := x)
        hs hNsGap a hsh hA' hB' hx
  calc (((arithIcc P.leadingCoeff D).card : ℝ))⁻¹ ^ 4 *
        gapMass (arithIcc P.leadingCoeff D) (iterDelta (s - 2) sh (dualFn N P f₀ f₁))
          (gapHalf P s N) a
      ≤ (((arithIcc P.leadingCoeff D).card : ℝ))⁻¹ ^ 4 *
        gapTot (arithIcc P.leadingCoeff D)
          (iterDelta (s - 2) sh (dualFn N P (gapLocalise f₀ a (gapNs P s N))
            (gapLocalise f₁ a (gapNs P s N)))) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ((symIcc (dSup P (gapNs P s N) N)).card : ℝ) *
        boxNormPow 2 (fun _ : Fin 2 => arithIcc P.leadingCoeff D)
          (symIcc (dSup P (gapNs P s N) N))
          (iterDelta (s - 2) sh (dualFn N P (gapLocalise f₀ a (gapNs P s N))
            (gapLocalise f₁ a (gapNs P s N)))) := by
        rw [hB]
        field_simp

/-- **The windowed levels are bounded by `2`.** -/
theorem boxNorm_gapLocalise_le_two {s N D : ℕ} (hN : 1 ≤ N) (hNs : N ≤ gapNs P s N)
    (hD : D ≤ N ^ P.natDegree)
    {f₀ f₁ : ℤ → ℂ} (hb0 : ∀ x : ℤ, ‖f₀ x‖ ≤ 1) (hb1 : ∀ x : ℤ, ‖f₁ x‖ ≤ 1) (a : ℤ)
    {sh : Fin (s - 2) → ℤ × ℤ}
    (hsh : ∀ i, (sh i).1 ∈ arithIcc P.leadingCoeff D ∧
      (sh i).2 ∈ arithIcc P.leadingCoeff D) :
    boxNormPow 2 (fun _ : Fin 2 => arithIcc P.leadingCoeff D)
      (symIcc (dSup P (gapNs P s N) N))
      (iterDelta (s - 2) sh (dualFn N P (gapLocalise f₀ a (gapNs P s N))
        (gapLocalise f₁ a (gapNs P s N)))) ≤ 2 := by
  have hsup : SupportIn (iterDelta (s - 2) sh (dualFn N P (gapLocalise f₀ a (gapNs P s N))
      (gapLocalise f₁ a (gapNs P s N)))) (dSup P (gapNs P s N) N + gapSig P s D) :=
    supportIn_iterDelta_gapLocalise (P := P) (s := s) (N := N) (D := D) hN hNs hsh a
  have hfin : FinSuppZ (iterDelta (s - 2) sh (dualFn N P (gapLocalise f₀ a (gapNs P s N))
      (gapLocalise f₁ a (gapNs P s N)))) := FinSuppZ.of_supportIn hsup
  have hbd : ∀ x : ℤ, ‖(iterDelta (s - 2) sh (dualFn N P (gapLocalise f₀ a (gapNs P s N))
      (gapLocalise f₁ a (gapNs P s N)))) x‖ ≤ 1 :=
    norm_iterDelta_le_one _ _ _ (dualFn_norm_le_one N P
      (norm_gapLocalise_le_one hb0 a _) (norm_gapLocalise_le_one hb1 a _))
  have h1 := boxNormPow_le_mass (t := 2) (by norm_num)
    (fun _ : Fin 2 => arithIcc P.leadingCoeff D) (symIcc (dSup P (gapNs P s N) N)) _ hbd hfin
  have h2 : (∑' x : ℤ, ‖(iterDelta (s - 2) sh (dualFn N P (gapLocalise f₀ a (gapNs P s N))
      (gapLocalise f₁ a (gapNs P s N)))) x‖) ≤ 2 * (dSup P (gapNs P s N) N + gapSig P s D) + 1 := by
    rw [tsum_eq_sum (s := symIcc (dSup P (gapNs P s N) N + gapSig P s D)) (fun x hx => by
      rw [mem_symIcc_iff] at hx
      rw [hsup x (not_le.mp hx), norm_zero])]
    calc ∑ x ∈ symIcc (dSup P (gapNs P s N) N + gapSig P s D),
          ‖(iterDelta (s - 2) sh (dualFn N P (gapLocalise f₀ a (gapNs P s N))
            (gapLocalise f₁ a (gapNs P s N)))) x‖
        ≤ ∑ _x ∈ symIcc (dSup P (gapNs P s N) N + gapSig P s D), (1 : ℝ) :=
          Finset.sum_le_sum (fun x _ => hbd x)
      _ = ((symIcc (dSup P (gapNs P s N) N + gapSig P s D)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = 2 * (dSup P (gapNs P s N) N + gapSig P s D) + 1 := by
          rw [symIcc_card']; push_cast; ring
  have hsig : gapSig P s D ≤ gapNs P s N := by
    rw [gapSig]
    calc s * D * P.leadingCoeff.natAbs ≤ s * N ^ P.natDegree * P.leadingCoeff.natAbs :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hD)
      _ = s * P.leadingCoeff.natAbs * N ^ P.natDegree := by ring
      _ ≤ gapHalf P s N := by
          rw [gapHalf]
          exact Nat.mul_le_mul_right _ (by omega)
      _ ≤ gapNs P s N := by rw [gapNs_eq_two_gapHalf]; omega
  have h3 : ((symIcc (dSup P (gapNs P s N) N)).card : ℝ)⁻¹
      * (2 * (dSup P (gapNs P s N) N + gapSig P s D) + 1) ≤ 2 := by
    rw [symIcc_card', dSup]
    push_cast
    rw [inv_mul_le_iff₀ (by positivity)]
    have hsigR : ((gapSig P s D : ℕ) : ℝ) ≤ ((gapNs P s N : ℕ) : ℝ) := by exact_mod_cast hsig
    nlinarith [hsigR, show (0 : ℝ) ≤ (polySup P N : ℝ) by positivity]
  calc boxNormPow 2 (fun _ : Fin 2 => arithIcc P.leadingCoeff D)
        (symIcc (dSup P (gapNs P s N) N)) _
      ≤ (∑' x : ℤ, ‖(iterDelta (s - 2) sh (dualFn N P (gapLocalise f₀ a (gapNs P s N))
          (gapLocalise f₁ a (gapNs P s N)))) x‖)
          * (((symIcc (dSup P (gapNs P s N) N)).card : ℝ))⁻¹ := h1
    _ ≤ (2 * (dSup P (gapNs P s N) N + gapSig P s D) + 1)
          * (((symIcc (dSup P (gapNs P s N) N)).card : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = ((symIcc (dSup P (gapNs P s N) N)).card : ℝ)⁻¹
          * (2 * (dSup P (gapNs P s N) N + gapSig P s D) + 1) := by ring
    _ ≤ 2 := h3

/-! ## Counting lemmas -/

/-- **Chebyshev counting.** -/
theorem card_filter_ge {ι : Type*} (t : Finset ι) (f : ι → ℝ) {T B : ℝ} (hB : 0 < B)
    (hf : ∀ i ∈ t, 0 ≤ f i) (hb : ∀ i ∈ t, f i ≤ B) (hT : T ≤ ∑ i ∈ t, f i) :
    T / (2 * B) ≤ ((t.filter (fun i => T / (2 * (t.card : ℝ)) ≤ f i)).card : ℝ) := by
  by_cases hT0 : T ≤ 0
  · have h1 : T / (2 * B) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hT0 (by positivity)
    have h2 : (0 : ℝ) ≤ ((t.filter (fun i => T / (2 * (t.card : ℝ)) ≤ f i)).card : ℝ) :=
      Nat.cast_nonneg _
    linarith
  · set m : Finset ι := t.filter (fun i => T / (2 * (t.card : ℝ)) ≤ f i) with hm
    have htcard : (0 : ℝ) < (t.card : ℝ) := by
      rcases Nat.eq_zero_or_pos t.card with h | h
      · exfalso
        have h0 := Finset.card_eq_zero.mp h
        rw [h0] at hT
        simp at hT
        linarith
      · exact_mod_cast h
    have hsplit := Finset.sum_filter_add_sum_filter_not (s := t)
      (p := fun i => T / (2 * (t.card : ℝ)) ≤ f i) (f := f)
    have h1 : ∑ i ∈ m, f i ≤ (m.card : ℝ) * B := by
      calc ∑ i ∈ m, f i ≤ ∑ _i ∈ m, B :=
            Finset.sum_le_sum (fun i hi =>
              hb i (by rw [hm] at hi; exact (Finset.mem_filter.mp hi).1))
        _ = (m.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
    have h2 : ∑ i ∈ t.filter (fun i => ¬ (T / (2 * (t.card : ℝ)) ≤ f i)), f i ≤ T / 2 := by
      calc ∑ i ∈ t.filter (fun i => ¬ (T / (2 * (t.card : ℝ)) ≤ f i)), f i
          ≤ ∑ _i ∈ t.filter (fun i => ¬ (T / (2 * (t.card : ℝ)) ≤ f i)),
              (T / (2 * (t.card : ℝ))) :=
            Finset.sum_le_sum (fun i hi => le_of_lt (not_le.mp (Finset.mem_filter.mp hi).2))
        _ = ((t.filter (fun i => ¬ (T / (2 * (t.card : ℝ)) ≤ f i))).card : ℝ)
              * (T / (2 * (t.card : ℝ))) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (t.card : ℝ) * (T / (2 * (t.card : ℝ))) := by
            have hle : (t.filter (fun i => ¬ (T / (2 * (t.card : ℝ)) ≤ f i))).card ≤ t.card :=
              Finset.card_filter_le _ _
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle)
              (by have : (0:ℝ) < T := not_le.mp hT0; positivity)
        _ = T / 2 := by field_simp
    have h3 : ∑ i ∈ t, f i ≤ (m.card : ℝ) * B + T / 2 := by
      rw [← hsplit]
      exact add_le_add h1 h2
    have h4 : T / 2 ≤ (m.card : ℝ) * B := by linarith
    have h5 : T / (2 * B) ≤ (m.card : ℝ) := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < 2 * B)]
      linarith
    rw [hm] at h5
    exact h5

/-- **Pigeonhole over the shift set.** -/
theorem exists_common_block {ι : Type*} (t : Finset ι) {A : Finset ℤ} (f : ℤ → ι → ℝ) {c : ℝ}
    (hA : A.Nonempty) (h : ∀ i ∈ t, c ≤ ∑ a ∈ A, f a i) (ht : t.Nonempty) :
    ∃ a ∈ A, c * (t.card : ℝ) / (A.card : ℝ) ≤ ∑ i ∈ t, f a i := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨a₀, ha₀⟩ := hA
  have hAcard : (0 : ℝ) < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨a₀, ha₀⟩
  have h1 : ∑ a ∈ A, ∑ i ∈ t, f a i < ∑ _a ∈ A, c * (t.card : ℝ) / (A.card : ℝ) := by
    refine Finset.sum_lt_sum (fun a ha => le_of_lt (hcon a ha)) ⟨a₀, ha₀, hcon a₀ ha₀⟩
  rw [Finset.sum_comm] at h1
  have h2 : ∑ _a ∈ A, c * (t.card : ℝ) / (A.card : ℝ) = c * (t.card : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp
  rw [h2] at h1
  have h3 : c * (t.card : ℝ) ≤ ∑ i ∈ t, ∑ a ∈ A, f a i := by
    calc c * (t.card : ℝ) = ∑ _i ∈ t, c := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ i ∈ t, ∑ a ∈ A, f a i := Finset.sum_le_sum h
  linarith

end

end Work.Peluse.Ulower.SsA
