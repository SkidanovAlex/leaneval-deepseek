import Mathlib
import Submission.Work.Peluse.UControl.lambdaMD_eq_inv_mul_LambdaZ
import Submission.Work.Peluse.UControl.assembly
import Submission.Work.Peluse.Concat.arithIcc_shrink_ge_two
import Submission.Work.Peluse.Pairing.boxSumPow_neg_directions

/-!
# Bookkeeping for `piecePet_of_props`: the ambient enlargement and the embedding

This module collects the elementary part of the reduction `Prop34 P → Prop36S P → PiecePet P`
(`Submission/Work/Peluse/UControl/piecePet_of_props.lean`).

The two chapters `Prop34`/`Prop36S` of `UControl/peluseFamily.lean` are stated at an ambient
`x`-range `N` and a `y`-range `M` linked by `M ^ deg P ≍ N`.  The data `Hyp` of `PiecePet` supplies
the relation only one way (`N₁ ≤ A' N^d` and `N^d ≤ A' γ⁻¹ N₁`), so the chapters are applied at the
*enlarged* ambient `Np = (⌈N^d/N₁⌉₊ + 1)·N₁`; the value of `Λ` at the enlarged ambient is the value
at `N₁` divided by the enlargement factor, and the output uniformity norm at `symIcc Np` is
transferred back to `symIcc N₁` (a gain: the box sum only sees the ambient through `|S|⁻¹`).
-/

set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse

/-! ## The ambient enlargement -/

/-- The ambient enlargement factor `⌈N^d / N₁⌉ + 1`. -/
def ambMu (d : ℕ) (N N₁ : ℕ) : ℕ := ⌈((N : ℝ) ^ d) / (N₁ : ℝ)⌉₊ + 1

lemma ambMu_two_le {d N N₁ : ℕ} (hN : 1 ≤ N) (hN₁ : 1 ≤ N₁) : 2 ≤ ambMu d N N₁ := by
  have hx : 0 < ((N : ℝ) ^ d) / (N₁ : ℝ) :=
    div_pos (pow_pos (by exact_mod_cast hN) d) (by exact_mod_cast hN₁)
  have : 1 ≤ ⌈((N : ℝ) ^ d) / (N₁ : ℝ)⌉₊ := Nat.ceil_pos.mpr hx
  simp only [ambMu]
  omega

lemma ambMu_pos {d N N₁ : ℕ} (hN : 1 ≤ N) (hN₁ : 1 ≤ N₁) : 1 ≤ ambMu d N N₁ :=
  le_trans (by norm_num) (ambMu_two_le hN hN₁)

/-- `N^d ≤ ambMu · N₁`. -/
lemma le_ambMu_mul {d N N₁ : ℕ} (hN₁ : 1 ≤ N₁) :
    (N : ℝ) ^ d ≤ (ambMu d N N₁ : ℝ) * N₁ := by
  have hN₁p : (0 : ℝ) < (N₁ : ℝ) := by exact_mod_cast hN₁
  have hceil : ((N : ℝ) ^ d) / (N₁ : ℝ) ≤ (⌈((N : ℝ) ^ d) / (N₁ : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have h1 : ((N : ℝ) ^ d) / (N₁ : ℝ) * (N₁ : ℝ) ≤
      (⌈((N : ℝ) ^ d) / (N₁ : ℝ)⌉₊ : ℝ) * (N₁ : ℝ) :=
    mul_le_mul_of_nonneg_right hceil hN₁p.le
  rw [div_mul_cancel₀ _ (ne_of_gt hN₁p)] at h1
  refine le_trans h1 (mul_le_mul_of_nonneg_right ?_ hN₁p.le)
  simp only [ambMu]
  push_cast
  linarith

/-- `ambMu · N₁ < N^d + 2 N₁`. -/
lemma ambMu_mul_lt {d N N₁ : ℕ} (hN₁ : 1 ≤ N₁) :
    (ambMu d N N₁ : ℝ) * (N₁ : ℝ) < (N : ℝ) ^ d + 2 * (N₁ : ℝ) := by
  have hN₁p : (0 : ℝ) < (N₁ : ℝ) := by exact_mod_cast hN₁
  have hx0 : (0 : ℝ) ≤ ((N : ℝ) ^ d) / (N₁ : ℝ) := by positivity
  have hceil : ((⌈((N : ℝ) ^ d) / (N₁ : ℝ)⌉₊ : ℕ) : ℝ) < ((N : ℝ) ^ d) / (N₁ : ℝ) + 1 :=
    Nat.ceil_lt_add_one hx0
  have ham : ((ambMu d N N₁ : ℕ) : ℝ) < ((N : ℝ) ^ d) / (N₁ : ℝ) + 2 := by
    simp only [ambMu]
    push_cast
    linarith
  calc (ambMu d N N₁ : ℝ) * (N₁ : ℝ)
      < (((N : ℝ) ^ d) / (N₁ : ℝ) + 2) * (N₁ : ℝ) := mul_lt_mul_of_pos_right ham hN₁p
    _ = (N : ℝ) ^ d + 2 * (N₁ : ℝ) := by field_simp

/-- `N₁ + N^{d-1} ≤ ambMu · N₁` for `1 ≤ d` (real form). -/
lemma ambMu_hscale_real {d N N₁ : ℕ} (hd : 1 ≤ d) (hN : 1 ≤ N) (hN₁ : 1 ≤ N₁) :
    (N₁ : ℝ) + (N : ℝ) ^ (d - 1) ≤ (ambMu d N N₁ : ℝ) * N₁ := by
  have hN₁p : (0 : ℝ) < (N₁ : ℝ) := by exact_mod_cast hN₁
  have hceil : ((N : ℝ) ^ d) / (N₁ : ℝ) ≤ (⌈((N : ℝ) ^ d) / (N₁ : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have h1 : ((N : ℝ) ^ d) / (N₁ : ℝ) * (N₁ : ℝ) ≤
      (⌈((N : ℝ) ^ d) / (N₁ : ℝ)⌉₊ : ℝ) * (N₁ : ℝ) :=
    mul_le_mul_of_nonneg_right hceil hN₁p.le
  rw [div_mul_cancel₀ _ (ne_of_gt hN₁p)] at h1
  have h2 : (⌈((N : ℝ) ^ d) / (N₁ : ℝ)⌉₊ : ℝ) * (N₁ : ℝ) + (N₁ : ℝ)
      ≤ (ambMu d N N₁ : ℝ) * (N₁ : ℝ) := by
    have hcast : (⌈((N : ℝ) ^ d) / (N₁ : ℝ)⌉₊ : ℝ) + 1 ≤ (ambMu d N N₁ : ℝ) := by
      simp only [ambMu]
      push_cast
      linarith
    nlinarith [hN₁p, hcast]
  have h3 : (N : ℝ) ^ (d - 1) ≤ (N : ℝ) ^ d := by
    have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    exact pow_le_pow_right₀ h1N (Nat.sub_le d 1)
  linarith

/-- `N₁ + N^{d-1} ≤ ambMu · N₁` for `1 ≤ d` (`ℕ` form). -/
lemma ambMu_hscale {d N N₁ : ℕ} (hd : 1 ≤ d) (hN : 1 ≤ N) (hN₁ : 1 ≤ N₁) :
    N₁ + N ^ (d - 1) ≤ ambMu d N N₁ * N₁ := by
  have h := ambMu_hscale_real (d := d) (N := N) (N₁ := N₁) hd hN hN₁
  exact_mod_cast h

/-- `⌈N^d/N₁⌉ ≤ A'/γ + 1` when `N^d ≤ A' γ⁻¹ N₁`. -/
lemma ambMu_le_of_scale {d N N₁ : ℕ} {A' γ : ℝ} (hN₁ : 1 ≤ N₁) (hγ : 0 < γ) (hA' : 1 ≤ A')
    (hsc2 : (N : ℝ) ^ d ≤ A' * γ⁻¹ * (N₁ : ℝ)) :
    ((⌈((N : ℝ) ^ d) / (N₁ : ℝ)⌉₊ : ℕ) : ℝ) ≤ A' / γ + 1 := by
  have hN₁p : (0 : ℝ) < (N₁ : ℝ) := by exact_mod_cast hN₁
  have hx0 : (0 : ℝ) ≤ ((N : ℝ) ^ d) / (N₁ : ℝ) := by positivity
  have hceil : ((⌈((N : ℝ) ^ d) / (N₁ : ℝ)⌉₊ : ℕ) : ℝ) < ((N : ℝ) ^ d) / (N₁ : ℝ) + 1 :=
    Nat.ceil_lt_add_one hx0
  have hdiv : ((N : ℝ) ^ d) / (N₁ : ℝ) ≤ A' / γ := by
    rw [div_le_div_iff₀ hN₁p hγ]
    calc (N : ℝ) ^ d * γ ≤ (A' * γ⁻¹ * (N₁ : ℝ)) * γ :=
          mul_le_mul_of_nonneg_right hsc2 hγ.le
      _ = A' * (N₁ : ℝ) := by field_simp
  linarith


/-! ## The ambient/direction transfer for `uNormPow` -/

lemma mem_symIcc {L : ℕ} {x : ℤ} : x ∈ symIcc L ↔ |x| ≤ (L : ℤ) := by
  simp [symIcc, abs_le]

/-- The cardinality of the symmetric interval. -/
lemma symIcc_card (L : ℕ) : (symIcc L).card = 2 * L + 1 := by
  rw [symIcc, Int.card_Icc]
  have h : ((L : ℤ) + 1 - (-(L : ℤ))) = ((2 * L + 1 : ℕ) : ℤ) := by
    push_cast; ring
  rw [h, Int.toNat_natCast]

lemma symIcc_mono {N N' : ℕ} (h : N ≤ N') : symIcc N ⊆ symIcc N' := by
  intro x hx
  rw [mem_symIcc] at hx ⊢
  exact le_trans hx (by exact_mod_cast h)

/-- The box sum is `|S|⁻¹` times a factor independent of the ambient set `S`. -/
lemma boxSumPow_eq_inv_mul_common_p {t : ℕ} (Q : Fin t → Finset ℤ) (f : ℤ → ℂ) :
    ∃ A : ℂ, ∀ S : Finset ℤ, boxSumPow t Q S f = ((S.card : ℂ))⁻¹ * A := by
  refine ⟨(∏ i : Fin t, (((Q i).card : ℂ))⁻¹) * (∏ i : Fin t, (((Q i).card : ℂ))⁻¹) *
      ∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i}, ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
        ∑' x : ℤ, ∏ ω : Fin t → Bool,
          (star^[weight ω]) (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)), ?_⟩
  intro S
  simp only [boxSumPow, prodCubeSum_eq]
  ring

/-- Changing the ambient set rescales the box-norm power by the ratio of the cardinalities. -/
lemma boxNormPow_symIcc_ratio_p {t : ℕ} (Q : Fin t → Finset ℤ) (N N' : ℕ) (f : ℤ → ℂ) :
    boxNormPow t Q (symIcc N') f
      = (((symIcc N).card : ℕ) : ℝ) / (((symIcc N').card : ℕ) : ℝ) *
          boxNormPow t Q (symIcc N) f := by
  obtain ⟨A, hA⟩ := boxSumPow_eq_inv_mul_common_p Q f
  have h1 : boxSumPow t Q (symIcc N') f = (((symIcc N').card : ℂ))⁻¹ * A := hA _
  have h2 : boxSumPow t Q (symIcc N) f = (((symIcc N).card : ℂ))⁻¹ * A := hA _
  rw [boxNormPow, boxNormPow, h1, h2, norm_mul, norm_mul, norm_inv, norm_inv,
    Complex.norm_natCast, Complex.norm_natCast]
  have hmem' : (0 : ℤ) ∈ symIcc N' := by rw [mem_symIcc]; simp
  have hmem : (0 : ℤ) ∈ symIcc N := by rw [mem_symIcc]; simp
  have ha : (((symIcc N').card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Finset.card_pos.mpr ⟨0, hmem'⟩))
  have hb : (((symIcc N).card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Finset.card_pos.mpr ⟨0, hmem⟩))
  field_simp

/-- Enlarging the ambient interval (which only rescales by `|S|⁻¹`) can only decrease the
uniformity-norm power. -/
lemma uNormPow_symIcc_mono {s : ℕ} (Q : Finset ℤ) {N N' : ℕ} (h : N ≤ N') (g : ℤ → ℂ) :
    uNormPow s Q (symIcc N') g ≤ uNormPow s Q (symIcc N) g := by
  have hratio := boxNormPow_symIcc_ratio_p (fun _ : Fin s => Q) N N' g
  have hcard : (((symIcc N).card : ℕ) : ℝ) ≤ (((symIcc N').card : ℕ) : ℝ) := by
    exact_mod_cast Finset.card_le_card (symIcc_mono h)
  have hpos : (0 : ℝ) < (((symIcc N').card : ℕ) : ℝ) := by
    have : 0 < (symIcc N').card := Finset.card_pos.mpr ⟨0, by rw [mem_symIcc]; simp⟩
    exact_mod_cast this
  have hnn : 0 ≤ boxNormPow s (fun _ : Fin s => Q) (symIcc N) g := norm_nonneg _
  simp only [uNormPow]
  rw [hratio]
  calc (((symIcc N).card : ℕ) : ℝ) / (((symIcc N').card : ℕ) : ℝ) *
        boxNormPow s (fun _ : Fin s => Q) (symIcc N) g
      ≤ 1 * boxNormPow s (fun _ : Fin s => Q) (symIcc N) g := by
        refine mul_le_mul_of_nonneg_right (by rw [div_le_one hpos]; exact hcard) hnn
    _ = boxNormPow s (fun _ : Fin s => Q) (symIcc N) g := one_mul _

/-- Reflection of the directions keeps the uniformity-norm power. -/
lemma uNormPow_arithIcc_neg_p (s : ℕ) (c : ℤ) (L N : ℕ) (f : ℤ → ℂ) :
    uNormPow s (arithIcc c L) (symIcc N) f
      = uNormPow s (arithIcc (-c) L) (symIcc N) (fun x : ℤ => f (-x)) := by
  have hfun : (fun _ : Fin s => arithIcc c L)
      = fun _ : Fin s => (arithIcc (-c) L).image (fun z : ℤ => -z) := by
    funext i
    rw [arithIcc, arithIcc, Finset.image_image]
    congr 1
    funext n
    simp
  simp only [uNormPow, boxNormPow]
  rw [hfun, Pairing.boxSumPow_neg_directions]

/-- **Shrinking the direction count and enlarging the ambient interval.**  A lower bound for the
uniformity-norm power at the *long* direction set `κ[L']` and the ambient `symIcc N'` transfers to
the short set `κ[L]` (`L ≤ L'`) and the ambient `symIcc N` (`N ≤ N'`), at the price of a constant
depending only on the level. -/
lemma uNormPow_shrink_ambient {s : ℕ} (hs : 2 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (κ : ℤ) (L L' N N' : ℕ) (g : ℤ → ℂ),
      κ ≠ 0 → 1 ≤ L → L ≤ L' → N ≤ N' →
      SupportIn g N → (∀ x : ℤ, ‖g x‖ ≤ 1) →
      C * uNormPow s (arithIcc κ L') (symIcc N') g
        ≤ uNormPow s (arithIcc κ L) (symIcc N) g := by
  obtain ⟨C₁, hC₁, H⟩ := Concat.arithIcc_shrink_ge_two (t := s) hs
  refine ⟨C₁, hC₁, ?_⟩
  intro κ L L' N N' g hκ hL hLL hNN hsupp hbnd
  have hsupp' : SupportIn g N' := hsupp.mono hNN
  have hmono : uNormPow s (arithIcc κ L) (symIcc N') g ≤ uNormPow s (arithIcc κ L) (symIcc N) g :=
    uNormPow_symIcc_mono _ hNN g
  have hshrink : C₁ * uNormPow s (arithIcc κ L') (symIcc N') g
      ≤ uNormPow s (arithIcc κ L) (symIcc N') g := by
    rcases lt_or_gt_of_ne hκ with hneg | hpos
    · -- `κ < 0`
      have hpos' : 0 < -κ := by omega
      have hbnd' : ∀ x : ℤ, ‖(fun x : ℤ => g (-x)) x‖ ≤ 1 := fun x => hbnd (-x)
      have hsupp'' : SupportIn (fun x : ℤ => g (-x)) N' := by
        intro x hx
        exact hsupp' (-x) (by simpa using hx)
      rw [uNormPow_arithIcc_neg_p s κ L' N' g, uNormPow_arithIcc_neg_p s κ L N' g]
      exact H (-κ) hpos' L L' hL hLL (f := fun x : ℤ => g (-x)) hsupp'' hbnd'
    · exact H κ hpos L L' hL hLL (f := g) hsupp' hbnd
  exact le_trans hshrink hmono

/-! ## The embedding of the bilinear triple into the full progression -/

/-- The embedding of the triple `(g₀,g₁,g₂)` into the functions
`F : Fin (d+1) → ℤ → ℂ` of the full progression `(x, x+y, x+y², …, x+y^{d-1}, x+P(y))`: the first
slot is `g₀`, the second `g₁`, the last `g₂`, and every intermediate slot is the indicator of the
ambient interval `symIcc Np`, which is `1` on the whole range on which those slots are evaluated. -/
def embF (d : ℕ) (Np : ℕ) (g₀ g₁ g₂ : ℤ → ℂ) : Fin (d + 1) → ℤ → ℂ :=
  fun i => if (i : ℕ) = 0 then g₀ else if (i : ℕ) = 1 then g₁ else
    if (i : ℕ) = d then g₂ else fun x => if x ∈ symIcc Np then (1 : ℂ) else 0

lemma embF_zero (d Np : ℕ) (g₀ g₁ g₂ : ℤ → ℂ) :
    embF d Np g₀ g₁ g₂ ⟨0, Nat.succ_pos d⟩ = g₀ := by
  simp [embF]

lemma embF_one {d : ℕ} (hd : 1 ≤ d) (Np : ℕ) (g₀ g₁ g₂ : ℤ → ℂ) :
    embF d Np g₀ g₁ g₂ 1 = g₁ := by
  have h1 : ((1 : Fin (d + 1)) : ℕ) = 1 := by
    rw [show ((1 : Fin (d + 1)) : ℕ) = 1 % (d + 1) from rfl, Nat.mod_eq_of_lt (by omega)]
  simp only [embF]
  rw [h1]
  norm_num

lemma embF_last {d : ℕ} (hd : 2 ≤ d) (Np : ℕ) (g₀ g₁ g₂ : ℤ → ℂ) :
    embF d Np g₀ g₁ g₂ ⟨d, Nat.lt_succ_self d⟩ = g₂ := by
  have h0 : ¬ (d = 0) := by omega
  have h1 : ¬ (d = 1) := by omega
  simp only [embF]
  rw [if_neg h0, if_neg h1]
  simp

/-- On the intermediate slots (`2 ≤ i ≤ d-1`) the embedding is the indicator of `symIcc Np`, hence
`1` on every point of `symIcc Np`. -/
lemma embF_mid {d : ℕ} (hd : 1 ≤ d) {Np : ℕ} {g₀ g₁ g₂ : ℤ → ℂ} {i : Fin (d + 1)}
    (hi2 : 2 ≤ (i : ℕ)) (hid : (i : ℕ) ≤ d - 1) {x : ℤ} (hx : x ∈ symIcc Np) :
    embF d Np g₀ g₁ g₂ i x = 1 := by
  have hlt : (i : ℕ) < d := by omega
  have hne0 : ¬ ((i : ℕ) = 0) := by omega
  have hne1 : ¬ ((i : ℕ) = 1) := by omega
  have hned : ¬ ((i : ℕ) = d) := by omega
  simp only [embF, hne0, hne1, hned, if_false]
  exact if_pos hx

lemma embF_supportIn {d Np N₁ : ℕ} {g₀ g₁ g₂ : ℤ → ℂ} (hN₁ : N₁ ≤ Np)
    (h₀ : SupportIn g₀ N₁) (h₁ : SupportIn g₁ N₁) (h₂ : SupportIn g₂ N₁) :
    ∀ i : Fin (d + 1), SupportIn (embF d Np g₀ g₁ g₂ i) Np := by
  intro i
  by_cases h0 : (i : ℕ) = 0
  · intro x hx
    rw [embF, if_pos h0]
    exact h₀ x (lt_of_le_of_lt hN₁ hx)
  · by_cases h1 : (i : ℕ) = 1
    · intro x hx
      rw [embF, if_neg h0, if_pos h1]
      exact h₁ x (lt_of_le_of_lt hN₁ hx)
    · by_cases hd : (i : ℕ) = d
      · intro x hx
        rw [embF, if_neg h0, if_neg h1, if_pos hd]
        exact h₂ x (lt_of_le_of_lt hN₁ hx)
      · intro x hx
        rw [embF, if_neg h0, if_neg h1, if_neg hd]
        rw [if_neg]
        intro hmem
        have hle : |x| ≤ (Np : ℤ) := mem_symIcc.mp hmem
        rw [← Int.natCast_natAbs] at hle
        have hle' : x.natAbs ≤ Np := by exact_mod_cast hle
        omega

lemma embF_bound {d Np : ℕ} {g₀ g₁ g₂ : ℤ → ℂ}
    (h₀ : ∀ x, ‖g₀ x‖ ≤ 1) (h₁ : ∀ x, ‖g₁ x‖ ≤ 1) (h₂ : ∀ x, ‖g₂ x‖ ≤ 1) :
    ∀ (i : Fin (d + 1)) (x : ℤ), ‖embF d Np g₀ g₁ g₂ i x‖ ≤ 1 := by
  intro i x
  by_cases h0 : (i : ℕ) = 0
  · rw [embF, if_pos h0]; exact h₀ x
  · by_cases h1 : (i : ℕ) = 1
    · rw [embF, if_neg h0, if_pos h1]; exact h₁ x
    · by_cases hd : (i : ℕ) = d
      · rw [embF, if_neg h0, if_neg h1, if_pos hd]; exact h₂ x
      · rw [embF, if_neg h0, if_neg h1, if_neg hd]
        by_cases hmem : x ∈ symIcc Np
        · rw [if_pos hmem]; norm_num
        · rw [if_neg hmem]; norm_num

/-- **The bridge.**  At the enlarged ambient `Np = ambMu · N₁` the full-progression average of the
embedded functions equals `ambMu⁻¹` times the bilinear average at `N₁`. -/
theorem embLambdaMD {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree) {N N₁ : ℕ}
    (hN : 1 ≤ N) (hN₁ : 1 ≤ N₁) (g₀ g₁ g₂ : ℤ → ℂ) (h₀ : SupportIn g₀ N₁) :
    LambdaMD (ambMu P.natDegree N N₁ * N₁) N P
        (embF P.natDegree (ambMu P.natDegree N N₁ * N₁) g₀ g₁ g₂)
      = (((ambMu P.natDegree N N₁ : ℕ) : ℂ))⁻¹ * LambdaZ N₁ N P g₀ g₁ g₂ := by
  have hd1 : 1 ≤ P.natDegree := by omega
  have hscale : N₁ + N ^ (P.natDegree - 1) ≤ ambMu P.natDegree N N₁ * N₁ :=
    ambMu_hscale (d := P.natDegree) (N := N) (N₁ := N₁) hd1 hN hN₁
  have hminge : 1 ≤ ambMu P.natDegree N N₁ * N₁ := by
    have := ambMu_pos (d := P.natDegree) hN hN₁
    nlinarith [hN₁]
  have hmid : ∀ (i : Fin (P.natDegree + 1)) (y : ℤ), 2 ≤ (i : ℕ) →
      (i : ℕ) ≤ P.natDegree - 1 →
      |y| ≤ (((ambMu P.natDegree N N₁ * N₁ : ℕ) : ℤ)) →
      embF P.natDegree (ambMu P.natDegree N N₁ * N₁) g₀ g₁ g₂ i y = 1 := by
    intro i y hi2 hid hy
    refine embF_mid hd1 hi2 hid ?_
    rw [mem_symIcc]
    exact hy
  exact lambdaMD_eq_inv_mul_LambdaZ (P := P) hd N (ambMu P.natDegree N N₁) N₁ hN hN₁
    (ambMu_pos (d := P.natDegree) hN hN₁) hscale g₀ g₁ g₂ _
    (embF_zero _ _ _ _ _) (embF_one hd1 _ _ _ _) (embF_last hd _ _ _ _) hmid h₀


/-- **The window bound.**  The data's smallness hypothesis `C·L ≤ γ^K N₁` together with the gauge
`A'·Cp ≤ C` forces the shift parameter to be small:
`δ' ≤ 2 γ^K / Cp`. -/
theorem delta_le_of_window_p {P : Polynomial ℤ} {A' C Cp : ℝ} {K : ℕ} {N N₁ : ℕ}
    {g₀ g₁ g₂ : ℤ → ℂ} {γ δ' : ℝ}
    (h : Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ') (hA' : 1 ≤ A') (hgauge : A' * Cp ≤ C)
    (hCp : 1 ≤ Cp) : δ' ≤ 2 * γ ^ K / Cp := by
  have h' := h
  obtain ⟨hd, hN, hN₁, hγ0, hγ1, hδ0, hδ1, hwin, hsc1, hsc2, hC1, hK1, hsmall, hnd,
    hS0, hS1, hS2, hb0, hb1, hb2, hΛ⟩ := h'
  have hL1 : 1 ≤ dirLen P δ' N := Work.Peluse.UControl.Hyp.one_le_dirLen h
  have hA'pos : (0 : ℝ) < A' := lt_of_lt_of_le one_pos hA'
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  have hCppos : (0 : ℝ) < Cp := lt_of_lt_of_le one_pos hCp
  have hL1R : (1 : ℝ) ≤ (dirLen P δ' N : ℝ) := by exact_mod_cast hL1
  have hC_le : C ≤ γ ^ K * (N₁ : ℝ) :=
    calc C ≤ C * (dirLen P δ' N : ℝ) := le_mul_of_one_le_right hCpos.le hL1R
      _ ≤ γ ^ K * (N₁ : ℝ) := hsmall
  have hNpos : (0 : ℝ) < (N : ℝ) ^ P.natDegree := by
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    positivity
  have hCp_le : Cp ≤ γ ^ K * (N : ℝ) ^ P.natDegree := by
    have h1 : A' * Cp ≤ γ ^ K * (N₁ : ℝ) := le_trans hgauge hC_le
    have h2 : γ ^ K * (N₁ : ℝ) ≤ γ ^ K * (A' * (N : ℝ) ^ P.natDegree) :=
      mul_le_mul_of_nonneg_left hsc1 (by positivity)
    have h3 : A' * Cp ≤ A' * (γ ^ K * (N : ℝ) ^ P.natDegree) := by linarith [le_trans h1 h2]
    have h4 : Cp ≤ γ ^ K * (N : ℝ) ^ P.natDegree := le_of_mul_le_mul_left h3 hA'pos
    exact h4
  -- `1 / N^d ≤ γ^K / Cp`
  have h1div : 1 / (N : ℝ) ^ P.natDegree ≤ γ ^ K / Cp := by
    rw [div_le_div_iff₀ hNpos hCppos]
    simpa using hCp_le
  -- `δ' ≤ L/N^d + 1/N^d`
  have hfloornn : (0 : ℤ) ≤ ⌊δ' * (N : ℝ) ^ P.natDegree⌋ := by
    by_contra hneg
    have hzero : (⌊δ' * (N : ℝ) ^ P.natDegree⌋).toNat = 0 := Int.toNat_of_nonpos (by omega)
    rw [dirLen, hzero] at hL1
    omega
  have hlt : δ' * (N : ℝ) ^ P.natDegree < (dirLen P δ' N : ℝ) + 1 := by
    have h := Int.lt_floor_add_one (δ' * (N : ℝ) ^ P.natDegree)
    have hcast : (⌊δ' * (N : ℝ) ^ P.natDegree⌋ : ℝ) = (dirLen P δ' N : ℝ) := by
      rw [dirLen]
      exact_mod_cast (Int.toNat_of_nonneg hfloornn).symm
    calc δ' * (N : ℝ) ^ P.natDegree < (⌊δ' * (N : ℝ) ^ P.natDegree⌋ : ℝ) + 1 := by
          exact_mod_cast h
      _ = (dirLen P δ' N : ℝ) + 1 := by rw [hcast]
  have hdelta : δ' ≤ (dirLen P δ' N : ℝ) / (N : ℝ) ^ P.natDegree
      + 1 / (N : ℝ) ^ P.natDegree := by
    have h1 : δ' = δ' * (N : ℝ) ^ P.natDegree / (N : ℝ) ^ P.natDegree :=
      (mul_div_cancel_right₀ _ (ne_of_gt hNpos)).symm
    have h2 : δ' * (N : ℝ) ^ P.natDegree / (N : ℝ) ^ P.natDegree
        < ((dirLen P δ' N : ℝ) + 1) / (N : ℝ) ^ P.natDegree :=
      div_lt_div_of_pos_right hlt hNpos
    have h3 : ((dirLen P δ' N : ℝ) + 1) / (N : ℝ) ^ P.natDegree
        = (dirLen P δ' N : ℝ) / (N : ℝ) ^ P.natDegree + 1 / (N : ℝ) ^ P.natDegree :=
      add_div _ _ _
    calc δ' = δ' * (N : ℝ) ^ P.natDegree / (N : ℝ) ^ P.natDegree := h1
      _ ≤ ((dirLen P δ' N : ℝ) + 1) / (N : ℝ) ^ P.natDegree := le_of_lt h2
      _ = (dirLen P δ' N : ℝ) / (N : ℝ) ^ P.natDegree + 1 / (N : ℝ) ^ P.natDegree := h3
  have hLdiv : (dirLen P δ' N : ℝ) / (N : ℝ) ^ P.natDegree ≤ γ ^ K * A' / C := by
    rw [div_le_div_iff₀ hNpos hCpos]
    have h1 : (dirLen P δ' N : ℝ) * C ≤ γ ^ K * (N₁ : ℝ) := by
      rw [mul_comm]; exact hsmall
    have h2 : γ ^ K * (N₁ : ℝ) ≤ γ ^ K * (A' * (N : ℝ) ^ P.natDegree) :=
      mul_le_mul_of_nonneg_left hsc1 (by positivity)
    linarith [le_trans h1 h2]
  have hA'C : γ ^ K * A' / C ≤ γ ^ K / Cp := by
    rw [div_le_div_iff₀ hCpos hCppos]
    nlinarith [hgauge, pow_nonneg hγ0.le K]
  have htwo : γ ^ K * A' / C + γ ^ K / Cp ≤ 2 * γ ^ K / Cp := by
    have h : 2 * γ ^ K / Cp = γ ^ K / Cp + γ ^ K / Cp := by ring
    linarith [hA'C, h]
  calc δ' ≤ (dirLen P δ' N : ℝ) / (N : ℝ) ^ P.natDegree + 1 / (N : ℝ) ^ P.natDegree := hdelta
    _ ≤ γ ^ K * A' / C + γ ^ K / Cp := add_le_add hLdiv h1div
    _ ≤ 2 * γ ^ K / Cp := htwo

end

end Work.Peluse.UControl
