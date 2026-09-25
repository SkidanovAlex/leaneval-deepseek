import Mathlib
import Submission.Commons.Analysis.Fourier.boundary_layer_l2
import Submission.Commons.Analysis.Fourier.bandOp_l2_multiplier_bound
import Submission.Commons.Analysis.Fourier.nested_scales_maximal_l2_real

/-!
# Boundary-layer `L²` square function for `1/8`-separated frequencies (real line, `2π`-convention)

This file proves `Commons.Analysis.Fourier.boundary_layer_eighth_separated_real`: the
boundary-layer square-function bound of Bourgain (1989), Lemma 4.11/4.13, for a family of
frequencies that is only `1/8`-separated, in the Fourier convention that carries `2π` in the
exponent.

The proof has three ingredients:
* a pointwise bound `∑_j ‖symb_j θ‖² ≤ 128` for the boundary-layer symbols (a counting
  argument: for `1/8`-separated frequencies, at each dyadic scale at most `16 h_j + 1`
  frequencies are near `θ`, and — because `h_{j'} ≤ h_j/2` — at most one scale `j ≥ 4`
  contributes at all);
* the general `L²` square-function bound for a countable family of band operators
  (`bandFamily_square_bound`), proved by Plancherel; and
* the identification of the target's bracket with the band kernel of the rescaled symbol,
  together with the `L¹ ∩ L²` truncation argument.
-/

namespace Commons.Analysis.Fourier

open MeasureTheory Filter
open scoped BigOperators ENNReal FourierTransform Topology

noncomputable section

open BoundaryLayer

/-! ## A point-counting lemma -/

private theorem card_le_of_pairwise_separated {α : Type*} {t : Finset α} (f : α → ℝ) {s : ℝ}
    (hs : 0 < s) (hsep : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → s ≤ |f x - f y|) {a b : ℝ} (hab : a ≤ b)
    (ha : ∀ x ∈ t, a ≤ f x) (hb : ∀ x ∈ t, f x ≤ b) :
    ((t.card : ℕ) : ℝ) ≤ (b - a) / s + 1 := by
  classical
  have hstep : ∀ x ∈ t, ∀ y ∈ t, f x < f y →
      ⌊(f x - a) / s⌋ + 1 ≤ ⌊(f y - a) / s⌋ := by
    intro x hx y hy hlt
    have hge : s ≤ f y - f x := by
      have h := hsep x hx y hy (ne_of_apply_ne f (ne_of_lt hlt))
      rw [abs_of_neg (sub_neg.mpr hlt)] at h
      linarith
    have h1 : (f x - a)/s + 1 ≤ (f y - a)/s := by
      rw [div_add_one (ne_of_gt hs), div_le_div_iff_of_pos_right hs]
      linarith
    calc ⌊(f x - a) / s⌋ + 1 = ⌊(f x - a)/s + 1⌋ := (Int.floor_add_one _).symm
      _ ≤ ⌊(f y - a)/s⌋ := Int.floor_mono h1
  have hinj : Set.InjOn (fun x => ⌊(f x - a)/s⌋) ↑t := by
    intro x hx y hy hxy
    dsimp only at hxy
    rcases lt_trichotomy (f x) (f y) with hlt | heq | hgt
    · exfalso
      have h := hstep x hx y hy hlt
      rw [hxy] at h
      omega
    · by_contra hne
      have h := hsep x hx y hy hne
      rw [heq, sub_self, abs_zero] at h
      linarith
    · exfalso
      have h := hstep y hy x hx hgt
      rw [← hxy] at h
      omega
  have hcard : (t.card : ℝ) = ((t.image (fun x => ⌊(f x - a)/s⌋)).card : ℝ) := by
    rw [Finset.card_image_of_injOn hinj]
  have hsub : t.image (fun x => ⌊(f x - a)/s⌋) ⊆ Finset.Icc (0:ℤ) ⌊(b - a)/s⌋ := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [Finset.mem_Icc]
    constructor
    · rw [Int.le_floor]; push_cast
      exact div_nonneg (by linarith [ha x hx]) (le_of_lt hs)
    · apply Int.floor_le_floor
      apply div_le_div_of_nonneg_right _ (le_of_lt hs)
      linarith [hb x hx]
  have hN : (0:ℤ) ≤ ⌊(b - a)/s⌋ := by
    rw [Int.floor_nonneg]; exact div_nonneg (by linarith) (le_of_lt hs)
  have hle : ((Finset.Icc (0:ℤ) ⌊(b - a)/s⌋).card : ℕ) ≤ ⌊(b - a)/s⌋.toNat + 1 := by
    rw [Int.card_Icc]; omega
  have hNcast : ((⌊(b - a)/s⌋.toNat : ℕ) : ℝ) = (⌊(b - a)/s⌋ : ℝ) := by
    have h := Int.toNat_of_nonneg hN
    exact_mod_cast h
  have h2 : ((Finset.Icc (0:ℤ) ⌊(b - a)/s⌋).card : ℝ) ≤ (⌊(b - a)/s⌋ : ℝ) + 1 := by
    calc ((Finset.Icc (0:ℤ) ⌊(b - a)/s⌋).card : ℝ)
        ≤ ((⌊(b - a)/s⌋.toNat + 1 : ℕ) : ℝ) := by exact_mod_cast hle
      _ = (⌊(b - a)/s⌋ : ℝ) + 1 := by rw [Nat.cast_add, Nat.cast_one, hNcast]
  calc ((t.card : ℕ) : ℝ) = ((t.image (fun x => ⌊(f x - a)/s⌋)).card : ℝ) := hcard
    _ ≤ (⌊(b - a)/s⌋ : ℝ) + 1 := by
        have h1 := Finset.card_le_card hsub
        calc ((t.image (fun x => ⌊(f x - a)/s⌋)).card : ℝ)
            ≤ ((Finset.Icc (0:ℤ) ⌊(b - a)/s⌋).card : ℝ) := by exact_mod_cast h1
          _ ≤ _ := h2
    _ ≤ (b - a)/s + 1 := by linarith [Int.floor_le ((b - a)/s)]

/-! ## The pointwise bound on the boundary-layer symbols -/

section SymbolBound

variable {K : ℕ} (lam : Fin K → ℝ)

/-- `(2:ℝ)^(-(3:ℤ)) = 1/8`, so a `2^{-3}`-separated family is `1/8`-separated. -/
private lemma eighth_le_abs (hsep : ∀ k l : Fin K, k ≠ l → (2 : ℝ) ^ (-(3 : ℤ)) ≤ |lam k - lam l|)
    (k l : Fin K) (hkl : k ≠ l) : (1 / 8 : ℝ) ≤ |lam k - lam l| := by
  have h : (2 : ℝ) ^ (-(3 : ℤ)) = (1 / 8 : ℝ) := by norm_num [zpow_neg]
  rw [← h]; exact hsep k l hkl

/-- The dyadic scale is a power of `1/2`. -/
private lemma hj_eq_pow (j : ℕ) : hj j = ((1 : ℝ) / 2) ^ (j + 1) := by
  induction j with
  | zero =>
      rw [hj, show (-(((0:ℕ)):ℝ) - 1) = (-1:ℝ) by norm_num, Real.rpow_neg_one]
      norm_num
  | succ k ih => rw [hj_half, ih]; ring

private lemma hj_four : hj 4 = 1 / 32 := by
  rw [hj_eq_pow]; norm_num

/-- The number of frequencies lying in the dyadic annulus of level `j` around `θ`. -/
private def cntAnn (j : ℕ) (θ : ℝ) : ℕ :=
  (Finset.univ.filter (fun k : Fin K => hj j / 2 < |θ - lam k| ∧ |θ - lam k| ≤ hj j)).card

/-- At most `16 h_j + 1` frequencies lie within `h_j` of `θ`. -/
private lemma cntNear_le (hsep : ∀ k l : Fin K, k ≠ l → (2 : ℝ) ^ (-(3 : ℤ)) ≤ |lam k - lam l|)
    (j : ℕ) (θ : ℝ) :
    (((Finset.univ.filter (fun k : Fin K => |θ - lam k| ≤ hj j)).card : ℕ) : ℝ)
      ≤ 16 * hj j + 1 := by
  have h := card_le_of_pairwise_separated
    (t := Finset.univ.filter (fun k : Fin K => |θ - lam k| ≤ hj j))
    (a := θ - hj j) (b := θ + hj j) lam (by norm_num : (0:ℝ) < 1/8)
    (fun x _ y _ hxy => eighth_le_abs lam hsep x y hxy)
    (by linarith [hj_pos j])
    (fun x hx => by
      rw [Finset.mem_filter] at hx
      have hx' : -hj j ≤ θ - lam x ∧ θ - lam x ≤ hj j := abs_le.mp hx.2
      linarith [hx'.1])
    (fun x hx => by
      rw [Finset.mem_filter] at hx
      have hx' : -hj j ≤ θ - lam x ∧ θ - lam x ≤ hj j := abs_le.mp hx.2
      linarith [hx'.2])
  calc (((Finset.univ.filter (fun k : Fin K => |θ - lam k| ≤ hj j)).card : ℕ) : ℝ)
      ≤ ((θ + hj j) - (θ - hj j)) / (1/8) + 1 := h
    _ = 16 * hj j + 1 := by ring

/-- At most `16 h_j + 1` frequencies lie in the annulus of level `j` around `θ`. -/
private lemma cntAnn_le (hsep : ∀ k l : Fin K, k ≠ l → (2 : ℝ) ^ (-(3 : ℤ)) ≤ |lam k - lam l|)
    (j : ℕ) (θ : ℝ) : ((cntAnn lam j θ : ℕ) : ℝ) ≤ 16 * hj j + 1 := by
  rw [cntAnn]
  refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) (cntNear_le lam hsep j θ)
  intro k hk
  rw [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, hk.2.2⟩

/-- For `j ≥ 4` the annulus of level `j` contains at most one frequency. -/
private lemma cntAnn_le_one (hsep : ∀ k l : Fin K, k ≠ l → (2 : ℝ) ^ (-(3 : ℤ)) ≤ |lam k - lam l|)
    {j : ℕ} (hj4 : 4 ≤ j) (θ : ℝ) : cntAnn lam j θ ≤ 1 := by
  have hle := cntAnn_le lam hsep j θ
  have h4 : hj j ≤ 1 / 32 := le_trans (hj_mono hj4) (le_of_eq hj_four)
  have h32 : ((cntAnn lam j θ : ℕ) : ℝ) ≤ 3 / 2 := by linarith
  by_contra hcon
  have h2 : (2 : ℝ) ≤ (cntAnn lam j θ : ℕ) := by
    exact_mod_cast (by omega : 2 ≤ cntAnn lam j θ)
  linarith

/-- At most one dyadic level `j ≥ 4` carries a nonzero annulus count. -/
private lemma cntAnn_large_unique
    (hsep : ∀ k l : Fin K, k ≠ l → (2 : ℝ) ^ (-(3 : ℤ)) ≤ |lam k - lam l|)
    {j j' : ℕ} (hj4 : 4 ≤ j) (hj4' : 4 ≤ j') (θ : ℝ)
    (h : cntAnn lam j θ ≠ 0) (h' : cntAnn lam j' θ ≠ 0) : j = j' := by
  by_contra hne
  obtain ⟨k, hk⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
  obtain ⟨k', hk'⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h')
  rw [Finset.mem_filter] at hk hk'
  obtain ⟨-, hk1, hk2⟩ := hk
  obtain ⟨-, hk1', hk2'⟩ := hk'
  have htri : |lam k - lam k'| ≤ |θ - lam k| + |θ - lam k'| := by
    calc |lam k - lam k'| = |(lam k - θ) + (θ - lam k')| := by congr 1; ring
      _ ≤ |lam k - θ| + |θ - lam k'| := abs_add_le _ _
      _ = |θ - lam k| + |θ - lam k'| := by rw [abs_sub_comm]
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hmono : hj j' ≤ hj j / 2 :=
      le_trans (hj_mono (by omega : j + 1 ≤ j')) (le_of_eq (hj_half j))
    have h4j : hj j ≤ 1 / 32 := le_trans (hj_mono hj4) (le_of_eq hj_four)
    have h5j : hj j' ≤ 1 / 64 := by linarith
    have hsum : hj j + hj j' ≤ 3 / 64 := by linarith
    rcases eq_or_ne k k' with hkk | hkk
    · have heq : |θ - lam k'| = |θ - lam k| := by rw [hkk]
      rw [heq] at hk2'
      linarith
    · have hge := eighth_le_abs lam hsep k k' hkk
      linarith
  · have hmono : hj j ≤ hj j' / 2 :=
      le_trans (hj_mono (by omega : j' + 1 ≤ j)) (le_of_eq (hj_half j'))
    have h4j : hj j' ≤ 1 / 32 := le_trans (hj_mono hj4') (le_of_eq hj_four)
    have h5j : hj j ≤ 1 / 64 := by linarith
    have hsum : hj j + hj j' ≤ 3 / 64 := by linarith
    rcases eq_or_ne k k' with hkk | hkk
    · have heq : |θ - lam k'| = |θ - lam k| := by rw [hkk]
      rw [heq] at hk2'
      linarith
    · have hge := eighth_le_abs lam hsep k k' hkk
      linarith

/-- Every boundary-layer symbol is bounded by the (annulus) frequency count at its scale. -/
private lemma symb_norm_le_cntAnn {φ : ℝ → ℝ} (h1 : ∀ x : ℝ, |x| ≤ 1 / 2 → φ x = 1)
    (h0 : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (hbdd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1)
    (j : ℕ) (θ : ℝ) : ‖symb lam φ j θ‖ ≤ ((cntAnn lam j θ : ℕ) : ℝ) := by
  have hterm : ∀ k : Fin K,
      ‖(Set.Ioc (lam k - hj j) (lam k + hj j)).indicator
          (fun θ => ((1 - φ ((θ - lam k) / hj j)) : ℂ)) θ‖
        ≤ (if hj j / 2 < |θ - lam k| ∧ |θ - lam k| ≤ hj j then (1 : ℝ) else 0) := by
    intro k
    by_cases hann : hj j / 2 < |θ - lam k| ∧ |θ - lam k| ≤ hj j
    · rw [if_pos hann]
      rw [Set.indicator_apply]
      by_cases hmem : θ ∈ Set.Ioc (lam k - hj j) (lam k + hj j)
      · rw [if_pos hmem]
        rw [show ((1 - φ ((θ - lam k) / hj j)) : ℂ)
              = (((1 - φ ((θ - lam k) / hj j)) : ℝ) : ℂ) from by norm_num,
            norm_ofReal, abs_le]
        have hy := hbdd ((θ - lam k) / hj j)
        exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
      · rw [if_neg hmem]; simp
    · rw [if_neg hann]
      rw [Set.indicator_apply]
      by_cases hmem : θ ∈ Set.Ioc (lam k - hj j) (lam k + hj j)
      · rw [if_pos hmem]
        have hle : |θ - lam k| ≤ hj j := by
          rw [Set.mem_Ioc] at hmem
          rw [abs_le]; constructor <;> linarith
        have hhalf : |(θ - lam k) / hj j| ≤ 1 / 2 := by
          have hnot : ¬ (hj j / 2 < |θ - lam k|) := fun hc => hann ⟨hc, hle⟩
          rw [abs_div, abs_of_pos (hj_pos j), div_le_iff₀ (hj_pos j)]
          linarith [not_lt.mp hnot]
        have hphi : φ ((θ - lam k) / hj j) = 1 := h1 _ hhalf
        rw [hphi]; norm_num
      · rw [if_neg hmem]; simp
  calc ‖symb lam φ j θ‖
      = ‖∑ k : Fin K, (Set.Ioc (lam k - hj j) (lam k + hj j)).indicator
          (fun θ => ((1 - φ ((θ - lam k) / hj j)) : ℂ)) θ‖ := rfl
    _ ≤ ∑ k : Fin K, ‖(Set.Ioc (lam k - hj j) (lam k + hj j)).indicator
          (fun θ => ((1 - φ ((θ - lam k) / hj j)) : ℂ)) θ‖ := norm_sum_le _ _
    _ ≤ ∑ k : Fin K, (if hj j / 2 < |θ - lam k| ∧ |θ - lam k| ≤ hj j then (1 : ℝ) else 0) :=
        Finset.sum_le_sum (fun k _ => hterm k)
    _ = ((cntAnn lam j θ : ℕ) : ℝ) := by
        rw [cntAnn, Finset.card_filter]
        push_cast
        rfl

/-- Uniform bound: every boundary-layer symbol is bounded by `9`. -/
private lemma symb_norm_le_nine
    (hsep : ∀ k l : Fin K, k ≠ l → (2 : ℝ) ^ (-(3 : ℤ)) ≤ |lam k - lam l|)
    {φ : ℝ → ℝ} (h1 : ∀ x : ℝ, |x| ≤ 1 / 2 → φ x = 1)
    (h0 : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (hbdd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1)
    (j : ℕ) (θ : ℝ) : ‖symb lam φ j θ‖ ≤ 9 := by
  refine le_trans (symb_norm_le_cntAnn lam h1 h0 hbdd j θ) ?_
  have h := cntAnn_le lam hsep j θ
  have := hj_le j
  linarith

/-- Numerical value of the small-scale contribution. -/
private lemma sum_range_four : ∑ j ∈ Finset.range 4, (16 * hj j + 1) ^ 2 = 119 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  rw [hj_eq_pow 0, hj_eq_pow 1, hj_eq_pow 2, hj_eq_pow 3]
  norm_num

/-- **Pointwise square-sum bound for the boundary-layer symbols**, `1/8`-separated case. -/
private lemma sum_symb_sq_le
    (hsep : ∀ k l : Fin K, k ≠ l → (2 : ℝ) ^ (-(3 : ℤ)) ≤ |lam k - lam l|)
    {φ : ℝ → ℝ} (h1 : ∀ x : ℝ, |x| ≤ 1 / 2 → φ x = 1)
    (h0 : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (hbdd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1)
    (θ : ℝ) (F : Finset ℕ) :
    ∑ j ∈ F, ‖symb lam φ j θ‖ ^ 2 ≤ 128 := by
  have hterm : ∀ j ∈ F, ‖symb lam φ j θ‖ ^ 2 ≤ ((cntAnn lam j θ : ℕ) : ℝ) ^ 2 := by
    intro j _
    have hb := symb_norm_le_cntAnn lam h1 h0 hbdd j θ
    nlinarith [norm_nonneg (symb lam φ j θ), (by positivity : (0:ℝ) ≤ ((cntAnn lam j θ : ℕ) : ℝ))]
  rw [← Finset.sum_filter_add_sum_filter_not F (fun j => 4 ≤ j)
    (fun j => ‖symb lam φ j θ‖ ^ 2)]
  have hsmall : ∑ j ∈ F.filter (fun j => ¬ 4 ≤ j), ‖symb lam φ j θ‖ ^ 2 ≤ 119 := by
    calc ∑ j ∈ F.filter (fun j => ¬ 4 ≤ j), ‖symb lam φ j θ‖ ^ 2
        ≤ ∑ j ∈ F.filter (fun j => ¬ 4 ≤ j), ((cntAnn lam j θ : ℕ) : ℝ) ^ 2 :=
          Finset.sum_le_sum (fun j hj => hterm j (Finset.mem_of_mem_filter j hj))
      _ ≤ ∑ j ∈ F.filter (fun j => ¬ 4 ≤ j), (16 * hj j + 1) ^ 2 :=
          Finset.sum_le_sum (fun j _ =>
            pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ ((cntAnn lam j θ : ℕ) : ℝ))
              (cntAnn_le lam hsep j θ) 2)
      _ ≤ ∑ j ∈ Finset.range 4, (16 * hj j + 1) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun j hj => by
              rw [Finset.mem_filter] at hj
              rw [Finset.mem_range]
              omega)
            (fun j _ _ => by positivity)
      _ = 119 := sum_range_four
  have hlarge : ∑ j ∈ F.filter (fun j => 4 ≤ j), ‖symb lam φ j θ‖ ^ 2 ≤ 1 := by
    refine le_trans (Finset.sum_le_sum (fun j hj => hterm j (Finset.mem_of_mem_filter j hj))) ?_
    by_cases hex : ∃ j ∈ F.filter (fun j => 4 ≤ j), cntAnn lam j θ ≠ 0
    · obtain ⟨j0, hj0F, hj0⟩ := hex
      rw [Finset.sum_eq_single j0 ?_ ?_]
      · have h1' : ((cntAnn lam j0 θ : ℕ) : ℝ) ≤ 1 := by
          have := cntAnn_le_one lam hsep (Finset.mem_filter.mp hj0F).2 θ
          exact_mod_cast this
        nlinarith [(by positivity : (0:ℝ) ≤ ((cntAnn lam j0 θ : ℕ) : ℝ))]
      · intro b hb hbne
        rw [Finset.mem_filter] at hb
        by_contra hb'
        have hb'' : cntAnn lam b θ ≠ 0 := fun hc => hb' (by rw [hc]; norm_num)
        exact hbne (cntAnn_large_unique lam hsep hb.2 (Finset.mem_filter.mp hj0F).2 θ hb'' hj0)
      · intro hnot
        exact absurd hj0F hnot
    · have hz0 : ∑ j ∈ F.filter (fun j => 4 ≤ j), ((cntAnn lam j θ : ℕ) : ℝ) ^ 2 = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hz : cntAnn lam j θ = 0 := by
          by_contra hc
          exact hex ⟨j, hj, hc⟩
        rw [hz]
        norm_num
      rw [hz0]
      norm_num
  linarith

end SymbolBound

/-! ## The rescaled symbol and the identification of the bracket -/

section Rescale

variable {K : ℕ} (lam : Fin K → ℝ)

/-- The pointwise square-sum bound for the symbols, in `ℝ≥0∞` form. -/
private lemma symb_tsum_sq_le
    (hsep : ∀ k l : Fin K, k ≠ l → (2 : ℝ) ^ (-(3 : ℤ)) ≤ |lam k - lam l|)
    {φ : ℝ → ℝ} (h1 : ∀ x : ℝ, |x| ≤ 1 / 2 → φ x = 1)
    (h0 : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (hbdd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1)
    (θ : ℝ) : ∑' j : ℕ, ‖symb lam φ j θ‖ₑ ^ (2:ℝ) ≤ ENNReal.ofReal 128 := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le (fun F => ?_)
  calc ∑ j ∈ F, ‖symb lam φ j θ‖ₑ ^ (2:ℝ)
      = ∑ j ∈ F, ENNReal.ofReal (‖symb lam φ j θ‖ ^ 2) :=
        Finset.sum_congr rfl (fun j _ => enorm_pow_two_eq _)
    _ = ENNReal.ofReal (∑ j ∈ F, ‖symb lam φ j θ‖ ^ 2) :=
        (ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)).symm
    _ ≤ ENNReal.ofReal 128 :=
        ENNReal.ofReal_le_ofReal (sum_symb_sq_le lam hsep h1 h0 hbdd θ F)

/-- The rescaled symbol whose band kernel is `1/9` times the boundary-layer bracket. -/
private def m2 (φ : ℝ → ℝ) (j : ℕ) : ℝ → ℂ :=
  fun θ => (((18 * Real.pi)⁻¹ : ℝ) : ℂ) * symb lam φ j ((2 * Real.pi)⁻¹ * θ)

private lemma measurable_m2 (φ : ℝ → ℝ) (hφ : Measurable φ) (j : ℕ) : Measurable (m2 lam φ j) := by
  unfold m2
  exact measurable_const.mul ((measurable_symb lam hφ j).comp (by fun_prop))

private lemma hasCompactSupport_m2 (φ : ℝ → ℝ) (j : ℕ) : HasCompactSupport (m2 lam φ j) := by
  have hne : (2 * Real.pi)⁻¹ ≠ 0 := by positivity
  have h1 : HasCompactSupport (fun ξ : ℝ => symb lam φ j ((2 * Real.pi)⁻¹ * ξ)) :=
    hasCompactSupport_comp_mul (symb lam φ j) (hasCompactSupport_symb lam φ j) _ hne
  have h2 : HasCompactSupport
      (fun ξ : ℝ => (((18 * Real.pi)⁻¹ : ℝ) : ℂ) *
        symb lam φ j ((2 * Real.pi)⁻¹ * ξ)) := h1.mul_left
  exact h2

private lemma norm_m2_le_one
    (hsep : ∀ k l : Fin K, k ≠ l → (2 : ℝ) ^ (-(3 : ℤ)) ≤ |lam k - lam l|)
    {φ : ℝ → ℝ} (h1 : ∀ x : ℝ, |x| ≤ 1 / 2 → φ x = 1)
    (h0 : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (hbdd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1)
    (j : ℕ) (θ : ℝ) : ‖m2 lam φ j θ‖ ≤ 1 := by
  have hb := symb_norm_le_nine lam hsep h1 h0 hbdd j ((2 * Real.pi)⁻¹ * θ)
  unfold m2
  rw [norm_mul, norm_ofReal, abs_of_pos (by positivity : (0:ℝ) < (18 * Real.pi)⁻¹)]
  have hpi : (3:ℝ) < Real.pi := Real.pi_gt_three
  have : (18 * Real.pi)⁻¹ * 9 ≤ 1 := by
    rw [inv_mul_le_iff₀ (by positivity : (0:ℝ) < 18 * Real.pi)]
    linarith
  nlinarith [norm_nonneg (symb lam φ j ((2 * Real.pi)⁻¹ * θ))]

private lemma m2_tsum_sq_le
    (hsep : ∀ k l : Fin K, k ≠ l → (2 : ℝ) ^ (-(3 : ℤ)) ≤ |lam k - lam l|)
    {φ : ℝ → ℝ} (h1 : ∀ x : ℝ, |x| ≤ 1 / 2 → φ x = 1)
    (h0 : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (hbdd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1)
    (θ : ℝ) :
    ∑' j : ℕ, ‖m2 lam φ j θ‖ₑ ^ (2:ℝ) ≤ ENNReal.ofReal (128 / (18 * Real.pi) ^ 2) := by
  have hc : (0:ℝ) ≤ ((18 * Real.pi)⁻¹) ^ 2 := by positivity
  calc ∑' j : ℕ, ‖m2 lam φ j θ‖ₑ ^ (2:ℝ)
      = ∑' j : ℕ, ENNReal.ofReal (((18 * Real.pi)⁻¹) ^ 2) *
          ‖symb lam φ j ((2 * Real.pi)⁻¹ * θ)‖ₑ ^ (2:ℝ) := by
        apply tsum_congr; intro j
        unfold m2
        rw [enorm_const_mul_sq]
    _ = ENNReal.ofReal (((18 * Real.pi)⁻¹) ^ 2) *
          ∑' j : ℕ, ‖symb lam φ j ((2 * Real.pi)⁻¹ * θ)‖ₑ ^ (2:ℝ) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (((18 * Real.pi)⁻¹) ^ 2) * ENNReal.ofReal 128 :=
        mul_le_mul_right (symb_tsum_sq_le lam hsep h1 h0 hbdd _) _
    _ = ENNReal.ofReal (128 / (18 * Real.pi) ^ 2) := by
        rw [← ENNReal.ofReal_mul hc]
        congr 1
        field_simp

end Rescale

/-! ## Identifying the target's bracket with the band kernel -/

section BracketId

variable {K : ℕ} (lam : Fin K → ℝ)

private lemma exp_scale (t x : ℝ) :
    Complex.exp (-(Complex.I * (((2 * Real.pi * t : ℝ)) : ℂ) * ((((2 * Real.pi)⁻¹ * x : ℝ)) : ℂ)))
      = Complex.exp (-(Complex.I * ((t : ℝ) : ℂ) * (x : ℂ))) := by
  congr 1
  push_cast
  field_simp

/-- The boundary-layer bracket at scale `j` and time `2π t` is `9` times the band kernel of the
rescaled symbol `m2`. -/
private lemma bst_twopi_eq {φ : ℝ → ℝ} (hφ : Measurable φ) (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1)
    (j : ℕ) (t : ℝ) :
    bst lam φ j (2 * Real.pi * t) = 9 * bandKernel (m2 lam φ j) t := by
  have hkern : bst lam φ j (2 * Real.pi * t) = bandKernel (symb lam φ j) (2 * Real.pi * t) :=
    bst_eq_kern lam hφ hbd j (2 * Real.pi * t)
  -- the substitution `θ = (2π)⁻¹ x` in the band kernel of the symbol
  have hsub := Measure.integral_comp_mul_left
    (g := fun x : ℝ => symb lam φ j x *
      Complex.exp (-(Complex.I * (((2 * Real.pi * t : ℝ)) : ℂ) * (x : ℂ))))
    ((2 * Real.pi)⁻¹)
  rw [show (((2 * Real.pi)⁻¹ : ℝ))⁻¹ = 2 * Real.pi by field_simp] at hsub
  rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), Complex.real_smul] at hsub
  have hL : (∫ x : ℝ, symb lam φ j ((2 * Real.pi)⁻¹ * x) *
        Complex.exp (-(Complex.I * (((2 * Real.pi * t : ℝ)) : ℂ) *
          ((((2 * Real.pi)⁻¹ * x : ℝ)) : ℂ))))
      = ∫ x : ℝ, symb lam φ j ((2 * Real.pi)⁻¹ * x) *
          Complex.exp (-(Complex.I * ((t : ℝ) : ℂ) * (x : ℂ))) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [exp_scale t x]
  rw [hL] at hsub
  -- `hsub : ∫ x, symb((2π)⁻¹x) e^{-i t x} = (2π) * bandKernel symb (2π t)`
  have hm2val : bandKernel (m2 lam φ j) t
      = (((18 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ x : ℝ, symb lam φ j ((2 * Real.pi)⁻¹ * x) *
            Complex.exp (-(Complex.I * ((t : ℝ) : ℂ) * (x : ℂ))) := by
    unfold bandKernel m2
    rw [show (fun x : ℝ => (((18 * Real.pi)⁻¹ : ℝ) : ℂ) * symb lam φ j ((2 * Real.pi)⁻¹ * x) *
          Complex.exp (-(Complex.I * ((t : ℝ) : ℂ) * (x : ℂ))))
        = fun x : ℝ => (((18 * Real.pi)⁻¹ : ℝ) : ℂ) *
            (symb lam φ j ((2 * Real.pi)⁻¹ * x) *
              Complex.exp (-(Complex.I * ((t : ℝ) : ℂ) * (x : ℂ)))) from by
      funext x; ring]
    exact integral_const_mul _ _
  rw [hkern, hm2val]
  change (∫ y : ℝ, symb lam φ j y *
      Complex.exp (-(Complex.I * (((2 * Real.pi * t : ℝ)) : ℂ) * (y : ℂ))))
    = 9 * ((((18 * Real.pi)⁻¹ : ℝ) : ℂ) *
        ∫ x : ℝ, symb lam φ j ((2 * Real.pi)⁻¹ * x) *
          Complex.exp (-(Complex.I * ((t : ℝ) : ℂ) * (x : ℂ))))
  rw [hsub]
  set B := ∫ y : ℝ, symb lam φ j y *
      Complex.exp (-(Complex.I * (((2 * Real.pi * t : ℝ)) : ℂ) * (y : ℂ))) with hB
  have hconst : (9 : ℂ) * ((((18 * Real.pi)⁻¹ : ℝ) : ℂ) *
      ((((2 : ℝ) * Real.pi : ℝ) : ℂ) * B)) = B := by
    have hcoef : (9:ℂ) * ((((18 * Real.pi)⁻¹ : ℝ) : ℂ) *
        ((((2 : ℝ) * Real.pi : ℝ)) : ℂ)) = 1 := by
      push_cast
      field_simp
      ring
    calc (9 : ℂ) * ((((18 * Real.pi)⁻¹ : ℝ) : ℂ) * ((((2 : ℝ) * Real.pi : ℝ) : ℂ) * B))
        = ((9:ℂ) * ((((18 * Real.pi)⁻¹ : ℝ) : ℂ) * ((((2 : ℝ) * Real.pi : ℝ) : ℂ)))) * B := by
          ring
      _ = 1 * B := by rw [hcoef]
      _ = B := one_mul B
  exact hconst.symm

end BracketId

/-! ## The `L²` square-function bound for a family of band operators -/

section BandFamily

set_option maxHeartbeats 1600000 in
/-- **`L²` square-function bound for a countable family of band operators** (`L¹ ∩ L²` case):
if the squared moduli of the symbols are pointwise summable with sum at most `A²`, then the
square function of the corresponding band operators is bounded by `A² (2π)²` in `L²`. -/
private theorem bandFamily_square_bound_L1L2 {ι : Type*} [Countable ι]
    (m : ι → ℝ → ℂ) (hm : ∀ i, Measurable (m i)) (hbd : ∀ i θ, ‖m i θ‖ ≤ 1)
    (hsupp : ∀ i, HasCompactSupport (m i)) (A : ℝ)
    (hA : ∀ θ, ∑' i, ‖m i θ‖ₑ ^ (2:ℝ) ≤ ENNReal.ofReal (A ^ 2))
    (f : ℝ → ℂ) (hf1 : MemLp f 1 (volume : Measure ℝ)) (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    ∫⁻ x, ∑' i, ‖∫ y, f y * bandKernel (m i) (x - y)‖ₑ ^ (2:ℝ)
      ≤ ENNReal.ofReal (A ^ 2 * (2 * Real.pi) ^ 2) * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
  have hm1 : ∀ i, MemLp (m i) 1 (volume : Measure ℝ) := fun i =>
    (hsupp i).memLp_of_bound (hm i).aestronglyMeasurable 1 (Filter.Eventually.of_forall (hbd i))
  have hm2 : ∀ i, MemLp (m i) 2 (volume : Measure ℝ) := fun i =>
    (hsupp i).memLp_of_bound (hm i).aestronglyMeasurable 1 (Filter.Eventually.of_forall (hbd i))
  have hmtop : ∀ i, MemLp (m i) ⊤ (volume : Measure ℝ) := fun i =>
    (hsupp i).memLp_of_bound (hm i).aestronglyMeasurable 1 (Filter.Eventually.of_forall (hbd i))
  have hsym : ∀ i,
      MemLp (fun ξ : ℝ => m i (-(2*Real.pi)*ξ) * 𝓕 f ξ) 1 (volume : Measure ℝ) ∧
      MemLp (fun ξ : ℝ => m i (-(2*Real.pi)*ξ) * 𝓕 f ξ) 2 (volume : Measure ℝ) := fun i =>
    symbol_memLp (m i) f (hm i) (hbd i) (hsupp i) hf1
  have hpt : ∀ i (x : ℝ), (∫ y, f y * bandKernel (m i) (x - y))
      = twoPiC * 𝓕⁻ (fun ξ => m i (-(2*Real.pi)*ξ) * 𝓕 f ξ) x := fun i x =>
    bandOp_pointwise (m i) f (hm i) (hm1 i) (hm2 i) (hmtop i) hf1 hf2 x
  have hper : ∀ i, ∫⁻ x, ‖∫ y, f y * bandKernel (m i) (x - y)‖ₑ ^ (2:ℝ)
      = ENNReal.ofReal ((2*Real.pi)^2) * ∫⁻ ξ, ‖m i (-(2*Real.pi)*ξ) * 𝓕 f ξ‖ₑ ^ (2:ℝ) := by
    intro i
    rw [show (∫⁻ x, ‖∫ y, f y * bandKernel (m i) (x - y)‖ₑ ^ (2:ℝ))
        = ∫⁻ x, ‖twoPiC * 𝓕⁻ (fun ξ => m i (-(2*Real.pi)*ξ) * 𝓕 f ξ) x‖ₑ ^ (2:ℝ) from
      lintegral_congr (fun x => by rw [hpt i x])]
    rw [lintegral_enorm_sq_const_mul]
    rw [show ‖twoPiC‖ ^ 2 = (2*Real.pi)^2 by
      rw [twoPiC, norm_ofReal, abs_of_pos (by positivity)]]
    rw [lintegral_enorm_fourierInv_eq (hsym i).1 (hsym i).2]
  have hmeas1 : ∀ i, AEMeasurable
      (fun x : ℝ => ‖∫ y, f y * bandKernel (m i) (x - y)‖ₑ ^ (2:ℝ)) volume := by
    intro i
    have hint : Integrable (fun ξ : ℝ => m i (-(2*Real.pi)*ξ) * 𝓕 f ξ) volume :=
      memLp_one_iff_integrable.mp (hsym i).1
    have hcont : Continuous (fun x : ℝ => 𝓕⁻ (fun ξ : ℝ => m i (-(2*Real.pi)*ξ) * 𝓕 f ξ) x) :=
      continuous_fourierInv_of_integrable _ hint
    have hcf : Continuous (fun x : ℝ => ‖∫ y, f y * bandKernel (m i) (x - y)‖ₑ ^ (2:ℝ)) := by
      rw [show (fun x : ℝ => ‖∫ y, f y * bandKernel (m i) (x - y)‖ₑ ^ (2:ℝ))
          = fun x => ‖twoPiC * 𝓕⁻ (fun ξ : ℝ => m i (-(2*Real.pi)*ξ) * 𝓕 f ξ) x‖ₑ ^ (2:ℝ)
          from funext (fun x => by rw [hpt i x])]
      exact continuous_enorm_pow_two_comp (continuous_const.mul hcont)
    exact hcf.aemeasurable
  have hmeas2 : ∀ i, AEMeasurable
      (fun ξ : ℝ => ‖m i (-(2*Real.pi)*ξ) * 𝓕 f ξ‖ₑ ^ (2:ℝ)) volume := by
    intro i
    have h1 : Measurable (fun ξ : ℝ => m i (-(2*Real.pi)*ξ)) :=
      (hm i).comp (by fun_prop)
    have h2 : Measurable (𝓕 f) := measurable_fourier hf1
    exact ((h1.mul h2).enorm.pow_const (2:ℝ)).aemeasurable
  calc ∫⁻ x, ∑' i, ‖∫ y, f y * bandKernel (m i) (x - y)‖ₑ ^ (2:ℝ)
      = ∑' i, ∫⁻ x, ‖∫ y, f y * bandKernel (m i) (x - y)‖ₑ ^ (2:ℝ) := lintegral_tsum hmeas1
    _ = ∑' i, ENNReal.ofReal ((2*Real.pi)^2) *
          ∫⁻ ξ, ‖m i (-(2*Real.pi)*ξ) * 𝓕 f ξ‖ₑ ^ (2:ℝ) := tsum_congr hper
    _ = ENNReal.ofReal ((2*Real.pi)^2) *
          ∑' i, ∫⁻ ξ, ‖m i (-(2*Real.pi)*ξ) * 𝓕 f ξ‖ₑ ^ (2:ℝ) := ENNReal.tsum_mul_left
    _ = ENNReal.ofReal ((2*Real.pi)^2) *
          ∫⁻ ξ, ∑' i, ‖m i (-(2*Real.pi)*ξ) * 𝓕 f ξ‖ₑ ^ (2:ℝ) := by
        rw [lintegral_tsum hmeas2]
    _ = ENNReal.ofReal ((2*Real.pi)^2) *
          ∫⁻ ξ, (∑' i, ‖m i (-(2*Real.pi)*ξ)‖ₑ ^ (2:ℝ)) * ‖𝓕 f ξ‖ₑ ^ (2:ℝ) := by
        congr 1
        apply lintegral_congr; intro ξ
        rw [← ENNReal.tsum_mul_right]
        apply tsum_congr; intro i
        rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
    _ ≤ ENNReal.ofReal ((2*Real.pi)^2) *
          ∫⁻ ξ, ENNReal.ofReal (A ^ 2) * ‖𝓕 f ξ‖ₑ ^ (2:ℝ) := by
        refine mul_le_mul_right ?_ _
        apply lintegral_mono; intro ξ
        exact mul_le_mul_left (hA (-(2*Real.pi)*ξ)) _
    _ = ENNReal.ofReal ((2*Real.pi)^2) *
          (ENNReal.ofReal (A ^ 2) * ∫⁻ ξ, ‖𝓕 f ξ‖ₑ ^ (2:ℝ)) := by
        congr 1
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal (A ^ 2 * (2*Real.pi)^2) * ∫⁻ ξ, ‖𝓕 f ξ‖ₑ ^ (2:ℝ) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2*Real.pi)^2)]
        congr 1
        ring
    _ = ENNReal.ofReal (A ^ 2 * (2*Real.pi)^2) * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
        rw [lintegral_enorm_fourier_eq (memLp_one_iff_integrable.mp hf1) hf2]

end BandFamily

section BandFamilyL2

set_option maxHeartbeats 1600000 in
/-- **`L²` square-function bound for a countable family of band operators.** -/
private theorem bandFamily_square_bound {ι : Type*} [Countable ι]
    (m : ι → ℝ → ℂ) (hm : ∀ i, Measurable (m i)) (hbd : ∀ i θ, ‖m i θ‖ ≤ 1)
    (hsupp : ∀ i, HasCompactSupport (m i)) (A : ℝ)
    (hA : ∀ θ, ∑' i, ‖m i θ‖ₑ ^ (2:ℝ) ≤ ENNReal.ofReal (A ^ 2))
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume : Measure ℝ)) :
    ∫⁻ x, ∑' i, ‖∫ y, f y * bandKernel (m i) (x - y)‖ₑ ^ (2:ℝ)
      ≤ ENNReal.ofReal (A ^ 2 * (2 * Real.pi) ^ 2) * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
  have hm1 : ∀ i, MemLp (m i) 1 (volume : Measure ℝ) := fun i =>
    (hsupp i).memLp_of_bound (hm i).aestronglyMeasurable 1 (Filter.Eventually.of_forall (hbd i))
  have hm2 : ∀ i, MemLp (m i) 2 (volume : Measure ℝ) := fun i =>
    (hsupp i).memLp_of_bound (hm i).aestronglyMeasurable 1 (Filter.Eventually.of_forall (hbd i))
  have hmtop : ∀ i, MemLp (m i) ⊤ (volume : Measure ℝ) := fun i =>
    (hsupp i).memLp_of_bound (hm i).aestronglyMeasurable 1 (Filter.Eventually.of_forall (hbd i))
  set C₀ : ℝ≥0∞ := ENNReal.ofReal (A ^ 2 * (2 * Real.pi) ^ 2) * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) with hC₀
  let S : ℕ → Set ℝ := fun n => Set.Icc (-(n : ℝ)) (n : ℝ)
  let ind : ℕ → ℝ → ℂ := fun n x => Set.indicator (S n) (fun _ => (1 : ℂ)) x
  let fN : ℕ → ℝ → ℂ := fun n x => f x * ind n x
  have hSmeas : ∀ n, MeasurableSet (S n) := fun n => measurableSet_Icc
  have hSfin : ∀ n, volume (S n) ≠ ⊤ := fun n =>
    (isCompact_Icc.measure_lt_top (μ := volume)).ne
  have hindtop : ∀ n, MemLp (ind n) ⊤ (volume : Measure ℝ) := fun n =>
    memLp_indicator_const ⊤ (hSmeas n) 1 (Or.inr (hSfin n))
  have hind2 : ∀ n, MemLp (ind n) 2 (volume : Measure ℝ) := fun n =>
    memLp_indicator_const 2 (hSmeas n) 1 (Or.inr (hSfin n))
  have hswap : ∀ n, (fun x => ind n x * f x) = fN n := fun n => by
    funext x; simp only [fN, ind]; ring
  have hfN2 : ∀ n, MemLp (fN n) 2 (volume : Measure ℝ) := fun n => (hswap n) ▸ (hindtop n).mul hf
  have hfN1 : ∀ n, MemLp (fN n) 1 (volume : Measure ℝ) := fun n =>
    memLp_one_iff_integrable.mpr ((hswap n) ▸ (hind2 n).integrable_mul hf)
  have hleN : ∀ n, ∫⁻ x, ‖fN n x‖ₑ ^ (2:ℝ) ≤ ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := fun n =>
    lintegral_mono (fun x => by
      rw [enorm_pow_two_eq, enorm_pow_two_eq]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : ‖fN n x‖ ≤ ‖f x‖ := by
        simp only [fN]
        rw [norm_mul]
        calc ‖f x‖ * ‖ind n x‖ ≤ ‖f x‖ * 1 :=
              mul_le_mul_of_nonneg_left (by
                simp only [ind, Set.indicator_apply]; split_ifs <;> simp) (norm_nonneg _)
          _ = ‖f x‖ := mul_one _
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2)
  have hb : ∀ n, ∫⁻ x, ∑' i, ‖∫ y, fN n y * bandKernel (m i) (x - y)‖ₑ ^ (2:ℝ) ≤ C₀ := by
    intro n
    refine le_trans (bandFamily_square_bound_L1L2 m hm hbd hsupp A hA (fN n) (hfN1 n) (hfN2 n)) ?_
    rw [hC₀]
    exact mul_le_mul_right (hleN n) (ENNReal.ofReal (A ^ 2 * (2 * Real.pi) ^ 2))
  have hconv : ∀ (i : ι) (x : ℝ), Tendsto (fun n => ∫ y, fN n y * bandKernel (m i) (x - y)) atTop
      (𝓝 (∫ y, f y * bandKernel (m i) (x - y))) := by
    intro i x
    have hK : MemLp (bandKernel (m i)) 2 (volume : Measure ℝ) :=
      bandKernel_memLp (m i) (hm i) (hbd i) (hsupp i)
    have hKx : MemLp (fun y : ℝ => bandKernel (m i) (x - y)) 2 (volume : Measure ℝ) :=
      hK.comp_measurePreserving (Measure.measurePreserving_sub_left (volume : Measure ℝ) x)
    have hbnd : Integrable (fun y : ℝ => ‖f y * bandKernel (m i) (x - y)‖) volume :=
      (hf.integrable_mul hKx).norm
    refine tendsto_integral_of_dominated_convergence
      (fun y : ℝ => ‖f y * bandKernel (m i) (x - y)‖) ?_ hbnd ?_ ?_
    · intro n
      exact (hfN2 n).aestronglyMeasurable.mul hKx.aestronglyMeasurable
    · intro n
      filter_upwards with y
      have h1 : ‖fN n y‖ ≤ ‖f y‖ := by
        simp only [fN]
        rw [norm_mul]
        calc ‖f y‖ * ‖ind n y‖ ≤ ‖f y‖ * 1 :=
              mul_le_mul_of_nonneg_left (by
                simp only [ind, Set.indicator_apply]; split_ifs <;> simp) (norm_nonneg _)
          _ = ‖f y‖ := mul_one _
      calc ‖fN n y * bandKernel (m i) (x - y)‖
          = ‖fN n y‖ * ‖bandKernel (m i) (x - y)‖ := norm_mul _ _
        _ ≤ ‖f y‖ * ‖bandKernel (m i) (x - y)‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = ‖f y * bandKernel (m i) (x - y)‖ := by rw [norm_mul]
    · filter_upwards with y
      have hev : ∀ᶠ n : ℕ in atTop, fN n y = f y := by
        filter_upwards [Filter.eventually_ge_atTop (Nat.ceil |y|)] with n hn
        have hy : y ∈ S n := by
          rw [Set.mem_Icc]
          exact abs_le.mp (Nat.ceil_le.mp hn)
        simp only [fN, ind, Set.indicator_of_mem hy, mul_one]
      refine (tendsto_const_nhds (x := f y * bandKernel (m i) (x - y))).congr' ?_
      filter_upwards [hev] with n hn
      rw [hn]
  have hliminf : ∀ x : ℝ, (∑' i, ‖∫ y, f y * bandKernel (m i) (x - y)‖ₑ ^ (2:ℝ))
      ≤ Filter.liminf (fun n => ∑' i,
          ‖∫ y, fN n y * bandKernel (m i) (x - y)‖ₑ ^ (2:ℝ)) atTop := by
    intro x
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le (fun s => ?_)
    have htend : Filter.Tendsto
        (fun n => ∑ i ∈ s, ‖∫ y, fN n y * bandKernel (m i) (x - y)‖ₑ ^ (2:ℝ)) atTop
        (𝓝 (∑ i ∈ s, ‖∫ y, f y * bandKernel (m i) (x - y)‖ₑ ^ (2:ℝ))) :=
      tendsto_finsetSum _ (fun i _ =>
        ((ENNReal.continuous_rpow_const (y := 2)).tendsto _).comp ((hconv i x).enorm))
    rw [htend.liminf_eq.symm]
    exact Filter.liminf_le_liminf
      (Filter.Eventually.of_forall (fun n => ENNReal.sum_le_tsum s))
  have hmeas : ∀ n : ℕ, Measurable (fun x : ℝ => ∑' i,
      ‖∫ y, fN n y * bandKernel (m i) (x - y)‖ₑ ^ (2:ℝ)) := by
    intro n
    refine Measurable.ennreal_tsum (fun i => ?_)
    obtain ⟨hs1, _⟩ := symbol_memLp (m i) (fN n) (hm i) (hbd i) (hsupp i) (hfN1 n)
    have hint : Integrable (fun ξ : ℝ => m i (-(2*Real.pi)*ξ) * 𝓕 (fN n) ξ) volume :=
      memLp_one_iff_integrable.mp hs1
    have hcont : Continuous (fun x : ℝ => 𝓕⁻ (fun ξ : ℝ => m i (-(2*Real.pi)*ξ) *
        𝓕 (fN n) ξ) x) := continuous_fourierInv_of_integrable _ hint
    rw [show (fun x : ℝ => ‖∫ y, fN n y * bandKernel (m i) (x - y)‖ₑ ^ (2:ℝ))
        = fun x => ‖twoPiC * 𝓕⁻ (fun ξ : ℝ => m i (-(2*Real.pi)*ξ) * 𝓕 (fN n) ξ) x‖ₑ ^ (2:ℝ)
        from funext (fun x => by
          rw [bandOp_pointwise (m i) (fN n) (hm i) (hm1 i) (hm2 i) (hmtop i) (hfN1 n) (hfN2 n) x])]
    exact (continuous_enorm_pow_two_comp (continuous_const.mul hcont)).measurable
  have hFatou : ∫⁻ x, ∑' i, ‖∫ y, f y * bandKernel (m i) (x - y)‖ₑ ^ (2:ℝ)
      ≤ Filter.liminf (fun n => ∫⁻ x, ∑' i,
          ‖∫ y, fN n y * bandKernel (m i) (x - y)‖ₑ ^ (2:ℝ)) atTop :=
    le_trans (lintegral_mono hliminf) (lintegral_liminf_le hmeas)
  rw [hC₀] at hb ⊢
  exact le_trans hFatou (Filter.liminf_le_of_frequently_le
    (Filter.Frequently.of_forall hb) ⟨0, Filter.Eventually.of_forall (fun n => bot_le)⟩)

end BandFamilyL2

/-! ## The bracket identity and the main theorem -/

section Main

variable {K : ℕ} (lam : Fin K → ℝ)

/-- The target's bracket is the boundary-layer bracket at time `2π t`. -/
private lemma bracket_eq_bst (φ : ℝ → ℝ) (j : ℕ) (t : ℝ) :
    (∑ k : Fin K,
        ∫ θ in (lam k - (2 : ℝ) ^ (-(j : ℝ) - 1))..(lam k + (2 : ℝ) ^ (-(j : ℝ) - 1)),
          ((1 - φ ((θ - lam k) / (2 : ℝ) ^ (-(j : ℝ) - 1))) : ℂ) *
            Complex.exp (-(2 * Real.pi * Complex.I * ((t : ℝ) : ℂ) * (θ : ℂ))))
      = bst lam φ j (2 * Real.pi * t) := by
  simp only [bst, hj, Fexp]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  congr 1
  push_cast
  ring

/-- If `φ` is not a.e. strongly measurable, the bracket vanishes. -/
private lemma bracket_eq_zero_of_not_aesm {φ : ℝ → ℝ}
    (h0 : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (hφ : ¬ AEStronglyMeasurable φ volume)
    (j : ℕ) (t : ℝ) :
    (∑ k : Fin K,
        ∫ θ in (lam k - (2 : ℝ) ^ (-(j : ℝ) - 1))..(lam k + (2 : ℝ) ^ (-(j : ℝ) - 1)),
          ((1 - φ ((θ - lam k) / (2 : ℝ) ^ (-(j : ℝ) - 1))) : ℂ) *
            Complex.exp (-(2 * Real.pi * Complex.I * ((t : ℝ) : ℂ) * (θ : ℂ)))) = 0 := by
  rw [bracket_eq_bst lam φ j t, bst_eq_zero_of_not_aesm lam h0 hφ j (2 * Real.pi * t)]

end Main

/-- **Boundary-layer `L²` square-function bound for `1/8`-separated frequencies**, in the Fourier
convention with `2π` in the exponent. -/
theorem boundary_layer_eighth_separated_real :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (lam : Fin N → ℝ),
      (∀ i j : Fin N, i ≠ j → (2 : ℝ) ^ (-(3 : ℤ)) ≤ |lam i - lam j|) →
      ∀ (φ : ℝ → ℝ), (∀ x : ℝ, |x| ≤ 1 / 2 → φ x = 1) →
        (∀ x : ℝ, 1 ≤ |x| → φ x = 0) → (∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) →
      ∀ (g : ℝ → ℂ), MeasureTheory.MemLp g 2 MeasureTheory.volume →
        MeasureTheory.lintegral MeasureTheory.volume (fun x : ℝ => ∑' j : ℕ,
            ENNReal.ofReal ‖∫ y : ℝ, g y *
              (∑ k : Fin N,
                ∫ θ in (lam k - (2 : ℝ) ^ (-(j : ℝ) - 1))..(lam k + (2 : ℝ) ^ (-(j : ℝ) - 1)),
                  ((1 - φ ((θ - lam k) / (2 : ℝ) ^ (-(j : ℝ) - 1))) : ℂ) *
                    Complex.exp (-(2 * Real.pi * Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ ^ (2:ℝ))
          ≤ ENNReal.ofReal (C ^ 2) * MeasureTheory.lintegral MeasureTheory.volume
              (fun x : ℝ => ENNReal.ofReal ‖g x‖ ^ (2:ℝ)) := by
  refine ⟨12, by norm_num, ?_⟩
  intro N lam hsep φ h1 h0 hbdd g hg
  by_cases hφ : AEStronglyMeasurable φ volume
  · rcases hφ with ⟨φ₀, hφ₀s, hφ₀⟩
    have hφ₀m : Measurable φ₀ := hφ₀s.measurable
    let gp : ℝ → ℝ := fun x =>
      if |x| ≤ 1 / 2 then 1 else if 1 ≤ |x| then 0 else max 0 (min 1 (φ₀ x))
    have hgpm : Measurable gp := by
      refine Measurable.ite ?_ measurable_const (Measurable.ite ?_ measurable_const ?_)
      · exact measurableSet_le measurable_abs measurable_const
      · exact measurableSet_le measurable_const measurable_abs
      · simpa only [max_comm] using ((measurable_const.min hφ₀m).max measurable_const)
    have hgp1 : ∀ x : ℝ, |x| ≤ 1 / 2 → gp x = 1 := by
      intro x hx
      simp only [gp]
      rw [if_pos hx]
    have hgp0 : ∀ x : ℝ, 1 ≤ |x| → gp x = 0 := by
      intro x hx
      simp only [gp]
      rw [if_neg (by linarith : ¬ |x| ≤ 1 / 2), if_pos hx]
    have hgpbdd : ∀ x : ℝ, 0 ≤ gp x ∧ gp x ≤ 1 := by
      intro x
      simp only [gp]
      split_ifs with hc1 hc2
      · exact ⟨by norm_num, by norm_num⟩
      · exact ⟨le_refl 0, by norm_num⟩
      · exact ⟨le_trans (le_max_left 0 _) le_rfl,
          max_le (by norm_num) (min_le_left _ _)⟩
    have hgpae : gp =ᵐ[volume] φ := by
      filter_upwards [hφ₀] with x hx
      simp only [gp]
      by_cases hc1 : |x| ≤ 1 / 2
      · rw [if_pos hc1, h1 x hc1]
      · rw [if_neg hc1]
        by_cases hc2 : 1 ≤ |x|
        · rw [if_pos hc2, h0 x hc2]
        · rw [if_neg hc2, ← hx, min_eq_right (hbdd x).2, max_eq_right (hbdd x).1]
    have hA2 : (Real.sqrt (128 / (18 * Real.pi) ^ 2)) ^ 2 = 128 / (18 * Real.pi) ^ 2 :=
      Real.sq_sqrt (by positivity)
    have hApt : ∀ θ : ℝ,
        ∑' j : ℕ, ‖m2 lam gp j θ‖ₑ ^ (2:ℝ) ≤ ENNReal.ofReal ((Real.sqrt (128 / (18 * Real.pi) ^ 2)) ^ 2) := by
      intro θ
      rw [hA2]
      exact m2_tsum_sq_le lam hsep hgp1 hgp0 hgpbdd θ
    have hmain := bandFamily_square_bound (m2 lam gp)
      (fun j => measurable_m2 lam gp hgpm j)
      (fun j θ => norm_m2_le_one lam hsep hgp1 hgp0 hgpbdd j θ)
      (fun j => hasCompactSupport_m2 lam gp j)
      (Real.sqrt (128 / (18 * Real.pi) ^ 2)) hApt g hg
    have hstep1 : (∫⁻ x, ∑' j : ℕ, ENNReal.ofReal ‖∫ y : ℝ, g y *
            (∑ k : Fin N,
              ∫ θ in (lam k - (2 : ℝ) ^ (-(j : ℝ) - 1))..(lam k + (2 : ℝ) ^ (-(j : ℝ) - 1)),
                ((1 - φ ((θ - lam k) / (2 : ℝ) ^ (-(j : ℝ) - 1))) : ℂ) *
                  Complex.exp (-(2 * Real.pi * Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ ^ (2:ℝ))
        = ∫⁻ x, ∑' j : ℕ, ENNReal.ofReal
            ‖∫ y : ℝ, g y * bst lam φ j (2 * Real.pi * (x - y))‖ ^ (2:ℝ) := by
      apply lintegral_congr; intro x
      apply tsum_congr; intro j
      have hZ : (∫ y : ℝ, g y *
            (∑ k : Fin N,
              ∫ θ in (lam k - (2 : ℝ) ^ (-(j : ℝ) - 1))..(lam k + (2 : ℝ) ^ (-(j : ℝ) - 1)),
                ((1 - φ ((θ - lam k) / (2 : ℝ) ^ (-(j : ℝ) - 1))) : ℂ) *
                  Complex.exp (-(2 * Real.pi * Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))))
          = ∫ y : ℝ, g y * bst lam φ j (2 * Real.pi * (x - y)) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [bracket_eq_bst lam φ j (x - y)]
      rw [hZ]
    have hstep2 : (∫⁻ x, ∑' j : ℕ, ENNReal.ofReal
            ‖∫ y : ℝ, g y * bst lam φ j (2 * Real.pi * (x - y))‖ ^ (2:ℝ))
        = ∫⁻ x, ∑' j : ℕ, ENNReal.ofReal
            ‖∫ y : ℝ, g y * bst lam gp j (2 * Real.pi * (x - y))‖ ^ (2:ℝ) := by
      apply lintegral_congr; intro x
      apply tsum_congr; intro j
      have hZ : (∫ y : ℝ, g y * bst lam φ j (2 * Real.pi * (x - y)))
          = ∫ y : ℝ, g y * bst lam gp j (2 * Real.pi * (x - y)) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [bst_congr_ae lam hgpae.symm j (2 * Real.pi * (x - y))]
      rw [hZ]
    have hstep3 : (∫⁻ x, ∑' j : ℕ, ENNReal.ofReal
            ‖∫ y : ℝ, g y * bst lam gp j (2 * Real.pi * (x - y))‖ ^ (2:ℝ))
        = ∫⁻ x, ∑' j : ℕ, ENNReal.ofReal 81 *
            ‖∫ y : ℝ, g y * bandKernel (m2 lam gp j) (x - y)‖ₑ ^ (2:ℝ) := by
      apply lintegral_congr; intro x
      apply tsum_congr; intro j
      have hZ : (∫ y : ℝ, g y * bst lam gp j (2 * Real.pi * (x - y)))
          = 9 * ∫ y : ℝ, g y * bandKernel (m2 lam gp j) (x - y) := by
        rw [show (fun y : ℝ => g y * bst lam gp j (2 * Real.pi * (x - y)))
            = fun y : ℝ => g y * (9 * bandKernel (m2 lam gp j) (x - y)) from
          funext (fun y => by rw [bst_twopi_eq lam hgpm hgpbdd j (x - y)])]
        rw [show (fun y : ℝ => g y * (9 * bandKernel (m2 lam gp j) (x - y)))
            = fun y : ℝ => 9 * (g y * bandKernel (m2 lam gp j) (x - y)) from
          funext (fun y => by ring)]
        rw [MeasureTheory.integral_const_mul]
      rw [hZ, ← enorm_eq_ofReal_norm,
        show (9 : ℂ) = (((9 : ℝ)) : ℂ) by norm_num, enorm_const_mul_sq,
        show (9 : ℝ) ^ 2 = 81 by norm_num]
    have hstep4 : (∫⁻ x, ∑' j : ℕ, ENNReal.ofReal 81 *
            ‖∫ y : ℝ, g y * bandKernel (m2 lam gp j) (x - y)‖ₑ ^ (2:ℝ))
        = ENNReal.ofReal 81 * ∫⁻ x, ∑' j : ℕ,
            ‖∫ y : ℝ, g y * bandKernel (m2 lam gp j) (x - y)‖ₑ ^ (2:ℝ) := by
      rw [show (fun x : ℝ => ∑' j : ℕ, ENNReal.ofReal 81 *
            ‖∫ y : ℝ, g y * bandKernel (m2 lam gp j) (x - y)‖ₑ ^ (2:ℝ))
          = fun x : ℝ => ENNReal.ofReal 81 * (∑' j : ℕ,
            ‖∫ y : ℝ, g y * bandKernel (m2 lam gp j) (x - y)‖ₑ ^ (2:ℝ)) from
        funext (fun x => ENNReal.tsum_mul_left)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hJ : (∫⁻ x, ENNReal.ofReal ‖g x‖ ^ (2:ℝ)) = ∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) := by
      apply lintegral_congr; intro x
      rw [enorm_eq_ofReal_norm]
    have hconst : (81 : ℝ) * ((Real.sqrt (128 / (18 * Real.pi) ^ 2)) ^ 2 * (2 * Real.pi) ^ 2)
        = 128 := by
      rw [hA2]
      field_simp
      ring
    rw [hstep1, hstep2, hstep3, hstep4, hJ]
    calc ENNReal.ofReal 81 * (∫⁻ x, ∑' j : ℕ,
            ‖∫ y : ℝ, g y * bandKernel (m2 lam gp j) (x - y)‖ₑ ^ (2:ℝ))
        ≤ ENNReal.ofReal 81 * (ENNReal.ofReal ((Real.sqrt (128 / (18 * Real.pi) ^ 2)) ^ 2 *
              (2 * Real.pi) ^ 2) * ∫⁻ x, ‖g x‖ₑ ^ (2:ℝ)) := mul_le_mul_right hmain _
      _ = (ENNReal.ofReal 81 * ENNReal.ofReal ((Real.sqrt (128 / (18 * Real.pi) ^ 2)) ^ 2 *
              (2 * Real.pi) ^ 2)) * ∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) := by rw [mul_assoc]
      _ = ENNReal.ofReal (81 * ((Real.sqrt (128 / (18 * Real.pi) ^ 2)) ^ 2 * (2 * Real.pi) ^ 2)) *
            ∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) := by
          rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 81)]
      _ = ENNReal.ofReal 128 * ∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) := by rw [hconst]
      _ ≤ ENNReal.ofReal ((12 : ℝ) ^ 2) * ∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) := by
          refine mul_le_mul_left ?_ _
          rw [show ((12 : ℝ) ^ 2) = 144 by norm_num]
          exact ENNReal.ofReal_le_ofReal (by norm_num)
  · have hzero : (fun x : ℝ => ∑' j : ℕ, ENNReal.ofReal ‖∫ y : ℝ, g y *
          (∑ k : Fin N,
            ∫ θ in (lam k - (2 : ℝ) ^ (-(j : ℝ) - 1))..(lam k + (2 : ℝ) ^ (-(j : ℝ) - 1)),
              ((1 - φ ((θ - lam k) / (2 : ℝ) ^ (-(j : ℝ) - 1))) : ℂ) *
                Complex.exp (-(2 * Real.pi * Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ ^ (2:ℝ))
        = fun _ => (0 : ℝ≥0∞) := by
      funext x
      have hterm : ∀ j : ℕ, ENNReal.ofReal ‖∫ y : ℝ, g y *
            (∑ k : Fin N,
              ∫ θ in (lam k - (2 : ℝ) ^ (-(j : ℝ) - 1))..(lam k + (2 : ℝ) ^ (-(j : ℝ) - 1)),
                ((1 - φ ((θ - lam k) / (2 : ℝ) ^ (-(j : ℝ) - 1))) : ℂ) *
                  Complex.exp (-(2 * Real.pi * Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ ^ (2:ℝ) = 0 := by
        intro j
        have hZ : (∫ y : ℝ, g y *
            (∑ k : Fin N,
              ∫ θ in (lam k - (2 : ℝ) ^ (-(j : ℝ) - 1))..(lam k + (2 : ℝ) ^ (-(j : ℝ) - 1)),
                ((1 - φ ((θ - lam k) / (2 : ℝ) ^ (-(j : ℝ) - 1))) : ℂ) *
                  Complex.exp (-(2 * Real.pi * Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))) = 0 := by
          rw [show (fun y : ℝ => g y *
              (∑ k : Fin N,
                ∫ θ in (lam k - (2 : ℝ) ^ (-(j : ℝ) - 1))..(lam k + (2 : ℝ) ^ (-(j : ℝ) - 1)),
                  ((1 - φ ((θ - lam k) / (2 : ℝ) ^ (-(j : ℝ) - 1))) : ℂ) *
                    Complex.exp (-(2 * Real.pi * Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))))
              = fun _ : ℝ => (0 : ℂ) from
            funext (fun y => by rw [bracket_eq_zero_of_not_aesm lam h0 hφ j (x - y), mul_zero])]
          exact integral_zero _ _
        rw [hZ, norm_zero, ENNReal.ofReal_zero,
          ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2)]
      have hfun : (fun j : ℕ => ENNReal.ofReal ‖∫ y : ℝ, g y *
            (∑ k : Fin N,
              ∫ θ in (lam k - (2 : ℝ) ^ (-(j : ℝ) - 1))..(lam k + (2 : ℝ) ^ (-(j : ℝ) - 1)),
                ((1 - φ ((θ - lam k) / (2 : ℝ) ^ (-(j : ℝ) - 1))) : ℂ) *
                  Complex.exp (-(2 * Real.pi * Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ ^ (2:ℝ))
          = fun _ : ℕ => (0 : ℝ≥0∞) := funext hterm
      rw [hfun]
      exact tsum_zero
    rw [show (∫⁻ x, ∑' j : ℕ, ENNReal.ofReal ‖∫ y : ℝ, g y *
          (∑ k : Fin N,
            ∫ θ in (lam k - (2 : ℝ) ^ (-(j : ℝ) - 1))..(lam k + (2 : ℝ) ^ (-(j : ℝ) - 1)),
              ((1 - φ ((θ - lam k) / (2 : ℝ) ^ (-(j : ℝ) - 1))) : ℂ) *
                Complex.exp (-(2 * Real.pi * Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ ^ (2:ℝ))
        = ∫⁻ x, (0 : ℝ≥0∞) from lintegral_congr (fun x => congrFun hzero x)]
    rw [lintegral_zero]
    exact bot_le

end
end Commons.Analysis.Fourier
