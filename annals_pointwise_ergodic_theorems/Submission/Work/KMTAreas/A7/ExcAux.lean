/-
# Auxiliary estimates for the exceptional part of the KMT large-scale analysis

This module collects the elementary ingredients of the proof of
`Work.KMTAreas.A7.ExceptionalBound`:

* `lacunary_pow_le`, `nBound`, `floor_a_gt` — the growth of a lacunary sequence, which bounds the
  *number* of scales at which the exceptional part can be nonzero;
* `envConst` and `le_envConst` — the finite envelope of a family of constants, used to turn the
  `ρ`-uniform `ℓ^q` bounds for the Ionescu--Wainger projections (which depend on the height pair
  `(l,k)`) into a *single* constant valid for all the pieces occurring in the exceptional part;
* `exceptionalPart_zero_left/right`, `eq_zero_of_eLpNorm_eq_zero` — the degenerate cases;
* `eLpNorm_piExact_le`, `eLpNorm_piece_le` — the `ℓ^q` bound for a single continuous frequency
  piece, from the projection bound;
* `eLpNorm_exceptionalPart_le` — the bound for a single term of the exceptional family;
* `ExceptionalBound_of_projBound` — the final assembly.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ExcDefs

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier
open Work.KMTContract
open Work.Analysis.EndVar

/-! ## Growth of a lacunary sequence -/

/-- A `Λ`-lacunary sequence with `a n ≥ 1` grows at least like `Λ^n`. -/
theorem lacunary_pow_le {Λ : NNReal} {a : ℕ → NNReal} (ha : Lacunary Λ a)
    (ha1 : ∀ n, 1 ≤ a n) (n : ℕ) : Λ ^ n ≤ a n := by
  induction n with
  | zero => simpa using ha1 0
  | succ n ih =>
      calc Λ ^ (n + 1) = Λ * Λ ^ n := by ring
        _ ≤ Λ * a n := by gcongr
        _ ≤ a (n + 1) := lacunary_mul_le ha ha1 n

/-- The index beyond which the lacunary sequence `a` certainly exceeds `2^B`.  Only the case
`1 < Λ` is used; the definition is total so that the constant `K` of the main theorem is a total
function of `Λ`. -/
noncomputable def nBound (Λ : NNReal) (B : ℕ) : ℕ :=
  if 1 < Λ then ⌈((B : ℝ) + 2) / Real.logb 2 (Λ : ℝ)⌉₊ else 0

/-- Past the index `nBound Λ B`, the lacunary scales exceed `2^B`. -/
theorem floor_a_gt {Λ : NNReal} (hΛ : 1 < Λ) {a : ℕ → NNReal} (ha : Lacunary Λ a)
    (ha1 : ∀ n, 1 ≤ a n) (B : ℕ) {n : ℕ} (hn : nBound Λ B ≤ n) : 2 ^ B < Nat.floor (a n) := by
  have hΛ0 : (0:ℝ) < (Λ:ℝ) := by exact_mod_cast (lt_trans zero_lt_one hΛ)
  have hlog : 0 < Real.logb 2 (Λ:ℝ) := Real.logb_pos (by norm_num) (by exact_mod_cast hΛ)
  have hceil : ((B : ℝ) + 2) / Real.logb 2 (Λ:ℝ) ≤ (nBound Λ B : ℝ) := by
    rw [nBound, if_pos hΛ]
    exact Nat.le_ceil _
  have hn' : ((B:ℝ) + 2) ≤ (n : ℝ) * Real.logb 2 (Λ:ℝ) := by
    have h2 : ((B : ℝ) + 2) ≤ (nBound Λ B : ℝ) * Real.logb 2 (Λ:ℝ) := by
      rw [div_le_iff₀ hlog] at hceil
      linarith
    have h3 : (nBound Λ B : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hpow : ((2:ℝ) ^ (B + 2)) ≤ (Λ:ℝ) ^ n := by
    have hlogpow : Real.logb 2 ((Λ:ℝ) ^ n) = (n:ℝ) * Real.logb 2 (Λ:ℝ) := Real.logb_pow 2 (Λ:ℝ) n
    have hL : Real.logb 2 ((2:ℝ) ^ (B + 2)) = ((B:ℝ) + 2) := by
      rw [Real.logb_pow 2 (2:ℝ) (B+2), Real.logb_self_eq_one (by norm_num)]
      push_cast; ring
    rw [← Real.logb_le_logb (by norm_num : (1:ℝ) < 2) (by positivity) (by positivity), hL, hlogpow]
    exact hn'
  have hle : ((2:ℝ) ^ (B+2)) ≤ (a n : ℝ) :=
    hpow.trans (by exact_mod_cast lacunary_pow_le ha ha1 n)
  have h1 : (2:ℕ) ^ (B+2) ≤ Nat.floor (a n) := by
    apply Nat.le_floor
    rw [← NNReal.coe_le_coe]
    push_cast
    exact hle
  calc 2 ^ B < 2 ^ (B+2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    _ ≤ Nat.floor (a n) := h1

/-! ## The finite envelope of a family of constants -/

/-- The least constant dominating `C` on the rectangle `[0,B₀] × [-KB-1, KB]`. -/
noncomputable def envConst (C : ℕ → ℤ → NNReal) (B₀ KB : ℕ) : NNReal :=
  (Finset.Icc 0 B₀).sup fun l => (Finset.Icc (-(KB : ℤ) - 1) (KB : ℤ)).sup fun m => C l m

theorem le_envConst {C : ℕ → ℤ → NNReal} {B₀ KB : ℕ} {l : ℕ} {m : ℤ}
    (hl : l ∈ Finset.Icc 0 B₀) (hm : m ∈ Finset.Icc (-(KB : ℤ) - 1) (KB : ℤ)) :
    C l m ≤ envConst C B₀ KB :=
  le_trans (Finset.le_sup (f := C l) hm)
    (Finset.le_sup (f := fun l' => (Finset.Icc (-(KB : ℤ) - 1) (KB : ℤ)).sup fun m => C l' m) hl)

theorem envConst_pos {C : ℕ → ℤ → NNReal} (hC : ∀ l k, 0 < C l k) (B₀ KB : ℕ) :
    0 < envConst C B₀ KB := by
  rw [envConst]
  have hmem : (0 : ℤ) ∈ Finset.Icc (-(KB : ℤ) - 1) (KB : ℤ) := by
    simp only [Finset.mem_Icc]
    omega
  have hmem2 : (0 : ℕ) ∈ Finset.Icc 0 B₀ := by
    simp only [Finset.mem_Icc]
    omega
  calc (0 : NNReal) < C 0 0 := hC 0 0
    _ ≤ (Finset.Icc (-(KB : ℤ) - 1) (KB : ℤ)).sup (C 0) := Finset.le_sup (f := C 0) hmem
    _ ≤ (Finset.Icc 0 B₀).sup
          (fun l' => (Finset.Icc (-(KB : ℤ) - 1) (KB : ℤ)).sup fun m => C l' m) :=
        Finset.le_sup (f := fun l' =>
          (Finset.Icc (-(KB : ℤ) - 1) (KB : ℤ)).sup fun m => C l' m) hmem2

/-! ## `ℓ^q` bounds for the continuous frequency pieces -/

/-- The `ℓ^q` norm of the exact-height projection `Π_{l,≤m}` at a fixed height, from the
projection bound: since the projection is a difference of two of the projections `kmtProj ρ l' m`
at the *same* frequency `m`, the envelope over the height rectangle suffices. -/
theorem eLpNorm_piExact_le {ρ : ℝ} {q : ℝ} (hq : 1 < q) {C : ℕ → ℤ → NNReal} {CC : NNReal}
    {B₀ KB : ℕ} {l : ℕ} (hl : l ≤ B₀) {m : ℤ}
    (hm : m ∈ Finset.Icc (-(KB : ℤ) - 1) (KB : ℤ))
    (hdom : ∀ l' ∈ Finset.Icc 0 B₀, ∀ m' ∈ Finset.Icc (-(KB : ℤ) - 1) (KB : ℤ), C l' m' ≤ CC)
    (hC : ∀ (l' : ℕ) (k' : ℤ) (u : ℤ → ℂ),
      eLpNorm (kmtProj ρ l' k' u) (ENNReal.ofReal q) Measure.count
        ≤ ENNReal.ofReal (C l' k' : ℝ) * eLpNorm u (ENNReal.ofReal q) Measure.count)
    (f : ℤ → ℂ) :
    eLpNorm (piExact (kmtPj ρ) l m f) (ENNReal.ofReal q) Measure.count
      ≤ ENNReal.ofReal (2 * (CC : ℝ)) * eLpNorm f (ENNReal.ofReal q) Measure.count := by
  have hq1 : 1 ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (le_of_lt hq)
  have hmem_l : l ∈ Finset.Icc 0 B₀ := by
    simp only [Finset.mem_Icc]; omega
  have hmem_l' : l - 1 ∈ Finset.Icc 0 B₀ := by
    simp only [Finset.mem_Icc]; omega
  have hAe : ∀ u : ℤ → ℂ, AEStronglyMeasurable u (Measure.count : Measure ℤ) :=
    fun u => (measurable_of_countable u).aestronglyMeasurable
  have harith : ENNReal.ofReal (2 * (CC : ℝ)) = 2 * ENNReal.ofReal (CC : ℝ) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  rw [piExact]
  split_ifs with h0
  · have hle : C 0 m ≤ CC := hdom 0 (by simp only [Finset.mem_Icc]; omega) m hm
    calc eLpNorm (kmtProj ρ 0 m f) (ENNReal.ofReal q) Measure.count
        ≤ ENNReal.ofReal (C 0 m : ℝ) * eLpNorm f (ENNReal.ofReal q) Measure.count := hC 0 m f
      _ ≤ ENNReal.ofReal (2 * (CC : ℝ)) * eLpNorm f (ENNReal.ofReal q) Measure.count := by
          refine mul_le_mul' ?_ le_rfl
          exact ENNReal.ofReal_le_ofReal (by
            have h := hle
            nlinarith [NNReal.coe_nonneg CC])
  · have hle₁ : C l m ≤ CC := hdom l hmem_l m hm
    have hle₂ : C (l - 1) m ≤ CC := hdom (l - 1) hmem_l' m hm
    calc eLpNorm (kmtProj ρ l m f - kmtProj ρ (l - 1) m f) (ENNReal.ofReal q) Measure.count
        ≤ eLpNorm (kmtProj ρ l m f) (ENNReal.ofReal q) Measure.count
          + eLpNorm (kmtProj ρ (l - 1) m f) (ENNReal.ofReal q) Measure.count :=
          eLpNorm_sub_le hq1
      _ ≤ ENNReal.ofReal (CC : ℝ) * eLpNorm f (ENNReal.ofReal q) Measure.count
          + ENNReal.ofReal (CC : ℝ) * eLpNorm f (ENNReal.ofReal q) Measure.count :=
          add_le_add ((hC l m f).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by
            exact_mod_cast hle₁)) le_rfl))
            ((hC (l - 1) m f).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by
              exact_mod_cast hle₂)) le_rfl))
      _ = ENNReal.ofReal (2 * (CC : ℝ)) * eLpNorm f (ENNReal.ofReal q) Measure.count := by
          rw [harith]; ring

/-- The `ℓ^q` norm of a continuous frequency piece, from the projection bound.  A piece is either
the exact-height projection `Π_{l,≤κ s}` or the difference of `Π_{l,≤κ s}` and `Π_{l,≤κ (s-1)}`,
so both frequencies have to lie in the envelope range. -/
theorem eLpNorm_piece_le {ρ : ℝ} {q : ℝ} (hq : 1 < q) {C : ℕ → ℤ → NNReal} {CC : NNReal}
    {B₀ KB : ℕ} {l : ℕ} (hl : l ≤ B₀) {κ : ℤ → ℤ} {a s : ℤ}
    (hs : κ s ∈ Finset.Icc (-(KB : ℤ)) (KB : ℤ))
    (hs' : κ (s - 1) ∈ Finset.Icc (-(KB : ℤ)) (KB : ℤ))
    (hdom : ∀ l' ∈ Finset.Icc 0 B₀, ∀ m' ∈ Finset.Icc (-(KB : ℤ) - 1) (KB : ℤ), C l' m' ≤ CC)
    (hC : ∀ (l' : ℕ) (k' : ℤ) (u : ℤ → ℂ),
      eLpNorm (kmtProj ρ l' k' u) (ENNReal.ofReal q) Measure.count
        ≤ ENNReal.ofReal (C l' k' : ℝ) * eLpNorm u (ENNReal.ofReal q) Measure.count)
    (f : ℤ → ℂ) :
    eLpNorm (piece (kmtPj ρ) l κ a s f) (ENNReal.ofReal q) Measure.count
      ≤ ENNReal.ofReal (4 * (CC : ℝ)) * eLpNorm f (ENNReal.ofReal q) Measure.count := by
  have hq1 : 1 ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (le_of_lt hq)
  have hAe : ∀ u : ℤ → ℂ, AEStronglyMeasurable u (Measure.count : Measure ℤ) :=
    fun u => (measurable_of_countable u).aestronglyMeasurable
  have hm1 : κ s ∈ Finset.Icc (-(KB : ℤ) - 1) (KB : ℤ) := by
    simp only [Finset.mem_Icc] at hs ⊢; omega
  have hm2 : κ (s - 1) ∈ Finset.Icc (-(KB : ℤ) - 1) (KB : ℤ) := by
    simp only [Finset.mem_Icc] at hs' ⊢; omega
  have h2 := eLpNorm_piExact_le (q := q) (C := C) (CC := CC) hq hl hm1 hdom hC f
  have h3 := eLpNorm_piExact_le (q := q) (C := C) (CC := CC) hq hl hm2 hdom hC f
  have harith : ENNReal.ofReal (4 * (CC : ℝ)) = 4 * ENNReal.ofReal (CC : ℝ) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4), ENNReal.ofReal_ofNat]
  have hq2 : ENNReal.ofReal (2 * (CC : ℝ)) ≤ ENNReal.ofReal (4 * (CC : ℝ)) := by
    apply ENNReal.ofReal_le_ofReal
    nlinarith [NNReal.coe_nonneg CC]
  rw [piece]
  split_ifs with h
  · exact h2.trans (mul_le_mul' hq2 le_rfl)
  · calc eLpNorm (piExact (kmtPj ρ) l (κ s) f - piExact (kmtPj ρ) l (κ (s - 1)) f)
          (ENNReal.ofReal q) Measure.count
        ≤ eLpNorm (piExact (kmtPj ρ) l (κ s) f) (ENNReal.ofReal q) Measure.count
          + eLpNorm (piExact (kmtPj ρ) l (κ (s - 1)) f) (ENNReal.ofReal q) Measure.count :=
          eLpNorm_sub_le hq1
      _ ≤ ENNReal.ofReal (2 * (CC : ℝ)) * eLpNorm f (ENNReal.ofReal q) Measure.count
          + ENNReal.ofReal (2 * (CC : ℝ)) * eLpNorm f (ENNReal.ofReal q) Measure.count :=
          add_le_add h2 h3
      _ = ENNReal.ofReal (4 * (CC : ℝ)) * eLpNorm f (ENNReal.ofReal q) Measure.count := by
          rw [harith]
          have h2' : ENNReal.ofReal (2 * (CC : ℝ)) = 2 * ENNReal.ofReal (CC : ℝ) := by
            rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
          rw [h2']; ring

/-! ## The degenerate cases -/

/-- The exceptional part of the zero function is zero. -/
theorem exceptionalPart_zero_left (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) :
    exceptionalPart ρ P C₀ a (0 : ℤ → ℂ) g l₁ l₂ k₁ k₂ = 0 := by
  funext n x
  rw [exceptionalPart]
  simp only [colTuple_eq, mainPartTuple, varpCol_apply, varpPiece, Fpiece, Gpiece,
    piece, piExact, kmtPj_proj, kmtProj_zero]
  by_cases h : (Nat.floor (a n)) = 0 <;>
    simp [h, AhalfR, Ahalf, Ablock]

/-- The exceptional part of a family with `g = 0` is zero. -/
theorem exceptionalPart_zero_right (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (f : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) :
    exceptionalPart ρ P C₀ a f (0 : ℤ → ℂ) l₁ l₂ k₁ k₂ = 0 := by
  funext n x
  rw [exceptionalPart]
  simp only [colTuple_eq, mainPartTuple, varpCol_apply, varpPiece, Fpiece, Gpiece,
    piece, piExact, kmtPj_proj, kmtProj_zero]
  by_cases h : (Nat.floor (a n)) = 0 <;>
    simp [h, AhalfR, Ahalf, Ablock]

/-- A function on `ℤ` with vanishing `ℓ^p` norm (with respect to the counting measure) vanishes. -/
theorem eq_zero_of_eLpNorm_eq_zero {g : ℤ → ℂ} {p : ENNReal} (hp : p ≠ 0)
    (h : eLpNorm g p Measure.count = 0) : g = 0 := by
  have hae : AEStronglyMeasurable g (Measure.count) :=
    (measurable_of_countable g).aestronglyMeasurable
  have hae0 : g =ᵐ[Measure.count] 0 := (eLpNorm_eq_zero_iff hp).mp h
  have hnull : Measure.count {y : ℤ | g y ≠ 0} = 0 := by
    have h1 : ∀ᵐ y ∂(Measure.count), g y = 0 := hae0
    rw [MeasureTheory.ae_iff] at h1
    simpa using h1
  funext x
  by_contra hx
  have hxmem : x ∈ {y : ℤ | g y ≠ 0} := hx
  have h1 : (Measure.count ({x} : Set ℤ)) ≤ Measure.count {y : ℤ | g y ≠ 0} :=
    MeasureTheory.measure_mono (Set.singleton_subset_iff.mpr hxmem)
  rw [Measure.count_singleton, hnull] at h1
  norm_num at h1

/-! ## The parameters of the exceptional regime are bounded -/

/-- The logarithmic scale of a scale `N ≤ 2^{B₀}` is at most `B₀`. -/
theorem logN_le_of_le_pow {N B₀ : ℕ} (hN : N ≤ 2 ^ B₀) (hB₀ : 1 ≤ B₀) : logN N ≤ (B₀ : ℤ) := by
  rw [logN]
  have h2le : 2 ≤ 2 ^ B₀ := by
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hB₀
  have h : Nat.log 2 (max N 2) ≤ B₀ := by
    have h2 : 0 < max N 2 := by omega
    rw [← Nat.lt_succ_iff, Nat.log_lt_iff_lt_pow (by norm_num) h2.ne']
    calc max N 2 ≤ 2 ^ B₀ := max_le hN h2le
      _ < 2 ^ (B₀ + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  exact_mod_cast h

/-- The two frequencies `k₁ - Log N` and `k₁ - 1 - Log N` of the `F`-piece lie in the interval
`[-KB, KB]` as soon as `KB ≥ B₀ + 1`. -/
theorem mem_freq_F {N k₁ B₀ KB : ℕ} (hlog : logN N ≤ (B₀:ℤ)) (hk₁ : k₁ ≤ B₀)
    (hB₀KB : B₀ + 1 ≤ KB) :
    (-(logN N) + (k₁ : ℤ)) ∈ Finset.Icc (-(KB:ℤ)) (KB:ℤ) ∧
    (-(logN N) + ((k₁ : ℤ) - 1)) ∈ Finset.Icc (-(KB:ℤ)) (KB:ℤ) := by
  have h0 : 0 ≤ logN N := logN_nonneg N
  have h1 : ((B₀:ℤ)) ≤ (KB:ℤ) := by exact_mod_cast (by omega : B₀ ≤ KB)
  simp only [Finset.mem_Icc]
  constructor <;> omega

/-- The two frequencies `d (k₂ - Log N)` and `d (k₂ - 1 - Log N)` of the `G`-piece lie in the
interval `[-KB, KB]` as soon as `KB ≥ (d+1)(B₀+2) + 2`. -/
theorem mem_freq_G {N k₂ B₀ KB d : ℕ} (hlog : logN N ≤ (B₀:ℤ)) (hk₂ : k₂ ≤ B₀)
    (hKB : (d+1)*(B₀+2)+2 ≤ KB) :
    ((d:ℤ) * (-(logN N) + (k₂:ℤ))) ∈ Finset.Icc (-(KB:ℤ)) (KB:ℤ) ∧
    ((d:ℤ) * (-(logN N) + ((k₂:ℤ) - 1))) ∈ Finset.Icc (-(KB:ℤ)) (KB:ℤ) := by
  have h0 : 0 ≤ logN N := logN_nonneg N
  have hd : 0 ≤ (d:ℤ) := Int.natCast_nonneg d
  have hdB : (d:ℤ) * (B₀:ℤ) ≤ (KB:ℤ) := by
    have : (d * B₀ : ℕ) ≤ KB := by nlinarith [hKB]
    exact_mod_cast this
  have hdB' : (d:ℤ) * ((B₀:ℤ) + 1) ≤ (KB:ℤ) := by
    have : (d * (B₀ + 1) : ℕ) ≤ KB := by nlinarith [hKB]
    exact_mod_cast this
  have hk₂' : (k₂:ℤ) ≤ (B₀:ℤ) := by exact_mod_cast hk₂
  simp only [Finset.mem_Icc]
  constructor
  · constructor
    · nlinarith [mul_le_mul_of_nonneg_left (show -(logN N) ≥ -(B₀:ℤ) by omega) hd]
    · nlinarith [mul_le_mul_of_nonneg_left hk₂' hd]
  · constructor
    · nlinarith [mul_le_mul_of_nonneg_left
        (show -(logN N) + ((k₂:ℤ) - 1) ≥ -((B₀:ℤ)+1) by omega) hd]
    · nlinarith [mul_le_mul_of_nonneg_left
        (show -(logN N) + ((k₂:ℤ) - 1) ≤ (B₀:ℤ) by omega) hd]

/-! ## The bound for a single term of the exceptional family -/

/-- The `ℓ^q` bound for the column `varpPiece`, from the projection bounds with constants bounded
by `CC₁` and `CC₂` on the exceptional rectangle. -/
theorem eLpNorm_varpPiece_le {ρ : ℝ} (P : Polynomial ℤ) (a : ℕ → NNReal)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ n : ℕ) {q1R q2R : ℝ} (hq1R : 1 < q1R) (hq2R : 1 < q2R)
    {C₁ C₂ : ℕ → ℤ → NNReal} {CC₁ CC₂ : NNReal} {B₀ KB : ℕ}
    (hdom₁ : ∀ l' ∈ Finset.Icc 0 B₀, ∀ m' ∈ Finset.Icc (-(KB : ℤ) - 1) (KB : ℤ),
      C₁ l' m' ≤ CC₁)
    (hdom₂ : ∀ l' ∈ Finset.Icc 0 B₀, ∀ m' ∈ Finset.Icc (-(KB : ℤ) - 1) (KB : ℤ),
      C₂ l' m' ≤ CC₂)
    (hsum : (ENNReal.ofReal q1R)⁻¹ + (ENNReal.ofReal q2R)⁻¹ ≤ 1)
    (hC₁ : ∀ (l' : ℕ) (k' : ℤ) (u : ℤ → ℂ),
      eLpNorm (kmtProj ρ l' k' u) (ENNReal.ofReal q1R) Measure.count
        ≤ ENNReal.ofReal (C₁ l' k' : ℝ) * eLpNorm u (ENNReal.ofReal q1R) Measure.count)
    (hC₂ : ∀ (l' : ℕ) (k' : ℤ) (u : ℤ → ℂ),
      eLpNorm (kmtProj ρ l' k' u) (ENNReal.ofReal q2R) Measure.count
        ≤ ENNReal.ofReal (C₂ l' k' : ℝ) * eLpNorm u (ENNReal.ofReal q2R) Measure.count)
    (hl₁ : l₁ ≤ B₀) (hl₂ : l₂ ≤ B₀) (hk₁ : k₁ ≤ B₀) (hk₂ : k₂ ≤ B₀)
    (hKB : (P.natDegree + 1) * (B₀ + 2) + 2 ≤ KB)
    (hlog : logN (Nat.floor (a n)) ≤ (B₀ : ℤ))
    (hF : MemLp (Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) (Nat.floor (a n)) f)
      (ENNReal.ofReal q1R) Measure.count)
    (hG : MemLp (Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) (Nat.floor (a n)) g)
      (ENNReal.ofReal q2R) Measure.count) :
    eLpNorm (varpPiece (kmtPj ρ) P P.natDegree (a n) f g l₁ l₂ k₁ k₂)
        (((ENNReal.ofReal q1R)⁻¹ + (ENNReal.ofReal q2R)⁻¹)⁻¹) Measure.count
      ≤ ENNReal.ofReal (16 * (CC₁ : ℝ) * (CC₂ : ℝ)) *
          (eLpNorm f (ENNReal.ofReal q1R) Measure.count *
            eLpNorm g (ENNReal.ofReal q2R) Measure.count) := by
  have hq : 1 ≤ (((ENNReal.ofReal q1R)⁻¹ + (ENNReal.ofReal q2R)⁻¹)⁻¹) :=
    ENNReal.one_le_inv.mpr hsum
  have hH : (ENNReal.ofReal q1R)⁻¹ + (ENNReal.ofReal q2R)⁻¹
      = (((ENNReal.ofReal q1R)⁻¹ + (ENNReal.ofReal q2R)⁻¹)⁻¹)⁻¹ := (inv_inv _).symm
  have hB₀KB : B₀ + 1 ≤ KB := by nlinarith [hKB]
  have hmemF := mem_freq_F hlog hk₁ hB₀KB
  have hmemG := mem_freq_G (d := P.natDegree) hlog hk₂ hKB
  have hFb : eLpNorm (Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) (Nat.floor (a n)) f)
        (ENNReal.ofReal q1R) Measure.count
      ≤ ENNReal.ofReal (4 * (CC₁ : ℝ)) * eLpNorm f (ENNReal.ofReal q1R) Measure.count :=
    eLpNorm_piece_le (q := q1R) (C := C₁) (CC := CC₁) (B₀ := B₀) (KB := KB) (l := l₁)
      (κ := fun s => -(logN (Nat.floor (a n))) + s) (a := 0) (s := (k₁ : ℤ))
      hq1R hl₁ hmemF.1 hmemF.2 hdom₁ hC₁ f
  have hGb : eLpNorm (Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) (Nat.floor (a n)) g)
        (ENNReal.ofReal q2R) Measure.count
      ≤ ENNReal.ofReal (4 * (CC₂ : ℝ)) * eLpNorm g (ENNReal.ofReal q2R) Measure.count :=
    eLpNorm_piece_le (q := q2R) (C := C₂) (CC := CC₂) (B₀ := B₀) (KB := KB) (l := l₂)
      (κ := fun s => (P.natDegree : ℤ) * (-(logN (Nat.floor (a n))) + s))
      (a := 0) (s := (k₂ : ℤ)) hq2R hl₂ hmemG.1 hmemG.2 hdom₂ hC₂ g
  have h1 : ENNReal.ofReal (4 * (CC₁ : ℝ)) = 4 * ENNReal.ofReal (CC₁ : ℝ) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4), ENNReal.ofReal_ofNat]
  have h2 : ENNReal.ofReal (4 * (CC₂ : ℝ)) = 4 * ENNReal.ofReal (CC₂ : ℝ) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4), ENNReal.ofReal_ofNat]
  have h3 : ENNReal.ofReal (16 * (CC₁ : ℝ) * (CC₂ : ℝ))
      = 16 * (ENNReal.ofReal (CC₁ : ℝ) * ENNReal.ofReal (CC₂ : ℝ)) := by
    rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 16 * (CC₁ : ℝ)),
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 16), ENNReal.ofReal_ofNat]
    ring
  refine (eLpNorm_AhalfR_le (μ := Measure.count) TZ measurePreserving_TZ (a n) X P
    (q := ((ENNReal.ofReal q1R)⁻¹ + (ENNReal.ofReal q2R)⁻¹)⁻¹)
    (q₁ := ENNReal.ofReal q1R) (q₂ := ENNReal.ofReal q2R) hH hq hF hG).trans ?_
  refine (mul_le_mul' hFb hGb).trans ?_
  rw [h1, h2, h3]
  exact le_of_eq (by ring_nf)

/-- The `ℓ^q` bound for a single term of the exceptional family: on the exceptional set the
exceptional part *is* the column `varpPiece`. -/
theorem eLpNorm_exceptionalPart_le {ρ : ℝ} (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ n : ℕ) {q1R q2R : ℝ} (hq1R : 1 < q1R) (hq2R : 1 < q2R)
    {C₁ C₂ : ℕ → ℤ → NNReal} {CC₁ CC₂ : NNReal} {B₀ KB : ℕ}
    (hdom₁ : ∀ l' ∈ Finset.Icc 0 B₀, ∀ m' ∈ Finset.Icc (-(KB : ℤ) - 1) (KB : ℤ),
      C₁ l' m' ≤ CC₁)
    (hdom₂ : ∀ l' ∈ Finset.Icc 0 B₀, ∀ m' ∈ Finset.Icc (-(KB : ℤ) - 1) (KB : ℤ),
      C₂ l' m' ≤ CC₂)
    (hsum : (ENNReal.ofReal q1R)⁻¹ + (ENNReal.ofReal q2R)⁻¹ ≤ 1)
    (hC₁ : ∀ (l' : ℕ) (k' : ℤ) (u : ℤ → ℂ),
      eLpNorm (kmtProj ρ l' k' u) (ENNReal.ofReal q1R) Measure.count
        ≤ ENNReal.ofReal (C₁ l' k' : ℝ) * eLpNorm u (ENNReal.ofReal q1R) Measure.count)
    (hC₂ : ∀ (l' : ℕ) (k' : ℤ) (u : ℤ → ℂ),
      eLpNorm (kmtProj ρ l' k' u) (ENNReal.ofReal q2R) Measure.count
        ≤ ENNReal.ofReal (C₂ l' k' : ℝ) * eLpNorm u (ENNReal.ofReal q2R) Measure.count)
    (hl₁ : l₁ ≤ B₀) (hl₂ : l₂ ≤ B₀) (hk₁ : k₁ ≤ B₀) (hk₂ : k₂ ≤ B₀)
    (hKB : (P.natDegree + 1) * (B₀ + 2) + 2 ≤ KB)
    (hlog : logN (Nat.floor (a n)) ≤ (B₀ : ℤ))
    (hExc : ExcPred ρ C₀ l₁ l₂ k₁ k₂ (Nat.floor (a n)))
    (hF : MemLp (Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) (Nat.floor (a n)) f)
      (ENNReal.ofReal q1R) Measure.count)
    (hG : MemLp (Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) (Nat.floor (a n)) g)
      (ENNReal.ofReal q2R) Measure.count) :
    eLpNorm (fun x => exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
        (((ENNReal.ofReal q1R)⁻¹ + (ENNReal.ofReal q2R)⁻¹)⁻¹) Measure.count
      ≤ ENNReal.ofReal (16 * (CC₁ : ℝ) * (CC₂ : ℝ)) *
          (eLpNorm f (ENNReal.ofReal q1R) Measure.count *
            eLpNorm g (ENNReal.ofReal q2R) Measure.count) := by
  have hpre : (fun x => exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
      = varpPiece (kmtPj ρ) P P.natDegree (a n) f g l₁ l₂ k₁ k₂ := by
    funext x
    exact (exceptionalPart_apply ρ P C₀ a f g l₁ l₂ k₁ k₂ n x).trans (if_pos hExc)
  rw [hpre]
  exact eLpNorm_varpPiece_le P a f g l₁ l₂ k₁ k₂ n hq1R hq2R hdom₁ hdom₂ hsum hC₁ hC₂
    hl₁ hl₂ hk₁ hk₂ hKB hlog hF hG


end

end Work.KMTAreas.A7
