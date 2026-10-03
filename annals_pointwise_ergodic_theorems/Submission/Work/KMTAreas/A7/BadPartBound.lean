/-
# The bad (non-Farey) part of the §8 linear lacunary estimate

This is the `hBadPart` input of `Work.KMTAreas.A7.lacunaryBumpVarEstimate_assembly`
(`Submission/Work/KMTAreas/A7/lacunaryBumpAssembly.lean`), i.e. the `¬ Farey` (wide-window,
"coarse") part of the paper's (lin-1). It is the statement of
`Work.KMTAreas.A7.lacunaryBumpBadPartBound`
(`Submission/Work/KMTAreas/A7/lacunaryBumpBadPartBound.lean`), restated here so that this module can
be proved independently; the consumer simply sets `lacunaryBumpBadPartBound := BadPartBound`.

## The proof, as implemented below

Write `M = logN (⌊a n⌋)`, and recall `Farey Cρc ρ l₁ k₁ a n :↔ (k₁:ℤ) - M ≤ fareyK Cρc ρ l₁`,
`Bads = core ∧ ¬ Farey`.

1. **No bad scale.** If `¬ ∃ n, Bads …, a n`, the masked family is identically `0`, so the
   left-hand side is `0`.
2. **A bad scale exists ⟹ the loss scale is bounded.** `exists_Lnat_le_of_bad` gives a constant
   `B = B ρ C₀ Cρc` with `Lnat l₁ l₂ k₁ k₂ ≤ B` whenever some bad scale exists. Hence
   `l₁, l₂, k₁, k₂ ≤ B`.
3. **A bad scale has `a n` bounded.** `¬ Farey` gives `fareyK Cρc ρ l₁ < (k₁:ℤ) - M`, and
   `Int.lt_floor_add_one` with `fareyK Cρc ρ l₁ = ⌊-(Cρc 2^{ρ l₁})⌋` gives
   `-(Cρc 2^{ρ l₁}) - 1 < fareyK Cρc ρ l₁`; hence `M < Cρc 2^{ρ l₁} + 1 + k₁ ≤ Θ`, where
   `Θ := Cρc 2^{ρ B} + 1 + B` depends only on `ρ, Cρc, B`. So `M ≤ Θn := Nat.ceil Θ`, and
   `⌊a n⌋ < 2^{Θn+1}` (`Nat.lt_pow_succ_log_self`), whence `a n < X := 2^{Θn+1} + 1`.
4. **Finitely many bad scales.** `lacunary_index_bound Λ hΛ a ha ha1 X hX1` gives `K` with
   `(K:ℝ) ≤ Real.log X / Real.log Λ + 2` and `a n < X → n < K`. So every bad scale is
   `< K ≤ K₀` with `K₀ := Nat.ceil (Real.log X / Real.log Λ + 2)`, depending only on
   `ρ, C₀, Cρc, Λ`. (The number of bad scales is bounded by `K₀` — *not* by the number of
   admissible scales.)
5. **Each single scale is bounded on `ℓ^p`.** `Tle_varphiNt_single_scale ρ hρ l p hp hptop` gives,
   for each height `l`, a constant `C l` with
   `‖Tle ρ l (varphiNt N k₁ t) f‖_p ≤ ofReal (C l) * ‖f‖_p` whenever `2^k₁ ≤ N` and
   `t ∈ Icc (1/2) 1`; taking the supremum over `l ≤ B` gives one constant `Cs` for all `l ≤ B`.
   On the core, `2^k₁ ≤ ⌊a n⌋` holds (`badPart_two_pow_le_floor_of_core`, reproved below from
   `mainRegime`). The *exact-height* multiplier is a difference,
   `Tex ρ l φ f = Tle ρ l φ f - Tle ρ (l-1) φ f` **for every `l`** (`badPart_Tex_eq_Tle_sub`, whose
   admissibility hypotheses come from
   `adm_of_bump (contDiff_varphiNt _ _ t) (hasCompactSupport_varphiNt _ _ t)`; at `l = 0` both
   sides vanish), and Minkowski gives
   `‖Tex ρ l₁ (varphiNt ⌊a n⌋ k₁ t) f‖_p ≤ ofReal (2 Cs) * ‖f‖_p` at every bad scale.
6. **Assembly.** `Submission.PointwiseErgodicTheorems.eLpNorm_variationalNorm_le_sum` (from
   `Submission/SingleScale.lean`) with `s = Finset.range K₀` and the support property of step 4
   gives `LHS ≤ ∑_{n < K₀} 4 * ‖(masked family) n‖_p ≤ ofReal (4 * 2 Cs * K₀) * ‖f‖_p`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.exists_Lnat_le_of_bad
import Submission.Work.KMTAreas.A7.lacunary_index_bound

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier
open Work.KMTContract Work.Analysis.EndVar

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## Local helpers for the bad-scale estimate -/

/-- `iwConv` with the empty frequency set vanishes (its symbol is identically zero). -/
theorem badPart_iwConv_empty (Φ : Circ → ℂ) (f : ℤ → ℂ) :
    iwConv (∅ : Finset Circ) Φ f = 0 := by
  funext n
  simp only [iwConv_apply]
  have hsym : iwSymbolSet (∅ : Finset Circ) Φ = (0 : Circ → ℂ) := by
    funext ξ
    simp [iwSymbolSet]
  rw [hsym]
  simp [iwKernel, fourierCoeff]

/-- **The exact-height multiplier at level `0` vanishes**: `iwArithFreqsNew ρ 0 = ∅` because
`(0 : ℕ) - 1 = 0`. -/
theorem badPart_Tex_zero_level (ρ : ℝ) (φ : ℝ → ℂ) (f : ℤ → ℂ) : Tex ρ 0 φ f = 0 := by
  have h01 : (0 : ℕ) - 1 = 0 := by omega
  have h : iwArithFreqsNew ρ 0 = (∅ : Finset Circ) := by
    simp only [iwArithFreqsNew, h01, Finset.sdiff_self]
  rw [Tex, h]
  exact badPart_iwConv_empty _ _

/-- **The exact-height multiplier is a difference of height-`≤` multipliers, for every `l ∈ ℕ`.**
At `l = 0` both sides are zero, and for `l ≥ 1` this is `Tex_eq_Tle_sub_of_bounded`. -/
theorem badPart_Tex_eq_Tle_sub (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l : ℕ) {φ : ℝ → ℂ}
    (hAdm : Adm (iwArithFreqs ρ l) φ) (hAdm' : Adm (iwArithFreqs ρ (l - 1)) φ)
    {f : ℤ → ℂ} {Bnd : ℝ} (hf : ∀ m : ℤ, ‖f m‖ ≤ Bnd) :
    Tex ρ l φ f = Tle ρ l φ f - Tle ρ (l - 1) φ f := by
  rcases Nat.eq_zero_or_pos l with h | h
  · subst h
    rw [badPart_Tex_zero_level]
    have h01 : (0 : ℕ) - 1 = 0 := by omega
    rw [h01, sub_self]
  · exact Tex_eq_Tle_sub_of_bounded ρ hρ hρ1 h hAdm hAdm' hf

/-- The threshold `2^{2^u}` of the scale split exceeds `2`. -/
theorem badPart_two_le_splitCut (ρ : ℝ) (L : ℕ) : 2 ≤ splitCut ρ L := by
  rw [splitCut]
  calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (2 ^ scaleCount 1 ρ L) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) Nat.one_le_two_pow

/-- On the core scales the height `k₁` satisfies `2 ^ k₁ ≤ ⌊a n⌋`. -/
theorem badPart_two_pow_le_floor_of_core {ρ : ℝ} {C₀ : ℕ} {l₁ l₂ k₁ k₂ : ℕ} {a : ℕ → NNReal}
    {n : ℕ} (h : core ρ C₀ l₁ l₂ k₁ k₂ a n) : 2 ^ k₁ ≤ Nat.floor (a n) := by
  obtain ⟨hin, hcut, hmain⟩ := h
  have hN : 2 < Nat.floor (a n) := lt_of_le_of_lt (badPart_two_le_splitCut ρ _) hcut
  have hk₁ : k₁ ≤ (logN (Nat.floor (a n))).toNat := le_trans (Nat.le_add_right k₁ _) hmain.1
  have hlog : (logN (Nat.floor (a n))).toNat = Nat.log 2 (max (Nat.floor (a n)) 2) := by
    simp [logN]
  have hne : max (Nat.floor (a n)) 2 ≠ 0 := by
    have : 2 ≤ max (Nat.floor (a n)) 2 := le_max_right _ _
    omega
  have hpow : 2 ^ Nat.log 2 (max (Nat.floor (a n)) 2) ≤ max (Nat.floor (a n)) 2 :=
    Nat.pow_log_le_self 2 hne
  have hmax : max (Nat.floor (a n)) 2 = Nat.floor (a n) := max_eq_left (le_of_lt hN)
  calc 2 ^ k₁ ≤ 2 ^ (logN (Nat.floor (a n))).toNat :=
        pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hk₁
    _ = 2 ^ Nat.log 2 (max (Nat.floor (a n)) 2) := by rw [hlog]
    _ ≤ max (Nat.floor (a n)) 2 := hpow
    _ = Nat.floor (a n) := hmax

/-- The single-scale bound for `Tle ρ l (varphiNt N k₁ t)` is *uniform* over `l ≤ B`. -/
theorem badPart_Tle_single_scale_uniform (ρ : ℝ) (hρ : 0 < ρ) (p : ENNReal) (hp : 1 < p)
    (hptop : p < ⊤) (B : ℕ) :
    ∃ C : NNReal, 0 < C ∧ ∀ (l : ℕ), l ≤ B → ∀ (N k₁ : ℕ), 2 ^ k₁ ≤ N → ∀ (t : ℝ),
      t ∈ Set.Icc (1 / 2 : ℝ) 1 → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (Tle ρ l (varphiNt N k₁ t) f) p
          (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal (C : ℝ) *
            MeasureTheory.eLpNorm f p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  choose Cl hClpos hClbd using fun l : ℕ => Tle_varphiNt_single_scale ρ hρ l p hp hptop
  refine ⟨(Finset.range (B + 1)).sup Cl, ?_, ?_⟩
  · exact lt_of_lt_of_le (hClpos 0)
      (Finset.le_sup (f := Cl) (Finset.mem_range.mpr (by omega)))
  · intro l hl N k₁ hNk t ht f
    have hmem : l ∈ Finset.range (B + 1) := Finset.mem_range.mpr (by omega)
    refine (hClbd l N k₁ hNk t ht f).trans ?_
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
    exact_mod_cast Finset.le_sup (f := Cl) hmem

/-- The variational norm of the zero family vanishes. -/
theorem badPart_variationalNorm_zero (r : NNReal) (hr : 1 ≤ r) :
    PointwiseErgodicTheorems.variationalNorm r (fun _ : ℕ => (0 : ℂ)) = 0 := by
  have h : (fun _ : ℕ => (0 : ℂ)) = (0 : ℕ → ℂ) := by
    funext x
    simp
  rw [h]
  have h2 := variationalNorm_smul (r := r) hr (0 : ℂ) (0 : ℕ → ℂ)
  simpa using h2

/-- `eLpNorm` of the identically vanishing `ℝ≥0∞`-valued function is zero. -/
theorem badPart_eLpNorm_zero_fun (p : ENNReal) (μ : MeasureTheory.Measure ℤ) :
    MeasureTheory.eLpNorm (fun _ : ℤ => (0 : ℝ≥0∞)) p μ = 0 := by
  have h : (fun _ : ℤ => (0 : ℝ≥0∞)) = (0 : ℤ → ℝ≥0∞) := by
    funext x
    rfl
  rw [h, MeasureTheory.eLpNorm_zero]

/-! ## The bad-scale estimate -/

theorem BadPartBound (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (hρC : ρ ≤ 1 / (2 * (C₀ : ℝ))) (Cρc : ℝ) (hCρc : 3 ≤ Cρc) (Λ : NNReal) (hΛ : 1 < Λ)
    (r : NNReal) (hr : 2 < r) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
      (ha1 : ∀ n, 1 ≤ a n) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1)
      (f : ℤ → ℂ) (Bf : ℝ) (hBf : ∀ m : ℤ, ‖f m‖ ≤ Bf),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
            ¬ Work.KMTAreas.A7.Farey Cρc ρ l₁ k₁ a n
          then Work.KMTAreas.A7.Tex ρ l₁
            (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) f x else 0))
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  classical
  obtain ⟨B, hB⟩ := exists_Lnat_le_of_bad ρ hρ hρ1 C₀ hC₀ hρC Cρc hCρc Λ hΛ
  obtain ⟨Cs, hCspos, hCs⟩ := badPart_Tle_single_scale_uniform ρ hρ p hp hptop B
  have hCsR : (0 : ℝ) < (Cs : ℝ) := NNReal.coe_pos.mpr hCspos
  set X : ℝ := (2 : ℝ) ^ ((B : ℝ) + Cρc * (2 : ℝ) ^ (ρ * (B : ℝ)) + 2) + 1 with hXdef
  have hX1 : (1 : ℝ) ≤ X := by
    have h1 : (0 : ℝ) < (2 : ℝ) ^ ((B : ℝ) + Cρc * (2 : ℝ) ^ (ρ * (B : ℝ)) + 2) :=
      Real.rpow_pos_of_pos (by norm_num) _
    rw [hXdef]; linarith
  set K₀ : ℕ := Nat.ceil (Real.log X / Real.log (Λ : ℝ) + 2) with hK₀def
  have hK₀le : Real.log X / Real.log (Λ : ℝ) + 2 ≤ (K₀ : ℝ) := by
    rw [hK₀def]; exact Nat.le_ceil _
  have hK₀2 : (2 : ℝ) ≤ (K₀ : ℝ) := by
    have hlogΛ : 0 < Real.log (Λ : ℝ) := Real.log_pos (by exact_mod_cast hΛ)
    have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX1
    have h0 : 0 ≤ Real.log X / Real.log (Λ : ℝ) := div_nonneg hlogX hlogΛ.le
    linarith
  have hCpos : (0 : ℝ) < 4 * (2 * (Cs : ℝ)) * (K₀ : ℝ) := by
    have h1 : (0 : ℝ) < 2 * (Cs : ℝ) := by linarith
    nlinarith
  refine ⟨4 * (2 * (Cs : ℝ)) * (K₀ : ℝ), hCpos, ?_⟩
  intro a ha ha1 l₁ l₂ k₁ k₂ t ht f Bf hBf
  have hr1 : (1 : NNReal) ≤ r := by
    have h2 : (1 : NNReal) ≤ 2 := by norm_num
    exact le_trans h2 (le_of_lt hr)
  have hp1 : (1 : ENNReal) ≤ p := le_of_lt hp
  set u : ℕ → ℤ → ℂ := fun n x =>
    if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₁ k₁ a n then
      Tex ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f x else 0 with hudef
  have hg : (fun x : ℤ => variationalNorm r (fun n : ℕ =>
        if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₁ k₁ a n then
          Tex ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f x else 0))
      = fun x : ℤ => variationalNorm r (fun n : ℕ => u n x) := by
    funext x
    simp only [hudef]
  rw [hg]
  by_cases hbad : ∃ n, Bads ρ C₀ Cρc l₁ l₂ k₁ k₂ a n
  · have hL : Lnat l₁ l₂ k₁ k₂ ≤ B := hB a ha ha1 l₁ l₂ k₁ k₂ hbad
    have hl₁B : l₁ ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
    have hl₁B' : l₁ - 1 ≤ B := by omega
    -- every bad scale is `< K₀`
    have hmem : ∀ n : ℕ, (core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₁ k₁ a n) → n < K₀ := by
      intro n hn
      obtain ⟨⟨hin, hcut, _⟩, hnf⟩ := hn
      obtain ⟨hlmax, hk₁, _⟩ := hin
      obtain ⟨K, hKle, hKbd⟩ := lacunary_index_bound Λ hΛ a ha ha1 X hX1
      have haX : (a n : ℝ) < X := by
        have hk₁B : k₁ ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
        have hl₁B2 : l₁ ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
        have hfarey : fareyK Cρc ρ l₁ < (k₁ : ℤ) - logN (Nat.floor (a n)) :=
          not_le.mp (by simpa only [Farey] using hnf)
        have hfloor : -(Cρc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) - 1
            < ((fareyK Cρc ρ l₁ : ℤ) : ℝ) := by
          have h := Int.lt_floor_add_one (-(Cρc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))))
          simp only [fareyK]
          linarith
        have hcast : ((fareyK Cρc ρ l₁ : ℤ) : ℝ)
            < (k₁ : ℝ) - (logN (Nat.floor (a n)) : ℝ) := by
          exact_mod_cast hfarey
        have hMlt : (logN (Nat.floor (a n)) : ℝ)
            < (k₁ : ℝ) + Cρc * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) + 1 := by linarith
        have hrpow : (2 : ℝ) ^ (ρ * (l₁ : ℝ)) ≤ (2 : ℝ) ^ (ρ * (B : ℝ)) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          have h1 : (l₁ : ℝ) ≤ (B : ℝ) := by exact_mod_cast hl₁B2
          nlinarith [hρ]
        have h2 : Cρc * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) ≤ Cρc * (2 : ℝ) ^ (ρ * (B : ℝ)) :=
          mul_le_mul_of_nonneg_left hrpow (by linarith)
        have hexp : (logN (Nat.floor (a n)) : ℝ) + 1
            < (B : ℝ) + Cρc * (2 : ℝ) ^ (ρ * (B : ℝ)) + 2 := by
          have h1 : (k₁ : ℝ) ≤ (B : ℝ) := by exact_mod_cast hk₁B
          linarith
        have hfloor_le : Nat.floor (a n) < 2 ^ ((logN (Nat.floor (a n))).toNat + 1) := by
          rcases Nat.eq_zero_or_pos (Nat.floor (a n)) with h | h
          · rw [h]; exact Nat.one_le_two_pow
          · have h2 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num)
              (max (Nat.floor (a n)) 2)
            rw [show Nat.log 2 (max (Nat.floor (a n)) 2)
                = (logN (Nat.floor (a n))).toNat from by simp [logN]] at h2
            exact lt_of_le_of_lt (le_max_left _ _) h2
        have hcast2 : (Nat.floor (a n) : ℝ)
            < (2 : ℝ) ^ (((logN (Nat.floor (a n))).toNat : ℝ) + 1) := by
          have h : ((Nat.floor (a n) : ℕ) : ℝ)
              < (((2 : ℕ) ^ ((logN (Nat.floor (a n))).toNat + 1) : ℕ) : ℝ) := by
            exact_mod_cast hfloor_le
          rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast] at h
          rw [show (((logN (Nat.floor (a n))).toNat + 1 : ℕ) : ℝ)
              = ((logN (Nat.floor (a n))).toNat : ℝ) + 1 by push_cast; ring] at h
          exact h
        have hexp2 : ((logN (Nat.floor (a n))).toNat : ℝ) + 1
            ≤ (B : ℝ) + Cρc * (2 : ℝ) ^ (ρ * (B : ℝ)) + 2 := by
          have h1 : ((logN (Nat.floor (a n))).toNat : ℝ) ≤ (logN (Nat.floor (a n)) : ℝ) := by
            have h2 : (0 : ℤ) ≤ logN (Nat.floor (a n)) := Int.natCast_nonneg _
            have h3 : ((logN (Nat.floor (a n))).toNat : ℤ) ≤ logN (Nat.floor (a n)) := by
              rw [Int.toNat_of_nonneg h2]
            exact_mod_cast h3
          linarith
        have h3 : (2 : ℝ) ^ (((logN (Nat.floor (a n))).toNat : ℝ) + 1)
            ≤ (2 : ℝ) ^ ((B : ℝ) + Cρc * (2 : ℝ) ^ (ρ * (B : ℝ)) + 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp2
        have hlt : (a n : ℝ) < (Nat.floor (a n) : ℝ) + 1 := Nat.lt_floor_add_one _
        have hfin : (Nat.floor (a n) : ℝ) + 1 < X := by
          rw [hXdef]
          linarith [lt_of_lt_of_le hcast2 h3]
        linarith
      have hKK₀ : K ≤ K₀ := by exact_mod_cast (le_trans hKle hK₀le)
      exact lt_of_lt_of_le (hKbd n haX) hKK₀
    have hsupp : ∀ n, n ∉ Finset.range K₀ → u n = 0 := by
      intro n hn
      funext x
      simp only [hudef, Pi.zero_apply]
      by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₁ k₁ a n
      · exact absurd hc (fun hc' => hn (Finset.mem_range.mpr (hmem n hc')))
      · rw [if_neg hc]
    have hscale : ∀ n ∈ Finset.range K₀, MeasureTheory.eLpNorm (fun x : ℤ => u n x) p
        (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal (2 * (Cs : ℝ)) *
            MeasureTheory.eLpNorm f p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
      intro n hn
      by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₁ k₁ a n
      · have hu_eq : u n = Tex ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f := by
          funext x
          rw [hudef]
          exact if_pos hc
        rw [hu_eq]
        have hNk : 2 ^ k₁ ≤ Nat.floor (a n) := badPart_two_pow_le_floor_of_core hc.1
        have hAdm : Adm (iwArithFreqs ρ l₁) (varphiNt (Nat.floor (a n)) k₁ t) :=
          adm_of_bump (contDiff_varphiNt _ k₁ t) (hasCompactSupport_varphiNt _ k₁ t)
        have hAdm' : Adm (iwArithFreqs ρ (l₁ - 1)) (varphiNt (Nat.floor (a n)) k₁ t) :=
          adm_of_bump (contDiff_varphiNt _ k₁ t) (hasCompactSupport_varphiNt _ k₁ t)
        rw [badPart_Tex_eq_Tle_sub ρ hρ hρ1 l₁ hAdm hAdm' hBf]
        have hA : MeasureTheory.eLpNorm (Tle ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f) p
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
            ≤ ENNReal.ofReal (Cs : ℝ) *
                MeasureTheory.eLpNorm f p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) :=
          hCs l₁ hl₁B (Nat.floor (a n)) k₁ hNk t ht f
        have hB' : MeasureTheory.eLpNorm (Tle ρ (l₁ - 1) (varphiNt (Nat.floor (a n)) k₁ t) f) p
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
            ≤ ENNReal.ofReal (Cs : ℝ) *
                MeasureTheory.eLpNorm f p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) :=
          hCs (l₁ - 1) hl₁B' (Nat.floor (a n)) k₁ hNk t ht f
        have hsub : MeasureTheory.eLpNorm (Tle ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f
              - Tle ρ (l₁ - 1) (varphiNt (Nat.floor (a n)) k₁ t) f) p
              (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
            ≤ MeasureTheory.eLpNorm (Tle ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f) p
                (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
              + MeasureTheory.eLpNorm (Tle ρ (l₁ - 1) (varphiNt (Nat.floor (a n)) k₁ t) f) p
                (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
          rw [sub_eq_add_neg]
          refine (MeasureTheory.eLpNorm_add_le hp1).trans (le_of_eq ?_)
          rw [MeasureTheory.eLpNorm_neg]
        calc MeasureTheory.eLpNorm (Tle ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f
                - Tle ρ (l₁ - 1) (varphiNt (Nat.floor (a n)) k₁ t) f) p
                (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
            ≤ MeasureTheory.eLpNorm (Tle ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f) p
                (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
              + MeasureTheory.eLpNorm (Tle ρ (l₁ - 1) (varphiNt (Nat.floor (a n)) k₁ t) f) p
                (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := hsub
          _ ≤ ENNReal.ofReal (Cs : ℝ) *
                MeasureTheory.eLpNorm f p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
              + ENNReal.ofReal (Cs : ℝ) *
                MeasureTheory.eLpNorm f p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) :=
              add_le_add hA hB'
          _ = ENNReal.ofReal (2 * (Cs : ℝ)) *
                MeasureTheory.eLpNorm f p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
              rw [← add_mul, ← ENNReal.ofReal_add hCsR.le hCsR.le]
              congr 1
              ring_nf
      · have hu_eq : u n = 0 := by
          funext x
          simp only [hudef]
          exact if_neg hc
        rw [hu_eq, MeasureTheory.eLpNorm_zero]
        exact bot_le
    have h1 := eLpNorm_variationalNorm_le_sum (r := r) (p := p)
      (μ := MeasureTheory.Measure.count) hr1 hp1 (u := u) (s := Finset.range K₀) hsupp
      (fun n _ => (measurable_of_countable (u n)).aestronglyMeasurable)
    refine h1.trans ?_
    have hsum : (∑ n ∈ Finset.range K₀, (4 : ENNReal) * MeasureTheory.eLpNorm (fun x : ℤ => u n x)
          p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ))
        ≤ ∑ _n ∈ Finset.range K₀, (4 : ENNReal) * (ENNReal.ofReal (2 * (Cs : ℝ)) *
            MeasureTheory.eLpNorm f p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)) :=
      Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hscale n hn) bot_le
    refine hsum.trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hcard' : ((K₀ : ℕ) : ENNReal) ≤ ENNReal.ofReal (K₀ : ℝ) := by
      rw [ENNReal.ofReal_natCast]
    refine (mul_le_mul_of_nonneg_right hcard' bot_le).trans ?_
    have hfin : ENNReal.ofReal (K₀ : ℝ) * ((4 : ENNReal) *
          (ENNReal.ofReal (2 * (Cs : ℝ)) *
            MeasureTheory.eLpNorm f p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)))
        = ENNReal.ofReal (4 * (2 * (Cs : ℝ)) * (K₀ : ℝ)) *
            MeasureTheory.eLpNorm f p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
      rw [show (4 : ENNReal) = ENNReal.ofReal 4 from (ENNReal.ofReal_ofNat 4).symm, ← mul_assoc,
        ← ENNReal.ofReal_mul (p := (K₀ : ℝ)) (q := (4 : ℝ)) (by positivity), ← mul_assoc,
        ← ENNReal.ofReal_mul (p := (K₀ : ℝ) * 4) (q := (2 * (Cs : ℝ))) (by positivity)]
      congr 1
      ring_nf
    rw [hfin]
  · have hzero : (fun x : ℤ => variationalNorm r (fun n : ℕ => u n x)) = fun _ : ℤ => 0 := by
      funext x
      have hz : (fun n : ℕ => u n x) = fun _ : ℕ => (0 : ℂ) := by
        funext n
        simp only [hudef]
        exact if_neg (fun hc => hbad ⟨n, hc⟩)
      rw [hz]
      exact badPart_variationalNorm_zero r hr1
    rw [hzero, badPart_eLpNorm_zero_fun]
    exact bot_le

end

end Work.KMTAreas.A7
