import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Maximal.polyBlockCore_eq_weighted
import Submission.Work.BourgainPlan.Maximal.poly_sharp_core_periodic

/-!
# `polyBlockCoreN` as a weighted periodised-neighbourhood sum

The arbitrary-scale analogue of `Work.BourgainPlan.Maximal.polyBlockCore_eq_weighted`.  The whole
argument is carried out for an *arbitrary* positive dilation `D > 0` with `D⁻¹ < 1/(2 c)`,
`c = P.leadingCoeff`; both the dyadic dilation `polyDil P k` and the lacunary-scale dilation
`polyDilN P N = N ^ deg P` are instances, so nothing in the proof depends on the scale being a
power of two.
-/

namespace Work.BourgainPlan.Oscillation

open Finset
open Classical
open scoped BigOperators
open Work.BourgainPlan.Maximal
open Commons.Analysis.ExponentialSums

noncomputable section
/-- **The weighted per-`(q,a)` collapse.**  Let `C > 0`, `c = C`, `r > 0` with `c r < 1/2`,
`1 ≤ q`, `a < q`, `θ ∈ (0,1)`, and let `w : ℤ → ℂ` be `q·C`-periodic, `w (b + m (qC)) = w b`.
Then the window sum over `l ∈ [-1,C]` of the sharp indicators at the `c`-scaled frequencies
`(a/q + l)/c` equals the sum over the residues `s ∈ [0,C)` of the periodised-neighbourhood
indicators at `(a + s q)/(q c)` — with the matching weights `w (a + l q)` and `w (a + s q)`. -/
private lemma weightedCollapse_gen (C q : ℕ) (w : ℤ → ℂ) (a : ℕ) (hC : 0 < C) (hq : 1 ≤ q)
    (ha : a < q) (hw : ∀ b m : ℤ, w (b + m * ((q * C : ℕ) : ℤ)) = w b)
    (r θ : ℝ) (hcr : (C : ℝ) * r < 1 / 2) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (∑ l ∈ Finset.Icc (-1 : ℤ) C, w ((a : ℤ) + l * (q : ℤ)) *
          (if |θ - (((a : ℝ) + (l : ℝ) * (q : ℝ)) / ((q : ℝ) * (C : ℝ)))| ≤ r
            then (1:ℂ) else 0))
      = ∑ s ∈ Finset.range C, w ((a : ℤ) + (s : ℤ) * (q : ℤ)) *
            perNbhd (((a : ℝ) + (s : ℝ) * (q : ℝ)) / ((q : ℝ) * (C : ℝ))) r θ := by
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hqne : (q:ℝ) ≠ 0 := ne_of_gt hqpos
  have hcpos : (0:ℝ) < (C:ℝ) := by exact_mod_cast hC
  have hcne : (C:ℝ) ≠ 0 := ne_of_gt hcpos
  -- the `perNbhd`-vs-`active` dictionary at the residue `s`
  have hdict : ∀ s : ℕ, perNbhd (((a:ℝ)+(s:ℝ)*(q:ℝ))/((q:ℝ)*(C:ℝ))) r θ = 1 ↔
      ∃ m : ℤ, |θ - ((a:ℝ) + (((s:ℤ) - m*(C:ℤ)):ℝ)*(q:ℝ))/((q:ℝ)*(C:ℝ))| ≤ r := by
    intro s
    have h1 : ∀ m : ℤ, ((a:ℝ) + (s:ℝ)*(q:ℝ))/((q:ℝ)*(C:ℝ)) - (m:ℝ)
        = ((a:ℝ) + (((s:ℤ) - m*(C:ℤ)):ℝ)*(q:ℝ))/((q:ℝ)*(C:ℝ)) := by
      intro m; field_simp; push_cast; ring
    rw [perNbhd_eq_one]
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨m, ?_⟩
      rw [show θ - ((a:ℝ) + (((s:ℤ) - m*(C:ℤ)):ℝ)*(q:ℝ))/((q:ℝ)*(C:ℝ))
          = θ + (m:ℝ) - ((a:ℝ) + (s:ℝ)*(q:ℝ))/((q:ℝ)*(C:ℝ)) by rw [← h1 m]; ring]
      exact hm
    · rintro ⟨m, hm⟩
      refine ⟨m, ?_⟩
      rw [show θ + (m:ℝ) - ((a:ℝ) + (s:ℝ)*(q:ℝ))/((q:ℝ)*(C:ℝ))
          = θ - ((a:ℝ) + (((s:ℤ) - m*(C:ℤ)):ℝ)*(q:ℝ))/((q:ℝ)*(C:ℝ)) by rw [← h1 m]; ring]
      exact hm
  -- separation of distinct window frequencies
  have hsep : ∀ l₁ l₂ : ℤ, l₁ ≠ l₂ →
      2 * r < |((a:ℝ)+(l₁:ℝ)*(q:ℝ))/((q:ℝ)*(C:ℝ))
        - ((a:ℝ)+(l₂:ℝ)*(q:ℝ))/((q:ℝ)*(C:ℝ))| := by
    intro l₁ l₂ hne
    have hcr' : 2 * r * (C:ℝ) < 1 := by nlinarith
    have hsub : ((a:ℝ)+(l₁:ℝ)*(q:ℝ))/((q:ℝ)*(C:ℝ))
        - ((a:ℝ)+(l₂:ℝ)*(q:ℝ))/((q:ℝ)*(C:ℝ)) = ((l₁:ℝ) - (l₂:ℝ))/(C:ℝ) := by
      field_simp; ring
    rw [hsub, abs_div, abs_of_pos hcpos]
    have hle1 : (1:ℝ) ≤ |(l₁:ℝ) - (l₂:ℝ)| := by
      have h1 : (1:ℤ) ≤ |l₁ - l₂| := Int.one_le_abs (sub_ne_zero.mpr hne)
      exact_mod_cast h1
    rw [lt_div_iff₀ hcpos]
    linarith
  -- every active window index lies in `[-1, C]`
  have hmem : ∀ l : ℤ, |θ - ((a:ℝ)+(l:ℝ)*(q:ℝ))/((q:ℝ)*(C:ℝ))| ≤ r →
      l ∈ Finset.Icc (-1:ℤ) (C:ℤ) := by
    intro l hl
    have hbound := abs_le.mp hl
    have hfreq : (C:ℝ) * (((a:ℝ) + (l:ℝ)*(q:ℝ))/((q:ℝ)*(C:ℝ)))
        = (a:ℝ)/(q:ℝ) + (l:ℝ) := by field_simp
    have hann : (0:ℝ) ≤ (a:ℝ)/(q:ℝ) := by positivity
    have han1 : (a:ℝ)/(q:ℝ) < 1 := by rw [div_lt_one hqpos]; exact_mod_cast ha
    have hct1 : (C:ℝ) * θ < (C:ℝ) := by
      calc (C:ℝ) * θ < (C:ℝ) * 1 := mul_lt_mul_of_pos_left hθ1 hcpos
        _ = (C:ℝ) := mul_one _
    rw [Finset.mem_Icc]
    constructor
    · have hlow : (-3/2:ℝ) < (l:ℝ) := by
        have h2 : (C:ℝ) * (((a:ℝ) + (l:ℝ)*(q:ℝ))/((q:ℝ)*(C:ℝ)))
            ≥ (C:ℝ) * (θ - r) := mul_le_mul_of_nonneg_left (by linarith [hbound.1]) hcpos.le
        nlinarith [hcr, hct1, hann, han1]
      by_contra hlt
      push_neg at hlt
      have h2 : l ≤ -2 := by omega
      have h3 : (l:ℝ) ≤ -2 := by exact_mod_cast h2
      linarith
    · have hup : (l:ℝ) < (C:ℝ) + 1/2 := by
        have h2 : (C:ℝ) * (((a:ℝ) + (l:ℝ)*(q:ℝ))/((q:ℝ)*(C:ℝ)))
            ≤ (C:ℝ) * (θ + r) := mul_le_mul_of_nonneg_left (by linarith [hbound.2]) hcpos.le
        nlinarith [hfreq, hcr, hct1, hann]
      by_contra hlt
      push_neg at hlt
      have h2 : (C:ℤ) + 1 ≤ l := by omega
      have h3 : (((C:ℤ) + 1 : ℤ) : ℝ) ≤ (l : ℝ) := by exact_mod_cast h2
      push_cast at h3
      linarith
  let F : ℤ → ℝ := fun j => ((a : ℝ) + (j : ℝ) * (q : ℝ)) / ((q : ℝ) * (C : ℝ))
  let W : ℤ → ℂ := fun j => w ((a : ℤ) + j * (q : ℤ))
  change (∑ l ∈ Finset.Icc (-1 : ℤ) C, W l * (if |θ - F l| ≤ r then (1:ℂ) else 0))
      = ∑ s ∈ Finset.range C, W (s : ℤ) * perNbhd (F (s : ℤ)) r θ
  have hsepF : ∀ l₁ l₂ : ℤ, l₁ ≠ l₂ → 2 * r < |F l₁ - F l₂| := fun l₁ l₂ hne => hsep l₁ l₂ hne
  have hmemF : ∀ l : ℤ, |θ - F l| ≤ r → l ∈ Finset.Icc (-1:ℤ) (C:ℤ) := fun l hl => hmem l hl
  by_cases h : ∃ j : ℤ, |θ - F j| ≤ r
  · obtain ⟨l₀, hl₀⟩ := h
    have hmem₀ := hmemF l₀ hl₀
    have huniq : ∀ j : ℤ, |θ - F j| ≤ r → j = l₀ := by
      intro j hj
      by_contra hne
      have h1 := hsepF j l₀ hne
      have htri : |F j - F l₀| ≤ 2*r := by
        calc |F j - F l₀| ≤ |F j - θ| + |θ - F l₀| := abs_sub_le _ _ _
          _ = |θ - F j| + |θ - F l₀| := by rw [abs_sub_comm (F j) θ]
          _ ≤ r + r := add_le_add hj hl₀
          _ = 2*r := by ring
      linarith
    let s₀ : ℕ := (l₀ % (C:ℤ)).toNat
    have hCne : (C:ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hC)
    have hs₀nn : 0 ≤ l₀ % (C:ℤ) := Int.emod_nonneg _ hCne
    have hs₀eq : (s₀:ℤ) = l₀ % (C:ℤ) := Int.toNat_of_nonneg hs₀nn
    have hs₀lt : s₀ < C := by
      have h1 : l₀ % (C:ℤ) < (C:ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hC)
      exact (Int.toNat_lt hs₀nn).mpr h1
    set t : ℤ := l₀ / (C:ℤ) with ht
    have hl₀eq : l₀ = (s₀:ℤ) + (C:ℤ)*t := by
      have h := Int.emod_add_mul_ediv l₀ (C:ℤ)
      rw [← hs₀eq, ← ht] at h
      exact h.symm
    have hL : (∑ l ∈ Finset.Icc (-1 : ℤ) C, W l * (if |θ - F l| ≤ r then (1:ℂ) else 0))
        = W l₀ := by
      rw [Finset.sum_eq_single l₀]
      · rw [if_pos hl₀, mul_one]
      · intro b hb hbne
        rw [if_neg (fun hbact => hbne (huniq b hbact)), mul_zero]
      · intro hnot; exact absurd hmem₀ hnot
    have hR : (∑ s ∈ Finset.range C, W (s:ℤ) * perNbhd (F (s:ℤ)) r θ) = W l₀ := by
      rw [Finset.sum_eq_single s₀]
      · have hper : perNbhd (F (s₀:ℤ)) r θ = 1 := by
          rw [perNbhd_eq_one]
          refine ⟨-t, ?_⟩
          have hl0R : (l₀:ℝ) = (s₀:ℝ) + (C:ℝ)*((t:ℤ):ℝ) := by
            have hh := congrArg (fun z : ℤ => (z:ℝ)) hl₀eq
            push_cast at hh
            linarith
          have key : θ + ((-t : ℤ) : ℝ) - F (s₀:ℤ) = θ - F l₀ := by
            dsimp only [F]
            rw [hl0R]
            push_cast
            field_simp
            ring
          rw [key]
          exact hl₀
        rw [hper, mul_one]
        change w ((a:ℤ) + (s₀:ℤ) * (q:ℤ)) = w ((a:ℤ) + l₀ * (q:ℤ))
        rw [show (a:ℤ) + l₀ * (q:ℤ)
            = ((a:ℤ) + (s₀:ℤ) * (q:ℤ)) + t * (((q*C:ℕ):ℤ)) by
          rw [hl₀eq]; push_cast; ring, hw]
      · intro s hs hsne
        have hper : perNbhd (F (s:ℤ)) r θ = 0 := by
          by_contra h0
          have h1 : perNbhd (F (s:ℤ)) r θ = 1 := perNbhd_ne_zero h0
          change perNbhd (((a:ℝ)+(s:ℝ)*(q:ℝ))/((q:ℝ)*(C:ℝ))) r θ = 1 at h1
          rw [hdict s] at h1
          obtain ⟨m, hm⟩ := h1
          have hm' : |θ - F ((s:ℤ) - m*(C:ℤ))| ≤ r := by
            simp only [F]
            simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] using hm
          have hjeq : (s:ℤ) - m*(C:ℤ) = l₀ := huniq _ hm'
          have hdiff : (s:ℤ) - (s₀:ℤ) = m*(C:ℤ) + (C:ℤ)*t := by linarith [hjeq, hl₀eq]
          have hdvd : (C:ℤ) ∣ (s:ℤ) - (s₀:ℤ) := ⟨m + t, by rw [hdiff]; ring⟩
          have hslt : (s:ℤ) < (C:ℤ) := by exact_mod_cast (Finset.mem_range.mp hs)
          have hs₀lt' : (s₀:ℤ) < (C:ℤ) := by exact_mod_cast hs₀lt
          have hmod : (s:ℤ) % (C:ℤ) = (s₀:ℤ) % (C:ℤ) := by
            rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
            exact Int.emod_eq_zero_of_dvd hdvd
          rw [Int.emod_eq_of_lt (Int.natCast_nonneg s) hslt,
              Int.emod_eq_of_lt (Int.natCast_nonneg s₀) hs₀lt'] at hmod
          exact hsne (by exact_mod_cast hmod)
        rw [hper, mul_zero]
      · intro hnot
        exact absurd (Finset.mem_range.mpr hs₀lt) hnot
    rw [hL, hR]
  · have hL : (∑ l ∈ Finset.Icc (-1 : ℤ) C, W l * (if |θ - F l| ≤ r then (1:ℂ) else 0)) = 0 := by
      refine Finset.sum_eq_zero (fun l hl => ?_)
      rw [if_neg (fun hh => h ⟨l, hh⟩), mul_zero]
    have hR : (∑ s ∈ Finset.range C, W (s:ℤ) * perNbhd (F (s:ℤ)) r θ) = 0 := by
      refine Finset.sum_eq_zero (fun s hs => ?_)
      have hper : perNbhd (F (s:ℤ)) r θ = 0 := by
        by_contra h0
        have h1 : perNbhd (F (s:ℤ)) r θ = 1 := perNbhd_ne_zero h0
        change perNbhd (((a:ℝ)+(s:ℝ)*(q:ℝ))/((q:ℝ)*(C:ℝ))) r θ = 1 at h1
        rw [hdict s] at h1
        obtain ⟨m, hm⟩ := h1
        have hm' : |θ - F ((s:ℤ) - m*(C:ℤ))| ≤ r := by
          simp only [F]
          simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] using hm
        exact h ⟨(s:ℤ) - m*(C:ℤ), hm'⟩
      rw [hper, mul_zero]
    rw [hL, hR]


/-! ## The general-dilation sharp collapse -/

/-- The sharp window `|D (θ - (a/q + l)/c)| ≤ 1` rewritten at the radius `D⁻¹`. -/
private lemma sharp_indicator_D (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) {q : ℕ}
    (hq : 1 ≤ q) (a : ℕ) (l : ℤ) (D : ℝ) (hD : 0 < D) (θ : ℝ) :
    (if |D * (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ)))| ≤ 1
        then (1:ℂ) else 0)
      = (if |θ - (((a:ℝ) + (l:ℝ)*(q:ℝ))/((q:ℝ)*(P.leadingCoeff:ℝ)))| ≤ D⁻¹
          then (1:ℂ) else 0) := by
  have hc0 : (0:ℝ) < (P.leadingCoeff:ℝ) := by exact_mod_cast hc
  have hcne : (P.leadingCoeff:ℝ) ≠ 0 := ne_of_gt hc0
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hqne : (q:ℝ) ≠ 0 := ne_of_gt hq0
  have hXY : (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ))
      = (((a:ℝ) + (l:ℝ)*(q:ℝ)) / ((q:ℝ)*(P.leadingCoeff:ℝ))) := by
    field_simp
  have hiff : (|D * (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ)))| ≤ 1)
      ↔ (|θ - (((a:ℝ) + (l:ℝ)*(q:ℝ))/((q:ℝ)*(P.leadingCoeff:ℝ)))| ≤ D⁻¹) := by
    rw [hXY, abs_mul, abs_of_pos hD]
    constructor
    · intro h
      rw [inv_eq_one_div, le_div_iff₀ hD]
      linarith
    · intro h
      rw [inv_eq_one_div, le_div_iff₀ hD] at h
      linarith
  by_cases h : |D * (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ)))| ≤ 1
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun hh => h (hiff.mpr hh))]

/-- **The weighted per-`(q,a)` collapse of the sharp core at an arbitrary dilation.**  Same as
`Work.BourgainPlan.Maximal.polyWeightedBlock_collapse` with `polyDil P k` replaced by an arbitrary
positive dilation `D`. -/
private lemma polyWeightedBlock_collapseD (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) {q a : ℕ}
    (hq : 1 ≤ q) (ha : a < q) (D : ℝ) (hD : 0 < D)
    (hsmall : D⁻¹ < 1 / (2 * (P.leadingCoeff : ℝ))) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
        starRingEnd ℂ (polyWeight P (q * P.leadingCoeff.toNat) ((a:ℤ) + l * (q:ℤ))) *
          (if |D * (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ)))| ≤ 1
            then (1:ℂ) else 0))
      = ∑ s ∈ Finset.range (P.leadingCoeff.toNat),
          starRingEnd ℂ (polyWeight P (q * P.leadingCoeff.toNat) ((a:ℤ) + (s:ℤ)*(q:ℤ))) *
            perNbhd (((a:ℝ) + (s:ℝ)*(q:ℝ)) / ((q:ℝ)*(P.leadingCoeff:ℝ))) D⁻¹ θ := by
  have hCc : (P.leadingCoeff.toNat : ℤ) = P.leadingCoeff :=
    Int.toNat_of_nonneg (le_of_lt hc)
  have hCcR : ((P.leadingCoeff.toNat : ℕ) : ℝ) = (P.leadingCoeff : ℝ) := by
    exact_mod_cast hCc
  have hCpos : 0 < P.leadingCoeff.toNat := by
    have h : (0:ℤ) < (P.leadingCoeff.toNat : ℤ) := by
      rw [Int.toNat_of_nonneg (le_of_lt hc)]; exact hc
    exact_mod_cast h
  have hcr : ((P.leadingCoeff.toNat : ℕ) : ℝ) * D⁻¹ < 1/2 := by
    rw [hCcR]
    have h := hsmall
    rw [lt_div_iff₀ (by positivity : (0:ℝ) < 2*(P.leadingCoeff:ℝ))] at h
    nlinarith
  have hw : ∀ b m : ℤ,
      (fun j => starRingEnd ℂ (polyWeight P (q * P.leadingCoeff.toNat) j))
        (b + m * ((q * P.leadingCoeff.toNat : ℕ) : ℤ))
      = (fun j => starRingEnd ℂ (polyWeight P (q * P.leadingCoeff.toNat) j)) b := by
    intro b m
    exact congrArg (starRingEnd ℂ) (polyWeight_add_modulus_mul P (q * P.leadingCoeff.toNat) b m)
  have hmain := weightedCollapse_gen (P.leadingCoeff.toNat) q
    (fun j => starRingEnd ℂ (polyWeight P (q * P.leadingCoeff.toNat) j)) a hCpos hq ha hw
    D⁻¹ θ hcr hθ0 hθ1
  rw [show (∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
        starRingEnd ℂ (polyWeight P (q * P.leadingCoeff.toNat) ((a:ℤ) + l * (q:ℤ))) *
          (if |D * (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ)))| ≤ 1
            then (1:ℂ) else 0))
      = ∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
          starRingEnd ℂ (polyWeight P (q * P.leadingCoeff.toNat) ((a:ℤ) + l * (q:ℤ))) *
            (if |θ - (((a:ℝ) + (l:ℝ)*(q:ℝ))/((q:ℝ)*(P.leadingCoeff:ℝ)))| ≤ D⁻¹
              then (1:ℂ) else 0) from
    Finset.sum_congr rfl (fun l _ => by rw [sharp_indicator_D P hc hq a l D hD θ])]
  simpa only [hCc, hCcR] using hmain
/-- **Injectivity of the graph of `polyBlockT`.**  Distinct triples `((q,a),s)` with
`(q,a) ∈ blockPair m`, `s < c` give distinct pairs (frequency, weight): if the frequencies agree
then `a/q + s = a'/q' + s'`, so `a/q - a'/q'` is an integer in `(-1,1)`, hence `0`, so
coprimality forces `(q,a) = (q',a')` and then `s = s'`. -/
private lemma polyBlockT_pair_injOn (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) (m : ℕ) :
    Set.InjOn (fun p : (ℕ × ℕ) × ℕ =>
      (((p.1.2 : ℝ) + (p.2 : ℝ) * (p.1.1 : ℝ)) / ((p.1.1 : ℝ) * (P.leadingCoeff : ℝ)),
        starRingEnd ℂ (polyWeight P (p.1.1 * P.leadingCoeff.toNat)
          ((p.1.2 : ℤ) + (p.2 : ℤ) * (p.1.1 : ℤ)))))
      ↑(blockPair m ×ˢ Finset.range (P.leadingCoeff.toNat)) := by
  intro x hx y hy hxy
  rw [Finset.mem_coe, Finset.mem_product] at hx hy
  obtain ⟨⟨q₁, a₁⟩, s₁⟩ := x
  obtain ⟨⟨q₂, a₂⟩, s₂⟩ := y
  obtain ⟨hxb, hs₁⟩ := hx
  obtain ⟨hyb, hs₂⟩ := hy
  obtain ⟨hq₁, _, ha₁, hg₁⟩ := mem_blockPair.mp hxb
  obtain ⟨hq₂, _, ha₂, hg₂⟩ := mem_blockPair.mp hyb
  rw [Finset.mem_range] at hs₁ hs₂
  have hq₁p : (0:ℝ) < (q₁:ℝ) := by exact_mod_cast (lt_of_lt_of_le (Nat.two_pow_pos m) hq₁)
  have hq₂p : (0:ℝ) < (q₂:ℝ) := by exact_mod_cast (lt_of_lt_of_le (Nat.two_pow_pos m) hq₂)
  have hq₁z : 0 < q₁ := lt_of_lt_of_le (Nat.two_pow_pos m) hq₁
  have hq₂z : 0 < q₂ := lt_of_lt_of_le (Nat.two_pow_pos m) hq₂
  have hcpos : (0:ℝ) < (P.leadingCoeff:ℝ) := by exact_mod_cast hc
  have hcne : (P.leadingCoeff:ℝ) ≠ 0 := ne_of_gt hcpos
  have hfreq := congrArg Prod.fst hxy
  simp only at hfreq
  have hkey : (a₁:ℝ)/q₁ - (a₂:ℝ)/q₂ = (s₂:ℝ) - (s₁:ℝ) := by
    have h := hfreq
    field_simp at h
    field_simp
    linarith [h]
  have hbnd₁ : (0:ℝ) ≤ (a₁:ℝ)/q₁ := by positivity
  have hbnd₁' : (a₁:ℝ)/q₁ < 1 := by rw [div_lt_one hq₁p]; exact_mod_cast ha₁
  have hbnd₂ : (0:ℝ) ≤ (a₂:ℝ)/q₂ := by positivity
  have hbnd₂' : (a₂:ℝ)/q₂ < 1 := by rw [div_lt_one hq₂p]; exact_mod_cast ha₂
  have hlt : |(s₂:ℝ) - (s₁:ℝ)| < 1 := by
    rw [← hkey, abs_lt]
    constructor <;> linarith
  have hs12 : s₁ = s₂ := by
    have hz : |(((s₂:ℤ) - (s₁:ℤ) : ℤ) : ℝ)| < 1 := by
      simpa only [Int.cast_sub, Int.cast_natCast] using hlt
    have h2 : |(s₂:ℤ) - (s₁:ℤ)| < 1 := by
      rw [← Int.cast_abs] at hz
      exact_mod_cast hz
    rw [abs_lt] at h2
    omega
  have hfr : (a₁:ℝ)/q₁ = (a₂:ℝ)/q₂ := by
    have h : (s₂:ℝ) - (s₁:ℝ) = 0 := by rw [← hs12]; simp
    linarith [hkey]
  obtain ⟨hqeq, haeq⟩ := frac_eq_of_coprime hq₁z hq₂z
    (Nat.coprime_iff_gcd_eq_one.mpr hg₁) (Nat.coprime_iff_gcd_eq_one.mpr hg₂) ha₁ ha₂ hfr
  subst hqeq
  subst haeq
  subst hs12
  rfl


/-- **The general-dilation sharp core is a weighted periodised-neighbourhood sum.** -/
private theorem polyBlockCore_gen (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) {m : ℕ}
    (D : ℝ) (hD : 0 < D)
    (hsmall : D⁻¹ < 1 / (2 * (P.leadingCoeff : ℝ))) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (∑ i ∈ blockPair m, ∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
        starRingEnd ℂ (polyWeight P (i.1 * P.leadingCoeff.toNat) ((i.2 : ℤ) + l * (i.1 : ℤ))) *
          (if |D * (θ - (((i.2 : ℝ)/(i.1 : ℝ) + (l : ℝ)) / (P.leadingCoeff : ℝ)))| ≤ 1
            then (1:ℂ) else 0))
      = ∑ p ∈ polyBlockT P m, p.2 * perNbhd p.1 D⁻¹ θ := by
  rw [polyBlockT, Finset.sum_image (polyBlockT_pair_injOn P hc m)]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  obtain ⟨hq, _, ha, _⟩ := mem_blockPair.mp hi
  have hq' : 1 ≤ i.1 := by
    have : 1 ≤ 2^m := Nat.one_le_two_pow
    omega
  exact polyWeightedBlock_collapseD P hc hq' ha D hD hsmall θ hθ0 hθ1

/-- The conjugate of a single arbitrary-scale sharp term, expanded into weight times the sharp
indicator. -/
private lemma star_polySharpTermN (P : Polynomial ℤ) (q a : ℕ) (l : ℤ) (N : ℕ) (θ : ℝ) :
    starRingEnd ℂ (polySharpTermN P q a l N θ)
      = starRingEnd ℂ (polyWeight P (q * P.leadingCoeff.toNat) ((a:ℤ) + l * (q:ℤ))) *
        (if |polyDilN P N * (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ)))| ≤ 1
          then (1:ℂ) else 0) := by
  rw [polySharpTermN, map_mul]
  congr 1
  by_cases h : |polyDilN P N * (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ)))| ≤ 1
  · rw [if_pos h]
    exact map_one _
  · rw [if_neg h]
    exact map_zero _

/-- The arbitrary-scale sharp core of the `m`-th denominator block is the weighted
periodised-neighbourhood sum over the (frequency, weight) family `polyBlockT P m`. -/
theorem polyBlockCoreN_eq_weighted (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff)
    (hd : 2 ≤ P.natDegree) {m N : ℕ} (hN : 1 ≤ N)
    (hsmall : (Work.BourgainPlan.Oscillation.polyDilN P N)⁻¹ < 1 / (2 * (P.leadingCoeff : ℝ)))
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    Work.BourgainPlan.Oscillation.polyBlockCoreN P m N θ
      = ∑ p ∈ Work.BourgainPlan.Maximal.polyBlockT P m,
          p.2 * Commons.Analysis.ExponentialSums.perNbhd p.1
            ((Work.BourgainPlan.Oscillation.polyDilN P N)⁻¹) θ := by
  have hD : 0 < polyDilN P N := by
    rw [polyDilN]
    exact pow_pos (by exact_mod_cast (by omega : 0 < N)) _
  rw [polyBlockCoreN]
  refine Eq.trans ?_ (polyBlockCore_gen P hc (polyDilN P N) hD hsmall θ hθ0 hθ1)
  refine Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun l hl => ?_))
  exact star_polySharpTermN P i.1 i.2 l N θ

end

end Work.BourgainPlan.Oscillation
