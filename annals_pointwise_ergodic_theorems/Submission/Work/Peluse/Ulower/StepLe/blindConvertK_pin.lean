/-
# The pinning half of `StepLe.blindConvertK`: dense constancy of the mixed phase

`Work.Peluse.Ulower.StepLe.blindConvertK` consumes a phase family `β` whose *Gowers transform*
(`mixedPhase β k = ∑_ω (-1)^{|ω|} β k.1 (ω ? k.2.1 : k.2.2)`) is pinned to a single value `v₀` on a
dense sub-family `H₂'` of `H₂` -- that is what makes the phases `blindPhase β h v₀ u v i₀ i` of
`blindConvertK_lowrank` *blind* (via `sum_blindPhase` and `blindPhase_blind`).

This file proves that pinning (`blindConvertK_pin`), i.e. the counting/rounding step 5 of the
assembly plan (`NOTES_blindConvertK_SESSION.md` §6, item 6 together with `pinValues`).  The
hypotheses say that the mixed phases live in the grid `(1/T)ℤ` (`hgr`, after the rounding
`aggr_round`), are `≤ 2^σ` in modulus (`hbound`), and are each `ε`-close to a rational with
denominator `≤ T₀` (`hpin`, the conclusion of the major-arc step `majorarc_pin`).  The conclusion is
a dense sub-family on which the transform is *exactly* constant.

The bookkeeping is done in two pigeonholes:

* the **fractional part** `Int.fract (mixedPhase β k)` is a grid value `m/T` with `0 ≤ m ≤ T`, and
  the pinning hypothesis descends to it (`distInt` is insensitive to adding an integer), so
  `pinValues` (`gridPinningCount` at `σ = 0`) extracts a sub-family carrying a fraction
  `4 (T₀+1) T₀ (⌊2εT⌋+1)` of `H₂` on which the fractional part is constant;
* the **integer part** `⌊mixedPhase β k⌋` lies in `[-(2^σ), 2^σ]` by `hbound`, so it takes at most
  `2^{σ+1}+1 ≤ 2^{σ+1}+3` values; pigeonholing (`exists_const_fiber`) makes it constant at the cost
  of that factor.

On the intersection the mixed phase is `fraction + integer part`, constant; and
`gowersDiff β k.2.1 k.1 k.2.2 = (-1)^σ · mixedPhase β k` (`gowersDiff_eq_sign_mixedPhase`) is then
constant too, which is exactly the form `fibrePairs`/`sum_blindPhase` consume.
-/

import Mathlib
import Submission.Work.Peluse.Ulower.StepLe.blindConvertK_grid
import Submission.Work.Peluse.Ulower.StepLe.pinValues

namespace Work.Peluse.Ulower.StepLe

noncomputable section

open scoped BigOperators

/-- **The fractional part of an integer multiple of `1/T` is a grid value `m/T`, `0 ≤ m ≤ T`.**
Write `m = T·q + r` with `r = m % T ∈ [0,T)`; then `m/T = q + r/T` with `q` an integer, so the
fractional part of `m/T` is `r/T` (and `r/T ∈ [0,1)`). -/
lemma fract_div_grid {T : ℕ} (hT : 1 ≤ T) (m : ℤ) :
    ∃ m' : ℕ, m' ≤ T ∧ Int.fract ((m : ℝ) / (T : ℝ)) = (m' : ℝ) / (T : ℝ) := by
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hTposZ : (0 : ℤ) < (T : ℤ) := by exact_mod_cast hT
  have hTne : (T : ℤ) ≠ 0 := ne_of_gt hTposZ
  have hm : (T : ℤ) * (m / (T : ℤ)) + m % (T : ℤ) = m := Int.mul_ediv_add_emod m (T : ℤ)
  have hrnn : 0 ≤ m % (T : ℤ) := Int.emod_nonneg m hTne
  have hrlt : m % (T : ℤ) < (T : ℤ) := Int.emod_lt_of_pos m hTposZ
  have hkey : (m : ℝ) / (T : ℝ)
      = ((m / (T : ℤ) : ℤ) : ℝ) + ((m % (T : ℤ) : ℤ) : ℝ) / (T : ℝ) := by
    have h1 : (m : ℝ) = (T : ℝ) * ((m / (T:ℤ) : ℤ) : ℝ) + ((m % (T:ℤ) : ℤ) : ℝ) := by
      have h2 : (((T:ℤ) * (m / (T:ℤ)) + m % (T:ℤ) : ℤ) : ℝ) = (m:ℝ) := by rw [hm]
      push_cast at h2 ⊢
      linarith
    field_simp
    linarith
  refine ⟨(m % (T:ℤ)).toNat, ?_, ?_⟩
  · have h1 : ((m % (T:ℤ)).toNat : ℤ) = m % (T:ℤ) := Int.toNat_of_nonneg hrnn
    omega
  · rw [hkey, Int.fract_intCast_add]
    have hfract : Int.fract (((m % (T:ℤ) : ℤ) : ℝ) / (T:ℝ))
        = ((m % (T:ℤ) : ℤ) : ℝ) / (T:ℝ) := by
      rw [Int.fract_eq_self]
      constructor
      · positivity
      · rw [div_lt_one hTpos]
        exact_mod_cast hrlt
    rw [hfract]
    have hcast : (((m % (T:ℤ)).toNat : ℕ) : ℝ) = (((m % (T:ℤ)) : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hrnn
    rw [hcast]

/-- **The pinning hypothesis descends to the fractional part.**  If `distInt (t·x) ≤ ε` with
`1 ≤ t`, then `Int.fract x` is `ε`-close to a rational `a/t`: take `n = round (t·x)`, so that
`|t·x - n| ≤ ε`, and `a = n - t·⌊x⌋`; then `fract x - a/t = x - n/t` and `|x - n/t| ≤ ε/t ≤ ε`. -/
lemma exists_rat_approx_fract {x ε : ℝ} {t : ℕ} (ht : 1 ≤ t) (hε : 0 ≤ ε)
    (h : Work.Peluse.distInt ((t : ℝ) * x) ≤ ε) :
    ∃ a : ℤ, |Int.fract x - (a : ℝ) / (t : ℝ)| ≤ ε := by
  have htpos : (0:ℝ) < (t:ℝ) := by exact_mod_cast ht
  refine ⟨round ((t:ℝ) * x) - (t : ℤ) * ⌊x⌋, ?_⟩
  have hround : |(t:ℝ) * x - ((round ((t:ℝ)*x) : ℤ) : ℝ)| ≤ ε := by
    simpa [Work.Peluse.distInt] using h
  have hdiff : Int.fract x - (((round ((t:ℝ)*x) - (t:ℤ) * ⌊x⌋ : ℤ)) : ℝ) / (t:ℝ)
      = x - ((round ((t:ℝ)*x) : ℤ) : ℝ) / (t:ℝ) := by
    rw [show Int.fract x = x - ((⌊x⌋ : ℤ) : ℝ) from rfl]
    push_cast
    field_simp
    ring
  rw [hdiff]
  have h2 : |x - ((round ((t:ℝ)*x) : ℤ) : ℝ) / (t:ℝ)|
      = |(t:ℝ) * x - ((round ((t:ℝ)*x) : ℤ) : ℝ)| / (t:ℝ) := by
    rw [show x - ((round ((t:ℝ)*x) : ℤ) : ℝ) / (t:ℝ)
        = ((t:ℝ) * x - ((round ((t:ℝ)*x) : ℤ) : ℝ)) / (t:ℝ) by
      field_simp]
    rw [abs_div, abs_of_pos htpos]
  rw [h2]
  have h3 : |(t:ℝ) * x - ((round ((t:ℝ)*x) : ℤ) : ℝ)| / (t:ℝ) ≤ ε / (t:ℝ) :=
    div_le_div_of_nonneg_right hround (le_of_lt htpos)
  have h4 : ε / (t:ℝ) ≤ ε := div_le_self hε (by exact_mod_cast ht)
  linarith

/-- **Pigeonhole over a function.**  A finite set has a sub-family carrying a fraction `1/|image|`
of its elements on which `f` is constant. -/
lemma exists_const_fiber {ι β : Type*} [DecidableEq ι] [DecidableEq β] [Nonempty β]
    (H : Finset ι) (f : ι → β) :
    ∃ H' ⊆ H, (H.card : ℝ) ≤ ((H.image f).card : ℝ) * (H'.card : ℝ) ∧
      ∃ c, ∀ k ∈ H', f k = c := by
  classical
  by_cases hH : H = ∅
  · refine ⟨∅, Finset.empty_subset H, ?_, Classical.arbitrary β, ?_⟩
    · simp [hH]
    · intro k hk; exact absurd hk (Finset.notMem_empty k)
  · obtain ⟨k₀, hk₀⟩ := Finset.nonempty_iff_ne_empty.mpr hH
    obtain ⟨c, -, hmax⟩ := Finset.exists_max_image (H.image f)
      (fun b => (H.filter (fun k => f k = b)).card) ⟨f k₀, Finset.mem_image_of_mem f hk₀⟩
    refine ⟨H.filter (fun k => f k = c), Finset.filter_subset _ _, ?_, c, ?_⟩
    · have hsum := Finset.card_eq_sum_card_fiberwise (s := H) (t := H.image f) (f := f)
        (fun k hk => Finset.mem_image_of_mem f hk)
      have hle : H.card ≤ (H.image f).card * (H.filter (fun k => f k = c)).card := by
        rw [hsum]
        calc ∑ b ∈ H.image f, (H.filter fun k => f k = b).card
            ≤ ∑ _b ∈ H.image f, (H.filter fun k => f k = c).card :=
              Finset.sum_le_sum (fun b hb => hmax b hb)
          _ = (H.image f).card * (H.filter fun k => f k = c).card := by
              rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
      exact_mod_cast hle
    · intro k hk; exact (Finset.mem_filter.mp hk).2

/-- **How many integer parts an `2^σ`-bounded family can have.**  If `|f k| ≤ 2^σ` on `H`, the
floors `⌊f k⌋` take at most `2^{σ+1}+1 ≤ 2^{σ+1}+3` values (they lie in the integer interval
`[-(2^σ), 2^σ]`). -/
lemma image_floor_card_le {σ : ℕ} {ι : Type*} [DecidableEq ι]
    (H : Finset ι) (f : ι → ℝ) (hb : ∀ k ∈ H, |f k| ≤ (2:ℝ)^σ) :
    ((H.image (fun k => ⌊f k⌋)).card : ℝ) ≤ (2:ℝ)^(σ+1) + 3 := by
  have hsub : H.image (fun k => ⌊f k⌋) ⊆ Finset.Icc (-((2:ℤ)^σ)) ((2:ℤ)^σ) := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hb k hk)
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · rw [Int.le_floor]
      have hcast : (((-(2:ℤ)^σ : ℤ)) : ℝ) = -((2:ℝ)^σ) := by push_cast; ring
      rw [hcast]; linarith
    · rw [Int.floor_le_iff]
      have hcast : (((2:ℤ)^σ : ℤ) : ℝ) = (2:ℝ)^σ := by push_cast; ring
      rw [hcast]; linarith
  have hcard : (Finset.Icc (-((2:ℤ)^σ)) ((2:ℤ)^σ)).card = 2^(σ+1) + 1 := by
    rw [Int.card_Icc]
    have h1 : ((2:ℤ)^σ + 1 - -((2:ℤ)^σ)) = (((2:ℕ)^(σ+1) + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [h1, Int.toNat_natCast]
  have hle : (H.image (fun k => ⌊f k⌋)).card ≤ 2^(σ+1) + 1 := by
    rw [← hcard]; exact Finset.card_le_card hsub
  have hleR : ((H.image (fun k => ⌊f k⌋)).card : ℝ) ≤ ((2:ℕ)^(σ+1) + 1 : ℕ) := by
    exact_mod_cast hle
  have h2 : (((2:ℕ)^(σ+1) + 1 : ℕ) : ℝ) = (2:ℝ)^(σ+1) + 1 := by push_cast; ring
  rw [h2] at hleR
  linarith

/-- **The pinning of the mixed phase.**  If every mixed phase of `β` on `H₂` is a grid value
`m/T` of modulus at most `2^σ` and is `ε`-close to a rational with denominator `≤ T₀`, then a
sub-family of density `1/((2^{σ+1}+3)·4(T₀+1)T₀(⌊2εT⌋+1))` carries a *constant* Gowers transform
`gowersDiff β k.2.1 k.1 k.2.2`.  This is the step that makes the phases `blindPhase β h v₀ u v i₀ i`
blind (`blindConvertK_lowrank`). -/
theorem blindConvertK_pin {σ D : ℕ} (hD : 1 ≤ D) {T T₀ : ℕ} (hT : 1 ≤ T) {ε : ℝ} (hε : 0 ≤ ε)
    (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ)
    (H₂ : Finset ((Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ)))
    (hgr : ∀ k ∈ H₂, ∃ m : ℤ, mixedPhase β k = (m : ℝ) / (T : ℝ))
    (hpin : ∀ k ∈ H₂, ∃ t : ℕ, 1 ≤ t ∧ t ≤ T₀ ∧ distInt ((t : ℝ) * mixedPhase β k) ≤ ε)
    (hbound : ∀ k ∈ H₂, |mixedPhase β k| ≤ (2 : ℝ) ^ σ) :
    ∃ H₂' ⊆ H₂,
      (H₂.card : ℝ) ≤ (((2 : ℝ) ^ (σ + 1) + 3) *
        (4 * ((T₀ + 1) * T₀) * (Nat.floor (2 * ε * (T : ℝ)) + 1))) * (H₂'.card : ℝ) ∧
      ∃ v₀ : ℝ, ∀ k ∈ H₂', gowersDiff β k.2.1 k.1 k.2.2 = v₀ := by
  classical
  -- the fractional part is a grid value `m/T`, `0 ≤ m ≤ T`
  have hgr_f : ∀ k ∈ H₂, ∃ m : ℕ, m ≤ T ∧ Int.fract (mixedPhase β k) = (m : ℝ) / (T : ℝ) := by
    intro k hk
    obtain ⟨m, hm⟩ := hgr k hk
    rw [hm]
    exact fract_div_grid hT m
  -- and the major-arc pinning descends to it
  have hpin_f : ∀ k ∈ H₂, ∃ t : ℕ, 1 ≤ t ∧ t ≤ T₀ ∧
      ∃ a : ℤ, |Int.fract (mixedPhase β k) - (a : ℝ) / (t : ℝ)| ≤ ε := by
    intro k hk
    obtain ⟨t, ht1, htT, hd⟩ := hpin k hk
    exact ⟨t, ht1, htT, exists_rat_approx_fract ht1 hε hd⟩
  -- first pigeonhole: a dense fibre on which the fractional part is constant
  obtain ⟨H₁, hH₁sub, hcard₁, v₀, hv₀⟩ :=
    pinValues hT hε H₂ (fun k => Int.fract (mixedPhase β k)) hgr_f hpin_f
  -- second pigeonhole: a dense fibre of the integer part
  obtain ⟨H₂', hH₂'sub, hcard₂, c, hc⟩ :=
    exists_const_fiber H₁ (fun k => ⌊mixedPhase β k⌋)
  have himg : ((H₁.image (fun k => ⌊mixedPhase β k⌋)).card : ℝ) ≤ (2 : ℝ) ^ (σ + 1) + 3 :=
    image_floor_card_le H₁ (fun k => mixedPhase β k) (fun k hk => hbound k (hH₁sub hk))
  refine ⟨H₂', hH₂'sub.trans hH₁sub, ?_, (-1 : ℝ) ^ σ * (v₀ + (c : ℝ)), ?_⟩
  · have hstep2 : (H₁.card : ℝ) ≤ ((2 : ℝ) ^ (σ + 1) + 3) * (H₂'.card : ℝ) :=
      le_trans hcard₂ (mul_le_mul_of_nonneg_right himg (Nat.cast_nonneg _))
    have hK0 : (0 : ℝ) ≤ 4 * ((T₀ + 1) * T₀) * (Nat.floor (2 * ε * (T : ℝ)) + 1) := by
      positivity
    calc (H₂.card : ℝ)
        ≤ (4 * ((T₀ + 1) * T₀) * (Nat.floor (2 * ε * (T : ℝ)) + 1)) * (H₁.card : ℝ) := hcard₁
      _ ≤ (4 * ((T₀ + 1) * T₀) * (Nat.floor (2 * ε * (T : ℝ)) + 1)) *
            (((2 : ℝ) ^ (σ + 1) + 3) * (H₂'.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hstep2 hK0
      _ = (((2 : ℝ) ^ (σ + 1) + 3) *
            (4 * ((T₀ + 1) * T₀) * (Nat.floor (2 * ε * (T : ℝ)) + 1))) *
            (H₂'.card : ℝ) := by ring
  · -- on `H₂'` the mixed phase is the (constant) fraction plus the (constant) integer part
    intro k hk
    rw [gowersDiff_eq_sign_mixedPhase]
    have h1 : Int.fract (mixedPhase β k) = v₀ := hv₀ k (hH₂'sub hk)
    have h2 : ⌊mixedPhase β k⌋ = c := hc k hk
    have h3 := Int.fract_add_floor (mixedPhase β k)
    rw [h1, h2] at h3
    rw [← h3]

end

end Work.Peluse.Ulower.StepLe
