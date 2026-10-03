/-
# Area 4 (route `Area4_6c`): the clean Moebius core of the §15 coprimality removal

Verbatim copy of §§0–4b of `Submission/Work/FIArea4/A6R/removal6.lean` (the exact Gaussian Möbius
removal `mobiusData6`/`moebiusSplit6` and its elementary bookkeeping), with the imports of the
*sorry-carrying* per-`w` dilation tree dropped (only `Mathlib`, `A6R2.Defs`, `A6Defs`,
`S15prim_defs`, `S15alt.Defs`, `GaussMoebiusCore` and `gaussMoebius_coprime_indicator` are used) and
the declarations moved to the namespace `Work.FIArea4.A4c` so that this module can be imported
alongside `A6R.removal6` without a name clash.

Section 5 of the original (`removal6_of_perW6b`, `removal6`) is *not* copied: it is exactly the
per-`w` dilation decay that the route `Area4_6c` replaces by the divisor-count lemma `CardDvdLe`.
-/
import Mathlib
import Submission.Work.FIArea4.A6R2.Defs
import Submission.Work.FIArea4.A6Defs
import Submission.Work.FIArea4.S15prim_defs
import Submission.Work.S15alt.Defs
import Submission.Work.FIArea4.GaussMoebiusCore
import Submission.Work.FIArea4.gaussMoebius_coprime_indicator

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4.A4c

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 0. Elementary facts about the round-6 bracket -/

/-- `S15Br6` is non-negative. -/
lemma S15Br6_nonneg (Pa : Work.FITop.Params) (X : ℕ) : 0 ≤ Work.FIArea4.S15Br6 Pa X := by
  unfold Work.FIArea4.S15Br6
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  have hN0 : (0 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have h1 : 0 ≤ (X : ℝ) ^ (-(1 : ℝ) / 2) * Pa.N :=
    mul_nonneg (Real.rpow_nonneg hX0 _) hN0
  have h2 : 0 ≤ Pa.N ^ ((1 : ℝ) / 3) * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ ((2 : ℝ) / 3) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hN0 _) (Real.rpow_nonneg hX0 _))
      (Real.rpow_nonneg hN0 _)
  have h3 : 0 ≤ Pa.N ^ ((23 : ℝ) / 24 + (1 : ℝ) / 1000) := Real.rpow_nonneg hN0 _
  linarith

/-! ## 1. The pair-independent Moebius data on `boxN`

(Self-contained copy of `Work.FIArea4.S15psiAux.mobiusData_boxN`, so that this module does not
depend on the wider §15 development.) -/

/-- `0` is not odd (in `ℤ`). -/
lemma not_odd_zero_int : ¬ Odd (0 : ℤ) := by
  rintro ⟨k, hk⟩
  omega

/-- **The only primary unit of `ℤ[i]` is `1`.**  (`ℤ[i]^× = {±1, ±i}` and, of these, only `1`
satisfies the primary condition (5.3)–(5.5) `Re` odd, `Im` even, `Im ≡ Re - 1 (mod 4)`.) -/
lemma isPrimary_unit_eq_one {w : GaussianInt} (h : Work.FIPlan.IsPrimary w)
    (hu : IsUnit w) : w = 1 := by
  rcases (Commons.NumberTheory.GaussianInt.units_classification w).mp hu with
    h1 | h1 | h1 | h1
  · exact h1
  · exfalso
    rw [h1] at h
    have hh : ((0 : ℤ) : ZMod 4) = ((-2 : ℤ) : ZMod 4) :=
      (ZMod.intCast_eq_intCast_iff 0 (-2) 4).mpr (by simpa using h.2.2)
    exact absurd hh (by decide)
  · exfalso
    rw [h1] at h
    exact not_odd_zero_int (by simpa using h.1)
  · exfalso
    rw [h1] at h
    exact not_odd_zero_int (by simpa using h.1)

/-- **The pair-independent Möbius data of the §15 coprimality removal.**

For every primitive box coefficient `β` on `boxN Pa` there are a finite set `W` of Gaussian
integers and a weight `μ` on it such that `‖μ‖ ≤ 1`, `1 ∈ W`, `μ 1 = 1`, every other element of
`W` is a non-zero non-unit, and

  `Σ_{w ∈ W, w ∣ z₁, w ∣ z₂} μ w = [ (z₁,z₂) = 1 ]`

for all `z₁, z₂ ∈ boxN Pa` on which `β` does not vanish — i.e. the coprimality indicator of the
§15 pair sums is the `(W,μ)`-divisor sum, with `(W,μ)` independent of the pair. -/
theorem mobiusData6 (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ)
    (hβ : Work.FIArea4.IsPrimBoxCoeff Pa φ β) :
    ∃ (W : Finset GaussianInt) (μ : GaussianInt → ℂ),
      (∀ w : GaussianInt, ‖μ w‖ ≤ 1) ∧ (1 ∈ W) ∧ (μ 1 = 1) ∧
      (∀ w ∈ W, w ≠ 1 → ¬ IsUnit w ∧ w ≠ 0) ∧
      (∀ z1 ∈ Work.FITop.boxN Pa, ∀ z2 ∈ Work.FITop.boxN Pa, β z1 ≠ 0 → β z2 ≠ 0 →
        Work.S15alt.mobSum W μ z1 z2 = Work.S15alt.coprimeInd z1 z2) := by
  classical
  obtain ⟨μ0, hμ0norm, hμ0one, hμ0ind⟩ := Work.FIArea4.gaussMoebius_coprime_indicator
  -- the weight: the `ℤ[i]`-Möbius function, switched off on the non-primary integers
  let μ : GaussianInt → ℂ := fun w => if Work.FIPlan.IsPrimary w then μ0 w else 0
  have hμeq : ∀ w : GaussianInt, μ w = if Work.FIPlan.IsPrimary w then μ0 w else 0 :=
    fun w => rfl
  -- the box: large enough that every primary divisor of a support point lies in it
  let R : ℤ := 1 + ∑ z ∈ Work.FITop.boxN Pa, (Work.FIPlan.gnorm z : ℤ)
  let W : Finset GaussianInt := (Work.FIPlan.gBox R).filter (fun w => Work.FIPlan.IsPrimary w)
  have hSnonneg : (0 : ℤ) ≤ ∑ z ∈ Work.FITop.boxN Pa, (Work.FIPlan.gnorm z : ℤ) :=
    Finset.sum_nonneg (fun z _ => Int.natCast_nonneg _)
  refine ⟨W, μ, ?_, ?_, ?_, ?_, ?_⟩
  · -- `‖μ w‖ ≤ 1`
    intro w
    rw [hμeq w]
    by_cases hp : Work.FIPlan.IsPrimary w
    · rw [if_pos hp]; exact hμ0norm w
    · rw [if_neg hp, norm_zero]; norm_num
  · -- `1 ∈ W`
    have h1R : (1 : ℤ) ≤ R := by simp only [R]; linarith
    refine Finset.mem_filter.mpr ⟨?_, Work.FIArea4.isPrimary_one⟩
    rw [Work.FIArea4.mem_gBox]
    refine ⟨?_, ?_, ?_, ?_⟩
    · show -R ≤ (1 : ℤ); linarith
    · show (1 : ℤ) ≤ R; linarith
    · show -R ≤ (0 : ℤ); linarith
    · show (0 : ℤ) ≤ R; linarith
  · -- `μ 1 = 1`
    rw [hμeq 1, if_pos Work.FIArea4.isPrimary_one]
    exact hμ0one
  · -- the elements of `W` other than `1` are non-zero non-units
    intro w hw hw1
    have hwprim : Work.FIPlan.IsPrimary w :=
      (Finset.mem_filter.mp (by simpa only [W] using hw)).2
    exact ⟨fun hu => hw1 (isPrimary_unit_eq_one hwprim hu),
      Work.FIArea4.isPrimary_ne_zero hwprim⟩
  · -- the divisor-sum identity
    intro z1 hz1 z2 hz2 hb1 hb2
    have hprim1 : Work.FIPlan.IsPrimary z1 := (hβ.1.2 z1 hb1).1.1
    have hprim2 : Work.FIPlan.IsPrimary z2 := (hβ.1.2 z2 hb2).1.1
    have hod1 : Odd (Work.FIPlan.gnorm z1) := Work.FIArea4.isPrimary_odd_gnorm hprim1
    have hod2 : Odd (Work.FIPlan.gnorm z2) := Work.FIArea4.isPrimary_odd_gnorm hprim2
    obtain ⟨s, hs1, hs2, hsind⟩ := hμ0ind z1 z2 hod1 hod2
    -- every primary divisor of a support point of the box lies in `W`
    have mem_W_of : ∀ {g w : GaussianInt}, g ∈ Work.FITop.boxN Pa → β g ≠ 0 → w ∣ g →
        Work.FIPlan.IsPrimary w → w ∈ W := by
      intro g w hg hbg hwdvd hwprim
      have hgprim : Work.FIPlan.IsPrimary g := (hβ.1.2 g hbg).1.1
      have hgod : Odd (Work.FIPlan.gnorm g) := Work.FIArea4.isPrimary_odd_gnorm hgprim
      have hg0 : g ≠ 0 := Work.FIArea4.odd_gnorm_ne_zero hgod
      have hle : (Work.FIPlan.gnorm g : ℤ) ≤ R := by
        have h1 := Finset.single_le_sum (s := Work.FITop.boxN Pa)
          (f := fun z => (Work.FIPlan.gnorm z : ℤ)) (fun z _ => Int.natCast_nonneg _) hg
        simp only [R]; linarith
      have hmem := Work.FIArea4.primaryDivisor_mem_gBox hg0 hwdvd hwprim
      have hmemR : w ∈ Work.FIPlan.gBox R := by
        rw [Work.FIArea4.mem_gBox] at hmem ⊢
        obtain ⟨h1, h2, h3, h4⟩ := hmem
        exact ⟨le_trans (neg_le_neg hle) h1, le_trans h2 hle,
          le_trans (neg_le_neg hle) h3, le_trans h4 hle⟩
      exact Finset.mem_filter.mpr ⟨hmemR, hwprim⟩
    -- the `(W, μ)`-sum over the primary common divisors is the sum on the set `s` of the indicator
    have hTeq : (W.filter (fun w => w ∣ z1 ∧ w ∣ z2)).filter
        (fun w => Work.FIPlan.IsPrimary w) = s := by
      refine Finset.Subset.antisymm ?_ ?_
      · intro w hw
        obtain ⟨hwdiv, hwp⟩ := Finset.mem_filter.mp hw
        obtain ⟨-, hwd1, hwd2⟩ := Finset.mem_filter.mp hwdiv
        exact hs2 w hwd1 hwd2 hwp
      · intro w hw
        obtain ⟨hwd1, hwd2, hwp⟩ := hs1 w hw
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨mem_W_of hz1 hb1 hwd1 hwp, hwd1, hwd2⟩, hwp⟩
    have hT1 : (∑ w ∈ W, (if w ∣ z1 ∧ w ∣ z2 then μ w else 0))
        = ∑ w ∈ W,
            (if w ∣ z1 ∧ w ∣ z2 then (if Work.FIPlan.IsPrimary w then μ0 w else 0) else 0) :=
      Finset.sum_congr rfl (fun w _ => by rw [hμeq w])
    have hT2 : (∑ w ∈ W,
          (if w ∣ z1 ∧ w ∣ z2 then (if Work.FIPlan.IsPrimary w then μ0 w else 0) else 0))
        = ∑ w ∈ (W.filter (fun w => w ∣ z1 ∧ w ∣ z2)).filter
            (fun w => Work.FIPlan.IsPrimary w), μ0 w := by
      conv_rhs => rw [Finset.sum_filter, Finset.sum_filter]
    show (∑ w ∈ W, (if w ∣ z1 ∧ w ∣ z2 then μ w else 0))
        = (if Work.FIPlan.GaussCoprime z1 z2 then 1 else 0)
    rw [hT1, hT2, hTeq]
    by_cases hcop : Work.FIPlan.GaussCoprime z1 z2
    · rw [if_pos hcop]; exact hsind.1 hcop
    · rw [if_neg hcop]; exact hsind.2 hcop

/-! ## 2. The Moebius split of the round-6 separated sums -/

/-- The round-6 coefficient of the array restricted to the Gaussian multiples of `w` is the
restriction of `A6R2.coef6 β` to the pairs divisible by `w`. -/
lemma coef6_restrArray (β : GaussianInt → ℂ) (w : GaussianInt) (i : S15Id) :
    A6R2.coef6 (Work.S15alt.restrArray β w) i
      = (if w ∣ i.1.1 ∧ w ∣ i.1.2 then A6R2.coef6 β i else 0) := by
  by_cases h1 : w ∣ i.1.1 <;> by_cases h2 : w ∣ i.1.2 <;>
    simp [A6R2.coef6, A6R2.w6, Work.S15alt.restrArray, h1, h2]

/-- The round-6 coefficient of a pair vanishes when one of the two coefficients does. -/
lemma coef6_eq_zero_of {β : GaussianInt → ℂ} {d : ℕ} {z1 z2 : GaussianInt}
    (h : β z1 = 0 ∨ β z2 = 0) : A6R2.coef6 β ((z1, z2), d) = 0 := by
  rcases h with h | h <;> simp [A6R2.coef6, h]

lemma S15ixSet_eq_filter_ngset6 (Pa : Work.FITop.Params) (X j : ℕ) :
    S15ixSet Pa X j
      = (A6R2.ngset6 Pa X j).filter (fun i => Work.FIPlan.GaussCoprime i.1.1 i.1.2) := by
  classical
  unfold S15ixSet A6R2.ngset6
  rw [Finset.filter_filter]
  exact Finset.filter_congr (fun i _ => ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩)

/-- **The exact Moebius removal of the pair coprimality from the round-6 difference.**

Given Moebius data `(W, μ)` whose divisor sum is the coprimality indicator on the support of `β`,
the difference of the unfiltered and the filtered separated round-6 sums is the `(W,μ)`-sum
(over the non-unit divisors) of the unfiltered sums of the restricted arrays `β_w`. -/
theorem moebiusSplit6 (Pa : Work.FITop.Params) (X j : ℕ) (β : GaussianInt → ℂ)
    (ℓ : ℤ) (u t : ℝ) {W : Finset GaussianInt} {μ : GaussianInt → ℂ}
    (hμ : ∀ z1 ∈ Work.FITop.boxN Pa, ∀ z2 ∈ Work.FITop.boxN Pa, β z1 ≠ 0 → β z2 ≠ 0 →
      Work.S15alt.mobSum W μ z1 z2 = Work.S15alt.coprimeInd z1 z2)
    (h1W : 1 ∈ W) (hμ1 : μ 1 = 1) :
    A6R2.expSum6 Pa X j β ℓ u t - A6R2.expSum6ng Pa X j β ℓ u t
      = ∑ w ∈ W.erase 1,
          μ w * A6R2.expSum6ng Pa X j (Work.S15alt.restrArray β w) ℓ u t := by
  classical
  set T : S15Id → ℂ := fun i => A6R2.coef6 β i * S15theta ℓ i.1.1 i.1.2 * S15phase X j u t i with hT
  have h6 : A6R2.expSum6 Pa X j β ℓ u t
      = ∑ i ∈ A6R2.ngset6 Pa X j,
          (if Work.FIPlan.GaussCoprime i.1.1 i.1.2 then T i else 0) := by
    unfold A6R2.expSum6
    rw [S15ixSet_eq_filter_ngset6, Finset.sum_filter]
  have hng : A6R2.expSum6ng Pa X j β ℓ u t = ∑ i ∈ A6R2.ngset6 Pa X j, T i := by
    unfold A6R2.expSum6ng
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hT]
  have hrestr : ∀ w : GaussianInt, A6R2.expSum6ng Pa X j (Work.S15alt.restrArray β w) ℓ u t
      = ∑ i ∈ A6R2.ngset6 Pa X j, (if w ∣ i.1.1 ∧ w ∣ i.1.2 then T i else 0) := by
    intro w
    unfold A6R2.expSum6ng
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [coef6_restrArray]
    simp only [hT]
    by_cases h : w ∣ i.1.1 ∧ w ∣ i.1.2 <;> simp [h]
  have hpoint : ∀ i ∈ A6R2.ngset6 Pa X j,
      (if ¬ Work.FIPlan.GaussCoprime i.1.1 i.1.2 then T i else 0)
        = -∑ w ∈ W.erase 1, μ w *
            (if w ∣ i.1.1 ∧ w ∣ i.1.2 then T i else 0) := by
    intro i hi
    have hii1 : i.1.1 ∈ Work.FITop.boxN Pa :=
      (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_filter.mp hi).1).1).1
    have hii2 : i.1.2 ∈ Work.FITop.boxN Pa :=
      (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_filter.mp hi).1).1).2
    by_cases hb : β i.1.1 = 0 ∨ β i.1.2 = 0
    · have hT0 : T i = 0 := by
        have h := coef6_eq_zero_of (d := i.2) hb
        simp only [hT]
        simp only [h, mul_zero, zero_mul]
      rw [hT0]
      simp
    · push_neg at hb
      obtain ⟨hb1, hb2⟩ := hb
      have hmu := hμ i.1.1 hii1 i.1.2 hii2 hb1 hb2
      simp only [Work.S15alt.mobSum, Work.S15alt.coprimeInd] at hmu
      have hc1 : (1 : GaussianInt) ∣ i.1.1 ∧ (1 : GaussianInt) ∣ i.1.2 :=
        ⟨one_dvd _, one_dvd _⟩
      have h1term : (if (1 : GaussianInt) ∣ i.1.1 ∧ (1 : GaussianInt) ∣ i.1.2 then μ 1 else 0)
          = 1 := by rw [if_pos hc1, hμ1]
      have herase := Finset.sum_erase_add W
        (fun w => if w ∣ i.1.1 ∧ w ∣ i.1.2 then μ w else 0) h1W
      rw [h1term] at herase
      have hsum_erase : (∑ w ∈ W.erase 1,
            (if w ∣ i.1.1 ∧ w ∣ i.1.2 then μ w else 0))
          = (∑ w ∈ W, (if w ∣ i.1.1 ∧ w ∣ i.1.2 then μ w else 0)) - 1 :=
        eq_sub_iff_add_eq.mpr herase
      have hstep : (∑ w ∈ W.erase 1,
            μ w * (if w ∣ i.1.1 ∧ w ∣ i.1.2 then T i else 0))
          = ∑ w ∈ W.erase 1,
              T i * (if w ∣ i.1.1 ∧ w ∣ i.1.2 then μ w else 0) :=
        Finset.sum_congr rfl (fun w _ => by
          by_cases h : w ∣ i.1.1 ∧ w ∣ i.1.2 <;> simp [h, mul_comm])
      rw [hstep, ← Finset.mul_sum, hsum_erase, hmu]
      by_cases hcop : Work.FIPlan.GaussCoprime i.1.1 i.1.2 <;> simp [hcop]
  have hA : A6R2.expSum6 Pa X j β ℓ u t - A6R2.expSum6ng Pa X j β ℓ u t
      = -∑ i ∈ A6R2.ngset6 Pa X j,
          (if ¬ Work.FIPlan.GaussCoprime i.1.1 i.1.2 then T i else 0) := by
    rw [h6, hng, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hcop : Work.FIPlan.GaussCoprime i.1.1 i.1.2 <;> simp [hcop]
  have hsumA : (∑ i ∈ A6R2.ngset6 Pa X j,
        (if ¬ Work.FIPlan.GaussCoprime i.1.1 i.1.2 then T i else 0))
      = -∑ w ∈ W.erase 1,
          μ w * A6R2.expSum6ng Pa X j (Work.S15alt.restrArray β w) ℓ u t := by
    have h1 : (∑ i ∈ A6R2.ngset6 Pa X j,
          (if ¬ Work.FIPlan.GaussCoprime i.1.1 i.1.2 then T i else 0))
        = -∑ i ∈ A6R2.ngset6 Pa X j, ∑ w ∈ W.erase 1,
            μ w * (if w ∣ i.1.1 ∧ w ∣ i.1.2 then T i else 0) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i hi => hpoint i hi)
    have h2 : (∑ i ∈ A6R2.ngset6 Pa X j, ∑ w ∈ W.erase 1,
            μ w * (if w ∣ i.1.1 ∧ w ∣ i.1.2 then T i else 0))
        = ∑ w ∈ W.erase 1,
            μ w * A6R2.expSum6ng Pa X j (Work.S15alt.restrArray β w) ℓ u t := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [hrestr w, Finset.mul_sum]
    rw [h1, h2]
  rw [hA, hsumA, neg_neg]

/-! ## 4. The `τ³`-energy of a restricted array -/

/-- The `τ³`-energy of the restricted array `β_w` as a sum over the points divisible by `w`. -/
lemma A6Ener3_restrArray (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) (w : GaussianInt) :
    A6Ener3 Pa (Work.S15alt.restrArray β w)
      = ∑ z ∈ (Work.FITop.boxN Pa).filter (fun z => w ∣ z),
          ((((z.re.natAbs.divisors.card : ℕ) : ℝ)) ^ 3) * Complex.normSq (β z) := by
  unfold A6Ener3 Work.S15alt.restrArray
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  by_cases h : w ∣ z <;> simp [h]

/-- Interchange of the `w`-sum and the `z`-sum when the `z`-range depends on `w` through `w ∣ z`. -/
lemma sum_swap_divisor (Pa : Work.FITop.Params) (W : Finset GaussianInt) (g : GaussianInt → ℝ) :
    (∑ w ∈ W, (Real.sqrt ((Work.FIPlan.gnorm w : ℝ)))⁻¹
        * (∑ z ∈ (Work.FITop.boxN Pa).filter (fun z => w ∣ z), g z))
      = ∑ z ∈ Work.FITop.boxN Pa, g z
          * (∑ w ∈ W.filter (fun w => w ∣ z), (Real.sqrt ((Work.FIPlan.gnorm w : ℝ)))⁻¹) := by
  have key : ∀ w z : GaussianInt,
      (Real.sqrt ((Work.FIPlan.gnorm w : ℝ)))⁻¹ * (if w ∣ z then g z else 0)
        = g z * (if w ∣ z then (Real.sqrt ((Work.FIPlan.gnorm w : ℝ)))⁻¹ else 0) := by
    intro w z
    by_cases h : w ∣ z <;> simp [h, mul_comm]
  have hL : (∑ w ∈ W, (Real.sqrt ((Work.FIPlan.gnorm w : ℝ)))⁻¹
        * (∑ z ∈ (Work.FITop.boxN Pa).filter (fun z => w ∣ z), g z))
      = ∑ w ∈ W, ∑ z ∈ Work.FITop.boxN Pa,
          (Real.sqrt ((Work.FIPlan.gnorm w : ℝ)))⁻¹ * (if w ∣ z then g z else 0) := by
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun z _ => by rw [mul_ite, mul_zero])
  have hR : (∑ z ∈ Work.FITop.boxN Pa, g z
        * (∑ w ∈ W.filter (fun w => w ∣ z), (Real.sqrt ((Work.FIPlan.gnorm w : ℝ)))⁻¹))
      = ∑ z ∈ Work.FITop.boxN Pa, ∑ w ∈ W,
          g z * (if w ∣ z then (Real.sqrt ((Work.FIPlan.gnorm w : ℝ)))⁻¹ else 0) := by
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun w _ => by rw [mul_ite, mul_zero])
  rw [hL, hR, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun z _ => Finset.sum_congr rfl (fun w _ => ?_))
  exact key w z
/-! ## 4b. The divisor swap with an arbitrary weight -/

/-- Interchange of the `w`-sum and the `z`-sum when the `z`-range depends on `w` through `w ∣ z`,
for an arbitrary weight `c` of the divisors. -/
lemma sum_swap_divisor_gen (Pa : Work.FITop.Params) (W : Finset GaussianInt)
    (c : GaussianInt -> ℝ) (g : GaussianInt -> ℝ) :
    (∑ w ∈ W, c w * (∑ z ∈ (Work.FITop.boxN Pa).filter (fun z => w ∣ z), g z))
      = ∑ z ∈ Work.FITop.boxN Pa, g z * (∑ w ∈ W.filter (fun w => w ∣ z), c w) := by
  have key : ∀ w z : GaussianInt,
      c w * (if w ∣ z then g z else 0) = g z * (if w ∣ z then c w else 0) := by
    intro w z
    by_cases h : w ∣ z <;> simp [h, mul_comm]
  have hL : (∑ w ∈ W, c w * (∑ z ∈ (Work.FITop.boxN Pa).filter (fun z => w ∣ z), g z))
      = ∑ w ∈ W, ∑ z ∈ Work.FITop.boxN Pa, c w * (if w ∣ z then g z else 0) := by
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun z _ => by rw [mul_ite, mul_zero])
  have hR : (∑ z ∈ Work.FITop.boxN Pa, g z * (∑ w ∈ W.filter (fun w => w ∣ z), c w))
      = ∑ z ∈ Work.FITop.boxN Pa, ∑ w ∈ W, g z * (if w ∣ z then c w else 0) := by
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun w _ => by rw [mul_ite, mul_zero])
  rw [hL, hR, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun z _ => Finset.sum_congr rfl (fun w _ => ?_))
  exact key w z

end

end Work.FIArea4.A4c
