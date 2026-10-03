import Mathlib
import Submission.Work.FIArea4.S15EGDefs
import Submission.Work.FIArea4.S15stratumDefs
import Submission.Work.FIArea4.S15EvarGDefs
import Submission.Work.FIArea4.A6Defs
import Submission.Work.FIArea4.S15prim_defs
import Submission.Work.FIArea4.S15cutDefs

namespace Work.FIArea4.A6R

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# `enerQuad6` — the `τ³`-energy bookkeeping of the §15 stratum arrays

Every stratum array `quadArrE K (S15strU β u t ℓ e) σ₁ σ₂` reads `β` at the *scaled* point
`w = ⟨σ₁·(e r), σ₂·s⟩` of the coordinate `(r,s)`.  The `p14Ener` weight of the coordinate is
`τ(r)`, and for a *fixed* point `w` the admissible pairs `(e,r)` are exactly
`e ∣ |Re w|`, `r = |Re w|/e` (with `s = |Im w|` forced), so the whole `Σ_e`-stratification
contributes at most `Σ_{e ∣ |Re w|} τ(|Re w|/e) ≤ τ(|Re w|)² ≤ τ(|Re w|)³` to the point `w`.
That is the `τ³` energy `A6Ener3`, with no logarithmic loss.

The technical contents are the fiber count (`psiMap_fiber_card_le`, the `e ↦ e` injection into
the divisors of `|Re w|`), the per-fiber `τ` bound (`psiMap_fiber_tau_sum_le`), and the assembly
(`sum_psiMap_tau_weight_le`).
-/

/-! ## 1. The point `⟨σ₁·(e r), σ₂·s⟩` read by the stratum `e` at the coordinate `(r,s)` -/

/-- The point `⟨σ₁·(e·r), σ₂·s⟩` at which the stratum array `S15strU β u t ℓ e` reads `β` on the
quadrant `(σ₁,σ₂)` at the coordinate `(r,s)`; the triple is packaged as `⟨e,⟨r,s⟩⟩`. -/
def psiMap (σ₁ σ₂ : ℤ) (x : ℕ × (ℕ × ℕ)) : GaussianInt :=
  ⟨σ₁ * ((x.1 * x.2.1 : ℕ) : ℤ), σ₂ * ((x.2.2 : ℕ) : ℤ)⟩

@[simp] lemma psiMap_re (σ₁ σ₂ : ℤ) (x : ℕ × (ℕ × ℕ)) :
    (psiMap σ₁ σ₂ x).re = σ₁ * ((x.1 * x.2.1 : ℕ) : ℤ) := rfl

@[simp] lemma psiMap_im (σ₁ σ₂ : ℤ) (x : ℕ × (ℕ × ℕ)) :
    (psiMap σ₁ σ₂ x).im = σ₂ * ((x.2.2 : ℕ) : ℤ) := rfl

/-- The real part of `psiMap σ₁ σ₂ x` has absolute value `x.1 * x.2.1` (the product `e·r`). -/
lemma psiMap_re_natAbs (σ₁ σ₂ : ℤ) (hσ₁ : σ₁ = 1 ∨ σ₁ = -1) (x : ℕ × (ℕ × ℕ)) :
    (psiMap σ₁ σ₂ x).re.natAbs = x.1 * x.2.1 := by
  rw [psiMap_re, Int.natAbs_mul, Int.natAbs_natCast]
  rcases hσ₁ with h1 | h1 <;> rw [h1] <;> simp

/-! ## 2. Membership in the box `boxN Pa` -/

lemma mem_gBox_iff' {R : ℤ} {z : GaussianInt} :
    z ∈ Work.FIPlan.gBox R ↔ z.re ∈ Finset.Icc (-R) R ∧ z.im ∈ Finset.Icc (-R) R := by
  rw [Work.FIPlan.gBox, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(Finset.mem_product.mp hp).1, (Finset.mem_product.mp hp).2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(z.re, z.im), Finset.mem_product.mpr ⟨h1, h2⟩, by cases z; rfl⟩

/-- The support of a primitive box coefficient lies in the inner box `boxN Pa`. -/
lemma betaSupportBoxN (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ)
    (hβ : IsPrimBoxCoeff Pa φ β) {z : GaussianInt} (hz : β z ≠ 0) :
    z ∈ Work.FITop.boxN Pa := by
  have hbox : z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa) := by
    rw [mem_gBox_iff', S15EG_radN_eq]
    have hp := hβ.inPolarBox hz
    have hθ : Pa.θ ≤ 1 := S15theta_le_one Pa
    have hN0 : (0 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
    have hgn : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N := by
      have h1 := hp.2.2.1
      nlinarith
    rw [gnorm_eq_re_sq_add_im_sq] at hgn
    simp only [Nat.cast_add, Nat.cast_pow] at hgn
    have hre_sq : ((z.re.natAbs : ℝ)) ^ 2 ≤ 2 * Pa.N := by
      nlinarith [sq_nonneg ((z.im.natAbs : ℝ))]
    have him_sq : ((z.im.natAbs : ℝ)) ^ 2 ≤ 2 * Pa.N := by
      nlinarith [sq_nonneg ((z.re.natAbs : ℝ))]
    have hreNat : z.re.natAbs ≤ S15EG_K Pa := by
      have h1 : (z.re.natAbs : ℝ) ≤ Real.sqrt (2 * Pa.N) := by
        calc (z.re.natAbs : ℝ) = Real.sqrt ((z.re.natAbs : ℝ) ^ 2) :=
              (Real.sqrt_sq (by positivity)).symm
          _ ≤ Real.sqrt (2 * Pa.N) := Real.sqrt_le_sqrt hre_sq
      exact_mod_cast le_trans h1 (S15EG_sqrt_two_le_K Pa)
    have himNat : z.im.natAbs ≤ S15EG_K Pa := by
      have h1 : (z.im.natAbs : ℝ) ≤ Real.sqrt (2 * Pa.N) := by
        calc (z.im.natAbs : ℝ) = Real.sqrt ((z.im.natAbs : ℝ) ^ 2) :=
              (Real.sqrt_sq (by positivity)).symm
          _ ≤ Real.sqrt (2 * Pa.N) := Real.sqrt_le_sqrt him_sq
      exact_mod_cast le_trans h1 (S15EG_sqrt_two_le_K Pa)
    constructor
    · rw [Finset.mem_Icc]
      refine ⟨?_, ?_⟩
      · have h1 : -(z.re) ≤ (z.re.natAbs : ℤ) := by
          rw [← Int.natAbs_neg]; exact Int.le_natAbs
        have h2 : (z.re.natAbs : ℤ) ≤ (S15EG_K Pa : ℤ) := by exact_mod_cast hreNat
        linarith
      · exact le_trans Int.le_natAbs (by exact_mod_cast hreNat)
    · rw [Finset.mem_Icc]
      refine ⟨?_, ?_⟩
      · have h1 : -(z.im) ≤ (z.im.natAbs : ℤ) := by
          rw [← Int.natAbs_neg]; exact Int.le_natAbs
        have h2 : (z.im.natAbs : ℤ) ≤ (S15EG_K Pa : ℤ) := by exact_mod_cast himNat
        linarith
      · exact le_trans Int.le_natAbs (by exact_mod_cast himNat)
  exact hbox

/-! ## 3. Pointwise domination of the quadrant array by `β` at the scaled point -/

/-- Each quadrant-array entry of the stratum `e` is dominated in `normSq` by the corresponding
value of `β`. -/
lemma quadArrE_normSq_le (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) (u t : ℝ) (ℓ : ℤ)
    (e r s : ℕ) (σ₁ σ₂ : ℤ) (hσ₁ : σ₁ = 1 ∨ σ₁ = -1) :
    Complex.normSq (quadArrE (S15EG_K Pa) (S15strU β u t ℓ e) σ₁ σ₂ r s)
      ≤ Complex.normSq (β (psiMap σ₁ σ₂ ⟨e, ⟨r, s⟩⟩)) := by
  have harg : (⟨(e : ℤ) * (σ₁ * (r : ℤ)), σ₂ * (s : ℤ)⟩ : GaussianInt)
      = psiMap σ₁ σ₂ ⟨e, ⟨r, s⟩⟩ := by
    unfold psiMap
    rcases hσ₁ with h | h <;> rw [h] <;> ext <;> push_cast <;> ring
  have h1 : ‖quadArrE (S15EG_K Pa) (S15strU β u t ℓ e) σ₁ σ₂ r s‖
      ≤ ‖β (psiMap σ₁ σ₂ ⟨e, ⟨r, s⟩⟩)‖ := by
    have h := S15EG_norm_quadArrE_le Pa β u t ℓ e σ₁ σ₂ r s
    rwa [harg] at h
  calc Complex.normSq (quadArrE (S15EG_K Pa) (S15strU β u t ℓ e) σ₁ σ₂ r s)
      = ‖quadArrE (S15EG_K Pa) (S15strU β u t ℓ e) σ₁ σ₂ r s‖ ^ 2 :=
        Complex.normSq_eq_norm_sq _
    _ ≤ ‖β (psiMap σ₁ σ₂ ⟨e, ⟨r, s⟩⟩)‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = Complex.normSq (β (psiMap σ₁ σ₂ ⟨e, ⟨r, s⟩⟩)) := (Complex.normSq_eq_norm_sq _).symm

/-! ## 4. The fiber of `psiMap` -/

/-- **Fiber count.**  For a point `w` of the Gaussian integers, at most `τ(|Re w|)` triples
`(e,r,s)` of a product box satisfy `⟨σ₁(e r), σ₂ s⟩ = w`: the third coordinate is `s = σ₂·Im w`
and the first two satisfy `e ∣ Re w`, so `e` runs through the divisors of `|Re w|`. -/
lemma psiMap_fiber_card_le (Y R S : ℕ) (σ₁ σ₂ : ℤ) (hσ₁ : σ₁ = 1 ∨ σ₁ = -1)
    (hσ₂ : σ₂ = 1 ∨ σ₂ = -1) (w : GaussianInt) :
    (((Finset.Icc 1 Y) ×ˢ ((Finset.Icc 1 R) ×ˢ (Finset.Icc 1 S))).filter
      (fun x => psiMap σ₁ σ₂ x = w)).card ≤ (w.re.natAbs).divisors.card := by
  set F := ((Finset.Icc 1 Y) ×ˢ ((Finset.Icc 1 R) ×ˢ (Finset.Icc 1 S))).filter
      (fun x => psiMap σ₁ σ₂ x = w) with hF
  by_cases hne : F.Nonempty
  · obtain ⟨x0, hx0⟩ := hne
    obtain ⟨hx0U, hx0w⟩ := Finset.mem_filter.mp hx0
    obtain ⟨he0, hrest⟩ := Finset.mem_product.mp hx0U
    obtain ⟨hr0, hs0⟩ := Finset.mem_product.mp hrest
    have he0' : 1 ≤ x0.1 := (Finset.mem_Icc.mp he0).1
    have hr0' : 1 ≤ x0.2.1 := (Finset.mem_Icc.mp hr0).1
    have hnmul : (x0.1 * x0.2.1 : ℕ) ≠ 0 := by
      have : 0 < x0.1 * x0.2.1 := Nat.mul_pos (by omega) (by omega)
      omega
    have hwr : w.re ≠ 0 := by
      have h := congrArg Zsqrtd.re hx0w
      simp only [psiMap] at h
      rw [← h]
      rcases hσ₁ with h1 | h1
      · rw [h1]; simp only [one_mul]; exact_mod_cast hnmul
      · rw [h1]; simp only [neg_mul, one_mul]; exact neg_ne_zero.mpr (by exact_mod_cast hnmul)
    have hdiv : w.re.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hwr
    refine Finset.card_le_card_of_injOn (fun x => x.1) ?_ ?_
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, hF] at hx
      obtain ⟨hxU, hxw⟩ := hx
      obtain ⟨hex, hrestx⟩ := Finset.mem_product.mp hxU
      change x.1 ∈ (w.re.natAbs).divisors
      rw [Nat.mem_divisors]
      refine ⟨?_, hdiv⟩
      have hre : w.re = (x.1 : ℤ) * (σ₁ * (x.2.1 : ℤ)) := by
        have h := congrArg Zsqrtd.re hxw
        simp only [psiMap] at h
        rw [← h]
        rcases hσ₁ with h1 | h1 <;> rw [h1] <;> push_cast <;> ring
      rw [hre, Int.natAbs_mul, Int.natAbs_natCast]
      exact Nat.dvd_mul_right _ _
    · intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_filter, hF] at hx hy
      obtain ⟨hxU, hxw⟩ := hx
      obtain ⟨hyU, hyw⟩ := hy
      obtain ⟨hex, hrestx⟩ := Finset.mem_product.mp hxU
      obtain ⟨hey, hresty⟩ := Finset.mem_product.mp hyU
      simp only at hxy
      have hy1 : 1 ≤ y.1 := (Finset.mem_Icc.mp hey).1
      have him : x.2.2 = y.2.2 := by
        have h := congrArg Zsqrtd.im hxw
        have h' := congrArg Zsqrtd.im hyw
        simp only [psiMap] at h h'
        have h2 : σ₂ * (x.2.2 : ℤ) = σ₂ * (y.2.2 : ℤ) := by rw [h, h']
        rcases hσ₂ with h2' | h2' <;> rw [h2'] at h2 <;> simp only [one_mul, neg_mul, neg_inj] at h2
        · exact_mod_cast h2
        · exact_mod_cast h2
      have hre : x.2.1 = y.2.1 := by
        have h := congrArg Zsqrtd.re hxw
        have h' := congrArg Zsqrtd.re hyw
        simp only [psiMap] at h h'
        have h2 : σ₁ * ((x.1 * x.2.1 : ℕ) : ℤ) = σ₁ * ((y.1 * y.2.1 : ℕ) : ℤ) := by rw [h, h']
        rcases hσ₁ with h1 | h1 <;> rw [h1] at h2 <;> simp only [one_mul, neg_mul, neg_inj] at h2
        · have h3 : x.1 * x.2.1 = y.1 * y.2.1 := by exact_mod_cast h2
          rw [hxy] at h3
          exact Nat.mul_left_cancel (by omega) h3
        · have h3 : x.1 * x.2.1 = y.1 * y.2.1 := by exact_mod_cast h2
          rw [hxy] at h3
          exact Nat.mul_left_cancel (by omega) h3
      exact Prod.ext hxy (Prod.ext hre him)
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]; simp

/-- **Per-fiber `τ`-weight.**  On the fiber of `psiMap` over `w`, the summation weight `τ(r)`
is at most `τ(|Re w|)`, and the fiber has at most `τ(|Re w|)` elements, so the total weight is
at most `τ(|Re w|)² ≤ τ(|Re w|)³`. -/
lemma psiMap_fiber_tau_sum_le (Y R S : ℕ) (σ₁ σ₂ : ℤ) (hσ₁ : σ₁ = 1 ∨ σ₁ = -1)
    (hσ₂ : σ₂ = 1 ∨ σ₂ = -1) (w : GaussianInt) :
    (∑ x ∈ ((Finset.Icc 1 Y) ×ˢ ((Finset.Icc 1 R) ×ˢ (Finset.Icc 1 S))).filter
        (fun x => psiMap σ₁ σ₂ x = w),
        (((x.2.1).divisors.card : ℕ) : ℝ))
      ≤ ((((w.re.natAbs).divisors.card : ℕ) : ℝ)) ^ 2 := by
  set F := ((Finset.Icc 1 Y) ×ˢ ((Finset.Icc 1 R) ×ˢ (Finset.Icc 1 S))).filter
      (fun x => psiMap σ₁ σ₂ x = w) with hF
  by_cases hne : F.Nonempty
  · obtain ⟨x0, hx0⟩ := hne
    obtain ⟨hx0U, hx0w⟩ := Finset.mem_filter.mp hx0
    obtain ⟨he0, hrest⟩ := Finset.mem_product.mp hx0U
    obtain ⟨hr0, hs0⟩ := Finset.mem_product.mp hrest
    have he0' : 1 ≤ x0.1 := (Finset.mem_Icc.mp he0).1
    have hr0' : 1 ≤ x0.2.1 := (Finset.mem_Icc.mp hr0).1
    have hdpos : 0 < w.re.natAbs := by
      have hmul : 0 < x0.1 * x0.2.1 := Nat.mul_pos (by omega) (by omega)
      have hw : w.re.natAbs = x0.1 * x0.2.1 := by
        have h := congrArg Zsqrtd.re hx0w
        rw [← h]
        exact psiMap_re_natAbs σ₁ σ₂ hσ₁ x0
      rw [hw]; exact hmul
    have hdne : w.re.natAbs ≠ 0 := Nat.pos_iff_ne_zero.mp hdpos
    have hcard : F.card ≤ (w.re.natAbs).divisors.card := by
      rw [hF]; exact psiMap_fiber_card_le Y R S σ₁ σ₂ hσ₁ hσ₂ w
    have hterm : ∀ x ∈ F, (((x.2.1).divisors.card : ℕ) : ℝ)
        ≤ (((w.re.natAbs).divisors.card : ℕ) : ℝ) := by
      intro x hx
      simp only [hF, Finset.mem_filter] at hx
      obtain ⟨hxU, hxw⟩ := hx
      obtain ⟨hex, hrestx⟩ := Finset.mem_product.mp hxU
      have hdvd : x.2.1 ∣ w.re.natAbs := by
        have hw : w.re.natAbs = x.1 * x.2.1 := by
          have h := congrArg Zsqrtd.re hxw
          rw [← h]
          exact psiMap_re_natAbs σ₁ σ₂ hσ₁ x
        rw [hw]; exact Nat.dvd_mul_left _ _
      exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hdne hdvd)
    calc (∑ x ∈ F, (((x.2.1).divisors.card : ℕ) : ℝ))
        ≤ ∑ x ∈ F, (((w.re.natAbs).divisors.card : ℕ) : ℝ) := Finset.sum_le_sum hterm
      _ = (F.card : ℝ) * (((w.re.natAbs).divisors.card : ℕ) : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((((w.re.natAbs).divisors.card : ℕ) : ℝ))
            * ((((w.re.natAbs).divisors.card : ℕ) : ℝ)) := by
            apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
            exact Nat.cast_nonneg _
      _ = ((((w.re.natAbs).divisors.card : ℕ) : ℝ)) ^ 2 := by ring
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]; simp

/-! ## 5. The reindexed `τ`-weighted energy bound -/

/-- **The reindexed `τ`-weighted energy bound.**  Summing `τ(r)·‖β‖²` over a product box
reindexed by `psiMap` is bounded by the `τ³` energy `A6Ener3 Pa β`: the fiber of `psiMap` over `w`
has `τ`-weight at most `τ(|Re w|)²`, and `τ² ≤ τ³`. -/
lemma sum_psiMap_tau_weight_le (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ)
    (hβ : IsPrimBoxCoeff Pa φ β) (Y R S : ℕ) (σ₁ σ₂ : ℤ)
    (hσ₁ : σ₁ = 1 ∨ σ₁ = -1) (hσ₂ : σ₂ = 1 ∨ σ₂ = -1) :
    (∑ x ∈ (Finset.Icc 1 Y) ×ˢ ((Finset.Icc 1 R) ×ˢ (Finset.Icc 1 S)),
        (((x.2.1).divisors.card : ℕ) : ℝ) * Complex.normSq (β (psiMap σ₁ σ₂ x)))
      ≤ A6Ener3 Pa β := by
  set U := (Finset.Icc 1 Y) ×ˢ ((Finset.Icc 1 R) ×ˢ (Finset.Icc 1 S)) with hU
  set G : ℕ × (ℕ × ℕ) → GaussianInt := psiMap σ₁ σ₂ with hG
  set f : GaussianInt → ℝ := fun w => Complex.normSq (β w) with hf
  change (∑ x ∈ U, (((x.2.1).divisors.card : ℕ) : ℝ) * f (G x)) ≤ A6Ener3 Pa β
  have hfval : ∀ w : GaussianInt, f w = Complex.normSq (β w) := by intro w; rw [hf]
  have hfnn : ∀ w : GaussianInt, 0 ≤ f w := by
    intro w; rw [hfval w]; exact Complex.normSq_nonneg _
  set U' := U.filter (fun x => β (G x) ≠ 0) with hU'
  -- (1) the points where `β` vanishes contribute nothing
  have step1 : (∑ x ∈ U', (((x.2.1).divisors.card : ℕ) : ℝ) * f (G x))
      = ∑ x ∈ U, (((x.2.1).divisors.card : ℕ) : ℝ) * f (G x) := by
    rw [hU', Finset.sum_filter]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    by_cases hb : β (G x) = 0
    · rw [if_neg (by simp [hb]), hfval, hb, Complex.normSq_zero, mul_zero]
    · rw [if_pos hb]
  -- (2) group by the fibers of `G`
  have hpair : (↑(U'.image G) : Set GaussianInt).PairwiseDisjoint
      (fun w => U'.filter (fun c => G c = w)) := by
    intro w hw w' hw' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter] at hx hx'
    exact hne (hx.2.symm.trans hx'.2)
  have step2 : (∑ x ∈ U', (((x.2.1).divisors.card : ℕ) : ℝ) * f (G x))
      = ∑ w ∈ U'.image G, ∑ x ∈ U'.filter (fun c => G c = w),
          (((x.2.1).divisors.card : ℕ) : ℝ) * f (G x) := by
    have h := Finset.sum_biUnion (s := U'.image G) (t := fun w => U'.filter (fun c => G c = w))
      (f := fun x => (((x.2.1).divisors.card : ℕ) : ℝ) * f (G x)) hpair
    rw [Finset.image_biUnion_filter_eq U' G] at h
    exact h
  have step3 : (∑ w ∈ U'.image G, ∑ x ∈ U'.filter (fun c => G c = w),
          (((x.2.1).divisors.card : ℕ) : ℝ) * f (G x))
      = ∑ w ∈ U'.image G,
          (∑ x ∈ U'.filter (fun c => G c = w), (((x.2.1).divisors.card : ℕ) : ℝ)) * f w := by
    refine Finset.sum_congr rfl (fun w hw => ?_)
    have hcong : (∑ x ∈ U'.filter (fun c => G c = w),
          (((x.2.1).divisors.card : ℕ) : ℝ) * f (G x))
        = ∑ x ∈ U'.filter (fun c => G c = w),
            (((x.2.1).divisors.card : ℕ) : ℝ) * f w :=
      Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2])
    rw [hcong, Finset.sum_mul]
  -- (3) bound each fiber by `τ(|Re w|)²` and then by `τ(|Re w|)³`
  have step4 : (∑ w ∈ U'.image G,
          (∑ x ∈ U'.filter (fun c => G c = w), (((x.2.1).divisors.card : ℕ) : ℝ)) * f w)
      ≤ ∑ w ∈ U'.image G, ((((w.re.natAbs).divisors.card : ℕ) : ℝ)) ^ 2 * f w := by
    refine Finset.sum_le_sum (fun w hw => ?_)
    apply mul_le_mul_of_nonneg_right _ (hfnn w)
    have hsub : U'.filter (fun c => G c = w) ⊆ U.filter (fun c => G c = w) := by
      intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨(Finset.mem_filter.mp hx.1).1, hx.2⟩
    calc (∑ x ∈ U'.filter (fun c => G c = w), (((x.2.1).divisors.card : ℕ) : ℝ))
        ≤ ∑ x ∈ U.filter (fun c => G c = w), (((x.2.1).divisors.card : ℕ) : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x hx hxnot => ?_)
          exact Nat.cast_nonneg _
      _ ≤ ((((w.re.natAbs).divisors.card : ℕ) : ℝ)) ^ 2 := by
          rw [hG, hU]
          exact psiMap_fiber_tau_sum_le Y R S σ₁ σ₂ hσ₁ hσ₂ w
  have step4b : (∑ w ∈ U'.image G, ((((w.re.natAbs).divisors.card : ℕ) : ℝ)) ^ 2 * f w)
      ≤ ∑ w ∈ U'.image G, ((((w.re.natAbs).divisors.card : ℕ) : ℝ)) ^ 3 * f w := by
    refine Finset.sum_le_sum (fun w hw => ?_)
    apply mul_le_mul_of_nonneg_right _ (hfnn w)
    rcases Nat.eq_zero_or_pos (w.re.natAbs.divisors.card) with h0 | hpos
    · rw [h0]; norm_num
    · have h1 : (1 : ℝ) ≤ (((w.re.natAbs).divisors.card : ℕ) : ℝ) := by exact_mod_cast hpos
      exact pow_le_pow_right₀ h1 (by norm_num)
  have step5 : (∑ w ∈ U'.image G, ((((w.re.natAbs).divisors.card : ℕ) : ℝ)) ^ 3 * f w)
      ≤ ∑ w ∈ Work.FITop.boxN Pa, ((((w.re.natAbs).divisors.card : ℕ) : ℝ)) ^ 3 * f w := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro w hw
      rw [Finset.mem_image] at hw
      obtain ⟨x, hx, hxw⟩ := hw
      simp only [hU', Finset.mem_filter] at hx
      rw [← hxw]
      exact betaSupportBoxN Pa φ β hβ hx.2
    · intro w hw hwnot
      exact mul_nonneg (by positivity) (hfnn w)
  have step6 : (∑ w ∈ Work.FITop.boxN Pa,
        ((((w.re.natAbs).divisors.card : ℕ) : ℝ)) ^ 3 * f w) = A6Ener3 Pa β := by
    unfold A6Ener3
    refine Finset.sum_congr rfl (fun w hw => ?_)
    rw [hfval w]
  calc (∑ x ∈ U, (((x.2.1).divisors.card : ℕ) : ℝ) * f (G x))
      = ∑ x ∈ U', (((x.2.1).divisors.card : ℕ) : ℝ) * f (G x) := step1.symm
    _ = ∑ w ∈ U'.image G, ∑ x ∈ U'.filter (fun c => G c = w),
          (((x.2.1).divisors.card : ℕ) : ℝ) * f (G x) := step2
    _ = ∑ w ∈ U'.image G,
          (∑ x ∈ U'.filter (fun c => G c = w), (((x.2.1).divisors.card : ℕ) : ℝ)) * f w := step3
    _ ≤ ∑ w ∈ U'.image G, ((((w.re.natAbs).divisors.card : ℕ) : ℝ)) ^ 2 * f w := step4
    _ ≤ ∑ w ∈ U'.image G, ((((w.re.natAbs).divisors.card : ℕ) : ℝ)) ^ 3 * f w := step4b
    _ ≤ ∑ w ∈ Work.FITop.boxN Pa, ((((w.re.natAbs).divisors.card : ℕ) : ℝ)) ^ 3 * f w := step5
    _ = A6Ener3 Pa β := step6

/-! ## 6. The main theorem -/

/-- **The `τ³`-energy bookkeeping of the §15 stratum arrays.**  For a primitive box coefficient
`β` and any of the four sign quadrants `(σ₁,σ₂)`, the sum over the strata `e ≤ S15Y Pa X j` of the
Proposition-14.1 τ-weighted energy `p14Ener (S15EG_Re Pa e) (S15EG_Se Pa) (quadArrE (S15EG_K Pa)
(S15strU β u t ℓ e) σ₁ σ₂)` is bounded by the `τ³`-energy `A6Ener3 Pa β` — with **no** logarithmic
loss, because each `z ∈ boxN Pa` occurs once for every `e ∣ |Re z|` and the weights add up to
`Σ_{e ∣ |Re z|} τ(|Re z|/e) = τ₂(|Re z|) ≤ τ(|Re z|)² ≤ τ(|Re z|)³`. -/
theorem enerQuad6 :
    ∃ C : ℝ, 0 < C ∧ ∀ (Pa : Work.FITop.Params) (X j : ℕ) (φ : ℝ) (β : GaussianInt → ℂ)
      (u t : ℝ) (ℓ : ℤ) (σ₁ σ₂ : ℤ),
      Work.FIArea4.IsPrimBoxCoeff Pa φ β → 1 ≤ X →
      (σ₁ = 1 ∨ σ₁ = -1) → (σ₂ = 1 ∨ σ₂ = -1) →
      (∑ e ∈ Finset.Icc 1 (Work.FIArea4.S15Y Pa X j),
          Work.FIArea4.p14Ener (Work.FIArea4.S15EG_Re Pa e) (Work.FIArea4.S15EG_Se Pa)
            (Work.FIArea4.quadArrE (Work.FIArea4.S15EG_K Pa)
              (Work.FIArea4.S15strU β u t ℓ e) σ₁ σ₂))
        ≤ C * Work.FIArea4.A6Ener3 Pa β := by
  refine ⟨1, one_pos, ?_⟩
  intro Pa X j φ β u t ℓ σ₁ σ₂ hβ hX hσ₁ hσ₂
  simp only [one_mul]
  -- the per-stratum `r`-range `2·S15EG_Re Pa e` is bounded by the fixed range `2·S15EG_Re Pa 1`
  have hRe_mono : ∀ e ∈ Finset.Icc 1 (S15Y Pa X j),
      2 * S15EG_Re Pa e ≤ 2 * S15EG_Re Pa 1 := by
    intro e he
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have h := S15EG_Re_anti Pa (le_refl 1) he1
    exact Nat.mul_le_mul_left 2 h
  have hstep1 : (∑ e ∈ Finset.Icc 1 (S15Y Pa X j),
        p14Ener (S15EG_Re Pa e) (S15EG_Se Pa)
          (quadArrE (S15EG_K Pa) (S15strU β u t ℓ e) σ₁ σ₂))
      ≤ ∑ e ∈ Finset.Icc 1 (S15Y Pa X j),
          ∑ r ∈ Finset.Icc 1 (2 * S15EG_Re Pa 1), ∑ s ∈ Finset.Icc 1 (2 * S15EG_Se Pa),
            (((r.divisors.card : ℕ) : ℝ)) * Complex.normSq (β (psiMap σ₁ σ₂ ⟨e, ⟨r, s⟩⟩)) := by
    apply Finset.sum_le_sum
    intro e he
    rw [p14Ener]
    calc (∑ r ∈ Finset.Icc 1 (2 * S15EG_Re Pa e), ∑ s ∈ Finset.Icc 1 (2 * S15EG_Se Pa),
            (((r.divisors.card : ℕ) : ℝ)) *
              Complex.normSq (quadArrE (S15EG_K Pa) (S15strU β u t ℓ e) σ₁ σ₂ r s))
        ≤ ∑ r ∈ Finset.Icc 1 (2 * S15EG_Re Pa e), ∑ s ∈ Finset.Icc 1 (2 * S15EG_Se Pa),
            (((r.divisors.card : ℕ) : ℝ)) * Complex.normSq (β (psiMap σ₁ σ₂ ⟨e, ⟨r, s⟩⟩)) := by
          apply Finset.sum_le_sum; intro r hr
          apply Finset.sum_le_sum; intro s hs
          exact mul_le_mul_of_nonneg_left (quadArrE_normSq_le Pa β u t ℓ e r s σ₁ σ₂ hσ₁)
            (Nat.cast_nonneg _)
      _ ≤ ∑ r ∈ Finset.Icc 1 (2 * S15EG_Re Pa 1), ∑ s ∈ Finset.Icc 1 (2 * S15EG_Se Pa),
            (((r.divisors.card : ℕ) : ℝ)) * Complex.normSq (β (psiMap σ₁ σ₂ ⟨e, ⟨r, s⟩⟩)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro r hr
            exact Finset.mem_Icc.mpr
              ⟨(Finset.mem_Icc.mp hr).1, le_trans (Finset.mem_Icc.mp hr).2 (hRe_mono e he)⟩
          · intro r hr hrnot
            exact Finset.sum_nonneg
              (fun s hs => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _))
  have hstep2 : (∑ e ∈ Finset.Icc 1 (S15Y Pa X j),
          ∑ r ∈ Finset.Icc 1 (2 * S15EG_Re Pa 1), ∑ s ∈ Finset.Icc 1 (2 * S15EG_Se Pa),
            (((r.divisors.card : ℕ) : ℝ)) * Complex.normSq (β (psiMap σ₁ σ₂ ⟨e, ⟨r, s⟩⟩)))
      = ∑ x ∈ (Finset.Icc 1 (S15Y Pa X j)) ×ˢ
              ((Finset.Icc 1 (2 * S15EG_Re Pa 1)) ×ˢ (Finset.Icc 1 (2 * S15EG_Se Pa))),
            (((x.2.1.divisors.card : ℕ) : ℝ)) * Complex.normSq (β (psiMap σ₁ σ₂ x)) := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun e he => ?_)
    rw [Finset.sum_product]
  calc (∑ e ∈ Finset.Icc 1 (S15Y Pa X j),
        p14Ener (S15EG_Re Pa e) (S15EG_Se Pa)
          (quadArrE (S15EG_K Pa) (S15strU β u t ℓ e) σ₁ σ₂))
      ≤ ∑ e ∈ Finset.Icc 1 (S15Y Pa X j),
          ∑ r ∈ Finset.Icc 1 (2 * S15EG_Re Pa 1), ∑ s ∈ Finset.Icc 1 (2 * S15EG_Se Pa),
            (((r.divisors.card : ℕ) : ℝ)) * Complex.normSq (β (psiMap σ₁ σ₂ ⟨e, ⟨r, s⟩⟩)) :=
        hstep1
    _ = ∑ x ∈ (Finset.Icc 1 (S15Y Pa X j)) ×ˢ
              ((Finset.Icc 1 (2 * S15EG_Re Pa 1)) ×ˢ (Finset.Icc 1 (2 * S15EG_Se Pa))),
            (((x.2.1.divisors.card : ℕ) : ℝ)) * Complex.normSq (β (psiMap σ₁ σ₂ x)) := hstep2
    _ ≤ A6Ener3 Pa β :=
        sum_psiMap_tau_weight_le Pa φ β hβ (S15Y Pa X j) (2 * S15EG_Re Pa 1)
          (2 * S15EG_Se Pa) σ₁ σ₂ hσ₁ hσ₂

end

end Work.FIArea4.A6R
