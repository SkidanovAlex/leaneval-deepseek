import Mathlib
import Submission.CDT.DerivOrderAt
import Submission.CDT.RatFuncConstants

/-!
# Residues of rational functions at a point

For a rational function `r ∈ K(X)` and a point `α ∈ K` we develop the first-order local structure
at `α`:

* `polePart α c = c/(X - α)` — the elementary simple pole;
* `ResidueAt α r c` — "`r` has at most a simple pole at `α`, with residue `c`", expressed as the
  *relation* `-1 ≤ ordAt α r` and `0 ≤ ordAt α (r - c/(X - α))` (subtracting `c/(X-α)` removes
  the possible simple pole).  The relation determines `c` uniquely (`ResidueAt.unique`), and is
  additive (`ResidueAt.add`) and `K`-homogeneous (`ResidueAt.const_mul`);
* `exists_residueAt` — every `r` with `ordAt α r ≥ -1` has a residue;
* `residueAt_dRat_div_self` — **the residue of the logarithmic derivative**: for `f ≠ 0`,
  `ResidueAt α ((dRat f)/f) (ordAt α f)`.  At a zero or pole of `f` the logarithmic derivative has
  the simple pole `ordAt α f/(X - α)`; where `f` is finite and nonzero it is holomorphic.

The residue of the logarithmic derivative is the only property of a residue that the
function-field Lindemann–Weierstrass theorem needs: applied to `Σᵢ cᵢ (dRat fᵢ)/fᵢ = dRat h` and
using that `dRat h` has no simple pole (`ordAt_dRat_ne_neg_one`), it gives
`Σᵢ cᵢ * ordAt α fᵢ = 0` for every `α`.
-/

noncomputable section

namespace Submission.CDT

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- The elementary function with a simple pole at `α` of residue `c`: `c/(X - α)`. -/
def polePart (α : K) (c : K) : RatFunc K :=
  algebraMap (Polynomial K) (RatFunc K) (Polynomial.C c)
    / algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C α)

/-- `X - α` as an element of `K(X)`. -/
def lin (α : K) : RatFunc K :=
  algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C α)

lemma polePart_eq (α : K) (c : K) : polePart α c = algebraMap K (RatFunc K) c / lin α := by
  rw [polePart, lin, am_C']

lemma lin_ne_zero (α : K) : lin α ≠ 0 := by
  rw [lin]
  exact RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero α)

lemma ordAt_lin (α : K) : ordAt α (lin α) = 1 := by
  rw [lin, ordAt_algebraMap, Polynomial.rootMultiplicity_X_sub_C_self]
  norm_num

/-- The order of vanishing of a constant. -/
lemma ordAt_const (α : K) (c : K) : ordAt α (algebraMap K (RatFunc K) c) = 0 := by
  rw [← am_C', ordAt_algebraMap, Polynomial.rootMultiplicity_C]
  norm_num

lemma const_ne_zero {c : K} (hc : c ≠ 0) : algebraMap K (RatFunc K) c ≠ 0 := by
  rw [← am_C']
  exact RatFunc.algebraMap_ne_zero (Polynomial.C_ne_zero.mpr hc)

lemma ordAt_polePart (α : K) {c : K} (hc : c ≠ 0) : ordAt α (polePart α c) = -1 := by
  rw [polePart_eq, ordAt_div α (const_ne_zero hc) (lin_ne_zero α), ordAt_const, ordAt_lin]
  norm_num

lemma polePart_ne_zero (α : K) {c : K} (hc : c ≠ 0) : polePart α c ≠ 0 := by
  intro h
  have := ordAt_polePart α hc
  rw [h, ordAt_zero] at this
  norm_num at this

lemma polePart_sub (α : K) (c d : K) : polePart α c - polePart α d = polePart α (c - d) := by
  rw [polePart_eq, polePart_eq, polePart_eq, ← sub_div, ← map_sub]

/-- **`r` has at most a simple pole at `α`, with residue `c`.**  Subtracting the elementary pole
`c/(X - α)` removes the singularity: `ordAt α (r - c/(X-α)) ≥ 0`. -/
def ResidueAt (α : K) (r : RatFunc K) (c : K) : Prop :=
  -1 ≤ ordAt α r ∧ 0 ≤ ordAt α (r - polePart α c)

/-- A holomorphic (i.e. `ordAt α r ≥ 0`) rational function has residue `0`. -/
lemma ResidueAt.of_ordAt_nonneg {α : K} {r : RatFunc K} (h : 0 ≤ ordAt α r) :
    ResidueAt α r 0 := by
  refine ⟨le_trans (by norm_num) h, ?_⟩
  rw [show polePart α (0 : K) = 0 from by
    rw [polePart_eq, map_zero, zero_div], sub_zero]
  exact h

/-- **Uniqueness of the residue.** -/
lemma ResidueAt.unique {α : K} {r : RatFunc K} {c d : K} (hc : ResidueAt α r c)
    (hd : ResidueAt α r d) : c = d := by
  by_contra hne
  have hdc : d - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hle : 0 ≤ ordAt α (polePart α d - polePart α c) := by
    have hsum : polePart α d - polePart α c
        = (r - polePart α c) + -(r - polePart α d) := by ring
    rcases eq_or_ne ((r - polePart α c) + -(r - polePart α d)) 0 with h0 | h0
    · rw [hsum, h0]; simp
    · rw [hsum]
      exact (le_min hc.2 (by rw [ordAt_neg]; linarith [hd.2])).trans
        (min_ordAt_le_ordAt_add α h0)
  rw [polePart_sub, ordAt_polePart α hdc] at hle
  norm_num at hle

/-- **Additivity of residues.** -/
lemma ResidueAt.add {α : K} {r s : RatFunc K} {c d : K} (hr : ResidueAt α r c)
    (hs : ResidueAt α s d) : ResidueAt α (r + s) (c + d) := by
  have hsum : polePart α (c + d) = polePart α c + polePart α d := by
    rw [polePart_eq, polePart_eq, polePart_eq, ← add_div, ← map_add]
  refine ⟨?_, ?_⟩
  · by_cases h0 : r + s = 0
    · rw [h0]; simp
    · exact (le_min hr.1 hs.1).trans (min_ordAt_le_ordAt_add α h0)
  · have h : r + s - polePart α (c + d) = (r - polePart α c) + (s - polePart α d) := by
      rw [hsum]; ring
    rw [h]
    rcases eq_or_ne ((r - polePart α c) + (s - polePart α d)) 0 with h0 | h0
    · rw [h0]; simp
    · exact (le_min hr.2 hs.2).trans (min_ordAt_le_ordAt_add α h0)

/-- **`K`-homogeneity of residues.** -/
lemma ResidueAt.const_mul {α : K} {r : RatFunc K} {c : K} (hr : ResidueAt α r c) (t : K) :
    ResidueAt α (algebraMap K (RatFunc K) t * r) (t * c) := by
  have hmul : polePart α (t * c) = algebraMap K (RatFunc K) t * polePart α c := by
    rw [polePart_eq, polePart_eq, map_mul, mul_div_assoc]
  have hsplit : algebraMap K (RatFunc K) t * r - algebraMap K (RatFunc K) t * polePart α c
      = algebraMap K (RatFunc K) t * (r - polePart α c) := by ring
  change -1 ≤ ordAt α (algebraMap K (RatFunc K) t * r) ∧
    0 ≤ ordAt α (algebraMap K (RatFunc K) t * r - polePart α (t * c))
  rw [hmul, hsplit]
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · refine ⟨?_, ?_⟩
    · rcases eq_or_ne r 0 with rfl | hr0
      · rw [mul_zero, ordAt_zero]; norm_num
      · rw [ordAt_mul α (const_ne_zero ht) hr0, ordAt_const]
        linarith [hr.1]
    · rcases eq_or_ne (r - polePart α c) 0 with h0 | h0
      · rw [h0, mul_zero, ordAt_zero]
      · rw [ordAt_mul α (const_ne_zero ht) h0, ordAt_const]
        linarith [hr.2]

/-- A nonzero residue means an honest simple pole. -/
lemma ResidueAt.ordAt_eq_neg_one {α : K} {r : RatFunc K} {c : K} (hr : ResidueAt α r c)
    (hc : c ≠ 0) : ordAt α r = -1 := by
  have hsplit : r = polePart α c + (r - polePart α c) := by ring
  have h3 : ordAt α (polePart α c) = -1 := ordAt_polePart α hc
  rcases eq_or_ne (r - polePart α c) 0 with h0 | h0
  · rw [hsplit, h0, add_zero, h3]
  · rw [hsplit, ordAt_add_of_lt α (polePart_ne_zero α hc) h0 (by rw [h3]; linarith [hr.2]), h3]

/-- The value at `α` of a rational function that is finite and nonzero there: `p(α)/q(α)` for the
canonical representative. -/
def valueAt (α : K) (g : RatFunc K) : K :=
  Polynomial.eval α g.num / Polynomial.eval α g.denom

/-- If `ordAt α g = 0` then the canonical denominator does not vanish at `α`, so `valueAt α g` is
well defined. -/
lemma eval_denom_ne_zero_of_ordAt_eq_zero {α : K} {g : RatFunc K} (hg : ordAt α g = 0) :
    Polynomial.eval α g.denom ≠ 0 := by
  have hq : g.denom ≠ 0 := RatFunc.denom_ne_zero g
  have hrm : Polynomial.rootMultiplicity α g.denom = 0 := by
    rcases eq_or_ne g 0 with rfl | hg0
    · simp
    · have hcop : IsCoprime g.num g.denom := RatFunc.isCoprime_num_denom g
      have hp : g.num ≠ 0 := RatFunc.num_ne_zero hg0
      have heq : ((Polynomial.rootMultiplicity α g.num : ℕ) : ℤ)
          = ((Polynomial.rootMultiplicity α g.denom : ℕ) : ℤ) := by
        have h := hg; rw [ordAt] at h; linarith
      by_contra hlt
      have h1 : 1 ≤ Polynomial.rootMultiplicity α g.denom := Nat.one_le_iff_ne_zero.mpr hlt
      have h2 : (Polynomial.X - Polynomial.C α) ∣ g.denom := by
        simpa using (le_rootMultiplicity_iff hq).mp h1
      have h3 : (Polynomial.X - Polynomial.C α) ∣ g.num := by
        have h4 : 1 ≤ Polynomial.rootMultiplicity α g.num := by
          have hZ : (1 : ℤ) ≤ (Polynomial.rootMultiplicity α g.num : ℤ) := by
            rw [heq]; exact_mod_cast h1
          exact_mod_cast hZ
        simpa using (le_rootMultiplicity_iff hp).mp h4
      exact not_isUnit_X_sub_C α (hcop.isUnit_of_dvd' h3 h2)
  intro h
  exact hq ((Polynomial.rootMultiplicity_eq_zero_iff.mp hrm) h)

/-- Away from `g`'s value, subtracting the value lowers the order of vanishing at `α` by at least
one. -/
lemma one_le_ordAt_sub_valueAt {α : K} {g : RatFunc K} (hg : ordAt α g = 0)
    (hne : g ≠ algebraMap K (RatFunc K) (valueAt α g)) :
    1 ≤ ordAt α (g - algebraMap K (RatFunc K) (valueAt α g)) := by
  set c : K := valueAt α g with hcdef
  have hq : g.denom ≠ 0 := RatFunc.denom_ne_zero g
  have hden : Polynomial.eval α g.denom ≠ 0 := eval_denom_ne_zero_of_ordAt_eq_zero hg
  have hcval : c = Polynomial.eval α g.num / Polynomial.eval α g.denom := hcdef
  have hcomp : g - algebraMap K (RatFunc K) c
      = algebraMap (Polynomial K) (RatFunc K) (g.num - Polynomial.C c * g.denom)
        / algebraMap (Polynomial K) (RatFunc K) g.denom := by
    conv_lhs => rw [num_denom_eq g]
    have hqd : algebraMap (Polynomial K) (RatFunc K) g.denom ≠ 0 :=
      RatFunc.algebraMap_ne_zero hq
    rw [← am_C', map_sub, map_mul]
    field_simp
  have hroot : Polynomial.eval α (g.num - Polynomial.C c * g.denom) = 0 := by
    rw [show Polynomial.eval α (g.num - Polynomial.C c * g.denom)
        = Polynomial.eval α g.num - c * Polynomial.eval α g.denom from by simp, hcval,
      div_mul_cancel₀ _ hden, sub_self]
  have hdiv : (Polynomial.X - Polynomial.C α)
      ∣ (g.num - Polynomial.C c * g.denom) :=
    Polynomial.dvd_iff_isRoot.mpr hroot
  have hqrm : Polynomial.rootMultiplicity α g.denom = 0 := by
    rcases eq_or_ne g 0 with rfl | hg0
    · simp
    · have hcop : IsCoprime g.num g.denom := RatFunc.isCoprime_num_denom g
      have hp : g.num ≠ 0 := RatFunc.num_ne_zero hg0
      have heq : ((Polynomial.rootMultiplicity α g.num : ℕ) : ℤ)
          = ((Polynomial.rootMultiplicity α g.denom : ℕ) : ℤ) := by
        have h := hg; rw [ordAt] at h; linarith
      by_contra hlt
      have h1 : 1 ≤ Polynomial.rootMultiplicity α g.denom := Nat.one_le_iff_ne_zero.mpr hlt
      have h2 : (Polynomial.X - Polynomial.C α) ∣ g.denom := by
        simpa using (le_rootMultiplicity_iff hq).mp h1
      have h3 : (Polynomial.X - Polynomial.C α) ∣ g.num := by
        have h4 : 1 ≤ Polynomial.rootMultiplicity α g.num := by
          have hZ : (1 : ℤ) ≤ (Polynomial.rootMultiplicity α g.num : ℤ) := by
            rw [heq]; exact_mod_cast h1
          exact_mod_cast hZ
        simpa using (le_rootMultiplicity_iff hp).mp h4
      exact not_isUnit_X_sub_C α (hcop.isUnit_of_dvd' h3 h2)
  rcases eq_or_ne (g.num - Polynomial.C c * g.denom) 0 with hzero | hnonzero
  · refine absurd (sub_eq_zero.mp ?_) hne
    rw [hcomp, hzero, map_zero, zero_div]
  · have hrm : 1 ≤ Polynomial.rootMultiplicity α
        (g.num - Polynomial.C c * g.denom) := by
      simpa using (le_rootMultiplicity_iff hnonzero).mpr (by simpa using hdiv)
    rw [hcomp]
    rw [ordAt_div α (RatFunc.algebraMap_ne_zero hnonzero) (RatFunc.algebraMap_ne_zero hq)]
    rw [ordAt_algebraMap, ordAt_algebraMap, hqrm, Nat.cast_zero, sub_zero]
    exact_mod_cast hrm

/-- **Existence of the residue**: every rational function with `ordAt α r ≥ -1` has a residue. -/
theorem exists_residueAt (α : K) (r : RatFunc K) (h : -1 ≤ ordAt α r) :
    ∃ c : K, ResidueAt α r c := by
  rcases lt_trichotomy (ordAt α r) 0 with hlt | heq | hgt
  · have hr : ordAt α r = -1 := by omega
    have hr0 : r ≠ 0 := fun h0 => by rw [h0] at hr; simp at hr
    set A : RatFunc K := lin α with hAdef
    have hA : A ≠ 0 := lin_ne_zero α
    have hordg : ordAt α (A * r) = 0 := by
      rw [ordAt_mul α hA hr0, ordAt_lin, hr]; ring
    refine ⟨valueAt α (A * r), le_of_eq hr.symm, ?_⟩
    set c : K := valueAt α (A * r) with hcdef
    have hsplit : r - polePart α c = (A * r - algebraMap K (RatFunc K) c) / A := by
      rw [polePart_eq, ← hAdef]
      field_simp
    rw [hsplit]
    rcases eq_or_ne (A * r) (algebraMap K (RatFunc K) c) with hcase | hcase
    · simp [hcase]
    · have h1 : 1 ≤ ordAt α (A * r - algebraMap K (RatFunc K) c) :=
        one_le_ordAt_sub_valueAt hordg hcase
      rw [ordAt_div α (sub_ne_zero.mpr hcase) hA, ordAt_lin]
      omega
  · exact ⟨0, ResidueAt.of_ordAt_nonneg (le_of_eq heq.symm)⟩
  · exact ⟨0, ResidueAt.of_ordAt_nonneg (le_of_lt hgt)⟩

section DerivativeAlgebra

/-- The derivative of the inverse: `(f⁻¹)' = -(f'/f²)`. -/
lemma dRat_inv (f : RatFunc K) (hf : f ≠ 0) : dRat f⁻¹ = -(dRat f) / f ^ 2 := by
  have h1 : dRat f * f⁻¹ + f * dRat f⁻¹ = 0 := by
    have h := dRat_mul f f⁻¹
    rw [mul_inv_cancel₀ hf, dRat_one] at h
    exact h.symm
  have h2 : f * dRat f⁻¹ = -(dRat f * f⁻¹) := eq_neg_of_add_eq_zero_right h1
  have h3 : f * dRat f⁻¹ * f = -(dRat f) := by
    rw [h2]; field_simp
  rw [eq_div_iff (pow_ne_zero 2 hf)]
  rw [show dRat f⁻¹ * f ^ 2 = f * dRat f⁻¹ * f by ring]
  exact h3

/-- The logarithmic derivative of the inverse. -/
lemma dRat_inv_div (f : RatFunc K) (hf : f ≠ 0) : dRat f⁻¹ / f⁻¹ = -(dRat f / f) := by
  have h2 : f ^ 2 * f⁻¹ = f := by field_simp
  rw [dRat_inv f hf, ← neg_div, div_div, h2]

/-- **The logarithmic derivative of a product is the sum of the logarithmic derivatives.** -/
lemma dRat_mul_div (x y : RatFunc K) (hx : x ≠ 0) (hy : y ≠ 0) :
    dRat (x * y) / (x * y) = dRat x / x + dRat y / y := by
  rw [dRat_mul]
  field_simp

/-- **The logarithmic derivative of a power**: `(f^n)'/f^n = n·(f'/f)`. -/
lemma dRat_pow_div (f : RatFunc K) (hf : f ≠ 0) (m : ℕ) :
    dRat (f ^ m) / f ^ m = algebraMap K (RatFunc K) ((m : ℕ) : K) * (dRat f / f) := by
  have hcast : ((m : ℕ) : RatFunc K) = algebraMap K (RatFunc K) ((m : ℕ) : K) :=
    (map_natCast (algebraMap K (RatFunc K)) m).symm
  rw [dRat_pow, ← hcast]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hpow : f ^ (m - 1) * f = f ^ m := by rw [← pow_succ, Nat.sub_add_cancel hm]
    field_simp
    calc ((m : ℕ) : RatFunc K) * f ^ (m - 1) * dRat f * f
        = ((m : ℕ) : RatFunc K) * dRat f * (f ^ (m - 1) * f) := by ring
      _ = ((m : ℕ) : RatFunc K) * dRat f * f ^ m := by rw [hpow]

end DerivativeAlgebra

/-- `polePart` is `K`-linear in the residue. -/
lemma polePart_mul (α : K) (t c : K) :
    polePart α (t * c) = algebraMap K (RatFunc K) t * polePart α c := by
  rw [polePart_eq, polePart_eq, map_mul, mul_div_assoc]

/-- The elementary simple pole has residue `c`. -/
lemma residueAt_polePart (α : K) (c : K) : ResidueAt α (polePart α c) c := by
  rcases eq_or_ne c 0 with rfl | hc
  · refine ⟨?_, ?_⟩
    · rw [show polePart α (0 : K) = 0 from by rw [polePart_eq, map_zero, zero_div]]
      simp
    · simp [sub_self]
  · exact ⟨le_of_eq (ordAt_polePart α hc).symm, by simp [sub_self]⟩

/-- **A rational function that is finite and nonzero at `α` has holomorphic logarithmic
derivative** (`(log f)' = f'/f` is finite where `f` is finite and nonzero). -/
lemma zero_le_ordAt_dRat_div_self_of_ordAt_eq_zero {α : K} {f : RatFunc K} (hf : f ≠ 0)
    (h0 : ordAt α f = 0) : 0 ≤ ordAt α (dRat f / f) := by
  have hp : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hq : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hcop : IsCoprime f.num f.denom := RatFunc.isCoprime_num_denom f
  have heq : Polynomial.rootMultiplicity α f.num = Polynomial.rootMultiplicity α f.denom := by
    have hZ : ((Polynomial.rootMultiplicity α f.num : ℕ) : ℤ)
        = ((Polynomial.rootMultiplicity α f.denom : ℕ) : ℤ) := by
      have h := h0; rw [ordAt] at h; linarith
    exact_mod_cast hZ
  have hnum0 : Polynomial.rootMultiplicity α f.num = 0 := by
    by_contra h
    have h1 : 1 ≤ Polynomial.rootMultiplicity α f.num := Nat.one_le_iff_ne_zero.mpr h
    have h2 : (Polynomial.X - Polynomial.C α) ∣ f.num := by
      simpa using (le_rootMultiplicity_iff hp).mp h1
    have h3 : (Polynomial.X - Polynomial.C α) ∣ f.denom := by
      have h4 : 1 ≤ Polynomial.rootMultiplicity α f.denom := by rw [← heq]; exact h1
      simpa using (le_rootMultiplicity_iff hq).mp h4
    exact not_isUnit_X_sub_C α (hcop.isUnit_of_dvd' h2 h3)
  have hden0 : Polynomial.rootMultiplicity α f.denom = 0 := by rw [← heq, hnum0]
  rcases eq_or_ne (dRat f) 0 with hd0 | hd0
  · rw [hd0, zero_div]; simp
  · rw [ordAt_div α hd0 hf, h0, sub_zero]
    have hN : f.num.derivative * f.denom - f.num * f.denom.derivative ≠ 0 := by
      intro h
      exact hd0 (by rw [dRat_eq_div, h, map_zero, zero_div])
    rw [dRat_eq_div]
    rw [ordAt_div α (RatFunc.algebraMap_ne_zero hN)
      (pow_ne_zero 2 (RatFunc.algebraMap_ne_zero hq))]
    rw [ordAt_pow, ordAt_algebraMap, ordAt_algebraMap]
    have h1 : (0 : ℤ) ≤ (Polynomial.rootMultiplicity α
        (f.num.derivative * f.denom - f.num * f.denom.derivative) : ℤ) := Int.natCast_nonneg _
    have h2 : (Polynomial.rootMultiplicity α f.denom : ℤ) = 0 := by rw [hden0]; rfl
    rw [h2, mul_zero, sub_zero]
    exact h1

/-- **The residue of the logarithmic derivative.**  For `f ≠ 0` and any `α`,
`ResidueAt α ((dRat f)/f) (ordAt α f)`: at a zero or pole of `f` the logarithmic derivative has
the simple pole `ordAt α f/(X - α)`, while where `f` is finite and nonzero it is holomorphic. -/
theorem residueAt_dRat_div_self (f : RatFunc K) (hf : f ≠ 0) (α : K) :
    ResidueAt α (dRat f / f) ((ordAt α f : ℤ) : K) := by
  have hAne : lin α ≠ 0 := lin_ne_zero α
  have hlogA : dRat (lin α) / lin α = polePart α 1 := by
    have h1 : dRat (lin α) = 1 := by
      rw [lin, dRat_algebraMap, Polynomial.derivative_X_sub_C, map_one]
    rw [h1, polePart_eq, map_one]
  have hAm : ∀ m : ℕ, dRat ((lin α) ^ m) / ((lin α) ^ m) = polePart α ((m : ℕ) : K) := by
    intro m
    rw [dRat_pow_div (lin α) hAne m, hlogA, ← polePart_mul, mul_one]
  rcases lt_or_ge (ordAt α f) 0 with hn | hn
  · -- `α` is a pole of `f` (the case `ordAt α f < 0`)
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = -ordAt α f :=
      ⟨(-ordAt α f).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hAmne : (lin α) ^ m ≠ 0 := pow_ne_zero m hAne
    have hg : f * (lin α) ^ m ≠ 0 := mul_ne_zero hf hAmne
    have hordg : ordAt α (f * (lin α) ^ m) = 0 := by
      rw [ordAt_mul α hf hAmne, ordAt_pow, ordAt_lin, mul_one]
      omega
    have hsplit : dRat f / f
        = polePart α (-(m : K)) + dRat (f * (lin α) ^ m) / (f * (lin α) ^ m) := by
      have hlog : dRat (f * (lin α) ^ m) / (f * (lin α) ^ m)
          = dRat f / f + polePart α ((m : ℕ) : K) := by
        calc dRat (f * (lin α) ^ m) / (f * (lin α) ^ m)
            = dRat f / f + dRat ((lin α) ^ m) / ((lin α) ^ m) :=
              dRat_mul_div _ _ hf hAmne
          _ = dRat f / f + polePart α ((m : ℕ) : K) := by rw [hAm]
      rw [hlog, polePart_eq, polePart_eq, map_neg]
      field_simp
      ring
    rw [hsplit]
    have hres := ResidueAt.add (residueAt_polePart α (-(m : K)))
      (ResidueAt.of_ordAt_nonneg (zero_le_ordAt_dRat_div_self_of_ordAt_eq_zero hg hordg))
    have hcast : (-(m : K) : K) = ((ordAt α f : ℤ) : K) := by
      have h2 : (((m : ℤ)) : K) = (((-(ordAt α f) : ℤ)) : K) := by rw [hm]
      rw [Int.cast_neg, Int.cast_natCast] at h2
      rw [h2]; ring
    simpa [hcast] using hres

  · -- `α` is not a pole of `f` (the case `0 ≤ ordAt α f`)
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = ordAt α f :=
      ⟨(ordAt α f).toNat, Int.toNat_of_nonneg hn⟩
    have hAmne : (lin α) ^ m ≠ 0 := pow_ne_zero m hAne
    have hg : f / (lin α) ^ m ≠ 0 := div_ne_zero hf hAmne
    have hordg : ordAt α (f / (lin α) ^ m) = 0 := by
      rw [ordAt_div α hf hAmne, ordAt_pow, ordAt_lin, mul_one]
      omega
    have hfg : f = (lin α) ^ m * (f / (lin α) ^ m) := by
      field_simp
    have hsplit : dRat f / f
        = polePart α ((m : ℕ) : K) + dRat (f / (lin α) ^ m) / (f / (lin α) ^ m) := by
      calc dRat f / f
          = dRat ((lin α) ^ m * (f / (lin α) ^ m))
              / ((lin α) ^ m * (f / (lin α) ^ m)) := by rw [← hfg]
        _ = dRat ((lin α) ^ m) / ((lin α) ^ m)
              + dRat (f / (lin α) ^ m) / (f / (lin α) ^ m) :=
              dRat_mul_div _ _ hAmne hg
        _ = polePart α ((m : ℕ) : K) + dRat (f / (lin α) ^ m) / (f / (lin α) ^ m) := by
              rw [hAm]
    rw [hsplit]
    have hres := ResidueAt.add (residueAt_polePart α ((m : ℕ) : K))
      (ResidueAt.of_ordAt_nonneg (zero_le_ordAt_dRat_div_self_of_ordAt_eq_zero hg hordg))
    simpa [← hm] using hres
end Submission.CDT
