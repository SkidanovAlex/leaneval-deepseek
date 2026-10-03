/-
# `Submission.Work.FIArea7CF.qBilinDefs` — clash-free copy of `Submission.Work.FIArea7.qBilinDefs`

Imports redirected to the `FIArea7CF` copies; renamed: mem_gBox_iff→qb_mem_gBox_iff.  The workspace contains several
incompatible declarations of `Work.FIArea7.mem_gBox_iff` (and of `norm_uniCoeff_le`,
`log_pow_le_rpow`, `gnorm_mk_eq`), so the amended area-7 assembly and the *FI* §§19–26
chain can only meet through copies.  See NOTES §63.
-/
import Mathlib
import Submission.Work.FIArea7.Classical172Defs
import Submission.Work.FIArea7.dirichletSym_mul
import Submission.Work.FIArea7.jacobiSym_sq_add_sq
import Submission.Work.FIArea7.cardDiscBoxLe

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Multiplicativity of the Gaussian norm, and the normalisation `ξ_w(1) = 1` -/

/-- `|zw|² = |z|²|w|²`. -/
lemma gnorm_mul_g (z w : GaussianInt) :
    Work.FIPlan.gnorm (z * w) = Work.FIPlan.gnorm z * Work.FIPlan.gnorm w := by
  simp [Work.FIPlan.gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

/-- `|z₁⋯z_k|² = ∏ᵢ |zᵢ|²`. -/
lemma gnorm_prod_univ {k : ℕ} (t : Fin k → GaussianInt) :
    Work.FIPlan.gnorm (∏ i, t i) = ∏ i, Work.FIPlan.gnorm (t i) := by
  induction (Finset.univ : Finset (Fin k)) using Finset.induction with
  | empty => simp [Work.FIPlan.gnorm]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, gnorm_mul_g, ih]

/-- `|w|² = (Re w)² + (Im w)²` as a natural number. -/
lemma gnorm_eq_natAbs_g (z : GaussianInt) :
    Work.FIPlan.gnorm z = (z.re ^ 2 + z.im ^ 2).natAbs := by
  have h1 : ((Work.FIPlan.gnorm z : ℕ) : ℤ) = z.re ^ 2 + z.im ^ 2 := norm_eq z
  have h2 : z.re ^ 2 + z.im ^ 2 = (((z.re ^ 2 + z.im ^ 2).natAbs : ℕ) : ℤ) :=
    (Int.natAbs_of_nonneg (by positivity)).symm
  exact Nat.cast_injective (h1.trans h2)

/-- *FI* (19.8): `ξ_w(1) = 1` for primary primitive `w`. -/
lemma dirichletSym_primary_one {w : GaussianInt} (hprim : Work.FIPlan.IsPrimary w)
    (hcop : IsCoprime w.re w.im) : DirichletSym w 1 = 1 := by
  obtain ⟨hro, hie, _⟩ := hprim
  have h := jacobiSym_sq_add_sq hro hie hcop
  rw [show DirichletSym w 1 = jacobiSym w.re (Work.FIPlan.gnorm w) by simp [DirichletSym],
    gnorm_eq_natAbs_g]
  exact h

/-! ## 1b. Box membership -/

lemma qb_mem_gBox_iff {R : ℤ} {z : GaussianInt} :
    z ∈ Work.FIPlan.gBox R ↔ z.re ∈ Finset.Icc (-R) R ∧ z.im ∈ Finset.Icc (-R) R := by
  rw [Work.FIPlan.gBox, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(Finset.mem_product.mp hp).1, (Finset.mem_product.mp hp).2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(z.re, z.im), Finset.mem_product.mpr ⟨h1, h2⟩, Zsqrtd.ext rfl rfl⟩

lemma mem_gBox_of_coords {R : ℤ} {z : GaussianInt} (h1 : |z.re| ≤ R) (h2 : |z.im| ≤ R) :
    z ∈ Work.FIPlan.gBox R := by
  rw [qb_mem_gBox_iff]
  obtain ⟨h1a, h1b⟩ := abs_le.mp h1
  obtain ⟨h2a, h2b⟩ := abs_le.mp h2
  exact ⟨Finset.mem_Icc.mpr ⟨h1a, h1b⟩, Finset.mem_Icc.mpr ⟨h2a, h2b⟩⟩

/-- `(Re z)² ≤ |z|²` as real numbers. -/
lemma re_sq_le_gnorm (z : GaussianInt) : (z.re : ℝ) ^ 2 ≤ (Work.FIPlan.gnorm z : ℝ) := by
  have h : ((Work.FIPlan.gnorm z : ℕ) : ℤ) = z.re ^ 2 + z.im ^ 2 := norm_eq z
  have h2 : z.re ^ 2 ≤ ((Work.FIPlan.gnorm z : ℕ) : ℤ) := by
    rw [h]; nlinarith [sq_nonneg z.im]
  have h3 : ((z.re ^ 2 : ℤ) : ℝ) ≤ ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by exact_mod_cast h2
  calc (z.re : ℝ) ^ 2 = ((z.re ^ 2 : ℤ) : ℝ) := by push_cast; ring
    _ ≤ _ := h3

/-- `(Im z)² ≤ |z|²` as real numbers. -/
lemma im_sq_le_gnorm (z : GaussianInt) : (z.im : ℝ) ^ 2 ≤ (Work.FIPlan.gnorm z : ℝ) := by
  have h : ((Work.FIPlan.gnorm z : ℕ) : ℤ) = z.re ^ 2 + z.im ^ 2 := norm_eq z
  have h2 : z.im ^ 2 ≤ ((Work.FIPlan.gnorm z : ℕ) : ℤ) := by
    rw [h]; nlinarith [sq_nonneg z.re]
  have h3 : ((z.im ^ 2 : ℤ) : ℝ) ≤ ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by exact_mod_cast h2
  calc (z.im : ℝ) ^ 2 = ((z.im ^ 2 : ℤ) : ℝ) := by push_cast; ring
    _ ≤ _ := h3

/-- If `|z|² ≤ R²` and `0 ≤ R` then `z ∈ gBox R`. -/
lemma mem_gBox_of_gnorm_sq_le {R : ℤ} (hR : 0 ≤ R) {z : GaussianInt}
    (h : (Work.FIPlan.gnorm z : ℝ) ≤ ((R : ℤ) : ℝ) ^ 2) : z ∈ Work.FIPlan.gBox R := by
  have hR0 : (0 : ℝ) ≤ ((R : ℤ) : ℝ) := by exact_mod_cast hR
  have key : ∀ a : ℝ, a ^ 2 ≤ ((R : ℤ) : ℝ) ^ 2 → |a| ≤ ((R : ℤ) : ℝ) := fun a ha =>
    (sq_le_sq.mp ha).trans_eq (abs_of_nonneg hR0)
  have h1 : |((z.re : ℤ) : ℝ)| ≤ ((R : ℤ) : ℝ) := key _ (le_trans (re_sq_le_gnorm z) h)
  have h2 : |((z.im : ℤ) : ℝ)| ≤ ((R : ℤ) : ℝ) := key _ (le_trans (im_sq_le_gnorm z) h)
  refine mem_gBox_of_coords ?_ ?_
  · obtain ⟨a, b⟩ := abs_le.mp h1
    exact abs_le.mpr ⟨by exact_mod_cast a, by exact_mod_cast b⟩
  · obtain ⟨a, b⟩ := abs_le.mp h2
    exact abs_le.mpr ⟨by exact_mod_cast a, by exact_mod_cast b⟩

/-- If `|z|² ≤ N⁶` with `N ≥ 1` then `z ∈ gBox ⌈N³⌉`. -/
lemma mem_gBox_ceil_of_gnorm_le {N : ℝ} (hN : 1 ≤ N) {z : GaussianInt}
    (hz : (Work.FIPlan.gnorm z : ℝ) ≤ N ^ 6) : z ∈ Work.FIPlan.gBox ⌈N ^ 3⌉ := by
  have hceil0 : (0 : ℤ) ≤ ⌈N ^ 3⌉ := by
    have : (0 : ℝ) ≤ (((⌈N ^ 3⌉ : ℤ)) : ℝ) := le_trans (by positivity) (Int.le_ceil (N ^ 3))
    exact_mod_cast this
  refine mem_gBox_of_gnorm_sq_le hceil0 ?_
  calc (Work.FIPlan.gnorm z : ℝ) ≤ N ^ 6 := hz
    _ = (N ^ 3) ^ 2 := by ring
    _ ≤ ((((⌈N ^ 3⌉ : ℤ)) : ℝ)) ^ 2 := by
        exact pow_le_pow_left₀ (by positivity) (Int.le_ceil (N ^ 3)) 2

lemma QBilin_eq_bilinSum (Rw Rz : ℤ) (α β : GaussianInt → ℂ) :
    QBilin Rw Rz α β
      = ∑ w ∈ Work.FIPlan.gBox Rw,
          α w * (∑ z ∈ Work.FIPlan.gBox Rz, β z * ((DirichletSym w z : ℤ) : ℂ)) := by
  rw [QBilin]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  ring

/-! ## 2. Tuples, boxes and the `6`-fold convolution -/

/-- The product of the entries of a tuple of Gaussian integers. -/
def tupProd {k : ℕ} (t : Fin k → GaussianInt) : GaussianInt := ∏ i, t i

/-- All `k`-tuples drawn from the box `gBox R`. -/
def boxTup (k : ℕ) (R : ℤ) : Finset (Fin k → GaussianInt) :=
  Fintype.piFinset (fun _ : Fin k => Work.FIPlan.gBox R)

/-- **The `6`-fold Dirichlet convolution of `β`**, truncated to the box `gBox R`:

  `conv6 R β u = Σ_{z₁,…,z₆ ∈ gBox R} [z₁⋯z₆ = u]·β_{z₁}⋯β_{z₆}`.

For `β` supported in the disc `|z|² ≤ N` this realises the *FI* coefficient
`β̃_z = Σ_{z₁⋯z₆=z} β_{z₁}⋯β_{z₆}` of p. 1027. -/
def conv6 (R : ℤ) (β : GaussianInt → ℂ) (u : GaussianInt) : ℂ :=
  ∑ t ∈ boxTup 6 R, if tupProd t = u then (∏ i : Fin 6, β (t i)) else 0

/-- The disc `|u|² ≤ X` cut out of the box `gBox R`. -/
def gDisc (R : ℤ) (X : ℝ) : Finset GaussianInt :=
  (Work.FIPlan.gBox R).filter (fun u => (Work.FIPlan.gnorm u : ℝ) ≤ X)

/-! ## 5. The coefficient support and the coherent pairs -/

/-- The admissible coefficient support inside a box: primary primitive `w ∈ gBox Rw` of norm
`≤ M` (the set on which the coefficients `α` of *FI* (21.1) may be nonzero). -/
def coeffSuppBox (M : ℝ) (Rw : ℤ) : Finset GaussianInt :=
  (Work.FIPlan.gBox Rw).filter (fun w => Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧
    (Work.FIPlan.gnorm w : ℝ) ≤ M)

/-- The **coherent** pairs of the coefficient support: pairs whose norm product has odd part a
square.  This is a *necessary* condition (*FI* Lemma 21.1 and its proof) for the complete sum
`Σ_{ζ (mod q)} ξ_{w₁}(ζ)ξ_{w₂}(ζ)`, `q = |w₁|²|w₂|²`, not to vanish. -/
def coherentPairs (M : ℝ) (Rw : ℤ) : Finset (GaussianInt × GaussianInt) :=
  ((coeffSuppBox M Rw).product (coeffSuppBox M Rw)).filter
    (fun p => ∃ s : ℕ, Work.FIPlan.oddPart (Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2) = s ^ 2)

/-- `#coeffSuppBox ≤ 9M`: the disc-in-box count `Work.FIArea7.cardDiscBoxLe`. -/
lemma card_coeffSuppBox_le (M : ℝ) (Rw : ℤ) (hM : 1 ≤ M) :
    ((coeffSuppBox M Rw).card : ℝ) ≤ 9 * M := by
  classical
  have hsub : coeffSuppBox M Rw ⊆ (Work.FIPlan.gBox Rw).filter
      (fun w => (Work.FIPlan.gnorm w : ℝ) ≤ M) := by
    intro w hw
    rw [coeffSuppBox, Finset.mem_filter] at hw
    exact Finset.mem_filter.mpr ⟨hw.1, hw.2.2.2⟩
  calc ((coeffSuppBox M Rw).card : ℝ)
      ≤ (((Work.FIPlan.gBox Rw).filter (fun w => (Work.FIPlan.gnorm w : ℝ) ≤ M)).card : ℝ) := by
        exact Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ 9 * M := cardDiscBoxLe Rw M hM

/-! ## 3. Pairing the `6`-fold convolution with a function of the product -/

lemma sum_conv6_mul_aux (R : ℤ) (β : GaussianInt → ℂ) (F : GaussianInt → ℂ)
    (U : Finset GaussianInt) :
    ∑ u ∈ U, conv6 R β u * F u
      = ∑ t ∈ boxTup 6 R,
          (∏ i : Fin 6, β (t i)) * (if tupProd t ∈ U then F (tupProd t) else 0) := by
  classical
  have h2 : (∑ u ∈ U, conv6 R β u * F u)
      = ∑ u ∈ U, ∑ t ∈ boxTup 6 R,
          (if tupProd t = u then (∏ i : Fin 6, β (t i)) else 0) * F u := by
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [conv6, Finset.sum_mul]
  rw [h2, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  have h1 : ∀ u ∈ U, ((if tupProd t = u then (∏ i : Fin 6, β (t i)) else 0)) * F u
      = (∏ i : Fin 6, β (t i)) * (if tupProd t = u then F u else 0) := by
    intro u _
    by_cases h : tupProd t = u <;> simp [h]
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, Finset.sum_ite_eq]

/-- **Pairing lemma for the `6`-fold convolution.**  If every product of a tuple of the box which
carries a nonzero coefficient lands in `U`, then

  `Σ_{u ∈ U} conv6 R β u · F u = Σ_{z₁,…,z₆ ∈ box} β_{z₁}⋯β_{z₆}·F(z₁⋯z₆)`. -/
lemma sum_conv6_mul (R : ℤ) (β : GaussianInt → ℂ) (F : GaussianInt → ℂ)
    (U : Finset GaussianInt)
    (hU : ∀ t ∈ boxTup 6 R, (∏ i : Fin 6, β (t i)) ≠ 0 → tupProd t ∈ U) :
    ∑ u ∈ U, conv6 R β u * F u
      = ∑ t ∈ boxTup 6 R, (∏ i : Fin 6, β (t i)) * F (tupProd t) := by
  rw [sum_conv6_mul_aux]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  by_cases h : (∏ i : Fin 6, β (t i)) = 0
  · simp [h]
  · rw [if_pos (hU t ht h)]

/-- `conv6` vanishes at `u` whose norm exceeds `N⁶`, for `β` supported in `|z|² ≤ N`. -/
lemma conv6_eq_zero_of_support {R : ℤ} {β : GaussianInt → ℂ} {N : ℝ} (_hN : 0 ≤ N)
    (hβ : ∀ z, β z ≠ 0 → (Work.FIPlan.gnorm z : ℝ) ≤ N) (u : GaussianInt)
    (hu : N ^ 6 < (Work.FIPlan.gnorm u : ℝ)) : conv6 R β u = 0 := by
  classical
  unfold conv6
  rw [Finset.sum_eq_zero]
  intro t _
  by_cases h : tupProd t = u
  · subst h
    have hprod : (∏ i : Fin 6, β (t i)) = 0 := by
      by_contra hne
      have hne' : ∀ i : Fin 6, β (t i) ≠ 0 :=
        fun i => (Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ i)
      have hb : ∀ i : Fin 6, (Work.FIPlan.gnorm (t i) : ℝ) ≤ N := fun i => hβ _ (hne' i)
      have hle : (Work.FIPlan.gnorm (tupProd t) : ℝ) ≤ N ^ 6 := by
        rw [tupProd, gnorm_prod_univ]
        have h1 : (((∏ i : Fin 6, Work.FIPlan.gnorm (t i)) : ℕ) : ℝ)
            = ∏ i : Fin 6, ((Work.FIPlan.gnorm (t i) : ℕ) : ℝ) := by push_cast; ring
        rw [h1]
        calc ∏ i : Fin 6, ((Work.FIPlan.gnorm (t i) : ℕ) : ℝ)
            ≤ ∏ _i : Fin 6, N := by
              refine Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => hb i)
          _ = N ^ 6 := by simp
      linarith
    rw [hprod]; simp
  · simp [h]

/-! ## 4. Multiplicativity of the Dirichlet symbol along a tuple -/

/-- `ξ_w(z₁⋯z_k) = ∏ᵢ ξ_w(zᵢ)` for primary primitive `w` (*FI* (19.2)). -/
lemma prod_dirichletSym {w : GaussianInt} (hprim : Work.FIPlan.IsPrimary w)
    (hcop : IsCoprime w.re w.im) {k : ℕ} (t : Fin k → GaussianInt) :
    (∏ i, ((DirichletSym w (t i) : ℤ) : ℂ)) = ((DirichletSym w (tupProd t) : ℤ) : ℂ) := by
  have hZ : (∏ i, DirichletSym w (t i)) = DirichletSym w (tupProd t) := by
    rw [tupProd]
    induction (Finset.univ : Finset (Fin k)) using Finset.induction with
    | empty => simp [dirichletSym_primary_one hprim hcop]
    | insert i s hi ih =>
        rw [Finset.prod_insert hi, Finset.prod_insert hi, ih,
          ← dirichletSym_mul hprim hcop]
  rw [← hZ]
  push_cast
  ring

end

end Work.FIArea7
