/-
# `Work.FIArea7.Pub213.prop213Pub` — *FI* Proposition 21.3 (21.10), direct route

An independent proof of `Work.FIArea7.Prop213` along *FI* pp. 1026–1027, using
`Work.FIArea7.qBilin_holder6` (*FI* (21.9)) for the Hölder step and the paper's "arrangement"
(p. 1027, `Pub213.exists_decomp`) together with *FI* (19.12) for primary primitive pairs
(`Pub213.dirichletSym_reciprocity_pp`) to obtain the transposed form of (21.9).

Let `C` be the monoid of `Prop213Aux.IsC` (units, powers of `1+i`, odd naturals).  Every nonzero
`z` is `c·z'` with `c ∈ C` and `z'` primary primitive.  Writing the `z`-sum of `QBilin` in these
classes, the `w`-coefficient `α_w ξ_w(c)` stays bounded on primary primitive `w` of norm `≤ M`,
and the class-`c` coefficient `β_c(z') = Σ_{z : c z' = z} β_z` is supported on primary primitive
`z'` of norm `≤ N/|c|²`.  Hence both (21.9) at `(M, N/|c|²)` and — after exchanging `w` and `z'` by
(19.12) — (21.9) at `(N/|c|², M)` bound each class, and the smaller of the two is
`≤ 3(M N_c^{11/12} + N_c^{11/12} M)·log^A`.  Summing over `c ∈ C` with
`Σ_c |c|^{-11/6}, Σ_c |c|^{-2} < ∞` (`Pub213.sum_CBox_rpow_le`) gives (21.10).
-/
import Mathlib
import Submission.Work.FIArea7.Pub213.Defs
import Submission.Work.FIArea7.Pub213.exists_decomp
import Submission.Work.FIArea7.Pub213.dirichletSym_reciprocity_pp
import Submission.Work.FIArea7.Pub213.sum_CBox_rpow_le
import Submission.Work.FIArea7.dirichletSym_mul
import Submission.Work.FIArea7.Classical172Defs



set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.FIArea7.Pub213

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The chosen `C`-part and primary primitive part of a nonzero Gaussian integer -/

/-- The chosen class `c ∈ C` of the arrangement. -/
def cPart (z : GaussianInt) : GaussianInt :=
  if h : z ≠ 0 then Classical.choose (exists_decomp z h) else 1

/-- The chosen primary primitive partner `z'` (`z = cPart z * ppPart z`). -/
def ppPart (z : GaussianInt) : GaussianInt :=
  if h : z ≠ 0 then
    Classical.choose (Classical.choose_spec (exists_decomp z h)).2
  else 1

lemma cPart_isC {z : GaussianInt} (hz : z ≠ 0) : Prop213Aux.IsC (cPart z) := by
  rw [cPart, dif_pos hz]
  exact (Classical.choose_spec (exists_decomp z hz)).1

lemma ppPart_isPP {z : GaussianInt} (hz : z ≠ 0) : Prop213Aux.IsPP (ppPart z) := by
  rw [ppPart, dif_pos hz]
  exact (Classical.choose_spec (Classical.choose_spec (exists_decomp z hz)).2).1

lemma cPart_mul_ppPart {z : GaussianInt} (hz : z ≠ 0) : cPart z * ppPart z = z := by
  rw [cPart, ppPart, dif_pos hz, dif_pos hz]
  exact (Classical.choose_spec (Classical.choose_spec (exists_decomp z hz)).2).2

lemma one_le_gnorm_ppPart {z : GaussianInt} (hz : z ≠ 0) :
    1 ≤ Work.FIPlan.gnorm (ppPart z) := by
  have h := Prop213Aux.IsPP.gnorm_pos (ppPart_isPP hz)
  omega

lemma ne_zero_cPart {z : GaussianInt} (hz : z ≠ 0) : cPart z ≠ 0 := by
  intro h
  have hz' : z = 0 := by rw [← cPart_mul_ppPart hz, h, zero_mul]
  exact hz hz'

lemma gnorm_cPart_mul_ppPart {z : GaussianInt} (hz : z ≠ 0) :
    Work.FIPlan.gnorm (cPart z) * Work.FIPlan.gnorm (ppPart z) = Work.FIPlan.gnorm z := by
  rw [← Work.FIArea7.gnorm_mul, cPart_mul_ppPart hz]

/-- `|z|²` of the primary primitive part never exceeds that of `z`. -/
lemma gnorm_ppPart_le {z : GaussianInt} (hz : z ≠ 0) :
    Work.FIPlan.gnorm (ppPart z) ≤ Work.FIPlan.gnorm z := by
  have h := gnorm_cPart_mul_ppPart hz
  have hpos : 1 ≤ Work.FIPlan.gnorm (cPart z) :=
    Nat.one_le_iff_ne_zero.mpr (fun h0 => ne_zero_cPart hz (Work.FIArea7.gnorm_eq_zero_iff.mp h0))
  calc Work.FIPlan.gnorm (ppPart z) = 1 * Work.FIPlan.gnorm (ppPart z) := (one_mul _).symm
    _ ≤ Work.FIPlan.gnorm (cPart z) * Work.FIPlan.gnorm (ppPart z) :=
        Nat.mul_le_mul_right _ hpos
    _ = Work.FIPlan.gnorm z := h

/-! ## 2. Boxes -/

lemma mem_gBox_coords {R : ℤ} {z : GaussianInt} (hz : z ∈ Work.FIPlan.gBox R) :
    -R ≤ z.re ∧ z.re ≤ R ∧ -R ≤ z.im ∧ z.im ≤ R := by
  rw [Work.FIPlan.gBox, Finset.mem_image] at hz
  obtain ⟨p, hp, hpz⟩ := hz
  rw [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
  rw [← hpz]
  exact ⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2⟩

lemma mem_gBox_of_coords {R : ℤ} {z : GaussianInt} (h1 : -R ≤ z.re) (h2 : z.re ≤ R)
    (h3 : -R ≤ z.im) (h4 : z.im ≤ R) : z ∈ Work.FIPlan.gBox R := by
  rw [Work.FIPlan.gBox, Finset.mem_image]
  refine ⟨(z.re, z.im), ?_, ?_⟩
  · rw [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  · cases z
    rfl

lemma gBox_eq_empty_of_neg {R : ℤ} (hR : R < 0) : Work.FIPlan.gBox R = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
  obtain ⟨h1, h2, -, -⟩ := mem_gBox_coords hz
  omega

lemma gnorm_le_two_sq {R : ℤ} (hR : 0 ≤ R) {z : GaussianInt}
    (hz : z ∈ Work.FIPlan.gBox R) : (Work.FIPlan.gnorm z : ℤ) ≤ 2 * R ^ 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_gBox_coords hz
  have hcoords : (Work.FIPlan.gnorm z : ℤ) = z.re ^ 2 + z.im ^ 2 := Work.FIArea7.norm_eq z
  have hzre : z.re ^ 2 ≤ R ^ 2 := by
    have h : |z.re| ≤ R := abs_le.mpr ⟨h1, h2⟩
    calc z.re ^ 2 = |z.re| ^ 2 := (sq_abs z.re).symm
      _ ≤ R ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  have hzim : z.im ^ 2 ≤ R ^ 2 := by
    have h : |z.im| ≤ R := abs_le.mpr ⟨h3, h4⟩
    calc z.im ^ 2 = |z.im| ^ 2 := (sq_abs z.im).symm
      _ ≤ R ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [hcoords]; linarith

/-- A box containing every primary primitive part of a nonzero element of `gBox R`. -/
def ppBox (R : ℤ) : ℤ := 2 * max R 0 + 1

lemma abs_re_cast_le_sqrt {z : GaussianInt} :
    |(z.re : ℝ)| ≤ Real.sqrt ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by
  have hsq : (z.re : ℝ) ^ 2 ≤ ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by
    have h2 : (Work.FIPlan.gnorm z : ℤ) = z.re ^ 2 + z.im ^ 2 := Work.FIArea7.norm_eq z
    have h3 : (z.re : ℤ) ^ 2 ≤ (Work.FIPlan.gnorm z : ℤ) := by rw [h2]; nlinarith [sq_nonneg z.im]
    exact_mod_cast h3
  calc |(z.re : ℝ)| = Real.sqrt ((z.re : ℝ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((Work.FIPlan.gnorm z : ℕ) : ℝ) := Real.sqrt_le_sqrt hsq

lemma abs_im_cast_le_sqrt {z : GaussianInt} :
    |(z.im : ℝ)| ≤ Real.sqrt ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by
  have hsq : (z.im : ℝ) ^ 2 ≤ ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by
    have h2 : (Work.FIPlan.gnorm z : ℤ) = z.re ^ 2 + z.im ^ 2 := Work.FIArea7.norm_eq z
    have h3 : (z.im : ℤ) ^ 2 ≤ (Work.FIPlan.gnorm z : ℤ) := by rw [h2]; nlinarith [sq_nonneg z.re]
    exact_mod_cast h3
  calc |(z.im : ℝ)| = Real.sqrt ((z.im : ℝ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((Work.FIPlan.gnorm z : ℕ) : ℝ) := Real.sqrt_le_sqrt hsq

lemma sqrt_ppPart_le {R : ℤ} (hR : 0 ≤ R) {z : GaussianInt}
    (hz : z ∈ Work.FIPlan.gBox R) (hz0 : z ≠ 0) :
    Real.sqrt ((Work.FIPlan.gnorm (ppPart z) : ℕ) : ℝ) ≤ 2 * (max R 0 : ℝ) + 1 := by
  have hgn : ((Work.FIPlan.gnorm (ppPart z) : ℕ) : ℝ) ≤ ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by
    exact_mod_cast gnorm_ppPart_le hz0
  have hgn2 : ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ 2 * (R : ℝ) ^ 2 := by
    have h := gnorm_le_two_sq hR hz
    exact_mod_cast h
  have h2 : Real.sqrt ((Work.FIPlan.gnorm (ppPart z) : ℕ) : ℝ)
      ≤ Real.sqrt (2 * (R : ℝ) ^ 2) := Real.sqrt_le_sqrt (le_trans hgn hgn2)
  have h3 : Real.sqrt (2 * (R : ℝ) ^ 2) ≤ 2 * (max R 0 : ℝ) + 1 := by
    have hmax : (R : ℝ) ≤ (max R 0 : ℝ) := by exact_mod_cast le_max_left R 0
    have hR0 : (0 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_nonneg ((2 : ℝ) * (max R 0 : ℝ))]
  exact le_trans h2 h3

lemma ppPart_mem_ppBox {R : ℤ} (hR : 0 ≤ R) {z : GaussianInt}
    (hz : z ∈ Work.FIPlan.gBox R) (hz0 : z ≠ 0) : ppPart z ∈ Work.FIPlan.gBox (ppBox R) := by
  have hsqrt := sqrt_ppPart_le hR hz hz0
  have hcast : ((ppBox R : ℤ) : ℝ) = 2 * (max R 0 : ℝ) + 1 := by
    simp only [ppBox]; push_cast; ring
  have hre : |(ppPart z).re| ≤ ppBox R := by
    have h1 : |(((ppPart z).re : ℤ) : ℝ)| ≤ 2 * (max R 0 : ℝ) + 1 :=
      le_trans (abs_re_cast_le_sqrt (z := ppPart z)) hsqrt
    have h2 : |(((ppPart z).re : ℤ) : ℝ)| ≤ ((ppBox R : ℤ) : ℝ) := by rw [hcast]; exact h1
    exact_mod_cast h2
  have him : |(ppPart z).im| ≤ ppBox R := by
    have h1 : |(((ppPart z).im : ℤ) : ℝ)| ≤ 2 * (max R 0 : ℝ) + 1 :=
      le_trans (abs_im_cast_le_sqrt (z := ppPart z)) hsqrt
    have h2 : |(((ppPart z).im : ℤ) : ℝ)| ≤ ((ppBox R : ℤ) : ℝ) := by rw [hcast]; exact h1
    exact_mod_cast h2
  refine mem_gBox_of_coords ?_ ?_ ?_ ?_
  · have := (abs_le.mp hre).1; omega
  · have := (abs_le.mp hre).2; omega
  · have := (abs_le.mp him).1; omega
  · have := (abs_le.mp him).2; omega

/-! ## 3. The class splitting of the `z`-sum -/

/-- The nonzero elements of the box belonging to the class `c`. -/
def zClass (Rz : ℤ) (c : GaussianInt) : Finset GaussianInt :=
  (Work.FIPlan.gBox Rz).filter (fun z => z ≠ 0 ∧ cPart z = c)

/-- The elements of the class `c` whose primary primitive part is `z'`. -/
def zClassP (Rz : ℤ) (c z' : GaussianInt) : Finset GaussianInt :=
  (Work.FIPlan.gBox Rz).filter (fun z => z ≠ 0 ∧ cPart z = c ∧ ppPart z = z')

/-- The coefficient of the class `c`: `β_c(z') = Σ_{z : cPart z = c, ppPart z = z'} β z`. -/
def betaC (Rz : ℤ) (c : GaussianInt) (β : GaussianInt → ℂ) : GaussianInt → ℂ :=
  fun z' => ∑ z ∈ zClassP Rz c z', β z

/-- The coefficient of the class `c` on the `w`-side: `α_c(w) = α_w · ξ_w(c)`. -/
def alphaC (c : GaussianInt) (α : GaussianInt → ℂ) : GaussianInt → ℂ :=
  fun w => α w * (((DirichletSym w c : ℤ)) : ℂ)

lemma mem_zClass {Rz : ℤ} {c z : GaussianInt} :
    z ∈ zClass Rz c ↔ z ∈ Work.FIPlan.gBox Rz ∧ z ≠ 0 ∧ cPart z = c := by
  simp only [zClass, Finset.mem_filter]

lemma mem_zClassP {Rz : ℤ} {c z' z : GaussianInt} :
    z ∈ zClassP Rz c z' ↔ z ∈ Work.FIPlan.gBox Rz ∧ z ≠ 0 ∧ cPart z = c ∧ ppPart z = z' := by
  simp only [zClassP, Finset.mem_filter]

lemma zClassP_eq_filter (Rz : ℤ) (c z' : GaussianInt) :
    zClassP Rz c z' = (zClass Rz c).filter (fun z => ppPart z = z') := by
  simp only [zClassP, zClass, Finset.filter_filter, and_assoc]

/-- **The arrangement identity.**  For primary primitive `w`, the `z`-sum over the elements of the
class `c` is `ξ_w(c)` times the box sum with the class-`c` coefficient. -/
lemma class_sum_eq {Rz R' : ℤ} {w c : GaussianInt} {β : GaussianInt → ℂ}
    (hw : Prop213Aux.IsPP w)
    (hbox : ∀ z ∈ zClass Rz c, ppPart z ∈ Work.FIPlan.gBox R') :
    ∑ z ∈ zClass Rz c, β z * ((DirichletSym w z : ℤ) : ℂ)
      = ((DirichletSym w c : ℤ) : ℂ) *
        ∑ z' ∈ Work.FIPlan.gBox R', betaC Rz c β z' * ((DirichletSym w z' : ℤ) : ℂ) := by
  have hstep1 : ∑ z ∈ zClass Rz c, β z * ((DirichletSym w z : ℤ) : ℂ)
      = ((DirichletSym w c : ℤ) : ℂ)
          * ∑ z ∈ zClass Rz c, β z * ((DirichletSym w (ppPart z) : ℤ) : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [mem_zClass] at hz
    obtain ⟨-, hz0, hzc⟩ := hz
    have hxi : ((DirichletSym w z : ℤ) : ℂ)
        = ((DirichletSym w c : ℤ) : ℂ) * ((DirichletSym w (ppPart z) : ℤ) : ℂ) := by
      conv_lhs => rw [← cPart_mul_ppPart hz0]
      rw [dirichletSym_mul hw.1 hw.2]
      push_cast
      rw [hzc]
    rw [hxi]
    ring
  rw [hstep1]
  congr 1
  have hswap : ∑ z ∈ zClass Rz c, β z * ((DirichletSym w (ppPart z) : ℤ) : ℂ)
      = ∑ z' ∈ Work.FIPlan.gBox R',
          (∑ z ∈ (zClass Rz c).filter (fun z => ppPart z = z'), β z)
            * ((DirichletSym w z' : ℤ) : ℂ) := by
    have h1 : ∑ z ∈ zClass Rz c, β z * ((DirichletSym w (ppPart z) : ℤ) : ℂ)
        = ∑ z ∈ zClass Rz c, ∑ z' ∈ Work.FIPlan.gBox R',
            (if ppPart z = z' then β z * ((DirichletSym w z' : ℤ) : ℂ) else 0) := by
      refine Finset.sum_congr rfl fun z hz => ?_
      have hsum := Finset.sum_eq_single (ppPart z)
        (s := Work.FIPlan.gBox R')
        (f := fun z' => if ppPart z = z' then β z * ((DirichletSym w z' : ℤ) : ℂ) else 0)
        (by intro z' _ hne; rw [if_neg (fun h => hne h.symm)])
        (by intro hmem; exact absurd (hbox z hz) hmem)
      rw [if_pos rfl] at hsum
      exact hsum.symm
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun z' _ => ?_
    rw [← Finset.sum_filter, Finset.sum_mul]
  rw [hswap]
  refine Finset.sum_congr rfl fun z' _ => ?_
  rw [betaC, zClassP_eq_filter]

end

end Work.FIArea7.Pub213
