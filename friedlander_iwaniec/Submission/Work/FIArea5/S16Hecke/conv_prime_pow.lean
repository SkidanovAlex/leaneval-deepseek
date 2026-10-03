/-
# `Submission.Work.FIArea5.S16Hecke.conv_prime_pow`

The four-fold Dirichlet convolution
`λ_1 ⍟ λ_{χ₁} ⍟ λ_{χ₂} ⍟ λ_{χ₁χ₂}` of Hecke eigenvalue sequences (for real, multiplicative,
bounded characters `χ₁, χ₂` of `ℤ[i]`) takes, at a prime power `p^e`, a **non-negative real**
value.

This is the local (Euler factor) positivity underlying `hecke_prod_coeff_nonneg`: it says that
the `p`-Euler factor of the product
`L(s, 1)L(s, χ₁)L(s, χ₂)L(s, χ₁χ₂)` has non-negative coefficients.

The proof classifies the local factor of `λ_χ(ν) = heckeLam χ 0 (p^ν)` by the splitting
behaviour of `p` in `ℤ[i]` (`heckeLam_splitSum`, `heckeLam_inertSum`):

* `p = 2`: every local factor is the Kronecker delta (`heckeLam_even`), so the value is `0`
  (or `1` when `e = 0`);
* `p = 1 mod 4` (split, `p = π π̄` primary): `λ_χ(p^ν) = geo (χ π) (χ π̄) ν`, i.e. the local
  factor is `1/((1 - χ(π)T)(1 - χ(π̄)T))`.  The four-fold product is therefore
  `Gab(χ₁π, χ₂π)(T) · Gab(χ₁π̄, χ₂π̄)(T)`, and each `Gab` has non-negative real coefficients
  (`Gab_nonneg`) for real parameters in `[-1,1]`, so the `e`-th coefficient is a sum of products
  of non-negative reals;
* `p = 3 mod 4` (inert, `p` primary generator `-p`): `λ_χ(p^ν) = geoInert (χ(-p)) ν`, i.e. the
  local factor is `1/(1 - χ(-p)T²)`, so the four-fold product is `Gab(χ₁(-p), χ₂(-p))` evaluated
  at `e/2` (and `0` for odd `e`).

The sequence calculus is packaged in `conv_defs` (`gc`, `GabC`, `db`); the bridge
`gabC_ofReal_alt` identifies `GabC` with the real `Gab` of `hecke_prod_local` for real
parameters (whence `Gab_nonneg`), and the three structural lemmas `cvs_regroup8`,
`cvs_regroup_inert` (reassociation of `cvs`-products) and `conv_pow_four` (the Dirichlet
convolution at a prime power is the nested Cauchy product of the local sequences) are proved in
the sibling modules, following `LSeries.convolution_def` and the classification of primary
elements of `ℤ[i]` (`splitPrimaryClass`, `inertPrimaryClass`).
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.hecke_prod_local
import Submission.Work.FIArea5.S16Hecke.heckeLam_localRec
import Submission.Work.FIArea5.S16Hecke.conv_defs
import Submission.Work.FIArea5.S16Hecke.gabC_ofReal_alt
import Submission.Work.FIArea5.S16Hecke.cvs_regroup8
import Submission.Work.FIArea5.S16Hecke.cvs_regroup_inert
import Submission.Work.FIArea5.S16Hecke.conv_pow_four

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke
open Finset
open scoped BigOperators
noncomputable section

private lemma ofReal_re_of_star_eq_self (z : ℂ) (hz : star z = z) : ((z.re : ℝ) : ℂ) = z := by
  rw [Complex.star_def] at hz
  have him : z.im = 0 := by
    have h := congrArg Complex.im hz
    rw [Complex.conj_im] at h
    linarith
  exact Complex.ext (Complex.ofReal_re z.re) (by rw [Complex.ofReal_im, him])

/-- Four-fold convolution of Hecke eigenvalue sequences at a prime power is a non-negative
real number. -/
theorem conv_prime_pow (chi₁ chi₂ : GaussianInt → ℂ)
    (h1₁ : chi₁ 1 = 1) (h1₂ : chi₂ 1 = 1)
    (hre₁ : ∀ z : GaussianInt, chi₁ z = star (chi₁ z))
    (hre₂ : ∀ z : GaussianInt, chi₂ z = star (chi₂ z))
    (hmul₁ : ∀ z w : GaussianInt, chi₁ (z * w) = chi₁ z * chi₁ w)
    (hmul₂ : ∀ z w : GaussianInt, chi₂ (z * w) = chi₂ z * chi₂ w)
    (hb₁ : ∀ z : GaussianInt, ‖chi₁ z‖ ≤ 1) (hb₂ : ∀ z : GaussianInt, ‖chi₂ z‖ ≤ 1)
    (p : ℕ) (hp : p.Prime) (e : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ LSeries.convolution (LSeries.convolution (LSeries.convolution
      (heckeLam (fun _ => (1:ℂ)) 0) (heckeLam chi₁ 0)) (heckeLam chi₂ 0))
      (heckeLam (fun z => chi₁ z * chi₂ z) 0) (p^e) = (c : ℂ) := by
  classical
  have hreal₁ : ∀ z : GaussianInt, ((chi₁ z).re : ℂ) = chi₁ z :=
    fun z => ofReal_re_of_star_eq_self (chi₁ z) (hre₁ z).symm
  have hreal₂ : ∀ z : GaussianInt, ((chi₂ z).re : ℂ) = chi₂ z :=
    fun z => ofReal_re_of_star_eq_self (chi₂ z) (hre₂ z).symm
  have hmul₃ : ∀ z w : GaussianInt,
      (fun z => chi₁ z * chi₂ z) (z * w)
        = (fun z => chi₁ z * chi₂ z) z * (fun z => chi₁ z * chi₂ z) w := by
    intro z w
    simp only [hmul₁ z w, hmul₂ z w]
    ring
  have h1₃ : (fun z => chi₁ z * chi₂ z) 1 = 1 := by simp [h1₁, h1₂]
  rcases hp.eq_two_or_odd' with hp2 | hpodd
  · -- p = 2 : every local factor is the Kronecker delta
    subst hp2
    have hd0 : (fun k : ℕ => heckeLam (fun _ => (1:ℂ)) 0 ((2:ℕ)^k)) = deltaC := by
      funext k
      rcases k with _ | m
      · simp [deltaC, heckeLam_one]
      · rw [heckeLam_even (fun _ => (1:ℂ)) 0
            (show Even ((2:ℕ)^(m+1)) from ⟨2^m, by rw [pow_succ]; ring⟩)]
        simp [deltaC]
    have hd1 : (fun k : ℕ => heckeLam chi₁ 0 ((2:ℕ)^k)) = deltaC := by
      funext k
      rcases k with _ | m
      · simp [deltaC, heckeLam_one, h1₁]
      · rw [heckeLam_even chi₁ 0
            (show Even ((2:ℕ)^(m+1)) from ⟨2^m, by rw [pow_succ]; ring⟩)]
        simp [deltaC]
    have hd2 : (fun k : ℕ => heckeLam chi₂ 0 ((2:ℕ)^k)) = deltaC := by
      funext k
      rcases k with _ | m
      · simp [deltaC, heckeLam_one, h1₂]
      · rw [heckeLam_even chi₂ 0
            (show Even ((2:ℕ)^(m+1)) from ⟨2^m, by rw [pow_succ]; ring⟩)]
        simp [deltaC]
    have hd3 : (fun k : ℕ => heckeLam (fun z => chi₁ z * chi₂ z) 0 ((2:ℕ)^k)) = deltaC := by
      funext k
      rcases k with _ | m
      · simp [deltaC, heckeLam_one, h1₃]
      · rw [heckeLam_even (fun z => chi₁ z * chi₂ z) 0
            (show Even ((2:ℕ)^(m+1)) from ⟨2^m, by rw [pow_succ]; ring⟩)]
        simp [deltaC]
    have hdδ : cvs (cvs (cvs deltaC deltaC) deltaC) deltaC = deltaC := by
      simp only [cvs_delta]
    refine ⟨(if e = 0 then (1:ℝ) else 0), ?_, ?_⟩
    · by_cases he : e = 0 <;> simp [he]
    · rw [conv_pow_four (heckeLam (fun _ => (1:ℂ)) 0) (heckeLam chi₁ 0) (heckeLam chi₂ 0)
          (heckeLam (fun z => chi₁ z * chi₂ z) 0) 2 hp e,
        hd0, hd1, hd2, hd3, hdδ]
      by_cases he : e = 0 <;> simp [he, deltaC]
  · -- p odd
    obtain ⟨k, hk⟩ := hpodd
    have hp41 : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases hp41 with h1mod | h3mod
    · -- split prime p = 1 mod 4
      obtain ⟨π, π', hπ, hπ', hgπ, hgπ', -, -, -, hclass⟩ := splitPrimaryClass p hp h1mod
      have hL0 : (fun ν : ℕ => heckeLam (fun _ => (1:ℂ)) 0 (p^ν)) = cvs (gc 1) (gc 1) := by
        funext ν
        rw [cvs_gc_geo 1 1,
          heckeLam_splitSum (fun _ => (1:ℂ)) 0 p hp.pos (by intro z w; simp) (by simp)
            π π' hπ hπ' hgπ hgπ' hclass ν]
        simp [psi_zero]
      have hL1 : (fun ν : ℕ => heckeLam chi₁ 0 (p^ν)) = cvs (gc (chi₁ π)) (gc (chi₁ π')) := by
        funext ν
        rw [cvs_gc_geo (chi₁ π) (chi₁ π'),
          heckeLam_splitSum chi₁ 0 p hp.pos hmul₁ h1₁ π π' hπ hπ' hgπ hgπ' hclass ν]
        simp [psi_zero]
      have hL2 : (fun ν : ℕ => heckeLam chi₂ 0 (p^ν)) = cvs (gc (chi₂ π)) (gc (chi₂ π')) := by
        funext ν
        rw [cvs_gc_geo (chi₂ π) (chi₂ π'),
          heckeLam_splitSum chi₂ 0 p hp.pos hmul₂ h1₂ π π' hπ hπ' hgπ hgπ' hclass ν]
        simp [psi_zero]
      have hL3 : (fun ν : ℕ => heckeLam (fun z => chi₁ z * chi₂ z) 0 (p^ν))
          = cvs (gc (chi₁ π * chi₂ π)) (gc (chi₁ π' * chi₂ π')) := by
        funext ν
        rw [cvs_gc_geo (chi₁ π * chi₂ π) (chi₁ π' * chi₂ π'),
          heckeLam_splitSum (fun z => chi₁ z * chi₂ z) 0 p hp.pos hmul₃ h1₃
            π π' hπ hπ' hgπ hgπ' hclass ν]
        simp [psi_zero]
      obtain ⟨a₁, ha₁⟩ : ∃ a : ℝ, ((a : ℂ)) = chi₁ π := ⟨(chi₁ π).re, hreal₁ π⟩
      obtain ⟨a₂, ha₂⟩ : ∃ a : ℝ, ((a : ℂ)) = chi₂ π := ⟨(chi₂ π).re, hreal₂ π⟩
      obtain ⟨b₁, hb₁'⟩ : ∃ b : ℝ, ((b : ℂ)) = chi₁ π' := ⟨(chi₁ π').re, hreal₁ π'⟩
      obtain ⟨b₂, hb₂'⟩ : ∃ b : ℝ, ((b : ℂ)) = chi₂ π' := ⟨(chi₂ π').re, hreal₂ π'⟩
      have hba₁ : |a₁| ≤ 1 := by
        have h := hb₁ π
        rw [← ha₁, Complex.norm_real, Real.norm_eq_abs] at h; exact h
      have hba₂ : |a₂| ≤ 1 := by
        have h := hb₂ π
        rw [← ha₂, Complex.norm_real, Real.norm_eq_abs] at h; exact h
      have hbb₁ : |b₁| ≤ 1 := by
        have h := hb₁ π'
        rw [← hb₁', Complex.norm_real, Real.norm_eq_abs] at h; exact h
      have hbb₂ : |b₂| ≤ 1 := by
        have h := hb₂ π'
        rw [← hb₂', Complex.norm_real, Real.norm_eq_abs] at h; exact h
      refine ⟨cvs (Gab a₁ a₂) (Gab b₁ b₂) e, ?_, ?_⟩
      · show 0 ≤ ∑ k ∈ Finset.range (e + 1), Gab a₁ a₂ k * Gab b₁ b₂ (e - k)
        exact Finset.sum_nonneg fun k _ =>
          mul_nonneg (Gab_nonneg a₁ a₂ hba₁ hba₂ k) (Gab_nonneg b₁ b₂ hbb₁ hbb₂ (e - k))
      · rw [conv_pow_four (heckeLam (fun _ => (1:ℂ)) 0) (heckeLam chi₁ 0) (heckeLam chi₂ 0)
            (heckeLam (fun z => chi₁ z * chi₂ z) 0) p hp e]
        rw [hL0, hL1, hL2, hL3]
        rw [← ha₁, ← ha₂, ← hb₁', ← hb₂']
        rw [cvs_regroup8 ((a₁ : ℝ) : ℂ) ((a₂ : ℝ) : ℂ) ((b₁ : ℝ) : ℂ) ((b₂ : ℝ) : ℂ)]
        rw [funext (gabC_ofReal_alt a₁ a₂), funext (gabC_ofReal_alt b₁ b₂), cvs_ofReal]
    · -- inert prime p = 3 mod 4
      obtain ⟨hq, -, hgq, hclass⟩ := inertPrimaryClass p hp h3mod
      have hL0 : (fun ν : ℕ => heckeLam (fun _ => (1:ℂ)) 0 (p^ν)) = db (gc 1) := by
        funext ν
        rw [← geoInert_eq_db 1,
          heckeLam_inertSum (fun _ => (1:ℂ)) 0 p hp.pos (by intro z w; simp) (by simp)
            (-(p : GaussianInt)) hq hgq hclass ν]
        simp [psi_zero]
      have hL1 : (fun ν : ℕ => heckeLam chi₁ 0 (p^ν))
          = db (gc (chi₁ (-(p : GaussianInt)))) := by
        funext ν
        rw [← geoInert_eq_db (chi₁ (-(p : GaussianInt))),
          heckeLam_inertSum chi₁ 0 p hp.pos hmul₁ h1₁ (-(p : GaussianInt)) hq hgq hclass ν]
        simp [psi_zero]
      have hL2 : (fun ν : ℕ => heckeLam chi₂ 0 (p^ν))
          = db (gc (chi₂ (-(p : GaussianInt)))) := by
        funext ν
        rw [← geoInert_eq_db (chi₂ (-(p : GaussianInt))),
          heckeLam_inertSum chi₂ 0 p hp.pos hmul₂ h1₂ (-(p : GaussianInt)) hq hgq hclass ν]
        simp [psi_zero]
      have hL3 : (fun ν : ℕ => heckeLam (fun z => chi₁ z * chi₂ z) 0 (p^ν))
          = db (gc (chi₁ (-(p : GaussianInt)) * chi₂ (-(p : GaussianInt)))) := by
        funext ν
        rw [← geoInert_eq_db (chi₁ (-(p : GaussianInt)) * chi₂ (-(p : GaussianInt))),
          heckeLam_inertSum (fun z => chi₁ z * chi₂ z) 0 p hp.pos hmul₃ h1₃
            (-(p : GaussianInt)) hq hgq hclass ν]
        simp [psi_zero]
      obtain ⟨r₁, hr₁⟩ : ∃ r : ℝ, ((r : ℂ)) = chi₁ (-(p : GaussianInt)) :=
        ⟨(chi₁ (-(p : GaussianInt))).re, hreal₁ _⟩
      obtain ⟨r₂, hr₂⟩ : ∃ r : ℝ, ((r : ℂ)) = chi₂ (-(p : GaussianInt)) :=
        ⟨(chi₂ (-(p : GaussianInt))).re, hreal₂ _⟩
      have hbr₁ : |r₁| ≤ 1 := by
        have h := hb₁ (-(p : GaussianInt))
        rw [← hr₁, Complex.norm_real, Real.norm_eq_abs] at h; exact h
      have hbr₂ : |r₂| ≤ 1 := by
        have h := hb₂ (-(p : GaussianInt))
        rw [← hr₂, Complex.norm_real, Real.norm_eq_abs] at h; exact h
      refine ⟨(if Even e then Gab r₁ r₂ (e / 2) else 0), ?_, ?_⟩
      · split
        · exact Gab_nonneg r₁ r₂ hbr₁ hbr₂ (e / 2)
        · exact le_refl 0
      · rw [conv_pow_four (heckeLam (fun _ => (1:ℂ)) 0) (heckeLam chi₁ 0) (heckeLam chi₂ 0)
            (heckeLam (fun z => chi₁ z * chi₂ z) 0) p hp e]
        rw [hL0, hL1, hL2, hL3]
        rw [← hr₁, ← hr₂]
        rw [cvs_regroup_inert ((r₁ : ℝ) : ℂ) ((r₂ : ℝ) : ℂ)]
        simp only [db, gabC_ofReal_alt]
        by_cases hev : Even e <;> simp [hev]

end
end Work.FIArea5.S16Hecke
