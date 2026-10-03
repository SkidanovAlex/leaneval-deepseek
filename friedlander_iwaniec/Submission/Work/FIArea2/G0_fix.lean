import Mathlib
import Submission.Work.FIArea2.G0_defect
import Submission.Work.FIArea2.Cnt_eq_Nsol
import Submission.Work.FIArea2.Nsol_eq_two_sum_jacobi
import Submission.Work.FIArea2.coprime_re_absDelta
import Submission.Work.FIArea2.coprime_residue_absDelta
import Submission.Work.FIArea2.a_mod_eight
import Submission.Work.FIArea2.eight_dvd_absDelta_of_congr
import Submission.Work.FIArea2.coprime_gnorm_absDelta

/-!
# The corrected kernel `G₀`, and the main term `D₀` it defines

**Import note (FITop6, 2026-09-26).**  The import of
`Submission.Work.FIArea2.area2_r3` has been dropped: every helper this file uses is provided by
its remaining imports (the file builds with the import removed), and `area2_r3` carries the
*superseded* round-3 area-2 theorem together with a `sorry`, which would put `sorryAx` into the
closure of every consumer of `G₀` (in particular `Work.FITop4.Red6.G0_eq_ratioSym_sum` and
`Red6.Tbeta_partition`, hence `prop41_of_areas6`).

`G0_defect.lean` shows that the frozen `Work.FIPlan.G0` is *not* *FI*'s `G₀` of (8.16): it uses
the Jacobi symbol of `Re(z̄₁z₂)` instead of that of the residue (6.6) `z₂/z₁`, and at the explicit
witness of that file the two differ by a factor `5`.

This file collects the **repair** as a self-contained package, so that a round-5 contract can be
re-pointed at the correct kernel with a single change: the kernel is defined as the *count* (6.12)
itself, `G0fix z₁ z₂ = Cnt z₁ z₂ / |Δ|`, and `C0fix`/`D0fix` transport it through (6.13), (7.10)
and (9.11) exactly as `C0mod`/`D0formMod` transport `Work.FIPlan.G0`:

* `G0fix_eq_two_sum` (once `Nsol_eq_two_sum_jacobi` and `Cnt_eq_Nsol` are available) — the count
  equals the (8.16) sum `2 ∑_{4d|Δ}(φ(d)/d)(a/d)` with the residue `a` of (6.6);
* `G0fix_ne_G0` — the two kernels are *not* the same function (the witness of `G0_defect`);
* `Dstar_sub_D0fix_eq_pairSum` — the analogue of `Dstar_sub_D0_eq_pairSum` for `D0fix`: `Area2`
  with the corrected main term is exactly the `β_{z₁}β̄_{z₂}`-weighted per-pair error of (9.1).
-/

namespace Work.FIArea2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The corrected (8.16) kernel**: the count (6.12), divided by `|Δ|`. -/
def G0fix (z1 z2 : GaussianInt) : ℝ :=
  (Cnt z1 z2 : ℝ) / (Work.FIPlan.absDelta z1 z2 : ℝ)

/-- **The corrected (6.13)+(7.10)**: `C₀ = |z₁z₂|^{-1/2}·2f̂(0)·log(2|z₁z₂/Δ|)·G₀`, with the
count-based kernel `G0fix`. -/
def C0fix (fhat : ℝ) (z1 z2 : GaussianInt) : ℝ :=
  (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4)) * (2 * fhat)
    * Work.FITop3.logFac z1 z2 * G0fix z1 z2

/-- **The corrected (9.11)**: `D₀ = ∑_{(z₁,z₂)=1} β_{z₁}β̄_{z₂}C₀(z₁,z₂)` with the corrected
kernel.  (`Work.FITop3.D0formMod` is the same with `Work.FIPlan.G0` in place of `G0fix`.) -/
def D0fix (Rz : ℤ) (fhat : ℝ) (β : GaussianInt → ℂ) : ℂ :=
  ∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
    (if Work.FIPlan.GaussCoprime z1 z2 then
      β z1 * star (β z2) * (C0fix fhat z1 z2 : ℂ) else 0)

/-- `D0fix` is real; pushing `re` inside the pair sum. -/
theorem D0fix_re_eq (Pa : Work.FITop.Params) (f : ℤ → ℝ) (β : GaussianInt → ℂ) :
    (D0fix (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β).re
      = ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          if Work.FIPlan.GaussCoprime z1 z2 then
            (β z1 * star (β z2)).re * C0fix (Work.FITop3.Fhat Pa f) z1 z2
          else 0 := by
  unfold D0fix Work.FITop.boxN
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun z1 _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun z2 _ => ?_
  by_cases hc : Work.FIPlan.GaussCoprime z1 z2
  · simp only [hc, if_true]
    rw [Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re]
    ring
  · simp [hc, Complex.zero_re]

/-- **`Area2` with the corrected main term**: the frozen left-hand side is the
`β_{z₁}β̄_{z₂}`-weighted sum of the per-pair errors `C(z₁,z₂) − C₀(z₁,z₂)` of (9.1), now with the
*correct* `C₀` (compare `Dstar_sub_D0_eq_pairSum` for the frozen one). -/
theorem Dstar_sub_D0fix_eq_pairSum (Pa : Work.FITop.Params) (f : ℤ → ℝ) (β : GaussianInt → ℂ) :
    Work.FITop3.Dstar Pa f β - (D0fix (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β).re
      = ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          if Work.FIPlan.GaussCoprime z1 z2 then
            (β z1 * star (β z2)).re
              * (Ccount Pa f z1 z2 - C0fix (Work.FITop3.Fhat Pa f) z1 z2)
          else 0 := by
  rw [Dstar_eq_pairSum, D0fix_re_eq, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun z1 _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun z2 _ => ?_
  by_cases hc : Work.FIPlan.GaussCoprime z1 z2 <;> simp [hc, mul_sub]

/-- The corrected kernel at the witness of `G0_defect`: the count is `120`, so `G0fix = 5`. -/
theorem G0fix_witness : G0fix (⟨1, 4⟩ : GaussianInt) ⟨1, 28⟩ = 5 := by
  unfold G0fix
  rw [witness1_Cnt]
  norm_num [Work.FIPlan.absDelta, Work.FIPlan.Delta]

/-- **The corrected kernel is not the frozen one**: at the witness, `G0fix = 5` while the frozen
`Work.FIPlan.G0 = 1`. -/
theorem G0fix_ne_G0 : G0fix (⟨1, 4⟩ : GaussianInt) ⟨1, 28⟩
    ≠ Work.FIPlan.G0 (⟨1, 4⟩ : GaussianInt) ⟨1, 28⟩ := by
  rw [G0fix_witness, witness1_G0]
  norm_num

/-! ## The corrected (8.16) -/

/-- **The corrected (8.16)**: under the hypotheses that make the count (6.12) equal the single
congruence (8.8) with the residue `a` of `z₂/z₁` (`Cnt_eq_Nsol`), with `4 ∣ |Δ|`, `a ≡ 1 (mod 8)`
and `(a,|Δ|) = 1` (the hypotheses of Corollary 8.3 and (8.11)),

  `Cnt z₁ z₂ = |Δ| · 2 ∑_{4d | Δ} (φ(d)/d)(a/d)`,

which is Lemma 8.4 / (8.16) — with the residue of (6.6), not with the symbol of `Re(z̄₁z₂)`. -/
theorem Cnt_eq_two_sum {z1 z2 : GaussianInt} {a : ℕ}
    (hD : Work.FIPlan.absDelta z1 z2 ≠ 0)
    (h4 : 4 ∣ Work.FIPlan.absDelta z1 z2)
    (hni : Nat.Coprime (Work.FIPlan.gnorm z1) (Work.FIPlan.absDelta z1 z2))
    (ha : (a : ℤ) * (Work.FIPlan.gnorm z1 : ℤ)
        ≡ (star z1 * z2).re [ZMOD (Work.FIPlan.absDelta z1 z2 : ℤ)])
    (ha8 : a % 8 = 1) (hcop : Nat.Coprime a (Work.FIPlan.absDelta z1 z2)) :
    (Cnt z1 z2 : ℝ) = (Work.FIPlan.absDelta z1 z2 : ℝ) * (2 *
      ∑ d ∈ (Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1)).filter
          (fun d => 4 * d ∣ Work.FIPlan.absDelta z1 z2),
        ((Nat.totient d : ℝ) / (d : ℝ)) * (jacobiSym (a : ℤ) d : ℝ)) := by
  rw [Cnt_eq_Nsol hD hni ha]
  exact Nsol_eq_two_sum_jacobi hD h4 ha8 hcop

/-- **The kernel form of the corrected (8.16)**: `G0fix z₁ z₂ = 2 ∑_{4d|Δ}(φ(d)/d)(a/d)`. -/
theorem G0fix_eq_two_sum {z1 z2 : GaussianInt} {a : ℕ}
    (hD : Work.FIPlan.absDelta z1 z2 ≠ 0)
    (h4 : 4 ∣ Work.FIPlan.absDelta z1 z2)
    (hni : Nat.Coprime (Work.FIPlan.gnorm z1) (Work.FIPlan.absDelta z1 z2))
    (ha : (a : ℤ) * (Work.FIPlan.gnorm z1 : ℤ)
        ≡ (star z1 * z2).re [ZMOD (Work.FIPlan.absDelta z1 z2 : ℤ)])
    (ha8 : a % 8 = 1) (hcop : Nat.Coprime a (Work.FIPlan.absDelta z1 z2)) :
    G0fix z1 z2 = 2 *
      ∑ d ∈ (Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1)).filter
          (fun d => 4 * d ∣ Work.FIPlan.absDelta z1 z2),
        ((Nat.totient d : ℝ) / (d : ℝ)) * (jacobiSym (a : ℤ) d : ℝ) := by
  have hpos : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hD
  unfold G0fix
  rw [Cnt_eq_two_sum hD h4 hni ha ha8 hcop]
  field_simp

/-! ## The corrected (8.16) in the paper's setting

The hypotheses of `Cnt_eq_two_sum` are exactly the side conditions that the paper's setting
supplies: `z₁ ≡ z₂ (mod 8)` gives `8 ∣ |Δ|` (`eight_dvd_absDelta_of_congr`), hence `4 ∣ |Δ|` and
`a ≡ 1 (mod 8)` (`a_mod_eight`); primitivity and coprimality give `(|z₁|²,|Δ|) = 1`
(`coprime_gnorm_absDelta`), `(Re(z̄₁z₂),|Δ|) = 1` (`coprime_re_absDelta`) and hence `(a,|Δ|) = 1`
(`coprime_residue_absDelta`).  The lemma below collects the consequences that do not need the
first one. -/

/-- **The corrected (8.16) for `z₁ ≡ z₂ (mod 8)`**: for an odd-norm `z₁`, `z₂ − z₁ = 8m`,
`|Δ| ≠ 0`, `(|z₁|²,|Δ|) = 1`, `(z₁,z₂) = (z₁,z̄₁) = (z₂,z̄₂) = 1` and `a·|z₁|² ≡ Re(z̄₁z₂) (mod |Δ|)`,
the count (6.12) equals `|Δ| · 2 ∑_{4d|Δ}(φ(d)/d)(a/d)`.  (The hypothesis `(|z₁|²,|Δ|) = 1` is
itself automatic; see `coprime_gnorm_absDelta`.) -/
theorem Cnt_eq_two_sum_of_congr {z1 z2 m : GaussianInt} {a : ℕ}
    (hodd : Odd (Work.FIPlan.gnorm z1))
    (hcongr : z2 - z1 = 8 * m)
    (hD : Work.FIPlan.absDelta z1 z2 ≠ 0)
    (hni : Nat.Coprime (Work.FIPlan.gnorm z1) (Work.FIPlan.absDelta z1 z2))
    (h12 : Work.FIPlan.GaussCoprime z1 z2)
    (h1 : IsCoprime z1 (star z1)) (h2 : IsCoprime z2 (star z2))
    (ha : (a : ℤ) * (Work.FIPlan.gnorm z1 : ℤ)
        ≡ (star z1 * z2).re [ZMOD (Work.FIPlan.absDelta z1 z2 : ℤ)]) :
    (Cnt z1 z2 : ℝ) = (Work.FIPlan.absDelta z1 z2 : ℝ) * (2 *
      ∑ d ∈ (Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1)).filter
          (fun d => 4 * d ∣ Work.FIPlan.absDelta z1 z2),
        ((Nat.totient d : ℝ) / (d : ℝ)) * (jacobiSym (a : ℤ) d : ℝ)) := by
  have h8 : 8 ∣ Work.FIPlan.absDelta z1 z2 := eight_dvd_absDelta_of_congr hcongr
  have h4 : 4 ∣ Work.FIPlan.absDelta z1 z2 := dvd_trans (by norm_num : (4 : ℕ) ∣ 8) h8
  have h0 : Nat.Coprime ((star z1 * z2).re).natAbs (Work.FIPlan.absDelta z1 z2) :=
    coprime_re_absDelta h12 h1 h2
  have hcop : Nat.Coprime a (Work.FIPlan.absDelta z1 z2) := coprime_residue_absDelta ha h0
  have ha8z : (a : ℤ) ≡ 1 [ZMOD 8] := a_mod_eight hodd hcongr h8 ha
  have ha8 : a % 8 = 1 := by
    have h2 : a ≡ 1 [MOD 8] := Int.natCast_modEq_iff.mp ha8z
    simpa [Nat.ModEq] using h2
  exact Cnt_eq_two_sum hD h4 hni ha ha8 hcop

/-- **The corrected (8.16) with every side condition derived**: for `z₁` of odd norm, `z₂ ≡ z₁
(mod 8)`, `Δ ≠ 0`, `(z₁,z₂) = (z₁,z̄₁) = (z₂,z̄₂) = 1`, and `a` a residue of `z₂/z₁` modulo `|Δ|`,
the count (6.12) is `|Δ| · 2 ∑_{4d|Δ}(φ(d)/d)(a/d)`.  All the side conditions of the paper's
Lemma 8.4 — `4 ∣ |Δ|`, `a ≡ 1 (mod 8)`, `(|z₁|²,|Δ|) = 1`, `(Re(z̄₁z₂),|Δ|) = 1`, `(a,|Δ|) = 1` —
are supplied by `eight_dvd_absDelta_of_congr`, `a_mod_eight`, `coprime_gnorm_absDelta`,
`coprime_re_absDelta` and `coprime_residue_absDelta`. -/
theorem Cnt_eq_two_sum_of_primitive {z1 z2 m : GaussianInt} {a : ℕ}
    (hodd : Odd (Work.FIPlan.gnorm z1))
    (hcongr : z2 - z1 = 8 * m)
    (hD : Work.FIPlan.absDelta z1 z2 ≠ 0)
    (h12 : Work.FIPlan.GaussCoprime z1 z2)
    (h1 : IsCoprime z1 (star z1)) (h2 : IsCoprime z2 (star z2))
    (ha : (a : ℤ) * (Work.FIPlan.gnorm z1 : ℤ)
        ≡ (star z1 * z2).re [ZMOD (Work.FIPlan.absDelta z1 z2 : ℤ)]) :
    (Cnt z1 z2 : ℝ) = (Work.FIPlan.absDelta z1 z2 : ℝ) * (2 *
      ∑ d ∈ (Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1)).filter
          (fun d => 4 * d ∣ Work.FIPlan.absDelta z1 z2),
        ((Nat.totient d : ℝ) / (d : ℝ)) * (jacobiSym (a : ℤ) d : ℝ)) :=
  Cnt_eq_two_sum_of_congr hodd hcongr hD (coprime_gnorm_absDelta h12 h1) h12 h1 h2 ha

end

end Work.FIArea2
