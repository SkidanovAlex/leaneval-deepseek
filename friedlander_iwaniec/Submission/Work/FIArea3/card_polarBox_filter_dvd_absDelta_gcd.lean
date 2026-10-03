/-
# `Submission.Work.FIArea3.card_polarBox_filter_dvd_absDelta_gcd` — the `Δ`-fibre count with the
coprimality hypothesis replaced by the `gcd` factor.

`polbox_delta_count.card_polarBox_filter_dvd_absDelta` counts, for `z₁` in the polar box and
`c` coprime to `z₁.re`,

  `#{z₂ ∈ polar box : c ∣ |Δ(z₁,z₂)|} ≤ (20u+3)(20u/c + 4)`,  `u = θ√N`,

by fibring the polar box over `z₂.re`: there are at most `20u+1` rows, and within a row `c ∣ Δ`
forces all the `im`-values to be congruent modulo `c`, so a row contributes at most `20u/c+1`.

Here the coprimality of `z₁.re` and `c` is dropped.  Writing `g = gcd(z₁.re, c)` and `c' = c/g`,
the congruence in a row is only modulo `c'` (from `c ∣ z₁.re·m ⟹ c' ∣ m`), so a row contributes at
most `20u/c' + 1 = 20u·g/c + 1 ≤ g·(20u/c + 4)`; the extra factor `g` in the bound is exactly what
the same row argument gives when `(z₁.re, c) ≠ 1`.

The file contains two statements: the geometric count `card_polarBox_filter_dvd_absDelta_of_dvd`
with an abstract modulus `d` (the only property used being `c ∣ z₁.re·m ⟹ d ∣ m`), and the
requested `card_polarBox_filter_dvd_absDelta_gcd`, which specialises `d` to `c/gcd(z₁.re, c)`.
-/
import Mathlib
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea4.polarBox_card_le
import Submission.Work.FIArea7.card_gBox_filter_dvd_absDelta
import Submission.Commons.NumberTheory.Int.ncard_int_residue_class_sq_le

namespace Work.FIArea3

open Finset Work.FIPlan
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- **Euclid's lemma with the gcd kept explicit.**  If `c ∣ a·m` in `ℤ` then already
`c / gcd(|a|, c) ∣ m`: writing `g = gcd(|a|, c)`, `c' = c/g` one has `a = g·a₁`, `c = g·c'`,
`c ∣ a·m` gives `c' ∣ a₁·m`, and `gcd(a₁, c') = 1`. -/
lemma dvd_div_gcd_of_dvd_mul {c : ℕ} (hc : 0 < c) {a m : ℤ} (h : (c : ℤ) ∣ a * m) :
    (((c / Nat.gcd a.natAbs c : ℕ)) : ℤ) ∣ m := by
  set g : ℕ := Nat.gcd a.natAbs c with hg
  have hgpos : 0 < g := by rw [hg]; exact Nat.gcd_pos_of_pos_right _ hc
  set c' : ℕ := c / g with hc'
  have hgZne : ((g : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hgpos.ne'
  have hga : ((g : ℕ) : ℤ) ∣ a := by
    have h1 := Int.gcd_dvd_left a (c : ℤ)
    have h2 : Int.gcd a (c : ℤ) = g := by rw [Int.gcd_eq_natAbs, hg, Int.natAbs_natCast]
    rwa [h2] at h1
  obtain ⟨a₁, ha₁⟩ := hga
  have hc_eq : (c : ℤ) = (g : ℤ) * (c' : ℤ) := by
    have h2 : c' * g = c := by
      rw [hc']; exact Nat.div_mul_cancel (by rw [hg]; exact Nat.gcd_dvd_right _ _)
    have h3 : (c : ℤ) = (c' : ℤ) * (g : ℤ) := by rw [← h2]; push_cast; ring
    rw [h3]; ring
  have hna₁ : a₁.natAbs = a.natAbs / g :=
    Nat.eq_div_of_mul_eq_right hgpos.ne' (by rw [ha₁, Int.natAbs_mul, Int.natAbs_natCast])
  have hcop_nat : (a₁.natAbs).Coprime c' := by
    have h1 := Nat.coprime_div_gcd_div_gcd (m := a.natAbs) (n := c) hgpos
    rw [← hg, ← hc', ← hna₁] at h1
    exact h1
  have hcop : IsCoprime ((c' : ℕ) : ℤ) a₁ := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using hcop_nat.symm
  have h3' : ((g : ℤ) * (c' : ℤ)) ∣ ((g : ℤ) * a₁) * m := by
    rw [hc_eq, ha₁] at h; exact h
  have h3 : ((g : ℤ) * (c' : ℤ)) ∣ (g : ℤ) * (a₁ * m) := by
    simpa only [mul_assoc] using h3'
  have h2 : ((c' : ℕ) : ℤ) ∣ a₁ * m := (mul_dvd_mul_iff_left hgZne).mp h3
  exact hcop.dvd_of_dvd_mul_left h2

/-- **The `Δ`-fibre count of the polar box with an abstract modulus.**  Let `d ≥ 1` be such that
`c ∣ z₁.re·m ⟹ d ∣ m` for all `m` (the case of interest is `d = c/gcd(z₁.re, c)`, for which
`d = c` when `(z₁.re, c) = 1`).  Then

  `#{z₂ ∈ polar box : c ∣ |Δ(z₁,z₂)|} ≤ (20u+3)(20u/d + 4)`,  `u = θ√N`.

The proof is the "one residue class per row" count: the polar box lies in the disc of radius `5u`
around the point of modulus `√N` at the mid-angle of the sector, so its points are pairwise within
`10u`; fibring over `z₂.re` gives at most `20u+1` rows, each of length `≤ 20u`, and inside a row the
divisibility `c ∣ Δ` forces all `im`-values into one class modulo `d`. -/
theorem card_polarBox_filter_dvd_absDelta_of_dvd (Pa : Work.FITop.Params) (φ : ℝ)
    (z₁ : GaussianInt) (hz₁ : z₁ ∈ polarBoxFinset Pa φ) (c : ℕ) (hc : 1 ≤ c)
    (d : ℕ) (hd : 1 ≤ d)
    (hdiv : ∀ m : ℤ, (c : ℤ) ∣ z₁.re * m → (d : ℤ) ∣ m) :
    (((polarBoxFinset Pa φ).filter (fun z₂ => c ∣ Work.FIPlan.absDelta z₁ z₂)).card : ℝ)
      ≤ (20 * (Pa.θ * Real.sqrt Pa.N) + 3)
          * (20 * (Pa.θ * Real.sqrt Pa.N) / (d : ℝ) + 4) := by
  classical
  set u : ℝ := Pa.θ * Real.sqrt Pa.N with hu
  have hu0 : 0 ≤ u := by
    rw [hu]; exact mul_nonneg Pa.hθ0.le (Real.sqrt_nonneg _)
  set c₀ : ℂ := (Real.sqrt Pa.N : ℂ)
    * Complex.exp (((φ + Real.pi * Pa.θ : ℝ) : ℂ) * Complex.I) with hc₀
  have h₀ : ‖z₁.toComplex - c₀‖ ≤ 5 * u := by
    have h := Work.FIArea4.dist_polarBox_le Pa φ z₁ (mem_polarBoxFinset.mp hz₁).2
    have hru : 5 * u = 5 * Pa.θ * Real.sqrt Pa.N := by rw [hu]; ring
    rw [hru]; exact h
  set S : Finset GaussianInt :=
    (polarBoxFinset Pa φ).filter (fun z₂ => c ∣ Work.FIPlan.absDelta z₁ z₂) with hS
  -- every element of `S` is within `10u` of `z₁`
  have hdist : ∀ z ∈ S, ‖z.toComplex - z₁.toComplex‖ ≤ 10 * u := by
    intro z hz
    rw [hS, Finset.mem_filter] at hz
    have hzbox : Work.FITop3.InPolarBox Pa φ z := (mem_polarBoxFinset.mp hz.1).2
    have hz5 : ‖z.toComplex - c₀‖ ≤ 5 * u := by
      have h := Work.FIArea4.dist_polarBox_le Pa φ z hzbox
      have hru : 5 * u = 5 * Pa.θ * Real.sqrt Pa.N := by rw [hu]; ring
      rw [hru]; exact h
    have hsplit : z.toComplex - z₁.toComplex = (z.toComplex - c₀) + (c₀ - z₁.toComplex) := by ring
    rw [hsplit]
    calc ‖(z.toComplex - c₀) + (c₀ - z₁.toComplex)‖
        ≤ ‖z.toComplex - c₀‖ + ‖c₀ - z₁.toComplex‖ := norm_add_le _ _
      _ ≤ 5 * u + 5 * u := add_le_add hz5 (by rw [norm_sub_rev]; exact h₀)
      _ = 10 * u := by ring
  -- the `re`-values of `S` lie in an interval of length `20u`
  have hre : ∀ z ∈ S, |((z.re : ℤ) : ℝ) - ((z₁.re : ℤ) : ℝ)| ≤ 10 * u := by
    intro z hz
    have h1 : |((z.re : ℤ) : ℝ) - ((z₁.re : ℤ) : ℝ)| ≤ ‖z.toComplex - z₁.toComplex‖ := by
      have hsub : ((z.re : ℤ) : ℝ) - ((z₁.re : ℤ) : ℝ) = (z.toComplex - z₁.toComplex).re := by
        simp [Complex.sub_re]
      rw [hsub]
      exact Complex.abs_re_le_norm _
    exact le_trans h1 (hdist z hz)
  -- fibres over `re`
  have hmapsto : Set.MapsTo (fun z : GaussianInt => z.re) (↑S : Set GaussianInt)
      (↑(S.image (fun z => z.re)) : Set ℤ) := by
    intro z hz
    exact Finset.mem_image_of_mem _ hz
  have hfib := Finset.card_eq_sum_card_fiberwise hmapsto
  -- the image has at most `20u+1` elements
  have himg : ((S.image (fun z => z.re)).card : ℝ) ≤ 20 * u + 1 := by
    have h := Work.FIArea4.card_int_le_of_mem_interval (S.image (fun z => z.re))
      (t := ((z₁.re : ℤ) : ℝ) - 10 * u) (ρ := 10 * u) (by linarith)
      (fun x hx => by
        rw [Finset.mem_image] at hx
        obtain ⟨z, hz, rfl⟩ := hx
        have h2 := hre z hz
        rw [abs_le] at h2
        constructor <;> linarith)
    linarith
  -- each fibre has at most `20u/d + 4` elements
  have hfib_le : ∀ b ∈ S.image (fun z => z.re),
      ((S.filter (fun z => z.re = b)).card : ℝ) ≤ 20 * u / (d : ℝ) + 4 := by
    intro b hb
    set F : Finset GaussianInt := S.filter (fun z => z.re = b) with hF
    set U : Finset ℤ := F.image (fun z => z.im - z₁.im) with hU
    have hUF : U.card = F.card := by
      rw [hU]
      refine Finset.card_image_of_injOn ?_
      intro x hx y hy hxy
      have hxF : x ∈ F := hx
      have hyF : y ∈ F := hy
      rw [hF, Finset.mem_filter] at hxF hyF
      exact Zsqrtd.ext (by rw [hxF.2, hyF.2]) (by simpa using hxy)
    -- pairwise congruence mod `d` on `U`
    have hcongU : ∀ x ∈ U, ∀ y ∈ U, (d : ℤ) ∣ x - y := by
      intro x hx y hy
      rw [hU, Finset.mem_image] at hx hy
      obtain ⟨z, hzF, rfl⟩ := hx
      obtain ⟨w, hwF, rfl⟩ := hy
      have hzS : z ∈ S := (Finset.mem_filter.mp hzF).1
      have hwS : w ∈ S := (Finset.mem_filter.mp hwF).1
      have hzP : c ∣ Work.FIPlan.absDelta z₁ z := (Finset.mem_filter.mp hzS).2
      have hwP : c ∣ Work.FIPlan.absDelta z₁ w := (Finset.mem_filter.mp hwS).2
      have hzr : z.re = b := (Finset.mem_filter.mp hzF).2
      have hwr : w.re = b := (Finset.mem_filter.mp hwF).2
      have hdz : (c : ℤ) ∣ Work.FIPlan.Delta z₁ z :=
        Work.FIArea7.dvd_Delta_of_dvd_absDelta hzP
      have hdw : (c : ℤ) ∣ Work.FIPlan.Delta z₁ w :=
        Work.FIArea7.dvd_Delta_of_dvd_absDelta hwP
      rw [Work.FIArea7.Delta_eq] at hdz hdw
      have hde : (c : ℤ) ∣ z₁.re * ((z.im - w.im : ℤ)) := by
        have : z₁.re * (z.im - w.im : ℤ)
            = (z₁.re * z.im - z₁.im * z.re) - (z₁.re * w.im - z₁.im * w.re) := by
          rw [hzr, ← hwr]; ring
        rw [this]; exact dvd_sub hdz hdw
      have h2 := hdiv (z.im - w.im) hde
      have hxy : (z.im - w.im : ℤ) = (z.im - z₁.im) - (w.im - z₁.im) := by ring
      rwa [hxy] at h2
    -- the elements of `U` are within `10u` of `0`
    have habs : ∀ a ∈ U, |(a : ℝ)| ≤ 10 * u := by
      intro a ha
      rw [hU, Finset.mem_image] at ha
      obtain ⟨z, hzF, rfl⟩ := ha
      have hzS : z ∈ S := (Finset.mem_filter.mp hzF).1
      have h1 : |((z.im : ℤ) : ℝ) - ((z₁.im : ℤ) : ℝ)| ≤ ‖z.toComplex - z₁.toComplex‖ := by
        have hsub : ((z.im : ℤ) : ℝ) - ((z₁.im : ℤ) : ℝ) = (z.toComplex - z₁.toComplex).im := by
          simp [Complex.sub_im]
        rw [hsub]
        exact Complex.abs_im_le_norm _
      have h2 : (((z.im - z₁.im : ℤ)) : ℝ) = ((z.im : ℤ) : ℝ) - ((z₁.im : ℤ) : ℝ) := by
        push_cast; ring
      rw [h2]
      linarith [h1, hdist z hzS]
    -- the fibre bound, via the residue-class count
    have hUle : (U.card : ℝ) ≤ 20 * u / (d : ℝ) + 1 := by
      rcases U.eq_empty_or_nonempty with h0 | ⟨r₀, hr₀⟩
      · rw [h0]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
      · have h := Commons.NumberTheory.Int.card_le_of_modEq_abs_le (d := d) hd (s := U) (r := r₀)
          (A := 10 * u) (by linarith) (fun a ha => by
            rw [Int.modEq_iff_dvd]
            exact hcongU r₀ hr₀ a ha) habs
        have h' : (2 * (10 * u)) / (d : ℝ) + 1 = 20 * u / (d : ℝ) + 1 := by ring
        linarith [h, h']
    have hcast : (F.card : ℝ) = (U.card : ℝ) := by rw [hUF]
    linarith [hUle, hcast]
  -- assemble
  have hsum : (S.card : ℝ) ≤ ((S.image (fun z => z.re)).card : ℝ) * (20 * u / (d : ℝ) + 4) := by
    have h1 : (∑ b ∈ S.image (fun z => z.re), ((S.filter (fun z => z.re = b)).card : ℝ))
        ≤ ∑ _b ∈ S.image (fun z => z.re), (20 * u / (d : ℝ) + 4) := Finset.sum_le_sum hfib_le
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    rw [hfib, Nat.cast_sum]
    exact h1
  have hbound : (S.card : ℝ) ≤ (20 * u + 1) * (20 * u / (d : ℝ) + 4) := by
    refine le_trans hsum (mul_le_mul_of_nonneg_right himg ?_)
    have : (0 : ℝ) ≤ 20 * u / (d : ℝ) := by positivity
    linarith
  have hfinal : (20 * u + 1) * (20 * u / (d : ℝ) + 4)
      ≤ (20 * u + 3) * (20 * u / (d : ℝ) + 4) := by
    have h4 : (0 : ℝ) ≤ 20 * u / (d : ℝ) + 4 := by positivity
    exact mul_le_mul_of_nonneg_right (by linarith) h4
  rw [hu] at hbound hfinal
  exact le_trans hbound hfinal

/-- **The `Δ`-fibre count of the polar box, with the `gcd(z₁.re, c)` factor.**  For `z₁` in the
polar box the number of `z₂` in the polar box with `c ∣ |Δ(z₁,z₂)|` is at most
`(20u+3)·g·(20u/c + 4)`, `u = θ√N`, `g = gcd(z₁.re, c)`.  This is
`card_polarBox_filter_dvd_absDelta` without the coprimality hypothesis `(z₁.re, c) = 1`, the
missing coprimality being paid for exactly by the factor `g`. -/
theorem card_polarBox_filter_dvd_absDelta_gcd (Pa : Work.FITop.Params) (φ : ℝ) (z₁ : GaussianInt)
    (hz₁ : z₁ ∈ Work.FIArea3.polarBoxFinset Pa φ) (c : ℕ) (hc : 1 ≤ c) :
    (((Work.FIArea3.polarBoxFinset Pa φ).filter
        (fun z₂ => c ∣ Work.FIPlan.absDelta z₁ z₂)).card : ℝ)
      ≤ (20 * (Pa.θ * Real.sqrt Pa.N) + 3)
          * ((Nat.gcd z₁.re.natAbs c : ℝ) * (20 * (Pa.θ * Real.sqrt Pa.N) / (c : ℝ) + 4)) := by
  classical
  have hc0 : 0 < c := hc
  have hgpos : 0 < Nat.gcd z₁.re.natAbs c := Nat.gcd_pos_of_pos_right _ hc0
  have hgle : Nat.gcd z₁.re.natAbs c ≤ c := Nat.gcd_le_right _ hc0
  have hd : 1 ≤ c / Nat.gcd z₁.re.natAbs c := by
    have h := Nat.div_pos hgle hgpos
    omega
  have hdiv : ∀ m : ℤ, (c : ℤ) ∣ z₁.re * m → ((c / Nat.gcd z₁.re.natAbs c : ℕ) : ℤ) ∣ m :=
    fun m hm => dvd_div_gcd_of_dvd_mul hc0 hm
  have hmain := card_polarBox_filter_dvd_absDelta_of_dvd Pa φ z₁ hz₁ c hc
    (c / Nat.gcd z₁.re.natAbs c) hd hdiv
  -- the arithmetic bookkeeping: `20u/(c/g) + 4 ≤ g·(20u/c + 4)`
  have hGX : ((Nat.gcd z₁.re.natAbs c : ℕ) : ℝ) * ((c / Nat.gcd z₁.re.natAbs c : ℕ) : ℝ)
      = (c : ℝ) := by
    have h : Nat.gcd z₁.re.natAbs c * (c / Nat.gcd z₁.re.natAbs c) = c := by
      rw [mul_comm]; exact Nat.div_mul_cancel (Nat.gcd_dvd_right z₁.re.natAbs c)
    exact_mod_cast h
  have hA0 : (0 : ℝ) ≤ 20 * (Pa.θ * Real.sqrt Pa.N) :=
    mul_nonneg (by norm_num) (mul_nonneg Pa.hθ0.le (Real.sqrt_nonneg _))
  have key : 20 * (Pa.θ * Real.sqrt Pa.N) / ((c / Nat.gcd z₁.re.natAbs c : ℕ) : ℝ) + 4
      ≤ ((Nat.gcd z₁.re.natAbs c : ℕ) : ℝ) * (20 * (Pa.θ * Real.sqrt Pa.N) / (c : ℝ) + 4) := by
    set A : ℝ := 20 * (Pa.θ * Real.sqrt Pa.N) with hA
    set G : ℝ := ((Nat.gcd z₁.re.natAbs c : ℕ) : ℝ) with hG
    set X : ℝ := ((c / Nat.gcd z₁.re.natAbs c : ℕ) : ℝ) with hX
    set C : ℝ := (c : ℝ) with hC
    have hGX' : G * X = C := by rw [hG, hX, hC]; exact hGX
    have hGpos : 0 < G := by rw [hG]; exact_mod_cast hgpos
    have hCpos' : 0 < C := by rw [hC]; exact_mod_cast hc0
    have hGne : G ≠ 0 := ne_of_gt hGpos
    have hXeq : X = C / G := by rw [eq_div_iff hGne]; rw [mul_comm]; exact hGX'
    rw [hXeq]
    have h1 : G * (A / C + 4) = A * G / C + 4 * G := by field_simp
    have h2 : A / (C / G) = A * G / C := by field_simp
    rw [h1, h2]
    have h3 : (4 : ℝ) ≤ 4 * G := by
      have hG1' : (1 : ℝ) ≤ G := by rw [hG]; exact_mod_cast hgpos
      linarith
    linarith
  refine le_trans hmain (mul_le_mul_of_nonneg_left key ?_)
  have h3 : (0 : ℝ) ≤ 20 * (Pa.θ * Real.sqrt Pa.N) + 3 := by linarith
  exact h3

end

end Work.FIArea3
