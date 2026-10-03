/-
# `Submission.Work.FIArea4.polarBox_card_le` — the size of the polar box (5.14)

The polar box of (5.14) — primary `z` with `N < |z|² ≤ (1+θ)N` and `arg z` in a sector of width
`2πθ` — has `O(θ²N + θ√N + 1)` Gaussian integers.  Geometrically the box is the intersection of
the *annular sector* `N < |z|² ≤ (1+θ)N`, `φ < arg z ≤ φ + 2πθ` with the discrete box `boxN`.

The proof is a single observation: the whole annular sector is contained in a disc of radius
`5θ√N`, namely the disc of radius `√N` at the mid-angle `φ + πθ`:
* radially `√((1+θ)N) - √N ≤ θ√N` because `√(1+θ) ≤ 1+θ`;
* angularly `|arg z - (φ + πθ)| ≤ πθ`, and the chord of the disc of radius `√N` is at most the
  arc length (`‖exp (I·a) - exp (I·b)‖ ≤ ‖a - b‖`).

A disc of real radius `ρ` contains at most `(2ρ+1)²` Gaussian integers, because its real and
imaginary parts lie in two intervals of length `2ρ`.  With `ρ = 5θ√N` this gives
`(10θ√N + 1)² ≤ 100 θ²N + 20 θ√N + 1 ≤ 100 (θ²N + θ√N + 1)`, which is the assertion.
-/
import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FITop.Defs
import Submission.Work.FITop3.Defs3

namespace Work.FIArea4

open scoped BigOperators
open scoped Classical

noncomputable section

/-! ## 0. Elementary facts about `ℤ[i]` and about discs -/

/-- `‖z‖² = |z|² = gnorm z` for a Gaussian integer, read in `ℂ`. -/
lemma normSq_toComplex_gnorm (z : GaussianInt) :
    ‖z.toComplex‖ ^ 2 = (((Work.FIPlan.gnorm z : ℕ)) : ℝ) := by
  have hnorm : Zsqrtd.norm z = z.re * z.re + z.im * z.im := by simp [Zsqrtd.norm]
  have hge : (0 : ℝ) ≤ (z.norm : ℝ) := by
    rw [hnorm]
    have : (0 : ℤ) ≤ z.re * z.re + z.im * z.im := by
      have h1 : (0 : ℤ) ≤ z.re * z.re := mul_self_nonneg _
      have h2 : (0 : ℤ) ≤ z.im * z.im := mul_self_nonneg _
      linarith
    exact_mod_cast this
  have hcast : (((z.norm.natAbs : ℕ)) : ℝ) = (z.norm : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg hge]
  rw [show Work.FIPlan.gnorm z = z.norm.natAbs from rfl, hcast, hnorm, Complex.sq_norm,
    Complex.normSq_apply, ← GaussianInt.intCast_re, ← GaussianInt.intCast_im]
  push_cast
  ring

/-- `‖z‖ = √(|z|²)` for a Gaussian integer. -/
lemma norm_toComplex_eq_sqrt_gnorm (z : GaussianInt) :
    ‖z.toComplex‖ = Real.sqrt ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by
  rw [← normSq_toComplex_gnorm z, Real.sqrt_sq (norm_nonneg _)]

/-- The norm of a real complex number is its absolute value. -/
lemma norm_ofReal_abs (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs]

/-- `‖z‖` depends only on `z.re`, `z.im` through `z.toComplex.re`, `z.toComplex.im`. -/
lemma ofReal_re_eq_re (z : GaussianInt) : ((z.re : ℤ) : ℝ) = z.toComplex.re := by
  rw [← Complex.ofReal_re ((z.re : ℤ) : ℝ), ← GaussianInt.intCast_re z]
  simp

/-- Same for the imaginary part. -/
lemma ofReal_im_eq_im (z : GaussianInt) : ((z.im : ℤ) : ℝ) = z.toComplex.im := by
  rw [← Complex.ofReal_re ((z.im : ℤ) : ℝ), ← GaussianInt.intCast_im z]
  simp

/-- **Disc counting.**  A finite set of integers lying in an interval of length `2ρ` has at most
`2ρ + 1` elements. -/
lemma card_int_le_of_mem_interval (S : Finset ℤ) {t ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ x ∈ S, t ≤ (x : ℝ) ∧ (x : ℝ) ≤ t + 2 * ρ) : (S.card : ℝ) ≤ 2 * ρ + 1 := by
  have hsub : S ⊆ Finset.Icc ⌈t⌉ ⌊t + 2 * ρ⌋ := by
    intro x hx
    obtain ⟨h1, h2⟩ := h x hx
    rw [Finset.mem_Icc]
    exact ⟨Int.ceil_le.mpr h1, Int.le_floor.mpr h2⟩
  have hcard : S.card ≤ (Finset.Icc ⌈t⌉ ⌊t + 2 * ρ⌋).card := Finset.card_le_card hsub
  rw [Int.card_Icc] at hcard
  have hmain : (((⌊t + 2 * ρ⌋ + 1 - ⌈t⌉ : ℤ).toNat : ℕ) : ℝ) ≤ 2 * ρ + 1 := by
    rcases le_or_gt 0 (⌊t + 2 * ρ⌋ + 1 - ⌈t⌉ : ℤ) with hk | hk
    · have hk' : (((⌊t + 2 * ρ⌋ + 1 - ⌈t⌉ : ℤ).toNat : ℕ) : ℝ)
          = (((⌊t + 2 * ρ⌋ + 1 - ⌈t⌉ : ℤ)) : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hk
      rw [hk']
      have h1 : ((⌊t + 2 * ρ⌋ : ℤ) : ℝ) ≤ t + 2 * ρ := Int.floor_le _
      have h2 : t ≤ ((⌈t⌉ : ℤ) : ℝ) := Int.le_ceil _
      push_cast
      linarith
    · have hk' : (((⌊t + 2 * ρ⌋ + 1 - ⌈t⌉ : ℤ).toNat : ℕ) : ℝ) = 0 := by
        rw [Int.toNat_of_nonpos hk.le]; norm_num
      rw [hk']; linarith
  calc (S.card : ℝ) ≤ (((⌊t + 2 * ρ⌋ + 1 - ⌈t⌉ : ℤ).toNat : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ 2 * ρ + 1 := hmain

/-- **A disc contains at most `(2ρ+1)²` Gaussian integers.**  The real and imaginary parts of the
points of the disc lie in intervals of length `2ρ`, and the map `z ↦ (z.re, z.im)` is injective. -/
lemma card_le_of_dist_le (A : Finset GaussianInt) (c : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ z ∈ A, ‖z.toComplex - c‖ ≤ ρ) : (A.card : ℝ) ≤ (2 * ρ + 1) ^ 2 := by
  set R : Finset ℤ := A.image (fun z => z.re) with hR
  set I : Finset ℤ := A.image (fun z => z.im) with hI
  have hcard1 : A.card ≤ R.card * I.card := by
    have hinj : Function.Injective (fun z : GaussianInt => (z.re, z.im)) := by
      intro a b hab
      exact Zsqrtd.ext (congrArg Prod.fst hab) (congrArg Prod.snd hab)
    calc A.card = (A.image (fun z : GaussianInt => (z.re, z.im))).card :=
          (Finset.card_image_of_injective A hinj).symm
      _ ≤ (R ×ˢ I).card := by
          apply Finset.card_le_card
          intro p hp
          obtain ⟨z, hz, hpz⟩ := Finset.mem_image.mp hp
          rw [← hpz]
          exact Finset.mem_product.mpr
            ⟨Finset.mem_image.mpr ⟨z, hz, rfl⟩, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
      _ = R.card * I.card := Finset.card_product R I
  have hRcard : (R.card : ℝ) ≤ 2 * ρ + 1 := by
    apply card_int_le_of_mem_interval (t := c.re - ρ) R hρ
    intro x hx
    obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hx
    rw [← he]
    have h1 := h z hz
    have h2 : |((z.re : ℤ) : ℝ) - c.re| ≤ ρ := by
      calc |((z.re : ℤ) : ℝ) - c.re| = |(z.toComplex - c).re| := by
            rw [ofReal_re_eq_re z, Complex.sub_re]
        _ ≤ ‖z.toComplex - c‖ := Complex.abs_re_le_norm _
        _ ≤ ρ := h1
    rw [abs_le] at h2
    constructor <;> linarith [h2.1, h2.2]
  have hIcard : (I.card : ℝ) ≤ 2 * ρ + 1 := by
    apply card_int_le_of_mem_interval (t := c.im - ρ) I hρ
    intro x hx
    obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hx
    rw [← he]
    have h1 := h z hz
    have h2 : |((z.im : ℤ) : ℝ) - c.im| ≤ ρ := by
      calc |((z.im : ℤ) : ℝ) - c.im| = |(z.toComplex - c).im| := by
            rw [ofReal_im_eq_im z, Complex.sub_im]
        _ ≤ ‖z.toComplex - c‖ := Complex.abs_im_le_norm _
        _ ≤ ρ := h1
    rw [abs_le] at h2
    constructor <;> linarith [h2.1, h2.2]
  calc (A.card : ℝ) ≤ (R.card : ℝ) * (I.card : ℝ) := by exact_mod_cast hcard1
    _ ≤ (2 * ρ + 1) * (2 * ρ + 1) := by
        apply mul_le_mul hRcard hIcard (by exact_mod_cast Nat.zero_le _) (by linarith)
    _ = (2 * ρ + 1) ^ 2 := by ring

/-! ## 1. The chord/arc inequality on the unit circle -/

/-- `‖exp (I a) - exp (I b)‖ ≤ |a - b|`: on the unit circle the chord is shorter than the arc. -/
lemma norm_exp_sub_exp_le (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ ≤ |a - b| := by
  have hkey : Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)
      = Complex.exp ((b : ℂ) * Complex.I)
        * (Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hkey, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [show ((a - b : ℝ) : ℂ) * Complex.I = Complex.I * ((a - b : ℝ) : ℂ) from mul_comm _ _]
  simpa [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)

/-! ## 2. The polar box lies in a disc of radius `5θ√N` -/

/-- **The polar box is contained in a disc of radius `5θ√N`**, centred at the point of modulus
`√N` at the mid-angle `φ + πθ` of the sector (5.14).  Radially the box is `θ√N` thick, and
angularly its points differ from the centre by at most `πθ` in angle, i.e. by at most `πθ√N` in
chord length. -/
lemma dist_polarBox_le (Pa : Work.FITop.Params) (φ : ℝ) (z : GaussianInt)
    (h : Work.FITop3.InPolarBox Pa φ z) :
    ‖z.toComplex - (Real.sqrt Pa.N : ℂ)
        * Complex.exp (((φ + Real.pi * Pa.θ : ℝ) : ℂ) * Complex.I)‖
      ≤ 5 * Pa.θ * Real.sqrt Pa.N := by
  obtain ⟨-, hNlo, hNhi, harglo, hargle⟩ := h
  set r : ℝ := ‖z.toComplex‖ with hr
  set s : ℝ := Real.sqrt Pa.N with hs
  set ψ : ℝ := Complex.arg z.toComplex with hψ
  set ψc : ℝ := φ + Real.pi * Pa.θ with hψc
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hθ0 : 0 < Pa.θ := Pa.hθ0
  have hr_eq : r = Real.sqrt ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by
    rw [hr]; exact norm_toComplex_eq_sqrt_gnorm z
  have hz_eq : z.toComplex = (r : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I) := by
    have h := Complex.norm_mul_exp_arg_mul_I z.toComplex
    rw [← hr, ← hψ] at h
    exact h.symm
  -- radial: the box is `θ√N` thick
  have hr_ge : s ≤ r := by
    rw [hr_eq, hs]
    exact Real.sqrt_le_sqrt (by linarith [hNlo])
  have hr_le : r ≤ Real.sqrt ((1 + Pa.θ) * Pa.N) := by
    rw [hr_eq]
    exact Real.sqrt_le_sqrt hNhi
  have hsqrt1 : Real.sqrt (1 + Pa.θ) ≤ 1 + Pa.θ := by
    have h1 : (1 : ℝ) ≤ 1 + Pa.θ := by linarith
    calc Real.sqrt (1 + Pa.θ) ≤ Real.sqrt ((1 + Pa.θ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 1 + Pa.θ := Real.sqrt_sq (by linarith)
  have hrad : |r - s| ≤ Pa.θ * s := by
    rw [abs_of_nonneg (by linarith)]
    have h2 : Real.sqrt ((1 + Pa.θ) * Pa.N) = Real.sqrt (1 + Pa.θ) * s := by
      rw [hs, Real.sqrt_mul (by linarith)]
    calc r - s ≤ Real.sqrt ((1 + Pa.θ) * Pa.N) - s := by linarith
      _ = (Real.sqrt (1 + Pa.θ) - 1) * s := by rw [h2]; ring
      _ ≤ Pa.θ * s := by
          apply mul_le_mul_of_nonneg_right _ hs0
          linarith
  -- angular: the sector has width `2πθ`, so the centre is within `πθ` in angle
  have hang : |ψ - ψc| ≤ Real.pi * Pa.θ := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hexp : ‖Complex.exp ((ψ : ℂ) * Complex.I) - Complex.exp ((ψc : ℂ) * Complex.I)‖
      ≤ |ψ - ψc| := norm_exp_sub_exp_le ψ ψc
  calc ‖z.toComplex - (Real.sqrt Pa.N : ℂ)
        * Complex.exp (((φ + Real.pi * Pa.θ : ℝ) : ℂ) * Complex.I)‖
      = ‖(r : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)
          - (s : ℂ) * Complex.exp ((ψc : ℂ) * Complex.I)‖ := by rw [hz_eq, ← hs, ← hψc]
    _ = ‖(((r - s : ℝ)) : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)
          + (s : ℂ) * (Complex.exp ((ψ : ℂ) * Complex.I)
              - Complex.exp ((ψc : ℂ) * Complex.I))‖ := by
        congr 1
        push_cast
        ring
    _ ≤ ‖(((r - s : ℝ)) : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)‖
          + ‖(s : ℂ) * (Complex.exp ((ψ : ℂ) * Complex.I)
              - Complex.exp ((ψc : ℂ) * Complex.I))‖ := norm_add_le _ _
    _ = |r - s| + s * ‖Complex.exp ((ψ : ℂ) * Complex.I)
            - Complex.exp ((ψc : ℂ) * Complex.I)‖ := by
        rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
          norm_ofReal_abs, norm_ofReal_abs, abs_of_nonneg hs0]
    _ ≤ Pa.θ * s + s * |ψ - ψc| := by
        have h2 : s * ‖Complex.exp ((ψ : ℂ) * Complex.I) - Complex.exp ((ψc : ℂ) * Complex.I)‖
            ≤ s * |ψ - ψc| := mul_le_mul_of_nonneg_left hexp hs0
        linarith
    _ ≤ 5 * Pa.θ * s := by
        have hπ4 : Real.pi < 4 := Real.pi_lt_four
        have hts : 0 ≤ Pa.θ * s := mul_nonneg hθ0.le hs0
        nlinarith [hang, hπ4, hts]

/-! ## 3. The size of the box -/

/-- The polar box (5.14) — primary `z` with `N < |z|² ≤ (1+θ)N` and `arg z` in a sector of width
`2πθ` — contains `O(θ²N + θ√N + 1)` Gaussian integers: it is an annular sector of area `πθ²N`
and perimeter `≲ θ√N`.  This is the "size of the box" saving used throughout §§5–17 (e.g. the
`vol B = πθ²N₀ ≍ πθ²N` of (5.14)). -/
theorem polarBox_card_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (Pa : Work.FITop.Params) (φ : ℝ),
      (((Work.FITop.boxN Pa).filter (fun z => Work.FITop3.InPolarBox Pa φ z)).card : ℝ)
        ≤ C * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) := by
  refine ⟨200, by norm_num, ?_⟩
  intro Pa φ
  set A : Finset GaussianInt :=
    (Work.FITop.boxN Pa).filter (fun z => Work.FITop3.InPolarBox Pa φ z) with hA
  set c : ℂ := (Real.sqrt Pa.N : ℂ)
    * Complex.exp (((φ + Real.pi * Pa.θ : ℝ) : ℂ) * Complex.I) with hc
  set ρ : ℝ := 5 * Pa.θ * Real.sqrt Pa.N with hρ
  have hρ0 : 0 ≤ ρ := by
    rw [hρ]
    exact mul_nonneg (mul_nonneg (by norm_num) Pa.hθ0.le) (Real.sqrt_nonneg _)
  have hdist : ∀ z ∈ A, ‖z.toComplex - c‖ ≤ ρ := by
    intro z hz
    have hbox : Work.FITop3.InPolarBox Pa φ z := by
      rw [hA] at hz
      exact (Finset.mem_filter.mp hz).2
    rw [hc, hρ]
    exact dist_polarBox_le Pa φ z hbox
  have hcard := card_le_of_dist_le A c hρ0 hdist
  refine le_trans hcard ?_
  have hs0 : 0 ≤ Real.sqrt Pa.N := Real.sqrt_nonneg _
  have hts : 0 ≤ Pa.θ * Real.sqrt Pa.N := mul_nonneg Pa.hθ0.le hs0
  have hsq : (Real.sqrt Pa.N) ^ 2 = Pa.N := Real.sq_sqrt (by linarith [Pa.hN1])
  rw [hρ]
  have hexpand : (2 * (5 * Pa.θ * Real.sqrt Pa.N) + 1) ^ 2
      = 100 * (Pa.θ ^ 2 * Pa.N) + 20 * (Pa.θ * Real.sqrt Pa.N) + 1 := by
    rw [show (2 * (5 * Pa.θ * Real.sqrt Pa.N) + 1) ^ 2
          = (10 * Pa.θ * Real.sqrt Pa.N) ^ 2 + 2 * (10 * Pa.θ * Real.sqrt Pa.N) + 1 by ring,
      show (10 * Pa.θ * Real.sqrt Pa.N) ^ 2 = 100 * Pa.θ ^ 2 * (Real.sqrt Pa.N) ^ 2 by ring,
      hsq]
    ring
  rw [hexpand]
  linarith

end

end Work.FIArea4
