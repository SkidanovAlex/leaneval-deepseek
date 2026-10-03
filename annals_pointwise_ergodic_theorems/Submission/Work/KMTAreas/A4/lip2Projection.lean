/-
# Proposition `lip-2`, the arc projection step

`Work.KMTAreas.A4.lip2Projection` is the *arc projection* step of the alternate inverse theorem
`lip-2` of Krause–Mirek–Tao, §5.2 (the last piece listed in the docstring of
`Work.KMTAreas.A4.lip2Step1`).

Given a `1`-bounded, absolutely summable `g : ℤ → ℂ` whose **windowed spectral mass**

  `B ≤ ∫_0^1 ‖ĝ(t)‖² · winFT M s t dt`

is large (here `winFT M s = 𝓕_ℤ (win M s)` is the Fourier transform of the normalized reproducing
window `win M s m = M⁻¹ ψ(m/M) e(m s)`, a bump of width `1/M` around `s`), the lemma produces a
function `G` which

* is bounded by an absolute constant `C` and has `ℓ¹` mass `≤ C ‖g‖₁`,
* has `ℤ`-Fourier transform supported in the closed arc of radius `1/M` centred at `-s`,
* pairs with `g` in the sense `B ≤ ‖bilinPair g G‖`.

The construction is the natural one: `G = star ∘ (win M s * g)` (conjugation of the windowed
frequency projection of `g`).  Writing `w = win M s`, `F = w * g`, one has

  `𝓕 F = 𝓕 w · 𝓕 g`, so `𝓕 F` is supported in the arc of radius `1/M` around `s`, and
  `𝓕 (star ∘ F) (ξ) = star (𝓕 F (-ξ))`, so `𝓕 G` is supported in the arc around `-s`;

and Parseval's identity for `ℓ¹` functions on `ℤ` gives

  `bilinPair g G = Σ_x g x · star (F x) = ∫_0^1 ĝ(t) star(𝓕F(t)) dt
                = ∫_0^1 ‖ĝ(t)‖² winFT M s t dt ≥ B`.

The three analytic inputs (the `ℓ¹` convolution package for `ℤ`, the Parseval identity for `ĝ`,
and the window support package) are proved in
`Work.KMTAreas.A4.zConvL1`, `Work.KMTAreas.A4.kmtFhatParseval` and
`Work.KMTAreas.A4.winPackage`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.winPackage
import Submission.Work.KMTAreas.A4.zConvL1
import Submission.Work.KMTAreas.A4.kmtFhatParseval

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-! ## Elementary frequency-circle facts -/

/-- The arc with the negated centre is the reflection of the arc. -/
theorem neg_mem_arcSet_iff {α ξ : FreqCircle} {r : ℝ} :
    -ξ ∈ arcSet α r ↔ ξ ∈ arcSet (-α) r := by
  constructor
  · rintro ⟨θ, hθ, hθeq⟩
    refine ⟨-θ, by simpa using hθ, ?_⟩
    have h : ξ = -(α + ((θ : ℝ) : FreqCircle)) := by rw [← hθeq]; simp
    rw [h, AddCircle.coe_neg, neg_add_rev, add_comm]
  · rintro ⟨θ, hθ, hθeq⟩
    refine ⟨-θ, by simpa using hθ, ?_⟩
    have h2 : -ξ = α + (((-θ : ℝ)) : FreqCircle) := by
      rw [hθeq, AddCircle.coe_neg, neg_add_rev, neg_neg]
      abel
    exact h2

/-- A character has modulus one. -/
theorem norm_fourier_eq_one (n : ℤ) (ξ : FreqCircle) : ‖(fourier n ξ : ℂ)‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

/-- `star (fourier n (-ξ)) = fourier n ξ`. -/
theorem star_fourier_neg (n : ℤ) (ξ : FreqCircle) :
    star ((fourier n (-ξ) : ℂ)) = (fourier n ξ : ℂ) := by
  rw [fourier_apply, fourier_apply, smul_neg, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj,
    Complex.star_def, Complex.conj_conj]

/-- The `ℤ`-Fourier transform of the pointwise conjugate is the conjugate transform at the
negated frequency. -/
theorem ZFourier_star_flip {F : ℤ → ℂ} (hF : Summable fun x : ℤ => ‖F x‖) (ξ : FreqCircle) :
    ZFourier (fun x => star (F x)) ξ = star (ZFourier F (-ξ)) := by
  have hs : Summable fun x : ℤ => F x * (fourier (-x) (-ξ) : ℂ) :=
    Summable.of_norm_bounded hF fun x => by
      rw [norm_mul, norm_fourier_eq_one, mul_one]
  have hmap2 : star (∑' x : ℤ, F x * (fourier (-x) (-ξ) : ℂ))
      = ∑' x : ℤ, star (F x * (fourier (-x) (-ξ) : ℂ)) :=
    Summable.map_tsum hs (starRingEnd ℂ) continuous_star
  rw [ZFourier, ZFourier, hmap2]
  refine tsum_congr fun x => ?_
  rw [star_mul, star_fourier_neg, mul_comm]

/-- The real-frequency Fourier transform `kmtFhat` is `ZFourier` at the corresponding point of the
frequency circle. -/
theorem kmtFhat_eq_ZFourier (f : ℤ → ℂ) (t : ℝ) :
    Work.A3.kmtFhat f t = ZFourier f ((t : ℝ) : FreqCircle) := by
  rw [Work.A3.kmtFhat, ZFourier]
  refine tsum_congr fun x => ?_
  congr 1
  rw [fourier_coe_apply]
  norm_num
  congr 1
  ring

/-! ## The arc projection -/

theorem lip2Projection :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : ℤ → ℂ), Summable (fun x : ℤ => ‖g x‖) → (∀ x : ℤ, ‖g x‖ ≤ 1) →
    ∀ (M : ℝ) (s : ℝ) (B : ℝ), 2 ≤ M →
      B ≤ ∫ t in (0 : ℝ)..1, ‖Work.A3.kmtFhat g t‖ ^ 2
        * (Work.KMTAreas.A4.winFT M s t).re →
      ∃ G : ℤ → ℂ,
        (∀ x : ℤ, ‖G x‖ ≤ C) ∧ Summable (fun x : ℤ => ‖G x‖) ∧
        (∑' x : ℤ, ‖G x‖ ≤ C * ∑' x : ℤ, ‖g x‖) ∧
        Work.Analysis.InverseTheory.FourierSupportIn G
          (Work.KMTAreas.A4.arcSet
            (-(((s : ℝ)) : Work.Analysis.InverseTheory.FreqCircle)) (1 / M)) ∧
        B ≤ ‖Work.Analysis.InverseTheory.bilinPair g G‖ := by
  obtain ⟨C₀, hC₀pos, hC₀le⟩ := win_tsum_le
  refine ⟨max C₀ 1, lt_of_lt_of_le hC₀pos (le_max_left _ _), ?_⟩
  intro g hgsum hgbd M s B hM hB
  have hMpos : (0 : ℝ) < M := by linarith
  have hM1 : (1 : ℝ) ≤ M := by linarith
  set w : ℤ → ℂ := win M ((s : ℝ) : FreqCircle) with hwdef
  have hwsum : Summable fun m : ℤ => ‖w m‖ := by
    rw [hwdef]; exact win_summable M hM1 _
  have hwC : (∑' m : ℤ, ‖w m‖) ≤ C₀ := by
    rw [hwdef]; exact hC₀le M _ hM1
  -- the `ℓ¹` convolution package
  have hz : Summable (fun x : ℤ => ‖∑' m : ℤ, w m * g (x - m)‖) ∧
      (∑' x : ℤ, ‖∑' m : ℤ, w m * g (x - m)‖ ≤ (∑' m : ℤ, ‖w m‖) * ∑' m : ℤ, ‖g m‖) ∧
      (∀ x : ℤ, ‖∑' m : ℤ, w m * g (x - m)‖ ≤ ∑' m : ℤ, ‖w m‖) ∧
      (∀ ξ : FreqCircle, ZFourier (fun x : ℤ => ∑' m : ℤ, w m * g (x - m)) ξ
        = ZFourier w ξ * ZFourier g ξ) :=
    zConvL1 w g hwsum hgsum hgbd
  -- the Parseval identity
  have hPK : ∀ a b : ℤ → ℂ, Summable (fun x : ℤ => ‖a x‖) → Summable (fun x : ℤ => ‖b x‖) →
      (∑' x : ℤ, a x * star (b x))
        = ∫ t in (0 : ℝ)..1, Work.A3.kmtFhat a t * star (Work.A3.kmtFhat b t) := by
    intro a b ha hb
    exact kmtFhatParseval a b ha hb
  -- the window support package
  have hwin : FourierSupportIn w (arcSet ((s : ℝ) : FreqCircle) (1 / M)) ∧
      (∀ t : ℝ, winFT M s t = ((winFT M s t).re : ℂ)) := by
    rw [hwdef]
    exact winPackage M s hM
  set F : ℤ → ℂ := fun x => ∑' m : ℤ, w m * g (x - m) with hFdef
  have hFsum : Summable fun x : ℤ => ‖F x‖ := hz.1
  have hFZ : ∀ ξ : FreqCircle, ZFourier F ξ = ZFourier w ξ * ZFourier g ξ := hz.2.2.2
  refine ⟨fun x => star (F x), ?_, ?_, ?_, ?_, ?_⟩
  · -- uniform bound
    intro x
    calc ‖star (F x)‖ = ‖F x‖ := norm_star _
      _ ≤ ∑' m : ℤ, ‖w m‖ := by rw [hFdef]; exact hz.2.2.1 x
      _ ≤ C₀ := hwC
      _ ≤ max C₀ 1 := le_max_left _ _
  · -- summability of the output
    rw [show (fun x : ℤ => ‖star (F x)‖) = fun x => ‖F x‖ from funext fun x => norm_star _]
    exact hFsum
  · -- `ℓ¹` mass bound
    have hg0 : (0 : ℝ) ≤ ∑' x : ℤ, ‖g x‖ := tsum_nonneg fun x => norm_nonneg _
    calc ∑' x : ℤ, ‖star (F x)‖ = ∑' x : ℤ, ‖F x‖ := tsum_congr fun x => norm_star _
      _ ≤ (∑' m : ℤ, ‖w m‖) * ∑' x : ℤ, ‖g x‖ := by rw [hFdef]; exact hz.2.1
      _ ≤ max C₀ 1 * ∑' x : ℤ, ‖g x‖ :=
          mul_le_mul_of_nonneg_right (hwC.trans (le_max_left C₀ 1)) hg0
  · -- Fourier support of the output
    intro ξ hξ
    have hneg : -ξ ∉ arcSet ((s : ℝ) : FreqCircle) (1 / M) :=
      fun hc => hξ (neg_mem_arcSet_iff.mp hc)
    have hw0 : ZFourier w (-ξ) = 0 := hwin.1 (-ξ) hneg
    have hF0 : ZFourier F (-ξ) = 0 := by rw [hFZ (-ξ), hw0, zero_mul]
    rw [ZFourier_star_flip hFsum ξ, hF0, star_zero]
  · -- the pairing bound
    have hwinreal : ∀ t : ℝ, star (winFT M s t) = winFT M s t := by
      intro t
      rw [hwin.2 t]
      exact Complex.conj_ofReal _
    have hwZF : ∀ t : ℝ, ZFourier w ((t : ℝ) : FreqCircle) = winFT M s t := by
      intro t
      rw [hwdef]
      exact winZFourier M s t hMpos
    have hhatF : ∀ t : ℝ, Work.A3.kmtFhat F t = winFT M s t * Work.A3.kmtFhat g t := by
      intro t
      rw [kmtFhat_eq_ZFourier F t, hFZ, hwZF t, ← kmtFhat_eq_ZFourier g t]
    have hkey : ∀ t : ℝ, Work.A3.kmtFhat g t * star (Work.A3.kmtFhat F t)
        = (((‖Work.A3.kmtFhat g t‖ ^ 2 * (winFT M s t).re : ℝ)) : ℂ) := by
      intro t
      have hst : star (winFT M s t) = winFT M s t := hwinreal t
      have hconj : Work.A3.kmtFhat g t * star (Work.A3.kmtFhat g t)
          = (((‖Work.A3.kmtFhat g t‖ ^ 2 : ℝ)) : ℂ) := by
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have hstarF : star (Work.A3.kmtFhat F t)
          = winFT M s t * star (Work.A3.kmtFhat g t) := by
        rw [hhatF t, star_mul, hst]
        ring
      calc Work.A3.kmtFhat g t * star (Work.A3.kmtFhat F t)
          = Work.A3.kmtFhat g t * (winFT M s t * star (Work.A3.kmtFhat g t)) := by rw [hstarF]
        _ = winFT M s t * (Work.A3.kmtFhat g t * star (Work.A3.kmtFhat g t)) := by ring
        _ = winFT M s t * (((‖Work.A3.kmtFhat g t‖ ^ 2 : ℝ)) : ℂ) := by rw [hconj]
        _ = (((winFT M s t).re : ℝ) : ℂ) * (((‖Work.A3.kmtFhat g t‖ ^ 2 : ℝ)) : ℂ) := by
              rw [hwin.2 t, Complex.ofReal_re]
        _ = (((winFT M s t).re * ‖Work.A3.kmtFhat g t‖ ^ 2 : ℝ) : ℂ) := by
              rw [Complex.ofReal_mul]
        _ = (((‖Work.A3.kmtFhat g t‖ ^ 2 * (winFT M s t).re : ℝ)) : ℂ) := by rw [mul_comm]
    have hInt : (∫ t in (0 : ℝ)..1, Work.A3.kmtFhat g t * star (Work.A3.kmtFhat F t))
        = (((∫ t in (0 : ℝ)..1, ‖Work.A3.kmtFhat g t‖ ^ 2 * (winFT M s t).re : ℝ)) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      exact intervalIntegral.integral_congr fun t _ => hkey t
    show B ≤ ‖(∑' x : ℤ, g x * star (F x))‖
    rw [hPK g F hgsum hFsum, hInt]
    calc B ≤ (∫ t in (0 : ℝ)..1, ‖Work.A3.kmtFhat g t‖ ^ 2 * (winFT M s t).re : ℝ) := hB
      _ = (((∫ t in (0 : ℝ)..1, ‖Work.A3.kmtFhat g t‖ ^ 2 * (winFT M s t).re : ℝ)) : ℂ).re :=
          (Complex.ofReal_re _).symm
      _ ≤ ‖((( ∫ t in (0 : ℝ)..1, ‖Work.A3.kmtFhat g t‖ ^ 2 * (winFT M s t).re : ℝ)) : ℂ)‖ := 
          Complex.re_le_norm _

end Work.KMTAreas.A4
