import Mathlib
import Submission.Work.Asymptotics.MiddleRange.exists_diffQuotient_lower_general
import Submission.Work.Asymptotics.jDiff_lower_near_I
import Submission.Work.Kernels.Kernels

/-!
# The lower bound `c₀ ‖z - (τ - n)‖ ≤ ‖j z - j τ‖` near the translated cusps `n + i s₀`

The contour points of CKMRV belong to the `SL(2,ℤ)`-orbit of the positive imaginary axis;
the kernel `K^{(d)}` has a pole exactly at the points `z = τ - n` (`n = ±1`) of the `T`-orbit
of `τ`, and the residue there is proportional to `j'(τ - n)` (`Work.Asymptotics.AfunFun_vadd_one`).
For the asymptotics one needs that `j` separates points near such a pole as strongly as the
Euclidean distance, *uniformly in the point* `τ - n` of the two horizontal lines
`{n + i s : |s - s₀| < δ}`:

  `∃ c₀ > 0, c₀ ‖z - (τ - n)‖ ≤ ‖j z - j τ‖`

under the *non-degeneracy hypothesis* that `j'` is bounded below by a positive constant on
the ball of radius `δ` around the pole `w = τ - n`.  (Such a hypothesis is exactly what makes
the pole simple; it excludes in particular the elliptic point `i`, where `j'` vanishes.)

## The two regimes

* If `s₀ ≠ 1`, the contour point `i s₀` is not an elliptic point of `SL(2,ℤ)`: `E₄² E₆` does not
  vanish there, so `j' (i s₀) ≠ 0` and, `j` being holomorphic hence strictly differentiable
  there, `Work.Asymptotics.MiddleRange.exists_diffQuotient_lower_general` gives the asserted
  lower bound on a neighbourhood of `i s₀`, in which we place `w = τ - n` and `z`.  The
  non-degeneracy hypothesis is not needed in this regime.

* If `s₀ = 1` the contour point is the elliptic point `i`, where `j' = 0` and `j` is two-to-one
  near `i` (`j(S τ) = j τ`): the plain lower bound is false there.  But the non-degeneracy
  hypothesis now *forces* the ball of radius `δ` around `w = τ - n` to avoid `i` (a zero of
  `j'`), i.e. `‖w - i‖ ≥ δ`; and then `z` is bounded away from `S w`:
  `‖z - S w‖ ≥ 2‖w - i‖ - ‖z - w‖ ≥ δ/2`.  The sharp two-factor bound
  `‖j τ - j z‖ ≥ c ‖τ - z‖ ‖z - S τ‖` of `Work.Asymptotics.jDiff_lower_near_I` therefore yields
  `‖j z - j τ‖ ≥ c (δ/2) ‖z - w‖` — with constant `c δ/2 > 0` depending only on `δ`.

In both regimes `j` is `1`-periodic (`Work.Kernels.KernelFacts.jInvariantFun_vadd_one`), so
`j τ = j (τ - n)`.
-/

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

/-! ## Elementary estimates -/

/-- `S` fixes the elliptic point `i`. -/
private lemma S_smul_I : ModularGroup.S • UpperHalfPlane.I = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, UpperHalfPlane.coe_I]
  rw [inv_neg, Complex.inv_I]
  ring

/-- `j'` vanishes at the elliptic point `i`: `j' = -2πi E₄² E₆/Δ` and `E₆(i) = 0`, since
`E₆(S z) = z⁶ E₆(z)` and `S i = i`, `i⁶ = -1`. -/
private lemma jprime_I_eq_zero : Work.Residues.jprime UpperHalfPlane.I = 0 := by
  have h6 : Work.Kernels.E6Fun UpperHalfPlane.I = 0 := by
    have h := Work.Residues.E6Fun_S_smul UpperHalfPlane.I
    rw [S_smul_I] at h
    have hI6 : (UpperHalfPlane.I : ℂ) ^ 6 = -1 := by
      rw [UpperHalfPlane.coe_I, show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, Complex.I_sq]
      norm_num
    rw [hI6, neg_one_mul] at h
    have h2 : (2 : ℂ) * Work.Kernels.E6Fun UpperHalfPlane.I = 0 := by linear_combination h
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  simp [Work.Residues.jprime, h6]

/-- The Euclidean distance of two points of `ℍ` is at most the sum of the coordinate
differences. -/
private lemma norm_coe_sub_coe_le (w v : UpperHalfPlane) :
    ‖(w : ℂ) - (v : ℂ)‖ ≤ |w.re - v.re| + |w.im - v.im| := by
  have h := Complex.norm_le_abs_re_add_abs_im ((w : ℂ) - (v : ℂ))
  simpa [Complex.sub_re, Complex.sub_im] using h

/-- The distance to the contour point `i t` is at most the sum of the coordinate
differences. -/
private lemma norm_coe_sub_imagAxis_le (w : UpperHalfPlane) (t : ℝ) (ht : 0 < t) :
    ‖(w : ℂ) - ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ)‖ ≤ |w.re| + |w.im - t| := by
  have h := norm_coe_sub_coe_le w (Work.Kernels.imagAxis t ht)
  have h1 : (Work.Kernels.imagAxis t ht).re = 0 := by simp [Work.Kernels.imagAxis]
  have h2 : (Work.Kernels.imagAxis t ht).im = t := by simp [Work.Kernels.imagAxis]
  rw [h1, h2, sub_zero] at h
  exact h

/-- The distance to `i` is at most the sum of the coordinate differences. -/
private lemma norm_coe_sub_I_le (w : UpperHalfPlane) :
    ‖(w : ℂ) - Complex.I‖ ≤ |w.re| + |w.im - 1| := by
  have h := norm_coe_sub_imagAxis_le w 1 (by norm_num)
  have h2 : ((Work.Kernels.imagAxis 1 (by norm_num : (0 : ℝ) < 1) : UpperHalfPlane) : ℂ)
      = Complex.I := by
    simp [Work.Kernels.imagAxis]
  rw [h2] at h
  exact h

/-- The coercion of the translate `-(n : ℝ) +ᵥ τ`. -/
private lemma coe_vadd_neg_int (τ : UpperHalfPlane) (n : ℤ) :
    ((-(n : ℝ)) +ᵥ τ : ℂ) = (τ : ℂ) - (n : ℂ) := by
  rw [UpperHalfPlane.coe_vadd]
  push_cast
  ring

/-- `j` is invariant under the translations occurring here: `j (τ - n) = j τ` for `n = ±1`. -/
private lemma jInvariantFun_vadd_neg_int (τ : UpperHalfPlane) {n : ℤ}
    (hn : n = 1 ∨ n = -1) :
    Work.Kernels.jInvariantFun ((-(n : ℝ)) +ᵥ τ) = Work.Kernels.jInvariantFun τ := by
  rcases hn with h | h
  · have h1 : (-(n : ℝ)) = -1 := by rw [h]; norm_num
    rw [h1]
    have h3 : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = τ := by rw [← add_vadd]; norm_num
    have h2 := Work.Kernels.KernelFacts.jInvariantFun_vadd_one ((-1 : ℝ) +ᵥ τ)
    rw [h3] at h2
    exact h2.symm
  · have h1 : (-(n : ℝ)) = 1 := by rw [h]; norm_num
    rw [h1]
    exact Work.Kernels.KernelFacts.jInvariantFun_vadd_one τ

/-- **`S` expands distances near `i`.**  On the disc of radius `1/6` around `i` the map
`z ↦ -1/z` moves points at least `3/2` times as far as `i`: from the exact identity
`z - (-1/z) = (z - i)(z + i)/z` we get `‖z - Sz‖ = ‖z - i‖ ‖z + i‖ / ‖z‖` and both `‖z + i‖`
and `‖z‖` are within `1/6` of `2` and `1`. -/
private lemma norm_sub_S_smul_ge (w : UpperHalfPlane) (h : ‖(w : ℂ) - Complex.I‖ ≤ 1/6) :
    (3/2) * ‖(w : ℂ) - Complex.I‖ ≤
      ‖(w : ℂ) - ((ModularGroup.S • w : UpperHalfPlane) : ℂ)‖ := by
  set c := (w : ℂ) with hc
  have hcne : c ≠ 0 := by
    rw [hc]; exact UpperHalfPlane.ne_zero w
  have hcoe : ((ModularGroup.S • w : UpperHalfPlane) : ℂ) = -c⁻¹ := by
    rw [Work.Rigidity.coe_S_smul, hc]
  have hle : ‖c - Complex.I‖ ≤ 1/6 := by rw [hc]; exact h
  have hfac : (c - -c⁻¹) * c = (c - Complex.I) * (c + Complex.I) := by
    have h1 : (c + c⁻¹) * c = c ^ 2 + 1 := by field_simp
    have h2 : (c - Complex.I) * (c + Complex.I) = c ^ 2 + 1 := by
      rw [show (c - Complex.I) * (c + Complex.I) = c ^ 2 - Complex.I ^ 2 by ring, Complex.I_sq]
      ring
    rw [sub_neg_eq_add, h1, h2]
  have hA : 0 ≤ ‖c - Complex.I‖ := norm_nonneg _
  have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hcne
  have hnormfac : ‖c - -c⁻¹‖ * ‖c‖ = ‖c - Complex.I‖ * ‖c + Complex.I‖ := by
    rw [← norm_mul, ← norm_mul, hfac]
  have hnormfac2 : ‖c - -c⁻¹‖ = ‖c - Complex.I‖ * ‖c + Complex.I‖ / ‖c‖ := by
    rw [eq_div_iff (ne_of_gt hpos)]
    exact hnormfac
  have hup : (11 : ℝ)/6 ≤ ‖c + Complex.I‖ := by
    have hsub : (c + Complex.I) - (c - Complex.I) = (2 : ℂ) * Complex.I := by ring
    have h2 := norm_sub_le (c + Complex.I) (c - Complex.I)
    rw [hsub, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat] at h2
    linarith
  have hdn : ‖c‖ ≤ 1 + ‖c - Complex.I‖ := by
    have h2 := norm_add_le Complex.I (c - Complex.I)
    have hre : Complex.I + (c - Complex.I) = c := by ring
    rw [hre, Complex.norm_I] at h2
    linarith
  have hlt : ‖c‖ ≤ 7/6 := by linarith
  have hinv : (6 : ℝ)/7 ≤ ‖c‖⁻¹ := by
    rw [le_inv_comm₀ (by norm_num : (0 : ℝ) < 6/7) hpos]
    norm_num
    linarith
  have hprod : (3 : ℝ)/2 ≤ ‖c + Complex.I‖ * ‖c‖⁻¹ := by
    have h1 : (11 : ℝ)/6 * (6/7) ≤ ‖c + Complex.I‖ * ‖c‖⁻¹ :=
      mul_le_mul hup hinv (by norm_num) (by positivity)
    have h2 : (11 : ℝ)/6 * (6/7) = 11/7 := by norm_num
    linarith
  have hkey : (3/2) * ‖c - Complex.I‖ ≤ ‖c - Complex.I‖ * ‖c + Complex.I‖ / ‖c‖ := by
    calc (3/2) * ‖c - Complex.I‖ ≤ (‖c + Complex.I‖ * ‖c‖⁻¹) * ‖c - Complex.I‖ :=
          mul_le_mul_of_nonneg_right hprod hA
      _ = ‖c - Complex.I‖ * ‖c + Complex.I‖ / ‖c‖ := by rw [div_eq_mul_inv]; ring
  rw [hcoe, hnormfac2]
  exact hkey

/-! ## The lower bound -/

theorem exists_lower_bound_jDiff (s₀ : ℝ) (hs₀ : 0 < s₀) :
    ∃ δmax : ℝ, 0 < δmax ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δmax → ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (τ z : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) →
        |τ.im - s₀| < δ → |τ.re - (n : ℝ)| < δ →
        ‖(z : ℂ) - ((τ : ℂ) - (n : ℂ))‖ < δ →
        (∃ c : ℝ, 0 < c ∧ ∀ ζ : UpperHalfPlane,
          ‖(ζ : ℂ) - ((τ : ℂ) - (n : ℂ))‖ < δ → c ≤ ‖Work.Residues.jprime ζ‖) →
        c₀ * ‖(z : ℂ) - ((τ : ℂ) - (n : ℂ))‖ ≤
          ‖Work.Kernels.jInvariantFun z - Work.Kernels.jInvariantFun τ‖ := by
  obtain ⟨ρB, cB, hρB, hcB, hB⟩ := jDiff_lower_near_I
  by_cases hs : s₀ = 1
  · -- regime `s₀ = 1`: the contour point `i` is elliptic, and the hypothesis keeps the ball
    -- around `w = τ - n` away from `i`.
    refine ⟨min (min (ρB / 8) (1 / 32)) 1,
      lt_min (lt_min (by linarith) (by norm_num)) (by norm_num), ?_⟩
    intro δ hδ hδmax
    have hδ1 : δ ≤ ρB / 8 := le_trans hδmax (le_trans (min_le_left _ _) (min_le_left _ _))
    have hδ2 : δ ≤ 1 / 32 := le_trans hδmax (le_trans (min_le_left _ _) (min_le_right _ _))
    refine ⟨cB * (δ / 2), by positivity, ?_⟩
    intro τ z n hn hτim hτre hzw hc
    set w : UpperHalfPlane := (-(n : ℝ)) +ᵥ τ with hw
    have hwcoe : (w : ℂ) = (τ : ℂ) - (n : ℂ) := by rw [hw]; exact coe_vadd_neg_int τ n
    have hjw : Work.Kernels.jInvariantFun w = Work.Kernels.jInvariantFun τ := by
      rw [hw]; exact jInvariantFun_vadd_neg_int τ hn
    have hnorm : ‖(z : ℂ) - ((τ : ℂ) - (n : ℂ))‖ = ‖(w : ℂ) - (z : ℂ)‖ := by
      rw [← hwcoe]
      exact norm_sub_rev _ _
    have hzw' : ‖(z : ℂ) - (w : ℂ)‖ < δ := by
      have h := hzw
      rw [← hwcoe] at h
      exact h
    have hwz' : ‖(w : ℂ) - (z : ℂ)‖ < δ := by
      rw [norm_sub_rev]
      exact hzw'
    have hwre : w.re = -(n : ℝ) + τ.re := by rw [hw, UpperHalfPlane.vadd_re]
    have hwim : w.im = τ.im := by rw [hw, UpperHalfPlane.vadd_im]
    have habsre : |w.re| = |τ.re - (n : ℝ)| := by rw [hwre]; congr 1; ring
    have habsim : |w.im - 1| = |τ.im - s₀| := by rw [hwim, ← hs]
    -- the ball of radius `δ` around `w` avoids the zero `i` of `j'`
    have hwI_ge : δ ≤ ‖(w : ℂ) - Complex.I‖ := by
      obtain ⟨c, hcpos, hc'⟩ := hc
      by_contra hcon
      rw [not_le] at hcon
      have hI : ‖((UpperHalfPlane.I : UpperHalfPlane) : ℂ) - ((τ : ℂ) - (n : ℂ))‖ < δ := by
        rw [UpperHalfPlane.coe_I, ← hwcoe, norm_sub_rev]
        exact hcon
      have hle := hc' UpperHalfPlane.I hI
      rw [jprime_I_eq_zero, norm_zero] at hle
      linarith
    have hwI_lt : ‖(w : ℂ) - Complex.I‖ < 2 * δ := by
      have h1 := norm_coe_sub_I_le w
      rw [habsre, habsim] at h1
      linarith
    have hwI_le : ‖(w : ℂ) - Complex.I‖ ≤ 1 / 6 := by linarith
    -- `z` stays at distance at least `δ/2` from `S w`
    have hzSw : δ / 2 ≤ ‖(z : ℂ) - ((ModularGroup.S • w : UpperHalfPlane) : ℂ)‖ := by
      have h1 : (3 / 2) * ‖(w : ℂ) - Complex.I‖ ≤
          ‖(w : ℂ) - ((ModularGroup.S • w : UpperHalfPlane) : ℂ)‖ :=
        norm_sub_S_smul_ge w hwI_le
      have h2 : ‖(w : ℂ) - ((ModularGroup.S • w : UpperHalfPlane) : ℂ)‖ ≤
          ‖(w : ℂ) - (z : ℂ)‖ + ‖(z : ℂ) - ((ModularGroup.S • w : UpperHalfPlane) : ℂ)‖ := by
        have h := norm_add_le ((w : ℂ) - (z : ℂ))
          ((z : ℂ) - ((ModularGroup.S • w : UpperHalfPlane) : ℂ))
        rw [show (w : ℂ) - (z : ℂ) +
              ((z : ℂ) - ((ModularGroup.S • w : UpperHalfPlane) : ℂ))
            = (w : ℂ) - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) from by ring] at h
        exact h
      have h3 := hwz'
      linarith
    have hwρ : ‖(w : ℂ) - Complex.I‖ < ρB := by linarith
    have hzρ : ‖(z : ℂ) - Complex.I‖ < ρB := by
      have h1 : ‖(z : ℂ) - Complex.I‖ ≤ ‖(z : ℂ) - (w : ℂ)‖ + ‖(w : ℂ) - Complex.I‖ := by
        have h := norm_add_le ((z : ℂ) - (w : ℂ)) ((w : ℂ) - Complex.I)
        rw [show (z : ℂ) - (w : ℂ) + ((w : ℂ) - Complex.I) = (z : ℂ) - Complex.I
            from by ring] at h
        exact h
      have h3 := hzw'
      linarith
    have hmain := hB w z hwρ hzρ
    calc cB * (δ / 2) * ‖(z : ℂ) - ((τ : ℂ) - (n : ℂ))‖
        = cB * (δ / 2) * ‖(w : ℂ) - (z : ℂ)‖ := by rw [hnorm]
      _ = cB * ‖(w : ℂ) - (z : ℂ)‖ * (δ / 2) := by ring
      _ ≤ cB * ‖(w : ℂ) - (z : ℂ)‖ *
            ‖(z : ℂ) - ((ModularGroup.S • w : UpperHalfPlane) : ℂ)‖ :=
          mul_le_mul_of_nonneg_left hzSw (by positivity)
      _ ≤ ‖Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun z‖ := hmain
      _ = ‖Work.Kernels.jInvariantFun z - Work.Kernels.jInvariantFun τ‖ := by
          rw [hjw]
          exact norm_sub_rev _ _
  · -- regime `s₀ ≠ 1`: `i s₀` is not elliptic, so `j` is locally bi-Lipschitz there.
    obtain ⟨ρA, hρA, cA, hcA, hA⟩ := MiddleRange.exists_diffQuotient_lower_general hs₀ hs
    refine ⟨min (min (ρA / 8) (1 / 32)) 1,
      lt_min (lt_min (by linarith) (by norm_num)) (by norm_num), ?_⟩
    intro δ hδ hδmax
    have hδ1 : δ ≤ ρA / 8 := le_trans hδmax (le_trans (min_le_left _ _) (min_le_left _ _))
    refine ⟨cA, hcA, ?_⟩
    intro τ z n hn hτim hτre hzw hc
    set w : UpperHalfPlane := (-(n : ℝ)) +ᵥ τ with hw
    have hwcoe : (w : ℂ) = (τ : ℂ) - (n : ℂ) := by rw [hw]; exact coe_vadd_neg_int τ n
    have hjw : Work.Kernels.jInvariantFun w = Work.Kernels.jInvariantFun τ := by
      rw [hw]; exact jInvariantFun_vadd_neg_int τ hn
    have hnorm : ‖(z : ℂ) - ((τ : ℂ) - (n : ℂ))‖ = ‖(w : ℂ) - (z : ℂ)‖ := by
      rw [← hwcoe]
      exact norm_sub_rev _ _
    have hzw' : ‖(z : ℂ) - (w : ℂ)‖ < δ := by
      have h := hzw
      rw [← hwcoe] at h
      exact h
    have hwz' : ‖(w : ℂ) - (z : ℂ)‖ < δ := by
      rw [norm_sub_rev]
      exact hzw'
    have hwre : w.re = -(n : ℝ) + τ.re := by rw [hw, UpperHalfPlane.vadd_re]
    have hwim : w.im = τ.im := by rw [hw, UpperHalfPlane.vadd_im]
    have habsre : |w.re| = |τ.re - (n : ℝ)| := by rw [hwre]; congr 1; ring
    have hwA_lt : ‖(w : ℂ) - ((Work.Kernels.imagAxis s₀ hs₀ : UpperHalfPlane) : ℂ)‖ < 2 * δ := by
      have h1 := norm_coe_sub_imagAxis_le w s₀ hs₀
      rw [habsre, hwim] at h1
      linarith
    have hwρ : ‖(w : ℂ) - ((Work.Kernels.imagAxis s₀ hs₀ : UpperHalfPlane) : ℂ)‖ < ρA := by
      linarith
    have hzρ : ‖(z : ℂ) - ((Work.Kernels.imagAxis s₀ hs₀ : UpperHalfPlane) : ℂ)‖ < ρA := by
      have h1 : ‖(z : ℂ) - ((Work.Kernels.imagAxis s₀ hs₀ : UpperHalfPlane) : ℂ)‖ ≤
          ‖(z : ℂ) - (w : ℂ)‖ +
            ‖(w : ℂ) - ((Work.Kernels.imagAxis s₀ hs₀ : UpperHalfPlane) : ℂ)‖ := by
        have h := norm_add_le ((z : ℂ) - (w : ℂ))
          ((w : ℂ) - ((Work.Kernels.imagAxis s₀ hs₀ : UpperHalfPlane) : ℂ))
        rw [show (z : ℂ) - (w : ℂ) +
              ((w : ℂ) - ((Work.Kernels.imagAxis s₀ hs₀ : UpperHalfPlane) : ℂ))
            = (z : ℂ) - ((Work.Kernels.imagAxis s₀ hs₀ : UpperHalfPlane) : ℂ) from by ring] at h
        exact h
      have h3 := hzw'
      linarith [hwA_lt]
    have hmain := hA w z hwρ hzρ
    calc cA * ‖(z : ℂ) - ((τ : ℂ) - (n : ℂ))‖ = cA * ‖(w : ℂ) - (z : ℂ)‖ := by rw [hnorm]
      _ ≤ ‖Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun z‖ := hmain
      _ = ‖Work.Kernels.jInvariantFun z - Work.Kernels.jInvariantFun τ‖ := by
          rw [hjw]
          exact norm_sub_rev _ _

end Work.Asymptotics
