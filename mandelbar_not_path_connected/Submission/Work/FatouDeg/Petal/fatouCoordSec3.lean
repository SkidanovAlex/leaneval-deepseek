/-
Copyright: subproject `Submission/Work/FatouDeg/Petal/` of `mandelbar_not_path_connected`.

Ported verbatim from `Submission/Work/MultiPetal/` of the same project, with the exponent
hypothesis `4 ≤ m` weakened to `3 ≤ m` (see `Submission/Work/FatouDeg/NOTES.md`).

# Multi-petal Leau--Fatou: the Fatou coordinate of `z ↦ z - z^m + z^(m+1) G z`

This file assembles `Work.FatouDeg.Petal.fatouCoordSec3` from the pieces in this directory:

* `DefsAux`                -- the map `Pfun`, the chart data `upoly/Qpoly/Ppoly/betac/Afun/Rfun`,
                              the Fatou coordinate `phifun`, and the domains `Pet`, `Dom`;
* `petalGeomAux`           -- sector invariance, modulus decrease and the chart contraction;
* `polyAlgebraAux`         -- `(1 - X G) * Qpoly ≡ 1 mod X^(m-1)` and `(m-1) P - X P' = Qpoly`;
* `defectBoundAux`         -- `‖Rfun z‖ ≤ C ‖z‖^m` on `Dom`;
* `orbitBoundsAux`         -- `‖P^[k] z‖^(m-1) ≤ ((‖z‖^(m-1))⁻¹ + c k)⁻¹` and `P^[k] z → 0`;
* `coordSumAux`            -- summability, holomorphy, the Abel equation, `φ = A + O(‖z‖)`;
* `coordDerivAux`          -- `‖(φ - A)'‖ ≤ D'` on the petal (Cauchy estimate);
* `marginAux`              -- a Cauchy disc of `Pet` inside `Dom`;
* `polyBoundsAux`          -- `Ppoly = 1/(m-1) + O(w)`, `Qpoly = 1 + O(w)` on the unit disc;
* `afunDerivAux`           -- `Re A' ≤ -(1/2)‖z‖^(-m)` on the petal, `‖A' z^m + 1‖ ≤ 1/4` on `Dom`;
* `stripImagePetAux`       -- the image of the petal contains the tail of every horizontal strip.
-/
import Submission.Work.FatouDeg.Petal.DefsAux
import Submission.Work.FatouDeg.Petal.petalGeomAux
import Submission.Work.FatouDeg.Petal.polyAlgebraAux
import Submission.Work.FatouDeg.Petal.defectBoundAux
import Submission.Work.FatouDeg.Petal.orbitBoundsAux
import Submission.Work.FatouDeg.Petal.coordSumAux
import Submission.Work.FatouDeg.Petal.coordDerivAux
import Submission.Work.FatouDeg.Petal.injOnAux
import Submission.Work.FatouDeg.Petal.marginAux
import Submission.Work.FatouDeg.Petal.polyBoundsAux
import Submission.Work.FatouDeg.Petal.afunDerivAux
import Submission.Work.FatouDeg.Petal.stripImagePetAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open scoped Topology
open Set Filter Metric

namespace Work.FatouDeg.Petal

/-- `Pfun m G` is the evaluation of the polynomial appearing in the target statement. -/
theorem Pfun_eq_eval (m : ℕ) (G : Polynomial ℂ) (z : ℂ) :
    Pfun m G z = (Polynomial.X - Polynomial.X ^ m + Polynomial.X ^ (m + 1) * G).eval z := by
  simp only [Pfun, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X]

/-- The function of the target statement is `Pfun m G`. -/
theorem eval_eq_Pfun (m : ℕ) (G : Polynomial ℂ) :
    (fun z : ℂ => (Polynomial.X - Polynomial.X ^ m + Polynomial.X ^ (m + 1) * G).eval z)
      = Pfun m G := by
  funext z
  exact (Pfun_eq_eval m G z).symm

/-- A bound for a polynomial on the closed unit ball. -/
theorem exists_bound_poly (G : Polynomial ℂ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, ‖z‖ ≤ 1 → ‖G.eval z‖ ≤ M := by
  have hcont : Continuous fun z : ℂ => G.eval z := by fun_prop
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro z hz
  exact le_trans (hM z (by simpa [Metric.mem_closedBall, dist_zero_right] using hz))
    (le_max_left _ _)

theorem fatouCoordSec3 (m : ℕ) (hm : 3 ≤ m) (G : Polynomial ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Pa : Set ℂ, ∃ φa : ℂ → ℂ,
      IsOpen Pa ∧ Pa.Nonempty ∧ Pa ⊆ Metric.ball 0 δ ∧ (0 : ℂ) ∉ Pa ∧
      Pa ⊆ {z : ℂ | 0 < z.re ∧ (m : ℝ) * |z.im| < z.re} ∧
      Set.MapsTo (fun z : ℂ => (Polynomial.X - Polynomial.X ^ m
        + Polynomial.X ^ (m + 1) * G).eval z) Pa Pa ∧
      (∀ z ∈ Pa, Filter.Tendsto
        (fun n : ℕ => ((fun z : ℂ => (Polynomial.X - Polynomial.X ^ m
          + Polynomial.X ^ (m + 1) * G).eval z)^[n]) z) Filter.atTop (nhds 0)) ∧
      DifferentiableOn ℂ φa Pa ∧ Set.InjOn φa Pa ∧
      (∀ z ∈ Pa, φa ((fun z : ℂ => (Polynomial.X - Polynomial.X ^ m
          + Polynomial.X ^ (m + 1) * G).eval z) z) = φa z + 1) ∧
      (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, ∀ τ : ℂ, C < τ.re → |τ.im| ≤ B →
        ∃ z ∈ Pa, φa z = τ) := by
  classical
  have hm1 : 1 ≤ m := by omega
  have hm2 : 2 ≤ m := by omega
  -- a bound for `G` near the origin
  obtain ⟨M, hMnn, hM⟩ := exists_bound_poly G
  -- the quantitative inputs, each with its own threshold
  obtain ⟨ρA, hρApos, hAgeom⟩ := petalGeomAux m hm G M
  obtain ⟨hcoefA, hPQA⟩ := polyAlgebraAux m hm2 G
  obtain ⟨ρC, hρCpos, hCdef⟩ := defectBoundAux m hm G M hcoefA hPQA
  obtain ⟨KP, hKPnn, hPbd⟩ := (polyBoundsAux m hm2 G).1
  obtain ⟨KQ, hKQnn, hQbd⟩ := (polyBoundsAux m hm2 G).2
  obtain ⟨ρD, hρDpos, hDder⟩ := afunDerivAux m hm G hKQnn hQbd
  -- a working radius below all the thresholds
  set ρw : ℝ := min (min ρA ρC) (min ρD 1) / 2 with hρwdef
  have hminpos : 0 < min (min ρA ρC) (min ρD 1) :=
    lt_min (lt_min hρApos hρCpos) (lt_min hρDpos one_pos)
  have hρw_le_min : ρw ≤ min (min ρA ρC) (min ρD 1) := by
    rw [hρwdef]; exact div_le_self hminpos.le (by norm_num)
  have hρwpos : 0 < ρw := by
    rw [hρwdef]; positivity
  have hρwA : ρw ≤ ρA := le_trans hρw_le_min (le_trans (min_le_left _ _) (min_le_left _ _))
  have hρwC : ρw ≤ ρC := le_trans hρw_le_min (le_trans (min_le_left _ _) (min_le_right _ _))
  have hρwD : ρw ≤ ρD := le_trans hρw_le_min (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρw1 : ρw ≤ 1 := le_trans hρw_le_min (le_trans (min_le_right _ _) (min_le_right _ _))
  have hρwhalf : ρw ≤ 1 / 2 := by
    have h1 : min (min ρA ρC) (min ρD 1) ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  have hMGw : ∀ z : ℂ, ‖z‖ ≤ 2 * ρw → ‖G.eval z‖ ≤ M := fun z hz => hM z (by linarith)
  -- geometry, defect bound, coordinate and its derivative, all at `ρw`
  obtain ⟨hmapDw, hmapPetw, hnormDw, c, hcpos, hcontrDw⟩ := hAgeom ρw hρwpos hρwA hMGw
  obtain ⟨C, hCnn, hdefectDw⟩ := hCdef ρw hρwpos hρwC hMGw
  obtain ⟨-, hdiffDw, habelDw, D, hDnn, hgrowthDw⟩ :=
    coordSumAux m hm G hρwpos hcpos hCnn hmapDw hnormDw hcontrDw hdefectDw
  have hκpos : (0 : ℝ) < 1 / (32 * (m : ℝ)) := by positivity
  have hmarginw := marginAux m hm hρwpos
  obtain ⟨D', hD'nn, hderivBoundw⟩ :=
    coordDerivAux m hm G hρwpos hκpos hDnn hdiffDw hgrowthDw hmarginw
  obtain ⟨hAfunRew, hAfunDomw⟩ := hDder ρw hρwpos hρwD
  -- the petal radius: it is also small compared with `1/D'`
  set ρ : ℝ := min (min ρw δ) ((1 / 2) * (2 * D' + 1)⁻¹) with hρdef
  have hD'invpos : 0 < (1 / 2) * (2 * D' + 1)⁻¹ := by
    have : (0 : ℝ) < 2 * D' + 1 := by linarith
    positivity
  have hρpos : 0 < ρ := by
    rw [hρdef]; exact lt_min (lt_min hρwpos hδ) hD'invpos
  have hρle_ρw : ρ ≤ ρw := by
    rw [hρdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hρle_δ : ρ ≤ δ := by
    rw [hρdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hρle_D : ρ ≤ (1 / 2) * (2 * D' + 1)⁻¹ := by rw [hρdef]; exact min_le_right _ _
  have hρle1 : ρ ≤ 1 := by linarith [hρle_ρw, hρwhalf]
  have hMG : ∀ z : ℂ, ‖z‖ ≤ 2 * ρ → ‖G.eval z‖ ≤ M := fun z hz => hM z (by linarith)
  obtain ⟨hmapD, hmapPet, hnormD, c₂, hc₂pos, hcontrD⟩ :=
    hAgeom ρ hρpos (le_trans hρle_ρw hρwA) hMG
  obtain ⟨C₂, hC₂nn, hdefectD⟩ := hCdef ρ hρpos (le_trans hρle_ρw hρwC) hMG
  obtain ⟨-, hdiffD, habelD, D₂, hD₂nn, hgrowthD⟩ :=
    coordSumAux m hm G hρpos hc₂pos hC₂nn hmapD hnormD hcontrD hdefectD
  have hmargin := marginAux m hm hρpos
  -- the petal at radius `ρ` sits inside the petal at radius `ρw`
  have hPet_sub : Pet m ρ ⊆ Pet m ρw := by
    intro z hz
    rw [mem_Pet] at hz ⊢
    exact ⟨lt_of_lt_of_le hz.1 hρle_ρw, hz.2⟩
  have hnormPet : ∀ z ∈ Pet m ρ, ‖Pfun m G z‖ ≤ ‖z‖ :=
    fun z hz => hnormD z (Pet_subset_Dom m hm1 ρ hz)
  have hcontrPet : ∀ z ∈ Pet m ρ, (‖z‖ ^ (m - 1))⁻¹ + c₂ ≤ (‖Pfun m G z‖ ^ (m - 1))⁻¹ :=
    fun z hz => hcontrD z (Pet_subset_Dom m hm1 ρ hz)
  -- `D' * ρ^m < 1/4`, the smallness needed below
  have hρmρ : ρ ^ m ≤ ρ := by
    have h1 : ρ ^ (m - 1) ≤ 1 := pow_le_one₀ hρpos.le hρle1
    have h2 : ρ ^ m = ρ * ρ ^ (m - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [h2]; nlinarith [hρpos.le, h1]
  have hD'ρm_lt : D' * ρ ^ m < 1 / 4 := by
    have h1 : D' * ρ ^ m ≤ D' * ρ := mul_le_mul_of_nonneg_left hρmρ hD'nn
    have h2 : D' * ρ ≤ D' * ((1 / 2) * (2 * D' + 1)⁻¹) :=
      mul_le_mul_of_nonneg_left hρle_D hD'nn
    have h3 : D' * ((1 / 2) * (2 * D' + 1)⁻¹) = D' / (2 * (2 * D' + 1)) := by
      rw [div_eq_mul_inv]; field_simp
    have h4 : D' / (2 * (2 * D' + 1)) < 1 / 4 := by
      rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * (2 * D' + 1))]
      linarith
    linarith
  -- the sign of the derivative of the coordinate on the petal
  have hsign : ∀ z ∈ Pet m ρ, (deriv (phifun m G) z).re < 0 := by
    intro z hz
    have hzρw : z ∈ Pet m ρw := hPet_sub hz
    have hzn : ‖z‖ < ρ := (mem_Pet.mp hz).1
    have hzre : 0 < z.re := by
      have h2 := (mem_Pet.mp hz).2
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      exact lt_of_le_of_lt (mul_nonneg hm0.le (abs_nonneg z.im)) h2
    have hz0 : z ≠ 0 := by intro h; rw [h] at hzre; simp at hzre
    have hpowpos : 0 < ‖z‖ ^ m := pow_pos (norm_pos_iff.mpr hz0) m
    have h2D : 2 * D' < (‖z‖ ^ m)⁻¹ := by
      rw [← one_div, lt_div_iff₀ hpowpos]
      have h1 : ‖z‖ ^ m ≤ ρ ^ m := pow_le_pow_left₀ (norm_nonneg z) hzn.le m
      have h2 : 2 * D' * ‖z‖ ^ m ≤ 2 * D' * ρ ^ m :=
        mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 2 * D')
      linarith
    have h1 : (deriv (phifun m G) z).re
        ≤ (deriv (Afun m G) z).re + ‖deriv (phifun m G) z - deriv (Afun m G) z‖ := by
      have hsplit : deriv (phifun m G) z
          = deriv (Afun m G) z + (deriv (phifun m G) z - deriv (Afun m G) z) := by ring
      conv_lhs => rw [hsplit]
      rw [Complex.add_re]
      linarith [Complex.re_le_norm (deriv (phifun m G) z - deriv (Afun m G) z)]
    have h2 := hAfunRew z hzρw
    have h3 := hderivBoundw z hzρw
    linarith
  -- injectivity of the coordinate on the petal
  have hinjPet : Set.InjOn (phifun m G) (Pet m ρ) :=
    injOnAux m hm G hρpos (hdiffD.mono (Pet_subset_Dom m hm1 ρ)) hsign
  -- the normalised derivative on the petal
  have hε : D' * ρ ^ m + 1 / 4 < 1 / 2 := by linarith
  have hderivPet : ∀ z ∈ Pet m ρ, ‖deriv (phifun m G) z * z ^ m + 1‖ ≤ D' * ρ ^ m + 1 / 4 := by
    intro z hz
    have hzρw : z ∈ Pet m ρw := hPet_sub hz
    have h3 := hderivBoundw z hzρw
    have h4 := hAfunDomw z (Pet_subset_Dom m hm1 ρw hzρw)
    have h5 : ‖z‖ ^ m ≤ ρ ^ m := pow_le_pow_left₀ (norm_nonneg z) (mem_Pet.mp hz).1.le m
    have hsplit : deriv (phifun m G) z * z ^ m + 1
        = (deriv (phifun m G) z - deriv (Afun m G) z) * z ^ m
          + (deriv (Afun m G) z * z ^ m + 1) := by ring
    calc ‖deriv (phifun m G) z * z ^ m + 1‖
        = ‖(deriv (phifun m G) z - deriv (Afun m G) z) * z ^ m
            + (deriv (Afun m G) z * z ^ m + 1)‖ := by rw [hsplit]
      _ ≤ ‖deriv (phifun m G) z - deriv (Afun m G) z‖ * ‖z ^ m‖
            + ‖deriv (Afun m G) z * z ^ m + 1‖ := by
          refine le_trans (norm_add_le _ _) (le_of_eq ?_)
          rw [norm_mul]
      _ ≤ D' * ρ ^ m + 1 / 4 := by
          rw [norm_pow]
          have h6 : D' * ‖z‖ ^ m ≤ D' * ρ ^ m := mul_le_mul_of_nonneg_left h5 hD'nn
          have h7 : ‖deriv (phifun m G) z - deriv (Afun m G) z‖ * ‖z‖ ^ m ≤ D' * ‖z‖ ^ m :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
          linarith
  -- the strip image
  have hstrip : ∀ B : ℝ, 0 ≤ B → ∃ Cc : ℝ, ∀ τ : ℂ, Cc < τ.re → |τ.im| ≤ B →
      ∃ z ∈ Pet m ρ, phifun m G z = τ :=
    stripImagePetAux m hm G hρpos hε hD₂nn hKPnn hκpos hdiffD hderivPet hgrowthD hPbd hmargin
  -- the orbits converge to `0`
  have htend : ∀ z ∈ Pet m ρ, Filter.Tendsto (fun k : ℕ => (Pfun m G)^[k] z) Filter.atTop (nhds 0) :=
    fun z hz => (orbitBoundsAux m hm G hc₂pos hmapPet hnormPet hcontrPet).2.2 z hz
  -- assembly
  refine ⟨Pet m ρ, (fun z : ℂ => if z ∈ Pet m ρ then phifun m G z else 0), isOpen_Pet m ρ,
    Pet_nonempty m hm1 hρpos, ?_, zero_notMem_Pet m ρ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    linarith [(mem_Pet.mp hz).1]
  · intro z hz
    have h2 := (mem_Pet.mp hz).2
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    exact ⟨lt_of_le_of_lt (mul_nonneg hm0.le (abs_nonneg z.im)) h2, h2⟩
  · intro z hz
    rw [eval_eq_Pfun]
    show Pfun m G z ∈ Pet m ρ
    exact hmapPet hz
  · intro z hz
    rw [eval_eq_Pfun]
    exact htend z hz
  · refine (hdiffD.mono (Pet_subset_Dom m hm1 ρ)).congr (fun z hz => ?_)
    change (if z ∈ Pet m ρ then phifun m G z else 0) = phifun m G z
    rw [if_pos hz]
  · intro z hz z' hz' heq
    have h1 : phifun m G z = phifun m G z' := by
      change (if z ∈ Pet m ρ then phifun m G z else 0)
        = (if z' ∈ Pet m ρ then phifun m G z' else 0) at heq
      rw [if_pos hz, if_pos hz'] at heq
      exact heq
    exact hinjPet hz hz' h1
  · intro z hz
    have hfz : Pfun m G z ∈ Pet m ρ := hmapPet hz
    rw [eval_eq_Pfun]
    change (if Pfun m G z ∈ Pet m ρ then phifun m G (Pfun m G z) else 0)
        = (if z ∈ Pet m ρ then phifun m G z else 0) + 1
    rw [if_pos hz, if_pos hfz]
    exact habelD z (Pet_subset_Dom m hm1 ρ hz)
  · intro B hB
    obtain ⟨Cc, hCc⟩ := hstrip B hB
    refine ⟨Cc, fun τ hτ hτB => ?_⟩
    obtain ⟨z, hz, hzτ⟩ := hCc τ hτ hτB
    refine ⟨z, hz, ?_⟩
    change (if z ∈ Pet m ρ then phifun m G z else 0) = τ
    rw [if_pos hz]
    exact hzτ

end Work.FatouDeg.Petal
