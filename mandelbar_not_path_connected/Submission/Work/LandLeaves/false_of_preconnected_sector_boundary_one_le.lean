import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Filter Asymptotics Set
open scoped Topology

/-- A purely imaginary complex number squares to minus the square of its norm. -/
private lemma sq_eq_neg_norm_sq_of_re_eq_zero {w : ℂ} (hw : w.re = 0) :
    w ^ 2 = -((‖w‖ ^ 2 : ℝ) : ℂ) := by
  have hnorm : ‖w‖ ^ 2 = w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hw]; ring
  rw [hnorm]
  apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im, hw]

set_option linter.unusedVariables false

theorem false_of_preconnected_sector_boundary_one_le {n : ℕ} (hn : 1 ≤ n) {c z : ℂ}
    (hc : c ≠ 0) (hzn : z ^ n = -1) (hz1 : z ≠ 1) {L : Set ℂ} (hLcpt : IsCompact L)
    (hLpre : IsPreconnected L) (hLne : L.Nonempty) (hLsph : L ⊆ Metric.sphere (0 : ℂ) 1)
    (hLsect : ∀ d ∈ L, (c * d ^ n).re = 0) (hLinv : ∀ d ∈ L, z * d ∈ L) : False := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  set γ : ℂ := -(((‖c‖ ^ 2 : ℝ)) : ℂ) / c ^ 2 with hγdef
  -- Every `d ∈ L` satisfies `d ^ (2 * n) = γ`.
  have hval : ∀ d ∈ L, d ^ (2 * n) = γ := by
    intro d hd
    have hdn : ‖d‖ = 1 := by
      have h := hLsph hd
      rw [Metric.mem_sphere] at h
      rwa [dist_zero_right] at h
    have hsq := sq_eq_neg_norm_sq_of_re_eq_zero (hLsect d hd)
    have hnorm : ‖c * d ^ n‖ ^ 2 = ‖c‖ ^ 2 := by
      rw [norm_mul, norm_pow, hdn, one_pow, mul_one]
    rw [hnorm] at hsq
    have hexp : (c * d ^ n) ^ 2 = c ^ 2 * d ^ (2 * n) := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm n 2]
    rw [hexp] at hsq
    rw [hγdef, eq_div_iff hc2, mul_comm]
    exact hsq
  -- `L` is contained in the root set of a nonzero polynomial, hence is finite.
  have h2n : 2 * n ≠ 0 := by omega
  have hp : (Polynomial.X ^ (2 * n) - Polynomial.C γ : Polynomial ℂ) ≠ 0 := by
    intro hp0
    have hcoeff :
        (Polynomial.X ^ (2 * n) - Polynomial.C γ : Polynomial ℂ).coeff (2 * n) = 1 := by
      simp [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C, h2n]
    rw [hp0, Polynomial.coeff_zero] at hcoeff
    exact zero_ne_one hcoeff
  have hSfin : {d : ℂ | (Polynomial.X ^ (2 * n) - Polynomial.C γ).IsRoot d}.Finite :=
    Polynomial.finite_setOfPred_isRoot hp
  have hsub : L ⊆ {d : ℂ | (Polynomial.X ^ (2 * n) - Polynomial.C γ).IsRoot d} := by
    intro d hd
    show (Polynomial.X ^ (2 * n) - Polynomial.C γ).IsRoot d
    unfold Polynomial.IsRoot
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      hval d hd, sub_self]
  have hLfin : L.Finite := hSfin.subset hsub
  have hLdisc : IsDiscrete L := hLfin.isDiscrete
  -- A preconnected discrete set is a subsingleton.
  have hLsub : L.Subsingleton := (hLpre.isDiscrete_iff_subsingleton).mp hLdisc
  obtain ⟨d0, hd0⟩ := hLne
  have hzd0 : z * d0 ∈ L := hLinv d0 hd0
  have heq : z * d0 = d0 := hLsub hzd0 hd0
  have hd0ne : d0 ≠ 0 := by
    have hdn : ‖d0‖ = 1 := by
      have h := hLsph hd0
      rw [Metric.mem_sphere] at h
      rwa [dist_zero_right] at h
    have : ‖d0‖ ≠ 0 := by rw [hdn]; norm_num
    exact norm_ne_zero_iff.mp this
  have hz : z = 1 := mul_right_cancel₀ hd0ne (by rw [heq, one_mul])
  exact hz1 hz

end Work.LandLeaves
