import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

/-! ## The vanishing of `D_z^j` on the zero function -/

/-- `D_z^j` of the identically zero function vanishes. -/
theorem DzIter_zero_fun (j : ℕ) :
    Work.Spaces.DzIter j (fun _ (_ : ℝ) => (0 : ℝ)) = fun _ _ => (0 : ℝ) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      funext z θ
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
      rw [deriv_const]
      ring

-- Import `Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux` (which defines
-- `KsFun α = fun z _ => α * (2 * z / (1 + z) ^ 2)` and
-- `KsTor α = fun z θ => Real.sin θ ^ 2 * KsFun α z θ`, and proves
-- `ks_Dz_bound : |D_z^j (KsFun α) z| ≤ 2*5040*203*α*(z/(1+z))` for `j ≤ 6`, `z ≥ 0`;
-- `DzIter_const_mul_apply`, `pzIter_DthIter_KsTor`, `DthIter_KsFun_eq_zero`,
-- `dthU_sinSq_weighted : |D_θ^i(sin²) θ| ≤ C*(α + sin 2θ)*sin(2θ)^{α/5}` for `1 ≤ i ≤ 6`,
-- `θ ∈ (0,π/2)`), plus `Submission.Work.Spaces.Defs`.
-- Route: `mixed j i A = DzIter j (DthIter i A)`; for `A = KsFun` use `DthIter_KsFun_eq_zero`
-- (`i ≥ 1`, both sides 0) and `ks_Dz_bound` (`i = 0`); for `A = KsTor` use
-- `DthIter_KsTor`/`DzIter_const_mul_apply` to factor the LHS as
-- `|D_θ^i(sin²) θ| * |D_z^j (KsFun α) z|` (`sin²θ ≤ 1` for `i = 0`) and multiply the two
-- bounds.  `θ ∈ Iθ` (needed by `ks_Dz_bound`) follows from `0 < θ < π/2`.
theorem ksMixed : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ A : ℝ → ℝ → ℝ,
    (A = (fun z (_ : ℝ) => α * (2 * z / (1 + z) ^ 2)) ∨
     A = (fun z θ : ℝ => Real.sin θ ^ 2 * (α * (2 * z / (1 + z) ^ 2)))) →
    ∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i A z θ| ≤ C * α * (z / (1 + z)) *
        (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1) := by
  obtain ⟨C1, hC1pos, hC1⟩ := dthU_sinSq_weighted
  refine ⟨2 * 5040 * 203 * max C1 1, ?_, ?_⟩
  · have h : (1 : ℝ) ≤ max C1 1 := le_max_right _ _
    nlinarith
  · intro α hαI A hA j i hji z θ hz hθ0 hθ2
    obtain ⟨hαpos, hα1⟩ := hαI
    have hαnn : (0 : ℝ) ≤ α := le_of_lt hαpos
    have hz0 : (0 : ℝ) ≤ z := le_of_lt hz
    have hz1 : (0 : ℝ) < 1 + z := by linarith
    have hzr : (0 : ℝ) ≤ z / (1 + z) := div_nonneg hz0 (le_of_lt hz1)
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ2⟩
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hsin0 : (0 : ℝ) ≤ Real.sin (2 * θ) := le_of_lt hsin
    have hX0 : (0 : ℝ) ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg hsin0 _)
    have hbr : 0 ≤ 2 * 5040 * 203 * α * (z / (1 + z)) :=
      mul_nonneg (mul_nonneg (by norm_num) hαnn) hzr
    -- the two functions named in the statement are `KsFun α` / `KsTor α`
    have hfun1 : (fun z (_ : ℝ) => α * (2 * z / (1 + z) ^ 2)) = KsFun α := rfl
    have hfun2 : (fun z θ : ℝ => Real.sin θ ^ 2 * (α * (2 * z / (1 + z) ^ 2)))
        = KsTor α := rfl
    rcases hA with hA | hA
    · -- ## the radial function `KsFun α`
      have hAK : A = KsFun α := by rw [hA]; exact hfun1
      subst hAK
      by_cases hi : 1 ≤ i
      · -- `i ≥ 1`: `D_θ^i (KsFun α) = 0`
        have hi6 : i ≤ 6 := by omega
        have hzero : Work.Spaces.DthIter i (KsFun α) = fun _ _ => (0 : ℝ) :=
          DthIter_KsFun_eq_zero α hi
        have hm : Work.Spaces.mixed j i (KsFun α) z θ = 0 := by
          rw [Work.Spaces.mixed, hzero, DzIter_zero_fun j]
        rw [hm, abs_zero, ite_eq_left hi]
        exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hαnn) hzr) hX0
      · -- `i = 0`
        have hi0 : i = 0 := by omega
        subst hi0
        have hb := ks_Dz_bound α hαnn j (by omega) z hz0 θ hθI
        have hb' : |Work.Spaces.mixed j 0 (KsFun α) z θ|
            ≤ 2 * 5040 * 203 * α * (z / (1 + z)) := by
          simpa only [Work.Spaces.mixed_zero_right] using hb
        rw [ite_eq_right (by norm_num : ¬ (1 ≤ 0)), mul_one]
        refine le_trans hb' ?_
        calc (2 * 5040 * 203 : ℝ) * α * (z / (1 + z))
            = (2 * 5040 * 203 : ℝ) * α * (z / (1 + z)) * 1 := by ring
          _ ≤ (2 * 5040 * 203 : ℝ) * α * (z / (1 + z)) * (max C1 1) :=
              mul_le_mul_of_nonneg_left (le_max_right C1 1) hbr
          _ = 2 * 5040 * 203 * max C1 1 * α * (z / (1 + z)) := by ring
    · -- ## the angular function `KsTor α`
      have hAK : A = KsTor α := by rw [hA]; exact hfun2
      subst hAK
      have hi6 : i ≤ 6 := by omega
      -- factor the mixed derivative
      have hfac : Work.Spaces.mixed j i (KsTor α) z θ
          = Work.Spaces.dthU^[i] (fun t : ℝ => Real.sin t ^ 2) θ
            * Work.Spaces.DzIter j (KsFun α) z θ := by
        rw [Work.Spaces.mixed]
        rw [show Work.Spaces.DthIter i (KsTor α)
              = fun z θ => Work.Spaces.dthU^[i] (fun t : ℝ => Real.sin t ^ 2) θ
                  * KsFun α z θ
            from funext fun z => funext fun θ => DthIter_KsTor α i z θ]
        rw [DzIter_const_mul_apply]
      rw [hfac, abs_mul]
      have hb := ks_Dz_bound α hαnn j (by omega) z hz0 θ hθI
      by_cases hi : 1 ≤ i
      · -- `i ≥ 1`: multiply the two bounds
        rw [ite_eq_left hi]
        have hd := hC1 α ⟨hαpos, hα1⟩ i hi hi6 θ ⟨hθ0, hθ2⟩
        have hXnn : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := hX0
        refine le_trans (mul_le_mul hd hb (abs_nonneg _)
          (mul_nonneg (le_of_lt hC1pos) hXnn)) ?_
        calc C1 * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
              * (2 * 5040 * 203 * α * (z / (1 + z)))
            = C1 * ((2 * 5040 * 203) * α * (z / (1 + z))
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by ring
          _ ≤ max C1 1 * ((2 * 5040 * 203) * α * (z / (1 + z))
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
              mul_le_mul_of_nonneg_right (le_max_left C1 1)
                (mul_nonneg hbr hXnn)
          _ = 2 * 5040 * 203 * max C1 1 * α * (z / (1 + z))
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
      · -- `i = 0`: `|sin²θ| ≤ 1`
        have hi0 : i = 0 := by omega
        subst hi0
        rw [ite_eq_right (by norm_num : ¬ (1 ≤ 0)), mul_one]
        simp only [Function.iterate_zero, id_eq]
        have hs2 : |Real.sin θ ^ 2| ≤ 1 := by
          rw [abs_of_nonneg (sq_nonneg _)]
          exact Real.sin_sq_le_one θ
        refine le_trans (mul_le_mul hs2 hb (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)) ?_
        calc (1 : ℝ) * (2 * 5040 * 203 * α * (z / (1 + z)))
            = (2 * 5040 * 203 : ℝ) * α * (z / (1 + z)) := by ring
          _ ≤ 2 * 5040 * 203 * max C1 1 * α * (z / (1 + z)) := by
              calc (2 * 5040 * 203 : ℝ) * α * (z / (1 + z))
                  = (2 * 5040 * 203 : ℝ) * α * (z / (1 + z)) * 1 := by ring
                _ ≤ (2 * 5040 * 203 : ℝ) * α * (z / (1 + z)) * (max C1 1) :=
                    mul_le_mul_of_nonneg_left (le_max_right C1 1) hbr
                _ = 2 * 5040 * 203 * max C1 1 * α * (z / (1 + z)) := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
