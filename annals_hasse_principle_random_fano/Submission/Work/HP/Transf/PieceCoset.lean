import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Transf.Basic
import Submission.Work.HP.Transf.PieceRankDrop

/-!
# A short vector in the unit coset of the section

If `v ∈ dualLat L`, `w ∈ L` with `⟪v,w⟫ = 1`, and `g₁, …, g_R` span the real span of the
section `L ∩ v^⊥`, then the coset `{y ∈ L : ⟪v,y⟫ = 1}` has a point `w'` with
`‖w'‖² ≤ (½ Σ‖g_j‖)² + 1/‖v‖²`.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP.Transf

variable {ι : Type*} [Fintype ι]

theorem exists_coset_short (L : Submodule ℤ (ι → ℝ)) (v w : ι → ℝ)
    (hv : v ∈ dualLat L) (hw : w ∈ L) (hvw : dotR v w = 1)
    (R : ℕ) (g : Fin R → (ι → ℝ)) (hg : ∀ j, g j ∈ secLat v L) (hgli : LinearIndependent ℝ g)
    (hspan : Submodule.span ℝ (Set.range g)
      = Submodule.span ℝ ((secLat v L : Submodule ℤ (ι → ℝ)) : Set (ι → ℝ))) :
    ∃ w' ∈ L, dotR v w' = 1 ∧ rNorm w' ^ 2 ≤ ((∑ j, rNorm (g j)) / 2) ^ 2 + 1 / rNorm v ^ 2 := by
  classical
  have hvne : v ≠ 0 := by
    intro h
    rw [h] at hvw
    simpa [dotR] using hvw
  have hvn : 0 < rNorm v := rNorm_pos_iff.mpr hvne
  set wH : ι → ℝ := w - ((dotR v w) / (rNorm v) ^ 2) • v with hwHdef
  have hwHker : dotR v wH = 0 := dotR_proj_perp v w
  have hwHspan : wH ∈ Submodule.span ℝ (L : Set (ι → ℝ)) := by
    rw [hwHdef]
    exact Submodule.sub_mem _ (Submodule.subset_span hw) (Submodule.smul_mem _ _ hv.1)
  have hwHmem : wH ∈ Submodule.span ℝ ((secLat v L : Submodule ℤ (ι → ℝ)) : Set (ι → ℝ)) := by
    rw [span_secLat L v w hv hw hvw]
    exact ⟨hwHspan, LinearMap.mem_ker.mpr hwHker⟩
  rw [← hspan] at hwHmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hwHmem
  -- round the coefficients
  set m : Fin R → ℤ := fun j => ⌊c j + 1 / 2⌋ with hmdef
  set y : ι → ℝ := ∑ j, m j • g j with hydef
  have hysec : y ∈ secLat v L := by
    rw [hydef]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hg j)
  have hmclose : ∀ j, |c j - (m j : ℝ)| ≤ 1 / 2 := by
    intro j
    have h1 : (m j : ℝ) ≤ c j + 1 / 2 := by rw [hmdef]; exact Int.floor_le _
    have h2 : c j + 1 / 2 < (m j : ℝ) + 1 := by rw [hmdef]; exact Int.lt_floor_add_one _
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hdiff : wH - y = ∑ j, (c j - (m j : ℝ)) • g j := by
    rw [hydef, ← hc, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sub_smul]
    congr 1
    exact (Int.cast_smul_eq_zsmul ℝ (m j) (g j)).symm
  have hbound : rNorm (wH - y) ≤ (∑ j, rNorm (g j)) / 2 := by
    rw [hdiff]
    have h1 : ∀ j, rNorm ((c j - (m j : ℝ)) • g j) ≤ (1 / 2) * rNorm (g j) := by
      intro j
      rw [rNorm_smul]
      exact mul_le_mul_of_nonneg_right (hmclose j) (rNorm_nonneg (g j))
    calc rNorm (∑ j, (c j - (m j : ℝ)) • g j)
        ≤ ∑ j, rNorm ((c j - (m j : ℝ)) • g j) := rNorm_sum_le _ _
      _ ≤ ∑ j, (1 / 2) * rNorm (g j) := Finset.sum_le_sum fun j _ => h1 j
      _ = (∑ j, rNorm (g j)) / 2 := by
        rw [div_eq_inv_mul, ← Finset.mul_sum]
        ring
  refine ⟨w - y, L.sub_mem hw (secLat_le v L hysec), ?_, ?_⟩
  · have hy0 : dotR v y = 0 := hysec.2
    rw [dotR_sub_right, hy0, sub_zero]
    exact hvw
  · have hperp : dotR (wH - y) v = 0 := by
      rw [dotR_comm, dotR_sub_right, hwHker, hysec.2, sub_zero]
    have hdecomp : w - y = (wH - y) + ((rNorm v) ^ 2)⁻¹ • v := by
      rw [hwHdef, hvw]
      ext i
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
    have h1 : |((rNorm v) ^ 2)⁻¹| * rNorm v = 1 / rNorm v := by
      rw [abs_of_pos (inv_pos.mpr (pow_pos hvn 2))]
      field_simp
    have horth : dotR (wH - y) (((rNorm v) ^ 2)⁻¹ • v) = 0 := by
      rw [dotR_smul_right, hperp, mul_zero]
    rw [hdecomp, rNorm_add_sq_of_orthogonal horth, rNorm_smul, h1]
    have h2 : (1 / rNorm v) ^ 2 = 1 / rNorm v ^ 2 := by rw [div_pow, one_pow]
    rw [h2]
    nlinarith [hbound, rNorm_nonneg (wH - y)]

end Work.HP.Transf
