import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7A.Est1.Defs
import Submission.Work.BoseB7A.PH_subset_PHq_sub
import Submission.Work.BoseB7A.Prep
import Submission.Work.BoseB7A.kernel_basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB7A.Est1

open Work.BoseB7

set_option maxHeartbeats 1000000

theorem OpZ_cD_bd (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
        (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Work.BoseB7A.Q3Kernel K₀ F T E →
        ∀ (s k : Mode), E.fL s ≠ 0 → k ∈ F.PHset E →
          (Work.BoseB7A.Est1.cD E k)⁻¹ * E.W1 k ^ 2 ≤ 2048 * K₀ ^ 2 * E.KH ^ 4 * E.aScat ^ 6 * E.D (s - k) := by
  obtain ⟨t₁, ht₁, hkb⟩ := Work.BoseB7A.kernel_basic K₀ b₀ hb₀
  refine ⟨min ((1 / 4 : ℝ) ^ 24) (min t₁ ((1 / 2 : ℝ) ^ (646 / 97 : ℝ))),
    lt_min (by norm_num) (lt_min ht₁ (Real.rpow_pos_of_pos (by norm_num) _)), ?_⟩
  intro Mode _ _ _ F T E hv htle hb hK s k hfL hk
  -- diluteness facts
  have hKH : 0 < E.KH := Work.BoseB7A.KH_pos E hv
  have ha : 0 < E.aScat := hv.a_pos
  have hKa : 0 < E.KH * E.aScat := mul_pos hKH ha
  have ht_A : hv.t ≤ (1 / 4 : ℝ) ^ 24 := le_trans htle (min_le_left _ _)
  have ht_B : hv.t ≤ (1 / 2 : ℝ) ^ (646 / 97 : ℝ) :=
    le_trans htle (le_trans (min_le_right _ _) (min_le_right _ _))
  have ht_t₁ : hv.t ≤ t₁ := le_trans htle (le_trans (min_le_right _ _) (min_le_left _ _))
  -- `𝓁 ≤ 1/2`, hence `1 - 𝓁² ≥ 1/2`
  have hlille : E.lille = hv.t ^ (97 / 646 : ℝ) := by
    rw [Work.BoseB7.lille_val E hv]
    simp only [Work.BoseBox.fsXp]
    congr 1
    norm_num
  have hlille_pos : 0 < E.lille := Work.BoseB7A.lille_pos E hv
  have hlille_le : E.lille ≤ 1 / 2 := by
    rw [hlille]
    have h2 : ((1 / 2 : ℝ) ^ (646 / 97 : ℝ)) ^ (97 / 646 : ℝ) = 1 / 2 := by
      rw [(Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2) (646 / 97) (97 / 646)).symm]
      rw [show (646 / 97 : ℝ) * (97 / 646) = 1 by norm_num, Real.rpow_one]
    rw [← h2]
    exact Real.rpow_le_rpow hv.t_pos.le ht_B (by norm_num)
  have hone : 1 / 2 ≤ 1 - E.lille ^ 2 := by
    have h := pow_le_pow_left₀ hlille_pos.le hlille_le 2
    linarith
  -- the two regions
  have hPHk : F.PH E.KH E.aScat k := (Finset.mem_filter.mp hk).2
  have hPHqk : F.PHq E.KH E.aScat k := Work.BoseB7A.PH_subset_PHq F E hv k hPHk
  have hsmall := Work.BoseB7A.ratio_small E hv ht_A
  have hPHqsub : F.PHq E.KH E.aScat (s - k) :=
    Work.BoseB7A.sub_mem_PHq F E hv hsmall hK.kmom_sub hK.fL_supp hfL hk
  -- the kinetic lower bounds of `kernel_basic`
  have hkb' := hkb F T E hv ht_t₁ hb hK
  have hDk : ‖F.kmom k‖ ^ 2 / 4 ≤ E.D k := hkb'.2.2.2.2 k hPHqk
  have hDsub : ‖F.kmom (s - k)‖ ^ 2 / 4 ≤ E.D (s - k) := hkb'.2.2.2.2 (s - k) hPHqsub
  have hkcut : 1 / (2 * E.KH * E.aScat) ≤ ‖F.kmom k‖ := hPHk
  have hsubcut : 1 / (4 * E.KH * E.aScat) ≤ ‖F.kmom (s - k)‖ := hPHqsub
  -- **left**: `𝒟_k ≥ 1/(16K_H²a²)`
  have hDk_lb : 1 / (16 * E.KH ^ 2 * E.aScat ^ 2) ≤ E.D k := by
    have hsq : (1 / (2 * E.KH * E.aScat)) ^ 2 ≤ ‖F.kmom k‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hkcut 2
    have hkey : (1 / (2 * E.KH * E.aScat)) ^ 2 / 4 = 1 / (16 * E.KH ^ 2 * E.aScat ^ 2) := by
      field_simp
      ring
    rw [← hkey]
    linarith
  have hcD_lb : 1 / (32 * E.KH ^ 2 * E.aScat ^ 2) ≤ cD E k := by
    rw [cD]
    have hmul : (1 / 2) * (1 / (16 * E.KH ^ 2 * E.aScat ^ 2))
        ≤ (1 - E.lille ^ 2) * (E.D k) :=
      mul_le_mul hone hDk_lb (by positivity) (by linarith)
    have hkey : (1 / 2) * (1 / (16 * E.KH ^ 2 * E.aScat ^ 2))
        = 1 / (32 * E.KH ^ 2 * E.aScat ^ 2) := by
      field_simp
      ring
    linarith [hmul, hkey]
  have hcD_pos : 0 < cD E k :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / (32 * E.KH ^ 2 * E.aScat ^ 2)) hcD_lb
  have hcD_inv : (cD E k)⁻¹ ≤ 32 * E.KH ^ 2 * E.aScat ^ 2 := by
    have hm_pos : 0 < 1 / (32 * E.KH ^ 2 * E.aScat ^ 2) := by positivity
    have h : (cD E k)⁻¹ ≤ (1 / (32 * E.KH ^ 2 * E.aScat ^ 2))⁻¹ :=
      (inv_le_inv₀ hcD_pos hm_pos).mpr hcD_lb
    have hkey : (1 / (32 * E.KH ^ 2 * E.aScat ^ 2))⁻¹ = 32 * E.KH ^ 2 * E.aScat ^ 2 := by
      field_simp
    rw [hkey] at h
    exact h
  have hW1 : E.W1 k ^ 2 ≤ (K₀ * E.aScat) ^ 2 := by
    rw [sq_le_sq]
    exact le_trans (hK.W1_le k) (le_abs_self _)
  -- **right**: `𝒟_{s-k} ≥ 1/(64K_H²a²)`
  have hDsub_lb : 1 / (64 * E.KH ^ 2 * E.aScat ^ 2) ≤ E.D (s - k) := by
    have hsq : (1 / (4 * E.KH * E.aScat)) ^ 2 ≤ ‖F.kmom (s - k)‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hsubcut 2
    have hkey : (1 / (4 * E.KH * E.aScat)) ^ 2 / 4 = 1 / (64 * E.KH ^ 2 * E.aScat ^ 2) := by
      field_simp
      ring
    rw [← hkey]
    linarith
  -- assemble
  have hLHS : (cD E k)⁻¹ * E.W1 k ^ 2 ≤ 32 * K₀ ^ 2 * E.KH ^ 2 * E.aScat ^ 4 := by
    have h1 : (cD E k)⁻¹ * E.W1 k ^ 2
        ≤ (32 * E.KH ^ 2 * E.aScat ^ 2) * (K₀ * E.aScat) ^ 2 :=
      mul_le_mul hcD_inv hW1 (sq_nonneg _) (by positivity)
    have h2 : (32 * E.KH ^ 2 * E.aScat ^ 2) * (K₀ * E.aScat) ^ 2
        = 32 * K₀ ^ 2 * E.KH ^ 2 * E.aScat ^ 4 := by ring
    linarith [h1, h2]
  have hRHS : 32 * K₀ ^ 2 * E.KH ^ 2 * E.aScat ^ 4
      ≤ 2048 * K₀ ^ 2 * E.KH ^ 4 * E.aScat ^ 6 * E.D (s - k) := by
    have hnn : (0 : ℝ) ≤ 2048 * K₀ ^ 2 * E.KH ^ 4 * E.aScat ^ 6 := by positivity
    have h := mul_le_mul_of_nonneg_left hDsub_lb hnn
    have hkey : 2048 * K₀ ^ 2 * E.KH ^ 4 * E.aScat ^ 6
          * (1 / (64 * E.KH ^ 2 * E.aScat ^ 2))
        = 32 * K₀ ^ 2 * E.KH ^ 2 * E.aScat ^ 4 := by
      field_simp
      ring
    linarith [h, hkey]
  linarith [hLHS, hRHS]

end Work.BoseB7A.Est1
