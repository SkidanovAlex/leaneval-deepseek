import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Transf.Basic
import Submission.Work.HP.Transf.PieceRankDrop

/-!
# Lower bound for the section lattice's dual

If `v ∈ dualLat L` is a shortest dual vector up to a factor `3/2`, `⟪v,w⟫ = 1` with `w ∈ L`,
and `dualLat (L ∩ v^⊥)` is nonzero, then its first successive minimum is at least `μ/4`,
where `μ = λ₁(dualLat L)`.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP.Transf

variable {ι : Type*} [Fintype ι]

theorem lamR_dual_section (L : Submodule ℤ (ι → ℝ)) (v w : ι → ℝ)
    (hv : v ∈ dualLat L) (hv0 : v ≠ 0) (hw : w ∈ L) (hvw : dotR v w = 1) (μ : ℝ)
    (hμ : lamR (dualLat L) 1 = μ) (hb : rNorm v ≤ 3 / 2 * μ)
    (hne : ∃ u ∈ dualLat (secLat v L), u ≠ 0) :
    μ / 4 ≤ lamR (dualLat (secLat v L)) 1 := by
  classical
  -- every nonzero element of the section's dual has norm at least `μ/4`
  have hmain : ∀ u ∈ dualLat (secLat v L), u ≠ 0 → μ / 4 ≤ rNorm u := by
    intro u hu hu0
    -- nearest integer to `⟪u,w⟫`
    set k₀ : ℤ := ⌊dotR u w + 1 / 2⌋ with hk0
    set t : ℝ := (k₀ : ℝ) - dotR u w with ht
    have ht_le : |t| ≤ 1 / 2 := by
      have h1 : (k₀ : ℝ) ≤ dotR u w + 1 / 2 := by rw [hk0]; exact Int.floor_le _
      have h2 : dotR u w + 1 / 2 < (k₀ : ℝ) + 1 := by rw [hk0]; exact Int.lt_floor_add_one _
      rw [abs_le]
      exact ⟨by rw [ht]; linarith, by rw [ht]; linarith⟩
    -- `z = u + t • v ∈ dualLat L`
    have hz : u + t • v ∈ dualLat L := by
      refine ⟨?_, ?_⟩
      · exact Submodule.add_mem _
          (Submodule.span_mono (secLat_le v L) hu.1) (Submodule.smul_mem _ t hv.1)
      · intro y hy
        obtain ⟨m, hm⟩ := hv.2 y hy
        have hm' : dotR v y = (m : ℝ) := hm
        -- `y = (y - m • w) + m • w`
        have hy0 : y - m • w ∈ secLat v L := by
          refine ⟨L.sub_mem hy (L.smul_mem m hw), ?_⟩
          rw [dotR_sub_right, dotR_zsmul_right, hm', hvw]
          ring
        obtain ⟨c, hc⟩ := hu.2 (y - m • w) hy0
        have hc' : dotR u (y - m • w) = (c : ℝ) := hc
        have hydecomp : y = (y - m • w) + m • w := by
          rw [sub_add_cancel]
        have hpair : dotR (u + t • v) y = (c : ℝ) + (m : ℝ) * (k₀ : ℝ) := by
          have h1 : dotR (u + t • v) y = dotR u y + t * dotR v y := by
            rw [dotR_add_left, dotR_smul_left]
          have h2 : dotR u y = dotR u (y - m • w) + (m : ℝ) * dotR u w := by
            conv_lhs => rw [hydecomp]
            rw [dotR_add_right, dotR_zsmul_right]
          rw [h1, h2, hc', hm', ht]
          ring
        refine ⟨c + m * k₀, ?_⟩
        change dotR (u + t • v) y = ((c + m * k₀ : ℤ) : ℝ)
        rw [hpair]
        push_cast
        ring
    have hz0 : u + t • v ≠ 0 := by
      intro hzero
      have hu_ker : dotR v u = 0 := by
        have hspanle : Submodule.span ℝ ((secLat v L : Submodule ℤ (ι → ℝ)) : Set (ι → ℝ))
            ≤ (dotRL v).ker := by
          rw [Submodule.span_le]
          intro y hy
          exact LinearMap.mem_ker.mpr hy.2
        exact hspanle hu.1
      have hv0' : dotR v u = 0 := hu_ker
      have hueq : u = -(t • v) := by
        rw [eq_neg_iff_add_eq_zero]
        exact hzero
      have : dotR v u = -(t * rNorm v ^ 2) := by
        rw [hueq, dotR_neg_right, dotR_smul_right, ← rNorm_sq]
      rw [hv0'] at this
      have hrne : rNorm v ≠ 0 := fun h => hv0 (rNorm_eq_zero_iff.mp h)
      have ht0 : t = 0 := by
        have h2 := this.symm
        have : t * rNorm v ^ 2 = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_right (pow_ne_zero 2 hrne)
      rw [ht0, zero_smul, add_zero] at hzero
      exact hu0 hzero
    have hle : μ ≤ rNorm (u + t • v) := by
      rw [← hμ]
      exact lamR_le_rNorm _ hz hz0
    have htri : rNorm (u + t • v) ≤ rNorm u + |t| * rNorm v := by
      refine (rNorm_triangle u (t • v)).trans_eq ?_
      rw [rNorm_smul]
    have hvn : 0 ≤ rNorm v := rNorm_nonneg v
    have : rNorm u ≥ μ - (1 / 2) * (3 / 2 * μ) := by
      have h2 : |t| * rNorm v ≤ (1 / 2) * (3 / 2 * μ) := by
        calc |t| * rNorm v ≤ (1 / 2) * rNorm v := by
              exact mul_le_mul_of_nonneg_right ht_le hvn
          _ ≤ (1 / 2) * (3 / 2 * μ) := mul_le_mul_of_nonneg_left hb (by norm_num)
      linarith
    linarith
  -- the infimum bound
  rw [lamR]
  refine le_csInf ?_ ?_
  · obtain ⟨u, hu, hu0⟩ := hne
    exact ⟨rNorm u, rNorm_nonneg u, fun _ : Fin 1 => u, fun _ => hu,
      by rw [linearIndependent_unique_iff]; exact hu0, fun _ => le_rfl⟩
  · rintro r ⟨-, f, hfL, hfI, hfr⟩
    exact (hmain (f 0) (hfL 0) (hfI.ne_zero 0)).trans (hfr 0)

end Work.HP.Transf
