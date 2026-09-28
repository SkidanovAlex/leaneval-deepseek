import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Transf.Basic

/-!
# Rank drop by the section `L ∩ v^⊥`

If `v` is a dual vector of the lattice `L` and `w ∈ L` has `⟨v,w⟩ = 1` (so `⟨v,·⟩ : L → ℤ` is
surjective), then the section `L ∩ v^⊥` has real rank exactly one less than that of `L`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.FM3

open Work.HP Work.HP.Transf

variable {ι : Type*} [Fintype ι]

theorem rank_secLat_add_one (L : Submodule ℤ (ι → ℝ)) (v w : ι → ℝ)
    (hv : v ∈ dualLat L) (hw : w ∈ L) (hwv : dotR v w = 1) :
    rkR (secLat v L) + 1 = rkR L := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h, dotR_zero_right] at hwv; exact one_ne_zero hwv.symm
  have hφw : dotRL v w = 1 := by rw [dotRL_apply]; exact hwv
  have hφker : ∀ y ∈ secLat v L, dotRL v y = 0 := by
    intro y hy; rw [dotRL_apply]; exact hy.2
  have hSle : Submodule.span ℝ (secLat v L : Set (ι → ℝ))
      ≤ Submodule.span ℝ (L : Set (ι → ℝ)) :=
    Submodule.span_mono fun y hy => hy.1
  have hSker : Submodule.span ℝ (secLat v L : Set (ι → ℝ)) ≤ LinearMap.ker (dotRL v) :=
    Submodule.span_le.mpr hφker
  have hsup : Submodule.span ℝ (secLat v L : Set (ι → ℝ)) ⊔ Submodule.span ℝ ({w} : Set (ι → ℝ))
      = Submodule.span ℝ (L : Set (ι → ℝ)) := by
    refine le_antisymm (sup_le hSle ?_) ?_
    · rw [Submodule.span_le]
      rintro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact Submodule.subset_span hw
    · rw [Submodule.span_le]
      intro z hz
      obtain ⟨k, hk⟩ := hv.2 z hz
      have hmem : z - k • w ∈ secLat v L := by
        refine ⟨Submodule.sub_mem _ hz (Submodule.smul_mem _ _ hw), ?_⟩
        show dotR v (z - k • w) = 0
        rw [← Int.cast_smul_eq_zsmul ℝ k w, dotR_sub_right, dotR_smul_right, hwv, mul_one]
        rw [show dotR v z = (k : ℝ) from hk, sub_self]
      have h2 : z - k • w ∈ Submodule.span ℝ (secLat v L : Set (ι → ℝ)) := Submodule.subset_span hmem
      have h3 : k • w ∈ Submodule.span ℝ ({w} : Set (ι → ℝ)) := by
        rw [Submodule.mem_span_singleton]
        exact ⟨(k : ℝ), Int.cast_smul_eq_zsmul ℝ k w⟩
      have h4 : (z - k • w) + (k • w + 0) ∈ Submodule.span ℝ (secLat v L : Set (ι → ℝ))
          ⊔ Submodule.span ℝ ({w} : Set (ι → ℝ)) :=
        Submodule.add_mem _
          (Submodule.mem_sup_left h2)
          (Submodule.add_mem _ (Submodule.mem_sup_right h3) (Submodule.zero_mem _))
      rwa [add_zero, sub_add_cancel] at h4
  have hdisj : Submodule.span ℝ (secLat v L : Set (ι → ℝ)) ⊓ Submodule.span ℝ ({w} : Set (ι → ℝ))
      = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [Submodule.mem_span_singleton] at hx2
    obtain ⟨c, hc⟩ := hx2
    have h1 : dotRL v x = 0 := LinearMap.mem_ker.mp (hSker hx1)
    rw [← hc, map_smul, hφw, smul_eq_mul, mul_one] at h1
    rw [← hc, h1, zero_smul]
  have hfin : Module.finrank ℝ ↥(Submodule.span ℝ (secLat v L : Set (ι → ℝ))) + 1
      = Module.finrank ℝ ↥(Submodule.span ℝ (L : Set (ι → ℝ))) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (Submodule.span ℝ (secLat v L : Set (ι → ℝ))) (Submodule.span ℝ ({w} : Set (ι → ℝ)))
    rw [hsup, hdisj, finrank_span_singleton hw0] at h
    simpa using h.symm
  exact hfin

end Work.HP.FM3
