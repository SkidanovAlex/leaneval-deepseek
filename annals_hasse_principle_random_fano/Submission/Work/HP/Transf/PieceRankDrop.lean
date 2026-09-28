import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Transf.Basic

/-!
# The section lattice and its rank

For `v ∈ dualLat L`, `w ∈ L` with `⟪v,w⟫ = 1`, the section lattice `secLat v L = L ∩ v^⊥`
has real span `span ℝ L ⊓ v^⊥` and rank one less than that of `L`.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP.Transf

variable {ι : Type*} [Fintype ι]

theorem span_secLat (L : Submodule ℤ (ι → ℝ)) (v w : ι → ℝ)
    (hv : v ∈ dualLat L) (hw : w ∈ L) (hvw : dotR v w = 1) :
    Submodule.span ℝ ((secLat v L : Submodule ℤ (ι → ℝ)) : Set (ι → ℝ))
      = Submodule.span ℝ (L : Set (ι → ℝ)) ⊓ (dotRL v).ker := by
  refine le_antisymm ?_ ?_
  · refine le_inf (Submodule.span_mono ?_) ?_
    · intro y hy; exact hy.1
    · rw [Submodule.span_le]
      intro y hy
      exact LinearMap.mem_ker.mpr hy.2
  · intro x ⟨hxL, hxker⟩
    have hΨ : ∀ y ∈ Submodule.span ℝ (L : Set (ι → ℝ)),
        y - (dotR v y) • w ∈
          Submodule.span ℝ ((secLat v L : Submodule ℤ (ι → ℝ)) : Set (ι → ℝ)) := by
      intro y hy
      refine Submodule.span_induction
        (p := fun y _ => y - (dotR v y) • w ∈
          Submodule.span ℝ ((secLat v L : Submodule ℤ (ι → ℝ)) : Set (ι → ℝ))) ?_ ?_ ?_ ?_ hy
      · intro y hyL
        obtain ⟨k, hk⟩ := hv.2 y hyL
        have hk' : dotR v y = (k : ℝ) := hk
        have hcast : ((k : ℝ) • w : ι → ℝ) = k • w := Int.cast_smul_eq_zsmul ℝ k w
        rw [hk', hcast]
        refine Submodule.subset_span ?_
        refine ⟨L.sub_mem hyL (L.smul_mem k hw), ?_⟩
        rw [dotR_sub_right, dotR_zsmul_right, hk', hvw]
        ring
      · simp
      · intro a b _ _ ha hb
        have : (a + b) - (dotR v (a + b)) • w
            = (a - (dotR v a) • w) + (b - (dotR v b) • w) := by
          rw [dotR_add_right, add_smul]
          abel
        rw [this]
        exact Submodule.add_mem _ ha hb
      · intro c a _ ha
        have : (c • a) - (dotR v (c • a)) • w = c • (a - (dotR v a) • w) := by
          simp only [dotR_smul_right, smul_sub, smul_smul]
        rw [this]
        exact Submodule.smul_mem _ c ha
    have hx0 : dotR v x = 0 := hxker
    have hxeq : x = x - (dotR v x) • w := by rw [hx0]; simp
    rw [hxeq]
    exact hΨ x hxL

theorem finrank_span_secLat (L : Submodule ℤ (ι → ℝ)) (v w : ι → ℝ)
    (hv : v ∈ dualLat L) (hw : w ∈ L) (hvw : dotR v w = 1) :
    Module.finrank ℝ (Submodule.span ℝ ((secLat v L : Submodule ℤ (ι → ℝ)) : Set (ι → ℝ))) + 1
      = Module.finrank ℝ (Submodule.span ℝ (L : Set (ι → ℝ))) := by
  rw [span_secLat L v w hv hw hvw]
  have hvne : v ≠ 0 := by
    intro h
    rw [h] at hvw
    simpa [dotR] using hvw
  -- `dotRL v` is surjective
  have hrange : (dotRL v).range = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro c
    refine ⟨c • w, ?_⟩
    simp only [dotRL_apply]
    have h1 : (∑ i, v i * (c • w) i) = c * ∑ i, v i * w i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply]; ring
    rw [h1, show (∑ i, v i * w i) = 1 from hvw]
    ring
  have hkerrank : Module.finrank ℝ (dotRL v).ker + 1 = Module.finrank ℝ (ι → ℝ) := by
    have h := LinearMap.finrank_range_add_finrank_ker (dotRL v)
    rw [hrange] at h
    rw [finrank_top, Module.finrank_self] at h
    omega
  -- `span ℝ L ⊔ ker = ⊤`
  have hwl : w ∈ Submodule.span ℝ (L : Set (ι → ℝ)) := Submodule.subset_span hw
  have hsup : Submodule.span ℝ (L : Set (ι → ℝ)) ⊔ (dotRL v).ker = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    have hmem : x - (dotRL v x) • w ∈ (dotRL v).ker := by
      rw [LinearMap.mem_ker, LinearMap.map_sub, LinearMap.map_smul, dotRL_eq_dotR]
      rw [show dotRL v w = dotR v w from rfl, hvw]
      ring
    have hx : x = (x - (dotRL v x) • w) + (dotRL v x) • w := by abel
    rw [hx]
    exact Submodule.add_mem _ (Submodule.mem_sup_right hmem)
      (Submodule.mem_sup_left (Submodule.smul_mem _ _ hwl))
  have hform := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span ℝ (L : Set (ι → ℝ))) (dotRL v).ker
  rw [hsup] at hform
  rw [finrank_top] at hform
  omega

end Work.HP.Transf
