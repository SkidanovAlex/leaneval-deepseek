import Mathlib
import Submission.Work.ThomBordism.Tower.BaseTheory

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.Tower

open Work.TangentClasses Work.Cohomology

theorem totGlue {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type} (Z : Work.TangentClasses.RealBundle B F ι) (W : ℕ → Set B)
    (hopen : ∀ a, IsOpen (W a)) (hmono : ∀ a b, a ≤ b → W a ⊆ W b) (k : ℕ)
    (f : (n : ℕ) → Work.ThomBordism.TotC Z (W n) k)
    (hf : ∀ a b (hab : a ≤ b),
      Work.Cohomology.rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono (hmono a b hab)) k (f b) = f a) :
    ∃! g : Work.ThomBordism.TotC Z (⋃ n, W n) k,
      ∀ n, Work.Cohomology.rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono (Set.subset_iUnion W n)) k g
        = f n := by
  have hopenV : ∀ n, IsOpen (Z.proj ⁻¹' W n) :=
    fun n => (hopen n).preimage (RealBundle.continuous_proj Z)
  have hmonoV : Monotone (fun n => Z.proj ⁻¹' W n) :=
    fun a b hab => Set.preimage_mono (hmono a b hab)
  have hfV : ∀ a b (hab : a ≤ b),
      rcResLM (Work.Thom.zeroComplement Z) (hmonoV hab) k (f b) = f a := by
    intro a b hab
    exact hf a b hab
  obtain ⟨g0, hg0, huniq⟩ := (rcKern_iUnion_limit (Work.Thom.zeroComplement Z)
    (fun n => Z.proj ⁻¹' W n) hopenV hmonoV k f).mpr hfV
  have hEU : Z.proj ⁻¹' (⋃ n, W n) ⊆ ⋃ n, Z.proj ⁻¹' W n := by
    intro x hx
    rw [Set.mem_preimage] at hx
    rw [Set.mem_iUnion] at hx ⊢
    exact hx
  have hUE : (⋃ n, Z.proj ⁻¹' W n) ⊆ Z.proj ⁻¹' (⋃ n, W n) := by
    intro x hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨n, hn⟩ := hx
    rw [Set.mem_preimage]
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  refine ⟨rcResLM (Work.Thom.zeroComplement Z) hEU k g0, ?_, ?_⟩
  · intro n
    have hcomp := DFunLike.congr_fun (rcResLM_comp (Work.Thom.zeroComplement Z)
      (Set.preimage_mono (Set.subset_iUnion W n)) hEU k) g0
    rw [LinearMap.comp_apply] at hcomp
    rw [hcomp]
    rw [rcResLM_proof_irrel _ (Set.subset_iUnion (fun m => Z.proj ⁻¹' W m) n) k]
    exact hg0 n
  · intro y hy
    have hy' : ∀ n, rcResLM (Work.Thom.zeroComplement Z)
        (Set.subset_iUnion (fun m => Z.proj ⁻¹' W m) n) k
        (rcResLM (Work.Thom.zeroComplement Z) hUE k y) = f n := by
      intro n
      have hcomp := DFunLike.congr_fun (rcResLM_comp (Work.Thom.zeroComplement Z)
        (Set.subset_iUnion (fun m => Z.proj ⁻¹' W m) n) hUE k) y
      rw [LinearMap.comp_apply] at hcomp
      rw [hcomp]
      rw [rcResLM_proof_irrel _ (Set.preimage_mono (Set.subset_iUnion W n)) k]
      exact hy n
    have h1 : rcResLM (Work.Thom.zeroComplement Z) hUE k y = g0 := huniq _ hy'
    have h2 : rcResLM (Work.Thom.zeroComplement Z) hEU k
        (rcResLM (Work.Thom.zeroComplement Z) hUE k y) = y := by
      have hcomp := DFunLike.congr_fun (rcResLM_comp (Work.Thom.zeroComplement Z) hEU hUE k) y
      rw [LinearMap.comp_apply] at hcomp
      rw [hcomp]
      exact rcResLM_self (Work.Thom.zeroComplement Z) (hEU.trans hUE) k y
    rw [← h2, h1]

end Work.ThomBordism.Tower
