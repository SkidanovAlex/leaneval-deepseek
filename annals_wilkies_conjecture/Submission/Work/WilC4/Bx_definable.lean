import Mathlib
import Submission.Work.WilC4.ulpm_BxDefs
import Submission.Work.WilC4.paramBnd_definable

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

variable {k : ℕ}

/-- Pulling a `Definable₁` set of reals back along a single coordinate: the set of tuples whose
`i`-th coordinate lies in a `∅`-definable set of reals is `∅`-definable. -/
lemma definable_coord_mem {n : ℕ} (i : Fin n) {S : Set ℝ}
    (hS : (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc S) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc {p : Fin n → ℝ | p i ∈ S} := by
  have h := hS.preimage_comp (fun _ : Fin 1 => i)
  convert h using 1
  ext p
  simp [Function.comp_apply]

theorem Bx_definable {k : ℕ} (Y : Set (Fin (k + 2) → ℝ))
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) (E : Set ℝ)
    (hMid : (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc (Work.WilC4.Mid E))
    (hSfam : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (Work.WilC4.Sfam Y)) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (Work.WilC4.Bx Y E) := by
  -- the boundary points of the parametrised level sets are `∅`-definable
  have hBnd := paramBnd_definable (n := k + 1) (S := Sfam Y) hSfam
  -- rewrite the parametric fibre `Pfib1 (Sfam Y) p` as the level set `Sfib Y (cOfF p) (mOfF p)`
  have hBnd' : (∅ : Set ℝ).Definable LRc
      {p : Fin (k + 2) → ℝ | WilC2.IsBnd (Sfib Y (cOfF p) (mOfF p)) (p 0)} := by
    convert hBnd using 1
    ext p
    simp only [Set.mem_ofPred_eq]
    rw [Pfib1_Sfam]
  -- the condition `mOfF p ∈ Mid E` on the last coordinate
  have hMidD : (∅ : Set ℝ).Definable LRc {p : Fin (k + 2) → ℝ | mOfF p ∈ Mid E} := by
    have h := definable_coord_mem (Fin.last (k + 1)) hMid
    convert h using 1
    ext p
    simp [mOfF]
  -- the parametrised crossing set is `∅`-definable
  have hCross : (∅ : Set ℝ).Definable LRc (CrossSet Y E) := by
    rw [CrossSet]
    exact hBnd'.inter hMidD
  -- project the value `m` away along the reindexing `e2f`
  have hPre : (∅ : Set ℝ).Definable LRc
      ((fun g : (Fin (k + 1) ⊕ Fin 1) → ℝ => g ∘ e2f k) ⁻¹' CrossSet Y E) :=
    hCross.preimage_comp (e2f k)
  have hProj := hPre.exists_of_finite (α := Fin (k + 1)) (β := Fin 1)
  -- and `Bx` is that projection
  rw [Bx_eq_BxProj Y E]
  exact hProj

end Work.WilC4
