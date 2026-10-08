import Mathlib
import Submission.Work.Models.PSL2.Defs
import Submission.Work.Models.PSL2.U_facts
import Submission.Work.Models.PSL2.B_facts
import Submission.Work.Models.PSL2.bruhat
import Submission.Work.Models.PSL2.w_facts

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Models.PSL2.normalizer_U`

The normalizer in `SL(2,F)` (`F` a field of characteristic `2`) of the unipotent radical
`U = { 1 + b E₀₁ | b ∈ F }` of the standard Borel is the standard Borel `B` (the upper
triangular matrices):

`N_{SL(2,F)}(U) = B`.

Both inclusions are proved.

* `B ≤ N(U)`: conjugation by an upper triangular matrix `g` sends the transvection
  `1 + t E₀₁ = unip t` to `unip (g₀₀² t)` (this is the explicit computation
  `Work.Models.PSL2.conj_unip_of_mem_B`); since `B` is a subgroup and `g⁻¹ ∈ B`, this
  gives both directions of the normalizer condition.

* `N(U) ≤ B`: if `g ∉ B`, the Bruhat decomposition (`Work.Models.PSL2.bruhat`) writes
  `g = b₁ w b₂` with `b₁, b₂ ∈ B`, so `w = b₁⁻¹ g b₂⁻¹` lies in `N(U)` as well. But `w`
  conjugates `unip 1` to the lower unipotent matrix `!![1,0;1,1]`, which is not in `U`
  (`Work.Models.PSL2.w_conj_unip_one_notin_U`); contradiction.

Characteristic `2` is used for `-x = x` (so that the inverse of `!![a,b;0,d]` is
`!![d,b;0,a]`) and for `x + x = 0` (in the cancellation of the two equal `g₀₀ g₀₁` terms).
-/

namespace Work.Models.PSL2

open Matrix

variable {F : Type*} [Field F] [CharP F 2]

/-- Conjugation of the transvection `unip t = 1 + t E₀₁` by an upper triangular matrix `g`
in `SL(2,F)`, `F` of characteristic `2`: the result is again a transvection, namely
`unip (g₀₀² t)`.

Indeed for `g = !![a,b;0,d]` (so `a d = 1` and `g⁻¹ = !![d,b;0,a]` in characteristic `2`)
the triple product is `!![1, a b + (a t + b) a; 0, 1]`, and `a b + (a t + b) a = a² t`
because the two `a b` terms cancel. -/
lemma conj_unip_of_mem_B {g : SL2 F} (hg : g ∈ B (F := F)) (t : F) :
    g * unip t * g⁻¹ = unip (((g : Matrix (Fin 2) (Fin 2) F) 0 0) ^ 2 * t) := by
  have h10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hg
  -- the determinant condition reads `a * d = 1` for an upper triangular matrix
  have hdet : (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    have h := g.2
    rw [Matrix.det_fin_two] at h
    rwa [h10, mul_zero, sub_zero] at h
  have hdet' : (g : Matrix (Fin 2) (Fin 2) F) 1 1 * (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    rw [mul_comm]; exact hdet
  -- the explicit inverse of an upper triangular matrix in characteristic `2`
  have hinv : ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
      !![(g : Matrix (Fin 2) (Fin 2) F) 1 1, (g : Matrix (Fin 2) (Fin 2) F) 0 1;
         0, (g : Matrix (Fin 2) (Fin 2) F) 0 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h10, CharTwo.neg_eq]
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, hinv, unip_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, hdet, hdet', pow_two,
      CharTwo.add_self_eq_zero]
  -- the only surviving entry is `a b + (a t + b) a`, which equals `a² t` by char. 2
  ring_nf
  rw [mul_two, CharTwo.add_self_eq_zero, zero_add]

/-- The Weyl element `w = !![0,1;1,0]` does not normalize `U`: it conjugates `unip 1` to the
lower unipotent matrix `!![1,0;1,1]`, whose `(1,0)`-entry is `1 ≠ 0`, while every element of
`U` has vanishing `(1,0)`-entry. -/
lemma w_conj_unip_one_notin_U :
    w (F := F) * unip 1 * (w (F := F))⁻¹ ∉ U (F := F) := by
  intro h
  rw [mem_U_iff] at h
  obtain ⟨s, hs⟩ := h
  have hwinv : (w (F := F))⁻¹ = w (F := F) := inv_eq_of_mul_eq_one_right (w_invol (F := F))
  have hcoe : ((w (F := F) * unip 1 * (w (F := F))⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F)
      = !![1, 0; 1, 1] := by
    simp [Matrix.SpecialLinearGroup.coe_mul, w_coe, unip_coe, hwinv]
  -- compare the `(1,0)`-entries of the two sides of `w * unip 1 * w⁻¹ = unip s`
  have h10 := congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F) 1 0) hs
  rw [hcoe, unip_coe] at h10
  simp at h10

theorem normalizer_U {F : Type*} [Field F] [CharP F 2] :
    Subgroup.normalizer
        ((Work.Models.PSL2.U (F := F) : Subgroup (Work.Models.SL2 F)) : Set (Work.Models.SL2 F))
      = Work.Models.PSL2.B (F := F) := by
  set N : Subgroup (SL2 F) :=
    Subgroup.normalizer ((U (F := F) : Subgroup (SL2 F)) : Set (SL2 F)) with hN
  -- `B` normalizes `U`: conjugation by `g ∈ B` maps `unip t` to `unip (g₀₀² t)`, and the
  -- same holds for `g⁻¹ ∈ B`, which gives both implications of the normalizer condition.
  have hB_le : B (F := F) ≤ N := by
    intro g hg
    rw [hN, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨_, conj_unip_of_mem_B hg t⟩
    · intro hh
      have heq : h = g⁻¹ * (g * h * g⁻¹) * g := by group
      rw [heq]
      obtain ⟨t, ht⟩ := hh
      rw [ht]
      exact ⟨_, by simpa using conj_unip_of_mem_B (B.inv_mem hg) t⟩
  refine le_antisymm ?_ hB_le
  -- an element outside `B` does not normalize `U`, because the Bruhat decomposition would
  -- then exhibit the Weyl element `w` in `N(U)`, which is impossible.
  intro g hg
  by_contra hgB
  have hwN : w (F := F) ∈ N := by
    rcases bruhat (F := F) g with hg1 | ⟨b₁, hb₁, b₂, hb₂, hge⟩
    · exact absurd hg1 hgB
    · have hw : w (F := F) = b₁⁻¹ * g * b₂⁻¹ := by rw [hge]; group
      rw [hw]
      exact N.mul_mem (N.mul_mem (N.inv_mem (hB_le hb₁)) hg) (N.inv_mem (hB_le hb₂))
  rw [hN] at hwN
  have hwU : w (F := F) * unip 1 * (w (F := F))⁻¹ ∈ U (F := F) :=
    ((Subgroup.mem_normalizer_iff.mp hwN) (unip 1)).mp ⟨1, rfl⟩
  exact w_conj_unip_one_notin_U hwU

end Work.Models.PSL2
