import Mathlib
import Submission.Work.EKLNonExc.Defs
import Submission.Work.EKLContract.Lemmas.Gamma3Facts
import Submission.Work.EKLContract.Lemmas.isClosed_Thick
import Submission.Work.EKLContract.Lemmas.V_open_one
import Submission.Work.EKLContract.Lemmas.mkX_mul

/-!
# Auxiliary facts for `DinjFacts`

Small, reusable lemmas about the quotient `X₃ = SL₃(ℝ)/Γ₃`, the boxes `V δ`/`clBox δ`, and the
discreteness of `Γ₃`, used in the proof that `Dinj δ` is closed and exhausts compacta.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Work.EKLNonExc
namespace DinjAux

open Work.EKLContract Filter Topology

noncomputable section

/-- The ambient space of `3 × 3` real matrices. -/
abbrev M3 := Matrix (Fin 3) (Fin 3) ℝ

/-- `mkX a = mkX b` iff `a⁻¹ b ∈ Γ₃`. -/
lemma mkX_eq_iff (a b : SL3) : mkX a = mkX b ↔ a⁻¹ * b ∈ Γ3 := QuotientGroup.eq

/-- `g • mkX k = h • mkX k` iff `k⁻¹ g⁻¹ h k ∈ Γ₃`. -/
lemma smul_mkX_eq_iff (g h k : SL3) : g • mkX k = h • mkX k ↔ k⁻¹ * g⁻¹ * h * k ∈ Γ3 := by
  rw [← Work.EKLContract.Lemmas.mkX_mul g k, ← Work.EKLContract.Lemmas.mkX_mul h k, mkX_eq_iff]
  constructor
  · intro hh
    have hc : (g * k)⁻¹ * (h * k) = k⁻¹ * g⁻¹ * h * k := by group
    rwa [hc] at hh
  · intro hh
    have hc : (g * k)⁻¹ * (h * k) = k⁻¹ * g⁻¹ * h * k := by group
    rwa [hc]

/-- The identity has a neighbourhood meeting `Γ₃` only in `1`. -/
lemma exists_nhds_inter_Γ3 :
    ∃ B : Set SL3, B ∈ 𝓝 (1 : SL3) ∧ B ∩ (Γ3 : Set SL3) = {1} := by
  have hd : IsDiscrete (Γ3 : Set SL3) :=
    isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ3)
  exact nhds_inter_eq_singleton_of_mem_discrete hd Γ3.one_mem

/-- The closed entrywise box in the matrix space. -/
def boxM (δ : ℝ) : Set M3 :=
  Set.univ.pi (fun i : Fin 3 => Set.univ.pi (fun j : Fin 3 =>
    Set.Icc ((1 : M3) i j - δ) ((1 : M3) i j + δ)))

lemma boxM_compact (δ : ℝ) : IsCompact (boxM δ) :=
  isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))

lemma boxM_closed (δ : ℝ) : IsClosed (boxM δ) := by
  rw [boxM]
  exact isClosed_set_pi (fun _ _ => isClosed_set_pi (fun _ _ => isClosed_Icc))

lemma mem_boxM (A : M3) (δ : ℝ) :
    A ∈ boxM δ ↔ ∀ i j, |A i j - (1 : M3) i j| ≤ δ := by
  rw [boxM]
  constructor
  · intro h i j
    have hij := (Set.mem_univ_pi.mp (Set.mem_univ_pi.mp h i)) j
    rw [Set.mem_Icc] at hij
    rw [abs_le]
    exact ⟨by linarith [hij.1], by linarith [hij.2]⟩
  · intro h
    refine Set.mem_univ_pi.mpr (fun i => ?_)
    refine Set.mem_univ_pi.mpr (fun j => ?_)
    rw [Set.mem_Icc]
    have hij := h i j
    rw [abs_le] at hij
    exact ⟨by linarith [hij.1], by linarith [hij.2]⟩

lemma clBox_eq_preimage (δ : ℝ) :
    clBox δ = (Subtype.val : SL3 → M3) ⁻¹' boxM δ := by
  ext g
  show (∀ i j, |g i j - (1 : M3) i j| ≤ δ) ↔ (↑g : M3) ∈ boxM δ
  rw [mem_boxM]

lemma isClosed_range_val : IsClosed (Set.range (Subtype.val : SL3 → M3)) :=
  (IsClosedEmbedding.subtypeVal (p := fun A : M3 => A.det = 1)
    (isClosed_singleton.preimage (continuous_id.matrix_det))).isClosed_range

/-- The closed box `clBox δ` is compact. -/
lemma clBox_compact (δ : ℝ) : IsCompact (clBox δ) := by
  have he : IsEmbedding (Subtype.val : SL3 → M3) := ⟨⟨rfl⟩, Subtype.coe_injective⟩
  have himg : (Subtype.val : SL3 → M3) '' clBox δ =
      boxM δ ∩ Set.range (Subtype.val : SL3 → M3) := by
    rw [clBox_eq_preimage]
    ext A
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨hg, Set.mem_range_self g⟩
    · rintro ⟨hbox, g, rfl⟩
      exact ⟨g, hbox, rfl⟩
  have h2 : IsCompact (boxM δ ∩ Set.range (Subtype.val : SL3 → M3)) :=
    (boxM_compact δ).of_isClosed_subset ((boxM_closed δ).inter isClosed_range_val)
      Set.inter_subset_left
  refine (he.isCompact_iff (s := clBox δ)).mpr ?_
  exact himg.symm ▸ h2

lemma V_subset_clBox {δ : ℝ} : V δ ⊆ clBox δ := fun _ hg _ _ => le_of_lt (hg _ _)

end

end DinjAux
end Work.EKLNonExc
