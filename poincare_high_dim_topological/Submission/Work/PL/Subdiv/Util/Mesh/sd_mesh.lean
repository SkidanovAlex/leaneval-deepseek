import Mathlib
import Submission.Work.PL.Subdiv.SdBasic
import Submission.Work.Cells.Connell.meshLT_dist_lt

/-!
# Mesh of the barycentric subdivision (blueprint G3, `sd_mesh`)

If every face of `K` has at most `d + 1` vertices (`PL.DimLE K d`) and the vertex diameter of
every face of `K` is `< δ` (`PL.MeshLT K δ`), then the vertex diameter of every face of the
barycentric subdivision `sd K` is `< d/(d+1) · δ`.

The faces of `sd K` are the barycenters of chains of faces of `K`. A chain of faces of `K` that
are all contained in a single face `S ∈ K.faces` spans a simplex of `sd K` with at most `|S| ≤ d+1`
vertices; the estimate is the classical contraction estimate for barycentric subdivision: if
`ρ ⊆ S` are faces then `bary S` lies on the segment from `bary ρ` to `bary (S \ ρ)` at parameter
`|S \ ρ| / |S|`, and `bary ρ`, `bary (S \ ρ)` both lie in the simplex `simp S`, whose diameter is
`< δ` because vertex distances in `S` are `< δ`. Hence
`dist (bary ρ) (bary S) < (|S| - |ρ|)/|S| · δ ≤ d/(d+1) · δ`.
-/

open Set Metric
open scoped BigOperators
open PL

namespace Work.PL.Subdiv.Util.Mesh

noncomputable section

variable {N : ℕ}

/-! ### Elementary facts about `bary` -/

/-- `card • bary = sum` (also valid for the empty finset, where both sides vanish). -/
lemma card_smul_bary (s : Finset (E N)) : (s.card : ℝ) • bary s = ∑ v ∈ s, v := by
  rcases Finset.eq_empty_or_nonempty s with h | h
  · subst h; simp [bary]
  · have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr h
    rw [bary_eq_smul_sum, ← mul_smul, mul_inv_cancel₀ hc, one_smul]

/-- The barycenter of `S` is the `card`-weighted average of the barycenters of `ρ` and `S \ ρ`. -/
lemma smul_bary_eq {S ρ : Finset (E N)} (hρS : ρ ⊆ S) (hρne : ρ.Nonempty) :
    (S.card : ℝ) • bary S = (ρ.card : ℝ) • bary ρ + ((S \ ρ).card : ℝ) • bary (S \ ρ) := by
  rw [card_smul_bary, card_smul_bary, card_smul_bary]
  rw [← Finset.sum_sdiff hρS, add_comm]

/-- Consequence of `smul_bary_eq`: `bary S` lies on the line through `bary ρ` and `bary (S \ ρ)`. -/
lemma smul_sub_bary_eq {S ρ : Finset (E N)} (hρS : ρ ⊆ S) (hρne : ρ.Nonempty) :
    (S.card : ℝ) • (bary S - bary ρ) = ((S \ ρ).card : ℝ) • (bary (S \ ρ) - bary ρ) := by
  have h := smul_bary_eq hρS hρne
  have hcard : (S.card : ℝ) = (ρ.card : ℝ) + ((S \ ρ).card : ℝ) := by
    have := Finset.card_sdiff_of_subset hρS
    rw [this, Nat.cast_sub (Finset.card_le_card hρS)]; ring
  rw [smul_sub, h, hcard, add_smul, smul_sub]
  module

/-- The exact distance formula: `dist (bary ρ) (bary S)` is `|S \ ρ|/|S|` times
`dist (bary ρ) (bary (S \ ρ))`. -/
lemma dist_bary_bary_eq {S ρ : Finset (E N)} (hρS : ρ ⊆ S) (hρne : ρ.Nonempty) :
    dist (bary ρ) (bary S) =
      ((S \ ρ).card : ℝ) / (S.card : ℝ) * dist (bary ρ) (bary (S \ ρ)) := by
  have hm : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr (hρne.mono hρS)
  have h := smul_sub_bary_eq hρS hρne
  have hnorm : (S.card : ℝ) * ‖bary S - bary ρ‖
      = ((S \ ρ).card : ℝ) * ‖bary (S \ ρ) - bary ρ‖ := by
    have h2 := congrArg norm h
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)] at h2
    exact h2
  rw [dist_eq_norm, dist_eq_norm, norm_sub_rev (bary ρ) (bary S),
      norm_sub_rev (bary ρ) (bary (S \ ρ))]
  rw [div_mul_eq_mul_div, eq_div_iff hm]
  simpa [mul_comm] using hnorm

/-! ### The arithmetic bound `|S \ ρ|/|S| ≤ d/(d+1)` -/

lemma div_sub_le {m k d : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) (hm : m ≤ d + 1) :
    ((m - k : ℕ) : ℝ) / (m : ℝ) ≤ (d : ℝ) / ((d + 1 : ℕ) : ℝ) := by
  have hk0 : 0 < k := hk
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    have : 0 < m := lt_of_lt_of_le hk0 hkm
    exact_mod_cast this
  have hd0 : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
  have hmle : (m : ℝ) ≤ (d : ℝ) + 1 := by
    have h : ((m : ℕ) : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by exact_mod_cast hm
    push_cast at h ⊢; linarith
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  rw [Nat.cast_sub hkm]
  rw [div_le_div_iff₀ hm0 hd0]
  push_cast
  nlinarith [hmle, hk1]

/-! ### The mesh estimate for a pair of nested faces -/

/-- If `A ⊆ B` are faces of `K` with `A ≠ B`, then the distance between the barycenters
`bary A` and `bary B` is `< d/(d+1) · δ`. -/
lemma dist_bary_pair_lt {K : Cx N} {d : ℕ} {δ : ℝ} (h : DimLE K d) (hδ : MeshLT K δ)
    (hδpos : 0 < δ) {A B : Finset (E N)} (hA : A ∈ K.faces) (hB : B ∈ K.faces)
    (hAB : A ⊆ B) (hne : A ≠ B) :
    dist (bary A) (bary B) < (d : ℝ) / (d + 1) * δ := by
  have hAne : A.Nonempty := K.nonempty_of_mem_faces hA
  have hBne : B.Nonempty := hAne.mono hAB
  have hlt : A.card < B.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hAB, hne⟩)
  have hTne : (B \ A).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset hAB]; omega
  have hbA : bary A ∈ simp B :=
    convexHull_mono (Finset.coe_subset.mpr hAB) (bary_mem_simp hAne)
  have hbT : bary (B \ A) ∈ simp B :=
    convexHull_mono (Finset.coe_subset.mpr Finset.sdiff_subset) (bary_mem_simp hTne)
  have hdist : dist (bary A) (bary (B \ A)) < δ :=
    Work.Cells.Connell.meshLT_dist_lt hδ hB hbA hbT
  rw [dist_bary_bary_eq hAB hAne]
  have hcoef : 0 < ((B \ A).card : ℝ) / (B.card : ℝ) := by
    apply div_pos
    · exact_mod_cast Finset.card_pos.mpr hTne
    · exact_mod_cast Finset.card_pos.mpr hBne
  calc ((B \ A).card : ℝ) / (B.card : ℝ) * dist (bary A) (bary (B \ A))
      < ((B \ A).card : ℝ) / (B.card : ℝ) * δ := mul_lt_mul_of_pos_left hdist hcoef
    _ ≤ (d : ℝ) / (d + 1) * δ := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hδpos)
        rw [Finset.card_sdiff_of_subset hAB]
        simpa using div_sub_le (by have hc := Finset.card_pos.mpr hAne; omega)
          (Finset.card_le_card hAB) (h B hB)

/-! ### Main statement -/

theorem sd_mesh {N : ℕ} {K : PL.Cx N} {d : ℕ} (hd : 0 < d) (h : PL.DimLE K d) {δ : ℝ}
    (hδ : PL.MeshLT K δ) : PL.MeshLT (Work.PL.Subdiv.sd K) ((d : ℝ) / (d + 1) * δ) := by
  intro t ht x hx y hy
  obtain ⟨-, C, hC, rfl⟩ := Work.PL.Subdiv.mem_sd_faces_iff.mp ht
  obtain ⟨ρ, hρC, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨ρ', hρ'C, rfl⟩ := Finset.mem_image.mp hy
  have hδpos : 0 < δ := by
    obtain ⟨u, hu⟩ := K.nonempty_of_mem_faces (hC.1 ρ hρC)
    have := hδ ρ (hC.1 ρ hρC) u hu u hu
    simpa using this
  rcases eq_or_ne ρ ρ' with rfl | hne
  · rw [dist_self]
    exact mul_pos (div_pos (by exact_mod_cast hd) (by positivity)) hδpos
  · rcases hC.2 ρ hρC ρ' hρ'C with hsub | hsub
    · exact dist_bary_pair_lt h hδ hδpos (hC.1 ρ hρC) (hC.1 ρ' hρ'C) hsub hne
    · rw [dist_comm]
      exact dist_bary_pair_lt h hδ hδpos (hC.1 ρ' hρ'C) (hC.1 ρ hρC) hsub (Ne.symm hne)

end

end Work.PL.Subdiv.Util.Mesh
