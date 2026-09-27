import Mathlib
import Submission.Work.PL.Subdiv.SdBasic
import Submission.Work.Cells.Connell.meshLT_dist_lt

/-!
# Iterated barycentric subdivision has arbitrarily small mesh

`exists_fine`: for a finite simplicial complex `K` with `DimLE K d`, `0 < d`, and any `δ > 0`
there is `r` such that every `r' ≥ r`-fold barycentric subdivision of `K` has mesh `< δ`.

The geometric heart is that one barycentric subdivision contracts the mesh by the factor
`d/(d+1)` (`sd_mesh_step`), which is proved from the elementary estimate on barycenters of
nested finite vertex sets (`dist_bary_contraction`).
-/

open Set Metric
open scoped BigOperators
open PL

namespace Work.PL.Subdiv.Util.Mesh

noncomputable section

/-- The barycenter of a nonempty vertex set satisfies `card • bary s = ∑ v`. -/
private lemma card_smul_bary {N : ℕ} (S : Finset (PL.E N)) :
    (S.card : ℝ) • Work.PL.Subdiv.bary S = ∑ v ∈ S, v := by
  rw [Work.PL.Subdiv.bary_eq_smul_sum, smul_smul]
  rcases S.eq_empty_or_nonempty with h | h
  · subst h; simp
  · rw [mul_inv_cancel₀ (by exact_mod_cast Finset.card_ne_zero.mpr h), one_smul]

/-- For `S ⊆ B` nonempty `B`, the difference of barycenters is the average of `v - bary S`
over `B \ S`. -/
private lemma bary_sub_bary {N : ℕ} (S B : Finset (PL.E N)) (hSB : S ⊆ B) (hB : B.Nonempty) :
    Work.PL.Subdiv.bary B - Work.PL.Subdiv.bary S
      = (B.card : ℝ)⁻¹ • ∑ v ∈ B \ S, (v - Work.PL.Subdiv.bary S) := by
  have hcard : (B.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hB
  have h2 : ∑ v ∈ B, (v - Work.PL.Subdiv.bary S)
      = ∑ v ∈ B, v - (B.card : ℝ) • Work.PL.Subdiv.bary S := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]
  have h1 : Work.PL.Subdiv.bary B - Work.PL.Subdiv.bary S
      = (B.card : ℝ)⁻¹ • ∑ v ∈ B, (v - Work.PL.Subdiv.bary S) := by
    rw [h2, smul_sub, Work.PL.Subdiv.bary_eq_smul_sum B, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  have hzero : ∑ v ∈ S, (v - Work.PL.Subdiv.bary S) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, card_smul_bary S,
        sub_self]
  have hsum : ∑ v ∈ B, (v - Work.PL.Subdiv.bary S)
      = ∑ v ∈ B \ S, (v - Work.PL.Subdiv.bary S) := by
    conv_lhs => rw [← Finset.sum_sdiff (s₁ := S) (s₂ := B) hSB]
    rw [hzero, add_zero]
  rw [h1, hsum]

/-- Triangle-inequality bound on the distance between the barycenters of `S ⊆ B`: it is at most
`|B \ S| / |B|` times any bound `ε` for the distance of the elements of `B \ S` to `bary S`. -/
private lemma dist_bary_le {N : ℕ} (S B : Finset (PL.E N)) (hSB : S ⊆ B) (hB : B.Nonempty) {ε : ℝ}
    (h : ∀ v ∈ B \ S, dist v (Work.PL.Subdiv.bary S) ≤ ε) :
    dist (Work.PL.Subdiv.bary S) (Work.PL.Subdiv.bary B)
      ≤ ((B \ S).card : ℝ) / (B.card : ℝ) * ε := by
  have hcard : (0:ℝ) < B.card := by exact_mod_cast Finset.card_pos.mpr hB
  rw [dist_eq_norm, norm_sub_rev, bary_sub_bary S B hSB hB]
  calc ‖(B.card : ℝ)⁻¹ • ∑ v ∈ B \ S, (v - Work.PL.Subdiv.bary S)‖
      = (B.card : ℝ)⁻¹ * ‖∑ v ∈ B \ S, (v - Work.PL.Subdiv.bary S)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (B.card:ℝ)⁻¹)]
    _ ≤ (B.card : ℝ)⁻¹ * ∑ v ∈ B \ S, ‖v - Work.PL.Subdiv.bary S‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = (B.card : ℝ)⁻¹ * ∑ v ∈ B \ S, dist v (Work.PL.Subdiv.bary S) := by
        simp only [dist_eq_norm]
    _ ≤ (B.card : ℝ)⁻¹ * ∑ v ∈ B \ S, ε :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum h) (by positivity)
    _ = ((B \ S).card : ℝ) / (B.card : ℝ) * ε := by
        rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]; ring

/-- Strict version of `dist_bary_le`: if `B \ S` is nonempty and the distances are `< ε`, then the
barycenter distance is strictly below `|B \ S| / |B| * ε`. -/
private lemma dist_bary_lt {N : ℕ} (S B : Finset (PL.E N)) (hSB : S ⊆ B) (hB : B.Nonempty) {ε : ℝ}
    (hne : (B \ S).Nonempty)
    (h : ∀ v ∈ B \ S, dist v (Work.PL.Subdiv.bary S) < ε) :
    dist (Work.PL.Subdiv.bary S) (Work.PL.Subdiv.bary B)
      < ((B \ S).card : ℝ) / (B.card : ℝ) * ε := by
  have hcard : (0:ℝ) < B.card := by exact_mod_cast Finset.card_pos.mpr hB
  have hsum_lt : ∑ v ∈ B \ S, dist v (Work.PL.Subdiv.bary S) < ∑ v ∈ B \ S, ε := by
    refine Finset.sum_lt_sum (fun v hv => le_of_lt (h v hv)) ?_
    obtain ⟨v, hv⟩ := hne
    exact ⟨v, hv, h v hv⟩
  rw [dist_eq_norm, norm_sub_rev, bary_sub_bary S B hSB hB]
  calc ‖(B.card : ℝ)⁻¹ • ∑ v ∈ B \ S, (v - Work.PL.Subdiv.bary S)‖
      = (B.card : ℝ)⁻¹ * ‖∑ v ∈ B \ S, (v - Work.PL.Subdiv.bary S)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (B.card:ℝ)⁻¹)]
    _ ≤ (B.card : ℝ)⁻¹ * ∑ v ∈ B \ S, ‖v - Work.PL.Subdiv.bary S‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = (B.card : ℝ)⁻¹ * ∑ v ∈ B \ S, dist v (Work.PL.Subdiv.bary S) := by
        simp only [dist_eq_norm]
    _ < (B.card : ℝ)⁻¹ * ∑ v ∈ B \ S, ε :=
        mul_lt_mul_of_pos_left hsum_lt (by positivity)
    _ = ((B \ S).card : ℝ) / (B.card : ℝ) * ε := by
        rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]; ring

/-- **Mesh contraction.**  If `ρ ⊊ ρ'` are two faces of a complex of dimension `≤ d` (with
`ρ.Nonempty`), then the barycenters are at distance `< d/(d+1) * ε` whenever `ε` bounds the
diameter of the vertices of `ρ'`. -/
private lemma dist_bary_contraction {N : ℕ} {K : PL.Cx N} {d : ℕ} (h : PL.DimLE K d) {ε : ℝ}
    (hε : PL.MeshLT K ε) {ρ ρ' : Finset (PL.E N)} (hρ' : ρ' ∈ K.faces)
    (hρ : ρ.Nonempty) (hsub : ρ ⊆ ρ') (hne : ρ ≠ ρ') :
    dist (Work.PL.Subdiv.bary ρ) (Work.PL.Subdiv.bary ρ') < ((d : ℝ) / (d + 1)) * ε := by
  have hεpos : 0 < ε := by
    obtain ⟨w, hw⟩ := K.nonempty_of_mem_faces hρ'
    have := hε ρ' hρ' w hw w hw
    simpa using this
  have hssub : ρ ⊂ ρ' := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
  obtain ⟨v, hvρ', hvρ⟩ := Finset.exists_of_ssubset hssub
  have hne' : (ρ' \ ρ).Nonempty := ⟨v, Finset.mem_sdiff.mpr ⟨hvρ', hvρ⟩⟩
  have hmesh : ∀ u ∈ ρ' \ ρ, dist u (Work.PL.Subdiv.bary ρ) < ε := by
    intro u hu
    have huρ' : u ∈ ρ' := (Finset.mem_sdiff.mp hu).1
    exact Work.Cells.Connell.meshLT_dist_lt hε hρ'
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr huρ'))
      (convexHull_mono (Finset.coe_subset.mpr hsub) (Work.PL.Subdiv.bary_mem_simp hρ))
  have hlt := dist_bary_lt ρ ρ' hsub (K.nonempty_of_mem_faces hρ') hne' hmesh
  have hle : ((ρ' \ ρ).card : ℝ) / (ρ'.card : ℝ) ≤ (d : ℝ) / (d + 1) := by
    have hm_pos : (0:ℝ) < ρ'.card :=
      by exact_mod_cast Finset.card_pos.mpr (K.nonempty_of_mem_faces hρ')
    have hd1 : (0:ℝ) < (d:ℝ) + 1 := by positivity
    have hk1 : (1:ℝ) ≤ ρ.card := by exact_mod_cast Finset.card_pos.mpr hρ
    have hk_le : (ρ.card : ℝ) ≤ (ρ'.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    have hmd : (ρ'.card : ℝ) ≤ (d:ℝ) + 1 := by
      have := h ρ' hρ'; exact_mod_cast this
    have hcarddiff : ((ρ' \ ρ).card : ℝ) = (ρ'.card : ℝ) - (ρ.card : ℝ) := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Nat.cast_sub (Finset.card_le_card hsub)]
    rw [div_le_div_iff₀ hm_pos hd1, hcarddiff]
    nlinarith [hk1, hk_le, hmd]
  exact lt_of_lt_of_le hlt (mul_le_mul_of_nonneg_right hle (le_of_lt hεpos))

/-- **One barycentric subdivision contracts the mesh by `d/(d+1)`.** -/
private lemma sd_mesh_step {N : ℕ} {K : PL.Cx N} {d : ℕ} (hd : 0 < d) (h : PL.DimLE K d) {ε : ℝ}
    (hε : PL.MeshLT K ε) :
    PL.MeshLT (Work.PL.Subdiv.sd K) ((d : ℝ) / (d + 1) * ε) := by
  intro t ht x hx y hy
  obtain ⟨-, C, hC, rfl⟩ := Work.PL.Subdiv.mem_sd_faces_iff.mp ht
  obtain ⟨ρ, hρC, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨ρ', hρ'C, rfl⟩ := Finset.mem_image.mp hy
  have hρ' : ρ' ∈ K.faces := hC.1 ρ' hρ'C
  rcases eq_or_ne ρ ρ' with hρρ | hne
  · rw [hρρ, dist_self]
    have hq : (0:ℝ) < (d:ℝ) / (d + 1) := by positivity
    have hεpos : 0 < ε := by
      obtain ⟨w, hw⟩ := K.nonempty_of_mem_faces hρ'
      have := hε ρ' hρ' w hw w hw
      simpa using this
    exact mul_pos hq hεpos
  · rcases hC.2 ρ hρC ρ' hρ'C with hsub | hsub
    · exact dist_bary_contraction h hε hρ' (K.nonempty_of_mem_faces (hC.1 ρ hρC)) hsub hne
    · rw [dist_comm]
      exact dist_bary_contraction h hε (hC.1 ρ hρC) (K.nonempty_of_mem_faces hρ') hsub (Ne.symm hne)

theorem exists_fine {N : ℕ} (K : PL.Cx N) (hK : K.faces.Finite) (d : ℕ) (hd : 0 < d)
    (h : PL.DimLE K d) (δ : ℝ) (hδ : 0 < δ) :
    ∃ r, ∀ r' ≥ r, PL.MeshLT (Work.PL.Subdiv.sdIter r' K hK) δ := by
  classical
  -- an explicit (positive) mesh bound for the finite complex `K`
  obtain ⟨D0, hD0pos, hmesh0⟩ : ∃ D0 : ℝ, 0 < D0 ∧ PL.MeshLT K D0 := by
    refine ⟨2 * (∑ v ∈ hK.toFinset.biUnion id, ‖v‖) + 1, by positivity, ?_⟩
    intro s hs x hx y hy
    have hsT : s ∈ hK.toFinset := (Set.Finite.mem_toFinset hK).mpr hs
    have hxV : x ∈ hK.toFinset.biUnion id := Finset.mem_biUnion.mpr ⟨s, hsT, hx⟩
    have hyV : y ∈ hK.toFinset.biUnion id := Finset.mem_biUnion.mpr ⟨s, hsT, hy⟩
    have hxb : ‖x‖ ≤ ∑ v ∈ hK.toFinset.biUnion id, ‖v‖ :=
      Finset.single_le_sum (fun v _ => norm_nonneg v) hxV
    have hyb : ‖y‖ ≤ ∑ v ∈ hK.toFinset.biUnion id, ‖v‖ :=
      Finset.single_le_sum (fun v _ => norm_nonneg v) hyV
    calc dist x y = ‖x - y‖ := dist_eq_norm x y
      _ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
      _ ≤ 2 * (∑ v ∈ hK.toFinset.biUnion id, ‖v‖) := by linarith
      _ < 2 * (∑ v ∈ hK.toFinset.biUnion id, ‖v‖) + 1 := by linarith
  -- the contraction factor
  set q : ℝ := (d:ℝ) / (d + 1) with hqdef
  have hqpos : 0 < q := by rw [hqdef]; positivity
  have hq1 : q < 1 := by
    rw [hqdef, div_lt_one (by positivity : (0:ℝ) < (d:ℝ) + 1)]
    exact_mod_cast Nat.lt_succ_self d
  -- the mesh after `r` subdivisions is `< q^r * D0`
  have hmesh : ∀ r, PL.MeshLT (Work.PL.Subdiv.sdIter r K hK) (q ^ r * D0) := by
    intro r
    induction r with
    | zero => simpa using hmesh0
    | succ n ih =>
        rw [Work.PL.Subdiv.sdIter_succ]
        have hstep := sd_mesh_step hd (Work.PL.Subdiv.sdIter_dimle n d K hK h) ih
        rw [show q ^ (n + 1) * D0 = q * (q ^ n * D0) by rw [pow_succ]; ring]
        exact hstep
  -- `q^r * D0 → 0`
  have hlim : Filter.Tendsto (fun r : ℕ => q ^ r * D0) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun r : ℕ => q ^ r) Filter.atTop (nhds (0:ℝ)) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hqpos) hq1
    simpa using h1.mul_const D0
  have hev : ∀ᶠ r in Filter.atTop, q ^ r * D0 < δ := by
    have hmem : {y : ℝ | y < δ} ∈ nhds (0:ℝ) := isOpen_Iio.mem_nhds hδ
    exact hlim.eventually hmem
  obtain ⟨r, hr⟩ := Filter.eventually_atTop.mp hev
  exact ⟨r, fun r' hr' s hs x hx y hy => lt_trans (hmesh r' s hs x hx y hy) (hr r' hr')⟩

end

end Work.PL.Subdiv.Util.Mesh
