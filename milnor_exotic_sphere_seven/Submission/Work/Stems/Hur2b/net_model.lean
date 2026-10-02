import Mathlib
import Submission.Work.Stems.Hur2b.NetData
import Submission.Work.Stems.Hur2b.NetLayout
import Submission.Work.Stems.Hur2b.NetExitGeom
import Submission.Work.Stems.Hur2b.NetTau
import Submission.Work.Stems.Hur2b.NetTree
import Submission.Work.Stems.Hur2b.NetReadDefs
import Submission.Work.Stems.Hur2b.net_rho_continuous
import Submission.Work.Stems.Hur2b.net_rho_zero
import Submission.Work.Stems.Hur2b.net_readExt_tree
import Submission.Work.Stems.Hur2b.net_exit_mem_bdy

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The pinched model of `∂I³`

We construct the map `ψ : I² → ∂I³` which

* is the base vertex `vertexBdy3 = (0,0,0)` on the boundary `∂I²`,
* agrees, on each of the six cells of the T-net, with the reading `netRead k`, and
* maps the collar (the complement of the six *open* cells) into the `1`-skeleton `Skel3`.

The map is assembled from two halves on the closed cover `{D, ∁ (interior D)}` of the square,
where `D = ⋃ k, netCell k` is the net region:

* on `D` it is the reading of a net cell containing the point (`psiDFun`);
* off the interior of `D` it is the *radial* model: the exit point `radialPoint (offOf y)` lies on
  `∂D`, and `psiCFun y` reads the walk there (`walk`) and contracts it towards the base vertex with
  the parameter `tau y`, so that it is constant on `∂I²`.

The two halves agree on `D ∩ ∁(interior D) = ∂D` (both give the walk value), and the pasting lemma
for the closed cover gives a continuous map with the three required properties.

The finite facts about the readings and the contraction (`net_readExt_agree`, `net_rho_one`,
`net_rho_mem`, `net_cellCoord_cellRead`, `net_readExt_skel_cell`) are stated as hypotheses of
`net_model_aux`, so that the assembly can be verified independently of them; the final theorem
`net_model` supplies them.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2b

open Work.Stems.Cubical Work.Stems.Hur2

noncomputable section

open Classical

/-! ## The finite facts about the readings and the contraction

(TEMPORARY PLACEHOLDERS: these are the lemmas the assembly below rests on.) -/

/-! ### The six readings agree on the overlaps of the net cells -/

theorem agree_01 (y : IC 2) (h : y ∈ netCell 0) (h' : y ∈ netCell 1) :
    readExt 0 y = readExt 1 y := by
  simp only [netCell, gridCell, Set.mem_ofPred_eq] at h h'
  push_cast at h h'
  apply Subtype.ext
  rw [readExt_val_0 h, readExt_val_1 h']
  have hy : (y 0 : ℝ) = 3/8 := by linarith [h.1, h.2.1, h'.1, h'.2.1]
  rw [hy]
  rw [show (19:ℝ) - 64 * (3/8) = -5 by norm_num, show (28:ℝ) - 64 * (3/8) = 4 by norm_num]
  rw [clamp_eq_zero_of_nonpos (by norm_num : (-5:ℝ) ≤ 0),
    clamp_eq_one_of_one_le (by norm_num : (1:ℝ) ≤ 4)]

theorem agree_12 (y : IC 2) (h : y ∈ netCell 1) (h' : y ∈ netCell 2) :
    readExt 1 y = readExt 2 y := by
  simp only [netCell, gridCell, Set.mem_ofPred_eq] at h h'
  push_cast at h h'
  apply Subtype.ext
  rw [readExt_val_1 h, readExt_val_2 h']
  have hy : (y 0 : ℝ) = 1/2 := by linarith [h.1, h.2.1, h'.1, h'.2.1]
  rw [hy]
  rw [show (28:ℝ) - 64 * (1/2) = -4 by norm_num, show (64:ℝ) * (1/2) - 36 = -4 by norm_num]
  rw [clamp_eq_zero_of_nonpos (by norm_num : (-4:ℝ) ≤ 0)]

theorem agree_23 (y : IC 2) (h : y ∈ netCell 2) (h' : y ∈ netCell 3) :
    readExt 2 y = readExt 3 y := by
  simp only [netCell, gridCell, Set.mem_ofPred_eq] at h h'
  push_cast at h h'
  apply Subtype.ext
  rw [readExt_val_2 h, readExt_val_3 h']
  have hy : (y 0 : ℝ) = 5/8 := by linarith [h.1, h.2.1, h'.1, h'.2.1]
  rw [hy]
  rw [show (64:ℝ) * (5/8) - 36 = 4 by norm_num, show (64:ℝ) * (5/8) - 45 = -5 by norm_num]
  rw [clamp_eq_one_of_one_le (by norm_num : (1:ℝ) ≤ 4),
    clamp_eq_zero_of_nonpos (by norm_num : (-5:ℝ) ≤ 0)]

theorem agree_04 (y : IC 2) (h : y ∈ netCell 0) (h' : y ∈ netCell 4) :
    readExt 0 y = readExt 4 y := by
  simp only [netCell, gridCell, Set.mem_ofPred_eq] at h h'
  push_cast at h h'
  apply Subtype.ext
  rw [readExt_val_0 h, readExt_val_4 h']
  have hy0 : (y 0 : ℝ) = 3/8 := by linarith [h.1, h.2.1, h'.1, h'.2.1]
  have hy1 : (y 1 : ℝ) = 3/8 := by linarith [h.2.2.1, h.2.2.2, h'.2.2.1, h'.2.2.2]
  rw [hy0, hy1]
  rw [show (64:ℝ) * (3/8) - 27 = -3 by norm_num, show (28:ℝ) - 64 * (3/8) = 4 by norm_num]
  rw [clamp_eq_zero_of_nonpos (by norm_num : (-3:ℝ) ≤ 0),
    clamp_eq_one_of_one_le (by norm_num : (1:ℝ) ≤ 4)]

theorem agree_14 (y : IC 2) (h : y ∈ netCell 1) (h' : y ∈ netCell 4) :
    readExt 1 y = readExt 4 y := by
  simp only [netCell, gridCell, Set.mem_ofPred_eq] at h h'
  push_cast at h h'
  apply Subtype.ext
  rw [readExt_val_1 h, readExt_val_4 h']
  have hy1 : (y 1 : ℝ) = 3/8 := by linarith [h.2.2.1, h.2.2.2, h'.2.2.1, h'.2.2.2]
  rw [hy1]
  rw [show (64:ℝ) * (3/8) - 27 = -3 by norm_num, show (19:ℝ) - 64 * (3/8) = -5 by norm_num]
  rw [clamp_eq_zero_of_nonpos (by norm_num : (-3:ℝ) ≤ 0),
    clamp_eq_zero_of_nonpos (by norm_num : (-5:ℝ) ≤ 0)]

theorem agree_05 (y : IC 2) (h : y ∈ netCell 0) (h' : y ∈ netCell 5) :
    readExt 0 y = readExt 5 y := by
  simp only [netCell, gridCell, Set.mem_ofPred_eq] at h h'
  push_cast at h h'
  apply Subtype.ext
  rw [readExt_val_0 h, readExt_val_5 h']
  have hy0 : (y 0 : ℝ) = 3/8 := by linarith [h.1, h.2.1, h'.1, h'.2.1]
  have hy1 : (y 1 : ℝ) = 1/2 := by linarith [h.2.2.1, h.2.2.2, h'.2.2.1, h'.2.2.2]
  rw [hy0, hy1]
  rw [show (19:ℝ) - 64 * (3/8) = -5 by norm_num, show (64:ℝ) * (1/2) - 27 = 5 by norm_num,
    show (64:ℝ) * (1/2) - 36 = -4 by norm_num, show (28:ℝ) - 64 * (3/8) = 4 by norm_num]
  rw [clamp_eq_zero_of_nonpos (by norm_num : (-5:ℝ) ≤ 0),
    clamp_eq_one_of_one_le (by norm_num : (1:ℝ) ≤ 5),
    clamp_eq_zero_of_nonpos (by norm_num : (-4:ℝ) ≤ 0),
    clamp_eq_one_of_one_le (by norm_num : (1:ℝ) ≤ 4)]

theorem agree_15 (y : IC 2) (h : y ∈ netCell 1) (h' : y ∈ netCell 5) :
    readExt 1 y = readExt 5 y := by
  simp only [netCell, gridCell, Set.mem_ofPred_eq] at h h'
  push_cast at h h'
  apply Subtype.ext
  rw [readExt_val_1 h, readExt_val_5 h']
  have hy1 : (y 1 : ℝ) = 1/2 := by linarith [h.2.2.1, h.2.2.2, h'.2.2.1, h'.2.2.2]
  rw [hy1]
  rw [show (64:ℝ) * (1/2) - 27 = 5 by norm_num, show (64:ℝ) * (1/2) - 36 = -4 by norm_num]
  rw [clamp_eq_one_of_one_le (by norm_num : (1:ℝ) ≤ 5),
    clamp_eq_zero_of_nonpos (by norm_num : (-4:ℝ) ≤ 0)]

theorem agree_24 (y : IC 2) (h : y ∈ netCell 2) (h' : y ∈ netCell 4) :
    readExt 2 y = readExt 4 y := by
  simp only [netCell, gridCell, Set.mem_ofPred_eq] at h h'
  push_cast at h h'
  apply Subtype.ext
  rw [readExt_val_2 h, readExt_val_4 h']
  have hy0 : (y 0 : ℝ) = 1/2 := by linarith [h.1, h.2.1, h'.1, h'.2.1]
  have hy1 : (y 1 : ℝ) = 3/8 := by linarith [h.2.2.1, h.2.2.2, h'.2.2.1, h'.2.2.2]
  rw [hy0, hy1]
  rw [show (64:ℝ) * (1/2) - 36 = -4 by norm_num, show (64:ℝ) * (3/8) - 27 = -3 by norm_num,
    show (19:ℝ) - 64 * (3/8) = -5 by norm_num, show (28:ℝ) - 64 * (1/2) = -4 by norm_num]
  rw [clamp_eq_zero_of_nonpos (by norm_num : (-4:ℝ) ≤ 0),
    clamp_eq_zero_of_nonpos (by norm_num : (-3:ℝ) ≤ 0),
    clamp_eq_zero_of_nonpos (by norm_num : (-5:ℝ) ≤ 0)]

theorem agree_25 (y : IC 2) (h : y ∈ netCell 2) (h' : y ∈ netCell 5) :
    readExt 2 y = readExt 5 y := by
  simp only [netCell, gridCell, Set.mem_ofPred_eq] at h h'
  push_cast at h h'
  apply Subtype.ext
  rw [readExt_val_2 h, readExt_val_5 h']
  have hy0 : (y 0 : ℝ) = 1/2 := by linarith [h.1, h.2.1, h'.1, h'.2.1]
  have hy1 : (y 1 : ℝ) = 1/2 := by linarith [h.2.2.1, h.2.2.2, h'.2.2.1, h'.2.2.2]
  rw [hy0, hy1]
  rw [show (64:ℝ) * (1/2) - 36 = -4 by norm_num, show (64:ℝ) * (1/2) - 27 = 5 by norm_num,
    show (28:ℝ) - 64 * (1/2) = -4 by norm_num]
  rw [clamp_eq_zero_of_nonpos (by norm_num : (-4:ℝ) ≤ 0),
    clamp_eq_one_of_one_le (by norm_num : (1:ℝ) ≤ 5)]

theorem netCell_disjoint_02 : ∀ y : IC 2, ¬ (y ∈ netCell 0 ∧ y ∈ netCell 2) := by
  intro y hh
  obtain ⟨h, h'⟩ := hh
  simp only [netCell, gridCell, Set.mem_ofPred_eq] at h h'
  push_cast at h h'
  linarith [h.1, h.2.1, h'.1, h'.2.1]

theorem netCell_disjoint_03 : ∀ y : IC 2, ¬ (y ∈ netCell 0 ∧ y ∈ netCell 3) := by
  intro y hh
  obtain ⟨h, h'⟩ := hh
  simp only [netCell, gridCell, Set.mem_ofPred_eq] at h h'
  push_cast at h h'
  linarith [h.1, h.2.1, h'.1, h'.2.1]

theorem netCell_disjoint_13 : ∀ y : IC 2, ¬ (y ∈ netCell 1 ∧ y ∈ netCell 3) := by
  intro y hh
  obtain ⟨h, h'⟩ := hh
  simp only [netCell, gridCell, Set.mem_ofPred_eq] at h h'
  push_cast at h h'
  linarith [h.1, h.2.1, h'.1, h'.2.1]

theorem netCell_disjoint_34 : ∀ y : IC 2, ¬ (y ∈ netCell 3 ∧ y ∈ netCell 4) := by
  intro y hh
  obtain ⟨h, h'⟩ := hh
  simp only [netCell, gridCell, Set.mem_ofPred_eq] at h h'
  push_cast at h h'
  linarith [h.1, h.2.1, h'.1, h'.2.1]

theorem netCell_disjoint_35 : ∀ y : IC 2, ¬ (y ∈ netCell 3 ∧ y ∈ netCell 5) := by
  intro y hh
  obtain ⟨h, h'⟩ := hh
  simp only [netCell, gridCell, Set.mem_ofPred_eq] at h h'
  push_cast at h h'
  linarith [h.1, h.2.1, h'.1, h'.2.1]

theorem netCell_disjoint_45 : ∀ y : IC 2, ¬ (y ∈ netCell 4 ∧ y ∈ netCell 5) := by
  intro y hh
  obtain ⟨h, h'⟩ := hh
  simp only [netCell, gridCell, Set.mem_ofPred_eq] at h h'
  push_cast at h h'
  linarith [h.2.2.1, h.2.2.2, h'.2.2.1, h'.2.2.2]

theorem net_readExt_agree : ∀ (y : IC 2) (k l : Fin 6), y ∈ netCell k → y ∈ netCell l →
    readExt k y = readExt l y := by
  intro y k l h h'
  fin_cases k <;> fin_cases l
  · rfl
  · exact agree_01 y h h'
  · exact (netCell_disjoint_02 y ⟨h, h'⟩).elim
  · exact (netCell_disjoint_03 y ⟨h, h'⟩).elim
  · exact agree_04 y h h'
  · exact agree_05 y h h'
  · exact (agree_01 y h' h).symm
  · rfl
  · exact agree_12 y h h'
  · exact (netCell_disjoint_13 y ⟨h, h'⟩).elim
  · exact agree_14 y h h'
  · exact agree_15 y h h'
  · exact (netCell_disjoint_02 y ⟨h', h⟩).elim
  · exact (agree_12 y h' h).symm
  · rfl
  · exact agree_23 y h h'
  · exact agree_24 y h h'
  · exact agree_25 y h h'
  · exact (netCell_disjoint_03 y ⟨h', h⟩).elim
  · exact (netCell_disjoint_13 y ⟨h', h⟩).elim
  · exact (agree_23 y h' h).symm
  · rfl
  · exact (netCell_disjoint_34 y ⟨h, h'⟩).elim
  · exact (netCell_disjoint_35 y ⟨h, h'⟩).elim
  · exact (agree_04 y h' h).symm
  · exact (agree_14 y h' h).symm
  · exact (agree_24 y h' h).symm
  · exact (netCell_disjoint_34 y ⟨h', h⟩).elim
  · rfl
  · exact (netCell_disjoint_45 y ⟨h, h'⟩).elim
  · exact (agree_05 y h' h).symm
  · exact (agree_15 y h' h).symm
  · exact (agree_25 y h' h).symm
  · exact (netCell_disjoint_35 y ⟨h', h⟩).elim
  · exact (netCell_disjoint_45 y ⟨h', h⟩).elim
  · rfl

/-! ### The contraction `rho` preserves the tree -/

theorem clamp_self_unitInterval (u : unitInterval) : clamp ((u : unitInterval) : ℝ) = u := by
  apply Subtype.ext
  exact clamp_val _ u.2

theorem prune_zero_of_p0 {p : IC 3} (hp : p 0 = 1) (t : ℝ) : (prune t p) 0 = 1 := by
  have hp' : (p 0 : ℝ) = 1 := by rw [hp]; rfl
  rw [prune, triple_zero, hp']
  rw [show (1:ℝ) + t * (1 - 1) * (1 - (1 - ↑(p 1)) * (1 - ↑(p 2))) = 1 by ring]
  exact clamp_eq_one_of_one_le le_rfl

theorem tree_prune {p : IC 3} (h : Tree p) (t : ℝ) : Tree (prune t p) := by
  have h1 : (prune t p) 1 = p 1 := by rw [prune, triple_one]
  have h2 : (prune t p) 2 = p 2 := by rw [prune, triple_two]
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact tree_br1 (by rw [h1, ha]) (by rw [h2, hb])
  · exact tree_br2 (prune_zero_of_p0 ha t) (by rw [h2, hb])
  · exact tree_br3 (prune_zero_of_p0 ha t) (by rw [h1, hb])
  · exact tree_br4 (by rw [h1, ha]) (by rw [h2, hb])
  · exact tree_br5 (prune_zero_of_p0 ha t) (by rw [h2, hb])
  · exact tree_br6 (by rw [h1, ha]) (by rw [h2, hb])
  · exact tree_br7 (by rw [h1, ha]) (by rw [h2, hb])

theorem fold1_of_pathSet {p : IC 3} (h : pathSet p) (t : ℝ) : Tree (fold1 t p) := by
  have h0 : (fold1 t p) 0 = p 0 := by rw [fold1, triple_zero]
  have h2 : (fold1 t p) 2 = p 2 := by rw [fold1, triple_two]
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · refine tree_br1 ?_ (by rw [h2, hb])
    have ha' : (p 1 : ℝ) = 0 := by rw [ha]; rfl
    have hb' : (p 2 : ℝ) = 0 := by rw [hb]; rfl
    rw [fold1, triple_one, ha', hb']
    rw [show (0:ℝ) + t * (1 - 0) * (↑(p 0) * 0) = 0 by ring]
    exact clamp_eq_zero_of_nonpos le_rfl
  · exact tree_br2 (by rw [h0, ha]) (by rw [h2, hb])
  · refine tree_br3 (by rw [h0, ha]) ?_
    have ha' : (p 0 : ℝ) = 1 := by rw [ha]; rfl
    have hb' : (p 1 : ℝ) = 1 := by rw [hb]; rfl
    rw [fold1, triple_one, ha', hb']
    rw [show (1:ℝ) + t * (1 - 1) * (1 * ↑(p 2)) = 1 by ring]
    exact clamp_eq_one_of_one_le le_rfl
  · exact tree_br5 (by rw [h0, ha]) (by rw [h2, hb])

theorem fold2_of_pathSet2 {p : IC 3} (h : pathSet2 p) (t : ℝ) : Tree (fold2 t p) := by
  have h0 : (fold2 t p) 0 = p 0 := by rw [fold2, triple_zero]
  have h1 : (fold2 t p) 1 = p 1 := by rw [fold2, triple_one]
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · refine tree_br1 (by rw [h1, ha]) ?_
    have hb' : (p 2 : ℝ) = 0 := by rw [hb]; rfl
    rw [fold2, triple_two, hb']
    rw [show (0:ℝ) * (1 - t * (↑(p 0) * ↑(p 1))) = 0 by ring]
    exact clamp_eq_zero_of_nonpos le_rfl
  · refine tree_br2 (by rw [h0, ha]) ?_
    have hb' : (p 2 : ℝ) = 0 := by rw [hb]; rfl
    rw [fold2, triple_two, hb']
    rw [show (0:ℝ) * (1 - t * (↑(p 0) * ↑(p 1))) = 0 by ring]
    exact clamp_eq_zero_of_nonpos le_rfl
  · exact tree_br3 (by rw [h0, ha]) (by rw [h1, hb])

theorem fold3_of_pathSet3 {p : IC 3} (h : pathSet3 p) (t : ℝ) : Tree (fold3 t p) := by
  have h0 : (fold3 t p) 0 = p 0 := by rw [fold3, triple_zero]
  have h2 : (fold3 t p) 2 = p 2 := by rw [fold3, triple_two]
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · refine tree_br1 ?_ (by rw [h2, hb])
    have ha' : (p 1 : ℝ) = 0 := by rw [ha]; rfl
    rw [fold3, triple_one, ha']
    rw [show (0:ℝ) * (1 - t * ↑(p 0)) = 0 by ring]
    exact clamp_eq_zero_of_nonpos le_rfl
  · exact tree_br2 (by rw [h0, ha]) (by rw [h2, hb])

theorem fold4_of_pathSet4 {p : IC 3} (h : pathSet4 p) (t : ℝ) : Tree (fold4 t p) := by
  have h1 : (fold4 t p) 1 = p 1 := by rw [fold4, triple_one]
  have h2 : (fold4 t p) 2 = p 2 := by rw [fold4, triple_two]
  obtain ⟨ha, hb⟩ := h
  exact tree_br1 (by rw [h1, ha]) (by rw [h2, hb])

theorem pathSet_prune_one {p : IC 3} (h : Tree p) : pathSet (prune 1 p) := by
  have h1 : (prune 1 p) 1 = p 1 := by rw [prune, triple_one]
  have h2 : (prune 1 p) 2 = p 2 := by rw [prune, triple_two]
  have hP0 : p 0 = 1 → (prune 1 p) 0 = 1 := by
    intro hp
    have hp' : (p 0 : ℝ) = 1 := by rw [hp]; rfl
    rw [prune, triple_zero, hp']
    rw [show (1:ℝ) + 1 * (1 - 1) * (1 - (1 - ↑(p 1)) * (1 - ↑(p 2))) = 1 by ring]
    exact clamp_eq_one_of_one_le le_rfl
  have hP1 : p 1 = 1 → p 2 = 1 → (prune 1 p) 0 = 1 := by
    intro hu hv
    have hu' : (p 1 : ℝ) = 1 := by rw [hu]; rfl
    have hv' : (p 2 : ℝ) = 1 := by rw [hv]; rfl
    rw [prune, triple_zero, hu', hv']
    rw [show (↑(p 0) : ℝ) + 1 * (1 - ↑(p 0)) * (1 - (1 - 1) * (1 - 1)) = 1 by ring]
    exact clamp_eq_one_of_one_le le_rfl
  have hP2 : p 1 = 1 → p 2 = 0 → (prune 1 p) 0 = 1 := by
    intro hu hv
    have hu' : (p 1 : ℝ) = 1 := by rw [hu]; rfl
    have hv' : (p 2 : ℝ) = 0 := by rw [hv]; rfl
    rw [prune, triple_zero, hu', hv']
    rw [show (↑(p 0) : ℝ) + 1 * (1 - ↑(p 0)) * (1 - (1 - 1) * (1 - 0)) = 1 by ring]
    exact clamp_eq_one_of_one_le le_rfl
  have hP3 : p 1 = 0 → p 2 = 1 → (prune 1 p) 0 = 1 := by
    intro hu hv
    have hu' : (p 1 : ℝ) = 0 := by rw [hu]; rfl
    have hv' : (p 2 : ℝ) = 1 := by rw [hv]; rfl
    rw [prune, triple_zero, hu', hv']
    rw [show (↑(p 0) : ℝ) + 1 * (1 - ↑(p 0)) * (1 - (1 - 0) * (1 - 1)) = 1 by ring]
    exact clamp_eq_one_of_one_le le_rfl
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inl ⟨by rw [h1, ha], by rw [h2, hb]⟩
  · exact Or.inr (Or.inl ⟨hP0 ha, by rw [h2, hb]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hP0 ha, by rw [h1, hb]⟩))
  · exact Or.inr (Or.inl ⟨hP2 ha hb, by rw [h2, hb]⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨hP0 ha, by rw [h2, hb]⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hP1 ha hb, by rw [h2, hb]⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hP3 ha hb, by rw [h2, hb]⟩))

theorem pathSet2_fold1_one {p : IC 3} (h : pathSet p) : pathSet2 (fold1 1 p) := by
  have h0 : (fold1 1 p) 0 = p 0 := by rw [fold1, triple_zero]
  have h2 : (fold1 1 p) 2 = p 2 := by rw [fold1, triple_two]
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · refine Or.inl ⟨?_, by rw [h2, hb]⟩
    have ha' : (p 1 : ℝ) = 0 := by rw [ha]; rfl
    have hb' : (p 2 : ℝ) = 0 := by rw [hb]; rfl
    rw [fold1, triple_one, ha', hb']
    rw [show (0:ℝ) + 1 * (1 - 0) * (↑(p 0) * 0) = 0 by ring]
    exact clamp_eq_zero_of_nonpos le_rfl
  · exact Or.inr (Or.inl ⟨by rw [h0, ha], by rw [h2, hb]⟩)
  · refine Or.inr (Or.inr ⟨by rw [h0, ha], ?_⟩)
    have ha' : (p 0 : ℝ) = 1 := by rw [ha]; rfl
    have hb' : (p 1 : ℝ) = 1 := by rw [hb]; rfl
    rw [fold1, triple_one, ha', hb']
    rw [show (1:ℝ) + 1 * (1 - 1) * (1 * ↑(p 2)) = 1 by ring]
    exact clamp_eq_one_of_one_le le_rfl
  · refine Or.inr (Or.inr ⟨by rw [h0, ha], ?_⟩)
    have ha' : (p 0 : ℝ) = 1 := by rw [ha]; rfl
    have hb' : (p 2 : ℝ) = 1 := by rw [hb]; rfl
    rw [fold1, triple_one, ha', hb']
    rw [show (↑(p 1) : ℝ) + 1 * (1 - ↑(p 1)) * (1 * 1) = 1 by ring]
    exact clamp_eq_one_of_one_le le_rfl

theorem pathSet3_fold2_one {p : IC 3} (h : pathSet2 p) : pathSet3 (fold2 1 p) := by
  have h0 : (fold2 1 p) 0 = p 0 := by rw [fold2, triple_zero]
  have h1 : (fold2 1 p) 1 = p 1 := by rw [fold2, triple_one]
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · refine Or.inl ⟨by rw [h1, ha], ?_⟩
    have hb' : (p 2 : ℝ) = 0 := by rw [hb]; rfl
    rw [fold2, triple_two, hb']
    rw [show (0:ℝ) * (1 - 1 * (↑(p 0) * ↑(p 1))) = 0 by ring]
    exact clamp_eq_zero_of_nonpos le_rfl
  · refine Or.inr ⟨by rw [h0, ha], ?_⟩
    have hb' : (p 2 : ℝ) = 0 := by rw [hb]; rfl
    rw [fold2, triple_two, hb']
    rw [show (0:ℝ) * (1 - 1 * (↑(p 0) * ↑(p 1))) = 0 by ring]
    exact clamp_eq_zero_of_nonpos le_rfl
  · refine Or.inr ⟨by rw [h0, ha], ?_⟩
    have ha' : (p 0 : ℝ) = 1 := by rw [ha]; rfl
    have hb' : (p 1 : ℝ) = 1 := by rw [hb]; rfl
    rw [fold2, triple_two, ha', hb']
    rw [show (↑(p 2) : ℝ) * (1 - 1 * (1 * 1)) = 0 by ring]
    exact clamp_eq_zero_of_nonpos le_rfl

theorem pathSet4_fold3_one {p : IC 3} (h : pathSet3 p) : pathSet4 (fold3 1 p) := by
  have h2 : (fold3 1 p) 2 = p 2 := by rw [fold3, triple_two]
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · refine ⟨?_, by rw [h2, hb]⟩
    have ha' : (p 1 : ℝ) = 0 := by rw [ha]; rfl
    rw [fold3, triple_one, ha']
    rw [show (0:ℝ) * (1 - 1 * ↑(p 0)) = 0 by ring]
    exact clamp_eq_zero_of_nonpos le_rfl
  · refine ⟨?_, by rw [h2, hb]⟩
    have ha' : (p 0 : ℝ) = 1 := by rw [ha]; rfl
    rw [fold3, triple_one, ha']
    rw [show (↑(p 1) : ℝ) * (1 - 1 * 1) = 0 by ring]
    exact clamp_eq_zero_of_nonpos le_rfl

theorem rho_mem_of_tree {p : IC 3} (h : Tree p) (t : ℝ) : Tree (rho t p) := by
  rw [rho]
  by_cases ht1 : t ≤ 1/5
  · rw [if_pos ht1]; exact tree_prune h (5*t)
  · rw [if_neg ht1]
    by_cases ht2 : t ≤ 2/5
    · rw [if_pos ht2]; exact fold1_of_pathSet (pathSet_prune_one h) (5*t-1)
    · rw [if_neg ht2]
      by_cases ht3 : t ≤ 3/5
      · rw [if_pos ht3]
        exact fold2_of_pathSet2 (pathSet2_fold1_one (pathSet_prune_one h)) (5*t-2)
      · rw [if_neg ht3]
        by_cases ht4 : t ≤ 4/5
        · rw [if_pos ht4]
          exact fold3_of_pathSet3
            (pathSet3_fold2_one (pathSet2_fold1_one (pathSet_prune_one h))) (5*t-3)
        · rw [if_neg ht4]
          exact fold4_of_pathSet4
            (pathSet4_fold3_one (pathSet3_fold2_one (pathSet2_fold1_one (pathSet_prune_one h))))
            (5*t-4)

theorem net_rho_one : ∀ p : IC 3, Tree p → rho 1 p = treeRoot := by
  intro p h
  have hq : pathSet4 (fold3 1 (fold2 1 (fold1 1 (prune 1 p)))) :=
    pathSet4_fold3_one (pathSet3_fold2_one (pathSet2_fold1_one (pathSet_prune_one h)))
  obtain ⟨ha, hb⟩ := hq
  rw [rho]
  rw [if_neg (by norm_num : ¬ ((1:ℝ) ≤ 1/5)),
    if_neg (by norm_num : ¬ ((1:ℝ) ≤ 2/5)),
    if_neg (by norm_num : ¬ ((1:ℝ) ≤ 3/5)),
    if_neg (by norm_num : ¬ ((1:ℝ) ≤ 4/5))]
  rw [show (5:ℝ) * 1 - 4 = 1 by norm_num]
  have hc : ((fold3 1 (fold2 1 (fold1 1 (prune 1 p))) 0 : unitInterval) : ℝ) * (1 - 1) = 0 := by
    ring
  funext i
  fin_cases i
  · show (fold4 1 (fold3 1 (fold2 1 (fold1 1 (prune 1 p))))) 0 = treeRoot 0
    rw [fold4, triple_zero, hc, clamp_eq_zero_of_nonpos le_rfl, treeRoot_apply]
  · show (fold4 1 (fold3 1 (fold2 1 (fold1 1 (prune 1 p))))) 1 = treeRoot 1
    rw [fold4, triple_one, ha, treeRoot_apply]
  · show (fold4 1 (fold3 1 (fold2 1 (fold1 1 (prune 1 p))))) 2 = treeRoot 2
    rw [fold4, triple_two, hb, treeRoot_apply]

theorem net_rho_mem : ∀ (t : ℝ) (p : IC 3), Tree p → Tree (rho t p) :=
  fun t _ h => rho_mem_of_tree h t

theorem cellCoord_zero (k : Fin 6) (z : IC 2) :
    ((cellCoord k z 0 : unitInterval) : ℝ) =
      clamp (8 * (z 0 : ℝ) - ((netCellIdx k).1 : ℝ)) := by
  rw [cellCoord_coe]; simp

theorem cellCoord_one (k : Fin 6) (z : IC 2) :
    ((cellCoord k z 1 : unitInterval) : ℝ) =
      clamp (8 * (z 1 : ℝ) - ((netCellIdx k).2 : ℝ)) := by
  rw [cellCoord_coe]; simp

theorem cellRead_val_zero (i j : Fin 8) (y : IC 2) :
    (((cellRead i j) y) 0 : ℝ) = (1:ℝ)/8 * (y 0 : ℝ) + ((i:ℕ):ℝ)/8 := by
  have hy0 : (0:ℝ) ≤ (y 0 : ℝ) ∧ (y 0 : ℝ) ≤ 1 := (y 0).2
  have hi0 : (0:ℝ) ≤ ((i:ℕ):ℝ) := Nat.cast_nonneg _
  have hi7 : ((i:ℕ):ℝ) ≤ 7 := by
    have h : (i:ℕ) ≤ 7 := by have := i.isLt; omega
    exact_mod_cast h
  have hb : (1:ℝ)/8 * (y 0 : ℝ) + ((i:ℕ):ℝ)/8 ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by linarith [hy0.1, hi0], by linarith [hy0.2, hi7]⟩
  have h0 : (((cellRead i j) y) 0 : ℝ) = clamp ((1:ℝ)/8 * (y 0 : ℝ) + ((i:ℕ):ℝ)/8) := rfl
  rw [h0]
  exact clamp_val _ hb

theorem cellRead_val_one (i j : Fin 8) (y : IC 2) :
    (((cellRead i j) y) 1 : ℝ) = (1:ℝ)/8 * (y 1 : ℝ) + ((j:ℕ):ℝ)/8 := by
  have hy1 : (0:ℝ) ≤ (y 1 : ℝ) ∧ (y 1 : ℝ) ≤ 1 := (y 1).2
  have hj0 : (0:ℝ) ≤ ((j:ℕ):ℝ) := Nat.cast_nonneg _
  have hj7 : ((j:ℕ):ℝ) ≤ 7 := by
    have h : (j:ℕ) ≤ 7 := by have := j.isLt; omega
    exact_mod_cast h
  have hb : (1:ℝ)/8 * (y 1 : ℝ) + ((j:ℕ):ℝ)/8 ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by linarith [hy1.1, hj0], by linarith [hy1.2, hj7]⟩
  have h1 : (((cellRead i j) y) 1 : ℝ) = clamp ((1:ℝ)/8 * (y 1 : ℝ) + ((j:ℕ):ℝ)/8) := rfl
  rw [h1]
  exact clamp_val _ hb

theorem net_cellCoord_cellRead (k : Fin 6) (y : IC 2) :
    cellCoord k ((cellRead (netCellIdx k).1 (netCellIdx k).2) y) = y := by
  have h0 : cellCoord k ((cellRead (netCellIdx k).1 (netCellIdx k).2) y) 0 = y 0 := by
    apply Subtype.ext
    rw [cellCoord_zero, cellRead_val_zero]
    rw [show 8 * ((1:ℝ)/8 * (y 0 : ℝ) + ((netCellIdx k).1 : ℝ)/8) - ((netCellIdx k).1 : ℝ)
        = (y 0 : ℝ) by ring]
    exact clamp_val _ (y 0).2
  have h1 : cellCoord k ((cellRead (netCellIdx k).1 (netCellIdx k).2) y) 1 = y 1 := by
    apply Subtype.ext
    rw [cellCoord_one, cellRead_val_one]
    rw [show 8 * ((1:ℝ)/8 * (y 1 : ℝ) + ((netCellIdx k).2 : ℝ)/8) - ((netCellIdx k).2 : ℝ)
        = (y 1 : ℝ) by ring]
    exact clamp_val _ (y 1).2
  funext c
  rcases (show c = 0 ∨ c = 1 from by fin_cases c <;> simp) with h | h
  · rw [h]; exact h0
  · rw [h]; exact h1

/-! ### The readings on the boundary of the square -/

theorem faceFun_self (i : Fin 3) (b : unitInterval) (t : IC 2) : faceFun i b t i = b := by
  rw [faceFun_apply, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same]

theorem faceFun_succAbove (i : Fin 3) (b : unitInterval) (t : IC 2) (j : Fin 2) :
    faceFun i b t (i.succAbove j) = t j := by
  rw [faceFun_apply, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_succAbove]

theorem skel_faceIncl_of (i : Fin 3) (b : Fin 2) (t : IC 2) (j : Fin 2)
    (h : t j = 0 ∨ t j = 1) : Skel3 ((faceIncl i b) t) := by
  have hsame : ((faceIncl i b) t).1 i = bval b := by
    show faceFun i (bval b) t i = bval b
    exact faceFun_self i (bval b) t
  have hother : ((faceIncl i b) t).1 (i.succAbove j) = t j := by
    show faceFun i (bval b) t (i.succAbove j) = t j
    exact faceFun_succAbove i (bval b) t j
  rcases h with h | h
  · exact ⟨i, i.succAbove j, Fin.ne_succAbove i j, b, 0, hsame, by rw [hother, h]; rfl⟩
  · exact ⟨i, i.succAbove j, Fin.ne_succAbove i j, b, 1, hsame, by rw [hother, h]; rfl⟩

theorem skel_readMap (i : Fin 3) (b : Fin 2) (α a β c : ℝ) (z : IC 2)
    (ha : clamp a = 0 ∨ clamp a = 1) (ha' : clamp (α + a) = 0 ∨ clamp (α + a) = 1)
    (hc : clamp c = 0 ∨ clamp c = 1) (hc' : clamp (β + c) = 0 ∨ clamp (β + c) = 1)
    (h : z 0 = 0 ∨ z 0 = 1 ∨ z 1 = 0 ∨ z 1 = 1) :
    Skel3 (((faceIncl i b).comp (readMap α a β c)) z) := by
  have h0 : (z 0 : ℝ) = 0 ∨ (z 0 : ℝ) = 1 ∨ (z 1 : ℝ) = 0 ∨ (z 1 : ℝ) = 1 := by
    rcases h with h | h | h | h
    · exact Or.inl (by rw [h]; rfl)
    · exact Or.inr (Or.inl (by rw [h]; rfl))
    · exact Or.inr (Or.inr (Or.inl (by rw [h]; rfl)))
    · exact Or.inr (Or.inr (Or.inr (by rw [h]; rfl)))
  rcases h0 with h0 | h0 | h0 | h0
  · refine skel_faceIncl_of i b (readMap α a β c z) 0 ?_
    rw [readMap_apply_zero, h0, show α * 0 + a = a by ring]
    exact ha
  · refine skel_faceIncl_of i b (readMap α a β c z) 0 ?_
    rw [readMap_apply_zero, h0, show α * 1 + a = α + a by ring]
    exact ha'
  · refine skel_faceIncl_of i b (readMap α a β c z) 1 ?_
    rw [readMap_apply_one, h0, show β * 0 + c = c by ring]
    exact hc
  · refine skel_faceIncl_of i b (readMap α a β c z) 1 ?_
    rw [readMap_apply_one, h0, show β * 1 + c = β + c by ring]
    exact hc'

theorem skel_readSwap (i : Fin 3) (b : Fin 2) (α a β c : ℝ) (z : IC 2)
    (ha : clamp a = 0 ∨ clamp a = 1) (ha' : clamp (α + a) = 0 ∨ clamp (α + a) = 1)
    (hc : clamp c = 0 ∨ clamp c = 1) (hc' : clamp (β + c) = 0 ∨ clamp (β + c) = 1)
    (h : z 0 = 0 ∨ z 0 = 1 ∨ z 1 = 0 ∨ z 1 = 1) :
    Skel3 (((faceIncl i b).comp (readSwap α a β c)) z) := by
  have h0 : (z 0 : ℝ) = 0 ∨ (z 0 : ℝ) = 1 ∨ (z 1 : ℝ) = 0 ∨ (z 1 : ℝ) = 1 := by
    rcases h with h | h | h | h
    · exact Or.inl (by rw [h]; rfl)
    · exact Or.inr (Or.inl (by rw [h]; rfl))
    · exact Or.inr (Or.inr (Or.inl (by rw [h]; rfl)))
    · exact Or.inr (Or.inr (Or.inr (by rw [h]; rfl)))
  rcases h0 with h0 | h0 | h0 | h0
  · refine skel_faceIncl_of i b (readSwap α a β c z) 1 ?_
    rw [readSwap_apply_one, h0, show α * 0 + a = a by ring]
    exact ha
  · refine skel_faceIncl_of i b (readSwap α a β c z) 1 ?_
    rw [readSwap_apply_one, h0, show α * 1 + a = α + a by ring]
    exact ha'
  · refine skel_faceIncl_of i b (readSwap α a β c z) 0 ?_
    rw [readSwap_apply_zero, h0, show β * 0 + c = c by ring]
    exact hc
  · refine skel_faceIncl_of i b (readSwap α a β c z) 0 ?_
    rw [readSwap_apply_zero, h0, show β * 1 + c = β + c by ring]
    exact hc'

theorem netRead_mem_skel (k : Fin 6) (z : IC 2) (hz : z ∈ Cube.boundary (Fin 2)) :
    Skel3 (netRead k z) := by
  have hb : z 0 = 0 ∨ z 0 = 1 ∨ z 1 = 0 ∨ z 1 = 1 := by
    obtain ⟨c, hc⟩ := hz
    rcases (show c = 0 ∨ c = 1 from by fin_cases c <;> simp) with hc0 | hc0
    · rw [hc0] at hc
      rcases hc with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rw [hc0] at hc
      rcases hc with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  fin_cases k
  · exact skel_readMap 1 1 (-8) 3 8 (-3) z
      (Or.inr (clamp_eq_one_of_one_le (by norm_num)))
      (Or.inl (clamp_eq_zero_of_nonpos (by norm_num)))
      (Or.inl (clamp_eq_zero_of_nonpos (by norm_num)))
      (Or.inr (clamp_eq_one_of_one_le (by norm_num))) hb
  · exact skel_readMap 0 0 (-8) 4 8 (-3) z
      (Or.inr (clamp_eq_one_of_one_le (by norm_num)))
      (Or.inl (clamp_eq_zero_of_nonpos (by norm_num)))
      (Or.inl (clamp_eq_zero_of_nonpos (by norm_num)))
      (Or.inr (clamp_eq_one_of_one_le (by norm_num))) hb
  · exact skel_readMap 1 0 8 (-4) 8 (-3) z
      (Or.inl (clamp_eq_zero_of_nonpos (by norm_num)))
      (Or.inr (clamp_eq_one_of_one_le (by norm_num)))
      (Or.inl (clamp_eq_zero_of_nonpos (by norm_num)))
      (Or.inr (clamp_eq_one_of_one_le (by norm_num))) hb
  · exact skel_readMap 0 1 8 (-5) 8 (-3) z
      (Or.inl (clamp_eq_zero_of_nonpos (by norm_num)))
      (Or.inr (clamp_eq_one_of_one_le (by norm_num)))
      (Or.inl (clamp_eq_zero_of_nonpos (by norm_num)))
      (Or.inr (clamp_eq_one_of_one_le (by norm_num))) hb
  · exact skel_readSwap 2 0 (-8) 4 (-8) 3 z
      (Or.inr (clamp_eq_one_of_one_le (by norm_num)))
      (Or.inl (clamp_eq_zero_of_nonpos (by norm_num)))
      (Or.inr (clamp_eq_one_of_one_le (by norm_num)))
      (Or.inl (clamp_eq_zero_of_nonpos (by norm_num))) hb
  · exact skel_readSwap 2 1 (-8) 4 8 (-4) z
      (Or.inr (clamp_eq_one_of_one_le (by norm_num)))
      (Or.inl (clamp_eq_zero_of_nonpos (by norm_num)))
      (Or.inl (clamp_eq_zero_of_nonpos (by norm_num)))
      (Or.inr (clamp_eq_one_of_one_le (by norm_num))) hb

theorem cellCoord_mem_boundary {k : Fin 6} {z : IC 2} (hk : z ∈ netCell k)
    (hno : z ∉ openNetCell k) : cellCoord k z ∈ Cube.boundary (Fin 2) := by
  have hgr : z ∈ gridCell (netCellIdx k).1 (netCellIdx k).2 := by
    rwa [show netCell k = gridCell (netCellIdx k).1 (netCellIdx k).2 from by
      fin_cases k <;> rfl] at hk
  simp only [gridCell, Set.mem_ofPred_eq] at hgr
  obtain ⟨hz0a, hz0b, hz1a, hz1b⟩ := hgr
  have hc0 := cellCoord_zero k z
  have hc1 := cellCoord_one k z
  rcases lt_or_ge (((netCellIdx k).1 : ℝ)/8) (z 0 : ℝ) with hlt | hle
  · rcases lt_or_ge (z 0 : ℝ) ((((netCellIdx k).1 : ℝ)+1)/8) with hlt2 | hle2
    · -- the first coordinate is strictly inside the cell
      have hnot : ¬ (((netCellIdx k).2 : ℝ)/8 < (z 1 : ℝ) ∧
          (z 1 : ℝ) < (((netCellIdx k).2 : ℝ)+1)/8) := by
        intro hh
        exact hno (by
          simp only [openNetCell, openCube, Set.mem_ofPred_eq]
          exact ⟨hlt, hlt2, hh.1, hh.2⟩)
      rcases lt_or_ge (((netCellIdx k).2 : ℝ)/8) (z 1 : ℝ) with hlt3 | hle3
      · rcases lt_or_ge (z 1 : ℝ) ((((netCellIdx k).2 : ℝ)+1)/8) with hlt4 | hle4
        · exact absurd ⟨hlt3, hlt4⟩ hnot
        · have hz : (z 1 : ℝ) = (((netCellIdx k).2 : ℝ)+1)/8 := le_antisymm hz1b hle4
          refine ⟨1, Or.inr ?_⟩
          apply Subtype.ext
          rw [hc1, hz,
            show 8 * ((((netCellIdx k).2 : ℝ)+1)/8) - ((netCellIdx k).2 : ℝ) = 1 by ring]
          exact clamp_val 1 ⟨by norm_num, le_refl 1⟩
      · have hz : (z 1 : ℝ) = ((netCellIdx k).2 : ℝ)/8 := le_antisymm hle3 hz1a
        refine ⟨1, Or.inl ?_⟩
        apply Subtype.ext
        rw [hc1, hz, show 8 * (((netCellIdx k).2 : ℝ)/8) - ((netCellIdx k).2 : ℝ) = 0 by ring]
        exact clamp_val 0 ⟨le_refl 0, by norm_num⟩
    · -- the first coordinate is the right end of the cell
      have hz : (z 0 : ℝ) = (((netCellIdx k).1 : ℝ)+1)/8 := le_antisymm hz0b hle2
      refine ⟨0, Or.inr ?_⟩
      apply Subtype.ext
      rw [hc0, hz,
        show 8 * ((((netCellIdx k).1 : ℝ)+1)/8) - ((netCellIdx k).1 : ℝ) = 1 by ring]
      exact clamp_val 1 ⟨by norm_num, le_refl 1⟩
  · -- the first coordinate is the left end of the cell
    have hz : (z 0 : ℝ) = ((netCellIdx k).1 : ℝ)/8 := le_antisymm hle hz0a
    refine ⟨0, Or.inl ?_⟩
    apply Subtype.ext
    rw [hc0, hz, show 8 * (((netCellIdx k).1 : ℝ)/8) - ((netCellIdx k).1 : ℝ) = 0 by ring]
    exact clamp_val 0 ⟨le_refl 0, by norm_num⟩

theorem net_readExt_skel_cell (k : Fin 6) (z : IC 2) (hk : z ∈ netCell k)
    (hno : z ∉ openNetCell k) : Skel3 (readExt k z) :=
  netRead_mem_skel k (cellCoord k z) (cellCoord_mem_boundary hk hno)

/-! ## Bundled forms of the finite facts -/

/-- The six readings agree on the overlaps of the net cells. -/
def AgreeReads : Prop :=
  ∀ (y : IC 2) (k l : Fin 6), y ∈ netCell k → y ∈ netCell l → readExt k y = readExt l y

/-- The contraction `rho` preserves the tree. -/
def MemTree : Prop := ∀ (t : ℝ) (p : IC 3), Tree p → Tree (rho t p)

/-- At time `1` the contraction has reached the base vertex. -/
def RhoOne : Prop := ∀ p : IC 3, Tree p → rho 1 p = treeRoot

/-- The clamped cell coordinates invert the cell reading. -/
def CellReadCoord : Prop := ∀ (k : Fin 6) (y : IC 2),
  cellCoord k ((cellRead (netCellIdx k).1 (netCellIdx k).2) y) = y

/-- A point of a net cell on the boundary of its cell reads into the `1`-skeleton. -/
def ReadSkel : Prop := ∀ (k : Fin 6) (z : IC 2), z ∈ netCell k → z ∉ openNetCell k →
  Skel3 (readExt k z)

/-! ## Closedness of the net region and its pieces -/

theorem continuous_coe (i : Fin 2) : Continuous fun z : IC 2 => ((z i : unitInterval) : ℝ) :=
  continuous_subtype_val.comp (continuous_apply i)

theorem isClosed_gridCell (i j : ℕ) : IsClosed (gridCell i j) := by
  have h : gridCell i j =
      ({y : IC 2 | (i:ℝ)/8 ≤ (y 0 : ℝ)} ∩ {y : IC 2 | (y 0 : ℝ) ≤ ((i:ℝ)+1)/8} ∩
       {y : IC 2 | (j:ℝ)/8 ≤ (y 1 : ℝ)}) ∩ {y : IC 2 | (y 1 : ℝ) ≤ ((j:ℝ)+1)/8} := by
    ext y
    simp only [gridCell, Set.mem_ofPred_eq, Set.mem_inter_iff]
    tauto
  rw [h]
  exact IsClosed.inter (IsClosed.inter (IsClosed.inter
    (isClosed_le continuous_const (continuous_coe 0))
    (isClosed_le (continuous_coe 0) continuous_const))
    (isClosed_le continuous_const (continuous_coe 1)))
    (isClosed_le (continuous_coe 1) continuous_const)

theorem isClosed_netCell (k : Fin 6) : IsClosed (netCell k) := by
  have h : netCell k = gridCell (netCellIdx k).1 (netCellIdx k).2 := by fin_cases k <;> rfl
  rw [h]
  exact isClosed_gridCell _ _

theorem isClosed_NetRegion : IsClosed NetRegion := by
  rw [show NetRegion = ⋃ k : Fin 6, netCell k from rfl]
  exact isClosed_iUnion_of_finite fun k => isClosed_netCell k

/-- The complement of the interior of the net region. -/
def OutSide : Set (IC 2) := {y | y ∉ interior NetRegion}

theorem isClosed_OutSide : IsClosed OutSide := by
  rw [OutSide]
  exact isClosed_compl_iff.mpr isOpen_interior

theorem mem_OutSide {y : IC 2} : y ∈ OutSide ↔ y ∉ interior NetRegion := Iff.rfl

theorem mem_NetBdy {y : IC 2} : y ∈ NetBdy ↔ y ∈ NetRegion ∧ y ∉ interior NetRegion :=
  Set.mem_sdiff y

/-! ## The offset of a point outside the interior of the net region -/

theorem offOf_ne_zero_of_notMem_interior {y : IC 2} (hy : y ∉ interior NetRegion) :
    offOf y ≠ 0 :=
  fun h => hy ((offOf_eq_zero_iff.mp h).symm ▸ netCentre_mem_interior)

theorem continuousOn_radialPoint_offOf :
    ContinuousOn (fun y : IC 2 => radialPoint (offOf y)) {y : IC 2 | offOf y ≠ 0} := by
  have hz : ContinuousOn (fun y : IC 2 => offOf y) {y : IC 2 | offOf y ≠ 0} :=
    (continuous_pi (fun i => continuous_offOf i)).continuousOn
  have h1 : ContinuousOn (fun y : IC 2 => exitScale (offOf y)) {y : IC 2 | offOf y ≠ 0} :=
    continuousOn_exitScale.comp hz (fun y hy => hy)
  have h2 : ContinuousOn (fun y : IC 2 => rayOff (offOf y)) {y : IC 2 | offOf y ≠ 0} := by
    have h3 : ContinuousOn (fun y : IC 2 => fun i => exitScale (offOf y) * offOf y i)
        {y : IC 2 | offOf y ≠ 0} := by
      refine continuousOn_pi.mpr fun i => ?_
      exact h1.mul (continuous_offOf i).continuousOn
    convert h3 using 2
    funext i
    rfl
  exact continuous_ptOf.continuousOn.comp h2 (fun y _ => Set.mem_univ _)

/-! ## The reading half of the model -/

/-- A net cell containing a point of the net region. -/
noncomputable def cellOf (y : IC 2) (hy : y ∈ NetRegion) : Fin 6 :=
  Classical.choose (Set.mem_iUnion.mp hy)

theorem cellOf_mem (y : IC 2) (hy : y ∈ NetRegion) : y ∈ netCell (cellOf y hy) :=
  Classical.choose_spec (Set.mem_iUnion.mp hy)

/-- On the net region: the reading of a containing cell. -/
noncomputable def psiDFun (y : IC 2) : Bdy3 :=
  if h : y ∈ NetRegion then readExt (cellOf y h) y else vertexBdy3

theorem psiDFun_eq (h_agree : AgreeReads) {y : IC 2} (hy : y ∈ NetRegion) {k : Fin 6}
    (hk : y ∈ netCell k) : psiDFun y = readExt k y := by
  show (if h : y ∈ NetRegion then readExt (cellOf y h) y else vertexBdy3) = readExt k y
  rw [dif_pos hy]
  exact h_agree y _ k (cellOf_mem y hy) hk

theorem continuousOn_psiDFun (h_agree : AgreeReads) : ContinuousOn psiDFun NetRegion := by
  rw [show NetRegion = ⋃ k : Fin 6, netCell k from rfl]
  refine LocallyFinite.continuousOn_iUnion (locallyFinite_of_finite netCell)
    (fun k => isClosed_netCell k) (fun k => ?_)
  refine ContinuousOn.congr (continuous_readExt k).continuousOn (fun y hy => ?_)
  exact psiDFun_eq h_agree (Set.mem_iUnion.mpr ⟨k, hy⟩) hy

/-! ## The walk on the boundary of the net region -/

/-- The walk value on `∂D`: the common reading of the net cells containing the point. -/
noncomputable def walk (h_agree : AgreeReads) : C(↥NetBdy, Bdy3) where
  toFun p := psiDFun (p : IC 2)
  continuous_toFun := by
    show Continuous ((fun y : IC 2 => psiDFun y) ∘ (Subtype.val : ↥NetBdy → IC 2))
    exact (continuousOn_psiDFun h_agree).comp_continuous continuous_subtype_val
      (fun p => (mem_NetBdy.mp p.2).1)

theorem walk_apply (h_agree : AgreeReads) (p : ↥NetBdy) :
    walk h_agree p = psiDFun (p : IC 2) := rfl

theorem walk_tree (h_agree : AgreeReads) (p : ↥NetBdy) : Tree ((walk h_agree p).1) := by
  obtain ⟨hpReg, hpOut⟩ := mem_NetBdy.mp p.2
  have h1 : walk h_agree p = readExt (cellOf (p : IC 2) hpReg) (p : IC 2) := by
    rw [walk_apply]
    exact psiDFun_eq h_agree hpReg (cellOf_mem (p : IC 2) hpReg)
  rw [show (walk h_agree p).1 = (readExt (cellOf (p : IC 2) hpReg) (p : IC 2)).1
    from congrArg Subtype.val h1]
  exact net_readExt_tree (cellOf_mem (p : IC 2) hpReg) hpOut

/-! ## The collar half of the model -/

/-- Off the interior of the net region: contract the walk value at the radial exit point. -/
noncomputable def psiCFun (h_agree : AgreeReads) (h_mem : MemTree) (y : IC 2) : Bdy3 :=
  if hy : y ∉ interior NetRegion then
    (⟨rho (tau y) (walk h_agree ⟨radialPoint (offOf y), net_exit_mem_bdy hy⟩).1,
      Tree_boundary (h_mem (tau y) _
        (walk_tree h_agree ⟨radialPoint (offOf y), net_exit_mem_bdy hy⟩))⟩ : Bdy3)
  else vertexBdy3

theorem psiCFun_eq (h_agree : AgreeReads) (h_mem : MemTree) {y : IC 2}
    (hy : y ∉ interior NetRegion) :
    psiCFun h_agree h_mem y =
      (⟨rho (tau y) (walk h_agree ⟨radialPoint (offOf y), net_exit_mem_bdy hy⟩).1,
        Tree_boundary (h_mem (tau y) _
          (walk_tree h_agree ⟨radialPoint (offOf y), net_exit_mem_bdy hy⟩))⟩ : Bdy3) := by
  unfold psiCFun
  rw [dif_pos hy]

theorem continuous_psiCFun_subtype (h_agree : AgreeReads) (h_mem : MemTree) :
    Continuous (OutSide.domRestrict (psiCFun h_agree h_mem)) := by
  show Continuous fun p : ↥OutSide => psiCFun h_agree h_mem (p : IC 2)
  have hrad : Continuous (OutSide.domRestrict (fun y : IC 2 => radialPoint (offOf y))) :=
    (continuousOn_radialPoint_offOf.mono
      (fun y hy => offOf_ne_zero_of_notMem_interior hy)).domRestrict
  have hR : Continuous fun p : ↥OutSide =>
      (⟨radialPoint (offOf (p : IC 2)), net_exit_mem_bdy p.2⟩ : ↥NetBdy) :=
    Continuous.subtype_mk hrad (fun p => net_exit_mem_bdy p.2)
  have hwalk : Continuous fun p : ↥OutSide =>
      walk h_agree ⟨radialPoint (offOf (p : IC 2)), net_exit_mem_bdy p.2⟩ :=
    (walk h_agree).continuous.comp hR
  have htau : Continuous fun p : ↥OutSide => tau (p : IC 2) :=
    (continuousOn_tau.mono (fun y hy => offOf_ne_zero_of_notMem_interior hy)).domRestrict
  have hcore : Continuous fun p : ↥OutSide =>
      rho (tau (p : IC 2)) (walk h_agree ⟨radialPoint (offOf (p : IC 2)),
        net_exit_mem_bdy p.2⟩).1 :=
    net_rho_continuous.comp (htau.prodMk (continuous_subtype_val.comp hwalk))
  have hg : Continuous fun p : ↥OutSide =>
      (⟨rho (tau (p : IC 2)) (walk h_agree ⟨radialPoint (offOf (p : IC 2)),
          net_exit_mem_bdy p.2⟩).1,
        Tree_boundary (h_mem (tau (p : IC 2)) _
          (walk_tree h_agree ⟨radialPoint (offOf (p : IC 2)), net_exit_mem_bdy p.2⟩))⟩ : Bdy3) :=
    Continuous.subtype_mk hcore (fun p => Tree_boundary (h_mem (tau (p : IC 2)) _
      (walk_tree h_agree ⟨radialPoint (offOf (p : IC 2)), net_exit_mem_bdy p.2⟩)))
  refine hg.congr (fun p => ?_)
  exact (psiCFun_eq h_agree h_mem p.2).symm

theorem continuousOn_psiCFun (h_agree : AgreeReads) (h_mem : MemTree) :
    ContinuousOn (psiCFun h_agree h_mem) OutSide :=
  continuousOn_iff_continuous_domRestrict.mpr (continuous_psiCFun_subtype h_agree h_mem)

/-! ## The two halves agree on `∂D` -/

theorem psiDFun_eq_psiCFun (h_agree : AgreeReads) (h_mem : MemTree) {y : IC 2}
    (hy : y ∈ NetBdy) : psiDFun y = psiCFun h_agree h_mem y := by
  obtain ⟨hyReg, hyOut⟩ := mem_NetBdy.mp hy
  have hk : y ∈ netCell (cellOf y hyReg) := cellOf_mem y hyReg
  rw [psiDFun_eq h_agree hyReg hk, psiCFun_eq h_agree h_mem hyOut]
  apply Subtype.ext
  show (readExt (cellOf y hyReg) y).1 =
    rho (tau y) (walk h_agree ⟨radialPoint (offOf y), net_exit_mem_bdy hyOut⟩).1
  have hpt : (⟨radialPoint (offOf y), net_exit_mem_bdy hyOut⟩ : ↥NetBdy) = ⟨y, hy⟩ :=
    Subtype.ext (net_exit_self hy)
  have hwalk : walk h_agree ⟨y, hy⟩ = readExt (cellOf y hyReg) y := by
    rw [walk_apply]
    exact psiDFun_eq h_agree hyReg hk
  rw [hpt, tau_eq_zero hy, net_rho_zero (walk_tree h_agree ⟨y, hy⟩), hwalk]

/-! ## The assembled model -/

/-- The pinched model of `∂I³`, assembled from the two halves. -/
noncomputable def psiFun (h_agree : AgreeReads) (h_mem : MemTree) (y : IC 2) : Bdy3 :=
  if y ∈ NetRegion then psiDFun y else psiCFun h_agree h_mem y

theorem psiFun_eq_left (h_agree : AgreeReads) (h_mem : MemTree) {y : IC 2} (hy : y ∈ NetRegion) :
    psiFun h_agree h_mem y = psiDFun y := by
  unfold psiFun
  rw [if_pos hy]

theorem psiFun_eq_right (h_agree : AgreeReads) (h_mem : MemTree) {y : IC 2} (hy : y ∉ NetRegion) :
    psiFun h_agree h_mem y = psiCFun h_agree h_mem y := by
  unfold psiFun
  rw [if_neg hy]

theorem continuous_psiFun (h_agree : AgreeReads) (h_mem : MemTree) :
    Continuous (psiFun h_agree h_mem) := by
  rw [← continuousOn_univ]
  rw [show (Set.univ : Set (IC 2)) = NetRegion ∪ OutSide from by
    ext y
    constructor
    · intro _
      by_cases h : y ∈ NetRegion
      · exact Or.inl h
      · exact Or.inr (mem_OutSide.mpr (fun hc => h (interior_subset hc)))
    · intro _; exact trivial]
  rw [continuousOn_union_iff_of_isClosed isClosed_NetRegion isClosed_OutSide]
  refine ⟨?_, ?_⟩
  · refine ContinuousOn.congr (continuousOn_psiDFun h_agree) (fun y hy => ?_)
    exact psiFun_eq_left h_agree h_mem hy
  · refine ContinuousOn.congr (continuousOn_psiCFun h_agree h_mem) (fun y hy => ?_)
    by_cases hyReg : y ∈ NetRegion
    · rw [psiFun_eq_left h_agree h_mem hyReg]
      exact psiDFun_eq_psiCFun h_agree h_mem (mem_NetBdy.mpr ⟨hyReg, mem_OutSide.mp hy⟩)
    · exact psiFun_eq_right h_agree h_mem hyReg

/-! ## The three properties -/

theorem not_mem_NetRegion_of_boundary {y : IC 2} (hy : y ∈ Cube.boundary (Fin 2)) :
    y ∉ NetRegion := by
  intro h
  obtain ⟨h1, h2, h3, h4⟩ := net_region_bounds h
  obtain ⟨i, hi⟩ := hy
  have hcoe0 : ∀ u : unitInterval, u = 0 → (u : ℝ) = 0 := by intro u hu; rw [hu]; norm_num
  have hcoe1 : ∀ u : unitInterval, u = 1 → (u : ℝ) = 1 := by intro u hu; rw [hu]; norm_num
  rcases (show i = 0 ∨ i = 1 from by fin_cases i <;> simp) with hi0 | hi0
  · rw [hi0] at hi
    rcases hi with h' | h'
    · linarith [hcoe0 _ h', h1]
    · linarith [hcoe1 _ h', h2]
  · rw [hi0] at hi
    rcases hi with h' | h'
    · linarith [hcoe0 _ h', h3]
    · linarith [hcoe1 _ h', h4]

theorem treeRoot_eq_zero : treeRoot = (0 : IC 3) := by
  funext i
  fin_cases i <;> rfl

theorem psiFun_boundary (h_agree : AgreeReads) (h_mem : MemTree) (h_one : RhoOne) {y : IC 2}
    (hy : y ∈ Cube.boundary (Fin 2)) : psiFun h_agree h_mem y = vertexBdy3 := by
  have hyNotReg : y ∉ NetRegion := not_mem_NetRegion_of_boundary hy
  have hyOut : y ∉ interior NetRegion := fun h => hyNotReg (interior_subset h)
  rw [psiFun_eq_right h_agree h_mem hyNotReg, psiCFun_eq h_agree h_mem hyOut]
  apply Subtype.ext
  show rho (tau y) (walk h_agree ⟨radialPoint (offOf y), net_exit_mem_bdy hyOut⟩).1 = (0 : IC 3)
  rw [← treeRoot_eq_zero,
    tau_eq_one hy,
    h_one _ (walk_tree h_agree ⟨radialPoint (offOf y), net_exit_mem_bdy hyOut⟩)]

theorem cellRead_mem_gridCell (i j : Fin 8) (y : IC 2) :
    (cellRead i j) y ∈ gridCell (i : ℕ) (j : ℕ) := by
  have h0 : (((cellRead i j) y) 0 : ℝ) = clamp ((1:ℝ)/8 * (y 0 : ℝ) + ((i:ℕ):ℝ)/8) := rfl
  have h1 : (((cellRead i j) y) 1 : ℝ) = clamp ((1:ℝ)/8 * (y 1 : ℝ) + ((j:ℕ):ℝ)/8) := rfl
  have hy0 : (0:ℝ) ≤ (y 0 : ℝ) ∧ (y 0 : ℝ) ≤ 1 := (y 0).2
  have hy1 : (0:ℝ) ≤ (y 1 : ℝ) ∧ (y 1 : ℝ) ≤ 1 := (y 1).2
  have hi0 : (0:ℝ) ≤ ((i:ℕ):ℝ) := Nat.cast_nonneg _
  have hj0 : (0:ℝ) ≤ ((j:ℕ):ℝ) := Nat.cast_nonneg _
  have hi7 : ((i:ℕ):ℝ) ≤ 7 := by
    have h : (i:ℕ) ≤ 7 := by have := i.isLt; omega
    exact_mod_cast h
  have hj7 : ((j:ℕ):ℝ) ≤ 7 := by
    have h : (j:ℕ) ≤ 7 := by have := j.isLt; omega
    exact_mod_cast h
  have hb0 : (1:ℝ)/8 * (y 0 : ℝ) + ((i:ℕ):ℝ)/8 ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by linarith [hy0.1, hi0], by linarith [hy0.2, hi7]⟩
  have hb1 : (1:ℝ)/8 * (y 1 : ℝ) + ((j:ℕ):ℝ)/8 ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by linarith [hy1.1, hj0], by linarith [hy1.2, hj7]⟩
  have hv0 : (((cellRead i j) y) 0 : ℝ) = (1:ℝ)/8 * (y 0 : ℝ) + ((i:ℕ):ℝ)/8 := by
    rw [h0, clamp_val _ hb0]
  have hv1 : (((cellRead i j) y) 1 : ℝ) = (1:ℝ)/8 * (y 1 : ℝ) + ((j:ℕ):ℝ)/8 := by
    rw [h1, clamp_val _ hb1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hv0]; linarith [hy0.1]
  · rw [hv0]; linarith [hy0.2]
  · rw [hv1]; linarith [hy1.1]
  · rw [hv1]; linarith [hy1.2]

theorem cellRead_mem_netCell (k : Fin 6) (y : IC 2) :
    (cellRead (netCellIdx k).1 (netCellIdx k).2) y ∈ netCell k := by
  rw [show netCell k = gridCell (netCellIdx k).1 (netCellIdx k).2 from by fin_cases k <;> rfl]
  exact cellRead_mem_gridCell (netCellIdx k).1 (netCellIdx k).2 y

theorem psiFun_comp_cellRead (h_agree : AgreeReads) (h_mem : MemTree) (h_cc : CellReadCoord)
    (k : Fin 6) (y : IC 2) :
    psiFun h_agree h_mem ((cellRead (netCellIdx k).1 (netCellIdx k).2) y) = netRead k y := by
  have hmem : (cellRead (netCellIdx k).1 (netCellIdx k).2) y ∈ netCell k :=
    cellRead_mem_netCell k y
  rw [psiFun_eq_left h_agree h_mem (Set.mem_iUnion.mpr ⟨k, hmem⟩),
    psiDFun_eq h_agree (Set.mem_iUnion.mpr ⟨k, hmem⟩) hmem]
  show netRead k (cellCoord k ((cellRead (netCellIdx k).1 (netCellIdx k).2) y)) = netRead k y
  rw [h_cc]

theorem psiFun_collar (h_agree : AgreeReads) (h_mem : MemTree) (h_skel : ReadSkel) {y : IC 2}
    (hy : y ∈ Collar) : Skel3 (psiFun h_agree h_mem y) := by
  by_cases hyReg : y ∈ NetRegion
  · have hk : y ∈ netCell (cellOf y hyReg) := cellOf_mem y hyReg
    have hno : y ∉ openNetCell (cellOf y hyReg) := (mem_Collar.mp hy) _
    rw [psiFun_eq_left h_agree h_mem hyReg, psiDFun_eq h_agree hyReg hk]
    exact h_skel _ _ hk hno
  · have hyOut : y ∉ interior NetRegion := fun h => hyReg (interior_subset h)
    rw [psiFun_eq_right h_agree h_mem hyReg, psiCFun_eq h_agree h_mem hyOut]
    exact Tree_skel (h_mem (tau y) _
      (walk_tree h_agree ⟨radialPoint (offOf y), net_exit_mem_bdy hyOut⟩))

/-! ## Assembly -/

theorem net_model_aux (h_agree : AgreeReads) (h_one : RhoOne) (h_mem : MemTree)
    (h_cc : CellReadCoord) (h_skel : ReadSkel) :
    ∃ ψ : ContinuousMap (IC 2) Bdy3,
      (∀ y ∈ Cube.boundary (Fin 2), ψ y = vertexBdy3) ∧
      (∀ (k : Fin 6) (y : IC 2),
        ψ ((cellRead (netCellIdx k).1 (netCellIdx k).2) y) = netRead k y) ∧
      (∀ y ∈ Collar, Skel3 (ψ y)) := by
  refine ⟨⟨psiFun h_agree h_mem, continuous_psiFun h_agree h_mem⟩, ?_, ?_, ?_⟩
  · intro y hy; exact psiFun_boundary h_agree h_mem h_one hy
  · intro k y; exact psiFun_comp_cellRead h_agree h_mem h_cc k y
  · intro y hy; exact psiFun_collar h_agree h_mem h_skel hy

theorem net_model :
    ∃ ψ : ContinuousMap (Work.Stems.Cubical.IC 2) Work.Stems.Hur2b.Bdy3,
      (∀ y ∈ Cube.boundary (Fin 2), ψ y = Work.Stems.Hur2b.vertexBdy3) ∧
      (∀ (k : Fin 6) (y : Work.Stems.Cubical.IC 2),
        ψ ((Work.Stems.Hur2b.cellRead (Work.Stems.Hur2b.netCellIdx k).1
              (Work.Stems.Hur2b.netCellIdx k).2) y) = Work.Stems.Hur2b.netRead k y) ∧
      (∀ y ∈ Work.Stems.Hur2b.Collar, Work.Stems.Hur2b.Skel3 (ψ y)) :=
  net_model_aux net_readExt_agree net_rho_one net_rho_mem net_cellCoord_cellRead
    net_readExt_skel_cell

end

end Work.Stems.Hur2b
