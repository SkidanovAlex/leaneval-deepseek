import Mathlib
import Submission.Work.Stems.Hur2b.NetTree

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Continuity of the tree contraction `rho`

`Work.Stems.Hur2b.rho : ℝ → IC 3 → IC 3` is the contraction of the tree of the walk to the base
vertex `(0,0,0)`, assembled from the five maps `prune`, `fold1`, …, `fold4` on the five consecutive
time intervals `[0,1/5]`, `[1/5,2/5]`, …, `[4/5,1]`.  This file proves that `rho`, as a map
`ℝ × IC 3 → IC 3`, is continuous.

Each of the five pieces is a composition of continuous maps (`clamp`, the coordinate projections,
and affine functions of `t`), and consecutive pieces agree on the shared endpoint: at `t = k/5`
the `k`-th folding map is evaluated at `0` (respectively the `(k+1)`-th at `1`, which is the value
already reached), where `foldᵢ 0` is the identity.  Continuity is then obtained by four applications
of the pasting lemma `Continuous.if_le`.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2b

open Work.Stems.Cubical Work.Stems.Hur2

noncomputable section

/-! ## The endpoint identities `foldᵢ 0 = id` -/

theorem fold1_zero (p : IC 3) : fold1 0 p = p := by
  unfold fold1
  rw [show (0:ℝ) * (1 - (p 1 : ℝ)) * ((p 0 : ℝ) * (p 2 : ℝ)) = 0 by ring, add_zero]
  have hcl : clamp (p 1 : ℝ) = p 1 := by rw [clamp]; exact clamp_of_mem (p 1).2
  rw [hcl]; exact triple_eta' p

theorem fold2_zero (p : IC 3) : fold2 0 p = p := by
  unfold fold2
  rw [show (0:ℝ) * ((p 0 : ℝ) * (p 1 : ℝ)) = 0 by ring, sub_zero, mul_one]
  have hcl : clamp (p 2 : ℝ) = p 2 := by rw [clamp]; exact clamp_of_mem (p 2).2
  rw [hcl]; exact triple_eta' p

theorem fold3_zero (p : IC 3) : fold3 0 p = p := by
  unfold fold3
  rw [show (0:ℝ) * (p 0 : ℝ) = 0 by ring, sub_zero, mul_one]
  have hcl : clamp (p 1 : ℝ) = p 1 := by rw [clamp]; exact clamp_of_mem (p 1).2
  rw [hcl]; exact triple_eta' p

theorem fold4_zero (p : IC 3) : fold4 0 p = p := by
  unfold fold4
  rw [sub_zero, mul_one]
  have hcl : clamp (p 0 : ℝ) = p 0 := by rw [clamp]; exact clamp_of_mem (p 0).2
  rw [hcl]; exact triple_eta' p

/-! ## Joint continuity of the folding maps -/

theorem continuous_fold1 : Continuous fun q : ℝ × IC 3 => fold1 q.1 q.2 := by
  unfold fold1
  refine continuous_triple ?_ ?_ ?_
  · exact (continuous_apply 0).comp continuous_snd
  · refine continuous_clamp.comp ?_; fun_prop
  · exact (continuous_apply 2).comp continuous_snd

theorem continuous_fold2 : Continuous fun q : ℝ × IC 3 => fold2 q.1 q.2 := by
  unfold fold2
  refine continuous_triple ?_ ?_ ?_
  · exact (continuous_apply 0).comp continuous_snd
  · exact (continuous_apply 1).comp continuous_snd
  · refine continuous_clamp.comp ?_; fun_prop

theorem continuous_fold3 : Continuous fun q : ℝ × IC 3 => fold3 q.1 q.2 := by
  unfold fold3
  refine continuous_triple ?_ ?_ ?_
  · exact (continuous_apply 0).comp continuous_snd
  · refine continuous_clamp.comp ?_; fun_prop
  · exact (continuous_apply 2).comp continuous_snd

theorem continuous_fold4 : Continuous fun q : ℝ × IC 3 => fold4 q.1 q.2 := by
  unfold fold4
  refine continuous_triple ?_ ?_ ?_
  · refine continuous_clamp.comp ?_; fun_prop
  · exact (continuous_apply 1).comp continuous_snd
  · exact (continuous_apply 2).comp continuous_snd

theorem continuous_prune1 : Continuous fun p : IC 3 => prune 1 p := by
  unfold prune
  refine continuous_triple ?_ ?_ ?_
  · refine continuous_clamp.comp ?_; fun_prop
  · exact continuous_apply 1
  · exact continuous_apply 2

/-! ## The partial foldings of `prune 1 p` -/

theorem continuous_S0 : Continuous fun q : ℝ × IC 3 => prune 1 q.2 :=
  continuous_prune1.comp continuous_snd

theorem continuous_S1 : Continuous fun q : ℝ × IC 3 => fold1 1 (prune 1 q.2) := by
  have hg : Continuous fun q : ℝ × IC 3 => (((1:ℝ), prune 1 q.2) : ℝ × IC 3) :=
    Continuous.prodMk continuous_const continuous_S0
  exact continuous_fold1.comp hg

theorem continuous_S2 : Continuous fun q : ℝ × IC 3 => fold2 1 (fold1 1 (prune 1 q.2)) := by
  have hg : Continuous fun q : ℝ × IC 3 => (((1:ℝ), fold1 1 (prune 1 q.2)) : ℝ × IC 3) :=
    Continuous.prodMk continuous_const continuous_S1
  exact continuous_fold2.comp hg

theorem continuous_S3 : Continuous fun q : ℝ × IC 3 => fold3 1 (fold2 1 (fold1 1 (prune 1 q.2))) := by
  have hg : Continuous fun q : ℝ × IC 3 => (((1:ℝ), fold2 1 (fold1 1 (prune 1 q.2))) : ℝ × IC 3) :=
    Continuous.prodMk continuous_const continuous_S2
  exact continuous_fold3.comp hg

/-! ## The five pieces of `rho` -/

/-- The first piece `prune (5t) p` of `rho`, on `t ∈ [0,1/5]`. -/
def P0 (q : ℝ × IC 3) : IC 3 := prune (5 * q.1) q.2

/-- The second piece, on `t ∈ [1/5,2/5]`. -/
def P1 (q : ℝ × IC 3) : IC 3 := fold1 (5 * q.1 - 1) (prune 1 q.2)

/-- The third piece, on `t ∈ [2/5,3/5]`. -/
def P2 (q : ℝ × IC 3) : IC 3 := fold2 (5 * q.1 - 2) (fold1 1 (prune 1 q.2))

/-- The fourth piece, on `t ∈ [3/5,4/5]`. -/
def P3 (q : ℝ × IC 3) : IC 3 := fold3 (5 * q.1 - 3) (fold2 1 (fold1 1 (prune 1 q.2)))

/-- The fifth piece, on `t ∈ [4/5,1]`. -/
def P4 (q : ℝ × IC 3) : IC 3 :=
  fold4 (5 * q.1 - 4) (fold3 1 (fold2 1 (fold1 1 (prune 1 q.2))))

theorem continuous_P0 : Continuous P0 := by
  unfold P0
  have hg : Continuous fun q : ℝ × IC 3 => (((5 * q.1), q.2) : ℝ × IC 3) :=
    Continuous.prodMk (by fun_prop) continuous_snd
  exact continuous_prune.comp hg

theorem continuous_P1 : Continuous P1 := by
  unfold P1
  have hg : Continuous fun q : ℝ × IC 3 => ((5 * q.1 - 1, prune 1 q.2) : ℝ × IC 3) :=
    Continuous.prodMk (by fun_prop) continuous_S0
  exact continuous_fold1.comp hg

theorem continuous_P2 : Continuous P2 := by
  unfold P2
  have hg : Continuous fun q : ℝ × IC 3 =>
      ((5 * q.1 - 2, fold1 1 (prune 1 q.2)) : ℝ × IC 3) :=
    Continuous.prodMk (by fun_prop) continuous_S1
  exact continuous_fold2.comp hg

theorem continuous_P3 : Continuous P3 := by
  unfold P3
  have hg : Continuous fun q : ℝ × IC 3 =>
      ((5 * q.1 - 3, fold2 1 (fold1 1 (prune 1 q.2))) : ℝ × IC 3) :=
    Continuous.prodMk (by fun_prop) continuous_S2
  exact continuous_fold3.comp hg

theorem continuous_P4 : Continuous P4 := by
  unfold P4
  have hg : Continuous fun q : ℝ × IC 3 =>
      ((5 * q.1 - 4, fold3 1 (fold2 1 (fold1 1 (prune 1 q.2)))) : ℝ × IC 3) :=
    Continuous.prodMk (by fun_prop) continuous_S3
  exact continuous_fold4.comp hg

/-! ## The nested pasting -/

/-- The last two pieces, pasted at `t = 4/5`. -/
def F4 (q : ℝ × IC 3) : IC 3 := if q.1 ≤ 4/5 then P3 q else P4 q

/-- The pieces from `t = 3/5` on, pasted at `t = 3/5`. -/
def F3 (q : ℝ × IC 3) : IC 3 := if q.1 ≤ 3/5 then P2 q else F4 q

/-- The pieces from `t = 2/5` on, pasted at `t = 2/5`. -/
def F2 (q : ℝ × IC 3) : IC 3 := if q.1 ≤ 2/5 then P1 q else F3 q

/-- The whole of `rho`, pasted at `t = 1/5`. -/
def F1 (q : ℝ × IC 3) : IC 3 := if q.1 ≤ 1/5 then P0 q else F2 q

theorem continuous_F4 : Continuous F4 := by
  unfold F4
  refine Continuous.if_le continuous_P3 continuous_P4 continuous_fst continuous_const ?_
  intro q hq
  have h1 : 5 * q.1 - 3 = 1 := by rw [hq]; norm_num
  have h2 : 5 * q.1 - 4 = 0 := by rw [hq]; norm_num
  simp only [P3, P4, h1, h2, fold4_zero]

theorem continuous_F3 : Continuous F3 := by
  unfold F3
  refine Continuous.if_le continuous_P2 continuous_F4 continuous_fst continuous_const ?_
  intro q hq
  have hle : q.1 ≤ (4:ℝ)/5 := by rw [hq]; norm_num
  have h1 : 5 * q.1 - 2 = 1 := by rw [hq]; norm_num
  have h2 : 5 * q.1 - 3 = 0 := by rw [hq]; norm_num
  show P2 q = F4 q
  unfold F4
  rw [if_pos hle]
  simp only [P2, P3, h1, h2, fold3_zero]

theorem continuous_F2 : Continuous F2 := by
  unfold F2
  refine Continuous.if_le continuous_P1 continuous_F3 continuous_fst continuous_const ?_
  intro q hq
  have hle : q.1 ≤ (3:ℝ)/5 := by rw [hq]; norm_num
  have h1 : 5 * q.1 - 1 = 1 := by rw [hq]; norm_num
  have h2 : 5 * q.1 - 2 = 0 := by rw [hq]; norm_num
  show P1 q = F3 q
  unfold F3
  rw [if_pos hle]
  simp only [P1, P2, h1, h2, fold2_zero]

theorem continuous_F1 : Continuous F1 := by
  unfold F1
  refine Continuous.if_le continuous_P0 continuous_F2 continuous_fst continuous_const ?_
  intro q hq
  have hle : q.1 ≤ (2:ℝ)/5 := by rw [hq]; norm_num
  have h1 : 5 * q.1 = 1 := by rw [hq]; norm_num
  have h2 : 5 * q.1 - 1 = 0 := by rw [hq]; norm_num
  show P0 q = F2 q
  unfold F2
  rw [if_pos hle]
  simp only [P0, P1]
  rw [h2, fold1_zero, h1]

theorem net_rho_continuous : Continuous fun q : ℝ × Work.Stems.Cubical.IC 3 => Work.Stems.Hur2b.rho q.1 q.2 := by
  have h : (fun q : ℝ × IC 3 => rho q.1 q.2) = F1 := by
    funext q
    simp only [F1, F2, F3, F4, P0, P1, P2, P3, P4, rho]
  rw [h]
  exact continuous_F1

end

end Work.Stems.Hur2b
