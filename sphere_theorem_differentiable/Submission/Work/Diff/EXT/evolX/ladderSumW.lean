import Mathlib
import Submission.Work.Diff.EXT.reaction0_jets
import Submission.Work.Diff.EXT.evolX.ladderAtoms
import Submission.Work.Diff.EXT.evolX.goodDataN_shift
import Submission.Work.Diff.EXT.evolX.atomZf_pair
import Submission.Work.Diff.EXT.evolX.atomZf_bound
import Submission.Work.Diff.EXT.evolX.atomSmooth
import Submission.Work.Diff.EXT.evolX.atomBound
import Submission.Work.Diff.EXT.evolX.curvActTAtomSum
import Submission.Work.Diff.EXT.evolX.atomExtStepW
import Submission.Work.Diff.EXT.evolX.swapDiffDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The atom-sum ladder for the adjacent-swap bound

This module assembles the bound of `Work.Diff.EXT.evolX.ckt_adjacent_swap_bound` from the atom
lemmas of `Submission/Work/Diff/EXT/evolX/`:

* `AtomC L N` packages the data of an atom of level `L` whose tuple has arity `N` (the split
  `(m,l)` with `m+l = L`, the insertion slot and the index maps), so that all atoms of a fixed level
  share one type while the arity can be written in the "level" form used by
  `Work.Diff.EXT.evolX.ladderStep`;
* `AtomC.sem` is the operator of the atom, `AtomC.shift1`/`shift2` are the two atoms produced by one
  covariant derivative (`Work.Diff.EXT.evolX.atomExtStep_v2`);
* `atomSum_bound` bounds any finite sum of level-`L` atoms by
  `card · finrank · Shape g x L · ∏ ‖F r x‖` (`Work.Diff.EXT.evolX.atomBound`);
* `ladder_sum` proves by induction on `i` that `ladderStep g j i (curvActT g j)` is (up to sign, and
  *eventually* at the base point — the orthonormal frame is only available near `x`) a finite sum of
  level-`(j+i)` atoms — the base case is `curvActT_eq_atomSum_v2`, the step `atomExtStep_v2`.

The `AtomC` data is built uniformly in `(j, i)` and does not depend on the base point, so the
constant in `ladder_bound` is uniform in `(g, x)`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

local macro "Tf" : term => `((y : M) → TangentSpace I y)

/-! ## The data of an atom of a fixed level and arity -/

/-- The data of an atom of level `L` whose tuple has arity `N`: the split `(m,l)` with `m + l = L`,
the insertion slot `s` and the two index maps. -/
structure AtomC (L N : ℕ) where
  /-- the level of the inner tower -/
  m : ℕ
  /-- the level of the inserted curvature vector -/
  l : ℕ
  /-- the level split -/
  hml : m + l = L
  /-- the insertion slot of the tower -/
  s : Fin (m + 4)
  /-- the tower-slot index map -/
  κ : Fin (m + 4) → Fin N
  /-- the index map of the arguments of the curvature vector -/
  ξ : Fin (l + 3) → Fin N
  /-- the partition condition -/
  hgood : GoodDataN m l N s κ ξ

/-- The operator of an atom. -/
noncomputable def AtomC.sem (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → Tf) {L N : ℕ} (d : AtomC L N)
    (F : Fin N → Tf) : M → ℝ :=
  Atom g W d.m d.l N d.s d.κ d.ξ F

/-- The atom obtained by attributing the new differentiation direction to the *tower*. -/
noncomputable def AtomC.shift1 {L N : ℕ} (d : AtomC L N) : AtomC (L + 1) (N + 1) where
  m := d.m + 1
  l := d.l
  hml := by have h := d.hml; omega
  s := Fin.succ d.s
  κ := Fin.cons 0 (fun i : Fin (d.m + 4) => Fin.succ (d.κ i))
  ξ := fun r : Fin (d.l + 3) => Fin.succ (d.ξ r)
  hgood := (goodDataN_shift d.m d.l N d.s d.κ d.ξ d.hgood).1

/-- The atom obtained by attributing the new differentiation direction to the *curvature vector*. -/
noncomputable def AtomC.shift2 {L N : ℕ} (d : AtomC L N) : AtomC (L + 1) (N + 1) where
  m := d.m
  l := d.l + 1
  hml := by have h := d.hml; omega
  s := d.s
  κ := fun i : Fin (d.m + 4) => Fin.succ (d.κ i)
  ξ := Fin.cons 0 (fun r : Fin (d.l + 3) => Fin.succ (d.ξ r))
  hgood := (goodDataN_shift d.m d.l N d.s d.κ d.ξ d.hgood).2

/-- **The combinatorics of the base atom**: the index maps `baseK`, `baseXi` partition the positions
of the tuple of `curvActT`. -/
theorem baseGoodDataN_ladder (j : ℕ) (s : Fin (j + 4)) :
    GoodDataN j 0 (j + 6) s (baseK j s) (baseXi j s) := by
  have hK : ∀ i : Fin (j + 4), i ≠ s → (baseK j s i : ℕ) = i.val + 2 := by
    intro i hi
    simp only [baseK]
    rw [if_neg hi]
  have hX0 : (baseXi j s (0 : Fin 3) : ℕ) = 0 := rfl
  have hX1 : (baseXi j s (1 : Fin 3) : ℕ) = 1 := rfl
  have hX2 : (baseXi j s (2 : Fin 3) : ℕ) = s.val + 2 := by
    simp only [baseXi]
    rfl
  have hsplit : ∀ r : Fin 3, r = 0 ∨ r = 1 ∨ r = 2 := by
    intro r
    rcases (show r.val = 0 ∨ r.val = 1 ∨ r.val = 2 by have := r.isLt; omega) with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i i' hi hi' h
    have h1 := hK i hi
    have h2 := hK i' hi'
    rw [h] at h1
    exact Fin.ext (by omega)
  · intro r r' h
    have hval : (baseXi j s r : ℕ) = (baseXi j s r' : ℕ) := congrArg Fin.val h
    rcases hsplit r with h1 | h1 | h1 <;> rcases hsplit r' with h2 | h2 | h2 <;>
      rw [h1, h2] at hval ⊢ <;> simp only [hX0, hX1, hX2] at hval <;>
      first | rfl | (exact absurd hval (by omega))
  · intro i r hi h
    have hval : (baseK j s i : ℕ) = (baseXi j s r : ℕ) := congrArg Fin.val h
    rw [hK i hi] at hval
    rcases hsplit r with h1 | h1 | h1
    · rw [h1] at hval
      simp only [hX0] at hval
      omega
    · rw [h1] at hval
      simp only [hX1] at hval
      omega
    · rw [h1] at hval
      simp only [hX2] at hval
      exact hi (Fin.ext (by omega))
  · intro u
    by_cases h0 : (u : ℕ) = 0
    · refine Or.inr ⟨(0 : Fin 3), Fin.ext ?_⟩
      rw [hX0]
      omega
    by_cases h1 : (u : ℕ) = 1
    · refine Or.inr ⟨(1 : Fin 3), Fin.ext ?_⟩
      rw [hX1]
      omega
    have huv : 2 ≤ (u : ℕ) := by omega
    by_cases hs : (⟨u.val - 2, by omega⟩ : Fin (j + 4)) = s
    · refine Or.inr ⟨(2 : Fin 3), Fin.ext ?_⟩
      have hsv : (⟨u.val - 2, by omega⟩ : Fin (j + 4)).val = s.val := congrArg Fin.val hs
      simp only [Fin.val_mk] at hsv
      rw [hX2]
      omega
    · refine Or.inl ⟨⟨u.val - 2, by omega⟩, hs, Fin.ext ?_⟩
      rw [hK _ hs]
      simp only [Fin.val_mk]
      omega

/-- The base atom of level `j` attached to the slot `s` of the curvature action `curvActT`. -/
noncomputable def baseC (j : ℕ) (s : Fin (j + 4)) : AtomC j (j + 6) where
  m := j
  l := 0
  hml := by omega
  s := s
  κ := baseK j s
  ξ := baseXi j s
  hgood := baseGoodDataN_ladder j s

/-- **The atom step**: `extStep` applied to an atom of level `m + l` is the sum of the two child
atoms. -/
theorem AtomC.extStep_sem (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (W : Fin (Module.finrank ℝ E) → Tf)
    (hW : ∀ i, SmTf (I := I) (M := M) (W i))
    (hON : ONFrameAt (I := I) (M := M) g x W)
    {L N : ℕ} (d : AtomC L N) (F : Fin (N + 1) → Tf)
    (hF : ∀ u, SmTf (I := I) (M := M) (F u)) :
    extStep (I := I) (M := M) g (AtomC.sem (I := I) (M := M) g W d) F x
      = AtomC.sem (I := I) (M := M) g W (AtomC.shift1 d) F x
        + AtomC.sem (I := I) (M := M) g W (AtomC.shift2 d) F x := by
  rw [show AtomC.sem (I := I) (M := M) g W d
        = (Atom (I := I) (M := M) g W d.m d.l N d.s d.κ d.ξ) from rfl,
    show AtomC.sem (I := I) (M := M) g W (AtomC.shift1 d)
        = (Atom (I := I) (M := M) g W (d.m + 1) d.l (N + 1) (Fin.succ d.s)
            (Fin.cons 0 (fun i : Fin (d.m + 4) => Fin.succ (d.κ i)))
            (fun r : Fin (d.l + 3) => Fin.succ (d.ξ r))) from rfl,
    show AtomC.sem (I := I) (M := M) g W (AtomC.shift2 d)
        = (Atom (I := I) (M := M) g W d.m (d.l + 1) (N + 1) d.s
            (fun i : Fin (d.m + 4) => Fin.succ (d.κ i))
            (Fin.cons 0 (fun r : Fin (d.l + 3) => Fin.succ (d.ξ r)))) from rfl]
  exact atomExtStepW (I := I) (M := M) hLC g x W hW hON d.m d.l N d.s d.κ d.ξ d.hgood F hF

/-! ## Germ-congruence of `mvfderiv` and of `extStep` -/

/-- `mvfderiv` of real-valued functions only depends on the germ.  (Local copy of
`Work.Diff.GE.mvfderiv_congr_of_eventuallyEq_real`, without the `Boundaryless`/compactness
hypotheses.) -/
theorem atomLadder_mvfderiv_congr_real {f f' : M → ℝ} {x : M} (h : f =ᶠ[𝓝 x] f') :
    mvfderiv I f x = mvfderiv I f' x := by
  rw [mvfderiv, mvfderiv, h.eq_of_nhds, Filter.EventuallyEq.mfderiv_eq h]
  all_goals first | rfl | (ext v; rfl)

/-- **`extStep` only depends on the germ of the operator** on smooth tuples. -/
theorem extStep_congr_of_eventuallyEq (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M) (x : M) {K : ℕ} {S S' : (Fin K → Tf) → M → ℝ}
    (h : ∀ F' : Fin K → Tf, (∀ u, SmTf (F' u)) → S F' =ᶠ[𝓝 x] S' F')
    (G : Fin (K + 1) → Tf) (hG : ∀ u, SmTf (G u)) :
    extStep (I := I) (M := M) g S G x = extStep (I := I) (M := M) g S' G x := by
  obtain ⟨hcov⟩ := (hLC g).1
  have hF : ∀ u, SmTf ((fun i : Fin K => G i.succ) u) := fun u => hG u.succ
  rw [extStep_eq_extD, extStep_eq_extD, Work.Diff.GE.extD_eq, Work.Diff.GE.extD_eq]
  congr 1
  · exact congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L (G 0 x))
      (atomLadder_mvfderiv_congr_real (I := I) (M := M)
        (h (fun i : Fin K => G i.succ) hF))
  · refine Finset.sum_congr rfl fun i _ => ?_
    exact (h _ (Work.Diff.GE.smoothTuple_upd (Submission.Diff.lcOf g) hcov (hG 0) hF i)).eq_of_nhds

/-! ## Linearity of `extStep` in the operator -/

/-- **Linearity of `extStep`** for a negated finite sum of operators, under the
`mvfderiv`-identification hypothesis (which holds for smooth operators). -/
theorem extStep_neg_sum {K : ℕ} {ι : Type*} [Fintype ι]
    (g : SMet I M) (S : ι → (Fin K → Tf) → M → ℝ) (x : M)
    (hmv : ∀ (F' : Fin K → Tf) (v : TangentSpace I x),
      (∀ i, SmTf (F' i)) →
      (mvfderiv I (fun y : M => - ∑ t : ι, S t F' y) x) v
        = - ∑ t : ι, (mvfderiv I (S t F') x) v) :
    ∀ (F : Fin (K + 1) → Tf),
      (∀ u, SmTf (F u)) →
      extStep (I := I) (M := M) g (fun F' => fun y => - ∑ t : ι, S t F' y) F x
        = - ∑ t : ι, extStep (I := I) (M := M) g (S t) F x := by
  intro F hF
  have hF'sm : ∀ i : Fin K, SmTf ((fun i : Fin K => F i.succ) i) := fun i => hF i.succ
  have hLHS : extStep (I := I) (M := M) g (fun F' => fun y => - ∑ t : ι, S t F' y) F x
      = mvfderiv I (fun y : M => - ∑ t : ι, S t (fun i : Fin K => F i.succ) y) x (F 0 x)
        - ∑ s : Fin K, (fun F' => fun y => - ∑ t : ι, S t F' y)
            (Function.update (fun i : Fin K => F i.succ) s
              (dirF (I := I) (M := M) g ((fun i : Fin K => F i.succ) s) (F 0))) x := rfl
  rw [hLHS, hmv (fun i : Fin K => F i.succ) (F 0 x) hF'sm]
  have h2 : (∑ s : Fin K, (fun F' => fun y => - ∑ t : ι, S t F' y)
        (Function.update (fun i : Fin K => F i.succ) s
          (dirF (I := I) (M := M) g ((fun i : Fin K => F i.succ) s) (F 0))) x)
      = ∑ s : Fin K, - ∑ t : ι, S t (Function.update (fun i : Fin K => F i.succ) s
          (dirF (I := I) (M := M) g ((fun i : Fin K => F i.succ) s) (F 0))) x :=
    Finset.sum_congr rfl (fun s _ => rfl)
  rw [h2]
  have h3 : (∑ t : ι, extStep (I := I) (M := M) g (S t) F x)
      = ∑ t : ι, (mvfderiv I (S t (fun i : Fin K => F i.succ)) x (F 0 x)
          - ∑ s : Fin K, S t (Function.update (fun i : Fin K => F i.succ) s
              (dirF (I := I) (M := M) g ((fun i : Fin K => F i.succ) s) (F 0))) x) :=
    Finset.sum_congr rfl (fun t _ => rfl)
  rw [h3, Finset.sum_sub_distrib]
  simp only [Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  ring

/-- The `mvfderiv` of a negated finite sum of smooth functions. -/
theorem mvfderiv_neg_sum_finset {ι : Type*} [Fintype ι] (S : ι → M → ℝ) (x : M)
    (v : TangentSpace I x)
    (hS : ∀ t, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) (S t) x) :
    (mvfderiv I (fun y : M => - ∑ t : ι, S t y) x) v
      = - ∑ t : ι, (mvfderiv I (S t) x) v := by
  have hsum := Work.Diff.EXT.mvfderiv_sum S x v hS
  rw [show (fun y : M => -∑ t : ι, S t y)
      = (-(fun y : M => ∑ t : ι, S t y)) from rfl, mvfderiv_neg,
    ContinuousLinearMap.neg_apply, hsum]

/-! ## The bound for a finite sum of atoms -/

/-- **The bound for a finite sum of atoms of level `L`.** -/
theorem atomSum_bound (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (W : Fin (Module.finrank ℝ E) → Tf)
    (hW : ∀ i, SmTf (W i))
    (hON : ONFrameAt (I := I) (M := M) g x W)
    {L N : ℕ} {ι : Type*} [Fintype ι] (dd : ι → AtomC L N)
    (F : Fin N → Tf) (hF : ∀ u, SmTf (F u)) :
    |∑ t : ι, AtomC.sem (I := I) (M := M) g W (dd t) F x|
      ≤ (Fintype.card ι : ℝ) * (Module.finrank ℝ E : ℝ) * Work.Diff.EXT.Shape g x L
          * ∏ r : Fin N, Work.Diff.EXT.gNrm g x (F r x) := by
  classical
  set P : ℝ := ∏ r : Fin N, Work.Diff.EXT.gNrm g x (F r x) with hP
  have hPnn : 0 ≤ P := Finset.prod_nonneg fun r _ => Work.Diff.EXT.gNrm_nonneg g x _
  have hSh : 0 ≤ Work.Diff.EXT.Shape g x L := Work.Diff.EXT.Shape_nonneg g x L
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by positivity
  have hterm : ∀ t : ι,
      |AtomC.sem (I := I) (M := M) g W (dd t) F x|
        ≤ (Module.finrank ℝ E : ℝ) * Work.Diff.EXT.Shape g x L * P := by
    intro t
    have h1 := atomBound (I := I) (M := M) hLC g x W hW hON (dd t).m (dd t).l N (dd t).s
      (dd t).κ (dd t).ξ (dd t).hgood F hF
    rw [← hP] at h1
    refine le_trans h1 (le_of_eq ?_)
    rw [(dd t).hml]
  calc |∑ t : ι, AtomC.sem (I := I) (M := M) g W (dd t) F x|
      ≤ ∑ t : ι, |AtomC.sem (I := I) (M := M) g W (dd t) F x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t : ι, (Module.finrank ℝ E : ℝ) * Work.Diff.EXT.Shape g x L * P :=
        Finset.sum_le_sum fun t _ => hterm t
    _ = (Fintype.card ι : ℝ) * ((Module.finrank ℝ E : ℝ) * Work.Diff.EXT.Shape g x L * P) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Fintype.card ι : ℝ) * (Module.finrank ℝ E : ℝ) * Work.Diff.EXT.Shape g x L * P := by
        ring

/-! ## The ladder -/

/-- **The ladder.**  For every `i`, the `i`-fold `extStep` of the curvature action `curvActT g j` is
(up to sign) a finite sum of level-`(j+i)` atoms, of a shape that is *uniform in the base point*
(the frame `W` enters only through the operators).

The identity is an eventual one at the base point, because the frame is only orthonormal near it
(`ONFrameAt`); the induction step uses `Filter.Eventually.eventually_nhds` to re-localise. -/
theorem ladder_sum_w (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (j : ℕ) (W : Fin (Module.finrank ℝ E) → Tf)
    (hW : ∀ i, SmTf (W i)) :
    ∀ i : ℕ, ∃ (ι : Type) (_ : Fintype ι) (_ : Fintype.card ι ≤ (j + 4) * 2 ^ i)
      (dd : ι → AtomC (j + i) ((j + 2 + i) + 4)),
      ∀ (x : M), ONFrameAt (I := I) (M := M) g x W →
      ∀ (F : Fin ((j + 2 + i) + 4) → Tf), (∀ u, SmTf (F u)) →
        ladderStep (I := I) (M := M) g j i (curvActT (I := I) (M := M) g j) F
          =ᶠ[𝓝 x] fun y : M => - ∑ t : ι, AtomC.sem (I := I) (M := M) g W (dd t) F y := by
  intro i
  induction i with
  | zero =>
    refine ⟨Fin (j + 4), inferInstance, ?_, ?_, ?_⟩
    · show Fintype.card (Fin (j + 4)) ≤ (j + 4) * 2 ^ 0
      simp
    · intro s
      exact baseC j s
    · intro x hON F hF
      filter_upwards [hON.eventually_nhds] with y hy
      have h := (curvActTAtomSum (I := I) (M := M) hLC g y j W hW hy F hF).2
      simpa only [ladderStep, AtomC.sem, baseC] using h
  | succ i ih =>
    obtain ⟨ι, hι, hcard, dd, hid⟩ := ih
    letI := hι
    let dd' : ι × Bool → AtomC (j + (i + 1)) ((j + 2 + (i + 1)) + 4) := fun u =>
      if u.2 then (AtomC.shift1 (dd u.1) : AtomC (j + (i + 1)) ((j + 2 + (i + 1)) + 4))
      else (AtomC.shift2 (dd u.1) : AtomC (j + (i + 1)) ((j + 2 + (i + 1)) + 4))
    refine ⟨ι × Bool, inferInstance, ?_, dd', ?_⟩
    · rw [Fintype.card_prod, Fintype.card_bool]
      calc Fintype.card ι * 2 ≤ ((j + 4) * 2 ^ i) * 2 := Nat.mul_le_mul_right 2 hcard
        _ = (j + 4) * 2 ^ (i + 1) := by rw [pow_succ]; ring
    · intro x hON F hF
      filter_upwards [hON.eventually_nhds] with y hy
      have hcongr := extStep_congr_of_eventuallyEq (I := I) (M := M) hLC g y
        (S := ladderStep (I := I) (M := M) g j i (curvActT (I := I) (M := M) g j))
        (S' := fun F' : Fin ((j + 2 + i) + 4) → Tf => fun z : M =>
          - ∑ t : ι, AtomC.sem (I := I) (M := M) g W (dd t) F' z)
        (fun F' hF' => hid y hy F' hF') F hF
      have hneg := extStep_neg_sum (I := I) (M := M) g
        (fun t : ι => AtomC.sem (I := I) (M := M) g W (dd t)) y
        (fun F' v hF' => mvfderiv_neg_sum_finset (I := I) (M := M)
          (fun t : ι => AtomC.sem (I := I) (M := M) g W (dd t) F') y v
          (fun t => (atomSmooth (I := I) (M := M) hLC g W hW (dd t).m (dd t).l _
              (dd t).s (dd t).κ (dd t).ξ F' hF').contMDiffAt.mdifferentiableAt (by simp)))
        F hF
      rw [ladderStep_succ, hcongr, hneg]
      congr 1
      have hstep : (∑ t : ι, extStep (I := I) (M := M) g
            (AtomC.sem (I := I) (M := M) g W (dd t)) F y)
          = ∑ t : ι, (AtomC.sem (I := I) (M := M) g W (AtomC.shift1 (dd t)) F y
              + AtomC.sem (I := I) (M := M) g W (AtomC.shift2 (dd t)) F y) :=
        Finset.sum_congr rfl fun t _ =>
          AtomC.extStep_sem (I := I) (M := M) hLC g y W hW hy (dd t) F hF
      have hprod : (∑ t : ι, ∑ b : Bool, AtomC.sem (I := I) (M := M) g W (dd' (t, b)) F y)
          = ∑ u : ι × Bool, AtomC.sem (I := I) (M := M) g W (dd' u) F y :=
        (Fintype.sum_prod_type (γ := ℝ) (fun u : ι × Bool =>
          AtomC.sem (I := I) (M := M) g W (dd' u) F y)).symm
      rw [hstep, ← hprod]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Fintype.sum_bool]
      have h1 : dd' (t, true) = AtomC.shift1 (dd t) := by
        dsimp only [dd']
        rw [if_pos rfl]
      have h2 : dd' (t, false) = AtomC.shift2 (dd t) := by
        dsimp only [dd']
        rw [if_neg (by simp : ¬ (((t, false) : ι × Bool).2 = true))]
      rw [h1, h2]

/-! ## The bound for the iterated step -/

/-- **The bound for the iterated step of the curvature action.**  The constant
`((j : ℝ) + 4) · 2^i · finrank ℝ E` is explicit and uniform in `(g, x)`. -/
theorem ladder_bound_w (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (j i : ℕ) (W : Fin (Module.finrank ℝ E) → Tf)
    (hW : ∀ i, SmTf (W i))
    (hON : ONFrameAt (I := I) (M := M) g x W) :
    ∀ (F : Fin ((j + 2 + i) + 4) → Tf), (∀ u, SmTf (F u)) →
      |ladderStep (I := I) (M := M) g j i (curvActT (I := I) (M := M) g j) F x|
        ≤ ((j : ℝ) + 4) * 2 ^ i * (Module.finrank ℝ E : ℝ)
            * Work.Diff.EXT.Shape g x (j + i)
            * ∏ r : Fin ((j + 2 + i) + 4), Work.Diff.EXT.gNrm g x (F r x) := by
  classical
  intro F hF
  obtain ⟨ι, hι, hcard, dd, hid⟩ := ladder_sum_w (I := I) (M := M) hLC g j W hW i
  letI := hι
  have hval : ladderStep (I := I) (M := M) g j i (curvActT (I := I) (M := M) g j) F x
      = - ∑ t : ι, AtomC.sem (I := I) (M := M) g W (dd t) F x :=
    (hid x hON F hF).eq_of_nhds
  have h1 := atomSum_bound (I := I) (M := M) hLC g x W hW hON dd F hF
  rw [hval, abs_neg]
  refine le_trans h1 ?_
  set P : ℝ := ∏ r : Fin ((j + 2 + i) + 4), Work.Diff.EXT.gNrm g x (F r x) with hPdef
  have hPnn : 0 ≤ P := Finset.prod_nonneg fun r _ => Work.Diff.EXT.gNrm_nonneg g x _
  have hSh : 0 ≤ Work.Diff.EXT.Shape g x (j + i) := Work.Diff.EXT.Shape_nonneg g x (j + i)
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by positivity
  have hcard' : (Fintype.card ι : ℝ) ≤ ((j : ℝ) + 4) * 2 ^ i := by
    have h2 : ((Fintype.card ι : ℕ) : ℝ) ≤ (((j + 4) * 2 ^ i : ℕ) : ℝ) := by
      exact_mod_cast hcard
    push_cast at h2 ⊢
    linarith
  have h2i : (0 : ℝ) ≤ ((j : ℝ) + 4) * 2 ^ i := by positivity
  calc (Fintype.card ι : ℝ) * (Module.finrank ℝ E : ℝ) * Work.Diff.EXT.Shape g x (j + i) * P
      ≤ (((j : ℝ) + 4) * 2 ^ i) * (Module.finrank ℝ E : ℝ)
          * Work.Diff.EXT.Shape g x (j + i) * P := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcard' hfr) hSh) hPnn
    _ = ((j : ℝ) + 4) * 2 ^ i * (Module.finrank ℝ E : ℝ)
          * Work.Diff.EXT.Shape g x (j + i) * P := by ring

end Work.Diff.EXT.evolX
