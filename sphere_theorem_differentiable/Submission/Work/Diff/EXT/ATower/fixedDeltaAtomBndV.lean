import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicFlip.towerEqLoweringDeltaTowerM
import Submission.Work.Diff.EXT.ConnCov.RicTr.DTB.BndVDeltaTower
import Submission.Work.Diff.EXT.ConnCov.aTowerMovingDefs
import Submission.Work.Diff.EXT.ConnCov.RicTowerKit
import Submission.Work.Diff.EXT.ConnCov.RicTowerDefs
import Submission.Work.Diff.EXT.LocalExtDefs
import Submission.Work.Diff.EXT.conn_diff_bound_of_shibounds
import Submission.Work.Diff.EXT.ATower.Defs
import Submission.Work.Diff.EXT.ATower.step_flip
import Submission.Work.Diff.EXT.ATower.bndV_metric_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ATower

/-!
# The bound for the flipped `δ`-atom

`Work.Diff.EXT.ConnCov.DTB.bndV_deltaTower` bounds the `∇^{G 0}`-tower of the connection difference
`∇^{G t} − ∇^{G 0}` in the **moving** metric `G t`.  The present statement is the corresponding
bound for the **reversed** family `s ↦ G (t - s)` — whose value at `t` is the initial metric
`G 0` and whose value at `0` is `G t` — measured in the initial metric `G 0`.  The reversed
family's connection difference is `∇^{G 0} − ∇^{G t}`, i.e. the *negative* of `covDiff G t`, so
two observations give the result:

* the `∇^{g}`-tower of a negated `(1,2)`-tensor is the negation of the tower (`vtowerM_neg`),
  whence the reversed tower is the negative of `DTB.deltaTower G t` (`deltaTowerM_flip`);
* the `G 0`- and the `G t`-quadratic forms differ by the uniform factor
  `exp (2 (finrank ℝ E · C) t)` on `[T/2, T)`, which transfers the bound
  `AMB.BndV G t … (C1 j)` of `DTB.bndV_deltaTower` to the initial metric
  (`Work.Diff.EXT.ATower.bndV_metric_le`).

No smoothness/Shi input is needed beyond the `hA` hypothesis: the whole content is the sign of the
connection difference, the identification of the two tower vocabularies, and the uniform comparison
of the two quadratic forms.
-/

section aux

open Work.Diff.EXT.ConnCov
open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- The covariant derivative of a *negated* section is the negation of the covariant derivative of
the section.  This is the `a = -1` case of the rule `∇(a • σ) = a • ∇σ` for covariant derivatives;
the smoothness hypothesis is the one needed to make both sides meaningful (`∇` of a
non-differentiable section is junk). -/
lemma cov_neg_section
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    {W : TF (I := I) (M := M)} {x : M}
    (hW : ContMDiffAt I I.tangent (⊤ : ℕ∞) (T% W) x) :
    cov (-W) x = -cov W x := by
  have h := cov.isCovariantDerivativeOn.smul_const (-1 : ℝ) (σ := W)
    (hW.mdifferentiableAt (by simp))
  rw [show (-1 : ℝ) • W = -W from by funext y; simp] at h
  simpa using h

/-- `RicFlip.vtowerM` *is* the `∇^{lcOf g}`-tower `DTB.vtower (lcOf g)` of the same base: the two
recursions coincide definitionally, so the two chapters' vocabularies may be used interchangeably. -/
lemma vtowerM_eq_vtower
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : SMet I M) (base : RicFlip.VOpM (I := I) (M := M) 0) (k : ℕ) :
    RicFlip.vtowerM g base k = DTB.vtower (lcOf g) base k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [show RicFlip.vtowerM g base (k + 1)
            = RicFlip.vstepM g (RicFlip.vtowerM g base k) from rfl,
        show DTB.vtower (lcOf g) base (k + 1)
            = DTB.vstep (lcOf g) (DTB.vtower (lcOf g) base k) from rfl,
        ih]
      exact rfl

/-- **The tower of a negated `(1,2)`-tensor is the negation of the tower** (with respect to the
same connection `∇^g`).  Induction on the level: one recursion step is linear in the tensor
argument, the only non-formal input being `cov_neg_section` (linearity of `∇` in the section) and
the smoothness of the intermediate towers on smooth fields (`RicFlip.smE_vtowerM`), which supplies
the hypotheses of that linearity. -/
theorem vtowerM_neg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M)
    (θ : TF (I := I) (M := M) → TF (I := I) (M := M) → TF (I := I) (M := M))
    (hθ : ∀ (X Y : TF (I := I) (M := M)), SmE I M X → SmE I M Y → SmE I M (θ X Y)) :
    ∀ (k : ℕ) (v : Fin k → TF (I := I) (M := M)) (X Y : TF (I := I) (M := M)),
      (∀ i, SmE I M (v i)) → SmE I M X → SmE I M Y →
      RicFlip.vtowerM g (fun (_ : Fin 0 → TF (I := I) (M := M)) X Y => -(θ X Y)) k v X Y
        = -(RicFlip.vtowerM g (fun (_ : Fin 0 → TF (I := I) (M := M)) X Y => θ X Y) k v X Y) := by
  intro k
  induction k with
  | zero =>
      intro v X Y hv hX hY
      rfl
  | succ k ih =>
      intro v X Y hv hX hY
      have hv' : ∀ i : Fin k, SmE I M (v i.succ) := fun i => hv i.succ
      have hv0 : SmE I M (v 0) := hv 0
      have hU : ∀ i : Fin k, SmE I M (fun y => (lcOf g) (v i.succ) y (v 0 y)) :=
        fun i => lcOf_apply_smE hLC g (v i.succ) (v 0) (hv i.succ) hv0
      have hX' : SmE I M (fun y => (lcOf g) X y (v 0 y)) := lcOf_apply_smE hLC g X (v 0) hX hv0
      have hY' : SmE I M (fun y => (lcOf g) Y y (v 0 y)) := lcOf_apply_smE hLC g Y (v 0) hY hv0
      have hsm : ∀ (w : Fin k → TF (I := I) (M := M)) (X' Y' : TF (I := I) (M := M)),
          (∀ i, SmE I M (w i)) → SmE I M X' → SmE I M Y' →
          SmE I M (RicFlip.vtowerM g (fun (_ : Fin 0 → TF (I := I) (M := M)) X Y => θ X Y)
            k w X' Y') :=
        fun w X' Y' hw hX' hY' =>
          RicFlip.smE_vtowerM hLC g (fun _ X Y => θ X Y)
            (fun _ X Y h1 h2 => hθ X Y h1 h2) k w X' Y' hw hX' hY'
      show RicFlip.vstepM g
          (RicFlip.vtowerM g (fun (_ : Fin 0 → TF (I := I) (M := M)) X Y => -(θ X Y)) k)
          v X Y
        = -(RicFlip.vstepM g
          (RicFlip.vtowerM g (fun (_ : Fin 0 → TF (I := I) (M := M)) X Y => θ X Y) k)
          v X Y)
      funext x
      simp only [RicFlip.vstepM, Pi.neg_apply]
      have hsum : (∑ i : Fin k,
            (RicFlip.vtowerM g (fun (_ : Fin 0 → TF (I := I) (M := M)) X Y => -(θ X Y)) k)
              (Function.update (fun j : Fin k => v j.succ) i
                (fun y => (lcOf g) (v i.succ) y (v 0 y))) X Y x)
          = ∑ i : Fin k,
            -((RicFlip.vtowerM g (fun (_ : Fin 0 → TF (I := I) (M := M)) X Y => θ X Y) k)
              (Function.update (fun j : Fin k => v j.succ) i
                (fun y => (lcOf g) (v i.succ) y (v 0 y))) X Y x) :=
        Finset.sum_congr rfl (fun i _ =>
          congrFun (ih (Function.update (fun j : Fin k => v j.succ) i
              (fun y => (lcOf g) (v i.succ) y (v 0 y))) X Y
            (RicFlip.smE_updateM i hv' (hU i)) hX hY) x)
      rw [hsum]
      rw [ih (fun i : Fin k => v i.succ) X Y hv' hX hY]
      rw [ih (fun i : Fin k => v i.succ) (fun y => (lcOf g) X y (v 0 y)) Y hv' hX' hY]
      rw [ih (fun i : Fin k => v i.succ) X (fun y => (lcOf g) Y y (v 0 y)) hv' hX hY']
      rw [cov_neg_section (lcOf g)
        (W := RicFlip.vtowerM g (fun (_ : Fin 0 → TF (I := I) (M := M)) X Y => θ X Y) k
          (fun i : Fin k => v i.succ) X Y)
        (hsm (fun i : Fin k => v i.succ) X Y hv' hX hY).contMDiffAt]
      simp only [Pi.neg_apply, neg_apply, Finset.sum_neg_distrib]
      abel

/-- **The reversed (`δ`-flipped) family has the negated `δ`-tower.**  For any family `Ĝ` whose
time-`t` metric is `G 0` and whose time-`0` metric is `G t` (the reversed Ricci flow
`Ĝ = fun s ↦ G (t - s)` being the case of interest), the `Ĝ t = ∇^{G 0}`-tower of its connection
difference `∇^{G 0} − ∇^{G t}` is minus the `∇^{G 0}`-tower of `∇^{G t} − ∇^{G 0}` (the `DTB`
object `deltaTower G t`). -/
lemma deltaTowerM_flip
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → SMet I M) (t : ℝ)
    {Ĝ : ℝ → SMet I M} (h0 : Ĝ 0 = G t) (hT : Ĝ t = G 0)
    (c : ℕ) (v : Fin c → TF (I := I) (M := M)) (X Z : TF (I := I) (M := M))
    (hv : ∀ i, SmE I M (v i)) (hX : SmE I M X) (hZ : SmE I M Z) :
    RicFlip.deltaTowerM Ĝ t c v X Z = -(DTB.deltaTower G t c v X Z) := by
  have hθ : ∀ (X Y : TF (I := I) (M := M)), SmE I M X → SmE I M Y →
      SmE I M (Work.Diff.EXT.ConnCov.covDiff G t X Y) :=
    fun X Y hX hY =>
      (lcOf_apply_smE hLC (G t) X Y hX hY).sub_section (lcOf_apply_smE hLC (G 0) X Y hX hY)
  have hbase : RicFlip.deltaBaseM Ĝ t
      = fun (_ : Fin 0 → TF (I := I) (M := M)) X Y =>
          -(Work.Diff.EXT.ConnCov.covDiff G t X Y) := by
    funext w X' Y'
    show Work.Diff.EXT.ConnCov.covDiff Ĝ t X' Y'
      = -(Work.Diff.EXT.ConnCov.covDiff G t X' Y')
    funext y
    simp only [Work.Diff.EXT.ConnCov.covDiff]
    rw [h0, hT]
    exact (neg_sub _ _).symm
  calc RicFlip.deltaTowerM Ĝ t c v X Z
      = RicFlip.vtowerM (Ĝ t) (RicFlip.deltaBaseM Ĝ t) c v X Z := rfl
    _ = RicFlip.vtowerM (G 0)
          (fun (_ : Fin 0 → TF (I := I) (M := M)) X Y =>
            -(Work.Diff.EXT.ConnCov.covDiff G t X Y)) c v X Z := by
        rw [hT, hbase]
    _ = -(RicFlip.vtowerM (G 0)
          (fun (_ : Fin 0 → TF (I := I) (M := M)) X Y =>
            Work.Diff.EXT.ConnCov.covDiff G t X Y) c v X Z) :=
        vtowerM_neg hLC (G 0) (fun X Y => Work.Diff.EXT.ConnCov.covDiff G t X Y) hθ c v X Z
          hv hX hZ
    _ = -(DTB.deltaTower G t c v X Z) := by
        rw [vtowerM_eq_vtower]
        rfl

end aux

theorem fixedDeltaAtomBndV
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hT : 0 < T)
    (C : ℝ) (hC : 0 ≤ C) (hflow : Submission.Diff.IsRicciFlow G T)
    (hbound : ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (k : ℕ) (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hA : ∀ j, j ≤ k → ∀ t ∈ Set.Ico (T / 2) T,
      Work.Diff.EXT.ATower.ValBound G t j
        (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G t) j) (B j)) :
    ∃ V : ℕ → ℝ, (∀ j, 0 ≤ V j) ∧ ∀ j, j ≤ k → ∀ t ∈ Set.Ico (T / 2) T,
      Work.Diff.EXT.ConnCov.AMB.BndV (I := I) (M := M) (fun _ : ℝ => G 0) t
        (Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM (fun s : ℝ => G (t - s)) t j) (V j) := by
  obtain ⟨C1, hC10, hC1⟩ :=
    Work.Diff.EXT.ConnCov.DTB.bndV_deltaTower (I := I) (M := M) hLC (G := G) (T := T)
      hT k B hB hA
  refine ⟨fun j => C1 j * Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * T / 2) ^ j
      * Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * T / 2)
      * Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * T / 2)
      * Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * T / 2), ?_, ?_⟩
  · intro j
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hC10 j)
            (pow_nonneg (Real.exp_nonneg _) j)) (Real.exp_nonneg _)) (Real.exp_nonneg _))
      (Real.exp_nonneg _)
  · intro j hj t ht
    -- the reversed family's `δ`-tower is minus the `DTB` one
    have hflip : ∀ (v : Fin j → TF (I := I) (M := M)) (X Z : TF (I := I) (M := M)),
        (∀ i, SmE I M (v i)) → SmE I M X → SmE I M Z →
        Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM (fun s : ℝ => G (t - s)) t j v X Z
          = -(Work.Diff.EXT.ConnCov.DTB.deltaTower G t j v X Z) :=
      fun v X Z hv hX hZ =>
        deltaTowerM_flip (I := I) (M := M) hLC G t (Ĝ := fun s : ℝ => G (t - s))
          (by simp) (by simp) j v X Z hv hX hZ
    -- rewriting the negation away, the bound holds in the moving metric
    have h2 : Work.Diff.EXT.ConnCov.AMB.BndV (I := I) (M := M) G t
        (Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM (fun s : ℝ => G (t - s)) t j) (C1 j) := by
      intro v X Z hv hX hZ x
      have hww : (G t).inner x
            ((Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM (fun s : ℝ => G (t - s)) t j v X Z) x)
            ((Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM (fun s : ℝ => G (t - s)) t j v X Z) x)
          = (G t).inner x (Work.Diff.EXT.ConnCov.DTB.deltaTower G t j v X Z x)
              (Work.Diff.EXT.ConnCov.DTB.deltaTower G t j v X Z x) := by
        rw [hflip v X Z hv hX hZ]
        simp
      rw [hww]
      exact hC1 j hj t ht v X Z hv hX hZ x
    -- transfer to the initial metric
    exact bndV_metric_le (I := I) (M := M) (G := G) (C₀ := C) (T := T) hT hC hmet ht
      (Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM (fun s : ℝ => G (t - s)) t j)
      (C := C1 j) (hC10 j) h2

end Work.Diff.EXT.ATower
