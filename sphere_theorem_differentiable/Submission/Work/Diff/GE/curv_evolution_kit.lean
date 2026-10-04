import Mathlib
import Submission.Diff.Evol
import Submission.Work.Diff.GE.scal_lapl_basic
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.Evol.Calc
import Submission.Work.Diff.GE.scal_lapl
import Submission.Work.Diff.Evol.RicPhi
import Submission.Work.Diff.Evol.rmP_fixed_deriv
import Submission.Work.Diff.Evol.rmFrame_moving_deriv
import Submission.Work.Diff.Evol.covDLC_B_identity
import Submission.Work.Diff.Evol.lapRmFrame_expansion
import Submission.Work.Diff.Evol.ricArr_rmFrame_eq_ricAt
import Submission.Work.Diff.Evol.ricci_identity_rm
import Submission.Work.Diff.EXT.ric_bound_of_curvBound
import Submission.Work.Diff.GE.Qhat_identity_kit
import Submission.Work.Diff.GE.cov2Ric_commutator

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Hamilton's curvature evolution `∂ₜ Rm = Δ Rm + Q(Rm)` (scalar-free assembly)

`Submission.Diff.CurvEvolution` (contract CE) says: along a Ricci flow, in a family of frames `e s`
which is `G s`-orthonormal and moves by the Uhlenbeck rule `∂ₛ eᵢ = Ric(eᵢ)^♯`, the curvature
components satisfy `∂ₛ rmFrame = lapRmFrame + Q (rmFrame)`.

This file assembles that statement from the pieces proved in the `Evol` area together with two
purely algebraic inputs proved under `Work.Diff.GE`:

* `Work.Diff.Evol.rmP_fixed_deriv` — the derivative of the curvature components at *fixed* vectors,
  `= −2 Ric(R(a,b)d, c) + ⟨(∇_a A)(b,d) − (∇_bA)(a,d), c⟩`;
* `Work.Diff.Evol.covDLC_B_identity` — the second factor is the six-term `∇²Ric` combination;
* `Work.Diff.GE.cov2Ric_commutator` (Ricci identity for `Ric`) — the antisymmetric part of the
  six-term combination is `−Ric(R(a,b)d,c) − Ric(d,R(a,b)c)`, leaving the `c`-trace identity
  `Work.Diff.GE.ricAt_rmVec_expand`;
* `Work.Diff.Evol.lapRmFrame_expansion` — `lapRmFrame = (∇²Ric-combination) + Q̂(Rm)`;
* `Work.Diff.Evol.rmFrame_moving_deriv` — the chain rule for the moving frame, with the
  frame-motion array `Xact`;
* `Work.Diff.GE.Qhat_identity_kit` — the algebra `−Q̂ + Xact + ricact = Q`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [CompactSpace M]

/-! ## 1. The `Ric`-trace of the curvature contracted into the frame -/

/-- `ricAt` is linear in its middle argument, in `Finset` form. -/
theorem ricAt_sum_middle (hLC : LCSmooth I M) (g : SMet I M) (x : M) (v : TangentSpace I x)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (u : ι → TangentSpace I x) :
    ricAt (lcOf g) x (∑ i ∈ s, c i • u i) v = ∑ i ∈ s, c i * ricAt (lcOf g) x (u i) v := by
  classical
  have hcov : ContMDiffCovariantDerivative (lcOf g) ∞ := (hLC g).1.some
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      simpa using Work.Diff.EXT.ricAt_smul_middle_L g hcov x (0 : ℝ) (0 : TangentSpace I x) v
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        Work.Diff.EXT.ricAt_add_middle_L g hcov x _ _ v,
        Work.Diff.EXT.ricAt_smul_middle_L g hcov x (c a) (u a) v, ih]

/-- `ricAt` is linear in its last argument, in `Finset` form. -/
theorem ricAt_sum_last (hLC : LCSmooth I M) (g : SMet I M) (x : M) (w : TangentSpace I x)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (u : ι → TangentSpace I x) :
    ricAt (lcOf g) x w (∑ i ∈ s, c i • u i) = ∑ i ∈ s, c i * ricAt (lcOf g) x w (u i) := by
  classical
  have hcov : ContMDiffCovariantDerivative (lcOf g) ∞ := (hLC g).1.some
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      simpa using Work.Diff.EXT.ricAt_smul_last_L g hcov x (0 : ℝ) w (0 : TangentSpace I x)
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        Work.Diff.EXT.ricAt_add_last_L g hcov x w _ _,
        Work.Diff.EXT.ricAt_smul_last_L g hcov x (c a) w (u a), ih]

/-- **The `Ric`-trace of `R(f i, f j) f l`** in a `g`-orthonormal frame `f`: it is the contraction
of the curvature array with the Ricci array. -/
theorem ricAt_rmVec_expand (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (f : Fin (Module.finrank ℝ E) → TangentSpace I x) (hf : IsONFrame g x f)
    (hn : 0 < Module.finrank ℝ E) (i j k l : Fin (Module.finrank ℝ E)) :
    ricAt (lcOf g) x (rmVec (lcOf g) x (f i) (f j) (f l)) (f k)
      = ∑ c, rmFrame g x f i j c l * Work.Diff.Evol.ricArr (rmFrame g x f) c k := by
  classical
  have hexp : rmVec (lcOf g) x (f i) (f j) (f l)
      = ∑ c, g.inner x (rmVec (lcOf g) x (f i) (f j) (f l)) (f c) • f c :=
    (sum_smul_inner_eq_self (I := I) (M := M) g x hn f hf _).symm
  rw [hexp, ricAt_sum_middle (I := I) (M := M) hLC g x (f k) Finset.univ _ (fun c ↦ f c)]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Work.Diff.Evol.ricArr_rmFrame_eq_ricAt (I := I) (M := M) hLC g x f hf c k]
  rfl

/-- **The `Ric`-trace with the curvature vector in the last slot.** -/
theorem ricAt_rmVec_expand_last (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (f : Fin (Module.finrank ℝ E) → TangentSpace I x) (hf : IsONFrame g x f)
    (hn : 0 < Module.finrank ℝ E) (i j k l : Fin (Module.finrank ℝ E)) :
    ricAt (lcOf g) x (f l) (rmVec (lcOf g) x (f i) (f j) (f k))
      = ∑ c, rmFrame g x f i j c k * Work.Diff.Evol.ricArr (rmFrame g x f) l c := by
  classical
  have hexp : rmVec (lcOf g) x (f i) (f j) (f k)
      = ∑ c, g.inner x (rmVec (lcOf g) x (f i) (f j) (f k)) (f c) • f c :=
    (sum_smul_inner_eq_self (I := I) (M := M) g x hn f hf _).symm
  rw [hexp, ricAt_sum_last (I := I) (M := M) hLC g x (f l) Finset.univ _ (fun c ↦ f c)]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Work.Diff.Evol.ricArr_rmFrame_eq_ricAt (I := I) (M := M) hLC g x f hf l c]
  rfl

/-! ## 2. The value of `∂ₛ rmFrame` in an Uhlenbeck frame is `lapRmFrame + Q` -/

/-- **The pointwise value identity.**  With `f` a `G t`-orthonormal frame at `x`, the value of
`∂ₛ rmFrame (G s) x (e s)` computed by the chain rule from the fixed-vector derivative
(`rmP_fixed_deriv`) and the Uhlenbeck velocity `Md i p = Ric(f i, f p)` equals
`lapRmFrame (G t) x f + Q (rmFrame (G t) x f)`. -/
theorem curvFrame_evolution_value (hLC : LCSmooth I M) (hLV : LCVariation I M)
    (hCV : CurvVariation I M) (G : ℝ → SMet I M) (T : ℝ) (hflow : IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : M)
    (f : Fin (Module.finrank ℝ E) → TangentSpace I x) (hf : IsONFrame (G t) x f)
    (hn : 0 < Module.finrank ℝ E) :
    (fun i j k l ↦
        (-2 * ricAt (lcOf (G t)) x (rmVec (lcOf (G t)) x (f i) (f j) (f l)) (f k)
            + (G t).inner x (covDLC G t (smoothExt x (f i)) (smoothExt x (f j))
                (smoothExt x (f l)) x
              - covDLC G t (smoothExt x (f j)) (smoothExt x (f i)) (smoothExt x (f l)) x) (f k))
          + ∑ p, (ricAt (lcOf (G t)) x (f i) (f p) * rmP (G t) x (f p) (f j) (f k) (f l)
                + ricAt (lcOf (G t)) x (f j) (f p) * rmP (G t) x (f i) (f p) (f k) (f l)
                + ricAt (lcOf (G t)) x (f k) (f p) * rmP (G t) x (f i) (f j) (f p) (f l)
                + ricAt (lcOf (G t)) x (f l) (f p) * rmP (G t) x (f i) (f j) (f k) (f p)))
      = lapRmFrame (G t) x f + Q (rmFrame (G t) x f) := by
  funext i j k l
  classical
  simp only [Pi.add_apply]
  set R : Curv4 (Module.finrank ℝ E) := rmFrame (G t) x f with hRdef
  have hRalg : IsAlgCurv R := isAlgCurv_rmFrame_kit hLC (G t) x f
  -- the frame-motion array is `Xact`
  have hX : (∑ p, (ricAt (lcOf (G t)) x (f i) (f p) * rmP (G t) x (f p) (f j) (f k) (f l)
        + ricAt (lcOf (G t)) x (f j) (f p) * rmP (G t) x (f i) (f p) (f k) (f l)
        + ricAt (lcOf (G t)) x (f k) (f p) * rmP (G t) x (f i) (f j) (f p) (f l)
        + ricAt (lcOf (G t)) x (f l) (f p) * rmP (G t) x (f i) (f j) (f k) (f p)))
      = Work.Diff.Evol.Xact R i j k l := by
    rw [hRdef]
    simp only [Work.Diff.Evol.Xact,
      Work.Diff.Evol.ricArr_rmFrame_eq_ricAt (I := I) (M := M) hLC (G t) x f hf]
    simp only [rmFrame_eq_rmP']
  -- the fixed-vector part, via the second Bianchi identity for `∂ₜ∇`
  have hD : (-2 * ricAt (lcOf (G t)) x (rmVec (lcOf (G t)) x (f i) (f j) (f l)) (f k)
        + (G t).inner x (covDLC G t (smoothExt x (f i)) (smoothExt x (f j))
            (smoothExt x (f l)) x
          - covDLC G t (smoothExt x (f j)) (smoothExt x (f i)) (smoothExt x (f l)) x) (f k))
      = -2 * ricAt (lcOf (G t)) x (rmVec (lcOf (G t)) x (f i) (f j) (f l)) (f k)
        + (-Work.Diff.Evol.cov2Ric (G t) x (f i) (f j) (f l) (f k) - Work.Diff.Evol.cov2Ric (G t) x (f i) (f l) (f j) (f k)
          + Work.Diff.Evol.cov2Ric (G t) x (f i) (f k) (f j) (f l) + Work.Diff.Evol.cov2Ric (G t) x (f j) (f i) (f l) (f k)
          + Work.Diff.Evol.cov2Ric (G t) x (f j) (f l) (f i) (f k)
          - Work.Diff.Evol.cov2Ric (G t) x (f j) (f k) (f i) (f l)) := by
    rw [Work.Diff.Evol.covDLC_B_identity (I := I) (M := M) hLC hLV G T hflow ht x
      (f i) (f j) (f k) (f l)]
  -- the Ricci identity for `Ric`: the antisymmetric pair of `cov2Ric` is the `Ric`-action
  have hcom := Work.Diff.GE.cov2Ric_commutator (I := I) (M := M) hLC (G t) x (f i) (f j) (f l) (f k)
  -- the Laplace expansion and the algebra of the reaction term
  have hLap := Work.Diff.Evol.lapRmFrame_expansion (I := I) (M := M) hLC (G t) x f hf i j k l
  rw [← hRdef] at hLap
  have hQ := Qhat_identity_kit R hRalg i j k l
  -- the traces of the curvature contracted into the frame
  have hexp1 := ricAt_rmVec_expand (I := I) (M := M) hLC (G t) x f hf hn i j k l
  have hexp2 := ricAt_rmVec_expand_last (I := I) (M := M) hLC (G t) x f hf hn i j k l
  have hricact : Work.Diff.Evol.ricact R i j k l
      = -ricAt (lcOf (G t)) x (rmVec (lcOf (G t)) x (f i) (f j) (f l)) (f k)
        + ricAt (lcOf (G t)) x (f l) (rmVec (lcOf (G t)) x (f i) (f j) (f k)) := by
    rw [hRdef]
    simp only [Work.Diff.Evol.ricact]
    rw [← hexp1, ← hexp2]
  -- the cov2Ric bookkeeping
  have hcore : -2 * ricAt (lcOf (G t)) x (rmVec (lcOf (G t)) x (f i) (f j) (f l)) (f k)
      + (-Work.Diff.Evol.cov2Ric (G t) x (f i) (f j) (f l) (f k) - Work.Diff.Evol.cov2Ric (G t) x (f i) (f l) (f j) (f k)
        + Work.Diff.Evol.cov2Ric (G t) x (f i) (f k) (f j) (f l) + Work.Diff.Evol.cov2Ric (G t) x (f j) (f i) (f l) (f k)
        + Work.Diff.Evol.cov2Ric (G t) x (f j) (f l) (f i) (f k) - Work.Diff.Evol.cov2Ric (G t) x (f j) (f k) (f i) (f l))
      = (Work.Diff.Evol.cov2Ric (G t) x (f i) (f k) (f j) (f l) - Work.Diff.Evol.cov2Ric (G t) x (f i) (f l) (f j) (f k)
        + Work.Diff.Evol.cov2Ric (G t) x (f j) (f l) (f i) (f k) - Work.Diff.Evol.cov2Ric (G t) x (f j) (f k) (f i) (f l))
        + (-ricAt (lcOf (G t)) x (rmVec (lcOf (G t)) x (f i) (f j) (f l)) (f k)
          + ricAt (lcOf (G t)) x (f l) (rmVec (lcOf (G t)) x (f i) (f j) (f k))) := by
    linarith [hcom]
  rw [hD, hX, hcore, hLap, ← hQ, hricact]
  ring

/-! ## 3. Contract CE -/

/-- **`CurvEvolution` from the shared pieces** (a second, self-contained assembly; the `Evol` area's
`Work.Diff.Evol.curv_evolution` proves the same statement). -/
theorem curv_evolution_kit
    (hLC : LCSmooth I M) (hLV : LCVariation I M) (hCV : CurvVariation I M) :
    CurvEvolution I M := by
  intro G T hflow t ht x e hon hd
  by_cases hn : 0 < Module.finrank ℝ E
  · -- the frame at time `t`
    set f : Fin (Module.finrank ℝ E) → TangentSpace I x := fun i ↦ e t i with hf
    have hfon : IsONFrame (G t) x f := by
      intro i j
      exact hon t ht i j
    -- the fixed-vector derivative values
    have hD : ∀ p q r u : Fin (Module.finrank ℝ E),
        HasDerivAt (fun s ↦ rmP (G s) x (f p) (f q) (f r) (f u))
          (-2 * ricAt (lcOf (G t)) x (rmVec (lcOf (G t)) x (f p) (f q) (f u)) (f r)
            + (G t).inner x (covDLC G t (smoothExt x (f p)) (smoothExt x (f q))
                (smoothExt x (f u)) x
              - covDLC G t (smoothExt x (f q)) (smoothExt x (f p)) (smoothExt x (f u)) x)
                (f r)) t :=
      fun p q r u ↦ Work.Diff.Evol.rmP_fixed_deriv (I := I) (M := M) hLC hLV hCV G T hflow
        ht x (f p) (f q) (f r) (f u)
    -- the chain rule for the moving frame
    have hchain := Work.Diff.Evol.rmFrame_moving_deriv (I := I) (M := M) hLC G t x f e
      (fun i p ↦ ricAt (lcOf (G t)) x (f i) (f p))
      (fun p q r u ↦ -2 * ricAt (lcOf (G t)) x (rmVec (lcOf (G t)) x (f p) (f q) (f u)) (f r)
        + (G t).inner x (covDLC G t (smoothExt x (f p)) (smoothExt x (f q))
            (smoothExt x (f u)) x
          - covDLC G t (smoothExt x (f q)) (smoothExt x (f p)) (smoothExt x (f u)) x) (f r))
      (fun i ↦ rfl) hfon hd hD
    -- identify the value
    refine hchain.congr_deriv ?_
    have hval := curvFrame_evolution_value (I := I) (M := M) hLC hLV hCV G T hflow ht x f hfon hn
    rw [← hval]
  · -- degenerate case
    have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hn
    have hval : ∀ v : Curv4 (Module.finrank ℝ E), v = 0 := by
      intro v
      funext i
      exact Fin.elim0 (h0 ▸ i)
    have hfun : (fun s : ℝ ↦ rmFrame (G s) x (e s))
        = fun _ : ℝ ↦ (0 : Curv4 (Module.finrank ℝ E)) := by
      funext s
      exact hval _
    rw [hfun, hval (lapRmFrame (G t) x (e t) + Q (rmFrame (G t) x (e t)))]
    exact hasDerivAt_const (c := (0 : Curv4 (Module.finrank ℝ E))) (x := t)

end Work.Diff.GE
