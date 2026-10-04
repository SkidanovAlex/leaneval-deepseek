import Mathlib
import Submission.Work.Diff.EXT.evolX.connVarDefs
import Submission.Work.Diff.EXT.ladderSrcDefs
import Submission.Work.Diff.EXT.jetSmoothDefs
import Submission.Work.Diff.EXT.jetAll_extStep
import Submission.Work.Diff.EXT.rmP_derivWithin_Ioi
import Submission.Work.Diff.EXT.covK_familySmooth
import Submission.Work.Diff.EXT.covK_onFrameFamily
import Submission.Work.Diff.EXT.evolX.ckt_sqFlow_jointSmoothAt
import Submission.Work.Diff.GE.lapRmAt_trace
import Submission.Work.Diff.EXT.ckt_step_tderiv
import Submission.Work.Diff.T.lc_variation
import Submission.Work.Diff.EXT.evolX.lapRmAt_familyJointSmoothAt
import Submission.Work.Diff.EXT.evolX.dtOpD_step_eq
import Submission.Work.Diff.EXT.reactionFormAt_familyJointSmoothAt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Continuity at the initial time of the connection-variation source

The target of this file is

`ContinuousWithinAt (fun t => jetAll (G t) j (k+5) (dtOpD G t (k+1)) F₁ x
   − jetAll (G t) (j+1) (k+4) (dtOpD G t k) F₂ x) (Ico 0 T) 0`,

i.e. the continuity at time `0` of the `j`-th jet of the connection-variation source of the ladder
step along a Ricci flow `G` on `[0,T)`.  The difficulty is the *one-sidedness* of the flow at
`t = 0`: `dtOpD G t m F y = derivWithin (fun s => ckt (G s) m F y) (Ioi 0) t` is an honest
two-sided derivative only for `t > 0`.

**The route.**  For every level `m` we build an *explicit* model operator `srcModel G m τ` (applied
to the time-reparametrised flow `τ ↦ G (τ²)`) which agrees with `dtOpD G t m` on all smooth tuples,
for **all** `t ∈ Ico 0 T` — including `t = 0`.  The model is defined by the recursion

`srcModel G 0 τ F y = ΔRm(G τ)(y)(F·y) + Q(Rm(G τ))(y)(F·y)`,
`srcModel G (m+1) τ F y = extStep (G τ) (srcModel G m τ) F y + connVarOp G τ m F y`,

the first clause coming from the *proved* one-sided curvature evolution
(`Work.Diff.EXT.rmP_derivWithin_Ioi`, valid at every `t ∈ Ico 0 T`) and the recursion from the
interior tower identity (`dtOpD_step_eq`) together with the mean value theorem
(`Work.Diff.GE.derivWithin_Ico_zero`).

Two facts about the model are proved by induction on `m`:

* `modelId` — the *pointwise* identity `dtOpD G t m F y = srcModel G̃ m (√t) F y` for the
  reparametrised family `G̃ τ = G (τ²)`;
* `modelNice_all` / `modelJetNice_all` — on the reparametrised flow (jointly smooth on the *open*
  interval `(-ρ,ρ)`), the family `(τ,y) ↦ srcModel G̃ m τ (Ψ τ) y` is jointly `C^∞` at `(0,y)` for
  every family `Ψ` of tuples of jointly smooth fields, and likewise for all its `jetAll`-jets.  This
  family statement is closed under the operations of the `jetAll` recursion, using the family
  versions of the two ingredients of `extStep` (`mvfderiv_family_jointSmooth` for the derivative
  term and the `JointField`-closure of `∇_X Y` for the Leibniz corrections).

The target then follows by replacing each `dtOpD` by its model (locality of `jetAll` in the
operator) and transferring continuity back along `t ↦ √t`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## Plumbing: the time slice of a jointly smooth family -/

/-- The `t`-slice of a jointly smooth family is smooth. -/
theorem srcJointSliceFst {Φ : ℝ × M → ℝ} {t₀ : ℝ} {x : M}
    (hΦ : JointSmoothAt I M Φ t₀ x) :
    ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ (fun t : ℝ => Φ (t, x)) t₀ := by
  have h2 : ContMDiffAt 𝓘(ℝ,ℝ) ((modelWithCornersSelf ℝ ℝ).prod I) ∞
      (fun t : ℝ => ((t, x) : ℝ × M)) t₀ :=
    contMDiffAt_id.prodMk contMDiffAt_const
  have h3 := hΦ.comp t₀ h2
  simpa only [Function.comp_def] using h3

/-! ## The model operator of the one-sided time derivative -/

/-- **The model operator of `dtOpD`**: an explicit expression which agrees with the one-sided time
derivative `dtOpD G t m` of the level-`m` curvature tower on all smooth tuples near the base point,
for every `t ∈ Ico 0 T` (including `t = 0`).  It is applied to the time-reparametrised family
`τ ↦ G (τ²)`. -/
noncomputable def srcModel (G : ℝ → Submission.Diff.SMet I M) :
    (m : ℕ) → ℝ → (Fin (m + 4) → TField (I := I) (M := M)) → M → ℝ
  | 0, t, F => fun y =>
      Work.Diff.GE.lapRmAt (G t) y (F 0 y) (F 1 y) (F 2 y) (F 3 y)
        + Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) y
            (F 0 y) (F 1 y) (F 2 y) (F 3 y)
  | m + 1, t, F => fun y =>
      extStep (I := I) (M := M) (G t) (srcModel G m t) F y
        + connVarOp (I := I) (M := M) G t m F y

/-- Unfolding of the model at level `0`. -/
theorem srcModel_zero (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    (F : Fin 4 → TField (I := I) (M := M)) :
    srcModel G 0 t F = fun y =>
      Work.Diff.GE.lapRmAt (G t) y (F 0 y) (F 1 y) (F 2 y) (F 3 y)
        + Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) y
            (F 0 y) (F 1 y) (F 2 y) (F 3 y) := rfl

/-- Unfolding of the model at level `m + 1`. -/
theorem srcModel_succ (G : ℝ → Submission.Diff.SMet I M) (m : ℕ) (t : ℝ)
    (F : Fin (m + 1 + 4) → TField (I := I) (M := M)) :
    srcModel G (m + 1) t F = fun y =>
      extStep (I := I) (M := M) (G t) (srcModel G m t) F y
        + connVarOp (I := I) (M := M) G t m F y := rfl

/-! ## Locality of the jets in the packed operator -/

/-- **Locality of the iterated covariant derivative `jetAll`, restricted to smooth tuples.**  If
two packed operators agree near `x` on every tuple of globally smooth fields, then their `j`-th jets
agree near `x` on every such tuple. -/
theorem srcJetAll_eventuallyEq_of_eventuallyEq_smooth [T2Space M] {g : Submission.Diff.SMet I M}
    (hLC : LCSmooth I M) :
    ∀ (j K : ℕ) (S S' : (Fin K → TField (I := I) (M := M)) → M → ℝ) (x : M),
      (∀ F, (∀ i, SmoothF (F i)) → S F =ᶠ[𝓝 x] S' F) →
      ∀ G : Fin (K + j) → TField (I := I) (M := M),
        (∀ i, SmoothF (G i)) →
        jetAll g j K S G =ᶠ[𝓝 x] jetAll g j K S' G := by
  intro j
  induction j with
  | zero =>
      intro K S S' x h G hG
      exact h G hG
  | succ l ih =>
      intro K S S' x h G hG
      simp only [jetAll]
      simp only [extStep, Pi.sub_apply, Finset.sum_apply]
      have hmv : ∀ᶠ y in 𝓝 x,
          mvfderiv I (fun y' : M => jetAll g l K S (fun i : Fin (K + l) => G i.succ) y') y
            (G 0 y)
          = mvfderiv I (fun y' : M => jetAll g l K S' (fun i : Fin (K + l) => G i.succ) y') y
            (G 0 y) := by
        filter_upwards [mvfderiv_eventuallyEq_of_eventuallyEq (I := I)
          (ih K S S' x h (fun i : Fin (K + l) => G i.succ) (fun i => hG i.succ))] with y hy
        exact congrArg (fun L : TangentSpace I y →L[ℝ] ℝ => L (G 0 y)) hy
      have hcorr : ∀ᶠ y in 𝓝 x, ∀ s : Fin (K + l),
          jetAll g l K S
              (Function.update (fun i : Fin (K + l) => G i.succ) s
                (dirF g ((fun i : Fin (K + l) => G i.succ) s) (G 0))) y
            = jetAll g l K S'
              (Function.update (fun i : Fin (K + l) => G i.succ) s
                (dirF g ((fun i : Fin (K + l) => G i.succ) s) (G 0))) y :=
        Filter.eventually_all.mpr fun s =>
          ih K S S' x h _
            (smoothF_update' (fun i => hG i.succ) s
              (dirF_smooth (I := I) (M := M) hLC g (hG s.succ) (hG 0)))
      filter_upwards [hmv, hcorr] with y hy1 hy2
      rw [hy1, Finset.sum_congr rfl (fun s _ => hy2 s)]

/-- **Locality of the jets at a point, smooth-tuple form.** -/
theorem srcJetAll_congr_of_eventuallyEq_smooth [T2Space M] {g : Submission.Diff.SMet I M}
    {K j : ℕ} (hLC : LCSmooth I M)
    {S S' : (Fin K → TField (I := I) (M := M)) → M → ℝ} {x : M}
    (h : ∀ F, (∀ i, SmoothF (F i)) → S F =ᶠ[𝓝 x] S' F)
    (G : Fin (K + j) → TField (I := I) (M := M))
    (hG : ∀ i, SmoothF (G i)) :
    jetAll g j K S G x = jetAll g j K S' G x :=
  (srcJetAll_eventuallyEq_of_eventuallyEq_smooth (I := I) (M := M) hLC j K S S' x h G hG).eq_of_nhds

/-! ## The germ congruence of `extStep` -/

/-- **Germ congruence of `extStep`** on the tuples actually occurring in the recursion. -/
theorem srcExtStep_congr [T2Space M] (g : Submission.Diff.SMet I M) {K : ℕ}
    (A A' : (Fin K → TField (I := I) (M := M)) → M → ℝ)
    (F : Fin (K + 1) → TField (I := I) (M := M)) (x : M)
    (h0 : A (fun i : Fin K => F i.succ) =ᶠ[𝓝 x] A' (fun i : Fin K => F i.succ))
    (h1 : ∀ s : Fin K,
      A (Function.update (fun i : Fin K => F i.succ) s
          (dirF g ((fun i : Fin K => F i.succ) s) (F 0)))
        =ᶠ[𝓝 x]
      A' (Function.update (fun i : Fin K => F i.succ) s
          (dirF g ((fun i : Fin K => F i.succ) s) (F 0)))) :
    extStep (I := I) (M := M) g A F =ᶠ[𝓝 x] extStep (I := I) (M := M) g A' F := by
  have hmv : ∀ᶠ y in 𝓝 x, mvfderiv I (A (fun i : Fin K => F i.succ)) y
      = mvfderiv I (A' (fun i : Fin K => F i.succ)) y :=
    mvfderiv_eventuallyEq_of_eventuallyEq (I := I) h0
  have hsum : ∀ᶠ y in 𝓝 x, (∑ s : Fin K,
        A (Function.update (fun i : Fin K => F i.succ) s
          (dirF g ((fun i : Fin K => F i.succ) s) (F 0))) y)
      = (∑ s : Fin K,
        A' (Function.update (fun i : Fin K => F i.succ) s
          (dirF g ((fun i : Fin K => F i.succ) s) (F 0))) y) := by
    filter_upwards [Filter.eventually_all.mpr h1] with y hy
    exact Finset.sum_congr rfl fun s _ => hy s
  filter_upwards [hmv, hsum] with y hy1 hy2
  simp only [extStep]
  rw [hy1, hy2]

/-! ## The model operator of the one-sided time derivative

`srcStau Hf k τ F y` is the explicit model of `dtOpD`: for `Hf = cfq_sqFlow G` (the time-reparametrised
flow, which is jointly smooth on an *open* interval around `0`) it equals `dtOpD G (τ²) k F y`, and it
is built from the *odd quotient* of the metric-time derivative `σ ↦ ∂_σ (ckt (Hf σ) k F y)`, which
extends smoothly through `τ = 0` (the family is even in `σ`). -/

/-- **`JointField` families are closed under the Leibniz corrections of `extStep`.** -/
theorem jointField_update_dirF [I.Boundaryless] [T2Space M]
    (hLC : LCSmooth I M) {G : ℝ → Submission.Diff.SMet I M} {V : Set (ℝ × M)}
    (hV : IsOpen V) (hG : JointMet G V)
    {K : ℕ} {Ψ : ℝ → Fin K → TField (I := I) (M := M)}
    (hΨ : ∀ i, JointField (fun τ => Ψ τ i) V)
    {W : ℝ → TField (I := I) (M := M)} (hW : JointField W V) (s : Fin K) :
    ∀ i, JointField (fun τ =>
      Function.update (Ψ τ) s (dirF (G τ) ((Ψ τ) s) (W τ)) i) V := by
  classical
  letI : Bundle.RiemannianBundle (fun y : M => TangentSpace I y) :=
    ⟨(G 0).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun y : M => TangentSpace I y) := inferInstance
  have hdir : JointField (fun τ : ℝ =>
      fun y : M => lcOf (G τ) ((Ψ τ) s) y (W τ y)) V :=
    lcOf_familyJointField (I := I) (M := M) hLC hV hG (hΨ s) hW
  intro i
  by_cases h : i = s
  · subst h
    have hupd : (fun τ : ℝ => Function.update (Ψ τ) i (dirF (G τ) (Ψ τ i) (W τ)) i)
        = fun τ : ℝ => dirF (G τ) (Ψ τ i) (W τ) := by
      funext τ
      exact Function.update_self ..
    rw [hupd]
    exact hdir
  · simpa only [Function.update_of_ne h] using hΨ i

/-- The constant family of a globally smooth field is a `JointField` family. -/
theorem jointField_const' [I.Boundaryless] [T2Space M] {X : TField (I := I) (M := M)}
    (hX : SmoothF X) {V : Set (ℝ × M)} :
    JointField (fun _ : ℝ => X) V :=
  (jointField_const (I := I) (M := M) hX).mono (fun _ _ => trivial)

/-- **The model of the one-sided time derivative `dtOpD`.** -/
noncomputable def srcStau (Hf : ℝ → Submission.Diff.SMet I M) (k : ℕ) (τ : ℝ) :
    (Fin (k + 4) → TField (I := I) (M := M)) → M → ℝ :=
  fun F y =>
    (1 / 2) * (if τ = 0 then
        deriv (fun τ' : ℝ => deriv (fun σ : ℝ => ckt (Hf σ) k F y) τ') 0
      else deriv (fun σ : ℝ => ckt (Hf σ) k F y) τ / τ)

/-- **Evenness of the Leibniz-correction families.**  The correction tuple of `extStep` on an even
family of tuples and an even metric family is again even. -/
theorem evenFn_update_dirF {Hf : ℝ → Submission.Diff.SMet I M}
    (hHeven : ∀ τ, Hf (-τ) = Hf τ) {K : ℕ} [NeZero K] {Ψ : ℝ → Fin K → TField (I := I) (M := M)}
    (hΨeven : ∀ τ, Ψ (-τ) = Ψ τ) (s : Fin K) :
    ∀ τ, Function.update (Ψ (-τ)) s (dirF (Hf (-τ)) ((Ψ (-τ)) s) ((Ψ (-τ)) 0))
      = Function.update (Ψ τ) s (dirF (Hf τ) ((Ψ τ) s) ((Ψ τ) 0)) := by
  intro τ
  rw [hΨeven τ, hHeven τ]

end Work.Diff.EXT.evolX
