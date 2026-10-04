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
import Submission.Work.Diff.EXT.evolX.srcStauDefs
import Submission.Work.Diff.EXT.evolX.srcStau_eq_dtOpD
import Submission.Work.Diff.EXT.evolX.srcJet_jointSmooth
import Submission.Work.Diff.EXT.evolX.mvfderivFamJointSmoothV2
import Submission.Work.Diff.EXT.oddDivJointSmooth
import Submission.Work.Diff.EXT.evolX.covK_familySmooth_twoParam

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

/-! ## The `t = 0` end of the tower: joint smoothness of `srcStau` from the odd quotient -/

/-- **The two-variable tower is jointly smooth.**  `(σ, τ, y) ↦ ∇^k Rm` of the metric `Hf σ`
evaluated at `y` on the tuple `Ψ τ` is jointly `C^∞`, for a metric family `Hf` jointly smooth on the
open set `V`, a tuple family `Ψ` whose every time slice is a jointly smooth family of fields on `V`
(`JointField`), and `(σ, y)`, `(τ, y) ∈ V`.

This is the two-parameter instance of `Work.Diff.EXT.evolX.covK_familySmooth_twoParam` (the
two-independent-time version of `Work.Diff.EXT.covK_familySmooth`), transported to `ckt` through
`Work.Diff.EXT.ckt_eq_covKRmExt`. -/
theorem ckt_twoParam_jointSmooth'
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {Hf : ℝ → Submission.Diff.SMet I M} {V : Set (ℝ × M)} (hV : IsOpen V)
    (hG : Work.Diff.EXT.JointMet Hf V) (k : ℕ)
    {Ψ : ℝ → Fin (k + 4) → Work.Diff.EXT.TField (I := I) (M := M)}
    (hΨ : ∀ i, Work.Diff.EXT.JointField (fun τ => Ψ τ i) V) :
    ∀ σ τ y, (σ, y) ∈ V → (τ, y) ∈ V →
      ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod ((modelWithCornersSelf ℝ ℝ).prod I))
        (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × (ℝ × M) => Work.Diff.EXT.ckt (Hf q.1) k (Ψ q.2.1) q.2.2)
        (σ, (τ, y)) := by
  intro σ τ y hσy hτy
  have h4 := Work.Diff.EXT.evolX.covK_familySmooth_twoParam (I := I) (M := M) hLC hV hG k
    (Vf := fun _ τ i => Ψ τ (Fin.castAdd 4 i))
    (fun i => Work.Diff.EXT.evolX.jointField2_of_jointField (I := I) (M := M)
      (hΨ (Fin.castAdd 4 i)))
    (A := fun _ τ => Ψ τ (Fin.natAdd k 0))
    (B := fun _ τ => Ψ τ (Fin.natAdd k 1))
    (C := fun _ τ => Ψ τ (Fin.natAdd k 2))
    (D := fun _ τ => Ψ τ (Fin.natAdd k 3))
    (Work.Diff.EXT.evolX.jointField2_of_jointField (I := I) (M := M) (hΨ _))
    (Work.Diff.EXT.evolX.jointField2_of_jointField (I := I) (M := M) (hΨ _))
    (Work.Diff.EXT.evolX.jointField2_of_jointField (I := I) (M := M) (hΨ _))
    (Work.Diff.EXT.evolX.jointField2_of_jointField (I := I) (M := M) (hΨ _))
  have hfun : (fun q : ℝ × (ℝ × M) => Work.Diff.EXT.ckt (Hf q.1) k (Ψ q.2.1) q.2.2)
      = fun q : ℝ × (ℝ × M) => Work.Diff.EXT.covKRmExt (Hf q.1) k
          (fun i : Fin k => Ψ q.2.1 (Fin.castAdd 4 i))
          (Ψ q.2.1 (Fin.natAdd k 0)) (Ψ q.2.1 (Fin.natAdd k 1))
          (Ψ q.2.1 (Fin.natAdd k 2)) (Ψ q.2.1 (Fin.natAdd k 3)) q.2.2 := by
    funext q
    exact Work.Diff.EXT.ckt_eq_covKRmExt (Hf q.1) k (Ψ q.2.1) q.2.2
  rw [hfun]
  exact h4.contMDiffAt ((Work.Diff.EXT.evolX.isOpen_W3 hV).mem_nhds ⟨hσy, hτy⟩)

/-- **Multiplication by a constant preserves joint smoothness.** -/
theorem jointSmoothAt_const_mul {Φ : ℝ × M → ℝ} {t₀ : ℝ} {x : M} (c : ℝ)
    (h : Work.Diff.EXT.JointSmoothAt I M Φ t₀ x) :
    Work.Diff.EXT.JointSmoothAt I M (fun p : ℝ × M => c * Φ p) t₀ x :=
  (contMDiffAt_const (c := c)).mul h

/-- **The hypothesis `hbase` of the jet induction**: for a `JointField` family `Ψ` which is even in
its time variable and a metric family `Hf` which is even too, the model `srcStau` of the one-sided
time derivative is jointly `C^∞` at `(0, x)`.

Indeed `srcStau Hf k τ (Ψ τ) = ½ · oddQuotient (∂_σ (ckt (Hf σ) k (Ψ τ)))|_{σ = τ}`: the inner
function `N (τ, y) = ∂_σ (ckt (Hf σ) k (Ψ τ) y)|_{σ = τ}` is jointly `C^∞` at `(0,x)` (the
two-variable tower `(σ, τ, y) ↦ ckt (Hf σ) k (Ψ τ) y` is, by
`Work.Diff.EXT.ckt_twoParam_jointSmooth`, and the `σ`-derivative of a jointly smooth family is
jointly smooth, `Work.Diff.EXT.evolX.jointSmoothAt_tDeriv`), it is *odd* in `τ` (the metric and the
tuple are even in their time variables), and the odd quotient extends smoothly through `τ = 0` by
`Work.Diff.EXT.oddDivJointSmooth`. -/
theorem srcStau_jointSmooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {Hf : ℝ → Submission.Diff.SMet I M} {V : Set (ℝ × M)} (hV : IsOpen V)
    (hG : Work.Diff.EXT.JointMet Hf V) (hHeven : ∀ τ, Hf (-τ) = Hf τ)
    {k : ℕ} {x : M} (hx : (0, x) ∈ V)
    {Ψ : ℝ → Fin (k + 4) → Work.Diff.EXT.TField (I := I) (M := M)}
    (hΨ : ∀ i, Work.Diff.EXT.JointField (fun τ => Ψ τ i) V)
    (hΨeven : ∀ τ, Ψ (-τ) = Ψ τ) :
    Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M => Work.Diff.EXT.evolX.srcStau Hf k p.1 (Ψ p.1) p.2) 0 x := by
  -- the two-variable tower is jointly `C^∞` at `(0, (0, x))`
  have h3 : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod ((modelWithCornersSelf ℝ ℝ).prod I))
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun q : ℝ × (ℝ × M) => Work.Diff.EXT.ckt (Hf q.1) k (Ψ q.2.1) q.2.2) (0, (0, x)) :=
    ckt_twoParam_jointSmooth' (I := I) (M := M) hLC hV hG k hΨ 0 0 x hx hx
  -- its `σ`-derivative, as a function of `(σ, (τ, y))`
  have hder : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod ((modelWithCornersSelf ℝ ℝ).prod I))
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun q : ℝ × (ℝ × M) =>
        deriv (fun s : ℝ => Work.Diff.EXT.ckt (Hf s) k (Ψ q.2.1) q.2.2) q.1) (0, (0, x)) :=
    Work.Diff.EXT.evolX.jointSmoothAt_tDeriv
      (I := (modelWithCornersSelf ℝ ℝ).prod I) (M := ℝ × M) h3
  -- restrict it to the diagonal `σ = τ`
  have hdiag : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I)
      ((modelWithCornersSelf ℝ ℝ).prod ((modelWithCornersSelf ℝ ℝ).prod I)) ∞
      (fun p : ℝ × M => (p.1, (p.1, p.2))) (0, x) := by
    refine ContMDiffAt.prodMk ?_ ?_
    · exact contMDiffAt_fst
    · exact ContMDiffAt.prodMk contMDiffAt_fst contMDiffAt_snd
  have hN : Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M =>
        deriv (fun s : ℝ => Work.Diff.EXT.ckt (Hf s) k (Ψ p.1) p.2) p.1) 0 x := by
    show ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ) ∞
      ((fun q : ℝ × (ℝ × M) =>
          deriv (fun s : ℝ => Work.Diff.EXT.ckt (Hf s) k (Ψ q.2.1) q.2.2) q.1)
        ∘ fun p : ℝ × M => (p.1, (p.1, p.2))) (0, x)
    exact ContMDiffAt.comp (0, x) hder hdiag
  -- it is odd in `τ`
  have hodd : ∀ τ y,
      (fun p : ℝ × M =>
        deriv (fun s : ℝ => Work.Diff.EXT.ckt (Hf s) k (Ψ p.1) p.2) p.1) (-τ, y)
        = - (fun p : ℝ × M =>
        deriv (fun s : ℝ => Work.Diff.EXT.ckt (Hf s) k (Ψ p.1) p.2) p.1) (τ, y) := by
    intro τ y
    have h1 : deriv (fun σ : ℝ => Work.Diff.EXT.ckt (Hf σ) k (Ψ τ) y) τ
        = - deriv (fun σ : ℝ => Work.Diff.EXT.ckt (Hf σ) k (Ψ τ) y) (-τ) := by
      have h := deriv_comp_neg
        (f := fun σ : ℝ => Work.Diff.EXT.ckt (Hf σ) k (Ψ τ) y) (x := τ)
      have hfun : (fun x : ℝ => Work.Diff.EXT.ckt (Hf (-x)) k (Ψ τ) y)
          = fun σ : ℝ => Work.Diff.EXT.ckt (Hf σ) k (Ψ τ) y := by
        funext x
        rw [hHeven x]
      rw [hfun] at h
      exact h
    show deriv (fun σ : ℝ => Work.Diff.EXT.ckt (Hf σ) k (Ψ (-τ)) y) (-τ)
        = - deriv (fun σ : ℝ => Work.Diff.EXT.ckt (Hf σ) k (Ψ τ) y) τ
    rw [hΨeven τ]
    linarith [h1]
  -- the odd quotient of `N` is jointly smooth
  have hQ := Work.Diff.EXT.oddDivJointSmooth (I := I) (M := M) hN hodd
  -- The value at `τ = 0` of the odd quotient of `N` is the second `σ`-derivative of the tower with
  -- the tuple frozen: the mixed term vanishes because `τ ↦ ckt (Hf σ) k (Ψ τ) y` is *even* for
  -- every `σ`.
  have hzero : ∀ y : M, (0, y) ∈ V →
      deriv (fun τ : ℝ => deriv (fun σ : ℝ => Work.Diff.EXT.ckt (Hf σ) k (Ψ τ) y) τ) 0
        = deriv (fun τ : ℝ => deriv (fun σ : ℝ => Work.Diff.EXT.ckt (Hf σ) k (Ψ 0) y) τ) 0 := by
    intro y hy
    have hD3 : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod ((modelWithCornersSelf ℝ ℝ).prod I))
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun q : ℝ × (ℝ × M) =>
          deriv (fun σ : ℝ => Work.Diff.EXT.ckt (Hf σ) k (Ψ q.2.1) q.2.2) q.1)
        (0, (0, y)) :=
      Work.Diff.EXT.evolX.jointSmoothAt_tDeriv (I := (modelWithCornersSelf ℝ ℝ).prod I)
        (M := ℝ × M)
        (ckt_twoParam_jointSmooth' (I := I) (M := M) hLC hV hG k hΨ 0 0 y hy hy)
    -- the restriction to the fixed base point `y`, with the *self* model on `ℝ × ℝ`
    have hmap : ContMDiffAt (modelWithCornersSelf ℝ (ℝ × ℝ))
        ((modelWithCornersSelf ℝ ℝ).prod ((modelWithCornersSelf ℝ ℝ).prod I)) ∞
        (fun q : ℝ × ℝ => (q.1, (q.2, y))) (0, 0) := by
      refine ContMDiffAt.prodMk ?_ ?_
      · exact (ContinuousLinearMap.fst ℝ ℝ ℝ).contMDiffAt
      · refine ContMDiffAt.prodMk ?_ ?_
        · exact (ContinuousLinearMap.snd ℝ ℝ ℝ).contMDiffAt
        · exact contMDiffAt_const
    set Φ : ℝ × ℝ → ℝ :=
      fun q => deriv (fun σ : ℝ => Work.Diff.EXT.ckt (Hf σ) k (Ψ q.2) y) q.1 with hΦdef
    have hΦsm : ContMDiffAt (modelWithCornersSelf ℝ (ℝ × ℝ))
        (modelWithCornersSelf ℝ ℝ) ∞ Φ (0, 0) := hD3.comp (0, 0) hmap
    have hfd : HasFDerivAt Φ (fderiv ℝ Φ (0, 0)) (0, 0) :=
      ((contMDiffAt_iff_contDiffAt.mp hΦsm).differentiableAt (by simp)).hasFDerivAt
    -- `τ ↦ Φ (0, τ)` is even, so `∂_τ Φ (0,0) = 0`
    have h01 : (fderiv ℝ Φ (0, 0)) ((0, 1) : ℝ × ℝ) = 0 := by
      have hc : HasDerivAt (fun τ : ℝ => ((0 : ℝ), τ)) ((0, 1) : ℝ × ℝ) 0 := by
        simpa using (hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk (hasDerivAt_id (0 : ℝ))
      have hcomp : HasDerivAt (fun τ : ℝ => Φ (0, τ))
          ((fderiv ℝ Φ (0, 0)) ((0, 1) : ℝ × ℝ)) 0 := hfd.comp_hasDerivAt 0 hc
      have hz : deriv (fun τ : ℝ => Φ (0, τ)) 0 = 0 := by
        have heven : ∀ τ : ℝ, Φ (0, -τ) = Φ (0, τ) := by
          intro τ
          rw [hΦdef]
          show deriv (fun σ : ℝ => Work.Diff.EXT.ckt (Hf σ) k (Ψ (-τ)) y) 0
              = deriv (fun σ : ℝ => Work.Diff.EXT.ckt (Hf σ) k (Ψ τ) y) 0
          rw [hΨeven τ]
        have hfun : (fun x : ℝ => Φ (0, -x)) = fun τ : ℝ => Φ (0, τ) :=
          funext fun x => heven x
        have h2 : deriv (fun τ : ℝ => Φ (0, -τ)) 0 = -deriv (fun τ : ℝ => Φ (0, τ)) 0 := by
          simpa using deriv_comp_neg (f := fun τ : ℝ => Φ (0, τ)) (x := (0 : ℝ))
        rw [hfun] at h2
        linarith
      rw [← hcomp.deriv]
      exact hz
    have hdiag1 : deriv (fun τ : ℝ => Φ (τ, τ)) 0
        = (fderiv ℝ Φ (0, 0)) ((1, 1) : ℝ × ℝ) := by
      have hc : HasDerivAt (fun τ : ℝ => ((τ, τ) : ℝ × ℝ)) ((1, 1) : ℝ × ℝ) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_id (0 : ℝ))
      have hcomp : HasDerivAt (fun τ : ℝ => Φ (τ, τ))
          ((fderiv ℝ Φ (0, 0)) ((1, 1) : ℝ × ℝ)) 0 :=
        hfd.comp_hasDerivAt (f := fun τ : ℝ => (τ, τ)) (f' := ((1, 1) : ℝ × ℝ)) 0 hc
      exact hcomp.deriv
    have hdiag2 : deriv (fun τ : ℝ => Φ (τ, 0)) 0
        = (fderiv ℝ Φ (0, 0)) ((1, 0) : ℝ × ℝ) := by
      have hc : HasDerivAt (fun τ : ℝ => ((τ, (0 : ℝ)) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ))
      have hcomp : HasDerivAt (fun τ : ℝ => Φ (τ, 0))
          ((fderiv ℝ Φ (0, 0)) ((1, 0) : ℝ × ℝ)) 0 :=
        hfd.comp_hasDerivAt (f := fun τ : ℝ => (τ, (0 : ℝ))) (f' := ((1, 0) : ℝ × ℝ)) 0 hc
      exact hcomp.deriv
    have hkey : (fderiv ℝ Φ (0, 0)) ((1, 1) : ℝ × ℝ)
        = (fderiv ℝ Φ (0, 0)) ((1, 0) : ℝ × ℝ) := by
      have hsplit : ((1, 1) : ℝ × ℝ) = ((1, 0) : ℝ × ℝ) + ((0, 1) : ℝ × ℝ) := by
        ext <;> simp
      rw [hsplit, map_add, h01, add_zero]
    rw [hdiag1, hdiag2, hkey]
  -- `srcStau` and the odd quotient of `N` agree near `(0, x)`
  have hQ2 := jointSmoothAt_const_mul (I := I) (M := M) (1 / 2) hQ
  refine hQ2.congr_of_eventuallyEq ?_
  filter_upwards [hV.mem_nhds hx] with p hp
  by_cases h0 : p.1 = 0
  · have hp' : ((0 : ℝ), p.2) ∈ V := by
      have hpp : ((0 : ℝ), p.2) = p := Prod.ext h0.symm rfl
      rwa [hpp]
    have hz := hzero p.2 hp'
    rw [h0, Work.Diff.EXT.evolX.srcStau_zero_eq]
    rw [if_pos rfl]
    rw [hz]
  · simp only [Work.Diff.EXT.evolX.srcStau]
    rw [if_neg h0, if_neg h0]

/-! ## The target -/

theorem srcConnVar_continuousAt_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (k j : ℕ) :
    ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T → ∀ x : M,
      ∀ (F₁ : Fin ((k + 1 + 4) + j) → Work.Diff.EXT.TField (I := I) (M := M)),
        (∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F₁ i)) →
      ∀ (F₂ : Fin ((k + 4) + (j + 1)) → Work.Diff.EXT.TField (I := I) (M := M)),
        (∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F₂ i)) →
        ContinuousWithinAt
          (fun t : ℝ =>
            Work.Diff.EXT.jetAll (G t) j (k + 1 + 4)
                (Work.Diff.EXT.dtOpD (I := I) (M := M) G t (k + 1)) F₁ x
              - Work.Diff.EXT.jetAll (G t) (j + 1) (k + 4)
                (Work.Diff.EXT.dtOpD (I := I) (M := M) G t k) F₂ x)
          (Set.Ico 0 T) 0 := by
  intro G T hflow x F₁ hF₁ F₂ hF₂
  by_cases hT : T ≤ 0
  · rw [Set.Ico_eq_empty_iff.mpr (not_lt.mpr hT)]
    simp [ContinuousWithinAt, nhdsWithin_empty]
  · have hTpos : 0 < T := not_le.mp hT
    obtain ⟨ρ, hρpos, hρT⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ^ 2 < T :=
      ⟨Real.sqrt T / 2, by positivity, by
        rw [div_pow, Real.sq_sqrt (le_of_lt hTpos)]; nlinarith⟩
    have hLC : Submission.Diff.LCSmooth I M := Work.EXT.lcSmooth_noBoundary (I := I) (M := M)
    set V : Set (ℝ × M) := Set.Ioo (-ρ) ρ ×ˢ (Set.univ : Set M) with hVdef
    have hViso : IsOpen V := isOpen_Ioo.prod isOpen_univ
    have hHf : Work.Diff.EXT.JointMet (Work.Diff.GE.cfq_sqFlow G) V := by
      have hsm : Submission.Diff.JointSmooth (Work.Diff.GE.cfq_sqFlow G) (Set.Ioo (-ρ) ρ) :=
        Work.Diff.GE.cfq_jointSmooth_sqFlow (I := I) (M := M) G hTpos hρpos hρT hflow.1
      exact (Work.Diff.EXT.jointMet_prod (I := I) (M := M) (Work.Diff.GE.cfq_sqFlow G)
        (Set.Ioo (-ρ) ρ)).mp hsm
    have hHeven : ∀ τ : ℝ, Work.Diff.GE.cfq_sqFlow G (-τ) = Work.Diff.GE.cfq_sqFlow G τ := by
      intro τ
      simp only [Work.Diff.GE.cfq_sqFlow, neg_sq]
    have hxV : (0, x) ∈ V := ⟨⟨by linarith, hρpos⟩, trivial⟩
    have hJ₁ : Work.Diff.EXT.JointSmoothAt I M
        (fun p : ℝ × M => Work.Diff.EXT.jetAll (Work.Diff.GE.cfq_sqFlow G p.1) j (k + 1 + 4)
          (Work.Diff.EXT.evolX.srcStau (Work.Diff.GE.cfq_sqFlow G) (k + 1) p.1) F₁ p.2) 0 x :=
      Work.Diff.EXT.evolX.srcJet_jointSmooth (I := I) (M := M) hLC hViso hHf hHeven
        (k := k + 1) hxV
        (hbase := fun Ψ hΨ hΨe =>
          srcStau_jointSmooth (I := I) (M := M) hLC hViso hHf hHeven hxV hΨ hΨe)
        (hmvf := fun hΦ hW =>
          Work.Diff.EXT.evolX.mvfderivFamJointSmoothV2 (I := I) (M := M) hΦ hW)
        j (fun _ => F₁) (fun i => Work.Diff.EXT.evolX.jointField_const' (I := I) (M := M) (hF₁ i))
        (fun _ => rfl)
    have hJ₂ : Work.Diff.EXT.JointSmoothAt I M
        (fun p : ℝ × M => Work.Diff.EXT.jetAll (Work.Diff.GE.cfq_sqFlow G p.1) (j + 1) (k + 4)
          (Work.Diff.EXT.evolX.srcStau (Work.Diff.GE.cfq_sqFlow G) k p.1) F₂ p.2) 0 x :=
      Work.Diff.EXT.evolX.srcJet_jointSmooth (I := I) (M := M) hLC hViso hHf hHeven
        (k := k) hxV
        (hbase := fun Ψ hΨ hΨe =>
          srcStau_jointSmooth (I := I) (M := M) hLC hViso hHf hHeven hxV hΨ hΨe)
        (hmvf := fun hΦ hW =>
          Work.Diff.EXT.evolX.mvfderivFamJointSmoothV2 (I := I) (M := M) hΦ hW)
        (j + 1) (fun _ => F₂) (fun i => Work.Diff.EXT.evolX.jointField_const' (I := I) (M := M) (hF₂ i))
        (fun _ => rfl)
    have hcont₁ : ContinuousAt (fun τ : ℝ =>
        Work.Diff.EXT.jetAll (Work.Diff.GE.cfq_sqFlow G τ) j (k + 1 + 4)
          (Work.Diff.EXT.evolX.srcStau (Work.Diff.GE.cfq_sqFlow G) (k + 1) τ) F₁ x) 0 :=
      (Work.Diff.EXT.evolX.srcJointSliceFst (I := I) (M := M) hJ₁).continuousAt
    have hcont₂ : ContinuousAt (fun τ : ℝ =>
        Work.Diff.EXT.jetAll (Work.Diff.GE.cfq_sqFlow G τ) (j + 1) (k + 4)
          (Work.Diff.EXT.evolX.srcStau (Work.Diff.GE.cfq_sqFlow G) k τ) F₂ x) 0 :=
      (Work.Diff.EXT.evolX.srcJointSliceFst (I := I) (M := M) hJ₂).continuousAt
    refine Work.Diff.GE.cfq_continuousWithinAt_of_continuousAt_comp_sq hTpos
      (hcont₁.sub hcont₂) (fun s hs => ?_)
    have hGs : G s = Work.Diff.GE.cfq_sqFlow G (Real.sqrt s) := by
      rw [Work.Diff.GE.cfq_sqFlow, Real.sq_sqrt hs.1]
    have hs₁ : Work.Diff.EXT.jetAll (Work.Diff.GE.cfq_sqFlow G (Real.sqrt s)) j (k + 1 + 4)
        (Work.Diff.EXT.dtOpD (I := I) (M := M) G s (k + 1)) F₁ x
        = Work.Diff.EXT.jetAll (Work.Diff.GE.cfq_sqFlow G (Real.sqrt s)) j (k + 1 + 4)
        (Work.Diff.EXT.evolX.srcStau (Work.Diff.GE.cfq_sqFlow G) (k + 1) (Real.sqrt s)) F₁ x :=
      Work.Diff.EXT.evolX.srcJetAll_congr_of_eventuallyEq_smooth (I := I) (M := M) hLC
        (g := Work.Diff.GE.cfq_sqFlow G (Real.sqrt s)) (K := k + 1 + 4) (j := j)
        (S := Work.Diff.EXT.dtOpD (I := I) (M := M) G s (k + 1))
        (S' := Work.Diff.EXT.evolX.srcStau (Work.Diff.GE.cfq_sqFlow G) (k + 1) (Real.sqrt s))
        (fun F hF => Filter.Eventually.of_forall (fun y =>
          congrFun (Work.Diff.EXT.evolX.srcStau_eq_dtOpD (I := I) (M := M) hLC hflow hs
            (k := k + 1) (F := F) hF) y))
        F₁ hF₁
    have hs₂ : Work.Diff.EXT.jetAll (Work.Diff.GE.cfq_sqFlow G (Real.sqrt s)) (j + 1) (k + 4)
        (Work.Diff.EXT.dtOpD (I := I) (M := M) G s k) F₂ x
        = Work.Diff.EXT.jetAll (Work.Diff.GE.cfq_sqFlow G (Real.sqrt s)) (j + 1) (k + 4)
        (Work.Diff.EXT.evolX.srcStau (Work.Diff.GE.cfq_sqFlow G) k (Real.sqrt s)) F₂ x :=
      Work.Diff.EXT.evolX.srcJetAll_congr_of_eventuallyEq_smooth (I := I) (M := M) hLC
        (g := Work.Diff.GE.cfq_sqFlow G (Real.sqrt s)) (K := k + 4) (j := j + 1)
        (S := Work.Diff.EXT.dtOpD (I := I) (M := M) G s k)
        (S' := Work.Diff.EXT.evolX.srcStau (Work.Diff.GE.cfq_sqFlow G) k (Real.sqrt s))
        (fun F hF => Filter.Eventually.of_forall (fun y =>
          congrFun (Work.Diff.EXT.evolX.srcStau_eq_dtOpD (I := I) (M := M) hLC hflow hs
            (k := k) (F := F) hF) y))
        F₂ hF₂
    rw [hGs, hs₁, hs₂]
    rfl

end Work.Diff.EXT.evolX
