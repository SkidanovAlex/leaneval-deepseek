import Mathlib
import Submission.Work.Diff.GE.EvolA.rmP_evol_fixed
import Submission.Work.Diff.GE.continuousWithinAt_rmP_zero
import Submission.Work.Diff.GE.derivWithin_Ico_zero
import Submission.Work.Diff.GE.lapRmAt_zero_continuous
import Submission.Work.Diff.GE.Rfa.reactionFormAtE_frame_indep
import Submission.Work.Diff.GE.metric_pairing_family_jointSmooth
import Submission.Work.Diff.EXT.covK_onFrameFamily
import Submission.Work.Diff.GE.continuous_flow_quantities
import Submission.Work.Diff.GE.covRmFrameSupplies

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The one-sided curvature evolution on `[0, T)`

`Work.Diff.EXT.rmP_derivWithin_Ioi`: along a Ricci flow `G` on `[0,T)`, every fixed-vector
component of the curvature satisfies `∂ₜ⁺ Rm = ΔRm + reactionMap(Rm)` on the *half-open* interval
`[0,T)`, i.e. `HasDerivWithinAt … (Set.Ioi 0) t` for `t ∈ Ico 0 T`.

For `t > 0` this is `Work.Diff.GE.EvolA.rmP_evol_fixed` (an honest `HasDerivAt` on the open
interval).  At `t = 0` the derivative is only one-sided: the mean-value-theorem lemma
`Work.Diff.GE.derivWithin_Ico_zero` produces the statement on `Ico 0 T` from the interior
derivative plus continuity at `0` of the function and of its derivative, and the two `nhdsWithin`
filters agree at `0`.

The only non-trivial input is therefore the continuity at `0⁺` of
`L s = lapRmAt (G s) x a b c d + reactionFormAt reactionMap (G s) x a b c d`:

* `ΔRm` is `Work.Diff.GE.lapRmAt_zero_continuous`, restated here with a *smooth* (not analytic)
  manifold hypothesis (the proof in that file never uses analyticity);
* the reaction term is a *tensorial* expression, computed in a `G s`-orthonormal frame; since the
  frame is only defined through `Classical.epsilon`, the statement is proved by replacing it by a
  jointly smooth orthonormal frame family (`Work.Diff.EXT.covK_onFrameFamily`) using the frame
  independence of the reaction form (`Work.Diff.GE.Rfa.reactionFormAtE_frame_indep`).

Along a Ricci flow the metric family is jointly smooth only on the half-open interval `[0,T)`, so
both continuity-at-`0` statements are obtained through the time reparametrisation `t = τ²`
(`Work.Diff.GE.cfq_sqFlow`), which turns `[0,T)` into an open neighbourhood of `0`; the conclusion
is transferred back by `Work.Diff.GE.cfq_continuousWithinAt_of_continuousAt_comp_sq`.
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.Diff.EXT

section Aux

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-! ## Frame independence of the reaction form -/

/-- **Frame independence of the reaction form, pointwise.**  If `F` commutes with the orthogonal
action `rot` on curvature arrays, then the reaction form computed in an explicit orthonormal frame
`e` does not depend on the choice of `e`, hence equals the `Classical.epsilon`-chosen value. -/
lemma reactAux_frameIndep
    (hLC : Submission.Diff.LCSmooth I M)
    (F : Submission.Diff.Alg.Curv4 (Module.finrank ℝ E) →
      Submission.Diff.Alg.Curv4 (Module.finrank ℝ E))
    (hFrot : ∀ A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ, ∀ R,
      F (Submission.Diff.Alg.rot A R) = Submission.Diff.Alg.rot A (F R))
    {g : Submission.Diff.SMet I M} {x : M}
    {e : Fin (Module.finrank ℝ E) → TangentSpace I x}
    (he : Submission.Diff.IsONFrame g x e) (a b c d : TangentSpace I x) :
    Work.Diff.GE.reactionFormAt F g x a b c d
      = Work.Diff.GE.Rfa.reactionFormAtE F g x e a b c d := by
  rw [Work.Diff.GE.Rfa.reactionFormAt_eq_reactionFormAtE]
  exact (Work.Diff.GE.Rfa.reactionFormAtE_frame_indep (I := I) (M := M) hLC F hFrot g x
    (Submission.Diff.onFrame g x) e (Work.Diff.GE.isONFrame_onFrame g x) he a b c d).symm

/-- **Frame independence of the reaction form, eventually.**  Under a jointly smooth family of
orthonormal frames on an open set `U ∋ (t,x)`, the reaction form agrees, near `(t,x)`, with its
explicit-frame version. -/
lemma reactAux_eventuallyEq
    (hLC : Submission.Diff.LCSmooth I M)
    (F : Submission.Diff.Alg.Curv4 (Module.finrank ℝ E) →
      Submission.Diff.Alg.Curv4 (Module.finrank ℝ E))
    (hFrot : ∀ A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ, ∀ R,
      F (Submission.Diff.Alg.rot A R) = Submission.Diff.Alg.rot A (F R))
    {G : ℝ → Submission.Diff.SMet I M} {t : ℝ} {x : M}
    {U : Set (ℝ × M)} (hU : IsOpen U) (hxU : (t, x) ∈ U)
    {e : ℝ → Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y}
    (hON : ∀ p ∈ U, Submission.Diff.IsONFrame (G p.1) p.2 (fun i => e p.1 i p.2))
    (V₁ V₂ V₃ V₄ : ℝ → Π y : M, TangentSpace I y) :
    (fun p : ℝ × M ↦ Work.Diff.GE.reactionFormAt F (G p.1) p.2
        (V₁ p.1 p.2) (V₂ p.1 p.2) (V₃ p.1 p.2) (V₄ p.1 p.2))
      =ᶠ[𝓝 (t, x)]
    (fun p : ℝ × M ↦ Work.Diff.GE.Rfa.reactionFormAtE F (G p.1) p.2 (fun i => e p.1 i p.2)
        (V₁ p.1 p.2) (V₂ p.1 p.2) (V₃ p.1 p.2) (V₄ p.1 p.2)) := by
  filter_upwards [hU.mem_nhds hxU] with p hp
  exact reactAux_frameIndep (I := I) (M := M) hLC F hFrot (hON p hp) _ _ _ _

/-! ## Joint smoothness of the reaction form -/

/-- **Joint smoothness of the reaction-form family in a moving frame.**  Using the equivariance of
`F` under orthogonal changes of frame, the reaction form `F (Rm)` may be evaluated in the given
jointly smooth orthonormal frame family `e`, and is therefore jointly smooth. -/
lemma reactAux_jointSmoothAt
    (hLC : Submission.Diff.LCSmooth I M)
    (F : Submission.Diff.Alg.Curv4 (Module.finrank ℝ E) →
      Submission.Diff.Alg.Curv4 (Module.finrank ℝ E))
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFrot : ∀ A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ, ∀ R,
      F (Submission.Diff.Alg.rot A R) = Submission.Diff.Alg.rot A (F R))
    {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : Submission.Diff.JointSmooth G J) {t : ℝ} (ht : t ∈ J) {x : M}
    {U : Set (ℝ × M)} (hU : IsOpen U) (hxU : (t, x) ∈ U)
    {e : ℝ → Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y}
    (he : ∀ i, ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M ↦ (⟨p.2, e p.1 i p.2⟩ : TangentBundle I M)) U)
    (hON : ∀ p ∈ U, Submission.Diff.IsONFrame (G p.1) p.2 (fun i => e p.1 i p.2))
    {V₁ V₂ V₃ V₄ : ℝ → Π y : M, TangentSpace I y}
    (hV₁ : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M ↦ (⟨p.2, V₁ p.1 p.2⟩ : TangentBundle I M)) (t, x))
    (hV₂ : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M ↦ (⟨p.2, V₂ p.1 p.2⟩ : TangentBundle I M)) (t, x))
    (hV₃ : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M ↦ (⟨p.2, V₃ p.1 p.2⟩ : TangentBundle I M)) (t, x))
    (hV₄ : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M ↦ (⟨p.2, V₄ p.1 p.2⟩ : TangentBundle I M)) (t, x)) :
    Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ Work.Diff.GE.reactionFormAt F (G p.1) p.2
        (V₁ p.1 p.2) (V₂ p.1 p.2) (V₃ p.1 p.2) (V₄ p.1 p.2)) t x := by
  have h : Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ Work.Diff.GE.Rfa.reactionFormAtE F (G p.1) p.2
        (fun i => e p.1 i p.2) (V₁ p.1 p.2) (V₂ p.1 p.2) (V₃ p.1 p.2) (V₄ p.1 p.2)) t x := by
    have hUJ : IsOpen (U ∩ (J ×ˢ (univ : Set M))) := hU.inter (hJ.prod isOpen_univ)
    have hpUJ : (t, x) ∈ U ∩ (J ×ˢ (univ : Set M)) := ⟨hxU, ht, mem_univ x⟩
    have hMet0 : Work.Diff.EXT.JointMet G (J ×ˢ (univ : Set M)) := hG
    have hMet : Work.Diff.EXT.JointMet G (U ∩ (J ×ˢ (univ : Set M))) :=
      hMet0.mono (fun p hp => hp.2)
    have hFr : ∀ i : Fin (Module.finrank ℝ E),
        Work.Diff.EXT.JointField (fun s : ℝ ↦ fun y : M ↦ e s i y)
          (U ∩ (J ×ˢ (univ : Set M))) :=
      fun i => (he i).mono (fun p hp => hp.1)
    have hrm : ∀ i j k l : Fin (Module.finrank ℝ E),
        ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ)
          (((⊤ : ℕ∞) : WithTop ℕ∞))
          (fun p : ℝ × M ↦ Submission.Diff.rmP (G p.1) p.2 (e p.1 i p.2) (e p.1 j p.2)
            (e p.1 k p.2) (e p.1 l p.2)) (t, x) := by
      intro i j k l
      exact (Work.Diff.EXT.rmP_familySmooth (I := I) (M := M) hLC hUJ hMet
        (hFr i) (hFr j) (hFr k) (hFr l)).contMDiffAt (hUJ.mem_nhds hpUJ)
    have harr : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ (Submission.Diff.Alg.Curv4 (Module.finrank ℝ E)))
        (((⊤ : ℕ∞) : WithTop ℕ∞))
        (fun p : ℝ × M ↦ Work.Diff.GE.Rfa.rmFrameField (G p.1) (fun i ↦ e p.1 i) p.2)
        (t, x) := by
      rw [contMDiffAt_pi_space]
      intro i
      rw [contMDiffAt_pi_space]
      intro j
      rw [contMDiffAt_pi_space]
      intro k
      rw [contMDiffAt_pi_space]
      intro l
      simpa only [Work.Diff.GE.Rfa.rmFrameField] using hrm i j k l
    have hFrm : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ (Submission.Diff.Alg.Curv4 (Module.finrank ℝ E)))
        (((⊤ : ℕ∞) : WithTop ℕ∞))
        (fun p : ℝ × M ↦ F (Work.Diff.GE.Rfa.rmFrameField (G p.1) (fun i ↦ e p.1 i) p.2))
        (t, x) :=
      (hF.contMDiff.contMDiffAt).comp (t, x) harr
    have hFcomp : ∀ i j k l : Fin (Module.finrank ℝ E),
        ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ)
          (((⊤ : ℕ∞) : WithTop ℕ∞))
          (fun p : ℝ × M ↦
            (F (Work.Diff.GE.Rfa.rmFrameField (G p.1) (fun i ↦ e p.1 i) p.2)) i j k l)
          (t, x) := by
      intro i j k l
      exact contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp
        (contMDiffAt_pi_space.mp hFrm i) j) k) l
    have hpair : ∀ (i : Fin (Module.finrank ℝ E)) (V : ℝ → Π y : M, TangentSpace I y),
        ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent (((⊤ : ℕ∞) : WithTop ℕ∞))
          (fun p : ℝ × M ↦ (⟨p.2, V p.1 p.2⟩ : TangentBundle I M)) (t, x) →
        ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ)
          (((⊤ : ℕ∞) : WithTop ℕ∞))
          (fun p : ℝ × M ↦ (G p.1).inner p.2 (e p.1 i p.2) (V p.1 p.2)) (t, x) :=
      fun i V hV => Work.Diff.GE.metric_pairing_family_jointSmooth (I := I) (M := M)
        (V := fun s : ℝ ↦ fun y : M ↦ e s i y) (Z := V) hJ hG ht
        ((he i).contMDiffAt (hU.mem_nhds hxU)) hV
    simp only [Work.Diff.GE.Rfa.reactionFormAtE]
    refine ContMDiffAt.sum (t := Finset.univ) (fun i _ => ?_)
    refine ContMDiffAt.sum (t := Finset.univ) (fun j _ => ?_)
    refine ContMDiffAt.sum (t := Finset.univ) (fun k _ => ?_)
    refine ContMDiffAt.sum (t := Finset.univ) (fun l _ => ?_)
    refine ContMDiffAt.mul ?_ (hFcomp i j k l)
    refine ContMDiffAt.mul ?_ (hpair l V₄ hV₄)
    refine ContMDiffAt.mul ?_ (hpair k V₃ hV₃)
    exact ContMDiffAt.mul (hpair i V₁ hV₁) (hpair j V₂ hV₂)
  exact h.congr_of_eventuallyEq
    (reactAux_eventuallyEq (I := I) (M := M) hLC F hFrot hU hxU hON V₁ V₂ V₃ V₄)

/-- **Restriction of a jointly smooth function of `(t,y)` to the slice `y = x`.** -/
lemma reactAux_contDiffAt_slice {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {Φ : ℝ × M → F'} {t : ℝ} {x : M}
    (h : Work.Diff.EXT.JointSmoothAt I M Φ t x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ ↦ Φ (s, x)) t := by
  have h2 : ContMDiffAt (modelWithCornersSelf ℝ ℝ) ((modelWithCornersSelf ℝ ℝ).prod I)
      ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ ↦ (s, x)) t :=
    contMDiffAt_id.prodMk contMDiffAt_const
  exact (h.comp t h2).contDiffAt

/-! ## Continuity of the reaction form at the initial time -/

/-- **Continuity of `s ↦ F(Rm(G s))` at a time where the family is jointly smooth.**  For a metric
family jointly smooth on an open time set `J ∋ t`, the reaction form `F(Rm)` evaluated at `x` on
four fixed vectors is continuous at `t`. -/
lemma reactAux_reaction_contDiffAt_of_jointSmooth
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : Submission.Diff.JointSmooth G J) {t : ℝ} (ht : t ∈ J) (x : M)
    (a b c d : TangentSpace I x) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun s : ℝ ↦ Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G s) x a b c d) t := by
  classical
  obtain ⟨W, hWopen, hWmem, -, Fr, hFr, hFrON⟩ :=
    Work.Diff.EXT.covK_onFrameFamily (I := I) (M := M) (G := G) (V := J ×ˢ (univ : Set M))
      (hJ.prod isOpen_univ) ((Work.Diff.EXT.jointMet_prod (I := I) (M := M) G J).mp hG)
      (p₀ := (t, x)) ⟨ht, trivial⟩
  let e : ℝ → Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y := fun s i y ↦ Fr s y i
  have heSm : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M ↦ (⟨p.2, e p.1 i p.2⟩ : TangentBundle I M)) W := by
    intro i
    have h := hFr i
    simpa only [Work.Diff.EXT.JointField, e] using h
  have heON : ∀ p ∈ W, Submission.Diff.IsONFrame (G p.1) p.2 (fun i => e p.1 i p.2) := by
    intro p hp
    have h := hFrON p hp
    simpa only [e] using h
  have hconst : ∀ u : TangentSpace I x,
      ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M ↦ (⟨p.2, Submission.Diff.smoothExt x u p.2⟩ : TangentBundle I M))
        (t, x) := by
    intro u
    have h := (Work.Diff.GE.smoothExt_cmdiff (I := I) (M := M) x u).contMDiffAt (x := x)
    have h2 : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) I ((⊤ : ℕ∞) : WithTop ℕ∞)
        (Prod.snd : ℝ × M → M) (t, x) := contMDiffAt_snd
    simpa only [Function.comp_def] using h.comp (t, x) h2
  have hjoint : Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G p.1) p.2
        (Submission.Diff.smoothExt x a p.2) (Submission.Diff.smoothExt x b p.2)
        (Submission.Diff.smoothExt x c p.2) (Submission.Diff.smoothExt x d p.2)) t x :=
    reactAux_jointSmoothAt (I := I) (M := M) hLC Work.Diff.GE.reactionMap
      (Work.Diff.GE.reactionMap_contDiff (Module.finrank ℝ E))
      (Work.Diff.GE.reactionMap_rot (Module.finrank ℝ E))
      hJ hG ht hWopen hWmem heSm heON
      (V₁ := fun _ y ↦ Submission.Diff.smoothExt x a y)
      (V₂ := fun _ y ↦ Submission.Diff.smoothExt x b y)
      (V₃ := fun _ y ↦ Submission.Diff.smoothExt x c y)
      (V₄ := fun _ y ↦ Submission.Diff.smoothExt x d y)
      (hconst a) (hconst b) (hconst c) (hconst d)
  refine (reactAux_contDiffAt_slice (I := I) (M := M) hjoint).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun s => ?_))
  show Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G s) x a b c d
    = Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G s) x
      (Submission.Diff.smoothExt x a x) (Submission.Diff.smoothExt x b x)
      (Submission.Diff.smoothExt x c x) (Submission.Diff.smoothExt x d x)
  rw [Work.Diff.GE.smoothExt_apply, Work.Diff.GE.smoothExt_apply, Work.Diff.GE.smoothExt_apply,
    Work.Diff.GE.smoothExt_apply]

/-- **Continuity of the reaction term at `0⁺` along a Ricci flow.** -/
lemma reactAux_reactionFormAt_continuousWithinAt_zero
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    (x : M) (a b c d : TangentSpace I x) :
    ContinuousWithinAt
      (fun s : ℝ ↦ Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G s) x a b c d)
      (Set.Ico 0 T) 0 := by
  by_cases hT : T ≤ 0
  · rw [Set.Ico_eq_empty_iff.mpr (not_lt.mpr hT)]
    simp [ContinuousWithinAt, nhdsWithin_empty]
  · have hTpos : 0 < T := not_le.mp hT
    set ρ : ℝ := Real.sqrt T / 2 with hρdef
    have hρ : 0 < ρ := by positivity
    have hρT : ρ ^ 2 < T := by
      rw [hρdef, div_pow, Real.sq_sqrt (le_of_lt hTpos)]
      nlinarith
    have hsq : Submission.Diff.JointSmooth (Work.Diff.GE.cfq_sqFlow G) (Set.Ioo (-ρ) ρ) :=
      Work.Diff.GE.cfq_jointSmooth_sqFlow (I := I) (M := M) G hTpos hρ hρT hflow.1
    have h0 : (0 : ℝ) ∈ Set.Ioo (-ρ) ρ := ⟨by linarith, hρ⟩
    have hcont : ContinuousAt
        (fun τ : ℝ ↦ Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap
          (Work.Diff.GE.cfq_sqFlow G τ) x a b c d) 0 :=
      (reactAux_reaction_contDiffAt_of_jointSmooth (I := I) (M := M) hLC isOpen_Ioo hsq h0
        x a b c d).continuousAt
    refine Work.Diff.GE.cfq_continuousWithinAt_of_continuousAt_comp_sq hTpos hcont ?_
    intro s hs
    show Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G s) x a b c d
      = Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap
          (Work.Diff.GE.cfq_sqFlow G (Real.sqrt s)) x a b c d
    rw [show Work.Diff.GE.cfq_sqFlow G (Real.sqrt s) = G s from by
      rw [Work.Diff.GE.cfq_sqFlow, Real.sq_sqrt hs.1]]

/-! ## Continuity of the Laplacian at the initial time -/

/-- **Continuity of `s ↦ ΔRm(G s)` at `0⁺` along a Ricci flow** (smooth-manifold version of
`Work.Diff.GE.lapRmAt_zero_continuous`). -/
lemma reactAux_lapRmAt_continuousWithinAt_zero [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) :
    ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T →
      ∀ x : M, ∀ a b c d : TangentSpace I x,
        ContinuousWithinAt (fun s : ℝ ↦ Work.Diff.GE.lapRmAt (G s) x a b c d)
          (Set.Ico 0 T) 0 := by
  intro G T hflow x a b c d
  by_cases hT : T ≤ 0
  · rw [Set.Ico_eq_empty_iff.mpr (not_lt.mpr hT)]
    simp [ContinuousWithinAt, nhdsWithin_empty]
  · have hTpos : 0 < T := not_le.mp hT
    set ρ : ℝ := Real.sqrt T / 2 with hρdef
    have hρ : 0 < ρ := by positivity
    have hρT : ρ ^ 2 < T := by
      rw [hρdef, div_pow, Real.sq_sqrt (le_of_lt hTpos)]
      nlinarith
    have hsq : Submission.Diff.JointSmooth (Work.Diff.GE.cfq_sqFlow G) (Set.Ioo (-ρ) ρ) :=
      Work.Diff.GE.cfq_jointSmooth_sqFlow (I := I) (M := M) G hTpos hρ hρT hflow.1
    have h0 : (0 : ℝ) ∈ Set.Ioo (-ρ) ρ := ⟨by linarith, hρ⟩
    have hcont : ContinuousAt (fun τ : ℝ ↦ Work.Diff.GE.lapRmAt
        (Work.Diff.GE.cfq_sqFlow G τ) x a b c d) 0 := by
      classical
      letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
        ⟨(Work.Diff.GE.cfq_sqFlow G 0).toRiemannianMetric⟩
      haveI : IsContMDiffRiemannianBundle I ∞ E (fun z : M ↦ TangentSpace I z) := inferInstance
      have hid : ∀ τ : ℝ, Work.Diff.GE.lapRmAt (Work.Diff.GE.cfq_sqFlow G τ) x a b c d
          = ∑ i, ∑ j, (Work.Diff.GE.GramInv (I := I) (Work.Diff.GE.cfq_sqFlow G) x τ x) i j *
              Work.Diff.GE.cov2Rm (Work.Diff.GE.cfq_sqFlow G τ) x
                (Work.Diff.GE.cFrame (I := I) x i x) (Work.Diff.GE.cFrame (I := I) x j x)
                a b c d := by
        intro τ
        have h := Work.Diff.GE.lapRmAt_eq_sum_invGram_aux (I := I) (M := M) hLC
          (Work.Diff.GE.cfq_sqFlow G τ) x a b c d
          (fun i => Work.Diff.GE.cFrame (I := I) x i x)
          (Work.Diff.GE.GramM (I := I) (Work.Diff.GE.cfq_sqFlow G) x τ x)
          (fun i j => rfl)
          (Work.Diff.GE.cfq_cFrame_span (I := I) x (mem_chart_source H x))
        simpa only [Work.Diff.GE.GramInv] using h
      have hterm : ∀ i j : Fin (Module.finrank ℝ E),
          ContinuousAt (fun τ : ℝ ↦
            (Work.Diff.GE.GramInv (I := I) (Work.Diff.GE.cfq_sqFlow G) x τ x) i j *
              Work.Diff.GE.cov2Rm (Work.Diff.GE.cfq_sqFlow G τ) x
                (Work.Diff.GE.cFrame (I := I) x i x) (Work.Diff.GE.cFrame (I := I) x j x)
                a b c d) 0 := by
        intro i j
        have hg : ContinuousAt (fun τ : ℝ ↦
            (Work.Diff.GE.GramInv (I := I) (Work.Diff.GE.cfq_sqFlow G) x τ x) i j) 0 :=
          Work.Diff.GE.cfq_continuousAt_of_jointSmoothAt (I := I) (M := M)
            (Work.Diff.GE.gramInv_jointSmooth (I := I) (M := M) (G := Work.Diff.GE.cfq_sqFlow G)
              isOpen_Ioo hsq h0 x i j)
        have hc : ContinuousAt (fun τ : ℝ ↦
            Work.Diff.GE.cov2Rm (Work.Diff.GE.cfq_sqFlow G τ) x
              (Work.Diff.GE.cFrame (I := I) x i x) (Work.Diff.GE.cFrame (I := I) x j x)
              a b c d) 0 :=
          Work.Diff.GE.cov2Rm_continuousAt_aux (I := I) (M := M) hLC isOpen_Ioo hsq h0 x
            (Work.Diff.GE.cFrame (I := I) x i x) (Work.Diff.GE.cFrame (I := I) x j x) a b c d
        exact hg.mul hc
      have hsum : ContinuousAt (fun τ : ℝ ↦ ∑ i, ∑ j,
          (Work.Diff.GE.GramInv (I := I) (Work.Diff.GE.cfq_sqFlow G) x τ x) i j *
              Work.Diff.GE.cov2Rm (Work.Diff.GE.cfq_sqFlow G τ) x
                (Work.Diff.GE.cFrame (I := I) x i x) (Work.Diff.GE.cFrame (I := I) x j x)
                a b c d) 0 := by
        refine Work.Diff.GE.cfq_continuousAt_finsetSum Finset.univ (fun i _ => ?_)
        refine Work.Diff.GE.cfq_continuousAt_finsetSum Finset.univ (fun j _ => ?_)
        exact hterm i j
      exact hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => hid τ)
    refine Work.Diff.GE.cfq_continuousWithinAt_of_continuousAt_comp_sq hTpos hcont ?_
    intro s hs
    show Work.Diff.GE.lapRmAt (G s) x a b c d
      = Work.Diff.GE.lapRmAt (Work.Diff.GE.cfq_sqFlow G (Real.sqrt s)) x a b c d
    rw [show Work.Diff.GE.cfq_sqFlow G (Real.sqrt s) = G s from by
      rw [Work.Diff.GE.cfq_sqFlow, Real.sq_sqrt hs.1]]

end Aux

theorem rmP_derivWithin_Ioi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) (hLV : Submission.Diff.LCVariation I M) :
    ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T →
      ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ a b c d : TangentSpace I x,
        HasDerivWithinAt (fun s => Submission.Diff.rmP (G s) x a b c d)
          (Work.Diff.GE.lapRmAt (G t) x a b c d
            + Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) x a b c d)
          (Set.Ioi 0) t := by
  intro G T hflow t ht x a b c d
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · -- the initial time: one-sided mean value theorem
    subst h0
    have hTpos : (0 : ℝ) < T := ht.2
    refine HasDerivWithinAt.mono_of_mem_nhdsWithin (t := Set.Ico 0 T) ?_ ?_
    · refine Work.Diff.GE.derivWithin_Ico_zero
        (fun s : ℝ ↦ Submission.Diff.rmP (G s) x a b c d)
        (fun s : ℝ ↦ Work.Diff.GE.lapRmAt (G s) x a b c d
          + Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G s) x a b c d) T hTpos ?_ ?_ ?_
      · intro s hs
        exact Work.Diff.GE.EvolA.rmP_evol_fixed hLC hLV G T hflow s hs x a b c d
      · exact Work.Diff.GE.continuousWithinAt_rmP_zero (I := I) (M := M) hLC hflow x a b c d
      · exact (reactAux_lapRmAt_continuousWithinAt_zero (I := I) (M := M) hLC G T hflow
            x a b c d).add
          (reactAux_reactionFormAt_continuousWithinAt_zero (I := I) (M := M) hLC hflow
            x a b c d)
    · refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
        ⟨Set.Iio T, Iio_mem_nhds hTpos, fun y hy => ⟨le_of_lt hy.2, hy.1⟩⟩
  · -- interior times: the two-sided derivative
    exact (Work.Diff.GE.EvolA.rmP_evol_fixed hLC hLV G T hflow t ⟨hpos, ht.2⟩
      x a b c d).hasDerivWithinAt

end Work.Diff.EXT
