import Mathlib
import Submission.Work.Diff.EXT.reactBase
import Submission.Work.Diff.EXT.reactionMap_rot
import Submission.Work.Diff.EXT.evX.jetAll_eq_MonSum
import Submission.Work.EXT.sum_inner_smul_eq_self_of_isONFrame
import Submission.Work.Diff.GE.Rfa.reactionFormAtE_frame_indep
import Submission.Work.Diff.EXT.KptArr_frame_indep
import Submission.Work.Diff.EXT.Mono.towerArr_mvfderiv
import Submission.Work.Diff.EXT.Mono.pairing_mvfderiv
import Submission.Work.Diff.EXT.RmPair.mvfderiv_rmSym
import Submission.Work.Diff.EXT.RmPair.rmSym_bound
import Submission.Work.Diff.EXT.Mono.MonoD_extStep
import Submission.Work.Diff.EXT.Mono.fam_props_T2b
import Submission.Work.Diff.EXT.Mono.smooth_MonoD_T2
import Submission.Work.Diff.EXT.Mono.MonoD_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The base case of the reaction ladder: the jets of the quadratic level-`0` reaction `Q(Rm)`

This module proves `Work.Diff.EXT.reaction0_jets`.  Its vocabulary and the elementary lemmas about
it live in `Submission.Work.Diff.EXT.reactBase`.

Route.  Write `S` for the level-`0` reaction operator `F ↦ fun y => Q(Rm_y)(F 0 y) … (F 3 y)`.
The `j`-th jet of `S` is a sum over the `2^j` distributions of the `j` differentiation directions
among the two factors of the quadratic form `Q = rmSym(·,·)`: each term is a *monomial*
`MonoD` of level `(a,b)`, `a + b = j`, contracted in a `g`-orthonormal frame.  The induction is
carried out with a frame field `W` which is smooth, orthonormal near `x` and *geodesic at* `x`
(then every frame-derivative term in the Leibniz expansion vanishes at `x`), and the resulting
germ identity is evaluated at `x`; the bound is then the componentwise Cauchy–Schwarz estimate.
-/

namespace Work.Diff.EXT

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## The frame independence of the monomial, and the level-`0` identity -/

theorem MonoD_frame_indep (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (y : M) (N a b : ℕ) (d₁ : Fin a → Fin N) (d₂ : Fin b → Fin N) (s : Fin 4 → Fin N)
    (e e' : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (he : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e i))
    (he' : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e' i))
    (hON : Submission.Diff.IsONFrame g y (fun i => e i y))
    (hON' : Submission.Diff.IsONFrame g y (fun i => e' i y))
    (hF : ∀ A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ,
      ∀ X Y : Curv4 (Module.finrank ℝ E),
        reactionBilin (rot A X) (rot A Y) = rot A (reactionBilin X Y))
    (F : Fin N → TField (I := I) (M := M))
    (hFs : ∀ r, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F r)) :
    MonoD (I := I) (M := M) g N a b d₁ d₂ s e F y
      = MonoD (I := I) (M := M) g N a b d₁ d₂ s e' F y := by
  have hrw : ∀ (e₀ : Fin (Module.finrank ℝ E) → TField (I := I) (M := M)),
      (∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e₀ i)) →
      MonoD (I := I) (M := M) g N a b d₁ d₂ s e₀ F y
        = ∑ i, ∑ j, ∑ k, ∑ l,
            reactionBilin (KptArr g y a (fun r => (F (d₁ r)) y) (fun i => e₀ i y))
              (KptArr g y b (fun r => (F (d₂ r)) y) (fun i => e₀ i y)) i j k l
            * (g.inner y (e₀ i y) (F (s 0) y) * g.inner y (e₀ j y) (F (s 1) y)
              * g.inner y (e₀ k y) (F (s 2) y) * g.inner y (e₀ l y) (F (s 3) y)) := by
    intro e₀ he₀
    simp only [MonoD]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))))
    rw [rmSym_eq_reactionBilin,
      TowerArr_eq_KptArr hLC g a (fun r => F (d₁ r)) (fun r => hFs (d₁ r)) e₀ he₀ y,
      TowerArr_eq_KptArr hLC g b (fun r => F (d₂ r)) (fun r => hFs (d₂ r)) e₀ he₀ y]
  rw [hrw e he, hrw e' he']
  exact KptArr_frame_indep hLC hF g y a b (fun r => (F (d₁ r)) y) (fun r => (F (d₂ r)) y)
    (fun i => e i y) (fun i => e' i y) hON hON' (fun t => F (s t) y)

theorem TowerArr_zero_eq (g : Submission.Diff.SMet I M)
    (dirs : Fin 0 → TField (I := I) (M := M))
    (e : Fin (Module.finrank ℝ E) → TField (I := I) (M := M)) (y : M) :
    TowerArr g 0 dirs e y = rmFrame g y (fun i => e i y) := by
  funext i j k l
  simp only [TowerArr, ckt]
  have hdirs : dirs = Fin.elim0 := by funext r; exact Fin.elim0 r
  rw [hdirs, Fin.elim0_append]
  simp only [Function.comp_apply]
  apply congrArg
  rfl

theorem MonoD_zero (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (x : M) (W : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (hWs : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (W i))
    (hWON : ∀ᶠ y in 𝓝 x, Submission.Diff.IsONFrame g y (fun i => W i y))
    (hF : ∀ A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ,
      ∀ X Y : Curv4 (Module.finrank ℝ E),
        reactionBilin (rot A X) (rot A Y) = rot A (reactionBilin X Y))
    (F : Fin 4 → TField (I := I) (M := M))
    (hFs : ∀ r, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F r)) :
    (fun y => Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap g y
        (F 0 y) (F 1 y) (F 2 y) (F 3 y))
      =ᶠ[𝓝 x] (fun y => MonoD (I := I) (M := M) g 4 0 0 (Fin.elim0) (Fin.elim0)
        (fun t => t) W F y) := by
  filter_upwards [hWON] with y hy
  rw [Work.Diff.GE.Rfa.reactionFormAt_eq_reactionFormAtE]
  rw [Work.Diff.GE.Rfa.reactionFormAtE_frame_indep hLC (Work.Diff.GE.reactionMap)
    (fun A hA R => reactionMap_rot A hA R) g y (fun i => W i y)
    (onFrame g y) hy (Work.Diff.GE.isONFrame_onFrame g y) (F 0 y) (F 1 y) (F 2 y) (F 3 y)]
  simp only [MonoD, rmSym_self, Work.Diff.GE.Rfa.reactionFormAtE]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
    Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))))
  rw [TowerArr_zero_eq]
  ring

/-! ## Linearity tools and the germ form of the frame independence -/

theorem mvfderiv_sum {ι : Type*} [Fintype ι] (f : ι → M → ℝ) (x : M) (v : TangentSpace I x)
    (h : ∀ i, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) (f i) x) :
    mvfderiv I (fun y => ∑ i, f i y) x v = ∑ i, mvfderiv I (f i) x v := by
  classical
  have hdiff : ∀ t : Finset ι, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (fun y : M => ∑ i ∈ t, f i y) x := by
    intro t
    refine (MDifferentiableAt.sum (t := t) (f := f) (fun i _ => h i)).congr_of_eventuallyEq ?_
    filter_upwards with y
    rw [Finset.sum_apply]
  have key : ∀ s : Finset ι,
      mvfderiv I (fun y => ∑ i ∈ s, f i y) x v = ∑ i ∈ s, mvfderiv I (f i) x v := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [show (fun y : M => ∑ i ∈ (∅ : Finset ι), f i y) = (fun _ : M => (0 : ℝ)) from by
        funext y; simp]
      rw [mvfderiv_const]
      simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      rw [show (fun y : M => ∑ i ∈ insert a s, f i y)
          = ((f a) + (fun y : M => ∑ i ∈ s, f i y)) from by
            funext y; rw [Finset.sum_insert ha]; rfl]
      rw [mvfderiv_add (h a) (hdiff s), add_apply, ih]
  simpa using key Finset.univ

theorem MonoF_eventuallyEq_of_ON (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (j : ℕ) (f : Fin j → Bool)
    (W W' : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (hWs : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (W i))
    (hW's : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (W' i))
    (hF : ∀ A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ,
      ∀ X Y : Curv4 (Module.finrank ℝ E),
        reactionBilin (rot A X) (rot A Y) = rot A (reactionBilin X Y))
    {y : M}
    (hWON : ∀ᶠ z in 𝓝 y, Submission.Diff.IsONFrame g z (fun i => W i z))
    (hW'ON : ∀ᶠ z in 𝓝 y, Submission.Diff.IsONFrame g z (fun i => W' i z))
    (G : Fin (4 + j) → TField (I := I) (M := M))
    (hG : ∀ r, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (G r)) :
    (fun z => MonoF (I := I) (M := M) g j f W G z)
      =ᶠ[𝓝 y] (fun z => MonoF (I := I) (M := M) g j f W' G z) := by
  filter_upwards [hWON, hW'ON] with z hz hz'
  exact MonoD_frame_indep hLC g z (4 + j) (fam j f).1.1 (fam j f).2.1 (fam j f).1.2
    (fam j f).2.2 (slotS j) W W' hWs hW's hz hz' hF G hG

theorem MonoF_cons_true (g : Submission.Diff.SMet I M) (j : ℕ) (f : Fin j → Bool)
    (e : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (F : Fin (4 + (j + 1)) → TField (I := I) (M := M)) (y : M) :
    MonoF (I := I) (M := M) g (j + 1) (Fin.cons true f) e F y
      = MonoD (I := I) (M := M) g ((4 + j) + 1) ((fam j f).1.1 + 1) (fam j f).2.1
          (Fin.cons 0 (fun r : Fin (fam j f).1.1 => ((fam j f).1.2 r).succ))
          (fun r => ((fam j f).2.2 r).succ)
          (fun t => ((slotS j) t).succ) e F y := by
  unfold MonoF
  rw [fam_cons_true, slotS_succ]
  simp only [Sigma.fst, Sigma.snd]
  rfl

theorem MonoF_cons_false (g : Submission.Diff.SMet I M) (j : ℕ) (f : Fin j → Bool)
    (e : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (F : Fin (4 + (j + 1)) → TField (I := I) (M := M)) (y : M) :
    MonoF (I := I) (M := M) g (j + 1) (Fin.cons false f) e F y
      = MonoD (I := I) (M := M) g ((4 + j) + 1) (fam j f).1.1 ((fam j f).2.1 + 1)
          (fun r => ((fam j f).1.2 r).succ)
          (Fin.cons 0 (fun r : Fin (fam j f).2.1 => ((fam j f).2.2 r).succ))
          (fun t => ((slotS j) t).succ) e F y := by
  unfold MonoF
  rw [fam_cons_false, slotS_succ]
  simp only [Sigma.fst, Sigma.snd]
  rfl

/-! ## The induction: the jet of the reaction is a sum of monomials -/

/-- Kato's geodesic frame is geodesic in the linear-map form: if `lcOf g (V j) y` vanishes on the
frame vectors `V m y` and the frame is orthonormal at `y`, then `lcOf g (V j) y = 0`. -/
theorem lcOf_eq_zero_of_geodesic (g : Submission.Diff.SMet I M) {y : M}
    (V : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (hON : Submission.Diff.IsONFrame g y (fun i => V i y))
    (h : ∀ m j, lcOf g (V j) y (V m y) = 0) (j : Fin (Module.finrank ℝ E)) :
    lcOf g (V j) y = 0 := by
  ext v
  have hv : v = ∑ m, g.inner y v (V m y) • V m y :=
    (Work.EXT.sum_inner_smul_eq_self_of_isONFrame g y (fun i => V i y) hON v).symm
  rw [hv, map_sum]
  refine Finset.sum_eq_zero (fun m _ => ?_)
  rw [map_smul, h m j, smul_zero]

/-- Pointwise linearity of `extStep` in its operator argument, over a finite sum. -/
theorem extStep_sum (g : Submission.Diff.SMet I M) {ι : Type*} [Fintype ι] {K : ℕ}
    (T : ι → (Fin K → TField (I := I) (M := M)) → M → ℝ)
    (F : Fin (K + 1) → TField (I := I) (M := M)) (x : M)
    (hdiff : ∀ f, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (T f (fun i : Fin K => F i.succ)) x) :
    extStep (I := I) (M := M) g (fun G y => ∑ f, T f G y) F x
      = ∑ f, extStep (I := I) (M := M) g (T f) F x := by
  unfold extStep
  rw [mvfderiv_sum (f := fun f => T f (fun i : Fin K => F i.succ)) x (F 0 x) (fun f => hdiff f)]
  simp only [Finset.sum_apply]
  rw [Finset.sum_sub_distrib, Finset.sum_comm]

/-- The reindexing `(Fin (j+1) → Bool) ≃ Bool × (Fin j → Bool)`: a word is its first letter
followed by its tail. -/
def piFinSuccEquiv (j : ℕ) : (Fin (j + 1) → Bool) ≃ Bool × (Fin j → Bool) where
  toFun f := (f 0, Fin.tail f)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by
    obtain ⟨b, h⟩ := p
    refine Prod.ext ?_ ?_
    · exact Fin.cons_zero (α := fun _ : Fin (j + 1) => Bool) b h
    · funext i; rfl

/-- **The expansion of the jet of the quadratic reaction as a sum of monomials.**  On any open set
`U` on which the smooth frame `W` is orthonormal, the `j`-th Ext-pattern jet of the level-`0`
reaction `Q(Rm)` is the sum of the `2^j` monomials `MonoF` indexed by the words `Fin j → Bool`. -/
theorem jetAll_expansion (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (W : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (hWs : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (W i))
    (U : Set M) (hUopen : IsOpen U)
    (hUsub : U ⊆ {y | Submission.Diff.IsONFrame g y (fun i => W i y)})
    (hbil : ∀ A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ,
      ∀ X Y : Curv4 (Module.finrank ℝ E),
        reactionBilin (rot A X) (rot A Y) = rot A (reactionBilin X Y))
    (j : ℕ) (F : Fin (4 + j) → TField (I := I) (M := M))
    (hF : ∀ r, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F r)) :
    ∀ y ∈ U, jetAll g j 4 (fun (F : Fin 4 → TField (I := I) (M := M)) (y : M) =>
        Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap g y (F 0 y) (F 1 y) (F 2 y) (F 3 y)) F y
      = ∑ f : Fin j → Bool, MonoF (I := I) (M := M) g j f W F y := by
  induction j with
  | zero =>
    intro y hy
    haveI : Unique (Fin 0 → Bool) :=
      ⟨⟨fun _ => true⟩, fun f => by funext i; exact Fin.elim0 i⟩
    rw [Fintype.sum_unique]
    have hid : slotS 0 = (fun t : Fin 4 => t) := by
      funext t; exact Fin.ext (by simp [slotS])
    have hM : ∀ f : Fin 0 → Bool,
        MonoF (I := I) (M := M) g 0 f W F y
        = MonoD (I := I) (M := M) g 4 0 0 (Fin.elim0) (Fin.elim0) (fun t => t) W F y := by
      intro f
      simp only [MonoF, fam]
      rw [hid]
    rw [hM]
    show Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap g y (F 0 y) (F 1 y) (F 2 y) (F 3 y)
      = MonoD (I := I) (M := M) g 4 0 0 (Fin.elim0) (Fin.elim0) (fun t => t) W F y
    have hz : ∀ᶠ z in 𝓝 y, Submission.Diff.IsONFrame g z (fun i => W i z) :=
      Filter.mem_of_superset (IsOpen.mem_nhds hUopen hy) (fun z hz => hUsub hz)
    exact Filter.EventuallyEq.eq_of_nhds (MonoD_zero hLC g y W hWs hz hbil F hF)
  | succ j ih =>
    intro y hy
    have hWONy : ∀ᶠ z in 𝓝 y, Submission.Diff.IsONFrame g z (fun i => W i z) :=
      Filter.mem_of_superset (IsOpen.mem_nhds hUopen hy) (fun z hz => hUsub hz)
    -- the tuple `F ∘ succ` and its smoothness
    have hFs : ∀ r : Fin (4 + j), Work.Diff.GE.SmoothFieldT (I := I) (M := M)
        ((fun i : Fin (4 + j) => F i.succ) r) := fun r => hF r.succ
    -- (1) the germ identity expressing `jetAll g j 4 S (F∘succ)` by its monomial sum
    have hT : (fun z : M => jetAll g j 4 (fun (F : Fin 4 → TField (I := I) (M := M)) (y : M) =>
          Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap g y
            (F 0 y) (F 1 y) (F 2 y) (F 3 y)) (fun i : Fin (4 + j) => F i.succ) z)
        =ᶠ[𝓝 y] (fun z : M => ∑ f : Fin j → Bool,
            MonoF (I := I) (M := M) g j f W (fun i : Fin (4 + j) => F i.succ) z) := by
      filter_upwards [IsOpen.mem_nhds hUopen hy] with z hz
      exact ih (fun i : Fin (4 + j) => F i.succ) hFs z hz
    have hTeq : extStep (I := I) (M := M) g
          (jetAll g j 4 (fun (F : Fin 4 → TField (I := I) (M := M)) (y : M) =>
            Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap g y
              (F 0 y) (F 1 y) (F 2 y) (F 3 y))) F y
        = extStep (I := I) (M := M) g
          (fun (G : Fin (4 + j) → TField (I := I) (M := M)) (z : M) =>
            ∑ f : Fin j → Bool, MonoF (I := I) (M := M) g j f W G z) F y := by
      unfold extStep
      rw [Work.Diff.GE.mvfderiv_congr_eventuallyEq hT]
      congr 1
      refine Finset.sum_congr rfl (fun x _ => ?_)
      refine ih _ (fun r => ?_) y hy
      rcases eq_or_ne r x with h | h
      · subst h
        rw [Function.update_self]
        exact dirF_smooth hLC g (hF r.succ) (hF 0)
      · rw [Function.update_of_ne h]
        exact hF r.succ
    -- (2) linearity in the operator
    have hlin : extStep (I := I) (M := M) g
          (fun (G : Fin (4 + j) → TField (I := I) (M := M)) (z : M) =>
            ∑ f : Fin j → Bool, MonoF (I := I) (M := M) g j f W G z) F y
        = ∑ f : Fin j → Bool,
            extStep (I := I) (M := M) g
              (fun (G : Fin (4 + j) → TField (I := I) (M := M)) (z : M) =>
                MonoF (I := I) (M := M) g j f W G z) F y :=
      extStep_sum (I := I) (M := M) g (fun f (G : Fin (4 + j) → TField (I := I) (M := M)) (z : M) =>
        MonoF (I := I) (M := M) g j f W G z) F y
        (fun f => (Mono.smooth_MonoD_T2 hLC g (4 + j) (fam j f).1.1 (fam j f).2.1 (fam j f).1.2
          (fam j f).2.2 (slotS j) W hWs (fun i : Fin (4 + j) => F i.succ) hFs).contMDiffAt.mdifferentiableAt (by simp))
    -- (3) the one-monomial step
    have hmono : ∀ f : Fin j → Bool,
        extStep (I := I) (M := M) g
          (fun (G : Fin (4 + j) → TField (I := I) (M := M)) (z : M) =>
            MonoF (I := I) (M := M) g j f W G z) F y
          = MonoF (I := I) (M := M) g (j + 1) (Fin.cons true f) W F y
            + MonoF (I := I) (M := M) g (j + 1) (Fin.cons false f) W F y := by
      intro f
      obtain ⟨E, hEs, hEON, hEx, hEgeo⟩ := Work.Diff.EXT.evX.geodesic_frame_clean g y
      have hEONy : Submission.Diff.IsONFrame g y (fun i => E i y) := by
        rw [show (fun i => E i y) = onFrame g y from funext hEx]
        exact Work.Diff.GE.isONFrame_onFrame g y
      have hWONy' : Submission.Diff.IsONFrame g y (fun i => W i y) := hUsub hy
      obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8⟩ := Mono.fam_props_T2b j f
      have hgerm : (fun z : M => MonoF (I := I) (M := M) g j f W
            (fun i : Fin (4 + j) => F i.succ) z)
          =ᶠ[𝓝 y] (fun z : M => MonoF (I := I) (M := M) g j f E
            (fun i : Fin (4 + j) => F i.succ) z) :=
        MonoF_eventuallyEq_of_ON hLC g j f W E hWs hEs hbil hWONy hEON
          (fun i : Fin (4 + j) => F i.succ) hFs
      have hsw : extStep (I := I) (M := M) g
            (fun (G : Fin (4 + j) → TField (I := I) (M := M)) (z : M) =>
              MonoF (I := I) (M := M) g j f W G z) F y
          = extStep (I := I) (M := M) g
            (fun (G : Fin (4 + j) → TField (I := I) (M := M)) (z : M) =>
              MonoF (I := I) (M := M) g j f E G z) F y := by
        unfold extStep
        rw [Work.Diff.GE.mvfderiv_congr_eventuallyEq hgerm]
        congr 1
        refine Finset.sum_congr rfl (fun x _ => ?_)
        refine MonoD_frame_indep hLC g y (4 + j) (fam j f).1.1 (fam j f).2.1 (fam j f).1.2
          (fam j f).2.2 (slotS j) W E hWs hEs hWONy' hEONy hbil _ (fun r => ?_)
        · rcases eq_or_ne r x with h | h
          · subst h
            rw [Function.update_self]
            exact dirF_smooth hLC g (hF r.succ) (hF 0)
          · rw [Function.update_of_ne h]
            exact hF r.succ
      rw [hsw]
      have hgeoE : ∀ i, lcOf g (E i) y = 0 :=
        fun i => lcOf_eq_zero_of_geodesic g E hEONy hEgeo i
      have hfam := fam_len j f
      have hcl := Mono.MonoD_extStep hLC g y E hEs hgeoE (4 + j) (fam j f).1.1 (fam j f).2.1
        (by omega) (fam j f).1.2 (fam j f).2.2 (slotS j) hp1 hp2 hp3 hp4 hp5 hp6 hp7 F hF
      rw [show (fun (G : Fin (4 + j) → TField (I := I) (M := M)) (z : M) =>
            MonoF (I := I) (M := M) g j f E G z)
          = MonoD (I := I) (M := M) g (4 + j) (fam j f).1.1 (fam j f).2.1 (fam j f).1.2
              (fam j f).2.2 (slotS j) E from rfl]
      rw [hcl]
      have hm1 : MonoD (I := I) (M := M) g ((4 + j) + 1) ((fam j f).1.1 + 1) (fam j f).2.1
            (Fin.cons 0 (fun r : Fin (fam j f).1.1 => ((fam j f).1.2 r).succ))
            (fun r => ((fam j f).2.2 r).succ) (fun t => ((slotS j) t).succ) E F y
          = MonoD (I := I) (M := M) g ((4 + j) + 1) ((fam j f).1.1 + 1) (fam j f).2.1
            (Fin.cons 0 (fun r : Fin (fam j f).1.1 => ((fam j f).1.2 r).succ))
            (fun r => ((fam j f).2.2 r).succ) (fun t => ((slotS j) t).succ) W F y :=
        MonoD_frame_indep hLC g y ((4 + j) + 1) ((fam j f).1.1 + 1) (fam j f).2.1
          (Fin.cons 0 (fun r : Fin (fam j f).1.1 => ((fam j f).1.2 r).succ))
          (fun r => ((fam j f).2.2 r).succ) (fun t => ((slotS j) t).succ) E W hEs hWs
          hEONy hWONy' hbil F hF
      have hm2 : MonoD (I := I) (M := M) g ((4 + j) + 1) (fam j f).1.1 ((fam j f).2.1 + 1)
            (fun r => ((fam j f).1.2 r).succ)
            (Fin.cons 0 (fun r : Fin (fam j f).2.1 => ((fam j f).2.2 r).succ))
            (fun t => ((slotS j) t).succ) E F y
          = MonoD (I := I) (M := M) g ((4 + j) + 1) (fam j f).1.1 ((fam j f).2.1 + 1)
            (fun r => ((fam j f).1.2 r).succ)
            (Fin.cons 0 (fun r : Fin (fam j f).2.1 => ((fam j f).2.2 r).succ))
            (fun t => ((slotS j) t).succ) W F y :=
        MonoD_frame_indep hLC g y ((4 + j) + 1) (fam j f).1.1 ((fam j f).2.1 + 1)
          (fun r => ((fam j f).1.2 r).succ)
          (Fin.cons 0 (fun r : Fin (fam j f).2.1 => ((fam j f).2.2 r).succ))
          (fun t => ((slotS j) t).succ) E W hEs hWs hEONy hWONy' hbil F hF
      rw [hm1, hm2]
      rw [MonoF_cons_true, MonoF_cons_false]
    -- (4) the sum over the words of length `j+1` splits by the first letter
    have hsum : (∑ f : Fin (j + 1) → Bool,
          MonoF (I := I) (M := M) g (j + 1) f W F y)
        = ∑ f : Fin j → Bool,
            (MonoF (I := I) (M := M) g (j + 1) (Fin.cons true f) W F y
              + MonoF (I := I) (M := M) g (j + 1) (Fin.cons false f) W F y) := by
      classical
      rw [← Fintype.sum_equiv (piFinSuccEquiv j).symm
        (fun p : Bool × (Fin j → Bool) =>
          MonoF (I := I) (M := M) g (j + 1) (Fin.cons p.1 p.2) W F y)
        (fun f => MonoF (I := I) (M := M) g (j + 1) f W F y) (fun p => rfl),
        Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
    rw [show jetAll g (j + 1) 4 (fun (F : Fin 4 → TField (I := I) (M := M)) (y : M) =>
        Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap g y (F 0 y) (F 1 y) (F 2 y) (F 3 y)) F y
        = extStep (I := I) (M := M) g
          (jetAll g j 4 (fun (F : Fin 4 → TField (I := I) (M := M)) (y : M) =>
            Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap g y
              (F 0 y) (F 1 y) (F 2 y) (F 3 y))) F y from rfl]
    rw [hTeq, hlin, hsum]
    exact Finset.sum_congr rfl (fun f _ => hmono f)

/-! ## Linearity of `rot` and the equivariance of `reactionBilin` -/

theorem rot_add {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (S T : Curv4 n) :
    rot A (S + T) = rot A S + rot A T := by
  ext i j k l
  simp only [rot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem rot_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (S : Curv4 n) :
    rot A (c • S) = c • rot A S := by
  ext i j k l
  simp only [rot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c' _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  ring

/-- `reactionBilin` commutes with the orthogonal action `rot`: it is built from the metric alone. -/
theorem reactionBilin_rot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (X Y : Curv4 n) :
    reactionBilin (rot A X) (rot A Y) = rot A (reactionBilin X Y) := by
  ext i j k l
  have hL : reactionBilin (rot A X) (rot A Y) i j k l
      = (rot A (Work.Diff.GE.reactionMap (X + Y) - Work.Diff.GE.reactionMap X
          - Work.Diff.GE.reactionMap Y)) i j k l / 2 := by
    have h1 : rot A (X + Y) = rot A X + rot A Y := rot_add A X Y
    have h2 : rot A (Work.Diff.GE.reactionMap (X + Y) - Work.Diff.GE.reactionMap X
        - Work.Diff.GE.reactionMap Y)
        = rot A (Work.Diff.GE.reactionMap (X + Y)) - rot A (Work.Diff.GE.reactionMap X)
          - rot A (Work.Diff.GE.reactionMap Y) := by
      rw [Work.Diff.GE.react.rot_sub, Work.Diff.GE.react.rot_sub]
    simp only [reactionBilin, Pi.sub_apply]
    rw [← h1, reactionMap_rot A hA (X + Y), reactionMap_rot A hA X, reactionMap_rot A hA Y,
      h2]
    simp only [Pi.sub_apply]
  have hR : (rot A (reactionBilin X Y)) i j k l
      = (rot A (Work.Diff.GE.reactionMap (X + Y) - Work.Diff.GE.reactionMap X
          - Work.Diff.GE.reactionMap Y)) i j k l / 2 := by
    have hs : reactionBilin X Y = (1 / 2 : ℝ) • (Work.Diff.GE.reactionMap (X + Y)
        - Work.Diff.GE.reactionMap X - Work.Diff.GE.reactionMap Y) := by
      funext i j k l
      simp only [reactionBilin, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hs, rot_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hL, hR]

/-- **The base case of the reaction ladder** (`Ladder(0,j)`): the `j`-th covariant-derivative jet of the *quadratic* level-`0` reaction `Q(Rm)` is bounded by `C · Shape_j`, i.e. by the sum of the square roots of the Frobenius norms of the two curvature-jet factors.  No Ricci flow is involved: this is a pure Riemannian-geometry statement (it is the base case of the reaction ladder, its only input besides `Work.Diff.EXT.ckt_step_tderiv`).

`Work.Diff.EXT.jetAll g j 4 S G` is the honest `j`-th covariant derivative of the packed operator `S` of arity `4` (the tower-style iteration of `Work.Diff.EXT.extStep`, whose ledger corrections cover *all* the slots of the running tuple, so that the `∇_{X₀}X_r` terms are handled).  The point of the statement is that `reactionFormAt reactionMap = Q(Rm)` is quadratic in `Rm` with only metric (parallel) contractions, so its `j`-th jet is a sum of metric contractions of `∇^a Rm` with `∇^b Rm`, `a + b = j`; each such monomial is bounded by `√(curvNormK g x a) · √(curvNormK g x b) · ∏‖vectors‖` by Cauchy–Schwarz on the components in an orthonormal frame, and `√f_a √f_b ≤ Shape (a+b)` is `Work.Diff.EXT.sqrt_mul_sqrt_le_Shape`.  Proof route: rewrite `reactionFormAt reactionMap g y (F 0 y) …` as the frame-free quadratic contraction of `Rm` with itself (a finite `Finset`/`ring` identity on the `finrank`-frame components `rmC`), then induct on `j` with the product rule for the covariant derivative of a metric contraction of two tensor fields (the metric is parallel) plus the componentwise Cauchy–Schwarz bound for the contraction; the model tools are `Work.Diff.EXT.multilinear_frame_bound` and `Work.Diff.EXT.sq_covKRmC_le_curvNormK`. -/
theorem reaction0_jets
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g : Submission.Diff.SMet I M) (x : M)
        (G : Fin (4 + j) → Work.Diff.EXT.TField (I := I) (M := M)),
        (∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (G i)) →
        |Work.Diff.EXT.jetAll g j 4
            (fun (F : Fin 4 → Work.Diff.EXT.TField (I := I) (M := M)) => fun (y : M) =>
              Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap g y (F 0 y) (F 1 y) (F 2 y) (F 3 y))
            G x|
          ≤ C * Work.Diff.EXT.Shape g x j
              * ∏ r : Fin (4 + j), Real.sqrt (g.inner x (G r x) (G r x)) := by
  obtain ⟨C₀, hC₀, hC₀b⟩ := RmPair.rmSym_bound (Module.finrank ℝ E)
  refine ⟨(2 : ℝ) ^ j * (C₀ * ((Module.finrank ℝ E : ℝ) ^ 4 + 1)), ?_, ?_⟩
  · positivity
  · intro g x G hG
    have hLC : Submission.Diff.LCSmooth I M := Work.EXT.lcSmooth_noBoundary
    obtain ⟨W, hWs, hWON, hWx, hWgeo⟩ := Work.Diff.EXT.evX.geodesic_frame_clean g x
    set U : Set M := interior {y : M | Submission.Diff.IsONFrame g y (fun i => W i y)} with hUdef
    have hUopen : IsOpen U := isOpen_interior
    have hxU : x ∈ U := mem_interior_iff_mem_nhds.mpr hWON
    have hUsub : U ⊆ {y : M | Submission.Diff.IsONFrame g y (fun i => W i y)} := interior_subset
    have hbil : ∀ A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ,
        ∀ X Y : Curv4 (Module.finrank ℝ E),
          reactionBilin (rot A X) (rot A Y) = rot A (reactionBilin X Y) :=
      fun A hA X Y => reactionBilin_rot A hA X Y
    have hexp := jetAll_expansion hLC g W hWs U hUopen hUsub hbil j G hG x hxU
    rw [hexp]
    have hmain : ∀ f : Fin j → Bool,
        |MonoF (I := I) (M := M) g j f W G x|
          ≤ (C₀ * ((Module.finrank ℝ E : ℝ) ^ 4 + 1)) * Shape g x j
            * ∏ r : Fin (4 + j), Real.sqrt (g.inner x (G r x) (G r x)) := by
      intro f
      obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8⟩ := Mono.fam_props_T2b j f
      have hfam := fam_len j f
      have hmb := Mono.MonoD_bound (C₀ := C₀) hC₀ hC₀b hLC g x (4 + j) (fam j f).1.1 (fam j f).2.1
        (fam j f).1.2 (fam j f).2.2 (slotS j) W hWs (hUsub hxU) G hG
      have hprod := hp8 (fun r => Real.sqrt (g.inner x (G r x) (G r x)))
      have hshape := sqrt_mul_sqrt_le_Shape g x (a := (fam j f).1.1) (b := (fam j f).2.1)
        (by omega)
      have hB : 0 ≤ ∏ r : Fin (4 + j), Real.sqrt (g.inner x (G r x) (G r x)) :=
        Finset.prod_nonneg (fun r _ => Real.sqrt_nonneg _)
      have hC1 : 0 ≤ C₀ * ((Module.finrank ℝ E : ℝ) ^ 4 + 1) :=
        mul_nonneg hC₀ (by positivity)
      calc |MonoF (I := I) (M := M) g j f W G x|
          ≤ (C₀ * ((Module.finrank ℝ E : ℝ) ^ 4 + 1))
              * (Real.sqrt (curvNormK g x (fam j f).1.1)
                  * ∏ r : Fin (fam j f).1.1, Real.sqrt (g.inner x (G ((fam j f).1.2 r) x) (G ((fam j f).1.2 r) x)))
              * (Real.sqrt (curvNormK g x (fam j f).2.1)
                  * ∏ r : Fin (fam j f).2.1, Real.sqrt (g.inner x (G ((fam j f).2.2 r) x) (G ((fam j f).2.2 r) x)))
              * (∏ t : Fin 4, Real.sqrt (g.inner x (G (slotS j t) x) (G (slotS j t) x))) := hmb
        _ = (C₀ * ((Module.finrank ℝ E : ℝ) ^ 4 + 1))
              * ((Real.sqrt (curvNormK g x (fam j f).1.1)
                    * Real.sqrt (curvNormK g x (fam j f).2.1))
                  * (∏ r : Fin (4 + j), Real.sqrt (g.inner x (G r x) (G r x)))) := by
            rw [← hprod]; ring
        _ ≤ (C₀ * ((Module.finrank ℝ E : ℝ) ^ 4 + 1))
              * (Shape g x j * ∏ r : Fin (4 + j), Real.sqrt (g.inner x (G r x) (G r x))) := by
            refine mul_le_mul_of_nonneg_left ?_ hC1
            exact mul_le_mul_of_nonneg_right hshape hB
        _ = (C₀ * ((Module.finrank ℝ E : ℝ) ^ 4 + 1)) * Shape g x j
              * ∏ r : Fin (4 + j), Real.sqrt (g.inner x (G r x) (G r x)) := by ring
    calc |∑ f : Fin j → Bool, MonoF (I := I) (M := M) g j f W G x|
        ≤ ∑ f : Fin j → Bool, |MonoF (I := I) (M := M) g j f W G x| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ f : Fin j → Bool, (C₀ * ((Module.finrank ℝ E : ℝ) ^ 4 + 1)) * Shape g x j
            * ∏ r : Fin (4 + j), Real.sqrt (g.inner x (G r x) (G r x)) :=
          Finset.sum_le_sum (fun f _ => hmain f)
      _ = ((2 : ℝ) ^ j * (C₀ * ((Module.finrank ℝ E : ℝ) ^ 4 + 1))) * Shape g x j
            * ∏ r : Fin (4 + j), Real.sqrt (g.inner x (G r x) (G r x)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_bool, nsmul_eq_mul]
          push_cast
          ring

end Work.Diff.EXT
