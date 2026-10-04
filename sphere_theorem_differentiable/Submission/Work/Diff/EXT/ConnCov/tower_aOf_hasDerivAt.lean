import Mathlib
import Submission.Work.Diff.EXT.ConnCov.Kit
import Submission.Work.Diff.T.lcOf_apply_inner_koszul
import Submission.Work.Diff.EXT.covK_metric_pairing_family
import Submission.Work.Diff.EXT.covK_spatialDeriv
import Submission.Work.Diff.EXT.covK_familySmooth
import Submission.Work.Diff.EXT.ATower.connDiff_flip_input
import Submission.Work.Diff.GE.hasDerivAt_mvfderiv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The time derivative of the `∇^{G 0}`-tower of the connection difference

The frozen tower `Work.Diff.EXT.covKAExt G t k` is the `k`-th iterated covariant derivative, with
respect to the *fixed* background connection `∇^{G 0} = lcOf (G 0)`, of the lowered connection
difference `aOf G t = g_t(∇^{g_t} − ∇^{g_0})`.  Equivalently
(`Work.Diff.EXT.ATower.tower_eq_covKAExt`)

`covKAExt G t k = tower (lcOf (G 0)) (fun _ => aOf G t) k`,

and the *only* time dependence of the right-hand side is through the base `aOf G t` (the recursion
step `ATower.step` uses the fixed connection `∇^{G 0}` everywhere else).

Hence the time derivative of the tower is obtained by differentiating the base in time, i.e. by
replacing `aOf G t` by `Work.Diff.EXT.ConnCov.dAOfBase G t`; this is exactly the statement proved
here.  Two ingredients are needed at each level:

* **Clairaut** (`Work.Diff.GE.hasDerivAt_mvfderiv`): `∂_s (mvfderiv I (Φ_s) x v) = mvfderiv I
  (∂_s Φ_s) x v`, which requires the joint smoothness of `(s,y) ↦ Φ_s y` near `(t,x)`;
* **differentiability of the correction terms**, which is the induction hypothesis one level down.

The joint smoothness of the tower family `(s,y) ↦ tower (lcOf (G 0)) (fun _ => aOf G s) k v A B C y`
is therefore proved *simultaneously* (in fact, first: the derivative statement uses it at one level
below), from

* the **Koszul formula** `Work.Diff.T.lcOf_apply_inner_koszul` for the joint smoothness at level `0`
  (it expresses `(G t).inner y (lcOf (G t) B y (A y)) (C y)`, for *fixed* smooth `A B C`, through
  jointly smooth metric pairings — this is what replaces the (still open) `covK_lcOfFamily`),
* `Work.Diff.EXT.covK_metric_pairing_family` (joint smoothness of the metric pairing),
* `Work.Diff.EXT.covK_spatialDeriv` (the spatial `mvfderiv` of a jointly smooth family is jointly
  smooth),
* `Work.Diff.EXT.ATower.lcOf_apply_smE` (spatial smoothness of `lcOf (G 0) Y Z`).

Note that the flow is only jointly smooth on the half-open slab `[0,T)`, which is *not* a
neighbourhood of the interior time `t`; everything is therefore done on the open cylinder
`V := (0,T) × M` (a neighbourhood of `(t,x)`), not on the slab.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.ConnCov

open Work.Diff.EXT.ATower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-! ## Two elementary helpers -/

/-- Overwriting one slot of a tuple of smooth fields keeps it smooth. -/
lemma smE_update {k : ℕ} {W : Fin k → (Π y : M, TangentSpace I y)}
    (hW : ∀ i, SmE I M (W i)) {j : Fin k} {X : Π y : M, TangentSpace I y} (hX : SmE I M X) :
    ∀ i, SmE I M (Function.update W j X i) := by
  intro i
  by_cases h : i = j
  · subst h
    rw [Function.update_self]
    exact hX
  · rw [Function.update_of_ne h]
    exact hW i

/-- **One recursion step of the tower, unfolded** (definitional). -/
lemma tower_succ_apply (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (β : Op3 (I := I) (M := M) 0) (k : ℕ)
    (w : Fin (k + 1) → (Π y : M, TangentSpace I y)) (A B C : Π y : M, TangentSpace I y)
    (x : M) :
    tower cov β (k + 1) w A B C x
      = mvfderiv I (tower cov β k (fun i : Fin k => w i.succ) A B C) x (w 0 x)
        - (∑ i : Fin k, tower cov β k
            (Function.update (fun j : Fin k => w j.succ) i
              (fun y => cov (w i.succ) y (w 0 y))) A B C x)
        - tower cov β k (fun i : Fin k => w i.succ) (fun y => cov A y (w 0 y)) B C x
        - tower cov β k (fun i : Fin k => w i.succ) A (fun y => cov B y (w 0 y)) C x
        - tower cov β k (fun i : Fin k => w i.succ) A B (fun y => cov C y (w 0 y)) x :=
  rfl

/-- At level `0` the tower is the base (definitional). -/
lemma tower_zero_apply (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (β : Op3 (I := I) (M := M) 0) (w : Fin 0 → (Π y : M, TangentSpace I y))
    (A B C : Π y : M, TangentSpace I y) (x : M) :
    tower cov β 0 w A B C x = β w A B C x :=
  rfl

/-- The Lie bracket of two globally smooth fields is globally smooth. -/
lemma smE_mlieBracket {X Y : Π y : M, TangentSpace I y} (hX : SmE I M X) (hY : SmE I M Y) :
    SmE I M (mlieBracket I X Y) := by
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  haveI : IsManifold I ((∞ : ℕ∞ω) + 1) M := by
    have h : (∞ : ℕ∞ω) + 1 = ∞ := by simp
    rw [h]; infer_instance
  intro y
  exact (hX y).mlieBracket_vectorField (hY y) (by simp)

/-- **Joint smoothness of the lowered connection difference** on an open set `V ⊆ ℝ × M`: this is
the `k = 0` case of the joint smoothness of the tower.  It is proved from the *Koszul formula* for
the Levi-Civita connection (`Work.Diff.T.lcOf_apply_inner_koszul`), which expresses the pairing
`(G t).inner y (lcOf (G t) B y (A y)) (C y)` — `A`, `B`, `C` are *fixed* smooth fields — through
jointly smooth metric pairings and their spatial derivatives (`covK_metric_pairing_family` and
`covK_spatialDeriv`).  (This avoids `covK_lcOfFamily`, whose proof chain is not yet closed.) -/
lemma aOf_contMDiffOn {G : ℝ → SMet I M} {V : Set (ℝ × M)} (hV : IsOpen V)
    (hJM : JointMet (I := I) (M := M) G V) (hLC : Submission.Diff.LCSmooth I M)
    {A B C : Π y : M, TangentSpace I y} (hA : SmE I M A) (hB : SmE I M B) (hC : SmE I M C) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => aOf G p.1 A B C p.2) V := by
  have hsub : V ⊆ (Set.univ : Set (ℝ × M)) := fun _ _ => trivial
  have cst : ∀ {W : Π y : M, TangentSpace I y}, SmE I M W →
      JointField (fun _ : ℝ => W) V :=
    fun {W} hW => ContMDiffOn.mono (jointField_const (I := I) (M := M) hW) hsub
  have hpair : ∀ {W1 W2 : Π y : M, TangentSpace I y}, SmE I M W1 → SmE I M W2 →
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => (G p.1).inner p.2 (W1 p.2) (W2 p.2)) V :=
    fun {W1 W2} h1 h2 => covK_metric_pairing_family (I := I) (M := M) (G := G) hJM
      (cst h1) (cst h2)
  have hderiv : ∀ {W1 W2 W3 : Π y : M, TangentSpace I y}, SmE I M W1 → SmE I M W2 → SmE I M W3 →
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => mvfderiv I
          (fun y : M => (G p.1).inner y (W1 y) (W2 y)) p.2 (W3 p.2)) V :=
    fun {W1 W2 W3} h1 h2 h3 => covK_spatialDeriv (I := I) (M := M)
      (Φ := fun s (y : M) => (G s).inner y (W1 y) (W2 y)) hV (hpair h1 h2) (cst h3)
  -- the pointwise Koszul identity
  have hpt : ∀ p : ℝ × M, aOf G p.1 A B C p.2
      = (1 / 2 : ℝ) *
          (mvfderiv I (fun y : M => (G p.1).inner y (B y) (C y)) p.2 (A p.2)
            + mvfderiv I (fun y : M => (G p.1).inner y (C y) (A y)) p.2 (B p.2)
            - mvfderiv I (fun y : M => (G p.1).inner y (A y) (B y)) p.2 (C p.2)
            - (G p.1).inner p.2 (B p.2) (mlieBracket I A C p.2)
            - (G p.1).inner p.2 (C p.2) (mlieBracket I B A p.2)
            + (G p.1).inner p.2 (A p.2) (mlieBracket I C B p.2))
        - (G p.1).inner p.2 ((Submission.Diff.lcOf (G 0)) B p.2 (A p.2)) (C p.2) := by
    intro p
    rw [aOf, map_sub, sub_apply,
      Work.Diff.T.lcOf_apply_inner_koszul (I := I) (M := M) G p.1 A B C hA hB hC p.2]
  -- smoothness of the six terms of the Koszul expression and of the constant correction
  have h1 := hderiv (W1 := B) (W2 := C) (W3 := A) hB hC hA
  have h2 := hderiv (W1 := C) (W2 := A) (W3 := B) hC hA hB
  have h3 := hderiv (W1 := A) (W2 := B) (W3 := C) hA hB hC
  have h4 := hpair (W1 := B) (W2 := mlieBracket I A C) hB (smE_mlieBracket hA hC)
  have h5 := hpair (W1 := C) (W2 := mlieBracket I B A) hC (smE_mlieBracket hB hA)
  have h6 := hpair (W1 := A) (W2 := mlieBracket I C B) hA (smE_mlieBracket hC hB)
  have h7 := hpair (W1 := fun y : M => (Submission.Diff.lcOf (G 0)) B y (A y)) (W2 := C)
    (lcOf_apply_smE hLC (G 0) B A hB hA) hC
  have hcomb : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (1 / 2 : ℝ) *
          (mvfderiv I (fun y : M => (G p.1).inner y (B y) (C y)) p.2 (A p.2)
            + mvfderiv I (fun y : M => (G p.1).inner y (C y) (A y)) p.2 (B p.2)
            - mvfderiv I (fun y : M => (G p.1).inner y (A y) (B y)) p.2 (C p.2)
            - (G p.1).inner p.2 (B p.2) (mlieBracket I A C p.2)
            - (G p.1).inner p.2 (C p.2) (mlieBracket I B A p.2)
            + (G p.1).inner p.2 (A p.2) (mlieBracket I C B p.2))
        - (G p.1).inner p.2 ((Submission.Diff.lcOf (G 0)) B p.2 (A p.2)) (C p.2)) V :=
    ((contMDiffOn_const (c := (1 / 2 : ℝ))).mul
      (((((h1.add h2).sub h3).sub h4).sub h5).add h6)).sub h7
  refine ContMDiffOn.congr hcomb (fun p hp => hpt p)

theorem tower_aOf_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T)
    (k : ℕ) (v : Fin k → (Π y : M, TangentSpace I y))
    (A B C : Π y : M, TangentSpace I y)
    (hv : ∀ i, Work.Diff.EXT.ATower.SmE I M (v i))
    (hA : Work.Diff.EXT.ATower.SmE I M A)
    (hB : Work.Diff.EXT.ATower.SmE I M B)
    (hC : Work.Diff.EXT.ATower.SmE I M C) (x : M) :
    HasDerivAt (fun s : ℝ => Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
        (fun _ => Work.Diff.EXT.aOf G s) k v A B C x)
      (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
        (Work.Diff.EXT.ConnCov.dAOfBase G t) k v A B C x) t := by
  classical
  -- ## the open cylinder on which the flow is jointly smooth
  let V : Set (ℝ × M) := Set.Ioo 0 T ×ˢ (Set.univ : Set M)
  have hV : IsOpen V := isOpen_Ioo.prod isOpen_univ
  have htx : (t, x) ∈ V := ⟨ht, Set.mem_univ x⟩
  have htz : ∀ z : M, (t, z) ∈ V := fun z => ⟨ht, Set.mem_univ z⟩
  have hVnhds : V ∈ 𝓝 (t, x) := hV.mem_nhds htx
  have hsub : V ⊆ (Set.univ : Set (ℝ × M)) := fun _ _ => trivial
  have hJM : JointMet (I := I) (M := M) G V :=
    ContMDiffOn.mono ((jointMet_prod (I := I) (M := M) G (Set.Ico 0 T)).mp hflow.1)
      (Set.prod_mono Set.Ioo_subset_Ico_self (subset_refl _))
  -- ## the base of the tower, and its time derivative
  let base : ℝ → Op3 (I := I) (M := M) 0 := fun s _ A B C y => aOf G s A B C y
  let baseD : Op3 (I := I) (M := M) 0 := dAOfBase G t
  -- ## (A) joint smoothness of the tower family
  have hJ : ∀ k : ℕ, ∀ (w : Fin k → (Π y : M, TangentSpace I y))
      (A B C : Π y : M, TangentSpace I y),
      (∀ i, SmE I M (w i)) → SmE I M A → SmE I M B → SmE I M C →
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M =>
          tower (Submission.Diff.lcOf (G 0)) (base p.1) k w A B C p.2) V := by
    intro k
    induction k with
    | zero =>
      intro w A B C hw hA hB hC
      refine ContMDiffOn.congr
        (aOf_contMDiffOn (I := I) (M := M) hV hJM hLC hA hB hC) (fun p hp => ?_)
      exact tower_zero_apply (Submission.Diff.lcOf (G 0)) (base p.1) w A B C p.2
    | succ k ih =>
      intro w A B C hw hA hB hC
      have htail : ∀ i : Fin k, SmE I M ((fun j : Fin k => w j.succ) i) := fun i => hw i.succ
      have hw0 : SmE I M (w 0) := hw 0
      have hFA : SmE I M (fun y : M => (Submission.Diff.lcOf (G 0)) A y (w 0 y)) :=
        lcOf_apply_smE hLC (G 0) A (w 0) hA hw0
      have hFB : SmE I M (fun y : M => (Submission.Diff.lcOf (G 0)) B y (w 0 y)) :=
        lcOf_apply_smE hLC (G 0) B (w 0) hB hw0
      have hFC : SmE I M (fun y : M => (Submission.Diff.lcOf (G 0)) C y (w 0 y)) :=
        lcOf_apply_smE hLC (G 0) C (w 0) hC hw0
      have hstep : (fun p : ℝ × M =>
            tower (Submission.Diff.lcOf (G 0)) (base p.1) (k + 1) w A B C p.2)
          = fun p : ℝ × M =>
              mvfderiv I (tower (Submission.Diff.lcOf (G 0)) (base p.1) k
                (fun i : Fin k => w i.succ) A B C) p.2 (w 0 p.2)
              - (∑ i : Fin k, tower (Submission.Diff.lcOf (G 0)) (base p.1) k
                  (Function.update (fun j : Fin k => w j.succ) i
                    (fun y => (Submission.Diff.lcOf (G 0)) (w i.succ) y (w 0 y))) A B C p.2)
              - tower (Submission.Diff.lcOf (G 0)) (base p.1) k
                  (fun i : Fin k => w i.succ)
                  (fun y => (Submission.Diff.lcOf (G 0)) A y (w 0 y)) B C p.2
              - tower (Submission.Diff.lcOf (G 0)) (base p.1) k
                  (fun i : Fin k => w i.succ) A
                  (fun y => (Submission.Diff.lcOf (G 0)) B y (w 0 y)) C p.2
              - tower (Submission.Diff.lcOf (G 0)) (base p.1) k
                  (fun i : Fin k => w i.succ) A B
                  (fun y => (Submission.Diff.lcOf (G 0)) C y (w 0 y)) p.2 := by
        funext p
        exact tower_succ_apply (Submission.Diff.lcOf (G 0)) (base p.1) k w A B C p.2
      rw [hstep]
      have h1 : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => mvfderiv I (tower (Submission.Diff.lcOf (G 0)) (base p.1) k
            (fun i : Fin k => w i.succ) A B C) p.2 (w 0 p.2)) V :=
        covK_spatialDeriv (I := I) (M := M)
          (Φ := fun s (y : M) => tower (Submission.Diff.lcOf (G 0)) (base s) k
            (fun i : Fin k => w i.succ) A B C y) hV
          (ih (fun i : Fin k => w i.succ) A B C htail hA hB hC)
          (show JointField (fun _ : ℝ => w 0) V from
            ContMDiffOn.mono (jointField_const (I := I) (M := M) hw0) hsub)
      have h2i : ∀ i : Fin k, ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => tower (Submission.Diff.lcOf (G 0)) (base p.1) k
              (Function.update (fun j : Fin k => w j.succ) i
                (fun y => (Submission.Diff.lcOf (G 0)) (w i.succ) y (w 0 y))) A B C p.2) V :=
        fun i => ih _ A B C
          (smE_update htail
            (lcOf_apply_smE hLC (G 0) (w i.succ) (w 0) (hw i.succ) hw0)) hA hB hC
      have h2 : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => ∑ i : Fin k, tower (Submission.Diff.lcOf (G 0)) (base p.1) k
              (Function.update (fun j : Fin k => w j.succ) i
                (fun y => (Submission.Diff.lcOf (G 0)) (w i.succ) y (w 0 y))) A B C p.2) V := by
        intro p hp
        exact ContMDiffWithinAt.sum (t := Finset.univ) (fun i _ => h2i i p hp)
      have h3 : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => tower (Submission.Diff.lcOf (G 0)) (base p.1) k
              (fun i : Fin k => w i.succ)
              (fun y => (Submission.Diff.lcOf (G 0)) A y (w 0 y)) B C p.2) V :=
        ih (fun i : Fin k => w i.succ) _ B C htail hFA hB hC
      have h4 : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => tower (Submission.Diff.lcOf (G 0)) (base p.1) k
              (fun i : Fin k => w i.succ) A
              (fun y => (Submission.Diff.lcOf (G 0)) B y (w 0 y)) C p.2) V :=
        ih (fun i : Fin k => w i.succ) A _ C htail hA hFB hC
      have h5 : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => tower (Submission.Diff.lcOf (G 0)) (base p.1) k
              (fun i : Fin k => w i.succ) A B
              (fun y => (Submission.Diff.lcOf (G 0)) C y (w 0 y)) p.2) V :=
        ih (fun i : Fin k => w i.succ) A B _ htail hA hB hFC
      exact ((((h1.sub h2).sub h3).sub h4).sub h5)
  -- ## (B) the time derivative of the tower family
  have hD : ∀ k : ℕ, ∀ (w : Fin k → (Π y : M, TangentSpace I y))
      (A B C : Π y : M, TangentSpace I y),
      (∀ i, SmE I M (w i)) → SmE I M A → SmE I M B → SmE I M C →
      ∀ z : M, HasDerivAt
        (fun s : ℝ => tower (Submission.Diff.lcOf (G 0)) (base s) k w A B C z)
        (tower (Submission.Diff.lcOf (G 0)) baseD k w A B C z) t := by
    intro k
    induction k with
    | zero =>
      intro w A B C hw hA hB hC z
      have h0 := aOf_contMDiffOn (I := I) (M := M) hV hJM hLC hA hB hC
      have hAt := h0.contMDiffAt (hV.mem_nhds (htz z))
      have hcomp : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => aOf G s A B C z) t := by
        have hslice : ContMDiffAt 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I) ∞ (fun s : ℝ => (s, z)) t :=
          contMDiffAt_id.prodMk (contMDiffAt_const (c := z))
        have hc := ContMDiffAt.comp (f := fun s : ℝ => (s, z))
          (g := fun p : ℝ × M => aOf G p.1 A B C p.2) t hAt hslice
        exact hc.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => rfl))
      exact (hcomp.contDiffAt.differentiableAt (by simp)).hasDerivAt
    | succ k ih =>
      intro w A B C hw hA hB hC z
      have htail : ∀ i : Fin k, SmE I M ((fun j : Fin k => w j.succ) i) := fun i => hw i.succ
      have hw0 : SmE I M (w 0) := hw 0
      have hFA : SmE I M (fun y : M => (Submission.Diff.lcOf (G 0)) A y (w 0 y)) :=
        lcOf_apply_smE hLC (G 0) A (w 0) hA hw0
      have hFB : SmE I M (fun y : M => (Submission.Diff.lcOf (G 0)) B y (w 0 y)) :=
        lcOf_apply_smE hLC (G 0) B (w 0) hB hw0
      have hFC : SmE I M (fun y : M => (Submission.Diff.lcOf (G 0)) C y (w 0 y)) :=
        lcOf_apply_smE hLC (G 0) C (w 0) hC hw0
      -- ## Clairaut: the `mvfderiv` term
      have hΦ : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => tower (Submission.Diff.lcOf (G 0)) (base p.1) k
            (fun i : Fin k => w i.succ) A B C p.2) (t, z) :=
        (hJ k (fun i : Fin k => w i.succ) A B C htail hA hB hC).contMDiffAt
          (hV.mem_nhds (htz z))
      have hd1 := Work.Diff.GE.hasDerivAt_mvfderiv (I := I) (M := M)
        (Φ := fun s (y : M) => tower (Submission.Diff.lcOf (G 0)) (base s) k
          (fun i : Fin k => w i.succ) A B C y)
        (t := t) (x := z) (v := w 0 z) hΦ
      have heqfun : (fun y : M => deriv (fun s : ℝ => tower (Submission.Diff.lcOf (G 0))
            (base s) k (fun i : Fin k => w i.succ) A B C y) t)
          = fun y : M => tower (Submission.Diff.lcOf (G 0)) baseD k
              (fun i : Fin k => w i.succ) A B C y :=
        funext (fun y => (ih (fun i : Fin k => w i.succ) A B C htail hA hB hC y).deriv)
      have hd1' : HasDerivAt
          (fun s : ℝ => mvfderiv I (fun y : M => tower (Submission.Diff.lcOf (G 0))
            (base s) k (fun i : Fin k => w i.succ) A B C y) z (w 0 z))
          (mvfderiv I (fun y : M => tower (Submission.Diff.lcOf (G 0)) baseD k
            (fun i : Fin k => w i.succ) A B C y) z (w 0 z)) t :=
        hd1.congr_deriv
          (congrArg (fun F : M → ℝ => mvfderiv I F z (w 0 z)) heqfun)
      -- ## the correction terms, one slot at a time
      have hd2i : ∀ i : Fin k, HasDerivAt
          (fun s : ℝ => tower (Submission.Diff.lcOf (G 0)) (base s) k
              (Function.update (fun j : Fin k => w j.succ) i
                (fun y => (Submission.Diff.lcOf (G 0)) (w i.succ) y (w 0 y))) A B C z)
          (tower (Submission.Diff.lcOf (G 0)) baseD k
              (Function.update (fun j : Fin k => w j.succ) i
                (fun y => (Submission.Diff.lcOf (G 0)) (w i.succ) y (w 0 y))) A B C z) t :=
        fun i => ih _ A B C
          (smE_update htail
            (lcOf_apply_smE hLC (G 0) (w i.succ) (w 0) (hw i.succ) hw0)) hA hB hC z
      have hd2 : HasDerivAt
          (fun s : ℝ => ∑ i : Fin k, tower (Submission.Diff.lcOf (G 0)) (base s) k
              (Function.update (fun j : Fin k => w j.succ) i
                (fun y => (Submission.Diff.lcOf (G 0)) (w i.succ) y (w 0 y))) A B C z)
          (∑ i : Fin k, tower (Submission.Diff.lcOf (G 0)) baseD k
              (Function.update (fun j : Fin k => w j.succ) i
                (fun y => (Submission.Diff.lcOf (G 0)) (w i.succ) y (w 0 y))) A B C z) t := by
        let Af : Fin k → ℝ → ℝ := fun i s => tower (Submission.Diff.lcOf (G 0)) (base s) k
          (Function.update (fun j : Fin k => w j.succ) i
            (fun y => (Submission.Diff.lcOf (G 0)) (w i.succ) y (w 0 y))) A B C z
        let Af' : Fin k → ℝ := fun i => tower (Submission.Diff.lcOf (G 0)) baseD k
          (Function.update (fun j : Fin k => w j.succ) i
            (fun y => (Submission.Diff.lcOf (G 0)) (w i.succ) y (w 0 y))) A B C z
        have hsum := HasDerivAt.sum (u := Finset.univ) (A := Af) (A' := Af')
          (fun i _ => hd2i i)
        refine hsum.congr_of_eventuallyEq ?_
        exact Filter.Eventually.of_forall (fun s => (Finset.sum_apply s Finset.univ Af).symm)
      have hd3 : HasDerivAt
          (fun s : ℝ => tower (Submission.Diff.lcOf (G 0)) (base s) k
              (fun i : Fin k => w i.succ)
              (fun y => (Submission.Diff.lcOf (G 0)) A y (w 0 y)) B C z)
          (tower (Submission.Diff.lcOf (G 0)) baseD k (fun i : Fin k => w i.succ)
              (fun y => (Submission.Diff.lcOf (G 0)) A y (w 0 y)) B C z) t :=
        ih (fun i : Fin k => w i.succ) _ B C htail hFA hB hC z
      have hd4 : HasDerivAt
          (fun s : ℝ => tower (Submission.Diff.lcOf (G 0)) (base s) k
              (fun i : Fin k => w i.succ) A
              (fun y => (Submission.Diff.lcOf (G 0)) B y (w 0 y)) C z)
          (tower (Submission.Diff.lcOf (G 0)) baseD k (fun i : Fin k => w i.succ) A
              (fun y => (Submission.Diff.lcOf (G 0)) B y (w 0 y)) C z) t :=
        ih (fun i : Fin k => w i.succ) A _ C htail hA hFB hC z
      have hd5 : HasDerivAt
          (fun s : ℝ => tower (Submission.Diff.lcOf (G 0)) (base s) k
              (fun i : Fin k => w i.succ) A B
              (fun y => (Submission.Diff.lcOf (G 0)) C y (w 0 y)) z)
          (tower (Submission.Diff.lcOf (G 0)) baseD k (fun i : Fin k => w i.succ) A B
              (fun y => (Submission.Diff.lcOf (G 0)) C y (w 0 y)) z) t :=
        ih (fun i : Fin k => w i.succ) A B _ htail hA hB hFC z
      exact ((((hd1'.sub hd2).sub hd3).sub hd4).sub hd5)
  exact hD k v A B C hv hA hB hC x

end Work.Diff.EXT.ConnCov
