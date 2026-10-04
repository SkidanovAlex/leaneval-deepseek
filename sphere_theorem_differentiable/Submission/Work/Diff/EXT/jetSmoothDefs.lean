import Mathlib
import Submission.Work.Diff.EXT.ladderSrcDefs
import Submission.Work.Diff.EXT.ladderEfDefs
import Submission.Work.Diff.EXT.jetAll_extStep
import Submission.Work.Diff.EXT.evolX.ladderPlumb
import Submission.Work.EXT.lcSmooth_noBoundary

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Linearity of `jetAll` in the packed operator, and the two source jets of the ladder step

`Work.Diff.EXT.ladderEfD_step` bounds the difference

`jetAll (G t) j (k+1+4) (reactOpEfD Ef G t (k+1)) − jetAll (G t) (j+1) (k+4) (reactOpEfD Ef G t k)`

of two jets of the *reaction* `R_k = ∂ₜ⁺(∇^k Rm) − Δ(∇^k Rm)` of a Ricci flow.  Since
`reactOpEfD Ef G t k = dtOpD G t k − lapOpE Ef (G t) k` *by definition* (as an operator
subtraction), the difference is the difference of the two *sources*

* `Work.Diff.EXT.srcConnvar G t k = dtOpD G t (k+1) − extStep (G t) (dtOpD G t k)` — the
  connection-variation source,
* `Work.Diff.EXT.srcLapComm Ef g k = lapOpE Ef g (k+1) − extStep g (lapOpE Ef g k)` — the
  Weitzenböck source,

equivalently (after moving the `extStep` from the jet order into the arity, which is
`Work.Diff.EXT.jetAll_extStep`) the four individual jets

`jetAll (G t) j (k+1+4) (dtOpD G t (k+1))`, `jetAll (G t) (j+1) (k+4) (dtOpD G t k)`,
`jetAll (G t) j (k+1+4) (lapOpE Ef (G t) (k+1))`, `jetAll (G t) (j+1) (k+4) (lapOpE Ef (G t) k)`.

## Why an extra hypothesis appears

`jetAll` is built from `mvfderiv`, and `mvfderiv I (fun y ↦ a y − b y) x` is **not** the difference
`mvfderiv I a x − mvfderiv I b x` unless both `a` and `b` are mdifferentiable at `x` (Mathlib's
`mfderiv` is `0` on the non-differentiable locus, so the "junk" does not respect subtraction).
Consequently the identity

`jetAll g j K (S − S') F x = jetAll g j K S F x − jetAll g j K S' F x`

— which is what makes the split of the reaction into its two sources valid — holds exactly on the
operators whose jets are mdifferentiable.  This module isolates that condition as
`Work.Diff.EXT.JetSmoothOp` and proves the linearity under it; the discharging of the condition for
the two concrete operators `dtOpD` and `lapOpE` is the (delegated) content of
`Work.Diff.EXT.evolX.opJetSmooth_dtOpD` / `Work.Diff.EXT.evolX.opJetSmooth_lapOpE`.

The mathematical content of the two source estimates themselves is
`Work.Diff.EXT.evolX.connVar_src_jets` and `Work.Diff.EXT.evolX.lapComm_src_jets`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **Smoothness of all the jets of a packed operator.**  `JetSmoothOp g K S x` says that, for every
jet order `l` and every tuple `F` of smooth fields, the function `y ↦ jetAll g l K S F y` is
mdifferentiable at every point of a neighbourhood of `x`.  This is exactly the condition under
which `mvfderiv` is additive on `S − S'` (and the Leibniz corrections of `extStep` are additive),
hence under which `jetAll` is linear in the operator. -/
def JetSmoothOp [T2Space M] (g : SMet I M) (K : ℕ)
    (S : (Fin K → TField (I := I) (M := M)) → M → ℝ) (x : M) : Prop :=
  ∀ᶠ y in 𝓝 x, ∀ (l : ℕ) (F : Fin (K + l) → TField (I := I) (M := M)),
    (∀ i, SmoothF (F i)) →
      MDifferentiableAt I 𝓘(ℝ, ℝ) (fun z : M => jetAll g l K S F z) y

/-- **`mvfderiv` is additive on a difference of mdifferentiable functions.** -/
theorem mvfderiv_sub_mdiff {a b : M → ℝ} {x : M}
    (ha : MDifferentiableAt I 𝓘(ℝ, ℝ) a x) (hb : MDifferentiableAt I 𝓘(ℝ, ℝ) b x) :
    mvfderiv I (a - b) x = mvfderiv I a x - mvfderiv I b x := by
  rw [mvfderiv_sub ha hb]

/-- Smoothness of a single-slot update, given the smoothness of the entries. -/
theorem smoothF_update' {K : ℕ} {F : Fin K → TField (I := I) (M := M)}
    (hF : ∀ i, SmoothF (F i)) (s : Fin K) {W : TField (I := I) (M := M)} (hW : SmoothF W) :
    ∀ i, SmoothF (Function.update F s W i) := by
  intro i
  rw [Function.update_apply]
  split_ifs with h
  · subst h; exact hW
  · exact hF i

/-- **Germ congruence of `extStep`**, in the tuples actually occurring in the recursion: only the
`K + 1` tuples `F ∘ Fin.succ` and `update (F ∘ Fin.succ) s (∇_{F 0}(F ∘ Fin.succ s))` matter. -/
theorem extStep_congr_at [T2Space M] (g : SMet I M) {K : ℕ}
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
    evolX.mvfderiv_eventuallyEq_of_eventuallyEq (I := I) h0
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

/-- **Pointwise additivity of `extStep` in the operator**, under the mdifferentiability of the two
value functions along the tail of the tuple. -/
theorem extStep_sub_apply [T2Space M] (g : SMet I M) {K : ℕ}
    (S S' : (Fin K → TField (I := I) (M := M)) → M → ℝ)
    (F : Fin (K + 1) → TField (I := I) (M := M)) (x : M)
    (hS : MDifferentiableAt I 𝓘(ℝ, ℝ) (S (fun i : Fin K => F i.succ)) x)
    (hS' : MDifferentiableAt I 𝓘(ℝ, ℝ) (S' (fun i : Fin K => F i.succ)) x) :
    extStep (I := I) (M := M) g (S - S') F x
      = extStep (I := I) (M := M) g S F x - extStep (I := I) (M := M) g S' F x := by
  have h := congrArg (fun (L : TangentSpace I x →L[ℝ] ℝ) => L (F 0 x))
    (mvfderiv_sub_mdiff (I := I) hS hS')
  simp only [sub_apply] at h
  simp only [extStep, Pi.sub_apply, Finset.sum_sub_distrib]
  rw [h]
  ring

/-- **`jetAll` is additive in the packed operator**, on operators all of whose jets are
mdifferentiable near `x`: the `j`-th jet of `S − S'` is the difference of the `j`-th jets.

The proof is the induction on the jet order.  At the step, `jetAll g (l+1) K T F` is
`extStep g (jetAll g l K T) F`, and both ingredients are available at the same stage:

* the `mvfderiv` term is additive because the two level-`l` jets are mdifferentiable at the base
  point (`JetSmoothOp`), and the `mvfderiv` of a germ-difference is the germ-difference of the
  `mvfderiv`s (`Work.Diff.EXT.evolX.mvfderiv_eventuallyEq_of_eventuallyEq`);
* the Leibniz corrections are additive term-by-term.

The induction is run with the *germ* statement `=ᶠ[𝓝 x]` as the conclusion, since the
`mvfderiv` at the next stage is taken at the same point but the operators there are evaluated
near `x`. -/
theorem jetAll_sub_of_JetSmoothOp [T2Space M] {g : SMet I M} {K : ℕ}
    (S S' : (Fin K → TField (I := I) (M := M)) → M → ℝ) (x : M)
    (hS : JetSmoothOp (I := I) (M := M) g K S x)
    (hS' : JetSmoothOp (I := I) (M := M) g K S' x) :
    ∀ (j : ℕ) (F : Fin (K + j) → TField (I := I) (M := M)),
      (∀ i, SmoothF (F i)) →
      jetAll g j K (S - S') F =ᶠ[𝓝 x]
        (fun z : M => jetAll g j K S F z - jetAll g j K S' F z) := by
  intro j
  induction j with
  | zero =>
      intro F hF
      filter_upwards with z
      simp only [jetAll, Pi.sub_apply]
  | succ l ih =>
      intro F hF
      have htail : ∀ i : Fin (K + l), SmoothF ((fun i : Fin (K + l) => F i.succ) i) :=
        fun i => hF i.succ
      have hW : ∀ s : Fin (K + l),
          SmoothF (dirF g ((fun i : Fin (K + l) => F i.succ) s) (F 0)) :=
        fun s => dirF_smooth (Work.EXT.lcSmooth_noBoundary (I := I) (M := M)) g (htail s) (hF 0)
      have h1 : extStep g (jetAll g l K (S - S')) F
          =ᶠ[𝓝 x] extStep g (jetAll g l K S - jetAll g l K S') F :=
        extStep_congr_at (I := I) (M := M) g (jetAll g l K (S - S'))
          (jetAll g l K S - jetAll g l K S') F x
          (ih (fun i : Fin (K + l) => F i.succ) htail)
          (fun s => ih (Function.update (fun i : Fin (K + l) => F i.succ) s
                (dirF g ((fun i : Fin (K + l) => F i.succ) s) (F 0)))
              (smoothF_update' htail s (hW s)))
      have h2 : extStep g (jetAll g l K S - jetAll g l K S') F
          =ᶠ[𝓝 x] (fun z : M => extStep g (jetAll g l K S) F z
            - extStep g (jetAll g l K S') F z) := by
        filter_upwards [hS, hS'] with z hzS hzS'
        exact extStep_sub_apply (I := I) (M := M) g (jetAll g l K S) (jetAll g l K S') F z
          (hzS l (fun i : Fin (K + l) => F i.succ) htail)
          (hzS' l (fun i : Fin (K + l) => F i.succ) htail)
      have e1 : jetAll g (l + 1) K (S - S') F = extStep g (jetAll g l K (S - S')) F := by
        simp only [jetAll]
      have e2 : (fun z : M => jetAll g (l + 1) K S F z - jetAll g (l + 1) K S' F z)
          = fun z : M => extStep g (jetAll g l K S) F z
              - extStep g (jetAll g l K S') F z := by
        funext z
        simp only [jetAll]
      rw [e1, e2]
      exact h1.trans h2

end Work.Diff.EXT
