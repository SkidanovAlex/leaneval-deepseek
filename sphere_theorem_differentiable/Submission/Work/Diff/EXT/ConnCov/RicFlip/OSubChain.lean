import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicFlip.OSubKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The chain rule for the one-atom substitutions (`OSubChain`)

`Work.Diff.EXT.ConnCov.RicFlip.O.OSub` is the *one-atom substitution* calculus of the connection
flip of the Ricci tower (`OSubKit`): a `b`-tuple whose `i`-th entry is the slot field `σ i`, except
at the atom index `idx`, where the entry is the atom `∇^{ord}δ := atomEval G t τ` applied to the
slots `τ`.

The target of this module is the **chain rule** for the packed covariant derivative `AMB.pD`, i.e.
for the scalar object `Θ` composed with the substitution:

  `pD cov (Θ ∘ Φ.eval) F = (pD cov Θ) (Φ.shift.eval F) + Θ (Φ.deriv.eval F)`.

It is the identity that lets the word/atom induction of `Work.Diff.EXT.ConnCov.ricTowerFlipBound`
commute the covariant derivative past a substitution.  `Φ.shift` is the substitution with the
direction slot `F 0` put in front (its `eval` is `Fin.cons (F 0) (Φ.eval (F ∘ succ))`, proved in
`OSubKit` as `OSub.eval_shift`), and `Φ.deriv` is the substitution obtained by replacing the atom
`∇^{ord}δ` by `∇^{ord+1}δ` with the direction slot as its *first* argument (`OSub.eval_deriv`).

## Proof (route)

Everything is pointwise at `x`.  Unfolding `AMB.pD` on both sides and using `eval_shift`,
`eval_deriv`, the two `mvfderiv`-terms are *literally equal*, so the content is the identity of the
connection-correction sums

  `∑ i : Fin b, Θ ((Φ.eval F')[i ↦ ∇_{…} F_0]) x - ∑ j : Fin a, Θ (Φ.eval (F'[j ↦ ∇_{F'_j} F_0])) x
      = Θ ((Φ.eval F')[idx ↦ ∇^{ord+1}δ …]) x`,

where `F' = F ∘ succ`.  Reindexing the second sum by the bijection `Φ.bij` of the one-atom
substitution (`OSub.sum_reindex`) splits it into
* the `σ i`-uses (`i ≠ Φ.idx`), which change exactly the slot `i` of `Φ.eval F'`
  (`OSub.eval_update_slot`) and cancel verbatim against the corresponding term of the first sum, and
* the `τ l`-uses (`l : Fin (ord+2)`), which change exactly the *atom* slot `idx`
  (`OSub.eval_update_atom`), with the atom carrying the `τ l`-th argument replaced.

The remaining identity is the **atom Leibniz rule** `Work.Diff.EXT.ConnCov.RicFlip.atomEvalDeriv`:
the covariant derivative of the atom along `F 0` is the same atom with each of its `ord + 2`
arguments replaced by its covariant derivative along `F 0`; since the atom *is* a `vtowerM` whose
recursion step `vstepM` has exactly this shape, this is the `vstepM`-unfolding plus `Fin`
bookkeeping.  The slot-update form of the additivity of `Θ` (`AMB.SlotAddP`, iterated over a finite
sum) then reassembles the pieces.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov.RicFlip

open Work.Diff.EXT.ATower

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## Elementary helpers -/

/-- Splitting a sum over `Fin b` at a single index, against a sum over the complement subtype. -/
lemma sum_fin_eq_add_subtype {b : ℕ} (idx : Fin b) (g : Fin b → ℝ) :
    (∑ i : Fin b, g i) = g idx + ∑ i : {i : Fin b // i ≠ idx}, g i := by
  have h := Finset.sum_erase_add (Finset.univ : Finset (Fin b)) g (Finset.mem_univ idx)
  have hsub : (∑ x ∈ Finset.univ.erase idx, g x) = ∑ i : {i : Fin b // i ≠ idx}, g i :=
    Finset.sum_subtype (Finset.univ.erase idx) (fun x => by simp) g
  rw [← h, hsub, add_comm]

/-- Smoothness of the zero tangent field (a local copy, to keep the import list light). -/
lemma smE_zero' : SmE I M (0 : AMB.TF (I := I) (M := M)) := by
  have h := contMDiff_zeroSection (𝕜 := ℝ) (F := E) (E := fun y : M => TangentSpace I y)
    (n := ∞) (IB := I)
  rw [SmE]
  exact h

/-- Smoothness of a finite sum of smooth tangent fields. -/
lemma smE_finset_sum {ι : Type*} (s : Finset ι) (u : ι → AMB.TF (I := I) (M := M))
    (hu : ∀ i, SmE I M (u i)) : SmE I M (∑ i ∈ s, u i) := by
  have h : (∑ i ∈ s, u i) = fun y : M => ∑ i ∈ s, u i y := by
    funext y; rw [Finset.sum_apply]
  rw [h]
  exact ContMDiff.sum_section (s := s) (t := u) (fun i _ => hu i)

/-- **Slot additivity of a packed object, iterated over a finite sum.** -/
lemma SlotAddPSum {N : ℕ} {Θ : AMB.Fam (I := I) (M := M) N}
    (hadd : AMB.SlotAddP (I := I) (M := M) Θ)
    {ι : Type*} (s : Finset ι) (j : Fin N)
    (H : Fin N → AMB.TF (I := I) (M := M)) (u : ι → AMB.TF (I := I) (M := M))
    (hH : ∀ i, SmE I M (H i)) (hu : ∀ i, SmE I M (u i)) (x : M) :
    Θ (Function.update H j (∑ i ∈ s, u i)) x = ∑ i ∈ s, Θ (Function.update H j (u i)) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h0 := hadd j H 0 0 hH smE_zero' smE_zero' x
      rw [add_zero] at h0
      simp only [Finset.sum_empty]
      exact add_left_cancel (show Θ (Function.update H j 0) x + Θ (Function.update H j 0) x
        = Θ (Function.update H j 0) x + 0 from by rw [add_zero]; exact h0.symm)
  | insert a t ha ih =>
      have hsum : SmE I M (∑ i ∈ t, u i) := smE_finset_sum t u hu
      rw [Finset.sum_insert ha, hadd j H (u a) (∑ i ∈ t, u i) hH (hu a) hsum x, ih,
        Finset.sum_insert ha]

/-! ## `Fin` bookkeeping for the atom Leibniz rule -/

section Atom

variable {a b ord : ℕ}

/-- Splitting a sum over `Fin (n+2)` into the `castAdd 2`-part and the last two slots. -/
lemma sum_fin_two_more {α : Type*} [AddCommMonoid α] {n : ℕ} (f : Fin (n+2) → α) :
    (∑ i : Fin (n+2), f i) = (∑ i : Fin n, f (Fin.castAdd 2 i))
      + f (Fin.natAdd n (0 : Fin 2)) + f (Fin.natAdd n (1 : Fin 2)) := by
  have h0 : ((Fin.last n).castSucc : Fin (n+2)) = Fin.natAdd n (0 : Fin 2) := by
    apply Fin.ext; simp
  have h1 : (Fin.last (n+1) : Fin (n+2)) = Fin.natAdd n (1 : Fin 2) := by
    apply Fin.ext; simp
  have h2 : ∀ i : Fin n, (i.castSucc.castSucc : Fin (n+2)) = Fin.castAdd 2 i := fun i => by
    apply Fin.ext; simp
  rw [Fin.sum_univ_castSucc (n := n+1) (f := f),
    Fin.sum_univ_castSucc (n := n) (f := fun i : Fin (n+1) => f i.castSucc), h0, h1]
  rw [show (∑ i : Fin n, f i.castSucc.castSucc) = (∑ i : Fin n, f (Fin.castAdd 2 i)) from
    Finset.sum_congr rfl (fun i _ => by rw [h2 i])]

lemma castAdd_ne_natAdd_zero {n : ℕ} (l : Fin n) :
    (Fin.castAdd 2 l : Fin (n+2)) ≠ (Fin.natAdd n (0 : Fin 2)) := by
  intro h
  have h2 := congrArg Fin.val h
  simp at h2
  omega

lemma castAdd_ne_natAdd_one {n : ℕ} (l : Fin n) :
    (Fin.castAdd 2 l : Fin (n+2)) ≠ (Fin.natAdd n (1 : Fin 2)) := by
  intro h
  have h2 := congrArg Fin.val h
  simp at h2
  omega

lemma natAdd_zero_ne_one {n : ℕ} :
    (Fin.natAdd n (0 : Fin 2) : Fin (n+2)) ≠ Fin.natAdd n (1 : Fin 2) := by
  intro h
  have h2 := congrArg Fin.val h
  simp at h2

/-- Pushing a `Function.update` through the reindexing `l ↦ Φ.τ (castAdd 2 l)`. -/
lemma update_castAdd (Φ : O.OSub a b ord) (F' : Fin a → AMB.TF (I := I) (M := M))
    (i : Fin ord) (W : AMB.TF (I := I) (M := M)) :
    Function.update (fun l : Fin ord => F' (Φ.τ (Fin.castAdd 2 l))) i W
      = fun l : Fin ord =>
          (Function.update F' (Φ.τ (Fin.castAdd 2 i)) W) (Φ.τ (Fin.castAdd 2 l)) := by
  funext l
  by_cases hl : l = i
  · subst hl; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hl]
    have hne : Φ.τ (Fin.castAdd 2 l) ≠ Φ.τ (Fin.castAdd 2 i) := fun hc =>
      hl (Fin.castAdd_inj.mp (Φ.τ_inj hc))
    rw [Function.update_of_ne hne]

lemma update_natAdd_zero_cast (Φ : O.OSub a b ord) (F' : Fin a → AMB.TF (I := I) (M := M))
    (W : AMB.TF (I := I) (M := M)) (l : Fin ord) :
    (Function.update F' (Φ.τ (Fin.natAdd ord (0 : Fin 2))) W) (Φ.τ (Fin.castAdd 2 l))
      = F' (Φ.τ (Fin.castAdd 2 l)) := by
  rw [Function.update_of_ne (fun hc => castAdd_ne_natAdd_zero l (Φ.τ_inj hc))]

lemma update_natAdd_one_cast (Φ : O.OSub a b ord) (F' : Fin a → AMB.TF (I := I) (M := M))
    (W : AMB.TF (I := I) (M := M)) (l : Fin ord) :
    (Function.update F' (Φ.τ (Fin.natAdd ord (1 : Fin 2))) W) (Φ.τ (Fin.castAdd 2 l))
      = F' (Φ.τ (Fin.castAdd 2 l)) := by
  rw [Function.update_of_ne (fun hc => castAdd_ne_natAdd_one l (Φ.τ_inj hc))]

/-- The `0`-slot of the last two is untouched by an update at the `1`-slot. -/
lemma update_natAdd_one_natAdd_zero (Φ : O.OSub a b ord) (F' : Fin a → AMB.TF (I := I) (M := M))
    (W : AMB.TF (I := I) (M := M)) :
    (Function.update F' (Φ.τ (Fin.natAdd ord (1 : Fin 2))) W) (Φ.τ (Fin.natAdd ord (0 : Fin 2)))
      = F' (Φ.τ (Fin.natAdd ord (0 : Fin 2))) := by
  rw [Function.update_of_ne (fun hc => natAdd_zero_ne_one (Φ.τ_inj hc))]

/-- The `1`-slot of the last two is untouched by an update at the `0`-slot. -/
lemma update_natAdd_zero_natAdd_one (Φ : O.OSub a b ord) (F' : Fin a → AMB.TF (I := I) (M := M))
    (W : AMB.TF (I := I) (M := M)) :
    (Function.update F' (Φ.τ (Fin.natAdd ord (0 : Fin 2))) W) (Φ.τ (Fin.natAdd ord (1 : Fin 2)))
      = F' (Φ.τ (Fin.natAdd ord (1 : Fin 2))) := by
  rw [Function.update_of_ne (fun hc => natAdd_zero_ne_one (Φ.τ_inj hc).symm)]

/-- **The atom Leibniz rule**: the covariant derivative of the atom `∇^{ord}δ` along the direction
`F 0` is `∇^{ord+1}δ`, i.e. the same atom with each of its `ord + 2` argument slots replaced by its
covariant derivative along `F 0`.  This is the `vstepM` recursion for the tower of the connection
difference plus `Fin` bookkeeping. -/
theorem atomEvalDeriv_local (Φ : O.OSub a b ord)
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    (F : Fin (a + 1) → AMB.TF (I := I) (M := M)) :
    O.atomEval G t (O.OSub.derivτ Φ.τ) F
      = fun x : M =>
          Submission.Diff.lcOf (G t)
              (O.atomEval G t Φ.τ (fun j : Fin a => F j.succ)) x (F 0 x)
          - ∑ l : Fin (ord + 2),
              O.atomEval G t Φ.τ
                (Function.update (fun j : Fin a => F j.succ) (Φ.τ l)
                  (fun y => Submission.Diff.lcOf (G t) (F (Φ.τ l).succ) y (F 0 y))) x := by
  have hLHS : O.atomEval G t (O.OSub.derivτ Φ.τ) F
      = vstepM (G t) (vtowerM (G t) (deltaBaseM G t) ord)
          (fun i : Fin (ord+1) => F (O.OSub.derivτ Φ.τ (Fin.castAdd 2 i)))
          (F (O.OSub.derivτ Φ.τ (Fin.natAdd (ord+1) (0:Fin 2))))
          (F (O.OSub.derivτ Φ.τ (Fin.natAdd (ord+1) (1:Fin 2)))) := rfl
  rw [hLHS]
  set F' : Fin a → AMB.TF (I := I) (M := M) := fun j => F j.succ with hF'def
  funext x
  simp only [vstepM]
  rw [sum_fin_two_more (f := fun l : Fin (ord+2) =>
    O.atomEval G t Φ.τ (Function.update F' (Φ.τ l)
      (fun y => Submission.Diff.lcOf (G t) (F (Φ.τ l).succ) y (F 0 y))) x)]
  -- the `lcOf`-term
  have hA : (Submission.Diff.lcOf (G t)
          (vtowerM (G t) (deltaBaseM G t) ord
            (fun i : Fin ord => F (O.OSub.derivτ Φ.τ (Fin.castAdd 2 i.succ)))
            (F (O.OSub.derivτ Φ.τ (Fin.natAdd (ord+1) (0:Fin 2))))
            (F (O.OSub.derivτ Φ.τ (Fin.natAdd (ord+1) (1:Fin 2))))) x)
        (F (O.OSub.derivτ Φ.τ (Fin.castAdd 2 (0:Fin (ord+1)))) x)
      = (Submission.Diff.lcOf (G t) (O.atomEval G t Φ.τ F') x) (F 0 x) := rfl
  -- the `∑ i : Fin ord` part
  have hB : (∑ i : Fin ord, vtowerM (G t) (deltaBaseM G t) ord
        (Function.update (fun i : Fin ord => F (O.OSub.derivτ Φ.τ (Fin.castAdd 2 i.succ))) i
          (fun y => (Submission.Diff.lcOf (G t)
              (F (O.OSub.derivτ Φ.τ (Fin.castAdd 2 i.succ))) y)
            (F (O.OSub.derivτ Φ.τ (Fin.castAdd 2 (0:Fin (ord+1)))) y)))
        (F (O.OSub.derivτ Φ.τ (Fin.natAdd (ord+1) (0:Fin 2))))
        (F (O.OSub.derivτ Φ.τ (Fin.natAdd (ord+1) (1:Fin 2)))) x)
      = (∑ i : Fin ord, O.atomEval G t Φ.τ
          (Function.update F' (Φ.τ (Fin.castAdd 2 i))
            (fun y => Submission.Diff.lcOf (G t)
              (F ((Φ.τ (Fin.castAdd 2 i)).succ)) y (F 0 y))) x) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hT : Function.update (fun i : Fin ord => F (O.OSub.derivτ Φ.τ (Fin.castAdd 2 i.succ))) i
          (fun y => (Submission.Diff.lcOf (G t)
              (F (O.OSub.derivτ Φ.τ (Fin.castAdd 2 i.succ))) y)
            (F (O.OSub.derivτ Φ.τ (Fin.castAdd 2 (0:Fin (ord+1)))) y))
        = fun l : Fin ord => (Function.update F' (Φ.τ (Fin.castAdd 2 i))
            (fun y => Submission.Diff.lcOf (G t)
              (F ((Φ.τ (Fin.castAdd 2 i)).succ)) y (F 0 y))) (Φ.τ (Fin.castAdd 2 l)) :=
      update_castAdd Φ F' i (fun y => Submission.Diff.lcOf (G t)
        (F ((Φ.τ (Fin.castAdd 2 i)).succ)) y (F 0 y))
    have hX : (F (O.OSub.derivτ Φ.τ (Fin.natAdd (ord+1) (0:Fin 2))))
        = (Function.update F' (Φ.τ (Fin.castAdd 2 i))
            (fun y => Submission.Diff.lcOf (G t)
              (F ((Φ.τ (Fin.castAdd 2 i)).succ)) y (F 0 y)))
          (Φ.τ (Fin.natAdd ord (0:Fin 2))) := by
      rw [Function.update_of_ne (fun hc => castAdd_ne_natAdd_zero i (Φ.τ_inj hc).symm)
        (fun y => Submission.Diff.lcOf (G t) (F ((Φ.τ (Fin.castAdd 2 i)).succ)) y (F 0 y)) F']
      rfl
    have hY : (F (O.OSub.derivτ Φ.τ (Fin.natAdd (ord+1) (1:Fin 2))))
        = (Function.update F' (Φ.τ (Fin.castAdd 2 i))
            (fun y => Submission.Diff.lcOf (G t)
              (F ((Φ.τ (Fin.castAdd 2 i)).succ)) y (F 0 y)))
          (Φ.τ (Fin.natAdd ord (1:Fin 2))) := by
      rw [Function.update_of_ne (fun hc => castAdd_ne_natAdd_one i (Φ.τ_inj hc).symm)
        (fun y => Submission.Diff.lcOf (G t) (F ((Φ.τ (Fin.castAdd 2 i)).succ)) y (F 0 y)) F']
      rfl
    rw [show O.atomEval G t Φ.τ (Function.update F' (Φ.τ (Fin.castAdd 2 i))
          (fun y => Submission.Diff.lcOf (G t)
            (F ((Φ.τ (Fin.castAdd 2 i)).succ)) y (F 0 y)))
        = vtowerM (G t) (deltaBaseM G t) ord
            (fun l : Fin ord => (Function.update F' (Φ.τ (Fin.castAdd 2 i))
              (fun y => Submission.Diff.lcOf (G t)
                (F ((Φ.τ (Fin.castAdd 2 i)).succ)) y (F 0 y))) (Φ.τ (Fin.castAdd 2 l)))
            ((Function.update F' (Φ.τ (Fin.castAdd 2 i))
              (fun y => Submission.Diff.lcOf (G t)
                (F ((Φ.τ (Fin.castAdd 2 i)).succ)) y (F 0 y))) (Φ.τ (Fin.natAdd ord (0:Fin 2))))
            ((Function.update F' (Φ.τ (Fin.castAdd 2 i))
              (fun y => Submission.Diff.lcOf (G t)
                (F ((Φ.τ (Fin.castAdd 2 i)).succ)) y (F 0 y))) (Φ.τ (Fin.natAdd ord (1:Fin 2))))
        from rfl]
    rw [← hT, ← hX, ← hY]
  -- the `X`-slot term
  have hC : vtowerM (G t) (deltaBaseM G t) ord
        (fun i : Fin ord => F (O.OSub.derivτ Φ.τ (Fin.castAdd 2 i.succ)))
        (fun y => (Submission.Diff.lcOf (G t)
            (F (O.OSub.derivτ Φ.τ (Fin.natAdd (ord+1) (0:Fin 2)))) y)
          (F (O.OSub.derivτ Φ.τ (Fin.castAdd 2 (0:Fin (ord+1)))) y))
        (F (O.OSub.derivτ Φ.τ (Fin.natAdd (ord+1) (1:Fin 2)))) x
      = O.atomEval G t Φ.τ (Function.update F' (Φ.τ (Fin.natAdd ord (0:Fin 2)))
          (fun y => Submission.Diff.lcOf (G t)
            (F ((Φ.τ (Fin.natAdd ord (0:Fin 2))).succ)) y (F 0 y))) x := by
    have hT : (fun i : Fin ord => F (O.OSub.derivτ Φ.τ (Fin.castAdd 2 i.succ)))
        = fun l : Fin ord => (Function.update F' (Φ.τ (Fin.natAdd ord (0:Fin 2)))
            (fun y => Submission.Diff.lcOf (G t)
              (F ((Φ.τ (Fin.natAdd ord (0:Fin 2))).succ)) y (F 0 y)))
              (Φ.τ (Fin.castAdd 2 l)) := by
      funext l
      rw [update_natAdd_zero_cast Φ F' (fun y => Submission.Diff.lcOf (G t)
        (F ((Φ.τ (Fin.natAdd ord (0:Fin 2))).succ)) y (F 0 y)) l]
      rfl
    have hX : (fun y => (Submission.Diff.lcOf (G t)
            (F (O.OSub.derivτ Φ.τ (Fin.natAdd (ord+1) (0:Fin 2)))) y)
          (F (O.OSub.derivτ Φ.τ (Fin.castAdd 2 (0:Fin (ord+1)))) y))
        = (Function.update F' (Φ.τ (Fin.natAdd ord (0:Fin 2)))
            (fun y => Submission.Diff.lcOf (G t)
              (F ((Φ.τ (Fin.natAdd ord (0:Fin 2))).succ)) y (F 0 y)))
          (Φ.τ (Fin.natAdd ord (0:Fin 2))) := by
      rw [Function.update_self (Φ.τ (Fin.natAdd ord (0:Fin 2)))
        (fun y => Submission.Diff.lcOf (G t)
          (F ((Φ.τ (Fin.natAdd ord (0:Fin 2))).succ)) y (F 0 y)) F']
      rfl
    have hY : (F (O.OSub.derivτ Φ.τ (Fin.natAdd (ord+1) (1:Fin 2))))
        = (Function.update F' (Φ.τ (Fin.natAdd ord (0:Fin 2)))
            (fun y => Submission.Diff.lcOf (G t)
              (F ((Φ.τ (Fin.natAdd ord (0:Fin 2))).succ)) y (F 0 y)))
          (Φ.τ (Fin.natAdd ord (1:Fin 2))) := by
      rw [update_natAdd_zero_natAdd_one Φ F' (fun y => Submission.Diff.lcOf (G t)
        (F ((Φ.τ (Fin.natAdd ord (0:Fin 2))).succ)) y (F 0 y))]
      rfl
    rw [show O.atomEval G t Φ.τ (Function.update F' (Φ.τ (Fin.natAdd ord (0:Fin 2)))
          (fun y => Submission.Diff.lcOf (G t)
            (F ((Φ.τ (Fin.natAdd ord (0:Fin 2))).succ)) y (F 0 y)))
        = vtowerM (G t) (deltaBaseM G t) ord
            (fun l : Fin ord => (Function.update F' (Φ.τ (Fin.natAdd ord (0:Fin 2)))
              (fun y => Submission.Diff.lcOf (G t)
                (F ((Φ.τ (Fin.natAdd ord (0:Fin 2))).succ)) y (F 0 y))) (Φ.τ (Fin.castAdd 2 l)))
            ((Function.update F' (Φ.τ (Fin.natAdd ord (0:Fin 2)))
              (fun y => Submission.Diff.lcOf (G t)
                (F ((Φ.τ (Fin.natAdd ord (0:Fin 2))).succ)) y (F 0 y))) (Φ.τ (Fin.natAdd ord (0:Fin 2))))
            ((Function.update F' (Φ.τ (Fin.natAdd ord (0:Fin 2)))
              (fun y => Submission.Diff.lcOf (G t)
                (F ((Φ.τ (Fin.natAdd ord (0:Fin 2))).succ)) y (F 0 y))) (Φ.τ (Fin.natAdd ord (1:Fin 2))))
        from rfl]
    rw [← hT, ← hX, ← hY]
  -- the `Y`-slot term
  have hD : vtowerM (G t) (deltaBaseM G t) ord
        (fun i : Fin ord => F (O.OSub.derivτ Φ.τ (Fin.castAdd 2 i.succ)))
        (F (O.OSub.derivτ Φ.τ (Fin.natAdd (ord+1) (0:Fin 2))))
        (fun y => (Submission.Diff.lcOf (G t)
            (F (O.OSub.derivτ Φ.τ (Fin.natAdd (ord+1) (1:Fin 2)))) y)
          (F (O.OSub.derivτ Φ.τ (Fin.castAdd 2 (0:Fin (ord+1)))) y)) x
      = O.atomEval G t Φ.τ (Function.update F' (Φ.τ (Fin.natAdd ord (1:Fin 2)))
          (fun y => Submission.Diff.lcOf (G t)
            (F ((Φ.τ (Fin.natAdd ord (1:Fin 2))).succ)) y (F 0 y))) x := by
    have hT : (fun i : Fin ord => F (O.OSub.derivτ Φ.τ (Fin.castAdd 2 i.succ)))
        = fun l : Fin ord => (Function.update F' (Φ.τ (Fin.natAdd ord (1:Fin 2)))
            (fun y => Submission.Diff.lcOf (G t)
              (F ((Φ.τ (Fin.natAdd ord (1:Fin 2))).succ)) y (F 0 y)))
              (Φ.τ (Fin.castAdd 2 l)) := by
      funext l
      rw [update_natAdd_one_cast Φ F' (fun y => Submission.Diff.lcOf (G t)
        (F ((Φ.τ (Fin.natAdd ord (1:Fin 2))).succ)) y (F 0 y)) l]
      rfl
    have hX : (F (O.OSub.derivτ Φ.τ (Fin.natAdd (ord+1) (0:Fin 2))))
        = (Function.update F' (Φ.τ (Fin.natAdd ord (1:Fin 2)))
            (fun y => Submission.Diff.lcOf (G t)
              (F ((Φ.τ (Fin.natAdd ord (1:Fin 2))).succ)) y (F 0 y)))
          (Φ.τ (Fin.natAdd ord (0:Fin 2))) := by
      rw [update_natAdd_one_natAdd_zero Φ F' (fun y => Submission.Diff.lcOf (G t)
        (F ((Φ.τ (Fin.natAdd ord (1:Fin 2))).succ)) y (F 0 y))]
      rfl
    have hY : (fun y => (Submission.Diff.lcOf (G t)
            (F (O.OSub.derivτ Φ.τ (Fin.natAdd (ord+1) (1:Fin 2)))) y)
          (F (O.OSub.derivτ Φ.τ (Fin.castAdd 2 (0:Fin (ord+1)))) y))
        = (Function.update F' (Φ.τ (Fin.natAdd ord (1:Fin 2)))
            (fun y => Submission.Diff.lcOf (G t)
              (F ((Φ.τ (Fin.natAdd ord (1:Fin 2))).succ)) y (F 0 y)))
          (Φ.τ (Fin.natAdd ord (1:Fin 2))) := by
      rw [Function.update_self (Φ.τ (Fin.natAdd ord (1:Fin 2)))
        (fun y => Submission.Diff.lcOf (G t)
          (F ((Φ.τ (Fin.natAdd ord (1:Fin 2))).succ)) y (F 0 y)) F']
      rfl
    rw [show O.atomEval G t Φ.τ (Function.update F' (Φ.τ (Fin.natAdd ord (1:Fin 2)))
          (fun y => Submission.Diff.lcOf (G t)
            (F ((Φ.τ (Fin.natAdd ord (1:Fin 2))).succ)) y (F 0 y)))
        = vtowerM (G t) (deltaBaseM G t) ord
            (fun l : Fin ord => (Function.update F' (Φ.τ (Fin.natAdd ord (1:Fin 2)))
              (fun y => Submission.Diff.lcOf (G t)
                (F ((Φ.τ (Fin.natAdd ord (1:Fin 2))).succ)) y (F 0 y))) (Φ.τ (Fin.castAdd 2 l)))
            ((Function.update F' (Φ.τ (Fin.natAdd ord (1:Fin 2)))
              (fun y => Submission.Diff.lcOf (G t)
                (F ((Φ.τ (Fin.natAdd ord (1:Fin 2))).succ)) y (F 0 y))) (Φ.τ (Fin.natAdd ord (0:Fin 2))))
            ((Function.update F' (Φ.τ (Fin.natAdd ord (1:Fin 2)))
              (fun y => Submission.Diff.lcOf (G t)
                (F ((Φ.τ (Fin.natAdd ord (1:Fin 2))).succ)) y (F 0 y))) (Φ.τ (Fin.natAdd ord (1:Fin 2))))
        from rfl]
    rw [← hT, ← hX, ← hY]
  rw [hA, hB, hC, hD]
  abel

end Atom

/-! ## The target -/

theorem OSubChain
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) {a b ord : ℕ}
    (Φ : Work.Diff.EXT.ConnCov.RicFlip.O.OSub a b ord)
    (Θ : Work.Diff.EXT.ConnCov.AMB.Fam (I := I) (M := M) b)
    (hadd : Work.Diff.EXT.ConnCov.AMB.SlotAddP (I := I) (M := M) Θ)
    (F : Fin (a + 1) → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
    (hF : ∀ j, Work.Diff.EXT.ATower.SmE I M (F j))
    (hsmE : ∀ i : Fin b, Work.Diff.EXT.ATower.SmE I M
      (Work.Diff.EXT.ConnCov.RicFlip.O.OSub.eval G t Φ (fun j : Fin a => F j.succ) i))
    (x : M) :
    Work.Diff.EXT.ConnCov.AMB.pD (Submission.Diff.lcOf (G t))
        (fun F' => Θ (Work.Diff.EXT.ConnCov.RicFlip.O.OSub.eval G t Φ F')) F x
      = Work.Diff.EXT.ConnCov.AMB.pD (Submission.Diff.lcOf (G t)) Θ
          (Work.Diff.EXT.ConnCov.RicFlip.O.OSub.eval G t
            (Work.Diff.EXT.ConnCov.RicFlip.O.OSub.shift Φ) F) x
        + Θ (Work.Diff.EXT.ConnCov.RicFlip.O.OSub.eval G t
            (Work.Diff.EXT.ConnCov.RicFlip.O.OSub.deriv Φ) F) x := by
  rw [Work.Diff.EXT.ConnCov.AMB.pD, Work.Diff.EXT.ConnCov.AMB.pD,
    Work.Diff.EXT.ConnCov.RicFlip.O.OSub.eval_shift,
    Work.Diff.EXT.ConnCov.RicFlip.O.OSub.eval_deriv]
  set F' : Fin a → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M) :=
    fun j => F j.succ with hF'def
  set E : Fin b → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M) :=
    Work.Diff.EXT.ConnCov.RicFlip.O.OSub.eval G t Φ F' with hEdef
  simp only [Fin.cons_zero, Fin.cons_succ]
  have heta : (fun j : Fin b => E j) = E := rfl
  rw [heta]
  -- the smoothness of the connection difference (base of the tower)
  have hbase : ∀ (w : Fin 0 → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
      (X Y : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)),
      Work.Diff.EXT.ATower.SmE I M X → Work.Diff.EXT.ATower.SmE I M Y →
      Work.Diff.EXT.ATower.SmE I M (deltaBaseM G t w X Y) := by
    intro w X Y hX hY
    show Work.Diff.EXT.ATower.SmE I M (Work.Diff.EXT.ConnCov.covDiff G t X Y)
    have h1 := lcOf_apply_smE hLC (G t) X Y hX hY
    have h2 := lcOf_apply_smE hLC (G 0) X Y hX hY
    have hfun : Work.Diff.EXT.ConnCov.covDiff G t X Y
        = (fun y : M => (lcOf (G t)) X y (Y y)) - (fun y : M => (lcOf (G 0)) X y (Y y)) :=
      rfl
    rw [hfun]
    exact h1.sub_section h2
  have hF'_smE : ∀ j : Fin a, Work.Diff.EXT.ATower.SmE I M (F' j) := fun j => hF j.succ
  -- smoothness of the atom and of the updated atoms
  have hA_smE : Work.Diff.EXT.ATower.SmE I M
      (Work.Diff.EXT.ConnCov.RicFlip.O.atomEval G t
        (Work.Diff.EXT.ConnCov.RicFlip.O.OSub.derivτ Φ.τ) F) :=
    smE_vtowerM (I := I) (M := M) hLC (G t) (deltaBaseM G t) hbase (ord+1)
      (fun i : Fin (ord+1) => F (Work.Diff.EXT.ConnCov.RicFlip.O.OSub.derivτ Φ.τ (Fin.castAdd 2 i)))
      (F (Work.Diff.EXT.ConnCov.RicFlip.O.OSub.derivτ Φ.τ (Fin.natAdd (ord+1) (0:Fin 2))))
      (F (Work.Diff.EXT.ConnCov.RicFlip.O.OSub.derivτ Φ.τ (Fin.natAdd (ord+1) (1:Fin 2))))
      (fun i => hF _) (hF _) (hF _)
  have hSl_smE : ∀ l : Fin (ord+2), Work.Diff.EXT.ATower.SmE I M
      (Work.Diff.EXT.ConnCov.RicFlip.O.atomEval G t Φ.τ
        (Function.update F' (Φ.τ l)
          (fun y => Submission.Diff.lcOf (G t) (F (Φ.τ l).succ) y (F 0 y)))) := by
    intro l
    have hW : Work.Diff.EXT.ATower.SmE I M
        (fun y => Submission.Diff.lcOf (G t) (F (Φ.τ l).succ) y (F 0 y)) :=
      lcOf_apply_smE hLC (G t) (F (Φ.τ l).succ) (F 0) (hF _) (hF 0)
    have hupd := smE_updateM (v := F') (Φ.τ l) hF'_smE hW
    exact smE_vtowerM (I := I) (M := M) hLC (G t) (deltaBaseM G t) hbase ord
      (fun i : Fin ord => (Function.update F' (Φ.τ l)
        (fun y => Submission.Diff.lcOf (G t) (F (Φ.τ l).succ) y (F 0 y))) (Φ.τ (Fin.castAdd 2 i)))
      ((Function.update F' (Φ.τ l)
        (fun y => Submission.Diff.lcOf (G t) (F (Φ.τ l).succ) y (F 0 y))) (Φ.τ (Fin.natAdd ord (0:Fin 2))))
      ((Function.update F' (Φ.τ l)
        (fun y => Submission.Diff.lcOf (G t) (F (Φ.τ l).succ) y (F 0 y))) (Φ.τ (Fin.natAdd ord (1:Fin 2))))
      (fun i => hupd _) (hupd _) (hupd _)
  have hsum_smE : Work.Diff.EXT.ATower.SmE I M
      (∑ l : Fin (ord+2), Work.Diff.EXT.ConnCov.RicFlip.O.atomEval G t Φ.τ
        (Function.update F' (Φ.τ l)
          (fun y => Submission.Diff.lcOf (G t) (F (Φ.τ l).succ) y (F 0 y)))) :=
    smE_finset_sum Finset.univ _ hSl_smE
  -- the atom Leibniz rule, at the level of functions
  have hVidx : (fun y => Submission.Diff.lcOf (G t) (E Φ.idx) y (F 0 y))
      = Work.Diff.EXT.ConnCov.RicFlip.O.atomEval G t
            (Work.Diff.EXT.ConnCov.RicFlip.O.OSub.derivτ Φ.τ) F
        + ∑ l : Fin (ord+2), Work.Diff.EXT.ConnCov.RicFlip.O.atomEval G t Φ.τ
            (Function.update F' (Φ.τ l)
              (fun y => Submission.Diff.lcOf (G t) (F (Φ.τ l).succ) y (F 0 y))) := by
    funext y
    have hAtom := congrFun (atomEvalDeriv_local (Φ := Φ) (G := G) (t := t) (F := F)) y
    have hsum_eq : (∑ l : Fin (ord+2), Work.Diff.EXT.ConnCov.RicFlip.O.atomEval G t Φ.τ
          (Function.update (fun j : Fin a => F j.succ) (Φ.τ l)
            (fun y => Submission.Diff.lcOf (G t) (F (Φ.τ l).succ) y (F 0 y))) y)
        = (∑ l : Fin (ord+2), Work.Diff.EXT.ConnCov.RicFlip.O.atomEval G t Φ.τ
          (Function.update F' (Φ.τ l)
            (fun y => Submission.Diff.lcOf (G t) (F (Φ.τ l).succ) y (F 0 y))) y) := by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [hF'def]
    rw [hsum_eq] at hAtom
    have hEidx : E Φ.idx = Work.Diff.EXT.ConnCov.RicFlip.O.atomEval G t Φ.τ
        (fun j : Fin a => F j.succ) := by
      rw [hEdef, Work.Diff.EXT.ConnCov.RicFlip.O.OSub.eval_atom, hF'def]
    rw [hEidx]
    simp only [Finset.sum_apply, Pi.add_apply]
    rw [hAtom]
    abel
  have hcore :
      (∑ i : Fin b, Θ (Function.update E i
          (fun y => Submission.Diff.lcOf (G t) (E i) y (F 0 y))) x)
      - (∑ j : Fin a, Θ (Work.Diff.EXT.ConnCov.RicFlip.O.OSub.eval G t Φ
          (Function.update F' j
            (fun y => Submission.Diff.lcOf (G t) (F j.succ) y (F 0 y)))) x)
      = Θ (Function.update E Φ.idx (Work.Diff.EXT.ConnCov.RicFlip.O.atomEval G t
          (Work.Diff.EXT.ConnCov.RicFlip.O.OSub.derivτ Φ.τ) F)) x := by
    rw [sum_fin_eq_add_subtype Φ.idx (fun i : Fin b => Θ (Function.update E i
      (fun y => Submission.Diff.lcOf (G t) (E i) y (F 0 y))) x)]
    rw [Work.Diff.EXT.ConnCov.RicFlip.O.OSub.sum_reindex Φ (fun s : Fin a =>
      Θ (Work.Diff.EXT.ConnCov.RicFlip.O.OSub.eval G t Φ
        (Function.update F' s
          (fun y => Submission.Diff.lcOf (G t) (F s.succ) y (F 0 y)))) x)]
    -- the non-atom slots cancel
    have hsig : (∑ i : {i : Fin b // i ≠ Φ.idx}, Θ (Function.update E i.1
          (fun y => Submission.Diff.lcOf (G t) (E i.1) y (F 0 y))) x)
        = (∑ i : {i : Fin b // i ≠ Φ.idx}, Θ (Work.Diff.EXT.ConnCov.RicFlip.O.OSub.eval G t Φ
            (Function.update F' (Φ.σ i.1)
              (fun y => Submission.Diff.lcOf (G t) (F (Φ.σ i.1).succ) y (F 0 y)))) x) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hW : (fun y => Submission.Diff.lcOf (G t) (E i.1) y (F 0 y))
          = (fun y => Submission.Diff.lcOf (G t) (F (Φ.σ i.1).succ) y (F 0 y)) := by
        have hEsl : E i.1 = F' (Φ.σ i.1) := by
          rw [hEdef]
          exact Work.Diff.EXT.ConnCov.RicFlip.O.OSub.eval_slot Φ F' i.2
        rw [hEsl]
      rw [hW]
      rw [hEdef, ← Work.Diff.EXT.ConnCov.RicFlip.O.OSub.eval_update_slot
        (G := G) (t := t) Φ F' i.1 i.2
        (fun y => Submission.Diff.lcOf (G t) (F (Φ.σ i.1).succ) y (F 0 y))]
    -- the atom slot: the `τ`-sum is the sum of the atom-slot updates
    have htau : (∑ l : Fin (ord+2), Θ (Work.Diff.EXT.ConnCov.RicFlip.O.OSub.eval G t Φ
          (Function.update F' (Φ.τ l)
            (fun y => Submission.Diff.lcOf (G t) (F (Φ.τ l).succ) y (F 0 y)))) x)
        = (∑ l : Fin (ord+2), Θ (Function.update E Φ.idx
            (Work.Diff.EXT.ConnCov.RicFlip.O.atomEval G t Φ.τ
              (Function.update F' (Φ.τ l)
                (fun y => Submission.Diff.lcOf (G t) (F (Φ.τ l).succ) y (F 0 y))))) x) := by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Work.Diff.EXT.ConnCov.RicFlip.O.OSub.eval_update_atom (G := G) (t := t) Φ F' l
        (fun y => Submission.Diff.lcOf (G t) (F (Φ.τ l).succ) y (F 0 y)), ← hEdef]
    rw [hsig, htau]
    -- the atom-slot identity
    have hAid : Θ (Function.update E Φ.idx
          (fun y => Submission.Diff.lcOf (G t) (E Φ.idx) y (F 0 y))) x
        = Θ (Function.update E Φ.idx (Work.Diff.EXT.ConnCov.RicFlip.O.atomEval G t
              (Work.Diff.EXT.ConnCov.RicFlip.O.OSub.derivτ Φ.τ) F)) x
          + ∑ l : Fin (ord+2), Θ (Function.update E Φ.idx
              (Work.Diff.EXT.ConnCov.RicFlip.O.atomEval G t Φ.τ
                (Function.update F' (Φ.τ l)
                  (fun y => Submission.Diff.lcOf (G t) (F (Φ.τ l).succ) y (F 0 y))))) x := by
      rw [hVidx,
        hadd Φ.idx E (Work.Diff.EXT.ConnCov.RicFlip.O.atomEval G t
            (Work.Diff.EXT.ConnCov.RicFlip.O.OSub.derivτ Φ.τ) F)
          (∑ l : Fin (ord+2), Work.Diff.EXT.ConnCov.RicFlip.O.atomEval G t Φ.τ
            (Function.update F' (Φ.τ l)
              (fun y => Submission.Diff.lcOf (G t) (F (Φ.τ l).succ) y (F 0 y))))
          hsmE hA_smE hsum_smE x,
        SlotAddPSum hadd Finset.univ Φ.idx E
          (fun l : Fin (ord+2) => Work.Diff.EXT.ConnCov.RicFlip.O.atomEval G t Φ.τ
            (Function.update F' (Φ.τ l)
              (fun y => Submission.Diff.lcOf (G t) (F (Φ.τ l).succ) y (F 0 y))))
          hsmE hSl_smE x]
    rw [hAid]
    ring
  rw [← hcore]
  ring

end Work.Diff.EXT.ConnCov.RicFlip
