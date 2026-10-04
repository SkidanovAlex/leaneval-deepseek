import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicFlip.OSubKit
import Submission.Work.Diff.EXT.ConnCov.pack_bridge
import Submission.Work.Diff.EXT.ConnCov.RicFlip.towerEqLoweringDeltaTowerM

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The *slot-exempting* insertion of the connection difference

For the flip of the fixed/moving towers of `baseRic` the third value slot of the base is a *dummy*
slot: `baseRic g v A B C = Ric(A,B)` does not depend on `C`.  Consequently the tower
`tower (lcOf g) (baseRic g) k` is **not additive in that slot** (it is *constant* there), so the
full insertion `AMB.Ins` — whose defining sum runs over *all* slots — cannot be used in the flip
identity: the flip only inserts into the slots in which the object is additive, and the correction
of the exempted slot cancels between the two connections because the object ignores it.

This module provides the slot-exempting insertion `InsExc c`, its decomposition into the
one-atom substitutions `insSub j` (so that the substitution calculus of
`Submission.Work.Diff.EXT.ConnCov.RicFlip.OSubKit` applies), and the two invariants of an object
which the flip uses:

* `AddExcept c τ` — `τ` is additive (on smooth fields) in every slot except `c`;
* `ConstIn c τ` — `τ` does not depend on the field in slot `c`.

The main result is the **flip identity**

`AMB.pD (lcOf (G 0)) τ = AMB.pD (lcOf (G t)) τ + InsExc c (covDiff G t) τ`

for `τ` satisfying `AddExcept c` and `ConstIn c`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.ConnCov.RicFlip

open Work.Diff.EXT.ConnCov.AMB

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-! ## The two invariants -/

/-- `AddExcept c τ` says that `τ` is additive in every slot except `c`, on smooth fields. -/
def AddExcept {N : ℕ} (c : Fin N) (τ : Fam (I := I) (M := M) N) : Prop :=
  ∀ (j : Fin N), j ≠ c → ∀ (H : Fin N → TF (I := I) (M := M)) (W W' : TF (I := I) (M := M)),
    (∀ i, Work.Diff.EXT.ATower.SmE I M (H i)) → Work.Diff.EXT.ATower.SmE I M W →
    Work.Diff.EXT.ATower.SmE I M W' → ∀ x,
    τ (Function.update H j (W + W')) x = τ (Function.update H j W) x + τ (Function.update H j W') x

/-- `ConstIn c τ` says that `τ` does not depend on the field in slot `c`. -/
def ConstIn {N : ℕ} (c : Fin N) (τ : Fam (I := I) (M := M) N) : Prop :=
  ∀ (H H' : Fin N → TF (I := I) (M := M)), (∀ i, i ≠ c → H i = H' i) → ∀ x, τ H x = τ H' x

/-- The subtraction rule which follows from `AddExcept` at a single slot. -/
theorem AddExcept.sub {N : ℕ} {c : Fin N} {τ : Fam (I := I) (M := M) N} (h : AddExcept c τ)
    {j : Fin N} (hj : j ≠ c) (H : Fin N → TF (I := I) (M := M)) (W W' : TF (I := I) (M := M))
    (hH : ∀ i, Work.Diff.EXT.ATower.SmE I M (H i)) (hW : Work.Diff.EXT.ATower.SmE I M W)
    (hW' : Work.Diff.EXT.ATower.SmE I M W') (hsub : Work.Diff.EXT.ATower.SmE I M (W - W'))
    (x : M) :
    τ (Function.update H j (W - W')) x = τ (Function.update H j W) x - τ (Function.update H j W') x := by
  have h1 := h j hj H W' (W - W') hH hW' hsub x
  have hfe : W' + (W - W') = W := by funext y; simp only [Pi.add_apply, Pi.sub_apply]; abel
  rw [hfe] at h1
  linarith

/-- The `Function.update` form of `ConstIn`. -/
theorem ConstIn.update {N : ℕ} {c : Fin N} {τ : Fam (I := I) (M := M) N} (h : ConstIn c τ)
    (H : Fin N → TF (I := I) (M := M)) (W W' : TF (I := I) (M := M)) (x : M) :
    τ (Function.update H c W) x = τ (Function.update H c W') x := by
  refine h _ _ (fun i hi => ?_) x
  rw [Function.update_of_ne hi, Function.update_of_ne hi]

/-! ## The insertion substitution -/

/-- `Fin.cases` at the value `1` of `Fin 2`. -/
@[simp] theorem fin_cases_one {α : Type*} (a : α) (f : Fin 1 → α) :
    Fin.cases a f (1 : Fin 2) = f 0 := by
  rw [show (1 : Fin 2) = (0 : Fin 1).succ from Fin.ext rfl]
  rfl

/-- **The one-slot insertion substitution.**  `insSub N j : OSub (N+1) N 0` reads the input tuple
`F : Fin (N+1) → TF` and returns the `N`-tuple whose `j`-th entry is the connection difference
`δ(F (j+1), F 0)` and whose other entries are the projections `F (i+1)`.  It is the substitution
singled out by the `j`-th term of the insertion sum. -/
noncomputable def insSub (N : ℕ) (j : Fin N) : O.OSub (N + 1) N 0 where
  idx := j
  τ := Fin.cases j.succ (fun _ : Fin 1 => 0)
  σ := fun i => i.succ
  bij := by
    have hinj : Function.Injective
        (Sum.elim (Fin.cases (j.succ : Fin (N+1)) (fun _ : Fin 1 => 0))
          (fun i : {i : Fin N // i ≠ j} => i.1.succ)) := by
      intro x y h
      rcases x with a | i <;> rcases y with b | i'
      · rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a', rfl⟩ <;>
        rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b', rfl⟩ <;>
        simp only [Sum.elim_inl, Fin.cases_zero, Fin.cases_succ] at h
        · rfl
        · exact absurd h (Fin.succ_ne_zero j)
        · exact absurd h.symm (Fin.succ_ne_zero j)
        · rw [Subsingleton.elim a' b']
      · rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a', rfl⟩ <;>
        simp only [Sum.elim_inl, Sum.elim_inr, Fin.cases_zero, Fin.cases_succ] at h
        · exact absurd (Fin.succ_injective N h) (fun hh => i'.2 hh.symm)
        · exact absurd h.symm (Fin.succ_ne_zero i'.1)
      · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b', rfl⟩ <;>
        simp only [Sum.elim_inl, Sum.elim_inr, Fin.cases_zero, Fin.cases_succ] at h
        · exact absurd (Fin.succ_injective N h) i.2
        · exact absurd h (Fin.succ_ne_zero i.1)
      · exact congrArg Sum.inr (Subtype.ext (Fin.succ_injective N h))
    refine ⟨hinj, ?_⟩
    intro m
    rcases Fin.eq_zero_or_eq_succ m with rfl | ⟨m', rfl⟩
    · exact ⟨Sum.inl 1, by simp⟩
    · by_cases hj : m' = j
      · subst hj
        exact ⟨Sum.inl 0, by simp⟩
      · exact ⟨Sum.inr ⟨m', hj⟩, by simp⟩

@[simp] theorem insSub_idx (N : ℕ) (j : Fin N) : (insSub N j).idx = j := rfl

@[simp] theorem insSub_τ_zero (N : ℕ) (j : Fin N) : (insSub N j).τ 0 = j.succ := rfl

theorem insSub_τ_one (N : ℕ) (j : Fin N) : (insSub N j).τ 1 = 0 := by
  rw [show (1 : Fin 2) = (0 : Fin 1).succ from Fin.ext rfl]
  rfl

@[simp] theorem fin_natAdd_zero_zero : (Fin.natAdd 0 (0 : Fin 2) : Fin (0 + 2)) = 0 := Fin.ext rfl

@[simp] theorem fin_natAdd_zero_one : (Fin.natAdd 0 (1 : Fin 2) : Fin (0 + 2)) = 1 := Fin.ext rfl

/-- The atom of the insertion substitution is the connection difference. -/
theorem insSub_atomEval (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (N : ℕ) (j : Fin N)
    (F : Fin (N + 1) → TF (I := I) (M := M)) :
    O.atomEval G t (insSub N j).τ F = fun y => covDiff G t (F j.succ) (F 0) y := by
  funext y
  simp only [O.atomEval, fin_natAdd_zero_zero, fin_natAdd_zero_one, insSub_τ_zero, insSub_τ_one,
    vtowerM, deltaBaseM]

@[simp] theorem insSub_σ (N : ℕ) (j : Fin N) (i : Fin N) : (insSub N j).σ i = i.succ := rfl

/-- The evaluation of the insertion substitution: it replaces the `j`-th entry of `F ∘ succ` by
the connection difference of the `j`-th entry with the direction `F 0`. -/
theorem insSub_eval (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (N : ℕ) (j : Fin N)
    (F : Fin (N + 1) → TF (I := I) (M := M)) :
    (insSub N j).eval G t F
      = Function.update (fun i : Fin N => F i.succ) j (fun y => covDiff G t (F j.succ) (F 0) y) := by
  funext i
  by_cases hi : i = j
  · rw [hi]
    rw [show (insSub N j).eval G t F j = O.atomEval G t (insSub N j).τ F from
      O.OSub.eval_atom (Φ := insSub N j) F]
    rw [insSub_atomEval, Function.update_self]
  · rw [show (insSub N j).eval G t F i = F ((insSub N j).σ i) from
      O.OSub.eval_slot (Φ := insSub N j) F hi]
    rw [insSub_σ, Function.update_of_ne hi]

/-! ## The slot-exempting insertion -/

/-- **The insertion into every slot except `c`.**  It is the sum of the one-atom substitutions
`insSub j` over the slots `j ≠ c`. -/
noncomputable def InsExc (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) {N : ℕ} (c : Fin N)
    (τ : Fam (I := I) (M := M) N) : Fam (I := I) (M := M) (N + 1) :=
  fun F x => ∑ j ∈ Finset.univ.erase c, τ ((insSub N j).eval G t F) x

theorem InsExc_apply (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) {N : ℕ} (c : Fin N)
    (τ : Fam (I := I) (M := M) N) (F : Fin (N + 1) → TF (I := I) (M := M)) (x : M) :
    InsExc G t c τ F x = ∑ j ∈ Finset.univ.erase c, τ ((insSub N j).eval G t F) x := rfl

/-- The insertion, unfolded on a tuple. -/
theorem InsExc_eq_sum (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) {N : ℕ} (c : Fin N)
    (τ : Fam (I := I) (M := M) N) (F : Fin (N + 1) → TF (I := I) (M := M)) (x : M) :
    InsExc G t c τ F x = ∑ j ∈ Finset.univ.erase c,
      τ (Function.update (fun i : Fin N => F i.succ) j
        (fun y => covDiff G t (F j.succ) (F 0) y)) x := by
  rw [InsExc_apply]
  exact Finset.sum_congr rfl (fun j _ => by rw [insSub_eval])

/-! ## The flip identity -/

/-- **The flip identity for a slot-exempting insertion.**  If `τ` is additive in every slot except
`c` and does not depend on the field in slot `c`, then one packed recursion step with the fixed
connection `∇^{G 0}` differs from one packed recursion step with the moving connection `∇^{G t}` by
exactly the insertion of the connection difference into all slots except `c`. -/
theorem pD_flip_NoC (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M)
    (t : ℝ) {N : ℕ} {c : Fin N} {τ : Fam (I := I) (M := M) N}
    (hadd : AddExcept c τ) (hconst : ConstIn c τ)
    (F : Fin (N + 1) → TF (I := I) (M := M))
    (hF : ∀ i, Work.Diff.EXT.ATower.SmE I M (F i)) :
    AMB.pD (Submission.Diff.lcOf (G 0)) τ F
      = AMB.pD (Submission.Diff.lcOf (G t)) τ F + InsExc G t c τ F := by
  have hlc : ∀ (g : SMet I M) (Y Z : TF (I := I) (M := M)), Work.Diff.EXT.ATower.SmE I M Y →
      Work.Diff.EXT.ATower.SmE I M Z → Work.Diff.EXT.ATower.SmE I M (fun y => lcOf g Y y (Z y)) :=
    fun g Y Z hY hZ => Work.Diff.EXT.ATower.lcOf_apply_smE hLC g Y Z hY hZ
  have hδsm : ∀ (Y Z : TF (I := I) (M := M)), Work.Diff.EXT.ATower.SmE I M Y →
      Work.Diff.EXT.ATower.SmE I M Z → Work.Diff.EXT.ATower.SmE I M (fun y => covDiff G t Y Z y) :=
    fun Y Z hY hZ => (hlc (G t) Y Z hY hZ).sub_section (hlc (G 0) Y Z hY hZ)
  have hstep : ∀ (g : SMet I M), AMB.pD (lcOf g) τ F
      = fun x => mvfderiv I (τ (fun i : Fin N => F i.succ)) x (F 0 x)
          - ∑ i : Fin N, τ (Function.update (fun j : Fin N => F j.succ) i
              (fun y => lcOf g (F i.succ) y (F 0 y))) x := fun g => rfl
  have hsplit : ∀ i : Fin N, i ≠ c → ∀ x : M,
      τ (Function.update (fun j : Fin N => F j.succ) i
          (fun y => lcOf (G t) (F i.succ) y (F 0 y))) x
        = τ (Function.update (fun j : Fin N => F j.succ) i
            (fun y => lcOf (G 0) (F i.succ) y (F 0 y))) x
          + τ (Function.update (fun j : Fin N => F j.succ) i
            (fun y => covDiff G t (F i.succ) (F 0) y)) x := by
    intro i hi x
    have hfield : (fun y : M => lcOf (G t) (F i.succ) y (F 0 y))
        = (fun y : M => lcOf (G 0) (F i.succ) y (F 0 y))
          + (fun y : M => covDiff G t (F i.succ) (F 0) y) := by
      funext y
      simp only [covDiff, Pi.add_apply, Pi.sub_apply]
      abel
    rw [hfield]
    exact hadd i hi (fun k : Fin N => F k.succ)
      (fun y => lcOf (G 0) (F i.succ) y (F 0 y))
      (fun y => covDiff G t (F i.succ) (F 0) y) (fun k => hF _)
      (hlc (G 0) _ _ (hF _) (hF 0)) (hδsm _ _ (hF _) (hF 0)) x
  have hsum : ∀ x : M, (∑ i : Fin N, τ (Function.update (fun j : Fin N => F j.succ) i
        (fun y => lcOf (G t) (F i.succ) y (F 0 y))) x)
      = (∑ i : Fin N, τ (Function.update (fun j : Fin N => F j.succ) i
            (fun y => lcOf (G 0) (F i.succ) y (F 0 y))) x)
        + (∑ i ∈ Finset.univ.erase c, τ (Function.update (fun j : Fin N => F j.succ) i
            (fun y => covDiff G t (F i.succ) (F 0) y)) x) := by
    intro x
    have hA : (∑ i : Fin N, τ (Function.update (fun j : Fin N => F j.succ) i
          (fun y => lcOf (G t) (F i.succ) y (F 0 y))) x)
        = (∑ i ∈ Finset.univ.erase c, τ (Function.update (fun j : Fin N => F j.succ) i
              (fun y => lcOf (G t) (F i.succ) y (F 0 y))) x)
          + τ (Function.update (fun j : Fin N => F j.succ) c
              (fun y => lcOf (G t) (F c.succ) y (F 0 y))) x :=
      (Finset.sum_erase_add _ _ (Finset.mem_univ c)).symm
    have hB : (∑ i ∈ Finset.univ.erase c, τ (Function.update (fun j : Fin N => F j.succ) i
              (fun y => lcOf (G t) (F i.succ) y (F 0 y))) x)
        = (∑ i ∈ Finset.univ.erase c, τ (Function.update (fun j : Fin N => F j.succ) i
              (fun y => lcOf (G 0) (F i.succ) y (F 0 y))) x)
          + (∑ i ∈ Finset.univ.erase c, τ (Function.update (fun j : Fin N => F j.succ) i
              (fun y => covDiff G t (F i.succ) (F 0) y)) x) := by
      rw [Finset.sum_congr rfl (fun i hi => hsplit i (Finset.mem_erase.mp hi).1 x),
        Finset.sum_add_distrib]
    have hC : (∑ i : Fin N, τ (Function.update (fun j : Fin N => F j.succ) i
              (fun y => lcOf (G 0) (F i.succ) y (F 0 y))) x)
        = (∑ i ∈ Finset.univ.erase c, τ (Function.update (fun j : Fin N => F j.succ) i
              (fun y => lcOf (G 0) (F i.succ) y (F 0 y))) x)
          + τ (Function.update (fun j : Fin N => F j.succ) c
              (fun y => lcOf (G 0) (F c.succ) y (F 0 y))) x :=
      (Finset.sum_erase_add _ _ (Finset.mem_univ c)).symm
    have hD : τ (Function.update (fun j : Fin N => F j.succ) c
          (fun y => lcOf (G t) (F c.succ) y (F 0 y))) x
        = τ (Function.update (fun j : Fin N => F j.succ) c
          (fun y => lcOf (G 0) (F c.succ) y (F 0 y))) x := ConstIn.update hconst _ _ _ x
    linarith
  rw [hstep (G 0), hstep (G t)]
  funext x
  simp only [Pi.add_apply]
  rw [hsum x, InsExc_eq_sum]
  ring

end Work.Diff.EXT.ConnCov.RicFlip
