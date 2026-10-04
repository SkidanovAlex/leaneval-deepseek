import Mathlib
import Submission.Work.Diff.EXT.ATower.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Packed form of the connection-difference tower, and the three induction invariants

`Work.Diff.EXT.ATower.tower cov base k` is the `k`-th iterated covariant derivative of `base` with
connection `cov`; it has `k` derivative slots (a `Fin k`-tuple of tangent fields) and three value
slots `A B C`.

This module packs the `k + 3` slots into a *single* `Fin (k + 3)`-tuple, which makes the recursion
uniform in the slot index:

* `tvdStepP g τ F` is one recursion step in packed coordinates: the covariant derivative of `τ`
  along the *first* slot of `F` (which is therefore the differentiation direction), with the
  connection correction inserted in each of the remaining `k + 3` slots;
* `tvdP g base k` is the packed tower, defined by its own recursion
  `tvdP g base (k+1) F = tvdStepP g (tvdP g base k) F` (definitional);
* `tvdTp g base k F` is the *same* object read off from the frozen `tower` (the link
  `tvdP = tvdTp` is proved in `tower_value_dep.lean`); using `tvdP` as the primary object keeps
  the induction free of index arithmetic;
* the three induction invariants `tvdSmT`, `tvdLinT`, `tvdGermT`:
  * `tvdSmT g base k`: `tvdP g base k F` is `C^∞` for tuples of `C^∞` fields;
  * `tvdLinT g base k`: `tvdP g base k` is `C^∞`-linear in each slot, in the finite-sum form
    "if the slot field is pointwise `∑ q, f q • X q` then the value is `∑ q, f q • _`";
  * `tvdGermT g base k`: the value at `x` depends only on the germs of the slot fields at `x`.

The small toolkit at the end (`tvd_mvfderiv_*`, `tvd_cov_*`) collects the Leibniz rules for
`mvfderiv` and for an arbitrary `CovariantDerivative` in the applied form used by the inductions.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.ATower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## The packed recursion -/

/-- **One recursion step in packed coordinates.**  The tuple `F : Fin (k+4) → TF` has the
differentiation direction in slot `0` and the `k+3` slots of `τ` in the slots `Fin.succ j`. -/
noncomputable def tvdStepP (g : SMet I M) {k : ℕ}
    (τ : (Fin (k + 3) → TF (I := I) (M := M)) → M → ℝ)
    (F : Fin (k + 4) → TF (I := I) (M := M)) : M → ℝ :=
  fun x => mvfderiv I (τ (fun j : Fin (k + 3) => F (Fin.succ j))) x (F 0 x)
    - ∑ j : Fin (k + 3), τ (Function.update (fun j' : Fin (k + 3) => F (Fin.succ j')) j
        (fun y : M => lcOf g (F (Fin.succ j)) y (F 0 y))) x

/-- **The packed tower**: `k + 3` slots packed into one `Fin (k+3)`-tuple. -/
noncomputable def tvdP (g : SMet I M) (base : Op3 (I := I) (M := M) 0) :
    ∀ k : ℕ, (Fin (k + 3) → TF (I := I) (M := M)) → M → ℝ
  | 0, F =>
      base (fun i : Fin 0 => i.elim0) (F (Fin.natAdd 0 0)) (F (Fin.natAdd 0 1))
        (F (Fin.natAdd 0 2))
  | k + 1, F => tvdStepP g (tvdP g base k) F

/-- The defining recursion of the packed tower. -/
theorem tvdP_succ (g : SMet I M) (base : Op3 (I := I) (M := M) 0) (k : ℕ)
    (F : Fin (k + 4) → TF (I := I) (M := M)) :
    tvdP g base (k + 1) F = tvdStepP g (tvdP g base k) F := rfl

/-- The packed tower read off from the frozen `tower` (the link between the two is proved in
`tower_value_dep.lean`). -/
noncomputable def tvdTp (g : SMet I M) (base : Op3 (I := I) (M := M) 0) (k : ℕ)
    (F : Fin (k + 3) → TF (I := I) (M := M)) : M → ℝ :=
  tower (lcOf g) base k (fun j : Fin k => F (Fin.castAdd 3 j))
    (F (Fin.natAdd k 0)) (F (Fin.natAdd k 1)) (F (Fin.natAdd k 2))

/-! ## The three induction invariants -/

/-- **Smoothness** of the packed tower on tuples of smooth fields. -/
def tvdSmT (g : SMet I M) (base : Op3 (I := I) (M := M) 0) (k : ℕ) : Prop :=
  ∀ F : Fin (k + 3) → TF (I := I) (M := M), (∀ j, SmE I M (F j)) → SmF I M (tvdP g base k F)

/-- **Slotwise `C^∞`-linearity** of the packed tower, in the finite-sum form: if the slot field `S`
is pointwise `∑ q, f q • X q` then the value of the tower is the corresponding combination. -/
def tvdLinT (g : SMet I M) (base : Op3 (I := I) (M := M) 0) (k : ℕ) : Prop :=
  ∀ (F : Fin (k + 3) → TF (I := I) (M := M)) (j : Fin (k + 3)) (ι : Type) [Fintype ι]
    (X : ι → TF (I := I) (M := M)) (f : ι → M → ℝ) (S : TF (I := I) (M := M)),
    (∀ i, SmE I M (F i)) → (∀ q, SmE I M (X q)) → (∀ q, SmF I M (f q)) → SmE I M S →
    (∀ y, S y = ∑ q, f q y • X q y) →
    ∀ y, tvdP g base k (Function.update F j S) y
      = ∑ q, f q y * tvdP g base k (Function.update F j (X q)) y

/-- **Germ-locality** of the packed tower: the value at `x` depends only on the germs of the slots
at `x` (no smoothness hypothesis is needed). -/
def tvdGermT (g : SMet I M) (base : Op3 (I := I) (M := M) 0) (k : ℕ) : Prop :=
  ∀ (F F' : Fin (k + 3) → TF (I := I) (M := M)) (x : M), (∀ j, F j =ᶠ[𝓝 x] F' j) →
    tvdP g base k F x = tvdP g base k F' x

/-- **Germ-locality of the packed tower on smooth tuples**: this is the form which is
*derivable* from the hypotheses on `base` (the `k = 0` case needs only that `base` is
value-dependent and smooth on smooth fields), and the form in which germ-locality is used by the
frame argument in `value_dep_of_germs_lin`. -/
def tvdGermTs (g : SMet I M) (base : Op3 (I := I) (M := M) 0) (k : ℕ) : Prop :=
  ∀ (F F' : Fin (k + 3) → TF (I := I) (M := M)) (x : M),
    (∀ j, SmE I M (F j)) → (∀ j, SmE I M (F' j)) → (∀ j, F j =ᶠ[𝓝 x] F' j) →
    tvdP g base k F x = tvdP g base k F' x

/-! ## Packing and unpacking of the slots

`tvdPack v A B C` packs a `Fin m`-tuple of fields and the three value slots into a single
`Fin (m+3)`-tuple.  These bookkeeping lemmas are what relates the packed recursion `tvdP` to the
frozen (unpacked) `tower`. -/

noncomputable def tvdPack {m : ℕ} (v : Fin m → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)) :
    Fin (m + 3) → TF (I := I) (M := M) :=
  Fin.addCases (motive := fun _ => TF (I := I) (M := M)) v ![A, B, C]

@[simp] lemma tvdPack_castAdd {m : ℕ} (v : Fin m → TF (I := I) (M := M))
    (A B C : TF (I := I) (M := M)) (i : Fin m) :
    tvdPack v A B C (Fin.castAdd 3 i) = v i :=
  Fin.addCases_left (motive := fun _ => TF (I := I) (M := M)) i

@[simp] lemma tvdPack_natAdd {m : ℕ} (v : Fin m → TF (I := I) (M := M))
    (A B C : TF (I := I) (M := M)) (j : Fin 3) :
    tvdPack v A B C (Fin.natAdd m j) = ![A, B, C] j :=
  Fin.addCases_right (motive := fun _ => TF (I := I) (M := M)) j

/-- Every tuple is the packing of its own slots. -/
lemma tvdPack_unpack {m : ℕ} (F : Fin (m + 3) → TF (I := I) (M := M)) :
    F = tvdPack (fun j : Fin m => F (Fin.castAdd 3 j)) (F (Fin.natAdd m (0 : Fin 3)))
      (F (Fin.natAdd m (1 : Fin 3))) (F (Fin.natAdd m (2 : Fin 3))) := by
  funext j
  refine Fin.addCases (motive := fun j => F j = tvdPack
      (fun j : Fin m => F (Fin.castAdd 3 j)) (F (Fin.natAdd m (0 : Fin 3)))
      (F (Fin.natAdd m (1 : Fin 3))) (F (Fin.natAdd m (2 : Fin 3))) j) ?_ ?_ j
  · intro i; rw [tvdPack_castAdd]
  · intro j'; rw [tvdPack_natAdd]; fin_cases j' <;> rfl

/-- Updating one of the first `m` slots of a packed tuple. -/
lemma tvdPack_update_castAdd {m : ℕ} (v : Fin m → TF (I := I) (M := M))
    (A B C : TF (I := I) (M := M)) (i : Fin m) (W : TF (I := I) (M := M)) :
    Function.update (tvdPack v A B C) (Fin.castAdd 3 i) W
      = tvdPack (Function.update v i W) A B C := by
  funext j
  refine Fin.addCases (motive := fun j => Function.update (tvdPack v A B C) (Fin.castAdd 3 i) W j
      = tvdPack (Function.update v i W) A B C j) ?_ ?_ j
  · intro i'
    rw [Function.update_apply, tvdPack_castAdd, tvdPack_castAdd]
    by_cases h : i' = i
    · subst h; rw [if_pos rfl, Function.update_self]
    · rw [if_neg (fun hh => h (Fin.castAdd_inj.mp hh)), Function.update_of_ne h]
  · intro j'
    rw [Function.update_apply, tvdPack_natAdd, tvdPack_natAdd, if_neg]
    intro hh
    have h2 := congrArg Fin.val hh
    rw [Fin.val_castAdd, Fin.val_natAdd] at h2
    have hi := i.isLt
    omega

/-- Updating the first value slot of a packed tuple. -/
lemma tvdPack_update_natAdd0 {m : ℕ} (v : Fin m → TF (I := I) (M := M))
    (A B C : TF (I := I) (M := M)) (W : TF (I := I) (M := M)) :
    Function.update (tvdPack v A B C) (Fin.natAdd m (0 : Fin 3)) W = tvdPack v W B C := by
  funext j
  refine Fin.addCases (motive := fun j => Function.update (tvdPack v A B C) (Fin.natAdd m (0 : Fin 3)) W j
      = tvdPack v W B C j) ?_ ?_ j
  · intro i
    rw [Function.update_apply, tvdPack_castAdd, tvdPack_castAdd, if_neg]
    intro hh
    have h2 := congrArg Fin.val hh
    rw [Fin.val_natAdd, Fin.val_castAdd] at h2
    have hi := i.isLt
    omega
  · intro j'
    rw [Function.update_apply, tvdPack_natAdd, tvdPack_natAdd]
    by_cases h : j' = (0 : Fin 3)
    · subst h; simp
    · rw [if_neg (fun hh => h (Fin.natAdd_inj m |>.mp hh))]
      fin_cases j' <;> simp_all

/-- Updating the second value slot of a packed tuple. -/
lemma tvdPack_update_natAdd1 {m : ℕ} (v : Fin m → TF (I := I) (M := M))
    (A B C : TF (I := I) (M := M)) (W : TF (I := I) (M := M)) :
    Function.update (tvdPack v A B C) (Fin.natAdd m (1 : Fin 3)) W = tvdPack v A W C := by
  funext j
  refine Fin.addCases (motive := fun j => Function.update (tvdPack v A B C) (Fin.natAdd m (1 : Fin 3)) W j
      = tvdPack v A W C j) ?_ ?_ j
  · intro i
    rw [Function.update_apply, tvdPack_castAdd, tvdPack_castAdd, if_neg]
    intro hh
    have h2 := congrArg Fin.val hh
    rw [Fin.val_natAdd, Fin.val_castAdd] at h2
    have hi := i.isLt
    omega
  · intro j'
    rw [Function.update_apply, tvdPack_natAdd, tvdPack_natAdd]
    by_cases h : j' = (1 : Fin 3)
    · subst h; simp
    · rw [if_neg (fun hh => h (Fin.natAdd_inj m |>.mp hh))]
      fin_cases j' <;> simp_all

/-- Updating the third value slot of a packed tuple. -/
lemma tvdPack_update_natAdd2 {m : ℕ} (v : Fin m → TF (I := I) (M := M))
    (A B C : TF (I := I) (M := M)) (W : TF (I := I) (M := M)) :
    Function.update (tvdPack v A B C) (Fin.natAdd m (2 : Fin 3)) W = tvdPack v A B W := by
  funext j
  refine Fin.addCases (motive := fun j => Function.update (tvdPack v A B C) (Fin.natAdd m (2 : Fin 3)) W j
      = tvdPack v A B W j) ?_ ?_ j
  · intro i
    rw [Function.update_apply, tvdPack_castAdd, tvdPack_castAdd, if_neg]
    intro hh
    have h2 := congrArg Fin.val hh
    rw [Fin.val_natAdd, Fin.val_castAdd] at h2
    have hi := i.isLt
    omega
  · intro j'
    rw [Function.update_apply, tvdPack_natAdd, tvdPack_natAdd]
    by_cases h : j' = (2 : Fin 3)
    · subst h; simp
    · rw [if_neg (fun hh => h (Fin.natAdd_inj m |>.mp hh))]
      fin_cases j' <;> simp_all

/-- The shift of a tuple: the slots `Fin.succ j` of `F : Fin (k+4) → TF` are the packing of `F`'s
slots `Fin.castAdd 3 (Fin.succ i)` and the last three slots. -/
lemma tvdShift_pack {k : ℕ} (F : Fin (k + 4) → TF (I := I) (M := M)) :
    (fun j : Fin (k + 3) => F (Fin.succ j))
      = tvdPack (fun i : Fin k => F (Fin.castAdd 3 (Fin.succ i)))
          (F (Fin.natAdd (k + 1) (0 : Fin 3))) (F (Fin.natAdd (k + 1) (1 : Fin 3)))
          (F (Fin.natAdd (k + 1) (2 : Fin 3))) := by
  funext j
  refine Fin.addCases (motive := fun j => F (Fin.succ j) = tvdPack
      (fun i : Fin k => F (Fin.castAdd 3 (Fin.succ i)))
      (F (Fin.natAdd (k + 1) (0 : Fin 3))) (F (Fin.natAdd (k + 1) (1 : Fin 3)))
      (F (Fin.natAdd (k + 1) (2 : Fin 3))) j) ?_ ?_ j
  · intro i
    rw [tvdPack_castAdd]
    exact congrArg F (Fin.ext rfl)
  · intro j'
    rw [tvdPack_natAdd]
    fin_cases j' <;> rfl

/-- The shift of a packed tuple. -/
lemma tvdShift_pack4 {k : ℕ} (v : Fin (k + 1) → TF (I := I) (M := M))
    (A B C : TF (I := I) (M := M)) :
    (fun j : Fin (k + 3) => tvdPack v A B C (Fin.succ j))
      = tvdPack (fun i : Fin k => v (Fin.succ i)) A B C := by
  funext j
  refine Fin.addCases (motive := fun j => tvdPack v A B C (Fin.succ j)
      = tvdPack (fun i : Fin k => v (Fin.succ i)) A B C j) ?_ ?_ j
  · intro i
    rw [tvdPack_castAdd]
    exact tvdPack_castAdd v A B C (Fin.succ i)
  · intro j'
    have h : (Fin.succ (Fin.natAdd k j') : Fin (k + 4)) = Fin.natAdd (k + 1) j' :=
      Fin.ext (by rw [Fin.val_succ, Fin.val_natAdd, Fin.val_natAdd]; omega)
    rw [h, tvdPack_natAdd, tvdPack_natAdd]

/-- The successor of a `castAdd` index. -/
lemma tvdPack_succ_castAdd {m : ℕ} (v : Fin (m + 1) → TF (I := I) (M := M))
    (A B C : TF (I := I) (M := M)) (i : Fin m) :
    tvdPack v A B C (Fin.succ (Fin.castAdd 3 i)) = v (Fin.succ i) := by
  have h : (Fin.succ (Fin.castAdd 3 i) : Fin (m + 1 + 3)) = Fin.castAdd 3 (Fin.succ i) :=
    Fin.ext rfl
  rw [h, tvdPack_castAdd]

/-- The successor of a `natAdd` index. -/
lemma tvdPack_succ_natAdd {m : ℕ} (v : Fin (m + 1) → TF (I := I) (M := M))
    (A B C : TF (I := I) (M := M)) (j : Fin 3) :
    tvdPack v A B C (Fin.succ (Fin.natAdd m j)) = ![A, B, C] j := by
  have h : (Fin.succ (Fin.natAdd m j) : Fin (m + 1 + 3)) = Fin.natAdd (m + 1) j :=
    Fin.ext (by rw [Fin.val_succ, Fin.val_natAdd, Fin.val_natAdd]; omega)
  rw [h, tvdPack_natAdd]

lemma tvdPack_succ_natAdd0 {m : ℕ} (v : Fin (m + 1) → TF (I := I) (M := M))
    (A B C : TF (I := I) (M := M)) :
    tvdPack v A B C (Fin.succ (Fin.natAdd m (0 : Fin 3))) = A := by
  rw [tvdPack_succ_natAdd]
  simp

lemma tvdPack_succ_natAdd1 {m : ℕ} (v : Fin (m + 1) → TF (I := I) (M := M))
    (A B C : TF (I := I) (M := M)) :
    tvdPack v A B C (Fin.succ (Fin.natAdd m (1 : Fin 3))) = B := by
  rw [tvdPack_succ_natAdd]
  simp

lemma tvdPack_succ_natAdd2 {m : ℕ} (v : Fin (m + 1) → TF (I := I) (M := M))
    (A B C : TF (I := I) (M := M)) :
    tvdPack v A B C (Fin.succ (Fin.natAdd m (2 : Fin 3))) = C := by
  rw [tvdPack_succ_natAdd]
  simp

/-- The first slot of a packed tuple is the first slot of `v`. -/
lemma tvdPack_zero {m : ℕ} (v : Fin (m + 1) → TF (I := I) (M := M))
    (A B C : TF (I := I) (M := M)) :
    tvdPack v A B C (0 : Fin (m + 1 + 3)) = v 0 := by
  have h : (0 : Fin (m + 1 + 3)) = Fin.castAdd 3 (0 : Fin (m + 1)) := Fin.ext rfl
  rw [h, tvdPack_castAdd]

/-- `tvdTp` on a packed tuple is the frozen `tower` on the unpacked data. -/
lemma tvdTp_pack {k : ℕ} (g : SMet I M) (base : Op3 (I := I) (M := M) 0)
    (v : Fin k → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)) :
    tvdTp g base k (tvdPack v A B C) = tower (lcOf g) base k v A B C := by
  rw [tvdTp]
  have h1 : (fun j : Fin k => tvdPack v A B C (Fin.castAdd 3 j)) = v := by
    funext j; rw [tvdPack_castAdd]
  rw [h1, tvdPack_natAdd, tvdPack_natAdd, tvdPack_natAdd]
  simp

/-! ## A small toolkit

Applied forms of the Leibniz rules for `mvfderiv` and for a covariant derivative, in exactly the
shape produced by the recursion `tvdStepP`. -/

/-- `mvfderiv` is linear in the direction, in finite-sum form. -/
theorem tvd_mvfderiv_dir_sum {F : M → ℝ} {x : M} {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (w : ι → TangentSpace I x) :
    mvfderiv I F x (∑ q ∈ s, a q • w q) = ∑ q ∈ s, a q * mvfderiv I F x (w q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert q s hq ih =>
      rw [Finset.sum_insert hq, Finset.sum_insert hq, map_add, map_smul, ih]
      simp

/-- Leibniz rule for `mvfderiv` of a pointwise product of two real functions. -/
theorem tvd_mvfderiv_mul {f h : M → ℝ} {x : M} {v : TangentSpace I x}
    (hf : MDiffAt f x) (hh : MDiffAt h x) :
    mvfderiv I (fun y : M => f y * h y) x v
      = f x * mvfderiv I h x v + mvfderiv I f x v * h x := by
  rw [show (fun y : M => f y * h y) = (f * h) from rfl]
  have h := congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v)
    (mvfderiv_smul (I := I) (a := f) (g := h) hf hh)
  simpa using h

/-- The pointwise (lambda) form of a finite sum of real functions is the function-space sum. -/
theorem tvd_sum_funext {ι : Type*} (s : Finset ι) (F : ι → M → ℝ) :
    (fun y : M => ∑ q ∈ s, F q y) = (∑ q ∈ s, F q) := by
  funext y; rw [Finset.sum_apply]

/-- The pointwise (lambda) form of a finite sum of tangent fields is the function-space sum. -/
theorem tvd_sum_funext_section {ι : Type*} (s : Finset ι) (f : ι → M → ℝ)
    (X : ι → TF (I := I) (M := M)) :
    (fun y : M => ∑ q ∈ s, f q y • X q y) = (∑ q ∈ s, f q • X q) := by
  funext y; rw [Finset.sum_apply]; rfl

/-- `mvfderiv` of a finite sum of real functions. -/
theorem tvd_mvfderiv_sum {x : M} {v : TangentSpace I x} {ι : Type*} (s : Finset ι)
    (F : ι → M → ℝ) (hF : ∀ q ∈ s, MDiffAt (F q) x) :
    mvfderiv I (fun y : M => ∑ q ∈ s, F q y) x v = ∑ q ∈ s, mvfderiv I (F q) x v := by
  rw [tvd_sum_funext s F]
  classical
  induction s using Finset.induction_on with
  | empty => simp [mvfderiv_const]
  | insert q s hq ih =>
      rw [Finset.sum_insert hq, Finset.sum_insert hq,
        mvfderiv_add (hF q (Finset.mem_insert_self q s))
          (MDifferentiableAt.sum (fun q' hq' => hF q' (Finset.mem_insert_of_mem hq')))]
      simp only [ContinuousLinearMap.add_apply]
      rw [ih (fun q' hq' => hF q' (Finset.mem_insert_of_mem hq'))]

/-- Additivity of a covariant derivative in the section, applied at a vector. -/
theorem tvd_cov_add_app (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    {σ σ' : TF (I := I) (M := M)} {x : M} {v : TangentSpace I x}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) :
    cov (σ + σ') x v = cov σ x v + cov σ' x v := by
  rw [(cov.isCovariantDerivativeOn (s := Set.univ)).add hσ hσ']
  rfl

/-- The Leibniz rule of a covariant derivative, applied at a vector. -/
theorem tvd_cov_leibniz_app (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    {σ : TF (I := I) (M := M)} {f : M → ℝ} {x : M} {v : TangentSpace I x}
    (hσ : MDiffAt (T% σ) x) (hf : MDiffAt f x) :
    cov (f • σ) x v = f x • cov σ x v + mvfderiv I f x v • σ x := by
  have h := congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L v)
    ((cov.isCovariantDerivativeOn (s := Set.univ)).leibniz hσ hf)
  simpa using h

/-- Germ-locality of a covariant derivative in the section, applied at a vector. -/
theorem tvd_cov_congr_app (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    {σ σ' : TF (I := I) (M := M)} {x : M} {v : TangentSpace I x}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) (h : σ =ᶠ[𝓝 x] σ') :
    cov σ x v = cov σ' x v := by
  rw [(cov.isCovariantDerivativeOn (s := Set.univ)).congr_of_eventuallyEq hσ hσ'
    (Filter.univ_mem) h]

/-- A covariant derivative of a constant multiple, applied at a vector. -/
theorem tvd_cov_smul_const_app (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    {σ : TF (I := I) (M := M)} {c : ℝ} {x : M} {v : TangentSpace I x} (hσ : MDiffAt (T% σ) x) :
    cov (c • σ) x v = c • cov σ x v := by
  rw [(cov.isCovariantDerivativeOn (s := Set.univ)).smul_const c hσ]
  rfl

/-- A covariant derivative of a finite sum of smooth combinations, as an equality of sections. -/
theorem tvd_cov_sum (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    {ι : Type*} (s : Finset ι) (f : ι → M → ℝ) (X : ι → TF (I := I) (M := M)) {x : M}
    (hX : ∀ q ∈ s, MDiffAt (T% (X q)) x) (hf : ∀ q ∈ s, MDiffAt (f q) x) :
    cov (fun y : M => ∑ q ∈ s, f q y • X q y) x
      = ∑ q ∈ s, cov (fun y : M => f q y • X q y) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h0 : (fun y : M => ∑ q ∈ (∅ : Finset ι), f q y • X q y)
          = (0 : Π y : M, TangentSpace I y) := by
        funext y; simp
      rw [h0, cov.zero]
      simp
  | insert q s hq ih =>
      have h2 : cov ((fun y : M => f q y • X q y)
            + fun y : M => ∑ q' ∈ s, f q' y • X q' y) x
          = cov (fun y : M => f q y • X q y) x
            + cov (fun y : M => ∑ q' ∈ s, f q' y • X q' y) x :=
        (cov.isCovariantDerivativeOn (s := Set.univ)).add
          (σ := fun y : M => f q y • X q y) (σ' := fun y : M => ∑ q' ∈ s, f q' y • X q' y)
          ((hf q (Finset.mem_insert_self q s)).smul_section (hX q (Finset.mem_insert_self q s)))
          (MDifferentiableAt.sum_section
            (fun q' hq' => (hf q' (Finset.mem_insert_of_mem hq')).smul_section
              (hX q' (Finset.mem_insert_of_mem hq'))))
      have h1 : (fun y : M => ∑ q' ∈ insert q s, f q' y • X q' y)
          = ((fun y : M => f q y • X q y) + fun y : M => ∑ q' ∈ s, f q' y • X q' y) := by
        funext y; rw [Finset.sum_insert hq]; rfl
      rw [h1, h2, ih (fun q' hq' => hX q' (Finset.mem_insert_of_mem hq'))
        (fun q' hq' => hf q' (Finset.mem_insert_of_mem hq')), Finset.sum_insert hq]

/-! ## Smoothness closure

`SmE I M X` is `ContMDiff ∞ (T% X)` and `SmF I M f` is `ContMDiff ∞ f`; the closure properties below
are the ones used by the induction. -/

theorem tvd_smE_add {X Y : TF (I := I) (M := M)} (hX : SmE I M X) (hY : SmE I M Y) :
    SmE I M (X + Y) :=
  ContMDiff.add_section hX hY

theorem tvd_smE_sub {X Y : TF (I := I) (M := M)} (hX : SmE I M X) (hY : SmE I M Y) :
    SmE I M (X - Y) :=
  ContMDiff.sub_section hX hY

theorem tvd_smE_smul {f : M → ℝ} {X : TF (I := I) (M := M)} (hf : SmF I M f) (hX : SmE I M X) :
    SmE I M (f • X) :=
  ContMDiff.smul_section hf hX

theorem tvd_smE_sum {ι : Type*} (s : Finset ι) (f : ι → M → ℝ)
    (X : ι → TF (I := I) (M := M)) (hf : ∀ q ∈ s, SmF I M (f q)) (hX : ∀ q ∈ s, SmE I M (X q)) :
    SmE I M (fun y : M => ∑ q ∈ s, f q y • X q y) :=
  ContMDiff.sum_section (s := s) (t := fun q y => f q y • X q y)
    (fun q hq => ContMDiff.smul_section (hf q hq) (hX q hq))

theorem tvd_smF_const : SmF I M (fun _ : M => (1 : ℝ)) := contMDiff_const

theorem tvd_smF_sum {ι : Type*} (s : Finset ι) (f : ι → M → ℝ) (hf : ∀ q ∈ s, SmF I M (f q)) :
    SmF I M (fun y : M => ∑ q ∈ s, f q y) :=
  ContMDiff.sum (t := s) (f := f) (fun q hq => hf q hq)

theorem tvd_smF_mul {f h : M → ℝ} (hf : SmF I M f) (hh : SmF I M h) : SmF I M (f * h) :=
  ContMDiff.mul hf hh

theorem tvd_smF_sub {f h : M → ℝ} (hf : SmF I M f) (hh : SmF I M h) : SmF I M (f - h) :=
  ContMDiff.sub hf hh

end Work.Diff.EXT.ATower
