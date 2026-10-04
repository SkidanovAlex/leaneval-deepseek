import Mathlib
import Submission.Work.Diff.EXT.ChartCoreDefs
import Submission.Work.Diff.GE.ExtTensor
import Submission.Work.Diff.T.metric_pairing_smooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The tower of covariant derivatives of the connection difference, as a packed `Fin (k+3)`-tuple

`Work.Diff.EXT.covKAExt G t k v A B C x` (frozen, `Submission/Work/Diff/EXT/ChartCoreDefs.lean`) is
the `k`-th covariant derivative, with respect to the *fixed* background connection
`∇^{G 0} = lcOf (G 0)`, of the lowered connection difference `aOf G t = g_t(∇^{g_t} − ∇^{g_0})`,
evaluated on `k` direction fields `v` and three argument fields `A B C`.

Its recursion is exactly the covariant-derivative (Leibniz) recursion on the `k + 3` slots of the
`(0,3)`-tensor `aOf G t`, with the *first* slot as the differentiation direction.  Packing the `k`
direction slots and the three argument slots into a single `Fin (k+3)`-tuple `F` gives the iteration
`cktA` below, for which `covKAExt G t k v A B C x = cktA G t k (mkT3 v (trip3 A B C)) x`
(`cktA_mkT3_eq`).

The reason for the packing is that the *tensoriality* of `covKAExt` (its value at `x` depends only
on the values of the `k + 3` fields at `x`) can then be proved by a uniform induction on `k`
following the already-proved `Work.Diff.EXT.TensProp` development for the curvature
(`Submission/Work/Diff/EXT/curvNormK_frame_indep.lean`): at every level the operator is smooth on
smooth tuples (`TensPropA.1`), `C^∞(M)`-linear in every slot (`TensPropA.2.1`) and local
(`TensPropA.2.2`), whence single-slot value dependence `cktA_val_dep` via
`Work.Diff.GE.field_value_dep_of_linear`.

## Contents

* `TfA` (tangent fields), `SmA` (smooth tangent fields), `dirFA` (`∇` of a field in a direction);
* `cktA` and its one-step unfolding `cktA_succ`;
* `TensPropA`, the induction statement;
* the elementary helpers `dirFA_add_dir`, `dirFA_smooth`, `dirFA_eventuallyEq`, `smA_update`,
  `mvfderiv_two_smulA`, `eventuallyEq_nhds_eventuallyA`, the `Fin.cons`/`update` bookkeeping lemmas
  `update_zero_eq_consA`, `update_succ_eq_consA`, and the derived slot additivity/constancy
  `TensPropA_add`, `TensPropA_smul`;
* the packing `mkT3`, `trip3` with the bridge `cktA_mkT3_eq`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Commons.Geometry.Manifold.VectorField

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-- A tangent field on `M`. -/
abbrev TfA : Type _ := Π y : M, TangentSpace I y

/-- A smooth tangent field on `M`. -/
abbrev SmA (X : TfA (I := I) (M := M)) : Prop := CMDiff ∞ (T% X)

/-- A smooth function on `M` (notation-free wrapper for `CMDiff ∞`). -/
abbrev SmFunA (f : M → ℝ) : Prop := CMDiff ∞ f

/-- Eventual equality of two `ℝ`-valued functions at `x` (notation-free wrapper for `=ᶠ[𝓝 x]`). -/
abbrev EvEqA (x : M) (p q : M → ℝ) : Prop := p =ᶠ[𝓝 x] q

/-- Eventual equality of two tangent fields at `x`. -/
abbrev EvEqFA (x : M) (p q : TfA (I := I) (M := M)) : Prop := p =ᶠ[𝓝 x] q

/-- `dirFA g X v0` is the covariant derivative `∇_{v0} X` of the field `X` in the direction of the
field `v0`, for the Levi-Civita connection of `g`, as a field. -/
noncomputable def dirFA (g : SMet I M) (X v0 : TfA (I := I) (M := M)) : TfA (I := I) (M := M) :=
  fun y => lcOf g X y (v0 y)

/-- **The packed recursion.**  `cktA G t k F` is the `k`-th covariant derivative with respect to the
fixed connection `∇^{G 0}` of the lowered connection difference `aOf G t`, evaluated on the `k + 3`
fields of `F`: the first `k` entries are the differentiation slots, the last three the argument
slots of `aOf`.  This is `covKAExt G t k` with the slots packed (`cktA_mkT3_eq`). -/
noncomputable def cktA (G : ℝ → SMet I M) (t : ℝ) :
    ∀ k : ℕ, (Fin (k + 3) → TfA (I := I) (M := M)) → M → ℝ
  | 0, F => fun y => aOf G t (F 0) (F 1) (F 2) y
  | k + 1, F => fun y =>
      mvfderiv I (cktA G t k (fun i : Fin (k + 3) => F i.succ)) y (F 0 y)
        - ∑ s : Fin (k + 3), cktA G t k (Function.update (fun i : Fin (k + 3) => F i.succ) s
            (dirFA (G 0) ((fun i : Fin (k + 3) => F i.succ) s) (F 0))) y

/-- The recursion, as an equality of functions. -/
lemma cktA_succ (G : ℝ → SMet I M) (t : ℝ) (k : ℕ) (F : Fin (k + 4) → TfA (I := I) (M := M)) :
    cktA G t (k + 1) F
      = (fun y : M => (mvfderiv I (cktA G t k (fun i : Fin (k + 3) => F i.succ)) y) (F 0 y))
        - ∑ s : Fin (k + 3), cktA G t k (Function.update (fun i : Fin (k + 3) => F i.succ) s
            (dirFA (G 0) ((fun i : Fin (k + 3) => F i.succ) s) (F 0))) := by
  funext y
  simp only [cktA, Finset.sum_apply, Pi.sub_apply]

/-- **The induction statement.**  For tuples of smooth fields, `cktA G t k` is smooth,
`C^∞(M)`-linear in every slot, and local. -/
def TensPropA (G : ℝ → SMet I M) (t : ℝ) (k : ℕ) : Prop :=
  ∀ F : Fin (k + 3) → TfA (I := I) (M := M),
    (∀ s, SmA (I := I) (M := M) (F s)) →
    CMDiff ∞ (fun y : M => cktA G t k F y) ∧
    (∀ (s : Fin (k + 3)) (X₁ X₂ : TfA (I := I) (M := M)) (f₁ f₂ : M → ℝ),
      SmA (I := I) (M := M) X₁ → SmA (I := I) (M := M) X₂ → CMDiff ∞ f₁ → CMDiff ∞ f₂ →
      cktA G t k (Function.update F s (f₁ • X₁ + f₂ • X₂))
        = f₁ • cktA G t k (Function.update F s X₁) + f₂ • cktA G t k (Function.update F s X₂)) ∧
    (∀ (x : M) (F' : Fin (k + 3) → TfA (I := I) (M := M)),
      (∀ s, SmA (I := I) (M := M) (F' s)) →
      (∀ s, F s =ᶠ[𝓝 x] F' s) → cktA G t k F =ᶠ[𝓝 x] cktA G t k F')

/-! ## Elementary helpers -/

/-- `dirFA` is additive and homogeneous in the *direction*. -/
lemma dirFA_add_dir (g : SMet I M) (X X₁ X₂ : TfA (I := I) (M := M)) (f₁ f₂ : M → ℝ) :
    dirFA g X (f₁ • X₁ + f₂ • X₂) = f₁ • dirFA g X X₁ + f₂ • dirFA g X X₂ := by
  funext y
  simp only [dirFA, Pi.add_apply, Pi.smul_apply', map_add, map_smul]

/-- `dirFA` of a smooth field in a smooth direction is smooth. -/
lemma dirFA_smooth (hLC : LCSmooth I M) (g : SMet I M) {X v0 : TfA (I := I) (M := M)}
    (hX : SmA (I := I) (M := M) X) (hv0 : SmA (I := I) (M := M) v0) :
    SmA (I := I) (M := M) (dirFA g X v0) := by
  obtain ⟨hcov⟩ := (hLC g).1
  exact Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
    (lcOf g) hcov hX hv0

/-- `Function.update` of a tuple at a slot, all fields smooth. -/
lemma smA_update {k : ℕ} {G : Fin k → TfA (I := I) (M := M)}
    (hG : ∀ i, SmA (I := I) (M := M) (G i)) {j : Fin k} {W : TfA (I := I) (M := M)}
    (hW : SmA (I := I) (M := M) W) : ∀ q, SmA (I := I) (M := M) ((Function.update G j W) q) := by
  intro q
  rcases eq_or_ne q j with h | h
  · subst h; rw [Function.update_self]; exact hW
  · rw [Function.update_of_ne h]; exact hG q

/-- The product rule for a sum of two scalar multiples, evaluated in a direction. -/
lemma mvfderiv_two_smulA_lambda (f₁ f₂ Φ₁ Φ₂ : M → ℝ) (x : M) (u : TangentSpace I x)
    (hf₁ : MDiffAt f₁ x) (hf₂ : MDiffAt f₂ x) (hΦ₁ : MDiffAt Φ₁ x) (hΦ₂ : MDiffAt Φ₂ x) :
    (mvfderiv I (fun y : M => f₁ y • Φ₁ y + f₂ y • Φ₂ y) x) u
      = f₁ x * ((mvfderiv I Φ₁ x) u) + ((mvfderiv I f₁ x) u) * Φ₁ x
        + f₂ x * ((mvfderiv I Φ₂ x) u) + ((mvfderiv I f₂ x) u) * Φ₂ x := by
  have hfun : (fun y : M => f₁ y • Φ₁ y + f₂ y • Φ₂ y) = f₁ • Φ₁ + f₂ • Φ₂ := rfl
  have hadd : mvfderiv I (f₁ • Φ₁ + f₂ • Φ₂) x
      = mvfderiv I (f₁ • Φ₁) x + mvfderiv I (f₂ • Φ₂) x :=
    mvfderiv_add (hf₁.smul hΦ₁) (hf₂.smul hΦ₂)
  have hs1 : mvfderiv I (f₁ • Φ₁) x = f₁ x • mvfderiv I Φ₁ x + (mvfderiv I f₁ x).smulRight (Φ₁ x) :=
    mvfderiv_smul hf₁ hΦ₁
  have hs2 : mvfderiv I (f₂ • Φ₂) x = f₂ x • mvfderiv I Φ₂ x + (mvfderiv I f₂ x).smulRight (Φ₂ x) :=
    mvfderiv_smul hf₂ hΦ₂
  rw [hfun, hadd, hs1, hs2]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

/-- The product rule for a sum of two scalar multiples (field form), evaluated in a direction. -/
lemma mvfderiv_two_smulA (f₁ f₂ Φ₁ Φ₂ : M → ℝ) (x : M) (u : TangentSpace I x)
    (hf₁ : MDiffAt f₁ x) (hf₂ : MDiffAt f₂ x) (hΦ₁ : MDiffAt Φ₁ x) (hΦ₂ : MDiffAt Φ₂ x) :
    (mvfderiv I (f₁ • Φ₁ + f₂ • Φ₂) x) u
      = f₁ x * ((mvfderiv I Φ₁ x) u) + ((mvfderiv I f₁ x) u) * Φ₁ x
        + f₂ x * ((mvfderiv I Φ₂ x) u) + ((mvfderiv I f₂ x) u) * Φ₂ x := by
  have hfun : (f₁ • Φ₁ + f₂ • Φ₂) = fun y : M => f₁ y • Φ₁ y + f₂ y • Φ₂ y := rfl
  rw [hfun]
  exact mvfderiv_two_smulA_lambda f₁ f₂ Φ₁ Φ₂ x u hf₁ hf₂ hΦ₁ hΦ₂

/-- An eventual equality near `x` is eventual near every nearby point. -/
lemma eventuallyEq_nhds_eventuallyA {α : Type*} [TopologicalSpace α] {x : α} {p q : α → M}
    (h : p =ᶠ[𝓝 x] q) : ∀ᶠ y in 𝓝 x, p =ᶠ[𝓝 y] q := by
  obtain ⟨U, hU, hUU⟩ := Filter.eventually_iff_exists_mem.mp h
  have hx : x ∈ interior U := mem_interior_iff_mem_nhds.mpr hU
  filter_upwards [isOpen_interior.mem_nhds hx] with y hy
  exact Filter.eventually_iff_exists_mem.mpr
    ⟨interior U, isOpen_interior.mem_nhds hy, fun z hz => hUU z (interior_subset hz)⟩

/-- `dirFA` is local in both arguments. -/
lemma dirFA_eventuallyEq {g : SMet I M} {X X' v v' : TfA (I := I) (M := M)} {x : M}
    (hX : SmA (I := I) (M := M) X) (hX' : SmA (I := I) (M := M) X')
    (hXeq : X =ᶠ[𝓝 x] X') (hveq : v =ᶠ[𝓝 x] v') :
    dirFA g X v =ᶠ[𝓝 x] dirFA g X' v' := by
  have h1 : ∀ᶠ y in 𝓝 x, X =ᶠ[𝓝 y] X' := eventuallyEq_nhds_eventuallyA hXeq
  have h2 : ∀ᶠ y in 𝓝 x, v =ᶠ[𝓝 y] v' := eventuallyEq_nhds_eventuallyA hveq
  filter_upwards [h1, h2] with y hyX hyv
  rw [dirFA, dirFA]
  rw [Work.Diff.GE.Kato3.lcOf_congr_eventuallyEq g (hX.mdifferentiableAt (by simp))
    (hX'.mdifferentiableAt (by simp)) hyX, hyv.eq_of_nhds]

/-- Updating the first slot of a tuple is `Fin.cons`. -/
lemma update_zero_eq_consA {k : ℕ} (F : Fin (k + 4) → TfA (I := I) (M := M))
    (W : TfA (I := I) (M := M)) :
    Function.update F 0 W = (Fin.cons W (fun i : Fin (k + 3) => F i.succ) : Fin (k + 4) → TfA) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rw [Fin.cons_zero (α := fun _ : Fin (k + 4) => TfA (I := I) (M := M)), Function.update_self]
  · intro j
    rw [Fin.cons_succ (α := fun _ : Fin (k + 4) => TfA (I := I) (M := M)),
      Function.update_of_ne (Fin.succ_ne_zero j) W F]

/-- Updating a non-first slot of a tuple is `Fin.cons` over the shifted tuple. -/
lemma update_succ_eq_consA {k : ℕ} (F : Fin (k + 4) → TfA (I := I) (M := M)) (j : Fin (k + 3))
    (W : TfA (I := I) (M := M)) :
    Function.update F j.succ W
      = (Fin.cons (F 0) (Function.update (fun i : Fin (k + 3) => F i.succ) j W)
          : Fin (k + 4) → TfA) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rw [Fin.cons_zero (α := fun _ : Fin (k + 4) => TfA (I := I) (M := M)),
      Function.update_of_ne (Ne.symm (Fin.succ_ne_zero j)) W F]
  · intro j'
    rw [Fin.cons_succ (α := fun _ : Fin (k + 4) => TfA (I := I) (M := M))]
    rcases eq_or_ne j' j with h | h
    · subst h; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (fun hh => h (Fin.succ_inj.mp hh)), Function.update_of_ne h]

/-! ## Derived slot additivity and constancy -/

lemma TensPropA_add {G : ℝ → SMet I M} {t : ℝ} {k : ℕ} (h : TensPropA G t k)
    {F : Fin (k + 3) → TfA (I := I) (M := M)} (hF : ∀ s, SmA (I := I) (M := M) (F s))
    (s : Fin (k + 3)) {X Y : TfA (I := I) (M := M)}
    (hX : SmA (I := I) (M := M) X) (hY : SmA (I := I) (M := M) Y) :
    cktA G t k (Function.update F s (X + Y))
      = cktA G t k (Function.update F s X) + cktA G t k (Function.update F s Y) := by
  have h1 := (h F hF).2.1 s X Y (fun _ : M => (1 : ℝ)) (fun _ : M => (1 : ℝ)) hX hY
    (contMDiff_const (c := (1 : ℝ))) (contMDiff_const (c := (1 : ℝ)))
  have e1 : (fun _ : M => (1 : ℝ)) • X + (fun _ : M => (1 : ℝ)) • Y = X + Y := by
    funext z; simp
  have e2 : (fun _ : M => (1 : ℝ)) • cktA G t k (Function.update F s X)
      = cktA G t k (Function.update F s X) := by funext z; simp
  have e3 : (fun _ : M => (1 : ℝ)) • cktA G t k (Function.update F s Y)
      = cktA G t k (Function.update F s Y) := by funext z; simp
  rw [e1, e2, e3] at h1
  exact h1

lemma TensPropA_smul {G : ℝ → SMet I M} {t : ℝ} {k : ℕ} (h : TensPropA G t k)
    {F : Fin (k + 3) → TfA (I := I) (M := M)} (hF : ∀ s, SmA (I := I) (M := M) (F s))
    (s : Fin (k + 3)) (c : ℝ) {X : TfA (I := I) (M := M)} (hX : SmA (I := I) (M := M) X) :
    cktA G t k (Function.update F s ((fun _ : M => c) • X))
      = (fun _ : M => c) • cktA G t k (Function.update F s X) := by
  have h1 := (h F hF).2.1 s X X (fun _ : M => c) (fun _ : M => (0 : ℝ)) hX hX
    (contMDiff_const (c := c)) (contMDiff_const (c := (0 : ℝ)))
  have e1 : (fun _ : M => c) • X + (fun _ : M => (0 : ℝ)) • X = (fun _ : M => c) • X := by
    funext z; simp
  have e2 : (fun _ : M => c) • cktA G t k (Function.update F s X)
      + (fun _ : M => (0 : ℝ)) • cktA G t k (Function.update F s X)
      = (fun _ : M => c) • cktA G t k (Function.update F s X) := by funext z; simp
  rw [e1, e2] at h1
  exact h1

/-! ## The packing and the bridge to `covKAExt` -/

/-- The three argument slots `A B C` of `covKAExt`, as a `Fin 3`-tuple of fields. -/
def trip3 (A B C : TfA (I := I) (M := M)) : Fin 3 → TfA (I := I) (M := M) := ![A, B, C]

@[simp] theorem trip3_zero (A B C : TfA (I := I) (M := M)) : trip3 A B C 0 = A := rfl

@[simp] theorem trip3_one (A B C : TfA (I := I) (M := M)) : trip3 A B C 1 = B := rfl

@[simp] theorem trip3_two (A B C : TfA (I := I) (M := M)) : trip3 A B C 2 = C := rfl

/-- Assemble a `Fin (k+3)`-tuple of fields from a `k`-tuple of differentiation slots and a
`3`-tuple of argument slots. -/
def mkT3 {k : ℕ} (w : Fin k → TfA (I := I) (M := M)) (B : Fin 3 → TfA (I := I) (M := M)) :
    Fin (k + 3) → TfA (I := I) (M := M) :=
  Fin.addCases (motive := fun _ => TfA (I := I) (M := M)) (fun i => w i) (fun p => B p)

lemma mkT3_castAdd {k : ℕ} (w : Fin k → TfA (I := I) (M := M))
    (B : Fin 3 → TfA (I := I) (M := M)) (i : Fin k) :
    mkT3 w B (Fin.castAdd 3 i) = w i := Fin.addCases_left i

lemma mkT3_natAdd {k : ℕ} (w : Fin k → TfA (I := I) (M := M))
    (B : Fin 3 → TfA (I := I) (M := M)) (p : Fin 3) :
    mkT3 w B (Fin.natAdd k p) = B p := Fin.addCases_right p

lemma succ_castAdd_three {k : ℕ} (i : Fin k) :
    (Fin.castAdd 3 i).succ = Fin.castAdd 3 i.succ := by
  ext; simp

lemma succ_natAdd_three {k : ℕ} (p : Fin 3) :
    (Fin.natAdd k p).succ = Fin.natAdd (k + 1) p := by
  ext; simp only [Fin.val_succ, Fin.val_natAdd]; omega

lemma natAdd_ne_castAdd_three {k : ℕ} (p : Fin 3) (i : Fin k) :
    Fin.natAdd k p ≠ Fin.castAdd 3 i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
  omega

lemma update_castAdd_mkT3 {k : ℕ} (w : Fin k → TfA (I := I) (M := M))
    (B : Fin 3 → TfA (I := I) (M := M)) (i : Fin k) (X : TfA (I := I) (M := M)) :
    Function.update (mkT3 w B) (Fin.castAdd 3 i) X = mkT3 (Function.update w i X) B := by
  funext s
  refine Fin.addCases ?_ ?_ s
  · intro j
    rw [mkT3_castAdd (Function.update w i X) B j]
    rcases eq_or_ne j i with h | h
    · subst h
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (fun hh => h (Fin.castAdd_inj.mp hh)) X (mkT3 w B),
        Function.update_of_ne h X w, mkT3_castAdd]
  · intro p
    rw [mkT3_natAdd (Function.update w i X) B p,
      Function.update_of_ne (natAdd_ne_castAdd_three p i) X (mkT3 w B), mkT3_natAdd]

lemma update_natAdd_mkT3 {k : ℕ} (w : Fin k → TfA (I := I) (M := M))
    (B : Fin 3 → TfA (I := I) (M := M)) (p : Fin 3) (X : TfA (I := I) (M := M)) :
    Function.update (mkT3 w B) (Fin.natAdd k p) X = mkT3 w (Function.update B p X) := by
  funext s
  refine Fin.addCases ?_ ?_ s
  · intro i
    rw [mkT3_castAdd w (Function.update B p X) i,
      Function.update_of_ne (Ne.symm (natAdd_ne_castAdd_three p i)) X (mkT3 w B), mkT3_castAdd]
  · intro q
    rw [mkT3_natAdd w (Function.update B p X) q]
    rcases eq_or_ne q p with h | h
    · subst h
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (fun hh => h ((Fin.natAdd_inj k).mp hh)) X (mkT3 w B),
        Function.update_of_ne h X B, mkT3_natAdd]

lemma mkT3_comp_succ {k : ℕ} (w : Fin (k + 1) → TfA (I := I) (M := M))
    (B : Fin 3 → TfA (I := I) (M := M)) :
    (fun i : Fin (k + 3) => mkT3 w B i.succ) = mkT3 (fun i : Fin k => w i.succ) B := by
  funext s
  refine Fin.addCases ?_ ?_ s
  · intro i
    rw [mkT3_castAdd (fun i : Fin k => w i.succ) B i, succ_castAdd_three, mkT3_castAdd]
  · intro p
    rw [mkT3_natAdd (fun i : Fin k => w i.succ) B p, succ_natAdd_three, mkT3_natAdd]

/-- The recursion `cktA` computes `covKAExt` on the corresponding packed tuple. -/
lemma cktA_mkT3_eq (G : ℝ → SMet I M) (t : ℝ) :
    ∀ (k : ℕ) (w : Fin k → TfA (I := I) (M := M)) (B : Fin 3 → TfA (I := I) (M := M)) (y : M),
      cktA G t k (mkT3 w B) y = covKAExt G t k w (B 0) (B 1) (B 2) y := by
  intro k
  induction k with
  | zero =>
      intro w B y
      rfl
  | succ k ih =>
      intro v A y
      have h0 : mkT3 v A 0 = v 0 := by
        rw [show (0 : Fin (k + 4)) = Fin.castAdd 3 (0 : Fin (k + 1)) from rfl, mkT3_castAdd]
      have htail : (fun i : Fin (k + 3) => mkT3 v A i.succ)
          = mkT3 (fun i : Fin k => v i.succ) A := mkT3_comp_succ v A
      have hder : cktA G t k (mkT3 (fun i : Fin k => v i.succ) A)
          = covKAExt G t k (fun i : Fin k => v i.succ) (A 0) (A 1) (A 2) :=
        funext (fun z => ih (fun i : Fin k => v i.succ) A z)
      have hsumk : (∑ i : Fin k, cktA G t k
            (Function.update (mkT3 (fun i : Fin k => v i.succ) A) (Fin.castAdd 3 i)
              (dirFA (G 0) ((mkT3 (fun i : Fin k => v i.succ) A) (Fin.castAdd 3 i)) (v 0))) y)
          = ∑ i : Fin k, covKAExt G t k (Function.update (fun i : Fin k => v i.succ) i
              (dirFA (G 0) (v i.succ) (v 0))) (A 0) (A 1) (A 2) y := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [update_castAdd_mkT3, mkT3_castAdd]
        exact ih (Function.update (fun i : Fin k => v i.succ) i (dirFA (G 0) (v i.succ) (v 0))) A y
      have hsum3 : (∑ p : Fin 3, cktA G t k
            (Function.update (mkT3 (fun i : Fin k => v i.succ) A) (Fin.natAdd k p)
              (dirFA (G 0) ((mkT3 (fun i : Fin k => v i.succ) A) (Fin.natAdd k p)) (v 0))) y)
          = ∑ p : Fin 3, covKAExt G t k (fun i : Fin k => v i.succ)
              ((Function.update A p (dirFA (G 0) (A p) (v 0))) 0)
              ((Function.update A p (dirFA (G 0) (A p) (v 0))) 1)
              ((Function.update A p (dirFA (G 0) (A p) (v 0))) 2) y := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [update_natAdd_mkT3, mkT3_natAdd]
        exact ih (fun i : Fin k => v i.succ) (Function.update A p (dirFA (G 0) (A p) (v 0))) y
      have hthree : (∑ p : Fin 3, covKAExt G t k (fun i : Fin k => v i.succ)
            ((Function.update A p (dirFA (G 0) (A p) (v 0))) 0)
            ((Function.update A p (dirFA (G 0) (A p) (v 0))) 1)
            ((Function.update A p (dirFA (G 0) (A p) (v 0))) 2) y)
          = covKAExt G t k (fun i : Fin k => v i.succ) (dirFA (G 0) (A 0) (v 0)) (A 1) (A 2) y
            + covKAExt G t k (fun i : Fin k => v i.succ) (A 0) (dirFA (G 0) (A 1) (v 0)) (A 2) y
            + covKAExt G t k (fun i : Fin k => v i.succ) (A 0) (A 1) (dirFA (G 0) (A 2) (v 0)) y := by
        rw [Fin.sum_univ_three]
        simp only [Function.update_self,
          Function.update_of_ne (by decide : (0 : Fin 3) ≠ 1),
          Function.update_of_ne (by decide : (0 : Fin 3) ≠ 2),
          Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0),
          Function.update_of_ne (by decide : (1 : Fin 3) ≠ 2),
          Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0),
          Function.update_of_ne (by decide : (2 : Fin 3) ≠ 1)]
      rw [cktA_succ]
      rw [Pi.sub_apply, Finset.sum_apply]
      rw [htail, h0, hder, Fin.sum_univ_add, hsumk, hsum3, hthree]
      rw [show covKAExt G t (k + 1) v (A 0) (A 1) (A 2) y
          = mvfderiv I (covKAExt G t k (fun i : Fin k => v i.succ) (A 0) (A 1) (A 2)) y
              (v 0 y)
            - (∑ i : Fin k, covKAExt G t k (Function.update (fun j : Fin k => v j.succ) i
                  (dirFA (G 0) (v i.succ) (v 0))) (A 0) (A 1) (A 2) y)
            - covKAExt G t k (fun i : Fin k => v i.succ)
                (dirFA (G 0) (A 0) (v 0)) (A 1) (A 2) y
            - covKAExt G t k (fun i : Fin k => v i.succ) (A 0)
                (dirFA (G 0) (A 1) (v 0)) (A 2) y
            - covKAExt G t k (fun i : Fin k => v i.succ) (A 0) (A 1)
                (dirFA (G 0) (A 2) (v 0)) y from rfl]
      ring

end Work.Diff.EXT
