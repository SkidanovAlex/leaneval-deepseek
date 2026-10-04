import Mathlib
import Submission.Work.Diff.EXT.reactDefs
import Submission.Work.Diff.GE.reaction_map_defs
import Submission.Work.Diff.GE.ReactionDefs
import Submission.Work.Diff.EXT.curvNormK_frame_indep
import Submission.Work.Diff.EXT.covKRmExt_eval_bound
import Submission.Work.EXT.lcSmooth_noBoundary

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-!
# The base case of the reaction ladder: the jets of the quadratic level-`0` reaction `Q(Rm)`

This module proves `Work.Diff.EXT.reaction0_jets`: for every `j` there is a constant `C` with

`|jetAll g j 4 (fun F y => reactionFormAt reactionMap g y (F 0 y) … (F 3 y)) G x| ≤
   C · Shape g x j · ∏ r, √(g.inner x (G r x) (G r x))`.

## The architecture

`S` is the *packed operator* of arity `4` given by the quadratic reaction `Q(Rm) = reactionMap ∘ rmC`
paired with the four slot vectors.  Its `j`-th Ext-pattern jet (`jetAll`) is the `j`-th covariant
derivative of the `(0,4)`-tensor field `y ↦ 𝔅(Rm_y, Rm_y)`, where `𝔅 = reactionBilin` is the
polarized bilinear form of `reactionMap`.  Since `𝔅` is built from the metric alone (it is
*parallel*), the Leibniz rule gives

`∇^j 𝔅(Rm, Rm) = Σ_{a+b=j} Σ_{distributions} 𝔅(∇^a Rm, ∇^b Rm)`,

and the value of the `a`-th factor on the `j` vector arguments is a component of the universal
tower `ckt g a` (`TowerArr`).  The bound then follows from the componentwise Cauchy–Schwarz
estimates `|∇^a Rm| ≤ √(curvNormK g x a)` and `√f_a √f_b ≤ Shape g x (a+b)`.

Everything is phrased in terms of the two objects `TowerArr` (the components of `∇^a Rm` in a frame,
as an array-valued function) and `MonoOp` (a monomial: the contraction of the two tower arrays with
the four slot pairings), so the induction is a statement about finitely many "monomial shapes".
-/

/-! ## The polarized bilinear form of the quadratic reaction -/

/-- **The polarized bilinear form** of the quadratic map `reactionMap`: the symmetric bilinear map
`𝔅` with `𝔅(R,R) = reactionMap R`.  It is *parallel* (built from the metric alone), which is what
makes the Leibniz rule `∇𝔅(T,T) = 𝔅(∇T,T) + 𝔅(T,∇T)` available. -/
noncomputable def reactionBilin {n : ℕ} (X Y : Curv4 n) : Curv4 n :=
  fun i j k l => (Work.Diff.GE.reactionMap (X + Y) i j k l - Work.Diff.GE.reactionMap X i j k l - Work.Diff.GE.reactionMap Y i j k l) / 2

/-- **The polarization data of `reactionMap`**: the expression obtained from the defining formula of
`reactionMap` by putting `X` into every "left" factor and `Y` into every "right" factor.  It is a
bilinear form on curvature arrays, and `rmPair Z Z = reactionMap Z` *by definition*. -/
noncomputable def rmPair {n : ℕ} (X Y : Curv4 n) : Curv4 n := fun i j k l =>
  (∑ p, ∑ q, (X i j p q * Y k l p q + 2 * X i p k q * Y j p l q - 2 * X i p l q * Y j p k q))
    - ∑ p, (Work.Diff.GE.ricF X i p * Y p j k l + Work.Diff.GE.ricF X j p * Y i p k l
            + Work.Diff.GE.ricF X l p * Y i j k p + Work.Diff.GE.ricF X k p * Y i j p l)

/-- **The symmetrized polarization** `rmSym X Y = (rmPair X Y + rmPair Y X)/2`; it is bilinear and
`rmSym X X = reactionMap X`.  It is the form in which the reaction is used below (so that the
product rule `∇(rmSym(u,v)) = rmSym(∇u,v) + rmSym(u,∇v)` is available). -/
noncomputable def rmSym {n : ℕ} (X Y : Curv4 n) : Curv4 n := fun i j k l =>
  (rmPair X Y i j k l + rmPair Y X i j k l) / 2

/-- `rmPair Z Z = reactionMap Z`, definitionally (the two sides are the same expression). -/
theorem rmPair_self {n : ℕ} (Z : Curv4 n) : rmPair Z Z = Work.Diff.GE.reactionMap Z := rfl

/-- `rmSym Z Z = reactionMap Z`. -/
theorem rmSym_self {n : ℕ} (Z : Curv4 n) : rmSym Z Z = Work.Diff.GE.reactionMap Z := by
  funext i j k l
  simp only [rmSym, Work.Diff.GE.reactionMap, Submission.Diff.Alg.Q, rmPair, Work.Diff.GE.ricF]
  ring

/-! ## Bilinearity of `rmPair` and the polarization identity -/

theorem sum2_add {n : ℕ} (f g : Fin n → Fin n → ℝ) :
    (∑ p, ∑ q, (f p q + g p q)) = (∑ p, ∑ q, f p q) + ∑ p, ∑ q, g p q := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun p _ => by rw [← Finset.sum_add_distrib])

theorem sum1_add {n : ℕ} (f g : Fin n → ℝ) :
    (∑ p, (f p + g p)) = (∑ p, f p) + ∑ p, g p := Finset.sum_add_distrib

theorem ricF_add {n : ℕ} (X₁ X₂ : Curv4 n) :
    Work.Diff.GE.ricF (X₁ + X₂) = Work.Diff.GE.ricF X₁ + Work.Diff.GE.ricF X₂ := by
  funext i p
  simp only [Work.Diff.GE.ricF, Pi.add_apply, Finset.sum_add_distrib]

/-- `rmPair` is additive in its first argument. -/
theorem rmPair_add_left {n : ℕ} (X₁ X₂ Y : Curv4 n) :
    rmPair (X₁ + X₂) Y = rmPair X₁ Y + rmPair X₂ Y := by
  funext i j k l
  have h1 : (∑ p, ∑ q, ((X₁ i j p q + X₂ i j p q) * Y k l p q
        + 2 * (X₁ i p k q + X₂ i p k q) * Y j p l q
        - 2 * (X₁ i p l q + X₂ i p l q) * Y j p k q))
      = (∑ p, ∑ q, (X₁ i j p q * Y k l p q + 2 * X₁ i p k q * Y j p l q - 2 * X₁ i p l q * Y j p k q))
        + (∑ p, ∑ q, (X₂ i j p q * Y k l p q + 2 * X₂ i p k q * Y j p l q - 2 * X₂ i p l q * Y j p k q)) := by
    rw [← sum2_add]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    ring
  have h2 : (∑ p, (Work.Diff.GE.ricF (X₁ + X₂) i p * Y p j k l
        + Work.Diff.GE.ricF (X₁ + X₂) j p * Y i p k l
        + Work.Diff.GE.ricF (X₁ + X₂) l p * Y i j k p
        + Work.Diff.GE.ricF (X₁ + X₂) k p * Y i j p l))
      = (∑ p, (Work.Diff.GE.ricF X₁ i p * Y p j k l + Work.Diff.GE.ricF X₁ j p * Y i p k l
        + Work.Diff.GE.ricF X₁ l p * Y i j k p + Work.Diff.GE.ricF X₁ k p * Y i j p l))
        + (∑ p, (Work.Diff.GE.ricF X₂ i p * Y p j k l + Work.Diff.GE.ricF X₂ j p * Y i p k l
        + Work.Diff.GE.ricF X₂ l p * Y i j k p + Work.Diff.GE.ricF X₂ k p * Y i j p l)) := by
    rw [← sum1_add]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [ricF_add]
    simp only [Pi.add_apply]
    ring
  simp only [rmPair, Pi.add_apply]
  rw [h1, h2]
  ring

/-- `rmPair` is additive in its second argument. -/
theorem rmPair_add_right {n : ℕ} (X Y₁ Y₂ : Curv4 n) :
    rmPair X (Y₁ + Y₂) = rmPair X Y₁ + rmPair X Y₂ := by
  funext i j k l
  have h1 : (∑ p, ∑ q, (X i j p q * (Y₁ k l p q + Y₂ k l p q)
        + 2 * X i p k q * (Y₁ j p l q + Y₂ j p l q)
        - 2 * X i p l q * (Y₁ j p k q + Y₂ j p k q)))
      = (∑ p, ∑ q, (X i j p q * Y₁ k l p q + 2 * X i p k q * Y₁ j p l q - 2 * X i p l q * Y₁ j p k q))
        + (∑ p, ∑ q, (X i j p q * Y₂ k l p q + 2 * X i p k q * Y₂ j p l q - 2 * X i p l q * Y₂ j p k q)) := by
    rw [← sum2_add]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    ring
  have h2 : (∑ p, (Work.Diff.GE.ricF X i p * (Y₁ p j k l + Y₂ p j k l)
        + Work.Diff.GE.ricF X j p * (Y₁ i p k l + Y₂ i p k l)
        + Work.Diff.GE.ricF X l p * (Y₁ i j k p + Y₂ i j k p)
        + Work.Diff.GE.ricF X k p * (Y₁ i j p l + Y₂ i j p l)))
      = (∑ p, (Work.Diff.GE.ricF X i p * Y₁ p j k l + Work.Diff.GE.ricF X j p * Y₁ i p k l
        + Work.Diff.GE.ricF X l p * Y₁ i j k p + Work.Diff.GE.ricF X k p * Y₁ i j p l))
        + (∑ p, (Work.Diff.GE.ricF X i p * Y₂ p j k l + Work.Diff.GE.ricF X j p * Y₂ i p k l
        + Work.Diff.GE.ricF X l p * Y₂ i j k p + Work.Diff.GE.ricF X k p * Y₂ i j p l)) := by
    rw [← sum1_add]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    ring
  simp only [rmPair, Pi.add_apply]
  rw [h1, h2]
  ring

/-- `rmSym` is symmetric. -/
theorem rmSym_comm {n : ℕ} (X Y : Curv4 n) : rmSym X Y = rmSym Y X := by
  funext i j k l
  simp only [rmSym]
  ring

/-- `rmSym` is the polarized bilinear form of `reactionMap`, i.e. it agrees with `reactionBilin`:
this follows from the bilinearity of `rmPair` and the identity `rmPair Z Z = reactionMap Z`. -/
theorem rmSym_eq_reactionBilin {n : ℕ} (X Y : Curv4 n) :
    rmSym X Y = reactionBilin X Y := by
  have h1 : rmPair (X + Y) (X + Y) = rmPair X X + rmPair X Y + rmPair Y X + rmPair Y Y := by
    funext i j k l
    rw [rmPair_add_left, rmPair_add_right, rmPair_add_right]
    simp only [Pi.add_apply]
    ring
  funext i j k l
  have h2 := congrFun (congrFun (congrFun (congrFun h1 i) j) k) l
  show (rmPair X Y i j k l + rmPair Y X i j k l) / 2
      = (rmPair (X + Y) (X + Y) i j k l - rmPair X X i j k l - rmPair Y Y i j k l) / 2
  rw [h2]
  simp only [Pi.add_apply]
  ring

/-- The tower array `∇^a Rm` in the frame `e`, as an array-valued function of the base point: its
`(i,j,k,l)`-entry is the `(i,j,k,l)`-component of `∇^a Rm` in the frame `e`, namely
`ckt g a (dirs ++ ![e i, e j, e l, e k])` (the four frame fields fill the four curvature slots of the
tower, in the `rmFrame` index convention). -/
noncomputable def TowerArr (g : SMet I M) (a : ℕ) (dirs : Fin a → TField (I := I) (M := M))
    (e : Fin (Module.finrank ℝ E) → TField (I := I) (M := M)) (y : M) : Curv4 (Module.finrank ℝ E) :=
  fun i j k l => ckt g a (Fin.append dirs ![e i, e j, e k, e l]) y

/-- **A monomial of level `(a,b)`.**  The data are the two tower levels `a`, `b` and the assignment
of the `a+b+4` tuple entries: the first `a` entries (through `dirs₁`) are the differentiation
directions of the first `∇^a Rm`-factor, the next `b` entries (`dirs₂`) those of the second factor,
and the last four are the vectors of the four slot pairings.  The value is the contraction of
`reactionBilin (∇^a Rm) (∇^b Rm)` with the four pairings, each frame index being paired with the
corresponding slot vector. -/
noncomputable def MonoOp (g : SMet I M) (a b : ℕ)
    (dirs₁ : Fin a → Fin (a + b + 4)) (dirs₂ : Fin b → Fin (a + b + 4))
    (e : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (F : Fin (a + b + 4) → TField (I := I) (M := M)) (y : M) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    reactionBilin (TowerArr g a (fun r => F (dirs₁ r)) e y)
      (TowerArr g b (fun r => F (dirs₂ r)) e y) i j k l
      * (g.inner y (e i y) (F (Fin.natAdd (a + b) 0) y)
        * g.inner y (e j y) (F (Fin.natAdd (a + b) 1) y)
        * g.inner y (e k y) (F (Fin.natAdd (a + b) 2) y)
        * g.inner y (e l y) (F (Fin.natAdd (a + b) 3) y))

/-- The array of components of `∇^a Rm` at `x` in the frame `e`, with the differentiation
directions `d` fixed (`KptArr` is the point-level form of `TowerArr`). -/
noncomputable def KptArr (g : SMet I M) (x : M) (a : ℕ)
    (d : Fin a → TangentSpace I x) (e : Fin (Module.finrank ℝ E) → TangentSpace I x) :
    Curv4 (Module.finrank ℝ E) :=
  fun i j k l => Kpt g x a (Fin.append d ![e i, e j, e k, e l])

/-- **The monomial of level `(a,b)` on a tuple of arity `N`.**

This is the *frame-based* form of one term of the Leibniz expansion of `∇^j (𝔅(Rm,Rm))`: the
contraction of `𝔅(∇^a Rm, ∇^b Rm)` (evaluated in the frame `e` on the direction fields selected by
`d₁` and `d₂`) with the four slot pairings against the fields selected by `s`.

The three index maps `d₁ : Fin a → Fin N`, `d₂ : Fin b → Fin N`, `s : Fin 4 → Fin N` say which
entry of the tuple `F : Fin N → TField` provides which slot of the monomial.  In the applications
`N = a + b + 4`, the three maps are injective with pairwise disjoint images covering `Fin N`, so
that `F` is a partition of the tuple into (the `a` directions of the first factor, the `b`
directions of the second factor, the four slot vectors). -/
noncomputable def MonoD (g : SMet I M) (N : ℕ) (a b : ℕ)
    (d₁ : Fin a → Fin N) (d₂ : Fin b → Fin N) (s : Fin 4 → Fin N)
    (e : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (F : Fin N → TField (I := I) (M := M)) (y : M) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    rmSym (TowerArr g a (fun r => F (d₁ r)) e y)
      (TowerArr g b (fun r => F (d₂ r)) e y) i j k l
      * (g.inner y (e i y) (F (s 0) y) * g.inner y (e j y) (F (s 1) y)
        * g.inner y (e k y) (F (s 2) y) * g.inner y (e l y) (F (s 3) y))

/-! ## The sharp evaluation bound for the tower -/

/-- **The sharp evaluation bound** for the tower `∇^k Rm`: the value of `∇^k Rm` at `x` on
`k + 4` tangent vectors is bounded by the square root of the Frobenius norm `curvNormK` times the
product of the `g`-norms of the vectors.  (This is the sharp form, without the `1 + √f` slack of
`covKRmExt_eval_bound`; it is what makes the target bound meaningful when `Shape` vanishes.) -/
theorem Kpt_norm_bound (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (x : M) (k : ℕ) (w : Fin (k + 4) → TangentSpace I x) :
    |Kpt g x k w| ≤ Real.sqrt (curvNormK g x k)
      * ∏ r : Fin (k + 4), Real.sqrt (g.inner x (w r) (w r)) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hone : Orthonormal ℝ (onFrame g x) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [show inner ℝ (onFrame g x i) (onFrame g x j)
        = g.inner x (onFrame g x i) (onFrame g x j) from rfl]
    exact Work.Diff.GE.isONFrame_onFrame g x i j
  have hb := multilinear_frame_bound (N := k + 4) (by omega) (KptLin hLC g x k)
    (onFrame g x) hone w
  have hb' : |Kpt g x k w| ≤ Real.sqrt
        (∑ w' : Fin (k + 4) → Fin (Module.finrank ℝ E),
          (Kpt g x k (fun s => onFrame g x (w' s))) ^ 2)
      * ∏ s : Fin (k + 4), Real.sqrt (inner ℝ (w s) (w s)) := by
    exact hb
  rw [Kpt_component_sum g x k] at hb'
  have hprod : (∏ s : Fin (k + 4), Real.sqrt (inner ℝ (w s) (w s)))
      = ∏ s : Fin (k + 4), Real.sqrt (g.inner x (w s) (w s)) :=
    Finset.prod_congr rfl fun s _ => by
      rw [show inner ℝ (w s) (w s) = g.inner x (w s) (w s) from rfl]
  rw [hprod] at hb'
  exact hb'

/-- **Cauchy–Schwarz** for the metric pairing: `|⟪u,v⟫| ≤ ‖u‖ ‖v‖`. -/
theorem inner_pairing_bound (g : Submission.Diff.SMet I M) (x : M) (u v : TangentSpace I x) :
    |g.inner x u v| ≤ Real.sqrt (g.inner x u u) * Real.sqrt (g.inner x v v) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  calc |g.inner x u v| = |inner ℝ u v| := rfl
    _ ≤ ‖u‖ * ‖v‖ := abs_real_inner_le_norm u v
    _ = Real.sqrt (inner ℝ u u) * Real.sqrt (inner ℝ v v) := by
        rw [norm_eq_sqrt_real_inner u, norm_eq_sqrt_real_inner v]
    _ = Real.sqrt (g.inner x u u) * Real.sqrt (g.inner x v v) := rfl

/-- The recursion of the tower, in the form used by the Ext pattern: the derivative of a component
of `∇^k Rm` along the field `X` is the next tower level plus the slot corrections. -/
theorem mvfderiv_ckt_T2 (g : Submission.Diff.SMet I M) (k : ℕ)
    (F : Fin (k + 4) → TField (I := I) (M := M)) (X : TField (I := I) (M := M)) (x : M) :
    mvfderiv I (fun y : M => ckt g k F y) x (X x)
      = ckt g (k + 1) (Fin.cons X F) x
        + ∑ s : Fin (k + 4), ckt g k (Function.update F s (dirF g (F s) X)) x := by
  have h := congrFun (ckt_succ g k (Fin.cons X F)) x
  simp only [Finset.sum_apply, Pi.sub_apply, Fin.cons_zero, Fin.cons_succ] at h
  rw [h]; ring

/-- If a slot of the tuple vanishes at `x`, the tower component vanishes at `x`. -/
theorem ckt_zero_slot_T2 (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (k : ℕ) {F : Fin (k + 4) → TField (I := I) (M := M)}
    (hF : ∀ s, SmoothF (F s)) (s : Fin (k + 4)) (x : M)
    {Y : TField (I := I) (M := M)} (hY : SmoothF Y) (hYx : Y x = 0) :
    ckt g k (Function.update F s Y) x = 0 := by
  have h1 : ckt g k (Function.update F s Y) x
      = ckt g k (Function.update F s (0 : TField (I := I) (M := M))) x :=
    ckt_val_dep hLC g k x hF s hY Work.Diff.GE.cmDiff_zeroField (by simpa using hYx)
  have h2 : ckt g k (Function.update F s (0 : TField (I := I) (M := M))) x = 0 := by
    have h := TensProp_smul hLC g (tensProp_all hLC g k) (F := F) hF s (0 : ℝ) (hF s)
    have e : (fun _ : M => (0 : ℝ)) • (F s) = (0 : TField (I := I) (M := M)) := by
      funext y; simp
    rw [e, Function.update_eq_self] at h
    simpa using congrFun h x
  rw [h1, h2]

/-! ## The remaining structural steps (statements) -/

/-- **The tower array is the `Kpt`-array at the point** (value dependence of the tower): the
`ckt`-based array of `∇^a Rm` in the frame fields `e`, evaluated at `y`, is the frame-component array
`KptArr` computed from the values of the fields at `y`. -/
theorem TowerArr_eq_KptArr (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (a : ℕ) (dirs : Fin a → TField (I := I) (M := M))
    (hdirs : ∀ r, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (dirs r))
    (e : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (he : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e i)) (y : M) :
    TowerArr g a dirs e y = KptArr g y a (fun r => dirs r y) (fun i => e i y) := by
  funext i j k l
  simp only [TowerArr, KptArr, Kpt]
  refine ckt_val_dep_all (I := I) (M := M) hLC g a y ?_ ?_ ?_
  · intro s
    refine Fin.addCases ?_ ?_ s
    · intro r
      rw [Fin.append_left]
      exact hdirs r
    · intro t
      rw [Fin.append_right]
      fin_cases t
      · simpa using he i
      · simpa using he j
      · simpa using he k
      · simpa using he l
  · intro s
    exact Work.Diff.GE.smoothExt_cmdiff y _
  · intro s
    refine Fin.addCases ?_ ?_ s
    · intro r
      rw [Fin.append_left, Fin.append_left, Work.Diff.GE.smoothExt_apply]
    · intro t
      rw [Fin.append_right, Fin.append_right, Work.Diff.GE.smoothExt_apply]
      fin_cases t <;> rfl


/-! ## The combinatorial bookkeeping of the monomial decomposition -/

/-- The four slot positions of the tuple of arity `4 + j`: the last four entries. -/
def slotS (j : ℕ) : Fin 4 → Fin (4 + j) := fun t => ⟨j + (t : ℕ), by omega⟩

lemma slotS_succ (j : ℕ) : slotS (j + 1) = fun t => (slotS j t).succ := by
  funext t
  refine Fin.ext ?_
  simp only [slotS, Fin.val_succ]
  omega

/-- **The bookkeeping of the monomial decomposition.**  For a word `f : Fin j → Bool` (which says,
for each of the `j` differentiation directions of the `j`-th jet, whether it was attributed to the
first or to the second factor of the quadratic reaction), `fam j f` is the data of the monomial of
level `(|f⁻¹ true|, |f⁻¹ false|)`: the number and the index-assignment of the directions of each of
the two factors.  It is defined by recursion on `j`, the *new* direction (the entry `0` of the tuple
at level `j+1`) being put *first* among the directions of the factor chosen by `f 0`. -/
noncomputable def fam : ∀ (j : ℕ), (Fin j → Bool) →
    (Σ a : ℕ, Fin a → Fin (4 + j)) × (Σ b : ℕ, Fin b → Fin (4 + j))
  | 0, _ => (⟨0, Fin.elim0⟩, ⟨0, Fin.elim0⟩)
  | (j + 1), f =>
    let p := fam j (Fin.tail f)
    match f 0 with
    | true => (⟨p.1.1 + 1, Fin.cons 0 (fun r : Fin p.1.1 => (p.1.2 r).succ)⟩,
              ⟨p.2.1, fun r => (p.2.2 r).succ⟩)
    | false => (⟨p.1.1, fun r => (p.1.2 r).succ⟩,
               ⟨p.2.1 + 1, Fin.cons 0 (fun r : Fin p.2.1 => (p.2.2 r).succ)⟩)

/-- The monomial attached to a word `f`: the level-`(a,b)` monomial `MonoD` with the direction
assignments `fam j f` and the four slots the last four entries of the tuple. -/
noncomputable def MonoF (g : SMet I M) (j : ℕ) (f : Fin j → Bool)
    (e : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (F : Fin (4 + j) → TField (I := I) (M := M)) (y : M) : ℝ :=
  MonoD (I := I) (M := M) g (4 + j) (fam j f).1.1 (fam j f).2.1 (fam j f).1.2 (fam j f).2.2
    (slotS j) e F y

lemma fam_len : ∀ (j : ℕ) (f : Fin j → Bool), (fam j f).1.1 + (fam j f).2.1 = j := by
  intro j
  induction j with
  | zero => intro f; rfl
  | succ j ih =>
    intro f
    cases hf : f 0
    · simp only [fam, hf]
      have := ih (Fin.tail f)
      omega
    · simp only [fam, hf]
      have := ih (Fin.tail f)
      omega

lemma fam_cons_true : ∀ (j : ℕ) (f : Fin j → Bool),
    fam (j + 1) (Fin.cons true f)
      = (⟨(fam j f).1.1 + 1, Fin.cons 0 (fun r : Fin (fam j f).1.1 => ((fam j f).1.2 r).succ)⟩,
         ⟨(fam j f).2.1, fun r => ((fam j f).2.2 r).succ⟩) := by
  intro j f
  have ht : Fin.tail (Fin.cons true f : Fin (j + 1) → Bool) = f := by
    funext i; rfl
  simp only [fam, Fin.cons_zero]
  rw [ht]

lemma fam_cons_false : ∀ (j : ℕ) (f : Fin j → Bool),
    fam (j + 1) (Fin.cons false f)
      = (⟨(fam j f).1.1, fun r => ((fam j f).1.2 r).succ⟩,
         ⟨(fam j f).2.1 + 1, Fin.cons 0 (fun r : Fin (fam j f).2.1 => ((fam j f).2.2 r).succ)⟩) := by
  intro j f
  have ht : Fin.tail (Fin.cons false f : Fin (j + 1) → Bool) = f := by
    funext i; rfl
  simp only [fam, Fin.cons_zero]
  rw [ht]

end Work.Diff.EXT
