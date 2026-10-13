/-
  WilG4c / SubstCharts.

  Chart transfer along a *parameter* substitution.  Given

  * `θ : ℝ^q → ℝ^p` and `μ : ℝ^p → ℝ^q` with `θ (μ l) = l` for `l ∈ Λ` (so `μ` is a section of
    `θ` over `Λ`),
  * a finite family `Φ` of charts for the pulled-back family `ν ↦ F (θ ν)` over the parameter
    region `{ν | θ ν ∈ Λ}` (in the sense of `ChartsOK`),

  one obtains a finite family `Φ'` of charts for `F` over `Λ`, without increasing the number of
  charts, by composing every chart of `Φ` with `μ`.  The `Ω`-condition on the substituted chart
  graphs is the composition `famGraph_paramSubst` below; the remaining conditions
  (cube-into-cube, `C^r`-regularity and unit derivative norms) transfer verbatim because
  `θ (μ l) = l`, and the `ε`-cover transfers for the same reason.

  The format/degree bookkeeping is linear in the input data: the format grows additively and the
  new degree is `(Dμ + 1) (p + q + n + 1) + (q + n + 1) Dg + c'` (all the multiplicative
  constants are absorbed in `c'`, which is chosen once and for all).

  The `Ω`-calculus machinery used here (closure under coordinate substitution and under the
  rectangular composition of graphs) is developed in the `SC` namespace below from the
  `Work.WilG0` substitution toolkit; it is self-contained and does not depend on the
  `Work.WilkG4c.GraphComp` layer.
-/
import Mathlib
import Submission.Work.WilG4c.FLemAPI
import Submission.Work.WilG4c.ParamChartsOK
import Submission.Work.WilG0.Defs
import Submission.Work.WilG0.API
import Submission.Work.WilG0.liftNM_mem
import Submission.Work.WilG0.liftNM_eq_cast
import Submission.Work.WilG0.diagSet_mem
import Submission.Work.WilG0.projLastIter_mem
import Submission.Work.WilG0.projLastIter_eq
import Submission.Work.WilG0.snocIt_natAdd
import Submission.Work.WilG0.snocIt_castAdd

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 0. The two `Ω`-calculus lemmas used: substitution and rectangular graph composition

These are self-contained copies of `GraphComp.subst_mem` and `graphOfCompGen`, built on the
resolvable `Work.WilG0` substitution toolkit (`snocIt`, `projLastIter`, `substSet_mem`, ...). -/

namespace SC

/-! ### 0.1 Closure of `Ω` under coordinate substitution -/

/-- The membership fact for the glued vector in the trailing block. -/
theorem snocIt_mem_liftNM {m : ℕ} {A : Set (Fin m → ℝ)} (n : ℕ) (ι : Fin m → Fin n)
    (x : Fin n → ℝ) (w : Fin m → ℝ) :
    Work.WilG0.snocIt n m x w ∈ Work.WilG0.liftNM n m A ↔ w ∈ A := by
  rw [Work.WilG0.liftNM, Set.mem_ofPred_eq]
  constructor
  · intro h
    rwa [show (fun j : Fin m => Work.WilG0.snocIt n m x w (Fin.natAdd n j)) = w from
      funext fun j => Work.WilG0.snocIt_natAdd n m x w j] at h
  · intro h
    rwa [show (fun j : Fin m => Work.WilG0.snocIt n m x w (Fin.natAdd n j)) = w from
      funext fun j => Work.WilG0.snocIt_natAdd n m x w j]

/-- The membership fact for the glued vector in the diagonal set. -/
theorem snocIt_mem_diagSet {m : ℕ} (n : ℕ) (ι : Fin m → Fin n) (x : Fin n → ℝ)
    (w : Fin m → ℝ) :
    Work.WilG0.snocIt n m x w ∈ Work.WilG0.diagSet n m ι ↔ x ∘ ι = w := by
  rw [Work.WilG0.diagSet, Set.mem_ofPred_eq]
  constructor
  · intro h
    funext j
    have h' := h j
    rw [Work.WilG0.snocIt_natAdd n m x w j, Work.WilG0.snocIt_castAdd n m x w (ι j)] at h'
    exact h'.symm
  · intro h j
    rw [Work.WilG0.snocIt_natAdd n m x w j, Work.WilG0.snocIt_castAdd n m x w (ι j)]
    exact congrFun h.symm j

/-- **The substitution atom.** If `A ⊆ ℝ^m` is in `Ω F D`, then for every `ι : Fin m → Fin n`
the pullback `{x | x ∘ ι ∈ A}` is in `Ω (max (F+n) (n+m) + 1 + m + n) (D+2)`. -/
theorem substSet_mem (S : SOMin) {m F D : ℕ} {A : Set (Fin m → ℝ)} (hA : A ∈ S.Ω F D m)
    (n : ℕ) (ι : Fin m → Fin n) :
    {x : Fin n → ℝ | x ∘ ι ∈ A} ∈
      S.Ω (max (F + n) (n + m) + 1 + m + n) (D + 2) n := by
  have hL : Work.WilG0.liftNM n m A ∈ S.Ω (max (F + n) (n + m)) D (n + m) :=
    Work.WilG0.Omega_mono_F (le_max_left _ _) (Work.WilG0.liftNM_mem hA n)
  have hE : Work.WilG0.diagSet n m ι ∈ S.Ω (max (F + n) (n + m)) 2 (n + m) :=
    Work.WilG0.Omega_mono_F (le_max_right _ _) (Work.WilG0.diagSet_mem S n m ι)
  have hI : Work.WilG0.liftNM n m A ∩ Work.WilG0.diagSet n m ι ∈
      S.Ω (max (F + n) (n + m) + 1) (D + 2) (n + m) :=
    Work.WilG0.Omega_inter2 hL hE
  have hP : Work.WilG0.projLastIter n m (Work.WilG0.liftNM n m A ∩ Work.WilG0.diagSet n m ι) ∈
      S.Ω (max (F + n) (n + m) + 1 + m + n) (D + 2) n :=
    Work.WilG0.projLastIter_mem S n m (max (F + n) (n + m) + 1) (D + 2) _ hI
  have hset : Work.WilG0.projLastIter n m
        (Work.WilG0.liftNM n m A ∩ Work.WilG0.diagSet n m ι) =
      {x : Fin n → ℝ | x ∘ ι ∈ A} := by
    rw [Work.WilG0.projLastIter_eq]
    ext x
    constructor
    · rintro ⟨w, hw⟩
      have h1 : w ∈ A := (snocIt_mem_liftNM n ι x w).mp hw.1
      have h2 : x ∘ ι = w := (snocIt_mem_diagSet n ι x w).mp hw.2
      show x ∘ ι ∈ A
      rw [h2]
      exact h1
    · intro hx
      refine ⟨x ∘ ι, ?_, ?_⟩
      · exact (snocIt_mem_liftNM n ι x (x ∘ ι)).mpr hx
      · exact (snocIt_mem_diagSet n ι x (x ∘ ι)).mpr rfl
  rw [hset] at hP
  exact hP

/-- If `A ⊆ ℝ^m` is `Ω F D m` and `σ : Fin m → Fin N`, then `{x : ℝ^N | x ∘ σ ∈ A}` is
`Ω (F + 2*(N+m) + 1) (D+2) N`. -/
theorem ZzSubstOmega (S : WilkiesDesign.SOMin) {m N F D : ℕ} (σ : Fin m → Fin N)
    {A : Set (Fin m → ℝ)} (hA : A ∈ S.Ω F D m) :
    {x : Fin N → ℝ | x ∘ σ ∈ A} ∈ S.Ω (F + 2 * (N + m) + 1) (D + 2) N := by
  have h := substSet_mem S hA N σ
  exact Work.WilG0.Omega_mono_F (by omega) h

/-! ### 0.2 The rectangular composition of graphs -/

/-- In `ℝ^{(M+1)+m}` with layout `(x, t, w)`, the substitution selecting `(w, t)`. -/
def sigGGen (M m : ℕ) : Fin (m + 1) → Fin ((M + 1) + m) :=
  Fin.snoc (fun j : Fin m => Fin.natAdd (M + 1) j) (Fin.castAdd m (Fin.last M))

/-- In `ℝ^{(M+1)+m}` with layout `(x, t, w)`, the substitution selecting `(x, w_j)`. -/
def sigPhiGen (M m : ℕ) (j : Fin m) : Fin (M + 1) → Fin ((M + 1) + m) :=
  Fin.snoc (fun i : Fin M => Fin.castAdd m (Fin.castSucc i)) (Fin.natAdd (M + 1) j)

@[simp] theorem sigGGen_last (M m : ℕ) :
    sigGGen M m (Fin.last m) = Fin.castAdd m (Fin.last M) := by
  simp [sigGGen]

@[simp] theorem sigGGen_castSucc (M m : ℕ) (j : Fin m) :
    sigGGen M m (Fin.castSucc j) = Fin.natAdd (M + 1) j := by
  simp [sigGGen]

@[simp] theorem sigPhiGen_last (M m : ℕ) (j : Fin m) :
    sigPhiGen M m j (Fin.last M) = Fin.natAdd (M + 1) j := by
  simp [sigPhiGen]

@[simp] theorem sigPhiGen_castSucc (M m : ℕ) (j : Fin m) (i : Fin M) :
    sigPhiGen M m j (Fin.castSucc i) = Fin.castAdd m (Fin.castSucc i) := by
  simp [sigPhiGen]

/-- The pullback of `graphOf g` under `sigGGen`. -/
def setGGen (M m : ℕ) (g : (Fin m → ℝ) → ℝ) : Set (Fin ((M + 1) + m) → ℝ) :=
  {z | z ∘ sigGGen M m ∈ graphOf g}

/-- The pullback of `graphOf (φ · j)` under `sigPhiGen`. -/
def setHGen (M m : ℕ) (φ : (Fin M → ℝ) → (Fin m → ℝ)) (j : Fin m) :
    Set (Fin ((M + 1) + m) → ℝ) :=
  {z | z ∘ sigPhiGen M m j ∈ graphOf (fun x : Fin M → ℝ => φ x j)}

theorem snocIt_sigGGen (M m : ℕ) (x : Fin (M + 1) → ℝ) (w : Fin m → ℝ) :
    Work.WilG0.snocIt (M + 1) m x w ∘ sigGGen M m = Fin.snoc w (x (Fin.last M)) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [Function.comp_apply, sigGGen_last, Work.WilG0.snocIt_castAdd, Fin.snoc_last]
  · intro j
    rw [Function.comp_apply, sigGGen_castSucc, Work.WilG0.snocIt_natAdd, Fin.snoc_castSucc]

theorem snocIt_sigPhiGen (M m : ℕ) (j : Fin m) (x : Fin (M + 1) → ℝ) (w : Fin m → ℝ) :
    Work.WilG0.snocIt (M + 1) m x w ∘ sigPhiGen M m j = Fin.snoc (Fin.init x) (w j) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [Function.comp_apply, sigPhiGen_last, Work.WilG0.snocIt_natAdd, Fin.snoc_last]
  · intro i
    rw [Function.comp_apply, sigPhiGen_castSucc, Work.WilG0.snocIt_castAdd, Fin.snoc_castSucc]
    simp [Fin.init]

theorem mem_setGGen {M m : ℕ} (g : (Fin m → ℝ) → ℝ) (x : Fin (M + 1) → ℝ) (w : Fin m → ℝ) :
    Work.WilG0.snocIt (M + 1) m x w ∈ setGGen M m g ↔ x (Fin.last M) = g w := by
  change (Work.WilG0.snocIt (M + 1) m x w ∘ sigGGen M m) ∈ graphOf g ↔ x (Fin.last M) = g w
  rw [snocIt_sigGGen]
  simp [graphOf]

theorem mem_setHGen {M m : ℕ} (φ : (Fin M → ℝ) → (Fin m → ℝ)) (j : Fin m)
    (x : Fin (M + 1) → ℝ) (w : Fin m → ℝ) :
    Work.WilG0.snocIt (M + 1) m x w ∈ setHGen M m φ j ↔ w j = φ (Fin.init x) j := by
  change (Work.WilG0.snocIt (M + 1) m x w ∘ sigPhiGen M m j) ∈
    graphOf (fun x : Fin M → ℝ => φ x j) ↔ w j = φ (Fin.init x) j
  rw [snocIt_sigPhiGen]
  simp [graphOf]

/-- The projection of the intersection is the graph of the composite. -/
theorem projLastIter_setGGen_inter (M m : ℕ) (g : (Fin m → ℝ) → ℝ)
    (φ : (Fin M → ℝ) → (Fin m → ℝ)) :
    Work.WilG0.projLastIter (M + 1) m (setGGen M m g ∩ ⋂ j : Fin m, setHGen M m φ j) =
      graphOf (g ∘ φ) := by
  rw [Work.WilG0.projLastIter_eq]
  ext x
  constructor
  · rintro ⟨w, hw⟩
    rw [Set.mem_inter_iff] at hw
    obtain ⟨hGm, hHm⟩ := hw
    rw [Set.mem_iInter] at hHm
    have hlast : x (Fin.last M) = g w := (mem_setGGen g x w).mp hGm
    have hwx : w = φ (Fin.init x) := by
      funext j
      exact (mem_setHGen φ j x w).mp (hHm j)
    rw [hwx] at hlast
    simpa [graphOf, Function.comp_def] using hlast
  · intro hx
    have hx' : x (Fin.last M) = g (φ (Fin.init x)) := by
      simpa [graphOf, Function.comp_def] using hx
    refine ⟨φ (Fin.init x), ?_⟩
    rw [Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨(mem_setGGen g x (φ (Fin.init x))).mpr hx',
      fun j => (mem_setHGen φ j x (φ (Fin.init x))).mpr rfl⟩

/-- **Composition of `Ω`-definable maps, rectangular case.**  If the graph of `g : ℝ^m → ℝ` and
the `m` coordinate graphs of `φ : ℝ^M → ℝ^m` are `Ω`-definable, then so is the graph of the
composite, with format and degree bounded by sums of the given formats/degrees plus constants
depending only on `m` and `M`. -/
theorem ZzGraphCompRect (S : WilkiesDesign.SOMin) (m M : ℕ)
    (hsubst : ∀ {m' N F D : ℕ} (σ : Fin m' → Fin N) {A : Set (Fin m' → ℝ)},
      A ∈ S.Ω F D m' → {x : Fin N → ℝ | x ∘ σ ∈ A} ∈ S.Ω (F + 2 * (N + m') + 1) (D + 2) N) :
    ∃ (C₁ C₂ : ℕ), ∀ (F₁ F₂ D₁ D₂ : ℕ) (g : (Fin m → ℝ) → ℝ)
      (φ : (Fin M → ℝ) → (Fin m → ℝ)),
      WilkiesDesign.graphOf g ∈ S.Ω F₁ D₁ (m + 1) →
      (∀ j : Fin m, WilkiesDesign.graphOf (fun x : Fin M → ℝ => φ x j) ∈ S.Ω F₂ D₂ (M + 1)) →
      WilkiesDesign.graphOf (g ∘ φ) ∈ S.Ω (F₁ + F₂ + C₁) (D₁ + m * D₂ + C₂) (M + 1) := by
  refine ⟨2 * (((M + 1) + m) + (m + 1)) + 1 +
      (2 * (((M + 1) + m) + (M + 1)) + 1) + 1 + 1 + m + (M + 1), 2 + 2 * m, ?_⟩
  intro F₁ F₂ D₁ D₂ g φ hg hφ
  have hG : setGGen M m g ∈
      S.Ω (F₁ + 2 * (((M + 1) + m) + (m + 1)) + 1) (D₁ + 2) ((M + 1) + m) :=
    hsubst (sigGGen M m) hg
  have hH : ∀ j : Fin m, setHGen M m φ j ∈
      S.Ω (F₂ + 2 * (((M + 1) + m) + (M + 1)) + 1) (D₂ + 2) ((M + 1) + m) :=
    fun j => hsubst (sigPhiGen M m j) (hφ j)
  have hG' : setGGen M m g ∈
      S.Ω ((F₁ + 2 * (((M + 1) + m) + (m + 1)) + 1) +
        (F₂ + 2 * (((M + 1) + m) + (M + 1)) + 1)) (D₁ + 2) ((M + 1) + m) :=
    Omega_mono_le S
      (Nat.le_add_right (F₁ + 2 * (((M + 1) + m) + (m + 1)) + 1)
        (F₂ + 2 * (((M + 1) + m) + (M + 1)) + 1)) le_rfl hG
  have hH' : ∀ j : Fin m, setHGen M m φ j ∈
      S.Ω ((F₁ + 2 * (((M + 1) + m) + (m + 1)) + 1) +
        (F₂ + 2 * (((M + 1) + m) + (M + 1)) + 1)) (D₂ + 2) ((M + 1) + m) :=
    fun j => Omega_mono_le S
      (Nat.le_add_left (F₂ + 2 * (((M + 1) + m) + (M + 1)) + 1)
        (F₁ + 2 * (((M + 1) + m) + (m + 1)) + 1)) le_rfl (hH j)
  have hA2 : (⋂ j : Fin m, setHGen M m φ j) ∈
      S.Ω ((F₁ + 2 * (((M + 1) + m) + (m + 1)) + 1) +
        (F₂ + 2 * (((M + 1) + m) + (M + 1)) + 1) + 1)
        (m * (D₂ + 2)) ((M + 1) + m) := by
    have h := S.inter (F := (F₁ + 2 * (((M + 1) + m) + (m + 1)) + 1) +
        (F₂ + 2 * (((M + 1) + m) + (M + 1)) + 1))
      (n := (M + 1) + m) (D := fun _ : Fin m => D₂ + 2)
      (A := fun j : Fin m => setHGen M m φ j) hH'
    have hsum : (∑ _ : Fin m, (D₂ + 2)) = m * (D₂ + 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp
    rw [hsum] at h
    exact h
  have hG'' : setGGen M m g ∈
      S.Ω ((F₁ + 2 * (((M + 1) + m) + (m + 1)) + 1) +
        (F₂ + 2 * (((M + 1) + m) + (M + 1)) + 1) + 1) (D₁ + 2) ((M + 1) + m) :=
    Omega_mono_le S
      (Nat.le_succ ((F₁ + 2 * (((M + 1) + m) + (m + 1)) + 1) +
        (F₂ + 2 * (((M + 1) + m) + (M + 1)) + 1))) le_rfl hG'
  have hInt : (setGGen M m g ∩ ⋂ j : Fin m, setHGen M m φ j) ∈
      S.Ω (((F₁ + 2 * (((M + 1) + m) + (m + 1)) + 1) +
        (F₂ + 2 * (((M + 1) + m) + (M + 1)) + 1) + 1) + 1)
        ((D₁ + 2) + m * (D₂ + 2)) ((M + 1) + m) :=
    Work.WilG0.Omega_inter2 hG'' hA2
  have hProj : Work.WilG0.projLastIter (M + 1) m
      (setGGen M m g ∩ ⋂ j : Fin m, setHGen M m φ j) ∈
      S.Ω ((((F₁ + 2 * (((M + 1) + m) + (m + 1)) + 1) +
        (F₂ + 2 * (((M + 1) + m) + (M + 1)) + 1) + 1) + 1) + m + (M + 1))
        ((D₁ + 2) + m * (D₂ + 2)) (M + 1) :=
    Work.WilG0.projLastIter_mem S (M + 1) m
      (((F₁ + 2 * (((M + 1) + m) + (m + 1)) + 1) +
        (F₂ + 2 * (((M + 1) + m) + (M + 1)) + 1) + 1) + 1)
      ((D₁ + 2) + m * (D₂ + 2)) _ hInt
  rw [projLastIter_setGGen_inter M m g φ] at hProj
  exact Omega_mono_le S (le_of_eq (by ring)) (le_of_eq (by ring)) hProj

end SC

/-! ## 1. `famGraph` as a graph, and graphs of coordinate projections -/

/-- The "flattening" of a family member: `famGraph f = graphOf (flatFn f)`. -/
def flatFn {p m : ℕ} (f : (Fin p → ℝ) → (Fin m → ℝ) → ℝ) : (Fin (p + m) → ℝ) → ℝ :=
  fun z => f (fun i => z (Fin.castAdd m i)) (fun j => z (Fin.natAdd p j))

theorem famGraph_eq_graphOf_flatFn {p m : ℕ} (f : (Fin p → ℝ) → (Fin m → ℝ) → ℝ) :
    WilkiesDesign.CG.famGraph f = graphOf (flatFn f) := rfl

/-- The graph of a coordinate projection is `Ω`-definable with format and degree the ambient
dimension (it is the zero set of the linear equation `X_last - X_i = 0`). -/
theorem SC.graphOf_coord (S : SOMin) {N : ℕ} (i : Fin N) :
    graphOf (fun x : Fin N → ℝ => x i) ∈ S.Ω (N + 1) 1 (N + 1) := by
  have h := S.hyp (N + 1)
    (MvPolynomial.X (Fin.last N) - MvPolynomial.X (i.castSucc) : MvPolynomial (Fin (N + 1)) ℝ)
  have hdeg : (MvPolynomial.X (Fin.last N) - MvPolynomial.X (i.castSucc) :
      MvPolynomial (Fin (N + 1)) ℝ).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    rw [max_le_iff]
    exact ⟨by simp [MvPolynomial.totalDegree_X], by simp [MvPolynomial.totalDegree_X]⟩
  have hset : {x : Fin (N + 1) → ℝ | MvPolynomial.eval x
        (MvPolynomial.X (Fin.last N) - MvPolynomial.X (i.castSucc) :
          MvPolynomial (Fin (N + 1)) ℝ) = 0}
      = graphOf (fun x : Fin N → ℝ => x i) := by
    ext z
    simp only [Set.mem_ofPred_eq, graphOf, MvPolynomial.eval_sub, MvPolynomial.eval_X,
      sub_eq_zero, Fin.init]
  rw [hset] at h
  exact Omega_mono_le S le_rfl hdeg h

/-! ## 2. The two projections of `ℝ^{p+n}` -/

/-- The parameter projection `ℝ^{p+n} → ℝ^p`. -/
def paramFn (p n : ℕ) : (Fin (p + n) → ℝ) → (Fin p → ℝ) := fun z i => z (Fin.castAdd n i)

/-- The variable projection `ℝ^{p+n} → ℝ^n`. -/
def dirFn (p n : ℕ) : (Fin (p + n) → ℝ) → (Fin n → ℝ) := fun z j => z (Fin.natAdd p j)

/-! ## 3. The graphs of the substituted charts -/

/-- **The `Ω`-condition on the substituted charts.**  If the coordinate graphs of `μ : ℝ^p → ℝ^q`
are `Ω (Aμ, Dμ)`-bounded and the graphs of the chart components `χ j : ℝ^q × ℝ^n → ℝ` are
`Ω (a, Dg)`-bounded, then the graphs of the substituted charts
`(l, t) ↦ χ j (μ l) t : ℝ^p × ℝ^n → ℝ` are `Ω`-bounded with an additive format gain and a degree
gain which is linear in `(1 + Dμ)` and `(1 + Dg)`.

Construction: the substitution `(l, t) ↦ (μ l, t)` is a composition of `μ` with the parameter
projection `paramFn` (a rectangular graph composition, one for each of the `q` parameter
coordinates), and `χ j (μ l) t = flatFn (χ j) ((μ l, t))` (a second rectangular graph
composition, in the ambient dimension `q + n`). -/
theorem famGraph_paramSubst (S : SOMin) (p q n : ℕ) :
    ∃ (a' : ℕ) (c' : ℕ), ∀ (Aμ Dμ a Dg : ℕ) (μ : (Fin p → ℝ) → (Fin q → ℝ))
      (χ : Fin n → (Fin q → ℝ) → (Fin n → ℝ) → ℝ),
      (∀ j : Fin q, graphOf (fun l : Fin p → ℝ => μ l j) ∈ S.Ω Aμ Dμ (p + 1)) →
      (∀ j : Fin n, famGraph (χ j) ∈ S.Ω a Dg (q + n + 1)) →
      ∀ j : Fin n, famGraph (fun (l : Fin p → ℝ) (t : Fin n → ℝ) => χ j (μ l) t) ∈
        S.Ω (Aμ + a + a') ((Dμ + 1) * (p + q + n + 1) + (q + n + 1) * Dg + c')
          (p + n + 1) := by
  obtain ⟨C1i, C2i, hi⟩ := SC.ZzGraphCompRect S p (p + n) (@SC.ZzSubstOmega S)
  obtain ⟨C1o, C2o, ho⟩ := SC.ZzGraphCompRect S (q + n) (p + n) (@SC.ZzSubstOmega S)
  refine ⟨(p + n + 1) + C1i + C1o, (q + n) * (p + C2i + 1) + C2o, ?_⟩
  intro Aμ Dμ a Dg μ χ hμ hχ j
  -- the composite parameter map `Φ : ℝ^{p+n} → ℝ^{q+n}`
  let Φ : (Fin (p + n) → ℝ) → (Fin (q + n) → ℝ) :=
    fun z => Fin.append (fun i => μ (paramFn p n z) i) (dirFn p n z)
  have hproj : ∀ i : Fin p,
      graphOf (fun z : Fin (p + n) → ℝ => paramFn p n z i) ∈ S.Ω (p + n + 1) 1 (p + n + 1) :=
    fun i => SC.graphOf_coord S (Fin.castAdd n i)
  -- the graphs of the `q` parameter coordinates of `Φ`
  have hμp : ∀ i : Fin q,
      graphOf (fun z : Fin (p + n) → ℝ => μ (paramFn p n z) i) ∈
        S.Ω (Aμ + (p + n + 1) + C1i) (Dμ + p * 1 + C2i) (p + n + 1) :=
    fun i => hi Aμ (p + n + 1) Dμ 1 (fun l => μ l i) (paramFn p n) (hμ i) hproj
  -- unify format and degree over all `q + n` coordinates of `Φ`
  have hμp' : ∀ i : Fin q,
      graphOf (fun z : Fin (p + n) → ℝ => μ (paramFn p n z) i) ∈
        S.Ω (Aμ + (p + n + 1) + C1i) (Dμ + p * 1 + C2i + 1) (p + n + 1) :=
    fun i => Omega_mono_le S le_rfl (by omega) (hμp i)
  have hdir : ∀ k : Fin n,
      graphOf (fun z : Fin (p + n) → ℝ => dirFn p n z k) ∈
        S.Ω (Aμ + (p + n + 1) + C1i) (Dμ + p * 1 + C2i + 1) (p + n + 1) := by
    intro k
    refine Omega_mono_le S ?_ ?_ (SC.graphOf_coord S (Fin.natAdd p k))
    · omega
    · omega
  have hcoord : ∀ i : Fin (q + n),
      graphOf (fun z : Fin (p + n) → ℝ => Φ z i) ∈
        S.Ω (Aμ + (p + n + 1) + C1i) (Dμ + p * 1 + C2i + 1) (p + n + 1) := by
    intro i
    induction i using Fin.addCases with
    | left i' => simpa only [Φ, Fin.append_left] using hμp' i'
    | right k => simpa only [Φ, Fin.append_right] using hdir k
  have hmain := ho a (Aμ + (p + n + 1) + C1i) Dg (Dμ + p * 1 + C2i + 1) (flatFn (χ j)) Φ
    (by simpa only [famGraph_eq_graphOf_flatFn] using hχ j) hcoord
  -- identify the composite with the substituted chart
  have hcomp : flatFn (fun (l : Fin p → ℝ) (t : Fin n → ℝ) => χ j (μ l) t) =
      flatFn (χ j) ∘ Φ := by
    funext z
    simp only [flatFn, Function.comp_apply, Φ, Fin.append_left, Fin.append_right, dirFn]
    rfl
  rw [famGraph_eq_graphOf_flatFn, hcomp]
  refine Omega_mono_le S ?_ ?_ hmain
  · -- format
    omega
  · -- degree
    have h1 : Dg ≤ (q + n + 1) * Dg := Nat.le_mul_of_pos_left Dg (by omega)
    have h2 : (q + n) * Dμ ≤ (Dμ + 1) * (p + q + n + 1) := by
      calc (q + n) * Dμ ≤ (p + q + n + 1) * Dμ := Nat.mul_le_mul_right (Dμ) (by omega)
        _ = Dμ * (p + q + n + 1) := Nat.mul_comm _ _
        _ ≤ (Dμ + 1) * (p + q + n + 1) := Nat.mul_le_mul_right (p + q + n + 1) (by omega)
    have h3 : Dg + (q + n) * Dμ ≤ (Dμ + 1) * (p + q + n + 1) + (q + n + 1) * Dg := by
      have := Nat.add_le_add h1 h2
      omega
    have h4 : Dg + (q + n) * (Dμ + p * 1 + C2i + 1) + C2o ≤
        (Dμ + 1) * (p + q + n + 1) + (q + n + 1) * Dg + ((q + n) * (p + C2i + 1) + C2o) := by
      have e1 : Dg + (q + n) * (Dμ + p * 1 + C2i + 1) + C2o =
          (Dg + (q + n) * Dμ) + ((q + n) * (p + C2i + 1) + C2o) := by ring
      have e2 : (Dμ + 1) * (p + q + n + 1) + (q + n + 1) * Dg +
          ((q + n) * (p + C2i + 1) + C2o) =
          ((Dμ + 1) * (p + q + n + 1) + (q + n + 1) * Dg) +
            ((q + n) * (p + C2i + 1) + C2o) := by ring
      rw [e1, e2]
      exact Nat.add_le_add_right h3 _
    exact h4

/-! ## 4. Monotonicity of `ChartsOK` -/

/-- `ChartsOK` is monotone in the format and the degree of the chart graphs. -/
theorem SC.ChartsOK_mono {S : SOMin} {p n k a a' Dg Dg' r : ℕ} {Λ : Set (Fin p → ℝ)}
    {F : Family k p n} {Φ : Finset (ChartTuple p n)} (h : ChartsOK S a Dg r Λ F Φ)
    (ha : a ≤ a') (hD : Dg ≤ Dg') : ChartsOK S a' Dg' r Λ F Φ :=
  fun φ hφ => ⟨fun j => Omega_mono_le S ha hD ((h φ hφ).1 j), (h φ hφ).2⟩

/-! ## 5. The theorem -/

theorem SubstCharts (S : WilkiesDesign.SOMin) (p q n k : ℕ) :
    ∃ (a' : ℕ) (c' : ℕ), ∀ (r : ℕ) (θ : (Fin q → ℝ) → (Fin p → ℝ))
      (μ : (Fin p → ℝ) → (Fin q → ℝ))
      (F : Work.WilkG4c.Family k p n) (Λ : Set (Fin p → ℝ))
      (Aθ Dθ Aμ Dμ : ℕ)
      (hθg : ∀ j : Fin p, WilkiesDesign.graphOf (fun ν : Fin q → ℝ => θ ν j) ∈
        S.Ω Aθ Dθ (q + 1))
      (hμg : ∀ j : Fin q, WilkiesDesign.graphOf (fun l : Fin p → ℝ => μ l j) ∈
        S.Ω Aμ Dμ (p + 1))
      (hpre : ∀ l ∈ Λ, θ (μ l) = l)
      (a Dg : ℕ) (Φ : Finset (Work.WilkG4c.ChartTuple q n))
      (hΦ : Work.WilkG4c.ChartsOK S a Dg r {ν : Fin q → ℝ | θ ν ∈ Λ}
        (fun i ν z => F i (θ ν) z) Φ),
      ∃ Φ' : Finset (Work.WilkG4c.ChartTuple p n),
        Φ'.card ≤ Φ.card ∧
        Work.WilkG4c.ChartsOK S (Aθ + Aμ + a + a')
          ((Dθ + Dμ + 1) * (p + q + n + 1) + (q + n + 1) * Dg + c') r Λ F Φ' ∧
        (∀ χ ∈ Φ, (fun j l t => χ j (μ l) t) ∈ Φ') ∧
        (∀ (ε : ℝ), Work.WilkG4c.Covers {ν : Fin q → ℝ | θ ν ∈ Λ}
          (fun i ν z => F i (θ ν) z) Φ ε → Work.WilkG4c.Covers Λ F Φ' ε) := by
  obtain ⟨a₀, c₀, hcomp⟩ := famGraph_paramSubst S p q n
  refine ⟨a₀, c₀, ?_⟩
  intro r θ μ F Λ Aθ Dθ Aμ Dμ hθg hμg hpre a Dg Φ hΦ
  -- (1) the `Ω`-condition on the substituted charts
  have hΩ : ∀ χ ∈ Φ, ∀ j : Fin n,
      famGraph (fun (l : Fin p → ℝ) (t : Fin n → ℝ) => χ j (μ l) t) ∈
        S.Ω (Aμ + a + a₀) ((Dμ + 1) * (p + q + n + 1) + (q + n + 1) * Dg + c₀)
          (p + n + 1) :=
    fun χ hχ j => hcomp Aμ Dμ a Dg μ χ hμg (fun j' => (hΦ χ hχ).1 j') j
  -- (2) raise the given charts to the format/degree of (1)
  have hΦ' : ChartsOK S (Aμ + a + a₀)
      ((Dμ + 1) * (p + q + n + 1) + (q + n + 1) * Dg + c₀) r
      {ν : Fin q → ℝ | θ ν ∈ Λ} (fun i ν z => F i (θ ν) z) Φ := by
    refine SC.ChartsOK_mono hΦ (by omega) ?_
    have h1 : Dg ≤ (q + n + 1) * Dg := Nat.le_mul_of_pos_left Dg (by omega)
    omega
  -- (3) transfer the charts along the section `μ`
  obtain ⟨Φ', hcard, hOK, hmem⟩ := ParamChartsOK S θ μ Λ F hpre Φ hΩ hΦ'
  refine ⟨Φ', hcard, ?_, hmem, ?_⟩
  · refine SC.ChartsOK_mono hOK (by omega) ?_
    have h1 : (Dμ + 1) * (p + q + n + 1) ≤ (Dθ + Dμ + 1) * (p + q + n + 1) :=
      Nat.mul_le_mul_right (p + q + n + 1) (by omega)
    omega
  · -- (4) the `ε`-cover transfers because `θ (μ l) = l`
    intro ε hcov l hl x hx
    have hν : μ l ∈ {ν : Fin q → ℝ | θ ν ∈ Λ} := by
      show θ (μ l) ∈ Λ
      rw [hpre l hl]
      exact hl
    obtain ⟨χ, hχ, t, ht, hlt⟩ := hcov (μ l) hν x hx
    refine ⟨(fun j l' t' => χ j (μ l') t'), hmem χ hχ, t, ht, ?_⟩
    intro i
    simpa only [hpre l hl] using hlt i

/-! ## 6. The same theorem under the namespace matching the area directory

The area directory is `Submission/Work/WilG4c` while the declarations it holds live in the
Lean namespace `Work.WilkG4c` (spelled with a `k`); the task registry of this workspace,
however, resolves the fully qualified name of this lemma from the directory and looks for
`Work.WilG4c.SubstCharts`.  We therefore record the same theorem under both spellings: the
statement (and hence the type, which is namespace-independent) is identical. -/

end Work.WilkG4c

namespace Work.WilG4c

/-- `Work.WilkG4c.SubstCharts`, re-exported under the `Work.WilG4c` spelling (the statement is
namespace-independent, so it is the same theorem). -/
theorem SubstCharts (S : WilkiesDesign.SOMin) (p q n k : ℕ) :
    ∃ (a' : ℕ) (c' : ℕ), ∀ (r : ℕ) (θ : (Fin q → ℝ) → (Fin p → ℝ))
      (μ : (Fin p → ℝ) → (Fin q → ℝ))
      (F : Work.WilkG4c.Family k p n) (Λ : Set (Fin p → ℝ))
      (Aθ Dθ Aμ Dμ : ℕ)
      (hθg : ∀ j : Fin p, WilkiesDesign.graphOf (fun ν : Fin q → ℝ => θ ν j) ∈
        S.Ω Aθ Dθ (q + 1))
      (hμg : ∀ j : Fin q, WilkiesDesign.graphOf (fun l : Fin p → ℝ => μ l j) ∈
        S.Ω Aμ Dμ (p + 1))
      (hpre : ∀ l ∈ Λ, θ (μ l) = l)
      (a Dg : ℕ) (Φ : Finset (Work.WilkG4c.ChartTuple q n))
      (hΦ : Work.WilkG4c.ChartsOK S a Dg r {ν : Fin q → ℝ | θ ν ∈ Λ}
        (fun i ν z => F i (θ ν) z) Φ),
      ∃ Φ' : Finset (Work.WilkG4c.ChartTuple p n),
        Φ'.card ≤ Φ.card ∧
        Work.WilkG4c.ChartsOK S (Aθ + Aμ + a + a')
          ((Dθ + Dμ + 1) * (p + q + n + 1) + (q + n + 1) * Dg + c') r Λ F Φ' ∧
        (∀ χ ∈ Φ, (fun j l t => χ j (μ l) t) ∈ Φ') ∧
        (∀ (ε : ℝ), Work.WilkG4c.Covers {ν : Fin q → ℝ | θ ν ∈ Λ}
          (fun i ν z => F i (θ ν) z) Φ ε → Work.WilkG4c.Covers Λ F Φ' ε) :=
  Work.WilkG4c.SubstCharts S p q n k

end Work.WilG4c
