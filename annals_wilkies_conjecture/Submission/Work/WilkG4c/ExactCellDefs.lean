import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4c.CellFibreInterval
import Submission.Work.WilG4c.GraphOfComp
import Submission.Work.WilG4c.StepFiberEnds
import Submission.Work.WilG5.Reindex
import Submission.Work.WilG4c.YbddAux
import Submission.Work.WilG4c.CellMonoDeriv
import Submission.Work.WilG4c.cellFibre_param
import Submission.Work.WilG4c.graphOfLinComb_mem
import Submission.Work.WilG4c.graphOfCompGen
import Submission.Work.WilG4c.DominatingPoly
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.Cell.isCell_of_mem_cylDecomp
import Submission.Work.WilG0.API
import Submission.Work.WilG0.Omega_inter2_le
import Submission.Work.WilkG4c.deriv_snoc_eq_fderiv
import Submission.Work.WilkG4c.hasDerivAt_snoc
import Submission.Work.WilkG4c.slice_strictMono
import Submission.Work.WilkG4c.slice_abs_sub_le
import Submission.Work.WilkG4c.exists_mem_image_ivt
import Submission.Work.WilkG4c.mem_Ioo_min_max_of_injOn
import Submission.Work.WilkG4c.eval_mono
import Submission.Work.WilkG4c.exists_eval_dom
import Submission.Work.WilkG4c.strictMonoOn_or_strictAntiOn_of_injOn

set_option autoImplicit false

noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG0 Work.WilG1

/-! ## Infrastructure

We flatten a one-variable family member to a function on `ℝ^{p+1}`, and introduce the two index
maps that exchange the last two coordinates of `ℝ^{p+2}` (used to build the set whose fibre is the
inverse of the dominating member). -/

/-- A one-variable family member `F : ℝ^p × ℝ → ℝ` read as a function on `ℝ^{p+1}`
(parameters first, then the single fibre coordinate). -/
def flatFam {p : ℕ} (F : (Fin p → ℝ) → (Fin 1 → ℝ) → ℝ) : (Fin (p + 1) → ℝ) → ℝ :=
  fun z => F (Fin.init z) (fun _ => z (Fin.last p))

theorem flatFun_eq_flatFam {p : ℕ} (F : (Fin p → ℝ) → (Fin 1 → ℝ) → ℝ) :
    Work.WilkG4c.flatFun F = flatFam F := by
  funext z
  unfold Work.WilkG4c.flatFun flatFam
  have h1 : (fun i : Fin p => z (Fin.castAdd 1 i)) = Fin.init z := by
    funext i
    exact congrArg z (Fin.ext rfl)
  have h2 : (fun j : Fin 1 => z (Fin.natAdd p j)) = (fun _ : Fin 1 => z (Fin.last p)) := by
    funext j
    exact congrArg z (Fin.ext (by have := j.isLt; simp only [Fin.natAdd, Fin.last]; omega))
  rw [h1, h2]

/-- The graph of a one-variable family is the graph of its flattening. -/
theorem famGraph_eq_graphOf_flatFam {p : ℕ} (F : (Fin p → ℝ) → (Fin 1 → ℝ) → ℝ) :
    famGraph F = graphOf (flatFam F) := by
  rw [Work.WilkG4c.famGraph_eq_graphOf_flatFun, flatFun_eq_flatFam]

/-- `insTop p` maps `Fin (p+1)` into `Fin (p+2)` keeping the first `p` coordinates and sending
the last coordinate to the last one. -/
def insTop (p : ℕ) : Fin (p + 1) → Fin (p + 2) :=
  Fin.snoc (fun i : Fin p => Fin.castSucc (Fin.castSucc i)) (Fin.last (p + 1))

/-- `swapTop p` swaps the last two coordinates of `Fin (p+2)`. -/
def swapTop (p : ℕ) : Fin (p + 2) → Fin (p + 2) :=
  Fin.snoc (insTop p) (Fin.castSucc (Fin.last p))

theorem insTop_castSucc {p : ℕ} (i : Fin p) :
    insTop p (Fin.castSucc i) = Fin.castSucc (Fin.castSucc i) := by
  simp [insTop]

theorem insTop_last {p : ℕ} : insTop p (Fin.last p) = Fin.last (p + 1) := by
  simp [insTop]

theorem swapTop_castSucc_castSucc {p : ℕ} (i : Fin p) :
    swapTop p (Fin.castSucc (Fin.castSucc i)) = Fin.castSucc (Fin.castSucc i) := by
  simp [swapTop, insTop]

theorem swapTop_castSucc_last {p : ℕ} :
    swapTop p (Fin.castSucc (Fin.last p)) = Fin.last (p + 1) := by
  simp [swapTop, insTop]

theorem swapTop_last {p : ℕ} :
    swapTop p (Fin.last (p + 1)) = Fin.castSucc (Fin.last p) := by
  simp [swapTop]

/-- Reading a point `(λ, η, s)` of `ℝ^{p+2}` through `insTop` forgets `η`. -/
theorem snoc_snoc_comp_insTop {p : ℕ} (l : Fin p → ℝ) (η s : ℝ) :
    (Fin.snoc (Fin.snoc l η : Fin (p + 1) → ℝ) s : Fin (p + 2) → ℝ) ∘ insTop p = Fin.snoc l s := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · show (Fin.snoc (Fin.snoc l η : Fin (p + 1) → ℝ) s : Fin (p + 2) → ℝ)
      (insTop p (Fin.last p)) = _
    rw [insTop_last, Fin.snoc_last, Fin.snoc_last]
  · intro j
    show (Fin.snoc (Fin.snoc l η : Fin (p + 1) → ℝ) s : Fin (p + 2) → ℝ)
      (insTop p (Fin.castSucc j)) = _
    rw [insTop_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]

/-- Reading a point `(λ, η, s)` of `ℝ^{p+2}` through `swapTop` gives `(λ, s, η)`. -/
theorem snoc_snoc_comp_swapTop {p : ℕ} (l : Fin p → ℝ) (η s : ℝ) :
    (Fin.snoc (Fin.snoc l η : Fin (p + 1) → ℝ) s : Fin (p + 2) → ℝ) ∘ swapTop p =
      Fin.snoc (Fin.snoc l s : Fin (p + 1) → ℝ) η := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · show (Fin.snoc (Fin.snoc l η : Fin (p + 1) → ℝ) s : Fin (p + 2) → ℝ)
      (swapTop p (Fin.last (p + 1))) = _
    rw [swapTop_last, Fin.snoc_castSucc, Fin.snoc_last, Fin.snoc_last]
  · intro j
    refine Fin.lastCases ?_ ?_ j
    · show (Fin.snoc (Fin.snoc l η : Fin (p + 1) → ℝ) s : Fin (p + 2) → ℝ)
        (swapTop p (Fin.castSucc (Fin.last p))) = _
      rw [swapTop_castSucc_last, Fin.snoc_last, Fin.snoc_castSucc, Fin.snoc_last]
    · intro i
      show (Fin.snoc (Fin.snoc l η : Fin (p + 1) → ℝ) s : Fin (p + 2) → ℝ)
        (swapTop p (Fin.castSucc (Fin.castSucc i))) = _
      rw [swapTop_castSucc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc,
        Fin.snoc_castSucc]

/-- The last coordinate of a point of the cube `inCubeSet p 1` lies in `(0,1)`. -/
theorem inCubeSet_one_last {p : ℕ} {w : Fin (p + 1) → ℝ}
    (h : w ∈ Work.WilG4c.inCubeSet p 1) : w (Fin.last p) ∈ Set.Ioo (0 : ℝ) 1 := by
  have h1 : (fun j : Fin 1 => w (Fin.natAdd p j)) ∈ openCube 1 := h
  have h2 := h1 0
  have h3 : (Fin.natAdd p (0 : Fin 1) : Fin (p + 1)) = Fin.last p :=
    Fin.ext (by have := (0 : Fin 1).isLt; simp only [Fin.natAdd, Fin.last]; omega)
  rw [← h3]
  exact h2

/-! ## The inverse set

`invSet κ f ⊆ ℝ^{p+2}` (coordinates `(λ, η, s)`) is the set of triples with `(λ, s) ∈ κ` and
`η = f (λ, s)`.  Its fibre over `(λ, η)` is the preimage of `η` under `f` inside the fibre of `κ`;
when `f` is strictly monotone along the fibres of `κ` this fibre is a single point, and
`StepFiberEnds` applied to `invSet κ f` therefore produces the inverse function of `f`. -/

/-- The set of triples `(λ, η, s) ∈ ℝ^{p+2}` with `(λ,s) ∈ κ` and `η = f (λ,s)`. -/
def invSet {p : ℕ} (κ : Set (Fin (p + 1) → ℝ)) (f : (Fin (p + 1) → ℝ) → ℝ) :
    Set (Fin (p + 2) → ℝ) :=
  {z | z ∘ insTop p ∈ κ} ∩ {z | z ∘ swapTop p ∈ graphOf f}

/-- Membership in the graph of a function of `p+1` variables, at a point written with `snoc`. -/
theorem mem_graphOf_snoc {p : ℕ} {f : (Fin (p + 1) → ℝ) → ℝ} {l : Fin p → ℝ} {η s : ℝ} :
    (Fin.snoc (Fin.snoc l s : Fin (p + 1) → ℝ) η : Fin (p + 2) → ℝ) ∈ graphOf f ↔
      η = f (Fin.snoc l s) := by
  rw [graphOf, Set.mem_ofPred_eq, Fin.snoc_last, Fin.init_snoc]

/-- `(λ, η, s) ∈ invSet κ f` iff `(λ,s) ∈ κ` and `η = f (λ,s)`. -/
theorem mem_invSet {p : ℕ} {κ : Set (Fin (p + 1) → ℝ)} {f : (Fin (p + 1) → ℝ) → ℝ}
    {l : Fin p → ℝ} {η s : ℝ} :
    (Fin.snoc (Fin.snoc l η : Fin (p + 1) → ℝ) s : Fin (p + 2) → ℝ) ∈ invSet κ f ↔
      (Fin.snoc l s ∈ κ ∧ f (Fin.snoc l s) = η) := by
  rw [invSet, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    rw [snoc_snoc_comp_insTop] at h1
    rw [snoc_snoc_comp_swapTop, mem_graphOf_snoc] at h2
    exact ⟨h1, h2.symm⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rwa [snoc_snoc_comp_insTop]
    · rw [snoc_snoc_comp_swapTop, mem_graphOf_snoc]
      exact h2.symm

/-- The projection of `invSet κ f` to `(λ, η)`: the graph of the map `(λ, s) ↦ f (λ,s)` over the
fibre of `κ`. -/
def imgSet {p : ℕ} (κ : Set (Fin (p + 1) → ℝ)) (f : (Fin (p + 1) → ℝ) → ℝ) :
    Set (Fin (p + 1) → ℝ) :=
  projLast (invSet κ f)

/-- `(λ, η) ∈ imgSet κ f` iff there is `s` with `(λ,s) ∈ κ` and `η = f (λ,s)`. -/
theorem mem_imgSet {p : ℕ} {κ : Set (Fin (p + 1) → ℝ)} {f : (Fin (p + 1) → ℝ) → ℝ}
    {l : Fin p → ℝ} {η : ℝ} :
    Fin.snoc l η ∈ imgSet κ f ↔ ∃ s : ℝ, Fin.snoc l s ∈ κ ∧ f (Fin.snoc l s) = η := by
  constructor
  · rintro ⟨s, hs⟩
    rw [mem_invSet] at hs
    exact ⟨s, hs⟩
  · rintro ⟨s, hs1, hs2⟩
    exact ⟨s, (mem_invSet).mpr ⟨hs1, hs2⟩⟩

/-- `Ω`-bounds of `invSet`. -/
theorem invSet_mem (S : SOMin) {p F0 F1 D0 D1 : ℕ} {κ : Set (Fin (p + 1) → ℝ)}
    {f : (Fin (p + 1) → ℝ) → ℝ}
    (hκ : κ ∈ S.Ω F1 D1 (p + 1)) (hf : graphOf f ∈ S.Ω F0 D0 (p + 2)) :
    invSet κ f ∈ S.Ω
      (max (F1 + 2 * ((p + 2) + (p + 1)) + 1) (F0 + 2 * ((p + 2) + (p + 2)) + 1) + 1)
      ((D1 + 2) + (D0 + 2)) (p + 2) := by
  have hA : {z : Fin (p + 2) → ℝ | z ∘ insTop p ∈ κ} ∈
      S.Ω (F1 + 2 * ((p + 2) + (p + 1)) + 1) (D1 + 2) (p + 2) :=
    Work.WilG4c.GraphComp.subst_mem S (insTop p) hκ
  have hB : {z : Fin (p + 2) → ℝ | z ∘ swapTop p ∈ graphOf f} ∈
      S.Ω (F0 + 2 * ((p + 2) + (p + 2)) + 1) (D0 + 2) (p + 2) :=
    Work.WilG4c.GraphComp.subst_mem S (swapTop p) hf
  exact Omega_inter2_le hA hB

/-- `Ω`-bounds of `imgSet`. -/
theorem imgSet_mem (S : SOMin) {p F0 F1 D0 D1 : ℕ} {κ : Set (Fin (p + 1) → ℝ)}
    {f : (Fin (p + 1) → ℝ) → ℝ}
    (hκ : κ ∈ S.Ω F1 D1 (p + 1)) (hf : graphOf f ∈ S.Ω F0 D0 (p + 2)) :
    imgSet κ f ∈ S.Ω
      (max (F1 + 2 * ((p + 2) + (p + 1)) + 1) (F0 + 2 * ((p + 2) + (p + 2)) + 1) + 1 + 1)
      ((D1 + 2) + (D0 + 2)) (p + 1) :=
  S.proj (invSet_mem S hκ hf)

/-- The graph of the "lifted" function `x ↦ f (Fin.init x)` on `ℝ^{p+1}` is the pullback of the
graph of `f` along `insTop p`. -/
theorem graphOf_lift_eq {p : ℕ} (f : (Fin p → ℝ) → ℝ) :
    graphOf (fun x : Fin (p + 1) → ℝ => f (Fin.init x)) =
      {z : Fin (p + 2) → ℝ | z ∘ insTop p ∈ graphOf f} := by
  ext z
  have harg : (fun i : Fin p => (z ∘ insTop p) (Fin.castSucc i)) = Fin.init (Fin.init z) := by
    funext i
    rw [Function.comp_apply, insTop_castSucc]
    rfl
  change z (Fin.last (p + 1)) = f (Fin.init (Fin.init z)) ↔
    (z ∘ insTop p) ∈ graphOf f
  rw [graphOf, Set.mem_ofPred_eq, Function.comp_apply, insTop_last,
    show Fin.init (z ∘ insTop p) = Fin.init (Fin.init z) from harg]

/-- `Ω`-bounds of the graph of a lifted function. -/
theorem graphOf_lift_mem (S : SOMin) {p F D : ℕ} {f : (Fin p → ℝ) → ℝ}
    (hf : graphOf f ∈ S.Ω F D (p + 1)) :
    graphOf (fun x : Fin (p + 1) → ℝ => f (Fin.init x)) ∈
      S.Ω (F + 2 * ((p + 2) + (p + 1)) + 1) (D + 2) (p + 2) := by
  rw [graphOf_lift_eq]
  exact Work.WilG4c.GraphComp.subst_mem S (insTop p) hf

/-- Coordinate of `Fin.snoc (Fin.init x) a`. -/
theorem snoc_init_castSucc {p : ℕ} (x : Fin (p + 1) → ℝ) (a : ℝ) (i : Fin p) :
    (Fin.snoc (Fin.init x) a : Fin (p + 1) → ℝ) (Fin.castSucc i) = x (Fin.castSucc i) := by
  rw [Fin.snoc_castSucc]
  rfl


/-! ## Index computations for a general point -/

/-- The point `z ∘ swapTop p` is `(z 0, …, z (p-1), z p, z (p+1))` with the last two swapped:
its last coordinate is `z p` and its `(p+1)`-st coordinate is `z (p+1)`. -/
theorem comp_swapTop_self {p : ℕ} (z : Fin (p + 2) → ℝ) :
    z ∘ swapTop p = (Fin.snoc (Fin.snoc (Fin.init (Fin.init z)) (z (Fin.last (p + 1))) :
        Fin (p + 1) → ℝ) (z (Fin.castSucc (Fin.last p))) : Fin (p + 2) → ℝ) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · show (z ∘ swapTop p) (Fin.last (p + 1)) =
      (Fin.snoc (Fin.snoc (Fin.init (Fin.init z)) (z (Fin.last (p + 1))) : Fin (p + 1) → ℝ)
        (z (Fin.castSucc (Fin.last p))) : Fin (p + 2) → ℝ) (Fin.last (p + 1))
    rw [Fin.snoc_last, Function.comp_apply, swapTop_last]
  · intro j
    show (z ∘ swapTop p) (Fin.castSucc j) =
      (Fin.snoc (Fin.snoc (Fin.init (Fin.init z)) (z (Fin.last (p + 1))) : Fin (p + 1) → ℝ)
        (z (Fin.castSucc (Fin.last p))) : Fin (p + 2) → ℝ) (Fin.castSucc j)
    rw [Fin.snoc_castSucc, Function.comp_apply]
    refine Fin.lastCases ?_ ?_ j
    · show z (swapTop p (Fin.castSucc (Fin.last p))) = _
      rw [swapTop_castSucc_last, Fin.snoc_last]
    · intro i
      show z (swapTop p (Fin.castSucc (Fin.castSucc i))) = _
      rw [swapTop_castSucc_castSucc, Fin.snoc_castSucc]
      rfl

/-- The point `z ∘ insTop p` is `(z 0, …, z (p-1), z (p+1))`, i.e. the first `p` coordinates of
`z` followed by its last one. -/
theorem comp_insTop_self {p : ℕ} (z : Fin (p + 2) → ℝ) :
    z ∘ insTop p = Fin.snoc (Fin.init (Fin.init z)) (z (Fin.last (p + 1))) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · show z (insTop p (Fin.last p)) = _
    rw [insTop_last, Fin.snoc_last]
  · intro j
    show z (insTop p (Fin.castSucc j)) = _
    rw [insTop_castSucc, Fin.snoc_castSucc]
    rfl

/-- The point `z ∘ swapTop p` is `(z 0, …, z (p-1), z (p+1), z p)`. -/
theorem init_comp_swapTop {p : ℕ} (z : Fin (p + 2) → ℝ) :
    Fin.init (z ∘ swapTop p) =
      Fin.snoc (Fin.init (Fin.init z)) (z (Fin.last (p + 1))) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [Fin.snoc_last]
    show (z ∘ swapTop p) (Fin.castSucc (Fin.last p)) = z (Fin.last (p + 1))
    rw [Function.comp_apply, swapTop_castSucc_last]
  · intro j
    rw [Fin.snoc_castSucc]
    show (z ∘ swapTop p) (Fin.castSucc (Fin.castSucc j)) = (Fin.init (Fin.init z)) j
    rw [Function.comp_apply, swapTop_castSucc_castSucc]
    rfl

/-- The last coordinate of `z ∘ swapTop p` is `z p`. -/
theorem last_comp_swapTop {p : ℕ} (z : Fin (p + 2) → ℝ) :
    (z ∘ swapTop p) (Fin.last (p + 1)) = z (Fin.castSucc (Fin.last p)) := by
  rw [Function.comp_apply, swapTop_last]

/-- Membership in `invSet κ f` in terms of the coordinates of a general point. -/
theorem mem_invSet_self {p : ℕ} {κ : Set (Fin (p + 1) → ℝ)} {f : (Fin (p + 1) → ℝ) → ℝ}
    (z : Fin (p + 2) → ℝ) :
    z ∈ invSet κ f ↔
      (Fin.snoc (Fin.init (Fin.init z)) (z (Fin.last (p + 1))) ∈ κ ∧
        f (Fin.snoc (Fin.init (Fin.init z)) (z (Fin.last (p + 1)))) =
          z (Fin.castSucc (Fin.last p))) := by
  rw [invSet, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    rw [comp_insTop_self] at h1
    rw [graphOf, Set.mem_ofPred_eq, Function.comp_apply, swapTop_last, init_comp_swapTop] at h2
    exact ⟨h1, h2.symm⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rwa [comp_insTop_self]
    · rw [graphOf, Set.mem_ofPred_eq, Function.comp_apply, swapTop_last, init_comp_swapTop]
      exact h2.symm

/-- **Intermediate value theorem in the "between min and max" form.** -/
theorem exists_eq_of_mem_Ioo_min_max {f : ℝ → ℝ} {a b y : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hy : y ∈ Set.Ioo (min (f a) (f b)) (max (f a) (f b))) :
    ∃ x ∈ Set.Icc a b, f x = y := by
  rcases le_total (f a) (f b) with h | h
  · rw [min_eq_left h, max_eq_right h] at hy
    exact intermediate_value_Icc hab hcont ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  · rw [min_eq_right h, max_eq_left h] at hy
    exact intermediate_value_Icc' hab hcont ⟨le_of_lt hy.1, le_of_lt hy.2⟩

/-! ## The chart and the facts it is built from -/

/-- The value of the per-cell chart at the parameter `l` and the cube point `t`:
`g` applied to the affine interpolation of the two ends `α l, β l`. -/
def chartVal {p : ℕ} (g : (Fin (p + 1) → ℝ) → ℝ) (α β : (Fin p → ℝ) → ℝ)
    (l : Fin p → ℝ) (t : Fin 1 → ℝ) : ℝ :=
  g (Fin.snoc l (α l + t 0 * (β l - α l)))

/-- The facts about the fibre of `κ` over `l` and about the inverse `g` of `f` along that fibre
that the construction of the chart uses. -/
structure CellFacts {p : ℕ} (κ : Set (Fin (p + 1) → ℝ)) (f : (Fin (p + 1) → ℝ) → ℝ)
    (g : (Fin (p + 1) → ℝ) → ℝ) (α β : (Fin p → ℝ) → ℝ) (l : Fin p → ℝ) : Prop where
  /-- `α l ≤ β l`. -/
  le : α l ≤ β l
  /-- `α l ≥ 0`. -/
  nonneg : 0 ≤ α l
  /-- `β l ≤ 1`. -/
  le_one : β l ≤ 1
  /-- The fibre is mapped into `[α l, β l]`. -/
  bound : ∀ s : ℝ, Fin.snoc l s ∈ κ → α l ≤ f (Fin.snoc l s) ∧ f (Fin.snoc l s) ≤ β l
  /-- `f` is injective on the fibre. -/
  inj : ∀ x y : ℝ, Fin.snoc l x ∈ κ → Fin.snoc l y ∈ κ →
    f (Fin.snoc l x) = f (Fin.snoc l y) → x = y
  /-- `(α l, β l)` is contained in the image of the fibre. -/
  ivt : ∀ η : ℝ, α l < η → η < β l → ∃ s : ℝ, Fin.snoc l s ∈ κ ∧ f (Fin.snoc l s) = η
  /-- `g` is the inverse of `f` along the fibre. -/
  inv_eq : ∀ η s : ℝ,
    (Fin.snoc (Fin.snoc l η : Fin (p + 1) → ℝ) s : Fin (p + 2) → ℝ) ∈ invSet κ f →
      g (Fin.snoc l η) = s
  /-- The affine interpolation of `(α l, β l)` lands in the image of the fibre. -/
  img : ∀ τ ∈ Set.Ioo (0 : ℝ) 1,
    ∃ s : ℝ, Fin.snoc l s ∈ κ ∧ f (Fin.snoc l s) = α l + τ * (β l - α l)
  /-- Interior fibre points are mapped strictly inside `(α l, β l)`. -/
  strict : α l < β l → ∀ x : ℝ, Fin.snoc l x ∈ κ →
    α l < f (Fin.snoc l x) ∧ f (Fin.snoc l x) < β l
  /-- In the non-degenerate case the fibre is an open interval. -/
  interval : α l < β l → ∃ A B : ℝ, A < B ∧ {s : ℝ | Fin.snoc l s ∈ κ} = Set.Ioo A B

end Work.WilkG4c
