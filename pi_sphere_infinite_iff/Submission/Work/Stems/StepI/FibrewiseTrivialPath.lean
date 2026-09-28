import Submission.Work.Stems.StepI.SqueezeDefs
import Submission.Work.Stems.StepI.squeezeH_evals
import Submission.Work.Stems.StepI.squeezeK_evals
import Submission.Work.Stems.StepI.continuous_squeezeHUnc
import Submission.Work.Stems.StepI.continuous_squeezeKUnc
import Submission.Work.Stems.StepI.trivsect_composites

/-!
# The fibrewise triviality of the path–loop fibration over a set with a path field

This is the missing instance of `Work.StemsB.FibrewiseTrivial` for the path–loop fibration
`evalOne X x₀ : PathSpace X x₀ → X`: for a set `W ⊆ X` with a **path field**
`sg : ↥W × I → X` from `d₀ ∈ W` to the identity (`sg (w,0) = d₀`, `sg (w,1) = w`), the path–loop
fibration is fibrewise trivial over `W` with fibre `p⁻¹(d₀)`.

The trivialisation is the classical one:
`Φ (γ) = (γ(1), γ * rev sg_{γ(1)})`, `Ψ (w, δ) = (w, δ * sg_w)`, and the two homotopies are the
reparametrisation ("squeeze") homotopies `squeezeH`, `squeezeK` built in the companion files.  All
four maps are packaged as `ContinuousMap`s using the joint continuity lemmas.

Downstream this unlocks both the Wang sequence over the sphere (`Work.StemsB.wangTauSphere` and
friends, which take the triviality over `sphLoopOuter` and `sphLoopBig` as hypotheses) and Step I of
the sphere-specific route (the transgression `H_{j+n}(p⁻¹Q, p⁻¹(Q ∩ P)) ≅ H_j (p⁻¹d₀)`).
-/

open scoped Topology unitInterval
open Work.StemsB

namespace Work.Stems.StepI

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {W : Set X} {d₀ : X}

/-! ## Joint continuity of the trivialisation and of the section (single conjuncts) -/

theorem continuous_trivUnc (sg : C(↥W × I, X)) (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X)) :
    Continuous (fun q : ↥((evalOne X x₀) ⁻¹' W) × I => trivFun sg q.1 q.2) := by
  show Continuous fun q : ↥((evalOne X x₀) ⁻¹' W) × I =>
    if (2 : ℝ) * ((q.2 : I) : ℝ) ≤ 1 then cmOf q.1 (clampI (2 * ((q.2 : I) : ℝ)))
    else sg (wOf q.1, clampI (2 - 2 * ((q.2 : I) : ℝ)))
  refine Continuous.if_le ?_ ?_ ?_ ?_ ?_
  · have h : Continuous fun q : ↥((evalOne X x₀) ⁻¹' W) × I => cmOf q.1 :=
      continuous_cmOf.comp continuous_fst
    exact continuous_eval.comp (h.prodMk (continuous_clampI.comp (by fun_prop)))
  · exact sg.continuous.comp (((continuous_wOf (x₀ := x₀)).comp continuous_fst).prodMk
      (continuous_clampI.comp (by fun_prop)))
  · fun_prop
  · fun_prop
  · intro q hq
    rw [hq, show (2 : ℝ) - 1 = 1 by norm_num, clampI_one, cmOf_one, hsg1]

theorem continuous_sectUnc (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀) :
    Continuous (fun q : (↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) × I => sectFun sg q.1 q.2) := by
  show Continuous fun q : (↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) × I =>
    if (2 : ℝ) * ((q.2 : I) : ℝ) ≤ 1 then fibCM q.1.2 (clampI (2 * ((q.2 : I) : ℝ)))
    else sg (q.1.1, clampI (2 * ((q.2 : I) : ℝ) - 1))
  refine Continuous.if_le ?_ ?_ ?_ ?_ ?_
  · have h : Continuous fun q : (↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) × I => fibCM q.1.2 :=
      (continuous_fibCM (x₀ := x₀) (d₀ := d₀)).comp (by fun_prop)
    exact continuous_eval.comp (h.prodMk (continuous_clampI.comp (by fun_prop)))
  · exact sg.continuous.comp (((continuous_fst.fst)).prodMk
      (continuous_clampI.comp (by fun_prop)))
  · fun_prop
  · fun_prop
  · intro q hq
    rw [hq, clampI_one, show (1 : ℝ) - 1 = 0 by norm_num, clampI_zero, fibCM_one, hsg0]

/-! ## The curried slices -/

/-- The slices of `trivFun`, as a curried continuous map. -/
def trivCurry (sg : C(↥W × I, X)) (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X)) :
    C(↥((evalOne X x₀) ⁻¹' W), C(I, X)) :=
  ContinuousMap.curry ⟨fun q : ↥((evalOne X x₀) ⁻¹' W) × I => trivFun sg q.1 q.2,
    continuous_trivUnc sg hsg1⟩

/-- The slices of `sectFun`, as a curried continuous map. -/
def sectCurry (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀) :
    C((↥W × ↥((evalOne X x₀) ⁻¹' {d₀})), C(I, X)) :=
  ContinuousMap.curry ⟨fun q : (↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) × I => sectFun sg q.1 q.2,
    continuous_sectUnc sg hsg0⟩

/-- The slices of `squeezeH`, as a curried continuous map. -/
def squeezeHCurry (sg : C(↥W × I, X)) (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X)) :
    C(↥((evalOne X x₀) ⁻¹' W) × I, C(I, X)) :=
  ContinuousMap.curry ⟨fun q : (↥((evalOne X x₀) ⁻¹' W) × I) × I => squeezeHUnc sg q,
    continuous_squeezeHUnc sg hsg1⟩

/-- The slices of `squeezeK`, as a curried continuous map. -/
def squeezeKCurry (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀) :
    C((↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) × I, C(I, X)) :=
  ContinuousMap.curry ⟨fun q : ((↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) × I) × I =>
      squeezeKUnc (x₀ := x₀) (d₀ := d₀) sg q, continuous_squeezeKUnc sg hsg0⟩

@[simp] theorem trivCurry_apply (sg : C(↥W × I, X)) (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X))
    (z : ↥((evalOne X x₀) ⁻¹' W)) (s : I) : trivCurry sg hsg1 z s = trivFun sg z s := rfl

@[simp] theorem sectCurry_apply (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀)
    (y : ↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) (s : I) :
    sectCurry sg hsg0 y s = sectFun sg y s := rfl

@[simp] theorem squeezeHCurry_apply (sg : C(↥W × I, X)) (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X))
    (q : ↥((evalOne X x₀) ⁻¹' W) × I) (s : I) :
    squeezeHCurry sg hsg1 q s = squeezeH sg q.1 (q.2 : ℝ) (s : ℝ) := rfl

@[simp] theorem squeezeKCurry_apply (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀)
    (q : (↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) × I) (s : I) :
    squeezeKCurry sg hsg0 q s = squeezeK sg q.1.1 (fibCM q.1.2) (q.2 : ℝ) (s : ℝ) := rfl

/-! ## The four maps of the triviality -/

/-- **The trivialisation** `Φ (z) = (z(1), z * rev sg_{z(1)})`. -/
def trivCMap (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀)
    (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X)) :
    C(↥((evalOne X x₀) ⁻¹' W), ↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) where
  toFun z := (wOf z, ⟨⟨trivCurry sg hsg1 z, trivCM_zero sg hsg1 z⟩,
    trivCM_one sg hsg0 hsg1 z⟩)
  continuous_toFun := Continuous.prodMk (continuous_wOf (x₀ := x₀))
    (Continuous.subtype_mk (Continuous.subtype_mk (trivCurry sg hsg1).continuous
      (fun z => trivCM_zero sg hsg1 z)) (fun z => trivCM_one sg hsg0 hsg1 z))

@[simp] theorem trivCMap_apply (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀)
    (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X)) (z : ↥((evalOne X x₀) ⁻¹' W)) :
    trivCMap sg hsg0 hsg1 z = (wOf z, ⟨⟨trivCurry sg hsg1 z, trivCM_zero sg hsg1 z⟩,
      trivCM_one sg hsg0 hsg1 z⟩) := rfl

theorem trivCMap_fst (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀)
    (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X)) (z : ↥((evalOne X x₀) ⁻¹' W)) :
    (trivCMap sg hsg0 hsg1 z).1 = wOf z := rfl


theorem sectCMap_mem (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀)
    (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X))
    (y : ↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) :
    (evalOne X x₀) ⟨sectCM sg hsg0 y, sectCM_zero sg hsg0 y⟩ ∈ W := by
  have h := sectCM_one sg hsg0 hsg1 y
  show sectCM sg hsg0 y 1 ∈ W
  rw [h]
  exact y.1.2

/-- **The section of the trivialisation** `Ψ (w, δ) = (w, δ * sg_w)`. -/
def sectCMap (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀)
    (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X)) :
    C((↥W × ↥((evalOne X x₀) ⁻¹' {d₀})), ↥((evalOne X x₀) ⁻¹' W)) where
  toFun y := ⟨⟨sectCurry sg hsg0 y, sectCM_zero sg hsg0 y⟩, sectCMap_mem sg hsg0 hsg1 y⟩
  continuous_toFun := Continuous.subtype_mk (Continuous.subtype_mk (sectCurry sg hsg0).continuous
    (fun y => sectCM_zero sg hsg0 y)) (fun y => sectCMap_mem sg hsg0 hsg1 y)

@[simp] theorem sectCMap_apply (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀)
    (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X))
    (y : ↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) :
    sectCMap sg hsg0 hsg1 y = ⟨⟨sectCurry sg hsg0 y, sectCM_zero sg hsg0 y⟩,
      sectCMap_mem sg hsg0 hsg1 y⟩ := rfl

theorem sectCMap_fst_val (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀)
    (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X)) (y : ↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) :
    ((sectCMap sg hsg0 hsg1 y).1.1) 1 = (y.1 : X) :=
  sectCM_one sg hsg0 hsg1 y


/-! ## Membership helpers for the two homotopy maps -/

theorem squeezeHMap_mem (sg : C(↥W × I, X)) (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X))
    (q : ↥((evalOne X x₀) ⁻¹' W) × I) :
    (evalOne X x₀) ⟨squeezeHCurry sg hsg1 q, squeezeH_at_zero sg q.1 q.2.2⟩ ∈ W := by
  have h := squeezeH_at_one sg hsg1 q.1 q.2.2
  show squeezeH sg q.1 (q.2 : ℝ) 1 ∈ W
  rw [h]
  exact (wOf q.1).2

theorem squeezeKMap_mem0 (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀)
    (q : (↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) × I) :
    (squeezeKCurry sg hsg0 q) 0 = x₀ := by
  show squeezeK sg q.1.1 (fibCM q.1.2) (q.2 : ℝ) 0 = x₀
  rw [squeezeK_at_zero sg q.1.1 (fibCM q.1.2) q.2.2]
  exact fibCM_zero q.1.2

theorem squeezeKMap_mem1 (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀)
    (q : (↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) × I) :
    (evalOne X x₀)
      ⟨squeezeKCurry sg hsg0 q, squeezeKMap_mem0 (x₀ := x₀) (d₀ := d₀) sg hsg0 q⟩ ∈
        ({d₀} : Set X) := by
  have h := squeezeK_at_one sg hsg0 q.1.1 (fibCM q.1.2) (fibCM_one q.1.2) q.2.2
  show squeezeK sg q.1.1 (fibCM q.1.2) (q.2 : ℝ) 1 ∈ ({d₀} : Set X)
  rw [h]
  exact Set.mem_singleton d₀

/-- **The homotopy `id ≃ Ψ ∘ Φ`**, over the base. -/
def squeezeHMap (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀)
    (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X)) :
    C(↥((evalOne X x₀) ⁻¹' W) × I, ↥((evalOne X x₀) ⁻¹' W)) where
  toFun q := ⟨⟨squeezeHCurry sg hsg1 q, squeezeH_at_zero sg q.1 q.2.2⟩,
    squeezeHMap_mem sg hsg1 q⟩
  continuous_toFun := Continuous.subtype_mk
    (Continuous.subtype_mk (squeezeHCurry sg hsg1).continuous
      (fun q => squeezeH_at_zero sg q.1 q.2.2))
    (fun q => squeezeHMap_mem sg hsg1 q)

@[simp] theorem squeezeHMap_apply (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀)
    (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X))
    (q : ↥((evalOne X x₀) ⁻¹' W) × I) (s : I) :
    (squeezeHMap sg hsg0 hsg1 q).1.1 s = squeezeH sg q.1 (q.2 : ℝ) (s : ℝ) := rfl

/-- **The homotopy `id ≃ Φ ∘ Ψ`**, on `↥W × p⁻¹(d₀)`, keeping the first coordinate fixed. -/
def squeezeKMap (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀)
    (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X)) :
    C((↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) × I, ↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) where
  toFun q := (q.1.1, ⟨⟨squeezeKCurry sg hsg0 q, squeezeKMap_mem0 sg hsg0 q⟩,
    squeezeKMap_mem1 sg hsg0 q⟩)
  continuous_toFun := Continuous.prodMk continuous_fst.fst
    (Continuous.subtype_mk (Continuous.subtype_mk (squeezeKCurry sg hsg0).continuous
      (fun q => squeezeKMap_mem0 sg hsg0 q))
      (fun q => squeezeKMap_mem1 sg hsg0 q))

@[simp] theorem squeezeKMap_apply (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀)
    (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X))
    (q : (↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) × I) (s : I) :
    ((squeezeKMap sg hsg0 hsg1 q).2.1.1) s =
      squeezeK sg q.1.1 (fibCM q.1.2) (q.2 : ℝ) (s : ℝ) := rfl

theorem squeezeKMap_fst (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀)
    (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X))
    (q : (↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) × I) :
    (squeezeKMap sg hsg0 hsg1 q).1 = q.1.1 := rfl

/-! ## The composite identities, in the form in which `FibrewiseTrivial` needs them -/

theorem sectCMap_trivCMap (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀)
    (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X)) (x : ↥((evalOne X x₀) ⁻¹' W)) (s : I) :
    (sectCMap sg hsg0 hsg1 (trivCMap sg hsg0 hsg1 x)).1.1 s =
      compFun sg (wOf x) (cmOf x) s := by
  show sectFun sg (wOf x, ⟨⟨trivCM sg hsg1 x, trivCM_zero sg hsg1 x⟩,
    trivCM_one sg hsg0 hsg1 x⟩) s = compFun sg (wOf x) (cmOf x) s
  exact sectFun_trivCM sg hsg0 hsg1 x (trivCM_one sg hsg0 hsg1 x) s

theorem trivCMap_sectCMap (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀)
    (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X))
    (y : ↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) (s : I) :
    (trivCMap sg hsg0 hsg1 (sectCMap sg hsg0 hsg1 y)).2.1.1 s =
      compFunK sg y.1 (fibCM y.2) s := by
  show trivFun sg (⟨⟨sectCM sg hsg0 y, sectCM_zero sg hsg0 y⟩,
    sectCMap_mem sg hsg0 hsg1 y⟩ : ↥((evalOne X x₀) ⁻¹' W)) s =
      compFunK sg y.1 (fibCM y.2) s
  exact trivFun_sectCM sg hsg0 hsg1 y _ s

theorem wOf_sectCMap (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀)
    (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X))
    (y : ↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) :
    wOf (sectCMap sg hsg0 hsg1 y) = y.1 :=
  Subtype.ext (sectCMap_fst_val sg hsg0 hsg1 y)

/-! ## The fibrewise triviality -/

/-- **The path–loop fibration is fibrewise trivial over any set carrying a path field.**
If `sg : ↥W × I → X` satisfies `sg (w, 0) = d₀` and `sg (w, 1) = w`, then the path–loop fibration
`evalOne X x₀ : PathSpace X x₀ → X` is fibrewise trivial over `W` with fibre `p⁻¹(d₀)`.

This is the instance of `Work.StemsB.FibrewiseTrivial` that both Step I of the sphere-specific
route and the Wang-sequence chapter consume. -/
theorem fibrewiseTrivial_of_pathField (sg : C(↥W × I, X))
    (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀) (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X))
    (hd : d₀ ∈ W) :
    FibrewiseTrivial (evalOne X x₀) W ⟨d₀, hd⟩ := by
  refine ⟨trivCMap sg hsg0 hsg1, sectCMap sg hsg0 hsg1, ?_, ?_, ?_, ?_⟩
  · intro x
    exact trivCMap_fst sg hsg0 hsg1 x
  · intro y
    exact sectCMap_fst_val sg hsg0 hsg1 y
  · refine ⟨squeezeHMap sg hsg0 hsg1, ?_, ?_, ?_⟩
    · intro x
      apply Subtype.ext
      apply Subtype.ext
      apply ContinuousMap.ext
      intro s
      show squeezeH sg x 0 (s : ℝ) = cmOf x s
      exact squeezeH_zero sg x s
    · intro x
      apply Subtype.ext
      apply Subtype.ext
      apply ContinuousMap.ext
      intro s
      show squeezeH sg x 1 (s : ℝ) =
        (sectCMap sg hsg0 hsg1 (trivCMap sg hsg0 hsg1 x)).1.1 s
      rw [sectCMap_trivCMap sg hsg0 hsg1 x s]
      exact squeezeH_one sg hsg1 x s
    · intro x t
      show squeezeH sg x (t : ℝ) 1 = (wOf x : X)
      exact squeezeH_at_one sg hsg1 x t.2
  · refine ⟨squeezeKMap sg hsg0 hsg1, ?_, ?_, ?_⟩
    · intro y
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        apply Subtype.ext
        apply ContinuousMap.ext
        intro s
        show squeezeK sg y.1 (fibCM y.2) 0 (s : ℝ) = fibCM y.2 s
        exact squeezeK_zero sg y.1 (fibCM y.2) s
    · intro y
      apply Prod.ext
      · exact (wOf_sectCMap sg hsg0 hsg1 y).symm
      · apply Subtype.ext
        apply Subtype.ext
        apply ContinuousMap.ext
        intro s
        show squeezeK sg y.1 (fibCM y.2) 1 (s : ℝ) =
          (trivCMap sg hsg0 hsg1 (sectCMap sg hsg0 hsg1 y)).2.1.1 s
        rw [trivCMap_sectCMap sg hsg0 hsg1 y s]
        exact squeezeK_one sg y.1 (fibCM y.2) s
    · intro y t
      rfl


/-! ## The instance from a contraction of the base -/

/-- The path field obtained by reversing a contraction of `W` to `d₀`. -/
def pathFieldOfContraction (c : C(↥W × I, ↥W)) (d₀ : X) : C(↥W × I, X) :=
  ⟨fun q => (c (q.1, clampI (1 - (q.2 : ℝ))) : X),
    continuous_subtype_val.comp (c.continuous.comp (continuous_fst.prodMk
      (continuous_clampI.comp (by fun_prop))))⟩

theorem pathFieldOfContraction_zero (c : C(↥W × I, ↥W)) (d₀ : X) (w : ↥W)
    {hd : d₀ ∈ W} (hc1 : c (w, 1) = ⟨d₀, hd⟩) :
    pathFieldOfContraction c d₀ (w, 0) = d₀ := by
  have h0 : (((0 : I)) : ℝ) = 0 := rfl
  show (c (w, clampI (1 - (((0 : I)) : ℝ))) : X) = d₀
  rw [h0, show (1 : ℝ) - 0 = 1 by norm_num, clampI_one]
  exact congrArg Subtype.val hc1

theorem pathFieldOfContraction_one (c : C(↥W × I, ↥W)) (d₀ : X) (w : ↥W)
    (hc0 : c (w, 0) = w) :
    pathFieldOfContraction c d₀ (w, 1) = (w : X) := by
  have h1 : (((1 : I)) : ℝ) = 1 := rfl
  show (c (w, clampI (1 - (((1 : I)) : ℝ))) : X) = (w : X)
  rw [h1, show (1 : ℝ) - 1 = 0 by norm_num, clampI_zero]
  exact congrArg Subtype.val hc0

/-- **A based contraction of `W` gives the fibrewise triviality of the path–loop fibration over
`W`**: the reversed contraction path is the required path field. -/
theorem fibrewiseTrivial_of_contraction {X : Type} [TopologicalSpace X] {x₀ : X} {W : Set X}
    {d₀ : X} (hd : d₀ ∈ W) (c : C(↥W × I, ↥W))
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = ⟨d₀, hd⟩) :
    FibrewiseTrivial (evalOne X x₀) W ⟨d₀, hd⟩ :=
  fibrewiseTrivial_of_pathField (pathFieldOfContraction c d₀)
    (fun w => pathFieldOfContraction_zero c d₀ w (hc1 w))
    (fun w => pathFieldOfContraction_one c d₀ w (hc0 w)) hd


end

end Work.Stems.StepI
