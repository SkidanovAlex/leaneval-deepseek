import Mathlib
import Submission.Work.Drive.boxRegDefs
import Submission.Work.Drive.unrestrictedFromBox
import Submission.Work.Drive.continuousAt_partial_fderiv
import Submission.Work.Drive.loopBoxData_eventually
import Submission.Work.Drive.projCharted

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# The class-level rows are *open* in the family parameter (the `(O)` brick of the class-row lane)

`CLASSROWS_DENSITY_MECHANISM.md` §3.1 names one missing piece of the class-row family `R` of the node
`Work.Drive.exists_classRowFamily`: the set of parameters at which one of the seven class rows
(`Work.Drive.PairReg`, `Work.Drive.EndTripleReg`, in their box-restricted forms
`Work.Drive.BoxPairReg`/`Work.Drive.BoxEndTripleReg`) holds is **open** in the family parameter.

This file supplies it, for an arbitrary jointly smooth family of plane class maps, plus its
consequence for the design's own `ClassRowsAt`.

## The mechanism

At a pair of box parameters `(y, y')` with `A y = B y'` (a *meet*), the two `2`-planes
`range (dA y)` and `range (dB y')` span `TℝP³` exactly when the charted difference map

> `rowPairDiff p A B x = χ_p (A (pairA x)) - χ_p (B (pairB x))`  (`x = (y,y') ∈ 𝔼⁴`)

has surjective derivative at `x` (`pairDiff_surjective_iff`).  Surjectivity of a continuous linear map
is *open* (`Work.Sard.isOpen_setOf_surjective_clm`), and the charted derivative is continuous in the
family parameter (`Work.Drive.continuousAt_partial_fderiv`), and the box is compact — so the abstract
compactness engine `Work.Drive.eventually_forall_meet_of_eventually` turns the pointwise statement at
the base parameter into the neighbourhood statement `eventually_boxPairReg`.

The three-chain row `EndTripleReg` is treated by the same device with the charted map

> `tripleDiff p F A B x = (χ_p (F (triA x)) - χ_p (A (triB x)), χ_p (F (triA x)) - χ_p (B (triC x)))`

on `𝔼⁶ → 𝔼³ × 𝔼³`: its derivative is *injective* exactly when the three class derivatives are
injective and their `2`-planes meet in `⊥` (`tripleDiff_injective_iff`); injectivity of a square
continuous linear map is again an open condition (via surjectivity).
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- The chart at `p` of a space modelled on `𝔼³`. -/
def chr3 (p : M) : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)) :=
  chartAt (EuclideanSpace ℝ (Fin 3)) p

/-! ## The two block projections of the pair-box `𝔼² × 𝔼² = 𝔼⁴` -/

/-- The first block index of the four-box. -/
def pLo (i : Fin 2) : Fin 4 := Fin.castAdd 2 i

/-- The second block index of the four-box. -/
def pHi (i : Fin 2) : Fin 4 := Fin.natAdd 2 i

/-- The projection of the four-box onto its first block, as a continuous linear map. -/
def pairA : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ContinuousLinearMap.comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm
    (ContinuousLinearMap.pi (fun i : Fin 2 => PiLp.proj 2 (fun _ : Fin 4 => ℝ) (pLo i)))

/-- The projection of the four-box onto its second block, as a continuous linear map. -/
def pairB : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ContinuousLinearMap.comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm
    (ContinuousLinearMap.pi (fun i : Fin 2 => PiLp.proj 2 (fun _ : Fin 4 => ℝ) (pHi i)))

lemma pairA_apply (x : EuclideanSpace ℝ (Fin 4)) (i : Fin 2) : pairA x i = x (pLo i) := by
  simp [pairA, PiLp.proj_apply]

lemma pairB_apply (x : EuclideanSpace ℝ (Fin 4)) (i : Fin 2) : pairB x i = x (pHi i) := by
  simp [pairB, PiLp.proj_apply]

/-- The point of the four-box with prescribed two blocks. -/
def pairMk (p q : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 (Fin.addCases (motive := fun _ => ℝ) (fun i : Fin 2 => p i) (fun j : Fin 2 => q j))

@[simp] lemma pairA_pairMk (p q : EuclideanSpace ℝ (Fin 2)) : pairA (pairMk p q) = p := by
  ext i
  simp only [pairA_apply, pairMk, pLo, Fin.addCases_left]

@[simp] lemma pairB_pairMk (p q : EuclideanSpace ℝ (Fin 2)) : pairB (pairMk p q) = q := by
  ext i
  simp only [pairB_apply, pairMk, pHi, Fin.addCases_right]

/-- The two block projections of the four-box are jointly surjective. -/
lemma pair_joint (p q : EuclideanSpace ℝ (Fin 2)) :
    ∃ v : EuclideanSpace ℝ (Fin 4), pairA v = p ∧ pairB v = q :=
  ⟨pairMk p q, pairA_pairMk p q, pairB_pairMk p q⟩

/-! ## The pair row and its charted difference map -/

/-- The chart region of the pair difference map. -/
def pairRegion (p : M) (A B : EuclideanSpace ℝ (Fin 2) → M) : Set (EuclideanSpace ℝ (Fin 4)) :=
  {x | A (pairA x) ∈ (chr3 p).source ∧ B (pairB x) ∈ (chr3 p).source}

/-- The charted difference map of two plane presentations. -/
def rowPairDiff (p : M) (A B : EuclideanSpace ℝ (Fin 2) → M) :
    EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 3) :=
  fun x => chr3 p (A (pairA x)) - chr3 p (B (pairB x))

theorem mem_pairRegion {p : M} {A B : EuclideanSpace ℝ (Fin 2) → M}
    {x : EuclideanSpace ℝ (Fin 4)} :
    x ∈ pairRegion p A B ↔ A (pairA x) ∈ (chr3 p).source ∧ B (pairB x) ∈ (chr3 p).source :=
  Iff.rfl

/-- The chart region of the pair difference map is open. -/
theorem isOpen_pairRegion (p : M) (A B : EuclideanSpace ℝ (Fin 2) → M)
    (hA : Continuous A) (hB : Continuous B) : IsOpen (pairRegion p A B) := by
  have h1 : Continuous fun x : EuclideanSpace ℝ (Fin 4) => A (pairA x) := hA.comp pairA.continuous
  have h2 : Continuous fun x : EuclideanSpace ℝ (Fin 4) => B (pairB x) := hB.comp pairB.continuous
  exact (h1.isOpen_preimage _ (chr3 p).open_source).inter
    (h2.isOpen_preimage _ (chr3 p).open_source)

/-- **The derivative of the chart-composition `χ ∘ f`** for a map of `𝔼²` into `M`. -/
theorem mfderiv_chart3_comp (f : EuclideanSpace ℝ (Fin 2) → M)
    (hf : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) f) (p : M)
    {s : EuclideanSpace ℝ (Fin 2)} (hs : f s ∈ (chr3 p).source) :
    mfderiv (𝓡 2) (𝓡 3) (fun u => chr3 p (f u)) s =
      (tangentCoordChange (𝓡 3) (f s) p (f s)).comp (mfderiv (𝓡 2) (𝓡 3) f s) := by
  have hφ : MDifferentiableAt (𝓡 3) (𝓡 3) (chartAt (EuclideanSpace ℝ (Fin 3)) p) (f s) :=
    mdifferentiableAt_atlas (chart_mem_atlas _ _) hs
  have hfs : MDifferentiableAt (𝓡 2) (𝓡 3) f s := (hf s).mdifferentiableAt (by simp)
  have hmain := mfderiv_comp s hφ hfs
  rw [mfderiv_chartAt_eq_tangentCoordChange hs] at hmain
  exact hmain

/-- The same, for the Fréchet derivative. -/
theorem fderiv_chart3_comp (f : EuclideanSpace ℝ (Fin 2) → M)
    (hf : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) f) (p : M)
    {s : EuclideanSpace ℝ (Fin 2)} (hs : f s ∈ (chr3 p).source) :
    fderiv ℝ (fun u => chr3 p (f u)) s =
      (tangentCoordChange (𝓡 3) (f s) p (f s)).comp (mfderiv (𝓡 2) (𝓡 3) f s) := by
  rw [← mfderiv_eq_fderiv]
  exact mfderiv_chart3_comp f hf p hs

theorem fderiv_chart3_comp_hasFDerivAt (f : EuclideanSpace ℝ (Fin 2) → M)
    (hf : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) f) (p : M)
    {s : EuclideanSpace ℝ (Fin 2)} (hs : f s ∈ (chr3 p).source) :
    HasFDerivAt (fun u => chr3 p (f u))
      ((tangentCoordChange (𝓡 3) (f s) p (f s)).comp (mfderiv (𝓡 2) (𝓡 3) f s)) s := by
  have h1 : MDifferentiableAt (𝓡 3) (𝓡 3) (chr3 p : M → EuclideanSpace ℝ (Fin 3)) (f s) :=
    mdifferentiableAt_atlas (chart_mem_atlas _ _) hs
  have h2 : MDifferentiableAt (𝓡 2) (𝓡 3) f s := (hf s).mdifferentiableAt (by simp)
  have hmd : MDifferentiableAt (𝓡 2) (𝓡 3) (fun u => chr3 p (f u)) s := h1.comp s h2
  rw [← fderiv_chart3_comp f hf p hs]
  exact hmd.differentiableAt.hasFDerivAt

/-- **The derivative of the pair difference map, pointwise.** -/
theorem fderiv_pairDiff_apply (p : M) (A B : EuclideanSpace ℝ (Fin 2) → M)
    (hA : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hB : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) B)
    {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ pairRegion p A B)
    (v : EuclideanSpace ℝ (Fin 4)) :
    fderiv ℝ (rowPairDiff p A B) x v =
      tangentCoordChange (𝓡 3) (A (pairA x)) p (A (pairA x))
          (mfderiv (𝓡 2) (𝓡 3) A (pairA x) (pairA v))
        - tangentCoordChange (𝓡 3) (B (pairB x)) p (B (pairB x))
          (mfderiv (𝓡 2) (𝓡 3) B (pairB x) (pairB v)) := by
  obtain ⟨hx1, hx2⟩ := hx
  have h1 := fderiv_chart3_comp_hasFDerivAt A hA p hx1
  have h2 := fderiv_chart3_comp_hasFDerivAt B hB p hx2
  have h1' : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 4) => chr3 p (A (pairA y)))
      (((tangentCoordChange (𝓡 3) (A (pairA x)) p (A (pairA x))).comp
        (mfderiv (𝓡 2) (𝓡 3) A (pairA x))).comp pairA) x := by
    have hc := h1.comp x (pairA.hasFDerivAt (x := x))
    simpa [Function.comp_def] using hc
  have h2' : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 4) => chr3 p (B (pairB y)))
      (((tangentCoordChange (𝓡 3) (B (pairB x)) p (B (pairB x))).comp
        (mfderiv (𝓡 2) (𝓡 3) B (pairB x))).comp pairB) x := by
    have hc := h2.comp x (pairB.hasFDerivAt (x := x))
    simpa [Function.comp_def] using hc
  have h3 : HasFDerivAt (rowPairDiff p A B)
      ((((tangentCoordChange (𝓡 3) (A (pairA x)) p (A (pairA x))).comp
          (mfderiv (𝓡 2) (𝓡 3) A (pairA x))).comp pairA)
        - (((tangentCoordChange (𝓡 3) (B (pairB x)) p (B (pairB x))).comp
          (mfderiv (𝓡 2) (𝓡 3) B (pairB x))).comp pairB)) x := by
    exact h1'.sub h2'
  rw [h3.fderiv]
  rw [sub_apply]
  rfl


/-! ## Linear algebra: the range of a chart-transported difference -/

section LinAlg

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The range of `X ∘ P` when `P` is onto. -/
lemma range_comp_eq_of_range_top (X : F →L[ℝ] G) (P : E →L[ℝ] F) (h : P.range = ⊤) :
    (X.comp P).range = X.range := by
  rw [show (X.comp P).range = (X.comp P).toLinearMap.range from rfl,
    show X.range = X.toLinearMap.range from rfl,
    ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp, h, Submodule.map_top]

/-- The range of `tc ∘ X` is the image of the range of `X`. -/
lemma range_comp_eq_map (tc : F →L[ℝ] G) (X : E →L[ℝ] F) :
    (tc.comp X).range = X.range.map tc.toLinearMap := by
  rw [show (tc.comp X).range = (tc.comp X).toLinearMap.range from rfl,
    ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp]

/-- **A bijective linear map preserves the property `range = ⊤`.** -/
lemma map_eq_top_iff_of_bijective (tc : F →ₗ[ℝ] G) (htc : Function.Bijective tc)
    (X : Submodule ℝ F) : X.map tc = ⊤ ↔ X = ⊤ := by
  constructor
  · intro h
    rw [Submodule.eq_top_iff']
    intro x
    have hx : tc x ∈ X.map tc := by rw [h]; exact Submodule.mem_top
    obtain ⟨x', hx', hxx'⟩ := hx
    rw [htc.1 hxx'] at hx'
    exact hx'
  · intro h
    rw [h, Submodule.map_top, LinearMap.range_eq_top.mpr htc.2]

/-- **A bijective linear map preserves injectivity of a composite.** -/
lemma injective_comp_iff_of_injective {tc : F →ₗ[ℝ] G} (htc : Function.Injective tc)
    (X : E →ₗ[ℝ] F) : Function.Injective (tc.comp X) ↔ Function.Injective X :=
  ⟨fun h a b hab => h (congrArg tc hab), fun h a b hab => h (htc hab)⟩

/-- The kernel of a product of continuous linear maps. -/
lemma ker_prod_clm (f : E →L[ℝ] F) (g : E →L[ℝ] G) : (f.prod g).ker = f.ker ⊓ g.ker := by
  ext x
  change (f x, g x) = 0 ↔ f x = 0 ∧ g x = 0
  exact Prod.mk_eq_zero

/-- Composing with an injective map does not change the kernel. -/
lemma ker_comp_clm_eq_of_ker_eq_bot {f : F →L[ℝ] G} {g : E →L[ℝ] F} (hf : f.ker = ⊥) :
    (f.comp g).ker = g.ker := by
  ext x
  change f (g x) = 0 ↔ g x = 0
  constructor
  · intro h
    have hx : g x ∈ f.ker := h
    rw [hf] at hx
    simpa using hx
  · intro h; rw [h, map_zero]

/-- **A bijective linear map preserves surjectivity of a composite.** -/
lemma surjective_comp_iff_of_bijective {tc : F →ₗ[ℝ] G} (htc : Function.Bijective tc)
    (X : E →ₗ[ℝ] F) : Function.Surjective (tc.comp X) ↔ Function.Surjective X := by
  rw [← LinearMap.range_eq_top, ← LinearMap.range_eq_top, LinearMap.range_comp,
    map_eq_top_iff_of_bijective tc htc]

end LinAlg

/-! ## The inverse of a tangent coordinate change at a chart-contained point -/

theorem tangentCoordChange_comp_inv3 {x y z : M}
    (h : z ∈ (extChartAt (𝓡 3) x).source ∩ (extChartAt (𝓡 3) y).source)
    (v : EuclideanSpace ℝ (Fin 3)) :
    tangentCoordChange (𝓡 3) y x z (tangentCoordChange (𝓡 3) x y z v) = v := by
  have h1 : z ∈ (extChartAt (𝓡 3) x).source ∩ (extChartAt (𝓡 3) y).source ∩
      (extChartAt (𝓡 3) x).source := ⟨⟨h.1, h.2⟩, h.1⟩
  have h2 := tangentCoordChange_comp (I := 𝓡 3) (w := x) (x := y) (y := x) (z := z) (v := v) h1
  rw [tangentCoordChange_self (I := 𝓡 3) h.1] at h2
  exact h2

theorem tangentCoordChange_injective3 {x y z : M}
    (h : z ∈ (extChartAt (𝓡 3) x).source ∩ (extChartAt (𝓡 3) y).source) :
    Function.Injective (tangentCoordChange (𝓡 3) x y z) :=
  fun a b hab => by
    have h1 := tangentCoordChange_comp_inv3 h a
    have h2 := tangentCoordChange_comp_inv3 h b
    rw [hab] at h1
    rw [h2] at h1
    exact h1.symm

/-- The chart source of `chr3 p` is the source of the extended chart at `p`. -/
lemma chr3_source (p : M) : (chr3 p).source = (extChartAt (𝓡 3) p).source := by
  rw [extChartAt_source]; rfl

/-! ## The pair row: the surjectivity criterion -/

/-- The tangent coordinate change of the pair difference map at a point, viewed as an endomorphism
of the model space `𝔼³`. -/
def pairTC (p : M) (A : EuclideanSpace ℝ (Fin 2) → M) (x : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  tangentCoordChange (𝓡 3) (A (pairA x)) p (A (pairA x))

/-- The tangent coordinate change of the *second* block of a pair difference map. -/
def pairTCB (p : M) (B : EuclideanSpace ℝ (Fin 2) → M) (x : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  tangentCoordChange (𝓡 3) (B (pairB x)) p (B (pairB x))

/-- The derivative of a plane presentation, read in the model space `𝔼³`. -/
def pairDA (A : EuclideanSpace ℝ (Fin 2) → M) (x : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  mfderiv (𝓡 2) (𝓡 3) A (pairA x)

/-- The derivative of a plane presentation in its second argument, read in the model space. -/
def pairDB (B : EuclideanSpace ℝ (Fin 2) → M) (x : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  mfderiv (𝓡 2) (𝓡 3) B (pairB x)

lemma pairDA_eq_mfderiv (A : EuclideanSpace ℝ (Fin 2) → M) (x : EuclideanSpace ℝ (Fin 4)) :
    pairDA A x = mfderiv (𝓡 2) (𝓡 3) A (pairA x) := rfl

lemma pairDB_eq_mfderiv (B : EuclideanSpace ℝ (Fin 2) → M) (x : EuclideanSpace ℝ (Fin 4)) :
    pairDB B x = mfderiv (𝓡 2) (𝓡 3) B (pairB x) := rfl

/-- **The two tangent coordinate changes of a meet agree.** -/
lemma pairTCB_eq (p : M) (A B : EuclideanSpace ℝ (Fin 2) → M) {x : EuclideanSpace ℝ (Fin 4)}
    (hmeet : A (pairA x) = B (pairB x)) : pairTCB p B x = pairTC p A x := by
  rw [pairTC, pairTCB]
  exact congrArg (fun c : M => tangentCoordChange (𝓡 3) c p c) hmeet.symm

/-- **The derivative of the pair difference map, as a `HasFDerivAt` statement.** -/
theorem hasFDerivAt_rowPairDiff (p : M) (A B : EuclideanSpace ℝ (Fin 2) → M)
    (hA : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hB : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) B)
    {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ pairRegion p A B) :
    HasFDerivAt (rowPairDiff p A B)
      ((pairTC p A x).comp ((pairDA A x).comp pairA)
        - (pairTCB p B x).comp ((pairDB B x).comp pairB)) x := by
  obtain ⟨hx1, hx2⟩ := hx
  have h1 := fderiv_chart3_comp_hasFDerivAt A hA p hx1
  have h2 := fderiv_chart3_comp_hasFDerivAt B hB p hx2
  have h1' : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 4) => chr3 p (A (pairA y)))
      ((pairTC p A x).comp ((pairDA A x).comp pairA)) x := by
    have hc := h1.comp x (pairA.hasFDerivAt (x := x))
    simpa only [Function.comp_def, pairTC, pairDA, ContinuousLinearMap.comp_assoc] using hc
  have h2' : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 4) => chr3 p (B (pairB y)))
      ((pairTCB p B x).comp ((pairDB B x).comp pairB)) x := by
    have hc := h2.comp x (pairB.hasFDerivAt (x := x))
    simpa only [Function.comp_def, pairTCB, pairDB, ContinuousLinearMap.comp_assoc] using hc
  exact h1'.sub h2'

/-- **The derivative of the pair difference map as a continuous linear map.** -/
theorem fderiv_rowPairDiff_eq (p : M) (A B : EuclideanSpace ℝ (Fin 2) → M)
    (hA : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hB : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) B)
    {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ pairRegion p A B)
    (hmeet : A (pairA x) = B (pairB x)) :
    fderiv ℝ (rowPairDiff p A B) x =
      (pairTC p A x).comp ((pairDA A x).comp pairA)
        - (pairTCB p B x).comp ((pairDB B x).comp pairB) :=
  (hasFDerivAt_rowPairDiff p A B hA hB hx).fderiv

/-- The tangent coordinate change is bijective at a chart-contained point. -/
lemma pairTC_bijective (p : M) (A B : EuclideanSpace ℝ (Fin 2) → M)
    {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ pairRegion p A B) :
    Function.Bijective (pairTC p A x).toLinearMap := by
  have hsrc : A (pairA x) ∈ (extChartAt (𝓡 3) (A (pairA x))).source ∩
      (extChartAt (𝓡 3) p).source :=
    ⟨mem_extChartAt_source (A (pairA x)), by rw [← chr3_source]; exact hx.1⟩
  have hinj : Function.Injective (pairTC p A x) := by
    show Function.Injective (tangentCoordChange (𝓡 3) (A (pairA x)) p (A (pairA x)))
    exact tangentCoordChange_injective3 hsrc
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- **The range of the derivative of the pair difference map at a meet.** -/
theorem range_fderiv_rowPairDiff (p : M) (A B : EuclideanSpace ℝ (Fin 2) → M)
    (hA : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hB : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) B)
    {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ pairRegion p A B)
    (hmeet : A (pairA x) = B (pairB x)) :
    (fderiv ℝ (rowPairDiff p A B) x).range
      = ((pairDA A x).range ⊔ (pairDB B x).range).map (pairTC p A x).toLinearMap := by
  have hPQ : ∀ a b : EuclideanSpace ℝ (Fin 2), ∃ v, pairA v = a ∧ pairB v = b := pair_joint
  have hZ : (pairTC p A x).comp ((pairDA A x).comp pairA)
        - (pairTC p A x).comp ((pairDB B x).comp pairB)
      = (pairTC p A x).comp ((pairDA A x).comp pairA - (pairDB B x).comp pairB) :=
    (ContinuousLinearMap.comp_sub _ _ _).symm
  rw [fderiv_rowPairDiff_eq p A B hA hB hx hmeet, pairTCB_eq p A B hmeet, hZ,
    range_comp_eq_map, range_comp_sub_comp _ _ _ _ hPQ]

/-- **The pair row is the surjectivity of the charted difference map.** -/
theorem rowPairDiff_surjective_iff (p : M) (A B : EuclideanSpace ℝ (Fin 2) → M)
    (hA : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hB : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) B)
    {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ pairRegion p A B)
    (hmeet : A (pairA x) = B (pairB x)) :
    Function.Surjective (fderiv ℝ (rowPairDiff p A B) x) ↔
      (mfderiv (𝓡 2) (𝓡 3) A (pairA x)).range ⊔ (mfderiv (𝓡 2) (𝓡 3) B (pairB x)).range = ⊤ := by
  have hbij : Function.Bijective (pairTC p A x).toLinearMap := pairTC_bijective p A B hx
  have hkey : Function.Surjective (fderiv ℝ (rowPairDiff p A B) x) ↔
      (pairDA A x).range ⊔ (pairDB B x).range = ⊤ := by
    constructor
    · intro hsurj
      have h1 : (fderiv ℝ (rowPairDiff p A B) x).range = ⊤ := LinearMap.range_eq_top.mpr hsurj
      rw [range_fderiv_rowPairDiff p A B hA hB hx hmeet] at h1
      exact (map_eq_top_iff_of_bijective (pairTC p A x).toLinearMap hbij
        ((pairDA A x).range ⊔ (pairDB B x).range)).mp h1
    · intro h
      refine LinearMap.range_eq_top.mp ?_
      rw [range_fderiv_rowPairDiff p A B hA hB hx hmeet,
        map_eq_top_iff_of_bijective (pairTC p A x).toLinearMap hbij
          ((pairDA A x).range ⊔ (pairDB B x).range)]
      exact h
  rw [hkey]
  rfl


/-! ## The three block projections of the triple box `𝔼² × 𝔼² × 𝔼² = 𝔼⁶` -/

/-- The first block index of the six-box. -/
def tIdx0 (i : Fin 2) : Fin 6 := ⟨i.val, by omega⟩
/-- The second block index of the six-box. -/
def tIdx1 (i : Fin 2) : Fin 6 := ⟨i.val + 2, by omega⟩
/-- The third block index of the six-box. -/
def tIdx2 (i : Fin 2) : Fin 6 := ⟨i.val + 4, by omega⟩

@[simp] theorem tIdx0_val (i : Fin 2) : (tIdx0 i : ℕ) = i.val := rfl
@[simp] theorem tIdx1_val (i : Fin 2) : (tIdx1 i : ℕ) = i.val + 2 := rfl
@[simp] theorem tIdx2_val (i : Fin 2) : (tIdx2 i : ℕ) = i.val + 4 := rfl

/-- The projection of the six-box onto its first block, as a continuous linear map. -/
def triA : EuclideanSpace ℝ (Fin 6) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ContinuousLinearMap.comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm
    (ContinuousLinearMap.pi (fun i : Fin 2 => PiLp.proj 2 (fun _ : Fin 6 => ℝ) (tIdx0 i)))

/-- The projection of the six-box onto its second block. -/
def triB : EuclideanSpace ℝ (Fin 6) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ContinuousLinearMap.comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm
    (ContinuousLinearMap.pi (fun i : Fin 2 => PiLp.proj 2 (fun _ : Fin 6 => ℝ) (tIdx1 i)))

/-- The projection of the six-box onto its third block. -/
def triC : EuclideanSpace ℝ (Fin 6) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ContinuousLinearMap.comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm
    (ContinuousLinearMap.pi (fun i : Fin 2 => PiLp.proj 2 (fun _ : Fin 6 => ℝ) (tIdx2 i)))

lemma triA_apply (x : EuclideanSpace ℝ (Fin 6)) (i : Fin 2) : triA x i = x (tIdx0 i) := by
  simp [triA, PiLp.proj_apply]
lemma triB_apply (x : EuclideanSpace ℝ (Fin 6)) (i : Fin 2) : triB x i = x (tIdx1 i) := by
  simp [triB, PiLp.proj_apply]
lemma triC_apply (x : EuclideanSpace ℝ (Fin 6)) (i : Fin 2) : triC x i = x (tIdx2 i) := by
  simp [triC, PiLp.proj_apply]

/-- The point of the six-box with prescribed three blocks. -/
def triMk (p q r : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 6) :=
  WithLp.toLp 2 (fun i : Fin 6 =>
    if h : (i : ℕ) < 2 then p ⟨i, h⟩
    else if h2 : (i : ℕ) < 4 then q ⟨(i : ℕ) - 2, by omega⟩
    else r ⟨(i : ℕ) - 4, by omega⟩)

@[simp] lemma triA_triMk (p q r : EuclideanSpace ℝ (Fin 2)) : triA (triMk p q r) = p := by
  ext i
  simp only [triA_apply, triMk, WithLp.ofLp_toLp, tIdx0]
  rw [dif_pos (show (i.val : ℕ) < 2 by omega)]

@[simp] lemma triB_triMk (p q r : EuclideanSpace ℝ (Fin 2)) : triB (triMk p q r) = q := by
  ext i
  simp only [triB_apply, triMk, WithLp.ofLp_toLp, tIdx1]
  rw [dif_neg (show ¬ ((i.val + 2 : ℕ) < 2) by omega),
    dif_pos (show (i.val + 2 : ℕ) < 4 by omega)]
  exact congrArg q (Fin.ext (by simp))

@[simp] lemma triC_triMk (p q r : EuclideanSpace ℝ (Fin 2)) : triC (triMk p q r) = r := by
  ext i
  simp only [triC_apply, triMk, WithLp.ofLp_toLp, tIdx2]
  rw [dif_neg (show ¬ ((i.val + 4 : ℕ) < 2) by omega),
    dif_neg (show ¬ ((i.val + 4 : ℕ) < 4) by omega)]
  exact congrArg r (Fin.ext (by simp))

/-- Every point of the six-box is reconstructed from its three blocks. -/
@[simp] lemma triMk_triA (v : EuclideanSpace ℝ (Fin 6)) : triMk (triA v) (triB v) (triC v) = v := by
  ext i
  rw [triMk, WithLp.ofLp_toLp]
  by_cases h : (i : ℕ) < 2
  · rw [dif_pos h]
    rw [triA_apply]
    exact congrArg v (Fin.ext rfl)
  · rw [dif_neg h]
    by_cases h2 : (i : ℕ) < 4
    · rw [dif_pos h2]
      rw [triB_apply]
      refine congrArg v (Fin.ext ?_)
      simp only [tIdx1_val]
      omega
    · rw [dif_neg h2]
      rw [triC_apply]
      refine congrArg v (Fin.ext ?_)
      simp only [tIdx2_val]
      omega

/-- The three block projections are jointly surjective. -/
lemma tri_joint (p q r : EuclideanSpace ℝ (Fin 2)) :
    ∃ v : EuclideanSpace ℝ (Fin 6), triA v = p ∧ triB v = q ∧ triC v = r :=
  ⟨triMk p q r, triA_triMk p q r, triB_triMk p q r, triC_triMk p q r⟩

/-! ## The generic box-pair regularity -/

/-- **The box-restricted pair regularity**, for a space `M` charted on `𝔼³`: at every pair of box
points with a common value, the two class `2`-planes span the tangent space. -/
def BoxPairRegG (A B : EuclideanSpace ℝ (Fin 2) → M) : Prop :=
  ∀ y y' : EuclideanSpace ℝ (Fin 2), y ∈ Submission.Drive.unitBox 1 →
    y' ∈ Submission.Drive.unitBox 1 → A y = B y' →
    (mfderiv (𝓡 2) (𝓡 3) A y).range ⊔ (mfderiv (𝓡 2) (𝓡 3) B y').range = ⊤

/-- At `M = ℝP³` this is the workspace's `BoxPairReg`. -/
theorem boxPairRegG_iff (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) :
    BoxPairRegG A B ↔ BoxPairReg A B := Iff.rfl

lemma pairA_mem_unitBox {x : EuclideanSpace ℝ (Fin 4)}
    (hx : x ∈ Submission.Drive.unitBox 3) : pairA x ∈ Submission.Drive.unitBox 1 :=
  fun i => hx (pLo i)

lemma pairB_mem_unitBox {x : EuclideanSpace ℝ (Fin 4)}
    (hx : x ∈ Submission.Drive.unitBox 3) : pairB x ∈ Submission.Drive.unitBox 1 :=
  fun i => hx (pHi i)

lemma pairMk_mem_unitBox {y y' : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ Submission.Drive.unitBox 1) (hy' : y' ∈ Submission.Drive.unitBox 1) :
    pairMk y y' ∈ Submission.Drive.unitBox 3 := by
  intro i
  revert i
  refine Fin.addCases (m := 2) (n := 2)
    (motive := fun i => (pairMk y y') i ∈ Set.Icc (0 : ℝ) 1) ?_ ?_
  · intro i
    simpa only [pairMk, pLo, Fin.addCases_left] using hy i
  · intro j
    simpa only [pairMk, pHi, Fin.addCases_right] using hy' j

/-! ## The pair difference map of a *family* -/

section Family

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The chart region of the pair difference map of a family. -/
def pairFamRegion (c : M) (A B : P → EuclideanSpace ℝ (Fin 2) → M) :
    Set (P × EuclideanSpace ℝ (Fin 4)) :=
  {q | A q.1 (pairA q.2) ∈ (chr3 c).source ∧ B q.1 (pairB q.2) ∈ (chr3 c).source}

/-- The charted pair difference map of a family, in the chart at `c`. -/
def pairFamDiff (c : M) (A B : P → EuclideanSpace ℝ (Fin 2) → M)
    (q : P × EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 3) :=
  chr3 c (A q.1 (pairA q.2)) - chr3 c (B q.1 (pairB q.2))

lemma pairFamDiff_eq (c : M) (A B : P → EuclideanSpace ℝ (Fin 2) → M)
    (q : P × EuclideanSpace ℝ (Fin 4)) :
    pairFamDiff c A B q = rowPairDiff c (A q.1) (B q.1) q.2 := rfl

/-- The family pair difference map, as a function of the box point at a fixed parameter. -/
lemma pairFamDiff_fun (c : M) (A B : P → EuclideanSpace ℝ (Fin 2) → M) (p : P) :
    (fun y : EuclideanSpace ℝ (Fin 4) => pairFamDiff c A B (p, y))
      = fun y => rowPairDiff c (A p) (B p) y := rfl

lemma contMDiff_pairFamA (A : P → EuclideanSpace ℝ (Fin 2) → M)
    (hA : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => A q.1 q.2)) :
    ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 4))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 4) => A q.1 (pairA q.2)) := by
  have hmid : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 4)))
      (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 4) => (q.1, pairA q.2)) := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  exact hA.comp hmid

lemma contMDiff_pairFamB (B : P → EuclideanSpace ℝ (Fin 2) → M)
    (hB : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => B q.1 q.2)) :
    ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 4))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 4) => B q.1 (pairB q.2)) := by
  have hmid : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 4)))
      (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 4) => (q.1, pairB q.2)) := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  exact hB.comp hmid

/-- The chart region of the family is open. -/
lemma isOpen_pairFamRegion (c : M) (A B : P → EuclideanSpace ℝ (Fin 2) → M)
    (hA : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => A q.1 q.2))
    (hB : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => B q.1 q.2)) :
    IsOpen (pairFamRegion c A B) := by
  have h1 := (contMDiff_pairFamA A hA).continuous
  have h2 := (contMDiff_pairFamB B hB).continuous
  exact (h1.isOpen_preimage _ (chr3 c).open_source).inter
    (h2.isOpen_preimage _ (chr3 c).open_source)

/-- The charted pair difference map of a family is smooth on its chart region. -/
lemma contDiffOn_pairFamDiff (c : M) (A B : P → EuclideanSpace ℝ (Fin 2) → M)
    (hA : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => A q.1 q.2))
    (hB : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => B q.1 q.2)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pairFamDiff c A B) (pairFamRegion c A B) := by
  have hAq := contMDiff_pairFamA A hA
  have hBq := contMDiff_pairFamB B hB
  have h1 : ContMDiffOn (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 4))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 4) => chr3 c (A q.1 (pairA q.2)))
      (pairFamRegion c A B) :=
    (contMDiffOn_extChartAt (I := 𝓡 3) (x := c) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).comp
      hAq.contMDiffOn (fun q hq => hq.1)
  have h2 : ContMDiffOn (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 4))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 4) => chr3 c (B q.1 (pairB q.2)))
      (pairFamRegion c A B) :=
    (contMDiffOn_extChartAt (I := 𝓡 3) (x := c) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).comp
      hBq.contMDiffOn (fun q hq => hq.2)
  have h3 : ContMDiffOn (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 4))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (pairFamDiff c A B) (pairFamRegion c A B) := h1.sub h2
  exact contMDiffOn_iff_contDiffOn.mp h3

/-- The partial derivative of the family's pair difference map is continuous. -/
lemma continuousAt_pairFamDiff_fderiv (c : M) (A B : P → EuclideanSpace ℝ (Fin 2) → M)
    (hA : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => A q.1 q.2))
    (hB : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => B q.1 q.2))
    {q₀ : P × EuclideanSpace ℝ (Fin 4)} (hq₀ : q₀ ∈ pairFamRegion c A B) :
    ContinuousAt (fun q : P × EuclideanSpace ℝ (Fin 4) =>
      fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 4) => pairFamDiff c A B (q.1, y)) q.2) q₀ :=
  continuousAt_partial_fderiv (isOpen_pairFamRegion c A B hA hB)
    (pairFamDiff c A B) (contDiffOn_pairFamDiff c A B hA hB) hq₀

end Family

/-! ## The openness of the box-pair regularity -/

section Open

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- **The single-point form of the box-pair regularity**, with the box membership as the only
hypothesis: this is the predicate whose *eventual* truth at a base meet is the content of the
openness proof. -/
def pairGood (A B : EuclideanSpace ℝ (Fin 2) → M)
    (x : EuclideanSpace ℝ (Fin 4)) : Prop :=
  x ∈ Submission.Drive.unitBox 3 →
    (mfderiv (𝓡 2) (𝓡 3) A (pairA x)).range ⊔ (mfderiv (𝓡 2) (𝓡 3) B (pairB x)).range = ⊤

lemma boxPairRegG_iff_forall_good (A B : EuclideanSpace ℝ (Fin 2) → M) :
    BoxPairRegG A B ↔ ∀ x, A (pairA x) = B (pairB x) → pairGood A B x := by
  constructor
  · intro h x hx
    intro hbox
    exact h (pairA x) (pairB x) (pairA_mem_unitBox hbox) (pairB_mem_unitBox hbox) hx
  · intro h y y' hy hy' hmeet
    have hbox : pairMk y y' ∈ Submission.Drive.unitBox 3 := pairMk_mem_unitBox hy hy'
    have hx : A (pairA (pairMk y y')) = B (pairB (pairMk y y')) := by
      simpa only [pairA_pairMk, pairB_pairMk] using hmeet
    have hAt : (mfderiv (𝓡 2) (𝓡 3) A (pairA (pairMk y y'))).range
        ⊔ (mfderiv (𝓡 2) (𝓡 3) B (pairB (pairMk y y'))).range = ⊤ :=
      h (pairMk y y') hx hbox
    rw [pairA_pairMk, pairB_pairMk] at hAt
    exact hAt

/-- **The local step**: at a base meet of the box-pair condition, the single-point predicate holds
for all nearby parameters and box points. -/
theorem pairGood_eventually_at_meet (A B : P → EuclideanSpace ℝ (Fin 2) → M)
    (hA : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => A q.1 q.2))
    (hB : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => B q.1 q.2))
    (h0 : BoxPairRegG (A 0) (B 0))
    {x₀ : EuclideanSpace ℝ (Fin 4)} (hx₀ : x₀ ∈ Submission.Drive.unitBox 3)
    (hmeet₀ : A 0 (pairA x₀) = B 0 (pairB x₀)) :
    ∀ᶠ q : P × EuclideanSpace ℝ (Fin 4) in 𝓝 ((0 : P), x₀),
      A q.1 (pairA q.2) = B q.1 (pairB q.2) → pairGood (A q.1) (B q.1) q.2 := by
  classical
  have hbase := (boxPairRegG_iff_forall_good (A 0) (B 0)).mp h0 x₀ hmeet₀
  set c : M := A 0 (pairA x₀) with hc
  have hreg0 : ((0 : P), x₀) ∈ pairFamRegion c A B := by
    refine ⟨?_, ?_⟩
    · show A 0 (pairA x₀) ∈ (chr3 c).source
      rw [← hc]
      exact mem_chart_source _ _
    · show B 0 (pairB x₀) ∈ (chr3 c).source
      rw [← hmeet₀]
      exact mem_chart_source _ _
  have hA0 : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (A 0) :=
    hA.comp (loopBox_contMDiff_const 0)
  have hB0 : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (B 0) :=
    hB.comp (loopBox_contMDiff_const 0)
  have hsurj0 : Function.Surjective (fderiv ℝ (rowPairDiff c (A 0) (B 0)) x₀) :=
    (rowPairDiff_surjective_iff c (A 0) (B 0) hA0 hB0 hreg0 hmeet₀).mpr (hbase hx₀)
  have hEvReg : ∀ᶠ q : P × EuclideanSpace ℝ (Fin 4) in 𝓝 ((0 : P), x₀),
      q ∈ pairFamRegion c A B :=
    (isOpen_pairFamRegion c A B hA hB).mem_nhds hreg0
  have hcontG := continuousAt_pairFamDiff_fderiv c A B hA hB hreg0
  have hEvSurj : ∀ᶠ q : P × EuclideanSpace ℝ (Fin 4) in 𝓝 ((0 : P), x₀),
      Function.Surjective (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 4) =>
        pairFamDiff c A B (q.1, y)) q.2) :=
    hcontG.preimage_mem_nhds
      ((Work.Sard.isOpen_setOf_surjective_clm (E := EuclideanSpace ℝ (Fin 4))
        (F := EuclideanSpace ℝ (Fin 3))).mem_nhds hsurj0)
  filter_upwards [hEvReg, hEvSurj] with q hreg hsurj hmeet
  have hAq : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (A q.1) :=
    hA.comp (loopBox_contMDiff_const q.1)
  have hBq : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (B q.1) :=
    hB.comp (loopBox_contMDiff_const q.1)
  have hsurj' : Function.Surjective (fderiv ℝ (rowPairDiff c (A q.1) (B q.1)) q.2) := by
    have h2 : Function.Surjective
        (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 4) => pairFamDiff c A B (q.1, y)) q.2) := hsurj
    rwa [pairFamDiff_fun c A B q.1] at h2
  intro _
  exact (rowPairDiff_surjective_iff c (A q.1) (B q.1) hAq hBq hreg hmeet).mp hsurj'

/-- **The box-pair regularity is an open property of the family parameter.** -/
theorem eventually_boxPairRegG_at (A B : P → EuclideanSpace ℝ (Fin 2) → M)
    (hA : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => A q.1 q.2))
    (hB : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => B q.1 q.2))
    (h0 : BoxPairRegG (A 0) (B 0)) :
    ∀ᶠ p in 𝓝 (0 : P), BoxPairRegG (A p) (B p) := by
  have hmeet_closed : IsClosed {q : P × EuclideanSpace ℝ (Fin 4) |
      A q.1 (pairA q.2) = B q.1 (pairB q.2)} :=
    isClosed_eq ((contMDiff_pairFamA A hA).continuous) ((contMDiff_pairFamB B hB).continuous)
  have hmain := eventually_forall_meet_of_eventually (P := P) (X := EuclideanSpace ℝ (Fin 4))
    (fun p x => A p (pairA x) = B p (pairB x)) hmeet_closed
    (Submission.Drive.unitBox 3) (isCompact_unitBox 3)
    (fun p x => pairGood (A p) (B p) x)
    (fun p y hy => by
      by_contra hcon
      exact hy (fun hbox => absurd hbox hcon))
    (fun x hx hmeet => pairGood_eventually_at_meet A B hA hB h0 hx hmeet)
  refine hmain.mono fun p hp => ?_
  refine (boxPairRegG_iff_forall_good (A p) (B p)).mpr fun x hx => hp x hx

end Open

/-! ## The triple row and its charted difference map -/

/-- The tangent coordinate change of a triple difference map, first block. -/
def triTF (p : M) (F : EuclideanSpace ℝ (Fin 2) → M) (x : EuclideanSpace ℝ (Fin 6)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  tangentCoordChange (𝓡 3) (F (triA x)) p (F (triA x))

/-- The tangent coordinate change of a triple difference map, second block. -/
def triTA (p : M) (A : EuclideanSpace ℝ (Fin 2) → M) (x : EuclideanSpace ℝ (Fin 6)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  tangentCoordChange (𝓡 3) (A (triB x)) p (A (triB x))

/-- The tangent coordinate change of a triple difference map, third block. -/
def triTB (p : M) (B : EuclideanSpace ℝ (Fin 2) → M) (x : EuclideanSpace ℝ (Fin 6)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  tangentCoordChange (𝓡 3) (B (triC x)) p (B (triC x))

/-- The derivative of the first plane presentation of a triple. -/
def triD1 (F : EuclideanSpace ℝ (Fin 2) → M) (x : EuclideanSpace ℝ (Fin 6)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  mfderiv (𝓡 2) (𝓡 3) F (triA x)

/-- The derivative of the second plane presentation of a triple. -/
def triD2 (A : EuclideanSpace ℝ (Fin 2) → M) (x : EuclideanSpace ℝ (Fin 6)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  mfderiv (𝓡 2) (𝓡 3) A (triB x)

/-- The derivative of the third plane presentation of a triple. -/
def triD3 (B : EuclideanSpace ℝ (Fin 2) → M) (x : EuclideanSpace ℝ (Fin 6)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  mfderiv (𝓡 2) (𝓡 3) B (triC x)

/-- The chart region of the triple difference map. -/
def tripleRegion (p : M) (F A B : EuclideanSpace ℝ (Fin 2) → M) :
    Set (EuclideanSpace ℝ (Fin 6)) :=
  {x | F (triA x) ∈ (chr3 p).source ∧ A (triB x) ∈ (chr3 p).source ∧
    B (triC x) ∈ (chr3 p).source}

/-- The charted difference map of three plane presentations. -/
def rowTripleDiff (p : M) (F A B : EuclideanSpace ℝ (Fin 2) → M) :
    EuclideanSpace ℝ (Fin 6) → EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) :=
  fun x => (chr3 p (F (triA x)) - chr3 p (A (triB x)),
            chr3 p (F (triA x)) - chr3 p (B (triC x)))

/-- **The three tangent coordinate changes of a triple meet agree.** -/
lemma triTA_eq (p : M) (F A : EuclideanSpace ℝ (Fin 2) → M) {x : EuclideanSpace ℝ (Fin 6)}
    (h1 : F (triA x) = A (triB x)) : triTA p A x = triTF p F x := by
  rw [triTA, triTF]
  exact congrArg (fun c : M => tangentCoordChange (𝓡 3) c p c) h1.symm

lemma triTB_eq (p : M) (F B : EuclideanSpace ℝ (Fin 2) → M) {x : EuclideanSpace ℝ (Fin 6)}
    (h2 : F (triA x) = B (triC x)) : triTB p B x = triTF p F x := by
  rw [triTB, triTF]
  exact congrArg (fun c : M => tangentCoordChange (𝓡 3) c p c) h2.symm

/-- **The derivative of the triple difference map, as a `HasFDerivAt` statement.** -/
theorem hasFDerivAt_rowTripleDiff (p : M) (F A B : EuclideanSpace ℝ (Fin 2) → M)
    (hF : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hA : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hB : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) B)
    {x : EuclideanSpace ℝ (Fin 6)} (hx : x ∈ tripleRegion p F A B) :
    HasFDerivAt (rowTripleDiff p F A B)
      (((triTF p F x).comp ((triD1 F x).comp triA)
          - (triTA p A x).comp ((triD2 A x).comp triB)).prod
        ((triTF p F x).comp ((triD1 F x).comp triA)
          - (triTB p B x).comp ((triD3 B x).comp triC))) x := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  have h1 := fderiv_chart3_comp_hasFDerivAt F hF p hx1
  have h2 := fderiv_chart3_comp_hasFDerivAt A hA p hx2
  have h3 := fderiv_chart3_comp_hasFDerivAt B hB p hx3
  have h1F : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 6) => chr3 p (F (triA x)))
      ((triTF p F x).comp ((triD1 F x).comp triA)) x := by
    have hc := h1.comp x (triA.hasFDerivAt (x := x))
    simpa only [Function.comp_def, triTF, triD1, ContinuousLinearMap.comp_assoc] using hc
  have h2A : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 6) => chr3 p (A (triB x)))
      ((triTA p A x).comp ((triD2 A x).comp triB)) x := by
    have hc := h2.comp x (triB.hasFDerivAt (x := x))
    simpa only [Function.comp_def, triTA, triD2, ContinuousLinearMap.comp_assoc] using hc
  have h3B : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 6) => chr3 p (B (triC x)))
      ((triTB p B x).comp ((triD3 B x).comp triC)) x := by
    have hc := h3.comp x (triC.hasFDerivAt (x := x))
    simpa only [Function.comp_def, triTB, triD3, ContinuousLinearMap.comp_assoc] using hc
  exact HasFDerivAt.prodMk (h1F.sub h2A) (h1F.sub h3B)

/-- **The derivative of the triple difference map, in the normalised form.** -/
theorem fderiv_rowTripleDiff_eq (p : M) (F A B : EuclideanSpace ℝ (Fin 2) → M)
    (hF : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hA : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hB : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) B)
    {x : EuclideanSpace ℝ (Fin 6)} (hx : x ∈ tripleRegion p F A B)
    (h1 : F (triA x) = A (triB x)) (h2 : F (triA x) = B (triC x)) :
    fderiv ℝ (rowTripleDiff p F A B) x =
      ((triTF p F x).comp ((triD1 F x).comp triA - (triD2 A x).comp triB)).prod
        ((triTF p F x).comp ((triD1 F x).comp triA - (triD3 B x).comp triC)) := by
  have e1 : (triTF p F x).comp ((triD1 F x).comp triA)
        - (triTA p A x).comp ((triD2 A x).comp triB)
      = (triTF p F x).comp ((triD1 F x).comp triA - (triD2 A x).comp triB) := by
    rw [triTA_eq p F A h1, ContinuousLinearMap.comp_sub]
  have e2 : (triTF p F x).comp ((triD1 F x).comp triA)
        - (triTB p B x).comp ((triD3 B x).comp triC)
      = (triTF p F x).comp ((triD1 F x).comp triA - (triD3 B x).comp triC) := by
    rw [triTB_eq p F B h2, ContinuousLinearMap.comp_sub]
  rw [(hasFDerivAt_rowTripleDiff p F A B hF hA hB hx).fderiv, e1, e2]

/-- `triMk` of the three zero blocks is zero. -/
@[simp] lemma triMk_zero : triMk (0 : EuclideanSpace ℝ (Fin 2)) 0 0
    = (0 : EuclideanSpace ℝ (Fin 6)) := by
  have h : triMk (triA (0 : EuclideanSpace ℝ (Fin 6))) (triB 0) (triC 0) = 0 := triMk_triA 0
  rwa [map_zero, map_zero, map_zero] at h

/-- **The linear algebra of the triple row**: the kernel of the difference pair is trivial exactly
when the three derivatives are injective and their `2`-planes have trivial triple intersection. -/
theorem ker_tri_eq_bot_iff (φ ψ χ : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    ((φ.comp triA - ψ.comp triB).ker ⊓ (φ.comp triA - χ.comp triC).ker = ⊥) ↔
      (Function.Injective φ ∧ Function.Injective ψ ∧ Function.Injective χ ∧
        φ.range ⊓ ψ.range ⊓ χ.range = ⊥) := by
  have hmemX : ∀ v : EuclideanSpace ℝ (Fin 6),
      (v ∈ (φ.comp triA - ψ.comp triB).ker) ↔ φ (triA v) = ψ (triB v) := by
    intro v
    rw [LinearMap.mem_ker]
    change φ (triA v) - ψ (triB v) = 0 ↔ φ (triA v) = ψ (triB v)
    exact sub_eq_zero
  have hmemY : ∀ v : EuclideanSpace ℝ (Fin 6),
      (v ∈ (φ.comp triA - χ.comp triC).ker) ↔ φ (triA v) = χ (triC v) := by
    intro v
    rw [LinearMap.mem_ker]
    change φ (triA v) - χ (triC v) = 0 ↔ φ (triA v) = χ (triC v)
    exact sub_eq_zero
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b hab
      obtain ⟨v, hv1, hv2, hv3⟩ := tri_joint (a - b) 0 0
      have hX : v ∈ (φ.comp triA - ψ.comp triB).ker := by
        rw [hmemX v, hv1, hv2, map_zero, map_sub, hab, sub_self]
      have hY : v ∈ (φ.comp triA - χ.comp triC).ker := by
        rw [hmemY v, hv1, hv3, map_zero, map_sub, hab, sub_self]
      have hv : v ∈ (φ.comp triA - ψ.comp triB).ker ⊓ (φ.comp triA - χ.comp triC).ker :=
        ⟨hX, hY⟩
      rw [h] at hv
      have hv0 : v = 0 := by simpa using hv
      have hsub : a - b = 0 := by rw [← hv1, hv0, map_zero]
      exact sub_eq_zero.mp hsub
    · intro a b hab
      obtain ⟨v, hv1, hv2, hv3⟩ := tri_joint 0 (a - b) 0
      have hX : v ∈ (φ.comp triA - ψ.comp triB).ker := by
        rw [hmemX v, hv1, hv2, map_zero, map_sub, hab, sub_self]
      have hY : v ∈ (φ.comp triA - χ.comp triC).ker := by
        rw [hmemY v, hv1, hv3, map_zero, map_zero]
      have hv : v ∈ (φ.comp triA - ψ.comp triB).ker ⊓ (φ.comp triA - χ.comp triC).ker :=
        ⟨hX, hY⟩
      rw [h] at hv
      have hv0 : v = 0 := by simpa using hv
      have hsub : a - b = 0 := by rw [← hv2, hv0, map_zero]
      exact sub_eq_zero.mp hsub
    · intro a b hab
      obtain ⟨v, hv1, hv2, hv3⟩ := tri_joint 0 0 (a - b)
      have hX : v ∈ (φ.comp triA - ψ.comp triB).ker := by
        rw [hmemX v, hv1, hv2, map_zero, map_zero]
      have hY : v ∈ (φ.comp triA - χ.comp triC).ker := by
        rw [hmemY v, hv1, hv3, map_zero, map_sub, hab, sub_self]
      have hv : v ∈ (φ.comp triA - ψ.comp triB).ker ⊓ (φ.comp triA - χ.comp triC).ker :=
        ⟨hX, hY⟩
      rw [h] at hv
      have hv0 : v = 0 := by simpa using hv
      have hsub : a - b = 0 := by rw [← hv3, hv0, map_zero]
      exact sub_eq_zero.mp hsub
    · rw [Submodule.eq_bot_iff]
      rintro w hw
      obtain ⟨hw1, hw2⟩ := Submodule.mem_inf.mp hw
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := Submodule.mem_inf.mp hw1
      obtain ⟨c, hc⟩ := hw2
      obtain ⟨v, hv1, hv2, hv3⟩ := tri_joint a b c
      have hX : v ∈ (φ.comp triA - ψ.comp triB).ker := by
        rw [hmemX v, hv1, hv2]
        exact ha.trans hb.symm
      have hY : v ∈ (φ.comp triA - χ.comp triC).ker := by
        rw [hmemY v, hv1, hv3]
        exact ha.trans hc.symm
      have hv : v ∈ (φ.comp triA - ψ.comp triB).ker ⊓ (φ.comp triA - χ.comp triC).ker :=
        ⟨hX, hY⟩
      rw [h] at hv
      have hv0 : v = 0 := by simpa using hv
      have ha0 : a = 0 := by rw [← hv1, hv0, map_zero]
      rw [← ha, ha0, map_zero]
  · rintro ⟨hφ, hψ, hχ, htri⟩
    rw [Submodule.eq_bot_iff]
    intro v hv
    obtain ⟨hX, hY⟩ := Submodule.mem_inf.mp hv
    have h1 : φ (triA v) = ψ (triB v) := (hmemX v).mp hX
    have h2 : φ (triA v) = χ (triC v) := (hmemY v).mp hY
    have hmem : φ (triA v) ∈ φ.range ⊓ ψ.range ⊓ χ.range := by
      refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
      · exact ⟨triA v, rfl⟩
      · exact ⟨triB v, h1.symm⟩
      · exact ⟨triC v, h2.symm⟩
    rw [htri] at hmem
    have h0 : φ (triA v) = 0 := by simpa using hmem
    have hvA : triA v = 0 := hφ (by rw [h0, map_zero])
    have hvB : triB v = 0 := hψ (by rw [← h1, h0, map_zero])
    have hvC : triC v = 0 := hχ (by rw [← h2, h0, map_zero])
    calc v = triMk (triA v) (triB v) (triC v) := (triMk_triA v).symm
      _ = triMk 0 0 0 := by rw [hvA, hvB, hvC]
      _ = 0 := triMk_zero

/-- **The triple row is the injectivity of the charted difference map.** -/
theorem rowTripleDiff_injective_iff (p : M) (F A B : EuclideanSpace ℝ (Fin 2) → M)
    (hF : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hA : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hB : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) B)
    {x : EuclideanSpace ℝ (Fin 6)} (hx : x ∈ tripleRegion p F A B)
    (h1 : F (triA x) = A (triB x)) (h2 : F (triA x) = B (triC x)) :
    Function.Injective (fderiv ℝ (rowTripleDiff p F A B) x) ↔
      (Function.Injective (mfderiv (𝓡 2) (𝓡 3) F (triA x)) ∧
       Function.Injective (mfderiv (𝓡 2) (𝓡 3) A (triB x)) ∧
       Function.Injective (mfderiv (𝓡 2) (𝓡 3) B (triC x)) ∧
       (mfderiv (𝓡 2) (𝓡 3) F (triA x)).range ⊓ (mfderiv (𝓡 2) (𝓡 3) A (triB x)).range ⊓
         (mfderiv (𝓡 2) (𝓡 3) B (triC x)).range = ⊥) := by
  have hsrc : F (triA x) ∈ (extChartAt (𝓡 3) (F (triA x))).source ∩
      (extChartAt (𝓡 3) p).source :=
    ⟨mem_extChartAt_source (F (triA x)), by rw [← chr3_source]; exact hx.1⟩
  have hker : (triTF p F x).ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    show Function.Injective (tangentCoordChange (𝓡 3) (F (triA x)) p (F (triA x)))
    exact tangentCoordChange_injective3 hsrc
  set Xp : EuclideanSpace ℝ (Fin 6) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (triD1 F x).comp triA - (triD2 A x).comp triB with hXp
  set Yp : EuclideanSpace ℝ (Fin 6) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (triD1 F x).comp triA - (triD3 B x).comp triC with hYp
  have hlin : fderiv ℝ (rowTripleDiff p F A B) x
      = ((triTF p F x).comp Xp).prod ((triTF p F x).comp Yp) := by
    rw [fderiv_rowTripleDiff_eq p F A B hF hA hB hx h1 h2, hXp, hYp]
  rw [hlin]
  have hiff : Function.Injective (((triTF p F x).comp Xp).prod ((triTF p F x).comp Yp)) ↔
      (((triTF p F x).comp Xp).prod ((triTF p F x).comp Yp)).ker = ⊥ :=
    LinearMap.ker_eq_bot.symm
  rw [hiff, ker_prod_clm, ker_comp_clm_eq_of_ker_eq_bot hker,
    ker_comp_clm_eq_of_ker_eq_bot hker, hXp, hYp]
  exact ker_tri_eq_bot_iff (triD1 F x) (triD2 A x) (triD3 B x)

/-! ## Infinite-dimensional-to-finite: injectivity vs surjectivity -/

/-- For an endomorphism of a finite-dimensional space, injectivity and surjectivity agree. -/
lemma clm_injective_iff_surjective_of_finrank {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (h : Module.finrank ℝ E = Module.finrank ℝ F) (L : E →L[ℝ] F) :
    Function.Injective L ↔ Function.Surjective L :=
  LinearMap.injective_iff_surjective_of_finrank_eq_finrank h

/-- **The set of injective continuous linear maps between finite-dimensional spaces of the same
dimension is open** (through the open set of surjective ones). -/
lemma isOpen_setOf_injective_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (h : Module.finrank ℝ E = Module.finrank ℝ F) :
    IsOpen {L : E →L[ℝ] F | Function.Injective L} := by
  have hset : {L : E →L[ℝ] F | Function.Injective L}
      = {L : E →L[ℝ] F | Function.Surjective L} := by
    ext L; exact clm_injective_iff_surjective_of_finrank h L
  rw [hset]
  exact Work.Sard.isOpen_setOf_surjective_clm

/-! ## The generic box end-triple regularity -/

/-- **The box-restricted end-triple regularity**, for a space `M` charted on `𝔼³`. -/
def BoxEndTripleRegG (F A B : EuclideanSpace ℝ (Fin 2) → M) : Prop :=
  ∀ y₀ y₁ y₂ : EuclideanSpace ℝ (Fin 2),
    (∀ k : Fin 3, (![y₀, y₁, y₂] : Fin 3 → EuclideanSpace ℝ (Fin 2)) k ∈
      Submission.Drive.unitBox 1) → F y₀ = A y₁ → F y₀ = B y₂ →
    (Function.Injective (mfderiv (𝓡 2) (𝓡 3) F y₀) ∧
     Function.Injective (mfderiv (𝓡 2) (𝓡 3) A y₁) ∧
     Function.Injective (mfderiv (𝓡 2) (𝓡 3) B y₂) ∧
     (mfderiv (𝓡 2) (𝓡 3) F y₀).range ⊓ (mfderiv (𝓡 2) (𝓡 3) A y₁).range ⊓
       (mfderiv (𝓡 2) (𝓡 3) B y₂).range = ⊥)

/-- At `M = ℝP³` this is the workspace's `BoxEndTripleReg`. -/
theorem boxEndTripleRegG_iff
    (F A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) :
    BoxEndTripleRegG F A B ↔ BoxEndTripleReg F A B := Iff.rfl

lemma triA_mem_unitBox {x : EuclideanSpace ℝ (Fin 6)}
    (hx : x ∈ Submission.Drive.unitBox 5) : triA x ∈ Submission.Drive.unitBox 1 :=
  fun i => hx (tIdx0 i)

lemma triB_mem_unitBox {x : EuclideanSpace ℝ (Fin 6)}
    (hx : x ∈ Submission.Drive.unitBox 5) : triB x ∈ Submission.Drive.unitBox 1 :=
  fun i => hx (tIdx1 i)

lemma triC_mem_unitBox {x : EuclideanSpace ℝ (Fin 6)}
    (hx : x ∈ Submission.Drive.unitBox 5) : triC x ∈ Submission.Drive.unitBox 1 :=
  fun i => hx (tIdx2 i)

lemma triMk_mem_unitBox {y₀ y₁ y₂ : EuclideanSpace ℝ (Fin 2)}
    (hy : ∀ k : Fin 3, (![y₀, y₁, y₂] : Fin 3 → EuclideanSpace ℝ (Fin 2)) k ∈
      Submission.Drive.unitBox 1) :
    triMk y₀ y₁ y₂ ∈ Submission.Drive.unitBox 5 := by
  intro i
  rw [triMk, WithLp.ofLp_toLp]
  by_cases h : (i : ℕ) < 2
  · rw [dif_pos h]; exact hy 0 ⟨i, h⟩
  · rw [dif_neg h]
    by_cases h2 : (i : ℕ) < 4
    · rw [dif_pos h2]; exact hy 1 _
    · rw [dif_neg h2]; exact hy 2 _

/-! ## The triple difference map of a *family* -/

section TripleFamily

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The chart region of the triple difference map of a family. -/
def tripleFamRegion (c : M) (F A B : P → EuclideanSpace ℝ (Fin 2) → M) :
    Set (P × EuclideanSpace ℝ (Fin 6)) :=
  {q | F q.1 (triA q.2) ∈ (chr3 c).source ∧ A q.1 (triB q.2) ∈ (chr3 c).source ∧
    B q.1 (triC q.2) ∈ (chr3 c).source}

/-- The charted triple difference map of a family, in the chart at `c`. -/
def tripleFamDiff (c : M) (F A B : P → EuclideanSpace ℝ (Fin 2) → M)
    (q : P × EuclideanSpace ℝ (Fin 6)) :
    EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) :=
  (chr3 c (F q.1 (triA q.2)) - chr3 c (A q.1 (triB q.2)),
   chr3 c (F q.1 (triA q.2)) - chr3 c (B q.1 (triC q.2)))

lemma tripleFamDiff_fun (c : M) (F A B : P → EuclideanSpace ℝ (Fin 2) → M) (p : P) :
    (fun y : EuclideanSpace ℝ (Fin 6) => tripleFamDiff c F A B (p, y))
      = fun y => rowTripleDiff c (F p) (A p) (B p) y := rfl

lemma contMDiff_tripleFamA (A : P → EuclideanSpace ℝ (Fin 2) → M)
    (hA : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => A q.1 q.2)) (k : Fin 3) :
    ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 6))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 6) =>
        A q.1 (((![triA, triB, triC] : Fin 3 → EuclideanSpace ℝ (Fin 6) →L[ℝ]
          EuclideanSpace ℝ (Fin 2)) k) q.2)) := by
  have hmid : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 6)))
      (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 6) =>
        (q.1, (![triA, triB, triC] : Fin 3 → _) k q.2)) := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  exact hA.comp hmid

lemma isOpen_tripleFamRegion (c : M) (F A B : P → EuclideanSpace ℝ (Fin 2) → M)
    (hF : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => F q.1 q.2))
    (hA : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => A q.1 q.2))
    (hB : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => B q.1 q.2)) :
    IsOpen (tripleFamRegion c F A B) := by
  have h1 := (contMDiff_tripleFamA F hF 0).continuous
  have h2 := (contMDiff_tripleFamA A hA 1).continuous
  have h3 := (contMDiff_tripleFamA B hB 2).continuous
  have e1 : (![triA, triB, triC] : Fin 3 → EuclideanSpace ℝ (Fin 6) →L[ℝ]
      EuclideanSpace ℝ (Fin 2)) 0 = triA := rfl
  have e2 : (![triA, triB, triC] : Fin 3 → EuclideanSpace ℝ (Fin 6) →L[ℝ]
      EuclideanSpace ℝ (Fin 2)) 1 = triB := rfl
  have e3 : (![triA, triB, triC] : Fin 3 → EuclideanSpace ℝ (Fin 6) →L[ℝ]
      EuclideanSpace ℝ (Fin 2)) 2 = triC := rfl
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [show tripleFamRegion c F A B
      = ((fun q : P × EuclideanSpace ℝ (Fin 6) => F q.1 (triA q.2)) ⁻¹' (chr3 c).source ∩
        (fun q : P × EuclideanSpace ℝ (Fin 6) => A q.1 (triB q.2)) ⁻¹' (chr3 c).source ∩
        (fun q : P × EuclideanSpace ℝ (Fin 6) => B q.1 (triC q.2)) ⁻¹' (chr3 c).source) from by
    ext q
    simp only [tripleFamRegion, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, and_assoc]]
  exact ((h1.isOpen_preimage _ (chr3 c).open_source).inter
    (h2.isOpen_preimage _ (chr3 c).open_source)).inter
    (h3.isOpen_preimage _ (chr3 c).open_source)

lemma contDiffOn_tripleFamDiff (c : M) (F A B : P → EuclideanSpace ℝ (Fin 2) → M)
    (hF : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => F q.1 q.2))
    (hA : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => A q.1 q.2))
    (hB : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => B q.1 q.2)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (tripleFamDiff c F A B)
      (tripleFamRegion c F A B) := by
  have hch := contMDiffOn_extChartAt (I := 𝓡 3) (x := c) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
  have e1 : (![triA, triB, triC] : Fin 3 → EuclideanSpace ℝ (Fin 6) →L[ℝ]
      EuclideanSpace ℝ (Fin 2)) 0 = triA := rfl
  have e2 : (![triA, triB, triC] : Fin 3 → EuclideanSpace ℝ (Fin 6) →L[ℝ]
      EuclideanSpace ℝ (Fin 2)) 1 = triB := rfl
  have e3 : (![triA, triB, triC] : Fin 3 → EuclideanSpace ℝ (Fin 6) →L[ℝ]
      EuclideanSpace ℝ (Fin 2)) 2 = triC := rfl
  have h1 : ContMDiffOn (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 6))) (𝓡 3)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 6) => chr3 c (F q.1 (triA q.2)))
      (tripleFamRegion c F A B) := by
    have hbase := contMDiff_tripleFamA F hF 0
    rw [e1] at hbase
    exact hch.comp hbase.contMDiffOn (fun q hq => hq.1)
  have h2 : ContMDiffOn (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 6))) (𝓡 3)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 6) => chr3 c (A q.1 (triB q.2)))
      (tripleFamRegion c F A B) := by
    have hbase := contMDiff_tripleFamA A hA 1
    rw [e2] at hbase
    exact hch.comp hbase.contMDiffOn (fun q hq => hq.2.1)
  have h3 : ContMDiffOn (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 6))) (𝓡 3)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 6) => chr3 c (B q.1 (triC q.2)))
      (tripleFamRegion c F A B) := by
    have hbase := contMDiff_tripleFamA B hB 2
    rw [e3] at hbase
    exact hch.comp hbase.contMDiffOn (fun q hq => hq.2.2)
  have h1' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 6) => chr3 c (F q.1 (triA q.2)))
      (tripleFamRegion c F A B) := contMDiffOn_iff_contDiffOn.mp h1
  have h2' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 6) => chr3 c (A q.1 (triB q.2)))
      (tripleFamRegion c F A B) := contMDiffOn_iff_contDiffOn.mp h2
  have h3' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 6) => chr3 c (B q.1 (triC q.2)))
      (tripleFamRegion c F A B) := contMDiffOn_iff_contDiffOn.mp h3
  exact (h1'.sub h2').prodMk (h1'.sub h3')

lemma continuousAt_tripleFamDiff_fderiv (c : M) (F A B : P → EuclideanSpace ℝ (Fin 2) → M)
    (hF : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => F q.1 q.2))
    (hA : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => A q.1 q.2))
    (hB : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => B q.1 q.2))
    {q₀ : P × EuclideanSpace ℝ (Fin 6)} (hq₀ : q₀ ∈ tripleFamRegion c F A B) :
    ContinuousAt (fun q : P × EuclideanSpace ℝ (Fin 6) =>
      fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 6) => tripleFamDiff c F A B (q.1, y)) q.2) q₀ :=
  continuousAt_partial_fderiv (isOpen_tripleFamRegion c F A B hF hA hB)
    (tripleFamDiff c F A B) (contDiffOn_tripleFamDiff c F A B hF hA hB) hq₀

end TripleFamily

/-! ## The openness of the box end-triple regularity -/

section TripleOpen

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- **The single-point form of the box end-triple regularity.** -/
def tripleGood (F A B : EuclideanSpace ℝ (Fin 2) → M)
    (x : EuclideanSpace ℝ (Fin 6)) : Prop :=
  x ∈ Submission.Drive.unitBox 5 →
    (Function.Injective (mfderiv (𝓡 2) (𝓡 3) F (triA x)) ∧
     Function.Injective (mfderiv (𝓡 2) (𝓡 3) A (triB x)) ∧
     Function.Injective (mfderiv (𝓡 2) (𝓡 3) B (triC x)) ∧
     (mfderiv (𝓡 2) (𝓡 3) F (triA x)).range ⊓ (mfderiv (𝓡 2) (𝓡 3) A (triB x)).range ⊓
       (mfderiv (𝓡 2) (𝓡 3) B (triC x)).range = ⊥)

lemma boxEndTripleRegG_iff_forall_good (F A B : EuclideanSpace ℝ (Fin 2) → M) :
    BoxEndTripleRegG F A B ↔ ∀ x, F (triA x) = A (triB x) → F (triA x) = B (triC x) →
      tripleGood F A B x := by
  constructor
  · intro h x h1 h2 hbox
    exact h (triA x) (triB x) (triC x)
      (by
        intro k
        fin_cases k
        · simpa using triA_mem_unitBox hbox
        · simpa using triB_mem_unitBox hbox
        · simpa using triC_mem_unitBox hbox) h1 h2
  · intro h y₀ y₁ y₂ hy h1 h2
    have hbox : triMk y₀ y₁ y₂ ∈ Submission.Drive.unitBox 5 := triMk_mem_unitBox hy
    have h1' : F (triA (triMk y₀ y₁ y₂)) = A (triB (triMk y₀ y₁ y₂)) := by
      simpa only [triA_triMk, triB_triMk, triC_triMk] using h1
    have h2' : F (triA (triMk y₀ y₁ y₂)) = B (triC (triMk y₀ y₁ y₂)) := by
      simpa only [triA_triMk, triB_triMk, triC_triMk] using h2
    have hAt := h (triMk y₀ y₁ y₂) h1' h2' hbox
    rw [triA_triMk, triB_triMk, triC_triMk] at hAt
    exact hAt

/-- **The local step** for the end-triple regularity. -/
theorem tripleGood_eventually_at_meet (F A B : P → EuclideanSpace ℝ (Fin 2) → M)
    (hF : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => F q.1 q.2))
    (hA : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => A q.1 q.2))
    (hB : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => B q.1 q.2))
    (h0 : BoxEndTripleRegG (F 0) (A 0) (B 0))
    {x₀ : EuclideanSpace ℝ (Fin 6)} (hx₀ : x₀ ∈ Submission.Drive.unitBox 5)
    (hmeet₁ : F 0 (triA x₀) = A 0 (triB x₀)) (hmeet₂ : F 0 (triA x₀) = B 0 (triC x₀)) :
    ∀ᶠ q : P × EuclideanSpace ℝ (Fin 6) in 𝓝 ((0 : P), x₀),
      F q.1 (triA q.2) = A q.1 (triB q.2) → F q.1 (triA q.2) = B q.1 (triC q.2) →
        tripleGood (F q.1) (A q.1) (B q.1) q.2 := by
  classical
  have hbase := (boxEndTripleRegG_iff_forall_good (F 0) (A 0) (B 0)).mp h0 x₀ hmeet₁ hmeet₂
  set c : M := F 0 (triA x₀) with hc
  have hreg0 : ((0 : P), x₀) ∈ tripleFamRegion c F A B := by
    refine ⟨?_, ?_, ?_⟩
    · show F 0 (triA x₀) ∈ (chr3 c).source
      rw [← hc]; exact mem_chart_source _ _
    · show A 0 (triB x₀) ∈ (chr3 c).source
      rw [← hmeet₁]; exact mem_chart_source _ _
    · show B 0 (triC x₀) ∈ (chr3 c).source
      rw [← hmeet₂]; exact mem_chart_source _ _
  have hF0 : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (F 0) :=
    hF.comp (loopBox_contMDiff_const 0)
  have hA0 : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (A 0) :=
    hA.comp (loopBox_contMDiff_const 0)
  have hB0 : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (B 0) :=
    hB.comp (loopBox_contMDiff_const 0)
  have hsurj0 : Function.Injective (fderiv ℝ (rowTripleDiff c (F 0) (A 0) (B 0)) x₀) :=
    (rowTripleDiff_injective_iff c (F 0) (A 0) (B 0) hF0 hA0 hB0 hreg0
      hmeet₁ hmeet₂).mpr (hbase hx₀)
  have hEvReg : ∀ᶠ q : P × EuclideanSpace ℝ (Fin 6) in 𝓝 ((0 : P), x₀),
      q ∈ tripleFamRegion c F A B :=
    (isOpen_tripleFamRegion c F A B hF hA hB).mem_nhds hreg0
  have hcontG := continuousAt_tripleFamDiff_fderiv c F A B hF hA hB hreg0
  have hEvSurj : ∀ᶠ q : P × EuclideanSpace ℝ (Fin 6) in 𝓝 ((0 : P), x₀),
      Function.Injective (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 6) =>
        tripleFamDiff c F A B (q.1, y)) q.2) := by
    have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 6))
        = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) := by
      simp [Module.finrank_prod]
    exact hcontG.preimage_mem_nhds
      ((isOpen_setOf_injective_clm hfin).mem_nhds hsurj0)
  filter_upwards [hEvReg, hEvSurj] with q hreg hsurj hmeet₁' hmeet₂'
  have hFq : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (F q.1) :=
    hF.comp (loopBox_contMDiff_const q.1)
  have hAq : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (A q.1) :=
    hA.comp (loopBox_contMDiff_const q.1)
  have hBq : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (B q.1) :=
    hB.comp (loopBox_contMDiff_const q.1)
  have hsurj' : Function.Injective (fderiv ℝ (rowTripleDiff c (F q.1) (A q.1) (B q.1)) q.2) := by
    have h2 : Function.Injective
        (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 6) => tripleFamDiff c F A B (q.1, y)) q.2) := hsurj
    rwa [tripleFamDiff_fun c F A B q.1] at h2
  intro _
  exact (rowTripleDiff_injective_iff c (F q.1) (A q.1) (B q.1) hFq hAq hBq hreg
    hmeet₁' hmeet₂').mp hsurj'

/-- **The box end-triple regularity is an open property of the family parameter.** -/
theorem eventually_boxEndTripleRegG_at (F A B : P → EuclideanSpace ℝ (Fin 2) → M)
    (hF : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => F q.1 q.2))
    (hA : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => A q.1 q.2))
    (hB : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => B q.1 q.2))
    (h0 : BoxEndTripleRegG (F 0) (A 0) (B 0)) :
    ∀ᶠ p in 𝓝 (0 : P), BoxEndTripleRegG (F p) (A p) (B p) := by
  have hmeet_closed : IsClosed {q : P × EuclideanSpace ℝ (Fin 6) |
      F q.1 (triA q.2) = A q.1 (triB q.2)} := by
    have e1 : (![triA, triB, triC] : Fin 3 → EuclideanSpace ℝ (Fin 6) →L[ℝ]
        EuclideanSpace ℝ (Fin 2)) 0 = triA := rfl
    have e2 : (![triA, triB, triC] : Fin 3 → EuclideanSpace ℝ (Fin 6) →L[ℝ]
        EuclideanSpace ℝ (Fin 2)) 1 = triB := rfl
    have h1 := contMDiff_tripleFamA F hF 0
    have h2 := contMDiff_tripleFamA A hA 1
    rw [e1] at h1
    rw [e2] at h2
    exact isClosed_eq h1.continuous h2.continuous
  have hmeet_closed2 : IsClosed {q : P × EuclideanSpace ℝ (Fin 6) |
      F q.1 (triA q.2) = B q.1 (triC q.2)} := by
    have e1 : (![triA, triB, triC] : Fin 3 → EuclideanSpace ℝ (Fin 6) →L[ℝ]
        EuclideanSpace ℝ (Fin 2)) 0 = triA := rfl
    have e3 : (![triA, triB, triC] : Fin 3 → EuclideanSpace ℝ (Fin 6) →L[ℝ]
        EuclideanSpace ℝ (Fin 2)) 2 = triC := rfl
    have h1 := contMDiff_tripleFamA F hF 0
    have h3 := contMDiff_tripleFamA B hB 2
    rw [e1] at h1
    rw [e3] at h3
    exact isClosed_eq h1.continuous h3.continuous
  have hmain := eventually_forall_meet_of_eventually (P := P) (X := EuclideanSpace ℝ (Fin 6))
    (fun p x => F p (triA x) = A p (triB x) ∧ F p (triA x) = B p (triC x))
    (hmeet_closed.inter hmeet_closed2)
    (Submission.Drive.unitBox 5) (isCompact_unitBox 5)
    (fun p x => tripleGood (F p) (A p) (B p) x)
    (fun p y hy => by
      by_contra hcon
      exact hy (fun hbox => absurd hbox hcon))
    (fun x hx hmeet => (tripleGood_eventually_at_meet F A B hF hA hB h0 hx
      hmeet.1 hmeet.2).mono fun q hq hmm => hq hmm.1 hmm.2)
  refine hmain.mono fun p hp => ?_
  refine (boxEndTripleRegG_iff_forall_good (F p) (A p) (B p)).mpr fun x h1 h2 => hp x ⟨h1, h2⟩

end TripleOpen


/-! ## The openness statements at an arbitrary base parameter -/

/-- **The box-pair regularity is an open property of the family parameter**, at an arbitrary base
point. -/
theorem eventually_boxPairRegG {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A B : P → EuclideanSpace ℝ (Fin 2) → M)
    (hA : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => A q.1 q.2))
    (hB : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => B q.1 q.2))
    (p₀ : P) (h0 : BoxPairRegG (A p₀) (B p₀)) :
    ∀ᶠ p in 𝓝 p₀, BoxPairRegG (A p) (B p) := by
  have hshift : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2)))
      (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => (p₀ + q.1, q.2)) := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  have htr := eventually_boxPairRegG_at (A := fun u : P => A (p₀ + u))
    (B := fun u : P => B (p₀ + u)) (hA.comp hshift) (hB.comp hshift) (by simpa using h0)
  have htend : Filter.Tendsto (fun p : P => p - p₀) (𝓝 p₀) (𝓝 (0 : P)) := by
    simpa using (continuous_sub_right p₀).tendsto p₀
  refine (htend.eventually htr).mono fun p hp => ?_
  have hpp : p₀ + (p - p₀) = p := by abel
  simpa only [hpp] using hp

/-- **The set of parameters at which the box-pair regularity holds is open.** -/
theorem isOpen_boxPairRegG {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {A B : P → EuclideanSpace ℝ (Fin 2) → M}
    (hA : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => A q.1 q.2))
    (hB : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => B q.1 q.2)) :
    IsOpen {p | BoxPairRegG (A p) (B p)} := by
  rw [isOpen_iff_mem_nhds]
  intro p₀ h0
  exact eventually_boxPairRegG A B hA hB p₀ h0

/-- **The box end-triple regularity is an open property of the family parameter**, at an arbitrary
base point. -/
theorem eventually_boxEndTripleRegG {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F A B : P → EuclideanSpace ℝ (Fin 2) → M)
    (hF : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => F q.1 q.2))
    (hA : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => A q.1 q.2))
    (hB : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => B q.1 q.2))
    (p₀ : P) (h0 : BoxEndTripleRegG (F p₀) (A p₀) (B p₀)) :
    ∀ᶠ p in 𝓝 p₀, BoxEndTripleRegG (F p) (A p) (B p) := by
  have hshift : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2)))
      (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => (p₀ + q.1, q.2)) := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  have htr := eventually_boxEndTripleRegG_at (F := fun u : P => F (p₀ + u))
    (A := fun u : P => A (p₀ + u)) (B := fun u : P => B (p₀ + u))
    (hF.comp hshift) (hA.comp hshift) (hB.comp hshift) (by simpa using h0)
  have htend : Filter.Tendsto (fun p : P => p - p₀) (𝓝 p₀) (𝓝 (0 : P)) := by
    simpa using (continuous_sub_right p₀).tendsto p₀
  refine (htend.eventually htr).mono fun p hp => ?_
  have hpp : p₀ + (p - p₀) = p := by abel
  simpa only [hpp] using hp

/-- **The set of parameters at which the box end-triple regularity holds is open.** -/
theorem isOpen_boxEndTripleRegG {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {F A B : P → EuclideanSpace ℝ (Fin 2) → M}
    (hF : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => F q.1 q.2))
    (hA : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => A q.1 q.2))
    (hB : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => B q.1 q.2)) :
    IsOpen {p | BoxEndTripleRegG (F p) (A p) (B p)} := by
  rw [isOpen_iff_mem_nhds]
  intro p₀ h0
  exact eventually_boxEndTripleRegG F A B hF hA hB p₀ h0

end

end Work.Drive
