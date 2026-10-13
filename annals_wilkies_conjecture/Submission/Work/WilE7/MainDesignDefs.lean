/-
  E7_prop_main: the dimension API for the BV lexicographic induction.

  This is the permanent home of the design of `sources/wilkiesE7main/wilkies_e7_main_design.md`
  (Claude design 2026-10-11, reviewed in `..._REVIEW.md`): the measure `NullDimLE`/`NullDimLT`, the
  absolute frontier drop `frontierDrop_abs` (proved from the delivered C4a curve selection), the
  projection rank `projRank` of an absolute stratum, and the induction statement `CoreLT`.

  Namespace `Work.WilE7.MainDesign`.  Everything in *this* file is proved (no `sorry`); the nodes of
  the design (`rankLocus_nullDimLE`, `stratum_nullDimLE`, `not_dimLE_of_projRank`, `equalDim_open`,
  `projRank_eq_dim_of_sub_fibreGood`, `sheets_of_localGraph`, `NullDimLE.mono_dim`,
  `Core_succ_of_CoreLT`, `CoreLT_zero`, `CoreLT_succ`, ...) live in their own modules under
  `Submission/Work/WilE7/DimAPI/` and import this one.

  The route in one paragraph.  BV Proposition 9 is a lexicographic induction on `(n, k)` with
  `k = dim π_n(X_α)`.  The measure must be closed under finite unions, so use *null* coordinate
  projections (`NullDimLE`) rather than `DimLE` (`ℚ ∪ (ℝ∖ℚ) = ℝ`).  The strata are taken at the
  *absolute* split `p = 0` (`hE5` at `p = 0`), which gives ambient locality for free
  (`Work.WilE7.hloc_of_good_abs`) and excludes cube-exit points, so no cube-face cuts are needed.
  The strict drop of the measure along the frontier is `frontierDrop_abs`, obtained from
  `Work.WilE7.FrontierCS.dimDrop_proved` (proved via the delivered C4a curve selection) and
  `Work.WilE7.frontierDrop_of_dimDrop`.  Sard turns "dimension `N - j`" into `NullDimLE`
  (`rankLocus_nullDimLE` / `stratum_nullDimLE`), and `NullDimLT` with the extra unconstrained base
  family `Y` in `CoreLT` makes the BV glueing formal.
-/
import Mathlib
import Submission.Work.WilE7.CoreDefs
import Submission.Work.WilE7.FrontierCS.Main
import Submission.Work.WilE7.FiberCutInputs

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
namespace Work.WilE7.MainDesign
open WilkiesDesign WilkiesDesign.E

/-! ## A. The measure: null coordinate projections (closed under finite unions, unlike `DimLE`) -/

/-- `dim X ≤ μ` in the measure sense: every projection of `X` to `μ+1` coordinates is
Lebesgue-null.  Implies `DimLE X μ` (A1) and, unlike `DimLE`, is closed under unions (A2). -/
def NullDimLE {N : ℕ} (X : Set (Fin N → ℝ)) (μ : ℕ) : Prop :=
  ∀ e : Fin (μ + 1) ↪ Fin N, MeasureTheory.volume ((fun x => x ∘ e) '' X) = 0

/-- `dim X < K` (`K = 0` means empty). This is the induction measure of `CoreLT`. -/
def NullDimLT {N : ℕ} (X : Set (Fin N → ℝ)) : ℕ → Prop
  | 0 => X = ∅
  | K + 1 => NullDimLE X K

/-- A1 (PROVED). -/
theorem NullDimLE.dimLE {N μ : ℕ} {X : Set (Fin N → ℝ)} (h : NullDimLE X μ) : DimLE X μ :=
  fun e => MeasureTheory.Measure.interior_eq_empty_of_null (h e)

/-- A2 (PROVED). -/
theorem NullDimLE.union {N μ : ℕ} {X Y : Set (Fin N → ℝ)} (hX : NullDimLE X μ)
    (hY : NullDimLE Y μ) : NullDimLE (X ∪ Y) μ := by
  intro e
  rw [Set.image_union]
  exact MeasureTheory.measure_union_null (hX e) (hY e)

/-- A3 (PROVED). -/
theorem NullDimLE.mono {N μ : ℕ} {X Y : Set (Fin N → ℝ)} (h : NullDimLE Y μ) (hXY : X ⊆ Y) :
    NullDimLE X μ :=
  fun e => MeasureTheory.measure_mono_null (Set.image_mono hXY) (h e)

/-- A4 (PROVED): coordinate projections do not raise the measure. -/
theorem NullDimLE.projFirst {n m μ : ℕ} {X : Set (Fin (n + m) → ℝ)} (h : NullDimLE X μ) :
    NullDimLE (projFirst n m '' X) μ := by
  intro e
  have := h (e.trans ⟨Fin.castAdd m, Fin.castAdd_injective n m⟩)
  rw [Set.image_image]
  exact this

/-- Finite unions of `NullDimLE` sets are `NullDimLE`. -/
theorem NullDimLE.iUnion {N μ : ℕ} {ι : Type*} [Finite ι] {f : ι → Set (Fin N → ℝ)}
    (hf : ∀ i, NullDimLE (f i) μ) : NullDimLE (⋃ i, f i) μ := by
  intro e
  rw [Set.image_iUnion]
  exact MeasureTheory.measure_iUnion_null fun i => hf i e

/-! ## B. Absolute strata (`p = 0`) and the PROVED frontier drop -/

/-- B1 (PROVED): over the trivial base the fibrewise closure is the closure. -/
theorem fiberClosure_zero {q : ℕ} (X : Set (Fin (0 + q) → ℝ)) :
    fiberClosure X = closure X := by
  have hq : 0 + q = q := Nat.zero_add q
  let φ : (Fin q → ℝ) ≃ₜ (Fin (0 + q) → ℝ) :=
    { toFun := fun y i => y (Fin.cast hq i)
      invFun := fun z i => z (Fin.cast hq.symm i)
      left_inv := fun y => by funext i; simp
      right_inv := fun z => by funext i; simp
      continuous_toFun := continuous_pi fun i => continuous_apply _
      continuous_invFun := continuous_pi fun i => continuous_apply _ }
  have hφ : ∀ (x : Fin 0 → ℝ) (y : Fin q → ℝ), Fin.append x y = φ y := by
    intro x y
    funext i
    refine Fin.addCases (fun j => j.elim0) (fun j => ?_) i
    rw [Fin.append_right]
    show y j = y (Fin.cast hq (Fin.natAdd 0 j))
    congr 1; ext; simp
  ext z
  simp only [fiberClosure, fiber, Set.mem_setOf_eq]
  have hpre : {y : Fin q → ℝ | Fin.append (projFirst 0 q z) y ∈ X} = φ ⁻¹' X := by
    ext y; simp [hφ]
  rw [hpre, ← φ.preimage_closure, Set.mem_preimage]
  have : φ (projSnd 0 q z) = z := by
    funext i
    show z (Fin.natAdd 0 (Fin.cast hq i)) = z i
    congr 1; ext; simp
  rw [this]

/-- B2 (PROVED, from `dimDrop_proved` + `frontierDrop_of_dimDrop` + B1): **absolute frontier
drop** — a nonempty `Good` absolute stratum inside the frontier of another has strictly more
equations, i.e. strictly smaller dimension `N - j`. -/
theorem frontierDrop_abs {q : ℕ} (S S' : Stratum 0 q) (hS : S.Good) (hS' : S'.Good)
    (hsub : S'.X.set ⊆ closure S.X.set \ S.X.set) (hne : S'.X.set.Nonempty) : S.j < S'.j := by
  have hFD : Work.WilE7.FrontierDrop :=
    Work.WilE7.frontierDrop_of_dimDrop Work.WilE7.FrontierCS.dimDrop_proved
  exact hFD 0 q S S' hS hS' (by rw [fiberClosure_zero]; exact hsub) hne

/-! ## C. Projection rank of an absolute stratum, Sard, and the converse -/

/-- Pull an absolute-stratum point (type `Fin (0 + N)`) to `Fin N`. -/
def absPt {N : ℕ} (z : Fin (0 + N) → ℝ) : Fin N → ℝ :=
  fun i => z (Fin.cast (Nat.zero_add N).symm i)

/-- The set of an absolute stratum, in `ℝ^N`. -/
def absSet {N : ℕ} (S : Stratum 0 N) : Set (Fin N → ℝ) := absPt '' S.X.set

/-- The Jacobian of the equations of a stratum at `z`, as a linear map. -/
def jac {p q : ℕ} (S : Stratum p q) (z : Fin (p + q) → ℝ) :
    (Fin (p + q) → ℝ) →ₗ[ℝ] (Fin S.j → ℝ) :=
  (Matrix.of fun (a : Fin S.j) (l : Fin (p + q)) =>
    eaEval S.X.c (eaD S.X.c l (S.h a)) z).mulVecLin

/-- The linear base projection `ℝ^{0+(n+m)} → ℝ^n`. -/
def basePrLin (n m : ℕ) : (Fin (0 + (n + m)) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.funLeft ℝ ℝ (fun i : Fin n => Fin.cast (Nat.zero_add _).symm (Fin.castAdd m i))

/-- The rank of `π_n` restricted to the tangent space `ker (jac S z)` of an absolute stratum. -/
def projRank {n m : ℕ} (S : Stratum 0 (n + m)) (z : Fin (0 + (n + m)) → ℝ) : ℕ :=
  Module.finrank ℝ ((LinearMap.ker (jac S z)).map (basePrLin n m))

/-! ## F. The lexicographic induction statement -/

/-- Base point of a level-`(n+1)` point. -/
def basePr (n m : ℕ) (z : Fin ((n + 1) + m) → ℝ) : Fin n → ℝ :=
  fun i => z ⟨i, by omega⟩

/-- **`CoreLT n K`**: level-`(n+1)` decompositions for families `X` whose base projections
`π_n(X i)` have dimension `< K`, made *simultaneously* compatible (through the base) with an
unconstrained base family `Y`.  The base family is what makes the BV glueing possible: the
`(n+1, K)` step calls `(n+1, K-1)` with `Y' := Y ++ π-data of Π ++ Σ` and uses that call's base
decomposition for everything (two different base decompositions cannot be merged into one
`IsCylDecompOn`). -/
def CoreLT (n K : ℕ) : Prop :=
  ∀ F : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 3) ℕ) (c : Polynomial ℕ),
    ∀ (D k l m m' : ℕ) (X : Fin k → SemiPf ((n + 1) + m)) (Y : Fin l → SemiPf (n + m')),
      (∀ i, (X i).fmt ≤ F ∧ (X i).deg ≤ D) → (∀ i, (Y i).fmt ≤ F ∧ (Y i).deg ≤ D) →
      (∀ i, NullDimLT (basePr n m '' (X i).set) K) →
      ∃ C : Finset (Set (Fin (n + 1) → ℝ)),
        IsCylDecompOn (n + 1) (cubeC (n + 1)) C ∧
        (∀ i, ∀ κ ∈ C, κ ⊆ projFirst (n + 1) m '' (X i).set ∨
          Disjoint κ (projFirst (n + 1) m '' (X i).set)) ∧
        (∀ i, ∀ κ ∈ C, Fin.init '' κ ⊆ projFirst n m' '' (Y i).set ∨
          Disjoint (Fin.init '' κ) (projFirst n m' '' (Y i).set)) ∧
        C.card ≤ MvPolynomial.eval ![D, k, l] b ∧
        ∀ κ ∈ C, (∃ P : StarPiece (n + 1), P.set = κ ∧ P.X.fmt ≤ a ∧ P.X.deg ≤ c.eval D) ∧
          SubPf (n + 1) κ

/-- F1 (PROVED): `NullDimLT · (n+1)` is automatic in `ℝ^n` (no `Fin (n+1) ↪ Fin n`). -/
theorem nullDimLT_top {n : ℕ} (X : Set (Fin n → ℝ)) : NullDimLT X (n + 1) := by
  intro e
  exact absurd (Fintype.card_le_of_embedding e) (by simp)

end Work.WilE7.MainDesign
