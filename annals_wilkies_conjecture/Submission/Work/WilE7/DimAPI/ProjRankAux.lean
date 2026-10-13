/-
  WilE7 / DimAPI — auxiliary definitions and elementary lemmas for the projection-rank API.

  These are the small pieces that `projRank_eq_dim_of_sub_fibreGood` (and its neighbours) need:

  * `absPtCLM N` — the coordinate reindexing `ℝ^{0+N} → ℝ^N` of `MainDesign.absPt`, as a
    *continuous linear map*, so that chain rules can be applied to it;
  * `absPtInv N` and the round-trip lemmas, showing that `MainDesign.absPt` is a bijection;
  * `eqMap S` — the defining-equation map `w ↦ (a ↦ eaEval S.X.c (S.h a) w)` of a stratum, whose
    differential is `MainDesign.jac S z` and whose kernel is therefore the tangent space of the
    stratum.
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs

set_option autoImplicit false
noncomputable section
namespace Work.WilE7.DimAPI

open WilkiesDesign WilkiesDesign.E

/-! ## The coordinate reindexing `absPt` as a continuous linear map -/

/-- `MainDesign.absPt` as a continuous linear map: it reindexes `Fin (0 + N)` by `Fin N`. -/
def absPtCLM (N : ℕ) : (Fin (0 + N) → ℝ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin N =>
    (ContinuousLinearMap.proj (Fin.cast (Nat.zero_add N).symm i) : (Fin (0 + N) → ℝ) →L[ℝ] ℝ)

@[simp] lemma absPtCLM_apply {N : ℕ} (z : Fin (0 + N) → ℝ) :
    absPtCLM N z = MainDesign.absPt z := by
  funext i
  rfl

/-- The inverse reindexing `ℝ^N → ℝ^{0+N}` of `MainDesign.absPt`. -/
def absPtInv (N : ℕ) : (Fin N → ℝ) → (Fin (0 + N) → ℝ) :=
  fun w i => w (Fin.cast (Nat.zero_add N) i)

lemma absPt_absPtInv (N : ℕ) (w : Fin N → ℝ) : MainDesign.absPt (absPtInv N w) = w := by
  funext i
  have h : Fin.cast (Nat.zero_add N) (Fin.cast (Nat.zero_add N).symm i) = i := Fin.ext (by simp)
  show w (Fin.cast (Nat.zero_add N) (Fin.cast (Nat.zero_add N).symm i)) = w i
  rw [h]

lemma absPtInv_absPt (N : ℕ) (z : Fin (0 + N) → ℝ) : absPtInv N (MainDesign.absPt z) = z := by
  funext i
  have h : Fin.cast (Nat.zero_add N).symm (Fin.cast (Nat.zero_add N) i) = i := Fin.ext (by simp)
  show z (Fin.cast (Nat.zero_add N).symm (Fin.cast (Nat.zero_add N) i)) = z i
  rw [h]

lemma absPt_injective (N : ℕ) : Function.Injective (@MainDesign.absPt N) := by
  intro z w h
  have h' := congrArg (absPtInv N) h
  rwa [absPtInv_absPt, absPtInv_absPt] at h'

lemma eq_zero_of_absPt_eq_zero {N : ℕ} {z : Fin (0 + N) → ℝ}
    (h : MainDesign.absPt z = 0) : z = 0 := by
  have h' := congrArg (absPtInv N) h
  rwa [absPtInv_absPt] at h'

/-! ## The defining-equation map of a stratum -/

/-- The defining-equation map of a stratum: `w ↦ (a ↦ eaEval S.X.c (S.h a) w)`. -/
def eqMap {p q : ℕ} (S : WilkiesDesign.E.Stratum p q) : (Fin (p + q) → ℝ) → (Fin S.j → ℝ) :=
  fun w a => WilkiesDesign.E.eaEval S.X.c (S.h a) w

lemma eqMap_apply {p q : ℕ} (S : WilkiesDesign.E.Stratum p q) (w : Fin (p + q) → ℝ)
    (a : Fin S.j) : eqMap S w a = WilkiesDesign.E.eaEval S.X.c (S.h a) w := rfl

/-- The defining-equation map of a stratum is analytic, being a finite product of analytic
functions. -/
lemma analyticAt_eqMap {p q : ℕ} (S : WilkiesDesign.E.Stratum p q) (z : Fin (p + q) → ℝ) :
    AnalyticAt ℝ (eqMap S) z := by
  refine AnalyticAt.pi fun a => ?_
  exact Work.WilE5.Strat.analyticAt_eaEval S.X.c (S.h a) z

/-- At a point of a `Good` stratum the defining equations vanish. -/
lemma eqMap_eq_zero_of_good {p q : ℕ} (S : WilkiesDesign.E.Stratum p q) (hS : S.Good)
    {z : Fin (p + q) → ℝ} (hz : z ∈ S.X.set) : eqMap S z = 0 :=
  funext fun a => (hS z hz).1 a

end Work.WilE7.DimAPI
