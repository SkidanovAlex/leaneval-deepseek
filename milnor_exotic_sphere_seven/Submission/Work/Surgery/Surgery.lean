import Submission.Work.Bordism.Middle
import Submission.Work.Bordism.bordant_trans
import Submission.Work.SignatureBordism.Signature
import Submission.Work.SignatureBordism.signature_prod

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Surgery moves and their effect on the middle intersection form

This file records, in the workspace's own model of closed oriented manifolds
(`Work.Bordism.ClosedOriented`, a space together with a fundamental class), the **surgery move** of
item `k`: a pair `M`, `M'` of closed oriented `2k`-manifolds such that `M'` is obtained from `M` by
surgery on a framed `S^k × D^k` — equivalently, such that a hyperbolic pair of the middle
cohomology of `M` is killed, i.e. the middle intersection form of `M` is the orthogonal sum of the
middle form of `M'` with a hyperbolic plane.

For an even-dimensional closed oriented manifold the middle intersection form is
`Work.Bordism.midForm M`, the quadratic form `y ↦ ⟨y ⌣ y, [M]⟩` on `H^k(M;ℚ)`, and its signature is
`Work.SignatureBordism.sigma`.

## Main results

* `Work.Surgery.hypQ` — the hyperbolic plane as a quadratic form over `ℚ`;
* `Work.Surgery.signature_hypQ` — its signature vanishes;
* `Work.Surgery.SurgeryMove k M M'` — the surgery move;
* **`Work.Surgery.sigma_eq_of_surgeryMove`** — *killing a hyperbolic pair does not change the
  signature*: `σ(M) = σ(M')`.  Together with the parity statement of
  `Work.UnimodularForms` this is the invariance of the middle form under surgery, and hence the
  algebraic core of the bordism computations of the dimension-`8` signature theorem;
* `Work.Surgery.ClosedOriented.empty` — the empty closed oriented manifold (the zero of the bordism
  group), and the interface statements `nullBordant_of_isBoundary` (a manifold which is the boundary
  of a compact oriented manifold is null-bordant — this is what makes a *sphere bundle* null-bordant,
  namely the boundary of its disc bundle) and `bordant_of_twoBoundaryComponents` (the two boundary
  ends of a compact oriented manifold are bordant).
-/

open scoped Manifold Topology ContDiff
open CategoryTheory

namespace Work.Surgery

open Work.Bordism Work.SignatureBordism
open QuadraticMap

noncomputable section

variable {k : ℕ}

/-! ## The hyperbolic plane as a quadratic form -/

/-- The weight function `(1, -1)` on `Fin 2`, whose weighted sum of squares is the hyperbolic
plane in diagonal form. -/
def hypW : Fin 2 → ℚ := fun i => if i = 0 then 1 else -1

/-- **The hyperbolic plane** as a quadratic form over `ℚ`, in diagonal form `x₀² - x₁²` on
`Fin 2 → ℚ` (which over `ℚ` is the form `(x, y) ↦ x * y` in suitable coordinates). -/
def hypQ : QuadraticForm ℚ (Fin 2 → ℚ) := weightedSumSquares ℚ hypW

/-- **The signature of the hyperbolic plane is zero.** -/
theorem signature_hypQ : signature hypQ = 0 := by
  have hpos : {i : Fin 2 | 0 < hypW i} = {0} := by
    ext i; fin_cases i <;> norm_num [hypW]
  have hneg : {i : Fin 2 | hypW i < 0} = {1} := by
    ext i; fin_cases i <;> norm_num [hypW]
  rw [hypQ, signature_weightedSumSquares (𝕜 := ℚ) (ι := Fin 2) (w := hypW), hpos, hneg,
    Set.ncard_singleton, Set.ncard_singleton]
  norm_num

/-! ## The surgery move -/

/-- **The surgery move of index `k`** on closed oriented `2k`-manifolds: `M'` is obtained from `M`
by surgery which kills a hyperbolic pair of the middle cohomology — equivalently, the middle
intersection form of `M` is the orthogonal sum of the middle form of `M'` with a hyperbolic plane
`ℍ`.

(That the geometric surgery on a framed embedded `S^k × D^k` has this effect on the middle form is
the geometric input of the dictionary; it is recorded here as the definition of the move.) -/
structure SurgeryMove (k : ℕ) (M M' : ClosedOriented (k + k)) : Prop where
  /-- the middle form of `M` is that of `M'` plus a hyperbolic plane -/
  isom : ∃ e : ratCohomology k (TopCat.toSSet.obj M.X) ≃ₗ[ℚ]
      (ratCohomology k (TopCat.toSSet.obj M'.X) × (Fin 2 → ℚ)),
    (midForm M).comp (e.symm : _ →ₗ[ℚ] _) = (midForm M').prod hypQ

/-- **Killing a hyperbolic pair does not change the signature**: a surgery move does not change
`σ`. -/
theorem sigma_eq_of_surgeryMove {M M' : ClosedOriented (k + k)} (h : SurgeryMove k M M')
    [FiniteDimensional ℚ (ratCohomology k (TopCat.toSSet.obj M.X))]
    [FiniteDimensional ℚ (ratCohomology k (TopCat.toSSet.obj M'.X))] :
    sigma k (TopCat.toSSet.obj M.X) M.c = sigma k (TopCat.toSSet.obj M'.X) M'.c := by
  obtain ⟨e, he⟩ := h.isom
  rw [sigma_eq_signature_midForm M, sigma_eq_signature_midForm M',
    ← signature_comp_linearEquiv (midForm M) e.symm, he, signature_prod, signature_hypQ, add_zero]

/-- The signature of a surgery move, in the `Work.Bordism` vocabulary. -/
theorem midForm_signature_eq_of_surgeryMove {M M' : ClosedOriented (k + k)}
    (h : SurgeryMove k M M') [FiniteDimensional ℚ (ratCohomology k (TopCat.toSSet.obj M.X))]
    [FiniteDimensional ℚ (ratCohomology k (TopCat.toSSet.obj M'.X))] :
    signature (midForm M) = signature (midForm M') := by
  rw [← sigma_eq_signature_midForm M, ← sigma_eq_signature_midForm M',
    sigma_eq_of_surgeryMove h]

/-! ## The interface with bordism -/

/-- **The empty closed oriented manifold**, the zero of the bordism group: the empty space with the
zero fundamental class. -/
def ClosedOriented.empty (n : ℕ) : ClosedOriented n where
  X := TopCat.of Empty
  c := 0

/-- **A manifold which is the boundary of a compact oriented manifold is null-bordant.**  The
hypothesis is the geometric bordism from `M` to the empty manifold, i.e. a compact oriented
`(n+1)`-manifold with boundary `M` together with its relative fundamental class.

This is the form in which a **sphere bundle** is null-bordant: for the unit sphere bundle `S` of a
vector bundle, the hypothesis is supplied by the disc bundle of that vector bundle (a construction,
not a proof), so `S` is null-bordant. -/
theorem nullBordant_of_isBoundary (n : ℕ) (M : ClosedOriented n)
    (h : GeometricBordism M (ClosedOriented.empty n)) :
    Bordant M (ClosedOriented.empty n) :=
  ⟨h.toBordism⟩

/-- **The two boundary ends of a compact oriented manifold are bordant**: the handlebody of a
surgery is a bordism between the two boundary pieces. -/
theorem bordant_of_twoBoundaryComponents (n : ℕ) (M M' : ClosedOriented n)
    (h : GeometricBordism M M') : Bordant M M' :=
  ⟨h.toBordism⟩

/-- **Null-bordism is a bordism invariant**: a manifold bordant to a null-bordant manifold is
null-bordant.  This is the form in which the elementary computations of `Ω^SO_8 ⊗ ℚ` use the
null-bordant pieces (sphere bundles, and manifolds obtained from them by surgery). -/
theorem nullBordant_of_bordant (n : ℕ) {M N : ClosedOriented n} (h : Bordant M N)
    (hN : Bordant N (ClosedOriented.empty n)) : Bordant M (ClosedOriented.empty n) :=
  Work.Bordism.bordant_trans h hN

end

end Work.Surgery
