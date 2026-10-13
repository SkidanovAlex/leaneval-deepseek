/-
  WilE7 / DimAPI: **the sheet projection is a closed map**.

  Given `X ⊆ ℝ^{p+q}` bounded and `C ⊆ ℝ^p`, the sheet space
  `SheetT X C = X ∩ π⁻¹' C` (with `π = projFirst p q`) carries the subspace topology, and
  `SheetP X C : SheetT X C → C` is the restriction of `π`.  Under the hypothesis that `X` is
  closed over `C` inside its own closure (every point of `closure X` projecting into `C` already
  lies in `X`), this continuous map is closed.

  Mathematics.  Let `K ⊆ SheetT X C` be closed and let `A = Subtype.val '' K`.  Since `K` is the
  trace of a closed set `F` of the ambient space, `closure A ⊆ F`; also `A ⊆ X`, so
  `closure A ⊆ closure X` is compact by boundedness of `X` (and properness of `ℝ^{p+q}`), whence
  `π '' closure A` is closed in `ℝ^p`.  For the identification of the preimages: a base point `x`
  lies in `π '' closure A` only through a point `z ∈ closure A` with `π z = x`; then `z ∈ closure X`
  and `π z ∈ C`, so `z ∈ X` by hypothesis, and `z ∈ F` because `closure A ⊆ F`, i.e.
  `z ∈ A = Subtype.val '' K` — so `x` already lies in `SheetP X C '' K`.  The reverse inclusion is
  immediate.  Hence `Subtype.val ⁻¹' (π '' closure A) = SheetP X C '' K`, closed in `C`.

  Note the statement uses `X` only through boundedness and the frontier hypothesis: no hypothesis
  on `C` is needed.
-/
import Mathlib
import Submission.Work.WilE7.DimAPI.SheetLocalDefs

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open Set

namespace Work.WilE7.DimAPI

/-- **The sheet projection is a closed map.**  If `X` is bounded and every point of `closure X`
lying over `C` already belongs to `X`, then `SheetP X C : SheetT X C → C` is closed. -/
theorem SheetP_closedMap {p q : ℕ} (X : Set (Fin (p + q) → ℝ)) (C : Set (Fin p → ℝ))
    (hbdd : Bornology.IsBounded X)
    (hclosed : ∀ z ∈ closure X, WilkiesDesign.E.projFirst p q z ∈ C → z ∈ X) :
    IsClosedMap (Work.WilE7.DimAPI.SheetP X C) := by
  intro K hK
  -- `K` is the trace, on the sheet space, of a closed set `F` of the ambient space
  rw [isClosed_induced_iff]
  obtain ⟨F, hFclosed, hKF⟩ := isClosed_induced_iff.mp hK
  set A : Set (Fin (p + q) → ℝ) := Subtype.val '' K with hAdef
  -- `A` is contained in `F` (hence so is its closure) and in `X` (hence so is its closure)
  have hAF : A ⊆ F := by
    rintro z ⟨w, hw, rfl⟩
    have h1 : w ∈ Subtype.val ⁻¹' F := by rw [hKF]; exact hw
    exact h1
  have hclAF : closure A ⊆ F := closure_minimal hAF hFclosed
  have hAX : A ⊆ X := by
    rintro z ⟨w, hw, rfl⟩
    exact w.2.1
  have hclAX : closure A ⊆ closure X := closure_mono hAX
  -- `closure A` is compact, since `X` is bounded and `ℝ^{p+q}` is proper
  have hcompA : IsCompact (closure A) :=
    hbdd.isCompact_closure.of_isClosed_subset isClosed_closure hclAX
  have hcont : Continuous (WilkiesDesign.E.projFirst p q) := by
    unfold WilkiesDesign.E.projFirst
    exact continuous_pi fun i => continuous_apply (Fin.castAdd q i)
  -- the projection of `closure A` is closed in `ℝ^p`
  have himg : IsClosed (WilkiesDesign.E.projFirst p q '' closure A) :=
    (hcompA.image hcont).isClosed
  refine ⟨WilkiesDesign.E.projFirst p q '' closure A, himg, ?_⟩
  ext x
  constructor
  · -- a base point over `closure A`: its lift lies in `X` by the frontier hypothesis and in `F`,
    -- hence in `K`
    intro hx
    obtain ⟨z, hz, hzπ⟩ := hx
    have hzC : WilkiesDesign.E.projFirst p q z ∈ C := by rw [hzπ]; exact x.2
    have hzX : z ∈ X := hclosed z (hclAX hz) hzC
    refine ⟨⟨z, hzX, hzC⟩, ?_, ?_⟩
    · have : (⟨z, hzX, hzC⟩ : Work.WilE7.DimAPI.SheetT X C).1 ∈ F := hclAF hz
      rw [← hKF]
      exact this
    · exact Subtype.ext (by rw [Work.WilE7.DimAPI.SheetP_val]; exact hzπ)
  · -- conversely the projection of `K` lies in the projection of its closure
    rintro ⟨w, hw, rfl⟩
    exact ⟨w.1, subset_closure ⟨w, hw, rfl⟩, rfl⟩

end Work.WilE7.DimAPI
