import Mathlib
import Submission.Work.EQ.UnivCover.Defs
import Submission.Work.EQ.UnivCover.Sheet
import Submission.Work.EQ.UnivCover.Topology

/-!
# The initial-segment map of the universal cover along a path

For a path `γ : Path x₀ x` in a space whose disc-like sets form a neighbourhood basis
(`HasDiscBasis X`), the map `t ↦ UC.segPt γ t` is the continuous lift of `γ` to the universal cover
`UC x₀`:

* it is continuous;
* it starts at the base point `UC.base x₀`;
* it ends at the homotopy class of `γ`;
* and it stays inside the sheets over any set that contains the corresponding piece of `γ`.

The file is self-contained: it only depends on the definitions (`Defs`), the sheaf-of-sheets
structure (`Sheet`) and the basis/topology of the cover (`Topology`).
-/

set_option autoImplicit false
open _root_.Topology
open scoped Topology
open Set

namespace Work.EQ.UnivCover

variable {X : Type*} [TopologicalSpace X] {x₀ : X}

/-! ## Two elementary facts about the initial segment `segTo` -/

/-- `segTo γ t` is the subpath of `γ` from `0` to `t`, with the source cast from `γ 0` to `x₀`. -/
theorem ucSegPt_segTo_subpath_cast {x : X} (γ : Path x₀ x) (t : unitInterval) :
    segTo γ t = (γ.subpath 0 t).cast γ.source.symm rfl := by
  apply Path.ext
  funext u
  rw [Path.cast_coe]
  simp only [segTo, Path.subpath]
  refine congrArg γ (Subtype.ext ?_)
  simp [Set.Icc.convexComb]

/-- Casting the left endpoint of a path homotopy class commutes with concatenation. -/
theorem ucSegPt_quot_cast_trans {a b c a' : X} (A : Path.Homotopic.Quotient a b)
    (B : Path.Homotopic.Quotient b c) (h : a' = a) :
    (A.cast h rfl).trans B = (A.trans B).cast h rfl := by
  induction A using Path.Homotopic.Quotient.ind with
  | mk p =>
    induction B using Path.Homotopic.Quotient.ind with
    | mk q =>
      rw [← Path.Homotopic.Quotient.mk_cast, ← Path.Homotopic.Quotient.mk_trans,
        ← Path.Homotopic.Quotient.mk_trans, ← Path.Homotopic.Quotient.mk_cast]
      congr 1

/-! ## Initial segments form a chain of sheets -/

/-- **The initial segments of a path form a chain of sheets.**  If `V` contains the piece of `γ`
whose parameters lie in the (unordered) interval with endpoints `s` and `t`, then the point of the
cover over `γ t` lies in the sheet through the point over `γ s`. -/
theorem ucSegPt_mem_sheet {x : X} (γ : Path x₀ x) {V : Set X} (s t : unitInterval)
    (hγ : ∀ u : unitInterval, u ∈ Set.uIcc s t → γ u ∈ V) :
    UC.segPt γ t ∈ UC.sheet (UC.segPt γ s) V := by
  rw [UC.mem_sheet_iff]
  change γ t ∈ V ∧ ∃ δ : Path (γ s) (γ t), (∀ a, δ a ∈ V) ∧
    Path.Homotopic.Quotient.mk (segTo γ t)
      = (Path.Homotopic.Quotient.mk (segTo γ s)).trans (Path.Homotopic.Quotient.mk δ)
  refine ⟨hγ t Set.right_mem_uIcc, γ.subpath s t, ?_, ?_⟩
  · intro a
    have hmem : (γ.subpath s t) a ∈ Set.range (γ.subpath s t) := ⟨a, rfl⟩
    rw [Path.range_subpath] at hmem
    obtain ⟨v, hv, hv'⟩ := hmem
    rw [← hv']
    exact hγ v hv
  · rw [ucSegPt_segTo_subpath_cast γ t, ucSegPt_segTo_subpath_cast γ s,
      Path.Homotopic.Quotient.mk_cast, Path.Homotopic.Quotient.mk_cast]
    rw [ucSegPt_quot_cast_trans, Path.Homotopic.mk_subpath_trans_mk_subpath γ 0 s t]

/-- **Nearby initial segments stay in the same sheet.**  If the piece of `γ` between `t₀` and `t`
lies in `W ⊆ V`, then `UC.segPt γ t` lies in every sheet over `V` through `UC.segPt γ t₀`. -/
theorem ucSegPt_mem_sheet_near {x : X} (γ : Path x₀ x) {V W : Set X} {e : UC x₀}
    {t₀ t : unitInterval} (he : UC.segPt γ t₀ ∈ UC.sheet e V) (hWV : W ⊆ V)
    (ht : ∀ u : unitInterval, u ∈ Set.uIcc t₀ t → γ u ∈ W) :
    UC.segPt γ t ∈ UC.sheet e V :=
  UC_sheet_trans he (ucSegPt_mem_sheet γ t₀ t ht) hWV

/-! ## Betweenness controls the distance in `unitInterval` -/

/-- A point of the unordered interval with endpoints `b` and `c` is no further from `b` than `c`. -/
theorem ucSegPt_dist_le_dist_of_mem_uIcc {a b c : unitInterval} (h : a ∈ Set.uIcc b c) :
    dist a b ≤ dist c b := by
  rw [Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, Real.dist_eq]
  rcases Set.mem_uIcc.mp h with ⟨hba, hac⟩ | ⟨hca, hab⟩
  · have hba' : (b : ℝ) ≤ (a : ℝ) := hba
    have hac' : (a : ℝ) ≤ (c : ℝ) := hac
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · have hca' : (c : ℝ) ≤ (a : ℝ) := hca
    have hab' : (a : ℝ) ≤ (b : ℝ) := hab
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

/-! ## Continuity -/

/-- **The initial-segment map of a path is continuous.** -/
theorem ucSegPt_continuous {x : X} (γ : Path x₀ x) (hB : HasDiscBasis X) :
    Continuous (UC.segPt γ) := by
  rw [(UC_isTopologicalBasis_basis hB).continuous_iff]
  rintro S ⟨e, V, hV, heV, rfl⟩
  rw [isOpen_iff_mem_nhds]
  intro t₀ ht₀
  -- a disc-like neighbourhood `W` of `γ t₀` inside `V`
  obtain ⟨W, hW, hγt₀W, hWV⟩ := hB (γ t₀) V hV.isOpen ht₀.1
  -- continuity of `γ` turns `W` into a neighbourhood of `t₀` in `unitInterval`
  have hnhds : γ ⁻¹' W ∈ 𝓝 t₀ := (hW.isOpen.preimage γ.continuous).mem_nhds hγt₀W
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine Filter.mem_of_superset (Metric.ball_mem_nhds t₀ (half_pos hε)) ?_
  intro t ht
  have htε : dist t t₀ < ε / 2 := ht
  refine ucSegPt_mem_sheet_near γ ht₀ hWV fun u hu => hball ?_
  have := ucSegPt_dist_le_dist_of_mem_uIcc hu
  show dist u t₀ < ε
  linarith

/-! ## The specification -/

/-- **Specification of the initial-segment point of the universal cover.** -/
theorem UC_segPt_spec {X : Type*} [TopologicalSpace X] {x₀ x : X} (hB : HasDiscBasis X)
    (γ : Path x₀ x) :
    Continuous (UC.segPt (γ := γ)) ∧ UC.segPt (γ := γ) 0 = UC.base x₀ ∧
      UC.segPt (γ := γ) 1 = (⟨x, Path.Homotopic.Quotient.mk γ⟩ : UC x₀) ∧
      (∀ (V : Set X) (s t : unitInterval), (s : ℝ) ≤ (t : ℝ) →
        (∀ u : unitInterval, (s : ℝ) ≤ u → (u : ℝ) ≤ t → γ u ∈ V) →
        UC.segPt γ t ∈ UC.sheet (UC.segPt γ s) V) := by
  -- Extensionality of the dependent pair `UC`, comparing the class fields up to the endpoint cast.
  have ext_cast : ∀ {e₁ e₂ : UC x₀} (h : e₁.pt = e₂.pt),
      e₁.cls.cast rfl h.symm = e₂.cls → e₁ = e₂ := by
    rintro ⟨p₁, c₁⟩ ⟨p₂, c₂⟩ h hc
    rw [UC.mk.injEq]
    exact ⟨h, (Path.Homotopic.Quotient.cast_heq rfl h.symm).symm.trans (heq_of_eq hc)⟩
  -- The initial point is the base point.
  have hend0 : UC.segPt γ 0 = UC.base x₀ := by
    refine ext_cast γ.source ?_
    change (Path.Homotopic.Quotient.mk (segTo γ 0)).cast rfl γ.source.symm
      = Path.Homotopic.Quotient.refl x₀
    have hpath : (segTo γ 0).cast rfl γ.source.symm = Path.refl x₀ := by
      ext s
      change γ (s * (0 : unitInterval)) = x₀
      rw [show s * (0 : unitInterval) = 0 from Subtype.ext (by simp)]
      exact γ.source
    rw [← Path.Homotopic.Quotient.mk_cast, hpath, Path.Homotopic.Quotient.mk_refl]
  -- The final point is the class of `γ`.
  have hend1 : UC.segPt γ 1 = (⟨x, Path.Homotopic.Quotient.mk γ⟩ : UC x₀) := by
    refine ext_cast γ.target ?_
    change (Path.Homotopic.Quotient.mk (segTo γ 1)).cast rfl γ.target.symm
      = Path.Homotopic.Quotient.mk γ
    have hpath : (segTo γ 1).cast rfl γ.target.symm = γ := by
      ext s
      change γ (s * (1 : unitInterval)) = γ s
      rw [show s * (1 : unitInterval) = s from Subtype.ext (by simp)]
    rw [← Path.Homotopic.Quotient.mk_cast, hpath]
  refine ⟨ucSegPt_continuous γ hB, hend0, hend1, ?_⟩
  -- Sheet membership for a piece of `γ` contained in `V`.
  intro V s t hst hV
  refine ucSegPt_mem_sheet γ s t fun u hu => ?_
  rw [Set.uIcc_of_le (show s ≤ t from hst)] at hu
  exact hV u hu.1 hu.2

end Work.EQ.UnivCover
