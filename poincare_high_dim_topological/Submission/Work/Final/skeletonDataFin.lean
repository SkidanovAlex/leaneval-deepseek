import Mathlib
import Submission.Work.Final.SkeletonFix
import Submission.Work.PL.Subdiv.DomDim

/-!
# `Work.Final.skeletonDataFin`

The genuine skeleta `Work.Geo.DualStretch.Low` / `Work.Geo.DualStretch.High` inhabit the repaired
interface `Work.Final.SkeletonDataFin n` of `Submission/Work/Final/SkeletonFix.lean`.

With the `P.faces.Finite` hypotheses of `SkeletonDataFin` every field is a delivered theorem:

* `low_sub`, `high_sub` — `Work.Geo.DualStretch.Low_subset_space`, `High_subset_space`;
* `low_closed`, `high_closed` — the (private) `isClosed_Low`/`isClosed_High` of
  `Submission/Work/Geo/DualStretch/dual_stretch.lean`, reproduced here as `isClosed_Low_fin` /
  `isClosed_High_fin` since the originals are `private`;
* `low_dom` — `Work.Geo.DualStretch.low_dom`;
* `high_dom` — `Work.Geo.DualStretch.high_dom` with the dimension cast
  `((n - p - 1 : ℕ) : ℤ) = (n : ℤ) - (p : ℤ) - 1` when `p + 1 ≤ n`, and `High P p = ∅`
  otherwise (via `Work.Geo.DualStretch.face_card_le`);
* `dual_stretch` — `Work.Geo.DualStretch.dual_stretch` verbatim.
-/

open Set Metric
open scoped Classical

namespace Work.Final

variable {n : ℕ}

/-- `Low P p`, for a finite complex, written as the finite union over the faces of cardinality
`≤ p + 1`; used only to exhibit it as closed. -/
theorem eq_biUnion_Low (P : PL.Cx n) (hP : P.faces.Finite) (p : ℕ) :
    Work.Geo.DualStretch.Low P p =
      ⋃ σ ∈ (hP.toFinset.filter (fun σ => σ.card ≤ p + 1)), PL.simp σ := by
  ext x; constructor
  · rintro ⟨s, hs, hc, hxs⟩
    exact mem_iUnion₂.mpr ⟨s, Finset.mem_filter.mpr
      ⟨(Set.Finite.mem_toFinset hP).mpr hs, hc⟩, hxs⟩
  · intro hx
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
    exact ⟨s, (Set.Finite.mem_toFinset hP).mp (Finset.mem_filter.mp hs).1,
      (Finset.mem_filter.mp hs).2, hxs⟩

/-- The `p`-skeleton `Low P p` of a finite complex is closed. -/
theorem isClosed_Low_fin (P : PL.Cx n) (hP : P.faces.Finite) (p : ℕ) :
    IsClosed (Work.Geo.DualStretch.Low P p) := by
  rw [eq_biUnion_Low P hP p]
  exact isClosed_biUnion_finset (fun σ _ => (Finset.finite_toSet σ).isClosed_convexHull ℝ)

/-- `High P p`, for a finite complex, written as the finite union over its finite cover
`Work.Geo.DualStretch.highCover`; used only to exhibit it as closed. -/
theorem eq_biUnion_High (P : PL.Cx n) (hP : P.faces.Finite) (p : ℕ) :
    Work.Geo.DualStretch.High P p =
      ⋃ s ∈ Work.Geo.DualStretch.highCover P hP p, PL.simp s := by
  apply Subset.antisymm (Work.Geo.DualStretch.High_subset_highCover P hP p)
  intro x hx
  obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
  rw [Work.Geo.DualStretch.highCover, Finset.mem_image] at hs
  obtain ⟨T, hT, rfl⟩ := hs
  rw [Finset.mem_filter] at hT
  exact ⟨T, fun σ hσ => (Set.Finite.mem_toFinset hP).mp (Finset.mem_powerset.mp hT.1 hσ),
    hT.2.1, hT.2.2.1, hT.2.2.2, hxs⟩

/-- The dual skeleton `High P p` of a finite complex is closed. -/
theorem isClosed_High_fin (P : PL.Cx n) (hP : P.faces.Finite) (p : ℕ) :
    IsClosed (Work.Geo.DualStretch.High P p) := by
  rw [eq_biUnion_High P hP p]
  exact isClosed_biUnion_finset (fun s _ => (Finset.finite_toSet s).isClosed_convexHull ℝ)

/-- `High P p` is `(n-p-1)`-dimensional, with the truncated natural-number dimension of the
`SkeletonDataFin` interface. -/
theorem high_dom_trunc (P : PL.Cx n) (hP : P.faces.Finite) (p : ℕ) :
    PL.DomDim (Work.Geo.DualStretch.High P p) ((n - p - 1 : ℕ) : ℤ) := by
  by_cases hpn : p + 1 ≤ n
  · have hcast : ((n - p - 1 : ℕ) : ℤ) = (n : ℤ) - (p : ℤ) - 1 := by omega
    rw [hcast]
    exact Work.Geo.DualStretch.high_dom P hP p
  · have hempty : Work.Geo.DualStretch.High P p = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨T, hT, hne, hchain, hcard, hx⟩
      obtain ⟨σ, hσ⟩ := hne
      have h1 : σ.card ≤ n + 1 := Work.Geo.DualStretch.face_card_le P (hT hσ)
      have h2 := hcard σ hσ
      omega
    rw [hempty]
    exact Work.PL.Subdiv.domDim_empty _

/-- `Work.Final.SkeletonDataFin n` is inhabited by the **genuine** skeleta of
`Work.Geo.DualStretch`: take `Low := Work.Geo.DualStretch.Low`,
`High := Work.Geo.DualStretch.High`.  With the `P.faces.Finite` hypotheses of `SkeletonDataFin`
every field is a delivered theorem:

* `low_sub`, `high_sub` — `Work.Geo.DualStretch.Low_subset_space`, `High_subset_space`;
* `low_closed`, `high_closed` — the *private* `isClosed_Low`/`isClosed_High` of
  `Submission/Work/Geo/DualStretch/dual_stretch.lean` (copy their proofs: rewrite `Low P p` as the
  finite union over `hP.toFinset.filter (fun s => s.card ≤ p + 1)` resp. `High P p` as the finite
  union over `Work.Geo.DualStretch.highCover P hP p`, and use `isClosed_biUnion_finset` with
  `(Finset.finite_toSet s).isClosed_convexHull ℝ`; `Work.Geo.DualStretch.High_subset_highCover` is
  public and gives one of the two inclusions);
* `low_dom` — `Work.Geo.DualStretch.low_dom P hP p`;
* `high_dom` — `Work.Geo.DualStretch.high_dom P hP p` gives
  `DomDim (High P p) ((n : ℤ) - (p : ℤ) - 1)`; convert the truncated cast
  `((n - p - 1 : ℕ) : ℤ) = (n : ℤ) - (p : ℤ) - 1` with `omega` when `p + 1 ≤ n`, and when `n ≤ p + 1`
  use that the field's dimension `0` is larger (or show `High P p = ∅` via
  `Work.Geo.DualStretch.face_card_le` and use `Work.PL.Subdiv.domDim_empty`);
* `dual_stretch` — `Work.Geo.DualStretch.dual_stretch` verbatim. -/
theorem skeletonDataFin (n : ℕ) : Nonempty (Work.Final.SkeletonDataFin n) :=
  ⟨{ Low := fun P p => Work.Geo.DualStretch.Low P p
     High := fun P p => Work.Geo.DualStretch.High P p
     low_sub := fun P p => Work.Geo.DualStretch.Low_subset_space P p
     high_sub := fun P p => Work.Geo.DualStretch.High_subset_space P p
     low_closed := fun P p hP => isClosed_Low_fin P hP p
     high_closed := fun P p hP => isClosed_High_fin P hP p
     low_dom := fun P p hP => Work.Geo.DualStretch.low_dom P hP p
     high_dom := fun P p hP => high_dom_trunc P hP p
     dual_stretch := fun _p β α hp hα hαβ P hP hsp N₁ N₂ h₁ h₂ hL hH =>
       Work.Geo.DualStretch.dual_stretch hp β α hα hαβ P hP hsp N₁ N₂ h₁ h₂ hL hH }⟩

end Work.Final
