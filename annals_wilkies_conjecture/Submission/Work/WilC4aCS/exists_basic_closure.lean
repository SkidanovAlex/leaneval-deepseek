import Mathlib
import Submission.Work.WilC4aCS.Defs

namespace Work.WilC4aCS

/-- The DNF piece of the Tarski–Seidenberg projection that still accumulates at the origin.

`Yw d a τ` is the `(x, z)`-set of the Weierstrass side, `Fin.init` maps it onto
`coefFun d a ⁻¹' (projLast (SAcoef.set)) = coefFun d a ⁻¹' Y.set`, and `Y.set` is the finite union
of its DNF disjuncts.  A finite union of closures is the closure of the union, so one disjunct has
`0` in its closure. -/
theorem exists_basic_closure {n l : ℕ} (d : Fin (l + 1) → ℕ)
    (a : ∀ i, Fin (d i) → (Fin n → ℝ) → ℝ) (τ : Fin l → ℝ)
    (Y : WilkiesDesign.E.SA (∑ i, d i))
    (hY : WilkiesDesign.E.SA.set Y = WilkiesDesign.projLast
      (WilkiesDesign.E.SA.set (Work.WilC4aCS.SAcoef l d τ)))
    (hcl : (0 : Fin (n + 1) → ℝ) ∈ closure (Work.WilC4aCS.Yw d a τ)) :
    ∃ B ∈ Y.basics, (0 : Fin n → ℝ) ∈ closure (Work.WilC4aCS.Base d a B) := by
  classical
  -- `Y.basics` membership, transported through `List.toFinset`.
  have hmem : ∀ B, B ∈ Y.basics.toFinset ↔ B ∈ Y.basics := fun B => List.mem_toFinset
  -- `Fin.init` is continuous.
  have hcont : Continuous (fun y : Fin (n + 1) → ℝ => Fin.init y) := by
    apply continuous_pi
    intro i
    exact continuous_apply i.castSucc
  -- Every point of `Yw` projects (by `Fin.init`) into the union of the DNF pieces `Base d a B`.
  have hsub : Fin.init '' (Yw d a τ) ⊆ ⋃ B ∈ Y.basics.toFinset, Base d a B := by
    rintro x ⟨y, hy, rfl⟩
    -- `hy` unfolds to membership of `Fin.snoc (coefFun d a (Fin.init y)) (y (Fin.last n))`.
    have hy' : Fin.snoc (coefFun d a (Fin.init y)) (y (Fin.last n)) ∈ (SAcoef l d τ).set := hy
    -- hence `coefFun d a (Fin.init y)` lies in the projection of `SAcoef.set` ...
    have hproj : coefFun d a (Fin.init y) ∈ WilkiesDesign.projLast ((SAcoef l d τ).set) :=
      ⟨y (Fin.last n), hy'⟩
    rw [← hY] at hproj
    -- ... which is `SA.set Y`, the union of its DNF disjuncts.
    unfold WilkiesDesign.E.SA.set at hproj
    obtain ⟨B, hB, hBx⟩ := hproj
    exact Set.mem_iUnion₂.mpr ⟨B, (hmem B).mpr hB, hBx⟩
  -- `0` lies in the closure of the union of the pieces.
  have h0 : (0 : Fin n → ℝ) ∈ closure (⋃ B ∈ Y.basics.toFinset, Base d a B) := by
    have hmem0 : (0 : Fin n → ℝ) ∈ Fin.init '' closure (Yw d a τ) :=
      ⟨(0 : Fin (n + 1) → ℝ), hcl, by funext i; rfl⟩
    exact closure_mono hsub (image_closure_subset_closure_image hcont hmem0)
  -- The closure of a finite union is the union of the closures.
  rw [Finset.closure_biUnion Y.basics.toFinset (fun B => Base d a B)] at h0
  simp only [Set.mem_iUnion] at h0
  obtain ⟨B, hBs, h0B⟩ := h0
  exact ⟨B, (hmem B).mp hBs, h0B⟩

end Work.WilC4aCS
