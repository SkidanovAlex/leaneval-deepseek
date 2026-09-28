import Mathlib
import Submission.Work.RatHurewicz.fibreNonvanishingFree
import Submission.Work.Serre.csrDefs
import Submission.Work.Serre.CWModel.Defs

namespace Work.RatHurewicz

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The subtype inclusion `(cylRetract q)⁻¹{b} ↪ (cylRetract q)⁻¹V` for `b ∈ V`, inside the
mapping cylinder of `q`. -/
def cylPrePtIncl {Γ : Type} [TopologicalSpace Γ] {X : Type} [TopologicalSpace X]
    (q : C(X, Γ)) {V : Set Γ} (b : Γ) (hb : b ∈ V) :
    C(↥((Work.Serre.cylRetract q) ⁻¹' ({b} : Set Γ)), ↥((Work.Serre.cylRetract q) ⁻¹' V)) where
  toFun x := ⟨(x : Work.Serre.cyl q), by
    have hx : (Work.Serre.cylRetract q) (x : Work.Serre.cyl q) = b := x.2
    show (Work.Serre.cylRetract q) (x : Work.Serre.cyl q) ∈ V
    rw [hx]; exact hb⟩
  continuous_toFun := by
    have hcont : Continuous (fun x : ↥((Work.Serre.cylRetract q) ⁻¹' ({b} : Set Γ)) =>
        (x : Work.Serre.cyl q)) := continuous_subtype_val
    exact hcont.subtype_mk (fun x => by
      have hx : (Work.Serre.cylRetract q) (x : Work.Serre.cyl q) = b := x.2
      show (Work.Serre.cylRetract q) (x : Work.Serre.cyl q) ∈ V
      rw [hx]; exact hb)

/-- **The `CVN` step.**  For a Serre fibration `q : X → Γ` with path connected base and path
connected fibres that are rationally `S^r` through degree `N`, every non-zero class
`U ∈ H^{r+1}(cyl q, range (cylIncl q); ℚ)` restricts to a non-zero class on the pair over any set
`V ∋ b`:

  `H^{r+1}(cyl q, A) ⟶ H^{r+1}((cylRetract q)⁻¹V, (cylRetract q)⁻¹V ∩ A)`  is non-zero on `U`.

Proof: the restriction to the fibre over `b` factors through the restriction to the part over `V`
(`Work.Thom.relCohMap_compA_apply`) and is injective (`Work.RatHurewicz.fibreNonvanishingFree`). -/
theorem cellwiseNonvanishing (r N : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ)
    {X : Type} [TopologicalSpace X] (q : C(X, Γ))
    (hq : Work.StemsB.IsSerreFibration q)
    (hpc : ∀ γ : Γ, PathConnectedSpace (Work.StemsB.fibre q γ))
    (hvan : ∀ γ : Γ, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hgen : ∀ γ : Γ, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) r
      ≅ ModuleCat.of ℚ ℚ))
    (V : Set Γ) (b : Γ) (hb : b ∈ V)
    (U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q)))
    (hU : U ≠ 0) :
    (Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥((Work.Serre.cylRetract q) ⁻¹' V), Work.Serre.cyl q))
      {x : ↥((Work.Serre.cylRetract q) ⁻¹' V) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
      (Set.range (Work.Serre.cylIncl q))
      (fun x hx => hx) ℚ (r + 1)).hom U ≠ 0 := by
  classical
  have hinj := Work.RatHurewicz.fibreNonvanishingFree r N hr hrN hΓ q hq hvan hpc hgen b
  have hfac : (Work.Thom.relCohMap (cylPrePtIncl q b hb)
        {x : ↥((Work.Serre.cylRetract q) ⁻¹' ({b} : Set Γ)) |
          (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
        {x : ↥((Work.Serre.cylRetract q) ⁻¹' V) |
          (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
        (fun x hx => hx) ℚ (r + 1)).hom
      ((Work.Thom.relCohMap
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥((Work.Serre.cylRetract q) ⁻¹' V), Work.Serre.cyl q))
        {x : ↥((Work.Serre.cylRetract q) ⁻¹' V) |
          (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
        (Set.range (Work.Serre.cylIncl q)) (fun x hx => hx) ℚ (r + 1)).hom U)
      = (Work.Thom.relCohMap
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥((Work.Serre.cylRetract q) ⁻¹' ({b} : Set Γ)), Work.Serre.cyl q))
        {x : ↥((Work.Serre.cylRetract q) ⁻¹' ({b} : Set Γ)) |
          (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
        (Set.range (Work.Serre.cylIncl q)) (fun x hx => hx) ℚ (r + 1)).hom U := by
    rw [Work.Thom.relCohMap_compA_apply
      {x : ↥((Work.Serre.cylRetract q) ⁻¹' ({b} : Set Γ)) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
      {x : ↥((Work.Serre.cylRetract q) ⁻¹' V) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
      (Set.range (Work.Serre.cylIncl q))
      (cylPrePtIncl q b hb)
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥((Work.Serre.cylRetract q) ⁻¹' V), Work.Serre.cyl q))
      (fun x hx => hx) (fun x hx => hx) (fun x hx => hx) ℚ (r + 1) U]
    exact congrArg (fun φ => φ.hom U)
      (Work.Thom.relCohMap_congrA
        {x : ↥((Work.Serre.cylRetract q) ⁻¹' ({b} : Set Γ)) |
          (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
        (Set.range (Work.Serre.cylIncl q))
        (f := (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥((Work.Serre.cylRetract q) ⁻¹' V), Work.Serre.cyl q)).comp (cylPrePtIncl q b hb))
        (f' := (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥((Work.Serre.cylRetract q) ⁻¹' ({b} : Set Γ)), Work.Serre.cyl q)))
        (ContinuousMap.ext fun x => rfl) (fun x hx => hx) (fun x hx => hx) ℚ (r + 1))
  intro hzero
  have hρ : (Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥((Work.Serre.cylRetract q) ⁻¹' ({b} : Set Γ)), Work.Serre.cyl q))
      {x : ↥((Work.Serre.cylRetract q) ⁻¹' ({b} : Set Γ)) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
      (Set.range (Work.Serre.cylIncl q)) (fun x hx => hx) ℚ (r + 1)).hom U
      = (Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥((Work.Serre.cylRetract q) ⁻¹' ({b} : Set Γ)), Work.Serre.cyl q))
      {x : ↥((Work.Serre.cylRetract q) ⁻¹' ({b} : Set Γ)) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
      (Set.range (Work.Serre.cylIncl q)) (fun x hx => hx) ℚ (r + 1)).hom 0 := by
    rw [← hfac, hzero]
    simp
  exact hU (hinj hρ)

/-- **The cellwise non-vanishing over an attached half-ball.**  In the setting of the cellular step
(`Γ' = attachCells (D-2) Γ ι f`), a non-zero relative class restricts non-trivially to the part of the
cylinder over the open half-ball `csrOpenBall i` of any attached cell. -/
theorem cellwiseNonvanishing_cell (r N D : ℕ) (hr : 1 ≤ r) (hD : 2 ≤ D) (hrN : r ≤ N)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
    {X : Type} [TopologicalSpace X] (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q)
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hgen : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) r
        ≅ ModuleCat.of ℚ ℚ))
    (i : ι)
    (U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q)))
    (hU : U ≠ 0) :
    (Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥((Work.Serre.cylRetract q) ⁻¹' Work.Serre.csrOpenBall (D - 2) Γ ι f i),
          Work.Serre.cyl q))
      {x : ↥((Work.Serre.cylRetract q) ⁻¹' Work.Serre.csrOpenBall (D - 2) Γ ι f i) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
      (Set.range (Work.Serre.cylIncl q))
      (fun x hx => hx) ℚ (r + 1)).hom U ≠ 0 :=
  cellwiseNonvanishing r N hr hrN
    (Work.Serre.CWModel.pathConnectedSpace_attachCells (D - 2) Γ ι f) q hq hpc hvan hgen
    _ _ (show Work.RatHurewicz.cellOrigin (D - 2) Γ ι f i
        ∈ Work.Serre.csrOpenBall (D - 2) Γ ι f i from
      ⟨Work.RatHurewicz.cellDiskCentre (D - 2), by
        simp [Work.RatHurewicz.cellInner, Work.RatHurewicz.cellDiskCentre],
        rfl⟩) U hU

end

end Work.RatHurewicz
