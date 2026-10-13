import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.DimAPI.rankLocusAux
import Submission.Work.WilE7.DimAPI.exists_locallyConstRank
import Submission.Work.WilE7.DimAPI.jac_eq_fderiv
import Submission.Work.WilE7.DimAPI.range_fderiv_good_eq_top
import Submission.Work.WilE7.Endgame.map_ker_eq_top_iff_prod_surjective
import Submission.Work.WilE7.Endgame.fderiv_prod_eq_jac_prod

/-!
# G2: persistence of the tangent–surjectivity condition `(ker (jac S ·)).map A = ⊤`

`S : Stratum 0 M` is an absolute stratum of `ℝ^(0+M)` with `S.j` defining equations `h`; it is
`Good`, so at every point `z ∈ S.X.set` the full Jacobian `jac S z` is onto `ℝ^(S.j)`
(`DimAPI.range_fderiv_good_eq_top`, `DimAPI.jac_eq_fderiv`).  Let `A : ℝ^(0+M) → ℝ^r` be a linear
map whose restriction to the tangent space `ker (jac S z)` is onto `ℝ^r`.

The lemma says that this condition persists: near `z` (in the ambient space, hence a fortiori for
points of `S.X.set`), `A` is onto `ker (jac S y)` for every `y`.

The proof is a single observation.  The pair map
`Ψ w = ((a ↦ h_a w), A w) : ℝ^(0+M) → ℝ^(S.j) × ℝ^r`
is analytic, and its differential is the matrix `(jac S y).prod A`.  At `z` the pair map
`(jac S z).prod A` is onto: given `(u,v)`, solve `jac S z w₁ = u` (possible because `jac S z` is
onto) and then `A w₂ = v - A w₁` with `w₂ ∈ ker (jac S z)` (possible by hypothesis); `w₁ + w₂`
works.  Surjectivity of a linear map between finite-dimensional spaces is an open condition on the
family (`isOpen_le_finrank_range_*` plus the fact that the target has dimension `S.j + r`), and
`y ↦ fderiv ℝ Ψ y` is continuous near `z` because `Ψ` is analytic, so
`(jac S y).prod A` remains onto for all `y` near `z`; its range has dimension `S.j + r` there,
which is the maximum possible, so it is all of the target.  Finally, if `(jac S y).prod A` is onto
then for every `v` there is `w` with `jac S y w = 0` and `A w = v`, i.e. `v ∈ A (ker (jac S y))`.
-/

set_option autoImplicit false
noncomputable section
open Classical Filter Topology

namespace Work.WilE7.Endgame

open WilkiesDesign WilkiesDesign.E

/-- **Lower semicontinuity of the rank, general target.**  The continuous linear maps
`E →L[ℝ] F`, with `F` finite-dimensional, whose range has dimension at least `M` form an open set.
This is `isOpen_setOfPred_nat_le_rank` (Mathlib) transported across the identification of
`LinearMap.rank` with `Module.finrank` of the range. -/
theorem isOpen_le_finrank_range_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] (M : ℕ) :
    IsOpen {f : E →L[ℝ] F | M ≤ Module.finrank ℝ (LinearMap.range (f : E →ₗ[ℝ] F))} := by
  have h := isOpen_setOfPred_nat_le_rank (𝕜 := ℝ) (E := E) (F := F) M
  convert h using 1
  ext f
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, LinearMap.rank, ← Module.finrank_eq_rank]
  exact (Nat.cast_le (α := Cardinal)).symm

/-- On a `Good` absolute stratum the full Jacobian has full range: it is the differential of the
equation map (`DimAPI.jac_eq_fderiv`), which is onto on a `Good` stratum
(`DimAPI.range_fderiv_good_eq_top`). -/
theorem jac_range_eq_top_of_good_abs {M : ℕ} (S : Stratum 0 M) (hS : S.Good)
    {z : Fin (0 + M) → ℝ} (hz : z ∈ S.X.set) : (Work.WilE7.MainDesign.jac S z).range = ⊤ := by
  rw [Work.WilE7.DimAPI.jac_eq_fderiv]
  exact Work.WilE7.DimAPI.range_fderiv_good_eq_top S hS hz

theorem g2_kjac_persist {M r : ℕ} (S : WilkiesDesign.E.Stratum 0 M)
    (hS : S.Good) (A : (Fin (0 + M) → ℝ) →ₗ[ℝ] (Fin r → ℝ))
    (z : Fin (0 + M) → ℝ) (hz : z ∈ S.X.set)
    (hA : (LinearMap.ker (Work.WilE7.MainDesign.jac S z)).map A = ⊤) :
    ∀ᶠ y in nhds z, y ∈ S.X.set →
      (LinearMap.ker (Work.WilE7.MainDesign.jac S y)).map A = ⊤ := by
  classical
  -- The analytic pair map `Ψ w = ((a ↦ h_a w), A w)`.
  set Ψ : (Fin (0 + M) → ℝ) → (Fin S.j → ℝ) × (Fin r → ℝ) := fun w =>
    ((fun a : Fin S.j => eaEval S.X.c (S.h a) w), (LinearMap.toContinuousLinearMap A) w) with hΨ
  have hΨan : AnalyticAt ℝ Ψ z := by
    rw [hΨ]
    exact (AnalyticAt.pi fun a => Work.WilE5.Strat.analyticAt_eaEval S.X.c (S.h a) z).prod
      ((LinearMap.toContinuousLinearMap A).analyticAt z)
  -- `Ψ` is analytic, so its derivative is continuous.
  have hcont : ContinuousAt (fderiv ℝ Ψ) z := hΨan.fderiv.continuousAt
  -- The derivative of `Ψ` is `jac S ·` paired with `A`.
  have hder : ∀ y, fderiv ℝ Ψ y
      = (((Work.WilE7.MainDesign.jac S y).prod A).toContinuousLinearMap) := by
    intro y
    rw [hΨ]
    exact fderiv_prod_eq_jac_prod S A y
  -- At `z` the pair map is onto, by `Good` and the hypothesis on `A`.
  have hJtop : (Work.WilE7.MainDesign.jac S z).range = ⊤ := jac_range_eq_top_of_good_abs S hS hz
  have hzsurj : Function.Surjective ((Work.WilE7.MainDesign.jac S z).prod A) :=
    (map_ker_eq_top_iff_prod_surjective (Work.WilE7.MainDesign.jac S z) A hJtop).mp hA
  -- The dimension of the target of the pair map is `S.j + r`.
  have hprod : Module.finrank ℝ ((Fin S.j → ℝ) × (Fin r → ℝ)) = S.j + r := by
    simp [Module.finrank_prod]
  -- Hence its range has the maximal possible dimension `S.j + r`.
  have hzrank : S.j + r ≤ Module.finrank ℝ (LinearMap.range
      ((fderiv ℝ Ψ z : (Fin (0 + M) → ℝ) →L[ℝ] ((Fin S.j → ℝ) × (Fin r → ℝ))) :
        (Fin (0 + M) → ℝ) →ₗ[ℝ] ((Fin S.j → ℝ) × (Fin r → ℝ)))) := by
    rw [hder z, LinearMap.coe_toContinuousLinearMap, LinearMap.range_eq_top.mpr hzsurj,
      Submodule.topEquiv.finrank_eq, hprod]
  -- Surjectivity is open, so the dimension bound persists near `z`.
  have hev : ∀ᶠ y in nhds z, S.j + r ≤ Module.finrank ℝ (LinearMap.range
      ((fderiv ℝ Ψ y : (Fin (0 + M) → ℝ) →L[ℝ] ((Fin S.j → ℝ) × (Fin r → ℝ))) :
        (Fin (0 + M) → ℝ) →ₗ[ℝ] ((Fin S.j → ℝ) × (Fin r → ℝ)))) :=
    hcont.preimage_mem_nhds
      ((isOpen_le_finrank_range_clm (E := Fin (0 + M) → ℝ)
        (F := (Fin S.j → ℝ) × (Fin r → ℝ)) (S.j + r)).mem_nhds hzrank)
  filter_upwards [hev] with y hy _hyS
  rw [hder y, LinearMap.coe_toContinuousLinearMap] at hy
  -- The range of `(jac S y).prod A` has dimension at most `S.j + r`, hence exactly `S.j + r`.
  have hle : Module.finrank ℝ (LinearMap.range ((Work.WilE7.MainDesign.jac S y).prod A))
      ≤ S.j + r := by
    have h := Submodule.finrank_le
      (s := LinearMap.range ((Work.WilE7.MainDesign.jac S y).prod A))
    rw [hprod] at h
    exact h
  have htop : LinearMap.range ((Work.WilE7.MainDesign.jac S y).prod A) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [hprod]
    exact le_antisymm hle hy
  -- So `(jac S y).prod A` is onto, and surjectivity of the pair map is the claim.
  exact (map_ker_eq_top_iff_prod_surjective (Work.WilE7.MainDesign.jac S y) A
    (jac_range_eq_top_of_good_abs S hS _hyS)).mpr (LinearMap.range_eq_top.mp htop)

end Work.WilE7.Endgame

