import Mathlib
import Submission.NK.GlobalCFTdeep.LogLattice.LogLatticeMain
import Submission.NK.GlobalCFTdeep.Herbrand.Mul
import Submission.NK.GlobalCFTdeep.Herbrand.hZero_trivial
import Submission.NK.GlobalCFTdeep.Herbrand.hOne_trivial
import Submission.NK.GlobalCFTdeep.Herbrand.finite_tateCohomology_of_moduleFinite

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep.LogLattice

open NK.GlobalCFT

/-!
# The relation `h(M) = n · h(M')` for `M = M' + ℤ·e`

This file supplies the auxiliary lattice-theoretic material for the short exact sequence of
`ℤ[Gal(L/K)]`-modules

  `0 ⟶ M' = logLattice T ⟶ M = unitLattice T ⟶ ℤ ⟶ 0`

of `NK.GlobalCFTdeep.LogLattice.hZero_mul_hOne_unitLattice`: the `T`-units' log lattice is a
`Gal(L/K)`-stable subgroup of the full log lattice `M = M' + ℤ·e` contained in the sum-zero
hyperplane, so it meets `ℤ·e` trivially (because `∑_{w ∈ T} 1 = |T| ≠ 0`), which makes the
coefficient of the `ℤ·e`-component of an element of `M` well defined.  The coefficient is
`ℤ`-linear, equivariant (for the trivial action) and identifies `M ⧸ M'` with `ℤ`.

## Main definitions

* `NK.GlobalCFTdeep.LogLattice.coeff` (the coefficient) and `coeffHom` (its linearity);
* `NK.GlobalCFTdeep.LogLattice.logLatticeIncl`, `unitLatticeToTrivial`: the two maps of the
  sequence, and `unitLatticeSES`, the short complex they form.
-/

/-- A vector of the log lattice `M' = log U(T)` has coordinate sum zero: it is the log vector of a
`T`-unit, for which the product formula gives `∑_w log |a|_w = log 1 = 0`. -/
theorem sum_eq_zero_of_mem_logLattice {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (T : Set (Place L)) [Fintype ↥T]
    (hTinf : ∀ w : Place L, w.IsInfinite → w ∈ T) {y : ↥T → ℝ}
    (hy : y ∈ logLattice T) : ∑ w : ↥T, y w = 0 := by
  obtain ⟨a, rfl⟩ := mem_logLattice.mp hy
  rw [logVecLin_apply]
  exact LogLattice.sum_logVec_eq_zero (K := K) T hTinf _ (Additive.toMul a).2

theorem sum_smul_oneVec {L : Type} [Field L] [NumberField L] (T : Set (Place L)) [Fintype ↥T]
    (n : ℤ) : (∑ w : ↥T, (n • oneVec T) w) = (n : ℝ) * (Nat.card ↥T : ℝ) := by
  simp [oneVec, Finset.sum_const, mul_comm]

/-- `T` is nonempty, because it contains all the infinite places of the number field `L` and there
is at least one of those. -/
theorem natCard_T_ne_zero {L : Type} [Field L] [NumberField L] (T : Set (Place L)) [Fintype ↥T]
    (hTinf : ∀ w : Place L, w.IsInfinite → w ∈ T) : (Nat.card ↥T : ℝ) ≠ 0 := by
  have hTne : Nonempty ↥T := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace L))
    exact ⟨⟨Place.ofInfinite w, hTinf _ trivial⟩⟩
  have h : Nat.card ↥T ≠ 0 := Nat.card_ne_zero.mpr ⟨hTne, inferInstance⟩
  exact_mod_cast h

/-- The multiple `n • e` of the all-ones vector lies in the log lattice only for `n = 0`:
`logLattice T ⊆ sumZero T` while `∑_w (n · e)_w = n · |T| ≠ 0` for `n ≠ 0`. -/
theorem smul_oneVec_mem_logLattice_iff {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (T : Set (Place L)) [Fintype ↥T]
    (hTinf : ∀ w : Place L, w.IsInfinite → w ∈ T) (n : ℤ) :
    n • oneVec T ∈ logLattice T ↔ n = 0 := by
  constructor
  · intro hn
    have h0 := sum_eq_zero_of_mem_logLattice (K := K) T hTinf hn
    rw [sum_smul_oneVec T n] at h0
    have h1 : (n : ℝ) = 0 := (mul_eq_zero.mp h0).resolve_right (natCard_T_ne_zero T hTinf)
    exact_mod_cast h1
  · intro hn
    subst hn
    simp

/-- **Existence and uniqueness of the coefficient**: an element of the full log lattice
`M = M' + ℤ·e` has a unique expression `x = y + k·e` with `y ∈ M'` and `k : ℤ`. -/
theorem existsUnique_coeff {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (T : Set (Place L)) [Fintype ↥T]
    (hTinf : ∀ w : Place L, w.IsInfinite → w ∈ T) {x : ↥T → ℝ}
    (hx : x ∈ unitLattice T) :
    ∃! k : ℤ, x - k • oneVec T ∈ logLattice T := by
  obtain ⟨y, hy, n, rfl⟩ := mem_unitLattice_iff.mp hx
  refine ⟨n, ?_, ?_⟩
  · simpa using hy
  · intro m hm
    have h1 : ((y + n • oneVec T) - m • oneVec T) -
        ((y + n • oneVec T) - n • oneVec T) ∈ logLattice T := sub_mem hm (by simpa using hy)
    have h2 : ((y + n • oneVec T) - m • oneVec T) -
        ((y + n • oneVec T) - n • oneVec T) = (n - m) • oneVec T := by
      rw [sub_zsmul]; abel
    rw [h2] at h1
    have h3 := (smul_oneVec_mem_logLattice_iff (K := K) T hTinf (n - m)).mp h1
    omega

/-- The coefficient of the `ℤ·e`-component of an element of the full log lattice. -/
noncomputable def coeff {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (T : Set (Place L)) [Fintype ↥T]
    (hTinf : ∀ w : Place L, w.IsInfinite → w ∈ T) (x : ↥(unitLattice T)) : ℤ :=
  Classical.choose (existsUnique_coeff (K := K) T hTinf x.2)

theorem coeff_spec {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (T : Set (Place L)) [Fintype ↥T]
    (hTinf : ∀ w : Place L, w.IsInfinite → w ∈ T) (x : ↥(unitLattice T)) :
    (x : ↥T → ℝ) - coeff (K := K) T hTinf x • oneVec T ∈ logLattice T :=
  (Classical.choose_spec (existsUnique_coeff (K := K) T hTinf x.2)).1

theorem coeff_unique {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (T : Set (Place L)) [Fintype ↥T]
    (hTinf : ∀ w : Place L, w.IsInfinite → w ∈ T) (x : ↥(unitLattice T)) {k : ℤ}
    (h : (x : ↥T → ℝ) - k • oneVec T ∈ logLattice T) : coeff (K := K) T hTinf x = k :=
  ExistsUnique.unique (existsUnique_coeff (K := K) T hTinf x.2) (coeff_spec (K := K) T hTinf x) h

theorem coeff_add {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (T : Set (Place L)) [Fintype ↥T]
    (hTinf : ∀ w : Place L, w.IsInfinite → w ∈ T) (x y : ↥(unitLattice T)) :
    coeff (K := K) T hTinf (x + y) = coeff (K := K) T hTinf x + coeff (K := K) T hTinf y := by
  apply coeff_unique (K := K) T hTinf
  have hx := coeff_spec (K := K) T hTinf x
  have hy := coeff_spec (K := K) T hTinf y
  have hcoe : ((x + y : ↥(unitLattice T)) : ↥T → ℝ) = (x : ↥T → ℝ) + (y : ↥T → ℝ) := rfl
  rw [hcoe, add_zsmul]
  convert add_mem hx hy using 1
  abel

theorem coeff_zsmul {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (T : Set (Place L)) [Fintype ↥T]
    (hTinf : ∀ w : Place L, w.IsInfinite → w ∈ T) (n : ℤ) (x : ↥(unitLattice T)) :
    coeff (K := K) T hTinf (n • x) = n * coeff (K := K) T hTinf x := by
  apply coeff_unique (K := K) T hTinf
  have hx := coeff_spec (K := K) T hTinf x
  have heq : ((n • x : ↥(unitLattice T)) : ↥T → ℝ) - (n * coeff (K := K) T hTinf x) • oneVec T =
      n • ((x : ↥T → ℝ) - coeff (K := K) T hTinf x • oneVec T) := by
    rw [AddSubgroup.coe_zsmul, smul_sub, smul_smul]
  rw [heq]
  exact zsmul_mem hx n

/-- **The coefficient map `M = M' + ℤ·e → ℤ` is `ℤ`-linear.** -/
noncomputable def coeffHom {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (T : Set (Place L)) [Fintype ↥T]
    (hTinf : ∀ w : Place L, w.IsInfinite → w ∈ T) : ↥(unitLattice T) →ₗ[ℤ] ℤ where
  toFun := coeff (K := K) T hTinf
  map_add' := coeff_add (K := K) T hTinf
  map_smul' n x := by
    rw [coeff_zsmul (K := K) T hTinf n x]
    simp

/-- **The inclusion `M' = logLattice T ↪ M = unitLattice T`** of `ℤ[Gal(L/K)]`-modules. -/
noncomputable def logLatticeIncl {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (T : Set (Place L)) [Fintype ↥T]
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T) :
    logLatticeRep T hT ⟶ unitLatticeRep T hT :=
  letI := permAction T hT ℝ
  letI : DistribMulAction (L ≃ₐ[K] L) ↥(logLattice T) :=
    stableDistribMulActionSubgroup (logLattice T) (fun σ x hx => smul_mem_logLattice T hT σ hx)
  letI : DistribMulAction (L ≃ₐ[K] L) ↥(unitLattice T) :=
    stableDistribMulActionSubgroup (unitLattice T) (fun σ x hx => smul_mem_unitLattice T hT σ hx)
  Rep.ofHom
    { toFun := fun x => ⟨(x : ↥T → ℝ), logLattice_le_unitLattice T x.2⟩
      map_add' := fun x y => rfl
      map_smul' := fun n x => rfl
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        rfl }

/-- **The coefficient map `M = M' + ℤ·e ↠ ℤ`**, sending `y + k·e` to `k`, as a map of
`ℤ[Gal(L/K)]`-modules (the action on `ℤ` being trivial). -/
noncomputable def unitLatticeToTrivial {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (T : Set (Place L)) [Fintype ↥T]
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hTinf : ∀ w : Place L, w.IsInfinite → w ∈ T) :
    unitLatticeRep T hT ⟶ Rep.trivial ℤ (L ≃ₐ[K] L) ℤ :=
  letI := permAction T hT ℝ
  letI : DistribMulAction (L ≃ₐ[K] L) ↥(unitLattice T) :=
    stableDistribMulActionSubgroup (unitLattice T) (fun σ x hx => smul_mem_unitLattice T hT σ hx)
  Rep.ofHom
    { coeffHom (K := K) T hTinf with
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        refine coeff_unique (K := K) T hTinf ((unitLatticeRep T hT).ρ σ x) ?_
        have hx := coeff_spec (K := K) T hTinf x
        have hmem : (fun w : ↥T => ((x : ↥T → ℝ) - coeff (K := K) T hTinf x • oneVec T)
            ⟨σ⁻¹ • (w : Place L), hT σ⁻¹ w.2⟩) ∈ logLattice T :=
          smul_mem_logLattice T hT σ hx
        show (fun w : ↥T => (x : ↥T → ℝ) ⟨σ⁻¹ • (w : Place L), hT σ⁻¹ w.2⟩) -
            coeff (K := K) T hTinf x • oneVec T ∈ logLattice T
        convert hmem using 1
        funext w
        simp [oneVec] }

/-- **The short complex `0 ⟶ M' ⟶ M ⟶ ℤ ⟶ 0`** of `ℤ[Gal(L/K)]`-modules attached to the
decomposition `M = M' + ℤ·e` of the full log lattice. -/
noncomputable def unitLatticeSES {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (T : Set (Place L)) [Fintype ↥T]
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hTinf : ∀ w : Place L, w.IsInfinite → w ∈ T) :
    ShortComplex (Rep ℤ (L ≃ₐ[K] L)) :=
  ShortComplex.mk (logLatticeIncl T hT) (unitLatticeToTrivial T hT hTinf) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    let y : ↥(logLattice T) := x
    refine coeff_unique (K := K) T hTinf ⟨(y : ↥T → ℝ), logLattice_le_unitLattice T y.2⟩ ?_
    simp)

theorem coeff_surjective {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (T : Set (Place L)) [Fintype ↥T]
    (hTinf : ∀ w : Place L, w.IsInfinite → w ∈ T) :
    Function.Surjective (coeffHom (K := K) T hTinf) := by
  intro k
  exact ⟨⟨k • oneVec T, ⟨0, zero_mem _, k, by rw [zero_add]⟩⟩,
    coeff_unique (K := K) T hTinf _ (by rw [sub_self]; exact zero_mem _)⟩

/-- **The sequence `0 ⟶ M' ⟶ M ⟶ ℤ ⟶ 0` is short exact**: the inclusion is injective, the
coefficient map is surjective, and its kernel consists exactly of the log lattice. -/
theorem unitLatticeSES_shortExact {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (T : Set (Place L)) [Fintype ↥T]
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hTinf : ∀ w : Place L, w.IsInfinite → w ∈ T) :
    (unitLatticeSES T hT hTinf).ShortExact := by
  refine Commons.RepresentationTheory.GroupCohomology.shortExact_of_mono_epi_elementwise _
    ((Rep.mono_iff_injective _).2 ?_) ((Rep.epi_iff_surjective _).2 ?_) ?_
  · intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : ↥(unitLattice T) => (z : ↥T → ℝ)) hxy
  · intro k
    exact coeff_surjective (K := K) T hTinf k
  · intro x hx
    let y : ↥(unitLattice T) := x
    have hx' : coeff (K := K) T hTinf y = 0 := hx
    refine ⟨⟨(y : ↥T → ℝ), ?_⟩, Subtype.ext rfl⟩
    simpa [hx'] using coeff_spec (K := K) T hTinf y

/-- **The relation `h(M) = n · h(M')` for `M = M' + ℤ·e`.**  The full log lattice
`M = unitLattice T = logLattice T + ℤ·oneVec` is an extension of the trivial `ℤ[Gal(L/K)]`-module
`ℤ` by `M' = logLattice T`, so the long exact sequence in Tate cohomology gives

  `hZero M · hOne M' = n · hZero M' · hOne M`,   `n = Nat.card (L ≃ₐ[K] L)`.

## Proof sketch

`unitLattice T = {x | ∃ y ∈ logLattice T, ∃ k : ℤ, x = y + k • oneVec}` and
`logLattice T ≤ sumZero` with `∑_w oneVec T w = |T| ≠ 0`, so `logLattice T ∩ ℤ • oneVec = 0` and the
quotient `unitLattice T ⧸ logLattice T ≅ ℤ` is generated by the class of `e` (with the trivial
`G`-action).  Build the short complex of `Rep ℤ G`-modules
`0 → logLatticeRep T hT → unitLatticeRep T hT → Rep.trivial ℤ G ℤ → 0` (the quotient map sends
`y + k • e` to `k`), check short-exactness with
`Commons.RepresentationTheory.GroupCohomology.shortExact_of_mono_epi_elementwise` and
`Rep.mono_iff_injective`/`Rep.epi_iff_surjective`, then conclude with the raw identity
`hZero_mul_hOne_of_shortExact` (`Herbrand/Mul.lean`) together with
`hZero_trivial`/`hOne_trivial`.  The finiteness hypotheses of the long exact sequence come from
`NK.GlobalCFTdeep.Herbrand.finite_tateCohomology_of_moduleFinite` applied to
`finite_logLattice T hTinf` / `finite_unitLattice T hTinf`.

(`hTinf` is needed: for `T = ∅` the statement is false.) -/
theorem hZero_mul_hOne_unitLattice {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (T : Set (NK.GlobalCFT.Place L)) [Fintype ↥T]
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : NK.GlobalCFT.Place L⦄, w ∈ T → σ • w ∈ T)
    (hTinf : ∀ w : NK.GlobalCFT.Place L, w.IsInfinite → w ∈ T)
    [IsCyclic (L ≃ₐ[K] L)] :
    NK.GlobalCFTdeep.hZero (NK.GlobalCFTdeep.unitLatticeRep (L := L) T hT) *
        NK.GlobalCFTdeep.hOne (NK.GlobalCFTdeep.logLatticeRep (L := L) T hT) =
      Nat.card (L ≃ₐ[K] L) * NK.GlobalCFTdeep.hZero
          (NK.GlobalCFTdeep.logLatticeRep (L := L) T hT) *
        NK.GlobalCFTdeep.hOne (NK.GlobalCFTdeep.unitLatticeRep (L := L) T hT) := by
  classical
  have hmain : NK.GlobalCFTdeep.hZero (NK.GlobalCFTdeep.unitLatticeRep (L := L) T hT) *
        NK.GlobalCFTdeep.hOne (NK.GlobalCFTdeep.logLatticeRep (L := L) T hT) =
      Nat.card (L ≃ₐ[K] L) * NK.GlobalCFTdeep.hZero
          (NK.GlobalCFTdeep.logLatticeRep (L := L) T hT) *
        NK.GlobalCFTdeep.hOne (NK.GlobalCFTdeep.unitLatticeRep (L := L) T hT) := by
    letI : CommGroup (L ≃ₐ[K] L) := IsCyclic.commGroup
    haveI hlogfin : Module.Finite ℤ (logLatticeRep T hT).V := finite_logLattice T hTinf
    haveI hunitfin : Module.Finite ℤ (unitLatticeRep T hT).V := finite_unitLattice T hTinf
    haveI hF1 : Finite ↥(tateCohomology (unitLatticeSES T hT hTinf).X₁ 0) :=
      (Herbrand.finite_tateCohomology_of_moduleFinite (logLatticeRep T hT)).1
    haveI hF2 : Finite ↥(tateCohomology (unitLatticeSES T hT hTinf).X₁ 1) :=
      (Herbrand.finite_tateCohomology_of_moduleFinite (logLatticeRep T hT)).2
    haveI hF3 : Finite ↥(tateCohomology (unitLatticeSES T hT hTinf).X₂ 0) :=
      (Herbrand.finite_tateCohomology_of_moduleFinite (unitLatticeRep T hT)).1
    haveI hF4 : Finite ↥(tateCohomology (unitLatticeSES T hT hTinf).X₂ 1) :=
      (Herbrand.finite_tateCohomology_of_moduleFinite (unitLatticeRep T hT)).2
    haveI hF5 : Finite ↥(tateCohomology (unitLatticeSES T hT hTinf).X₃ 0) :=
      (Herbrand.finite_tateCohomology_of_moduleFinite (Rep.trivial ℤ (L ≃ₐ[K] L) ℤ)).1
    haveI hF6 : Finite ↥(tateCohomology (unitLatticeSES T hT hTinf).X₃ 1) :=
      (Herbrand.finite_tateCohomology_of_moduleFinite (Rep.trivial ℤ (L ≃ₐ[K] L) ℤ)).2
    have hOne3 : hOne (unitLatticeSES T hT hTinf).X₃ = 1 := Herbrand.hOne_trivial (L ≃ₐ[K] L)
    have hZero3 : hZero (unitLatticeSES T hT hTinf).X₃ = Nat.card (L ≃ₐ[K] L) :=
      Herbrand.hZero_trivial (L ≃ₐ[K] L)
    have hmult := hZero_mul_hOne_of_shortExact (unitLatticeSES T hT hTinf)
      (unitLatticeSES_shortExact T hT hTinf)
    rw [hOne3, hZero3, mul_one] at hmult
    rw [Nat.mul_comm (hZero (unitLatticeSES T hT hTinf).X₁) (Nat.card (L ≃ₐ[K] L))] at hmult
    exact hmult
  exact hmain

end NK.GlobalCFTdeep.LogLattice
