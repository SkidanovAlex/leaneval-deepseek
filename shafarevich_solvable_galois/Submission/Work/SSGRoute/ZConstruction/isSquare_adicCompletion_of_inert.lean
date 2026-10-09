import Mathlib
import Submission.Work.SSGRoute.ZConstruction.LocalSquares
import Submission.Work.SSGRoute.ZDataTwo.finPairEqZeroOfKillsInertia
import Submission.Work.SSGRoute.NodeS37.finiteFieldQuadraticSquares
import Submission.Work.SSGRoute.NodeS37.henselUnitSquare
import Submission.Commons.NumberTheory.NumberField.Completion.exists_ringEquiv_adicCompletion_of_residue_ringEquiv
import Submission.Commons.NumberTheory.NumberField.Completion.adicCompletionMap_mem_integers_iff
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_residueField_adicCompletion_eq_pow_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.liesOver_maximalIdeal_adicCompletionIntegers
import Submission.Commons.NumberTheory.NumberField.Completion.compactSpace_adicCompletionIntegers
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver

open scoped NumberField WithZero

namespace Work.SSGRoute.ZConstruction

/-- **Hensel lifting for the integers of an odd adic completion**: a unit of
`P.adicCompletionIntegers M` whose residue is a square is a square in the completion
`P.adicCompletion M` (in fact its square root may be taken to be a unit of the completion).

This is the general-number-field form of `Work.SSGRoute.NodeS37.exists_sq_of_residue_isSquare`
(which is stated only for `K : IntermediateField k Ω`); the proof is the same short argument via
`Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow` at `n = 2`, with the Henselian
instance `Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing`. -/
theorem exists_unit_sq_of_residue_isSquare_adicCompletion {M : Type} [Field M] [NumberField M]
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M))
    (h2 : IsUnit (2 : P.adicCompletionIntegers M))
    (u : (P.adicCompletionIntegers M)ˣ)
    (hsq : IsSquare ((IsLocalRing.residue (P.adicCompletionIntegers M))
      (u : P.adicCompletionIntegers M))) :
    ∃ c : (P.adicCompletion M)ˣ,
      (c : P.adicCompletion M) ^ 2 =
        algebraMap (P.adicCompletionIntegers M) (P.adicCompletion M)
          (u : P.adicCompletionIntegers M) := by
  classical
  haveI := Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing
    (R := NumberField.RingOfIntegers M) (K := M) P
  have hmem : Units.map (IsLocalRing.residue (P.adicCompletionIntegers M)).toMonoidHom u ∈
      (powMonoidHom 2).range := by
    obtain ⟨w, hw⟩ := hsq
    have hne : (IsLocalRing.residue (P.adicCompletionIntegers M))
        (u : P.adicCompletionIntegers M) ≠ 0 :=
      IsUnit.ne_zero (IsUnit.map _ (Units.isUnit u))
    refine ⟨Units.mk0 w (by rintro rfl; exact hne (by simpa using hw)), ?_⟩
    ext
    rw [powMonoidHom_apply, Units.coe_map, Units.val_pow_eq_pow_val, pow_two, Units.val_mk0]
    change w * w =
      (IsLocalRing.residue (P.adicCompletionIntegers M)) (u : P.adicCompletionIntegers M)
    rw [hw]
  obtain ⟨b, hb⟩ := Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow
    (R := P.adicCompletionIntegers M) 2 (by simpa using h2) u hmem
  have hb2 : b ^ 2 = u := by
    rw [powMonoidHom_apply] at hb
    exact hb
  refine ⟨Units.map (algebraMap (P.adicCompletionIntegers M) (P.adicCompletion M)).toMonoidHom b, ?_⟩
  have hb2coe : ((b : P.adicCompletionIntegers M)) ^ 2 = ((u : P.adicCompletionIntegers M)) := by
    have h := congrArg (fun v : (P.adicCompletionIntegers M)ˣ => (v : P.adicCompletionIntegers M)) hb2
    simpa [Units.val_pow_eq_pow_val, pow_two] using h
  rw [Units.coe_map, ← map_pow, hb2coe]
  rfl

/-- **`2` is a unit of the integers of the completion at a prime lying over a prime at which `2` is a unit.**

If `𝔓` lies over `𝔭` and `2` is a unit in `𝔭.adicCompletionIntegers L`, then `2` is a unit in
`𝔓.adicCompletionIntegers K`.  The ring homomorphism
`Commons.NumberTheory.NumberField.Completion.intCompletionMap 𝔭 𝔓 hLies` sends `2` to `2`, so
`IsUnit (2 : 𝔭.adicCompletionIntegers L)` maps to `IsUnit (2 : 𝔓.adicCompletionIntegers K)`. -/
theorem isUnit_two_adicCompletionIntegers_of_liesOver {L K : Type} [Field L] [NumberField L]
    [Field K] [NumberField K] [Algebra L K] [FiniteDimensional L K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (𝔓 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hLies : 𝔓.asIdeal.LiesOver 𝔭.asIdeal)
    (h2 : IsUnit (2 : 𝔭.adicCompletionIntegers L)) :
    IsUnit (2 : 𝔓.adicCompletionIntegers K) := by
  have h2' : (Commons.NumberTheory.NumberField.Completion.intCompletionMap 𝔭 𝔓 hLies)
      (2 : 𝔭.adicCompletionIntegers L) = (2 : 𝔓.adicCompletionIntegers K) := by
    simpa using map_ofNat (Commons.NumberTheory.NumberField.Completion.intCompletionMap 𝔭 𝔓 hLies) 2
  rw [← h2']
  exact IsUnit.map
    (Commons.NumberTheory.NumberField.Completion.intCompletionMap 𝔭 𝔓 hLies).toMonoidHom h2

/-- **An inert quadratic residue extension turns a residue unit into a square.**

Let `L ⊆ K` be number fields, `𝔓` a prime of `𝓞 K` lying over `𝔭` with **inertia degree 2** over `𝔭`,
and let `2` be a unit in `𝔭.adicCompletionIntegers L`.  Then for every unit `b` of
`𝔭.adicCompletionIntegers L`, the residue of its image under
`Commons.NumberTheory.NumberField.Completion.intCompletionMap 𝔭 𝔓 hLies` is a square in
`IsLocalRing.ResidueField (𝔓.adicCompletionIntegers K)`.

Indeed the natural map `ψ = natResidueMap 𝔭 𝔓 hLies` of residue fields is injective, the residue
extension has degree `2` (from `hint`, via the cardinalities of the residue fields), the base
residue field is a finite field of odd order (since `2` is a unit there), and every element of a
finite field of odd order is a square in a quadratic extension of it
(`Work.SSGRoute.NodeS37.isSquare_algebraMap_of_finrank_two`). -/
theorem isSquare_residue_intCompletionMap_of_inertiaDeg_two {L K : Type} [Field L] [NumberField L]
    [Field K] [NumberField K] [Algebra L K] [FiniteDimensional L K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (𝔓 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hLies : 𝔓.asIdeal.LiesOver 𝔭.asIdeal)
    (h2 : IsUnit (2 : 𝔭.adicCompletionIntegers L))
    (hint : 𝔓.asIdeal.inertiaDeg (NumberField.RingOfIntegers L) = 2)
    (b : (𝔭.adicCompletionIntegers L)ˣ) :
    IsSquare ((IsLocalRing.residue (𝔓.adicCompletionIntegers K))
      (Units.map (Commons.NumberTheory.NumberField.Completion.intCompletionMap 𝔭 𝔓 hLies).toMonoidHom b)) := by
  classical
  let F := IsLocalRing.ResidueField (𝔭.adicCompletionIntegers L)
  let E := IsLocalRing.ResidueField (𝔓.adicCompletionIntegers K)
  let ψ : F →+* E := Commons.NumberTheory.NumberField.Completion.natResidueMap 𝔭 𝔓 hLies
  have hψinj : Function.Injective ψ :=
    Commons.NumberTheory.NumberField.Completion.natResidueMap_injective 𝔭 𝔓 hLies
  haveI hFfin : Finite F :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion L 𝔭
  haveI hEfin : Finite E :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion K 𝔓
  -- the residue of the image of `b` under the integer-ring map is `ψ (residue b)`
  have hres : (IsLocalRing.residue (𝔓.adicCompletionIntegers K))
      (Units.map (Commons.NumberTheory.NumberField.Completion.intCompletionMap 𝔭 𝔓 hLies).toMonoidHom b) =
      ψ ((IsLocalRing.residue (𝔭.adicCompletionIntegers L)) (b : 𝔭.adicCompletionIntegers L)) := by
    rw [show ((Units.map (Commons.NumberTheory.NumberField.Completion.intCompletionMap 𝔭 𝔓 hLies).toMonoidHom b :
        (𝔓.adicCompletionIntegers K)ˣ) : 𝔓.adicCompletionIntegers K) =
        Commons.NumberTheory.NumberField.Completion.intCompletionMap 𝔭 𝔓 hLies
          (b : 𝔭.adicCompletionIntegers L) from Units.coe_map _ _]
    exact Commons.NumberTheory.NumberField.Completion.natResidueMap_residue 𝔭 𝔓 hLies
      (b : 𝔭.adicCompletionIntegers L)
  rw [hres]
  -- `2` gives nonzero elements of both residue fields
  have hres2 : (IsLocalRing.residue (𝔭.adicCompletionIntegers L))
      (2 : 𝔭.adicCompletionIntegers L) = (2 : F) := by
    simpa using map_ofNat (IsLocalRing.residue (𝔭.adicCompletionIntegers L)) 2
  have h2F : (2 : F) ≠ 0 := by
    rw [← hres2]
    exact (IsLocalRing.residue_ne_zero_iff_isUnit (2 : 𝔭.adicCompletionIntegers L)).mpr h2
  -- the base residue field is a finite field of odd order
  have hcharF : ringChar F ≠ 2 := by
    intro h
    haveI : CharP F 2 := h ▸ (inferInstance : CharP F (ringChar F))
    exact h2F (CharP.cast_eq_zero F 2)
  haveI : Fintype F := Fintype.ofFinite F
  have hodd : Odd (Fintype.card F) := by
    rw [Nat.odd_iff]
    exact FiniteField.odd_card_of_char_ne_two hcharF
  -- the degree of the residue extension is the inertia degree `2`
  haveI : Fintype E := Fintype.ofFinite E
  letI : Algebra F E := ψ.toAlgebra
  haveI : Module.Finite F E := Module.Finite.of_finite
  have hpow : Nat.card E = Nat.card F ^ Module.finrank F E := Module.natCard_eq_pow_finrank
  have hpow' : Nat.card E =
      Nat.card F ^ 𝔓.asIdeal.inertiaDeg (NumberField.RingOfIntegers L) :=
    Commons.NumberTheory.NumberField.Completion.natCard_residueField_adicCompletion_eq_pow_inertiaDeg
      L K 𝔭 𝔓 hLies
  have hbase : 2 ≤ Nat.card F := Finite.one_lt_card
  have hfin : Module.finrank F E = 2 := by
    refine Nat.pow_right_injective hbase ?_
    show Nat.card F ^ Module.finrank F E = Nat.card F ^ 2
    rw [← hpow, hpow', hint]
  -- `2` is nonzero in the residue field of `𝔓`
  have hmap2 : ψ (2 : F) = (2 : E) := by
    simpa using map_ofNat ψ 2
  have h2E : (2 : E) ≠ 0 := by
    intro hzero
    refine h2F (hψinj ?_)
    rw [hmap2, map_zero]
    exact hzero
  have hcharE : ringChar E ≠ 2 := by
    intro h
    haveI : CharP E 2 := h ▸ (inferInstance : CharP E (ringChar E))
    exact h2E (CharP.cast_eq_zero E 2)
  exact Work.SSGRoute.NodeS37.isSquare_algebraMap_of_finrank_two hfin hcharE hodd
    ((IsLocalRing.residue (𝔭.adicCompletionIntegers L)) (b : 𝔭.adicCompletionIntegers L))

theorem isSquare_adicCompletion_of_inert {L K : Type} [Field L] [NumberField L] [Field K]
    [NumberField K] [Algebra L K] [FiniteDimensional L K] [IsGalois L K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (𝔓 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hLies : 𝔓.asIdeal.LiesOver 𝔭.asIdeal)
    (h2 : IsUnit (2 : 𝔭.adicCompletionIntegers L))
    (hunr : 𝔓.asIdeal.ramificationIdx (NumberField.RingOfIntegers L) = 1)
    (hint : 𝔓.asIdeal.inertiaDeg (NumberField.RingOfIntegers L) = 2)
    (a : Lˣ) (ha : 𝔭.valuation L (a : L) = 1) :
    ∃ s : (𝔓.adicCompletion K)ˣ,
      ((s : 𝔓.adicCompletion K)) ^ 2
        = algebraMap K (𝔓.adicCompletion K) (algebraMap L K (a : L)) := by
  classical
  -- `a` is a unit of the `𝔭`-adic integers of `L`
  have hval_a : Valued.v (R := 𝔭.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
      ((a : L) : 𝔭.adicCompletion L) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
      (R := NumberField.RingOfIntegers L) (K := L) 𝔭 (a : L)]
    exact ha
  have hmem_a : ((a : L) : 𝔭.adicCompletion L) ∈ 𝔭.adicCompletionIntegers L :=
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
      (NumberField.RingOfIntegers L) L 𝔭).mpr (le_of_eq hval_a)
  let b : 𝔭.adicCompletionIntegers L := ⟨((a : L) : 𝔭.adicCompletion L), hmem_a⟩
  have hbval : Valued.v (R := 𝔭.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
      (b : 𝔭.adicCompletion L) = 1 := hval_a
  have hunitb : IsUnit b :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
      (R := NumberField.RingOfIntegers L) (K := L) (v := 𝔭) (a := b)).mpr hbval
  let bU : (𝔭.adicCompletionIntegers L)ˣ := hunitb.unit
  have hbU : (bU : 𝔭.adicCompletionIntegers L) = b := IsUnit.unit_spec hunitb
  -- the corresponding unit of the `𝔓`-adic integers of `K`
  let u : (𝔓.adicCompletionIntegers K)ˣ :=
    Units.map (Commons.NumberTheory.NumberField.Completion.intCompletionMap 𝔭 𝔓 hLies).toMonoidHom bU
  -- its residue is a square
  have hsq : IsSquare ((IsLocalRing.residue (𝔓.adicCompletionIntegers K))
      (u : 𝔓.adicCompletionIntegers K)) :=
    isSquare_residue_intCompletionMap_of_inertiaDeg_two 𝔭 𝔓 hLies h2 hint bU
  -- Hensel: lift the square root of the residue
  have h2K : IsUnit (2 : 𝔓.adicCompletionIntegers K) :=
    isUnit_two_adicCompletionIntegers_of_liesOver 𝔭 𝔓 hLies h2
  obtain ⟨c, hc⟩ := exists_unit_sq_of_residue_isSquare_adicCompletion 𝔓 h2K u hsq
  refine ⟨c, ?_⟩
  -- identify the square with the image of `a`
  have hu1 : ((u : 𝔓.adicCompletionIntegers K) : 𝔓.adicCompletion K) =
      (Commons.RingTheory.Henselian.adicCompletionMap 𝔭 𝔓 hLies)
        ((a : L) : 𝔭.adicCompletion L) := by
    rw [show (u : 𝔓.adicCompletionIntegers K) =
        Commons.NumberTheory.NumberField.Completion.intCompletionMap 𝔭 𝔓 hLies
          (bU : 𝔭.adicCompletionIntegers L) from Units.coe_map _ _,
      Commons.NumberTheory.NumberField.Completion.intCompletionMap_coe]
    rw [hbU]
  have hu2 : (Commons.RingTheory.Henselian.adicCompletionMap 𝔭 𝔓 hLies)
      ((a : L) : 𝔭.adicCompletion L) =
      algebraMap K (𝔓.adicCompletion K) (algebraMap L K (a : L)) := by
    rw [Commons.RingTheory.Henselian.adicCompletionMap_apply 𝔭 𝔓 hLies (a : L)]
    rfl
  rw [hc]
  show ((u : 𝔓.adicCompletionIntegers K) : 𝔓.adicCompletion K) =
    algebraMap K (𝔓.adicCompletion K) (algebraMap L K (a : L))
  rw [hu1, hu2]

end Work.SSGRoute.ZConstruction
