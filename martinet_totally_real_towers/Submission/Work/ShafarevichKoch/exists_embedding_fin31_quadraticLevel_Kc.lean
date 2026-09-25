import Mathlib
import Submission.Work.ShafarevichKoch.GeneratorRank
import Submission.Work.ShafarevichKoch.isGalois_of_finrank_eq_two
import Submission.Work.ClassFieldTower.WitnessField
import Submission.Work.ClassFieldTower.hasGenusLevel_witness
import Submission.Work.ClassFieldTower.ProTwoGenus
import Submission.Work.ClassFieldTower.exists_fiveUnramifiedQuadratics_of_unramified_exponentTwo

/-!
# `Work.ShafarevichKoch.exists_embedding_fin31_quadraticLevel_Kc`

The genus field of `Kc = ℚ(√-30030)` is the multiquadratic field
`wM = ℚ(√8, √-3, √5, √-7, √-11, √13)`, a finite unramified Galois extension of `Kc` of degree
`2^5 = 32` whose Galois group has exponent `2` (`Work.ClassFieldTower.hasGenusLevel_witness`).
By the universal property of the maximal unramified pro-`2` extension `Kc_∅ = M.K`, this field
embeds into `M.K`; hence `M.K` contains an intermediate field `L` with
`Gal(L/Kc) ≃ (ℤ/2)^5`.

An exponent-`2` group of order `32` has exactly `2^5 - 1 = 31` subgroups of index `2` (the
kernels of the nontrivial linear functionals), and by the Galois correspondence each of them cuts
out a subextension of `L/Kc` of degree `2`.  These `31` quadratic levels are pairwise distinct,
which is the statement proved here: there are at least `31` unramified quadratic levels of
`Kc_∅/Kc`.  (The companion upper bound is `card_unramifiedQuadraticLevels_le_Kc_thirtytwo`.)
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

/-! ## The explicit linear functionals on `(ℤ/2)^5` -/

/-- The `𝔽₂`-linear functional `x ↦ ∑ i, v i * x i` on `(ℤ/2)^5`. -/
private def dot31 (v : Fin 5 → ZMod 2) : (Fin 5 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  ∑ i : Fin 5, v i • LinearMap.proj i

private theorem dot31_apply (v x : Fin 5 → ZMod 2) : dot31 v x = ∑ i, v i * x i := by
  simp [dot31, LinearMap.proj, Finset.sum_apply]

private theorem dot31_single (v : Fin 5 → ZMod 2) (i : Fin 5) (b : ZMod 2) :
    dot31 v (Pi.single i b) = v i * b := by
  rw [dot31_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; rw [Pi.single_eq_of_ne hj, mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- The same functional, as a homomorphism of multiplicative groups. -/
private def chi31 (v : Fin 5 → ZMod 2) :
    Multiplicative (Fin 5 → ZMod 2) →* Multiplicative (ZMod 2) :=
  AddMonoidHom.toMultiplicative (dot31 v).toAddMonoidHom

private theorem chi31_ofAdd (v x : Fin 5 → ZMod 2) :
    chi31 v (Multiplicative.ofAdd x) = Multiplicative.ofAdd (dot31 v x) := by
  simp [chi31]

private theorem zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

private theorem ofAdd_eq_one_iff (a : ZMod 2) : Multiplicative.ofAdd a = 1 ↔ a = 0 := by
  constructor
  · intro h
    have := congrArg Multiplicative.toAdd h
    simpa using this
  · intro h; rw [h]; rfl

private theorem chi31_surjective (v : Fin 5 → ZMod 2) (hv : v ≠ 0) :
    Function.Surjective (chi31 v) := by
  have hex : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  obtain ⟨i, hi⟩ := hex
  have hi1 : v i = 1 := by
    rcases zmod2_eq_zero_or_one (v i) with h | h
    · exact absurd h hi
    · exact h
  intro y
  refine ⟨Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd y)), ?_⟩
  rw [chi31_ofAdd, dot31_single, hi1, one_mul]
  simp

/-- The kernel of a nonzero functional on `(ℤ/2)^5` has `16` elements. -/
private theorem chi31_ker_card (v : Fin 5 → ZMod 2) (hv : v ≠ 0) :
    Nat.card ↥((chi31 v).ker) = 16 := by
  have hrange : (chi31 v).range = ⊤ := MonoidHom.range_eq_top.mpr (chi31_surjective v hv)
  have hidx : (chi31 v).ker.index = 2 := by
    rw [Subgroup.index_ker, hrange, Subgroup.card_top, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card]
  have hcard := Subgroup.card_mul_index (chi31 v).ker
  rw [hidx] at hcard
  have h32 : Nat.card (Multiplicative (Fin 5 → ZMod 2)) = 32 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun,
      Fintype.card_fin, ZMod.card]
    norm_num
  rw [h32] at hcard
  omega

/-- Distinct nonzero functionals on `(ℤ/2)^5` have distinct kernels. -/
private theorem chi31_ker_injective :
    Function.Injective (fun v : Fin 5 → ZMod 2 => (chi31 v).ker) := by
  intro v w hvw
  have hker : (chi31 v).ker = (chi31 w).ker := hvw
  funext i
  have hiff0 : dot31 v (Pi.single i (1 : ZMod 2)) = 0 ↔
      dot31 w (Pi.single i (1 : ZMod 2)) = 0 := by
    have hmem : Multiplicative.ofAdd (Pi.single i (1 : ZMod 2)) ∈ (chi31 v).ker ↔
        Multiplicative.ofAdd (Pi.single i (1 : ZMod 2)) ∈ (chi31 w).ker := by rw [hker]
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, chi31_ofAdd, chi31_ofAdd,
      ofAdd_eq_one_iff, ofAdd_eq_one_iff] at hmem
    exact hmem
  have hiff : v i = 0 ↔ w i = 0 := by
    simpa only [dot31_single, mul_one] using hiff0
  rcases zmod2_eq_zero_or_one (w i) with hw | hw
  · rw [hiff.mpr hw, hw]
  · have hvne : v i ≠ 0 := fun h => by
      have h0 : w i = 0 := hiff.mp h
      rw [hw] at h0
      exact one_ne_zero h0
    rcases zmod2_eq_zero_or_one (v i) with hv | hv
    · exact absurd hv hvne
    · rw [hv, hw]

/-! ## The `31` quadratic levels of `Kc_∅` -/

theorem exists_embedding_fin31_quadraticLevel_Kc
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2) :
    Nonempty (Fin 31 ↪ Work.ShafarevichKoch.QuadraticLevel Work.ClassFieldTower.Kc M) := by
  classical
  obtain ⟨L₀, iL, iNL, iAL, hfd, hgal, hdiff, hexp, hcard⟩ := hasGenusLevel_witness
  letI : Field L₀ := iL
  letI : NumberField L₀ := iNL
  letI : Algebra Kc L₀ := iAL
  letI : FiniteDimensional Kc L₀ := hfd
  letI : IsGalois Kc L₀ := hgal
  -- (1) `Gal(L₀/Kc) ≃* (ℤ/2)^5`
  obtain ⟨e⟩ := nonempty_mulEquiv_galoisGroup_five (F := Kc) L₀ hexp hcard
  -- (2) `L₀` embeds into the maximal unramified pro-`2` extension `Kc_∅ = M.K`
  have hpro : IsPGroup 2 (L₀ ≃ₐ[Kc] L₀) := fun σ => ⟨1, by rw [pow_one]; exact hexp σ⟩
  obtain ⟨φ, -⟩ := M.universal L₀ hpro hdiff
  -- (3) `[L₀ : Kc] = 32`
  have hfr32 : Module.finrank Kc L₀ = 32 := by
    rw [← IsGalois.card_aut_eq_finrank Kc L₀, hcard]
    norm_num
  -- (4) the quadratic level attached to a nonzero functional
  let lv : (Fin 5 → ZMod 2) → IntermediateField Kc L₀ :=
    fun v => IntermediateField.fixedField ((chi31 v).ker.comap e)
  have lv_finrank : ∀ (v : Fin 5 → ZMod 2) (hv : v ≠ 0),
      Module.finrank Kc ↥(lv v) = 2 := by
    intro v hv
    have h1 : Module.finrank ↥(lv v) L₀ = 16 := by
      rw [show lv v = IntermediateField.fixedField ((chi31 v).ker.comap e) from rfl,
        IntermediateField.finrank_fixedField_eq_card,
        Subgroup.comap_equiv_eq_map_symm e (chi31 v).ker,
        Subgroup.card_map_of_injective e.symm.injective]
      exact chi31_ker_card v hv
    have htower : Module.finrank Kc ↥(lv v) * Module.finrank ↥(lv v) L₀ = Module.finrank Kc L₀ :=
      Module.finrank_mul_finrank Kc ↥(lv v) L₀
    rw [h1, hfr32] at htower
    omega
  have map_finrank : ∀ (v : Fin 5 → ZMod 2) (hv : v ≠ 0),
      Module.finrank Kc ↥(IntermediateField.map φ (lv v)) = 2 := by
    intro v hv
    rw [← LinearEquiv.finrank_eq (IntermediateField.equivMap (lv v) φ).toLinearEquiv]
    exact lv_finrank v hv
  have lv_injective : Function.Injective lv := by
    intro v w hvw
    have h := congrArg (fun L : IntermediateField Kc L₀ => IntermediateField.fixingSubgroup L) hvw
    simp only [lv, IntermediateField.fixingSubgroup_fixedField] at h
    refine chi31_ker_injective (Subgroup.comap_injective ?_ h)
    exact MulEquiv.surjective e
  -- (5) the `31` nonzero vectors
  have hcard31 : Fintype.card {v : Fin 5 → ZMod 2 // v ≠ 0} = 31 := by
    rw [Fintype.card_subtype_compl (fun v : Fin 5 → ZMod 2 => v = 0)]
    rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]
    have h1 : Fintype.card {v : Fin 5 → ZMod 2 // v = 0} = 1 := by
      rw [Fintype.card_eq_one_iff]
      exact ⟨⟨0, rfl⟩, fun x => Subtype.ext x.2⟩
    rw [h1]
    norm_num
  let idx : Fin 31 ≃ {v : Fin 5 → ZMod 2 // v ≠ 0} := (Fintype.equivFinOfCardEq hcard31).symm
  refine ⟨⟨fun i => ⟨IntermediateField.map φ (lv (idx i).1),
      map_finrank (idx i).1 (idx i).2⟩, ?_⟩⟩
  intro i j hij
  have hval : IntermediateField.map φ (lv (idx i).1) =
      IntermediateField.map φ (lv (idx j).1) := congrArg Subtype.val hij
  have hlv : lv (idx i).1 = lv (idx j).1 := IntermediateField.map_injective φ hval
  have hvec : (idx i).1 = (idx j).1 := lv_injective hlv
  exact idx.injective (Subtype.ext hvec)

end Work.ShafarevichKoch
