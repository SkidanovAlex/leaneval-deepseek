import Mathlib
import Submission.Work.ShafarevichKoch.GeneratorRank
import Submission.Work.ShafarevichKoch.exists_embedding_fin31_quadraticLevel_Kc
import Submission.Work.ClassFieldTower.ProTwoGenus

/-!
# `Work.ShafarevichKoch.card_quadraticLevel_ge_of_hasGenusLevel`

The genus-theory lower bound for the number of unramified quadratic levels, in the general
form used by the Shafarevich--Koch chapter: if `F` has a **genus level**
(`Work.ClassFieldTower.HasGenusLevel F`, i.e. a finite unramified Galois extension `L/F` with
`Gal(L/F)` of exponent `2` and order `2 ^ 5`), then for **every** maximal unramified pro-`2`
extension `M = F_∅` of `F` there are at least `2 ^ 5 - 1 = 31` distinct unramified quadratic
levels `F ⊆ K ⊆ F_∅` with `[K : F] = 2`, i.e.

  `Nonempty (Fin 31 ↪ QuadraticLevel F M)`.

This is the generalisation of the concrete witness computation
`Work.ShafarevichKoch.exists_embedding_fin31_quadraticLevel_Kc` (for `F = Kc = ℚ(√-30030)`) to an
arbitrary number field `F` carrying a genus level: the argument only uses `HasGenusLevel F`, the
universal property `M.universal` of the maximal unramified pro-`2` extension and the elementary
fact that a finite group of exponent `2` and order `2 ^ 5` is `(ℤ/2)^5`.

Concretely, `L₀` embeds into `F_∅` via `φ : L₀ →ₐ[F] M.K`; the `31` nonzero `𝔽₂`-linear
functionals `χ : Gal(L₀/F) ≃* (ℤ/2)^5 → ℤ/2` have distinct kernels, each of index `2`, whose fixed
fields are quadratic over `F`; pushing them forward along `φ` gives `31` distinct quadratic levels
of `F_∅/F`.  (The companion upper bound is
`Work.ShafarevichKoch.card_unramifiedQuadraticLevels_le_classGroupTwoRank`.)
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

/-! ## The explicit `𝔽₂`-linear functionals on `(ℤ/2)^5` -/

/-- The `𝔽₂`-linear functional `x ↦ ∑ i, v i * x i` on `(ℤ/2)^5`. -/
private def dotGen (v : Fin 5 → ZMod 2) : (Fin 5 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  ∑ i : Fin 5, v i • LinearMap.proj i

private theorem dotGen_apply (v x : Fin 5 → ZMod 2) : dotGen v x = ∑ i, v i * x i := by
  simp [dotGen, LinearMap.proj, Finset.sum_apply]

private theorem dotGen_single (v : Fin 5 → ZMod 2) (i : Fin 5) (b : ZMod 2) :
    dotGen v (Pi.single i b) = v i * b := by
  rw [dotGen_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; rw [Pi.single_eq_of_ne hj, mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- The same functional, as a homomorphism of multiplicative groups. -/
private def chiGen (v : Fin 5 → ZMod 2) :
    Multiplicative (Fin 5 → ZMod 2) →* Multiplicative (ZMod 2) :=
  AddMonoidHom.toMultiplicative (dotGen v).toAddMonoidHom

private theorem chiGen_ofAdd (v x : Fin 5 → ZMod 2) :
    chiGen v (Multiplicative.ofAdd x) = Multiplicative.ofAdd (dotGen v x) := by
  simp [chiGen]

private theorem zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

private theorem ofAdd_eq_one_iff (a : ZMod 2) : Multiplicative.ofAdd a = 1 ↔ a = 0 := by
  constructor
  · intro h
    have := congrArg Multiplicative.toAdd h
    simpa using this
  · intro h; rw [h]; rfl

private theorem chiGen_surjective (v : Fin 5 → ZMod 2) (hv : v ≠ 0) :
    Function.Surjective (chiGen v) := by
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
  rw [chiGen_ofAdd, dotGen_single, hi1, one_mul]
  simp

/-- The kernel of a nonzero functional on `(ℤ/2)^5` has `16` elements. -/
private theorem chiGen_ker_card (v : Fin 5 → ZMod 2) (hv : v ≠ 0) :
    Nat.card ↥((chiGen v).ker) = 16 := by
  have hrange : (chiGen v).range = ⊤ := MonoidHom.range_eq_top.mpr (chiGen_surjective v hv)
  have hidx : (chiGen v).ker.index = 2 := by
    rw [Subgroup.index_ker, hrange, Subgroup.card_top, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card]
  have hcard := Subgroup.card_mul_index (chiGen v).ker
  rw [hidx] at hcard
  have h32 : Nat.card (Multiplicative (Fin 5 → ZMod 2)) = 32 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun,
      Fintype.card_fin, ZMod.card]
    norm_num
  rw [h32] at hcard
  omega

/-- Distinct nonzero functionals on `(ℤ/2)^5` have distinct kernels. -/
private theorem chiGen_ker_injective :
    Function.Injective (fun v : Fin 5 → ZMod 2 => (chiGen v).ker) := by
  intro v w hvw
  have hker : (chiGen v).ker = (chiGen w).ker := hvw
  funext i
  have hiff0 : dotGen v (Pi.single i (1 : ZMod 2)) = 0 ↔
      dotGen w (Pi.single i (1 : ZMod 2)) = 0 := by
    have hmem : Multiplicative.ofAdd (Pi.single i (1 : ZMod 2)) ∈ (chiGen v).ker ↔
        Multiplicative.ofAdd (Pi.single i (1 : ZMod 2)) ∈ (chiGen w).ker := by rw [hker]
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, chiGen_ofAdd, chiGen_ofAdd,
      ofAdd_eq_one_iff, ofAdd_eq_one_iff] at hmem
    exact hmem
  have hiff : v i = 0 ↔ w i = 0 := by
    simpa only [dotGen_single, mul_one] using hiff0
  rcases zmod2_eq_zero_or_one (w i) with hw | hw
  · rw [hiff.mpr hw, hw]
  · have hvne : v i ≠ 0 := fun h => by
      have h0 : w i = 0 := hiff.mp h
      rw [hw] at h0
      exact one_ne_zero h0
    rcases zmod2_eq_zero_or_one (v i) with hv | hv
    · exact absurd hv hvne
    · rw [hv, hw]

/-- **`Gal(L/F) ≃* (𝔽₂)^5` for an exponent-`2` Galois group of order `2 ^ 5`.**

Universe-polymorphic form of `Work.ClassFieldTower.nonempty_mulEquiv_galoisGroup_five` (which
fixes `F : Type`), so that it applies to a base field `F : Type*`. -/
private theorem nonempty_mulEquiv_galoisGroup_five' {F : Type*} [Field F] (L : Type)
    [Field L] [Algebra F L] [FiniteDimensional F L] (hexp : ∀ σ : L ≃ₐ[F] L, σ ^ 2 = 1)
    (hcard : Nat.card (L ≃ₐ[F] L) = 2 ^ 5) :
    Nonempty ((L ≃ₐ[F] L) ≃* Multiplicative (Fin 5 → ZMod 2)) := by
  classical
  letI : IsMulCommutative (L ≃ₐ[F] L) :=
    ⟨Std.Commutative.mk (Work.ClassFieldTower.mul_comm_of_sq_eq_one hexp)⟩
  exact
    Commons.GroupTheory.SpecificGroups.ZModProd.exists_mulEquiv_multiplicative_fin_zmod_two_of_fintype_commutative_pow_two_eq_one_card
      hexp hcard

/-- **The genus-theory lower bound, general form.**  If `F` carries a genus level
(`Work.ClassFieldTower.HasGenusLevel F`) then every maximal unramified pro-`2` extension `M` of
`F` has at least `2 ^ 5 - 1 = 31` unramified quadratic levels. -/
theorem card_quadraticLevel_ge_of_hasGenusLevel (F : Type*) [Field F] [NumberField F]
    (h : Work.ClassFieldTower.HasGenusLevel F)
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2) :
    Nonempty (Fin 31 ↪ Work.ShafarevichKoch.QuadraticLevel F M) := by
  classical
  obtain ⟨L₀, iL, iNL, iAL, hfd, hgal, hdiff, hexp, hcard⟩ := h
  letI : Field L₀ := iL
  letI : NumberField L₀ := iNL
  letI : Algebra F L₀ := iAL
  letI : FiniteDimensional F L₀ := hfd
  letI : IsGalois F L₀ := hgal
  -- (1) `Gal(L₀/F) ≃* (ℤ/2)^5`
  obtain ⟨e⟩ := nonempty_mulEquiv_galoisGroup_five' (F := F) L₀ hexp hcard
  -- (2) `L₀` embeds into the maximal unramified pro-`2` extension `F_∅ = M.K`
  have hpro : IsPGroup 2 (L₀ ≃ₐ[F] L₀) := fun σ => ⟨1, by rw [pow_one]; exact hexp σ⟩
  obtain ⟨φ, -⟩ := M.universal L₀ hpro hdiff
  -- (3) `[L₀ : F] = 32`
  have hfr32 : Module.finrank F L₀ = 32 := by
    rw [← IsGalois.card_aut_eq_finrank F L₀, hcard]
    norm_num
  -- (4) the quadratic level attached to a nonzero functional
  let lv : (Fin 5 → ZMod 2) → IntermediateField F L₀ :=
    fun v => IntermediateField.fixedField ((chiGen v).ker.comap e)
  have lv_finrank : ∀ (v : Fin 5 → ZMod 2) (hv : v ≠ 0),
      Module.finrank F ↥(lv v) = 2 := by
    intro v hv
    have h1 : Module.finrank ↥(lv v) L₀ = 16 := by
      rw [show lv v = IntermediateField.fixedField ((chiGen v).ker.comap e) from rfl,
        IntermediateField.finrank_fixedField_eq_card,
        Subgroup.comap_equiv_eq_map_symm e (chiGen v).ker,
        Subgroup.card_map_of_injective e.symm.injective]
      exact chiGen_ker_card v hv
    have htower : Module.finrank F ↥(lv v) * Module.finrank ↥(lv v) L₀ = Module.finrank F L₀ :=
      Module.finrank_mul_finrank F ↥(lv v) L₀
    rw [h1, hfr32] at htower
    omega
  have map_finrank : ∀ (v : Fin 5 → ZMod 2) (hv : v ≠ 0),
      Module.finrank F ↥(IntermediateField.map φ (lv v)) = 2 := by
    intro v hv
    rw [← LinearEquiv.finrank_eq (IntermediateField.equivMap (lv v) φ).toLinearEquiv]
    exact lv_finrank v hv
  have lv_injective : Function.Injective lv := by
    intro v w hvw
    have h := congrArg (fun L : IntermediateField F L₀ => IntermediateField.fixingSubgroup L) hvw
    simp only [lv, IntermediateField.fixingSubgroup_fixedField] at h
    refine chiGen_ker_injective (Subgroup.comap_injective ?_ h)
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
