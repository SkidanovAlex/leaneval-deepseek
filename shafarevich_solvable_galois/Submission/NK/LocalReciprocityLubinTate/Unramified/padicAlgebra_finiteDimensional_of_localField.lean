import Mathlib.Computability.Reduce
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Submission.NK.LocalReciprocityLubinTate.Unramified.exists_prime_vlt_one
import Submission.NK.LocalReciprocityLubinTate.Unramified.ratCast_veq_pow_padicValRat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A characteristic-zero nonarchimedean local field is a finite extension of `ℚ_[p]`

Let `F` be a field of characteristic zero carrying a valuative relation (an equivalence class of
valuations) whose topology is the valuation topology, which is locally compact and non-discrete
(`IsNonarchimedeanLocalField`).  Then `F` is a *finite* extension of the `p`-adic field `ℚ_[p]`,
where `p` is the residue characteristic of `F`.

This is the standard structure theorem for characteristic-zero local fields (Serre, *Local Fields*,
Ch. II §4; Neukirch, *Algebraic Number Theory*, Ch. II §5).  The argument is:

* `F` is Hausdorff for the valuation topology;
* some rational prime `p` has `(p : F) <ᵥ 1` (the residue characteristic, provided by
  `NK.LocalReciprocityLubinTate.Unramified.exists_prime_vlt_one`);
* the valuation of `F` restricted to `ℚ ⊆ F` is the `p`-adic valuation, in the form
  `(q : F) =ᵥ (p : F) ^ (padicValRat p q)` for `q : ℚ` with `padicValRat p q ≥ 0`
  (`NK.LocalReciprocityLubinTate.Unramified.ratCast_veq_pow_padicValRat`);
* consequently `algebraMap ℚ F` is uniformly continuous for the `p`-adic uniformity on `ℚ`, and
  since `ℚ_[p]` is the completion of `ℚ`, it extends to a ring homomorphism `ℚ_[p] →+* F`
  (`IsDenseInducing.extendRingHom`);
* the resulting `ℚ_[p]`-vector space structure on `F` has continuous scalar multiplication
  (because the extension is continuous and `F` is a topological ring), and `F` is locally compact,
  so `F` is finite dimensional over `ℚ_[p]` by Riesz's theorem
  (`FiniteDimensional.of_locallyCompactSpace`).

## Main result

* `padicAlgebra_finiteDimensional_of_localField`
-/

namespace NK.LocalReciprocityLubinTate.Unramified

open Filter ValuativeRel
open scoped Topology ValuativeRel

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

universe u

noncomputable section

/-! ## Hausdorffness of a nonarchimedean local field -/

/-- A nonarchimedean local field is Hausdorff for the topology induced by its valuation: for `x ≠ 0`
the set `{k | v k < v x}` is a neighbourhood of `0` avoiding `x`. -/
lemma padicAlg_t2Space (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : T2Space F := by
  refine IsTopologicalAddGroup.t2Space_of_zero_sep fun x hx ↦ ?_
  have hx0 : valuation F x ≠ 0 := fun h0 ↦
    hx ((ValuativeRel.vle_zero_iff).mp ((ValuativeRel.valuation_eq_zero_iff).mp h0))
  refine ⟨{k : F | valuation F k < valuation F x}, ?_, ?_⟩
  · rw [IsValuativeTopology.mem_nhds_zero_iff]
    exact ⟨Units.mk0 _ hx0, fun y hy ↦ by simpa using hy⟩
  · simp only [Set.mem_ofPred_eq, lt_self_iff_false, not_false_eq_true]

/-! ## Powers of an element of valuation `< 1` are cofinal to `0` -/

/-- If `x <ᵥ 1` and `y ≠ 0` in a nonarchimedean local field, then `x ^ N <ᵥ y` for some `N`.
The proof uses that the value group of a nonarchimedean local field has rank one, hence embeds
strictly monotonically into `ℝ≥0`, where the corresponding statement is
`exists_pow_lt_of_lt_one`. -/
lemma padicAlg_exists_pow_vlt_one (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {x y : F} (hx : x <ᵥ 1) (hy : y ≠ 0) :
    ∃ N : ℕ, x ^ N <ᵥ y := by
  let S : ValuativeRel.RankLeOneStruct F := (ValuativeRel.IsRankLeOne.nonempty (R := F)).some
  have hmono : StrictMono S.emb := S.strictMono
  have hle : ∀ a b : ValueGroupWithZero F, a ≤ b → S.emb a ≤ S.emb b := by
    intro a b hab
    rcases eq_or_lt_of_le hab with h | h
    · simp [h]
    · exact (hmono h).le
  have hrefl : ∀ a b : ValueGroupWithZero F, S.emb a < S.emb b → a < b := by
    intro a b hab
    rcases lt_trichotomy a b with h | h | h
    · exact h
    · exact absurd hab (by simp [h])
    · exact absurd (hle b a h.le) (not_le_of_gt hab)
  have hvx : valuation F x < 1 := by
    simpa using (Valuation.vlt_iff_lt (v := valuation F)).mp hx
  have hembx : S.emb (valuation F x) < 1 := by simpa using hmono hvx
  have hvy : valuation F y ≠ 0 := fun h ↦
    hy ((ValuativeRel.vle_zero_iff).mp ((ValuativeRel.valuation_eq_zero_iff (R := F)).mp h))
  have hemby : 0 < S.emb (valuation F y) := by
    refine lt_of_le_of_ne bot_le (fun h ↦ hvy ?_)
    exact hmono.injective (by rw [← h, map_zero])
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hemby hembx
  refine ⟨N, ?_⟩
  rw [Valuation.vlt_iff_lt (v := valuation F)]
  refine hrefl _ _ ?_
  rw [map_pow (valuation F) x N, map_pow]
  exact hN

/-! ## The `p`-adic norm on `ℚ` versus the valuation of `F` -/

/-- **The comparison of the `p`-adic norm on `ℚ` with the valuation of `F`.**  For every `y ≠ 0` in
`F` there is `ε > 0` such that every rational with `padicNorm p` less than `ε` has image in `F` of
valuation `<ᵥ y`. -/
lemma padicAlg_exists_padicNorm_lt_imp_vlt (F : Type u) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] {p : ℕ} (hp : Nat.Prime p)
    (hlt : (p : F) <ᵥ 1) {y : F} (hy : y ≠ 0) :
    ∃ ε : ℚ, 0 < ε ∧ ∀ q : ℚ, padicNorm p q < ε → (algebraMap ℚ F q) <ᵥ y := by
  obtain ⟨N, hN⟩ := padicAlg_exists_pow_vlt_one F hlt hy
  refine ⟨(p : ℚ) ^ (-(N : ℤ)), zpow_pos (by exact_mod_cast hp.pos) _, ?_⟩
  intro q hq
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [map_zero]
    exact (ValuativeRel.zero_vlt_iff).mpr hy
  · have hval : (N : ℤ) ≤ padicValRat p q := by
      rw [padicNorm.eq_zpow_of_nonzero hq0] at hq
      rw [zpow_lt_zpow_iff_right₀ (by exact_mod_cast hp.one_lt)] at hq
      omega
    have hvle1 : (p : F) ≤ᵥ 1 := hlt.vle
    have hpow : (p : F) ^ (padicValRat p q).toNat ≤ᵥ (p : F) ^ N :=
      pow_vle_pow_of_vle_one hvle1 (by omega)
    have hveq : (algebraMap ℚ F q) =ᵥ (p : F) ^ (padicValRat p q).toNat :=
      ratCast_veq_pow_padicValRat F hp hlt hq0 (by omega)
    exact vlt_of_vle_of_vlt (vle_of_veq_of_vle hveq hpow) hN

/-! ## The main theorem -/

theorem padicAlgebra_finiteDimensional_of_localField (F : Type u) [Field F] [CharZero F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    ∃ (p : ℕ) (_ : Fact p.Prime) (_ : Algebra ℚ_[p] F), FiniteDimensional ℚ_[p] F := by
  haveI hT2 : T2Space F := padicAlg_t2Space F
  haveI hT3 : T3Space F := inferInstance
  -- the residue characteristic
  obtain ⟨p, hp, hlt⟩ := exists_prime_vlt_one F
  haveI hpFact : Fact p.Prime := ⟨hp⟩
  -- the canonical uniformities
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  haveI hComplete : CompleteSpace F := inferInstance
  -- the `p`-adic uniformity on `ℚ`, pulled back from `ℚ_[p]`
  letI : UniformSpace ℚ := UniformSpace.comap (algebraMap ℚ ℚ_[p]) inferInstance
  haveI hUAG : IsUniformAddGroup ℚ := IsUniformAddGroup.comap (algebraMap ℚ ℚ_[p])
  have hui : IsUniformInducing (algebraMap ℚ ℚ_[p]) :=
    isUniformInducing_iff_uniformSpace.mpr rfl
  have hdr : DenseRange (algebraMap ℚ ℚ_[p]) := Padic.denseRange_ratCast p
  -- `algebraMap ℚ F` is continuous at `0` for the `p`-adic topology on `ℚ`
  have hcont : ContinuousAt (algebraMap ℚ F) 0 := by
    rw [ContinuousAt, map_zero]
    have hbℚ : (𝓝 (0 : ℚ)).HasBasis (fun ε : ℝ ↦ 0 < ε)
        fun ε ↦ {q : ℚ | ‖(q : ℚ_[p])‖ < ε} := by
      have h := (Metric.nhds_basis_ball (x := (0 : ℚ_[p]))).comap (algebraMap ℚ ℚ_[p])
      simpa [Metric.mem_ball, dist_eq_norm, nhds_induced, Set.preimage] using h
    refine (hbℚ.tendsto_iff (IsValuativeTopology.hasBasis_nhds_zero F)).mpr ?_
    rintro γ -
    obtain ⟨a, b, hab⟩ :=
      ValuativeRel.exists_valuation_posSubmonoid_div_valuation_posSubmonoid_eq (R := F) γ
    set y : F := (a : F) / (b : F) with hy
    have hy_ne : y ≠ 0 := by
      rw [hy]
      exact div_ne_zero (ValuativeRel.val_posSubmonoid_ne_zero a)
        (ValuativeRel.val_posSubmonoid_ne_zero b)
    have hy_val : valuation F y = (γ : ValueGroupWithZero F) := by
      rw [hy, Valuation.map_div]
      exact hab
    obtain ⟨ε₀, hε₀pos, hε₀⟩ := padicAlg_exists_padicNorm_lt_imp_vlt F hp hlt hy_ne
    have hε₀pos' : (0 : ℝ) < (ε₀ : ℝ) := by exact_mod_cast hε₀pos
    refine ⟨(ε₀ : ℝ), hε₀pos', ?_⟩
    intro q hq
    show valuation F (algebraMap ℚ F q) < (γ : ValueGroupWithZero F)
    rw [← hy_val]
    refine (Valuation.vlt_iff_lt (v := valuation F)).mp (hε₀ q ?_)
    have hq' : ((padicNorm p q : ℚ) : ℝ) < ((ε₀ : ℚ) : ℝ) := by simpa using hq
    exact_mod_cast hq'
  have huc : UniformContinuous (algebraMap ℚ F) :=
    uniformContinuous_of_continuousAt_zero _ hcont
  -- extension to `ℚ_[p]`
  let φ : ℚ_[p] →+* F := IsDenseInducing.extendRingHom hui hdr huc
  have hφcont : Continuous (φ : ℚ_[p] → F) :=
    (uniformContinuous_uniformly_extend hui hdr huc).continuous
  letI : Algebra ℚ_[p] F := φ.toAlgebra
  haveI : ContinuousSMul ℚ_[p] F :=
    ⟨by
      rw [show (fun z : ℚ_[p] × F ↦ z.1 • z.2)
          = fun z : ℚ_[p] × F ↦ algebraMap ℚ_[p] F z.1 * z.2 from
        funext fun z ↦ Algebra.smul_def _ _]
      exact (hφcont.comp continuous_fst).mul continuous_snd⟩
  exact ⟨p, hpFact, inferInstance, FiniteDimensional.of_locallyCompactSpace ℚ_[p]⟩

end

end NK.LocalReciprocityLubinTate.Unramified
