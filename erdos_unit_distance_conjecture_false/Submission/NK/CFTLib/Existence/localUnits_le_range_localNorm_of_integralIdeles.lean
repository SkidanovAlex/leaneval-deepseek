import Mathlib
import Submission.NK.GlobalCFT.Place
import Submission.NK.CFTLib.Existence.localNormImage_of_forall_ne
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFT.IdeleClassGroup
import Submission.NK.GlobalCFT.NormFunctorial
import Submission.NK.GlobalCFTdeep.NormIndex.localNorm_finiteIndex_archimedean
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE_le_normImage
import Submission.NK.CFTLib.Existence.localNormUnits_of_fiber_prod
import Submission.NK.CFTLib.Existence.ramificationIdx_eq_one_or_eq_prime_of_finrank_eq_prime

open scoped NumberField RestrictedProduct NumberField.LiesOver
open NumberField IsDedekindDomain

namespace NK.CFTLib.Existence

open NK.GlobalCFT

/-!
# Local units are local norms, from the global conditions

Let `L / K` be a finite Galois extension of number fields of prime degree `p`, let
`hgap` be the "Hasse principle with one exceptional place" for the norm group of `L / K`, and let
`hray` say that the norm class subgroup `N_{L/K} C_L` contains the image of the integral idèles
`𝕀_K⁰`.  Then

* at every finite place `q | Q`, every local unit of `K_Q` is the norm of a local unit of `L_q`;
* at every infinite place, the local norm `L_w^× → K_v^×` is surjective.

The proof of the finite part: for `u` a local unit at `Q` the single-place idèle
`a = u` at `Q`, `1` elsewhere, is integral, so by `hray` it is a principal idèle times an idèle
norm, `a = (c) · N(y)`.  At every place `v ≠ Q` we have `(c)_v = N(y^{-1})_v`, so `c` is a local
norm away from the single place `Q`; by `hgap`, `c = N(z)` is a global norm and hence
`a = N(zy)` is an idèle norm.  Reading the `Q`-component,
`u = ∏_{q | Q} N_{L_{q}/K_Q}(x_{q})`; the local extraction from this product is
`NK.CFTLib.Existence.localNormUnits_of_fiber_prod`.

The proof of the archimedean part: at a complex place `v` (or a real place covered by real
places) the local extension is trivial and the norm is an isomorphism.  If `v` is real but is
covered by complex `w`, then *all* places of `L` above `v` are complex (the Galois group acts
transitively on them), so the local norm at `v` is a product of norms `z ↦ |z|²` and is
therefore non-negative on `K_v = ℝ`.  Applying the finite-place argument at the single idele
`-1` at `v` exhibits `-1` as such a product, a contradiction; the hypotheses are inconsistent and
the claim holds vacuously.
-/

/-- **The decomposition of an integral idèle attached to `hray`**: an idèle which is a local unit at
every finite place is a principal idèle times an idèle norm. -/
theorem exists_principalIdele_mul_mem_normImage_of_mem_integralIdeles
    {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (hray : (Idele.integralIdeles K).map (IdeleClassGroup.mk K) ≤ Idele.normClassSubgroup K L)
    (a : Idele K) (ha : a ∈ Idele.integralIdeles K) :
    ∃ c : Kˣ, ∃ n ∈ Idele.normImage K L, a = Idele.principalIdele K c * n := by
  have h1 : IdeleClassGroup.mk K a ∈ Idele.normClassSubgroup K L := hray ⟨a, ha, rfl⟩
  rw [Idele.normClassSubgroup] at h1
  obtain ⟨n, hn, hmn⟩ := Subgroup.mem_map.mp h1
  rw [IdeleClassGroup.mk_eq_mk_iff] at hmn
  rw [Idele.mem_principalSubgroup] at hmn
  obtain ⟨c, hc⟩ := hmn
  exact ⟨c, n, hn, by rw [hc]; simp [mul_comm, mul_left_comm]⟩

/-- **The "one exceptional place" gap `hgap` removes the principal factor**: an integral idèle
which is `1` at every place different from `v₀` is an idèle norm.

Indeed, writing `a = (c) · N(y)`, the principal idèle `(c)` agrees with `N(y^{-1})` at every place
`v ≠ v₀`, so `c` is a local norm away from the single place `v₀` and hence a global norm by
`hgap`. -/
theorem mem_normImage_of_eq_one_off
    {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (hray : (Idele.integralIdeles K).map (IdeleClassGroup.mk K) ≤ Idele.normClassSubgroup K L)
    (hgap : ∀ {x : Kˣ} {v₀ : Place K},
      (∀ v : Place K, v ≠ v₀ → ∃ y : Idele L,
        Idele.principalIdele K x v = Idele.normIdeleFun K L y v) →
      Idele.principalIdele K x ∈ Idele.normImage K L)
    {a : Idele K} (ha : a ∈ Idele.integralIdeles K) {v₀ : Place K}
    (h1 : ∀ v, v ≠ v₀ → a v = 1) : a ∈ Idele.normImage K L := by
  obtain ⟨c, n, hn, haeq⟩ := exists_principalIdele_mul_mem_normImage_of_mem_integralIdeles hray a ha
  obtain ⟨y, hy⟩ := Idele.mem_normImage.mp hn
  have hloc : ∀ v : Place K, v ≠ v₀ → ∃ y' : Idele L,
      Idele.principalIdele K c v = Idele.normIdeleFun K L y' v := by
    intro v hv
    refine ⟨y⁻¹, ?_⟩
    have h2 : (1 : (Place.localField K v)ˣ) =
        Idele.principalIdele K c v * Idele.normIdeleFun K L y v := by
      have h3 := congrArg (fun z : Idele K => z v) haeq
      rw [Idele.mul_apply, hy v] at h3
      rw [← h3, h1 v hv]
    rw [Idele.normIdeleFun_inv_apply, eq_inv_iff_mul_eq_one]
    exact h2.symm
  have hpc : Idele.principalIdele K c ∈ Idele.normImage K L := hgap hloc
  obtain ⟨z, hz⟩ := Idele.mem_normImage.mp hpc
  refine Idele.mem_normImage.mpr ⟨z * y, fun v => ?_⟩
  have h4 := congrArg (fun z : Idele K => z v) haeq
  rw [Idele.mul_apply] at h4
  rw [h4, hz v, hy v]
  exact (Norm.globalCFT_normIdeleFun_mul z y v).symm

/-- If the infinite place `v` is real and every infinite place of `L` above it is complex, then
the idèle norm at `v` is non-negative as a real number: each local factor is a complex norm square
`z ↦ |z|²`. -/
theorem normIdeleFun_ofInfinite_nonneg_of_isReal_of_forall_isComplex
    {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    {v : NumberField.InfinitePlace K} (hvR : v.IsReal)
    (hC : ∀ w : NumberField.InfinitePlace L, w.LiesOver v → w.IsComplex)
    (x : Idele L) :
    0 ≤ (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hvR)
        (((Idele.normIdeleFun K L x (Place.ofInfinite v) : v.Completionˣ) : v.Completion)) := by
  rw [Idele.normIdeleFun_ofInfinite, Units.coe_prod, map_prod]
  refine Finset.prod_nonneg (fun w' _ => ?_)
  have hwl : (w'.1 : NumberField.InfinitePlace L).LiesOver v := (Place.mem_fiberInfinite).mp w'.2
  haveI := hwl
  rw [show Place.localNormInfinite w'.1 v =
    Units.map (Algebra.norm v.Completion : w'.1.Completion →* v.Completion) from rfl]
  simp only [Units.coe_map]
  rw [NK.GlobalCFTdeep.NormIndex.localNormInfinite_norm_eq_real_complex hvR (hC w'.1 hwl)
    ((x (Place.ofInfinite w'.1)) : w'.1.Completion)]
  exact Complex.normSq_nonneg _

/-- If `w` is a complex infinite place of `L` above the infinite place `v` of `K` and `L / K` is
Galois, then *every* infinite place of `L` above `v` is complex: the Galois group acts transitively
on the places above `v`, and complexness is invariant under the Galois action. -/
theorem isComplex_of_liesOver_of_isComplex
    {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] {v : NumberField.InfinitePlace K} {w : NumberField.InfinitePlace L}
    [w.LiesOver v] (hwC : w.IsComplex) :
    ∀ w' : NumberField.InfinitePlace L, w'.LiesOver v → w'.IsComplex := by
  intro w' hw'
  haveI hw'L := hw'
  have hcomap : w.comap (algebraMap K L) = w'.comap (algebraMap K L) := by
    rw [NumberField.InfinitePlace.LiesOver.comap_eq w v,
      NumberField.InfinitePlace.LiesOver.comap_eq w' v]
  obtain ⟨σ, hσ⟩ :=
    MulAction.mem_orbit_iff.mp (NumberField.InfinitePlace.mem_orbit_iff.mpr hcomap)
  rw [← hσ]
  exact NumberField.InfinitePlace.isComplex_smul_iff.mpr hwC

/-- **A real place of `K` cannot be covered by complex places of `L`** under the hypotheses
`hray` and `hgap`: the single idèle `-1` at `v` is an idèle norm, but the norm at `v` is then a
non-negative real number. -/
theorem false_of_isReal_of_isComplex
    {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hgap : ∀ {x : Kˣ} {v₀ : Place K},
      (∀ v : Place K, v ≠ v₀ → ∃ y : Idele L,
        Idele.principalIdele K x v = Idele.normIdeleFun K L y v) →
      Idele.principalIdele K x ∈ Idele.normImage K L)
    (hray : (Idele.integralIdeles K).map (IdeleClassGroup.mk K) ≤ Idele.normClassSubgroup K L)
    (v : NumberField.InfinitePlace K) (w : NumberField.InfinitePlace L) [w.LiesOver v]
    (hvR : v.IsReal) (hwC : w.IsComplex) : False := by
  classical
  have hallC := isComplex_of_liesOver_of_isComplex (K := K) (L := L) (v := v) (w := w) hwC
  set u₀ : v.Completionˣ :=
    Units.map (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hvR).symm.toMulEquiv.toMonoidHom
      (Units.mk0 (-1 : ℝ) (by norm_num)) with hu₀
  set a : Idele K :=
    NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele (Place.ofInfinite v) u₀ with ha_def
  have ha_int : a ∈ Idele.integralIdeles K := by
    intro v' hv'
    obtain ⟨Q', rfl⟩ := Place.isFinite_iff.mp hv'
    rw [ha_def, NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele_apply_of_ne
      (w := Place.ofInfinite v) (w' := Place.ofFinite Q') (u := u₀) (by simp)]
    exact Subgroup.one_mem _
  have ha_off : ∀ v', v' ≠ Place.ofInfinite v → a v' = 1 := by
    intro v' hv'
    cases v' with
    | inl w' =>
        rw [ha_def, NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele_apply_of_ne
          (w := Place.ofInfinite v) (w' := Place.ofInfinite w') (u := u₀) hv']
    | inr Q' =>
        rw [ha_def, NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele_apply_of_ne
          (w := Place.ofInfinite v) (w' := Place.ofFinite Q') (u := u₀) (by simpa using hv')]
  obtain ⟨x, hx⟩ := Idele.mem_normImage.mp (mem_normImage_of_eq_one_off hray hgap ha_int ha_off)
  have hval : u₀ = Idele.normIdeleFun K L x (Place.ofInfinite v) := by
    have h := hx (Place.ofInfinite v)
    rw [ha_def, NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele_apply_self] at h
    exact h
  have hneg : (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hvR)
      (u₀ : v.Completion) = -1 := by
    rw [hu₀]
    simp
  have hpos : (0 : ℝ) ≤ (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hvR)
      ((Idele.normIdeleFun K L x (Place.ofInfinite v) : v.Completionˣ) : v.Completion) :=
    normIdeleFun_ofInfinite_nonneg_of_isReal_of_forall_isComplex hvR hallC x
  rw [← hval, hneg] at hpos
  norm_num at hpos

theorem localUnits_le_range_localNorm_of_integralIdeles
    {K : Type} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = p)
    (hgap : ∀ {x : Kˣ} {v₀ : NK.GlobalCFT.Place K},
      (∀ v : NK.GlobalCFT.Place K, v ≠ v₀ → ∃ y : NK.GlobalCFT.Idele L,
        NK.GlobalCFT.Idele.principalIdele K x v = NK.GlobalCFT.Idele.normIdeleFun K L y v) →
      NK.GlobalCFT.Idele.principalIdele K x ∈ NK.GlobalCFT.Idele.normImage K L)
    (hray : (NK.GlobalCFT.Idele.integralIdeles K).map (NK.GlobalCFT.IdeleClassGroup.mk K) ≤
      NK.GlobalCFT.Idele.normClassSubgroup K L) :
    (∀ (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
       (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
       (hq : q.asIdeal.LiesOver Q.asIdeal),
        ∀ u ∈ NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite Q),
          ∃ u' ∈ NK.GlobalCFT.Place.localUnits L (NK.GlobalCFT.Place.ofFinite q),
            NK.GlobalCFT.Place.localNormFinite q Q hq u' = u) ∧
    (∀ (v : NumberField.InfinitePlace K) (w : NumberField.InfinitePlace L) [w.LiesOver v]
       (u : v.Completionˣ), ∃ u' : w.Completionˣ,
        NK.GlobalCFT.Place.localNormInfinite w v u' = u) := by
  classical
  constructor
  · -- finite places
    intro Q q hq u hu
    set a : Idele K :=
      NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele (Place.ofFinite Q) u with ha_def
    have ha_int : a ∈ Idele.integralIdeles K := by
      intro v hv
      obtain ⟨Q', rfl⟩ := Place.isFinite_iff.mp hv
      by_cases h : Q' = Q
      · subst h
        rw [ha_def, NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele_apply_self]
        exact hu
      · rw [ha_def, NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele_apply_of_ne
          (w := Place.ofFinite Q) (w' := Place.ofFinite Q') (u := u) (by simpa using h)]
        exact Subgroup.one_mem _
    have ha_off : ∀ v, v ≠ Place.ofFinite Q → a v = 1 := by
      intro v hv
      cases v with
      | inl w' =>
          rw [ha_def, NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele_apply_of_ne
            (w := Place.ofFinite Q) (w' := Place.ofInfinite w') (u := u) (by simpa using hv)]
      | inr Q' =>
          rw [ha_def, NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele_apply_of_ne
            (w := Place.ofFinite Q) (w' := Place.ofFinite Q') (u := u) hv]
    obtain ⟨x, hx⟩ :=
      Idele.mem_normImage.mp (mem_normImage_of_eq_one_off hray hgap ha_int ha_off)
    have hprod : u = ∏ q' ∈ (Place.primesOverFinite Q).attach,
        (Place.localNormFinite (q' : HeightOneSpectrum (𝓞 L)) Q
          ((Place.mem_primesOverFinite (K := K) (L := L) (Q := Q) (q := q')).mp q'.2))
          (x (Place.ofFinite q'.1)) := by
      have h := hx (Place.ofFinite Q)
      rw [ha_def, NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele_apply_self,
        Idele.normIdeleFun_ofFinite] at h
      exact h
    exact localNormUnits_of_fiber_prod (Fact.out) hdeg Q q hq u hu x hprod
  · -- infinite places
    intro v w hwv u
    haveI hwl : w.LiesOver v := hwv
    rcases v.isReal_or_isComplex with hvR | hvC
    · rcases w.isReal_or_isComplex with hwR | hwC
      · have htop := NK.GlobalCFTdeep.NormIndex.localNormInfinite_range_eq_top_of_real_real
          (K := K) (L := L) (v := v) (w := w) hvR hwR
        have hmem : u ∈ (Place.localNormInfinite w v).range := by
          rw [show Place.localNormInfinite w v =
            Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion) from rfl, htop]
          exact Subgroup.mem_top u
        exact MonoidHom.mem_range.mp hmem
      · exact (false_of_isReal_of_isComplex hgap hray v w hvR hwC).elim
    · have hwC : w.IsComplex :=
        NumberField.InfinitePlace.LiesOver.isComplex_of_isComplex_under w hvC
      have htop := NK.GlobalCFTdeep.NormIndex.localNormInfinite_range_eq_top_of_complex_complex
        (K := K) (L := L) (v := v) (w := w) hvC hwC
      have hmem : u ∈ (Place.localNormInfinite w v).range := by
        rw [show Place.localNormInfinite w v =
          Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion) from rfl, htop]
        exact Subgroup.mem_top u
      exact MonoidHom.mem_range.mp hmem

end NK.CFTLib.Existence
