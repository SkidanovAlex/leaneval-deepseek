import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.Work.SSGRoute.PinnedTwin.Basic
import Submission.Work.SSGRoute.PinnedTwin.exists_primes_not_conj_avoid
import Submission.Work.SSGRoute.PinnedTwin.exists_signPattern_notMem_range
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain
open scoped NumberField RestrictedProduct
open Commons.NumberTheory.NumberField.Completion (placeSmul)

namespace Work.SSGRoute.PinnedTwin

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

/-! ## Auxiliary definitions and small lemmas -/

/-- The `±1` unit of `𝓞 K` attached to a residue class `χ : ZMod 2`. -/
private def sgnU (χ : ZMod 2) : (𝓞 K)ˣ := if χ = 0 then 1 else -1

private lemma sgnU_mul_self (χ : ZMod 2) : sgnU (K := K) χ * sgnU χ = 1 := by
  unfold sgnU; split <;> simp

private lemma sgnU_inv (χ : ZMod 2) : (sgnU (K := K) χ)⁻¹ = sgnU χ := by
  rw [inv_eq_iff_mul_eq_one]; exact sgnU_mul_self χ

private lemma sgnU_coe (χ : ZMod 2) :
    ((sgnU (K := K) χ : (𝓞 K)ˣ) : 𝓞 K) = if χ = 0 then 1 else -1 := by
  unfold sgnU; split <;> simp

private lemma sgnU_mem_localUnits (χ : ZMod 2) (q : HeightOneSpectrum (𝓞 K)) :
    ((sgnU (K := K) χ : (𝓞 K)ˣ) : 𝓞 K) ∉ q.asIdeal := by
  rw [← HeightOneSpectrum.valuation_eq_one_iff_notMem (K := K) q]
  rw [sgnU_coe]; split <;> simp

/-- **A unit of `𝓞 K` moved by `ρ`.**  If `ρ ≠ 1` there is an integral element of `K` which `ρ`
does not fix. -/
private lemma exists_moved_integral (ρ : K ≃ₐ[k] K) (hρ : ρ ≠ 1) :
    ∃ y : 𝓞 K, rhoRing ρ y ≠ y := by
  by_contra hcon
  push Not at hcon
  apply hρ
  ext x
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 K) x
  rw [← hab]
  suffices h : ρ (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b)
      = algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b by
    rwa [AlgEquiv.one_apply]
  rw [map_div₀]
  have ha : ρ (algebraMap (𝓞 K) K a) = algebraMap (𝓞 K) K a := by
    have h1 := algebraMap_galRestrict_apply (𝓞 k) (K := k) (L := K) (B := 𝓞 K) ρ a
    rw [← h1]
    exact congrArg (algebraMap (𝓞 K) K) (hcon a)
  have hb' : ρ (algebraMap (𝓞 K) K b) = algebraMap (𝓞 K) K b := by
    have h1 := algebraMap_galRestrict_apply (𝓞 k) (K := k) (L := K) (B := 𝓞 K) ρ b
    rw [← h1]
    exact congrArg (algebraMap (𝓞 K) K) (hcon b)
  rw [ha, hb']

/-- Only finitely many height one primes contain a given nonzero integral element. -/
private lemma finite_setOf_mem_asIdeal {z : 𝓞 K} (hz : z ≠ 0) :
    {q : HeightOneSpectrum (𝓞 K) | z ∈ q.asIdeal}.Finite := by
  refine (Ideal.finite_factors (I := Ideal.span {z}) ?_).subset ?_
  · simpa [Ideal.span_singleton_eq_bot] using hz
  · intro q hq
    exact Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_iff_mem _ |>.mpr hq)

/-- At a prime `q`, the canonical local isomorphism intertwines the embedding of `K` with `ρ`. -/
private lemma localRingEquiv_symm_algebraMap (ρ : K ≃ₐ[k] K)
    (q : HeightOneSpectrum (𝓞 K)) (y : K) :
    (NK.GlobalCFT.Place.localRingEquiv ρ⁻¹ (NK.GlobalCFT.Place.ofFinite q)).symm
        (algebraMap K ((NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q).adicCompletion K) y) =
      algebraMap K (q.adicCompletion K) (ρ y) := by
  refine (RingEquiv.symm_apply_eq
    (NK.GlobalCFT.Place.localRingEquiv ρ⁻¹ (NK.GlobalCFT.Place.ofFinite q))).mpr ?_
  have hy : ρ⁻¹ (ρ y) = y := by
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have h := NK.GlobalCFT.Place.localRingEquiv_algebraMap ρ⁻¹
    (NK.GlobalCFT.Place.ofFinite q) (ρ y)
  rw [hy] at h
  exact h.symm

/-- The congruence subgroup of a modulus is contained in the integral idèles. -/
private lemma congSubgroup_le_integralIdeles (𝔪 : NK.NUV2.RouteB.Modulus K) :
    NK.NUV2.RouteB.CongSubgroup K 𝔪 ≤ NK.GlobalCFT.Idele.integralIdeles K := by
  intro x hx
  rw [NK.GlobalCFT.Idele.mem_integralIdeles]
  intro v hv
  rw [NK.GlobalCFT.Place.isFinite_iff] at hv
  obtain ⟨q, rfl⟩ := hv
  rw [NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one]
  exact (hx.1 q).1

/-- The component of `ρ • u` at a prime at which `u` is `1` at the conjugate prime. -/
private lemma smul_apply_finite_moved (ρ : K ≃ₐ[k] K) (u : NK.GlobalCFT.Idele K)
    (q : HeightOneSpectrum (𝓞 K))
    (h : u (NK.GlobalCFT.Place.ofFinite
      (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q)) = 1) :
    (ρ • u) (NK.GlobalCFT.Place.ofFinite q) = 1 := by
  rw [NK.GlobalCFT.Idele.smul_apply]
  rw [show u (ρ⁻¹ • NK.GlobalCFT.Place.ofFinite q)
      = u (NK.GlobalCFT.Place.ofFinite
          (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q)) from rfl]
  rw [h, map_one]

/-- The action of `Gal(K/k)` preserves the integral idèles. -/
private lemma smul_mem_integralIdeles (ρ : K ≃ₐ[k] K) {u : NK.GlobalCFT.Idele K}
    (hu : u ∈ NK.GlobalCFT.Idele.integralIdeles K) :
    ρ • u ∈ NK.GlobalCFT.Idele.integralIdeles K := by
  rw [NK.GlobalCFT.Idele.mem_integralIdeles] at hu ⊢
  intro v hv
  rw [NK.GlobalCFT.Idele.smul_apply]
  have hv' : NK.GlobalCFT.Place.IsFinite (ρ⁻¹ • v) := by
    rw [NK.GlobalCFT.Place.isFinite_iff] at hv ⊢
    obtain ⟨q, rfl⟩ := hv
    exact ⟨NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q,
      (NK.GlobalCFT.Place.smul_ofFinite ρ⁻¹ q)⟩
  refine (NK.GlobalCFT.Place.localRingEquiv_mem_localUnits ρ⁻¹ v _).mpr ?_
  have hcomp : Units.map (NK.GlobalCFT.Place.localRingEquiv ρ⁻¹ v).toMonoidHom
        (Units.map (NK.GlobalCFT.Place.localRingEquiv ρ⁻¹ v).symm.toMonoidHom (u (ρ⁻¹ • v)))
      = u (ρ⁻¹ • v) := by
    refine Units.ext ?_
    simp
  rw [hcomp]
  exact hu _ hv'

/-! ## The main theorem -/

theorem twistIdeleExists {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hne : Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮 ≠ 𝔮) :
    ∃ (𝔪 : NK.NUV2.RouteB.Modulus K) (u : NK.GlobalCFT.Idele K),
      𝔪.pos = ∅ ∧
      (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        𝔪.exps (Commons.NumberTheory.NumberField.Completion.placeSmul ρ q) = 𝔪.exps q) ∧
      𝔪.exps (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮) ≠ 0 ∧
      u ∈ NK.GlobalCFT.Idele.integralIdeles K ∧
      ρ • u * u⁻¹ ∉ NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.NUV2.RouteB.CongSubgroup K 𝔪 := by
  classical
  -- ## `ρ` is not the identity
  have hρne : ρ ≠ 1 := by
    intro h
    exact hne (by rw [h, Commons.NumberTheory.NumberField.Completion.placeSmul_one])
  -- ## an integral element moved by `ρ`, and the anti-invariant integral element `w`
  obtain ⟨y, hy⟩ := exists_moved_integral (k := k) (K := K) ρ hρne
  set w : 𝓞 K := y - rhoRing ρ y with hwdef
  have hw_ne : w ≠ 0 := sub_ne_zero.mpr hy.symm
  have hwK_ne : ((w : 𝓞 K) : K) ≠ 0 := by
    simpa using hw_ne
  have hw_anti : rhoRing ρ w = -w := by
    rw [hwdef, map_sub, rhoRing_mul_self ρ hρ2 y]
    ring
  have hw_anti' : ρ (algebraMap (𝓞 K) K w) = -algebraMap (𝓞 K) K w := by
    have h1 : (galRestrict (𝓞 k) k K (𝓞 K) ρ) w = -w := hw_anti
    rw [← algebraMap_galRestrict_apply (𝓞 k) (K := k) (L := K) (B := 𝓞 K) ρ w, h1]
    simp
  -- ## the finite set of primes carrying the "trivial local action", and the prime set `s`
  have hfin : {q : HeightOneSpectrum (𝓞 K) | w ∈ q.asIdeal}.Finite :=
    finite_setOf_mem_asIdeal hw_ne
  set Bad : Finset (HeightOneSpectrum (𝓞 K)) :=
    hfin.toFinset ∪ {𝔮, placeSmul ρ 𝔮} with hBaddef
  obtain ⟨s, hscard, hsnotBad, hsodd, hsorbit⟩ :=
    exists_primes_not_conj_avoid (k := k) (K := K) ρ hρ2 (NumberField.Units.rank K + 2) Bad
  -- `w` is a unit at every prime of `s`
  have hw_unit : ∀ q ∈ s, (w : 𝓞 K) ∉ q.asIdeal := by
    intro q hq
    have hqb : q ∉ Bad := hsnotBad q hq
    have hqf : q ∉ hfin.toFinset := fun hq' =>
      hqb (by rw [hBaddef]; exact Finset.mem_union_left _ hq')
    rwa [Set.Finite.mem_toFinset] at hqf
  -- ## the sign pattern
  have hrank : NumberField.Units.rank K + 1 < s.card := by omega
  obtain ⟨χ, hχ⟩ := exists_signPattern_notMem_range s hsodd hrank
  -- ## the support and the modulus
  set T : Finset (HeightOneSpectrum (𝓞 K)) := insert 𝔮 s with hTdef
  set S : Finset (HeightOneSpectrum (𝓞 K)) := T ∪ T.image (placeSmul ρ) with hSdef
  have hρρ : ∀ x : HeightOneSpectrum (𝓞 K), placeSmul ρ (placeSmul ρ x) = x :=
    fun x => placeSmul_placeSmul ρ hρ2 x
  have hS_stab : ∀ q : HeightOneSpectrum (𝓞 K), placeSmul ρ q ∈ S ↔ q ∈ S := by
    intro q
    have hmem : ∀ x : HeightOneSpectrum (𝓞 K),
        (placeSmul ρ x ∈ T ∪ T.image (placeSmul ρ)) ↔ (x ∈ T ∪ T.image (placeSmul ρ)) := by
      intro x
      constructor
      · intro h
        rcases Finset.mem_union.mp h with h | h
        · refine Finset.mem_union.mpr (Or.inr ?_)
          exact Finset.mem_image.mpr ⟨placeSmul ρ x, h, hρρ x⟩
        · obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp h
          have hyx' : y = x := by
            have hh := congrArg (placeSmul ρ) hyx
            rwa [hρρ y, hρρ x] at hh
          refine Finset.mem_union.mpr (Or.inl ?_)
          rwa [hyx'] at hy
      · intro h
        rcases Finset.mem_union.mp h with h | h
        · refine Finset.mem_union.mpr (Or.inr ?_)
          exact Finset.mem_image.mpr ⟨x, h, rfl⟩
        · obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp h
          have hxy : placeSmul ρ x = y := by rw [← hyx, hρρ y]
          rw [hxy]
          exact Finset.mem_union.mpr (Or.inl hy)
    rw [hSdef]
    exact hmem q
  have hS_fin : {q : HeightOneSpectrum (𝓞 K) | q ∈ S}.Finite := S.finite_toSet
  set 𝔪 : NK.NUV2.RouteB.Modulus K :=
    ⟨fun q => if q ∈ S then 2 else 0, by
      rw [NK.NUV2.RouteB.HasFiniteSupport, Filter.eventually_cofinite]
      have hset : {q : HeightOneSpectrum (𝓞 K) | ¬((if q ∈ S then 2 else 0) = 0)}
          = (↑S : Set (HeightOneSpectrum (𝓞 K))) := by
        ext q
        simp only [Set.mem_ofPred_eq, Finset.mem_coe]
        constructor
        · intro hq
          by_contra hqS
          exact hq (if_neg hqS)
        · intro hqS
          rw [if_pos hqS]
          norm_num
      rw [hset]
      exact hS_fin, ∅⟩ with h𝔪def
  have hmemS : ∀ q : HeightOneSpectrum (𝓞 K), q ∈ s → q ∈ S := by
    intro q hq
    rw [hSdef]
    refine Finset.mem_union.mpr (Or.inl ?_)
    rw [hTdef]
    exact Finset.mem_insert_of_mem hq
  have hmemSq : placeSmul ρ 𝔮 ∈ S := by
    rw [hSdef]
    refine Finset.mem_union.mpr (Or.inr ?_)
    exact Finset.mem_image.mpr ⟨𝔮, (by rw [hTdef]; exact Finset.mem_insert_self 𝔮 s), rfl⟩
  -- ## the local components of the idèle `u`
  set vq : (q : HeightOneSpectrum (𝓞 K)) → q ∈ s → Kˣ :=
    fun q hq => if placeSmul ρ q = q then
        (if χ q = 0 then 1 else Units.mk0 ((w : 𝓞 K) : K) hwK_ne)
      else (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) (sgnU (K := K) (χ q)) : Kˣ)
    with hvqdef
  have hvq_val : ∀ (q : HeightOneSpectrum (𝓞 K)) (hq : q ∈ s),
      q.valuation K ((vq q hq : Kˣ) : K) = 1 := by
    intro q hq
    by_cases hfix : placeSmul ρ q = q
    · have hval : vq q hq =
          (if χ q = 0 then (1 : Kˣ) else Units.mk0 (((w : 𝓞 K) : K)) hwK_ne) := by
        simp only [hvqdef, if_pos hfix]
      rw [hval]
      by_cases hχ0 : χ q = 0
      · rw [if_pos hχ0]; simp
      · rw [if_neg hχ0, Units.val_mk0]
        rw [HeightOneSpectrum.valuation_eq_one_iff_notMem]
        exact hw_unit q hq
    · have hval : vq q hq =
          Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) (sgnU (K := K) (χ q)) := by
        simp only [hvqdef, if_neg hfix]
      rw [hval, Units.coe_map]
      exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := K) (v := q)).mpr
        (sgnU_mem_localUnits (K := K) (χ q) q)
  -- ## the idèle `u`
  set u : NK.GlobalCFT.Idele K :=
    ⟨fun v => match v with
      | Sum.inl _ => 1
      | Sum.inr q => if hq : q ∈ s then
          (Units.map (algebraMap K (q.adicCompletion K) : K →* q.adicCompletion K) (vq q hq) :
            (NK.GlobalCFT.Place.localField K (Sum.inr q))ˣ)
          else 1, by
        rw [Filter.eventually_cofinite]
        refine ((s.image NK.GlobalCFT.Place.ofFinite).finite_toSet).subset ?_
        rintro (_ | q) hv
        · exact absurd (NK.GlobalCFT.Place.mem_localUnits_ofInfinite (w := _) (x := 1)) hv
        · refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨q, ?_, rfl⟩)
          by_contra hq
          refine absurd ?_ hv
          show (if h : q ∈ s then
            (Units.map (algebraMap K (q.adicCompletion K) : K →* q.adicCompletion K) (vq q h) :
              (NK.GlobalCFT.Place.localField K (Sum.inr q))ˣ) else 1) ∈
            NK.GlobalCFT.Place.localUnits K (Sum.inr q)
          rw [dif_neg hq]
          exact Subgroup.one_mem _⟩ with hudef
  have hu_loc : ∀ (q : HeightOneSpectrum (𝓞 K)) (hq : q ∈ s),
      u (NK.GlobalCFT.Place.ofFinite q)
        = Units.map (algebraMap K (q.adicCompletion K) : K →* q.adicCompletion K) (vq q hq) := by
    intro q hq
    show (if h : q ∈ s then
      (Units.map (algebraMap K (q.adicCompletion K) : K →* q.adicCompletion K) (vq q h) :
        (NK.GlobalCFT.Place.localField K (Sum.inr q))ˣ) else 1) = _
    rw [dif_pos hq]
  have hu_loc' : ∀ q : HeightOneSpectrum (𝓞 K), q ∉ s →
      u (NK.GlobalCFT.Place.ofFinite q) = 1 := by
    intro q hq
    show (if h : q ∈ s then
      (Units.map (algebraMap K (q.adicCompletion K) : K →* q.adicCompletion K) (vq q h) :
        (NK.GlobalCFT.Place.localField K (Sum.inr q))ˣ) else 1) = 1
    rw [dif_neg hq]
  have huloc_unit : ∀ (q : HeightOneSpectrum (𝓞 K)) (hq : q ∈ s),
      Units.map (algebraMap K (q.adicCompletion K) : K →* q.adicCompletion K) (vq q hq)
        ∈ NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite q) := by
    intro q hq
    rw [NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one, Units.coe_map]
    change Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (algebraMap K (q.adicCompletion K) ((vq q hq : Kˣ) : K)) = 1
    rw [Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq]
    exact hvq_val q hq
  have hu_int : u ∈ NK.GlobalCFT.Idele.integralIdeles K := by
    rw [NK.GlobalCFT.Idele.mem_integralIdeles]
    intro v hv
    rw [NK.GlobalCFT.Place.isFinite_iff] at hv
    obtain ⟨q, rfl⟩ := hv
    by_cases hq : q ∈ s
    · rw [hu_loc q hq]; exact huloc_unit q hq
    · rw [hu_loc' q hq]; exact Subgroup.one_mem _
  -- ## the twist component at a prime of `s`
  have htwist : ∀ (q : HeightOneSpectrum (𝓞 K)) (hq : q ∈ s),
      (ρ • u * u⁻¹) (NK.GlobalCFT.Place.ofFinite q) =
        Units.map (algebraMap K (q.adicCompletion K) : K →* q.adicCompletion K)
          (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) (sgnU (K := K) (χ q))) := by
    intro q hq
    by_cases hfix : placeSmul ρ q = q
    · -- ## `ρ`-fixed prime
      have hq'_eq : NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q = q := by
        rw [← NK.GlobalCFT.Inclusion.globalCFT_placeSmul_eq_smulHeightOneSpectrum ρ⁻¹ q,
          placeSmul_inv ρ hρ2 q, hfix]
      have hq's : NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q ∈ s := by
        rw [hq'_eq]; exact hq
      have hvq_eq : vq (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q) hq's = vq q hq := by
        simp only [hvqdef]
        rw [hq'_eq]
      -- the `ρ`-component at `q`
      have hsmul : (ρ • u) (NK.GlobalCFT.Place.ofFinite q)
          = Units.map (algebraMap K (q.adicCompletion K) : K →* q.adicCompletion K)
              (Units.map ρ.toMonoidHom (vq q hq)) := by
        refine Units.ext ?_
        rw [NK.GlobalCFT.Idele.smul_apply]
        simp only [NK.GlobalCFT.Place.smul_ofFinite]
        rw [hu_loc (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q) hq's]
        rw [Units.coe_map, Units.coe_map, hvq_eq]
        change (NK.GlobalCFT.Place.localRingEquiv ρ⁻¹ (NK.GlobalCFT.Place.ofFinite q)).symm
            (algebraMap K ((NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q).adicCompletion K)
              ((vq q hq : Kˣ) : K))
          = algebraMap K (q.adicCompletion K) (ρ ((vq q hq : Kˣ) : K))
        exact localRingEquiv_symm_algebraMap ρ q ((vq q hq : Kˣ) : K)
      -- the anti-invariance of `w` at the level of units
      have hK : Units.map ρ.toMonoidHom (vq q hq) * (vq q hq)⁻¹
          = Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) (sgnU (K := K) (χ q)) := by
        simp only [hvqdef, if_pos hfix]
        split_ifs with hχ0
        · rw [map_one, inv_one, mul_one,
            show sgnU (K := K) (χ q) = 1 from by unfold sgnU; rw [if_pos hχ0], map_one]
        · have hρw : ((Units.map ρ.toMonoidHom (Units.mk0 (((w : 𝓞 K) : K)) hwK_ne) : Kˣ) : K)
              = -((w : 𝓞 K) : K) := by
            rw [Units.coe_map]
            change ρ (algebraMap (𝓞 K) K w) = -algebraMap (𝓞 K) K w
            exact hw_anti'
          have hW : ((Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) (sgnU (K := K) (χ q)) : Kˣ) :
                K) = -1 := by
            rw [Units.coe_map, sgnU_coe, if_neg hχ0]
            simp
          refine Units.ext ?_
          rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, hρw, hW]
          rw [neg_mul, mul_inv_cancel₀ hwK_ne]
      -- assemble
      rw [NK.GlobalCFT.Idele.mul_apply, NK.GlobalCFT.Idele.inv_apply, hsmul, hu_loc q hq]
      rw [← map_inv, ← map_mul, hK]
    · -- ## the prime `q` is moved by `ρ`
      have hq'ns : NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q ∉ s := by
        intro hmem
        rw [← NK.GlobalCFT.Inclusion.globalCFT_placeSmul_eq_smulHeightOneSpectrum ρ⁻¹ q,
          placeSmul_inv ρ hρ2 q] at hmem
        exact hfix (hsorbit q hq hmem)
      have hK : (vq q hq)⁻¹
          = Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) (sgnU (K := K) (χ q)) := by
        have hv : vq q hq
            = Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) (sgnU (K := K) (χ q)) := by
          simp only [hvqdef, if_neg hfix]
        rw [hv, ← map_inv, sgnU_inv]
      rw [NK.GlobalCFT.Idele.mul_apply, NK.GlobalCFT.Idele.inv_apply,
        smul_apply_finite_moved ρ u q (hu_loc' _ hq'ns), hu_loc q hq, one_mul]
      rw [← map_inv, hK]
  -- ## assembling the result
  refine ⟨𝔪, u, rfl, ?_, ?_, hu_int, ?_⟩
  · -- stability of the exponents
    intro q
    show (if placeSmul ρ q ∈ S then 2 else 0) = (if q ∈ S then 2 else 0)
    by_cases h : q ∈ S
    · rw [if_pos h, if_pos ((hS_stab q).mpr h)]
    · rw [if_neg h, if_neg (fun hh => h ((hS_stab q).mp hh))]
  · -- the exponent at `ρ𝔮` is non-zero
    show (if placeSmul ρ 𝔮 ∈ S then 2 else 0) ≠ 0
    rw [if_pos hmemSq]
    norm_num
  · -- the escape clause
    intro hmem
    obtain ⟨p, hp, w', hw', hpw⟩ := Subgroup.mem_sup.mp hmem
    obtain ⟨ε, hε⟩ := NK.GlobalCFT.Idele.mem_principalSubgroup.mp hp
    have hpt : NK.GlobalCFT.Idele.principalIdele K ε * w' = ρ • u * u⁻¹ := by
      rw [hε]; exact hpw
    have htint : ρ • u * u⁻¹ ∈ NK.GlobalCFT.Idele.integralIdeles K :=
      Subgroup.mul_mem _ (smul_mem_integralIdeles ρ hu_int) (Subgroup.inv_mem _ hu_int)
    -- `ε` is a unit of `𝓞 K`
    have hεval : ∀ q : HeightOneSpectrum (𝓞 K), q.valuation K (ε : K) = 1 := by
      intro q
      have h1 : (NK.GlobalCFT.Idele.principalIdele K ε) (NK.GlobalCFT.Place.ofFinite q)
          ∈ NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite q) := by
        have hsplit : (NK.GlobalCFT.Idele.principalIdele K ε) (NK.GlobalCFT.Place.ofFinite q)
            = ((ρ • u * u⁻¹) (NK.GlobalCFT.Place.ofFinite q))
              * ((w' (NK.GlobalCFT.Place.ofFinite q)))⁻¹ := by
          calc (NK.GlobalCFT.Idele.principalIdele K ε) (NK.GlobalCFT.Place.ofFinite q)
              = ((NK.GlobalCFT.Idele.principalIdele K ε) * w')
                  (NK.GlobalCFT.Place.ofFinite q)
                  * ((w' (NK.GlobalCFT.Place.ofFinite q)))⁻¹ := by
                rw [NK.GlobalCFT.Idele.mul_apply]
                exact (mul_inv_cancel_right _ _).symm
            _ = ((ρ • u * u⁻¹) (NK.GlobalCFT.Place.ofFinite q))
                  * ((w' (NK.GlobalCFT.Place.ofFinite q)))⁻¹ := by rw [hpt]
        rw [hsplit]
        refine Subgroup.mul_mem _ (htint _ (NK.GlobalCFT.Place.isFinite_ofFinite q)) ?_
        exact Subgroup.inv_mem _
          (congSubgroup_le_integralIdeles 𝔪 hw' _ (NK.GlobalCFT.Place.isFinite_ofFinite q))
      rw [NK.GlobalCFT.Idele.principalIdele_apply,
        NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one, Units.coe_map] at h1
      change Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (algebraMap K (q.adicCompletion K) (ε : K)) = 1 at h1
      rw [Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq] at h1
      exact h1
    have hεint : (ε : K) ∈ (algebraMap (𝓞 K) K).range :=
      HeightOneSpectrum.mem_integers_of_valuation_le_one (K := K) (ε : K)
        (fun q => le_of_eq (hεval q))
    have hεinvint : (((ε⁻¹ : Kˣ) : K)) ∈ (algebraMap (𝓞 K) K).range :=
      HeightOneSpectrum.mem_integers_of_valuation_le_one (K := K) (((ε⁻¹ : Kˣ) : K)) (fun q => by
        rw [show (((ε⁻¹ : Kˣ) : K)) = (ε : K)⁻¹ from by simp, map_inv₀, hεval q]
        simp)
    obtain ⟨a, ha⟩ := RingHom.mem_range.mp hεint
    obtain ⟨b, hb⟩ := RingHom.mem_range.mp hεinvint
    have hab : a * b = 1 := by
      apply NumberField.RingOfIntegers.coe_injective
      rw [map_mul, map_one, ha, hb]
      simp
    have hba : b * a = 1 := by rw [mul_comm, hab]
    let e : (𝓞 K)ˣ := { val := a, inv := b, val_inv := hab, inv_val := hba }
    have he_coe : ((e : (𝓞 K)ˣ) : 𝓞 K) = a := rfl
    -- the congruence at the primes of `s`
    have hcong : ∀ (q : HeightOneSpectrum (𝓞 K)) (hq : q ∈ s),
        Ideal.Quotient.mk (q.asIdeal ^ 2) ((e : (𝓞 K)ˣ) : 𝓞 K)
          = Ideal.Quotient.mk (q.asIdeal ^ 2) (((sgnU (K := K) (χ q) : (𝓞 K)ˣ) : 𝓞 K)) := by
      intro q hq
      have hexp2 : 𝔪.exps q = 2 := by
        show (if q ∈ S then 2 else 0) = 2
        rw [if_pos (hmemS q hq)]
      have hexp : Valued.v
          (((w' (NK.GlobalCFT.Place.ofFinite q) : (q.adicCompletion K)ˣ) :
              q.adicCompletion K) - 1)
          ≤ WithZero.exp (-(2 : ℤ)) := by
        have h := (NK.NUV2.RouteB.Modulus.mem_congSubgroup_iff.mp hw').1 q
        rw [NK.NUV2.RouteB.IsCongAt, hexp2] at h
        exact h.2
      -- the value of the twist at `q`
      have htw := htwist q hq
      -- the product identity at `q`
      have hpwq : (algebraMap K (q.adicCompletion K) (ε : K))
            * ((w' (NK.GlobalCFT.Place.ofFinite q) : (q.adicCompletion K)ˣ) : q.adicCompletion K)
          = algebraMap K (q.adicCompletion K) ((sgnU (K := K) (χ q) : (𝓞 K)ˣ) : K) := by
        have h : ((((NK.GlobalCFT.Idele.principalIdele K ε * w') (NK.GlobalCFT.Place.ofFinite q)) :
              (q.adicCompletion K)ˣ) : q.adicCompletion K)
            = ((((ρ • u * u⁻¹) (NK.GlobalCFT.Place.ofFinite q)) : (q.adicCompletion K)ˣ) :
                q.adicCompletion K) := by
          rw [hpt]
        rw [NK.GlobalCFT.Idele.mul_apply, Units.val_mul, NK.GlobalCFT.Idele.principalIdele_apply,
          Units.coe_map, htw, Units.coe_map, Units.coe_map] at h
        exact h
      -- the crucial valuation bound
      have hval : Valued.v (algebraMap K (q.adicCompletion K)
            ((ε : K) - ((sgnU (K := K) (χ q) : (𝓞 K)ˣ) : K))) ≤ WithZero.exp (-(2 : ℤ)) := by
        have h1 : algebraMap K (q.adicCompletion K)
              ((ε : K) - ((sgnU (K := K) (χ q) : (𝓞 K)ˣ) : K))
            = algebraMap K (q.adicCompletion K) (ε : K)
              * (1 - ((w' (NK.GlobalCFT.Place.ofFinite q) : (q.adicCompletion K)ˣ) :
                  q.adicCompletion K)) := by
          rw [map_sub, mul_sub, mul_one, hpwq]
        rw [h1, map_mul]
        have hε1 : Valued.v (algebraMap K (q.adicCompletion K) (ε : K)) = 1 := by
          rw [Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq]
          exact hεval q
        have hneg : Valued.v (1 - ((w' (NK.GlobalCFT.Place.ofFinite q) :
              (q.adicCompletion K)ˣ) : q.adicCompletion K)) ≤ WithZero.exp (-(2 : ℤ)) := by
          have hW : (1 : q.adicCompletion K)
              - ((w' (NK.GlobalCFT.Place.ofFinite q) : (q.adicCompletion K)ˣ) :
                  q.adicCompletion K)
              = -(((w' (NK.GlobalCFT.Place.ofFinite q) : (q.adicCompletion K)ˣ) :
                  q.adicCompletion K) - 1) := by ring
          rw [hW, Valuation.map_neg]
          exact hexp
        calc Valued.v (algebraMap K (q.adicCompletion K) (ε : K))
              * Valued.v (1 - ((w' (NK.GlobalCFT.Place.ofFinite q) :
                  (q.adicCompletion K)ˣ) : q.adicCompletion K))
            ≤ 1 * WithZero.exp (-(2 : ℤ)) :=
              mul_le_mul' (le_of_eq hε1) hneg
          _ = WithZero.exp (-(2 : ℤ)) := one_mul _
      -- descend to `𝓞 K ⧸ q ^ 2`
      rw [Ideal.Quotient.eq]
      rw [he_coe]
      have hmem : a - ((sgnU (K := K) (χ q) : (𝓞 K)ˣ) : 𝓞 K) ∈ q.asIdeal ^ 2 := by
        rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem]
        have h1 : q.intValuation (a - ((sgnU (K := K) (χ q) : (𝓞 K)ˣ) : 𝓞 K))
            = q.valuation K (algebraMap (𝓞 K) K
                (a - ((sgnU (K := K) (χ q) : (𝓞 K)ˣ) : 𝓞 K))) :=
          (HeightOneSpectrum.valuation_of_algebraMap (K := K) (v := q)
            (a - ((sgnU (K := K) (χ q) : (𝓞 K)ˣ) : 𝓞 K))).symm
        rw [h1]
        have harg : algebraMap (𝓞 K) K (a - ((sgnU (K := K) (χ q) : (𝓞 K)ˣ) : 𝓞 K))
            = (ε : K) - ((sgnU (K := K) (χ q) : (𝓞 K)ˣ) : K) := by
          rw [map_sub, ha]
        rw [harg, ← Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq]
        exact hval
      exact hmem
    -- contradiction with the sign pattern
    obtain ⟨q, hq, hqne⟩ := hχ e
    refine hqne ?_
    rw [hcong q hq, sgnU_coe]

end Work.SSGRoute.PinnedTwin
