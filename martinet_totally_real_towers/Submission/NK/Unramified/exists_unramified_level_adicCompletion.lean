import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.Basic
import Submission.NK.LocalReciprocity.NormGroup
import Submission.NK.Unramified.exists_adjoin_galois_abelian_subfield

universe u

/-!
# The unramified level of degree `m` of a `p`-adic field, inside the algebraic closure

For a number field `K`, a finite place `Q` of `K` and `m ≥ 1`, this file constructs the
unramified extension of degree `m` of the local field `Q.adicCompletion K` *inside*
`AlgebraicClosure (Q.adicCompletion K)`: an intermediate field `E = F⟮θ⟯` which is finite
Galois over `F = Q.adicCompletion K` with abelian automorphism group, of degree `m`, and whose
norm group is

`N_{E/F} Eˣ = ⟨π^m⟩ · U⁰ = NK.LocalReciprocityLubinTate.unramifiedNormGroup K Q m`,

where `π` is the uniformiser of `F` and `U⁰` the units of its ring of integers.

The construction goes through the arithmetic input
`Commons.NumberTheory.NumberField.Completion.exists_galois_unramified_tower_with_subfield`:
taking the trivial Galois extension `K / K` there, we obtain a finite **Galois** extension
`L / K` of number fields and a place `q | Q` with `e(q|Q) = 1` and `f(q|Q) = m`.  The local
extension `L_q / K_Q` is then unramified of degree `m`, its Galois group is cyclic
(`isCyclic_algEquiv_adicCompletion_of_ramificationIdx_eq_one`, because the Frobenius generates
the decomposition group of an unramified place), and its norm group is computed by
`normGroup_eq_unramifiedNormGroup_aux` below.  Finally the abstract local extension is realised
inside the algebraic closure by `exists_adjoin_galois_abelian_subfield` (the primitive element
theorem plus `IsAlgClosed.lift`).
-/

open scoped NumberField
open IsDedekindDomain.HeightOneSpectrum

set_option linter.style.haveILetI false

namespace NK.Unramified

/-! ## Auxiliary results on the units of the completion -/

/-- For a submonoid `S` of a monoid `M`, the image of `Sˣ` in `Mˣ` under the map induced by the
inclusion `S ↪ M` is the subgroup `S.units` of units of `M` lying in `S`. -/
private lemma map_units_subtype_top_aux {M : Type*} [Monoid M] (S : Submonoid M) :
    Subgroup.map (Units.map S.subtype) ⊤ = S.units := by
  ext u
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, -, hy⟩
    rw [Submonoid.mem_units_iff]
    refine ⟨?_, ?_⟩
    · rw [← hy]; simp
    · rw [← hy, ← map_inv]; simp
  · intro hu
    obtain ⟨h1, h2⟩ := (Submonoid.mem_units_iff S u).mp hu
    refine ⟨Units.mk ⟨(u : M), h1⟩ ⟨((u⁻¹ : Mˣ) : M), h2⟩ (Subtype.ext (by simp))
      (Subtype.ext (by simp)), Subgroup.mem_top _, ?_⟩
    exact Units.ext rfl

/-- `u` is one of the units `U⁰` of the completion `Q.adicCompletion K` if and only if its
valuation is `1`. -/
private theorem mem_adicUnits_iff_aux {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (u : (Q.adicCompletion K)ˣ) :
    u ∈ NK.LocalReciprocityLubinTate.adicUnits K Q ↔
      Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (u : Q.adicCompletion K) = 1 := by
  rw [← IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
  have h : NK.LocalReciprocityLubinTate.adicUnits K Q = (Q.adicCompletionIntegers K).units := by
    rw [NK.LocalReciprocityLubinTate.adicUnits]
    exact map_units_subtype_top_aux (Q.adicCompletionIntegers K).toSubmonoid
  rw [h]

/-! ## The norm group of an unramified extension -/

/-- **The norm group of an unramified local extension.**  If `L / K` is a finite Galois extension
of number fields, `Q' | Q` a place with ramification index `1`, then the norm group of the local
extension `L_{Q'} / K_Q` is `⟨π^f⟩ · U⁰`, where `f = f(Q'|Q)` is the inertia degree, `π` a
uniformiser of `K_Q` and `U⁰` the units of its ring of integers. -/
private theorem normGroup_eq_unramifiedNormGroup_aux {K : Type} [Field K] [NumberField K]
    {L : Type*} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (h : Q'.asIdeal.LiesOver Q.asIdeal)
    (hunr : Q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    letI : Algebra (Q.adicCompletion K) (Q'.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q Q' h)
    NK.LocalReciprocity.normGroup (Q.adicCompletion K) (Q'.adicCompletion L)
      = NK.LocalReciprocityLubinTate.unramifiedNormGroup K Q
        (Q'.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) := by
  letI : Algebra (Q.adicCompletion K) (Q'.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q Q' h)
  set f : ℕ := Q'.asIdeal.inertiaDeg (𝓞 K) with hf
  have hfpos : 0 < f := by rw [hf]; exact Ideal.inertiaDeg_pos Q'.asIdeal _
  have hπ : Valued.v ((NK.LocalReciprocityLubinTate.uniformizerUnit K Q :
      (Q.adicCompletion K)ˣ) : Q.adicCompletion K) = WithZero.exp (-1) := by
    simp only [NK.LocalReciprocityLubinTate.uniformizerUnit, Units.val_mk0]
    exact Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one Q
  have hπpow : ∀ k : ℤ, Valued.v (((NK.LocalReciprocityLubinTate.uniformizerUnit K Q ^ k :
      (Q.adicCompletion K)ˣ) : Q.adicCompletion K)) = WithZero.exp (-k) := by
    intro k
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hπ, ← WithZero.exp_zsmul]
    congr 1
    simp
  have hπfval : Valued.v (((NK.LocalReciprocityLubinTate.uniformizerUnit K Q ^ f :
      (Q.adicCompletion K)ˣ) : Q.adicCompletion K)) = WithZero.exp (-(f : ℤ)) := by
    rw [Units.val_pow_eq_pow_val, map_pow, hπ, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hnorm : ∀ y : Q.adicCompletion K,
      (∃ x : Q'.adicCompletion L, Algebra.norm (Q.adicCompletion K) x = y) ↔
        ∃ z : Q.adicCompletion K, Valued.v y = (Valued.v z) ^ f := by
    intro y
    rw [hf]
    exact Commons.NumberTheory.NumberField.Completion.norm_range_of_ramificationIdx_eq_one
      Q Q' h hunr y
  have hval_unit : ∀ u : (Q.adicCompletionIntegers K)ˣ,
      Valued.v (((u : Q.adicCompletionIntegers K) : Q.adicCompletion K)) = 1 := by
    intro u
    have hle : Valued.v (((u : Q.adicCompletionIntegers K) : Q.adicCompletion K)) ≤ 1 :=
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K Q).mp
        (u : Q.adicCompletionIntegers K).2
    have hnot : ¬ Valued.v (((u : Q.adicCompletionIntegers K) : Q.adicCompletion K)) < 1 := by
      intro hlt
      have hmem : (u : Q.adicCompletionIntegers K) ∈
          IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) :=
        (Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one Q
          (u : Q.adicCompletionIntegers K)).mpr hlt
      have hnu := (IsLocalRing.mem_maximalIdeal (u : Q.adicCompletionIntegers K)).mp hmem
      exact hnu (Units.isUnit u)
    exact le_antisymm hle (not_lt.mp hnot)
  haveI : Module.Finite (Q.adicCompletion K) (Q'.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q Q' h
  change NK.LocalReciprocity.normGroup (Q.adicCompletion K) (Q'.adicCompletion L)
      = Subgroup.zpowers (NK.LocalReciprocityLubinTate.uniformizerUnit K Q ^ f) ⊔
        NK.LocalReciprocityLubinTate.adicUnits K Q
  apply le_antisymm
  · -- ## norms lie in `⟨π^f⟩ · U⁰`
    intro x hx
    rw [NK.LocalReciprocity.normGroup_eq_range] at hx
    obtain ⟨u, hu⟩ := hx
    have hu' : Algebra.norm (Q.adicCompletion K) (u : Q'.adicCompletion L) =
        (x : Q.adicCompletion K) := by
      rw [← congrArg (fun w : (Q.adicCompletion K)ˣ => (w : Q.adicCompletion K)) hu, Units.coe_map]
    obtain ⟨z, hz⟩ := (hnorm (x : Q.adicCompletion K)).mp ⟨(u : Q'.adicCompletion L), hu'⟩
    rcases eq_or_ne z 0 with rfl | hz0
    · exfalso
      have hvx : Valued.v ((x : Q.adicCompletion K)) ≠ 0 :=
        (Valuation.ne_zero_iff _).mpr (Units.ne_zero x)
      rw [map_zero, zero_pow hfpos.ne'] at hz
      exact hvx hz
    · obtain ⟨u₀, k, hk⟩ :=
        Commons.NumberTheory.NumberField.Completion.exists_units_mul_uniformizer_zpow_adicCompletion Q
          (Units.mk0 z hz0)
      have hk' : (z : Q.adicCompletion K) =
          ((u₀ : Q.adicCompletionIntegers K) : Q.adicCompletion K) *
          (((Commons.RingTheory.Henselian.uniformizer (R := 𝓞 K) (K := K) Q :
            Q.adicCompletionIntegers K)) : Q.adicCompletion K) ^ k := by
        simpa using hk
      have huz : Valued.v (z : Q.adicCompletion K) = WithZero.exp (-k) := by
        rw [hk', map_mul, map_zpow₀, hval_unit u₀,
          Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one, one_mul,
          ← WithZero.exp_zsmul]
        congr 1
        simp
      have hxval : Valued.v ((x : Q.adicCompletion K)) = WithZero.exp (-((f : ℤ) * k)) := by
        rw [hz, huz, ← WithZero.exp_nsmul]
        congr 1
        ring
      have hb : (x * (NK.LocalReciprocityLubinTate.uniformizerUnit K Q ^ f) ^ (-k)) ∈
          NK.LocalReciprocityLubinTate.adicUnits K Q := by
        rw [mem_adicUnits_iff_aux, Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀,
          hπfval, hxval, ← WithZero.exp_zsmul]
        rw [← WithZero.exp_add]
        congr 1
        ring
      exact Subgroup.mem_sup.mpr ⟨(NK.LocalReciprocityLubinTate.uniformizerUnit K Q ^ f) ^ k,
        Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩,
        x * (NK.LocalReciprocityLubinTate.uniformizerUnit K Q ^ f) ^ (-k), hb, by
          rw [mul_comm x, ← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]⟩
  · -- ## `⟨π^f⟩ · U⁰ ≤ N`
    intro x hx
    rw [Subgroup.mem_sup] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← hk]
    have hbval : Valued.v ((b : Q.adicCompletion K)) = 1 := (mem_adicUnits_iff_aux Q b).mp hb
    have hvalL : Valued.v ((((NK.LocalReciprocityLubinTate.uniformizerUnit K Q ^ f) ^ k * b :
        (Q.adicCompletion K)ˣ) : Q.adicCompletion K)) = WithZero.exp (-((f : ℤ) * k)) := by
      rw [Units.val_mul, map_mul, hbval, mul_one, Units.val_zpow_eq_zpow_val, map_zpow₀, hπfval,
        ← WithZero.exp_zsmul]
      congr 1
      ring
    have hvalR : (Valued.v (((NK.LocalReciprocityLubinTate.uniformizerUnit K Q ^ k :
        (Q.adicCompletion K)ˣ) : Q.adicCompletion K))) ^ f = WithZero.exp (-((f : ℤ) * k)) := by
      rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hπ, ← WithZero.exp_zsmul,
        ← WithZero.exp_nsmul]
      congr 1
      ring
    obtain ⟨y, hy⟩ := (hnorm _).mpr
      ⟨((NK.LocalReciprocityLubinTate.uniformizerUnit K Q ^ k : (Q.adicCompletion K)ˣ) :
        Q.adicCompletion K), by rw [hvalL, hvalR]⟩
    refine ⟨Units.mk0 y ?_, ?_⟩
    · intro h0
      have hne : Algebra.norm (Q.adicCompletion K) y ≠ 0 := by
        rw [hy]
        exact Units.ne_zero _
      exact hne (by rw [h0, Algebra.norm_zero])
    · apply Units.ext
      rw [Units.coe_map, Units.val_mk0]
      exact hy

/-! ## The unramified level -/

/-- **The unramified level of degree `m` of `Q.adicCompletion K`, inside the algebraic closure.**

There is an intermediate field `E` of `AlgebraicClosure (Q.adicCompletion K)`, generated by a
single element, which is finite Galois over `F = Q.adicCompletion K` with commutative
automorphism group, of degree `m`, and whose norm group is
`⟨π^m⟩ · U⁰ = NK.LocalReciprocityLubinTate.unramifiedNormGroup K Q m`. -/
theorem exists_unramified_level_adicCompletion (K : Type) [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (m : ℕ) (hm : 1 ≤ m) :
    ∃ (E : IntermediateField (Q.adicCompletion K) (AlgebraicClosure (Q.adicCompletion K)))
      (θ : AlgebraicClosure (Q.adicCompletion K)),
      E = IntermediateField.adjoin (Q.adicCompletion K) {θ} ∧
      FiniteDimensional (Q.adicCompletion K) E ∧
      IsGalois (Q.adicCompletion K) E ∧
      (∀ σ τ : ↥E ≃ₐ[Q.adicCompletion K] ↥E, σ * τ = τ * σ) ∧
      Module.finrank (Q.adicCompletion K) ↥E = m ∧
      NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥E
        = NK.LocalReciprocityLubinTate.unramifiedNormGroup K Q m := by
  classical
  -- ## Step 1. A finite Galois extension `L / K` with a place `q | Q` which is unramified of
  -- inertia degree `m` (taking the trivial Galois extension `K / K` in the tower construction).
  obtain ⟨L'', hf'', hnf'', hAlg1, hAlg2, hST'', hfd1, hfd2, hgal1, hgal2, q'', hq''over, hq''e,
    hq''f, L, hfL, hnfL, hAlgKL, hfdKL, hgalKL, hAlgL'', hSTL, hfdL'', hgalL'',
    q, hqover, hq''overq, hqe, hqf⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_galois_unramified_tower_with_subfield
      (L := K) (L' := K) Q Q (Ideal.LiesOver.mk (by rw [Ideal.under]; rfl)) m (by omega)
  haveI : FiniteDimensional K L := hfdKL
  haveI : IsGalois K L := hgalKL
  -- ## Step 2. `f(Q|Q) = 1`, hence `f(q|Q) = m`.
  have hself : @Ideal.inertiaDeg (𝓞 K) _ Q.asIdeal (𝓞 K) _
      (NumberField.inst_ringOfIntegersAlgebra K K) = 1 := by
    letI : Algebra (𝓞 K) (𝓞 K) := NumberField.inst_ringOfIntegersAlgebra K K
    have halg : (algebraMap (𝓞 K) (𝓞 K) : 𝓞 K →+* 𝓞 K) = RingHom.id (𝓞 K) := by
      ext x
      rfl
    haveI : Q.asIdeal.LiesOver Q.asIdeal := Ideal.LiesOver.mk (by
      show Q.asIdeal = Ideal.under (𝓞 K) Q.asIdeal
      rw [Ideal.under, halg, Ideal.comap_id])
    rw [Ideal.inertiaDeg_eq_of_isMaximal Q.asIdeal Q.asIdeal]
    exact Module.finrank_self _
  have hmf : q.asIdeal.inertiaDeg (𝓞 K) = m := by rw [hqf, hself, mul_one]
  -- ## Step 3. The local extension `L_q / K_Q` and its invariants.
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hqover)
  have hfin : Module.finrank (Q.adicCompletion K) (q.adicCompletion L) = m := by
    rw [← Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
        Q q hqover, hqe, one_mul, hmf]
  haveI hfdloc : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hqover
  haveI hgalloc : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion Q q hqover
  have hcyc : IsCyclic (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isCyclic_algEquiv_adicCompletion_of_ramificationIdx_eq_one
      Q q hqover hqe
  -- the local Galois group is cyclic, hence commutative
  have hcomm : ∀ σ τ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L,
      σ * τ = τ * σ := by
    obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcyc
    intro σ τ
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ▸ Subgroup.mem_top σ)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ▸ Subgroup.mem_top τ)
    rw [← hi, ← hj, ← zpow_add, add_comm, zpow_add]
  -- the norm group of the unramified extension of degree `m`
  have hN : NK.LocalReciprocity.normGroup (Q.adicCompletion K) (q.adicCompletion L)
      = NK.LocalReciprocityLubinTate.unramifiedNormGroup K Q m := by
    rw [normGroup_eq_unramifiedNormGroup_aux Q q hqover hqe, hmf]
  -- ## Step 4. Realise the local extension inside the algebraic closure.
  exact exists_adjoin_galois_abelian_subfield hcomm m hfin
    (NK.LocalReciprocityLubinTate.unramifiedNormGroup K Q m) hN

end NK.Unramified
