import Mathlib
import Submission.NK.CFTLib.Arl.Defs
import Submission.NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFTdeep.NormIndex.localNorm_finiteIndex_archimedean
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField WithZero NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace NK.NUV2.ARL

open NK.GlobalCFT

/-- The value group `ℤᵐ⁰ = WithZero (Multiplicative ℤ)` of the logarithmic valuation used
throughout this file. -/
abbrev NuvValGroup : Type := WithZero (Multiplicative ℤ)

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Valuation arithmetic -/

section ValuationCalc

variable {F : Type*} [Field F] {v : Valuation F NuvValGroup}

/-- The set `{x | v (x - 1) ≤ δ}` is closed under multiplication, for `δ ≤ 1`. -/
private lemma val_mul_sub_one_le {x y : F} {δ : NuvValGroup} (hδ : δ ≤ 1)
    (hx : v (x - 1) ≤ δ) (hy : v (y - 1) ≤ δ) : v (x * y - 1) ≤ δ := by
  have hy1 : v y ≤ 1 := by
    have h := Valuation.map_add v (y - 1) 1
    rw [sub_add_cancel, Valuation.map_one] at h
    exact h.trans (max_le (hy.trans hδ) le_rfl)
  have hxy : x * y - 1 = (x - 1) * y + (y - 1) := by ring
  rw [hxy]
  refine (Valuation.map_add v _ _).trans (max_le ?_ hy)
  rw [Valuation.map_mul]
  simpa using mul_le_mul' hx hy1

/-- The set `{x | v (x - 1) ≤ δ}` is closed under finite products, for `δ ≤ 1`. -/
private lemma val_prod_sub_one_le {ι : Type*} (s : Finset ι) (f : ι → F) {δ : NuvValGroup}
    (hδ : δ ≤ 1) (hf : ∀ i ∈ s, v (f i - 1) ≤ δ) : v ((∏ i ∈ s, f i) - 1) ≤ δ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t hat ih =>
      rw [Finset.prod_insert hat]
      exact val_mul_sub_one_le hδ (hf a (Finset.mem_insert_self a t))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- The same for finite products of units. -/
private lemma val_prod_units_sub_one_le {ι : Type*} (s : Finset ι) (f : ι → Fˣ) {δ : NuvValGroup}
    (hδ : δ ≤ 1) (hf : ∀ i ∈ s, v ((f i : F) - 1) ≤ δ) :
    v ((↑(∏ i ∈ s, f i) : F) - 1) ≤ δ := by
  rw [Units.coe_prod]
  exact val_prod_sub_one_le s (fun i => (f i : F)) hδ hf

end ValuationCalc

/-! ## The local norm at a finite place preserves the congruence `≡ 1 mod m` -/

section LocalNormFinite

/-- **The local norm of a principal unit is a principal unit.**  If `u ≡ 1 mod m` in the local
field `L_q`, then `N_{L_q/K_Q}(u) ≡ 1 mod m` in `K_Q`.

This is the elementary fact that the norm (the product of the conjugates) of `1 + m·y` is
`1 + m·(an integral element)`; the reference level is the *integer* `m`, so no estimate on
ramification indices is needed. -/
private theorem val_localNormFinite_sub_one_le
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (m : ℕ)
    (u : (q.adicCompletion L)ˣ)
    (hu : Valued.v (R := q.adicCompletion L) (Γ₀ := NuvValGroup) ((u : q.adicCompletion L) - 1) ≤
      Valued.v (R := q.adicCompletion L) (Γ₀ := NuvValGroup) (((m : ℕ) : q.adicCompletion L))) :
    Valued.v (R := Q.adicCompletion K) (Γ₀ := NuvValGroup)
        (((Place.localNormFinite q Q hq u : (Q.adicCompletion K)ˣ) : Q.adicCompletion K) - 1) ≤
      Valued.v (R := Q.adicCompletion K) (Γ₀ := NuvValGroup) (((m : ℕ) : Q.adicCompletion K)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  haveI hfd : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hgal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion Q q hq
  -- the ramification exponent
  set e : ℕ := q.asIdeal.ramificationIdx (𝓞 K) with he
  -- the integer `m` in the two completions
  set mK : Q.adicCompletion K := ((m : ℕ) : Q.adicCompletion K) with hmK
  set mL : q.adicCompletion L := ((m : ℕ) : q.adicCompletion L) with hmL
  have hmL_eq : mL = algebraMap (Q.adicCompletion K) (q.adicCompletion L) mK := by
    simp [mL, mK]
  -- the valuation of the image of an element of the base field
  have hpow : ∀ z : Q.adicCompletion K,
      Valued.v (R := q.adicCompletion L) (Γ₀ := NuvValGroup)
          (algebraMap (Q.adicCompletion K) (q.adicCompletion L) z) =
        (Valued.v (R := Q.adicCompletion K) (Γ₀ := NuvValGroup) z) ^ e := by
    intro z
    rw [RingHom.algebraMap_toAlgebra, he]
    exact Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow Q q hq z
  have hu' : Valued.v (R := q.adicCompletion L) (Γ₀ := NuvValGroup)
      ((u : q.adicCompletion L) - 1) ≤ Valued.v (R := q.adicCompletion L) (Γ₀ := NuvValGroup) mL := by
    rw [hmL]; exact hu
  have hδ1 : Valued.v (R := q.adicCompletion L) (Γ₀ := NuvValGroup) mL ≤ 1 := by
    rw [hmL]
    exact NK.CFTLib.Arl.val_natCast_le_one (K := L) q m
  -- every conjugate of `u` is `≡ 1 mod m`
  have hσ : ∀ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L,
      Valued.v (R := q.adicCompletion L) (Γ₀ := NuvValGroup) (σ (u : q.adicCompletion L) - 1) ≤
        Valued.v (R := q.adicCompletion L) (Γ₀ := NuvValGroup) mL := by
    intro σ
    have h1 : σ ((u : q.adicCompletion L) - 1) = σ (u : q.adicCompletion L) - 1 := by
      rw [map_sub, map_one]
    rw [← h1,
      Commons.NumberTheory.NumberField.Completion.val_algEquiv_adicCompletion Q q hq σ
        ((u : q.adicCompletion L) - 1)]
    exact hu'
  -- the product over the Galois group
  have hprod : Valued.v (R := q.adicCompletion L) (Γ₀ := NuvValGroup)
      ((∏ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L,
        σ (u : q.adicCompletion L)) - 1) ≤
      Valued.v (R := q.adicCompletion L) (Γ₀ := NuvValGroup) mL :=
    val_prod_sub_one_le (v := Valued.v (R := q.adicCompletion L) (Γ₀ := NuvValGroup))
      Finset.univ _ hδ1 (fun σ _ => hσ σ)
  -- the product is the norm
  have hnorm : (∏ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L,
        σ (u : q.adicCompletion L)) =
      algebraMap (Q.adicCompletion K) (q.adicCompletion L)
        (Algebra.norm (Q.adicCompletion K) (u : q.adicCompletion L)) :=
    (Algebra.norm_eq_prod_automorphisms (Q.adicCompletion K) (u : q.adicCompletion L)).symm
  have hA : Valued.v (R := q.adicCompletion L) (Γ₀ := NuvValGroup)
      (algebraMap (Q.adicCompletion K) (q.adicCompletion L)
        (Algebra.norm (Q.adicCompletion K) (u : q.adicCompletion L)) - 1) ≤
      Valued.v (R := q.adicCompletion L) (Γ₀ := NuvValGroup) mL := by
    rw [← hnorm]
    exact hprod
  -- descend to the base field
  have hB : (Valued.v (R := Q.adicCompletion K) (Γ₀ := NuvValGroup)
        (Algebra.norm (Q.adicCompletion K) (u : q.adicCompletion L) - 1)) ^ e ≤
      (Valued.v (R := Q.adicCompletion K) (Γ₀ := NuvValGroup) mK) ^ e := by
    rw [← hpow (Algebra.norm (Q.adicCompletion K) (u : q.adicCompletion L) - 1), ← hpow mK,
      ← hmL_eq, map_sub, map_one]
    exact hA
  have he_ne : e ≠ 0 := by
    rw [he]
    exact (Ideal.ramificationIdx_pos (q := q.asIdeal) (𝓞 K)).ne'
  have hfin : Valued.v (R := Q.adicCompletion K) (Γ₀ := NuvValGroup)
      (Algebra.norm (Q.adicCompletion K) (u : q.adicCompletion L) - 1) ≤
      Valued.v (R := Q.adicCompletion K) (Γ₀ := NuvValGroup) mK :=
    (pow_le_pow_iff_left₀ zero_le zero_le he_ne).mp hB
  have hcoe : (((Place.localNormFinite q Q hq u : (Q.adicCompletion K)ˣ) : Q.adicCompletion K)) =
      Algebra.norm (Q.adicCompletion K) (u : q.adicCompletion L) := by
    rw [Place.localNormFinite, Units.coe_map]
  rw [hcoe]
  exact hfin

end LocalNormFinite

/-! ## Positivity at the archimedean places -/

section Positivity

variable {w : InfinitePlace K}

/-- `PosAtReal` is preserved by finite products of units. -/
private lemma posAtReal_finsetProd {ι : Type*} (s : Finset ι) (f : ι → w.Completionˣ)
    (hf : ∀ i ∈ s, NK.CFTLib.Arl.PosAtReal w (f i)) :
    NK.CFTLib.Arl.PosAtReal w (∏ i ∈ s, f i) := by
  intro hw
  rw [Units.coe_prod, map_prod]
  exact Finset.prod_pos fun i hi => hf i hi hw

/-- The norm `Units.map (Algebra.norm v.Completion)` at an infinite place sends positive units to
positive units. -/
private lemma posAtReal_unitsMap_norm {v : InfinitePlace K} {w : InfinitePlace L}
    [hw : w.LiesOver v] (x : w.Completionˣ) (hx : NK.CFTLib.Arl.PosAtReal w x) :
    NK.CFTLib.Arl.PosAtReal v
      (Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion) x) := by
  intro hv
  rw [Units.coe_map]
  rcases InfinitePlace.isReal_or_isComplex w with hwR | hwC
  · rw [NK.GlobalCFTdeep.NormIndex.localNormInfinite_norm_eq_real_real (K := K) (L := L)
      (v := v) (w := w) hv hwR (x : w.Completion)]
    exact hx hwR
  · rw [NK.GlobalCFTdeep.NormIndex.localNormInfinite_norm_eq_real_complex (K := K) (L := L)
      (v := v) (w := w) hv hwC (x : w.Completion)]
    refine (Complex.normSq_pos).mpr fun h0 => ?_
    exact Units.ne_zero x
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hwC).injective
        (by rw [h0, map_zero]))

/-- The local norm at an infinite place of a positive unit is positive. -/
private lemma posAtReal_localNormInfinite {v : InfinitePlace K} {w : InfinitePlace L}
    [hw : w.LiesOver v] (x : w.Completionˣ) (hx : NK.CFTLib.Arl.PosAtReal w x) :
    NK.CFTLib.Arl.PosAtReal v (Place.localNormInfinite w v x) :=
  posAtReal_unitsMap_norm x hx

/-- The archimedean component of the idèlic norm: if every infinite component of `u` is positive
(real) then so is every infinite component of `N_{L/K} u`. -/
private theorem posAtReal_normIdeleHom {u : Idele L}
    (hpos : ∀ w' : InfinitePlace L, NK.CFTLib.Arl.PosAtReal w' (u (Place.ofInfinite w')))
    (w : InfinitePlace K) :
    NK.CFTLib.Arl.PosAtReal w (Idele.normIdeleHom K L u (Place.ofInfinite w)) := by
  rw [Idele.normIdeleHom_apply, Idele.normIdeleFun_ofInfinite]
  refine posAtReal_finsetProd _ _ ?_
  intro w' _
  haveI : (w'.1 : InfinitePlace L).LiesOver w :=
    (Place.mem_fiberInfinite (K := K) (L := L) (v := w) (w := w'.1)).mp w'.2
  exact posAtReal_localNormInfinite _ (hpos w'.1)

end Positivity

/-! ## The two componentwise statements for the idèlic norm -/

section Components

/-- The congruence component of the idèlic norm: if every finite component of `u` is `≡ 1 mod m`
then so is every finite component of `N_{L/K} u`. -/
private theorem val_normIdeleHom_congr {m : ℕ} {u : Idele L}
    (hcong : ∀ q' : HeightOneSpectrum (𝓞 L), (m : 𝓞 L) ∈ q'.asIdeal →
      Valued.v (R := q'.adicCompletion L) (Γ₀ := NuvValGroup)
        (((u (Place.ofFinite q') : (q'.adicCompletion L)ˣ) : q'.adicCompletion L) - 1) ≤
      Valued.v (R := q'.adicCompletion L) (Γ₀ := NuvValGroup) (((m : ℕ) : q'.adicCompletion L)))
    (𝔭 : HeightOneSpectrum (𝓞 K)) (h𝔭 : (m : 𝓞 K) ∈ 𝔭.asIdeal) :
    Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := NuvValGroup)
      (((Idele.normIdeleHom K L u (Place.ofFinite 𝔭) : (𝔭.adicCompletion K)ˣ) :
        𝔭.adicCompletion K) - 1) ≤
      Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := NuvValGroup)
        (((m : ℕ) : 𝔭.adicCompletion K)) := by
  rw [Idele.normIdeleHom_apply, Idele.normIdeleFun_ofFinite]
  refine val_prod_units_sub_one_le (v := Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := NuvValGroup))
    _ _ (NK.CFTLib.Arl.val_natCast_le_one (K := K) 𝔭 m) ?_
  intro q' _
  have hq' : q'.1.asIdeal.LiesOver 𝔭.asIdeal :=
    (Place.mem_primesOverFinite (K := K) (L := L) (Q := 𝔭) (q := q'.1)).mp q'.2
  have hmq' : (m : 𝓞 L) ∈ q'.1.asIdeal := by
    haveI : q'.1.asIdeal.LiesOver 𝔭.asIdeal := hq'
    rw [← map_natCast (algebraMap (𝓞 K) (𝓞 L)) m]
    exact (Ideal.mem_of_liesOver q'.1.asIdeal 𝔭.asIdeal (m : 𝓞 K)).mp h𝔭
  exact val_localNormFinite_sub_one_le 𝔭 q'.1 hq' m (u (Place.ofFinite q'.1)) (hcong q'.1 hmq')

end Components

theorem normAdjustment {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (m : ℕ) (hm : 0 < m)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K, (m : NumberField.RingOfIntegers K) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1)
    (U : Subgroup (NK.GlobalCFT.Idele K)) (hU : NK.CFTLib.Arl.IsCongruenceSubgroup m U) :
    ∀ y : NK.GlobalCFT.Idele L, ∃ d : Lˣ,
      NK.GlobalCFT.Idele.normIdeleHom K L
        (y * NK.GlobalCFT.Idele.principalIdele L d) ∈ U := by
  classical
  intro y
  obtain ⟨V, hV, hadj⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust L m hm
  obtain ⟨d, hd⟩ := hadj y
  refine ⟨d, ?_⟩
  set u : Idele L := y * Idele.principalIdele L d with hudef
  have hpair := (hV.1 u).mp hd
  have hcong : ∀ q' : HeightOneSpectrum (𝓞 L), (m : 𝓞 L) ∈ q'.asIdeal →
      Valued.v (R := q'.adicCompletion L) (Γ₀ := NuvValGroup)
        (((u (Place.ofFinite q') : (q'.adicCompletion L)ˣ) : q'.adicCompletion L) - 1) ≤
      Valued.v (R := q'.adicCompletion L) (Γ₀ := NuvValGroup) (((m : ℕ) : q'.adicCompletion L)) :=
    fun q' hq' => hpair.1 q' hq'
  have hpos : ∀ w' : InfinitePlace L, NK.CFTLib.Arl.PosAtReal w' (u (Place.ofInfinite w')) :=
    fun w' => hpair.2 w'
  refine (hU.1 _).mpr ⟨fun 𝔭 h𝔭 => val_normIdeleHom_congr hcong 𝔭 h𝔭,
    fun w => posAtReal_normIdeleHom hpos w⟩

end NK.NUV2.ARL
