import Mathlib
import Submission.NK.CFTLib.ArtinReciprocityIdeal.LangDefs
import Submission.NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFTdeep.NormIndex.localNorm_finiteIndex_archimedean
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow
import Submission.Commons.NumberTheory.NumberField.Completion.val_norm_adicCompletion_eq_pow

/-!
# Norming the principal ray down

`NK.CFTLib.ArtinReciprocityIdeal.norm_principalRay_le`: if `E/K` is a finite Galois extension of
number fields, `m ∣ m'` and `β ∈ Eˣ` is `≡ 1 mod* m'`, then `N_{E/K}(β) ≡ 1 mod* m`, so that the
principal ideal `(N_{E/K}(β))` lies in the principal ray `P(m)`.

The proof has two halves.

* *Finite places.*  Using `normIdeleHom_principalIdele`, the principal idèle of `Nβ` is the idèlic
  norm of the principal idèle of `β`, and its component at a prime `𝔭` of `K` is the product
  `∏_{𝔮 | 𝔭} N_{E_𝔮/K_𝔭}(β)` of the local norms.  Each factor is `≡ 1 mod m` because the local norm
  of a principal unit is a principal unit
  (`val_localNormFinite_sub_one_le`: the norm of `1 + x` is the product of the conjugates, and every
  `K_𝔭`-automorphism of `E_𝔮` preserves the valuation), and a product of `≡ 1 mod m` units is
  `≡ 1 mod m` (`val_prod_units_sub_one_le`).
* *Archimedean places.*  At a real place `w` of `K`, the value of `Nβ` is the product of the local
  norms at the places `w' | w`: those are either the (positive) real value of `β` at `w'`, or
  `‖β‖²` in the real/complex case, so the product is positive (`posAtReal_normIdeleHom`).

Both halves are restated in the vocabulary `CongrOne` of `LangDefs.lean` as the auxiliary statement
`norm_congrOne`, and the passage from the modulus `m'` to the modulus `m` is
`congrOne_of_dvd`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

open scoped NumberField nonZeroDivisors WithZero NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.ArtinReciprocityIdeal

open NK.GlobalCFT

/-- The value group `ℤᵐ⁰ = WithZero (Multiplicative ℤ)` of the adic valuations. -/
abbrev NormRayValGroup : Type := WithZero (Multiplicative ℤ)

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Valuation arithmetic in the value group -/

section ValuationCalc

variable {F : Type*} [Field F] {v : Valuation F NormRayValGroup}

/-- The set `{x | v (x - 1) ≤ δ}` is closed under multiplication, for `δ ≤ 1`. -/
private lemma val_mul_sub_one_le {x y : F} {δ : NormRayValGroup} (hδ : δ ≤ 1)
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
private lemma val_prod_sub_one_le {ι : Type*} (s : Finset ι) (f : ι → F) {δ : NormRayValGroup}
    (hδ : δ ≤ 1) (hf : ∀ i ∈ s, v (f i - 1) ≤ δ) : v ((∏ i ∈ s, f i) - 1) ≤ δ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t hat ih =>
      rw [Finset.prod_insert hat]
      exact val_mul_sub_one_le hδ (hf a (Finset.mem_insert_self a t))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- The same for finite products of units. -/
private lemma val_prod_units_sub_one_le {ι : Type*} (s : Finset ι) (f : ι → Fˣ)
    {δ : NormRayValGroup} (hδ : δ ≤ 1) (hf : ∀ i ∈ s, v ((f i : F) - 1) ≤ δ) :
    v ((↑(∏ i ∈ s, f i) : F) - 1) ≤ δ := by
  rw [Units.coe_prod]
  exact val_prod_sub_one_le s (fun i => (f i : F)) hδ hf

end ValuationCalc

/-! ## The local norm at a finite place preserves the congruence `≡ 1 mod m` -/

section LocalNormFinite

/-- **The local norm of a principal unit is a principal unit.**  If `u ≡ 1 mod m` in the local
field `E_q`, then `N_{E_q/K_Q}(u) ≡ 1 mod m` in `K_Q`.

The norm `N(1 + x) = ∏_σ (1 + σ x)` is the product of the conjugates, and every `K_Q`-automorphism
`σ` of `E_q` preserves the `q`-adic valuation (`val_algEquiv_adicCompletion`), so each conjugate is
again `≡ 1 mod m`; the expansion of `∏_σ(1 + σx) - 1` as a sum of products of at least one
`σx` then bounds `N u - 1` by `m`.  Descending from `E_q` to `K_Q` multiplies valuations by the
ramification index `e`, and `u ↦ u^e` is injective on the value group. -/
private theorem val_localNormFinite_sub_one_le
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (m : ℕ) (u : (q.adicCompletion L)ˣ)
    (hu : Valued.v (R := q.adicCompletion L) (Γ₀ := NormRayValGroup)
        ((u : q.adicCompletion L) - 1) ≤
      Valued.v (R := q.adicCompletion L) (Γ₀ := NormRayValGroup)
        (((m : ℕ) : q.adicCompletion L))) :
    Valued.v (R := Q.adicCompletion K) (Γ₀ := NormRayValGroup)
        (((Place.localNormFinite q Q hq u : (Q.adicCompletion K)ˣ) : Q.adicCompletion K) - 1) ≤
      Valued.v (R := Q.adicCompletion K) (Γ₀ := NormRayValGroup)
        (((m : ℕ) : Q.adicCompletion K)) := by
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
      Valued.v (R := q.adicCompletion L) (Γ₀ := NormRayValGroup)
          (algebraMap (Q.adicCompletion K) (q.adicCompletion L) z) =
        (Valued.v (R := Q.adicCompletion K) (Γ₀ := NormRayValGroup) z) ^ e := by
    intro z
    rw [RingHom.algebraMap_toAlgebra, he]
    exact Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow Q q hq z
  have hu' : Valued.v (R := q.adicCompletion L) (Γ₀ := NormRayValGroup)
      ((u : q.adicCompletion L) - 1) ≤ Valued.v (R := q.adicCompletion L) (Γ₀ := NormRayValGroup) mL := by
    rw [hmL]; exact hu
  have hδ1 : Valued.v (R := q.adicCompletion L) (Γ₀ := NormRayValGroup) mL ≤ 1 := by
    rw [hmL]
    exact NK.CFTLib.Arl.val_natCast_le_one (K := L) q m
  -- every conjugate of `u` is `≡ 1 mod m`
  have hσ : ∀ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L,
      Valued.v (R := q.adicCompletion L) (Γ₀ := NormRayValGroup) (σ (u : q.adicCompletion L) - 1) ≤
        Valued.v (R := q.adicCompletion L) (Γ₀ := NormRayValGroup) mL := by
    intro σ
    have h1 : σ ((u : q.adicCompletion L) - 1) = σ (u : q.adicCompletion L) - 1 := by
      rw [map_sub, map_one]
    rw [← h1,
      Commons.NumberTheory.NumberField.Completion.val_algEquiv_adicCompletion Q q hq σ
        ((u : q.adicCompletion L) - 1)]
    exact hu'
  -- the product over the Galois group
  have hprod : Valued.v (R := q.adicCompletion L) (Γ₀ := NormRayValGroup)
      ((∏ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L,
        σ (u : q.adicCompletion L)) - 1) ≤
      Valued.v (R := q.adicCompletion L) (Γ₀ := NormRayValGroup) mL :=
    val_prod_sub_one_le (v := Valued.v (R := q.adicCompletion L) (Γ₀ := NormRayValGroup))
      Finset.univ _ hδ1 (fun σ _ => hσ σ)
  -- the product is the norm
  have hnorm : (∏ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L,
        σ (u : q.adicCompletion L)) =
      algebraMap (Q.adicCompletion K) (q.adicCompletion L)
        (Algebra.norm (Q.adicCompletion K) (u : q.adicCompletion L)) :=
    (Algebra.norm_eq_prod_automorphisms (Q.adicCompletion K) (u : q.adicCompletion L)).symm
  have hA : Valued.v (R := q.adicCompletion L) (Γ₀ := NormRayValGroup)
      (algebraMap (Q.adicCompletion K) (q.adicCompletion L)
        (Algebra.norm (Q.adicCompletion K) (u : q.adicCompletion L)) - 1) ≤
      Valued.v (R := q.adicCompletion L) (Γ₀ := NormRayValGroup) mL := by
    rw [← hnorm]
    exact hprod
  -- descend to the base field
  have hB : (Valued.v (R := Q.adicCompletion K) (Γ₀ := NormRayValGroup)
        (Algebra.norm (Q.adicCompletion K) (u : q.adicCompletion L) - 1)) ^ e ≤
      (Valued.v (R := Q.adicCompletion K) (Γ₀ := NormRayValGroup) mK) ^ e := by
    rw [← hpow (Algebra.norm (Q.adicCompletion K) (u : q.adicCompletion L) - 1), ← hpow mK,
      ← hmL_eq, map_sub, map_one]
    exact hA
  have he_ne : e ≠ 0 := by
    rw [he]
    exact (Ideal.ramificationIdx_pos (q := q.asIdeal) (𝓞 K)).ne'
  have hfin : Valued.v (R := Q.adicCompletion K) (Γ₀ := NormRayValGroup)
      (Algebra.norm (Q.adicCompletion K) (u : q.adicCompletion L) - 1) ≤
      Valued.v (R := Q.adicCompletion K) (Γ₀ := NormRayValGroup) mK :=
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
      Valued.v (R := q'.adicCompletion L) (Γ₀ := NormRayValGroup)
        (((u (Place.ofFinite q') : (q'.adicCompletion L)ˣ) : q'.adicCompletion L) - 1) ≤
      Valued.v (R := q'.adicCompletion L) (Γ₀ := NormRayValGroup) (((m : ℕ) : q'.adicCompletion L)))
    (𝔭 : HeightOneSpectrum (𝓞 K)) (h𝔭 : (m : 𝓞 K) ∈ 𝔭.asIdeal) :
    Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := NormRayValGroup)
      (((Idele.normIdeleHom K L u (Place.ofFinite 𝔭) : (𝔭.adicCompletion K)ˣ) :
        𝔭.adicCompletion K) - 1) ≤
      Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := NormRayValGroup)
        (((m : ℕ) : 𝔭.adicCompletion K)) := by
  rw [Idele.normIdeleHom_apply, Idele.normIdeleFun_ofFinite]
  refine val_prod_units_sub_one_le (v := Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := NormRayValGroup))
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

/-! ## The passage from the modulus `m'` to the modulus `m` -/

/-- **Monotonicity of the congruence condition in the modulus.**  If `a ≡ 1 mod* m'` and `m ∣ m'`,
then `a ≡ 1 mod* m`. -/
theorem congrOne_of_dvd {K : Type*} [Field K] [NumberField K] {m m' : ℕ} (hmm : m ∣ m')
    {a : Kˣ} (h : CongrOne (K := K) m' a) : CongrOne (K := K) m a := by
  obtain ⟨k, rfl⟩ := hmm
  refine ⟨fun 𝔭 h𝔭 => ?_, h.2⟩
  have hmk : ((m * k : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal := by
    have h2 : (k : 𝓞 K) * (m : 𝓞 K) ∈ 𝔭.asIdeal := Ideal.mul_mem_left 𝔭.asIdeal (k : 𝓞 K) h𝔭
    simpa only [Nat.cast_mul, mul_comm] using h2
  have hle : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (((m * k : ℕ) : 𝔭.adicCompletion K)) ≤
      Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (((m : ℕ) : 𝔭.adicCompletion K)) := by
    have h1 : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (((k : ℕ) : 𝔭.adicCompletion K)) ≤ 1 :=
      NK.CFTLib.Arl.val_natCast_le_one 𝔭 k
    rw [Nat.cast_mul, Valuation.map_mul]
    exact le_trans (mul_le_mul_of_nonneg_left h1 zero_le) (le_of_eq (mul_one _))
  exact (h.1 𝔭 hmk).trans hle

/-! ## The norm of a `CongrOne` unit is `CongrOne` -/

/-- **The norm of a unit congruent to `1` modulo `m` is again congruent to `1` modulo `m`.** -/
theorem norm_congrOne {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
    (m : ℕ) {β : Eˣ} (hβ : CongrOne (K := E) m β) :
    CongrOne (K := K) m (Units.map (Algebra.norm K) β) := by
  constructor
  · intro 𝔭 h𝔭
    have h := val_normIdeleHom_congr (K := K) (L := E) (m := m)
      (u := Idele.principalIdele E β) (fun q' hq' => by
        have hcomp : (((Idele.principalIdele E β) (Place.ofFinite q') :
            (q'.adicCompletion E)ˣ) : q'.adicCompletion E)
            = algebraMap E (q'.adicCompletion E) (β : E) := by
          rw [Idele.principalIdele_apply, Units.coe_map]
          rfl
        rw [hcomp]
        exact hβ.1 q' hq') 𝔭 h𝔭
    rw [Idele.normIdeleHom_principalIdele] at h
    exact h
  · intro w hw
    have h := posAtReal_normIdeleHom (K := K) (L := E) (u := Idele.principalIdele E β)
      (fun w' hw' => by
        have hcomp : (((Idele.principalIdele E β) (Place.ofInfinite w') :
            w'.Completionˣ) : w'.Completion) = algebraMap E w'.Completion (β : E) := by
          rw [Idele.principalIdele_apply, Units.coe_map]
          rfl
        rw [hcomp]
        exact hβ.2 w' hw') w
    rw [Idele.normIdeleHom_principalIdele] at h
    exact h hw

/-! ## Norming the principal ray down -/

/-- **Norming the principal ray down.**  Let `E/K` be a finite Galois extension of number fields
and `m ∣ m'` natural numbers.  If `β ∈ Eˣ` is `≡ 1 mod* m'` (`CongrOne m' β`: `β` is `1` modulo
`m'` at every prime dividing `(m')` and positive at every real place of `E`), then the principal
ideal of the norm `N_{E/K}(β)` lies in the principal ray `P(m)`: `(N_{E/K}(β)) ∈ principalRay K m`.

This is the "norming down" step of Lang's proof of the cyclic conductor theorem
(*Algebraic Number Theory*, Ch. X §2, p. 205): `N_{E/K}(β) ≡ 1 mod* m` because
`Nβ - 1 = ∏_σ σβ - 1 = Σ_{∅ ≠ S} ∏_{σ ∈ S} (σβ - 1)` is divisible by `m'` (each `σβ - 1` is
divisible by `m'` by Galois-invariance of `m'`), hence by `m`; and `Nβ` is positive at the real
places of `K` as a product of conjugates of a totally positive element. -/
theorem norm_principalRay_le {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
    (m m' : ℕ) (hmm : m ∣ m') {β : Eˣ} (hβ : CongrOne (K := E) m' β) :
    spanUnit (K := K) (Units.map (Algebra.norm K) β) ∈ principalRay K m :=
  Subgroup.subset_closure ⟨Units.map (Algebra.norm K) β,
    congrOne_of_dvd hmm (norm_congrOne (K := K) (E := E) m' hβ), rfl⟩

end NK.CFTLib.ArtinReciprocityIdeal
