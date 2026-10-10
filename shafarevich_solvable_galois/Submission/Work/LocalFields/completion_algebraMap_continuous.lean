import Mathlib.RingTheory.Henselian
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Submission.Work.LocalFields.LocalFieldAPI
import Submission.Work.LocalFields.exists_pow_eq_of_one_sub_lt_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Continuity of the structure map `K_v →+* L_w` of any compatible `K_v`-algebra structure

The main result of this file is `Work.LocalFields.completion_algebraMap_continuous`: for number
fields `K ⊆ L` with `L/K` finite Galois, a finite prime `w` of `L` lying over `v` of `K`, and any
`K_v`-algebra structure on `L_w` compatible with the inclusion `K ⊆ L` (i.e. satisfying the
`IsScalarTower K K_v L_w` condition), the structure map `σ : K_v →+* L_w` is continuous.

The proof does not use any uniqueness theorem for valuations on local fields.  Instead it uses the
rigidity of local fields under `n`-th powers
(`Work.LocalFields.exists_pow_eq_of_one_sub_lt_one`): every principal unit of `K_v` is an `n`-th
power for every `n` coprime to the residue characteristic.  This forces `σ` to send principal
units and units of `𝒪_{K_v}` to units of `𝒪_{L_w}`; combined with the explicit relation
`w (σ y) = (v y) ^ e` on the dense subfield `K` (`e = e(w/v)` the ramification index) this
determines `w ∘ σ` on all of `K_v` and gives continuity.
-/

namespace Work.LocalFields

open scoped NumberField Valued WithZero

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : Work.LocalFields.FinitePrime K) (w : Work.LocalFields.FinitePrime L)
  [hw : w.asIdeal.LiesOver v.asIdeal]
  [φ : Algebra (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)]
  [IsScalarTower K (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)]

set_option linter.unusedSectionVars false

/-! ## Elementary facts about the value group `ℤᵐ⁰` -/

/-- Powers of an element of `ℤᵐ⁰` are computed by `WithZero.log`/`WithZero.exp`. -/
lemma compAlgMap_withZero_log_pow (a : ℤᵐ⁰) (ha : a ≠ 0) (n : ℕ) :
    WithZero.log (a ^ n) = n * WithZero.log a := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, WithZero.log_mul (pow_ne_zero k ha) ha, ih, Nat.cast_succ]
    ring

/-- `(exp(-1))^n = exp(-n)` for natural `n`. -/
lemma compAlgMap_exp_neg_one_pow (n : ℕ) :
    (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) ^ n = WithZero.exp (-(n : ℤ)) := by
  rw [← WithZero.exp_nsmul]; congr 1; simp

/-- `(exp(-1))^n = exp(-n)` for integral `n`. -/
lemma compAlgMap_exp_neg_one_zpow (n : ℤ) :
    (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) ^ n = WithZero.exp (-n) := by
  rw [← WithZero.exp_zsmul]; congr 1; simp

/-- `(exp k)^n = exp (n k)` for integral `k` and `n`. -/
lemma compAlgMap_exp_int_zpow (k n : ℤ) :
    (WithZero.exp k : ℤᵐ⁰) ^ n = WithZero.exp (n * k) := by
  rw [← WithZero.exp_zsmul]; congr 1

/-- For every nonzero `C : ℤᵐ⁰` and every `e ≠ 0` there is a nonzero `A : ℤᵐ⁰` with
`A ^ e < C`. -/
lemma compAlgMap_exists_small_radius (e : ℕ) (he : e ≠ 0) {C : ℤᵐ⁰} (hC : C ≠ 0) :
    ∃ A : ℤᵐ⁰, A ≠ 0 ∧ A ^ e < C := by
  refine ⟨WithZero.exp (min (WithZero.log C) 0 - 1), WithZero.exp_pos.ne', ?_⟩
  have hkey : (e : ℤ) * (min (WithZero.log C) 0 - 1) < WithZero.log C := by
    have h1 : min (WithZero.log C) 0 - 1 ≤ 0 := by omega
    have h2 : (1 : ℤ) ≤ (e : ℤ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr he
    have h3 : min (WithZero.log C) 0 - 1 < WithZero.log C := by omega
    nlinarith [h1, h2, h3]
  calc WithZero.exp (min (WithZero.log C) 0 - 1) ^ e
      = WithZero.exp ((e : ℤ) * (min (WithZero.log C) 0 - 1)) := by
        rw [← WithZero.exp_nsmul, nsmul_eq_mul]
    _ < C := by
        rw [← WithZero.exp_log hC, WithZero.exp_lt_exp]
        simpa using hkey

/-! ## The structure map `σ = φ.algebraMap` -/

/-- `σ = φ.algebraMap` is injective: it is a ring homomorphism from a field. -/
lemma compAlgMap_injective :
    Function.Injective (φ.algebraMap : Completion K v → Completion L w) := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  by_contra hx0
  exact (IsUnit.ne_zero (IsUnit.map (φ.algebraMap) (IsUnit.mk0 x hx0))) hx

/-- **The `e`-th power relation on `K`.**  For `y : K`, the `w`-adic valuation of
`σ y = algebraMap K L_w y` is the `e`-th power of the `v`-adic valuation of `y`, where
`e = e(w/v)` is the ramification index. -/
lemma compAlgMap_val_algebraMap (y : K) :
    Valued.v (R := Completion L w) (φ.algebraMap (algebraMap K (Completion K v) y))
      = (Valued.v (R := Completion K v) (algebraMap K (Completion K v) y))
          ^ (v.asIdeal.ramificationIdx' w.asIdeal) := by
  have h1 : algebraMap K (Completion L w) y
      = algebraMap L (Completion L w) (algebraMap K L y) :=
    IsScalarTower.algebraMap_apply K L (Completion L w) y
  rw [← IsScalarTower.algebraMap_apply K (Completion K v) (Completion L w) y, h1]
  have h2 : Valued.v (R := Completion L w) (algebraMap L (Completion L w) (algebraMap K L y))
      = (IsDedekindDomain.HeightOneSpectrum.valuation L w) (algebraMap K L y) := by
    rw [show algebraMap L (Completion L w) (algebraMap K L y)
          = ((algebraMap K L y : L) : Completion L w) from by
      rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]; rfl]
    rw [IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe]
  rw [h2, ← IsDedekindDomain.HeightOneSpectrum.valuation_liesOver L v w y]
  congr 1
  · rw [show algebraMap K (Completion K v) y = (y : Completion K v) from by
      rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]; rfl]
    rw [IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe]
  all_goals (haveI := w.isPrime
             exact (Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot).symm)

/-- **Principal units map to units.**  If `t` lies in the maximal ideal of `𝒪_{K_v}`, then
`σ (1 + t)` is a unit of `𝒪_{L_w}`.

The proof is the `n`-th power rigidity: `1 + t` is an `n`-th power in `K_v` for every `n` coprime
to the residue characteristic, so its image under `σ` has value group element which is an `n`-th
power in the ordered group `ℤᵐ⁰^×` for all such `n`; hence it is `1`. -/
lemma compAlgMap_val_one_add_of_lt_one {t : Completion K v} (ht : Valued.v t < 1) :
    Valued.v (R := Completion L w) (φ.algebraMap (1 + t)) = 1 := by
  set p := ringChar (𝓀[Completion K v]) with hp_def
  have hp : Nat.Prime p := CharP.prime_ringChar _
  have hp1 : 1 < p + 1 := by have h := hp.one_lt; omega
  have hcop : Nat.Coprime (p + 1) p := by
    rw [Nat.coprime_comm, Nat.coprime_self_add_right]; exact Nat.coprime_one_right p
  have h1t : Valued.v (R := Completion K v) (1 + t) = 1 := by
    have := Valuation.map_add_eq_of_lt_left (Valued.v (R := Completion K v)) (x := 1) (y := t)
      (by simpa using ht)
    simpa using this
  have h1t_ne : (1 + t : Completion K v) ≠ 0 := by
    intro h; rw [h, map_zero] at h1t; exact one_ne_zero h1t.symm
  have hW_ne : Valued.v (R := Completion L w) (φ.algebraMap (1 + t)) ≠ 0 := by
    intro h
    rw [Valuation.zero_iff] at h
    exact h1t_ne (compAlgMap_injective v w (h.trans (map_zero _).symm))
  set A := WithZero.log (Valued.v (R := Completion L w) (φ.algebraMap (1 + t))) with hA_def
  have hA : A = 0 := by
    by_contra hA0
    obtain ⟨k, hk⟩ : ∃ k : ℕ, A.natAbs < (p+1)^k := ⟨A.natAbs, Nat.lt_pow_self hp1⟩
    have hn : Nat.Coprime ((p+1)^k) (ringChar (𝓀[Completion K v])) := by
      rw [← hp_def]; simpa using Nat.Coprime.pow k 1 hcop
    obtain ⟨y, hy⟩ := exists_pow_eq_of_one_sub_lt_one (k := Completion K v) hn
      (x := 1 + t) (by simpa using ht)
    have hn0 : (p+1)^k ≠ 0 := by positivity
    have hy_ne : y ≠ 0 := by
      intro h; rw [h, zero_pow hn0] at hy; exact h1t_ne hy.symm
    have hWy_ne : Valued.v (R := Completion L w) (φ.algebraMap y) ≠ 0 := by
      intro h; rw [Valuation.zero_iff] at h
      exact hy_ne (compAlgMap_injective v w (h.trans (map_zero _).symm))
    have hAeq : A = (((p+1)^k : ℕ) : ℤ) *
        WithZero.log (Valued.v (R := Completion L w) (φ.algebraMap y)) := by
      have h1 : φ.algebraMap (1 + t) = (φ.algebraMap y) ^ ((p+1)^k) := by rw [← hy, map_pow]
      rw [hA_def, h1, map_pow, compAlgMap_withZero_log_pow _ hWy_ne]
    have hdvd : (((p+1)^k : ℕ) : ℤ) ∣ A := ⟨_, hAeq⟩
    obtain ⟨c, hc⟩ := hdvd
    have hc0 : c ≠ 0 := by rintro rfl; simp at hc; exact hA0 hc
    have hnat : A.natAbs = (p+1)^k * c.natAbs := by
      rw [hc, Int.natAbs_mul, Int.natAbs_natCast]
    have hle : (p+1)^k ≤ A.natAbs := by
      rw [hnat]; exact Nat.le_mul_of_pos_right _ (Int.natAbs_pos.mpr hc0)
    omega
  have : Valued.v (R := Completion L w) (φ.algebraMap (1 + t)) = WithZero.exp A := by
    rw [hA_def, WithZero.exp_log hW_ne]
  rw [this, hA, WithZero.exp_zero]

/-- **Units of `𝒪_{K_v}` map to units of `𝒪_{L_w}`.** -/
lemma compAlgMap_val_of_val_eq_one {u : Completion K v} (hu : Valued.v u = 1) :
    Valued.v (R := Completion L w) (φ.algebraMap u) = 1 := by
  set u₀ : 𝒪[Completion K v] := ⟨u, le_of_eq hu⟩ with hu₀
  have hunit : IsUnit u₀ := by
    rw [(Valuation.integer.integers (Valued.v (R := Completion K v))).isUnit_iff_valuation_eq_one]
    exact hu
  set q := Fintype.card (𝓀[Completion K v]) with hq
  have hq2 : 2 ≤ q := by
    have h := IsLocalField.one_lt_card_residueField (k := Completion K v)
    rw [Nat.card_eq_fintype_card] at h
    exact h
  have hres_ne : IsLocalRing.residue (𝒪[Completion K v]) u₀ ≠ 0 :=
    IsUnit.ne_zero (IsUnit.map _ hunit)
  have hpoweq : (IsLocalRing.residue (𝒪[Completion K v]) u₀) ^ (q - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one _ hres_ne
  have hmem : u₀ ^ (q - 1) - 1 ∈ 𝓂[Completion K v] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_one, map_pow, hpoweq, sub_self]
  have hcoe : ((u₀ ^ (q - 1) - 1 : 𝒪[Completion K v]) : Completion K v) = u ^ (q - 1) - 1 := by
    push_cast; rfl
  have hlt : Valued.v (R := Completion K v) (u ^ (q - 1) - 1) < 1 := by
    rw [← hcoe]; exact (mem_maximalIdeal_iff_v_lt_one).mp hmem
  have hkey := compAlgMap_val_one_add_of_lt_one v w (t := u ^ (q - 1) - 1) hlt
  have hsplit : φ.algebraMap u ^ (q - 1) = φ.algebraMap (1 + (u ^ (q - 1) - 1)) := by
    simp only [map_add, map_sub, map_pow, map_one]
    ring
  rw [← hsplit, map_pow] at hkey
  have hq1 : q - 1 ≠ 0 := by omega
  have hfin : (Valued.v (R := Completion L w) (φ.algebraMap u)) ^ (q - 1) = 1 ^ (q - 1) := by
    rw [hkey, one_pow]
  exact (pow_left_inj₀ (a := Valued.v (R := Completion L w) (φ.algebraMap u)) (b := 1)
    (zero_le) (zero_le) hq1).mp hfin

/-- **The value of `σ` is the `e`-th power of the `v`-adic valuation, everywhere on `K_v`.**

Writing `x = γ₀^{-log v x} · y` with a `K`-element `γ₀` of value `exp(-1)` reduces this to the unit
case (`compAlgMap_val_of_val_eq_one`) and the relation on `K` (`compAlgMap_val_algebraMap`). -/
lemma compAlgMap_val_eq_pow (x : Completion K v) :
    Valued.v (R := Completion L w) (φ.algebraMap x)
      = (Valued.v (R := Completion K v) x) ^ (v.asIdeal.ramificationIdx' w.asIdeal) := by
  set e := v.asIdeal.ramificationIdx' w.asIdeal with he_def
  have he : e ≠ 0 := by
    rw [he_def]
    exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver (S := 𝓞 L)
      w.asIdeal v.ne_bot
  rcases eq_or_ne x 0 with rfl | hx
  · simp [zero_pow he]
  · obtain ⟨γ, hγ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_surjective K v
      (WithZero.exp (-1 : ℤ))
    set γ₀ : Completion K v := algebraMap K (Completion K v) γ with hγ₀_def
    have hVγ₀ : Valued.v (R := Completion K v) γ₀ = WithZero.exp (-1 : ℤ) := by
      rw [hγ₀_def]
      rw [show algebraMap K (Completion K v) γ = (γ : Completion K v) from by
        rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]; rfl]
      rw [IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe]
      exact hγ
    have hxV : Valued.v (R := Completion K v) x ≠ 0 :=
      fun h => hx ((Valuation.zero_iff (Valued.v (R := Completion K v))).mp h)
    set a : ℤ := WithZero.log (Valued.v (R := Completion K v) x) with ha_def
    have hVx : Valued.v (R := Completion K v) x = WithZero.exp a := by
      rw [ha_def, WithZero.exp_log hxV]
    set y : Completion K v := x * γ₀ ^ a with hy_def
    have hVy : Valued.v (R := Completion K v) y = 1 := by
      rw [hy_def, map_mul, map_zpow₀, hVγ₀, compAlgMap_exp_neg_one_zpow, hVx,
        ← WithZero.exp_add]
      simp
    have hWy : Valued.v (R := Completion L w) (φ.algebraMap y) = 1 :=
      compAlgMap_val_of_val_eq_one v w hVy
    have hσγ₀ : Valued.v (R := Completion L w) (φ.algebraMap γ₀) = WithZero.exp (-(e : ℤ)) := by
      rw [hγ₀_def, compAlgMap_val_algebraMap v w γ, hVγ₀, compAlgMap_exp_neg_one_pow]
    have hchain : Valued.v (R := Completion L w) (φ.algebraMap x)
        * (WithZero.exp (-(e : ℤ))) ^ a = 1 := by
      have h1 : φ.algebraMap y = φ.algebraMap x * (φ.algebraMap γ₀) ^ a := by
        rw [hy_def, map_mul, map_zpow₀]
      rw [← hWy, h1, map_mul, map_zpow₀, hσγ₀]
    have hWσx : Valued.v (R := Completion L w) (φ.algebraMap x)
        = WithZero.exp (a * (e : ℤ)) := by
      rw [eq_inv_of_mul_eq_one_left hchain, compAlgMap_exp_int_zpow, ← WithZero.exp_neg]
      congr 1
      ring
    rw [hWσx, hVx, ← WithZero.exp_nsmul]
    congr 1
    rw [nsmul_eq_mul]; ring

/-! ## The main theorem -/

/-- **The structure map `K_v →+* L_w` of any `K_v`-algebra structure on `L_w` compatible with
`K ⊆ L` is continuous.**  (The `IsScalarTower` hypothesis makes this a statement about `φ`.)

This is the technical heart of `Work.LocalFields.completion_algebra_range_eq`: applied to
`σ := φ.algebraMap` it yields `σ = CompletionHom.ringHom v w` because both are continuous and
agree on the image of `K`, which is dense in `K_v`.

Proof route: let `σ := φ.algebraMap` and `R := σ⁻¹(𝒪_{L_w})`.  By
`Work.LocalFields.completion_algebraMap_mem_intRing`, `𝒪_{K_v} ⊆ R`; since `𝒪_{K_v}` is a DVR
(Krull dimension one) and `R ≠ ⊤` (take `λ ∈ K` with `v(λ) > 1`; then `σ(λ) = ρ(λ)` has
`w`-adic valuation `> 1`), `R = 𝒪_{K_v}`.  Hence `σ(𝒪_{K_v}) ⊆ 𝒪_{L_w}`, and `σ(𝔪_{K_v}) ⊆
𝔪_{L_w}`: if `π` is a uniformizer of `K_v` and `σ(π)` were a unit then `σ(π)⁻¹ = σ(π⁻¹) ∈
𝒪_{L_w}`, so `π⁻¹ ∈ R = 𝒪_{K_v}`, contradicting `v(π⁻¹) > 1`.  Thus
`σ(𝔪_{K_v}^n) ⊆ 𝔪_{L_w}^n` for all `n`, i.e. `σ` is continuous at `0`, hence continuous. -/
theorem completion_algebraMap_continuous {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : Work.LocalFields.FinitePrime K) (w : Work.LocalFields.FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal]
    [φ : Algebra (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)]
    [IsScalarTower K (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)] :
    Continuous (φ.algebraMap) := by
  refine continuous_of_continuousAt_zero (φ.algebraMap) ?_
  rw [ContinuousAt, map_zero, Filter.tendsto_def]
  intro s hs
  rw [Valued.mem_nhds_zero] at hs
  obtain ⟨γ', hγ'⟩ := hs
  rw [Valued.mem_nhds_zero]
  set e := v.asIdeal.ramificationIdx' w.asIdeal with he_def
  have he : e ≠ 0 := by
    rw [he_def]
    exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver (S := 𝓞 L)
      w.asIdeal v.ne_bot
  set C : ℤᵐ⁰ := MonoidWithZeroHom.ValueGroup₀.embedding γ'.1 with hC_def
  have hC : C ≠ 0 := by
    rw [hC_def]
    exact fun h => (Units.ne_zero γ')
      (MonoidWithZeroHom.ValueGroup₀.embedding_injective (by rw [h, map_zero]))
  obtain ⟨A, hA0, hAlt⟩ := compAlgMap_exists_small_radius e he hC
  obtain ⟨x₀, hx₀⟩ := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective K v A
  have hE : MonoidWithZeroHom.ValueGroup₀.embedding
      ((Valued.v (R := Completion K v)).restrict x₀) = A := by
    rw [Valuation.embedding_restrict, hx₀]
  refine ⟨Units.mk0 ((Valued.v (R := Completion K v)).restrict x₀)
    (fun h => hA0 (by rw [← hE, h, map_zero])), ?_⟩
  intro x hx
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hx
  rw [Valuation.restrict_lt_iff_lt_embedding] at hx
  rw [hE] at hx
  apply hγ'
  simp only [Set.mem_ofPred_eq]
  rw [Valuation.restrict_lt_iff_lt_embedding, ← hC_def]
  rw [compAlgMap_val_eq_pow v w x]
  exact lt_of_le_of_lt (pow_le_pow_left₀ (zero_le) (le_of_lt hx) e) hAlt

end Work.LocalFields
