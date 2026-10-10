import Mathlib.RingTheory.Henselian
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
import Submission.Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists
import Submission.Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing
import Submission.Commons.RingTheory.Henselian.valuation_completion_liesOver
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField WithZero NNReal WithZeroMulInt nonZeroDivisors BigOperators
open NumberField
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section

namespace Commons.NumberTheory.NumberField.Completion

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev AK (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) := Q.adicCompletionIntegers K
abbrev AL (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) := q.adicCompletionIntegers L
abbrev mAK (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : Ideal (AK Q) :=
  IsLocalRing.maximalIdeal (AK Q)
abbrev mAL (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) : Ideal (AL q) :=
  IsLocalRing.maximalIdeal (AL q)

noncomputable def intsMap (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    AK Q →+* AL q where
  toFun := fun x => ⟨Commons.RingTheory.Henselian.adicCompletionMap Q q hq (x : Q.adicCompletion K),
    (Commons.RingTheory.Henselian.adicCompletionMap_mem_integers Q q hq x.2)⟩
  map_one' := by ext; simp
  map_mul' := by intro x y; ext; simp
  map_add' := by intro x y; ext; simp
  map_zero' := by ext; simp

lemma intsMap_isLocalHom (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) : IsLocalHom (intsMap Q q hq) := by
  constructor
  intro a ha
  let A := AK Q
  let B := AL q
  by_contra hnon
  have ha_mA : a ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal]
    exact hnon
  have hval_a : Valued.v ((a : Q.adicCompletion K)) < (1 : Zstar0) := by
    exact (Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one
      Q a).mp ha_mA
  have hval_b : Valued.v ((intsMap Q q hq a : B) : q.adicCompletion L) < (1 : Zstar0) := by
    change Valued.v (Commons.RingTheory.Henselian.adicCompletionMap Q q hq (a : Q.adicCompletion K)) < 1
    rw [Commons.RingTheory.Henselian.valuation_completion_liesOver Q q hq (a : Q.adicCompletion K)]
    have hpos : 1 ≤ Q.asIdeal.ramificationIdx' q.asIdeal := by
      have hpos0 : 0 < q.asIdeal.ramificationIdx (𝓞 K) := by
        exact Ideal.ramificationIdx_pos (R := 𝓞 K) (S := 𝓞 L) q.asIdeal
      have hc : q.asIdeal.ramificationIdx (𝓞 K) = Q.asIdeal.ramificationIdx' q.asIdeal := by
        exact (Ideal.ramificationIdx'_eq_ramificationIdx (R := 𝓞 K) (S := 𝓞 L)
          (p := Q.asIdeal) (q := q.asIdeal) Q.ne_bot).symm
      rw [hc] at hpos0
      exact Nat.succ_le_of_lt hpos0
    have hle : (Valued.v (a : Q.adicCompletion K)) ^ Q.asIdeal.ramificationIdx' q.asIdeal ≤
        (Valued.v (a : Q.adicCompletion K)) := by
      simpa using (pow_le_pow_of_le_one (a := Valued.v (a : Q.adicCompletion K))
        bot_le (le_of_lt hval_a) hpos)
    exact lt_of_le_of_lt hle hval_a
  have hunit_val : Valued.v ((intsMap Q q hq a : B) : q.adicCompletion L) = (1 : Zstar0) := by
    exact (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
      (R := 𝓞 L) (K := L) (v := q) (a := intsMap Q q hq a)).1 ha
  exact (ne_of_lt hval_b) hunit_val

-- residue map from the number-field quotient to the completion residue (K side)
lemma valued_lt_one_le_exp_neg_one {y : Zstar0} (hy : y < (1 : Zstar0)) :
    y ≤ WithZero.exp (-1 : ℤ) := by
  by_cases hy0 : y = 0
  · simp [hy0]
  · rw [← WithZero.exp_log hy0]
    apply WithZero.exp_le_exp.2
    have hlog : WithZero.log y < (0 : ℤ) := by
      rw [← WithZero.exp_log hy0, ← WithZero.exp_zero] at hy
      exact WithZero.exp_lt_exp.mp hy
    omega

lemma exp_neg_one_lt_one : (WithZero.exp (-1 : ℤ) : Zstar0) < (1 : Zstar0) := by
  rw [← WithZero.exp_zero]
  exact WithZero.exp_lt_exp.mpr (by norm_num)

/-- A uniformizer of the ring of integers of a completion has valuation `exp (-1)`. -/
lemma uniformizer_val (F : Type*) [Field F] [NumberField F]
    (V : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    Valued.v (algebraMap (V.adicCompletionIntegers F) (V.adicCompletion F)
        (Commons.RingTheory.Henselian.uniformizer (R := 𝓞 F) (K := F) V)) =
      WithZero.exp (-1 : ℤ) := by
  let A := V.adicCompletionIntegers F
  let ϖ : A := Commons.RingTheory.Henselian.uniformizer (R := 𝓞 F) (K := F) V
  have hle : Valued.v ((ϖ : A) : V.adicCompletion F) ≤ WithZero.exp (-1 : ℤ) := by
    have hmA : ϖ ∈ mAK V := by
      change ϖ ∈ IsLocalRing.maximalIdeal A
      rw [Commons.RingTheory.Henselian.maximalIdeal_eq_span_uniformizer (R := 𝓞 F) (K := F) V]
      exact Ideal.mem_span_singleton_self ϖ
    have hlt : Valued.v ((ϖ : A) : V.adicCompletion F) < (1 : Zstar0) := by
      exact (Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one
        V ϖ).mp (by change ϖ ∈ IsLocalRing.maximalIdeal A; exact hmA)
    exact valued_lt_one_le_exp_neg_one hlt
  have hge : WithZero.exp (-1 : ℤ) ≤ Valued.v ((ϖ : A) : V.adicCompletion F) := by
    rcases Commons.RingTheory.Henselian.adicCompletion_valued_surjective V
      (WithZero.exp (-1 : ℤ)) with ⟨y, hy⟩
    have hyA : y ∈ A := by
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) (K := F) V]
      rw [hy]
      exact le_of_lt (by simpa using (exp_neg_one_lt_one : (WithZero.exp (-1 : ℤ) : Zstar0) < 1))
    have hymA : (⟨y, hyA⟩ : A) ∈ mAK V := by
      change (⟨y, hyA⟩ : A) ∈ IsLocalRing.maximalIdeal A
      rw [Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one V (⟨y, hyA⟩ : A)]
      rw [hy]
      exact (exp_neg_one_lt_one : (WithZero.exp (-1 : ℤ) : Zstar0) < 1)
    have hspan : (⟨y, hyA⟩ : A) ∈ Ideal.span ({ϖ} : Set A) := by
      rw [← Commons.RingTheory.Henselian.maximalIdeal_eq_span_uniformizer (R := 𝓞 F) (K := F) V]
      change (⟨y, hyA⟩ : A) ∈ mAK V
      exact hymA
    rcases (Ideal.mem_span_singleton' (x := (⟨y, hyA⟩ : A)) (y := ϖ)).mp hspan with ⟨b, hb⟩
    have hb' : y = ((ϖ : A) : V.adicCompletion F) * ((b : A) : V.adicCompletion F) := by
      -- from hb : ⟨y,hyA⟩ = ϖ * b in A: coerce to completion
      have hb'' := congrArg (fun z : A => (z : V.adicCompletion F)) hb
      simpa [mul_comm, mul_left_comm, mul_assoc] using hb''.symm
    have hvb_le : Valued.v ((b : A) : V.adicCompletion F) ≤ (1 : Zstar0) := (b : A).2
    -- hy : v(y) = exp(-1); hb': y = ϖ·b: v(y) = v(ϖ)·v(b) ≤ v(ϖ)
    have hmain : WithZero.exp (-1 : ℤ) ≤ Valued.v ((ϖ : A) : V.adicCompletion F) := by
      calc
        WithZero.exp (-1 : ℤ) = Valued.v (y) := hy.symm
        _ = Valued.v ((ϖ : A) : V.adicCompletion F) * Valued.v ((b : A) : V.adicCompletion F) := by
          rw [hb', map_mul]
        _ ≤ Valued.v ((ϖ : A) : V.adicCompletion F) * (1 : Zstar0) := by
          exact mul_le_mul_of_nonneg_left hvb_le (bot_le)
        _ = Valued.v ((ϖ : A) : V.adicCompletion F) := by simp
    exact hmain
  exact le_antisymm hle hge

noncomputable def uniK (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : AK Q :=
  Commons.RingTheory.Henselian.uniformizer (R := 𝓞 K) (K := K) Q
noncomputable def uniL (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) : AL q :=
  Commons.RingTheory.Henselian.uniformizer (R := 𝓞 L) (K := L) q

lemma mAK_eq_span_uniK (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    mAK Q = Ideal.span ({uniK Q} : Set (AK Q)) := by
  simpa [uniK] using (Commons.RingTheory.Henselian.maximalIdeal_eq_span_uniformizer
    (R := 𝓞 K) (K := K) Q)

lemma mAL_eq_span_uniL (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    mAL q = Ideal.span ({uniL q} : Set (AL q)) := by
  simpa [uniL] using (Commons.RingTheory.Henselian.maximalIdeal_eq_span_uniformizer
    (R := 𝓞 L) (K := L) q)

/-- two elements of a valuation ring with equal valuations generate the same ideal -/
lemma span_singleton_eq_of_val_eq (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (gx gy : AL q)
    (h : Valued.v ((gx : AL q) : q.adicCompletion L) =
      Valued.v ((gy : AL q) : q.adicCompletion L)) :
    Ideal.span ({gx} : Set (AL q)) = Ideal.span ({gy} : Set (AL q)) := by
  ext z
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  rw [Valuation.Integers.dvd_iff_le
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers (R := 𝓞 L) L q)]
  rw [Valuation.Integers.dvd_iff_le
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers (R := 𝓞 L) L q)]
  rw [show Valued.v (algebraMap (AL q) (q.adicCompletion L) gx) =
      Valued.v ((gx : AL q) : q.adicCompletion L) by rfl]
  rw [show Valued.v (algebraMap (AL q) (q.adicCompletion L) gy) =
      Valued.v ((gy : AL q) : q.adicCompletion L) by rfl]
  rw [h]

/-- valuations of the two generators of `mA·B` and `mB^e` are equal -/
lemma gen_val (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    Valued.v (((intsMap Q q hq (uniK Q)) : AL q) : q.adicCompletion L) =
      Valued.v (((uniL q ^ Q.asIdeal.ramificationIdx' q.asIdeal : AL q) : q.adicCompletion L)) := by
  let e := Q.asIdeal.ramificationIdx' q.asIdeal
  have hL : Valued.v ((intsMap Q q hq (uniK Q) : AL q) : q.adicCompletion L) =
      (Valued.v ((uniK Q : AK Q) : Q.adicCompletion K)) ^ e := by
    simpa [intsMap, e] using Commons.RingTheory.Henselian.valuation_completion_liesOver
      Q q hq ((uniK Q : AK Q) : Q.adicCompletion K)
  have hK : Valued.v ((uniK Q : AK Q) : Q.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    simpa [uniK, AK] using uniformizer_val K Q
  have hR : Valued.v ((uniL q ^ e : AL q) : q.adicCompletion L) =
      (WithZero.exp (-1 : ℤ)) ^ e := by
    have hcoe : ((uniL q ^ e : AL q) : q.adicCompletion L) =
        ((uniL q : AL q) : q.adicCompletion L) ^ e := by
      simp
    rw [hcoe, map_pow]
    have hvL : Valued.v ((uniL q : AL q) : q.adicCompletion L) = WithZero.exp (-1 : ℤ) := by
      simpa [uniL, AL] using uniformizer_val L q
    rw [hvL]
  calc
    Valued.v (((intsMap Q q hq (uniK Q)) : AL q) : q.adicCompletion L)
        = (Valued.v ((uniK Q : AK Q) : Q.adicCompletion K)) ^ e := hL
    _ = (WithZero.exp (-1 : ℤ)) ^ e := by rw [hK]
    _ = Valued.v (((uniL q ^ e : AL q) : q.adicCompletion L)) := hR.symm

-- ideal-power identity
lemma maximalIdeal_pow_eq_map (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    (mAL q) ^ Q.asIdeal.ramificationIdx' q.asIdeal = (mAK Q).map (intsMap Q q hq) := by
  have hspan : Ideal.span ({(intsMap Q q hq (uniK Q))} : Set (AL q)) =
      Ideal.span ({uniL q ^ Q.asIdeal.ramificationIdx' q.asIdeal} : Set (AL q)) := by
    exact span_singleton_eq_of_val_eq q (intsMap Q q hq (uniK Q))
      (uniL q ^ Q.asIdeal.ramificationIdx' q.asIdeal) (gen_val Q q hq)
  calc
    (mAL q) ^ Q.asIdeal.ramificationIdx' q.asIdeal
        = Ideal.span ({uniL q ^ Q.asIdeal.ramificationIdx' q.asIdeal} : Set (AL q)) := by
          rw [mAL_eq_span_uniL q, Ideal.span_singleton_pow]
    _ = Ideal.span ({(intsMap Q q hq (uniK Q))} : Set (AL q)) := hspan.symm
    _ = (mAK Q).map (intsMap Q q hq) := by
          rw [mAK_eq_span_uniK Q, Ideal.map_span]
          congr 1
          simp




/-- Clearing denominators into the ring of integers `A` of a completion of `K`, leaving at
least one coefficient outside the maximal ideal `mA` (a "primitive" multiple of a family of
`K`-coefficients). -/
lemma intsMap_mem_mB_pow (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) {a : AK Q} (ha : a ∈ mAK Q) :
    intsMap Q q hq a ∈ mAL q ^ Q.asIdeal.ramificationIdx' q.asIdeal := by
  have hmap : intsMap Q q hq a ∈ (mAK Q).map (intsMap Q q hq) :=
    Ideal.mem_map_of_mem (intsMap Q q hq) ha
  rw [← maximalIdeal_pow_eq_map Q q hq] at hmap
  exact hmap

lemma cancel_pow_dvr (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (π : AL q) (hπ : mAL q = Ideal.span ({π} : Set (AL q)))
    {n : ℕ} {x : AL q} (hx : π ^ n * x ∈ mAL q ^ (n + 1)) : x ∈ mAL q := by
  have hsp : π ^ n * x ∈ Ideal.span ({π ^ (n + 1)} : Set (AL q)) := by
    rw [hπ, Ideal.span_singleton_pow] at hx
    exact hx
  rcases (Ideal.mem_span_singleton' (x := π ^ n * x) (y := π ^ (n + 1))).mp hsp with ⟨z, hz⟩
  have hπn : π ^ n ≠ 0 := pow_ne_zero n (by
    intro hπ0
    have : mAL q = ⊥ := by rw [hπ, hπ0]; simp
    have hne : mAL q ≠ ⊥ := by simpa [mAL] using (IsDiscreteValuationRing.not_a_field (AL q))
    exact hne this)
  have hcancel : x = z * π := by
    apply mul_left_cancel₀ hπn
    calc
      π ^ n * x = z * π ^ (n + 1) := hz.symm
      _ = π ^ n * (z * π) := by ring
  rw [hcancel]
  rw [hπ]
  exact Ideal.mem_span_singleton'.mpr ⟨z, by rw [mul_comm]⟩

/-- LEVEL LEMMA -/
lemma level_no_relation
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    {f0 : ℕ} (π : AL q) (hπ : mAL q = Ideal.span ({π} : Set (AL q)))
    (w : Fin f0 → AL q)
    (hwres : ∀ (a : Fin f0 → AK Q),
      (∑ j : Fin f0,
        Ideal.Quotient.mk (mAL q) (intsMap Q q hq (a j)) *
          Ideal.Quotient.mk (mAL q) (w j)) = 0 → ∀ j : Fin f0, a j ∈ mAK Q)
    (a : (Fin (Q.asIdeal.ramificationIdx' q.asIdeal) × Fin f0) → AK Q)
    (hunit : ∃ p, a p ∉ mAK Q)
    (hrel : (∑ i : Fin (Q.asIdeal.ramificationIdx' q.asIdeal),
        ∑ j : Fin f0,
          (intsMap Q q hq (a (i, j)) * π ^ (i : ℕ) * w j : AL q)) = 0) :
    False := by
  classical
  let e := Q.asIdeal.ramificationIdx' q.asIdeal
  have he_pos : 0 < e := by
    haveI : q.asIdeal.LiesOver Q.asIdeal := hq
    have h : e = q.asIdeal.ramificationIdx (𝓞 K) := by
      exact (Ideal.ramificationIdx'_eq_ramificationIdx (R := 𝓞 K) (S := 𝓞 L)
        (p := Q.asIdeal) (q := q.asIdeal) Q.ne_bot)
    rw [h]
    exact Ideal.ramificationIdx_pos (R := 𝓞 K) q.asIdeal
  let P : ℕ → Prop := fun n => ∃ (h : n < e) (j : Fin f0), a (⟨n, h⟩, j) ∉ mAK Q
  have hex : ∃ n : ℕ, P n := by
    rcases hunit with ⟨p, hp⟩
    exact ⟨(p.1 : ℕ), p.1.2, p.2, hp⟩
  let n0 : ℕ := Nat.find hex
  have hn0 : P n0 := Nat.find_spec hex
  have hn0min : ∀ m : ℕ, m < n0 → ¬ P m := fun m hm => Nat.find_min hex hm
  rcases hn0 with ⟨hn0lt, j0, hj0u⟩
  let i0 : Fin e := ⟨n0, hn0lt⟩
  have hNle : n0 + 1 ≤ e := Nat.succ_le_of_lt hn0lt
  let term (i : Fin e) (j : Fin f0) : AL q := intsMap Q q hq (a (i, j)) * π ^ (i : ℕ) * w j
  have term_off (i : Fin e) (j : Fin f0) (h : i ≠ i0) : term i j ∈ mAL q ^ (n0 + 1) := by
    by_cases hle : (i : ℕ) < n0
    · have ham : a (i, j) ∈ mAK Q := by
        by_contra hnot
        have hP : P (i : ℕ) := ⟨i.2, j, hnot⟩
        exact hn0min (i : ℕ) hle hP
      have hc : intsMap Q q hq (a (i, j)) ∈ mAL q ^ e := intsMap_mem_mB_pow Q q hq ham
      have hm : intsMap Q q hq (a (i, j)) ∈ mAL q ^ (n0 + 1) := (Ideal.pow_le_pow_right hNle) hc
      simpa [term, mul_comm, mul_left_comm, mul_assoc] using
        (Ideal.mul_mem_left (mAL q ^ (n0 + 1)) (w j)
          (Ideal.mul_mem_left (mAL q ^ (n0 + 1)) (π ^ (i : ℕ)) hm))
    · have hgt : n0 < (i : ℕ) := lt_of_le_of_ne (Nat.le_of_not_gt hle) (by
        intro heq
        apply h
        apply Fin.ext
        exact heq.symm)
      have hNle2 : n0 + 1 ≤ (i : ℕ) := Nat.succ_le_of_lt hgt
      have hpi : π ^ (i : ℕ) ∈ mAL q ^ (i : ℕ) := by
        rw [hπ]
        by_cases hi : (i : ℕ) = 0
        · simp [hi]
        · rw [Ideal.span_singleton_pow]
          exact Ideal.subset_span (by simp)
      have hm : π ^ (i : ℕ) ∈ mAL q ^ (n0 + 1) := (Ideal.pow_le_pow_right hNle2) hpi
      simpa [term, mul_comm, mul_left_comm, mul_assoc] using
        (Ideal.mul_mem_left (mAL q ^ (n0 + 1)) (w j)
          (Ideal.mul_mem_left (mAL q ^ (n0 + 1)) (intsMap Q q hq (a (i, j))) hm))
  let g : Fin e → AL q := fun i => ∑ j : Fin f0, term i j
  have hrelG : (∑ i : Fin e, g i) = 0 := by
    simpa [g] using hrel
  have htotalG : (∑ i : Fin e, g i) ∈ mAL q ^ (n0 + 1) := by
    rw [hrelG]
    exact Ideal.zero_mem _
  have hrestG : (∑ i ∈ (Finset.univ.erase i0), g i) ∈ mAL q ^ (n0 + 1) := by
    apply Ideal.sum_mem
    intro i hi
    dsimp [g]
    apply Ideal.sum_mem
    intro j hj
    exact term_off i j (Finset.mem_erase.mp hi).1
  have hsumAll : (∑ i : Fin e, g i) = (∑ i ∈ (Finset.univ.erase i0), g i) + g i0 := by
    simpa using (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin e))) (f := g) (a := i0)
      (Finset.mem_univ i0)).symm
  have hgi0 : g i0 ∈ mAL q ^ (n0 + 1) := by
    have hEq : g i0 = (∑ i : Fin e, g i) - (∑ i ∈ (Finset.univ.erase i0), g i) := by
      rw [hsumAll]
      abel
    rw [hEq]
    exact sub_mem htotalG hrestG
  let G0 : AL q := ∑ j : Fin f0, intsMap Q q hq (a (i0, j)) * w j
  have hgG : g i0 = π ^ n0 * G0 := by
    dsimp [g, G0]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hi0n : (i0 : ℕ) = n0 := by simp [i0]
    calc
      term i0 j = (intsMap Q q hq (a (i0, j)) * π ^ n0 * w j : AL q) := by simp [term, hi0n]
      _ = π ^ n0 * (intsMap Q q hq (a (i0, j)) * w j) := by ring
  have hlevel : π ^ n0 * G0 ∈ mAL q ^ (n0 + 1) := by
    rwa [hgG] at hgi0
  have hG0 : G0 ∈ mAL q := cancel_pow_dvr q π hπ hlevel
  have hsum0 : (∑ j : Fin f0, Ideal.Quotient.mk (mAL q) (intsMap Q q hq (a (i0, j))) *
      Ideal.Quotient.mk (mAL q) (w j)) = 0 := by
    have hG0quot : (Ideal.Quotient.mk (mAL q) G0) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hG0
    have hG0exp : (Ideal.Quotient.mk (mAL q) G0) =
        ∑ j : Fin f0, Ideal.Quotient.mk (mAL q) (intsMap Q q hq (a (i0, j))) *
          Ideal.Quotient.mk (mAL q) (w j) := by
      simp [G0, map_sum, map_mul]
    exact hG0exp.symm.trans hG0quot
  have hall : ∀ j : Fin f0, a (i0, j) ∈ mAK Q := hwres (fun j => a (i0, j)) hsum0
  exact hj0u (hall j0)

/-- Clearing denominators -/
lemma exists_integral_scale (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {ι : Type*} [Fintype ι] (c : ι → Q.adicCompletion K)
    (hne : ∃ i, c i ≠ 0) :
    ∃ (s : ι → AK Q) (t : Q.adicCompletion K),
      t ≠ 0 ∧ (∀ i, (s i : Q.adicCompletion K) = t * c i) ∧ ∃ i₀, s i₀ ∉ mAK Q := by
  classical
  let idx : Finset ι := Finset.univ.filter (fun i => c i ≠ 0)
  have hidx : idx.Nonempty := by
    rcases hne with ⟨i, hi⟩
    exact ⟨i, by simp [idx, hi]⟩
  have hmax : ∃ i₀ ∈ idx, ∀ i ∈ idx, Valued.v (c i) ≤ Valued.v (c i₀) := by
    exact Finset.exists_max_image idx (fun i => Valued.v (c i)) hidx
  rcases hmax with ⟨i0, hi0idx, hmax⟩
  have hc0 : c i0 ≠ 0 := (Finset.mem_filter.mp hi0idx).2
  let t : Q.adicCompletion K := (c i0)⁻¹
  have hv0 : Valued.v (c i0) ≠ 0 := by
    intro hz
    exact hc0 ((Valuation.zero_iff (v := (Valued.v : Valuation (Q.adicCompletion K) Zstar0))).mp hz)
  have hval : ∀ i, Valued.v (t * c i) ≤ (1 : Zstar0) := by
    intro i
    by_cases hci : c i = 0
    · simp [t, hci]
    · have hvi : Valued.v (c i) ≠ 0 := by
        intro hz
        exact hci ((Valuation.zero_iff (v := (Valued.v : Valuation (Q.adicCompletion K) Zstar0))).mp hz)
      have hle : Valued.v (c i) ≤ Valued.v (c i0) := hmax i (by simp [idx, hci])
      have hpos : 0 < Valued.v (c i0) := by
        rw [pos_iff_ne_zero]
        exact hv0
      have hvT : Valued.v t = (Valued.v (c i0))⁻¹ := by
        simp [t, map_inv₀]
      calc
        Valued.v (t * c i) = Valued.v t * Valued.v (c i) := by rw [map_mul]
        _ = Valued.v (c i) * (Valued.v (c i0))⁻¹ := by rw [hvT, mul_comm]
        _ ≤ (1 : Zstar0) := by
          simpa [div_eq_mul_inv] using div_le_one_of_le₀ hle (le_of_lt hpos)
  have hmem : ∀ i, (t * c i) ∈ (AK Q : Set (Q.adicCompletion K)) := by
    intro i
    exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
      (R := 𝓞 K) (K := K) (v := Q) (x := t * c i)).mpr (hval i)
  refine ⟨fun i => ⟨t * c i, hmem i⟩, t, inv_ne_zero hc0, ?_, ⟨i0, ?_⟩⟩
  · intro i
    rfl
  · change ¬ (⟨t * c i0, hmem i0⟩ : AK Q) ∈ mAK Q
    have hsub : (⟨t * c i0, hmem i0⟩ : AK Q) = 1 := by
      apply Subtype.ext
      exact inv_mul_cancel₀ hc0
    rw [hsub]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    simp

-- algebra structure instances we will need inside the main theorem
noncomputable abbrev algKvLw (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
  RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)

/-- no zero relation over the whole index set -/
lemma no_univ_relation
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    {f0 : ℕ} (π : AL q) (hπ : mAL q = Ideal.span ({π} : Set (AL q)))
    (w : Fin f0 → AL q)
    (hwres : ∀ (a : Fin f0 → AK Q),
      (∑ j : Fin f0,
        Ideal.Quotient.mk (mAL q) (intsMap Q q hq (a j)) *
          Ideal.Quotient.mk (mAL q) (w j)) = 0 → ∀ j : Fin f0, a j ∈ mAK Q) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) := algKvLw Q q hq
    ∀ (g : (Fin (Q.asIdeal.ramificationIdx' q.asIdeal) × Fin f0) → Q.adicCompletion K),
      (∑ x : (Fin (Q.asIdeal.ramificationIdx' q.asIdeal) × Fin f0),
        g x • ((((π : AL q) : q.adicCompletion L) ^ (x.1 : ℕ)) *
          (((w x.2 : AL q) : q.adicCompletion L)))) = 0 →
        ∀ x : (Fin (Q.asIdeal.ramificationIdx' q.asIdeal) × Fin f0), g x = 0 := by
  classical
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) := algKvLw Q q hq
  let e := Q.asIdeal.ramificationIdx' q.asIdeal
  let ι := Fin e × Fin f0
  let v : ι → q.adicCompletion L := fun x =>
    (((π : AL q) : q.adicCompletion L) ^ (x.1 : ℕ)) * (((w x.2 : AL q) : q.adicCompletion L))
  intro g hg x0
  have hsmulA : ∀ (r : Q.adicCompletion K) (x : q.adicCompletion L), r • x =
      Commons.RingTheory.Henselian.adicCompletionMap Q q hq r * x := by
    intro r x
    rfl
  by_contra hne
  rcases exists_integral_scale Q g ⟨x0, hne⟩ with ⟨s, t, ht0, hst, i1, hsi1⟩
  have hsmul : (t • (∑ x : ι, g x • v x)) = 0 := by
    rw [hg]
    exact smul_zero t
  have hmul : (∑ x : ι, ((t * g x) • v x)) = 0 := by
    simpa [Finset.smul_sum, smul_smul, mul_comm, mul_left_comm, mul_assoc] using hsmul
  have hrepl : (∑ x : ι, (((s x : Q.adicCompletion K) • v x))) = 0 := by
    refine (Finset.sum_congr rfl (fun x _ => ?_)).trans hmul
    congr 1
    exact (hst x)
  -- express the Lw-relation as a relation in the integer ring B
  have hBrel : (∑ i : Fin e, ∑ j : Fin f0,
        (intsMap Q q hq (s (i, j)) * π ^ (i : ℕ) * w j : AL q)) = 0 := by
    apply Subtype.ext
    calc
      (((∑ i : Fin e, ∑ j : Fin f0,
          (intsMap Q q hq (s (i, j)) * π ^ (i : ℕ) * w j : AL q)) : AL q) : q.adicCompletion L)
          = ∑ i : Fin e, ∑ j : Fin f0,
              ((((intsMap Q q hq (s (i, j)) * π ^ (i : ℕ) * w j : AL q)) : AL q) : q.adicCompletion L) := by
              simp
      _ = ∑ x : ι, (((s x : Q.adicCompletion K) • v x)) := by
              have hterm : ∀ i : Fin e, ∀ j : Fin f0,
                  ((((intsMap Q q hq (s (i, j)) * π ^ (i : ℕ) * w j : AL q)) : AL q) : q.adicCompletion L) =
                    ((s (i, j) : Q.adicCompletion K) • v (i, j)) := by
                intro i j
                have hA : (((intsMap Q q hq (s (i, j)) : AL q) : q.adicCompletion L)) =
                    Commons.RingTheory.Henselian.adicCompletionMap Q q hq
                      ((s (i, j) : AK Q) : Q.adicCompletion K) := rfl
                have hB : (((π ^ (i : ℕ) : AL q) : q.adicCompletion L)) =
                    (((π : AL q) : q.adicCompletion L) ^ (i : ℕ)) := by
                  exact map_pow (algebraMap (AL q) (q.adicCompletion L)) π (i : ℕ)
                calc
                  ((((intsMap Q q hq (s (i, j)) * π ^ (i : ℕ) * w j : AL q)) : AL q) : q.adicCompletion L)
                      = (((intsMap Q q hq (s (i, j)) : AL q) : q.adicCompletion L) *
                          (((π ^ (i : ℕ) : AL q) : q.adicCompletion L)) *
                          (((w j : AL q) : q.adicCompletion L))) := by
                          simp
                  _ = Commons.RingTheory.Henselian.adicCompletionMap Q q hq
                        ((s (i, j) : AK Q) : Q.adicCompletion K) *
                          (((π : AL q) : q.adicCompletion L) ^ (i : ℕ)) *
                          (((w j : AL q) : q.adicCompletion L)) := by
                          rw [hA, hB]
                  _ = ((s (i, j) : AK Q) : Q.adicCompletion K) •
                        ((((π : AL q) : q.adicCompletion L) ^ (i : ℕ)) *
                          (((w j : AL q) : q.adicCompletion L))) := by
                          rw [hsmulA]
                          ring_nf
              have hprod : (∑ i : Fin e, ∑ j : Fin f0, ((s (i, j) : Q.adicCompletion K) • v (i, j))) =
                  (∑ x : ι, ((s x : Q.adicCompletion K) • v x)) := by
                exact (Fintype.sum_prod_type (fun x : ι => ((s x : Q.adicCompletion K) • v x))).symm
              calc
                (∑ i : Fin e, ∑ j : Fin f0,
                    ((((intsMap Q q hq (s (i, j)) * π ^ (i : ℕ) * w j : AL q)) : AL q) : q.adicCompletion L))
                    = ∑ i : Fin e, ∑ j : Fin f0, ((s (i, j) : Q.adicCompletion K) • v (i, j)) := by
                        apply Finset.sum_congr rfl
                        intro i _
                        apply Finset.sum_congr rfl
                        intro j _
                        exact hterm i j
                _ = ∑ x : ι, ((s x : Q.adicCompletion K) • v x) := hprod
      _ = 0 := hrepl
  exact level_no_relation Q q hq π hπ w hwres s ⟨i1, hsi1⟩ hBrel

/-- linear independence of the family {π^i · w j} over the completed field -/
theorem family_independent
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    {f0 : ℕ} (π : AL q) (hπ : mAL q = Ideal.span ({π} : Set (AL q)))
    (w : Fin f0 → AL q)
    (hwres : ∀ (a : Fin f0 → AK Q),
      (∑ j : Fin f0,
        Ideal.Quotient.mk (mAL q) (intsMap Q q hq (a j)) *
          Ideal.Quotient.mk (mAL q) (w j)) = 0 → ∀ j : Fin f0, a j ∈ mAK Q) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) := algKvLw Q q hq
    LinearIndependent (Q.adicCompletion K)
      (fun x : (Fin (Q.asIdeal.ramificationIdx' q.asIdeal)) × (Fin f0) =>
        (((π : AL q) : q.adicCompletion L) ^ (x.1 : ℕ)) *
          (((w x.2 : AL q) : q.adicCompletion L))) := by
  classical
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) := algKvLw Q q hq
  rw [linearIndependent_iff]
  intro l hl
  have hlsum : (∑ x : (Fin (Q.asIdeal.ramificationIdx' q.asIdeal) × Fin f0), l x •
      ((((π : AL q) : q.adicCompletion L) ^ (x.1 : ℕ)) *
        (((w x.2 : AL q) : q.adicCompletion L)))) = 0 := by
    rw [Finsupp.linearCombination_apply] at hl
    have hsf : l.sum (fun i a => a • ((((π : AL q) : q.adicCompletion L) ^ (i.1 : ℕ)) *
        (((w i.2 : AL q) : q.adicCompletion L)))) =
        (∑ x : (Fin (Q.asIdeal.ramificationIdx' q.asIdeal) × Fin f0),
          l x • ((((π : AL q) : q.adicCompletion L) ^ (x.1 : ℕ)) *
            (((w x.2 : AL q) : q.adicCompletion L)))) := by
      exact Finsupp.sum_fintype l (fun i a => a • ((((π : AL q) : q.adicCompletion L) ^ (i.1 : ℕ)) *
        (((w i.2 : AL q) : q.adicCompletion L)))) (by intro i; simp)
    rw [hsf] at hl
    simpa using hl
  have hNo := no_univ_relation Q q hq π hπ w hwres (fun x : (Fin (Q.asIdeal.ramificationIdx' q.asIdeal) × Fin f0) =>
      l x) hlsum
  apply Finsupp.ext
  intro x
  exact hNo x

-- ================================================================
-- PART 2
-- ================================================================

/-- two finite fields over finite bases with equal cardinalities have equal finranks -/
lemma finrank_eq_of_card_eq {F₁ F₂ E₁ E₂ : Type*}
    [Field F₁] [Field F₂] [Field E₁] [Field E₂]
    [Algebra F₁ E₁] [Algebra F₂ E₂]
    [Fintype F₁] [Fintype F₂] [Fintype E₁] [Fintype E₂]
    [Module.Finite F₁ E₁] [Module.Finite F₂ E₂]
    (hF : Fintype.card F₁ = Fintype.card F₂) (hE : Fintype.card E₁ = Fintype.card E₂) :
    Module.finrank F₁ E₁ = Module.finrank F₂ E₂ := by
  have hc1 := Module.card_eq_pow_finrank (K := F₁) (V := E₁)
  have hc2 := Module.card_eq_pow_finrank (K := F₂) (V := E₂)
  have hpow : Fintype.card F₁ ^ Module.finrank F₁ E₁ =
      Fintype.card F₁ ^ Module.finrank F₂ E₂ := by
    calc
      Fintype.card F₁ ^ Module.finrank F₁ E₁ = Fintype.card E₁ := hc1.symm
      _ = Fintype.card E₂ := hE
      _ = Fintype.card F₂ ^ Module.finrank F₂ E₂ := hc2
      _ = Fintype.card F₁ ^ Module.finrank F₂ E₂ := by rw [hF]
  have hcard_ge2 : 2 ≤ Fintype.card F₁ := Nat.succ_le_of_lt (Fintype.one_lt_card (α := F₁))
  exact (Nat.pow_right_injective hcard_ge2) hpow

-- ================================================================
-- PART 3: the main theorem
-- ================================================================
theorem finrank_adicCompletion_ge_ef
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
        q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) ≤
      @Module.finrank (Q.adicCompletion K) (q.adicCompletion L) _ _
        (RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)).toModule := by
  classical
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) := algKvLw Q q hq
  haveI : Module.Finite (Q.adicCompletion K) (q.adicCompletion L) := module_finite_adicCompletion Q q hq
  -- completed integer rings and their residue fields
  letI : Algebra (AK Q) (AL q) := (intsMap Q q hq).toAlgebra
  haveI : IsLocalHom (algebraMap (AK Q) (AL q)) := by
    change IsLocalHom (intsMap Q q hq)
    exact intsMap_isLocalHom Q q hq
  haveI : (mAL q).LiesOver (mAK Q) := inferInstance
  haveI : (mAL q).LiesOver (mAK Q) := inferInstance
  -- maximality of the number-field primes
  haveI : Q.asIdeal.IsMaximal := Q.isPrime.isMaximal Q.ne_bot
  haveI : q.asIdeal.IsMaximal := q.isPrime.isMaximal q.ne_bot
  -- residue fields of the completions
  letI : Field ((AK Q) ⧸ mAK Q) := Ideal.Quotient.field (I := mAK Q)
  letI : Field ((AL q) ⧸ mAL q) := Ideal.Quotient.field (I := mAL q)
  -- finiteness
  have hfinA : Finite ((AK Q) ⧸ mAK Q) := by
    rcases Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists (K := K) Q with ⟨e⟩
    change Finite ((AK Q) ⧸ mAK Q)
    exact Finite.of_equiv ((𝓞 K) ⧸ Q.asIdeal) e.symm.toEquiv
  have hfinB : Finite ((AL q) ⧸ mAL q) := by
    rcases Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists (K := L) q with ⟨e⟩
    change Finite ((AL q) ⧸ mAL q)
    exact Finite.of_equiv ((𝓞 L) ⧸ q.asIdeal) e.symm.toEquiv
  haveI : Module.Finite ((AK Q) ⧸ mAK Q) ((AL q) ⧸ mAL q) :=
    Module.Finite.of_finite (R := (AK Q) ⧸ mAK Q) (M := (AL q) ⧸ mAL q)
  haveI : Module.Free ((AK Q) ⧸ mAK Q) ((AL q) ⧸ mAL q) :=
    Module.Free.of_divisionRing ((AK Q) ⧸ mAK Q) ((AL q) ⧸ mAL q)
  let f0 : ℕ := Module.finrank ((AK Q) ⧸ mAK Q) ((AL q) ⧸ mAL q)
  -- basis of the residue extension, indexed by Fin f0
  let b0 := Module.Free.chooseBasis ((AK Q) ⧸ mAK Q) ((AL q) ⧸ mAL q)
  have hcard0 : Fintype.card (Module.Free.ChooseBasisIndex ((AK Q) ⧸ mAK Q) ((AL q) ⧸ mAL q)) = f0 := by
    exact (Module.finrank_eq_card_chooseBasisIndex ((AK Q) ⧸ mAK Q) ((AL q) ⧸ mAL q)).symm
  let b : Module.Basis (Fin f0) ((AK Q) ⧸ mAK Q) ((AL q) ⧸ mAL q) :=
    b0.reindex (Fintype.equivFinOfCardEq hcard0)
  -- lift basis vectors to the integer ring of the completion of L
  let w : Fin f0 → AL q := fun j => Classical.choose (Ideal.Quotient.mk_surjective (b j))
  have hw (j : Fin f0) : Ideal.Quotient.mk (mAL q) (w j) = b j :=
    Classical.choose_spec (Ideal.Quotient.mk_surjective (b j))
  -- residue independence in the form required by the level lemma
  have hwres : ∀ (a : Fin f0 → AK Q),
      (∑ j : Fin f0,
        Ideal.Quotient.mk (mAL q) (intsMap Q q hq (a j)) *
          Ideal.Quotient.mk (mAL q) (w j)) = 0 → ∀ j : Fin f0, a j ∈ mAK Q := by
    intro a hrel j
    -- coefficient: mkB(ψ a) = algebraMap κA κB (mkA a)
    have hterm (j : Fin f0) : Ideal.Quotient.mk (mAL q) (intsMap Q q hq (a j)) =
        algebraMap ((AK Q) ⧸ mAK Q) ((AL q) ⧸ mAL q) (Ideal.Quotient.mk (mAK Q) (a j)) := by
      change Ideal.Quotient.mk (mAL q) (algebraMap (AK Q) (AL q) (a j)) =
        algebraMap ((AK Q) ⧸ mAK Q) ((AL q) ⧸ mAL q) (Ideal.Quotient.mk (mAK Q) (a j))
      rw [Ideal.Quotient.algebraMap_mk_of_liesOver (A := AK Q) (B := AL q) (P := mAL q)
        (p := mAK Q)]
    -- relation as a κA-linear combination of the basis
    have hrel' : (∑ j : Fin f0,
        Ideal.Quotient.mk (mAK Q) (a j) •
          (b j : (AL q) ⧸ mAL q)) = 0 := by
      have hrew : (∑ j : Fin f0,
          Ideal.Quotient.mk (mAL q) (intsMap Q q hq (a j)) *
            Ideal.Quotient.mk (mAL q) (w j)) =
          (∑ j : Fin f0,
            Ideal.Quotient.mk (mAK Q) (a j) •
              (b j : (AL q) ⧸ mAL q)) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        calc
          Ideal.Quotient.mk (mAL q) (intsMap Q q hq (a j)) *
              Ideal.Quotient.mk (mAL q) (w j)
              = algebraMap ((AK Q) ⧸ mAK Q) ((AL q) ⧸ mAL q)
                  (Ideal.Quotient.mk (mAK Q) (a j)) * (b j : (AL q) ⧸ mAL q) := by
                  rw [hterm j, hw j]
          _ = Ideal.Quotient.mk (mAK Q) (a j) • (b j : (AL q) ⧸ mAL q) := by
                  simp [Algebra.smul_def]
      rw [← hrew]
      exact hrel
    have hind := (linearIndependent_iff'.mp b.linearIndependent)
      (Finset.univ : Finset (Fin f0)) (fun j => Ideal.Quotient.mk (mAK Q) (a j)) hrel'
    have hmk0 : Ideal.Quotient.mk (mAK Q) (a j) = 0 := hind j (Finset.mem_univ j)
    exact (Ideal.Quotient.eq_zero_iff_mem (I := mAK Q)).mp hmk0
  -- linear independence over the completion of K
  let π : AL q := uniL q
  have hπ : mAL q = Ideal.span ({π} : Set (AL q)) := mAL_eq_span_uniL q
  have hfam := family_independent Q q hq π hπ w hwres
  -- size of the family
  have hcardfam : Fintype.card (Fin (Q.asIdeal.ramificationIdx' q.asIdeal) × Fin f0) =
      Q.asIdeal.ramificationIdx' q.asIdeal * f0 := by simp
  have hle := LinearIndependent.fintype_card_le_finrank hfam
  have hbound : Q.asIdeal.ramificationIdx' q.asIdeal * f0 ≤
      @Module.finrank (Q.adicCompletion K) (q.adicCompletion L) _ _
        ((algKvLw Q q hq).toModule) := by
    simpa [hcardfam] using hle
  -- f0 = inertia degree
  have hf0 : f0 = q.asIdeal.inertiaDeg (𝓞 K) := by
    classical
    let κQ := (𝓞 K) ⧸ Q.asIdeal
    let κq := (𝓞 L) ⧸ q.asIdeal
    haveI : q.asIdeal.LiesOver Q.asIdeal := hq
    letI : Field κQ := Ideal.Quotient.field (I := Q.asIdeal)
    letI : Field κq := Ideal.Quotient.field (I := q.asIdeal)
    have hfinQ : Finite κQ := by
      change Finite ((𝓞 K) ⧸ Q.asIdeal)
      exact Ideal.finiteQuotientOfFreeOfNeBot (I := Q.asIdeal) Q.ne_bot
    have hfinq : Finite κq := by
      change Finite ((𝓞 L) ⧸ q.asIdeal)
      exact Ideal.finiteQuotientOfFreeOfNeBot (I := q.asIdeal) q.ne_bot
    haveI : Finite ((AK Q) ⧸ mAK Q) := hfinA
    haveI : Finite ((AL q) ⧸ mAL q) := hfinB
    haveI : Finite κQ := hfinQ
    haveI : Finite κq := hfinq
    haveI : Fintype ((AK Q) ⧸ mAK Q) := Fintype.ofFinite ((AK Q) ⧸ mAK Q)
    haveI : Fintype ((AL q) ⧸ mAL q) := Fintype.ofFinite ((AL q) ⧸ mAL q)
    haveI : Fintype κQ := Fintype.ofFinite κQ
    haveI : Fintype κq := Fintype.ofFinite κq
    haveI : Module.Finite κQ κq := Module.Finite.of_finite (R := κQ) (M := κq)
    have hcA : Fintype.card ((AK Q) ⧸ mAK Q) = Fintype.card κQ := by
      rcases Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists (K := K) Q with ⟨e⟩
      change Fintype.card ((AK Q) ⧸ mAK Q) = Fintype.card ((𝓞 K) ⧸ Q.asIdeal)
      exact Fintype.card_congr e.toEquiv
    have hcB : Fintype.card ((AL q) ⧸ mAL q) = Fintype.card κq := by
      rcases Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists (K := L) q with ⟨e⟩
      change Fintype.card ((AL q) ⧸ mAL q) = Fintype.card ((𝓞 L) ⧸ q.asIdeal)
      exact Fintype.card_congr e.toEquiv
    have hffin : Module.finrank ((AK Q) ⧸ mAK Q) ((AL q) ⧸ mAL q) = Module.finrank κQ κq := by
      exact finrank_eq_of_card_eq (F₁ := (AK Q) ⧸ mAK Q) (E₁ := (AL q) ⧸ mAL q)
        (F₂ := κQ) (E₂ := κq) hcA hcB
    have hfin2 : Module.finrank κQ κq = q.asIdeal.inertiaDeg (𝓞 K) := by
      exact (Ideal.inertiaDeg_eq_of_isMaximal (R := 𝓞 K) (S := 𝓞 L) (p := Q.asIdeal) (q := q.asIdeal)).symm
    simpa [f0] using (hffin.trans hfin2)
  have he : Q.asIdeal.ramificationIdx' q.asIdeal = q.asIdeal.ramificationIdx (𝓞 K) := by
    exact (Ideal.ramificationIdx'_eq_ramificationIdx (R := 𝓞 K) (S := 𝓞 L)
      (p := Q.asIdeal) (q := q.asIdeal) Q.ne_bot)
  -- final
  calc
    q.asIdeal.ramificationIdx (𝓞 K) * q.asIdeal.inertiaDeg (𝓞 K)
        = Q.asIdeal.ramificationIdx' q.asIdeal * f0 := by rw [he, hf0]
    _ ≤ @Module.finrank (Q.adicCompletion K) (q.adicCompletion L) _ _
        (RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)).toModule := by
        simpa [algKvLw] using hbound