import Mathlib
import Submission.Commons.Analysis.Nonarchimedean.exists_exp_log_adicCompletion_log_val_eq
import Submission.Commons.NumberTheory.NumberField.Completion.val_le_exp_neg_iff_mem_maximalIdeal_pow

open scoped WithZero NumberField
open IsDedekindDomain

namespace NK.NUV2

variable {K : Type*} [Field K] [NumberField K]

/-- **The additive cover of a level propagates to every deeper level.**
If every element of `𝔪 ^ M` is a `ℤ`-linear combination of the `b i` modulo `2 𝔪 ^ M`, then the
same holds for `𝔪 ^ k` for every `k ≥ M`, with the `b i` replaced by `π ^ (k - M) * b i`
(`π` a uniformiser): multiplying the identity `𝔪 ^ M = ⟨b⟩ + 2 𝔪 ^ M` by the single scalar
`π ^ (k - M)` does not create any new `ℤ`-coefficients. -/
lemma cover_of_cover (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (π : q.adicCompletionIntegers K)
    (hπmax : IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) = Ideal.span {π})
    {n : ℕ} (b : Fin n → q.adicCompletionIntegers K) {M k : ℕ} (hMk : M ≤ k)
    (hcov : ∀ x ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ M,
      ∃ z ∈ AddSubgroup.closure (Set.range b),
      ∃ y ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ M,
        x = z + (2 : q.adicCompletionIntegers K) * y)
    (x : q.adicCompletionIntegers K)
    (hx : x ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ k) :
    ∃ z ∈ AddSubgroup.closure (Set.range (fun i => π ^ (k - M) * b i)),
    ∃ y ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ k,
      x = z + (2 : q.adicCompletionIntegers K) * y := by
  have hπk : (IsLocalRing.maximalIdeal (q.adicCompletionIntegers K)) ^ k =
      Ideal.span {π ^ k} := by rw [hπmax, Ideal.span_singleton_pow]
  rw [hπk, Ideal.mem_span_singleton] at hx
  obtain ⟨a, ha⟩ := hx
  have hc : π ^ M * a ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ M := by
    rw [hπmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨a, rfl⟩
  obtain ⟨z, hzB, y, hyM, hzy⟩ := hcov (π ^ M * a) hc
  have hzT : π ^ (k - M) * z ∈
      AddSubgroup.closure (Set.range (fun i => π ^ (k - M) * b i)) := by
    refine AddSubgroup.closure_induction (p := fun w _ => π ^ (k - M) * w ∈
      AddSubgroup.closure (Set.range (fun i => π ^ (k - M) * b i))) ?_ ?_ ?_ ?_ hzB
    · rintro w ⟨i, rfl⟩
      exact AddSubgroup.subset_closure (Set.mem_range_self i)
    · rw [mul_zero]
      exact AddSubgroup.zero_mem _
    · intro u v hu hv ihu ihv
      rw [mul_add]
      exact AddSubgroup.add_mem _ ihu ihv
    · intro u hu ihu
      rw [mul_neg]
      exact AddSubgroup.neg_mem _ ihu
  have hyk : π ^ (k - M) * y ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ k := by
    rw [hπk, Ideal.mem_span_singleton]
    rw [hπmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hyM
    obtain ⟨w, hw⟩ := hyM
    refine ⟨w, ?_⟩
    rw [hw, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hMk]
  have hxr : π ^ k * a = π ^ (k - M) * (π ^ M * a) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hMk]
  refine ⟨π ^ (k - M) * z, hzT, π ^ (k - M) * y, hyk, ?_⟩
  rw [ha, hxr, hzy]
  ring

/-- **A small element has `exp` in the units of the ring of integers**, congruent to `1` to the
same precision. -/
lemma exists_unit_exp (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (exp : q.adicCompletion K → q.adicCompletion K) {M₀ : ℕ} (hM₀ : 1 ≤ M₀)
    (hexp_sub : ∀ x : q.adicCompletion K,
      Valued.v x ≤ (WithZero.exp (-(M₀ : ℤ)) : Zstar0) →
      Valued.v (exp x - 1) = Valued.v x)
    {M' : ℕ} (hM₀M' : M₀ ≤ M') (x : q.adicCompletion K)
    (hx : Valued.v x ≤ (WithZero.exp (-(M' : ℤ)) : Zstar0)) :
    ∃ w : (q.adicCompletionIntegers K)ˣ,
      (((w : q.adicCompletionIntegers K)) : q.adicCompletion K) = exp x ∧
      Valued.v ((((w : q.adicCompletionIntegers K)) : q.adicCompletion K) - 1) ≤
        (WithZero.exp (-(M' : ℤ)) : Zstar0) := by
  have hM' : 1 ≤ M' := le_trans hM₀ hM₀M'
  have hx0 : Valued.v x ≤ (WithZero.exp (-(M₀ : ℤ)) : Zstar0) :=
    le_trans hx (WithZero.exp_le_exp.mpr (by omega))
  have hsub : Valued.v (exp x - 1) = Valued.v x := hexp_sub x hx0
  have hxlt : Valued.v x < (1 : Zstar0) := by
    refine lt_of_le_of_lt hx ?_
    rw [show (1 : Zstar0) = WithZero.exp 0 from WithZero.exp_zero.symm]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hval : Valued.v (exp x) = (1 : Zstar0) := by
    have h1 : exp x = 1 + (exp x - 1) := by ring
    have hlt : Valued.v (exp x - 1) < Valued.v (1 : q.adicCompletion K) := by
      rw [map_one, hsub]; exact hxlt
    rw [h1, Valuation.map_add_eq_of_lt_left (v := (Valued.v : Valuation (q.adicCompletion K) Zstar0))
      (x := (1 : q.adicCompletion K)) (y := exp x - 1) hlt, map_one]
  have hmem : exp x ∈ q.adicCompletionIntegers K :=
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (R := NumberField.RingOfIntegers K)
      (K := K) q).mpr (le_of_eq hval)
  have hunit : IsUnit (⟨exp x, hmem⟩ : q.adicCompletionIntegers K) :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mpr hval
  refine ⟨IsUnit.unit hunit, ?_, ?_⟩
  · show (((IsUnit.unit hunit : q.adicCompletionIntegers K)) : q.adicCompletion K) = exp x
    rw [IsUnit.unit_spec]
  · rw [IsUnit.unit_spec, hsub]
    exact hx

/-- **From an additive cover of `𝔪 ^ M'` by `β` to a multiplicative cover of the principal
units `1 + 𝔪 ^ M'` by `exp (β i)` modulo squares.** -/
lemma unit_cover_aux (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {M₀ : ℕ} (hM₀ : 1 ≤ M₀)
    (exp : q.adicCompletion K → q.adicCompletion K)
    (hexp_zero : exp 0 = 1)
    (hexp_sub : ∀ x : q.adicCompletion K,
      Valued.v x ≤ (WithZero.exp (-(M₀ : ℤ)) : Zstar0) →
      Valued.v (exp x - 1) = Valued.v x)
    (hexp_add : ∀ x y : q.adicCompletion K,
      Valued.v x ≤ (WithZero.exp (-(M₀ : ℤ)) : Zstar0) →
      Valued.v y ≤ (WithZero.exp (-(M₀ : ℤ)) : Zstar0) → exp (x + y) = exp x * exp y)
    (log : q.adicCompletion K → q.adicCompletion K)
    (hlog : ∀ y : q.adicCompletion K,
      Valued.v (y - 1) ≤ (WithZero.exp (-(M₀ : ℤ)) : Zstar0) →
      Valued.v (log y) ≤ (WithZero.exp (-(M₀ : ℤ)) : Zstar0) ∧
      Valued.v (log y) = Valued.v (y - 1) ∧ exp (log y) = y)
    {n : ℕ} (β : Fin n → q.adicCompletionIntegers K) {M' : ℕ} (hM₀M' : M₀ ≤ M')
    (hβ : ∀ i, β i ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ M')
    (hcov : ∀ x ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ M',
      ∃ z ∈ AddSubgroup.closure (Set.range β),
      ∃ y ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ M',
        x = z + (2 : q.adicCompletionIntegers K) * y) :
    ∃ b' : Fin n → (q.adicCompletionIntegers K)ˣ,
      (∀ i, Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          (((b' i : q.adicCompletionIntegers K) : q.adicCompletion K) - 1) ≤
        (WithZero.exp (-(M' : ℤ)) : WithZero (Multiplicative ℤ))) ∧
      (∀ u : (q.adicCompletionIntegers K)ˣ,
        Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
            (((u : q.adicCompletionIntegers K) : q.adicCompletion K) - 1) ≤
          (WithZero.exp (-(M' : ℤ)) : WithZero (Multiplicative ℤ)) →
        ∃ z ∈ Subgroup.closure (Set.range b'), ∃ w : (q.adicCompletionIntegers K)ˣ,
          Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
              (((w : q.adicCompletionIntegers K) : q.adicCompletion K) - 1) ≤
            (WithZero.exp (-(M' : ℤ)) : WithZero (Multiplicative ℤ)) ∧
          u = z * w ^ 2) := by
  have hM' : 1 ≤ M' := le_trans hM₀ hM₀M'
  have hδle : (WithZero.exp (-(M' : ℤ)) : Zstar0) ≤ (WithZero.exp (-(M₀ : ℤ)) : Zstar0) :=
    WithZero.exp_le_exp.mpr (by omega)
  have hδ1 : (WithZero.exp (-(M' : ℤ)) : Zstar0) ≤ 1 := by
    rw [show (1 : Zstar0) = WithZero.exp 0 from WithZero.exp_zero.symm]
    exact WithZero.exp_le_exp.mpr (by omega)
  have hβval : ∀ i, Valued.v ((β i : q.adicCompletionIntegers K) : q.adicCompletion K) ≤
      (WithZero.exp (-(M' : ℤ)) : Zstar0) := fun i =>
    (Commons.NumberTheory.NumberField.Completion.val_le_exp_neg_iff_mem_maximalIdeal_pow q (β i) M').mpr
      (hβ i)
  choose b' hb'eq hb'val using
    fun i => exists_unit_exp q exp hM₀ hexp_sub hM₀M' (β i : q.adicCompletion K) (hβval i)
  set S : Subgroup (q.adicCompletionIntegers K)ˣ := Subgroup.closure (Set.range b') with hS
  set T : AddSubgroup (q.adicCompletionIntegers K) := AddSubgroup.closure (Set.range β) with hT
  refine ⟨b', hb'val, ?_⟩
  have hTsub : ∀ z ∈ T, z ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ M' := by
    intro z hz
    refine AddSubgroup.closure_induction (p := fun w _ => w ∈
      IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ M') ?_ ?_ ?_ ?_ hz
    · rintro w ⟨i, rfl⟩
      exact hβ i
    · exact Ideal.zero_mem _
    · intro u v hu hv ihu ihv
      exact Ideal.add_mem _ ihu ihv
    · intro u hu ihu
      exact neg_mem ihu
  have hTval : ∀ z ∈ T, Valued.v ((z : q.adicCompletionIntegers K) : q.adicCompletion K) ≤
      (WithZero.exp (-(M' : ℤ)) : Zstar0) := fun z hz =>
    (Commons.NumberTheory.NumberField.Completion.val_le_exp_neg_iff_mem_maximalIdeal_pow q z M').mpr
      (hTsub z hz)
  have hTval₀ : ∀ z ∈ T, Valued.v ((z : q.adicCompletionIntegers K) : q.adicCompletion K) ≤
      (WithZero.exp (-(M₀ : ℤ)) : Zstar0) := fun z hz => le_trans (hTval z hz) hδle
  have hPT : ∀ z ∈ T, ∃ s ∈ S,
      ((s : q.adicCompletionIntegers K) : q.adicCompletion K) =
        exp ((z : q.adicCompletionIntegers K) : q.adicCompletion K) := by
    intro z hz
    refine AddSubgroup.closure_induction (p := fun w _ => ∃ s ∈ S,
      ((s : q.adicCompletionIntegers K) : q.adicCompletion K) =
        exp ((w : q.adicCompletionIntegers K) : q.adicCompletion K)) ?_ ?_ ?_ ?_ hz
    · rintro w ⟨i, rfl⟩
      exact ⟨b' i, Subgroup.subset_closure (Set.mem_range_self i), hb'eq i⟩
    · refine ⟨1, S.one_mem, ?_⟩
      rw [show ((0 : q.adicCompletionIntegers K) : q.adicCompletion K) = 0 from rfl, hexp_zero]
      simp
    · intro u v hu hv ihu ihv
      obtain ⟨su, hsu, hueq⟩ := ihu
      obtain ⟨sv, hsv, hveq⟩ := ihv
      refine ⟨su * sv, S.mul_mem hsu hsv, ?_⟩
      have hsum : exp (((u : q.adicCompletionIntegers K) : q.adicCompletion K) +
          ((v : q.adicCompletionIntegers K) : q.adicCompletion K)) =
          ((su : q.adicCompletionIntegers K) : q.adicCompletion K) *
            ((sv : q.adicCompletionIntegers K) : q.adicCompletion K) := by
        rw [hexp_add _ _ (hTval₀ u hu) (hTval₀ v hv), hueq, hveq]
      have hsrc : (((u : q.adicCompletionIntegers K) : q.adicCompletion K) +
          ((v : q.adicCompletionIntegers K) : q.adicCompletion K)) =
          (((u + v : q.adicCompletionIntegers K)) : q.adicCompletion K) := by push_cast; ring
      rw [hsrc] at hsum
      rw [hsum]
      push_cast
      rfl
    · intro u hu ihu
      obtain ⟨su, hsu, hueq⟩ := ihu
      refine ⟨su⁻¹, S.inv_mem hsu, ?_⟩
      have hune : exp ((u : q.adicCompletionIntegers K) : q.adicCompletion K) ≠ 0 := by
        rw [← hueq]
        intro hcon
        exact Units.ne_zero su (Subtype.ext hcon)
      have hadd := hexp_add ((u : q.adicCompletionIntegers K) : q.adicCompletion K)
        (-((u : q.adicCompletionIntegers K) : q.adicCompletion K)) (hTval₀ u hu)
        (by rw [Valuation.map_neg]; exact hTval₀ u hu)
      rw [add_neg_cancel, hexp_zero] at hadd
      have hinv : exp (-((u : q.adicCompletionIntegers K) : q.adicCompletion K)) =
          (exp ((u : q.adicCompletionIntegers K) : q.adicCompletion K))⁻¹ :=
        ((mul_eq_one_iff_inv_eq₀ hune).mp hadd.symm).symm
      have hneg : ((↑(-u) : q.adicCompletionIntegers K) : q.adicCompletion K) =
          -((u : q.adicCompletionIntegers K) : q.adicCompletion K) := by push_cast; ring
      rw [hneg, hinv, ← hueq]
      have hmulA : ((su : (q.adicCompletionIntegers K)ˣ) : q.adicCompletionIntegers K) *
          ((su⁻¹ : (q.adicCompletionIntegers K)ˣ) : q.adicCompletionIntegers K) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hmulL : (((su : (q.adicCompletionIntegers K)ˣ) : q.adicCompletionIntegers K) :
            q.adicCompletion K) *
          (((su⁻¹ : (q.adicCompletionIntegers K)ˣ) : q.adicCompletionIntegers K) :
            q.adicCompletion K) = 1 := by
        have h := congrArg (fun t : q.adicCompletionIntegers K => (t : q.adicCompletion K)) hmulA
        push_cast at h
        exact h
      have hsu_ne : ((su : q.adicCompletionIntegers K) : q.adicCompletion K) ≠ 0 := by
        intro hcon
        exact Units.ne_zero su (Subtype.ext hcon)
      exact ((mul_eq_one_iff_inv_eq₀ hsu_ne).mp hmulL).symm
  intro u hu
  have hlogu := hlog ((u : q.adicCompletionIntegers K) : q.adicCompletion K) (le_trans hu hδle)
  obtain ⟨hαle, hαval, hαexp⟩ := hlogu
  have hαA : log ((u : q.adicCompletionIntegers K) : q.adicCompletion K) ∈
      q.adicCompletionIntegers K := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (R := NumberField.RingOfIntegers K)
      (K := K) q, hαval]
    exact le_trans hu hδ1
  have hαle' : Valued.v (log ((u : q.adicCompletionIntegers K) : q.adicCompletion K)) ≤
      (WithZero.exp (-(M' : ℤ)) : Zstar0) := by
    rw [hαval]; exact hu
  obtain ⟨z, hzT, y, hy𝔪, hzy⟩ := hcov ⟨log ((u : q.adicCompletionIntegers K) : q.adicCompletion K), hαA⟩
    ((Commons.NumberTheory.NumberField.Completion.val_le_exp_neg_iff_mem_maximalIdeal_pow q _ M').mp
      hαle')
  obtain ⟨s, hsS, hseq⟩ := hPT z hzT
  have hyval : Valued.v ((y : q.adicCompletionIntegers K) : q.adicCompletion K) ≤
      (WithZero.exp (-(M' : ℤ)) : Zstar0) :=
    (Commons.NumberTheory.NumberField.Completion.val_le_exp_neg_iff_mem_maximalIdeal_pow q y M').mpr hy𝔪
  have hyval₀ : Valued.v ((y : q.adicCompletionIntegers K) : q.adicCompletion K) ≤
      (WithZero.exp (-(M₀ : ℤ)) : Zstar0) := le_trans hyval hδle
  obtain ⟨w, hweq, hwval⟩ := exists_unit_exp q exp hM₀ hexp_sub hM₀M'
    (y : q.adicCompletion K) hyval
  refine ⟨s, hsS, w, hwval, ?_⟩
  have h2ymem : (2 : q.adicCompletionIntegers K) * y ∈
      IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ M' :=
    Ideal.mul_mem_left _ _ hy𝔪
  have h2yval : Valued.v ((((2 : q.adicCompletionIntegers K) * y :
        q.adicCompletionIntegers K)) : q.adicCompletion K) ≤
      (WithZero.exp (-(M₀ : ℤ)) : Zstar0) := by
    refine le_trans ?_ hδle
    exact (Commons.NumberTheory.NumberField.Completion.val_le_exp_neg_iff_mem_maximalIdeal_pow q _ M').mpr
      h2ymem
  have hmain : ((u : q.adicCompletionIntegers K) : q.adicCompletion K) =
      ((s : q.adicCompletionIntegers K) : q.adicCompletion K) *
        (((w : q.adicCompletionIntegers K) : q.adicCompletion K)) ^ 2 := by
    calc ((u : q.adicCompletionIntegers K) : q.adicCompletion K)
        = exp (log ((u : q.adicCompletionIntegers K) : q.adicCompletion K)) := hαexp.symm
      _ = exp (((z : q.adicCompletionIntegers K) : q.adicCompletion K) +
            (((2 : q.adicCompletionIntegers K) * y : q.adicCompletionIntegers K) :
              q.adicCompletion K)) := by
            congr 1
            have hco := congrArg (fun t : q.adicCompletionIntegers K => (t : q.adicCompletion K)) hzy
            simpa using hco
      _ = exp (((z : q.adicCompletionIntegers K) : q.adicCompletion K)) *
            exp ((((2 : q.adicCompletionIntegers K) * y : q.adicCompletionIntegers K) :
              q.adicCompletion K)) := hexp_add _ _ (hTval₀ z hzT) h2yval
      _ = exp (((z : q.adicCompletionIntegers K) : q.adicCompletion K)) *
            (exp (((y : q.adicCompletionIntegers K) : q.adicCompletion K))) ^ 2 := by
            congr 1
            have h2 : ((((2 : q.adicCompletionIntegers K) * y : q.adicCompletionIntegers K) :
                q.adicCompletion K)) =
                ((y : q.adicCompletionIntegers K) : q.adicCompletion K) +
                  ((y : q.adicCompletionIntegers K) : q.adicCompletion K) := by
              show (2 : q.adicCompletion K) * ((y : q.adicCompletionIntegers K) :
                  q.adicCompletion K) = ((y : q.adicCompletionIntegers K) : q.adicCompletion K) +
                    ((y : q.adicCompletionIntegers K) : q.adicCompletion K)
              ring
            rw [h2, hexp_add _ _ hyval₀ hyval₀, sq]
      _ = ((s : q.adicCompletionIntegers K) : q.adicCompletion K) *
            (((w : q.adicCompletionIntegers K) : q.adicCompletion K)) ^ 2 := by
            rw [← hseq, hweq]
  apply Units.ext
  apply Subtype.ext
  rw [hmain]
  push_cast
  ring

theorem unitCover_two (K : Type) [Field K] [NumberField K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h : q.asIdeal.LiesOver (Ideal.span {(2 : ℤ)}))
    (b : Fin (q.asIdeal.ramificationIdx ℤ * q.asIdeal.inertiaDeg ℤ) → q.adicCompletionIntegers K)
    (M : ℕ) (hM : 1 ≤ M)
    (hb : ∀ i, b i ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ M)
    (hcov : ∀ x ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ M,
      ∃ z ∈ AddSubgroup.closure (Set.range b),
      ∃ y ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ M,
        x = z + (2 : q.adicCompletionIntegers K) * y) :
    ∃ M' : ℕ, M ≤ M' ∧ 1 ≤ M' ∧ ∃ b' : Fin (q.asIdeal.ramificationIdx ℤ * q.asIdeal.inertiaDeg ℤ) → (q.adicCompletionIntegers K)ˣ,
        (∀ i, Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (((b' i : q.adicCompletionIntegers K) : q.adicCompletion K) - 1) ≤ (WithZero.exp (-(M' : ℤ)) : WithZero (Multiplicative ℤ))) ∧
        (∀ u : (q.adicCompletionIntegers K)ˣ,
          Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (((u : q.adicCompletionIntegers K) : q.adicCompletion K) - 1) ≤ (WithZero.exp (-(M' : ℤ)) : WithZero (Multiplicative ℤ)) →
          ∃ z ∈ Subgroup.closure (Set.range b'), ∃ w : (q.adicCompletionIntegers K)ˣ,
            Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (((w : q.adicCompletionIntegers K) : q.adicCompletion K) - 1) ≤ (WithZero.exp (-(M' : ℤ)) : WithZero (Multiplicative ℤ)) ∧
            u = z * w ^ 2) := by
  classical
  obtain ⟨M₀, hM₀, exp, log, hser, hexp_sub, hexp_zero, hexp_add, hlog, hlog_exp⟩ :=
    Commons.Analysis.Nonarchimedean.exists_exp_log_adicCompletion_log_val_eq (K := K) q
  obtain ⟨π, hπval, hπmax⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_uniformizer_adicCompletionIntegers (K := K) q
  have hMle : M ≤ max M M₀ := le_max_left _ _
  have hM₀le : M₀ ≤ max M M₀ := le_max_right _ _
  have hβ : ∀ i, (fun i => π ^ (max M M₀ - M) * b i) i ∈
      IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ (max M M₀) := by
    intro i
    have hbM := hb i
    rw [hπmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hbM
    obtain ⟨c, hc⟩ := hbM
    show π ^ (max M M₀ - M) * b i ∈
      IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ (max M M₀)
    rw [hπmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    refine ⟨c, ?_⟩
    rw [hc, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hMle]
  have hcov' : ∀ x ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ (max M M₀),
      ∃ z ∈ AddSubgroup.closure (Set.range (fun i => π ^ (max M M₀ - M) * b i)),
      ∃ y ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ (max M M₀),
        x = z + (2 : q.adicCompletionIntegers K) * y :=
    fun x hx => cover_of_cover q π hπmax b hMle hcov x hx
  exact ⟨max M M₀, hMle, le_trans hM hMle,
    unit_cover_aux q hM₀ exp hexp_zero hexp_sub hexp_add log hlog
      (fun i => π ^ (max M M₀ - M) * b i) hM₀le hβ hcov'⟩

end NK.NUV2
