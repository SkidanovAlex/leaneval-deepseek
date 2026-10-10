import Mathlib
import Submission.Work.MotC2.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- `letI`/`haveI` are needed below to register the discrete valuation ring instances carried by
-- `IsRatPlace`; the style linter would prefer `let`/`have`, which drops them from the instance
-- search, so it is silenced here.
set_option linter.style.haveILetI false

namespace Work.MotC2

/-! ## Auxiliary lemmas used in the proof of `DVRMaximal` -/

/-- In a discrete valuation ring every prime ideal is either `⊥` or the maximal ideal. -/
lemma dvr_prime_eq_bot_or_maximalIdeal {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (P : Ideal R) (hP : P.IsPrime) :
    P = ⊥ ∨ P = IsLocalRing.maximalIdeal R := by
  by_cases h : P = ⊥
  · exact Or.inl h
  · refine Or.inr ?_
    obtain ⟨P₀, -, huniq⟩ :=
      ((IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime R).mp inferInstance).2
    have h1 : P = P₀ := huniq P ⟨h, hP⟩
    have h2 : IsLocalRing.maximalIdeal R = P₀ :=
      huniq (IsLocalRing.maximalIdeal R)
        ⟨IsDiscreteValuationRing.not_a_field R,
          (IsLocalRing.maximalIdeal.isMaximal R).isPrime⟩
    rw [h1, h2]

/-- The inverse of a unit of a subalgebra of a field, transported to the ambient field. -/
lemma subalgebra_coe_unit_inv {L K : Type*} [Field L] [Field K] [Algebra L K]
    (S : Subalgebra L K) (u : Sˣ) :
    (((u⁻¹ : Sˣ) : S) : K) = (((u : Sˣ) : S) : K)⁻¹ := by
  have h : ((u : Sˣ) : S) * ((u⁻¹ : Sˣ) : S) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : (((u : Sˣ) : S) : K) * (((u⁻¹ : Sˣ) : S) : K) = 1 := by
    rw [← Subalgebra.coe_mul, h, Subalgebra.coe_one]
  exact (inv_eq_of_mul_eq_one_right h2).symm

/-- If `S` is a `PreValuationRing` subalgebra of a field `K` whose elements generate `K` as
fractions, then every nonzero `f : K` either lies in `S` or has its inverse in `S`. -/
lemma mem_or_inv_mem_of_preValuationRing {L K : Type*} [Field L] [Field K] [Algebra L K]
    (S : Subalgebra L K) [PreValuationRing S]
    (hfrac : ∀ f : K, ∃ s₁ s₂ : S, (s₂ : K) ≠ 0 ∧ f * (s₂ : K) = (s₁ : K))
    {f : K} (hf : f ≠ 0) : f ∈ S ∨ f⁻¹ ∈ S := by
  obtain ⟨s₁, s₂, hs₂, hprod⟩ := hfrac f
  have hs₁ : (s₁ : K) ≠ 0 := by
    intro h
    rw [h, mul_eq_zero] at hprod
    rcases hprod with h' | h'
    · exact hf h'
    · exact hs₂ h'
  obtain ⟨c, hc | hc⟩ := PreValuationRing.cond s₁ s₂
  · -- `s₁ * c = s₂`, so `f * (s₂) = (s₁) = s₁ * s₂ / s₂` gives `f = c⁻¹`
    right
    have hmap : (s₁ : K) * (c : K) = (s₂ : K) := by rw [← Subalgebra.coe_mul, hc]
    have h1 : f * (c : K) = 1 := by
      have h2 : (f * (c : K)) * (s₁ : K) = 1 * (s₁ : K) := by
        rw [mul_assoc, mul_comm (c : K) (s₁ : K), hmap, hprod, one_mul]
      exact mul_right_cancel₀ hs₁ h2
    have hc' : (c : K) = f⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    rw [← hc']
    exact c.2
  · -- `s₂ * c = s₁`, so `f = s₁ / s₂ = c`
    left
    have hmap : (s₂ : K) * (c : K) = (s₁ : K) := by rw [← Subalgebra.coe_mul, hc]
    have h1 : f = (c : K) := by
      have h2 : f * (s₂ : K) = (c : K) * (s₂ : K) := by
        rw [hprod, ← hmap, mul_comm]
      exact mul_right_cancel₀ hs₂ h2
    rw [h1]
    exact c.2

/-
NOTE: the earlier negative review of this statement was caused by `IsRatPlace` not recording that
the fraction field of the subalgebra is `L(E)`; that conjunct has now been added, so the statement
is the true maximality of a place among DVR subrings of `L(E)`.

Route.  Let `S ≤ T` be two rational places and suppose `f ∈ T`, `f ∉ S`, `f ≠ 0`.  Since `S` is a
valuation ring, `f⁻¹ ∈ S ≤ T`; as `f, f⁻¹ ∈ T` both are units of `T`, and `f⁻¹ ∉ Sˣ` (else
`f ∈ S`), so `f⁻¹ ∈ 𝔪_S` while `f⁻¹ ∉ 𝔪_T`.  Hence `𝔪_T ∩ S` is a prime ideal of `S` strictly
smaller than `𝔪_S`; since a DVR has exactly the primes `⊥` and `𝔪`, it is `⊥`.  Then all non-zero
elements of `S` are units of `T`, so `T` contains the fraction field of `S`, which is `S`'s
fraction field, equal to `L(E)` by `IsRatPlace`; hence `T = L(E)`, contradicting `𝔪_T ≠ ⊥`
(`IsDiscreteValuationRing.not_a_field'`).  Useful auxiliary: in a discrete valuation ring `R` every
prime ideal is `⊥` or `IsLocalRing.maximalIdeal R` (from `IsDiscreteValuationRing.TFAE`, item 2 of
the list: `IsDedekindDomain R` and a Dedekind domain has Krull dimension one).
-/
theorem DVRMaximal (L : Type*) [Field L] (E : WeierstrassCurve L)
    (S T : Subalgebra L (Work.MotC2.Func E))
    (hS : Work.MotC2.IsRatPlace E S) (hT : Work.MotC2.IsRatPlace E T) (hle : S ≤ T) :
    S = T := by
  obtain ⟨⟨hSdvr, _⟩, hSfrac⟩ := hS
  obtain ⟨⟨hTdvr, _⟩, _⟩ := hT
  letI := hSdvr
  letI := hTdvr
  refine le_antisymm hle ?_
  rw [SetLike.le_def]
  intro x hxT
  -- suppose for contradiction that `x ∈ T`, `x ∉ S`
  by_contra hxS
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxS S.zero_mem
  -- `S` is a valuation ring, so `x⁻¹ ∈ S`
  have hxinv : x⁻¹ ∈ S := by
    rcases mem_or_inv_mem_of_preValuationRing S hSfrac hx0 with h | h
    · exact absurd h hxS
    · exact h
  set sx : S := ⟨x⁻¹, hxinv⟩ with hsxdef
  have hsx : (sx : Func E) = x⁻¹ := rfl
  -- `x⁻¹` is a nonunit of `S`, i.e. lies in the maximal ideal of `S`
  have hsx_mem : sx ∈ IsLocalRing.maximalIdeal S := by
    rw [IsLocalRing.mem_maximalIdeal]
    rintro ⟨u, hu⟩
    have hux : ((u : S) : Func E) = x⁻¹ := by rw [hu, hsx]
    have h2 : (((u⁻¹ : Sˣ) : S) : Func E) = x := by
      rw [subalgebra_coe_unit_inv S u, hux, inv_inv]
    exact hxS (by rw [← h2]; exact ((u⁻¹ : Sˣ) : S).2)
  -- `x⁻¹` is a unit of `T`, since `x ∈ T`
  have hφsx_unit : IsUnit ((Subalgebra.inclusion hle) sx) := by
    have hφsx_mul : (Subalgebra.inclusion hle) sx * (⟨x, hxT⟩ : T) = 1 := by
      apply Subtype.ext
      rw [Subalgebra.coe_mul, Subalgebra.coe_inclusion, hsx, Subalgebra.coe_one]
      exact inv_mul_cancel₀ hx0
    exact ⟨⟨_, _, hφsx_mul, by rw [mul_comm]; exact hφsx_mul⟩, rfl⟩
  have hsxT_notMem : (Subalgebra.inclusion hle) sx ∉ IsLocalRing.maximalIdeal T :=
    IsLocalRing.notMem_maximalIdeal.mpr hφsx_unit
  -- the prime ideal `𝔪_T ∩ S` is strictly smaller than `𝔪_S`, hence is `⊥`
  let P : Ideal S := Ideal.comap (Subalgebra.inclusion hle) (IsLocalRing.maximalIdeal T)
  have hPprime : P.IsPrime := by
    haveI : (IsLocalRing.maximalIdeal T).IsPrime :=
      (IsLocalRing.maximalIdeal.isMaximal T).isPrime
    exact Ideal.IsPrime.comap (Subalgebra.inclusion hle)
  have hsxP : sx ∉ P := fun h => hsxT_notMem (Ideal.mem_comap.mp h)
  have hPne : P ≠ IsLocalRing.maximalIdeal S := fun h => hsxP (h ▸ hsx_mem)
  have hPbot : P = ⊥ := by
    rcases dvr_prime_eq_bot_or_maximalIdeal P hPprime with h | h
    · exact h
    · exact absurd h hPne
  -- hence every nonzero element of `S` is a unit of `T`
  have key : ∀ s : S, s ≠ 0 → (Subalgebra.inclusion hle) s ∉ IsLocalRing.maximalIdeal T := by
    intro s hs hmem
    have h1 : s ∈ P := Ideal.mem_comap.mpr hmem
    rw [hPbot] at h1
    exact hs (Ideal.mem_bot.mp h1)
  -- so `T` contains the fraction field of `S`, which is all of `L(E)`
  have all_mem : ∀ f : Func E, f ∈ T := by
    intro f
    by_cases hf : f = 0
    · rw [hf]
      exact T.zero_mem
    obtain ⟨s₁, s₂, hs₂, hprod⟩ := hSfrac f
    have hs₂ne : s₂ ≠ 0 := fun h => hs₂ (by rw [h]; rfl)
    have hunit : IsUnit ((Subalgebra.inclusion hle) s₂) :=
      IsLocalRing.notMem_maximalIdeal.mp (key s₂ hs₂ne)
    have hval : ((hunit.unit : Tˣ) : T) = (Subalgebra.inclusion hle) s₂ := IsUnit.unit_spec hunit
    have h2 : (((hunit.unit⁻¹ : Tˣ) : T) : Func E) = (s₂ : Func E)⁻¹ := by
      rw [subalgebra_coe_unit_inv T hunit.unit, hval, Subalgebra.coe_inclusion]
    have hf1 : f = (s₁ : Func E) * (s₂ : Func E)⁻¹ := by
      rw [← hprod, mul_assoc, mul_inv_cancel₀ hs₂, mul_one]
    have hfeq : f = (((⟨(s₁ : Func E), hle s₁.2⟩ : T) *
        ((hunit.unit⁻¹ : Tˣ) : T) : T) : Func E) := by
      rw [Subalgebra.coe_mul, h2]
      simpa using hf1
    rw [hfeq]
    exact (⟨(s₁ : Func E), hle s₁.2⟩ * ((hunit.unit⁻¹ : Tˣ) : T)).2
  -- but `T` is a discrete valuation ring, hence not a field
  have hne : IsLocalRing.maximalIdeal T ≠ ⊥ := IsDiscreteValuationRing.not_a_field T
  obtain ⟨a, ha_mem, ha_ne⟩ := (Submodule.ne_bot_iff (IsLocalRing.maximalIdeal T)).mp hne
  have ha0 : (a : Func E) ≠ 0 := by
    intro h
    exact ha_ne (Subtype.ext (by simpa using h))
  obtain ⟨t, ht⟩ : ∃ t : T, (t : Func E) = (a : Func E)⁻¹ :=
    ⟨⟨(a : Func E)⁻¹, all_mem _⟩, rfl⟩
  have h1 : a * t = 1 := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, ht, Subalgebra.coe_one]
    exact mul_inv_cancel₀ ha0
  have hunit : IsUnit a := ⟨⟨a, t, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  exact ((IsLocalRing.mem_maximalIdeal a).mp ha_mem) hunit

end Work.MotC2
