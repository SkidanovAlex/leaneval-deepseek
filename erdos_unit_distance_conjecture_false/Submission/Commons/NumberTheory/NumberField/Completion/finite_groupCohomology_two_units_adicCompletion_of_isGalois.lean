import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.NumberTheory.NumberField.Completion.exists_ramificationSubgroups_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.isCyclic_algEquiv_fixedField_inertia
import Submission.Commons.NumberTheory.NumberField.Completion.finite_groupCohomology_two_units_of_solvable
import Submission.Commons.NumberTheory.NumberField.Completion.residueActionHom_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.map_maximalIdeal_eq_maximalIdeal_pow
import Submission.Commons.NumberTheory.NumberField.Completion.exists_isPrimitiveRoot_lift_adicCompletionB

open scoped commutatorElement
open scoped NumberField
open IsDedekindDomain.HeightOneSpectrum

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

noncomputable section

namespace Commons.NumberTheory.NumberField.Completion

/-! ## General ring lemmas about congruences modulo powers of an ideal -/

theorem sub_mem_pow_of_ringEquiv {R : Type*} [CommRing R] (I : Ideal R) (σ : R ≃+* R)
    (hI : ∀ x ∈ I, σ x ∈ I) {i : ℕ} (hσ : ∀ x : R, σ x - x ∈ I ^ (i + 1)) :
    ∀ (k : ℕ) (x : R), x ∈ I ^ k → σ x - x ∈ I ^ (i + k) := by
  intro k
  induction k with
  | zero =>
    intro x _
    exact Ideal.pow_le_pow_right (Nat.le_succ i) (hσ x)
  | succ k ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      have h1 : σ (a * b) - a * b = (σ a - a) * (σ b) + a * (σ b - b) := by
        rw [map_mul]; ring
      rw [h1]
      refine add_mem ?_ ?_
      · have h2 : I ^ (i + k) * I ≤ I ^ (i + (k + 1)) := by
          rw [show i + (k + 1) = (i + k) + 1 from by ring, pow_succ]
        exact h2 (Ideal.mul_mem_mul (ih a ha) (hI b hb))
      · have h2 : I ^ k * I ^ (i + 1) ≤ I ^ (i + (k + 1)) := by
          rw [← pow_add, show k + (i + 1) = i + (k + 1) from by ring]
        exact h2 (Ideal.mul_mem_mul ha (hσ b))
    · intro x y hx hy
      rw [map_add]
      have : σ x + σ y - (x + y) = (σ x - x) + (σ y - y) := by ring
      rw [this]
      exact add_mem hx hy

theorem commutator_sub_mem_pow {R : Type*} [CommRing R] (I : Ideal R)
    (σ τ : R ≃+* R) (hσI : ∀ x ∈ I, σ x ∈ I) (hτI : ∀ x ∈ I, τ x ∈ I)
    {i j : ℕ}
    (hσ : ∀ x : R, σ x - x ∈ I ^ (i + 1)) (hτ : ∀ x : R, τ x - x ∈ I ^ (j + 1)) :
    ∀ x : R, (⁅σ, τ⁆) x - x ∈ I ^ (i + j + 1) := by
  intro x
  set z : R := (τ * σ)⁻¹ x with hz
  have hz' : τ (σ z) = x := by
    rw [hz]
    exact RingEquiv.apply_symm_apply (τ * σ) x
  have hz2 : σ⁻¹ (τ⁻¹ x) = z := by
    rw [hz, mul_inv_rev, RingAut.mul_apply]
  have hcomm : (⁅σ, τ⁆) x = σ (τ z) := by
    rw [commutatorElement_def]
    rw [show (σ * τ * σ⁻¹ * τ⁻¹ : R ≃+* R) = σ * τ * (σ⁻¹ * τ⁻¹) from by group]
    simp only [RingAut.mul_apply]
    rw [hz2]
  have hA : σ (τ z - z) - (τ z - z) ∈ I ^ (i + (j + 1)) :=
    sub_mem_pow_of_ringEquiv I σ hσI hσ (j + 1) (τ z - z) (hτ z)
  have hB : τ (σ z - z) - (σ z - z) ∈ I ^ (j + (i + 1)) :=
    sub_mem_pow_of_ringEquiv I τ hτI hτ (i + 1) (σ z - z) (hσ z)
  rw [show i + (j + 1) = i + j + 1 from by ring] at hA
  rw [show j + (i + 1) = i + j + 1 from by ring] at hB
  have hgoal : σ (τ z) - τ (σ z) ∈ I ^ (i + j + 1) := by
    have hEq : σ (τ z) - τ (σ z) =
        (σ (τ z - z) - (τ z - z)) - (τ (σ z - z) - (σ z - z)) := by
      rw [map_sub, map_sub]; ring
    rw [hEq]
    exact sub_mem hA hB
  rw [hcomm, ← hz']
  exact hgoal

theorem exists_eq_bot_of_iInf_eq_bot_of_antitone {G : Type*} [Group G] [Fintype G]
    (H : ℕ → Subgroup G) (hanti : Antitone H) (hinf : ⨅ n, H n = ⊥) :
    ∃ N : ℕ, H N = ⊥ := by
  classical
  have hex : ∀ g : G, g ≠ 1 → ∃ n, g ∉ H n := by
    intro g hg
    by_contra h
    push Not at h
    have : g ∈ ⨅ n, H n := Subgroup.mem_iInf.mpr h
    rw [hinf] at this
    exact hg (Subgroup.mem_bot.mp this)
  let nf : G → ℕ := fun g => if hg : g = 1 then 0 else Classical.choose (hex g hg)
  have hnf : ∀ g, g ≠ 1 → g ∉ H (nf g) := by
    intro g hg
    have h1 : nf g = Classical.choose (hex g hg) := by simp [nf, hg]
    rw [h1]
    exact Classical.choose_spec (hex g hg)
  refine ⟨(Finset.univ.filter (fun g : G => g ≠ 1)).sup nf + 1, ?_⟩
  refine le_antisymm ?_ bot_le
  intro g hg
  rw [Subgroup.mem_bot]
  by_contra hg1
  have hgF : g ∈ Finset.univ.filter (fun g : G => g ≠ 1) := by simp [hg1]
  have hle : nf g ≤ (Finset.univ.filter (fun g : G => g ≠ 1)).sup nf := Finset.le_sup hgF
  have hge : H ((Finset.univ.filter (fun g : G => g ≠ 1)).sup nf + 1) ≤ H (nf g) :=
    hanti (by omega)
  exact hnf g hg1 (hge hg)



theorem eq_one_of_pow_eq_one_of_sub_mem_maximalIdeal {B : Type*} [CommRing B] [IsLocalRing B]
    [IsDomain B] {N : ℕ} (hN : IsUnit (N : B)) {w : B} (hw : w ^ N = 1)
    (hwmem : w - 1 ∈ IsLocalRing.maximalIdeal B) : w = 1 := by
  have hfac : (w - 1) * (∑ i ∈ Finset.range N, w ^ i) = 0 := by
    rw [mul_geom_sum, hw, sub_self]
  have hterm : ∀ i ∈ Finset.range N, w ^ i - 1 ∈ IsLocalRing.maximalIdeal B := by
    intro i _
    have hh : w ^ i - 1 = (w - 1) * (∑ j ∈ Finset.range i, w ^ j) := by rw [mul_geom_sum]
    rw [hh]
    exact Ideal.mul_mem_right _ _ hwmem
  have hsum : (∑ i ∈ Finset.range N, (w ^ i - 1)) ∈ IsLocalRing.maximalIdeal B :=
    Ideal.sum_mem (IsLocalRing.maximalIdeal B) (fun i hi => hterm i hi)
  have hsplit : (∑ i ∈ Finset.range N, (w ^ i - 1 : B)) =
      (∑ i ∈ Finset.range N, w ^ i) - (N : B) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hEq : (∑ i ∈ Finset.range N, w ^ i) =
      (N : B) + ∑ i ∈ Finset.range N, (w ^ i - 1) := by
    rw [hsplit]; ring
  have hNnotmem : (N : B) ∉ IsLocalRing.maximalIdeal B := fun hh => hh hN
  have hEq2 : (N : B) = (∑ i ∈ Finset.range N, w ^ i) -
      ∑ i ∈ Finset.range N, (w ^ i - 1) := by
    rw [hEq]; ring
  have hmain : (∑ i ∈ Finset.range N, w ^ i) ∉ IsLocalRing.maximalIdeal B := by
    intro h
    refine hNnotmem ?_
    rw [hEq2]
    exact sub_mem h hsum
  rcases mul_eq_zero.mp hfac with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h (fun h0 => hmain (h0 ▸ Submodule.zero_mem _))





theorem sub_sq_mem_of_uniformizer_congruence {B : Type*} [CommRing B] [IsDomain B] [IsLocalRing B]
    {π : B} (hπ : IsLocalRing.maximalIdeal B = Ideal.span {π})
    (σ : B ≃+* B)
    (hσm : ∀ x ∈ IsLocalRing.maximalIdeal B, σ x ∈ IsLocalRing.maximalIdeal B)
    (hσ : ∀ x : B, σ x - x ∈ IsLocalRing.maximalIdeal B)
    (hπσ : σ π - π ∈ IsLocalRing.maximalIdeal B ^ 2)
    (hunits : ∀ u : B, IsUnit u → σ u - u ∈ IsLocalRing.maximalIdeal B ^ 2) :
    ∀ x : B, σ x - x ∈ IsLocalRing.maximalIdeal B ^ 2 := by
  have hπmem : π ∈ IsLocalRing.maximalIdeal B := by
    rw [hπ]; exact Ideal.mem_span_singleton.mpr ⟨1, by ring⟩
  have key_m : ∀ y ∈ IsLocalRing.maximalIdeal B,
      σ y - y ∈ IsLocalRing.maximalIdeal B ^ 2 := by
    intro y hy
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.mp (hπ ▸ hy)
    have hderiv : σ (π * t) - π * t =
        σ t * (σ π - π) + (σ t - t) * π := by
      rw [map_mul]; ring
    rw [hderiv]
    refine add_mem (Ideal.mul_mem_left (IsLocalRing.maximalIdeal B ^ 2) (σ t) hπσ) ?_
    rw [pow_two]
    exact Ideal.mul_mem_mul (hσ t) hπmem
  intro x
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  · by_cases hunit : IsUnit x
    · exact hunits x hunit
    · exact key_m x (show x ∈ IsLocalRing.maximalIdeal B from hunit)



/-! ## The local Galois group of an adic completion is solvable -/

private theorem solvable_algEquiv_adicCompletion_aux
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    Group.IsSolvable (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  haveI hFD : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hGal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion Q q hq
  obtain ⟨Gs, hGnorm, hGanti, hGinf, hGcard, hGmem⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_ramificationSubgroups_adicCompletion Q q hq
  set B := q.adicCompletionIntegers L with hBdef
  set mm : Ideal B := IsLocalRing.maximalIdeal B with hmmdef
  have hpres : ∀ (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (y : q.adicCompletion L),
      σ y ∈ B ↔ y ∈ B := fun σ y =>
    Commons.NumberTheory.NumberField.Completion.algEquiv_mem_adicCompletionIntegers_iff_adicCompletion
      Q q hq σ y
  let actFun : (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) → B ≃+* B :=
    fun σ =>
    { toFun := fun x => ⟨σ (x : q.adicCompletion L), (hpres σ (x : q.adicCompletion L)).mpr x.2⟩
      invFun := fun y => ⟨σ.symm (y : q.adicCompletion L),
        (hpres σ.symm (y : q.adicCompletion L)).mpr y.2⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  have actFun_coe : ∀ (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (x : B), ((actFun σ x : B) : q.adicCompletion L) = σ (x : q.adicCompletion L) :=
    fun σ x => rfl
  have hact : ∀ (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) (x : B),
      actFun σ x = ⟨σ (x : q.adicCompletion L), (hpres σ (x : q.adicCompletion L)).mpr x.2⟩ :=
    fun σ x => rfl
  have actFun_one : actFun 1 = 1 := by
    refine RingEquiv.ext fun x => ?_
    apply Subtype.ext
    change ((1 : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (x : q.adicCompletion L)) = ((1 : B ≃+* B) x : B)
    simp
  have actFun_mul : ∀ (σ τ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L),
      actFun (σ * τ) = actFun σ * actFun τ := by
    intro σ τ
    refine RingEquiv.ext fun x => ?_
    apply Subtype.ext
    change ((σ * τ) (x : q.adicCompletion L)) = ((actFun σ * actFun τ) x : B)
    rw [RingAut.mul_apply]
    change σ (τ (x : q.adicCompletion L)) = σ ((actFun τ x : B) : q.adicCompletion L)
    rfl
  let actHom : (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) →* (B ≃+* B) :=
    { toFun := actFun, map_one' := actFun_one, map_mul' := actFun_mul }
  have actHom_apply : ∀ σ x, actHom σ x = actFun σ x := fun σ x => rfl
  have hmem_iff : ∀ (n : ℕ) (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L),
      σ ∈ Gs n ↔ ∀ x : B, actFun σ x - x ∈ mm ^ (n + 1) := by
    intro n σ
    rw [hGmem n σ]
    constructor
    · intro h x
      obtain ⟨hx, hq'⟩ := h x
      have hq'' : Ideal.Quotient.mk (mm ^ (n+1)) (actFun σ x) =
          Ideal.Quotient.mk (mm ^ (n+1)) x := by
        rw [show actFun σ x = (⟨σ (x : q.adicCompletion L), hx⟩ : B) from Subtype.ext rfl]
        exact hq'
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := mm ^ (n+1)) (actFun σ x) x).mp hq''
    · intro h x
      exact ⟨(hpres σ (x : q.adicCompletion L)).mpr x.2,
        (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := mm ^ (n+1))
          (actFun σ x) x).mpr (h x)⟩
  have actFun_mem : ∀ (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      {y : B}, y ∈ mm → actFun σ y ∈ mm := by
    intro σ y hy
    show ¬ IsUnit (actFun σ y)
    intro hu
    exact (show ¬ IsUnit y from hy) (by simpa using hu.map (actFun σ.symm).toMonoidHom)
  -- ### (A) commutators of the higher ramification subgroups
  have hcommA : ∀ (i j : ℕ), 1 ≤ i → 1 ≤ j → ⁅Gs i, Gs j⁆ ≤ Gs (i + j) := by
    intro i j hi hj
    rw [Subgroup.commutator_le]
    intro σ hσ τ hτ
    rw [hmem_iff (i + j) ⁅σ, τ⁆]
    intro x
    have hσ' : ∀ y : B, actFun σ y - y ∈ mm ^ (i + 1) := (hmem_iff i σ).mp hσ
    have hτ' : ∀ y : B, actFun τ y - y ∈ mm ^ (j + 1) := (hmem_iff j τ).mp hτ
    have hcomm : actFun ⁅σ, τ⁆ = ⁅actFun σ, actFun τ⁆ := by
      have := map_commutatorElement actHom (g₁ := σ) (g₂ := τ)
      exact this
    rw [hcomm]
    exact commutator_sub_mem_pow mm (actFun σ) (actFun τ) (fun y hy => actFun_mem σ hy)
      (fun y hy => actFun_mem τ hy) hσ' hτ' x
  have hmem0 : ∀ (ρ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L),
      ρ ∈ Gs 0 → ∀ x : B, actFun ρ x - x ∈ mm := by
    intro ρ hρ x
    have h := (hmem_iff 0 ρ).mp hρ x
    rwa [zero_add, pow_one] at h
  have hcommB : ⁅Gs 0, Gs 0⁆ ≤ Gs 1 := by
    obtain ⟨π, hπval, hπ⟩ :=
      Commons.NumberTheory.NumberField.Completion.exists_uniformizer_adicCompletionIntegers q
    have hπmem : π ∈ mm := by
      rw [hmmdef, hπ]
      exact Ideal.mem_span_singleton.mpr ⟨1, by ring⟩
    have hπ0 : π ≠ 0 := by
      intro h0
      have h := hπval
      rw [h0] at h
      rw [show ((0 : B) : q.adicCompletion L) = 0 from rfl, map_zero] at h
      exact WithZero.exp_ne_zero h.symm
    have hcvex : ∀ σ : ↥(Gs 0), ∃ c : B,
        actFun (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) π = c * π := by
      intro σ
      have hmem : actFun (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) π
          ∈ IsLocalRing.maximalIdeal B :=
        actFun_mem (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) hπmem
      have hmem' : actFun (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) π
          ∈ Ideal.span {π} := hπ ▸ hmem
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hmem'
      exact ⟨c, by rw [hc, mul_comm]⟩
    have hcvuniq : ∀ σ : ↥(Gs 0), ∃! c : B,
        actFun (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) π = c * π := by
      intro σ
      obtain ⟨c, hc⟩ := hcvex σ
      refine ⟨c, hc, ?_⟩
      intro d hd
      have h : (c - d) * π = 0 := by rw [sub_mul, ← hc, ← hd, sub_self]
      rcases mul_eq_zero.mp h with h' | h'
      · exact (sub_eq_zero.mp h').symm
      · exact absurd h' hπ0
    let cval : ↥(Gs 0) → B := fun σ => Classical.choose (hcvuniq σ)
    have hcval : ∀ σ : ↥(Gs 0),
        actFun (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) π = cval σ * π :=
      fun σ => (Classical.choose_spec (hcvuniq σ)).1
    have hcvone : cval 1 * π = π := by
      rw [← hcval 1]
      rw [show ((1 : ↥(Gs 0)) :
          q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) = 1 from rfl]
      rw [actFun_one]
      rfl
    have hcval_one : cval 1 = 1 := by
      refine mul_right_cancel₀ hπ0 ?_
      rw [hcvone, one_mul]
    have hcval_mul : ∀ σ τ : ↥(Gs 0),
        cval (σ * τ) - cval σ * cval τ ∈ mm := by
      intro σ τ
      have h1 : cval (σ * τ) * π =
          actFun (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
            (cval τ) * (cval σ * π) := by
        rw [← hcval (σ * τ)]
        rw [show actFun ((σ * τ : ↥(Gs 0)) :
              q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
            = actFun (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) *
              actFun (τ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
            from rfl]
        rw [RingAut.mul_apply]
        rw [hcval τ]
        rw [map_mul]
        rw [hcval σ]
      have heq : cval (σ * τ) =
          actFun (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) (cval τ)
            * cval σ := by
        refine mul_right_cancel₀ hπ0 ?_
        rw [h1]
        ring
      have h3 : actFun (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) (cval τ)
          - cval τ ∈ mm := hmem0 _ σ.2 (cval τ)
      have h4 : cval (σ * τ) - cval σ * cval τ =
          (actFun (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) (cval τ)
            - cval τ) * cval σ := by
        rw [heq]; ring
      rw [h4]
      exact Ideal.mul_mem_right (cval σ) mm h3
    have hchi_hom : ∀ σ τ : ↥(Gs 0),
        Ideal.Quotient.mk mm (cval (σ * τ)) =
          Ideal.Quotient.mk mm (cval σ) * Ideal.Quotient.mk mm (cval τ) := by
      intro σ τ
      rw [← map_mul (Ideal.Quotient.mk mm)]
      rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      exact hcval_mul σ τ
    have hchi_one : Ideal.Quotient.mk mm (cval 1) = 1 := by rw [hcval_one, map_one]
    rw [Subgroup.commutator_le]
    intro σ hσ τ hτ
    rw [hmem_iff 1 ⁅σ, τ⁆]
    intro x
    have hγmem : ⁅σ, τ⁆ ∈ Gs 0 :=
      mul_mem (mul_mem (mul_mem hσ hτ) (inv_mem hσ)) (inv_mem hτ)
    have hσi : σ⁻¹ ∈ Gs 0 := inv_mem hσ
    have hτi : τ⁻¹ ∈ Gs 0 := inv_mem hτ
    have ha : Ideal.Quotient.mk mm (cval ⟨σ, hσ⟩) *
        Ideal.Quotient.mk mm (cval ⟨σ⁻¹, hσi⟩) = 1 := by
      have h := hchi_hom ⟨σ, hσ⟩ ⟨σ⁻¹, hσi⟩
      rw [show (⟨σ, hσ⟩ * ⟨σ⁻¹, hσi⟩ : ↥(Gs 0)) = 1 from
        Subtype.ext (mul_inv_cancel σ)] at h
      exact h.symm.trans hchi_one
    have hb : Ideal.Quotient.mk mm (cval ⟨τ, hτ⟩) *
        Ideal.Quotient.mk mm (cval ⟨τ⁻¹, hτi⟩) = 1 := by
      have h := hchi_hom ⟨τ, hτ⟩ ⟨τ⁻¹, hτi⟩
      rw [show (⟨τ, hτ⟩ * ⟨τ⁻¹, hτi⟩ : ↥(Gs 0)) = 1 from
        Subtype.ext (mul_inv_cancel τ)] at h
      exact h.symm.trans hchi_one
    have hγzero : Ideal.Quotient.mk mm (cval ⟨⁅σ, τ⁆, hγmem⟩) = 1 := by
      have h1 : Ideal.Quotient.mk mm (cval ⟨⁅σ, τ⁆, hγmem⟩) =
          Ideal.Quotient.mk mm (cval ⟨σ, hσ⟩) * Ideal.Quotient.mk mm (cval ⟨τ, hτ⟩) *
            Ideal.Quotient.mk mm (cval ⟨σ⁻¹, hσi⟩) *
              Ideal.Quotient.mk mm (cval ⟨τ⁻¹, hτi⟩) := by
        rw [show (⟨⁅σ, τ⁆, hγmem⟩ : ↥(Gs 0)) =
            ⟨σ, hσ⟩ * ⟨τ, hτ⟩ * ⟨σ⁻¹, hσi⟩ * ⟨τ⁻¹, hτi⟩ from Subtype.ext rfl]
        rw [hchi_hom, hchi_hom, hchi_hom]
      rw [h1]
      have hprod : Ideal.Quotient.mk mm (cval ⟨σ, hσ⟩) * Ideal.Quotient.mk mm (cval ⟨τ, hτ⟩) *
            Ideal.Quotient.mk mm (cval ⟨σ⁻¹, hσi⟩) *
              Ideal.Quotient.mk mm (cval ⟨τ⁻¹, hτi⟩) =
          (Ideal.Quotient.mk mm (cval ⟨σ, hσ⟩) * Ideal.Quotient.mk mm (cval ⟨σ⁻¹, hσi⟩)) *
            (Ideal.Quotient.mk mm (cval ⟨τ, hτ⟩) *
              Ideal.Quotient.mk mm (cval ⟨τ⁻¹, hτi⟩)) := by
        ring
      rw [hprod, ha, hb, mul_one]
    have hcval_1 : cval ⟨⁅σ, τ⁆, hγmem⟩ - 1 ∈ mm := by
      rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      rw [map_one, hγzero]
    have hπγ : actFun ⁅σ, τ⁆ π - π ∈ mm ^ 2 := by
      have h1 : actFun ⁅σ, τ⁆ π = cval ⟨⁅σ, τ⁆, hγmem⟩ * π := hcval ⟨⁅σ, τ⁆, hγmem⟩
      rw [h1]
      have h2 : cval ⟨⁅σ, τ⁆, hγmem⟩ * π - π =
          (cval ⟨⁅σ, τ⁆, hγmem⟩ - 1) * π := by ring
      rw [h2, pow_two]
      exact Ideal.mul_mem_mul hcval_1 hπmem
    have hkey : ∀ y ∈ mm, actFun ⁅σ, τ⁆ y - y ∈ mm ^ 2 := by
      intro y hy
      have hy' : y ∈ Ideal.span {π} := by
        rw [← hπ, ← hmmdef]
        exact hy
      obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.mp hy'
      have hderiv : actFun ⁅σ, τ⁆ (π * t) - π * t =
          actFun ⁅σ, τ⁆ t * (actFun ⁅σ, τ⁆ π - π) + (actFun ⁅σ, τ⁆ t - t) * π := by
        rw [map_mul]; ring
      rw [hderiv]
      refine add_mem (Ideal.mul_mem_left (mm ^ 2) (actFun ⁅σ, τ⁆ t) hπγ) ?_
      rw [pow_two]
      exact Ideal.mul_mem_mul (hmem0 _ hγmem t) hπmem
    have hunits : ∀ u : B, IsUnit u → actFun ⁅σ, τ⁆ u - u ∈ mm ^ 2 := by
      intro u hu
      obtain ⟨uu, huu⟩ := hu
      have hu2 : IsUnit u := ⟨uu, huu⟩
      haveI : Finite (IsLocalRing.ResidueField B) :=
        Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion L q
      haveI : Fintype (IsLocalRing.ResidueField B) := Fintype.ofFinite _
      haveI : Fintype (IsLocalRing.ResidueField B)ˣ := Fintype.ofFinite _
      set N := Fintype.card (IsLocalRing.ResidueField B) - 1 with hNdef
      set ru : IsLocalRing.ResidueField B := IsLocalRing.residue B u with hrudef
      have hru : ru ≠ 0 := by
        rw [hrudef, IsLocalRing.residue_ne_zero_iff_isUnit]
        exact hu2
      have hNcard : N = Fintype.card (IsLocalRing.ResidueField B)ˣ := by
        rw [hNdef, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
          Nat.card_units (IsLocalRing.ResidueField B)]
      have huN : u ^ N - 1 ∈ mm := by
        have h1 : IsLocalRing.residue B (u ^ N) = 1 := by
          rw [map_pow, ← hrudef]
          have h2 : (Units.map (IsLocalRing.residue B).toMonoidHom uu) ^ N = 1 := by
            rw [hNcard]; exact pow_card_eq_one
          have h3 := congrArg (fun z : (IsLocalRing.ResidueField B)ˣ =>
            (z : IsLocalRing.ResidueField B)) h2
          have h4 : ((Units.map (IsLocalRing.residue B).toMonoidHom uu :
              (IsLocalRing.ResidueField B)ˣ) : IsLocalRing.ResidueField B) = ru := by
            rw [hrudef, ← huu]
            rfl
          rw [← h4]
          exact h3
        rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_one, h1, sub_self]
      have hkey2 : (actFun ⁅σ, τ⁆ u) ^ N - u ^ N ∈ mm ^ 2 := by
        rw [← map_pow]
        have h1 : u ^ N = 1 + (u ^ N - 1) := by ring
        rw [h1]
        rw [show actFun ⁅σ, τ⁆ (1 + (u ^ N - 1)) - (1 + (u ^ N - 1)) =
            actFun ⁅σ, τ⁆ (u ^ N - 1) - (u ^ N - 1) from by rw [map_add, map_one]; ring]
        exact hkey (u ^ N - 1) huN
      set Z : B := ∑ i ∈ Finset.range N, (actFun ⁅σ, τ⁆ u) ^ i * u ^ (N - 1 - i) with hZdef
      have hfac : (actFun ⁅σ, τ⁆ u) ^ N - u ^ N = (actFun ⁅σ, τ⁆ u - u) * Z := by
        rw [hZdef]
        exact (Commute.mul_geom_sum₂ (Commute.all _ _) N).symm
      have hresγu : IsLocalRing.residue B (actFun ⁅σ, τ⁆ u) = ru := by
        have h := hmem0 ⁅σ, τ⁆ hγmem u
        rw [← IsLocalRing.residue_eq_zero_iff] at h
        rw [map_sub] at h
        rw [hrudef]
        exact sub_eq_zero.mp h
      have hZres : IsLocalRing.residue B Z =
          (N : IsLocalRing.ResidueField B) * ru ^ (N - 1) := by
        rw [hZdef, map_sum]
        have h1 : ∀ i ∈ Finset.range N,
            IsLocalRing.residue B ((actFun ⁅σ, τ⁆ u) ^ i * u ^ (N - 1 - i)) = ru ^ (N - 1) := by
          intro i hi
          have hi' : i ≤ N - 1 := by
            have := Finset.mem_range.mp hi
            omega
          rw [map_mul, map_pow, map_pow, hresγu, hrudef]
          rw [← pow_add, show i + (N - 1 - i) = N - 1 from by omega]
        rw [Finset.sum_congr rfl h1]
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hNne : (N : IsLocalRing.ResidueField B) ≠ 0 := by
        have hN1 : 1 ≤ Fintype.card (IsLocalRing.ResidueField B) := Fintype.card_pos
        rw [hNdef, Nat.cast_sub hN1, FiniteField.cast_card_eq_zero, Nat.cast_one, zero_sub]
        exact neg_ne_zero.mpr (one_ne_zero : (1 : IsLocalRing.ResidueField B) ≠ 0)
      have hZunit : IsUnit Z := by
        rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hZres]
        exact mul_ne_zero hNne (pow_ne_zero _ hru)
      have hstep : (actFun ⁅σ, τ⁆ u - u) * Z ∈ mm ^ 2 := by
        rw [← hfac]; exact hkey2
      obtain ⟨z, hz⟩ := hZunit
      have heq : (actFun ⁅σ, τ⁆ u - u) * Z * ↑(z⁻¹) = actFun ⁅σ, τ⁆ u - u := by
        rw [← hz, mul_assoc, Units.mul_inv, mul_one]
      have hfin := Ideal.mul_mem_right (↑(z⁻¹)) (mm ^ 2) hstep
      rw [heq] at hfin
      exact hfin
    exact sub_sq_mem_of_uniformizer_congruence hπ (actFun ⁅σ, τ⁆)
      (fun y hy => actFun_mem ⁅σ, τ⁆ hy)
      (hmem0 _ hγmem) hπγ hunits x

  -- ### (C) the unramified quotient is abelian
  have hcommC : ⁅(⊤ : Subgroup (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)),
      (⊤ : Subgroup (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L))⁆ ≤ Gs 0 := by
    obtain ⟨ρ, hρker, hρrange⟩ :=
      Commons.NumberTheory.NumberField.Completion.residueActionHom_adicCompletion Q q hq
    haveI hcyc : IsCyclic ρ.range := by
      rw [hρrange]
      haveI : Finite (IsLocalRing.ResidueField (q.adicCompletionIntegers L)) :=
        Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion L q
      letI : Algebra (IsLocalRing.ResidueField (Q.adicCompletionIntegers K))
          (IsLocalRing.ResidueField (q.adicCompletionIntegers L)) :=
        (Commons.NumberTheory.NumberField.Completion.natResidueMap Q q hq).toAlgebra
      exact (Commons.NumberTheory.NumberField.Completion.fixSubgroupMulEquiv
        (Commons.NumberTheory.NumberField.Completion.natResidueMap Q q hq)).isCyclic.mpr
        inferInstance
    haveI : IsMulCommutative ρ.range := inferInstance
    rw [Subgroup.commutator_le]
    intro σ _ τ _
    rw [hmem_iff 0 ⁅σ, τ⁆]
    intro x
    rw [Nat.zero_add, pow_one]
    have h1 : ρ ⁅σ, τ⁆ = 1 := by
      rw [map_commutatorElement ρ (g₁ := σ) (g₂ := τ)]
      refine commutatorElement_eq_one_iff_mul_comm.mpr ?_
      have h := IsMulCommutative.is_comm.comm (⟨ρ σ, ⟨σ, rfl⟩⟩ : ρ.range) ⟨ρ τ, ⟨τ, rfl⟩⟩
      have h' := congrArg (fun z : ρ.range => (z : RingAut
        (IsLocalRing.ResidueField (q.adicCompletionIntegers L)))) h
      simpa using h'
    have h3 : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (⁅σ, τ⁆ (x : q.adicCompletion L) - (x : q.adicCompletion L)) < 1 :=
      (hρker ⁅σ, τ⁆).mp (by rw [MonoidHom.mem_ker]; exact h1) x
    refine (Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one
      q (actFun ⁅σ, τ⁆ x - x)).mpr ?_
    rw [show ((actFun ⁅σ, τ⁆ x - x : B) : q.adicCompletion L) =
      ⁅σ, τ⁆ (x : q.adicCompletion L) - (x : q.adicCompletion L) from by
        rw [AddSubgroupClass.coe_sub, actFun_coe]]
    exact h3
  -- ### assembly
  let Gd : ℕ → Subgroup (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
    fun n => match n with | 0 => ⊤ | (k + 1) => Gs k
  have hGd_zero : Gd 0 = ⊤ := rfl
  have hGd_succ : ∀ k, Gd (k + 1) = Gs k := fun k => rfl
  have hGdstep : ∀ k, ⁅Gd k, Gd k⁆ ≤ Gd (k + 1) := by
    intro k
    match k with
    | 0 =>
      rw [hGd_zero, hGd_succ 0]
      exact hcommC
    | 1 =>
      rw [hGd_succ 0, hGd_succ 1]
      exact hcommB
    | (m + 2) =>
      rw [hGd_succ (m + 1), hGd_succ (m + 2)]
      refine le_trans (hcommA (m + 1) (m + 1) (by omega) (by omega)) ?_
      exact hGanti (by omega)
  have hder : ∀ k, derivedSeries (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) k
      ≤ Gd k := by
    intro k
    induction k with
    | zero => exact le_top
    | succ k ih =>
      rw [derivedSeries_succ]
      exact le_trans (Subgroup.commutator_mono ih ih) (hGdstep k)
  haveI : Fintype (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
    Fintype.ofFinite _
  obtain ⟨N, hN⟩ := exists_eq_bot_of_iInf_eq_bot_of_antitone Gs hGanti hGinf
  refine ⟨⟨N + 1, ?_⟩⟩
  have h := hder (N + 1)
  rw [hGd_succ N, hN] at h
  exact le_bot_iff.mp h

/-! ## The target -/

theorem finite_groupCohomology_two_units_adicCompletion_of_isGalois
    {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    Finite (groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) (q.adicCompletion L)) 2) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  haveI hFD : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hGal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion Q q hq
  exact Commons.NumberTheory.NumberField.Completion.finite_groupCohomology_two_units_of_solvable
    Q (solvable_algEquiv_adicCompletion_aux Q q hq)

end Commons.NumberTheory.NumberField.Completion
