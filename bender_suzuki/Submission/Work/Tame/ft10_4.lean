import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau
import Submission.Work.Tame.Chapter10
import Submission.Work.Tame.Hyp
import Submission.Work.Tame.ft10_3
import Submission.Work.Clifford.galoisChar_mem_Irr
import Submission.Work.Clifford.exists_aut_of_isPrimitiveRoot_pow
import Submission.Work.CNOdd.trace_mem_adjoin_primitiveRoot

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

noncomputable section

open Classical

namespace Work.Tame

universe u

variable {X : Type*} [Group X] [Fintype X]

/-! ## Step 1: a ring endomorphism of `ℂ` commutes with the Dade map `τ` -/

/-- A ring endomorphism of `ℂ` commutes with induction: it distributes over the rational scalar
`|H|⁻¹` and over the finite sum of values of `φ`. -/
theorem map_indFun {K : Subgroup X} (σ : ℂ →+* ℂ) (φ : ↥K → ℂ) (x : X) :
    σ (Induction.indFun K φ x) = Induction.indFun K (fun h => σ (φ h)) x := by
  rw [Induction.indFun_apply_def, Induction.indFun_apply_def, map_mul, map_inv₀, map_natCast,
    map_sum]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : y * x * y⁻¹ ∈ K
  · rw [dif_pos hy, dif_pos hy]
  · rw [dif_neg hy, dif_neg hy, map_zero]

theorem map_alphaI1LM {Lhat : Set X} (K : Subgroup X) (σ : ℂ →+* ℂ)
    (α : ↥(Lgrp Lhat) → ℂ) (N : ↥(Lgrp (K : Set X))) :
    σ (alphaI1LM Lhat K α N) = alphaI1LM Lhat K (fun m => σ (α m)) N := rfl

theorem map_alphaI2LM {Lhat : Set X} (K : Subgroup X) (σ : ℂ →+* ℂ)
    (α : ↥(Lgrp Lhat) → ℂ) (N : ↥(Lgrp (K : Set X))) :
    σ (alphaI2LM Lhat K α N) = alphaI2LM Lhat K (fun m => σ (α m)) N := by
  rw [alphaI2LM_apply, alphaI2LM_apply, map_indFun]

/-- **A ring endomorphism of `ℂ` commutes with `τ`.**  For any `σ : ℂ →+* ℂ`, any class
function `α` of `𝔏 = N(L̂)` and any `x : X`:
`σ ((τ α) x) = τ (fun m => σ (α m)) x`.  This is purely structural: the right hand side of (9.4)
is a rational combination of values `α m` at fixed elements `m` of `𝔏`. -/
theorem ft10_4_tau_map {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X} (σ : ℂ →+* ℂ)
    (α : ↥(Lgrp Lhat) → ℂ) (x : X) :
    σ (tau Lhat n Hs α x) = tau Lhat n Hs (fun m => σ (α m)) x := by
  rw [tau_apply, tau_apply, map_add, map_sum]
  congr 1
  · exact map_indFun σ α x
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_indFun]
    congr 1
    funext N
    simp only [Pi.sub_apply, map_sub, map_alphaI1LM, map_alphaI2LM]

/-! ## Step 2: values of virtual characters lie in the cyclotomic field `ℚ_a` -/

/-- An irreducible character of a finite group takes at `g` a value in `ℚ(ζ_a)` whenever
`orderOf g ∣ a`: it is the trace of a representation element of order dividing `a`, hence a sum
of `a`-th roots of unity. -/
theorem irr_apply_mem_adjoin {G : Type*} [Group G] [Fintype G] {χ : G → ℂ}
    (hχ : χ ∈ CharCore.Irr G) {a : ℕ} (ha : 0 < a) {g : G} (hg : orderOf g ∣ a) :
    χ g ∈ Algebra.adjoin ℚ ({z : ℂ | z ^ a = 1} : Set ℂ) := by
  obtain ⟨V, -, hVχ⟩ := (CharCore.mem_Irr_iff_fdrep (G := G) χ).mp hχ
  have hga : g ^ a = 1 := orderOf_dvd_iff_pow_eq_one.mp hg
  have hT : (V.ρ g) ^ a = 1 := by rw [← map_pow, hga, map_one]
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ a :=
    ⟨_, Complex.isPrimitiveRoot_exp a ha.ne'⟩
  have htrace := Work.CNOdd.trace_mem_adjoin_primitiveRoot (V.ρ g) ha hT hζ
  have hsub : Algebra.adjoin ℚ ({ζ} : Set ℂ) ≤
      Algebra.adjoin ℚ ({z : ℂ | z ^ a = 1} : Set ℂ) :=
    Algebra.adjoin_mono (by
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hζ.pow_eq_one)
  rw [← hVχ]
  exact hsub htrace

/-- **Value of a virtual character at an element whose order divides `a`.**  `ℚ_a` is closed
under addition and integer multiples, and the irreducible characters take there the values
supplied by `irr_apply_mem_adjoin`. -/
theorem ft10_4_vchar_apply {G : Type*} [Group G] [Fintype G] {χ : G → ℂ}
    (hχ : CharCore.IsVChar χ) {a : ℕ} (ha : 0 < a) {g : G} (hg : orderOf g ∣ a) :
    χ g ∈ Algebra.adjoin ℚ ({z : ℂ | z ^ a = 1} : Set ℂ) := by
  obtain ⟨c, rfl⟩ := (CharCore.isVChar_iff_exists_int_coeffs (G := G) (f := χ)).mp hχ
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  refine Subalgebra.sum_mem _ (t := Finset.univ) (fun χ _ => ?_)
  exact Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ (c χ)) (irr_apply_mem_adjoin χ.2 ha hg)

/-! ## Step 3: the norm-one endgame -/

/-- Pairing the function identity of the endgame with an irreducible character `θ`. -/
private theorem endgame_pair {G : Type*} [Group G] [Fintype G] {χ ψ θ : G → ℂ}
    {ε δ : ℂ} {D E : ℕ} (σ : ℂ ≃+* ℂ) (hσε : σ ε = ε) (hσδ : σ δ = δ)
    (hfun : ∀ g : G, (D : ℂ) * σ (ε * χ g) - (E : ℂ) * σ (δ * ψ g)
        = (D : ℂ) * (ε * χ g) - (E : ℂ) * (δ * ψ g))
    (hχ' : (fun g => σ (χ g)) ∈ Work.Coherence.Irr G)
    (hψ' : (fun g => σ (ψ g)) ∈ Work.Coherence.Irr G)
    (hχ : χ ∈ Work.Coherence.Irr G) (hψ : ψ ∈ Work.Coherence.Irr G)
    (hθ : θ ∈ Work.Coherence.Irr G) :
    (D : ℂ) * ε * (if (fun g => σ (χ g)) = θ then 1 else 0)
        - (E : ℂ) * δ * (if (fun g => σ (ψ g)) = θ then 1 else 0)
      = (D : ℂ) * ε * (if χ = θ then 1 else 0) - (E : ℂ) * δ * (if ψ = θ then 1 else 0) := by
  have key := congrArg (fun f => Work.Coherence.cfInner f θ) (funext hfun)
  have h1 : (fun g : G => (D : ℂ) * σ (ε * χ g) - (E : ℂ) * σ (δ * ψ g))
      = (D : ℂ) • (ε • (fun g => σ (χ g))) - (E : ℂ) • (δ • (fun g => σ (ψ g))) := by
    funext g
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_mul, hσε, hσδ]
  have h2 : (fun g : G => (D : ℂ) * (ε * χ g) - (E : ℂ) * (δ * ψ g))
      = (D : ℂ) • (ε • χ) - (E : ℂ) • (δ • ψ) := by
    funext g
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [h1, h2] at key
  simp only [Work.Coherence.cfInner_sub_left, Work.Coherence.cfInner_smul_left] at key
  rw [Work.Clifford.cfInner_eq_ite_of_mem_Irr_coherence hχ' hθ,
    Work.Clifford.cfInner_eq_ite_of_mem_Irr_coherence hψ' hθ,
    Work.Clifford.cfInner_eq_ite_of_mem_Irr_coherence hχ hθ,
    Work.Clifford.cfInner_eq_ite_of_mem_Irr_coherence hψ hθ] at key
  simpa only [mul_assoc] using key

/-- The endgame with explicit signs: if `P = ε • χ`, `Q = δ • ψ` with distinct irreducible
`χ, ψ` and `ε, δ = ±1`, and the function identity and degree identity of Feit–Thompson's
Lemma 10.4 hold, then `σ` fixes `χ` pointwise. -/
private theorem endgame_signs {G : Type*} [Group G] [Fintype G] {χ ψ : G → ℂ}
    (hχC : χ ∈ Work.Coherence.Irr G) (hψC : ψ ∈ Work.Coherence.Irr G) (hne : χ ≠ ψ)
    (σ : ℂ ≃+* ℂ) {ε δ : ℂ} (hε : ε = 1 ∨ ε = -1) (hδ : δ = 1 ∨ δ = -1)
    {D E : ℕ} (hD : 0 < D) (hE : 0 < E)
    (hfun : ∀ g : G, (D : ℂ) * σ (ε * χ g) - (E : ℂ) * σ (δ * ψ g)
        = (D : ℂ) * (ε * χ g) - (E : ℂ) * (δ * ψ g))
    (hdeg : (D : ℂ) * (ε * χ 1) = (E : ℂ) * (δ * ψ 1)) :
    ∀ g : G, σ (χ g) = χ g := by
  have hχ' : (fun g => σ (χ g)) ∈ Work.Coherence.Irr G :=
    Work.Clifford.galoisChar_mem_Irr σ hχC
  have hψ' : (fun g => σ (ψ g)) ∈ Work.Coherence.Irr G :=
    Work.Clifford.galoisChar_mem_Irr σ hψC
  have hσε : σ ε = ε := by rcases hε with h | h <;> simp [h]
  have hσδ : σ δ = δ := by rcases hδ with h | h <;> simp [h]
  have hDε : (D : ℂ) * ε ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · exact_mod_cast hD.ne'
    · rcases hε with h | h <;> simp [h]
  by_cases hcase : (fun g : G => σ (χ g)) = χ
  · intro g; exact congrFun hcase g
  · exfalso
    have peq := endgame_pair σ hσε hσδ hfun hχ' hψ' hχC hψC hχC
    rw [if_neg hcase, if_pos rfl, if_neg (fun h : ψ = χ => hne h.symm)] at peq
    simp only [mul_zero, mul_one, zero_sub, sub_zero] at peq
    by_cases hZ : (fun g : G => σ (ψ g)) = χ
    · have hEδ : (E : ℂ) * δ = -((D : ℂ) * ε) := by
        rw [if_pos hZ, mul_one] at peq
        exact neg_eq_iff_eq_neg.mp peq
      have hd : (D : ℂ) * ε * (χ 1) = (E : ℂ) * δ * (ψ 1) := by
        have h := hdeg
        rw [← mul_assoc, ← mul_assoc] at h
        exact h
      rw [hEδ] at hd
      have hzero : ((D : ℂ) * ε) * ((χ 1) + (ψ 1)) = 0 := by
        rw [mul_add, hd]; ring
      have hsum : (χ 1) + (ψ 1) = 0 := (mul_eq_zero.mp hzero).resolve_left hDε
      obtain ⟨n, hn, hχn⟩ := Work.Coherence.irr_degree_pos hχC
      obtain ⟨m, hm, hψm⟩ := Work.Coherence.irr_degree_pos hψC
      rw [hχn, hψm] at hsum
      have hcast : ((n + m : ℕ) : ℂ) = 0 := by
        push_cast
        exact hsum
      have hnm : n + m = 0 := by exact_mod_cast hcast
      omega
    · rw [if_neg hZ] at peq
      simp only [mul_zero, neg_zero] at peq
      exact hDε peq.symm

/-- **The norm-one endgame of Feit–Thompson Lemma 10.4.** -/
theorem ft10_4_endgame {G : Type*} [Group G] [Fintype G] (σ : ℂ ≃+* ℂ) {P Q : G → ℂ}
    (hP : CharCore.IsVChar P) (hQ : CharCore.IsVChar Q)
    (hPn : Coherence.cfInner P P = 1) (hQn : Coherence.cfInner Q Q = 1)
    (hPQ : Coherence.cfInner P Q = 0) {D E : ℕ} (hD : 0 < D) (hE : 0 < E)
    (hfun : ∀ g : G, (D : ℂ) * σ (P g) - (E : ℂ) * σ (Q g) = (D : ℂ) * P g - (E : ℂ) * Q g)
    (hdeg : (D : ℂ) * P 1 = (E : ℂ) * Q 1) :
    ∀ g : G, σ (P g) = P g := by
  obtain ⟨χ, hχIrr, hPcase⟩ := CharCore.vchar_norm_one hP hPn
  obtain ⟨ψ, hψIrr, hQcase⟩ := CharCore.vchar_norm_one hQ hQn
  have hχC : χ ∈ Coherence.Irr G := CharCore.mem_Irr_iff_coherence.mp hχIrr
  have hψC : ψ ∈ Coherence.Irr G := CharCore.mem_Irr_iff_coherence.mp hψIrr
  have hne : χ ≠ ψ := by
    rintro rfl
    have hPQne : Coherence.cfInner P Q ≠ 0 := by
      rcases hPcase with hPχ | hPχ <;> rcases hQcase with hQψ | hQψ
      · rw [hQψ] at hQn
        rw [hPχ, hQψ, hQn]; norm_num
      · rw [hQψ, Coherence.cfInner_neg_left, Coherence.cfInner_neg_right, neg_neg] at hQn
        rw [hPχ, hQψ, Coherence.cfInner_neg_right, hQn]; norm_num
      · rw [hQψ] at hQn
        rw [hPχ, hQψ, Coherence.cfInner_neg_left, hQn]; norm_num
      · rw [hQψ, Coherence.cfInner_neg_left, Coherence.cfInner_neg_right, neg_neg] at hQn
        rw [hPχ, hQψ, Coherence.cfInner_neg_left, Coherence.cfInner_neg_right, neg_neg, hQn]
        norm_num
    rw [hPQ] at hPQne
    exact hPQne rfl
  rcases hPcase with hPχ | hPχ <;> rcases hQcase with hQψ | hQψ
  · have hfun' : ∀ g : G, (D : ℂ) * σ ((1 : ℂ) * χ g) - (E : ℂ) * σ ((1 : ℂ) * ψ g)
        = (D : ℂ) * ((1 : ℂ) * χ g) - (E : ℂ) * ((1 : ℂ) * ψ g) := by
      intro g
      have h := hfun g
      rw [hPχ, hQψ] at h
      simpa using h
    have hdeg' : (D : ℂ) * ((1 : ℂ) * χ 1) = (E : ℂ) * ((1 : ℂ) * ψ 1) := by
      have h := hdeg
      rw [hPχ, hQψ] at h
      simpa using h
    have hgoal := endgame_signs hχC hψC hne σ (Or.inl rfl) (Or.inl rfl) hD hE hfun' hdeg'
    intro g
    rw [hPχ]
    exact hgoal g
  · have hfun' : ∀ g : G, (D : ℂ) * σ ((1 : ℂ) * χ g) - (E : ℂ) * σ ((-1 : ℂ) * ψ g)
        = (D : ℂ) * ((1 : ℂ) * χ g) - (E : ℂ) * ((-1 : ℂ) * ψ g) := by
      intro g
      have h := hfun g
      rw [hPχ, hQψ] at h
      simp only [Pi.neg_apply] at h
      simpa using h
    have hdeg' : (D : ℂ) * ((1 : ℂ) * χ 1) = (E : ℂ) * ((-1 : ℂ) * ψ 1) := by
      have h := hdeg
      rw [hPχ, hQψ] at h
      simpa using h
    have hgoal := endgame_signs hχC hψC hne σ (Or.inl rfl) (Or.inr rfl) hD hE hfun' hdeg'
    intro g
    rw [hPχ]
    exact hgoal g
  · have hfun' : ∀ g : G, (D : ℂ) * σ ((-1 : ℂ) * χ g) - (E : ℂ) * σ ((1 : ℂ) * ψ g)
        = (D : ℂ) * ((-1 : ℂ) * χ g) - (E : ℂ) * ((1 : ℂ) * ψ g) := by
      intro g
      have h := hfun g
      rw [hPχ, hQψ] at h
      simp only [Pi.neg_apply] at h
      simpa using h
    have hdeg' : (D : ℂ) * ((-1 : ℂ) * χ 1) = (E : ℂ) * ((1 : ℂ) * ψ 1) := by
      have h := hdeg
      rw [hPχ, hQψ] at h
      simpa using h
    have hgoal := endgame_signs hχC hψC hne σ (Or.inr rfl) (Or.inl rfl) hD hE hfun' hdeg'
    intro g
    rw [hPχ]
    simp only [Pi.neg_apply, map_neg]
    exact congrArg Neg.neg (hgoal g)
  · have hfun' : ∀ g : G, (D : ℂ) * σ ((-1 : ℂ) * χ g) - (E : ℂ) * σ ((-1 : ℂ) * ψ g)
        = (D : ℂ) * ((-1 : ℂ) * χ g) - (E : ℂ) * ((-1 : ℂ) * ψ g) := by
      intro g
      have h := hfun g
      rw [hPχ, hQψ] at h
      simp only [Pi.neg_apply] at h
      simpa using h
    have hdeg' : (D : ℂ) * ((-1 : ℂ) * χ 1) = (E : ℂ) * ((-1 : ℂ) * ψ 1) := by
      have h := hdeg
      rw [hPχ, hQψ] at h
      simpa using h
    have hgoal := endgame_signs hχC hψC hne σ (Or.inr rfl) (Or.inr rfl) hD hE hfun' hdeg'
    intro g
    rw [hPχ]
    simp only [Pi.neg_apply, map_neg]
    exact congrArg Neg.neg (hgoal g)

/-! ## Step 4: the cyclotomic fixed-field step -/

/-- **Cyclotomic fixed-field step.**  If `a ∣ m` and `c ∈ ℚ(ζ_m)` is fixed by every ring
automorphism of `ℂ` which fixes all `a`-th roots of unity, then `c ∈ ℚ(ζ_a)`. -/
theorem ft10_4_galois_fixed {a m : ℕ} (ha : 0 < a) (hm : 0 < m) (ham : a ∣ m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ m) {c : ℂ} (hc : c ∈ Algebra.adjoin ℚ ({ζ} : Set ℂ))
    (hfix : ∀ σ : ℂ ≃+* ℂ, (∀ z : ℂ, z ^ a = 1 → σ z = z) → σ c = c) :
    c ∈ Algebra.adjoin ℚ ({z : ℂ | z ^ a = 1} : Set ℂ) := by
  classical
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : NeZero a := ⟨ha.ne'⟩
  -- the primitive `a`-th root of unity `ζ ^ (m / a)`
  have hζa : IsPrimitiveRoot (ζ ^ (m / a)) a := by
    have h := hζ.pow_of_dvd (Nat.div_pos (Nat.le_of_dvd hm ham) ha).ne' (Nat.div_dvd_of_dvd ham)
    rwa [Nat.div_div_self ham hm.ne'] at h
  -- the base field `Ki = ℚ(ζ ^ (m / a))` and the cyclotomic field `L = Ki⟮ζ⟯ = ℚ(ζ)`
  let Ki : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({ζ ^ (m / a)} : Set ℂ)
  let L : IntermediateField ↥Ki ℂ := IntermediateField.adjoin ↥Ki ({ζ} : Set ℂ)
  have hζalg : IsAlgebraic ↥Ki ζ := by
    refine IsIntegral.isAlgebraic ⟨Polynomial.X ^ m - Polynomial.C 1, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub_C 1 hm.ne'
    · show Polynomial.aeval ζ (Polynomial.X ^ m - Polynomial.C 1) = 0
      rw [map_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, map_one, hζ.pow_eq_one, sub_self]
  haveI hcyc : IsCyclotomicExtension {m} ↥Ki ↥L := by
    change IsCyclotomicExtension {m} ↥Ki (IntermediateField.adjoin ↥Ki ({ζ} : Set ℂ)).toSubalgebra
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζalg]
    exact IsPrimitiveRoot.adjoin_isCyclotomicExtension ↥Ki hζ
  haveI hgal : IsGalois ↥Ki ↥L := IsCyclotomicExtension.isGalois {m} ↥Ki ↥L
  haveI hfin : FiniteDimensional ↥Ki ↥L := IsCyclotomicExtension.finiteDimensional {m} ↥Ki ↥L
  have hζLmem : ζ ∈ (L : Set ℂ) :=
    IntermediateField.subset_adjoin ↥Ki ({ζ} : Set ℂ) (Set.mem_singleton ζ)
  have hcL : c ∈ (L : Set ℂ) := by
    have hgen : (Algebra.adjoin ℚ ({ζ} : Set ℂ) : Set ℂ) ⊆ (L : Set ℂ) := by
      intro x hx
      induction hx using Algebra.adjoin_induction with
      | mem y hy =>
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact hζLmem
      | algebraMap q =>
          have h1 : (algebraMap ↥Ki ℂ (algebraMap ℚ ↥Ki q)) ∈ (L : Set ℂ) :=
            Subalgebra.algebraMap_mem _ _
          simpa using h1
      | add y z hy hz ihy ihz => exact L.add_mem ihy ihz
      | mul y z hy hz ihy ihz => exact L.mul_mem ihy ihz
    exact hgen hc
  -- every `Ki`-automorphism of `L` fixes `c`
  have key : ∀ f : Gal(↥L/↥Ki), f ⟨c, hcL⟩ = ⟨c, hcL⟩ := by
    intro f
    have hζL : IsPrimitiveRoot (⟨ζ, hζLmem⟩ : ↥L) m :=
      IsPrimitiveRoot.of_map_of_injective (f := L.val) (by simpa using hζ)
        (fun x y h => Subtype.ext h)
    have hmap : IsPrimitiveRoot (f ⟨ζ, hζLmem⟩) m :=
      hζL.map_of_injective (f := (f : ↥L →* ↥L)) f.injective
    obtain ⟨k, hklt, hkcop, hkeq⟩ := (hζL.isPrimitiveRoot_iff).mp hmap
    have hζamem : ζ ^ (m / a) ∈ (Ki : Set ℂ) :=
      IntermediateField.subset_adjoin ℚ ({ζ ^ (m / a)} : Set ℂ) (Set.mem_singleton _)
    have hζaLpow : (algebraMap ↥Ki ↥L ⟨ζ ^ (m / a), hζamem⟩ : ↥L)
        = (⟨ζ, hζLmem⟩ : ↥L) ^ (m / a) := by
      apply Subtype.ext
      change L.val (algebraMap ↥Ki ↥L ⟨ζ ^ (m / a), hζamem⟩)
        = L.val ((⟨ζ, hζLmem⟩ : ↥L) ^ (m / a))
      rw [AlgHom.commutes, map_pow, IntermediateField.algebraMap_apply]
      rfl
    have hfixζaL : f (algebraMap ↥Ki ↥L ⟨ζ ^ (m / a), hζamem⟩)
        = algebraMap ↥Ki ↥L ⟨ζ ^ (m / a), hζamem⟩ := AlgEquiv.commutes f _
    have hpoweq : (⟨ζ, hζLmem⟩ : ↥L) ^ (k * (m / a)) = (⟨ζ, hζLmem⟩ : ↥L) ^ (m / a) := by
      calc (⟨ζ, hζLmem⟩ : ↥L) ^ (k * (m / a))
          = ((⟨ζ, hζLmem⟩ : ↥L) ^ k) ^ (m / a) := by rw [pow_mul]
        _ = (f ⟨ζ, hζLmem⟩) ^ (m / a) := by rw [← hkeq]
        _ = f ((⟨ζ, hζLmem⟩ : ↥L) ^ (m / a)) := by rw [map_pow]
        _ = f (algebraMap ↥Ki ↥L ⟨ζ ^ (m / a), hζamem⟩) := by rw [hζaLpow]
        _ = algebraMap ↥Ki ↥L ⟨ζ ^ (m / a), hζamem⟩ := hfixζaL
        _ = (⟨ζ, hζLmem⟩ : ↥L) ^ (m / a) := by rw [hζaLpow]
    -- `a ∣ k - 1` when `k ≠ 0`
    have hmdvd : a ∣ k - 1 ∨ k = 0 := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · exact Or.inr hk0
      · left
        have hA : (⟨ζ, hζLmem⟩ : ↥L) ^ ((k - 1) * (m / a)) = 1 := by
          have h3 : (⟨ζ, hζLmem⟩ : ↥L) ^ ((k - 1) * (m / a) + m / a)
              = (⟨ζ, hζLmem⟩ : ↥L) ^ (m / a) := by
            rw [← hpoweq]
            congr 1
            conv_rhs => rw [show k = (k - 1) + 1 from by omega]
            rw [add_mul, one_mul]
          rw [pow_add] at h3
          have h4 : (⟨ζ, hζLmem⟩ : ↥L) ^ ((k - 1) * (m / a))
                * (⟨ζ, hζLmem⟩ : ↥L) ^ (m / a)
              = 1 * (⟨ζ, hζLmem⟩ : ↥L) ^ (m / a) := by
            rw [one_mul]
            exact h3
          exact mul_right_cancel₀ (pow_ne_zero _ (hζL.ne_zero (NeZero.ne m))) h4
        have hB : m ∣ (k - 1) * (m / a) := (hζL.pow_eq_one_iff_dvd _).mp hA
        have hC : a * (m / a) ∣ (k - 1) * (m / a) := by
          have h0 : a * (m / a) = m := by rw [mul_comm]; exact Nat.div_mul_cancel ham
          rw [h0]
          exact hB
        exact Nat.dvd_of_mul_dvd_mul_right (Nat.div_pos (Nat.le_of_dvd hm ham) ha) hC
    -- an automorphism of `ℂ` realising `ζ ↦ ζ ^ k` fixes `c`
    obtain ⟨σ, hσ⟩ := Work.Clifford.exists_aut_of_isPrimitiveRoot_pow hm hζ hkcop
    have hσζa : σ (ζ ^ (m / a)) = ζ ^ (m / a) := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        have hm1 : m = 1 := (Nat.coprime_zero_left m).mp hkcop
        subst hm1
        have ha1 : a = 1 := Nat.dvd_one.mp ham
        subst ha1
        have hζ1 : ζ = 1 := by simpa using hζ.pow_eq_one
        simp only [Nat.div_one, pow_one]
        simp [hζ1]
      · have hdvd : a ∣ k - 1 := hmdvd.resolve_right (by omega)
        calc σ (ζ ^ (m / a)) = (σ ζ) ^ (m / a) := by rw [map_pow]
          _ = (ζ ^ k) ^ (m / a) := by rw [hσ]
          _ = (ζ ^ (m / a)) ^ k := by rw [← pow_mul, ← pow_mul, Nat.mul_comm k (m / a)]
          _ = (ζ ^ (m / a)) ^ ((k - 1) + 1) := by
                conv_lhs => rw [show k = (k - 1) + 1 from by omega]
          _ = (ζ ^ (m / a)) ^ (k - 1) * (ζ ^ (m / a)) := by rw [pow_add, pow_one]
          _ = 1 * (ζ ^ (m / a)) := by rw [(hζa.pow_eq_one_iff_dvd (k - 1)).mpr hdvd]
          _ = ζ ^ (m / a) := one_mul _
    have hσroot : ∀ z : ℂ, z ^ a = 1 → σ z = z := by
      intro z hz
      obtain ⟨i, -, hi⟩ := hζa.eq_pow_of_pow_eq_one hz
      rw [← hi, map_pow, hσζa]
    have hσc : σ c = c := hfix σ hσroot
    have hσKi : ∀ x : ℂ, x ∈ (Ki : Set ℂ) → σ x = x := by
      intro x hx
      induction hx using IntermediateField.adjoin_induction with
      | mem y hy =>
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact hσζa
      | algebraMap q => exact map_ratCast σ q
      | add y z hy hz ihy ihz => rw [map_add, ihy, ihz]
      | mul y z hy hz ihy ihz => rw [map_mul, ihy, ihz]
      | inv y hy ihy => rw [map_inv₀, ihy]
    -- `σ` and `f` agree on `L`, hence `f c = σ c = c`
    let σAlg : ℂ ≃ₐ[↥Ki] ℂ := AlgEquiv.ofRingEquiv (f := σ) (fun x => by
      rw [IntermediateField.algebraMap_apply]
      exact hσKi (x : ℂ) x.2)
    have hagree : (σAlg.toAlgHom.comp L.val) = (L.val.comp f.toAlgHom) := by
      refine (hζL.powerBasis ↥Ki).algHom_ext ?_
      rw [IsPrimitiveRoot.powerBasis_gen]
      show σ ((⟨ζ, hζLmem⟩ : ↥L) : ℂ) = (f ⟨ζ, hζLmem⟩ : ℂ)
      have hcoe : ((⟨ζ, hζLmem⟩ : ↥L) : ℂ) = ζ := rfl
      rw [hcoe, hσ, ← hkeq]
      have hcoe2 : ((⟨ζ, hζLmem⟩ : ↥L) ^ k : ℂ) = ζ ^ k := by
        change L.val ((⟨ζ, hζLmem⟩ : ↥L) ^ k) = ζ ^ k
        rw [map_pow]
        rfl
      exact hcoe2.symm
    have hmain : σ c = (f ⟨c, hcL⟩ : ℂ) := by
      have h1 := congrArg (fun g => g ⟨c, hcL⟩) hagree
      simpa [σAlg] using h1
    apply Subtype.ext
    rw [← hmain, hσc]
  -- `c ∈ Ki`
  have hcKi : c ∈ (Ki : Set ℂ) := by
    obtain ⟨kKi, hkKi⟩ :=
      (IsGalois.mem_range_algebraMap_iff_fixed (F := ↥Ki) (E := ↥L) ⟨c, hcL⟩).mpr key
    have h2 := congrArg Subtype.val hkKi
    have h3 : ((kKi : ↥Ki) : ℂ) = c := by
      simpa [IntermediateField.algebraMap_apply] using h2
    rw [← h3]
    exact kKi.2
  -- `Ki = ℚ[ζ ^ (m / a)]` and `ℚ[ζ ^ (m / a)] = ℚ[{z | z ^ a = 1}]`
  have hζalgQ : IsAlgebraic ℚ (ζ ^ (m / a)) := by
    refine IsIntegral.isAlgebraic ⟨Polynomial.X ^ a - Polynomial.C 1, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub_C 1 ha.ne'
    · show Polynomial.aeval (ζ ^ (m / a)) (Polynomial.X ^ a - Polynomial.C 1) = 0
      rw [map_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, map_one, hζa.pow_eq_one, sub_self]
  have hKieq : (Ki.toSubalgebra : Subalgebra ℚ ℂ) = Algebra.adjoin ℚ ({ζ ^ (m / a)} : Set ℂ) :=
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζalgQ
  have hgenerated : Algebra.adjoin ℚ ({z : ℂ | z ^ a = 1} : Set ℂ)
      = Algebra.adjoin ℚ ({ζ ^ (m / a)} : Set ℂ) := by
    refine le_antisymm ?_ ?_
    · rw [Algebra.adjoin_le_iff]
      intro z hz
      rw [Set.mem_setOf_eq] at hz
      obtain ⟨i, -, hi⟩ := hζa.eq_pow_of_pow_eq_one hz
      rw [← hi]
      exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) i
    · rw [Algebra.adjoin_le_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact Algebra.subset_adjoin (by rw [Set.mem_setOf_eq]; exact hζa.pow_eq_one)
  rw [hgenerated, ← hKieq]
  exact hcKi

/-! ## Step 5: assembly -/

/-- The order of an element of `L̂ ∩ 𝔏` divides Feit–Thompson's exponent `a`. -/
theorem orderOf_dvd_LhatExponent {Lhat : Set X} {l : X} (hl : l ∈ Lhat)
    (hl' : l ∈ Lgrp Lhat) : orderOf l ∣ LhatExponent Lhat := by
  rw [LhatExponent]
  refine Finset.dvd_lcm ?_
  rw [Finset.mem_filter]
  refine ⟨?_, hl⟩
  change l ∈ (Finset.univ : Finset ↥(Lgrp Lhat)).sup (fun a => ({a.val} : Finset X))
  rw [Finset.mem_sup]
  exact ⟨⟨l, hl'⟩, Finset.mem_univ _, by simp⟩

/-- `a = LhatExponent Lhat` is positive: the defining `lcm` runs over a non-empty set of
positive integers (it contains `1 ∈ L̂`). -/
theorem LhatExponent_pos {Lhat : Set X} : 0 < LhatExponent Lhat := by
  rw [LhatExponent]
  refine Nat.pos_of_ne_zero (fun h0 => ?_)
  obtain ⟨b, -, hb⟩ := Finset.lcm_eq_zero_iff.mp h0
  exact (orderOf_pos b).ne' hb

/-- `a = LhatExponent Lhat` divides `|X|`: it is the lcm of orders of elements of the subgroup
`𝔏 = N(L̂)`. -/
theorem LhatExponent_dvd_card {Lhat : Set X} : LhatExponent Lhat ∣ Nat.card X := by
  rw [LhatExponent]
  exact Finset.lcm_dvd (fun b _ => orderOf_dvd_natCard b)

/-- A ring endomorphism of `ℂ` which fixes a set of generators pointwise fixes the whole
`ℚ`-subalgebra they generate. -/
theorem map_eq_self_of_mem_adjoin {σ : ℂ →+* ℂ} {s : Set ℂ} (hσ : ∀ z ∈ s, σ z = z)
    {c : ℂ} (hc : c ∈ Algebra.adjoin ℚ s) : σ c = c := by
  induction hc using Algebra.adjoin_induction with
  | mem x hx => exact hσ x hx
  | algebraMap q => exact map_ratCast σ q
  | add x y hx hy ihx ihy => rw [map_add, ihx, ihy]
  | mul x y hx hy ihx ihy => rw [map_mul, ihx, ihy]

/-- **Feit–Thompson Lemma 10.4** (p. 815).  Let `L̂` be tamely imbedded in the non-degenerate sense
`HasTameData`, and let `𝓢` be a coherent subset of `𝓘(L̂)` — formalised as `FTCoherent` together
with `∀ χ ∈ S, IsVChar χ` and `∀ χ ∈ S, χ` vanishes outside `L̂` — consisting of pairwise
orthogonal characters and containing at least two distinct irreducible characters of `𝔏`.  Let
`a = LhatExponent Lhat` be the least common multiple of the orders of the elements of `L̂`.  If
`lam` is an irreducible character in `𝓢`, then every value assumed by `lam^τ` lies in `ℚ_a`, the
field obtained from `ℚ` by adjoining the `a`-th roots of unity — formalised as membership in
`Algebra.adjoin ℚ {z : ℂ | z ^ a = 1}`.

Feit–Thompson's proof: for another irreducible `lam₁ ∈ 𝓢` one has
`lam₁(1)·lam - lam(1)·lam₁ ∈ 𝓘₀(𝓢) ⊆ 𝓘₀(L̂)`; any automorphism `σ` of `ℚ_{|𝔛|}` fixing `ℚ_a`
satisfies `σ[{(lam₁(1)lam - lam(1)lam₁)}^τ] = {(lam₁(1)σ(lam) - lam(1)σ(lam₁))}^τ` (this is where
`lam, lam₁ ∈ 𝓘(L̂)` is used: `σ` acts on the values at the elements of `L̂`, whose orders divide
`a`), whence `lam₁(1)σ(lam^τ) - lam(1)σ(lam₁^τ) = lam₁(1)lam^τ - lam(1)lam₁^τ`; since both
`lam^τ` and `lam₁^τ` have norm `1`, this forces `σ(lam^τ) = lam^τ`. -/
theorem ft10_4 {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} (h : IsTamelyImbedded Lhat n Hs) (hD : HasTameData Lhat n Hs)
    {S : Finset (↥(Lgrp Lhat) → ℂ)} (hcoh : FTCoherent Lhat n Hs S)
    (hv : ∀ χ ∈ S, CharCore.IsVChar χ)
    (hvan : ∀ χ ∈ S, ∀ l : ↥(Lgrp Lhat), (l : X) ∉ Lhat → χ l = 0)
    (horth : ∀ χ ∈ S, ∀ ψ ∈ S, χ ≠ ψ → Coherence.cfInner χ ψ = 0)
    (h2 : ∃ χ ∈ S, ∃ ψ ∈ S, χ ≠ ψ ∧ χ ∈ CharCore.Irr ↥(Lgrp Lhat) ∧
      ψ ∈ CharCore.Irr ↥(Lgrp Lhat))
    {lam : ↥(Lgrp Lhat) → ℂ} (hlam : lam ∈ S) (hirr : lam ∈ CharCore.Irr ↥(Lgrp Lhat))
    {τ' : (↥(Lgrp Lhat) → ℂ) →ₗ[ℤ] (X → ℂ)} (hτ' : IsExtension Lhat n Hs S τ') :
    ∀ x : X, τ' lam x ∈ Algebra.adjoin ℚ ({z : ℂ | z ^ LhatExponent Lhat = 1} : Set ℂ) := by
  classical
  have ha_pos : 0 < LhatExponent Lhat := LhatExponent_pos
  have ham : LhatExponent Lhat ∣ Nat.card X := LhatExponent_dvd_card
  have hm_pos : 0 < Nat.card X := Nat.card_pos
  -- a second irreducible character in `𝓢`
  obtain ⟨χ₀, hχ₀S, ψ₀, hψ₀S, hne₀, hχ₀irr, hψ₀irr⟩ := h2
  obtain ⟨lam1, hlam1S, hlam1irr, hlam1ne⟩ :
      ∃ lam1 ∈ S, lam1 ∈ CharCore.Irr ↥(Lgrp Lhat) ∧ lam1 ≠ lam := by
    by_cases hc : χ₀ = lam
    · exact ⟨ψ₀, hψ₀S, hψ₀irr, fun hh => hne₀ (hc.trans hh.symm)⟩
    · exact ⟨χ₀, hχ₀S, hχ₀irr, hc⟩
  -- degrees of `lam1` and `λ`
  obtain ⟨D, hD1, hDdvd⟩ := CharCore.irr_degree_dvd hlam1irr
  obtain ⟨E, hE1, hEdvd⟩ := CharCore.irr_degree_dvd hirr
  have hDpos : 0 < D := Nat.pos_of_dvd_of_pos hDdvd Nat.card_pos
  have hEpos : 0 < E := Nat.pos_of_dvd_of_pos hEdvd Nat.card_pos
  -- `β = lam1(1)·λ - λ(1)·lam1 ∈ 𝓘₀(𝓢) ⊆ 𝓘₀(L̂)`
  set β : ↥(Lgrp Lhat) → ℂ := (D : ℤ) • lam - (E : ℤ) • lam1 with hβdef
  have hβmem : β ∈ Coherence.ZSpan S := by
    rw [hβdef]
    exact AddSubgroup.sub_mem _ (AddSubgroup.zsmul_mem _ (Coherence.self_mem_zSpan hlam) D)
      (AddSubgroup.zsmul_mem _ (Coherence.self_mem_zSpan hlam1S) E)
  have hβ0 : β 1 = 0 := by
    have h3 : β = (D : ℤ) • lam - (E : ℤ) • lam1 := hβdef
    have h4 := congrFun h3 1
    simp only [Pi.sub_apply, Pi.smul_apply, hE1, hD1] at h4
    rw [h4]
    simp only [zsmul_eq_mul, Int.cast_natCast]
    ring
  have hβZ : β ∈ Coherence.ZSpan0 S := Coherence.mem_zSpan0.mpr ⟨hβmem, hβ0⟩
  have hβvanish : ∀ m : ↥(Lgrp Lhat), (m : X) ∉ Lhat → β m = 0 := hcoh.2.1 β hβZ
  have hτβ : τ' β = tau Lhat n Hs β := hτ'.1 β hβZ
  have hβapply : ∀ x : X, τ' β x = (D : ℂ) * (τ' lam x) - (E : ℂ) * (τ' lam1 x) := by
    intro x
    have h1 : τ' β = (D : ℤ) • τ' lam - (E : ℤ) • τ' lam1 := by
      rw [hβdef, map_sub, map_zsmul, map_zsmul]
    have h2 := congrFun h1 x
    simp only [Pi.sub_apply, Pi.smul_apply] at h2
    simpa only [zsmul_eq_mul, Int.cast_natCast] using h2
  have hsuppinf : ∀ i : Fin n, Hs i ⊓ Lgrp Lhat = ⊥ := by
    rcases hD with hDne | hn0
    · exact h.supp_inf hDne
    · subst hn0
      intro i
      exact i.elim0
  -- the degree of `τ β` vanishes, hence `D·τ'λ(1) = E·τ'lam1(1)`
  have hdeg : (D : ℂ) * (τ' lam 1) = (E : ℂ) * (τ' lam1 1) := by
    have h0 : τ' β 1 = 0 := by
      rw [hτβ, tau_apply_one hsuppinf hβ0]
    rw [hβapply 1] at h0
    exact sub_eq_zero.mp h0
  -- norms and orthogonality of `τ'λ`, `τ'lam1`
  have hlamC : lam ∈ Coherence.Irr ↥(Lgrp Lhat) := CharCore.mem_Irr_iff_coherence.mp hirr
  have hlam1C : lam1 ∈ Coherence.Irr ↥(Lgrp Lhat) := CharCore.mem_Irr_iff_coherence.mp hlam1irr
  have hPn : Coherence.cfInner (τ' lam) (τ' lam) = 1 := by
    rw [hτ'.2.1.inner_eq lam (Coherence.self_mem_zSpan hlam) lam (Coherence.self_mem_zSpan hlam),
      Work.Clifford.cfInner_eq_ite_of_mem_Irr_coherence hlamC hlamC, if_pos rfl]
  have hQn : Coherence.cfInner (τ' lam1) (τ' lam1) = 1 := by
    rw [hτ'.2.1.inner_eq lam1 (Coherence.self_mem_zSpan hlam1S) lam1 (Coherence.self_mem_zSpan hlam1S),
      Work.Clifford.cfInner_eq_ite_of_mem_Irr_coherence hlam1C hlam1C, if_pos rfl]
  have hPQ : Coherence.cfInner (τ' lam) (τ' lam1) = 0 := by
    rw [hτ'.2.1.inner_eq lam (Coherence.self_mem_zSpan hlam) lam1 (Coherence.self_mem_zSpan hlam1S),
      horth lam hlam lam1 hlam1S (fun h => hlam1ne h.symm)]
  -- the key: every automorphism of `ℂ` fixing `ℚ_a` fixes every value of `τ'λ`
  have key : ∀ σ : ℂ ≃+* ℂ, (∀ z : ℂ, z ^ LhatExponent Lhat = 1 → σ z = z) →
      ∀ x : X, σ (τ' lam x) = τ' lam x := by
    intro σ hσ x
    have hσβ : ∀ m : ↥(Lgrp Lhat), σ (β m) = β m := by
      intro m
      by_cases hm : (m : X) ∈ Lhat
      · have hmem : β m ∈ Algebra.adjoin ℚ
            ({z : ℂ | z ^ LhatExponent Lhat = 1} : Set ℂ) := by
          have hlm : lam m ∈ Algebra.adjoin ℚ
              ({z : ℂ | z ^ LhatExponent Lhat = 1} : Set ℂ) :=
            ft10_4_vchar_apply (hv lam hlam) ha_pos (by rw [← Subgroup.orderOf_coe m]; exact orderOf_dvd_LhatExponent hm m.2)
          have hl1m : lam1 m ∈ Algebra.adjoin ℚ
              ({z : ℂ | z ^ LhatExponent Lhat = 1} : Set ℂ) :=
            ft10_4_vchar_apply (hv lam1 hlam1S) ha_pos (by rw [← Subgroup.orderOf_coe m]; exact orderOf_dvd_LhatExponent hm m.2)
          have hβm : β m = ((D : ℤ) : ℂ) * lam m - ((E : ℤ) : ℂ) * lam1 m := by
            have h3 : β = (D : ℤ) • lam - (E : ℤ) • lam1 := hβdef
            have h4 := congrFun h3 m
            simp only [Pi.sub_apply, Pi.smul_apply] at h4
            simpa only [zsmul_eq_mul] using h4
          rw [hβm]
          exact Subalgebra.sub_mem _ (Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ D) hlm)
            (Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ E) hl1m)
        exact map_eq_self_of_mem_adjoin
          (σ := σ) (s := {z : ℂ | z ^ LhatExponent Lhat = 1}) (fun z hz => hσ z hz) hmem
      · rw [hβvanish m hm, map_zero]
    have hσtau : ∀ y : X, σ (tau Lhat n Hs β y) = tau Lhat n Hs β y := by
      intro y
      have h1 : (fun m : ↥(Lgrp Lhat) => σ (β m)) = β := funext hσβ
      calc σ (tau Lhat n Hs β y) = tau Lhat n Hs (fun m => σ (β m)) y :=
            ft10_4_tau_map σ β y
        _ = tau Lhat n Hs β y := by rw [h1]
    have hσβ' : ∀ y : X, σ (τ' β y) = τ' β y := by
      intro y
      rw [hτβ, hσtau y]
    have hfun : ∀ y : X, (D : ℂ) * σ (τ' lam y) - (E : ℂ) * σ (τ' lam1 y)
        = (D : ℂ) * (τ' lam y) - (E : ℂ) * (τ' lam1 y) := by
      intro y
      calc (D : ℂ) * σ (τ' lam y) - (E : ℂ) * σ (τ' lam1 y)
          = σ ((D : ℂ) * (τ' lam y) - (E : ℂ) * (τ' lam1 y)) := by
            rw [map_sub, map_mul, map_mul, map_natCast, map_natCast]
        _ = σ (τ' β y) := by rw [hβapply y]
        _ = τ' β y := hσβ' y
        _ = (D : ℂ) * (τ' lam y) - (E : ℂ) * (τ' lam1 y) := by rw [hβapply y]
    exact ft10_4_endgame σ (hτ'.2.2 lam hlam) (hτ'.2.2 lam1 hlam1S) hPn hQn hPQ hDpos hEpos
      hfun hdeg x
  -- conclusion: the value lies in `ℚ(ζ_{|X|})` and is fixed by all automorphisms fixing `ℚ_a`
  intro x
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ (Nat.card X) :=
    ⟨_, Complex.isPrimitiveRoot_exp (Nat.card X) (Nat.pos_iff_ne_zero.mp hm_pos)⟩
  have hcx : τ' lam x ∈ Algebra.adjoin ℚ ({ζ} : Set ℂ) := by
    refine (Algebra.adjoin_le_iff.mpr ?_) (ft10_4_vchar_apply (hτ'.2.2 lam hlam) hm_pos
      (orderOf_dvd_natCard x))
    intro z hz
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hz
    rw [← hi]
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton ζ)) i
  exact ft10_4_galois_fixed ha_pos hm_pos ham hζ hcx (fun σ hσ => key σ hσ x)

end Work.Tame
