import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.CosetCover
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

set_option linter.style.haveILetI false

open MvPolynomial

namespace Commons.Algebra.MvPolynomial

/-! # A homogeneous linear form avoiding all minimal primes of small height -/

/-- The `ℂ`-algebra endomorphism of `ℂ[X_1,…,X_n]` that kills the first `k` variables and
fixes the remaining ones. -/
noncomputable def varProj (n k : ℕ) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  MvPolynomial.aeval fun i : Fin n => if (i : ℕ) < k then 0 else MvPolynomial.X i

private lemma varProj_zero (n : ℕ) : varProj n 0 = AlgHom.id ℂ (MvPolynomial (Fin n) ℂ) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [varProj]

private lemma varProj_self (n : ℕ) :
    varProj n n = MvPolynomial.aeval (0 : Fin n → MvPolynomial (Fin n) ℂ) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [varProj]

private lemma varProj_succ_comp (n k : ℕ) :
    (varProj n (k+1)).comp (varProj n k) = varProj n (k+1) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply]
  have hXk : varProj n k (X i) = (if (i:ℕ) < k then 0 else MvPolynomial.X i) := by simp [varProj]
  have hXk1 : varProj n (k+1) (X i) = (if (i:ℕ) < k+1 then 0 else MvPolynomial.X i) := by simp [varProj]
  rw [hXk, hXk1]
  by_cases h : (i:ℕ) < k
  · rw [if_pos h, map_zero, if_pos (by omega)]
  · rw [if_neg h, hXk1]

private lemma ker_varProj_le_succ (n k : ℕ) :
    RingHom.ker (varProj n k) ≤ RingHom.ker (varProj n (k+1)) := by
  intro p hp
  simp only [RingHom.mem_ker] at hp ⊢
  rw [← varProj_succ_comp n k]
  simp only [AlgHom.comp_apply, hp, map_zero]

private lemma ker_varProj_lt_succ {n k : ℕ} (hk : k < n) :
    RingHom.ker (varProj n k) < RingHom.ker (varProj n (k+1)) := by
  refine lt_of_le_of_ne (ker_varProj_le_succ n k) (fun heq => ?_)
  have hmem : (MvPolynomial.X ⟨k, hk⟩ : MvPolynomial (Fin n) ℂ) ∈
      RingHom.ker (varProj n (k+1)) := by
    simp only [RingHom.mem_ker, varProj, MvPolynomial.aeval_X]
    simp
  have hnotmem : (MvPolynomial.X ⟨k, hk⟩ : MvPolynomial (Fin n) ℂ) ∉
      RingHom.ker (varProj n k) := by
    simp only [RingHom.mem_ker, varProj, MvPolynomial.aeval_X]
    simp
  rw [heq] at hnotmem
  exact hnotmem hmem

/-- The kernel of the augmentation `X i ↦ 0` is the ideal spanned by all variables. -/
lemma ker_aeval_zero_eq_idealOfVars (n : ℕ) :
    RingHom.ker (MvPolynomial.aeval (0 : Fin n → MvPolynomial (Fin n) ℂ)) =
      MvPolynomial.idealOfVars (Fin n) ℂ := by
  ext p
  rw [MvPolynomial.idealOfVars, ← Set.image_univ, MvPolynomial.mem_ideal_span_X_image,
    RingHom.mem_ker]
  have hiff : (∀ m ∈ p.support, ∃ i : Fin n, m i ≠ 0) ↔ p.coeff 0 = 0 := by
    constructor
    · intro h
      by_contra hc
      have hm : (0 : Fin n →₀ ℕ) ∈ p.support := by
        rw [MvPolynomial.mem_support_iff]; exact hc
      obtain ⟨i, hi⟩ := h 0 hm
      exact hi (by simp)
    · intro h m hm
      have hm0 : m ≠ 0 := by
        intro h0
        rw [h0, MvPolynomial.mem_support_iff] at hm
        exact hm h
      by_contra hc
      push Not at hc
      exact hm0 (Finsupp.ext fun i => by simpa using hc i)
  have hU : (∀ m ∈ p.support, ∃ i ∈ Set.univ, m i ≠ 0) ↔
      ∀ m ∈ p.support, ∃ i : Fin n, m i ≠ 0 := by simp
  rw [hU, hiff]
  constructor
  · intro h
    have hc := congrArg MvPolynomial.constantCoeff h
    rw [MvPolynomial.aeval_zero] at hc
    simpa only [MvPolynomial.algebraMap_eq, MvPolynomial.constantCoeff_C, map_zero,
      MvPolynomial.constantCoeff_eq] using hc
  · intro h
    rw [MvPolynomial.aeval_zero, MvPolynomial.algebraMap_eq, MvPolynomial.C_eq_zero,
      MvPolynomial.constantCoeff_eq]
    exact h

/-- A prime ideal containing all variables has height at least the number of variables. -/
lemma idealOfVars_le_height {n : ℕ} (p : Ideal (MvPolynomial (Fin n) ℂ)) [p.IsPrime]
    (h : MvPolynomial.idealOfVars (Fin n) ℂ ≤ p) : (n : ℕ∞) ≤ p.height := by
  have hK0 : RingHom.ker (varProj n 0) = ⊥ := by
    rw [varProj_zero]
    exact (RingHom.injective_iff_ker_eq_bot (AlgHom.id ℂ (MvPolynomial (Fin n) ℂ))).mp
      (fun a b h => h)
  have hKn : RingHom.ker (varProj n n) ≤ p := by
    rw [varProj_self, ker_aeval_zero_eq_idealOfVars]; exact h
  have key : ∀ k ≤ n, (k : ℕ∞) ≤ (RingHom.ker (varProj n k)).height := by
    intro k
    induction k with
    | zero => intro _; simp [hK0]
    | succ k ih =>
        intro hk
        have hkn : k < n := Nat.lt_of_succ_le hk
        have hstep := ker_varProj_lt_succ (n := n) hkn
        haveI : (RingHom.ker (varProj n k)).IsPrime := RingHom.ker_isPrime _
        haveI : (RingHom.ker (varProj n (k+1))).IsPrime := RingHom.ker_isPrime _
        have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hstep
        have h2 : (k : ℕ∞) + 1 ≤ (RingHom.ker (varProj n k)).height + 1 := by
          gcongr; exact ih (Nat.le_of_lt hkn)
        calc (k+1 : ℕ∞) = (k : ℕ∞) + 1 := by norm_cast
          _ ≤ (RingHom.ker (varProj n k)).height + 1 := h2
          _ ≤ (RingHom.ker (varProj n (k+1))).height := h1
  exact (key n le_rfl).trans (Ideal.height_mono hKn)

theorem exists_isHomogeneous_one_notMem_minimalPrimes {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ))
    (hht : ∀ p ∈ I.minimalPrimes, p.height < (n : ℕ∞)) :
    ∃ ℓ : MvPolynomial (Fin n) ℂ, ℓ.IsHomogeneous 1 ∧ ∀ p ∈ I.minimalPrimes, ℓ ∉ p := by
  classical
  haveI hfin : Finite ↥(I.minimalPrimes) :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) ℂ) I).to_subtype
  let ψ : (Fin n → ℂ) →ₗ[ℂ] MvPolynomial (Fin n) ℂ :=
    Fintype.linearCombination ℂ (fun i : Fin n => (X i : MvPolynomial (Fin n) ℂ))
  have hψ_single : ∀ i : Fin n, ψ (Pi.single i (1 : ℂ)) = (X i : MvPolynomial (Fin n) ℂ) := by
    intro i
    rw [show ψ (Pi.single i 1) = Fintype.linearCombination ℂ _ (Pi.single i 1) from rfl,
      Fintype.linearCombination_apply]
    simp
  have hψ_hom : ∀ a, (ψ a).IsHomogeneous 1 := by
    intro a
    rw [show ψ a = Fintype.linearCombination ℂ _ a from rfl, Fintype.linearCombination_apply]
    apply MvPolynomial.IsHomogeneous.sum
    intro i _
    rw [MvPolynomial.smul_eq_C_mul]
    exact MvPolynomial.isHomogeneous_C_mul_X _ _
  set W : Ideal (MvPolynomial (Fin n) ℂ) → Submodule ℂ (Fin n → ℂ) :=
    fun p => Submodule.comap ψ (p.restrictScalars ℂ) with hWdef
  have hWmem : ∀ p a, a ∈ W p ↔ ψ a ∈ p := fun p a => Iff.rfl
  have hproper : ∀ x : ↥(I.minimalPrimes), W x.val ≠ ⊤ := by
    intro x hx
    haveI := x.property.isPrime
    have hle : MvPolynomial.idealOfVars (Fin n) ℂ ≤ x.val := by
      rw [MvPolynomial.idealOfVars, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      have hmem : ψ (Pi.single i (1 : ℂ)) ∈ x.val :=
        (hWmem x.val _).mp (by rw [hx]; exact Submodule.mem_top)
      rwa [hψ_single i] at hmem
    have h1 : (n : ℕ∞) ≤ x.val.height := idealOfVars_le_height x.val hle
    have h2 : x.val.height < (n : ℕ∞) := hht x.val x.property
    exact (not_lt.mpr h1) h2
  have hnotcover : (⋃ x : ↥(I.minimalPrimes), (W x.val : Set (Fin n → ℂ))) ≠ Set.univ := by
    intro hc
    obtain ⟨x, hx⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hc
    exact hproper x hx
  obtain ⟨a, ha⟩ := (Set.ne_univ_iff_exists_notMem _).mp hnotcover
  have ha' : ∀ x : ↥(I.minimalPrimes), a ∉ W x.val := by
    intro x hx
    exact ha (Set.mem_iUnion.mpr ⟨x, hx⟩)
  refine ⟨ψ a, hψ_hom a, fun p hp hmem => ?_⟩
  exact ha' ⟨p, hp⟩ ((hWmem p a).mpr hmem)

end Commons.Algebra.MvPolynomial