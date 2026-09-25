import Mathlib
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.NumberTheory.NumberField.Completion.val_norm_adicCompletion_eq_pow
import Submission.Commons.NumberTheory.NumberField.Completion.compactSpace_adicCompletionIntegers
import Submission.Commons.NumberTheory.NumberField.Completion.val_le_exp_neg_iff_mem_maximalIdeal_pow
import Submission.Commons.FieldTheory.Galois.exists_normalBasis_trace_eq_one
import Submission.Commons.Analysis.Nonarchimedean.exp_map_ringEquiv
import Submission.Commons.NumberTheory.NumberField.continuous_algEquiv_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow
import Submission.Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one
import Submission.Commons.Analysis.Nonarchimedean.exists_exp_adicCompletion

open scoped NumberField WithZero
open IsDedekindDomain.HeightOneSpectrum

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Commons.NumberTheory.NumberField.Completion.AdicTateExp

noncomputable section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
  [Algebra (Q.adicCompletion K) (q.adicCompletion L)]
  [FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L)]
  [IsGalois (Q.adicCompletion K) (q.adicCompletion L)]

/-- The two ways of pushing an integer of `K_Q` into `L_q` agree. -/
theorem algebraMap_int_eq (c : Q.adicCompletionIntegers K) :
    algebraMap (Q.adicCompletionIntegers K) (q.adicCompletion L) c
      = algebraMap (Q.adicCompletion K) (q.adicCompletion L)
          (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) c) := by
  rw [IsScalarTower.algebraMap_apply (Q.adicCompletionIntegers K) (Q.adicCompletion K)
    (q.adicCompletion L)]

theorem conj_sum_eq_one (b : q.adicCompletion L)
    (hb : Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) b = 1) :
    ∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • b = 1 := by
  have h := trace_eq_sum_automorphisms (K := Q.adicCompletion K) (L := q.adicCompletion L) b
  rw [hb, map_one] at h
  simpa [AlgEquiv.smul_def] using h.symm

/-- The integral lattice spanned by the conjugates of `b`. -/
def conjLattice (b : q.adicCompletion L) : AddSubgroup (q.adicCompletion L) where
  carrier := {x : q.adicCompletion L |
    ∃ a : Gal(q.adicCompletion L/Q.adicCompletion K) → Q.adicCompletion K,
      (∀ σ, a σ ∈ (Q.adicCompletionIntegers K : Set (Q.adicCompletion K))) ∧
        ∑ σ, a σ • (σ • b) = x}
  add_mem' := by
    rintro x y ⟨a, ha, rfl⟩ ⟨c, hc, rfl⟩
    refine ⟨a + c, fun σ => (Q.adicCompletionIntegers K).toSubring.add_mem (ha σ) (hc σ), ?_⟩
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun σ _ => by rw [Pi.add_apply, add_smul]
  zero_mem' := ⟨0, fun σ => (Q.adicCompletionIntegers K).toSubring.zero_mem, by simp⟩
  neg_mem' := by
    rintro x ⟨a, ha, rfl⟩
    refine ⟨-a, fun σ => (Q.adicCompletionIntegers K).toSubring.neg_mem (ha σ), ?_⟩
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun σ _ => by rw [Pi.neg_apply, neg_smul]

theorem mem_conjLattice (b x : q.adicCompletion L) :
    x ∈ conjLattice Q q b ↔
      ∃ a : Gal(q.adicCompletion L/Q.adicCompletion K) → Q.adicCompletion K,
        (∀ σ, a σ ∈ (Q.adicCompletionIntegers K : Set (Q.adicCompletion K))) ∧
          ∑ σ, a σ • (σ • b) = x := Iff.rfl

/-- Re-indexing a sum of conjugates under left translation. -/
theorem sum_mulLeft_smul (b : q.adicCompletion L)
    (σ : Gal(q.adicCompletion L/Q.adicCompletion K))
    (f : Gal(q.adicCompletion L/Q.adicCompletion K) → Q.adicCompletion K) :
    ∑ τ, f τ • ((σ * τ) • b) = ∑ ρ, f (σ⁻¹ * ρ) • (ρ • b) := by
  refine Fintype.sum_equiv (Equiv.mulLeft σ) (fun τ => f τ • ((σ * τ) • b))
    (fun ρ => f (σ⁻¹ * ρ) • (ρ • b)) (fun τ => ?_)
  simp only [Equiv.coe_mulLeft, inv_mul_cancel_left]

/-- The action of `σ` on a conjugate sum. -/
theorem smul_sum_conj (b : q.adicCompletion L)
    (σ : Gal(q.adicCompletion L/Q.adicCompletion K))
    (a : Gal(q.adicCompletion L/Q.adicCompletion K) → Q.adicCompletion K) :
    σ • (∑ τ, a τ • (τ • b)) = ∑ ρ, a (σ⁻¹ * ρ) • (ρ • b) := by
  have h1 : σ • (∑ τ, a τ • (τ • b)) = ∑ τ, a τ • ((σ * τ) • b) := by
    rw [AlgEquiv.smul_def, map_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_smul]
    simp only [AlgEquiv.smul_def, AlgEquiv.mul_apply]
  rw [h1, sum_mulLeft_smul Q q b σ a]

/-- The lattice is stable under the Galois action. -/
theorem conjLattice_stable (b : q.adicCompletion L)
    (σ : Gal(q.adicCompletion L/Q.adicCompletion K)) {x : q.adicCompletion L}
    (hx : x ∈ conjLattice Q q b) : σ • x ∈ conjLattice Q q b := by
  obtain ⟨a, ha, hxa⟩ := (mem_conjLattice Q q b x).mp hx
  rw [← hxa, smul_sum_conj Q q b σ a]
  exact (mem_conjLattice Q q b _).mpr ⟨fun ρ => a (σ⁻¹ * ρ), fun ρ => ha _, rfl⟩

theorem one_mem_conjLattice (b : q.adicCompletion L)
    (hb : Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) b = 1) :
    (1 : q.adicCompletion L) ∈ conjLattice Q q b := by
  refine (mem_conjLattice Q q b 1).mpr ⟨fun _ => 1, fun _ => one_mem _, ?_⟩
  simp only [one_smul]
  exact conj_sum_eq_one Q q b hb

/-- Coefficient uniqueness for conjugate sums. -/
theorem coeff_sum_unique (b : q.adicCompletion L)
    (hLI : LinearIndependent (Q.adicCompletion K)
      (fun σ : Gal(q.adicCompletion L/Q.adicCompletion K) => σ • b))
    {a a' : Gal(q.adicCompletion L/Q.adicCompletion K) → Q.adicCompletion K}
    (h : ∑ σ, a σ • (σ • b) = ∑ σ, a' σ • (σ • b)) : a = a' := by
  have h2 : ∑ σ, (a σ - a' σ) • (σ • b) = 0 := by
    have h1 : ∀ σ, (a σ - a' σ) • (σ • b) = a σ • (σ • b) - a' σ • (σ • b) := by
      intro σ; rw [sub_smul]
    rw [Finset.sum_congr rfl fun σ _ => h1 σ, Finset.sum_sub_distrib, h, sub_self]
  have h3 := Fintype.linearIndependent_iff.mp hLI (fun σ => a σ - a' σ) h2
  funext σ
  exact sub_eq_zero.mp (h3 σ)

/-- The coefficients of a fixed conjugate sum are constant. -/
theorem coeffs_of_fixed (b : q.adicCompletion L)
    (hLI : LinearIndependent (Q.adicCompletion K)
      (fun σ : Gal(q.adicCompletion L/Q.adicCompletion K) => σ • b))
    (σgen : Gal(q.adicCompletion L/Q.adicCompletion K)) (hgen : Subgroup.zpowers σgen = ⊤)
    {c : Gal(q.adicCompletion L/Q.adicCompletion K) → Q.adicCompletion K}
    (hfix : ∀ σ : Gal(q.adicCompletion L/Q.adicCompletion K),
      σ • (∑ τ : Gal(q.adicCompletion L/Q.adicCompletion K), c τ • (τ • b))
        = ∑ τ : Gal(q.adicCompletion L/Q.adicCompletion K), c τ • (τ • b)) :
    ∀ τ, c τ = c 1 := by
  have hcoeff : ∀ ρ, c (σgen⁻¹ * ρ) = c ρ := by
    intro ρ
    have h3 : (∑ ρ : Gal(q.adicCompletion L/Q.adicCompletion K), c (σgen⁻¹ * ρ) • (ρ • b))
        = ∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), c σ • (σ • b) := by
      rw [← smul_sum_conj Q q b σgen c]
      exact hfix σgen
    exact congr_fun (coeff_sum_unique Q q b hLI h3) ρ
  have hstep_up : ∀ ρ, c (σgen * ρ) = c ρ := by
    intro ρ
    have h := hcoeff (σgen * ρ)
    rw [inv_mul_cancel_left] at h
    exact h.symm
  have hnat : ∀ k : ℕ, c (σgen ^ k) = c 1 := by
    intro k; induction k with
    | zero => simp
    | succ n ih => rw [pow_succ', hstep_up (σgen ^ n), ih]
  have hneg : ∀ k : ℕ, c (σgen ^ (-(k : ℤ))) = c 1 := by
    intro k; induction k with
    | zero => simp
    | succ n ih =>
        have h1 : σgen ^ (-(↑(n + 1) : ℤ)) = σgen⁻¹ * σgen ^ (-(↑n : ℤ)) := by
          rw [show (-(↑(n + 1) : ℤ)) = -1 + -(↑n : ℤ) by push_cast; ring, zpow_add, zpow_neg_one]
        rw [h1, hcoeff, ih]
  intro τ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (by rw [hgen]; exact Subgroup.mem_top τ)
  by_cases hk0 : 0 ≤ k
  · rw [← hk, ← Int.toNat_of_nonneg hk0, zpow_natCast]
    exact hnat k.toNat
  · have hklt : k < 0 := by omega
    have h2 : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (by omega)
    have hk' : k = -(((-k).toNat : ℤ)) := by omega
    have h3 : σgen ^ k = σgen ^ (-(((-k).toNat : ℤ))) := by
      conv_lhs => rw [hk']
    rw [← hk, h3]
    exact hneg (-k).toNat

/-- The invariant elements of the lattice are the integral multiples of one. -/
theorem fixed_mem_conjLattice (b : q.adicCompletion L)
    (hb : Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) b = 1)
    (hLI : LinearIndependent (Q.adicCompletion K)
      (fun σ : Gal(q.adicCompletion L/Q.adicCompletion K) => σ • b))
    (σgen : Gal(q.adicCompletion L/Q.adicCompletion K)) (hgen : Subgroup.zpowers σgen = ⊤)
    {x : q.adicCompletion L} (hx : x ∈ conjLattice Q q b)
    (hfix : ∀ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • x = x) :
    ∃ a : Q.adicCompletionIntegers K, a • (1 : q.adicCompletion L) = x := by
  obtain ⟨c, hc, hxc⟩ := (mem_conjLattice Q q b x).mp hx
  have hconst : ∀ τ, c τ = c 1 := by
    refine coeffs_of_fixed Q q b hLI σgen hgen ?_
    intro σ
    rw [hxc]
    exact hfix σ
  refine ⟨⟨c 1, hc 1⟩, ?_⟩
  have hsum : (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), c σ • (σ • b))
      = c 1 • (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • b) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun σ _ => by rw [hconst σ]
  rw [← hxc, hsum, conj_sum_eq_one Q q b hb]
  rw [Algebra.smul_def, mul_one, Algebra.smul_def, mul_one, algebraMap_int_eq]
  rfl

/-- Invariance of the conjugate sum under the Galois action. -/
theorem conjTrace_conj (b : q.adicCompletion L)
    (σ : Gal(q.adicCompletion L/Q.adicCompletion K)) (y : q.adicCompletion L) :
    ∑ τ : Gal(q.adicCompletion L/Q.adicCompletion K), τ • (σ • y)
      = ∑ τ : Gal(q.adicCompletion L/Q.adicCompletion K), τ • y := by
  refine Fintype.sum_equiv (Equiv.mulRight σ) (fun τ => τ • (σ • y)) (fun ρ => ρ • y)
    (fun τ => ?_)
  simp only [Equiv.coe_mulRight]
  rw [mul_smul]

/-- The trace of a lattice element is an integral multiple of one. -/
theorem trace_mem_conjLattice (b : q.adicCompletion L)
    (hb : Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) b = 1)
    {x : q.adicCompletion L} (hx : x ∈ conjLattice Q q b) :
    ∃ a : Q.adicCompletionIntegers K, a • (1 : q.adicCompletion L) = ∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • x := by
  obtain ⟨c, hc, hxc⟩ := (mem_conjLattice Q q b x).mp hx
  refine ⟨∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), ⟨c σ, hc σ⟩, ?_⟩
  have hstep : ∀ τ : Gal(q.adicCompletion L/Q.adicCompletion K),
      (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • (c τ • (τ • b)))
        = c τ • (1 : q.adicCompletion L) := by
    intro τ
    have h2 : ∀ σ : Gal(q.adicCompletion L/Q.adicCompletion K),
        σ • (c τ • (τ • b)) = c τ • (σ • (τ • b)) := by
      intro σ
      rw [AlgEquiv.smul_def, map_smul]
      simp only [AlgEquiv.smul_def]
    have h3 : (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • (τ • b)) = 1 := by
      rw [conjTrace_conj Q q b τ b, conj_sum_eq_one Q q b hb]
    calc (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • (c τ • (τ • b)))
        = ∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), c τ • (σ • (τ • b)) :=
          Finset.sum_congr rfl (fun σ _ => h2 σ)
      _ = c τ • (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • (τ • b)) :=
          (Finset.smul_sum).symm
      _ = c τ • 1 := by rw [h3]
  have hpush : ∀ σ : Gal(q.adicCompletion L/Q.adicCompletion K),
      σ • (∑ τ : Gal(q.adicCompletion L/Q.adicCompletion K), c τ • (τ • b))
        = ∑ τ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • (c τ • (τ • b)) := by
    intro σ
    rw [AlgEquiv.smul_def, map_sum]
    simp only [AlgEquiv.smul_def]
  rw [← hxc]
  simp only [hpush]
  rw [Finset.sum_comm]
  simp only [hstep]
  rw [Finset.sum_smul]
  exact Finset.sum_congr rfl fun (τ : Gal(q.adicCompletion L/Q.adicCompletion K)) _ => by
    rw [Algebra.smul_def, mul_one, Algebra.smul_def, mul_one, algebraMap_int_eq]
    rfl

/-- `b` itself lies in the lattice. -/
theorem mem_b_conjLattice (b : q.adicCompletion L) : b ∈ conjLattice Q q b := by
  classical
  refine (mem_conjLattice Q q b b).mpr ⟨fun σ => if σ = 1 then 1 else 0, ?_, ?_⟩
  · intro σ
    by_cases hσ : σ = 1
    · simpa [hσ] using (Q.adicCompletionIntegers K).toSubring.one_mem
    · simpa [hσ] using (Q.adicCompletionIntegers K).toSubring.zero_mem
  · rw [Finset.sum_eq_single (1 : Gal(q.adicCompletion L/Q.adicCompletion K))]
    · simp
    · intro σ _ hσ; simp [hσ]
    · intro h; exact absurd (Finset.mem_univ 1) h

/-- `a • b` lies in the lattice for every integer `a`. -/
theorem scalar_mul_b_mem_conjLattice (b : q.adicCompletion L)
    (a : Q.adicCompletionIntegers K) :
    algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) a • b ∈ conjLattice Q q b := by
  classical
  refine (mem_conjLattice Q q b _).mpr
    ⟨fun σ => if σ = 1 then algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) a
      else 0, ?_, ?_⟩
  · intro σ
    by_cases hσ : σ = 1
    · simpa [hσ] using a.2
    · simp [hσ]
  · rw [Finset.sum_eq_single (1 : Gal(q.adicCompletion L/Q.adicCompletion K))]
    · simp
    · intro σ _ hσ; simp [hσ]
    · intro h; exact absurd (Finset.mem_univ 1) h

/-- The trace map on the lattice is onto the integral multiples of one. -/
theorem trace_surj_conjLattice (b : q.adicCompletion L)
    (hb : Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) b = 1)
    (a : Q.adicCompletionIntegers K) :
    ∃ u ∈ conjLattice Q q b,
      (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • u) = a • (1 : q.adicCompletion L) := by
  refine ⟨algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) a • b,
    scalar_mul_b_mem_conjLattice Q q b a, ?_⟩
  have h1 : ∀ σ : Gal(q.adicCompletion L/Q.adicCompletion K),
      σ • (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) a • b)
        = algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) a • (σ • b) := by
    intro σ
    simp only [AlgEquiv.smul_def, map_smul]
  simp only [h1]
  rw [← Finset.smul_sum, conj_sum_eq_one Q q b hb]
  rw [Algebra.smul_def, mul_one, Algebra.smul_def, mul_one]
  exact (algebraMap_int_eq Q q a).symm


/-- The lattice is closed under multiplication by integral scalars. -/
theorem conjLattice_smul_mem (b : q.adicCompletion L) {c : Q.adicCompletion K}
    (hc : c ∈ (Q.adicCompletionIntegers K : Set (Q.adicCompletion K)))
    {x : q.adicCompletion L} (hx : x ∈ conjLattice Q q b) : c • x ∈ conjLattice Q q b := by
  obtain ⟨a, ha, hxa⟩ := (mem_conjLattice Q q b x).mp hx
  refine (mem_conjLattice Q q b _).mpr ⟨fun σ => c * a σ, fun σ => ?_, ?_⟩
  · exact (Q.adicCompletionIntegers K).toSubring.mul_mem hc (ha σ)
  · rw [← hxa, Finset.smul_sum]
    exact Finset.sum_congr rfl fun σ _ => by rw [mul_smul]

/-- The conjugate sum of a lattice element in terms of its coefficients. -/
theorem trace_eq_smul_one (b : q.adicCompletion L)
    (hb : Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) b = 1)
    {x : q.adicCompletion L} (hx : x ∈ conjLattice Q q b) :
    ∃ a : Gal(q.adicCompletion L/Q.adicCompletion K) → Q.adicCompletion K,
      (∀ σ, a σ ∈ (Q.adicCompletionIntegers K : Set (Q.adicCompletion K))) ∧
        (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • x) = (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), a σ) • (1 : q.adicCompletion L) := by
  obtain ⟨c, hc, hxc⟩ := (mem_conjLattice Q q b x).mp hx
  refine ⟨c, hc, ?_⟩
  have hstep : ∀ τ : Gal(q.adicCompletion L/Q.adicCompletion K),
      (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • (c τ • (τ • b)))
        = c τ • (1 : q.adicCompletion L) := by
    intro τ
    have h2 : ∀ σ : Gal(q.adicCompletion L/Q.adicCompletion K),
        σ • (c τ • (τ • b)) = c τ • (σ • (τ • b)) := by
      intro σ
      rw [AlgEquiv.smul_def, map_smul]
      simp only [AlgEquiv.smul_def]
    have h3 : (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • (τ • b)) = 1 := by
      rw [conjTrace_conj Q q b τ b, conj_sum_eq_one Q q b hb]
    calc (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • (c τ • (τ • b)))
        = ∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), c τ • (σ • (τ • b)) :=
          Finset.sum_congr rfl (fun σ _ => h2 σ)
      _ = c τ • (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • (τ • b)) :=
          (Finset.smul_sum).symm
      _ = c τ • 1 := by rw [h3]
  have hpush : ∀ σ : Gal(q.adicCompletion L/Q.adicCompletion K),
      σ • (∑ τ : Gal(q.adicCompletion L/Q.adicCompletion K), c τ • (τ • b))
        = ∑ τ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • (c τ • (τ • b)) := by
    intro σ
    rw [AlgEquiv.smul_def, map_sum]
    simp only [AlgEquiv.smul_def]
  rw [← hxc]
  simp only [hpush]
  rw [Finset.sum_comm]
  simp only [hstep]
  rw [Finset.sum_smul]


/-- The conjugate sum of a general conjugate sum with coefficients `c`. -/
theorem trace_conj_eq (b : q.adicCompletion L)
    (hb : Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) b = 1)
    (c : Gal(q.adicCompletion L/Q.adicCompletion K) → Q.adicCompletion K) :
    (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K),
        σ • (∑ τ : Gal(q.adicCompletion L/Q.adicCompletion K), c τ • (τ • b)))
      = (∑ τ : Gal(q.adicCompletion L/Q.adicCompletion K), c τ) • (1 : q.adicCompletion L) := by
  have hstep : ∀ τ : Gal(q.adicCompletion L/Q.adicCompletion K),
      (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • (c τ • (τ • b)))
        = c τ • (1 : q.adicCompletion L) := by
    intro τ
    have h2 : ∀ σ : Gal(q.adicCompletion L/Q.adicCompletion K),
        σ • (c τ • (τ • b)) = c τ • (σ • (τ • b)) := by
      intro σ
      rw [AlgEquiv.smul_def, map_smul]
      simp only [AlgEquiv.smul_def]
    have h3 : (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • (τ • b)) = 1 := by
      rw [conjTrace_conj Q q b τ b, conj_sum_eq_one Q q b hb]
    calc (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • (c τ • (τ • b)))
        = ∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), c τ • (σ • (τ • b)) :=
          Finset.sum_congr rfl (fun σ _ => h2 σ)
      _ = c τ • (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • (τ • b)) :=
          (Finset.smul_sum).symm
      _ = c τ • 1 := by rw [h3]
  have hpush : ∀ σ : Gal(q.adicCompletion L/Q.adicCompletion K),
      σ • (∑ τ : Gal(q.adicCompletion L/Q.adicCompletion K), c τ • (τ • b))
        = ∑ τ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • (c τ • (τ • b)) := by
    intro σ
    rw [AlgEquiv.smul_def, map_sum]
    simp only [AlgEquiv.smul_def]
  simp only [hpush]
  rw [Finset.sum_comm]
  simp only [hstep]
  rw [Finset.sum_smul]

/-- The conjugate sum of a lattice element is the image of an integer of `K_Q`. -/
theorem trace_eq_algebraMap (b : q.adicCompletion L)
    (hb : Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) b = 1)
    {x : q.adicCompletion L} (hx : x ∈ conjLattice Q q b) :
    ∃ a : Q.adicCompletionIntegers K,
      (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • x)
        = algebraMap (Q.adicCompletionIntegers K) (q.adicCompletion L) a := by
  obtain ⟨c, hc, hxc⟩ := (mem_conjLattice Q q b x).mp hx
  refine ⟨∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), ⟨c σ, hc σ⟩, ?_⟩
  rw [← hxc, trace_conj_eq Q q b hb c, Algebra.smul_def, mul_one]
  rw [show (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), c σ)
      = algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)
        (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), ⟨c σ, hc σ⟩) from by
    rw [map_sum]; rfl]
  exact (algebraMap_int_eq Q q _).symm

/-- The conjugates of `b` by powers of `σgen` lie in the lattice. -/
theorem mem_pow_smul_conjLattice (b : q.adicCompletion L)
    (σgen : Gal(q.adicCompletion L/Q.adicCompletion K)) (i : ℕ) :
    σgen ^ i • b ∈ conjLattice Q q b := by
  induction i with
  | zero => simpa using mem_b_conjLattice Q q b
  | succ k ih =>
      rw [pow_succ', mul_smul]
      exact conjLattice_stable Q q b σgen ih

/-- Coboundary form of `σgen^m • b - b` for natural `m`. -/
theorem exists_sub_mem_conjLattice_pow (b : q.adicCompletion L)
    (σgen : Gal(q.adicCompletion L/Q.adicCompletion K)) (m : ℕ) :
    ∃ w ∈ conjLattice Q q b, σgen ^ m • b - b = σgen • w - w := by
  refine ⟨∑ i ∈ Finset.range m, σgen ^ i • b, ?_, ?_⟩
  · exact (conjLattice Q q b).sum_mem fun i _ => mem_pow_smul_conjLattice Q q b σgen i
  · have h1 : σgen • (∑ i ∈ Finset.range m, σgen ^ i • b)
        = ∑ i ∈ Finset.range m, σgen ^ (i + 1) • b := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [← mul_smul, pow_succ']
    have h2 : (∑ i ∈ Finset.range m, σgen ^ (i + 1) • b)
        - (∑ i ∈ Finset.range m, σgen ^ i • b) = σgen ^ m • b - b := by
      have hh := Finset.sum_range_sub (fun i => σgen ^ i • b) m
      simpa using hh
    rw [h1, h2]

/-- Coboundary form of `τ • b - b` for group elements `τ` in the cyclic group generated by
`σgen`. -/
theorem exists_sub_mem_conjLattice (b : q.adicCompletion L)
    (σgen : Gal(q.adicCompletion L/Q.adicCompletion K)) (hgen : Subgroup.zpowers σgen = ⊤)
    (τ : Gal(q.adicCompletion L/Q.adicCompletion K)) :
    ∃ w ∈ conjLattice Q q b, τ • b - b = σgen • w - w := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (by rw [hgen]; exact Subgroup.mem_top τ)
  by_cases hk0 : 0 ≤ k
  · obtain ⟨w, hw, hw'⟩ := exists_sub_mem_conjLattice_pow Q q b σgen k.toNat
    exact ⟨w, hw, by rw [← hk, ← Int.toNat_of_nonneg hk0, zpow_natCast]; exact hw'⟩
  · have hklt : k < 0 := by omega
    have h2 : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (by omega)
    obtain ⟨w, hw, hw'⟩ := exists_sub_mem_conjLattice_pow Q q b σgen (-k).toNat
    have hwz : σgen ^ (-k) • b - b = σgen • w - w := by
      have h4 : (σgen ^ ((-k).toNat : ℕ) : Gal(q.adicCompletion L/Q.adicCompletion K))
          = σgen ^ (-k) := by
        conv_rhs => rw [← h2]
        rw [zpow_natCast]
      rw [← h4]
      exact hw'
    refine ⟨-(σgen ^ k • w), (conjLattice Q q b).neg_mem
      (conjLattice_stable Q q b (σgen ^ k) hw), ?_⟩
    have hkey : σgen ^ k • b - b = -(σgen ^ k • (σgen ^ (-k) • b - b)) := by
      rw [smul_sub, ← mul_smul, ← zpow_add, add_neg_cancel, zpow_zero, one_smul, neg_sub]
    have hfin : -(σgen ^ k • (σgen • w - w))
        = σgen • (-(σgen ^ k • w)) - (-(σgen ^ k • w)) := by
      simp only [smul_sub, smul_neg, neg_sub]
      rw [← mul_smul, ← mul_smul]
      rw [← zpow_add_one, ← zpow_one_add, show (1 : ℤ) + k = k + 1 by ring]
      abel
    rw [← hk, hkey, hwz, hfin]

/-- The kernel of the trace on the lattice is the image of `σgen - 1`. -/
theorem ker_trace_conjLattice (b : q.adicCompletion L)
    (hb : Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) b = 1)
    (hLI : LinearIndependent (Q.adicCompletion K)
      (fun σ : Gal(q.adicCompletion L/Q.adicCompletion K) => σ • b))
    (σgen : Gal(q.adicCompletion L/Q.adicCompletion K)) (hgen : Subgroup.zpowers σgen = ⊤)
    {x : q.adicCompletion L} (hx : x ∈ conjLattice Q q b)
    (htr : (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • x) = 0) :
    ∃ u ∈ conjLattice Q q b, x = σgen • u - u := by
  classical
  obtain ⟨c, hc, hxc⟩ := (mem_conjLattice Q q b x).mp hx
  have htr' : (∑ τ : Gal(q.adicCompletion L/Q.adicCompletion K), c τ) = 0 := by
    have h1 := trace_conj_eq Q q b hb c
    rw [hxc, htr] at h1
    have h2 : algebraMap (Q.adicCompletion K) (q.adicCompletion L)
        (∑ τ : Gal(q.adicCompletion L/Q.adicCompletion K), c τ) = 0 := by
      rw [Algebra.smul_def, mul_one] at h1
      exact h1.symm
    exact (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).injective (by rw [h2, map_zero])
  choose w hw hw' using fun τ => exists_sub_mem_conjLattice Q q b σgen hgen τ
  refine ⟨∑ τ : Gal(q.adicCompletion L/Q.adicCompletion K), c τ • w τ, ?_, ?_⟩
  · exact (conjLattice Q q b).sum_mem fun τ _ => conjLattice_smul_mem Q q b (hc τ) (hw τ)
  · have hx2 : x = ∑ τ : Gal(q.adicCompletion L/Q.adicCompletion K), c τ • (τ • b - b) := by
      rw [← hxc]
      have hone : ∀ τ : Gal(q.adicCompletion L/Q.adicCompletion K),
          c τ • (τ • b - b) = c τ • (τ • b) - c τ • b := fun τ => smul_sub _ _ _
      rw [Finset.sum_congr rfl (fun τ _ => hone τ), Finset.sum_sub_distrib, ← Finset.sum_smul,
        htr', zero_smul, sub_zero]
    rw [hx2]
    simp only [hw']
    have hsplit : ∀ σ : Gal(q.adicCompletion L/Q.adicCompletion K),
        c σ • (σgen • w σ - w σ) = c σ • (σgen • w σ) - c σ • w σ := fun σ => smul_sub _ _ _
    rw [Finset.sum_congr rfl (fun σ _ => hsplit σ), Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun σ _ => by
        simp only [AlgEquiv.smul_def, map_smul]


/-- Integrality of the image of an integer of `K_Q` in `L_q`. -/
theorem algebraMap_int_mem (c : Q.adicCompletionIntegers K) :
    algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) c
      ∈ (Q.adicCompletionIntegers K : Set (Q.adicCompletion K)) := c.2

/-- The scalar `π^M` as an element of the base field. -/
def cM (π : Q.adicCompletionIntegers K) (M : ℕ) : Q.adicCompletion K :=
  algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) (π ^ M)

theorem algebraMap_mul_int (π : Q.adicCompletionIntegers K) (M : ℕ)
    (a : Q.adicCompletionIntegers K) :
    algebraMap (Q.adicCompletionIntegers K) (q.adicCompletion L) (π ^ M * a)
      = algebraMap (Q.adicCompletionIntegers K) (q.adicCompletion L) (π ^ M)
        * algebraMap (Q.adicCompletion K) (q.adicCompletion L)
            (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) a) := by
  rw [map_mul, ← algebraMap_int_eq Q q a]

/-- The level-`M` submodule `π^M • V`, as a predicate. -/
def InLevel (π : Q.adicCompletionIntegers K) (b : q.adicCompletion L) (M : ℕ)
    (x : q.adicCompletion L) : Prop :=
  ∃ v ∈ conjLattice Q q b, cM Q π M • v = x

theorem inLevel_iff (π : Q.adicCompletionIntegers K) (b : q.adicCompletion L) (M : ℕ)
    (x : q.adicCompletion L) :
    InLevel Q q π b M x ↔ ∃ v ∈ conjLattice Q q b, cM Q π M • v = x := Iff.rfl

theorem InLevel_le {π : Q.adicCompletionIntegers K} {b : q.adicCompletion L} {M : ℕ}
    {x : q.adicCompletion L} (hx : InLevel Q q π b M x) : x ∈ conjLattice Q q b := by
  obtain ⟨v, hv, rfl⟩ := hx
  exact conjLattice_smul_mem Q q b (algebraMap_int_mem Q (π ^ M)) hv

theorem InLevel.mono {π : Q.adicCompletionIntegers K} {b : q.adicCompletion L} {M M' : ℕ}
    (h : M ≤ M') {x : q.adicCompletion L} (hx : InLevel Q q π b M' x) :
    InLevel Q q π b M x := by
  obtain ⟨v, hv, rfl⟩ := hx
  refine ⟨cM Q π (M' - M) • v,
    conjLattice_smul_mem Q q b (algebraMap_int_mem Q (π ^ (M' - M))) hv, ?_⟩
  rw [smul_smul, cM, cM, ← map_mul, ← pow_add, Nat.add_sub_cancel' h]
  rw [cM]

theorem InLevel.stable {π : Q.adicCompletionIntegers K} {b : q.adicCompletion L} {M : ℕ}
    (σ : Gal(q.adicCompletion L/Q.adicCompletion K)) {x : q.adicCompletion L}
    (hx : InLevel Q q π b M x) : InLevel Q q π b M (σ • x) := by
  obtain ⟨v, hv, rfl⟩ := hx
  refine ⟨σ • v, conjLattice_stable Q q b σ hv, ?_⟩
  simp only [AlgEquiv.smul_def, map_smul]

theorem InLevel.invariants {π : Q.adicCompletionIntegers K} {b : q.adicCompletion L}
    (hb : Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) b = 1)
    (hLI : LinearIndependent (Q.adicCompletion K)
      (fun σ : Gal(q.adicCompletion L/Q.adicCompletion K) => σ • b))
    (σgen : Gal(q.adicCompletion L/Q.adicCompletion K)) (hgen : Subgroup.zpowers σgen = ⊤)
    {M : ℕ} {x : q.adicCompletion L} (hx : InLevel Q q π b M x)
    (hfix : ∀ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • x = x) :
    ∃ a : Q.adicCompletionIntegers K,
      algebraMap (Q.adicCompletionIntegers K) (q.adicCompletion L) (π ^ M * a) = x := by
  obtain ⟨v, hv, rfl⟩ := hx
  obtain ⟨c, hc, hvc⟩ := (mem_conjLattice Q q b v).mp hv
  have hxpand : cM Q π M • v
      = ∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K),
          (cM Q π M * c σ) • (σ • b) := by
    rw [← hvc, Finset.smul_sum]
    exact Finset.sum_congr rfl fun σ _ => by rw [smul_smul]
  have hconst : ∀ τ, cM Q π M * c τ = cM Q π M * c 1 := by
    refine coeffs_of_fixed Q q b hLI σgen hgen ?_
    intro σ
    rw [← hxpand]
    exact hfix σ
  refine ⟨⟨c 1, hc 1⟩, ?_⟩
  rw [hxpand]
  have hsum : (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), (cM Q π M * c σ) • (σ • b))
      = algebraMap (Q.adicCompletion K) (q.adicCompletion L) (cM Q π M * c 1)
        * (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • b) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hconst σ, Algebra.smul_def]
  have hcoe : algebraMap (Q.adicCompletion K) (q.adicCompletion L) (c 1)
      = algebraMap (Q.adicCompletionIntegers K) (q.adicCompletion L) (⟨c 1, hc 1⟩) :=
    (algebraMap_int_eq Q q (⟨c 1, hc 1⟩)).symm
  have hcM : algebraMap (Q.adicCompletion K) (q.adicCompletion L) (cM Q π M)
      = algebraMap (Q.adicCompletionIntegers K) (q.adicCompletion L) (π ^ M) :=
    (algebraMap_int_eq Q q (π ^ M)).symm
  rw [hsum, conj_sum_eq_one Q q b hb, mul_one, map_mul, map_mul, hcM, hcoe]

theorem InLevel.trace_mem {π : Q.adicCompletionIntegers K} {b : q.adicCompletion L}
    (hb : Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) b = 1)
    {M : ℕ} {x : q.adicCompletion L} (hx : InLevel Q q π b M x) :
    ∃ a : Q.adicCompletionIntegers K,
      algebraMap (Q.adicCompletionIntegers K) (q.adicCompletion L) (π ^ M * a)
        = ∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • x := by
  obtain ⟨v, hv, rfl⟩ := hx
  obtain ⟨d, hd⟩ := trace_eq_algebraMap Q q b hb hv
  refine ⟨d, ?_⟩
  have h1 : ∀ σ : Gal(q.adicCompletion L/Q.adicCompletion K),
      σ • (cM Q π M • v) = cM Q π M • (σ • v) := by
    intro σ
    simp only [AlgEquiv.smul_def, map_smul]
  have hcM : algebraMap (Q.adicCompletion K) (q.adicCompletion L) (cM Q π M)
      = algebraMap (Q.adicCompletionIntegers K) (q.adicCompletion L) (π ^ M) :=
    (algebraMap_int_eq Q q (π ^ M)).symm
  simp only [h1]
  rw [← Finset.smul_sum, hd, Algebra.smul_def, hcM, ← map_mul]

theorem InLevel.trace_surj {π : Q.adicCompletionIntegers K} {b : q.adicCompletion L}
    (hb : Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) b = 1) (M : ℕ)
    (a : Q.adicCompletionIntegers K) :
    ∃ u : q.adicCompletion L, InLevel Q q π b M u ∧
      (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • u)
        = algebraMap (Q.adicCompletionIntegers K) (q.adicCompletion L) (π ^ M * a) := by
  refine ⟨cM Q π M • (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) a • b), ?_, ?_⟩
  · refine ⟨algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) a • b,
      conjLattice_smul_mem Q q b (algebraMap_int_mem Q a) (mem_b_conjLattice Q q b), rfl⟩
  · have h1 : ∀ σ : Gal(q.adicCompletion L/Q.adicCompletion K),
        σ • (cM Q π M
            • (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) a • b))
          = cM Q π M
            • (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) a • (σ • b)) := by
      intro σ
      simp only [AlgEquiv.smul_def, map_smul]
    simp only [h1]
    rw [← Finset.smul_sum]
    have h2 : (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K),
          algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) a • (σ • b))
        = algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) a • (1 : q.adicCompletion L) := by
      rw [← Finset.smul_sum, conj_sum_eq_one Q q b hb]
    rw [h2, smul_smul]
    rw [show cM Q π M * algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) a
        = algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) (π ^ M * a) from by
      rw [cM, map_mul]]
    rw [Algebra.smul_def, mul_one]
    exact (algebraMap_int_eq Q q (π ^ M * a)).symm


/-- Definitional unfolding of the lattice: the euclidean-domain basis element. -/
theorem generic_bounded (b : q.adicCompletion L)
    (hv_le_one : ∀ c : Q.adicCompletion K,
      c ∈ (Q.adicCompletionIntegers K : Set (Q.adicCompletion K)) →
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (algebraMap (Q.adicCompletion K) (q.adicCompletion L) c) ≤ 1) :
    ∃ κ : ℤ, ∀ x ∈ conjLattice Q q b,
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) x
        ≤ (WithZero.exp κ : WithZero (Multiplicative ℤ)) := by
  classical
  refine ⟨Finset.univ.sup' Finset.univ_nonempty fun σ :
      Gal(q.adicCompletion L/Q.adicCompletion K) =>
    (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) (σ • b)).log, ?_⟩
  intro x hx
  obtain ⟨c, hc, rfl⟩ := (mem_conjLattice Q q b x).mp hx
  refine Valuation.map_sum_le _ fun σ _ => ?_
  by_cases hσ : σ • b = 0
  · rw [Algebra.smul_def, hσ, mul_zero, map_zero]
    exact bot_le
  · have hvne : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) (σ • b) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr hσ
    have h2 : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) (σ • b)
        ≤ (WithZero.exp (Finset.univ.sup' Finset.univ_nonempty fun τ :
            Gal(q.adicCompletion L/Q.adicCompletion K) =>
          (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
            (τ • b)).log) : WithZero (Multiplicative ℤ)) := by
      rw [← WithZero.exp_log hvne]
      exact WithZero.exp_le_exp.mpr
        (Finset.le_sup' (fun τ : Gal(q.adicCompletion L/Q.adicCompletion K) =>
          (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
            (τ • b)).log) (Finset.mem_univ σ))
    rw [Algebra.smul_def, map_mul]
    calc Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
            (algebraMap (Q.adicCompletion K) (q.adicCompletion L) (c σ))
          * Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) (σ • b)
        ≤ 1 * (WithZero.exp (Finset.univ.sup' Finset.univ_nonempty fun τ :
            Gal(q.adicCompletion L/Q.adicCompletion K) =>
          (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
            (τ • b)).log) : WithZero (Multiplicative ℤ)) :=
          mul_le_mul' (hv_le_one (c σ) (hc σ)) h2
      _ = WithZero.exp (Finset.univ.sup' Finset.univ_nonempty fun τ :
            Gal(q.adicCompletion L/Q.adicCompletion K) =>
          (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
            (τ • b)).log) := one_mul _


/-- The conjugate basis of `L_q` over `K_Q`. -/
def conjBasis (b : q.adicCompletion L)
    (hLI : LinearIndependent (Q.adicCompletion K)
      (fun σ : Gal(q.adicCompletion L/Q.adicCompletion K) => σ • b)) :
    Module.Basis (Gal(q.adicCompletion L/Q.adicCompletion K)) (Q.adicCompletion K)
      (q.adicCompletion L) :=
  basisOfLinearIndependentOfCardEqFinrank hLI
    (Fintype.card_eq_nat_card.trans
      (IsGalois.card_aut_eq_finrank (Q.adicCompletion K) (q.adicCompletion L)))

theorem conjBasis_apply (b : q.adicCompletion L)
    (hLI : LinearIndependent (Q.adicCompletion K)
      (fun σ : Gal(q.adicCompletion L/Q.adicCompletion K) => σ • b))
    (σ : Gal(q.adicCompletion L/Q.adicCompletion K)) :
    conjBasis Q q b hLI σ = σ • b := by
  rw [conjBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

/-- The lattice contains a deep ball. -/
theorem conjLattice_commensurable (b : q.adicCompletion L)
    (hb : Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) b = 1)
    (hLI : LinearIndependent (Q.adicCompletion K)
      (fun σ : Gal(q.adicCompletion L/Q.adicCompletion K) => σ • b))
    (hval : ∀ y : Q.adicCompletion K,
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          (algebraMap (Q.adicCompletion K) (q.adicCompletion L) y)
        = (Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) y)
          ^ (q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)))
    (he : 1 ≤ q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K))
    (hv : ∀ (σ : Gal(q.adicCompletion L/Q.adicCompletion K)) (z : q.adicCompletion L),
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) (σ • z)
        = Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) z) :
    ∃ D : ℤ, ∀ x : q.adicCompletion L,
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) x
          ≤ (WithZero.exp (-D) : WithZero (Multiplicative ℤ)) →
        x ∈ conjLattice Q q b := by
  classical
  haveI : Algebra.IsSeparable (Q.adicCompletion K) (q.adicCompletion L) := inferInstance
  set B := conjBasis Q q b hLI with hB
  have hBa : ∀ σ : Gal(q.adicCompletion L/Q.adicCompletion K), B σ = σ • b :=
    fun σ => conjBasis_apply Q q b hLI σ
  set d : Gal(q.adicCompletion L/Q.adicCompletion K) → q.adicCompletion L :=
    fun σ => ((Algebra.traceForm (Q.adicCompletion K) (q.adicCompletion L)).dualBasis
      (traceForm_nondegenerate (Q.adicCompletion K) (q.adicCompletion L)) B) σ with hddef
  have hfun : ∀ σ : Gal(q.adicCompletion L/Q.adicCompletion K),
      (Algebra.traceForm (Q.adicCompletion K) (q.adicCompletion L)).flip (d σ) = B.coord σ := by
    intro σ
    refine LinearMap.ext fun x => ?_
    rw [← B.sum_repr x]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_smul, map_smul]
    rw [LinearMap.BilinForm.flip_apply, Algebra.traceForm_apply, Module.Basis.coord_apply,
      B.repr_self]
    rw [show Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) (B τ * d σ)
        = (if τ = σ then (1 : Q.adicCompletion K) else 0) from by
      rw [mul_comm, ← Algebra.traceForm_apply]
      have h6 := LinearMap.BilinForm.apply_dualBasis_left
        (traceForm_nondegenerate (Q.adicCompletion K) (q.adicCompletion L)) B σ τ
      by_cases h : τ = σ <;> simpa [h] using h6]
    by_cases h : τ = σ
    · subst h; simp
    · simp [h]
  have hcoord : ∀ (x : q.adicCompletion L) (σ : Gal(q.adicCompletion L/Q.adicCompletion K)),
      B.repr x σ = Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) (x * d σ) := by
    intro x σ
    rw [← Module.Basis.coord_apply B σ x, ← hfun σ]
    rw [LinearMap.BilinForm.flip_apply, Algebra.traceForm_apply, mul_comm,
      ← Algebra.traceForm_apply]

  -- the constant
  refine ⟨Finset.univ.sup' Finset.univ_nonempty fun σ :
      Gal(q.adicCompletion L/Q.adicCompletion K) =>
    (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) (d σ)).log, ?_⟩
  intro x hx
  have hdv : ∀ σ : Gal(q.adicCompletion L/Q.adicCompletion K),
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) (d σ)
        ≤ (WithZero.exp (Finset.univ.sup' Finset.univ_nonempty fun τ :
            Gal(q.adicCompletion L/Q.adicCompletion K) =>
          (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) (d τ)).log)
          : WithZero (Multiplicative ℤ)) := by
    intro σ
    by_cases h0 : d σ = 0
    · rw [h0, map_zero]; exact bot_le
    · have h0' : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) (d σ) ≠ 0 :=
        (Valuation.ne_zero_iff _).mpr h0
      rw [← WithZero.exp_log h0']
      exact WithZero.exp_le_exp.mpr
        (Finset.le_sup' (fun τ : Gal(q.adicCompletion L/Q.adicCompletion K) =>
          (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) (d τ)).log)
          (Finset.mem_univ σ))
  -- the trace bound
  have htr : ∀ z : q.adicCompletion L,
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (algebraMap (Q.adicCompletion K) (q.adicCompletion L)
          (Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) z))
        ≤ Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) z := by
    intro z
    rw [trace_eq_sum_automorphisms (K := Q.adicCompletion K) (L := q.adicCompletion L) z]
    refine Valuation.map_sum_le _ fun σ _ => ?_
    simpa only [AlgEquiv.smul_def] using le_of_eq (hv σ z)
  -- integrality of the coefficients
  have hcint : ∀ σ : Gal(q.adicCompletion L/Q.adicCompletion K),
      B.repr x σ ∈ (Q.adicCompletionIntegers K : Set (Q.adicCompletion K)) := by
    intro σ
    show Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (B.repr x σ) ≤ 1
    have h1 : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (algebraMap (Q.adicCompletion K) (q.adicCompletion L) (B.repr x σ)) ≤ 1 := by
      refine le_trans (le_of_eq (by rw [hcoord x σ])) ?_
      refine le_trans (htr (x * d σ)) ?_
      rw [map_mul]
      refine le_trans (mul_le_mul' hx (hdv σ)) ?_
      rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
      simp
    rw [hval (B.repr x σ)] at h1
    by_contra hcon
    rw [not_le] at hcon
    have h2 : (1 : WithZero (Multiplicative ℤ))
        < (Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
            (B.repr x σ)) ^ (q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) :=
      one_lt_pow' hcon (by omega)
    exact absurd (lt_of_lt_of_le h2 h1) (lt_irrefl 1)
  refine (mem_conjLattice Q q b x).mpr ⟨fun σ => B.repr x σ, hcint, ?_⟩
  calc (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), B.repr x σ • (σ • b))
      = ∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), B.repr x σ • B σ :=
        Finset.sum_congr rfl fun σ _ => by rw [hBa σ]
    _ = x := B.sum_repr x


/-- A valuation bound giving membership in a level of the lattice. -/
theorem InLevel_of_valued_le (π : Q.adicCompletionIntegers K) (b : q.adicCompletion L)
    {D : ℤ}
    (hD : ∀ y : q.adicCompletion L, Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) y
      ≤ (WithZero.exp (-D) : WithZero (Multiplicative ℤ)) → y ∈ conjLattice Q q b)
    (hπ0 : algebraMap (Q.adicCompletionIntegers K) (q.adicCompletion L) π ≠ 0)
    {M : ℕ} {x : q.adicCompletion L}
    (hx : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) x
      ≤ (WithZero.exp (-D) : WithZero (Multiplicative ℤ))
        * (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
            (algebraMap (Q.adicCompletionIntegers K) (q.adicCompletion L) π)) ^ M) :
    InLevel Q q π b M x := by
  refine ⟨x / ((algebraMap (Q.adicCompletionIntegers K) (q.adicCompletion L) π) ^ M), ?_, ?_⟩
  · have hAv : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (algebraMap (Q.adicCompletionIntegers K) (q.adicCompletion L) π) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr hπ0
    refine hD _ ?_
    rw [map_div₀, map_pow, div_le_iff₀ (pow_pos (lt_of_le_of_ne bot_le (Ne.symm hAv)) M)]
    exact hx
  · rw [Algebra.smul_def, cM, ← algebraMap_int_eq Q q (π ^ M)]
    simp only [map_pow]
    exact mul_div_cancel₀ x (pow_ne_zero M hπ0)


theorem cM_ne_zero {π : Q.adicCompletionIntegers K}
    (hπ0 : algebraMap (Q.adicCompletionIntegers K) (q.adicCompletion L) π ≠ 0) (M : ℕ) :
    cM Q π M ≠ 0 := by
  intro h
  have h3 : algebraMap (Q.adicCompletionIntegers K) (q.adicCompletion L) (π ^ M) = 0 := by
    have h5 : algebraMap (Q.adicCompletion K) (q.adicCompletion L) (cM Q π M) = 0 := by
      rw [h, map_zero]
    have h6 : algebraMap (Q.adicCompletion K) (q.adicCompletion L)
        (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) (π ^ M)) = 0 := by
      simpa only [cM] using h5
    rw [← algebraMap_int_eq Q q (π ^ M)] at h6
    exact h6
  rw [map_pow] at h3
  exact (pow_ne_zero M hπ0) h3

theorem InLevel.add {π : Q.adicCompletionIntegers K} {b : q.adicCompletion L} {M : ℕ}
    {x y : q.adicCompletion L} (hx : InLevel Q q π b M x) (hy : InLevel Q q π b M y) :
    InLevel Q q π b M (x + y) := by
  obtain ⟨v, hv, rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hy
  exact ⟨v + w, (conjLattice Q q b).add_mem hv hw, smul_add _ _ _⟩

theorem InLevel.neg {π : Q.adicCompletionIntegers K} {b : q.adicCompletion L} {M : ℕ}
    {x : q.adicCompletion L} (hx : InLevel Q q π b M x) : InLevel Q q π b M (-x) := by
  obtain ⟨v, hv, rfl⟩ := hx
  exact ⟨-v, (conjLattice Q q b).neg_mem hv, smul_neg _ _⟩

theorem InLevel.smul_mem {π : Q.adicCompletionIntegers K} {b : q.adicCompletion L} {M : ℕ}
    {x : q.adicCompletion L} (c : Q.adicCompletionIntegers K) (hx : InLevel Q q π b M x) :
    InLevel Q q π b M
      (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) c • x) := by
  obtain ⟨v, hv, rfl⟩ := hx
  refine ⟨algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) c • v,
    conjLattice_smul_mem Q q b (algebraMap_int_mem Q c) hv, ?_⟩
  exact smul_comm _ _ _

theorem InLevel.valued_le {π : Q.adicCompletionIntegers K} {b : q.adicCompletion L} {M : ℕ}
    {κ : ℤ} (hκ : ∀ y ∈ conjLattice Q q b,
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) y
        ≤ (WithZero.exp κ : WithZero (Multiplicative ℤ)))
    {x : q.adicCompletion L} (hx : InLevel Q q π b M x) :
    Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) x
      ≤ Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          (algebraMap (Q.adicCompletion K) (q.adicCompletion L) (cM Q π M))
        * (WithZero.exp κ : WithZero (Multiplicative ℤ)) := by
  obtain ⟨v, hv, rfl⟩ := hx
  rw [Algebra.smul_def, map_mul]
  exact mul_le_mul' le_rfl (hκ v hv)

end
end Commons.NumberTheory.NumberField.Completion.AdicTateExp

namespace Commons.NumberTheory.NumberField.Completion.AdicTateExp

noncomputable section

/-- The `q`-adic valuation on the completion, as a bundled `Valuation`. -/
abbrev adicV {F : Type*} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) :=
  Valued.v (R := v.adicCompletion F) (Γ₀ := WithZero (Multiplicative ℤ))

/-- Bundled exponential on the ball of radius `exp (-M)` of a `p`-adic completion: the
series data, the valuation estimate `v (exp x - 1) = v x`, multiplicativity, and the
existence of a small "logarithm" `exp x = y` for `y` close to `1`. -/
structure ExpLog {F : Type*} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (M : ℕ) where
  hM : 1 ≤ M
  exp : v.adicCompletion F → v.adicCompletion F
  conv : ∀ x : v.adicCompletion F, adicV v x ≤ WithZero.exp (-(M : ℤ)) →
      HasSum (fun n : ℕ => x ^ n / ((n.factorial : ℕ) : v.adicCompletion F)) (exp x)
  val_exp_sub_one : ∀ x : v.adicCompletion F, adicV v x ≤ WithZero.exp (-(M : ℤ)) →
      adicV v (exp x - 1) = adicV v x
  exp_zero : exp 0 = 1
  exp_add : ∀ x y : v.adicCompletion F, adicV v x ≤ WithZero.exp (-(M : ℤ)) →
      adicV v y ≤ WithZero.exp (-(M : ℤ)) → exp (x + y) = exp x * exp y
  exists_exp_eq : ∀ y : v.adicCompletion F, adicV v (y - 1) ≤ WithZero.exp (-(M : ℤ)) →
      ∃ x : v.adicCompletion F, adicV v x ≤ WithZero.exp (-(M : ℤ)) ∧ exp x = y

namespace ExpLog

variable {F : Type*} [Field F] [NumberField F]
  {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} {M : ℕ} (E : ExpLog v M)

theorem val_exp {x : v.adicCompletion F} (hx : adicV v x ≤ WithZero.exp (-(M : ℤ))) :
    adicV v (E.exp x) = 1 := by
  have hMe : WithZero.exp (-(M : ℤ)) ≤ WithZero.exp (-(1 : ℤ)) := by
    rw [WithZero.exp_le_exp]; have := E.hM; omega
  have hx1 : adicV v x < (1 : WithZero (Multiplicative ℤ)) := by
    refine lt_of_le_of_lt (le_trans hx hMe) ?_
    rw [show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) from WithZero.exp_zero.symm,
      WithZero.exp_lt_exp]
    norm_num
  have hlt : adicV v (E.exp x - 1) < adicV v (1 : v.adicCompletion F) := by
    rw [E.val_exp_sub_one x hx, Valuation.map_one]; exact hx1
  have h := Valuation.map_add_eq_of_lt_right (adicV v) hlt
  rw [sub_add_cancel] at h
  simpa using h

theorem exp_ne_zero {x : v.adicCompletion F} (hx : adicV v x ≤ WithZero.exp (-(M : ℤ))) :
    E.exp x ≠ 0 := by
  intro h
  have h1 := E.val_exp hx
  rw [h, map_zero] at h1
  exact zero_ne_one h1

/-- `exp` of a small element and of its negative are inverse to each other. -/
theorem exp_neg {x : v.adicCompletion F} (hx : adicV v x ≤ WithZero.exp (-(M : ℤ))) :
    E.exp (-x) = (E.exp x)⁻¹ := by
  have hneg : adicV v (-x) ≤ WithZero.exp (-(M : ℤ)) := by
    rw [Valuation.map_neg]; exact hx
  have h := E.exp_add x (-x) hx hneg
  rw [add_neg_cancel, E.exp_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem exp_sub {x y : v.adicCompletion F} (hx : adicV v x ≤ WithZero.exp (-(M : ℤ)))
    (hy : adicV v y ≤ WithZero.exp (-(M : ℤ))) :
    E.exp (x - y) = E.exp x / E.exp y := by
  have hneg : adicV v (-y) ≤ WithZero.exp (-(M : ℤ)) := by
    rw [Valuation.map_neg]; exact hy
  rw [sub_eq_add_neg, E.exp_add x (-y) hx hneg, E.exp_neg hy, div_eq_mul_inv]

/-- On the ball the exponential is injective. -/
theorem exp_inj {x y : v.adicCompletion F} (hx : adicV v x ≤ WithZero.exp (-(M : ℤ)))
    (hy : adicV v y ≤ WithZero.exp (-(M : ℤ))) (h : E.exp x = E.exp y) : x = y := by
  have hsub : adicV v (x - y) ≤ WithZero.exp (-(M : ℤ)) :=
    le_trans (Valuation.map_sub (adicV v) x y) (max_le hx hy)
  have h1 : E.exp (x - y) = 1 := by
    rw [E.exp_sub hx hy, h, div_self (E.exp_ne_zero hy)]
  have h0 : adicV v (x - y) = 0 := by
    rw [← E.val_exp_sub_one (x - y) hsub, h1, sub_self, map_zero]
  by_contra hne
  exact (Valuation.ne_zero_iff (adicV v)).mpr (sub_ne_zero.mpr hne) h0

/-- The exponential converts sums into products. -/
theorem exp_finset_sum {ι : Type*} (s : Finset ι) (f : ι → v.adicCompletion F)
    (hsub : ∀ t : Finset ι, t ⊆ s → adicV v (∑ i ∈ t, f i) ≤ WithZero.exp (-(M : ℤ))) :
    E.exp (∑ i ∈ s, f i) = ∏ i ∈ s, E.exp (f i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, E.exp_zero]
  | insert a s ha ih =>
      have hsa : ∀ t, t ⊆ s → adicV v (∑ i ∈ t, f i) ≤ WithZero.exp (-(M : ℤ)) :=
        fun t ht => hsub t (Finset.Subset.trans ht (Finset.subset_insert a s))
      have hfa : adicV v (f a) ≤ WithZero.exp (-(M : ℤ)) := by
        have hh := hsub {a} (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self a s))
        simpa using hh
      have hfs : adicV v (∑ i ∈ s, f i) ≤ WithZero.exp (-(M : ℤ)) := hsub s (Finset.subset_insert a s)
      rw [Finset.sum_insert ha, Finset.prod_insert ha, E.exp_add (f a) (∑ i ∈ s, f i) hfa hfs,
        ih hsa]

end ExpLog
/-- A power of a value of the form `exp c`. -/
private theorem exp_pow (c : ℤ) (n : ℕ) :
    (WithZero.exp c : WithZero (Multiplicative ℤ)) ^ n = WithZero.exp (c * (n : ℤ)) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, mul_zero, WithZero.exp_zero]
  | succ k ih => rw [pow_succ, ih, ← WithZero.exp_add]; congr 1; push_cast; ring

section Main

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
  [hq : q.asIdeal.LiesOver Q.asIdeal]
  {Mexp : ℕ}

local instance instAdic : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
  RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
local instance instFD : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
  module_finite_adicCompletion Q q hq
local instance instGal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
  isGalois_adicCompletion Q q hq

/-- **The value of a uniformizer of `K_Q` inside `L_q`.**  It is `exp (-e)` where `e` is the
ramification index of `q` over `Q`. -/
theorem val_unifQ {π : Q.adicCompletionIntegers K}
    (hπ : adicV Q
      (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) π) = WithZero.exp (-1)) :
    adicV q (algebraMap (Q.adicCompletionIntegers K) (q.adicCompletion L) π)
      = WithZero.exp (-((q.asIdeal.ramificationIdx (𝓞 K) : ℤ))) := by
  rw [algebraMap_int_eq Q q π]
  change (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)))
      (Commons.RingTheory.Henselian.adicCompletionMap Q q hq
        (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) π))
      = WithZero.exp (-((q.asIdeal.ramificationIdx (𝓞 K) : ℤ)))
  rw [Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow Q q hq
      (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) π), hπ, exp_pow]
  congr 1; ring

/-- The value of `π ^ M` inside `L_q`. -/
theorem val_unifQ_pow {π : Q.adicCompletionIntegers K}
    (hπ : adicV Q
      (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) π) = WithZero.exp (-1))
    (Ml : ℕ) :
    (adicV q (algebraMap (Q.adicCompletionIntegers K) (q.adicCompletion L) π)) ^ Ml
      = WithZero.exp (-((Ml : ℤ) * (q.asIdeal.ramificationIdx (𝓞 K) : ℤ))) := by
  rw [val_unifQ Q q hπ, exp_pow]
  congr 1; ring

/-- The level `π ^ M · V` as an additive subgroup of `L_q`. -/
def levelSub (π : Q.adicCompletionIntegers K) (b : q.adicCompletion L) (Ml : ℕ) :
    AddSubgroup (q.adicCompletion L) where
  carrier := {x | InLevel Q q π b Ml x}
  add_mem' := fun hx hy => InLevel.add Q q hx hy
  zero_mem' := ⟨0, (conjLattice Q q b).zero_mem, smul_zero _⟩
  neg_mem' := fun hx => InLevel.neg Q q hx

theorem mem_levelSub {π : Q.adicCompletionIntegers K} {b : q.adicCompletion L} {Ml : ℕ}
    {x : q.adicCompletion L} :
    x ∈ levelSub Q q π b Ml ↔ InLevel Q q π b Ml x := Iff.rfl

theorem levelSub_stable (π : Q.adicCompletionIntegers K) (b : q.adicCompletion L) (Ml : ℕ)
    (σ : Gal(q.adicCompletion L/Q.adicCompletion K)) {x : q.adicCompletion L}
    (hx : x ∈ levelSub Q q π b Ml) : σ • x ∈ levelSub Q q π b Ml :=
  InLevel.stable Q q σ hx

/-- The kernel of the trace on a level of the lattice is the image of `σgen - 1`. -/
theorem ker_trace_level {π : Q.adicCompletionIntegers K} {b : q.adicCompletion L} {Ml : ℕ}
    (hb : Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) b = 1)
    (hLI : LinearIndependent (Q.adicCompletion K)
      (fun σ : Gal(q.adicCompletion L/Q.adicCompletion K) => σ • b))
    (σgen : Gal(q.adicCompletion L/Q.adicCompletion K)) (hgen : Subgroup.zpowers σgen = ⊤)
    (hπ0 : cM Q π Ml ≠ 0) {x : q.adicCompletion L} (hx : x ∈ levelSub Q q π b Ml)
    (htr : (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • x) = 0) :
    ∃ u ∈ levelSub Q q π b Ml, x = σgen • u - u := by
  obtain ⟨v, hv, rfl⟩ := (mem_levelSub Q q).mp hx
  have htrv : (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • v) = 0 := by
    have h1 : (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K),
        σ • (cM Q π Ml • v)) = cM Q π Ml • (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • v) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun σ _ => by simp only [AlgEquiv.smul_def, map_smul]
    rw [h1] at htr
    exact (smul_eq_zero.mp htr).resolve_left hπ0
  obtain ⟨u, hu, hu'⟩ := ker_trace_conjLattice Q q b hb hLI σgen hgen hv htrv
  refine ⟨cM Q π Ml • u, (mem_levelSub Q q).mpr ⟨u, hu, rfl⟩, ?_⟩
  rw [hu', smul_sub]
  congr 1
  simp only [AlgEquiv.smul_def, map_smul]

/-- **The exponential commutes with the Galois action.** -/
theorem ExpLog.exp_map_algEquiv (E : ExpLog q Mexp)
    (σ : Gal(q.adicCompletion L/Q.adicCompletion K)) {x : q.adicCompletion L}
    (hx : adicV q x ≤ WithZero.exp (-(Mexp : ℤ))) :
    σ (E.exp x) = E.exp (σ • x) := by
  have hcont : Continuous (σ.toRingEquiv) :=
    Commons.NumberTheory.NumberField.continuous_algEquiv_adicCompletion Q q hq σ
  have hv : ∀ z : q.adicCompletion L, adicV q (σ.toRingEquiv z) = adicV q z := fun z =>
    Commons.NumberTheory.NumberField.Completion.val_algEquiv_adicCompletion Q q hq σ z
  exact Commons.Analysis.Nonarchimedean.exp_map_ringEquiv q Mexp E.exp E.conv σ.toRingEquiv
    hcont hv x hx

/-- The subgroup of units obtained as the exponential of a level of the lattice. -/
def expSubgroup (E : ExpLog q Mexp) (π : Q.adicCompletionIntegers K) (b : q.adicCompletion L)
    (Ml : ℕ) (hball : ∀ x ∈ levelSub Q q π b Ml, adicV q x ≤ WithZero.exp (-(Mexp : ℤ))) :
    Subgroup (q.adicCompletion L)ˣ where
  carrier := {w | ∃ x ∈ levelSub Q q π b Ml, E.exp x = (w : q.adicCompletion L)}
  mul_mem' := by
    rintro w₁ w₂ ⟨x₁, hx₁, h₁⟩ ⟨x₂, hx₂, h₂⟩
    refine ⟨x₁ + x₂, (levelSub Q q π b Ml).add_mem hx₁ hx₂, ?_⟩
    rw [Units.val_mul, ← h₁, ← h₂, E.exp_add x₁ x₂ (hball x₁ hx₁) (hball x₂ hx₂)]
  one_mem' := ⟨0, (levelSub Q q π b Ml).zero_mem, by rw [E.exp_zero]; rfl⟩
  inv_mem' := by
    rintro w ⟨x, hx, h⟩
    refine ⟨-x, (levelSub Q q π b Ml).neg_mem hx, ?_⟩
    rw [E.exp_neg (hball x hx),
      show ((w⁻¹ : (q.adicCompletion L)ˣ) : q.adicCompletion L) = (↑w)⁻¹ from by simp,
      ← h]

theorem mem_expSubgroup {E : ExpLog q Mexp} {π : Q.adicCompletionIntegers K}
    {b : q.adicCompletion L} {Ml : ℕ} {hball : ∀ x ∈ levelSub Q q π b Ml,
      adicV q x ≤ WithZero.exp (-(Mexp : ℤ))} {w : (q.adicCompletion L)ˣ} :
    w ∈ expSubgroup Q q E π b Ml hball ↔
      ∃ x ∈ levelSub Q q π b Ml, E.exp x = (w : q.adicCompletion L) := Iff.rfl

theorem expSubgroup_mem_exp {E : ExpLog q Mexp} {π : Q.adicCompletionIntegers K}
    {b : q.adicCompletion L} {Ml : ℕ} {hball : ∀ x ∈ levelSub Q q π b Ml,
      adicV q x ≤ WithZero.exp (-(Mexp : ℤ))} {x : q.adicCompletion L}
    (hx : x ∈ levelSub Q q π b Ml) :
    Units.mk0 (E.exp x) (E.exp_ne_zero (hball x hx)) ∈ expSubgroup Q q E π b Ml hball :=
  (mem_expSubgroup Q q).mpr ⟨x, hx, rfl⟩

theorem expSubgroup_val_eq_one {E : ExpLog q Mexp} {π : Q.adicCompletionIntegers K}
    {b : q.adicCompletion L} {Ml : ℕ} {hball : ∀ x ∈ levelSub Q q π b Ml,
      adicV q x ≤ WithZero.exp (-(Mexp : ℤ))} {w : (q.adicCompletion L)ˣ}
    (hw : w ∈ expSubgroup Q q E π b Ml hball) :
    adicV q (w : q.adicCompletion L) = 1 := by
  obtain ⟨x, hx, hw'⟩ := (mem_expSubgroup Q q).mp hw
  rw [← hw']
  exact E.val_exp (hball x hx)

theorem expSubgroup_stable {E : ExpLog q Mexp} {π : Q.adicCompletionIntegers K}
    {b : q.adicCompletion L} {Ml : ℕ} {hball : ∀ x ∈ levelSub Q q π b Ml,
      adicV q x ≤ WithZero.exp (-(Mexp : ℤ))}
    (σ : Gal(q.adicCompletion L/Q.adicCompletion K)) {w : (q.adicCompletion L)ˣ}
    (hw : w ∈ expSubgroup Q q E π b Ml hball) :
    σ • w ∈ expSubgroup Q q E π b Ml hball := by
  obtain ⟨x, hx, hw'⟩ := (mem_expSubgroup Q q).mp hw
  refine (mem_expSubgroup Q q).mpr ⟨σ • x, levelSub_stable Q q π b Ml σ hx, ?_⟩
  rw [show ((σ • w : (q.adicCompletion L)ˣ) : q.adicCompletion L) = σ (w : q.adicCompletion L) from by
      simp,
    ← hw', ExpLog.exp_map_algEquiv Q q E σ (hball x hx)]

theorem expSubgroup_mem_principal {E : ExpLog q Mexp} {π : Q.adicCompletionIntegers K}
    {b : q.adicCompletion L} {Ml : ℕ} {hball : ∀ x ∈ levelSub Q q π b Ml,
      adicV q x ≤ WithZero.exp (-(Mexp : ℤ))}
    {D : ℤ} (hD : ∀ y : q.adicCompletion L, adicV q y ≤ WithZero.exp (-D) →
      y ∈ conjLattice Q q b)
    (hπ : adicV Q
      (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) π) = WithZero.exp (-1))
    {M₃ : ℕ} (hM₃e : (Mexp : ℤ) ≤ (M₃ : ℤ))
    (hM₃D : D + (Ml : ℤ) * (q.asIdeal.ramificationIdx (𝓞 K) : ℤ) ≤ (M₃ : ℤ))
    {x : (q.adicCompletionIntegers L)ˣ}
    (hx : (x : q.adicCompletionIntegers L) - 1 ∈
      IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) ^ M₃) :
    Units.map (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L)).toMonoidHom x ∈
      expSubgroup Q q E π b Ml hball := by
  have hvx : adicV q (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L)
      ((x : q.adicCompletionIntegers L) - 1)) ≤ WithZero.exp (-(M₃ : ℤ)) :=
    (val_le_exp_neg_iff_mem_maximalIdeal_pow q ((x : q.adicCompletionIntegers L) - 1) M₃).mpr hx
  have hπne : adicV q (algebraMap (Q.adicCompletionIntegers K) (q.adicCompletion L) π) ≠ 0 := by
    rw [val_unifQ Q q hπ]; exact WithZero.exp_ne_zero
  have hπ0 : algebraMap (Q.adicCompletionIntegers K) (q.adicCompletion L) π ≠ 0 :=
    (Valuation.ne_zero_iff _).mp hπne
  have hlog : adicV q (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) x - 1)
      ≤ WithZero.exp (-(Mexp : ℤ)) := by
    have harg : algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) x - 1
        = algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L)
            ((x : q.adicCompletionIntegers L) - 1) := by rw [map_sub, map_one]
    rw [harg]
    exact le_trans hvx (WithZero.exp_le_exp.mpr (by omega))
  have harg : algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) x - 1
      = algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L)
          ((x : q.adicCompletionIntegers L) - 1) := by rw [map_sub, map_one]
  obtain ⟨z, hzball, hzexp⟩ := E.exists_exp_eq _ hlog
  have hzval : adicV q z
      = adicV q (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) x - 1) := by
    rw [← E.val_exp_sub_one z hzball, hzexp]
  have hmem : z ∈ levelSub Q q π b Ml := by
    refine (mem_levelSub Q q).mpr (InLevel_of_valued_le Q q π b hD hπ0 ?_)
    have h3 : adicV q z ≤ WithZero.exp (-(M₃ : ℤ)) := by rw [hzval, harg]; exact hvx
    refine le_trans h3 ?_
    rw [val_unifQ_pow Q q hπ Ml, ← WithZero.exp_add, WithZero.exp_le_exp]
    linarith [hM₃D]
  refine (mem_expSubgroup Q q).mpr ⟨z, hmem, ?_⟩
  rw [hzexp, Units.coe_map]
  rfl

theorem expSubgroup_norm_surj {E : ExpLog q Mexp} {π : Q.adicCompletionIntegers K}
    {b : q.adicCompletion L} {Ml : ℕ} {hball : ∀ x ∈ levelSub Q q π b Ml,
      adicV q x ≤ WithZero.exp (-(Mexp : ℤ))}
    (hb : Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) b = 1)
    (hLI : LinearIndependent (Q.adicCompletion K)
      (fun σ : Gal(q.adicCompletion L/Q.adicCompletion K) => σ • b))
    (σgen : Gal(q.adicCompletion L/Q.adicCompletion K)) (hgen : Subgroup.zpowers σgen = ⊤)
    {w : (q.adicCompletion L)ˣ} (hw : w ∈ expSubgroup Q q E π b Ml hball)
    (hfix : ∀ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • w = w) :
    ∃ v ∈ expSubgroup Q q E π b Ml hball,
      algebraMap (Q.adicCompletion K) (q.adicCompletion L)
        (Algebra.norm (Q.adicCompletion K) (v : q.adicCompletion L)) = (w : q.adicCompletion L) := by
  obtain ⟨x, hx, hw'⟩ := (mem_expSubgroup Q q).mp hw
  have hxfix : ∀ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • x = x := by
    intro σ
    refine E.exp_inj (hball _ (levelSub_stable Q q π b Ml σ hx)) (hball x hx) ?_
    rw [← ExpLog.exp_map_algEquiv Q q E σ (hball x hx)]
    have h1 : ((σ • w : (q.adicCompletion L)ˣ) : q.adicCompletion L) = σ (w : q.adicCompletion L) := by
      simp
    rw [hw', ← h1, hfix σ]
  obtain ⟨a, ha⟩ := InLevel.invariants Q q hb hLI σgen hgen hx hxfix
  obtain ⟨u, hu, hu'⟩ := trace_surj_conjLattice Q q b hb a
  have hay : InLevel Q q π b Ml (cM Q π Ml • u) := ⟨u, hu, rfl⟩
  have hmem : cM Q π Ml • u ∈ levelSub Q q π b Ml := (mem_levelSub Q q).mpr hay
  have hyval : adicV q (cM Q π Ml • u) ≤ WithZero.exp (-(Mexp : ℤ)) := hball _ hmem
  refine ⟨Units.mk0 (E.exp (cM Q π Ml • u)) (E.exp_ne_zero hyval),
    expSubgroup_mem_exp Q q hmem, ?_⟩
  show algebraMap (Q.adicCompletion K) (q.adicCompletion L)
      (Algebra.norm (Q.adicCompletion K) (E.exp (cM Q π Ml • u))) = (w : q.adicCompletion L)
  have hsum : (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • (cM Q π Ml • u)) = x := by
    have h1 : ∀ σ : Gal(q.adicCompletion L/Q.adicCompletion K),
        σ • (cM Q π Ml • u) = cM Q π Ml • (σ • u) := fun σ => by
      simp only [AlgEquiv.smul_def, map_smul]
    rw [Finset.sum_congr rfl (fun σ _ => h1 σ), ← Finset.smul_sum, hu', ← ha]
    rw [Algebra.smul_def, Algebra.smul_def, mul_one]
    rw [show cM Q π Ml = algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) (π ^ Ml)
        from rfl, ← algebraMap_int_eq Q q (π ^ Ml), map_mul]
  calc algebraMap (Q.adicCompletion K) (q.adicCompletion L)
        (Algebra.norm (Q.adicCompletion K) (E.exp (cM Q π Ml • u)))
      = ∏ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • (E.exp (cM Q π Ml • u)) := by
        rw [Algebra.norm_eq_prod_automorphisms]
        simp only [AlgEquiv.smul_def]
    _ = ∏ σ : Gal(q.adicCompletion L/Q.adicCompletion K), E.exp (σ • (cM Q π Ml • u)) := by
        refine Finset.prod_congr rfl fun σ _ =>
          ExpLog.exp_map_algEquiv Q q E σ (hball _ hmem)
    _ = E.exp (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • (cM Q π Ml • u)) :=
        (E.exp_finset_sum Finset.univ (fun σ => σ • (cM Q π Ml • u)) (by
          intro t _
          refine hball _ ((levelSub Q q π b Ml).sum_mem fun σ _ =>
            levelSub_stable Q q π b Ml σ hmem))).symm
    _ = E.exp x := by rw [hsum]
    _ = (w : q.adicCompletion L) := hw'

theorem expSubgroup_norm_eq_one {E : ExpLog q Mexp} {π : Q.adicCompletionIntegers K}
    {b : q.adicCompletion L} {Ml : ℕ} {hball : ∀ x ∈ levelSub Q q π b Ml,
      adicV q x ≤ WithZero.exp (-(Mexp : ℤ))}
    (hb : Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) b = 1)
    (hLI : LinearIndependent (Q.adicCompletion K)
      (fun σ : Gal(q.adicCompletion L/Q.adicCompletion K) => σ • b))
    (σgen : Gal(q.adicCompletion L/Q.adicCompletion K)) (hgen : Subgroup.zpowers σgen = ⊤)
    (hπ0 : cM Q π Ml ≠ 0)
    {w : (q.adicCompletion L)ˣ} (hw : w ∈ expSubgroup Q q E π b Ml hball)
    (hN : algebraMap (Q.adicCompletion K) (q.adicCompletion L)
      (Algebra.norm (Q.adicCompletion K) (w : q.adicCompletion L)) = 1) :
    ∃ v ∈ expSubgroup Q q E π b Ml hball,
      (w : q.adicCompletion L) = σgen (v : q.adicCompletion L) / (v : q.adicCompletion L) := by
  obtain ⟨x, hx, hw'⟩ := (mem_expSubgroup Q q).mp hw
  have hsub : ∀ t : Finset (Gal(q.adicCompletion L/Q.adicCompletion K)), t ⊆ Finset.univ →
      adicV q (∑ σ ∈ t, σ • x) ≤ WithZero.exp (-(Mexp : ℤ)) := by
    intro t _
    refine hball _ ((levelSub Q q π b Ml).sum_mem fun σ _ => levelSub_stable Q q π b Ml σ hx)
  have htr : (∑ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ • x) = 0 := by
    refine E.exp_inj (hsub Finset.univ (Finset.Subset.refl _))
      (by rw [map_zero]; exact bot_le) ?_
    have hprod : (∏ σ : Gal(q.adicCompletion L/Q.adicCompletion K), E.exp (σ • x))
        = algebraMap (Q.adicCompletion K) (q.adicCompletion L)
            (Algebra.norm (Q.adicCompletion K) (w : q.adicCompletion L)) := by
      rw [show (∏ σ : Gal(q.adicCompletion L/Q.adicCompletion K), E.exp (σ • x))
          = ∏ σ : Gal(q.adicCompletion L/Q.adicCompletion K), σ (w : q.adicCompletion L) from
        Finset.prod_congr rfl (fun σ _ => by
          rw [← ExpLog.exp_map_algEquiv Q q E σ (hball x hx), hw'])]
      exact (Algebra.norm_eq_prod_automorphisms (Q.adicCompletion K) (w : q.adicCompletion L)).symm
    rw [E.exp_finset_sum Finset.univ (fun σ => σ • x) hsub, hprod, hN, E.exp_zero]
  obtain ⟨u, hu, hu'⟩ := ker_trace_level Q q (π := π) (b := b) hb hLI σgen hgen hπ0 hx htr
  refine ⟨Units.mk0 (E.exp u) (E.exp_ne_zero (hball u hu)),
    expSubgroup_mem_exp Q q hu, ?_⟩
  show (w : q.adicCompletion L) = σgen (E.exp u) / E.exp u
  rw [← hw', hu', E.exp_sub (hball _ (levelSub_stable Q q π b Ml σgen hu)) (hball u hu),
    ExpLog.exp_map_algEquiv Q q E σgen (hball u hu)]

end Main

end

end Commons.NumberTheory.NumberField.Completion.AdicTateExp

namespace Commons.NumberTheory.NumberField.Completion

open AdicTateExp

/-- **Existence of an open subgroup of the units with trivial Tate cohomology.**

This is the local input used in the proof of the Neukirch–Uchida theorem (CoNF 12.2.1). -/
theorem exists_open_subgroup_units_tate_trivial_exp
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ (σgen : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L),
      Subgroup.zpowers σgen = ⊤ →
    ∃ W : Subgroup (q.adicCompletion L)ˣ,
      (∀ w ∈ W, Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          (w : q.adicCompletion L) = 1) ∧
      (∀ (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) (w : (q.adicCompletion L)ˣ),
        w ∈ W → σ • w ∈ W) ∧
      (∃ M : ℕ, ∀ x : (q.adicCompletionIntegers L)ˣ,
        (x : q.adicCompletionIntegers L) - 1 ∈
            IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) ^ M →
          Units.map (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L)).toMonoidHom x ∈ W) ∧
      (∀ w ∈ W,
        (∀ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L, σ • w = w) →
        ∃ v ∈ W, algebraMap (Q.adicCompletion K) (q.adicCompletion L)
            (Algebra.norm (Q.adicCompletion K) (v : q.adicCompletion L)) = (w : q.adicCompletion L)) ∧
      (∀ w : (q.adicCompletion L)ˣ, w ∈ W →
        algebraMap (Q.adicCompletion K) (q.adicCompletion L)
            (Algebra.norm (Q.adicCompletion K) (w : q.adicCompletion L)) = 1 →
        ∃ v ∈ W, (w : q.adicCompletion L) = σgen (v : q.adicCompletion L) / (v : q.adicCompletion L)) := by
  classical
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  intro σgen hgen
  haveI : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion Q q hq
  have he : 1 ≤ q.asIdeal.ramificationIdx (𝓞 K) := Ideal.ramificationIdx_pos q.asIdeal (𝓞 K)
  have hval : ∀ y : Q.adicCompletion K,
      (adicV q) (algebraMap (Q.adicCompletion K) (q.adicCompletion L) y)
        = ((adicV Q) y) ^ (q.asIdeal.ramificationIdx (𝓞 K)) := by
    intro y
    rw [show algebraMap (Q.adicCompletion K) (q.adicCompletion L) y
        = Commons.RingTheory.Henselian.adicCompletionMap Q q hq y from rfl]
    exact Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow Q q hq y
  have hv : ∀ (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (z : q.adicCompletion L), (adicV q) (σ • z) = (adicV q) z := fun σ z =>
    Commons.NumberTheory.NumberField.Completion.val_algEquiv_adicCompletion Q q hq σ z
  obtain ⟨b, hb, hLI, -⟩ :=
    Commons.FieldTheory.Galois.exists_normalBasis_trace_eq_one (K := Q.adicCompletion K)
      (L := q.adicCompletion L)
  have hv_le_one : ∀ c : Q.adicCompletion K,
      c ∈ (Q.adicCompletionIntegers K : Set (Q.adicCompletion K)) →
      (adicV q) (algebraMap (Q.adicCompletion K) (q.adicCompletion L) c) ≤ 1 := by
    intro c hc
    rw [hval c]
    exact pow_le_one₀ bot_le hc
  obtain ⟨κ, hκ⟩ := generic_bounded Q q b hv_le_one
  obtain ⟨D, hD⟩ := conjLattice_commensurable Q q b hb hLI hval he hv
  let π : Q.adicCompletionIntegers K :=
    Commons.RingTheory.Henselian.uniformizer (R := 𝓞 K) (K := K) Q
  have hπ : (adicV Q) (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) π)
      = WithZero.exp (-1) :=
    Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one Q
  have hπnone : (adicV q) (algebraMap (Q.adicCompletionIntegers K) (q.adicCompletion L) π) ≠ 0 := by
    rw [val_unifQ Q q hπ]; exact WithZero.exp_ne_zero
  have hπ0 : algebraMap (Q.adicCompletionIntegers K) (q.adicCompletion L) π ≠ 0 :=
    (Valuation.ne_zero_iff _).mp hπnone
  obtain ⟨Me, hMe, exp, hconv, hvalsub, hexp0, hexpadd, hexists⟩ :=
    Commons.Analysis.Nonarchimedean.exists_exp_adicCompletion q
  let E : ExpLog q Me := ⟨hMe, exp, hconv, hvalsub, hexp0, hexpadd, hexists⟩
  let Ml : ℕ := Me + (max κ 0).toNat
  let M₃ : ℕ := Me + Ml * q.asIdeal.ramificationIdx (𝓞 K) + D.toNat
  have hMle : (Me : ℤ) + κ ≤ (Ml : ℤ) * (q.asIdeal.ramificationIdx (𝓞 K) : ℤ) := by
    have he1 : (1 : ℤ) ≤ (q.asIdeal.ramificationIdx (𝓞 K) : ℤ) := by exact_mod_cast he
    have hMl0 : (0 : ℤ) ≤ (Ml : ℤ) := Int.natCast_nonneg _
    have h2 : (Me : ℤ) + κ ≤ (Ml : ℤ) := by
      have hcast : (Ml : ℤ) = (Me : ℤ) + max κ 0 := by
        show ((Me + (max κ 0).toNat : ℕ) : ℤ) = (Me : ℤ) + max κ 0
        rw [Nat.cast_add, Int.toNat_of_nonneg (le_max_right κ 0)]
      rw [hcast]; exact add_le_add (le_refl _) (le_max_left κ 0)
    calc (Me : ℤ) + κ ≤ (Ml : ℤ) := h2
      _ = (Ml : ℤ) * 1 := (mul_one _).symm
      _ ≤ (Ml : ℤ) * (q.asIdeal.ramificationIdx (𝓞 K) : ℤ) :=
          mul_le_mul_of_nonneg_left he1 hMl0
  have hball : ∀ x ∈ levelSub Q q π b Ml, (adicV q) x ≤ WithZero.exp (-(Me : ℤ)) := by
    intro x hx
    have h1 := InLevel.valued_le Q q hκ ((mem_levelSub Q q).mp hx)
    refine le_trans h1 ?_
    have h2 : (adicV q) (algebraMap (Q.adicCompletion K) (q.adicCompletion L) (cM Q π Ml))
        = WithZero.exp (-((Ml : ℤ) * (q.asIdeal.ramificationIdx (𝓞 K) : ℤ))) := by
      rw [show cM Q π Ml
          = algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) (π ^ Ml) from rfl,
        ← algebraMap_int_eq Q q (π ^ Ml), map_pow, Valuation.map_pow]
      exact val_unifQ_pow Q q hπ Ml
    rw [h2, ← WithZero.exp_add, WithZero.exp_le_exp]
    linarith
  have hcM : cM Q π Ml ≠ 0 := cM_ne_zero Q q hπ0 Ml
  have hM₃e : (Me : ℤ) ≤ (M₃ : ℤ) := by
    have : (M₃ : ℤ) = (Me : ℤ) + (Ml : ℤ) * (q.asIdeal.ramificationIdx (𝓞 K) : ℤ) + D.toNat := by
      show ((Me + Ml * q.asIdeal.ramificationIdx (𝓞 K) + D.toNat : ℕ) : ℤ) = _
      push_cast; ring
    rw [this]
    have h1 : (0 : ℤ) ≤ (Ml : ℤ) * (q.asIdeal.ramificationIdx (𝓞 K) : ℤ) := by
      refine mul_nonneg (Int.natCast_nonneg _) ?_
      exact_mod_cast Nat.zero_le _
    have h2 : (0 : ℤ) ≤ (D.toNat : ℤ) := Int.natCast_nonneg _
    linarith
  have hM₃D : D + (Ml : ℤ) * (q.asIdeal.ramificationIdx (𝓞 K) : ℤ) ≤ (M₃ : ℤ) := by
    have : (M₃ : ℤ) = (Me : ℤ) + (Ml : ℤ) * (q.asIdeal.ramificationIdx (𝓞 K) : ℤ) + D.toNat := by
      show ((Me + Ml * q.asIdeal.ramificationIdx (𝓞 K) + D.toNat : ℕ) : ℤ) = _
      push_cast; ring
    rw [this]
    have h1 : D ≤ (D.toNat : ℤ) := Int.self_le_toNat D
    have h2 : (0 : ℤ) ≤ (Me : ℤ) := Int.natCast_nonneg _
    linarith
  refine ⟨expSubgroup Q q E π b Ml hball, ?_, ?_, ⟨M₃, ?_⟩, ?_, ?_⟩
  · intro w hw
    exact expSubgroup_val_eq_one Q q hw
  · intro σ w hw
    exact expSubgroup_stable Q q σ hw
  · intro x hx
    exact expSubgroup_mem_principal Q q hD hπ hM₃e hM₃D hx
  · intro w hw hfix
    exact expSubgroup_norm_surj Q q hb hLI σgen hgen hw hfix
  · intro w hw hN
    exact expSubgroup_norm_eq_one Q q hb hLI σgen hgen hcM hw hN

end Commons.NumberTheory.NumberField.Completion
