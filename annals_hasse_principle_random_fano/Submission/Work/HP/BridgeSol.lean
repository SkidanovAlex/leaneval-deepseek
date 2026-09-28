import Mathlib
import Submission.Work.HP.BridgeDefs
import Submission.Work.HP.BridgeEval

/-!
# `HasSolutionsIn` under scaling and base change, and `HasRatZero`

The challenge's `HasSolutionsIn f S` asks for a unimodular point of `f` over `S`.  Here we
prove that this only depends on the `ℚ`-line spanned by `f` (so that it descends to the
projectivization), that it transfers from `ℚ` to any `ℚ`-algebra, and that for
`f = formOf d n a` over `ℚ` it is the same as `HasRatZero`, i.e. a non-zero *integer* zero.
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset

namespace Work.HP

open HassePrincipleRandomFano (HasSolutionsIn)

theorem hasSolutionsIn_smul {σ : Type*} (f : MvPolynomial σ ℚ) (S : Type*) [CommSemiring S]
    [Algebra ℚ S] (c : ℚ) (hc : c ≠ 0) :
    HasSolutionsIn (c • f) S ↔ HasSolutionsIn f S := by
  have hsmul : ∀ x : σ → S, aeval x (c • f) = (algebraMap ℚ S c) * aeval x f := by
    intro x
    rw [MvPolynomial.smul_eq_C_mul, map_mul, aeval_C]
  constructor
  · rintro ⟨x, hx, hf⟩
    refine ⟨x, hx, ?_⟩
    have h1 : (algebraMap ℚ S c) * aeval x f = 0 := by rw [← hsmul x]; exact hf
    calc aeval x f = (algebraMap ℚ S c⁻¹) * ((algebraMap ℚ S c) * aeval x f) := by
          rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
      _ = 0 := by rw [h1, mul_zero]
  · rintro ⟨x, hx, hf⟩
    exact ⟨x, hx, by rw [hsmul x, hf, mul_zero]⟩

theorem hasSolutionsIn_of_rat {σ : Type*} [Fintype σ] (f : MvPolynomial σ ℚ) (S : Type*)
    [CommSemiring S] [Algebra ℚ S] (h : HasSolutionsIn f ℚ) : HasSolutionsIn f S := by
  obtain ⟨x, hx, hf⟩ := h
  refine ⟨fun i => algebraMap ℚ S (x i), ?_, ?_⟩
  · refine (Ideal.eq_top_iff_one _).2 ?_
    have h1 : (1 : ℚ) ∈ (Ideal.span (Set.range x) : Ideal ℚ) := by
      rw [hx]; exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at h1
    obtain ⟨c, hc⟩ := h1
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun i => algebraMap ℚ S (c i), ?_⟩
    have hc' : (∑ i, c i * x i) = 1 := by simpa using hc
    have hsum : (∑ i, algebraMap ℚ S (c i) * algebraMap ℚ S (x i)) = 1 := by
      calc (∑ i, algebraMap ℚ S (c i) * algebraMap ℚ S (x i))
          = ∑ i, algebraMap ℚ S (c i * x i) :=
            Finset.sum_congr rfl fun i _ => (map_mul _ _ _).symm
        _ = algebraMap ℚ S (∑ i, c i * x i) := (map_sum _ _ _).symm
        _ = 1 := by rw [hc']; exact map_one _
    simpa [smul_eq_mul] using hsum
  · have hnat := MvPolynomial.comp_aeval_apply (f := x) (φ := Algebra.ofId ℚ S) f
    simp only [Algebra.ofId_apply] at hnat
    rw [← hnat, hf, map_zero]

/-- A non-zero rational vector has a non-zero integer multiple. -/
lemma exists_int_smul {n : ℕ} (x : Fin (n + 1) → ℚ) (hx : x ≠ 0) :
    ∃ (D : ℕ) (z : Fin (n + 1) → ℤ), D ≠ 0 ∧
      (∀ i, ((z i : ℤ) : ℚ) = (D : ℚ) * x i) ∧ z ≠ 0 := by
  classical
  set D : ℕ := ∏ i, (x i).den with hD
  have hDne : D ≠ 0 := by
    rw [hD]; exact Finset.prod_ne_zero_iff.2 fun i _ => (x i).den_nz
  set z : Fin (n + 1) → ℤ := fun i => ((D / (x i).den : ℕ) : ℤ) * (x i).num with hz
  have hdiv : ∀ i, (x i).den ∣ D := fun i => by
    rw [hD]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hzi : ∀ i, ((z i : ℤ) : ℚ) = (D : ℚ) * x i := by
    intro i
    have hmul : ((x i).den : ℚ) * x i = ((x i).num : ℚ) := by
      rw [mul_comm, Rat.mul_den_eq_num]
    have hDi : ((D / (x i).den : ℕ) : ℚ) * ((x i).den : ℚ) = (D : ℚ) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel (hdiv i)]
    rw [hz, Int.cast_mul, Int.cast_natCast]
    calc ((D / (x i).den : ℕ) : ℚ) * ((x i).num : ℚ)
        = ((D / (x i).den : ℕ) : ℚ) * (((x i).den : ℚ) * x i) := by rw [hmul]
      _ = (D : ℚ) * x i := by rw [← mul_assoc, hDi]
  refine ⟨D, z, hDne, hzi, ?_⟩
  intro hzero
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext fun i => by simpa using h i)
  have h1 : ((z i : ℤ) : ℚ) = 0 := by rw [congrFun hzero i]; rfl
  rw [hzi i] at h1
  have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast hDne
  exact hi ((mul_eq_zero.1 h1).resolve_left hD0)

/-- Casting `formEval` from `ℤ` to `ℚ`. -/
lemma formEval_intCast (d n : ℕ) (a : Mon d n → ℤ) (y : Fin (n + 1) → ℤ) :
    ((formEval d n a y : ℤ) : ℚ) = formEval d n a (fun i => (y i : ℚ)) := by
  simp only [formEval, veronese]
  push_cast
  ring

theorem hasSolutionsIn_rat (d n : ℕ) (a : Mon d n → ℤ) :
    HasSolutionsIn (formOf d n a) ℚ ↔ HasRatZero d n a := by
  constructor
  · rintro ⟨x, hx, hf⟩
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0] at hx
      have hbot : (Ideal.span (Set.range (0 : Fin (n + 1) → ℚ)) : Ideal ℚ) = ⊥ := by
        rw [Ideal.span_eq_bot]
        rintro y ⟨i, rfl⟩
        simp
      rw [hbot] at hx
      exact bot_ne_top hx
    obtain ⟨D, z, hDne, hzi, hz0⟩ := exists_int_smul x hx0
    refine ⟨z, hz0, ?_⟩
    have h2 : (fun i => (z i : ℚ)) = fun i => (D : ℚ) * x i := funext hzi
    have h1 : aeval (fun i => (z i : ℚ)) (formOf d n a) = 0 := by
      rw [h2, aeval_formOf_mul, hf, mul_zero]
    rw [aeval_formOf] at h1
    have h3 : ((formEval d n a z : ℤ) : ℚ) = 0 := by
      rw [formEval_intCast]; exact h1
    exact_mod_cast h3
  · rintro ⟨y, hy0, hy⟩
    refine ⟨fun i => (y i : ℚ), ?_, ?_⟩
    · refine (Ideal.eq_top_iff_one _).2 ?_
      obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
        by_contra h
        push Not at h
        exact hy0 (funext fun i => by simpa using h i)
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨fun j => if j = i then ((y i : ℚ))⁻¹ else 0, ?_⟩
      rw [Finset.sum_eq_single i]
      · simp [smul_eq_mul, hi]
      · intro j _ hj; simp [hj]
      · intro h; exact absurd (Finset.mem_univ i) h
    · rw [aeval_formOf, ← formEval_intCast]
      rw [hy]; simp

end Work.HP
