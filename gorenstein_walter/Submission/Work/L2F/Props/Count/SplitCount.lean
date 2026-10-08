import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Props.Count.Defs
import Submission.Work.L2F.Props.Count.Basic
import Submission.Work.L2F.Mat2.sq_eq_trace_smul_sub_det

open scoped MatrixGroups
open Matrix Polynomial

namespace Work.L2F.Props.Count

/-! ## 1. Elementary algebra of `2 × 2` matrices -/

section MatEntries

variable {α : Type*}

@[simp] theorem mat_apply_00 (a b c d : α) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) α) 0 0 = a := rfl

@[simp] theorem mat_apply_01 (a b c d : α) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) α) 0 1 = b := rfl

@[simp] theorem mat_apply_10 (a b c d : α) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) α) 1 0 = c := rfl

@[simp] theorem mat_apply_11 (a b c d : α) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) α) 1 1 = d := rfl

theorem trace_fin_two_of [AddCommMonoid α] (a b c d : α) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) α).trace = a + d := by
  rw [Matrix.trace_fin_two]
  rfl

end MatEntries

/-- **Nilpotent binomial expansion.**  In any ring, if `N * N = 0` then
`(1 + N) ^ n = 1 + (n : R) * N`. -/
theorem pow_one_add_of_mul_self_eq_zero (R : Type*) [Ring R] (N : R) (h : N * N = 0) (n : ℕ) :
    (1 + N) ^ n = 1 + (n : R) * N := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hk : ((k : R) * N) * N = 0 := by rw [mul_assoc, h, mul_zero]
    rw [pow_succ, ih, mul_add, mul_one, add_mul, one_mul, hk, add_zero]
    push_cast
    noncomm_ring

/-- A unipotent `2 × 2` matrix over a field with `(r : F) ≠ 0` and `M ^ r = 1` is `1`. -/
theorem unipotent_eq_one {F : Type*} [Field F] (r : ℕ) (hr : (r : F) ≠ 0)
    (M : Matrix (Fin 2) (Fin 2) F) (hM : (M - 1) * (M - 1) = 0) (hrM : M ^ r = 1) : M = 1 := by
  have h1 : M = 1 + (M - 1) := by abel
  rw [h1] at hrM
  rw [pow_one_add_of_mul_self_eq_zero _ _ hM r] at hrM
  have hmul0 : (r : Matrix (Fin 2) (Fin 2) F) * (M - 1) = 0 :=
    add_left_cancel (a := (1 : Matrix (Fin 2) (Fin 2) F)) (by simpa using hrM)
  have hcast : (r : Matrix (Fin 2) (Fin 2) F) = (r : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    simp [Matrix.natCast_apply, Matrix.smul_apply, Matrix.one_apply]
  have hsmul : (r : F) • (M - 1) = 0 := by
    rw [hcast, smul_mul_assoc, one_mul] at hmul0
    exact hmul0
  have hN0 : M - 1 = 0 := by
    ext i j
    have hij : ((r : F) • (M - 1)) i j = 0 := by rw [hsmul, Matrix.zero_apply]
    rw [Matrix.smul_apply] at hij
    rcases mul_eq_zero.mp hij with h' | h'
    · exact absurd h' hr
    · exact h'
  exact sub_eq_zero.mp hN0

/-- If `x ∈ SL(2,F)` has trace `μ + μ⁻¹` with `μ ≠ μ⁻¹` and `μ ^ n = 1`, then `x ^ n = 1`. -/
theorem pow_eq_one_of_trace {F : Type*} [Field F] (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (μ : F) (hμ : μ ≠ 0) (hne : μ ≠ μ⁻¹) (n : ℕ) (hn : μ ^ n = 1)
    (ht : (x : Matrix (Fin 2) (Fin 2) F).trace = μ + μ⁻¹) : x ^ n = 1 := by
  have hchar : (x : Matrix (Fin 2) (Fin 2) F).charpoly = (X - C μ) * (X - C μ⁻¹) := by
    have hmul : (C μ * C μ⁻¹ : F[X]) = 1 := by rw [← C_mul, mul_inv_cancel₀ hμ, C_1]
    rw [Matrix.charpoly_fin_two, Matrix.SpecialLinearGroup.det_coe, ht, C_add, C_1]
    rw [show (X - C μ) * (X - C μ⁻¹) = X ^ 2 - (C μ + C μ⁻¹) * X + C μ * C μ⁻¹ from by ring,
      hmul]
  have hne' : μ⁻¹ - μ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hcop : IsCoprime (X - C μ) (X - C μ⁻¹) := by
    refine ⟨C ((μ⁻¹ - μ)⁻¹), -C ((μ⁻¹ - μ)⁻¹), ?_⟩
    have h1 : C ((μ⁻¹ - μ)⁻¹) * (X - C μ) + (-C ((μ⁻¹ - μ)⁻¹)) * (X - C μ⁻¹)
        = C ((μ⁻¹ - μ)⁻¹) * ((X - C μ) - (X - C μ⁻¹)) := by ring
    rw [h1, show (X - C μ) - (X - C μ⁻¹) = C (μ⁻¹ - μ) from by rw [map_sub]; ring,
      ← C_mul, inv_mul_cancel₀ hne', C_1]
  have hdvd1 : (X - C μ) ∣ (X : F[X]) ^ n - 1 := by
    rw [dvd_iff_isRoot]
    simp [hn]
  have hdvd2 : (X - C μ⁻¹) ∣ (X : F[X]) ^ n - 1 := by
    rw [dvd_iff_isRoot]
    simp [inv_pow, hn]
  have hdvd : (X - C μ) * (X - C μ⁻¹) ∣ (X : F[X]) ^ n - 1 := hcop.mul_dvd hdvd1 hdvd2
  obtain ⟨g, hg⟩ := hdvd
  have haev : (Polynomial.aeval (x : Matrix (Fin 2) (Fin 2) F)) ((X : F[X]) ^ n - 1) = 0 := by
    rw [hg, map_mul]
    have hzero : (Polynomial.aeval (x : Matrix (Fin 2) (Fin 2) F))
        ((X - C μ) * (X - C μ⁻¹)) = 0 := by
      rw [← hchar]
      exact Matrix.aeval_self_charpoly _
    rw [hzero, zero_mul]
  have hmat : (x : Matrix (Fin 2) (Fin 2) F) ^ n = 1 := by
    have h := haev
    rw [show (Polynomial.aeval (x : Matrix (Fin 2) (Fin 2) F)) ((X : F[X]) ^ n - 1)
        = (x : Matrix (Fin 2) (Fin 2) F) ^ n - 1 from by simp] at h
    exact sub_eq_zero.mp h
  have hh : ((x ^ n : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_pow]
    exact hmat
  exact Matrix.SpecialLinearGroup.ext _ _ (fun i j => by
    simp only [hh, Matrix.SpecialLinearGroup.coe_one])

/-- Eigenvectors are propagated by powers. -/
theorem mulVec_pow_of_eigen {F : Type*} [Field F] (M : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F)
    (μ : F) (h : M *ᵥ v = μ • v) (k : ℕ) : (M ^ k) *ᵥ v = μ ^ k • v := by
  induction k with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, ← pow_succ']

/-- The eigenvalue of an eigenvector of a matrix is a root of its characteristic polynomial. -/
theorem isRoot_charpoly_of_eigen {F : Type*} [Field F] (M : Matrix (Fin 2) (Fin 2) F)
    (v : Fin 2 → F) (μ : F) (hv : v ≠ 0) (h : M *ᵥ v = μ • v) : M.charpoly.IsRoot μ := by
  have h1 : Module.End.HasEigenvalue (Matrix.toLin' M) μ := by
    rw [Module.End.hasEigenvalue_iff, Submodule.ne_bot_iff]
    exact ⟨v, by rwa [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply], hv⟩
  rwa [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin'] at h1

/-- A subtype whose predicate is `x = a ∨ x = b`, with `a ≠ b`, has two elements. -/
theorem Nat.card_subtype_eq_two {α : Type*} [Fintype α] (p : α → Prop) (a b : α) (hab : a ≠ b)
    (h : ∀ x, p x ↔ x = a ∨ x = b) : Nat.card {x // p x} = 2 := by
  classical
  have h0 : Nat.card {x : α // p x} = ({x : α | p x} : Set α).ncard := rfl
  have h1 : ({x : α | p x} : Set α).ncard = ({x : α | x = a ∨ x = b} : Set α).ncard := by
    congr 1
    ext x
    exact h x
  have h2 : ({x : α | x = a ∨ x = b} : Set α).ncard = 2 := by
    rw [show ({x : α | x = a ∨ x = b} : Set α) = ↑({a, b} : Finset α) from by
        ext x
        simp,
      Set.ncard_coe_finset, Finset.card_pair hab]
  rw [h0, h1, h2]

/-- The solutions of `p * (t - p) = 1` are exactly `a` and `b` when `t = a + b`, `a * b = 1` and
`a ≠ b`. -/
theorem roots_card {F : Type*} [Field F] [Fintype F] (t a b : F) (hab : a ≠ b) (ht : t = a + b)
    (hab1 : a * b = 1) : Nat.card {p : F // p * (t - p) = 1} = 2 := by
  apply Nat.card_subtype_eq_two _ a b hab
  intro p
  rw [ht]
  constructor
  · intro h
    have e : p * (a + b - p) = a * b := by rw [h, hab1]
    have h'' : (p - a) * (p - b) = 0 := by
      have h2 : (p - a) * (p - b) = a * b - p * (a + b - p) := by ring
      rw [h2, e, sub_self]
    rcases mul_eq_zero.mp h'' with h3 | h3
    · exact Or.inl (sub_eq_zero.mp h3)
    · exact Or.inr (sub_eq_zero.mp h3)
  · rintro (hpa | hpb)
    · rw [hpa, show a + b - a = b from by ring, hab1]
    · rw [hpb, show a + b - b = a from by ring, mul_comm b a, hab1]

/-! ## 2. The number of elements of `SL(2,F)` with a prescribed split trace -/

/-- The number of elements of `SL(2,F)` whose trace is `a + b`, where `a * b = 1` and `a ≠ b`, is
`q (q + 1)`: these are exactly the matrices with eigenvalues `a` and `b`. -/
theorem TraceCount (F : Type*) [Field F] [Fintype F] (a b : F) (hab : a ≠ b) (hab1 : a * b = 1) :
    Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F //
        (x : Matrix (Fin 2) (Fin 2) F).trace = a + b} = Nat.card F * (Nat.card F + 1) := by
  classical
  set t : F := a + b with ht
  -- (i) elements with vanishing `(0,1)` entry: `{p // p * (t - p) = 1} × F`
  have hAz : Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F //
      (x : Matrix (Fin 2) (Fin 2) F).trace = t ∧ (x : Matrix (Fin 2) (Fin 2) F) 0 1 = 0}
      = 2 * Nat.card F := by
    have e : {x : Matrix.SpecialLinearGroup (Fin 2) F //
        (x : Matrix (Fin 2) (Fin 2) F).trace = t ∧ (x : Matrix (Fin 2) (Fin 2) F) 0 1 = 0}
        ≃ {p : F // p * (t - p) = 1} × F :=
      { toFun := fun x =>
          (⟨(x.1 : Matrix (Fin 2) (Fin 2) F) 0 0, by
            have hdet : (x : Matrix (Fin 2) (Fin 2) F).det = 1 :=
              Matrix.SpecialLinearGroup.det_coe _
            have htrc : (x : Matrix (Fin 2) (Fin 2) F).trace = t := x.2.1
            rw [Matrix.det_fin_two] at hdet
            rw [Matrix.trace_fin_two] at htrc
            rw [x.2.2, zero_mul, sub_zero] at hdet
            rw [show (x : Matrix (Fin 2) (Fin 2) F) 1 1
                = t - (x : Matrix (Fin 2) (Fin 2) F) 0 0 from by
                  linear_combination htrc] at hdet
            exact hdet⟩, (x.1 : Matrix (Fin 2) (Fin 2) F) 1 0)
        invFun := fun q =>
          ⟨⟨!![q.1.1, 0; q.2, t - q.1.1], by
              rw [Matrix.det_fin_two_of]
              rw [show q.1.1 * (t - q.1.1) - 0 * q.2 = q.1.1 * (t - q.1.1) from by ring]
              exact q.1.2⟩,
            by
              rw [trace_fin_two_of]
              ring,
            by rfl⟩
        left_inv := by
          rintro ⟨x, hx, hx0⟩
          refine Subtype.ext (Subtype.ext (Matrix.ext fun i j => ?_))
          have htrc : (x : Matrix (Fin 2) (Fin 2) F) 0 0
              + (x : Matrix (Fin 2) (Fin 2) F) 1 1
              = t := by
            have h := hx
            rwa [Matrix.trace_fin_two] at h
          fin_cases i <;> fin_cases j
          · rfl
          · exact hx0.symm
          · rfl
          · show t - (x : Matrix (Fin 2) (Fin 2) F) 0 0 = (x : Matrix (Fin 2) (Fin 2) F) 1 1
            linear_combination -htrc
        right_inv := by
          rintro ⟨⟨p, hp⟩, c⟩
          refine Prod.ext ?_ ?_
          · exact Subtype.ext rfl
          · rfl }
    rw [Nat.card_congr e, Nat.card_prod, roots_card t a b hab (by rw [ht]) hab1]
  -- (ii) elements with nonvanishing `(0,1)` entry: `F × Fˣ`
  have hAnz : Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F //
      (x : Matrix (Fin 2) (Fin 2) F).trace = t ∧ (x : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0}
      = Nat.card F * Nat.card Fˣ := by
    have e : {x : Matrix.SpecialLinearGroup (Fin 2) F //
        (x : Matrix (Fin 2) (Fin 2) F).trace = t ∧ (x : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0}
        ≃ F × Fˣ :=
      { toFun := fun x => ((x.1 : Matrix (Fin 2) (Fin 2) F) 0 0,
          Units.mk0 ((x.1 : Matrix (Fin 2) (Fin 2) F) 0 1) (by simpa using x.2.2))
        invFun := fun p => ⟨⟨!![p.1, (p.2 : F);
            (p.1 * (t - p.1) - 1) * ((p.2 : F))⁻¹, t - p.1], by
            have hp : (p.2 : F) ≠ 0 := Units.ne_zero p.2
            rw [Matrix.det_fin_two_of]
            field_simp
            ring⟩,
          by
            rw [trace_fin_two_of]
            ring,
          by
            show (p.2 : F) ≠ 0
            exact Units.ne_zero p.2⟩
        left_inv := by
          rintro ⟨x, hx, hx0⟩
          refine Subtype.ext (Subtype.ext (Matrix.ext fun i j => ?_))
          have hdet : (x : Matrix (Fin 2) (Fin 2) F) 0 0
              * (x : Matrix (Fin 2) (Fin 2) F) 1 1
              - (x : Matrix (Fin 2) (Fin 2) F) 0 1
              * (x : Matrix (Fin 2) (Fin 2) F) 1 0
              = 1 := by
            have h := Matrix.SpecialLinearGroup.det_coe x
            rwa [Matrix.det_fin_two] at h
          have htrc : (x : Matrix (Fin 2) (Fin 2) F) 0 0
              + (x : Matrix (Fin 2) (Fin 2) F) 1 1
              = t := by
            have h := hx
            rwa [Matrix.trace_fin_two] at h
          fin_cases i <;> fin_cases j
          · rfl
          · show ((Units.mk0 ((x : Matrix (Fin 2) (Fin 2) F) 0 1)
                  (by simpa using hx0) : Fˣ) : F) = (x : Matrix (Fin 2) (Fin 2) F) 0 1
            rw [Units.val_mk0]
          · show (((x : Matrix (Fin 2) (Fin 2) F) 0 0 * (t - (x : Matrix (Fin 2) (Fin 2) F) 0 0)
                  - 1) * (((Units.mk0 ((x : Matrix (Fin 2) (Fin 2) F) 0 1)
                    (by simpa using hx0) : Fˣ) : F))⁻¹)
                = (x : Matrix (Fin 2) (Fin 2) F) 1 0
            rw [Units.val_mk0]
            rw [show (x : Matrix (Fin 2) (Fin 2) F) 1 1
                = t - (x : Matrix (Fin 2) (Fin 2) F) 0 0 from by linear_combination htrc]
              at hdet
            field_simp
            linear_combination hdet
          · show t - (x : Matrix (Fin 2) (Fin 2) F) 0 0 = (x : Matrix (Fin 2) (Fin 2) F) 1 1
            linear_combination -htrc }
    rw [Nat.card_congr e, Nat.card_prod]
  -- (iii) split according to whether the `(0,1)` entry vanishes
  have hsplit : Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F //
        (x : Matrix (Fin 2) (Fin 2) F).trace = t}
      = Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F //
          (x : Matrix (Fin 2) (Fin 2) F).trace = t ∧ (x : Matrix (Fin 2) (Fin 2) F) 0 1 = 0}
        + Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F //
          (x : Matrix (Fin 2) (Fin 2) F).trace = t ∧ (x : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0} := by
    have hset : ({x : Matrix.SpecialLinearGroup (Fin 2) F |
          (x : Matrix (Fin 2) (Fin 2) F).trace = t} : Set _)
        = {x : Matrix.SpecialLinearGroup (Fin 2) F |
              (x : Matrix (Fin 2) (Fin 2) F).trace = t ∧
                (x : Matrix (Fin 2) (Fin 2) F) 0 1 = 0}
          ∪ {x : Matrix.SpecialLinearGroup (Fin 2) F |
              (x : Matrix (Fin 2) (Fin 2) F).trace = t ∧
                (x : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0} := by
      ext x
      by_cases h : (x : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 <;> simp [h]
    have hdisj : Disjoint ({x : Matrix.SpecialLinearGroup (Fin 2) F |
          (x : Matrix (Fin 2) (Fin 2) F).trace = t ∧
            (x : Matrix (Fin 2) (Fin 2) F) 0 1 = 0} : Set _)
        {x : Matrix.SpecialLinearGroup (Fin 2) F |
          (x : Matrix (Fin 2) (Fin 2) F).trace = t ∧
            (x : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0} := by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact hx'.2 hx.2
    have hc1 : ({x : Matrix.SpecialLinearGroup (Fin 2) F |
          (x : Matrix (Fin 2) (Fin 2) F).trace = t ∧
            (x : Matrix (Fin 2) (Fin 2) F) 0 1 = 0} : Set _).ncard
        = Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F //
            (x : Matrix (Fin 2) (Fin 2) F).trace = t ∧ (x : Matrix (Fin 2) (Fin 2) F) 0 1 = 0} := rfl
    have hc2 : ({x : Matrix.SpecialLinearGroup (Fin 2) F |
          (x : Matrix (Fin 2) (Fin 2) F).trace = t ∧
            (x : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0} : Set _).ncard
        = Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F //
            (x : Matrix (Fin 2) (Fin 2) F).trace = t ∧ (x : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0} := rfl
    rw [show Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F //
          (x : Matrix (Fin 2) (Fin 2) F).trace = t}
        = ({x : Matrix.SpecialLinearGroup (Fin 2) F |
              (x : Matrix (Fin 2) (Fin 2) F).trace = t} : Set _).ncard from rfl,
      hset, Set.ncard_union_eq hdisj, hc1, hc2]
  obtain ⟨k, hk⟩ : ∃ k, Nat.card F = k + 1 := by
    have hpos : 0 < Nat.card F := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_pos_iff.mpr ⟨0⟩
    exact ⟨Nat.card F - 1, (Nat.sub_add_cancel hpos).symm⟩
  rw [hsplit, hAz, hAnz, Nat.card_units, hk, Nat.add_sub_cancel]
  ring

/-! ## 3. The fibres of `u ↦ u + u⁻¹` on the units of order `r` -/

/-- A unit of order `r` (`r` prime, `r ≠ 2`) is different from its inverse. -/
theorem inv_ne_self_of_orderOf {F : Type*} [Field F] (r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2)
    (u : Fˣ) (hu : orderOf u = r) : (u : F) ≠ ((u : F))⁻¹ := by
  intro h
  have hu2 : u ^ 2 = (1 : Fˣ) := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_two]
    nth_rewrite 1 [h]
    exact inv_mul_cancel₀ (Units.ne_zero u)
  have hdvd : orderOf u ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hu2
  rw [hu] at hdvd
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hdvd)

/-- There are exactly two units `v` of order `r` with `v + v⁻¹ = u + u⁻¹`, namely `u` and
`u⁻¹`. -/
theorem FiberTwo (F : Type*) [Field F] [Fintype F] (r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2)
    (u : Fˣ) (hu : orderOf u = r) :
    Nat.card {v : Fˣ // orderOf v = r ∧
      (v : F) + ((v : F))⁻¹ = (u : F) + ((u : F))⁻¹} = 2 := by
  classical
  have key : ∀ v : Fˣ, (orderOf v = r ∧
      (v : F) + ((v : F))⁻¹ = (u : F) + ((u : F))⁻¹) ↔ v = u ∨ v = u⁻¹ := by
    intro v
    constructor
    · rintro ⟨hv, heq⟩
      have hμ0 : (v : F) ≠ 0 := Units.ne_zero v
      have hν0 : (u : F) ≠ 0 := Units.ne_zero u
      have h : ((v : F) - (u : F)) * ((v : F) * (u : F) - 1) = 0 := by
        have hc := congrArg (fun z : F => z * ((v : F) * (u : F))) heq
        field_simp at hc
        linear_combination hc
      rcases mul_eq_zero.mp h with h1 | h1
      · exact Or.inl (Units.ext (sub_eq_zero.mp h1))
      · refine Or.inr (Units.ext ?_)
        have h3 : (v : F) * (u : F) = 1 := sub_eq_zero.mp h1
        have h4 : v * u = 1 := by
          refine Units.ext ?_
          rw [Units.val_mul, Units.val_one]
          exact h3
        have h5 : v = u⁻¹ := mul_eq_one_iff_eq_inv.mp h4
        rw [h5, Units.val_inv_eq_inv_val]
    · rintro (rfl | h)
      · exact ⟨hu, rfl⟩
      · refine ⟨?_, ?_⟩
        · rw [h, orderOf_inv, hu]
        · rw [h, Units.val_inv_eq_inv_val, inv_inv]
          ring
  have hune' : u ≠ u⁻¹ := by
    intro h
    have hu2 : u ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [h]
      exact inv_mul_cancel u
    have hdvd : orderOf u ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hu2
    rw [hu] at hdvd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hdvd)
  rw [Nat.card_congr (Equiv.subtypeEquivRight key)]
  exact Nat.card_subtype_eq_two _ u u⁻¹ hune' (fun _ => Iff.rfl)

/-! ## 4. Eigenvectors versus traces -/

/-- An element of `SL(2,F)` of prime order `r ≠ 2` with an eigenvector over `F` has trace
`u + u⁻¹` for a unit `u` of order `r`. -/
theorem exists_unit_trace_of_eigenvector {F : Type*} [Field F] (r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrc : (r : F) ≠ 0) (x : Matrix.SpecialLinearGroup (Fin 2) F) (hx : orderOf x = r)
    (hv : Work.L2F.Count.HasEigenvector F (x : Matrix (Fin 2) (Fin 2) F)) :
    ∃ u : Fˣ, orderOf u = r ∧
      (x : Matrix (Fin 2) (Fin 2) F).trace = (u : F) + ((u : F))⁻¹ := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨v, hv0, μ, hμv⟩ := hv
  have hxr : x ^ r = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hxr' : (x : Matrix (Fin 2) (Fin 2) F) ^ r = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hxr, Matrix.SpecialLinearGroup.coe_one]
  have hroot : ((x : Matrix (Fin 2) (Fin 2) F).charpoly).IsRoot μ :=
    isRoot_charpoly_of_eigen _ v μ hv0 hμv
  have hμr : μ ^ r = 1 := by
    have h1 := mulVec_pow_of_eigen (x : Matrix (Fin 2) (Fin 2) F) v μ hμv r
    rw [hxr', Matrix.one_mulVec] at h1
    have h2 : (μ ^ r - 1) • v = 0 := by
      rw [sub_smul, one_smul, h1.symm, sub_self]
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.mp hv0
    have h3 := congrFun h2 i
    rw [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h3
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hi)
  have hμne1 : μ ≠ 1 := by
    intro hμ1
    have hroot1 : ((x : Matrix (Fin 2) (Fin 2) F).charpoly).IsRoot 1 := by
      rwa [hμ1] at hroot
    rw [Work.L2F.Count.charpoly_sl, Work.L2F.Count.quad_isRoot_iff, one_pow, mul_one] at hroot1
    have ht2 : (x : Matrix (Fin 2) (Fin 2) F).trace = 2 := by linear_combination -hroot1
    have hsq : ((x : Matrix (Fin 2) (Fin 2) F) - 1) * ((x : Matrix (Fin 2) (Fin 2) F) - 1)
        = 0 := by
      have hCH := Work.L2F.Mat2.sq_eq_trace_smul_sub_det F (x : Matrix (Fin 2) (Fin 2) F)
      rw [Matrix.SpecialLinearGroup.det_coe, one_smul, ht2] at hCH
      rw [show ((2 : F) • (x : Matrix (Fin 2) (Fin 2) F))
          = (x : Matrix (Fin 2) (Fin 2) F) + (x : Matrix (Fin 2) (Fin 2) F) from by
        rw [show (2 : F) = 1 + 1 from by norm_num, add_smul, one_smul]] at hCH
      rw [mul_sub, sub_mul, mul_one, one_mul, hCH]
      noncomm_ring
    have hM1 : (x : Matrix (Fin 2) (Fin 2) F) = 1 :=
      unipotent_eq_one r hrc _ hsq (by rw [← Matrix.SpecialLinearGroup.coe_pow, hxr,
        Matrix.SpecialLinearGroup.coe_one])
    have hx1 : x = 1 := Subtype.ext hM1
    rw [hx1, orderOf_one] at hx
    exact hr.ne_one hx.symm
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h, zero_pow hr.pos.ne'] at hμr
    exact zero_ne_one hμr
  have htrace : (x : Matrix (Fin 2) (Fin 2) F).trace = μ + μ⁻¹ := by
    rw [Work.L2F.Count.charpoly_sl, Work.L2F.Count.quad_isRoot_iff] at hroot
    field_simp
    linear_combination -hroot
  refine ⟨Units.mk0 μ hμ0, ?_, htrace⟩
  refine (orderOf_eq_prime_iff).mpr ⟨?_, ?_⟩
  · refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact hμr
  · intro h
    exact hμne1 (by simpa using congrArg (fun z : Fˣ => (z : F)) h)

/-- An element of `SL(2,F)` with trace `u + u⁻¹` for a unit `u` of prime order `r ≠ 2` has order
`r` and an eigenvector over `F`. -/
theorem orderOf_and_hasEigenvector_of_trace {F : Type*} [Field F] (r : ℕ) (hr : r.Prime)
    (hr2 : r ≠ 2) (hrc : (r : F) ≠ 0) (u : Fˣ) (hu : orderOf u = r)
    (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (ht : (x : Matrix (Fin 2) (Fin 2) F).trace = (u : F) + ((u : F))⁻¹) :
    orderOf x = r ∧ Work.L2F.Count.HasEigenvector F (x : Matrix (Fin 2) (Fin 2) F) := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨hpow, hone⟩ := (orderOf_eq_prime_iff).mp hu
  have hμr : (u : F) ^ r = 1 := by
    have h := congrArg (fun z : Fˣ => (z : F)) hpow
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at h
  have hμ1 : (u : F) ≠ 1 := fun h => hone (Units.ext (by simpa using h))
  have hμ0 : (u : F) ≠ 0 := Units.ne_zero u
  have hne : (u : F) ≠ ((u : F))⁻¹ := inv_ne_self_of_orderOf r hr hr2 u hu
  have hXr : x ^ r = 1 := pow_eq_one_of_trace x (u : F) hμ0 hne r hμr ht
  have hXne : x ≠ 1 := by
    intro h1
    have ht2 : (u : F) + ((u : F))⁻¹ = 2 := by
      rw [← ht, h1, Matrix.SpecialLinearGroup.coe_one, Matrix.trace_one]
      simp
    have hsq : ((u : F) - 1) ^ 2 = 0 := by
      have h3 : (u : F) ^ 2 + 1 = 2 * (u : F) := by
        have h := congrArg (· * (u : F)) ht2
        rw [add_mul, inv_mul_cancel₀ hμ0] at h
        simpa [pow_two] using h
      linear_combination h3
    have h4 : (u : F) - 1 = 0 := by
      have h5 := hsq
      rw [pow_two] at h5
      exact mul_self_eq_zero.mp h5
    exact hμ1 (sub_eq_zero.mp h4)
  have heig : Work.L2F.Count.HasEigenvector F (x : Matrix (Fin 2) (Fin 2) F) := by
    refine (Work.L2F.Count.hasEigenvector_iff_charpoly_isRoot _).mpr ⟨(u : F), ?_⟩
    rw [Work.L2F.Count.charpoly_sl, Work.L2F.Count.quad_isRoot_iff, ht]
    field_simp
    ring
  exact ⟨(orderOf_eq_prime_iff).mpr ⟨hXr, hXne⟩, heig⟩

/-! ## 5. The sets that are counted -/

/-- The units of `F` of order `r`. -/
abbrev Uset (F : Type*) [Field F] (r : ℕ) : Type _ := {u : Fˣ // orderOf u = r}

/-- The number `u + u⁻¹` attached to a unit of order `r`. -/
abbrev phi (F : Type*) [Field F] (r : ℕ) (u : Uset F r) : F := (u.1 : F) + ((u.1 : F))⁻¹

/-- The set of traces `u + u⁻¹`. -/
abbrev Tset (F : Type*) [Field F] (r : ℕ) : Type _ := {t : F // ∃ u : Uset F r, phi F r u = t}

/-- `u ↦ u + u⁻¹` as a map onto the set of traces. -/
abbrev phiT (F : Type*) [Field F] (r : ℕ) (u : Uset F r) : Tset F r :=
  ⟨phi F r u, ⟨u, rfl⟩⟩

/-- Elements of `SL(2,F)` of order `r` having an eigenvector over `F`. -/
abbrev Sset (F : Type*) [Field F] (r : ℕ) : Type _ :=
  {x : Matrix.SpecialLinearGroup (Fin 2) F //
    orderOf x = r ∧ Work.L2F.Count.HasEigenvector F (x : Matrix (Fin 2) (Fin 2) F)}

/-- Elements of `SL(2,F)` whose trace is `u + u⁻¹` for a unit `u` of order `r`. -/
abbrev Zset (F : Type*) [Field F] (r : ℕ) : Type _ :=
  {x : Matrix.SpecialLinearGroup (Fin 2) F //
    ∃ u : Uset F r, phi F r u = (x : Matrix (Fin 2) (Fin 2) F).trace}

/-- The trace map `Zset → Tset`. -/
abbrev gZ (F : Type*) [Field F] (r : ℕ) : Zset F r → Tset F r :=
  fun x => ⟨(x.1 : Matrix (Fin 2) (Fin 2) F).trace, x.2⟩

/-- The elements of `SL(2,F)` with trace `t`. -/
abbrev Atlas (F : Type*) [Field F] (t : F) : Type _ :=
  {x : Matrix.SpecialLinearGroup (Fin 2) F // (x : Matrix (Fin 2) (Fin 2) F).trace = t}

/-! ## 6. The main theorem -/

theorem SplitCount (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0) (r : ℕ) (hr : r.Prime)
    (hr2 : r ≠ 2) (hrc : (r : F) ≠ 0) :
    2 * (Nat.card F - 1) * Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F //
        orderOf x = r ∧ Work.L2F.Count.HasEigenvector F (x : Matrix (Fin 2) (Fin 2) F)}
      = (Nat.card F ^ 2 - 1) * Nat.card {u : Fˣ // orderOf u = r} * Nat.card F := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  -- `Sset = Zset`
  have hSZ : Nat.card (Sset F r) = Nat.card (Zset F r) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by
      constructor
      · rintro ⟨hx, hv⟩
        obtain ⟨u, hu, ht⟩ := exists_unit_trace_of_eigenvector r hr hr2 hrc x hx hv
        exact ⟨⟨u, hu⟩, ht.symm⟩
      · rintro ⟨u, ht⟩
        exact orderOf_and_hasEigenvector_of_trace r hr hr2 hrc u.1 u.2 x ht.symm))
  -- `Zset` fibres over `Tset`
  have hfiberZ : ∀ t : Tset F r, Nat.card {x : Zset F r // gZ F r x = t}
      = Nat.card F * (Nat.card F + 1) := by
    intro t
    obtain ⟨u₀, hu₀⟩ := t.2
    have hne : (u₀.1 : F) ≠ ((u₀.1 : F))⁻¹ := inv_ne_self_of_orderOf r hr hr2 u₀.1 u₀.2
    have hmul : (u₀.1 : F) * ((u₀.1 : F))⁻¹ = 1 := mul_inv_cancel₀ (Units.ne_zero u₀.1)
    have hAt : Nat.card (Atlas F (t.1)) = Nat.card F * (Nat.card F + 1) := by
      rw [show (t.1 : F) = (u₀.1 : F) + ((u₀.1 : F))⁻¹ from hu₀.symm]
      exact TraceCount F (u₀.1 : F) ((u₀.1 : F))⁻¹ hne hmul
    have eAtlas : {x : Zset F r // gZ F r x = t} ≃ Atlas F (t.1) :=
      { toFun := fun x => ⟨x.1.1, Subtype.ext_iff.mp x.2⟩
        invFun := fun y => ⟨⟨y.1, by
            refine ⟨u₀, ?_⟩
            rw [hu₀, y.2]⟩, Subtype.ext y.2⟩
        left_inv := by rintro ⟨⟨x, hx⟩, hxg⟩; exact Subtype.ext (Subtype.ext rfl)
        right_inv := by rintro ⟨y, hy⟩; exact Subtype.ext rfl }
    rw [Nat.card_congr eAtlas]
    exact hAt
  have hZT : Nat.card (Zset F r) = Nat.card (Tset F r) * (Nat.card F * (Nat.card F + 1)) := by
    rw [show Nat.card (Zset F r)
        = Nat.card (Σ t : Tset F r, {x : Zset F r // gZ F r x = t}) from
      Nat.card_congr (Equiv.sigmaFiberEquiv (gZ F r)).symm]
    rw [Nat.card_sigma]
    rw [show (∑ t : Tset F r, Nat.card {x : Zset F r // gZ F r x = t})
        = ∑ _t : Tset F r, Nat.card F * (Nat.card F + 1) from
      Finset.sum_congr rfl (fun t _ => hfiberZ t)]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul,
      Nat.cast_id]
  -- `Uset` fibres over `Tset`
  have hfiberU : ∀ t : Tset F r, Nat.card {u : Uset F r // phiT F r u = t} = 2 := by
    intro t
    obtain ⟨u₀, hu₀⟩ := t.2
    have hFT := FiberTwo F r hr hr2 u₀.1 u₀.2
    have e : {u : Uset F r // phiT F r u = t}
        ≃ {v : Fˣ // orderOf v = r ∧
            (v : F) + ((v : F))⁻¹ = (u₀.1 : F) + ((u₀.1 : F))⁻¹} :=
      (Equiv.subtypeEquivRight (fun u : Uset F r =>
        show phiT F r u = t ↔ (u.1 : F) + ((u.1 : F))⁻¹ = t.1 from Subtype.ext_iff)).trans
        ((Equiv.subtypeEquivRight (fun u : Uset F r =>
            Iff.intro
              (fun h => by
                rw [h, show (t.1 : F) = (u₀.1 : F) + ((u₀.1 : F))⁻¹ from hu₀.symm])
              (fun h => by
                rw [h, show (u₀.1 : F) + ((u₀.1 : F))⁻¹ = t.1 from hu₀]))).trans
          (Equiv.subtypeSubtypeEquivSubtypeInter (fun v : Fˣ => orderOf v = r)
            (fun v : Fˣ => (v : F) + ((v : F))⁻¹ = (u₀.1 : F) + ((u₀.1 : F))⁻¹)))
    rw [Nat.card_congr e]
    exact hFT
  have hUT : Nat.card (Uset F r) = 2 * Nat.card (Tset F r) := by
    rw [show Nat.card (Uset F r)
        = Nat.card (Σ t : Tset F r, {u : Uset F r // phiT F r u = t}) from
      Nat.card_congr (Equiv.sigmaFiberEquiv (phiT F r)).symm]
    rw [Nat.card_sigma]
    rw [show (∑ t : Tset F r, Nat.card {u : Uset F r // phiT F r u = t})
        = ∑ _t : Tset F r, 2 from Finset.sum_congr rfl (fun t _ => hfiberU t)]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul,
      Nat.cast_id]
    ring
  have hN : 2 * Nat.card (Sset F r) = Nat.card (Uset F r) * (Nat.card F * (Nat.card F + 1)) := by
    rw [hSZ, hZT, hUT]
    ring
  have hq1 : (Nat.card F - 1) * (Nat.card F + 1) = Nat.card F ^ 2 - 1 := by
    obtain ⟨k, hk⟩ : ∃ k, Nat.card F = k + 1 := by
      have hpos : 0 < Nat.card F := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_pos_iff.mpr ⟨0⟩
      exact ⟨Nat.card F - 1, (Nat.sub_add_cancel hpos).symm⟩
    rw [hk, Nat.add_sub_cancel]
    have h2 : (k + 1) ^ 2 = k * (k + 2) + 1 := by ring
    have h3 : k + 1 + 1 = k + 2 := by ring
    rw [h3]
    omega
  calc 2 * (Nat.card F - 1) * Nat.card (Sset F r)
      = (Nat.card F - 1) * (2 * Nat.card (Sset F r)) := by ring
    _ = (Nat.card F - 1) * (Nat.card (Uset F r) * (Nat.card F * (Nat.card F + 1))) := by
        rw [hN]
    _ = ((Nat.card F - 1) * (Nat.card F + 1)) * Nat.card (Uset F r) * Nat.card F := by ring
    _ = (Nat.card F ^ 2 - 1) * Nat.card (Uset F r) * Nat.card F := by rw [hq1]

end Work.L2F.Props.Count
