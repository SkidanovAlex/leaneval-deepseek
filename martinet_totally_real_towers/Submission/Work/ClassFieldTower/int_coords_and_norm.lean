import Mathlib
import Submission.Work.ClassFieldTower.WitnessField

namespace Work.ClassFieldTower

open NumberField

noncomputable section


/-! ## The `ℚ`-basis `{1, sc}` and trace/norm of `x + y·sc`

We compute the trace and the norm of a general element `x + y·sc` of `Kc = ℚ(√-d)`
(`d = 30030`) from the `ℚ`-basis `{1, sc}` of `Kc`: the matrix of left multiplication
by `x + y·sc` in this basis is `[[x, -d y], [y, x]]`, with trace `2x` and determinant
`x² + d y²`.
-/

lemma linearIndependent_pair_one_sc : LinearIndependent ℚ ![1, sc] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have ht : t = 0 := by
    by_contra ht
    have h1 : algebraMap ℚ Kc t * sc = -(algebraMap ℚ Kc s) := by
      have h2 : algebraMap ℚ Kc s + algebraMap ℚ Kc t * sc = 0 := by
        simpa [Algebra.smul_def] using h
      linear_combination h2
    have ht' : (algebraMap ℚ Kc t) ≠ 0 :=
      fun hz => ht ((algebraMap ℚ Kc).injective (by rw [hz, map_zero]))
    have h4 : sc = -(algebraMap ℚ Kc s) / (algebraMap ℚ Kc t) := by
      rw [eq_div_iff ht', mul_comm]; exact h1
    have h3 : sc = algebraMap ℚ Kc (-(s / t)) := by
      rw [h4, map_neg, map_div₀, neg_div]
    exact sc_not_rat (-(s / t)) h3
  subst ht
  constructor
  · have h2 : algebraMap ℚ Kc s = 0 := by simpa [Algebra.smul_def] using h
    exact (algebraMap ℚ Kc).injective (by rw [h2, map_zero])
  · rfl

lemma span_pair_one_sc : ⊤ ≤ Submodule.span ℚ (Set.range ![1, sc]) := by
  intro z _
  obtain ⟨x, y, hxy⟩ := exists_coords z
  rw [hxy]
  have h1 : (1 : Kc) ∈ Submodule.span ℚ (Set.range ![1, sc]) :=
    Submodule.subset_span (Set.mem_range_self (0 : Fin 2))
  have h2 : sc ∈ Submodule.span ℚ (Set.range ![1, sc]) :=
    Submodule.subset_span (Set.mem_range_self (1 : Fin 2))
  have h3 : algebraMap ℚ Kc x + algebraMap ℚ Kc y * sc = x • (1 : Kc) + y • sc := by
    rw [Algebra.smul_def, Algebra.smul_def, mul_one]
  rw [h3]
  exact Submodule.add_mem _ (Submodule.smul_mem _ x h1) (Submodule.smul_mem _ y h2)

/-- The pair `(1, sc)` as a `ℚ`-basis of `Kc`. -/
noncomputable def basisPair : Module.Basis (Fin 2) ℚ Kc :=
  Module.Basis.mk (v := ![1, sc]) linearIndependent_pair_one_sc span_pair_one_sc

lemma basisPair_zero : basisPair 0 = (1 : Kc) := by
  rw [basisPair, Module.Basis.mk_apply]; rfl

lemma basisPair_one : basisPair 1 = sc := by
  rw [basisPair, Module.Basis.mk_apply]; rfl

lemma basisPair_repr (a b : ℚ) :
    basisPair.repr (algebraMap ℚ Kc a + algebraMap ℚ Kc b * sc) = ![a, b] := by
  have h : algebraMap ℚ Kc a + algebraMap ℚ Kc b * sc = ∑ i, ![a, b] i • basisPair i := by
    rw [Fin.sum_univ_two, basisPair_zero, basisPair_one]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Algebra.smul_def, Algebra.smul_def, mul_one]
  rw [h, Module.Basis.repr_sum_self]

lemma basisPair_mul_sc (a b : ℚ) :
    (algebraMap ℚ Kc a + algebraMap ℚ Kc b * sc) * sc
      = algebraMap ℚ Kc (-((dWit : ℚ) * b)) + algebraMap ℚ Kc a * sc := by
  have h : algebraMap ℚ Kc b * sc * sc = algebraMap ℚ Kc (-((dWit : ℚ) * b)) := by
    rw [mul_assoc, sc_sq, ← map_mul]
    congr 1
    simp only [aWit]
    ring
  calc (algebraMap ℚ Kc a + algebraMap ℚ Kc b * sc) * sc
      = algebraMap ℚ Kc a * sc + algebraMap ℚ Kc b * sc * sc := by ring
    _ = algebraMap ℚ Kc a * sc + algebraMap ℚ Kc (-((dWit : ℚ) * b)) := by rw [h]
    _ = algebraMap ℚ Kc (-((dWit : ℚ) * b)) + algebraMap ℚ Kc a * sc := by ring

lemma basisPair_leftMulMatrix_00 (a b : ℚ) :
    Algebra.leftMulMatrix basisPair (algebraMap ℚ Kc a + algebraMap ℚ Kc b * sc) 0 0 = a := by
  rw [Algebra.leftMulMatrix_eq_repr_mul, basisPair_zero, mul_one, basisPair_repr]
  rfl

lemma basisPair_leftMulMatrix_01 (a b : ℚ) :
    Algebra.leftMulMatrix basisPair (algebraMap ℚ Kc a + algebraMap ℚ Kc b * sc) 0 1
      = -((dWit : ℚ) * b) := by
  rw [Algebra.leftMulMatrix_eq_repr_mul, basisPair_one, basisPair_mul_sc, basisPair_repr]
  rfl

lemma basisPair_leftMulMatrix_10 (a b : ℚ) :
    Algebra.leftMulMatrix basisPair (algebraMap ℚ Kc a + algebraMap ℚ Kc b * sc) 1 0 = b := by
  rw [Algebra.leftMulMatrix_eq_repr_mul, basisPair_zero, mul_one, basisPair_repr]
  rfl

lemma basisPair_leftMulMatrix_11 (a b : ℚ) :
    Algebra.leftMulMatrix basisPair (algebraMap ℚ Kc a + algebraMap ℚ Kc b * sc) 1 1 = a := by
  rw [Algebra.leftMulMatrix_eq_repr_mul, basisPair_one, basisPair_mul_sc, basisPair_repr]
  rfl

/-- The matrix of multiplication by `x + y·sc` in the basis `{1, sc}`. -/
lemma basisPair_leftMulMatrix (a b : ℚ) :
    Algebra.leftMulMatrix basisPair (algebraMap ℚ Kc a + algebraMap ℚ Kc b * sc)
      = !![a, -((dWit : ℚ) * b); b, a] := by
  rw [Matrix.eta_fin_two (Algebra.leftMulMatrix basisPair
        (algebraMap ℚ Kc a + algebraMap ℚ Kc b * sc)),
      basisPair_leftMulMatrix_00 a b, basisPair_leftMulMatrix_01 a b, basisPair_leftMulMatrix_10 a b, basisPair_leftMulMatrix_11 a b]

/-- The trace of `x + y·sc` is `2x`. -/
lemma basisPair_trace (a b : ℚ) :
    Algebra.trace ℚ Kc (algebraMap ℚ Kc a + algebraMap ℚ Kc b * sc) = 2 * a := by
  rw [Algebra.trace_eq_matrix_trace basisPair, basisPair_leftMulMatrix, Matrix.trace_fin_two_of]
  ring

/-- The norm of `x + y·sc` is `x² + d y²`. -/
lemma basisPair_norm (a b : ℚ) :
    Algebra.norm ℚ (algebraMap ℚ Kc a + algebraMap ℚ Kc b * sc)
      = a ^ 2 + (dWit : ℚ) * b ^ 2 := by
  rw [Algebra.norm_eq_matrix_det basisPair, basisPair_leftMulMatrix, Matrix.det_fin_two_of]
  ring

/-! ## The arithmetic of `d = 30030` -/

lemma dWit_squarefree_nat : Squarefree (dWit : ℕ) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro x hx hd
  have h1 : x * x ≤ (dWit : ℕ) := Nat.le_of_dvd (by norm_num [dWit]) hd
  have h2 : x ≤ 173 := by
    have : (dWit : ℕ) = 30030 := rfl
    nlinarith [h1]
  interval_cases x <;> norm_num at hx <;> norm_num at hd

lemma dWit_squarefree_int : Squarefree (dWit : ℤ) := by
  have h : Squarefree ((dWit : ℕ) : ℤ) := by
    rw [Int.squarefree_natCast]; exact dWit_squarefree_nat
  simpa using h

/-- In `ZMod 4`, `p² + 2q² = 0` forces `p² = q² = 0`. -/
lemma zmod4_sq_add_two_sq (p q : ZMod 4) (h : p ^ 2 + 2 * q ^ 2 = 0) :
    p ^ 2 = 0 ∧ q ^ 2 = 0 := by
  revert p q
  decide

/-- **Parity step.** If `4 ∣ u² + d·v²` with `d = 30030 ≡ 2 (mod 4)`, then `u` and `v` are even. -/
lemma even_of_four_dvd_sq_add_dWit_sq {u v : ℤ} (h : (4 : ℤ) ∣ u ^ 2 + (dWit : ℤ) * v ^ 2) :
    Even u ∧ Even v := by
  obtain ⟨k, hk⟩ := h
  have hz : ((u : ZMod 4)) ^ 2 + 2 * ((v : ZMod 4)) ^ 2 = 0 := by
    have hc := congrArg (fun n : ℤ => (n : ZMod 4)) hk
    push_cast at hc
    have h4 : (4 : ZMod 4) = 0 := by decide
    have h30 : (30030 : ZMod 4) = 2 := by decide
    rw [h4, h30] at hc
    simpa using hc
  have key := zmod4_sq_add_two_sq (u : ZMod 4) (v : ZMod 4) hz
  have keyu : (4 : ℤ) ∣ u ^ 2 := by
    have h4 : ((u ^ 2 : ℤ) : ZMod 4) = 0 := by
      push_cast
      exact key.1
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (u ^ 2) 4).mp h4
  have keyv : (4 : ℤ) ∣ v ^ 2 := by
    have h4 : ((v ^ 2 : ℤ) : ZMod 4) = 0 := by
      push_cast
      exact key.2
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (v ^ 2) 4).mp h4
  constructor
  · have h2 : (2 : ℤ) ∣ u ^ 2 := dvd_trans (by norm_num : (2 : ℤ) ∣ 4) keyu
    exact even_iff_two_dvd.mpr (Int.prime_two.dvd_of_dvd_pow h2)
  · have h2 : (2 : ℤ) ∣ v ^ 2 := dvd_trans (by norm_num : (2 : ℤ) ∣ 4) keyv
    exact even_iff_two_dvd.mpr (Int.prime_two.dvd_of_dvd_pow h2)

/-- **`𝓞 ℚ(√-d) = ℤ[√-d]` and the norm form.**

Hints for the proof. `Work.ClassFieldTower.exists_coords` gives, for every `z : Kc`, rationals
`x y` with `z = x + y * sc`. For `z` in the ring of integers one shows `2x ∈ ℤ` and
`x² + d y² ∈ ℤ` (the trace and the norm of an integral element are integral, and `ℚ ∩ 𝓞 Kc = ℤ`;
`Algebra.isIntegral_trace`/`isIntegral_norm` are in Mathlib), then the parity argument
(`u := 2x`, `v := 2y` satisfy `u² + d v² ≡ 0 mod 4` with `d ≡ 2 mod 4`, which forces `u, v` even)
gives `x y ∈ ℤ`.

For the norm formula: `{1, scR}` is a `ℤ`-basis of `𝓞 Kc` (spanning by the coordinate statement;
independent because `sc ∉ ℚ`, use `sc_not_rat`) and `Algebra.norm_eq_matrix_det` computes the norm
as the determinant of `Algebra.leftMulMatrix` of the multiplication by `z`; the matrix of
multiplication by `x + y·sc` in the basis `(1, sc)` is `[[x, -d y], [y, x]]` with determinant
`x² + d y²` (use `scR_sq : scR * scR = -(30030 : 𝓞 Kc)`). -/
theorem int_coords_and_norm (z : NumberField.RingOfIntegers Work.ClassFieldTower.Kc) :
    ∃ x y : ℤ, (z : Work.ClassFieldTower.Kc) = (x : Work.ClassFieldTower.Kc)
        + (y : Work.ClassFieldTower.Kc) * Work.ClassFieldTower.sc ∧
      Algebra.norm ℤ z = x ^ 2 + (Work.ClassFieldTower.dWit : ℤ) * y ^ 2 := by
  obtain ⟨a, b, hab⟩ := exists_coords (z : Kc)
  -- ### The trace and the norm of `z` are the integers `2a` and `a² + d b²`
  have hA : ∃ n : ℤ, (n : ℚ) = a ^ 2 + (dWit : ℚ) * b ^ 2 :=
    ⟨Algebra.norm ℤ z, by rw [Algebra.coe_norm_int, hab]; exact basisPair_norm a b⟩
  obtain ⟨A, hA⟩ := hA
  have hu : ∃ n : ℤ, (n : ℚ) = 2 * a :=
    ⟨Algebra.trace ℤ (𝓞 Kc) z, by rw [Algebra.coe_trace_int, hab]; exact basisPair_trace a b⟩
  obtain ⟨u, hu⟩ := hu
  -- ### `2b ∈ ℤ`
  have hv : ∃ v : ℤ, (v : ℚ) = 2 * b := by
    have hdv : (4 * (A : ℚ) - (u : ℚ) ^ 2) = (dWit : ℚ) * (2 * b) ^ 2 := by
      have h0 : ((4 * A - u ^ 2 : ℤ) : ℚ) = (dWit : ℚ) * (2 * b) ^ 2 := by
        rw [Int.cast_sub, Int.cast_mul, Int.cast_pow, hA, hu]; ring
      rw [← h0]
      push_cast
      ring
    have hint : IsIntegral ℤ ((dWit : ℚ) * (2 * b)) := by
      refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
      have hsq : ((dWit : ℚ) * (2 * b)) ^ 2 = (((dWit : ℤ) * (4 * A - u ^ 2) : ℤ) : ℚ) := by
        have h1 : ((dWit : ℚ) * (2 * b)) ^ 2 = (dWit : ℚ) * ((dWit : ℚ) * (2 * b) ^ 2) := by ring
        rw [h1, ← hdv]
        push_cast
        ring
      rw [hsq]
      exact isIntegral_algebraMap
    obtain ⟨m, hm⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hint
    have hmc : ((m : ℤ) : ℚ) = (dWit : ℚ) * (2 * b) := by simpa using hm
    have hm2 : m ^ 2 = (dWit : ℤ) * (4 * A - u ^ 2) := by
      apply Int.cast_injective (α := ℚ)
      push_cast
      rw [hmc, hdv]
      ring
    obtain ⟨c, hc⟩ := (Squarefree.dvd_pow_iff_dvd dWit_squarefree_int
      (by norm_num : (2 : ℕ) ≠ 0)).mp ⟨4 * A - u ^ 2, hm2⟩
    refine ⟨c, ?_⟩
    have hm' : ((m : ℤ) : ℚ) = (dWit : ℚ) * (c : ℚ) := by
      rw [hc]
      push_cast
      ring
    have h2 : (dWit : ℚ) * (c : ℚ) = (dWit : ℚ) * (2 * b) := by rw [← hm', hmc]
    exact mul_left_cancel₀ (by norm_num [dWit] : (dWit : ℚ) ≠ 0) h2
  obtain ⟨v, hv⟩ := hv
  -- ### Parity
  have h4A : 4 * A = u ^ 2 + (dWit : ℤ) * v ^ 2 := by
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [hA, hu, hv]
    ring
  have hEven : Even u ∧ Even v := even_of_four_dvd_sq_add_dWit_sq ⟨A, h4A.symm⟩
  obtain ⟨x, hx⟩ : ∃ x : ℤ, u = 2 * x := by
    obtain ⟨k, hk⟩ := hEven.1
    exact ⟨k, by omega⟩
  obtain ⟨y, hy⟩ : ∃ y : ℤ, v = 2 * y := by
    obtain ⟨k, hk⟩ := hEven.2
    exact ⟨k, by omega⟩
  have hxq : ((x : ℤ) : ℚ) = a := by
    have h : ((2 * x : ℤ) : ℚ) = (2 : ℚ) * a := by rw [← hx]; exact hu
    push_cast at h
    linarith
  have hyq : ((y : ℤ) : ℚ) = b := by
    have h : ((2 * y : ℤ) : ℚ) = (2 : ℚ) * b := by rw [← hy]; exact hv
    push_cast at h
    linarith
  refine ⟨x, y, ?_, ?_⟩
  · rw [hab]
    rw [show (x : Kc) = algebraMap ℚ Kc ((x : ℤ) : ℚ) from rfl,
      show (y : Kc) = algebraMap ℚ Kc ((y : ℤ) : ℚ) from rfl, hxq, hyq]
  · apply Int.cast_injective (α := ℚ)
    push_cast
    rw [Algebra.coe_norm_int, hab, basisPair_norm, ← hxq, ← hyq]
    norm_num

end

end Work.ClassFieldTower
