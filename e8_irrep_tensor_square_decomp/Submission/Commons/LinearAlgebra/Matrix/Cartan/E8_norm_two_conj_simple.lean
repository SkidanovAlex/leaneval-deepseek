import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.FiniteType
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_diag_offdiag_symm
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_posDef
import Submission.Commons.LinearAlgebra.Matrix.Cartan.reflect_involutive
import Submission.Commons.LinearAlgebra.Matrix.Cartan.reflect_dotProduct_inv

/-!
# Roots of `E₈` of squared length two are Weyl-conjugate to simple roots

The main result `Commons.LinearAlgebra.Matrix.Cartan.E8_norm_two_conj_simple` proves that every
vector `μ : Fin 8 → ℤ` of squared length `2` for the form `⟪μ,ν⟫ = μ ⬝ A⁻¹ ν` (`A = E₈` Cartan
matrix) can be brought to a simple root `α_k = (fun i => A k i)` by a sequence of simple
reflections `(sᵢ μ)ⱼ = μⱼ - μᵢ A_{ij}`.

The proof strategy is the standard "reflect into the dominant chamber" one, but the termination
measure is the **height** `h(μ) = ∑ᵢ (A⁻¹ μ)ᵢ`, which strictly increases under a reflection at a
negative coordinate (`sᵢ μ = μ - μᵢ αᵢ` drops the `i`-th coordinate of `A⁻¹μ`).  The height is
bounded because the squared length is invariant under the reflections and `A x ⬝ x ≤ 2` forces
`|μᵢ| ≤ 2` (here `A` is positive definite, `Commons.LinearAlgebra.Matrix.Cartan.E8_posDef`, and
`μ = A x`).  The dominant vectors of squared length `2` are then easily classified: they are the
`0/1`-vectors whose support is a single node `i` with `(A⁻¹)_{ii} = 2`, i.e. the highest root
`θ = ω₈`.  Finally `θ` is explicitly conjugated to the simple root `α₇` by a fixed word.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

namespace Commons.LinearAlgebra.Matrix.Cartan

namespace E8NormTwo

/-- The `E₈` Cartan matrix. -/
abbrev E8 : Matrix (Fin 8) (Fin 8) ℤ := CartanMatrix.E₈

/-- The `E₈` Cartan matrix over `ℚ`. -/
abbrev E8q : Matrix (Fin 8) (Fin 8) ℚ := CartanMatrix.E₈.map (Int.castRingHom ℚ)

/-- The inverse of the `E₈` Cartan matrix (integral, since `det E₈ = 1`). -/
def E8inv : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 4,  5,  7, 10,  8,  6,  4, 2;
      5,  8, 10, 15, 12,  9,  6, 3;
      7, 10, 14, 20, 16, 12,  8, 4;
     10, 15, 20, 30, 24, 18, 12, 6;
      8, 12, 16, 24, 20, 15, 10, 5;
      6,  9, 12, 18, 15, 12,  8, 4;
      4,  6,  8, 12, 10,  8,  6, 3;
      2,  3,  4,  6,  5,  4,  3, 2]

/-- The integral squared length `μ ⬝ A⁻¹ μ`. -/
def qZ (v : Fin 8 → ℤ) : ℤ := ∑ i, ∑ j, v i * E8inv i j * v j

/-- The squared length as it appears in the statement, `μ ⬝ A⁻¹ μ` over `ℚ`. -/
noncomputable def e8q (v : Fin 8 → ℤ) : ℚ := ∑ i, ∑ j, (v i : ℚ) * (E8q)⁻¹ i j * (v j : ℚ)

/-- The simple reflection at the node `i`, `(sᵢ v)ⱼ = vⱼ - vᵢ A_{ij}`. -/
def e8refl (v : Fin 8 → ℤ) (i : Fin 8) : Fin 8 → ℤ := fun j => v j - v i * E8 i j

/-- The height `h(v) = ∑ᵢ (A⁻¹ v)ᵢ`, i.e. the sum of the coefficients of `v` in the simple root
basis. -/
def e8ht (v : Fin 8 → ℤ) : ℤ := ∑ i, ∑ j, E8inv i j * v j

/-- The highest root `θ = ω₈` in `ω`-coordinates. -/
def e8th : Fin 8 → ℤ := fun i => if i = 7 then 1 else 0

/-- The bilinear form of the Cartan matrix. -/
def form2 (x y : Fin 8 → ℚ) : ℚ := ∑ i, ∑ j, x i * (E8 i j : ℚ) * y j

/-- `A⁻¹ v` for an integral weight `v`, as a rational vector. -/
def xc (v : Fin 8 → ℤ) : Fin 8 → ℚ := fun i => ∑ k, (E8inv i k : ℚ) * (v k : ℚ)

/-! ## Elementary entries of `E₈` and `E₈⁻¹` -/

lemma E8_symm (i j : Fin 8) : E8 i j = E8 j i := E8_diag_offdiag_symm.1 i j

lemma E8inv_nonneg (i j : Fin 8) : 0 ≤ E8inv i j := by
  fin_cases i <;> fin_cases j <;> norm_num [E8inv]

lemma E8inv_diag_ge_two (i : Fin 8) : 2 ≤ E8inv i i := by
  fin_cases i <;> norm_num [E8inv]

lemma E8inv_diag_eq (i : Fin 8) : E8inv i i = 2 → i = 7 := by
  fin_cases i <;> simp [E8inv]

lemma E8inv_mul_E8 : E8inv * E8 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [E8inv, E8, CartanMatrix.E₈, CartanMatrix.E_eight_eq, Matrix.mul_apply, Fin.sum_univ_eight] <;> norm_num)

lemma E8q_mul_E8inv : E8q * (E8inv.map (Int.castRingHom ℚ)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [E8inv, E8q, CartanMatrix.E₈, CartanMatrix.E_eight_eq, Matrix.mul_apply, Fin.sum_univ_eight] <;> norm_num)

lemma E8q_inv : (E8q)⁻¹ = E8inv.map (Int.castRingHom ℚ) := by
  refine Matrix.inv_eq_left_inv ?_
  rw [mul_eq_one_comm]
  exact E8q_mul_E8inv

lemma e8q_eq_qZ (v : Fin 8 → ℤ) : e8q v = (qZ v : ℚ) := by
  rw [e8q, qZ, E8q_inv]
  push_cast
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  simp only [Matrix.map_apply, Int.coe_castRingHom]

lemma qZ_eq_two_of_e8q {v : Fin 8 → ℤ} (h : e8q v = 2) : qZ v = 2 := by
  rw [e8q_eq_qZ] at h
  exact_mod_cast h

/-! ## The reflection: invariance of the form and the height formula -/

lemma qZ_refl (v : Fin 8 → ℤ) (i : Fin 8) : qZ (e8refl v i) = qZ v := by
  fin_cases i <;>
    (simp [qZ, e8refl, E8inv, E8, CartanMatrix.E₈, CartanMatrix.E_eight_eq, Fin.sum_univ_eight] <;> ring)

lemma e8ht_refl (v : Fin 8 → ℤ) (i : Fin 8) : e8ht (e8refl v i) = e8ht v - v i := by
  fin_cases i <;>
    (simp [e8ht, e8refl, E8inv, E8, CartanMatrix.E₈, CartanMatrix.E_eight_eq, Fin.sum_univ_eight] <;> ring)

/-! ## The positive Cartan form and the bound `|μᵢ| ≤ 2` -/

lemma form2_bilin (x y : Fin 8 → ℚ) (t : ℚ) :
    form2 (x - t • y) (x - t • y) = form2 x x - 2 * t * form2 x y + t^2 * form2 y y := by
  simp [form2, Fin.sum_univ_eight, E8, CartanMatrix.E₈, CartanMatrix.E_eight_eq]
  ring

lemma form2_nonneg (x : Fin 8 → ℚ) : 0 ≤ form2 x x := by
  by_cases hx : x = 0
  · subst hx; simp [form2]
  · exact le_of_lt (E8_posDef x hx)

lemma form2_single (x : Fin 8 → ℚ) (j : Fin 8) :
    form2 x (Pi.single j (1 : ℚ)) = (E8q.mulVec x) j := by
  fin_cases j <;>
    (simp [form2, E8q, E8, CartanMatrix.E₈, CartanMatrix.E_eight_eq, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_eight] <;>
      ring)

lemma form2_single_self (j : Fin 8) :
    form2 (Pi.single j (1 : ℚ)) (Pi.single j (1 : ℚ)) = 2 := by
  fin_cases j <;> simp [form2, E8, CartanMatrix.E₈, CartanMatrix.E_eight_eq, Fin.sum_univ_eight]

lemma E8q_mul_xc (v : Fin 8 → ℤ) : E8q.mulVec (xc v) = fun j => (v j : ℚ) := by
  have hx : xc v = (E8inv.map (Int.castRingHom ℚ)).mulVec (fun k => (v k : ℚ)) := by
    funext i
    rw [Matrix.mulVec_apply_eq_sum]
    simp [xc, Matrix.map_apply, Int.coe_castRingHom]
  rw [hx, Matrix.mulVec_mulVec, E8q_mul_E8inv, Matrix.one_mulVec]

lemma form2_xc_self (v : Fin 8 → ℤ) : form2 (xc v) (xc v) = (qZ v : ℚ) := by
  simp [form2, qZ, xc, E8, E8inv, CartanMatrix.E₈, CartanMatrix.E_eight_eq, Fin.sum_univ_eight]
  ring

/-- Every vector of squared length `2` has all `ω`-coordinates bounded by `2` in absolute value. -/
lemma sq_le_four (v : Fin 8 → ℤ) (hv : qZ v = 2) (j : Fin 8) : (v j)^2 ≤ 4 := by
  have hcf : form2 (xc v) (xc v) = 2 := by rw [form2_xc_self, hv]; norm_num
  have hAx : form2 (xc v) (Pi.single j (1 : ℚ)) = (v j : ℚ) := by
    rw [form2_single, E8q_mul_xc]
  have hpsd : 0 ≤ form2 (xc v - ((v j : ℚ)/2) • Pi.single j (1 : ℚ))
      (xc v - ((v j : ℚ)/2) • Pi.single j (1 : ℚ)) := form2_nonneg _
  rw [form2_bilin, hcf, hAx, form2_single_self] at hpsd
  have hvj : ((v j : ℤ) : ℚ)^2 ≤ 4 := by nlinarith [hpsd]
  exact_mod_cast hvj

/-- The height of a vector of squared length `2` is at most `1240`. -/
lemma e8ht_le (v : Fin 8 → ℤ) (hv : qZ v = 2) : e8ht v ≤ 1240 := by
  have h2 : ∀ j : Fin 8, v j ≤ 2 := by
    intro j
    have := sq_le_four v hv j
    nlinarith [this]
  rw [e8ht]
  calc ∑ i, ∑ j, E8inv i j * v j ≤ ∑ i, ∑ j, E8inv i j * 2 := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        exact mul_le_mul_of_nonneg_left (h2 j) (E8inv_nonneg i j)
    _ = 1240 := by decide

/-! ## The dominant vectors of squared length `2` -/

lemma diag_le_qZ (v : Fin 8 → ℤ) (hd : ∀ i, 0 ≤ v i) :
    (∑ i, E8inv i i * (v i)^2) ≤ qZ v := by
  rw [qZ]
  apply Finset.sum_le_sum; intro i _
  have hsingle := Finset.single_le_sum (s := Finset.univ)
    (f := fun j => E8inv i j * v i * v j)
    (fun j _ => mul_nonneg (mul_nonneg (E8inv_nonneg i j) (hd i)) (hd j)) (Finset.mem_univ i)
  calc E8inv i i * (v i)^2 = E8inv i i * v i * v i := by ring
    _ ≤ ∑ j ∈ Finset.univ, E8inv i j * v i * v j := hsingle
    _ = ∑ j, v i * E8inv i j * v j := by
        apply Finset.sum_congr rfl; intro j _; ring

/-- A dominant vector of squared length `2` is the highest root `θ = ω₈`. -/
lemma dominant_eq_th (v : Fin 8 → ℤ) (hd : ∀ i, 0 ≤ v i) (hv : qZ v = 2) : v = e8th := by
  have hsum : (∑ i, E8inv i i * (v i)^2) ≤ 2 := by
    rw [← hv]; exact diag_le_qZ v hd
  have hterm : ∀ i, 0 ≤ E8inv i i * (v i)^2 := fun i =>
    mul_nonneg (le_trans (by norm_num) (E8inv_diag_ge_two i)) (sq_nonneg _)
  have hsingle : ∀ i, E8inv i i * (v i)^2 ≤ 2 := fun i =>
    (Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ i)).trans hsum
  have hsq1 : ∀ i, (v i)^2 ≤ 1 := by
    intro i
    have := E8inv_diag_ge_two i
    nlinarith [hsingle i]
  have hv01 : ∀ i, v i = 0 ∨ v i = 1 := by
    intro i
    have h1 : v i ≤ 1 := by nlinarith [hsq1 i]
    have h0 := hd i
    omega
  have hex : ∃ i, v i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hz : qZ v = 0 := by simp [qZ, hcon]
    omega
  obtain ⟨i0, hi0⟩ := hex
  have hother : ∀ j, j ≠ i0 → v j = 0 := by
    intro j hj
    rcases hv01 j with h | h
    · exact h
    · exfalso
      have hsub : ({i0, j} : Finset (Fin 8)) ⊆ Finset.univ := Finset.subset_univ _
      have hpair := (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun k _ _ => hterm k)).trans hsum
      rw [Finset.sum_insert (by simpa [eq_comm] using hj), Finset.sum_singleton] at hpair
      have hvi0 : (1 : ℤ) ≤ v i0 := by
        have := hd i0; omega
      have hj1 : (1 : ℤ) ≤ v j := by omega
      have h1 := E8inv_diag_ge_two i0
      have h2 := E8inv_diag_ge_two j
      nlinarith [hpair, h1, h2, hvi0, hj1]
  have hvi0 : v i0 = 1 := by
    rcases hv01 i0 with h | h
    · exact absurd h hi0
    · exact h
  have hq : qZ v = E8inv i0 i0 := by
    rw [qZ]
    rw [Finset.sum_eq_single i0]
    · rw [Finset.sum_eq_single i0]
      · simp [hvi0]
      · intro j _ hj; simp [hother j hj]
      · intro h; exact absurd (Finset.mem_univ i0) h
    · intro i _ hi; simp [hother i hi]
    · intro h; exact absurd (Finset.mem_univ i0) h
  have hi07 : i0 = 7 := by
    refine E8inv_diag_eq i0 ?_
    rw [← hq]; exact hv
  funext i
  by_cases hi : i = 7
  · subst hi; rw [hi07] at hvi0; simpa [e8th] using hvi0
  · have hii0 : i ≠ i0 := by rintro rfl; exact hi hi07
    rw [hother i hii0, e8th]; simp [hi]

/-! ## An explicit word taking the highest root to a simple root -/

/-- The word of simple reflections, applied to `θ = ω₈`, produces the simple root `α₇`. -/
def thetaWord : List (Fin 8) :=
  [7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6]

lemma thetaWord_spec : thetaWord.foldl e8refl e8th = fun i => E8 7 i := by decide

/-! ## Termination and the main induction -/

lemma int_toNat_lt {a b : ℤ} (ha : 0 ≤ a) (h : a < b) : a.toNat < b.toNat := by
  have hb : 0 ≤ b := le_of_lt (lt_of_le_of_lt ha h)
  have h1 : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha
  have h2 : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb
  omega

/-- The main inductive statement: any vector of squared length `2` can be brought to a simple
root by a sequence of simple reflections. -/
theorem reduce_exists (v : Fin 8 → ℤ) (hv : qZ v = 2) :
    ∃ (L : List (Fin 8)) (k : Fin 8), L.foldl e8refl v = fun i => E8 k i := by
  suffices H : ∀ n, ∀ v : Fin 8 → ℤ, (1240 - e8ht v).toNat = n → qZ v = 2 →
      ∃ (L : List (Fin 8)) (k : Fin 8), L.foldl e8refl v = fun i => E8 k i by
    exact H _ v rfl hv
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hn hv
    by_cases hd : ∀ i, 0 ≤ v i
    · refine ⟨thetaWord, 7, ?_⟩
      rw [dominant_eq_th v hd hv]
      exact thetaWord_spec
    · push Not at hd
      obtain ⟨i, hi⟩ := hd
      have hbound := e8ht_le v hv
      have hbound' := e8ht_le (e8refl v i) (by rw [qZ_refl]; exact hv)
      have hlt : (1240 - e8ht (e8refl v i)).toNat < n := by
        rw [← hn]
        apply int_toNat_lt
        · omega
        · rw [e8ht_refl]; omega
      obtain ⟨L, k, hL⟩ := ih _ hlt (e8refl v i) rfl (by rw [qZ_refl]; exact hv)
      exact ⟨i :: L, k, by simpa [List.foldl_cons] using hL⟩

end E8NormTwo

open E8NormTwo

/-- Every nonzero vector of squared length `2` for the `E₈` form `⟪μ,ν⟫ = μ ⬝ A⁻¹ ν`
(`A = CartanMatrix.E₈`) is Weyl-conjugate to a **simple root**, where the simple reflections act on
weights by `(sᵢ μ)ⱼ = μⱼ - μᵢ A i j` (this is the action in the `ω`-basis: `sᵢμ = μ - ⟨μ,αᵢ∨⟩ αᵢ`).

Equivalently: the vectors of squared length `2` form the root system of type `E₈`, on which the
Weyl group acts transitively.  A concrete route: the roots in the standard realisation are the `240`
vectors given by the project's root-system data (or by `±2εᵢ±2εⱼ` and the even-sign `(±1,…,±1)` in
doubled coordinates); every such vector can be brought to a simple root by the "reflect into the
dominant chamber / reduce the height" algorithm, using
`Commons.LinearAlgebra.Matrix.Cartan.reflect_involutive` and the finite root system data. -/
theorem E8_norm_two_conj_simple (μ : Fin 8 → ℤ)
    (h : (∑ i, ∑ j, (μ i : ℚ) * ((CartanMatrix.E₈.map (Int.castRingHom ℚ))⁻¹) i j * (μ j : ℚ)) = 2) :
    ∃ (L : List (Fin 8)) (k : Fin 8),
      L.foldl (fun v i => fun j => v j - v i * CartanMatrix.E₈ i j) μ
        = (fun i => CartanMatrix.E₈ k i) := by
  obtain ⟨L, k, hL⟩ := E8NormTwo.reduce_exists μ (E8NormTwo.qZ_eq_two_of_e8q h)
  exact ⟨L, k, hL⟩

end Commons.LinearAlgebra.Matrix.Cartan