/-
Copyright: work module for the Elgindi finite-time singularity project.

# The eigenpolynomials `p_n` span the odd polynomials

`EigBasis.lean` defines the eigenpolynomials of the angular operator `L₀` as

  `eigPoly n u = p_n(u) = Σ_{k<n} c_k u^{2k+1}`,  `c_k = eigCoef n k`,
  `c_{k+1}/c_k = (4k²+10k-λ_n)/((2k+3)(2k+2))`,  `c_0 = 1`,

with `λ_n = 4(n-1)²+10(n-1)`.  Since

  `4k²+10k-λ_n = (k-(n-1))·(4(k+(n-1))+10)`,

each factor of the product giving `c_k` is nonzero as long as `k ≤ n-1`; in particular the
*top* coefficient `eigCoef n (n-1)` of `p_n` does not vanish, so `p_n` has degree exactly
`2n-1`.  Hence `p_1, p_2, …, p_{m+1}` are a triangular family of odd polynomials of degrees
`1, 3, …, 2m+1` and every odd monomial is a finite linear combination of them:

  `u^{2m+1} = Σ_{k ≤ m} a_k · p_{k+1}(u)`.

This is the "odd polynomials are spanned by the eigenpolynomials" fact used to expand the
odd functions of the angular variable in the eigenbasis of `L₀` (see `LevelOne.lean`,
`eigFun_span_dense.lean`).

The proof is a triangular induction: the top term of `p_{m+2}` is the leading coefficient
`c = eigCoef (m+2) (m+1) ≠ 0`, and the lower terms `u^{2k+1}`, `k ≤ m`, are already known
to be combinations of `p_1, …, p_{k+1}` by the induction hypothesis.  The span statements are
packaged in the local predicate `OddSpan`.
-/
import Mathlib.Analysis.Normed.Field.Basic
import Submission.Work.FTS.EllipticEst.LevelOneAsm.EigBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.EllipticEst.LevelOneAsm

set_option autoImplicit false

/-! ### The leading coefficient of the eigenpolynomial -/

/-- `eigCoef (n+1) k = c_k` is nonzero for all `k ≤ n`: by the recurrence,
`c_k = ∏_{j<k} (4j²+10j-λ_{n+1})/((2j+3)(2j+2))` and, for `j < n`,
`4j²+10j-λ_{n+1} = (j-n)·(4(j+n)+10) ≠ 0`. -/
lemma eigCoef_ne_zero : ∀ (a k : ℕ), k ≤ a → eigCoef (a + 1) k ≠ 0 := by
  intro a k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have hk' : k ≤ a := by omega
      rw [show eigCoef (a+1) (k+1) = eigCoef (a+1) k *
          ((4*(k:ℝ)^2 + 10*(k:ℝ) - eigLam (a+1)) / ((2*(k:ℝ)+3)*(2*(k:ℝ)+2)))
          from by simp [eigCoef]]
      refine mul_ne_zero (ih hk') (div_ne_zero ?_ ?_)
      · have hnum : (4*(k:ℝ)^2 + 10*(k:ℝ) - eigLam (a+1)) =
            ((k:ℝ) - (a:ℝ)) * (4*((k:ℝ)+(a:ℝ)) + 10) := by
          rw [show eigLam (a+1) = 4*(a:ℝ)^2 + 10*(a:ℝ) from by
            rw [eigLam, eigLamNat]; simp only [Nat.add_sub_cancel]; push_cast; ring]
          ring
        rw [hnum]
        refine mul_ne_zero ?_ ?_
        · refine sub_ne_zero.mpr ?_
          have : k ≠ a := by omega
          exact_mod_cast this
        · have h1 : (0:ℝ) ≤ (k:ℝ) := by positivity
          have h2 : (0:ℝ) ≤ (a:ℝ) := by positivity
          linarith
      · have h1 : (0:ℝ) < 2*(k:ℝ)+3 := by positivity
        have h2 : (0:ℝ) < 2*(k:ℝ)+2 := by positivity
        positivity

/-! ### Two elementary facts about `eigPoly` -/

/-- `p_1(u) = u`. -/
lemma eigPoly_one (u : ℝ) : eigPoly 1 u = u := by
  rw [eigPoly, Finset.range_one, Finset.sum_singleton, eigCoef_zero]
  norm_num

/-- The top term of the eigenpolynomial: `p_{m+2}` splits off its leading monomial
`eigCoef (m+2) (m+1) · u^{2(m+1)+1}`. -/
lemma eigPoly_split (m : ℕ) (u : ℝ) :
    eigPoly (m + 2) u = (∑ k ∈ Finset.range (m + 1), eigCoef (m + 2) k * u ^ (2 * k + 1))
      + eigCoef (m + 2) (m + 1) * u ^ (2 * (m + 1) + 1) := by
  rw [eigPoly]
  exact Finset.sum_range_succ (fun k => eigCoef (m + 2) k * u ^ (2 * k + 1)) (m + 1)

/-! ### The span predicate -/

/-- `OddSpan N p` says that the function `p` is a finite linear combination
`Σ_{k<N} a_k · p_{k+1}` of the first `N` eigenpolynomials. -/
def OddSpan (N : ℕ) (p : ℝ → ℝ) : Prop :=
  ∃ a : ℕ → ℝ, ∀ u : ℝ, p u = ∑ k ∈ Finset.range N, a k * eigPoly (k + 1) u

namespace OddSpan

protected lemma zero (N : ℕ) : OddSpan N (fun _ : ℝ => 0) :=
  ⟨fun _ => 0, fun u => by simp⟩

/-- Transport along a pointwise equal function. -/
protected lemma congr {N : ℕ} {p q : ℝ → ℝ} (hp : OddSpan N p) (h : ∀ u : ℝ, q u = p u) :
    OddSpan N q := by
  obtain ⟨a, ha⟩ := hp
  exact ⟨a, fun u => by rw [h u]; exact ha u⟩

protected lemma add {N : ℕ} {p q : ℝ → ℝ} (hp : OddSpan N p) (hq : OddSpan N q) :
    OddSpan N (fun u => p u + q u) := by
  obtain ⟨a, ha⟩ := hp
  obtain ⟨b, hb⟩ := hq
  refine ⟨fun k => a k + b k, fun u => ?_⟩
  show p u + q u = ∑ k ∈ Finset.range N, (a k + b k) * eigPoly (k + 1) u
  rw [ha u, hb u, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => by ring)

protected lemma smul {N : ℕ} {p : ℝ → ℝ} (hp : OddSpan N p) (c : ℝ) :
    OddSpan N (fun u => c * p u) := by
  obtain ⟨a, ha⟩ := hp
  refine ⟨fun k => c * a k, fun u => ?_⟩
  show c * p u = ∑ k ∈ Finset.range N, (c * a k) * eigPoly (k + 1) u
  rw [ha u, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => by ring)

protected lemma sub {N : ℕ} {p q : ℝ → ℝ} (hp : OddSpan N p) (hq : OddSpan N q) :
    OddSpan N (fun u => p u - q u) := by
  have h := hp.add (hq.smul (-1))
  exact h.congr (fun u => by ring)

/-- `OddSpan` is closed under finite sums. -/
protected lemma sum {N : ℕ} {ι : Type*} {s : Finset ι} {f : ι → ℝ → ℝ}
    (h : ∀ i ∈ s, OddSpan N (f i)) : OddSpan N (fun u => ∑ i ∈ s, f i u) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using OddSpan.zero N
  | insert i s hi ih =>
      have h1 : OddSpan N (f i) := h i (Finset.mem_insert_self i s)
      have h2 : OddSpan N (fun u => ∑ j ∈ s, f j u) :=
        ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      refine (h1.add h2).congr (fun u => ?_)
      exact Finset.sum_insert hi

/-- A single eigenpolynomial `p_{k+1}` with `k < N` lies in the span. -/
protected lemma eigPoly {N k : ℕ} (hk : k < N) : OddSpan N (eigPoly (k+1)) := by
  refine ⟨fun j => if j = k then 1 else 0, fun u => ?_⟩
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hjne; simp [hjne]
  · intro hnot; exact absurd (Finset.mem_range.mpr hk) hnot

/-- The span grows with `N`. -/
protected lemma mono {N M : ℕ} (hNM : N ≤ M) {p : ℝ → ℝ} (hp : OddSpan N p) :
    OddSpan M p := by
  obtain ⟨a, ha⟩ := hp
  refine ⟨fun j => if j < N then a j else 0, fun u => ?_⟩
  rw [ha u]
  have h1 : (∑ x ∈ Finset.range N, (if x < N then a x else 0) * eigPoly (x+1) u)
      = ∑ x ∈ Finset.range N, a x * eigPoly (x+1) u := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    simp [Finset.mem_range.mp hx]
  have h2 : (∑ x ∈ Finset.range N, (if x < N then a x else 0) * eigPoly (x+1) u)
      = ∑ x ∈ Finset.range M, (if x < N then a x else 0) * eigPoly (x+1) u := by
    refine Finset.sum_subset (Finset.range_subset_range.mpr hNM) (fun x _ hxN => ?_)
    have hxN' : ¬ (x < N) := by simpa [Finset.mem_range] using hxN
    rw [ite_eq_right hxN', zero_mul]
  rw [← h1, h2]

end OddSpan

/-! ### The triangular induction -/

/-- Every odd monomial `u^{2j+1}` with `j ≤ m` is a combination of `p_1, …, p_{m+1}`. -/
theorem eigPoly_spans_odd_aux (m : ℕ) :
    ∀ j ≤ m, OddSpan (m+1) (fun u : ℝ => u ^ (2*j+1)) := by
  induction m with
  | zero =>
      intro j hj
      obtain rfl : j = 0 := Nat.eq_zero_of_le_zero hj
      refine ⟨fun _ => 1, fun u => ?_⟩
      show u ^ (2*0+1) = ∑ k ∈ Finset.range 1, 1 * eigPoly (k+1) u
      rw [Finset.sum_range_one, eigPoly_one]
      norm_num
  | succ m ih =>
      intro j hj
      rcases Nat.lt_or_eq_of_le hj with hlt | rfl
      · exact (ih j (Nat.lt_succ_iff.mp hlt)).mono (by omega)
      · -- the new monomial `u^{2(m+1)+1}`: solve `p_{m+2}` for its top term
        have hc : eigCoef (m + 2) (m + 1) ≠ 0 := eigCoef_ne_zero (m+1) (m+1) (le_refl _)
        have hA : OddSpan (m+2) (fun u : ℝ => (eigCoef (m + 2) (m + 1))⁻¹ * eigPoly (m+2) u) :=
          (OddSpan.eigPoly (N := m+2) (k := m+1) (by omega)).smul _
        have hB : OddSpan (m+2) (fun u : ℝ => ∑ k ∈ Finset.range (m+1),
            ((eigCoef (m + 2) (m + 1))⁻¹ * eigCoef (m+2) k) * u ^ (2*k+1)) :=
          OddSpan.sum (fun k hk => ((ih k (by have := Finset.mem_range.mp hk; omega)).mono
            (by omega)).smul _)
        have hmain : OddSpan (m+2) (fun u : ℝ =>
            (eigCoef (m + 2) (m + 1))⁻¹ * eigPoly (m + 2) u
              - ∑ k ∈ Finset.range (m + 1),
                  ((eigCoef (m + 2) (m + 1))⁻¹ * eigCoef (m + 2) k) * u ^ (2 * k + 1)) :=
          hA.sub hB
        refine OddSpan.congr hmain (fun u => ?_)
        show u ^ (2*(m+1)+1) = (eigCoef (m + 2) (m + 1))⁻¹ * eigPoly (m + 2) u
              - ∑ k ∈ Finset.range (m + 1),
                  ((eigCoef (m + 2) (m + 1))⁻¹ * eigCoef (m + 2) k) * u ^ (2 * k + 1)
        have hsplit := eigPoly_split m u
        have h1 : eigCoef (m + 2) (m + 1) * u ^ (2*(m+1)+1)
            = eigPoly (m+2) u - ∑ k ∈ Finset.range (m+1), eigCoef (m+2) k * u ^ (2*k+1) := by
          rw [hsplit]; ring
        calc u ^ (2*(m+1)+1)
            = (eigCoef (m + 2) (m + 1))⁻¹ * (eigCoef (m + 2) (m + 1) * u ^ (2*(m+1)+1)) := by
              rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
          _ = (eigCoef (m + 2) (m + 1))⁻¹ * (eigPoly (m+2) u
                - ∑ k ∈ Finset.range (m+1), eigCoef (m+2) k * u ^ (2*k+1)) := by rw [h1]
          _ = (eigCoef (m + 2) (m + 1))⁻¹ * eigPoly (m+2) u
                - ∑ k ∈ Finset.range (m+1), ((eigCoef (m + 2) (m + 1))⁻¹ * eigCoef (m+2) k)
                  * u ^ (2*k+1) := by
              rw [mul_sub, Finset.mul_sum]
              congr 1
              exact Finset.sum_congr rfl (fun k _ => by ring)

/-- **The eigenpolynomials span the odd polynomials**: every odd monomial `u^{2m+1}` is a
finite linear combination of `p_1, …, p_{m+1}`. -/
theorem eigPoly_spans_odd (m : ℕ) : ∃ a : ℕ → ℝ, ∀ u : ℝ,
    u ^ (2 * m + 1) =
      ∑ k ∈ Finset.range (m + 1), a k * Work.FTS.EllipticEst.LevelOneAsm.eigPoly (k + 1) u :=
  eigPoly_spans_odd_aux m m (le_refl m)

end Work.FTS.EllipticEst.LevelOneAsm
