import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.RingTheory.Polynomial.DegreeLT

set_option maxHeartbeats 1000000

/-!
# Complete family of polynomials (real version)

This file proves `p51_complete_family`: a linear-algebra fact used in the proof of
Proposition 5.1 of A. Poëls, "On approximation to a real number by algebraic numbers
of bounded degree", Annals of Math 201 (2025).

Statement in words.  Let `2 ≤ k ≤ n + 1` and let `q : Fin k → ℝ[X]` be a linearly
independent family with `natDegree (q i) ≤ n` for every `i`, and with the first two
polynomials of degree exactly `n` and coprime.  We construct a "complete" family

    S = (q0, X q0, ..., X^(n+1-k) q0,  q1, X q1, ..., X^(n+1-k) q1,  R_3, ..., R_k)

of `2n - k + 2` linearly independent real polynomials, where each `R_j` has the form
`X^t * q_i` for some `2 ≤ i ≤ j` and `natDegree(q_i) + t ≤ 2n - k + 1`.
-/

namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree

open Polynomial
open scoped BigOperators

noncomputable section

/-! ## Section A : elementary polynomial degree facts -/

lemma natDegree_X_pow_mul_le (p : Polynomial ℝ) (t : ℕ) :
    (X ^ t * p).natDegree ≤ p.natDegree + t := by
  by_cases hp : p = 0
  · simp [hp]
  · rw [Polynomial.natDegree_X_pow_mul t hp]

lemma degree_lt_of_natDegree_lt {N : ℕ} {P : Polynomial ℝ} (h : P.natDegree < N) :
    P.degree < (N : WithBot ℕ) := by
  exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast h)

lemma mem_degreeLT_of_natDegree_lt {N : ℕ} {P : Polynomial ℝ} (h : P.natDegree < N) :
    P ∈ Polynomial.degreeLT ℝ N := by
  exact Polynomial.mem_degreeLT.mpr (degree_lt_of_natDegree_lt h)

/-! ## Section B : linear independence of shifted coprime pairs -/

/-- Bezout-style division: if `U*p + V*q = 0` with `p,q` coprime and the degrees of `U,V`
are smaller than the degrees of `q,p`, then `U = 0` and `V = 0`. -/
lemma cop_add_mul_eq_zero {p q U V : Polynomial ℝ}
    (hpq : IsCoprime p q) (hUV : U * p + V * q = 0)
    (hU : U.natDegree < q.natDegree) (hV : V.natDegree < p.natDegree) :
    U = 0 ∧ V = 0 := by
  rcases hpq with ⟨s, t, hst⟩
  have hp0 : p ≠ 0 := by
    intro hp0
    have : V.natDegree < 0 := by simpa [hp0] using hV
    omega
  have hq0 : q ≠ 0 := by
    intro hq0
    have : U.natDegree < 0 := by simpa [hq0] using hU
    omega
  have hqV : q * V = -(U * p) := by
    calc
      q * V = (U * p + V * q) - U * p := by ring
      _ = 0 - U * p := by rw [hUV]
      _ = -(U * p) := by ring
  have hVeq : V = p * (s * V - t * U) := by
    calc
      V = 1 * V := by ring
      _ = (s * p + t * q) * V := by rw [← hst]
      _ = s * p * V + t * (q * V) := by ring
      _ = s * p * V + t * (-(U * p)) := by rw [hqV]
      _ = p * (s * V - t * U) := by ring
  have hVzero : V = 0 := by
    by_contra hV0
    have hpdvd : p ∣ V := ⟨s * V - t * U, hVeq⟩
    have hle := Polynomial.natDegree_le_of_dvd hpdvd hV0
    exact (not_lt_of_ge hle) hV
  have hUzero : U = 0 := by
    have hUp : U * p = 0 := by
      simpa [hVzero] using hUV
    exact mul_eq_zero.mp hUp |>.resolve_right hp0
  exact ⟨hUzero, hVzero⟩

lemma coeff_C_mul_X_pow_of_ne {x : ℝ} {k n : ℕ} (h : k ≠ n) :
    (Polynomial.C x * X ^ k).coeff n = 0 := by
  rw [Polynomial.coeff_C_mul_X_pow]
  exact if_neg h.symm

lemma coeff_C_mul_X_pow_self {x : ℝ} {k : ℕ} :
    (Polynomial.C x * X ^ k).coeff k = x := by
  rw [Polynomial.coeff_C_mul_X_pow]
  simp

lemma sum_smul_X_pow_mul {a : ℕ} (p : Polynomial ℝ) (c : Fin (a+1) → ℝ) :
    (∑ t : Fin (a+1), c t • (X ^ t.1 * p)) =
      (∑ t : Fin (a+1), Polynomial.C (c t) * X ^ t.1) * p := by
  calc
    (∑ t : Fin (a+1), c t • (X ^ t.1 * p))
        = ∑ t : Fin (a+1), (Polynomial.C (c t) * X ^ t.1) * p := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [mul_assoc]
            exact Polynomial.smul_eq_C_mul (c t)
    _ = (∑ t : Fin (a+1), Polynomial.C (c t) * X ^ t.1) * p := by
            rw [Finset.sum_mul]

lemma coeff_fin_sum (a : ℕ) (c : Fin (a+1) → ℝ) (N : ℕ) (hN : a < N) :
    (∑ t : Fin (a+1), Polynomial.C (c t) * X ^ t.1).coeff N = 0 := by
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero ?_
  intro t ht
  have htN : t.1 ≠ N := by omega
  exact coeff_C_mul_X_pow_of_ne htN

lemma natDegree_fin_sum_le (a : ℕ) (c : Fin (a+1) → ℝ) :
    (∑ t : Fin (a+1), Polynomial.C (c t) * X ^ t.1).natDegree ≤ a := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  exact coeff_fin_sum a c N hN

/-- Linear independence of shifted coprime polynomials: if a polynomial combination
`(∑ c_t X^t) p + (∑ d_t X^t) q = 0` with degrees of the coefficient polynomials bounded
by `a` and `b` below the degrees of `q` and `p`, all coefficients vanish. -/
lemma shift_blocks_linIndep {p q : Polynomial ℝ} (hpq : IsCoprime p q)
    (a b : ℕ) (c : Fin (a+1) → ℝ) (d : Fin (b+1) → ℝ)
    (ha : a < q.natDegree) (hb : b < p.natDegree)
    (h : (∑ t : Fin (a+1), c t • (X ^ t.1 * p)) + (∑ t : Fin (b+1), d t • (X ^ t.1 * q)) = 0) :
    (∀ t : Fin (a+1), c t = 0) ∧ (∀ t : Fin (b+1), d t = 0) := by
  let U : Polynomial ℝ := ∑ t : Fin (a+1), Polynomial.C (c t) * X ^ t.1
  let V : Polynomial ℝ := ∑ t : Fin (b+1), Polynomial.C (d t) * X ^ t.1
  have hUV : U * p + V * q = 0 := by
    dsimp [U, V]
    rw [← sum_smul_X_pow_mul p c, ← sum_smul_X_pow_mul q d]
    exact h
  have hUdeg : U.natDegree < q.natDegree := lt_of_le_of_lt (natDegree_fin_sum_le a c) ha
  have hVdeg : V.natDegree < p.natDegree := lt_of_le_of_lt (natDegree_fin_sum_le b d) hb
  have hUV0 := cop_add_mul_eq_zero hpq hUV hUdeg hVdeg
  constructor
  · intro t
    have hU0 : U = 0 := hUV0.1
    have hc := congrArg (fun (P : Polynomial ℝ) => P.coeff t.1) hU0
    dsimp [U] at hc
    rw [Polynomial.finsetSum_coeff] at hc
    have hsingle : (∑ s : Fin (a+1), (Polynomial.C (c s) * X ^ s.1).coeff t.1) = c t := by
      rw [Finset.sum_eq_single t]
      · simp
      · intro s hs hst
        exact coeff_C_mul_X_pow_of_ne (by intro h; exact hst (Fin.ext h))
      · intro ht0
        exact (ht0 (Finset.mem_univ t)).elim
    exact hsingle.symm.trans hc
  · intro t
    have hV0 : V = 0 := hUV0.2
    have hc := congrArg (fun (P : Polynomial ℝ) => P.coeff t.1) hV0
    dsimp [V] at hc
    rw [Polynomial.finsetSum_coeff] at hc
    have hsingle : (∑ s : Fin (b+1), (Polynomial.C (d s) * X ^ s.1).coeff t.1) = d t := by
      rw [Finset.sum_eq_single t]
      · simp
      · intro s hs hst
        exact coeff_C_mul_X_pow_of_ne (by intro h; exact hst (Fin.ext h))
      · intro ht0
        exact (ht0 (Finset.mem_univ t)).elim
    exact hsingle.symm.trans hc

/-! ## Section C : dimension of span of shifted families -/

/-- Bundle of hypotheses on the polynomial family `q`. -/
structure QData where
  n : ℕ
  k : ℕ
  hn : 1 ≤ n
  hk2 : 2 ≤ k
  hkn : k ≤ n + 1
  q : Fin k → Polynomial ℝ
  hdeg : ∀ i : Fin k, (q i).natDegree ≤ n
  hdeg0 : (q ⟨0, lt_of_lt_of_le (by norm_num) hk2⟩).natDegree = n
  hdeg1 : (q ⟨1, lt_of_lt_of_le (by norm_num) hk2⟩).natDegree = n
  hcop : IsCoprime (q ⟨0, lt_of_lt_of_le (by norm_num) hk2⟩) (q ⟨1, lt_of_lt_of_le (by norm_num) hk2⟩)
  hlin : LinearIndependent ℝ q

namespace QData

/-- Ambient module: real polynomials of degree `< 2n`. -/
abbrev E (F : QData) := Polynomial.degreeLT ℝ (2 * F.n)

example (F : QData) (s t : Submodule ℝ F.E) : s ⊓ t = s ⊓ t := rfl


lemma n_lt_2n (F : QData) : F.n < 2 * F.n := by
  have hn1 : (1 : ℕ) ≤ F.n := F.hn
  omega

/-- Embed a polynomial of degree `< 2n`. -/
def emb (F : QData) (P : Polynomial ℝ) (h : P.natDegree < 2 * F.n) : F.E :=
  ⟨P, mem_degreeLT_of_natDegree_lt h⟩

/-- The family member `q i` as an element of the ambient space. -/
def eQ (F : QData) (i : Fin F.k) : F.E :=
  F.emb (F.q i) (lt_of_le_of_lt (F.hdeg i) (F.n_lt_2n))

/-- `X^t * q i` as an element of the ambient space. -/
def emk (F : QData) (t : ℕ) (i : Fin F.k) (h : (F.q i).natDegree + t < 2 * F.n) : F.E :=
  F.emb (X ^ t * F.q i) (lt_of_le_of_lt (natDegree_X_pow_mul_le (F.q i) t) h)

/-- The generating set of the span of the first `r+1` polynomials (indices `≤ r`)
shifted up to degree `≤ ℓ`. -/
def gens (F : QData) (r ℓ : ℕ) : Set F.E :=
  { v | ∃ i : Fin F.k, i.val ≤ r ∧ ∃ t : ℕ,
      ∃ ht : (F.q i).natDegree + t < 2 * F.n,
        t ≤ ℓ - (F.q i).natDegree ∧ v = F.emk t i ht }

/-- The subspace spanned by shifts of `q_0, ..., q_r` up to degree `≤ ℓ`. -/
abbrev V (F : QData) (r ℓ : ℕ) : Submodule ℝ F.E := Submodule.span ℝ (F.gens r ℓ)

lemma emk_val (F : QData) (t : ℕ) (i : Fin F.k) (h : (F.q i).natDegree + t < 2 * F.n) :
    ((F.emk t i h : F.E) : Polynomial ℝ) = X ^ t * F.q i := rfl

lemma eQ_val (F : QData) (i : Fin F.k) :
    ((F.eQ i : F.E) : Polynomial ℝ) = F.q i := rfl

lemma mem_V_emk (F : QData) (r ℓ : ℕ) {i : Fin F.k} (hi : i.val ≤ r) (t : ℕ)
    (ht : (F.q i).natDegree + t < 2 * F.n) (htℓ : t ≤ ℓ - (F.q i).natDegree) :
    F.emk t i ht ∈ F.V r ℓ := by
  exact Submodule.subset_span (by
    refine ⟨i, hi, t, ht, htℓ, rfl⟩)

lemma mem_V_of_mem_gens {F : QData} {r ℓ : ℕ} {v : F.E} (hv : v ∈ F.gens r ℓ) :
    v ∈ F.V r ℓ := Submodule.subset_span hv


/-! #### Degree bounds of elements of `V` -/

lemma gens_mem_natDegree_le (F : QData) (r ℓ : ℕ) (hℓlo : F.n ≤ ℓ)
    {v : F.E} (hv : v ∈ F.gens r ℓ) : (v : Polynomial ℝ).natDegree ≤ ℓ := by
  rcases hv with ⟨i, hi, t, ht, htℓ, rfl⟩
  have hdegℓ : (F.q i).natDegree ≤ ℓ := le_trans (F.hdeg i) hℓlo
  have htdeg : (F.q i).natDegree + t ≤ ℓ := by
    have h1 : t + (F.q i).natDegree ≤ (ℓ - (F.q i).natDegree) + (F.q i).natDegree :=
      Nat.add_le_add_right htℓ _
    rw [Nat.sub_add_cancel hdegℓ] at h1
    omega
  calc
    (X ^ t * F.q i).natDegree ≤ (F.q i).natDegree + t := natDegree_X_pow_mul_le (F.q i) t
    _ ≤ ℓ := htdeg

/-- The subspace of `F.E` of elements whose underlying polynomial has degree `< ℓ+1`. -/
def degSub (F : QData) (ℓ : ℕ) : Submodule ℝ F.E :=
  Submodule.comap (F.E.subtype) (Polynomial.degreeLT ℝ (ℓ + 1))

lemma degSub_mem (F : QData) (ℓ : ℕ) (v : F.E) :
    v ∈ F.degSub ℓ ↔ (v : Polynomial ℝ) ∈ Polynomial.degreeLT ℝ (ℓ + 1) := by
  rfl

lemma V_le_degSub (F : QData) (r ℓ : ℕ) (hℓlo : F.n ≤ ℓ) :
    F.V r ℓ ≤ F.degSub ℓ := by
  change Submodule.span ℝ (F.gens r ℓ) ≤ F.degSub ℓ
  rw [Submodule.span_le]
  intro v hv
  exact F.degSub_mem ℓ v |>.mpr (mem_degreeLT_of_natDegree_lt
    (Nat.lt_succ_of_le (F.gens_mem_natDegree_le r ℓ hℓlo hv)))

lemma V_mem_natDegree_le (F : QData) (r ℓ : ℕ) (hℓlo : F.n ≤ ℓ)
    {v : F.E} (hv : v ∈ F.V r ℓ) : (v : Polynomial ℝ).natDegree ≤ ℓ := by
  have hvdeg : (v : Polynomial ℝ) ∈ Polynomial.degreeLT ℝ (ℓ + 1) :=
    (F.degSub_mem ℓ v).mp ((F.V_le_degSub r ℓ hℓlo) hv)
  have hlt : (v : Polynomial ℝ).natDegree < ℓ + 1 := by
    by_cases hp0 : (v : Polynomial ℝ) = 0
    · simp [hp0]
    · exact (Polynomial.natDegree_lt_iff_degree_lt (p := (v : Polynomial ℝ)) hp0).mpr
        (Polynomial.mem_degreeLT.mp hvdeg)
  omega

/-! #### Monotonicity of `V r ℓ` in the level `ℓ` -/

lemma gens_mono_level (F : QData) (r ℓ : ℕ) : F.gens r ℓ ⊆ F.gens r (ℓ + 1) := by
  intro v hv
  rcases hv with ⟨i, hi, t, ht, htℓ, rfl⟩
  refine ⟨i, hi, t, ht, ?_, rfl⟩
  exact le_trans htℓ (Nat.sub_le_sub_right (Nat.le_succ ℓ) (F.q i).natDegree)

lemma V_mono_level (F : QData) (r ℓ : ℕ) : F.V r ℓ ≤ F.V r (ℓ + 1) := by
  exact Submodule.span_mono (F.gens_mono_level r ℓ)

/-! #### The multiplication-by-X generators and the identity `V(ℓ+1) = V ℓ ⊔ X(V ℓ)` -/

/-- Generators obtained from `V r ℓ` by multiplication by `X` (exponents shifted by one). -/
def xgens (F : QData) (r ℓ : ℕ) : Set F.E :=
  { v | ∃ i : Fin F.k, i.val ≤ r ∧ ∃ t : ℕ,
      ∃ ht : (F.q i).natDegree + (t + 1) < 2 * F.n,
        t ≤ ℓ - (F.q i).natDegree ∧ v = F.emk (t + 1) i ht }

/-- `X · V r ℓ` is contained in `V r (ℓ+1)`. -/
lemma xgens_subset_gens_succ (F : QData) (r ℓ : ℕ) (hℓlo : F.n ≤ ℓ) :
    F.xgens r ℓ ⊆ F.gens r (ℓ + 1) := by
  intro v hv
  rcases hv with ⟨i, hi, t, ht, htℓ, rfl⟩
  refine ⟨i, hi, t + 1, ht, ?_, rfl⟩
  have hdegℓ : (F.q i).natDegree ≤ ℓ := le_trans (F.hdeg i) hℓlo
  have hsub : (ℓ + 1) - (F.q i).natDegree = (ℓ - (F.q i).natDegree) + 1 := by omega
  rw [hsub]
  exact Nat.succ_le_succ htℓ

lemma span_xgens_le_V_succ (F : QData) (r ℓ : ℕ) (hℓlo : F.n ≤ ℓ) :
    Submodule.span ℝ (F.xgens r ℓ) ≤ F.V r (ℓ + 1) := by
  change Submodule.span ℝ (F.xgens r ℓ) ≤ Submodule.span ℝ (F.gens r (ℓ + 1))
  exact Submodule.span_mono (F.xgens_subset_gens_succ r ℓ hℓlo)

/-- Every generator of `V(ℓ+1)` lies in `V(ℓ)` or in `X(V(ℓ))`. -/
lemma gens_succ_subset_sup (F : QData) (r ℓ : ℕ) (hℓlo : F.n ≤ ℓ) :
    F.gens r (ℓ + 1) ⊆ (F.V r ℓ : Set F.E) ∪ F.xgens r ℓ := by
  intro v hv
  rcases hv with ⟨i, hi, t, ht, htℓ, rfl⟩
  by_cases ht0 : t = 0
  · left
    subst ht0
    exact F.mem_V_emk r ℓ hi 0 ht (by simp)
  · right
    refine ⟨i, hi, t - 1, ?_, ?_, ?_⟩
    · have ht1 : 1 ≤ t := Nat.succ_le_of_lt (Nat.pos_of_ne_zero ht0)
      omega
    · have hdegℓ : (F.q i).natDegree ≤ ℓ := le_trans (F.hdeg i) hℓlo
      have hsub : (ℓ + 1) - (F.q i).natDegree = (ℓ - (F.q i).natDegree) + 1 := by omega
      have ht1 : 1 ≤ t := Nat.succ_le_of_lt (Nat.pos_of_ne_zero ht0)
      rw [hsub] at htℓ
      omega
    · apply Subtype.ext
      change (X ^ t * F.q i) = (X ^ (t - 1 + 1) * F.q i)
      have ht1 : 1 ≤ t := Nat.succ_le_of_lt (Nat.pos_of_ne_zero ht0)
      congr 1
      rw [← show t = t - 1 + 1 by omega]

lemma V_succ_le_sup (F : QData) (r ℓ : ℕ) (hℓlo : F.n ≤ ℓ) :
    F.V r (ℓ + 1) ≤ F.V r ℓ ⊔ Submodule.span ℝ (F.xgens r ℓ) := by
  change Submodule.span ℝ (F.gens r (ℓ + 1)) ≤ F.V r ℓ ⊔ Submodule.span ℝ (F.xgens r ℓ)
  rw [Submodule.span_le]
  intro v hv
  rcases (F.gens_succ_subset_sup r ℓ hℓlo) hv with hv1 | hv2
  · exact Submodule.mem_sup_left hv1
  · exact Submodule.mem_sup_right (Submodule.subset_span hv2)

lemma V_succ_eq_sup (F : QData) (r ℓ : ℕ) (hℓlo : F.n ≤ ℓ) :
    F.V r (ℓ + 1) = F.V r ℓ ⊔ Submodule.span ℝ (F.xgens r ℓ) := by
  apply le_antisymm
  · exact F.V_succ_le_sup r ℓ hℓlo
  · exact sup_le (F.V_mono_level r ℓ) (F.span_xgens_le_V_succ r ℓ hℓlo)




/-! #### Multiplication by `X` as a linear map -/

lemma natDegree_X_mul_le (p : Polynomial ℝ) : (X * p).natDegree ≤ p.natDegree + 1 := by
  simpa using (natDegree_X_pow_mul_le p 1)

/-- Multiplication by `X` maps `V r ℓ` linearly into the ambient space (when `ℓ+1 < 2n`). -/
def xmul (F : QData) (r ℓ : ℕ) (hℓlo : F.n ≤ ℓ) (hℓ : ℓ + 1 < 2 * F.n) :
    F.V r ℓ →ₗ[ℝ] F.E where
  toFun x :=
    ⟨(X * (x.1 : Polynomial ℝ) : Polynomial ℝ),
      mem_degreeLT_of_natDegree_lt
        (lt_of_le_of_lt
          (le_trans (natDegree_X_mul_le (x.1 : Polynomial ℝ))
            (Nat.succ_le_succ (F.V_mem_natDegree_le r ℓ hℓlo x.2)))
          hℓ)⟩
  map_add' x y := by
    ext i
    simp [mul_add, add_mul, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  map_smul' a x := by
    ext i
    simp [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, mul_add, add_mul]


/-- `xmul` is injective because `X` is not a zero divisor. -/
lemma xmul_injective (F : QData) (r ℓ : ℕ) (hℓlo : F.n ≤ ℓ) (hℓ : ℓ + 1 < 2 * F.n) :
    Function.Injective (F.xmul r ℓ hℓlo hℓ) := by
  intro x y hxy
  have hval : X * (x.1 : Polynomial ℝ) = X * (y.1 : Polynomial ℝ) := by
    have hc := congrArg (fun v : F.E => (v : Polynomial ℝ)) hxy
    simpa [xmul] using hc
  have hp := mul_left_cancel₀ (by simp : (X : Polynomial ℝ) ≠ 0) hval
  apply Subtype.ext
  apply Subtype.ext
  exact hp

lemma finrank_range_xmul (F : QData) (r ℓ : ℕ) (hℓlo : F.n ≤ ℓ) (hℓ : ℓ + 1 < 2 * F.n) :
    Module.finrank ℝ ((F.xmul r ℓ hℓlo hℓ).range) = Module.finrank ℝ (F.V r ℓ) := by
  exact LinearMap.finrank_range_of_inj (F.xmul_injective r ℓ hℓlo hℓ)

lemma xmul_apply_gen (F : QData) (r ℓ : ℕ) (hℓlo : F.n ≤ ℓ) (hℓ : ℓ + 1 < 2 * F.n)
    {i : Fin F.k} (hi : i.val ≤ r) (t : ℕ)
    (ht : (F.q i).natDegree + t < 2 * F.n) (htℓ : t ≤ ℓ - (F.q i).natDegree) :
    F.xmul r ℓ hℓlo hℓ ⟨F.emk t i ht, F.mem_V_emk r ℓ hi t ht htℓ⟩ =
      F.emk (t + 1) i (by
        have hdegℓ : (F.q i).natDegree ≤ ℓ := le_trans (F.hdeg i) hℓlo
        have h1 : t + (F.q i).natDegree ≤ (ℓ - (F.q i).natDegree) + (F.q i).natDegree :=
          Nat.add_le_add_right htℓ _
        rw [Nat.sub_add_cancel hdegℓ] at h1
        omega) := by
  apply Subtype.ext
  change X * (X ^ t * F.q i) = X ^ (t + 1) * F.q i
  rw [pow_succ', mul_assoc]

/-- `xmul` sends elements of `V r ℓ` into `span (xgens r ℓ)`. -/
lemma xmul_mem_span_xgens (F : QData) (r ℓ : ℕ) (hℓlo : F.n ≤ ℓ) (hℓ : ℓ + 1 < 2 * F.n)
    (x : F.V r ℓ) : F.xmul r ℓ hℓlo hℓ x ∈ Submodule.span ℝ (F.xgens r ℓ) := by
  refine Submodule.span_induction (p := fun (z : F.E) (hz : z ∈ F.V r ℓ) =>
      F.xmul r ℓ hℓlo hℓ ⟨z, hz⟩ ∈ Submodule.span ℝ (F.xgens r ℓ)) ?_ ?_ ?_ ?_ x.2
  · intro z hz
    have hz_orig := hz
    rcases hz with ⟨i, hi, t, ht, htℓ, rfl⟩
    have heq : (⟨F.emk t i ht, (Submodule.subset_span hz_orig)⟩ : F.V r ℓ) =
        ⟨F.emk t i ht, F.mem_V_emk r ℓ hi t ht htℓ⟩ := by
      apply Subtype.ext
      rfl
    rw [heq, F.xmul_apply_gen r ℓ hℓlo hℓ hi t ht htℓ]
    exact Submodule.subset_span (by
      refine ⟨i, hi, t, ?_, htℓ, rfl⟩
      have hdegℓ : (F.q i).natDegree ≤ ℓ := le_trans (F.hdeg i) hℓlo
      have h1 : t + (F.q i).natDegree ≤ (ℓ - (F.q i).natDegree) + (F.q i).natDegree :=
        Nat.add_le_add_right htℓ _
      rw [Nat.sub_add_cancel hdegℓ] at h1
      omega)
  · change (F.xmul r ℓ hℓlo hℓ (0 : F.V r ℓ)) ∈ Submodule.span ℝ (F.xgens r ℓ)
    rw [map_zero]
    exact Submodule.zero_mem _
  · intro z w hz hw hz' hw'
    have hsum : (⟨z + w, Submodule.add_mem (p := F.V r ℓ) hz hw⟩ : F.V r ℓ) = ⟨z, hz⟩ + ⟨w, hw⟩ := by
      apply Subtype.ext
      rfl
    rw [hsum, map_add]
    exact Submodule.add_mem (p := Submodule.span ℝ (F.xgens r ℓ)) hz' hw'
  · intro a z hz hz'
    have hsm : (⟨a • z, Submodule.smul_mem (p := F.V r ℓ) a hz⟩ : F.V r ℓ) = a • ⟨z, hz⟩ := by
      apply Subtype.ext
      rfl
    rw [hsm, map_smul]
    exact Submodule.smul_mem (p := Submodule.span ℝ (F.xgens r ℓ)) a hz'

lemma range_xmul_le_span_xgens (F : QData) (r ℓ : ℕ) (hℓlo : F.n ≤ ℓ) (hℓ : ℓ + 1 < 2 * F.n) :
    (F.xmul r ℓ hℓlo hℓ).range ≤ Submodule.span ℝ (F.xgens r ℓ) := by
  intro w hw
  rcases (LinearMap.mem_range.mp hw) with ⟨x, rfl⟩
  exact F.xmul_mem_span_xgens r ℓ hℓlo hℓ x

/-- Each generator `X^(t+1) q_i` of `xgens r ℓ` lies in the range of `xmul`. -/
lemma xgens_mem_range (F : QData) (r ℓ : ℕ) (hℓlo : F.n ≤ ℓ) (hℓ : ℓ + 1 < 2 * F.n)
    {v : F.E} (hv : v ∈ F.xgens r ℓ) : v ∈ (F.xmul r ℓ hℓlo hℓ).range := by
  rcases hv with ⟨i, hi, t, ht, htℓ, rfl⟩
  have ht' : (F.q i).natDegree + t < 2 * F.n := by omega
  refine ⟨⟨F.emk t i ht', F.mem_V_emk r ℓ hi t ht' htℓ⟩, ?_⟩
  have heq1 := F.xmul_apply_gen r ℓ hℓlo hℓ hi t ht' htℓ
  rw [heq1]

lemma span_xgens_le_range_xmul (F : QData) (r ℓ : ℕ) (hℓlo : F.n ≤ ℓ) (hℓ : ℓ + 1 < 2 * F.n) :
    Submodule.span ℝ (F.xgens r ℓ) ≤ (F.xmul r ℓ hℓlo hℓ).range := by
  rw [Submodule.span_le]
  intro v hv
  exact F.xgens_mem_range r ℓ hℓlo hℓ hv

lemma xmul_range_eq_span_xgens (F : QData) (r ℓ : ℕ) (hℓlo : F.n ≤ ℓ) (hℓ : ℓ + 1 < 2 * F.n) :
    (F.xmul r ℓ hℓlo hℓ).range = Submodule.span ℝ (F.xgens r ℓ) := by
  exact le_antisymm (F.range_xmul_le_span_xgens r ℓ hℓlo hℓ) (F.span_xgens_le_range_xmul r ℓ hℓlo hℓ)

/-- The successor subspace is the join of `V r ℓ` with the range of multiplication by `X`. -/
lemma V_succ_eq_sup_range (F : QData) (r ℓ : ℕ) (hℓlo : F.n ≤ ℓ) (hℓ : ℓ + 1 < 2 * F.n) :
    F.V r (ℓ + 1) = F.V r ℓ ⊔ (F.xmul r ℓ hℓlo hℓ).range := by
  rw [F.xmul_range_eq_span_xgens r ℓ hℓlo hℓ]
  exact F.V_succ_eq_sup r ℓ hℓlo

/-! #### The dimension sequence `ℓ ↦ finrank (V r ℓ)` is strictly increasing with decreasing increments -/

/-- `q0` is nonzero. -/
lemma q0_ne_zero (F : QData) : F.q ⟨0, lt_of_lt_of_le (by norm_num) F.hk2⟩ ≠ 0 := by
  intro hz
  have h := F.hdeg0
  simp [hz] at h
  have hn : 1 ≤ F.n := F.hn
  omega

lemma xgens_mono_level (F : QData) (r ℓ : ℕ) : F.xgens r ℓ ⊆ F.xgens r (ℓ + 1) := by
  intro v hv
  rcases hv with ⟨i, hi, t, ht, htℓ, rfl⟩
  refine ⟨i, hi, t, ht, ?_, rfl⟩
  exact le_trans htℓ (Nat.sub_le_sub_right (Nat.le_succ ℓ) (F.q i).natDegree)

/-- `V r ℓ` is strictly contained in `V r (ℓ+1)`: the element `X^(ℓ+1-n) q0` is new. -/
lemma V_lt_succ (F : QData) (r ℓ : ℕ) (hℓlo : F.n ≤ ℓ) (hℓ : ℓ + 1 < 2 * F.n) :
    F.V r ℓ < F.V r (ℓ + 1) := by
  let i0 : Fin F.k := ⟨0, lt_of_lt_of_le (by norm_num) F.hk2⟩
  let t0 : ℕ := ℓ + 1 - F.n
  have ht : (F.q i0).natDegree + t0 < 2 * F.n := by
    have hn : (F.q i0).natDegree = F.n := F.hdeg0
    dsimp [t0]
    rw [hn]
    omega
  have hm : F.emk t0 i0 ht ∈ F.V r (ℓ + 1) := by
    exact F.mem_V_emk r (ℓ + 1) (by dsimp [i0]; simp) t0 ht (by
      dsimp [t0]
      rw [F.hdeg0])
  refine lt_of_le_of_ne (F.V_mono_level r ℓ) ?_
  intro heq
  have hmem : F.emk t0 i0 ht ∈ F.V r ℓ := by
    rw [heq]
    exact hm
  have hdeg := F.V_mem_natDegree_le r ℓ hℓlo hmem
  have hnd : (F.emk t0 i0 ht : Polynomial ℝ).natDegree = ℓ + 1 := by
    dsimp [t0]
    rw [F.emk_val]
    rw [Polynomial.natDegree_X_pow_mul t0 (F.q0_ne_zero)]
    rw [F.hdeg0]
    exact Nat.add_sub_of_le (by omega)
  omega

/-- The rank strictly increases by at least one at each level. -/
lemma V_rank_incr (F : QData) (r ℓ : ℕ) (hℓlo : F.n ≤ ℓ) (hℓ : ℓ + 1 < 2 * F.n) :
    Module.finrank ℝ (F.V r ℓ) + 1 ≤ Module.finrank ℝ (F.V r (ℓ + 1)) := by
  have hlt := F.V_lt_succ r ℓ hℓlo hℓ
  exact Nat.succ_le_of_lt (Submodule.finrank_lt_finrank_of_lt hlt)

/-- Sub-range of `xmul` at level `ℓ-1` is contained in `V r ℓ`. -/
lemma range_xmul_prev_le_nextV (F : QData) (r ℓ : ℕ) (hℓlo1 : F.n + 1 ≤ ℓ)
    (hℓprev_lo : F.n ≤ ℓ - 1) (hℓprev_hi : (ℓ - 1) + 1 < 2 * F.n) :
    (F.xmul r (ℓ - 1) hℓprev_lo hℓprev_hi).range ≤ F.V r ℓ := by
  rw [F.xmul_range_eq_span_xgens r (ℓ - 1) hℓprev_lo hℓprev_hi]
  change Submodule.span ℝ (F.xgens r (ℓ - 1)) ≤ Submodule.span ℝ (F.gens r ℓ)
  exact Submodule.span_mono (by
    have hpos : 1 ≤ ℓ := by omega
    have hs := F.xgens_subset_gens_succ r (ℓ - 1) hℓprev_lo
    simpa [Nat.sub_add_cancel hpos] using hs)

/-- Sub-range of `xmul` at level `ℓ-1` is contained in the range of `xmul` at level `ℓ`. -/
lemma range_xmul_prev_le_range (F : QData) (r ℓ : ℕ) (hℓlo : F.n ≤ ℓ) (hℓ : ℓ + 1 < 2 * F.n)
    (hℓprev_lo : F.n ≤ ℓ - 1) (hℓprev_hi : (ℓ - 1) + 1 < 2 * F.n) :
    (F.xmul r (ℓ - 1) hℓprev_lo hℓprev_hi).range ≤ (F.xmul r ℓ hℓlo hℓ).range := by
  rw [F.xmul_range_eq_span_xgens r (ℓ - 1) hℓprev_lo hℓprev_hi]
  rw [F.xmul_range_eq_span_xgens r ℓ hℓlo hℓ]
  exact Submodule.span_mono (by
    have hpos : 1 ≤ ℓ := by omega
    have hs := F.xgens_mono_level r (ℓ - 1)
    simpa [Nat.sub_add_cancel hpos] using hs)

/-- The increments of the dimension sequence are decreasing (concavity). -/
lemma V_rank_incr_decr (F : QData) (r ℓ : ℕ) (hℓlo1 : F.n + 1 ≤ ℓ) (hℓ : ℓ + 1 < 2 * F.n) :
    Module.finrank ℝ (F.V r (ℓ + 1)) - Module.finrank ℝ (F.V r ℓ) ≤
      Module.finrank ℝ (F.V r ℓ) - Module.finrank ℝ (F.V r (ℓ - 1)) := by
  have hpos : 1 ≤ ℓ := by omega
  have hℓprev_lo : F.n ≤ ℓ - 1 := by omega
  have hℓprev_hi : (ℓ - 1) + 1 < 2 * F.n := by
    rw [Nat.sub_add_cancel hpos]
    omega
  let A : Submodule ℝ F.E := F.V r ℓ
  let B : Submodule ℝ F.E := F.V r (ℓ + 1)
  let C : Submodule ℝ F.E := F.V r (ℓ - 1)
  let R : Submodule ℝ F.E := (F.xmul r ℓ (by omega) hℓ).range
  let R' : Submodule ℝ F.E := (F.xmul r (ℓ - 1) hℓprev_lo hℓprev_hi).range
  let I : Submodule ℝ F.E := A ⊓ R
  have hCB : C ≤ A := by
    dsimp [C, A]
    have hs := F.V_mono_level r (ℓ - 1)
    simpa [Nat.sub_add_cancel hpos] using hs
  have hsup : F.V r (ℓ + 1) = A ⊔ R := by
    dsimp [A, R]
    exact F.V_succ_eq_sup_range r ℓ (by omega) hℓ
  have hRrank : Module.finrank ℝ R = Module.finrank ℝ A := by
    dsimp [A, R]
    exact F.finrank_range_xmul r ℓ (by omega) hℓ
  have hCrank : Module.finrank ℝ R' = Module.finrank ℝ C := by
    dsimp [C, R']
    exact F.finrank_range_xmul r (ℓ - 1) hℓprev_lo hℓprev_hi
  have hR'leA : R' ≤ A := by
    dsimp [R', A]
    exact F.range_xmul_prev_le_nextV r ℓ hℓlo1 hℓprev_lo hℓprev_hi
  have hR'leR : R' ≤ R := by
    dsimp [R', R]
    exact F.range_xmul_prev_le_range r ℓ (by omega) hℓ hℓprev_lo hℓprev_hi
  have hR'leI : R' ≤ I := by
    dsimp [I]
    exact le_inf hR'leA hR'leR
  have hCI : Module.finrank ℝ C ≤ Module.finrank ℝ I := by
    have hmono := Submodule.finrank_mono hR'leI
    rw [hCrank] at hmono
    exact hmono
  have hsup2 : Module.finrank ℝ B + Module.finrank ℝ I = Module.finrank ℝ A + Module.finrank ℝ A := by
    have hs := Submodule.finrank_sup_add_finrank_inf_eq A R
    dsimp [B, I]
    rw [← hsup, hRrank] at hs
    exact hs
  have hA : Module.finrank ℝ A ≤ Module.finrank ℝ B := by
    dsimp [A, B]
    exact le_of_lt (Submodule.finrank_lt_finrank_of_lt (F.V_lt_succ r ℓ (by omega) hℓ))
  dsimp [A, B, C] at hCB hsup2 hCI hA
  omega



/-! #### Prefix ranks: base at level `n`, full at level `2n-1`, and the Annals bound -/

/-- The index-embedding of a prefix into `Fin k`. -/
def prefixEmb (F : QData) (r : ℕ) (hr : r ≤ F.k - 1) (u : Fin (r + 1)) : Fin F.k :=
  ⟨u.val, by
    have hk1 : 1 ≤ F.k := le_trans (by norm_num) F.hk2
    have hsucc : r + 1 ≤ (F.k - 1) + 1 := Nat.succ_le_succ hr
    have hsub : F.k - 1 + 1 = F.k := Nat.sub_add_cancel hk1
    exact lt_of_lt_of_le u.isLt (by rwa [hsub] at hsucc)⟩

/-- The first `r+1` polynomials are linearly independent in the ambient module. -/
lemma prefix_linIndep (F : QData) (r : ℕ) (hr : r ≤ F.k - 1) :
    LinearIndependent ℝ (fun u : Fin (r + 1) => F.eQ (F.prefixEmb r hr u)) := by
  have hlin_poly : LinearIndependent ℝ (fun u : Fin (r + 1) => F.q (F.prefixEmb r hr u)) := by
    -- subfamily of an independent family
    exact F.hlin.comp (F.prefixEmb r hr) (by
      intro a b hab
      apply Fin.ext
      have hv := congrArg Fin.val hab
      simpa [prefixEmb] using hv)
  -- transfer from polynomial to ambient submodule
  exact LinearIndependent.of_comp F.E.subtype hlin_poly

/-- Base rank: `V r n` has dimension at least `r + 1`. -/
lemma V_base_rank (F : QData) (r : ℕ) (hr : r ≤ F.k - 1) :
    r + 1 ≤ Module.finrank ℝ (F.V r F.n) := by
  have hspan : Submodule.span ℝ (Set.range (fun u : Fin (r + 1) => F.eQ (F.prefixEmb r hr u))) ≤
      F.V r F.n := by
    rw [Submodule.span_le]
    intro v hv
    rcases hv with ⟨u, rfl⟩
    change F.eQ (F.prefixEmb r hr u) ∈ F.V r F.n
    have ht : (F.q (F.prefixEmb r hr u)).natDegree + 0 < 2 * F.n := by
      have hdeg := F.hdeg (F.prefixEmb r hr u)
      have hlt : (F.q (F.prefixEmb r hr u)).natDegree < 2 * F.n := lt_of_le_of_lt hdeg F.n_lt_2n
      simpa using hlt
    have heqE : F.eQ (F.prefixEmb r hr u) = F.emk 0 (F.prefixEmb r hr u) ht := by
      apply Subtype.ext
      simp [eQ, emk, emb]
    rw [heqE]
    exact F.mem_V_emk r F.n (i := F.prefixEmb r hr u)
      (by simpa [prefixEmb] using (Nat.le_of_lt_succ u.isLt)) 0 ht (by simp)
  have hfin := finrank_span_eq_card (R := ℝ) (b := fun u : Fin (r + 1) => F.eQ (F.prefixEmb r hr u))
    (F.prefix_linIndep r hr)
  -- hfin : finrank (span range) = Fintype.card (Fin (r+1))
  have hmono := Submodule.finrank_mono hspan
  rw [hfin] at hmono
  simpa using hmono


/-- index of q0 and q1 inside `Fin k`. -/
def i0 (F : QData) : Fin F.k := ⟨0, lt_of_lt_of_le (by norm_num) F.hk2⟩
def i1 (F : QData) : Fin F.k := ⟨1, lt_of_lt_of_le (by norm_num) F.hk2⟩

/-- The block family `(X^t q0, X^t q1)` for `t < n` as elements of the ambient space. -/
def blockFam (F : QData) : Fin (F.n - 1 + 1) ⊕ Fin (F.n - 1 + 1) → F.E := fun a =>
  match a with
  | Sum.inl t => F.emk t.val (F.i0) (by
      have hn : (F.q (F.i0)).natDegree = F.n := F.hdeg0
      have hpos : 1 ≤ F.n := F.hn
      have ht : t.val < F.n := by omega
      omega)
  | Sum.inr t => F.emk t.val (F.i1) (by
      have hn : (F.q (F.i1)).natDegree = F.n := F.hdeg1
      have hpos : 1 ≤ F.n := F.hn
      have ht : t.val < F.n := by omega
      omega)

/-- The block family is linearly independent. -/
lemma blockFam_linIndep (F : QData) : LinearIndependent ℝ (F.blockFam) := by
  classical
  apply Fintype.linearIndependent_iff.2
  intro c hc
  have hsum : (∑ t : Fin (F.n - 1 + 1), c (Sum.inl t) • F.blockFam (Sum.inl t)) +
      (∑ t : Fin (F.n - 1 + 1), c (Sum.inr t) • F.blockFam (Sum.inr t)) = 0 := by
    simpa [Fintype.sum_sum_type] using hc
  have hpoly : (∑ t : Fin (F.n - 1 + 1), c (Sum.inl t) • (X ^ t.val * F.q (F.i0))) +
      (∑ t : Fin (F.n - 1 + 1), c (Sum.inr t) • (X ^ t.val * F.q (F.i1))) = 0 := by
    have hc' := congrArg (fun v : F.E => (v : Polynomial ℝ)) hsum
    simpa [blockFam, F.emk_val] using hc'
  have hres : (∀ t : Fin (F.n - 1 + 1), c (Sum.inl t) = 0) ∧
      (∀ t : Fin (F.n - 1 + 1), c (Sum.inr t) = 0) := by
    refine shift_blocks_linIndep (p := F.q (F.i0)) (q := F.q (F.i1))
      (a := F.n - 1) (b := F.n - 1)
      (c := fun t : Fin (F.n - 1 + 1) => c (Sum.inl t))
      (d := fun t : Fin (F.n - 1 + 1) => c (Sum.inr t)) ?hpq ?ha ?hb ?h
    · exact (by simpa [i0, i1] using F.hcop)
    · have hpos : 1 ≤ F.n := F.hn
      have hn : F.n - 1 < F.n := by omega
      have hd : (F.q (F.i1)).natDegree = F.n := by simpa [i1] using F.hdeg1
      simpa [hd] using hn
    · have hpos : 1 ≤ F.n := F.hn
      have hn : F.n - 1 < F.n := by omega
      have hd : (F.q (F.i0)).natDegree = F.n := by simpa [i0] using F.hdeg0
      simpa [hd] using hn
    · exact hpoly
  intro a
  cases a with
  | inl t => exact hres.1 t
  | inr t => exact hres.2 t


/-- The dimension of the ambient module `E` is `2n`. -/
lemma finrank_E (F : QData) : Module.finrank ℝ F.E = 2 * F.n := by
  let B : ℕ := 2 * F.n
  have hb : Module.finrank ℝ (Polynomial.degreeLT ℝ B) = B := by
    simpa using (Module.finrank_eq_card_basis (Polynomial.degreeLT.basis ℝ B))
  change Module.finrank ℝ F.E = B
  simpa [E, B] using hb

/-- The elements of the block family lie in `V 1 (2n-1)`. -/
lemma blockFam_subset_V1 (F : QData) :
    (Set.range F.blockFam) ⊆ (F.V 1 (2 * F.n - 1) : Set F.E) := by
  rintro v ⟨a, rfl⟩
  cases a with
  | inl t =>
      have h1 : (F.q (F.i0)).natDegree + t.val < 2 * F.n := by
        have hd : (F.q (F.i0)).natDegree = F.n := F.hdeg0
        have hpos : 1 ≤ F.n := F.hn
        omega
      have h2 : t.val ≤ (2 * F.n - 1) - (F.q (F.i0)).natDegree := by
        have hd : (F.q (F.i0)).natDegree = F.n := F.hdeg0
        have hpos : 1 ≤ F.n := F.hn
        omega
      have hmem : F.emk t.val (F.i0) h1 ∈ F.V 1 (2 * F.n - 1) :=
        F.mem_V_emk 1 (2 * F.n - 1) (i := F.i0) (by dsimp [i0]; simp) t.val h1 h2
      simpa [blockFam] using hmem
  | inr t =>
      have h1 : (F.q (F.i1)).natDegree + t.val < 2 * F.n := by
        have hd : (F.q (F.i1)).natDegree = F.n := F.hdeg1
        have hpos : 1 ≤ F.n := F.hn
        omega
      have h2 : t.val ≤ (2 * F.n - 1) - (F.q (F.i1)).natDegree := by
        have hd : (F.q (F.i1)).natDegree = F.n := F.hdeg1
        have hpos : 1 ≤ F.n := F.hn
        omega
      have hmem : F.emk t.val (F.i1) h1 ∈ F.V 1 (2 * F.n - 1) :=
        F.mem_V_emk 1 (2 * F.n - 1) (i := F.i1) (by dsimp [i1]; simp) t.val h1 h2
      simpa [blockFam] using hmem




/-- `V r ℓ` is monotone in the prefix length `r`. -/
lemma V_mono_r (F : QData) (ℓ : ℕ) {a b : ℕ} (hab : a ≤ b) : F.V a ℓ ≤ F.V b ℓ := by
  exact Submodule.span_mono (by
    intro v hv
    rcases hv with ⟨i, hi, t, ht, htℓ, rfl⟩
    refine ⟨i, le_trans hi hab, t, ht, htℓ, rfl⟩)

/-- For `1 ≤ r` the subspace `V r (2n-1)` has dimension at least `2n`. -/
lemma V_full_ge (F : QData) (r : ℕ) (hr : 1 ≤ r) : 2 * F.n ≤ Module.finrank ℝ (F.V r (2 * F.n - 1)) := by
  have hb1 : Submodule.span ℝ (Set.range F.blockFam) ≤ F.V r (2 * F.n - 1) := by
    calc
      Submodule.span ℝ (Set.range F.blockFam) ≤ F.V 1 (2 * F.n - 1) :=
        Submodule.span_le.mpr (F.blockFam_subset_V1)
      _ ≤ F.V r (2 * F.n - 1) := by
        exact Submodule.span_mono (by
          intro v hv
          rcases hv with ⟨i, hi, t, ht, htℓ, rfl⟩
          refine ⟨i, le_trans hi hr, t, ht, htℓ, rfl⟩)
  have hfin := finrank_span_eq_card (R := ℝ) (b := F.blockFam) (F.blockFam_linIndep)
  have hmono := Submodule.finrank_mono hb1
  rw [hfin] at hmono
  have hcard : Fintype.card (Fin (F.n - 1 + 1) ⊕ Fin (F.n - 1 + 1)) = 2 * F.n := by
    simp [Fintype.card_sum]
    have hpos : 1 ≤ F.n := F.hn
    omega
  simpa [hcard] using hmono

/-! #### A pure arithmetic form of Lemma 5.2 (Annals, §5) -/

/-- A telescoping lower bound: with steps of size at least `c`, `d n ≥ d 0 + c * n`. -/
lemma nat_bound_of_step {d : ℕ → ℕ} {c n : ℕ}
    (h : ∀ j, j < n → d j + c ≤ d (j + 1)) : d 0 + c * n ≤ d n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hprev : d 0 + c * n ≤ d n := ih (fun j hj => h j (by omega))
      have hlast : d n + c ≤ d (n + 1) := h n (by omega)
      rw [Nat.mul_succ]
      omega

/-- If the sequence of increments is non-increasing, later increments are ≤ earlier ones. -/
lemma decr_chain_aux {g : ℕ → ℕ} (j : ℕ) : ∀ m : ℕ,
    (∀ k, j ≤ k → k < j + m → g (k + 1) ≤ g k) → g (j + m) ≤ g j := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      intro h
      have hstep : g (j + m + 1) ≤ g (j + m) := by
        have hs := h (j + m) (by omega) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
      have hrec : g (j + m) ≤ g j := ih (fun k hk1 hk2 => h k hk1 (by omega))
      exact le_trans hstep hrec

lemma decr_chain {g : ℕ → ℕ} {j m : ℕ} (hjm : j ≤ m)
    (h : ∀ k, j ≤ k → k < m → g (k + 1) ≤ g k) : g m ≤ g j := by
  have h' : ∀ k, j ≤ k → k < j + (m - j) → g (k + 1) ≤ g k := by
    intro k hk1 hk2
    have hklt : k < m := by omega
    exact h k hk1 hklt
  have haux := decr_chain_aux (g := g) j (m - j) h'
  have hdecomp : j + (m - j) = m := Nat.add_sub_of_le hjm
  simpa [hdecomp] using haux

/-- If every step from `a` up to `b` increases by exactly one, the total increase is `b-a`. -/
lemma step_aux {d : ℕ → ℕ} (a : ℕ) : ∀ t : ℕ,
    (∀ u, a ≤ u → u < a + t → d (u + 1) = d u + 1) → d (a + t) = d a + t := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
      intro h
      have hrec : d (a + t) = d a + t := ih (fun u hu1 hu2 => h u hu1 (by omega))
      have hlast : d (a + t + 1) = d (a + t) + 1 := by
        have hs := h (a + t) (by omega) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
      rw [← Nat.add_assoc, hlast, hrec]
      omega

lemma nat_eq_of_step {d : ℕ → ℕ} {a b : ℕ} (hab : a ≤ b)
    (h : ∀ u, a ≤ u → u < b → d (u + 1) = d u + 1) : d b = d a + (b - a) := by
  have h' : ∀ u, a ≤ u → u < a + (b - a) → d (u + 1) = d u + 1 := by
    intro u hu1 hu2
    have hult : u < b := by omega
    exact h u hu1 hult
  have haux := step_aux (d := d) a (b - a) h'
  have hdecomp : a + (b - a) = b := Nat.add_sub_of_le hab
  rwa [hdecomp] at haux

/-- A pure arithmetic version of Lemma 5.2: if `d(0) ≥ r+1`, the `d`-sequence is strictly
increasing with decreasing increments and `2 n0 ≤ d(n0-1)`, then `d(m0) ≥ 2 m0 + r + 1`
whenever `m0 ≤ n0 - r`. -/
lemma annals_seq_bound {n0 r m0 : ℕ} (d : ℕ → ℕ)
    (hr1 : 1 ≤ r) (hm0 : m0 ≤ n0 - r) (hd0 : r + 1 ≤ d 0)
    (hfull : 2 * n0 ≤ d (n0 - 1))
    (hincr : ∀ m, m ≤ n0 - 2 → d m + 1 ≤ d (m + 1))
    (hdecr : ∀ m, 1 ≤ m → m ≤ n0 - 2 → d (m + 1) - d m ≤ d m - d (m - 1)) :
    2 * m0 + (r + 1) ≤ d m0 := by
  by_contra h
  have hlt : d m0 < 2 * m0 + (r + 1) := by omega
  have hm0pos : 0 < m0 := by
    by_contra hz
    have hm0z : m0 = 0 := by omega
    subst m0
    omega
  let m := m0 - 1
  have hmdef : m + 1 = m0 := by dsimp [m]; omega
  have hm_le : m ≤ n0 - 2 := by dsimp [m]; omega
  have hle1 : 1 ≤ m + 1 := by omega
  by_cases hge2 : 2 ≤ d (m + 1) - d m
  · have hall : ∀ j, j < m + 1 → d j + 2 ≤ d (j + 1) := by
      intro j hj
      have hjm : j ≤ m := by omega
      let g : ℕ → ℕ := fun u => d (u + 1) - d u
      have hgd : ∀ k, j ≤ k → k < m → g (k + 1) ≤ g k := by
        intro k hk1 hk2
        dsimp [g]
        exact hdecr (k + 1) (by omega) (by omega)
      have hgm : g m ≤ g j := decr_chain (j := j) (m := m) hjm hgd
      have hg2 : 2 ≤ g j := le_trans hge2 hgm
      have hinc1 : d j + 1 ≤ d (j + 1) := hincr j (by omega)
      dsimp [g] at hg2
      omega
    have htotal := nat_bound_of_step (c := 2) (n := m + 1) (d := d)
      (by intro j hj; exact hall j hj)
    have hd0m : d 0 + 2 * m0 ≤ d m0 := by
      simpa [hmdef, Nat.mul_succ] using htotal
    omega
  · have hinc1m : d (m + 1) - d m = 1 := by
      have hle : d m + 1 ≤ d (m + 1) := hincr m hm_le
      omega
    have hlater : ∀ u, m + 1 ≤ u → u < n0 - 1 → d (u + 1) = d u + 1 := by
      intro u hu1 hu2
      let g : ℕ → ℕ := fun t => d (t + 1) - d t
      have hgd : ∀ k, m + 1 ≤ k → k < u → g (k + 1) ≤ g k := by
        intro k hk1 hk2
        dsimp [g]
        exact hdecr (k + 1) (by omega) (by omega)
      have hcu : g u ≤ g (m + 1) := decr_chain (j := m + 1) (m := u) hu1 hgd
      have hgm1 : g (m + 1) ≤ g m := by
        dsimp [g]
        exact hdecr (m + 1) hle1 (by omega)
      have hle1u : g u ≤ 1 := by
        have htrans : g u ≤ g m := le_trans hcu hgm1
        simpa [g, hinc1m] using htrans
      have hge1 : 1 ≤ g u := by
        have hincu : d u + 1 ≤ d (u + 1) := hincr u (by omega)
        change 1 ≤ d (u + 1) - d u
        omega
      change d (u + 1) = d u + 1
      have h1 : d (u + 1) - d u ≤ 1 := by simpa [g] using hle1u
      have h2 : 1 ≤ d (u + 1) - d u := by simpa [g] using hge1
      omega
    have hdist := nat_eq_of_step (a := m + 1) (b := n0 - 1) (d := d) (by omega) hlater
    have hd2 : d (n0 - 1) = d m0 + (n0 - 1 - m0) := by
      rw [hdist]
      rw [hmdef]
    rw [hd2] at hfull
    omega


/-- The Annals Lemma 5.2 bound, specialized to the prefix `V r (n + m)`. -/
lemma V_prefix_bound (F : QData) (hn2 : 2 ≤ F.n) (r : ℕ) (hr1 : 1 ≤ r) (hr : r ≤ F.k - 1) (m0 : ℕ)
    (hm0 : m0 ≤ F.n - r) :
    2 * m0 + (r + 1) ≤ Module.finrank ℝ (F.V r (F.n + m0)) := by
  let d : ℕ → ℕ := fun m => Module.finrank ℝ (F.V r (F.n + m))
  have hd0 : r + 1 ≤ d 0 := by
    dsimp [d]
    simpa using (F.V_base_rank r hr)
  have hfull : 2 * F.n ≤ d (F.n - 1) := by
    dsimp [d]
    have hlev : F.n + (F.n - 1) = 2 * F.n - 1 := by omega
    rw [hlev]
    exact F.V_full_ge r hr1
  have hincr : ∀ m, m ≤ F.n - 2 → d m + 1 ≤ d (m + 1) := by
    intro m hm
    dsimp [d]
    have hlev : (F.n + m) + 1 = F.n + (m + 1) := by omega
    rw [← hlev]
    exact F.V_rank_incr r (F.n + m) (by omega) (by omega)
  have hdecr : ∀ m, 1 ≤ m → m ≤ F.n - 2 → d (m + 1) - d m ≤ d m - d (m - 1) := by
    intro m hm1 hm2
    dsimp [d]
    have hdec := F.V_rank_incr_decr r (F.n + m) (by omega) (by omega)
    have hlev1 : (F.n + m) + 1 = F.n + (m + 1) := by omega
    have hlev2 : (F.n + m) - 1 = F.n + (m - 1) := by omega
    rw [hlev1, hlev2] at hdec
    simpa using hdec
  change 2 * m0 + (r + 1) ≤ d m0
  exact annals_seq_bound (n0 := F.n) (r := r) (m0 := m0) d hr1 hm0 hd0 hfull hincr hdecr

/-! #### A linear-independence criterion by a nested flag -/

/-- If each later vector of a `Fin`-indexed family lies outside the span of all earlier ones,
the family is linearly independent. -/
lemma fin_linIndep_of_nth_not_mem_span {R : Type*} [Field R] {M : Type*} [AddCommGroup M] [Module R M]
    {n : ℕ} (v : Fin n → M)
    (h : ∀ i : Fin n, v i ∉ Submodule.span R (Set.range (fun j : Fin i.val => v ⟨j, by omega⟩))) :
    LinearIndependent R v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i0
  by_contra hgi0
  let S : Finset (Fin n) := Finset.univ.filter (fun i => g i ≠ 0)
  have hSne : S.Nonempty := ⟨i0, by simp [S, hgi0]⟩
  rcases (Finset.exists_max_image S Fin.val hSne) with ⟨a, haS, hamax⟩
  have hga : g a ≠ 0 := (Finset.mem_filter.mp haS).2
  let rest : M := (Finset.univ.erase a).sum (fun i => g i • v i)
  have hrest : rest ∈ Submodule.span R (Set.range (fun j : Fin a.val => v ⟨j, by omega⟩)) := by
    dsimp [rest]
    apply Submodule.sum_mem
    intro i hi
    by_cases hgi : g i = 0
    · simp [hgi]
    · have hiS : i ∈ S := by simpa [S] using hgi
      have hia_val : i.val ≤ a.val := hamax i hiS
      have hin : i ≠ a := (Finset.mem_erase.mp hi).1
      have hilt : i.val < a.val := by
        have hne : i.val ≠ a.val := by
          intro hh
          apply hin
          apply Fin.ext
          exact hh
        omega
      have hval2 : v i = v ⟨i.val, by omega⟩ := by
        congr 1
      exact Submodule.smul_mem (p := Submodule.span R (Set.range (fun j : Fin a.val => v ⟨j, by omega⟩)))
        (g i) (by
          rw [hval2]
          exact Submodule.subset_span ⟨⟨i.val, by omega⟩, rfl⟩)
  have hsep := Finset.sum_erase_add (s := Finset.univ) (f := fun i => g i • v i) (a := a) (Finset.mem_univ a)
  have hsum0 : g a • v a + rest = 0 := by
    have hg0 : (Finset.univ.erase a).sum (fun i => g i • v i) + g a • v a = 0 := by
      rw [← hsep] at hg
      exact hg
    simpa [rest, add_comm] using hg0
  have hval : v a = (-(g a)⁻¹) • rest := by
    have h1 : (g a)⁻¹ • (g a • v a) = v a := by
      rw [smul_smul, inv_mul_cancel₀ hga, one_smul]
    have h2 : (g a)⁻¹ • (g a • v a + rest) = 0 := by
      rw [hsum0, smul_zero]
    have h2eq : (g a)⁻¹ • (g a • v a + rest) = v a + (g a)⁻¹ • rest := by
      calc
        (g a)⁻¹ • (g a • v a + rest)
            = (g a)⁻¹ • (g a • v a) + (g a)⁻¹ • rest := by rw [smul_add]
        _ = v a + (g a)⁻¹ • rest := by rw [h1]
    have h2'' : v a + (g a)⁻¹ • rest = 0 := by
      rw [← h2eq]
      exact h2
    have h3 : v a = -((g a)⁻¹ • rest) := eq_neg_of_add_eq_zero_left h2''
    calc
      v a = -((g a)⁻¹ • rest) := h3
      _ = (-(g a)⁻¹) • rest := by simp [neg_smul]
  have hmem : v a ∈ Submodule.span R (Set.range (fun j : Fin a.val => v ⟨j, by omega⟩)) := by
    rw [hval]
    exact Submodule.smul_mem (p := Submodule.span R (Set.range (fun j : Fin a.val => v ⟨j, by omega⟩)))
      (-(g a)⁻¹) hrest
  exact h a hmem



/-! #### Construction of the complete family inside the ambient module -/

/-- `M = n + 2 - k` : the number of shifts of each of the first two polynomials. -/
abbrev M0 (F : QData) := F.n + 2 - F.k

/-- `D = 2n - k + 1` : the degree ceiling. -/
abbrev D0 (F : QData) := 2 * F.n - F.k + 1

lemma M0_pos (F : QData) : 1 ≤ F.M0 := by
  dsimp [M0]
  have hkn : F.k ≤ F.n + 1 := F.hkn
  omega

lemma D0_eq_n_add_M0_sub (F : QData) : F.D0 = F.n + (F.M0 - 1) := by
  dsimp [D0, M0]
  have hkn : F.k ≤ F.n + 1 := F.hkn
  have hk2 : 2 ≤ F.k := F.hk2
  omega

/-- The `2M` first elements of the family: `X^t q0` and `X^t q1` for `t < M`. -/
def sblock (F : QData) : Fin (2 * F.M0) → F.E := fun a =>
  if ha : a.val < F.M0 then
    F.emk a.val (F.i0) (by
      have hdeg : (F.q (F.i0)).natDegree = F.n := F.hdeg0
      rw [hdeg]
      have hM : F.M0 ≤ F.n := by
        dsimp [M0]
        have hk2 : 2 ≤ F.k := F.hk2
        omega
      have hpos : 1 ≤ F.M0 := by
        dsimp [M0]
        have hkn : F.k ≤ F.n + 1 := F.hkn
        omega
      omega)
  else
    F.emk (a.val - F.M0) (F.i1) (by
      have hdeg : (F.q (F.i1)).natDegree = F.n := F.hdeg1
      rw [hdeg]
      have hb : F.M0 ≤ a.val := by omega
      have hM : F.M0 ≤ F.n := by
        dsimp [M0]
        have hk2 : 2 ≤ F.k := F.hk2
        omega
      have hpos : 1 ≤ F.M0 := by
        dsimp [M0]
        have hkn : F.k ≤ F.n + 1 := F.hkn
        omega
      omega)

abbrev NN (F : QData) := 2 * F.M0 + (F.k - 2)


/-- If `A ≤ B` and `A` has smaller dimension than `B`, some element of `B` is not in `A`. -/
lemma submodule_exists_of_finrank_lt {K : Type*} [Field K] {E : Type*} [AddCommGroup E]
    [Module K E] [Module.Finite K E] {A B : Submodule K E} (hAB : A ≤ B)
    (hdim : Module.finrank K A < Module.finrank K B) : ∃ v : E, v ∈ B ∧ v ∉ A := by
  classical
  have hne : A ≠ B := by
    intro heq
    have hfin : Module.finrank K A = Module.finrank K B := by rw [heq]
    omega
  by_contra h
  push_neg at h
  have hBA : B ≤ A := by
    intro v hv
    exact h v hv
  exact hne (le_antisymm hAB hBA)


lemma D0_sub_n (F : QData) : F.D0 - F.n = F.M0 - 1 := by
  dsimp [D0, M0]
  have hkn : F.k ≤ F.n + 1 := F.hkn
  have hk2 : 2 ≤ F.k := F.hk2
  omega

lemma D0_lt_2n (F : QData) : F.D0 < 2 * F.n := by
  dsimp [D0]
  have hk2 : 2 ≤ F.k := F.hk2
  have hkn : F.k ≤ F.n + 1 := F.hkn
  omega

/-- The element `X^t q_i` with `natDegree + t ≤ D0`. -/
def emkOf (F : QData) (i : Fin F.k) (t : ℕ) (ht : (F.q i).natDegree + t ≤ F.D0) : F.E :=
  F.emk t i (lt_of_le_of_lt ht (F.D0_lt_2n))

/-- The block values lie in `V 1 (D0)`. -/
lemma sblock_mem_V1 (F : QData) (a : Fin (2 * F.M0)) : F.sblock a ∈ F.V 1 F.D0 := by
  have hk2 : 2 ≤ F.k := F.hk2
  have hkn : F.k ≤ F.n + 1 := F.hkn
  have hpos : 1 ≤ F.M0 := F.M0_pos
  have hM : F.M0 ≤ F.n := by
    dsimp [M0]
    omega
  dsimp [sblock]
  by_cases ha : a.val < F.M0
  · rw [dif_pos ha]
    have hdeg : (F.q (F.i0)).natDegree = F.n := F.hdeg0
    exact F.mem_V_emk 1 F.D0 (i := F.i0) (by dsimp [i0]; simp) a.val
      (by rw [hdeg]; omega)
      (by
        rw [hdeg, F.D0_sub_n]
        omega)
  · rw [dif_neg ha]
    have hdeg : (F.q (F.i1)).natDegree = F.n := F.hdeg1
    exact F.mem_V_emk 1 F.D0 (i := F.i1) (by dsimp [i1]; simp) (a.val - F.M0)
      (by rw [hdeg]; omega)
      (by
        rw [hdeg, F.D0_sub_n]
        omega)

/-- Generators with index `≤ 1` at level `D0` belong to the span of the block family. -/
lemma gen_le1_mem_block {F : QData} {i : Fin F.k} (hi : i.val ≤ 1) {t : ℕ}
    (ht : (F.q i).natDegree + t < 2 * F.n) (htℓ : t ≤ F.D0 - (F.q i).natDegree) :
    F.emk t i ht ∈ Submodule.span ℝ (Set.range F.sblock) := by
  classical
  by_cases hi0 : i.val = 0
  · have hi_eq : i = F.i0 := by
      apply Fin.ext
      simp [i0, hi0]
    have hdeg0 : (F.q i).natDegree = F.n := by rw [hi_eq]; exact F.hdeg0
    have htl0 : t ≤ F.D0 - F.n := by
      rw [hdeg0] at htℓ
      simpa using htℓ
    have htlM : t < F.M0 := by
      have hpos : 1 ≤ F.M0 := F.M0_pos
      rw [F.D0_sub_n] at htl0
      omega
    let a : Fin (2 * F.M0) := ⟨t, by omega⟩
    have hsa : F.sblock a = F.emk t i ht := by
      dsimp [sblock, a]
      rw [dif_pos htlM]
      apply Subtype.ext
      simpa [hi_eq]
    rw [← hsa]
    exact Submodule.subset_span ⟨a, rfl⟩
  · have hi1 : i.val = 1 := by omega
    have hi_eq : i = F.i1 := by
      apply Fin.ext
      simp [i1, hi1]
    have hdeg1 : (F.q i).natDegree = F.n := by rw [hi_eq]; exact F.hdeg1
    have htl0 : t ≤ F.D0 - F.n := by
      rw [hdeg1] at htℓ
      simpa using htℓ
    have htlM : t < F.M0 := by
      have hpos : 1 ≤ F.M0 := F.M0_pos
      rw [F.D0_sub_n] at htl0
      omega
    let a : Fin (2 * F.M0) := ⟨F.M0 + t, by omega⟩
    have hsa : F.sblock a = F.emk t i ht := by
      dsimp [sblock, a]
      rw [dif_neg (by omega : ¬ F.M0 + t < F.M0)]
      apply Subtype.ext
      change X ^ (F.M0 + t - F.M0) * F.q (F.i1) = X ^ t * F.q i
      have hsub : F.M0 + t - F.M0 = t := by omega
      rw [hsub]
      simpa [hi_eq]
    rw [← hsa]
    exact Submodule.subset_span ⟨a, rfl⟩

/-- The set of the first `2M` block vectors. -/
def blockSet (F : QData) : Set F.E := Set.range F.sblock

/-- The dimension of the span of the block vectors is at most `2M`. -/
lemma finrank_blockSet_le (F : QData) : Module.finrank ℝ (Submodule.span ℝ (F.blockSet)) ≤ 2 * F.M0 := by
  have h := finrank_range_le_card (R := ℝ) (b := F.sblock)
  have hc : Fintype.card (Fin (2 * F.M0)) = 2 * F.M0 := by simp
  change (Set.range F.sblock).finrank ℝ ≤ 2 * F.M0
  rwa [hc] at h


/-- Extras of length `c` with the index constraints and nested-independence. -/
def ExtraProp (F : QData) (c : ℕ) : Prop :=
  ∃ e : Fin c → F.E,
    (∀ j : Fin c, ∃ i : Fin F.k, 2 ≤ i.val ∧ i.val ≤ j.val + 2 ∧
      ∃ t : ℕ, ∃ hdeg : (F.q i).natDegree + t ≤ F.D0,
        e j = F.emkOf i t hdeg) ∧
    (∀ j : Fin c, e j ∉ Submodule.span ℝ (F.blockSet ∪ Set.range (fun u : Fin j.val => e ⟨u.val, by omega⟩)))

/-- The span of the block vectors is contained in `V r (D0)` for `1 ≤ r`. -/
lemma blockSpan_le_V (F : QData) {r : ℕ} (hr : 1 ≤ r) :
    Submodule.span ℝ (F.blockSet) ≤ F.V r F.D0 := by
  have h1 : Submodule.span ℝ (F.blockSet) ≤ F.V 1 F.D0 := by
    exact Submodule.span_le.mpr (by
      intro v hv
      rcases hv with ⟨a, rfl⟩
      exact F.sblock_mem_V1 a)
  exact le_trans h1 (F.V_mono_r F.D0 hr)

/-- Given a `c`-extra family, every member lies in `V (c+2) (D0)`. -/
lemma extras_mem_V (F : QData) {c : ℕ} {e : Fin c → F.E}
    (hwit : ∀ j : Fin c, ∃ i : Fin F.k, 2 ≤ i.val ∧ i.val ≤ j.val + 2 ∧
      ∃ t : ℕ, ∃ hdeg : (F.q i).natDegree + t ≤ F.D0, e j = F.emkOf i t hdeg)
    (j : Fin c) : e j ∈ F.V (c + 2) F.D0 := by
  rcases hwit j with ⟨i, hi2, hile, t, hdeg, heq⟩
  rw [heq]
  -- emkOf i t hdeg = emk t i (lt_of_le_of_lt hdeg (D0_lt_2n))
  exact F.mem_V_emk (c + 2) F.D0 (i := i) (by have hj : j.val < c := j.isLt; omega) t
    (by exact lt_of_le_of_lt hdeg (F.D0_lt_2n))
    (by
      have hdeg' : (F.q i).natDegree + t ≤ F.D0 := hdeg
      omega)



/-- Produce the next extra: an element of `V (c+2)(D0)` outside the span of the blocks and the
previous extras, given by an `X^t q_i` with `2 ≤ i.val ≤ c+2` and `natDegree + t ≤ D0`. -/
lemma exists_new_extra (F : QData) (hn2 : 2 ≤ F.n) (c : ℕ) (hc : c + 2 ≤ F.k - 1)
    {e : Fin c → F.E}
    (hwit : ∀ j : Fin c, ∃ i : Fin F.k, 2 ≤ i.val ∧ i.val ≤ j.val + 2 ∧
        ∃ t : ℕ, ∃ hdeg : (F.q i).natDegree + t ≤ F.D0, e j = F.emkOf i t hdeg) :
    ∃ (g : F.E) (i : Fin F.k) (hi2 : 2 ≤ i.val) (hile : i.val ≤ c + 2)
      (t : ℕ) (hdeg : (F.q i).natDegree + t ≤ F.D0),
        g = F.emkOf i t hdeg ∧
        g ∉ Submodule.span ℝ (F.blockSet ∪ Set.range e) := by
  classical
  have hk2 : 2 ≤ F.k := F.hk2
  have hkn : F.k ≤ F.n + 1 := F.hkn
  have hn1 : 1 ≤ F.n := F.hn
  let r : ℕ := c + 2
  have hr1 : 1 ≤ r := by dsimp [r]; omega
  have hrk : r ≤ F.k - 1 := by dsimp [r]; simpa [r] using hc
  have hm0 : F.M0 - 1 ≤ F.n - r := by
    have hle1 : c + 2 ≤ F.k - 1 := hc
    have hle2 : c + 2 ≤ F.n := by
      exact le_trans hc (by omega)
    have hk : F.k - 1 ≤ F.n := by
      have hkn' : F.k ≤ F.n + 1 := hkn
      omega
    dsimp [r, M0]
    omega
  have hb := F.V_prefix_bound hn2 r hr1 hrk (F.M0 - 1) hm0
  have hbD : 2 * F.M0 + c + 1 ≤ Module.finrank ℝ (F.V r F.D0) := by
    have hlv : F.n + (F.M0 - 1) = F.D0 := F.D0_eq_n_add_M0_sub |>.symm
    have hlv' : F.V r (F.n + (F.M0 - 1)) = F.V r F.D0 := by rw [hlv]
    dsimp [r] at hb
    rw [hlv'] at hb
    omega
  let W : Submodule ℝ F.E := Submodule.span ℝ (F.blockSet ∪ Set.range e)
  have hblock : Submodule.span ℝ (F.blockSet) ≤ W := by
    dsimp [W]
    exact Submodule.span_mono (by intro x hx; exact Or.inl hx)
  have hWsup : W ≤ Submodule.span ℝ (F.blockSet) ⊔ Submodule.span ℝ (Set.range e) := by
    dsimp [W]
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with h1 | h2
    · exact Submodule.mem_sup_left (Submodule.subset_span h1)
    · exact Submodule.mem_sup_right (Submodule.subset_span h2)
  have hdimW : Module.finrank ℝ W ≤ 2 * F.M0 + c := by
    have h1 : Module.finrank ℝ (Submodule.span ℝ (Set.range e)) ≤ c := by
      have hf := finrank_range_le_card (R := ℝ) (b := e)
      have hc' : Fintype.card (Fin c) = c := by simp
      change (Set.range e).finrank ℝ ≤ c
      rwa [hc'] at hf
    have hsum := Submodule.finrank_add_le_finrank_add_finrank
      (Submodule.span ℝ (F.blockSet)) (Submodule.span ℝ (Set.range e))
    have hb2 := F.finrank_blockSet_le
    have hmonoW := Submodule.finrank_mono hWsup
    omega
  have hWV : W ≤ F.V r F.D0 := by
    intro v hv
    have hspan : Submodule.span ℝ (F.blockSet ∪ Set.range e) ≤ F.V r F.D0 := by
      apply Submodule.span_le.mpr
      intro x hx
      rcases hx with hx1 | hx2
      · exact (F.blockSpan_le_V hr1) (Submodule.subset_span hx1)
      · rcases hx2 with ⟨u, rfl⟩
        exact F.extras_mem_V hwit u
    exact hspan hv
  have hVgt : Module.finrank ℝ W < Module.finrank ℝ (F.V r F.D0) := by omega
  rcases submodule_exists_of_finrank_lt (K := ℝ) (A := W) (B := F.V r F.D0) hWV hVgt with ⟨v, hvV, hvW⟩
  have hgen : ∃ g : F.E, g ∈ F.gens r F.D0 ∧ g ∉ W := by
    by_contra hnone
    push_neg at hnone
    have hVW : F.V r F.D0 ≤ W := by
      change Submodule.span ℝ (F.gens r F.D0) ≤ W
      rw [Submodule.span_le]
      intro g hg
      exact hnone g hg
    exact hvW (hVW hvV)
  rcases hgen with ⟨g, hggens, hgW⟩
  rcases hggens with ⟨i, hi, t, ht, htℓ, hg_eq⟩
  have hge2 : 2 ≤ i.val := by
    by_contra hle
    have hmem := gen_le1_mem_block (i := i) (by omega) ht htℓ
    exact hgW (hblock (by simpa [blockSet, ← hg_eq] using hmem))
  have hD_deg : (F.q i).natDegree ≤ F.D0 := le_trans (F.hdeg i) (by
    dsimp [D0]
    omega)
  have hdeg : (F.q i).natDegree + t ≤ F.D0 := by omega
  have heqG : g = F.emkOf i t hdeg := by
    rw [hg_eq]
    apply Subtype.ext
    rfl
  refine ⟨g, i, hge2, (by simpa [r] using hi), t, hdeg, heqG, ?_⟩
  simpa [W] using hgW


/-- Existence of `c` extras with the index constraints and nested independence. -/
lemma exists_extras (F : QData) (c : ℕ) : c ≤ F.k - 2 → F.ExtraProp c := by
  intro hc
  classical
  induction c with
  | zero =>
      let e : Fin 0 → F.E := Fin.elim0
      refine ⟨e, ?_, ?_⟩
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
  | succ m ih =>
      have hk2 : 2 ≤ F.k := F.hk2
      have hkn : F.k ≤ F.n + 1 := F.hkn
      have hc1 : m + 1 ≤ F.k - 2 := hc
      have hn2 : 2 ≤ F.n := by omega
      have hc_m : m ≤ F.k - 2 := by omega
      rcases ih hc_m with ⟨e, hwit, hout⟩
      have hcE : m + 2 ≤ F.k - 1 := by omega
      rcases exists_new_extra F hn2 m hcE hwit with ⟨g, i, hi2, hile, t, hdeg, heqG, hgW⟩
      let e' : Fin (m + 1) → F.E := fun j => if hjm : j.val < m then e ⟨j.val, hjm⟩ else g
      refine ⟨e', ?_, ?_⟩
      · intro j
        by_cases hjm : j.val < m
        · rcases hwit ⟨j.val, hjm⟩ with ⟨i2, hi2b, hileb, t2, hdeg2, heq2⟩
          refine ⟨i2, hi2b, hileb, t2, hdeg2, ?_⟩
          have he' : e' j = e ⟨j.val, hjm⟩ := by
            dsimp [e']
            rw [dif_pos hjm]
          rw [he']
          exact heq2
        · have hjm_eq : j.val = m := by omega
          refine ⟨i, hi2, ?_, t, hdeg, ?_⟩
          · have : i.val ≤ j.val + 2 := by omega
            exact this
          · have he' : e' j = g := by
              dsimp [e']
              rw [dif_neg hjm]
            rw [he']
            exact heqG
      · intro j
        by_cases hjm : j.val < m
        · have he' : e' j = e ⟨j.val, hjm⟩ := by
            dsimp [e']
            rw [dif_pos hjm]
          have hprefix : (Set.range (fun u : Fin j.val => e' ⟨u.val, by omega⟩)) =
              Set.range (fun u : Fin j.val => e ⟨u.val, by omega⟩) := by
            apply Set.Subset.antisymm <;> intro x hx
            · rcases hx with ⟨u, rfl⟩
              refine ⟨u, ?_⟩
              have hu : u.val < m := by omega
              dsimp [e']
              rw [dif_pos hu]
            · rcases hx with ⟨u, rfl⟩
              refine ⟨u, ?_⟩
              have hu : u.val < m := by omega
              dsimp [e']
              rw [dif_pos hu]
          rw [he', hprefix]
          exact hout ⟨j.val, hjm⟩
        · have hjm_eq : j.val = m := by omega
          have he' : e' j = g := by
            dsimp [e']
            rw [dif_neg hjm]
          rw [he']
          intro hg
          have hpre : (Set.range (fun u : Fin j.val => e' ⟨u.val, by omega⟩)) ⊆ Set.range e := by
            intro x hx
            rcases hx with ⟨u, rfl⟩
            refine ⟨⟨u.val, by omega⟩, ?_⟩
            have hu : u.val < m := by omega
            dsimp [e']
            rw [dif_pos hu]
          have hg2 : g ∈ Submodule.span ℝ (F.blockSet ∪ Set.range e) := by
            have hmono1 : Submodule.span ℝ (F.blockSet ∪ Set.range (fun u : Fin j.val => e' ⟨u.val, by omega⟩)) ≤
                Submodule.span ℝ (F.blockSet ∪ Set.range e) := by
              exact Submodule.span_mono (by
                intro x hx
                rcases hx with h1 | h2
                · exact Or.inl h1
                · exact Or.inr (hpre h2))
            exact hmono1 hg
          exact hgW hg2



/-! #### The complete family `S`: blocks and extras, and its linear independence -/

/-- Embed a shift index `< M0` into the index set of the full block family (of length `n`). -/
def eblockIdx (F : QData) (u : Fin F.M0) : Fin (F.n - 1 + 1) :=
  ⟨u.val, by
    have hn1 : 1 ≤ F.n := F.hn
    have hM : F.M0 ≤ F.n := by
      dsimp [M0]
      have hk2 : 2 ≤ F.k := F.hk2
      omega
    have hlt : u.val < F.n := lt_of_lt_of_le u.isLt hM
    omega⟩

/-- The two shifted blocks of length `M0`: `X^t q0` and `X^t q1` for `t < M0`. -/
def eblock (F : QData) : Fin F.M0 ⊕ Fin F.M0 → F.E := fun a =>
  F.blockFam (Sum.map (F.eblockIdx) (F.eblockIdx) a)

/-- The `M0`-shifted block family is linearly independent. -/
lemma eblock_linIndep (F : QData) : LinearIndependent ℝ F.eblock := by
  have hφ : Function.Injective (F.eblockIdx) := by
    intro a b h
    apply Fin.ext
    simpa [eblockIdx] using congrArg Fin.val h
  have hmap : Function.Injective (Sum.map F.eblockIdx F.eblockIdx) :=
    (Sum.map_injective (f := F.eblockIdx) (g := F.eblockIdx)).2 ⟨hφ, hφ⟩
  have hlin : LinearIndependent ℝ (fun a : Fin F.M0 ⊕ Fin F.M0 =>
      F.blockFam (Sum.map F.eblockIdx F.eblockIdx a)) := by
    exact F.blockFam_linIndep.comp (Sum.map F.eblockIdx F.eblockIdx) hmap
  change LinearIndependent ℝ (fun a : Fin F.M0 ⊕ Fin F.M0 =>
      F.blockFam (Sum.map F.eblockIdx F.eblockIdx a))
  exact hlin

/-- The value of an `inl` block element. -/
lemma eblock_inl_eq (F : QData) (u : Fin F.M0) :
    F.eblock (Sum.inl u) = F.emk u.val (F.i0) (by
      have hdeg : (F.q (F.i0)).natDegree = F.n := F.hdeg0
      rw [hdeg]
      have hpos : 1 ≤ F.M0 := F.M0_pos
      have hM : F.M0 ≤ F.n := by
        dsimp [M0]
        have hk2 : 2 ≤ F.k := F.hk2
        omega
      omega) := by
  simp [eblock, blockFam, eblockIdx]

/-- The value of an `inr` block element. -/
lemma eblock_inr_eq (F : QData) (u : Fin F.M0) :
    F.eblock (Sum.inr u) = F.emk u.val (F.i1) (by
      have hdeg : (F.q (F.i1)).natDegree = F.n := F.hdeg1
      rw [hdeg]
      have hpos : 1 ≤ F.M0 := F.M0_pos
      have hM : F.M0 ≤ F.n := by
        dsimp [M0]
        have hk2 : 2 ≤ F.k := F.hk2
        omega
      omega) := by
  simp [eblock, blockFam, eblockIdx]

/-- A `q0`-shift of the interleaved block equals the corresponding `inl` element. -/
lemma sblock_eq_eblock_inl (F : QData) {a : ℕ} (ha : a < 2 * F.M0) (haM : a < F.M0) :
    F.sblock ⟨a, ha⟩ = F.eblock (Sum.inl (⟨a, haM⟩ : Fin F.M0)) := by
  rw [F.eblock_inl_eq ⟨a, haM⟩]
  dsimp [sblock]
  rw [dif_pos haM]

/-- A `q1`-shift of the interleaved block equals the corresponding `inr` element. -/
lemma sblock_eq_eblock_inr (F : QData) {a : ℕ} (ha : a < 2 * F.M0) (haM : F.M0 ≤ a) :
    F.sblock ⟨a, ha⟩ = F.eblock (Sum.inr (⟨a - F.M0, by omega⟩ : Fin F.M0)) := by
  rw [F.eblock_inr_eq ⟨a - F.M0, by omega⟩]
  dsimp [sblock]
  rw [dif_neg (by omega : ¬ a < F.M0)]



/-- The complete family: the `2M0` block vectors followed by the `k-2` extras. -/
def compFam (F : QData) (e : Fin (F.k - 2) → F.E) : Fin (2 * F.n - F.k + 2) → F.E := fun ℓ =>
  if hℓ : ℓ.val < 2 * F.M0 then
    F.sblock ⟨ℓ.val, hℓ⟩
  else
    e ⟨ℓ.val - 2 * F.M0, by
      have hk2 : 2 ≤ F.k := F.hk2
      have hkn : F.k ≤ F.n + 1 := F.hkn
      have hN : ℓ.val < 2 * F.n - F.k + 2 := ℓ.isLt
      have hge : 2 * F.M0 ≤ ℓ.val := by omega
      dsimp [M0] at hge hN ⊢
      omega⟩

/-- The `q0`-part of a block element is not in the span of the preceding block elements. -/
lemma sblock_notMem_prev_left (F : QData) (a : ℕ) (ha2 : a < 2 * F.M0) (haM : a < F.M0) :
    F.sblock ⟨a, ha2⟩ ∉ Submodule.span ℝ
      (Set.range (fun u : Fin a => F.sblock ⟨u.val, by omega⟩)) := by
  classical
  let a0 : Fin F.M0 ⊕ Fin F.M0 := Sum.inl (⟨a, haM⟩ : Fin F.M0)
  have h0 := LinearIndependent.notMem_span (F.eblock_linIndep) (i := a0)
  intro hmem
  have hE : F.sblock ⟨a, ha2⟩ = F.eblock a0 := F.sblock_eq_eblock_inl ha2 haM
  have hsub : (Set.range (fun u : Fin a => F.sblock ⟨u.val, by omega⟩)) ⊆
      F.eblock '' ({a0}ᶜ) := by
    intro x hx
    rcases hx with ⟨u, rfl⟩
    have huM : u.val < F.M0 := by omega
    have hne : Sum.inl (⟨u.val, huM⟩ : Fin F.M0) ≠ a0 := by
      dsimp [a0]
      intro hh
      injection hh with hv
      have hvv : u.val = a := congrArg Fin.val hv
      omega
    exact ⟨Sum.inl (⟨u.val, huM⟩ : Fin F.M0), hne,
      (F.sblock_eq_eblock_inl (by omega : u.val < 2 * F.M0) huM).symm⟩
  rw [hE] at hmem
  exact h0 (by
    have hspan : Submodule.span ℝ (Set.range (fun u : Fin a => F.sblock ⟨u.val, by omega⟩)) ≤
        Submodule.span ℝ (F.eblock '' ({a0}ᶜ)) := Submodule.span_mono hsub
    exact hspan hmem)

/-- The `q1`-part of a block element is not in the span of the preceding block elements. -/
lemma sblock_notMem_prev_right (F : QData) (a : ℕ) (ha2 : a < 2 * F.M0) (haM : F.M0 ≤ a) :
    F.sblock ⟨a, ha2⟩ ∉ Submodule.span ℝ
      (Set.range (fun u : Fin a => F.sblock ⟨u.val, by omega⟩)) := by
  classical
  let t : ℕ := a - F.M0
  have htM : t < F.M0 := by dsimp [t]; omega
  let a0 : Fin F.M0 ⊕ Fin F.M0 := Sum.inr (⟨t, htM⟩ : Fin F.M0)
  have h0 := LinearIndependent.notMem_span (F.eblock_linIndep) (i := a0)
  intro hmem
  have hE : F.sblock ⟨a, ha2⟩ = F.eblock a0 := by
    simpa [a0, t] using (F.sblock_eq_eblock_inr ha2 haM)
  have hsub : (Set.range (fun u : Fin a => F.sblock ⟨u.val, by omega⟩)) ⊆
      F.eblock '' ({a0}ᶜ) := by
    intro x hx
    rcases hx with ⟨u, rfl⟩
    by_cases huM : u.val < F.M0
    · -- q0-part: inl, never equal to inr
      have hne : Sum.inl (⟨u.val, huM⟩ : Fin F.M0) ≠ a0 := by
        dsimp [a0]
        simp
      exact ⟨Sum.inl (⟨u.val, huM⟩ : Fin F.M0), hne,
        (F.sblock_eq_eblock_inl (by omega : u.val < 2 * F.M0) huM).symm⟩
    · -- q1-part with exponent u.val - M0 < t
      have hge : F.M0 ≤ u.val := by omega
      have hvt : u.val - F.M0 < t := by
        dsimp [t]
        omega
      have hvt' : u.val - F.M0 < F.M0 := lt_trans hvt htM
      have hne : Sum.inr (⟨u.val - F.M0, hvt'⟩ : Fin F.M0) ≠ a0 := by
        dsimp [a0]
        intro hh
        injection hh with hv
        have hvv : u.val - F.M0 = t := congrArg Fin.val hv
        dsimp [t] at hvv
        omega
      exact ⟨Sum.inr (⟨u.val - F.M0, hvt'⟩ : Fin F.M0), hne,
        (F.sblock_eq_eblock_inr (by omega : u.val < 2 * F.M0) hge).symm⟩
  rw [hE] at hmem
  exact h0 (by
    have hspan : Submodule.span ℝ (Set.range (fun u : Fin a => F.sblock ⟨u.val, by omega⟩)) ≤
        Submodule.span ℝ (F.eblock '' ({a0}ᶜ)) := Submodule.span_mono hsub
    exact hspan hmem)

/-- Each block element of the complete family lies outside the span of the preceding ones. -/
lemma sblock_notMem_prev (F : QData) (a : ℕ) (ha2 : a < 2 * F.M0) :
    F.sblock ⟨a, ha2⟩ ∉ Submodule.span ℝ
      (Set.range (fun u : Fin a => F.sblock ⟨u.val, by omega⟩)) := by
  by_cases haM : a < F.M0
  · exact F.sblock_notMem_prev_left a ha2 haM
  · exact F.sblock_notMem_prev_right a ha2 (by omega)

/-- An extra of the complete family lies outside the span of the preceding elements. -/
lemma compFam_extra_notMem_prev (F : QData) (e : Fin (F.k - 2) → F.E)
    (hout : ∀ j : Fin (F.k - 2), e j ∉ Submodule.span ℝ
      (F.blockSet ∪ Set.range (fun u : Fin j.val => e ⟨u.val, by omega⟩)))
    (ℓ : ℕ) (hℓ : ℓ < 2 * F.n - F.k + 2) (hℓ2 : 2 * F.M0 ≤ ℓ) :
    F.compFam e ⟨ℓ, hℓ⟩ ∉ Submodule.span ℝ
      (Set.range (fun u : Fin ℓ => F.compFam e ⟨u.val, by omega⟩)) := by
  classical
  let j0 : ℕ := ℓ - 2 * F.M0
  have hj0 : j0 < F.k - 2 := by
    have hk2 : 2 ≤ F.k := F.hk2
    have hkn : F.k ≤ F.n + 1 := F.hkn
    dsimp [j0]
    dsimp [M0] at hℓ hℓ2 ⊢
    omega
  have hcomp : F.compFam e ⟨ℓ, hℓ⟩ = e ⟨j0, hj0⟩ := by
    dsimp [compFam]
    rw [dif_neg (by omega : ¬ ℓ < 2 * F.M0)]
  have hsub : (Set.range (fun u : Fin ℓ => F.compFam e ⟨u.val, by omega⟩)) ⊆
      F.blockSet ∪ Set.range (fun u : Fin j0 => e ⟨u.val, by omega⟩) := by
    intro x hx
    rcases hx with ⟨u, rfl⟩
    by_cases hu2 : u.val < 2 * F.M0
    · left
      have hval : F.compFam e ⟨u.val, by omega⟩ = F.sblock ⟨u.val, hu2⟩ := by
        simp [compFam, hu2]
      change F.compFam e ⟨u.val, by omega⟩ ∈ F.blockSet
      rw [hval]
      exact ⟨⟨u.val, hu2⟩, rfl⟩
    · right
      have hge : 2 * F.M0 ≤ u.val := by omega
      have hval : F.compFam e ⟨u.val, by omega⟩ = e ⟨u.val - 2 * F.M0, by omega⟩ := by
        simp [compFam, (by omega : ¬ u.val < 2 * F.M0)]
      change F.compFam e ⟨u.val, by omega⟩ ∈ Set.range (fun u : Fin j0 => e ⟨u.val, by omega⟩)
      rw [hval]
      refine ⟨⟨u.val - 2 * F.M0, by dsimp [j0]; omega⟩, rfl⟩
  intro hmem
  have hmem2 : e ⟨j0, hj0⟩ ∈ Submodule.span ℝ
      (F.blockSet ∪ Set.range (fun u : Fin j0 => e ⟨u.val, by omega⟩)) := by
    have hspan : Submodule.span ℝ (Set.range (fun u : Fin ℓ => F.compFam e ⟨u.val, by omega⟩)) ≤
        Submodule.span ℝ (F.blockSet ∪ Set.range (fun u : Fin j0 => e ⟨u.val, by omega⟩)) :=
      Submodule.span_mono hsub
    rw [hcomp] at hmem
    exact hspan hmem
  exact hout ⟨j0, hj0⟩ hmem2



/-- Polynomial value of a `q0` block element. -/
lemma sblock_poly_left (F : QData) {a : ℕ} (ha2 : a < 2 * F.M0) (haM : a < F.M0) :
    ((F.sblock ⟨a, ha2⟩ : F.E) : Polynomial ℝ) = X ^ a * F.q (F.i0) := by
  dsimp [sblock]
  rw [dif_pos haM]
  rfl

/-- Polynomial value of a `q1` block element. -/
lemma sblock_poly_right (F : QData) {a : ℕ} (ha2 : a < 2 * F.M0) (haM : F.M0 ≤ a) :
    ((F.sblock ⟨a, ha2⟩ : F.E) : Polynomial ℝ) = X ^ (a - F.M0) * F.q (F.i1) := by
  dsimp [sblock]
  rw [dif_neg (by omega : ¬ a < F.M0)]
  rfl

/-- The complete family is linearly independent provided every extra avoids the span of the
block vectors together with the earlier extras. -/
lemma compFam_linIndep (F : QData) (e : Fin (F.k - 2) → F.E)
    (hout : ∀ j : Fin (F.k - 2), e j ∉ Submodule.span ℝ
      (F.blockSet ∪ Set.range (fun u : Fin j.val => e ⟨u.val, by omega⟩))) :
    LinearIndependent ℝ (F.compFam e) := by
  classical
  apply fin_linIndep_of_nth_not_mem_span
  intro ℓ
  by_cases hℓb : ℓ.val < 2 * F.M0
  · have hrest : (Set.range (fun u : Fin ℓ.val => F.compFam e ⟨u.val, by omega⟩)) =
        (Set.range (fun u : Fin ℓ.val => F.sblock ⟨u.val, by omega⟩)) := by
      apply Set.Subset.antisymm <;> intro x hx <;> rcases hx with ⟨u, rfl⟩ <;> refine ⟨u, ?_⟩
      · have hu : u.val < 2 * F.M0 := by omega
        simp [compFam, hu]
      · have hu : u.val < 2 * F.M0 := by omega
        simp [compFam, hu]
    have h1 : F.compFam e ℓ = F.sblock ⟨ℓ.val, hℓb⟩ := by
      dsimp [compFam]
      rw [dif_pos hℓb]
    rw [h1, hrest]
    exact F.sblock_notMem_prev ℓ.val hℓb
  · have hℓ2 : 2 * F.M0 ≤ ℓ.val := by omega
    exact F.compFam_extra_notMem_prev e hout ℓ.val ℓ.isLt hℓ2


end QData

open QData

/-! ## The complete-family theorem -/

theorem p51_complete_family (n k : ℕ) (hn : 1 ≤ n) (hk2 : 2 ≤ k) (hkn : k ≤ n + 1) :
    ∀ (q : Fin k → Polynomial ℝ),
      (∀ i : Fin k, (q i).natDegree ≤ n) →
      (q ⟨0, by omega⟩).natDegree = n →
      (q ⟨1, by omega⟩).natDegree = n →
      IsCoprime (q ⟨0, by omega⟩) (q ⟨1, by omega⟩) →
      LinearIndependent ℝ q →
      ∃ S : Fin (2 * n - k + 2) → Polynomial ℝ,
        (∀ ℓ : Fin (2 * n - k + 2), ℓ.val < n + 2 - k →
            S ℓ = Polynomial.X ^ ℓ.val * q ⟨0, by omega⟩) ∧
        (∀ ℓ : Fin (2 * n - k + 2), n + 2 - k ≤ ℓ.val →
            ℓ.val < 2 * (n + 2 - k) →
            S ℓ = Polynomial.X ^ (ℓ.val - (n + 2 - k)) * q ⟨1, by omega⟩) ∧
        (∀ j : Fin (k - 2), ∃ i : Fin k, 2 ≤ i.val ∧ i.val ≤ j.val + 2 ∧
            ∃ t : ℕ, (q i).natDegree + t ≤ 2 * n - k + 1 ∧
            S ⟨2 * (n + 2 - k) + j.val, by have hj : j.val < k - 2 := j.isLt; omega⟩ =
              Polynomial.X ^ t * q i) ∧
        LinearIndependent ℝ S := by
  intro q hdeg hdeg0 hdeg1 hcop hlin
  classical
  let F : QData := { n := n, k := k, hn := hn, hk2 := hk2, hkn := hkn, q := q, hdeg := hdeg, hdeg0 := hdeg0, hdeg1 := hdeg1, hcop := hcop, hlin := hlin }
  rcases QData.exists_extras F (F.k - 2) (by omega) with ⟨e, hwit, hout⟩
  let S : Fin (2 * n - k + 2) → Polynomial ℝ :=
    fun ℓ => ((F.compFam e ℓ : F.E) : Polynomial ℝ)
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · -- the `q0`-block part
    intro ℓ hℓ1
    dsimp [S]
    have hℓM : ℓ.val < F.M0 := by
      change ℓ.val < n + 2 - k
      omega
    have hℓ2 : ℓ.val < 2 * F.M0 := by
      change ℓ.val < 2 * (n + 2 - k)
      omega
    have hcf : F.compFam e ℓ = F.sblock ⟨ℓ.val, hℓ2⟩ := by
      dsimp [compFam]
      rw [dif_pos hℓ2]
    rw [hcf]
    rw [F.sblock_poly_left (a := ℓ.val) hℓ2 hℓM]
    rfl
  · -- the `q1`-block part
    intro ℓ hℓM0 hℓ1
    dsimp [S]
    have hℓM : F.M0 ≤ ℓ.val := by
      change n + 2 - k ≤ ℓ.val
      omega
    have hℓ2 : ℓ.val < 2 * F.M0 := by
      change ℓ.val < 2 * (n + 2 - k)
      omega
    have hcf : F.compFam e ℓ = F.sblock ⟨ℓ.val, hℓ2⟩ := by
      dsimp [compFam]
      rw [dif_pos hℓ2]
    rw [hcf]
    rw [F.sblock_poly_right (a := ℓ.val) hℓ2 hℓM]
    rfl
  · -- the extras
    intro j
    let idx : Fin (F.k - 2) := ⟨j.val, by have hj : j.val < k - 2 := j.isLt; omega⟩
    rcases hwit idx with ⟨i, hi2, hile, t, hdeg, heq⟩
    refine ⟨i, hi2, ?_, t, ?_, ?_⟩
    · simpa [idx] using hile
    · change (q i).natDegree + t ≤ 2 * n - k + 1
      exact hdeg
    · dsimp [S]
      have hidx_ge : ¬ (⟨2 * (n + 2 - k) + j.val, by have hj : j.val < k - 2 := j.isLt; omega⟩ :
          Fin (2 * n - k + 2)).val < 2 * F.M0 := by
        change ¬ 2 * (n + 2 - k) + j.val < 2 * (n + 2 - k)
        omega
      have hcf : F.compFam e ⟨2 * (n + 2 - k) + j.val,
          by
            have hj : j.val < k - 2 := j.isLt
            change 2 * (n + 2 - k) + j.val < 2 * n - k + 2
            omega⟩ = e idx := by
        dsimp [compFam]
        rw [dif_neg hidx_ge]
        congr 1
        apply Fin.ext
        dsimp [idx]
        change (2 * (n + 2 - k) + j.val) - 2 * (n + 2 - k) = j.val
        omega
      rw [hcf]
      rw [heq]
      rfl
  · -- linear independence
    have hLI_E : LinearIndependent ℝ (F.compFam e) := QData.compFam_linIndep F e hout
    have hmap : LinearIndependent ℝ (fun ℓ : Fin (2 * F.n - F.k + 2) =>
        ((F.compFam e ℓ : F.E) : Polynomial ℝ)) := by
      exact LinearIndependent.map' hLI_E F.E.subtype (Submodule.ker_subtype F.E)
    change LinearIndependent ℝ (fun ℓ : Fin (2 * n - k + 2) =>
        ((F.compFam e ℓ : F.E) : Polynomial ℝ))
    exact hmap


end

end Commons.NumberTheory.DiophantineApproximation.BoundedDegree