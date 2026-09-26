import Submission.Work.RouteB.MethodI

open OnPropertyT Submission.FreeGroupAut Submission.Helpers
open scoped BigOperators

set_option autoImplicit false

/-!
# Method II: the inductive hypersimplex method of Kaluba–Kielak–Nowak

Kaluba–Kielak–Nowak, *Method II* (`Adj+kOp>=0 Xn`), is the second
symmetrisation method of the paper; it is the one used for `SAut(F_6)`, where
Method I stops (Method I with the `SAut(F_5)` certificate and `k = 2` needs
`k(n-3) = 4 ≤ m-3`, i.e. `m ≥ 7`).

The input is the inductive identity (`lem: induction` of the paper): with
`h = h_n` the number of permutations taking the sub-simplex to one containing
a given edge, and

    `X_n := ∑_σ σ(Δ_{n-1}) · ∑_{τ ≠ σ} τ(Δ_{n-1})`,

the *hypersimplex* element, one has

    `Δ_n² - λ' Δ_n = (1/h²) (∑_σ σ(Δ_{n-1}² - λ h Δ_{n-1}) + X_n - (μ h/3) Δ_n)`

with `λ' = (λ + μ/3)/h`, and the key point (`Xn` of the paper) is that
`X_n` is a combination of `Sq_n`, `Adj_n`, `Op_n` with coefficients determined by
counting, which makes `X_n - (μh/3)Δ_n` a sum of squares as soon as a
certificate `Adj_5 + k Op_5 - μ Δ_5 ∈ Σ²` with `k ≤ n-3` is available.

We work with the full symmetric group `S_n` instead of the paper's alternating
group `A_n`; this only doubles the constant `h`, and we re-derive the
coefficients in that convention (`hCoef n = cDelta n (n-1) = (n-2)(n-1)!`).

The formalisation uses the *counting identities* of `SymCounting.lean` applied
to the sub-simplex on the first `n-1` vertices (`SqPair n (n-1)` etc.) to avoid
the paper's explicit coefficient computation `X_n = α Sq_n + β Adj_n + γ Op_n`:
the identity `X_n = h² Δ_n² - ∑_σ σ(Δ_{n-1}²)` together with
`∑_σ σ(Sq_{n-1}) = cSq n (n-1) • Sq_n` (and the two analogues) produces the
same result, with the coefficients delivered by the already proved ratio
identities `cSq_mul`, `cOp_mul`.
-/

namespace Submission.RouteB

namespace Edge

variable {m n : ℕ}

/-! ## The square identity `Δ_r² = Sq_r + Adj_r + Op_r` for a sub-simplex -/

lemma product_eq_Dsub_Psub_Qsub' (m r : ℕ) :
    (Esub m r) ×ˢ (Esub m r) = Dsub m r ∪ (Psub m r ∪ Qsub m r) := by
  ext x
  rw [Finset.mem_product, Finset.mem_union, Finset.mem_union, mem_Dsub, mem_Psub, mem_Qsub]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases h : x.1 = x.2
    · exact Or.inl ⟨h, h1⟩
    · rcases Edge.trichotomy h with hh | hh
      · exact Or.inr (Or.inl ⟨hh, h1, h2⟩)
      · exact Or.inr (Or.inr ⟨hh, h1, h2⟩)
  · rintro (⟨h, h1⟩ | ⟨h, h1, h2⟩ | ⟨h, h1, h2⟩)
    · exact ⟨h1, h ▸ h1⟩
    · exact ⟨h1, h2⟩
    · exact ⟨h1, h2⟩

lemma disjoint_Dsub_Psub_union_Qsub' (m r : ℕ) :
    Disjoint (Dsub m r) (Psub m r ∪ Qsub m r) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [mem_Dsub] at hx
  rw [Finset.mem_union, mem_Psub, mem_Qsub] at hx'
  rcases hx' with ⟨h, _⟩ | ⟨h, _⟩
  · exact h.1 hx.1
  · exact Edge.op_irrefl x.1 (hx.1 ▸ h)

lemma disjoint_Psub_Qsub' (m r : ℕ) : Disjoint (Psub m r) (Qsub m r) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [mem_Psub] at hx
  rw [mem_Qsub] at hx'
  exact hx.1.2 hx'.1

/-- **The paper's `sum of sq adj op` for a sub-simplex**: for every `r`,
`Δ_r² = Sq_r + Adj_r + Op_r` inside `ℝG_m`. -/
theorem deltaSub_sq_eq' (m r : ℕ) :
    deltaSub m r ^ 2 = SqPair m r + AdjPair m r + OpPair m r := by
  have hprod : deltaSub m r ^ 2
      = ∑ x ∈ (Esub m r) ×ˢ (Esub m r), edgeLap x.1 * edgeLap x.2 := by
    rw [deltaSub_eq_sum, sq, Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun p _ => Finset.mul_sum _ _ _)]
    exact (Finset.sum_product' (Esub m r) (Esub m r)
      (fun a b => edgeLap a * edgeLap b)).symm
  rw [hprod, product_eq_Dsub_Psub_Qsub', Finset.sum_union (disjoint_Dsub_Psub_union_Qsub' m r),
    Finset.sum_union (disjoint_Psub_Qsub' m r), SqPair, AdjPair, OpPair, add_assoc]

/-! ## The coefficient `h_n`

We use the full symmetric group `S_n`, so our constant is
`hCoef n = cDelta n (n-1) = (n-2)(n-1)!`, twice the paper's `h_n`. -/

/-- The hypersimplex constant `h = cDelta n (n-1)`: the number of permutations
`σ : S_n` with `{i,j} ⊆ σ({0, …, n-2})` for a fixed edge `{i,j}`. -/
noncomputable def hCoef (n : ℕ) : ℝ := cDelta n (n - 1)

/-- The paper's `delta using edges`, averaged: `∑_σ σ(Δ_{n-1}) = hCoef n • Δ_n`. -/
theorem hCoef_smul_deltaSub (n : ℕ) (hn : 2 ≤ n) :
    (∑ σ : Equiv.Perm (Fin n), permRingHom σ (deltaSub n (n - 1))) = hCoef n • deltaSub n n :=
  sum_permRingHom_deltaSub n (n - 1) hn

lemma hCoef_pos (n : ℕ) (hn : 4 ≤ n) : 0 < hCoef n := by
  have h := cSq_pos n (n - 1) (by omega) (by omega)
  show (0 : ℝ) < cDelta n (n - 1)
  rw [← cSq_eq_cDelta n (n - 1)]
  exact h

lemma hCoef_ne_zero (n : ℕ) (hn : 4 ≤ n) : hCoef n ≠ 0 := ne_of_gt (hCoef_pos n hn)

/-- `hCoef n = (n-2)·(n-1)!`. -/
theorem hCoef_eq (n : ℕ) (hn : 2 ≤ n) :
    hCoef n = ((n : ℝ) - 2) * ((n - 1).factorial : ℝ) := by
  have hfac : ((n : ℕ).factorial : ℝ) = (n : ℝ) * (((n - 1).factorial : ℕ) : ℝ) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.factorial_succ, Nat.cast_mul, show k + 1 - 1 = k from by omega]
  have hchoose_n : (n.choose 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := cast_choose_two n
  have hchoose_n1 : ((n - 1).choose 2 : ℝ) = ((n : ℝ) - 1) * ((n : ℝ) - 2) / 2 := by
    rw [cast_choose_two (n - 1), Nat.cast_sub (show 1 ≤ n by omega)]
    ring
  have hcard : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) = ((n.factorial : ℕ) : ℝ) := by
    rw [Fintype.card_perm, Fintype.card_fin]
  rw [hCoef, cDelta, card_Esub (show n - 1 ≤ n by omega), card_Esub le_rfl, hcard,
    hchoose_n, hchoose_n1, hfac]
  have h1 : ((n : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    linarith
  have h2 : ((n : ℝ) - 1) ≠ 0 := by
    have : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    linarith
  field_simp

/-! ## The hypersimplex element `X_n` -/

/-- `(r • x) * (r • x) = r² • (x * x)`. -/
lemma smul_mul_smul_self {A : Type*} [Semiring A] [Algebra ℝ A] (r : ℝ) (x : A) :
    (r • x) * (r • x) = r ^ 2 • x ^ 2 := by
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
  congr 1 <;> rw [← pow_two]

/-- The paper's hypersimplex element `X_n = ∑_σ σ(Δ_{n-1}) ∑_{τ ≠ σ} τ(Δ_{n-1})`. -/
noncomputable def Xn (n : ℕ) : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin n))) :=
  ∑ σ : Equiv.Perm (Fin n),
    permRingHom σ (deltaSub n (n - 1))
      * ∑ τ ∈ Finset.univ.erase σ, permRingHom τ (deltaSub n (n - 1))

/-- **The defining identity of `X_n`**: `h² Δ_n² = ∑_σ σ(Δ_{n-1}²) + X_n`. -/
theorem Xn_add_sum_sq (n : ℕ) (hn : 2 ≤ n) :
    hCoef n ^ 2 • (deltaSub n n) ^ 2
      = (∑ σ : Equiv.Perm (Fin n), permRingHom σ ((deltaSub n (n - 1)) ^ 2)) + Xn n := by
  classical
  have hsum := hCoef_smul_deltaSub n hn
  have hsquare : (∑ σ : Equiv.Perm (Fin n), permRingHom σ (deltaSub n (n - 1)))
        * (∑ σ : Equiv.Perm (Fin n), permRingHom σ (deltaSub n (n - 1)))
      = (∑ σ : Equiv.Perm (Fin n), permRingHom σ ((deltaSub n (n - 1)) ^ 2)) + Xn n := by
    rw [Finset.sum_mul_sum, Xn, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Equiv.Perm (Fin n)))
      (fun τ => permRingHom σ (deltaSub n (n - 1)) * permRingHom τ (deltaSub n (n - 1)))
      (Finset.mem_univ σ)
    rw [← hsplit, show permRingHom σ ((deltaSub n (n - 1)) ^ 2)
      = permRingHom σ (deltaSub n (n - 1)) * permRingHom σ (deltaSub n (n - 1))
      from by rw [sq, map_mul]]
    rw [Finset.mul_sum]
    abel
  rw [← hsquare, hsum]
  exact (smul_mul_smul_self (hCoef n) (deltaSub n n)).symm

/-- **The hypersimplex decomposition**: `X_n` is a combination of `Sq_n`, `Adj_n`,
`Op_n` with the counting coefficients. -/
theorem Xn_eq (n : ℕ) (hn : 4 ≤ n) :
    Xn n = (hCoef n ^ 2 - hCoef n) • SqLap n
      + (hCoef n ^ 2 - cAdj n (n - 1)) • AdjLap n
      + (hCoef n ^ 2 - cOp n (n - 1)) • OpLap n := by
  classical
  have hsum : (∑ σ : Equiv.Perm (Fin n), permRingHom σ ((deltaSub n (n - 1)) ^ 2))
      = hCoef n • SqLap n + cAdj n (n - 1) • AdjLap n + cOp n (n - 1) • OpLap n := by
    rw [deltaSub_sq_eq' n (n - 1)]
    rw [Finset.sum_congr rfl (fun σ _ => by rw [map_add, map_add])]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      sum_permRingHom_SqPair n (n - 1) (by omega), sum_permRingHom_AdjPair n (n - 1) (by omega),
      sum_permRingHom_OpPair n (n - 1) (by omega), hCoef, ← cSq_eq_cDelta n (n - 1)]
  have hkey : Xn n = hCoef n ^ 2 • (deltaSub n n) ^ 2
      - (∑ σ : Equiv.Perm (Fin n), permRingHom σ ((deltaSub n (n - 1)) ^ 2)) := by
    have h := Xn_add_sum_sq n (by omega)
    rw [h]
    abel
  rw [hkey, hsum, deltaSub_sq_eq n]
  module

/-! ## The counting ratios -/

/-- `cAdj n (n-1)·(n-2) = h·(n-3)`. -/
theorem cAdj_ratio (n : ℕ) (hn : 4 ≤ n) :
    ((n : ℝ) - 2) * cAdj n (n - 1) = hCoef n * ((n : ℝ) - 3) := by
  have h := cSq_mul n (n - 1) (by omega) (by omega)
  have hcast : (((n - 1 : ℕ) : ℝ) - 2) = ((n : ℝ) - 3) := by
    rw [Nat.cast_sub (show 1 ≤ n by omega)]
    ring
  rw [hcast] at h
  rw [mul_comm ((n : ℝ) - 2) (cAdj n (n - 1)), ← h, hCoef, ← cSq_eq_cDelta n (n - 1)]

/-- `cOp n (n-1)·(n-2) = h·(n-4)`. -/
theorem cOp_ratio (n : ℕ) (hn : 5 ≤ n) :
    ((n : ℝ) - 2) * cOp n (n - 1) = hCoef n * ((n : ℝ) - 4) := by
  have h := cOp_mul n (n - 1) (by omega) (by omega) (by omega)
  have hcast : (((n - 1 : ℕ) : ℝ) - 3) = ((n : ℝ) - 4) := by
    rw [Nat.cast_sub (show 1 ≤ n by omega)]
    ring
  rw [hcast] at h
  have h1 := cAdj_ratio n (by omega)
  have hnm3 : ((n : ℝ) - 3) ≠ 0 := by
    have : (3 : ℝ) < n := by exact_mod_cast (by omega : 3 < n)
    linarith
  refine mul_right_cancel₀ hnm3 ?_
  calc ((n : ℝ) - 2) * cOp n (n - 1) * ((n : ℝ) - 3)
      = (cOp n (n - 1) * ((n : ℝ) - 3)) * ((n : ℝ) - 2) := by ring
    _ = (cAdj n (n - 1) * ((n : ℝ) - 4)) * ((n : ℝ) - 2) := by rw [h]
    _ = ((n : ℝ) - 2) * cAdj n (n - 1) * ((n : ℝ) - 4) := by ring
    _ = (hCoef n * ((n : ℝ) - 3)) * ((n : ℝ) - 4) := by rw [h1]
    _ = hCoef n * ((n : ℝ) - 4) * ((n : ℝ) - 3) := by ring

/-- **The hypersimplex identity of Method II**:
`(n-2)·X_n = h·((n-2)(h-1)·Δ_n² + Adj_n + 2·Op_n)`. -/
theorem Xn_ratio (n : ℕ) (hn : 5 ≤ n) :
    ((n : ℝ) - 2) • Xn n
      = hCoef n • ((((n : ℝ) - 2) * (hCoef n - 1)) • (deltaSub n n) ^ 2
          + AdjLap n + 2 • OpLap n) := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast (by omega : 3 ≤ n)
  have hR1 := cAdj_ratio n (by omega)
  have hR2 := cOp_ratio n hn
  have hA : cAdj n (n - 1) = hCoef n * ((n : ℝ) - 3) / ((n : ℝ) - 2) := by
    rw [eq_div_iff (by linarith : ((n : ℝ) - 2) ≠ 0), mul_comm]
    exact hR1
  have hO : cOp n (n - 1) = hCoef n * ((n : ℝ) - 4) / ((n : ℝ) - 2) := by
    rw [eq_div_iff (by linarith : ((n : ℝ) - 2) ≠ 0), mul_comm]
    exact hR2
  have h1 : ((n : ℝ) - 2) * (hCoef n ^ 2 - hCoef n)
      = hCoef n * (((n : ℝ) - 2) * (hCoef n - 1)) := by ring
  have h2' : ((n : ℝ) - 2) * (hCoef n ^ 2 - cAdj n (n - 1))
      = hCoef n * ((((n : ℝ) - 2) * (hCoef n - 1)) + 1) := by
    rw [mul_sub, hR1]; ring
  have h3' : ((n : ℝ) - 2) * (hCoef n ^ 2 - cOp n (n - 1))
      = hCoef n * ((((n : ℝ) - 2) * (hCoef n - 1)) + 2) := by
    rw [mul_sub, hR2]; ring
  rw [Xn_eq n (by omega), smul_add, smul_add, smul_smul, smul_smul, smul_smul,
    h1, h2', h3', deltaSub_sq_eq n]
  module

/-! ## Self-adjointness of the sub-simplex Laplacian -/

lemma genSub_inv_mem {r : ℕ} {x : MulAut (FreeGroup (Fin m))} (hx : x ∈ genSub m r) :
    x⁻¹ ∈ genSub m r := by
  rw [genSub, Finset.mem_biUnion] at hx ⊢
  obtain ⟨p, hp, hxp⟩ := hx
  exact ⟨p, hp, Submission.PropertyT.inv_mem_of_mem (SEdge_symm p) hxp⟩

theorem genSub_inv_eq (m r : ℕ) :
    ((genSub m r : Finset (MulAut (FreeGroup (Fin m)))) : Set (MulAut (FreeGroup (Fin m))))⁻¹
      = ((genSub m r : Finset (MulAut (FreeGroup (Fin m)))) : Set (MulAut (FreeGroup (Fin m)))) := by
  ext x
  constructor
  · intro hx
    have h : x⁻¹ ∈ genSub m r := Set.mem_inv.mp hx
    simpa using genSub_inv_mem h
  · intro hx
    rw [Set.mem_inv]
    exact genSub_inv_mem hx

/-- The sub-simplex Laplacian is self-adjoint. -/
theorem star_deltaSub (m r : ℕ) : star (deltaSub m r) = deltaSub m r :=
  Submission.PropertyT.star_laplacian (genSub m r) (genSub_inv_eq m r)

/-- The square of a self-adjoint element is a sum of hermitian squares. -/
theorem IsSOS.sq_of_star_eq {A : Type*} [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A]
    {x : A} (hx : star x = x) : IsSOS (x ^ 2) := by
  refine ⟨{x}, ?_⟩
  rw [Finset.sum_singleton, hx, ← pow_two]

/-! ## The level-`5` certificate

`Adj_n + 2·Op_n − (μ(n−2)/3)·Δ_n ∈ Σ²` follows from the certificate
`Adj_5 + k·Op_5 − μ·Δ_5 ∈ Σ²` (transported to `ℝG_n`) whenever `k ≤ n-3`:
the `S_n`-average of the certificate is
`cAdj·Adj_n + k cOp·Op_n − μ cSq·Δ_n`, and `k cOp/cAdj = 2k/(n-3) ≤ 2`,
`μ cSq/cAdj = μ(n-2)/3`. -/

lemma cOp_nonneg (m n : ℕ) : 0 ≤ cOp m n := by
  unfold cOp
  positivity

theorem adjOp_sos_of_cert5 (n : ℕ) (hn : 6 ≤ n) (k mu : ℝ) (hk : 0 ≤ k)
    (hkn : k ≤ (n : ℝ) - 3)
    (hcert : IsSOS (AdjPair n 5 + k • OpPair n 5 - mu • deltaSub n 5)) :
    IsSOS (AdjLap n + 2 • OpLap n - (mu * ((n : ℝ) - 2) / 3) • deltaSub n n) := by
  classical
  have hCpos : 0 < cAdj n 5 := cAdj_pos n 5 (by omega) (by omega)
  have hCne : cAdj n 5 ≠ 0 := ne_of_gt hCpos
  have havg : IsSOS (∑ σ : Equiv.Perm (Fin n),
      permRingHom σ (AdjPair n 5 + k • OpPair n 5 - mu • deltaSub n 5)) :=
    IsSOS.finset_sum Finset.univ
      (fun σ _ => IsSOS.map (permRingHom σ) (permRingHom_star σ) hcert)
  have hscaled : IsSOS ((cAdj n 5)⁻¹ • (∑ σ : Equiv.Perm (Fin n),
      permRingHom σ (AdjPair n 5 + k • OpPair n 5 - mu • deltaSub n 5))) :=
    IsSOS.smul (le_of_lt (inv_pos.mpr hCpos)) havg
  have hid : (cAdj n 5)⁻¹ • (∑ σ : Equiv.Perm (Fin n),
        permRingHom σ (AdjPair n 5 + k • OpPair n 5 - mu • deltaSub n 5))
      = AdjLap n + (k * cOp n 5 / cAdj n 5) • OpLap n
          - (mu * cSq n 5 / cAdj n 5) • deltaSub n n := by
    rw [sum_permRingHom_cert n 5 (by omega) (by omega) k mu, smul_sub, smul_add, smul_smul,
      smul_smul, smul_smul, inv_mul_cancel₀ hCne, one_smul, inv_mul_eq_div, inv_mul_eq_div]
  rw [hid] at hscaled
  have hratio_delta : mu * cSq n 5 / cAdj n 5 = mu * ((n : ℝ) - 2) / 3 := by
    have h := cSq_mul n 5 (by omega) (by omega)
    have hkey : cSq n 5 * 3 = cAdj n 5 * ((n : ℝ) - 2) := by
      norm_num at h ⊢
      exact h
    rw [div_eq_div_iff hCne (by norm_num : (3 : ℝ) ≠ 0)]
    linear_combination mu * hkey
  have hratio_op : k * cOp n 5 / cAdj n 5 ≤ 2 := by
    have h := cOp_mul n 5 (by omega) (by omega) (by omega)
    have hkey : cOp n 5 * ((n : ℝ) - 3) = 2 * cAdj n 5 := by
      norm_num at h ⊢
      rw [h]; ring
    rw [div_le_iff₀ hCpos]
    calc k * cOp n 5 ≤ ((n : ℝ) - 3) * cOp n 5 :=
          mul_le_mul_of_nonneg_right hkn (cOp_nonneg n 5)
      _ = cOp n 5 * ((n : ℝ) - 3) := by ring
      _ = 2 * cAdj n 5 := hkey
  rw [hratio_delta] at hscaled
  have h2 : 0 ≤ 2 - k * cOp n 5 / cAdj n 5 := by linarith
  have hgoal := hscaled.add (IsSOS.smul h2 (isSOS_OpLap n))
  convert hgoal using 1
  module

/-! ## Method II -/

/-- **Kaluba–Kielak–Nowak, Method II** (`lem: induction` + `Xn`): from a
certificate `Δ_{n-1}² − λΔ_{n-1} ∈ Σ²` (transported to `ℝG_n`) and a certificate
`Adj_5 + k·Op_5 − μ·Δ_5 ∈ Σ²` with `k ≤ n-3`, the element
`Δ_n² − ((λ + μ/3)/h_n)Δ_n` is a sum of hermitian squares. -/
theorem methodII_cert (n : ℕ) (hn : 6 ≤ n) (k mu lam : ℝ) (hk : 0 ≤ k)
    (hkn : k ≤ (n : ℝ) - 3) (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (hcert : IsSOS (deltaSub n (n - 1) ^ 2 - lam • deltaSub n (n - 1)))
    (h5 : IsSOS (AdjPair n 5 + k • OpPair n 5 - mu • deltaSub n 5)) :
    IsSOS (deltaSub n n ^ 2 - ((lam + mu / 3) / hCoef n) • deltaSub n n) := by
  classical
  have hn4 : 4 ≤ n := by omega
  have hn5 : 5 ≤ n := by omega
  have hpos : 0 < hCoef n := hCoef_pos n hn4
  have hne : hCoef n ≠ 0 := ne_of_gt hpos
  -- the transported certificate, averaged over `S_n`
  have hC : IsSOS (∑ σ : Equiv.Perm (Fin n),
      permRingHom σ (deltaSub n (n - 1) ^ 2 - lam • deltaSub n (n - 1))) :=
    IsSOS.finset_sum Finset.univ
      (fun σ _ => IsSOS.map (permRingHom σ) (permRingHom_star σ) hcert)
  -- the hypersimplex term
  have hAdjOp := adjOp_sos_of_cert5 n hn k mu hk hkn h5
  have hp : 0 ≤ ((n : ℝ) - 2) * (hCoef n - 1) := by
    have h1 : (1 : ℝ) ≤ hCoef n := by
      rw [hCoef_eq n (by omega)]
      have h2 : (1 : ℝ) ≤ (n : ℝ) - 2 := by
        have : (3 : ℝ) ≤ n := by exact_mod_cast (by omega : 3 ≤ n)
        linarith
      have h3 : (1 : ℝ) ≤ ((n - 1).factorial : ℝ) := by
        have : (1 : ℕ) ≤ (n - 1).factorial := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
        exact_mod_cast this
      nlinarith [h2, h3]
    have h4 : (0 : ℝ) ≤ (n : ℝ) - 2 := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
      linarith
    nlinarith [h1, h4]
  have hsq : IsSOS ((deltaSub n n) ^ 2) := IsSOS.sq_of_star_eq (star_deltaSub n n)
  have hbr : IsSOS ((((n : ℝ) - 2) * (hCoef n - 1)) • (deltaSub n n) ^ 2
      + (AdjLap n + 2 • OpLap n - (mu * ((n : ℝ) - 2) / 3) • deltaSub n n)) :=
    (IsSOS.smul hp hsq).add hAdjOp
  -- the multiplied hypersimplex identity
  have hmulti : ((n : ℝ) - 2) • (Xn n - (mu * hCoef n / 3) • deltaSub n n)
      = hCoef n • ((((n : ℝ) - 2) * (hCoef n - 1)) • (deltaSub n n) ^ 2
          + (AdjLap n + 2 • OpLap n - (mu * ((n : ℝ) - 2) / 3) • deltaSub n n)) := by
    rw [smul_sub, Xn_ratio n (by omega), smul_smul]
    module
  have hB : IsSOS (Xn n - (mu * hCoef n / 3) • deltaSub n n) := by
    have h1 : IsSOS (((n : ℝ) - 2) • (Xn n - (mu * hCoef n / 3) • deltaSub n n)) := by
      rw [hmulti]
      exact IsSOS.smul (le_of_lt hpos) hbr
    have h2 : (Xn n - (mu * hCoef n / 3) • deltaSub n n)
        = (((n : ℝ) - 2)⁻¹) • (((n : ℝ) - 2) • (Xn n - (mu * hCoef n / 3) • deltaSub n n)) := by
      rw [smul_smul, inv_mul_cancel₀ (by linarith : ((n : ℝ) - 2) ≠ 0), one_smul]
    rw [h2]
    exact IsSOS.smul (le_of_lt (inv_pos.mpr (by linarith : (0 : ℝ) < (n : ℝ) - 2))) h1
  -- the inductive identity
  have hsplit : (∑ σ : Equiv.Perm (Fin n),
        permRingHom σ (deltaSub n (n - 1) ^ 2 - lam • deltaSub n (n - 1)))
      = (∑ σ : Equiv.Perm (Fin n), permRingHom σ ((deltaSub n (n - 1)) ^ 2))
          - (lam * hCoef n) • deltaSub n n := by
    rw [Finset.sum_congr rfl (fun σ _ => by rw [map_sub, permRingHom_smul]),
      Finset.sum_sub_distrib, sum_smul_fintype, hCoef_smul_deltaSub n (by omega), smul_smul]
  have hscal : hCoef n ^ 2 * ((lam + mu / 3) / hCoef n) = lam * hCoef n + mu * hCoef n / 3 := by
    field_simp
  have hkey : hCoef n ^ 2 • (deltaSub n n ^ 2 - ((lam + mu / 3) / hCoef n) • deltaSub n n)
      = (∑ σ : Equiv.Perm (Fin n),
            permRingHom σ (deltaSub n (n - 1) ^ 2 - lam • deltaSub n (n - 1)))
          + (Xn n - (mu * hCoef n / 3) • deltaSub n n) := by
    rw [hsplit, smul_sub, smul_smul, hscal, Xn_add_sum_sq n (by omega)]
    module
  have hsum : IsSOS (hCoef n ^ 2 • (deltaSub n n ^ 2 - ((lam + mu / 3) / hCoef n) • deltaSub n n)) := by
    rw [hkey]
    exact hC.add hB
  have hfinal : (deltaSub n n ^ 2 - ((lam + mu / 3) / hCoef n) • deltaSub n n)
      = ((hCoef n ^ 2)⁻¹) • (hCoef n ^ 2 • (deltaSub n n ^ 2 - ((lam + mu / 3) / hCoef n) • deltaSub n n)) := by
    rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hne), one_smul]
  rw [hfinal]
  exact IsSOS.smul (by positivity) hsum

end Edge

end Submission.RouteB
