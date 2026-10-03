import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.DualityDefs
import Submission.Work.ORHughesFree.NaturalExtension.DualityAPI
import Submission.Work.ORHughesFree.NaturalExtension.truncGrowthDefs
import Submission.Work.ORHughesFree.NaturalExtension.EltDeg
import Submission.Work.ORHughesFree.NaturalExtension.coeffElt_mul
import Submission.Work.ORHughesFree.NaturalExtension.CmatAux

namespace Work.ORHughesFree.NaturalExtension

universe u

/-! ## The convolution formula for coefficients, at an arbitrary universe

`coeffElt_mul` is stated for `U : Type`, so it cannot be applied when `U = R` lives in an
arbitrary universe.  We restate it (with the same proof) at `R : Type u`. -/

private theorem ofAdd_inv_mul_cmp (v w : ℤ) :
    (Multiplicative.ofAdd v)⁻¹ * Multiplicative.ofAdd w = Multiplicative.ofAdd (w - v) := by
  rw [← ofAdd_neg, ← ofAdd_add]
  congr 1
  ring

private theorem coeffElt_mul_cmp {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    (f g : SkewL R) (w : ℤ) {L K : ℕ} (hL : lowDeg f ≤ L) (hK : upDeg f ≤ K) :
    coeffElt (f * g) w =
      ∑ v ∈ Finset.Icc (-(L : ℤ)) (K : ℤ),
        coeffElt f v * ((Multiplicative.ofAdd v) • coeffElt g (w - v)) := by
  classical
  rw [coeffElt, SkewMonoidAlgebra.coeff_mul_left]
  rw [Finsupp.sum_of_support_subset f.coeff (support_subset_Icc_image f hL hK)
      (fun a b => b * a • g.coeff (a⁻¹ * Multiplicative.ofAdd w)) (by intro i hi; simp)]
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl fun v _ => ?_
    simp only [coeffElt]
    rw [ofAdd_inv_mul_cmp]
  · intro a _ b _ hab
    exact Multiplicative.ofAdd.injective hab

/-! ## The vectors `Vvec p n k`

`Vvec p n k` is the coefficient vector of `t^k * p`, read in degrees `0,…,n`. -/

private theorem Vvec_eq_cvec_Tpow_cmp {R : Type u} [Ring R]
    [MulSemiringAction (Multiplicative ℤ) R] (p : SkewL R) (n : ℕ) (k : ℤ) :
    Vvec p n k = cvec R n (Tpow k * p) := by
  funext s
  show (Multiplicative.ofAdd k) • coeffElt p ((((s : ℕ)) : ℤ) - k) = cvec R n (Tpow k * p) s
  rw [cvec, coeffElt_Tpow_mul]

/-- `Vvec p n k` vanishes when `k` exceeds `upDeg p` (with the wrong sign). -/
private theorem Vvec_eq_zero_of_lt_neg_upDeg_cmp {R : Type u} [Ring R]
    [MulSemiringAction (Multiplicative ℤ) R] (p : SkewL R) (n : ℕ) {k : ℤ}
    (h : k < -(upDeg p : ℤ)) : Vvec p n k = 0 := by
  funext s
  show (Multiplicative.ofAdd k) • coeffElt p ((((s : ℕ)) : ℤ) - k) = 0
  have hk : (upDeg p : ℤ) < (((s : ℕ)) : ℤ) - k := by omega
  rw [coeffElt_eq_zero_of_gt_upDeg p hk, smul_zero]

/-- `Vvec p n k` vanishes for `k > n`, since `p` has no negative-degree coefficients. -/
private theorem Vvec_eq_zero_of_gt_n_cmp {R : Type u} [Ring R]
    [MulSemiringAction (Multiplicative ℤ) R] (p : SkewL R)
    (hp : ∀ k : ℤ, k < 0 → coeffElt p k = 0) (n : ℕ) {k : ℤ} (h : (n : ℤ) < k) :
    Vvec p n k = 0 := by
  funext s
  show (Multiplicative.ofAdd k) • coeffElt p ((((s : ℕ)) : ℤ) - k) = 0
  have hk : (((s : ℕ)) : ℤ) - k < 0 := by
    have hs : ((s : ℕ)) ≤ n := Nat.lt_succ_iff.mp s.isLt
    omega
  rw [hp _ hk, smul_zero]

/-- For `0 ≤ k`, the vector `Vvec p n k` is a row of `Cmat p n` (or `0` when `k > n`). -/
private theorem Vvec_mem_Crows_cmp {R : Type u} [Ring R]
    [MulSemiringAction (Multiplicative ℤ) R] (p : SkewL R)
    (hp : ∀ k : ℤ, k < 0 → coeffElt p k = 0) (n : ℕ) {k : ℤ} (hk : 0 ≤ k) :
    Vvec p n k ∈ Crows p n := by
  by_cases hkn : k ≤ (n : ℤ)
  · let r : Fin (n + 1) := ⟨k.toNat, by
      have h1 : k.toNat ≤ n := Int.toNat_le.mpr hkn
      omega⟩
    have hkr : ((r : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk
    have hrow : (fun s : Fin (n + 1) => Cmat p n r s) ∈ Crows p n :=
      Submodule.subset_span (Set.mem_range_self r)
    convert hrow using 1
    funext s
    show (Multiplicative.ofAdd k) • coeffElt p ((((s : ℕ)) : ℤ) - k)
        = (Multiplicative.ofAdd ((r : ℕ) : ℤ)) • coeffElt p
            ((((s : ℕ)) : ℤ) - ((r : ℕ) : ℤ))
    rw [hkr]
  · have hkn' : (n : ℤ) < k := not_le.mp hkn
    rw [Vvec_eq_zero_of_gt_n_cmp p hp n hkn']
    exact Submodule.zero_mem _

/-- For `-upDeg p ≤ k < 0`, the vector `Vvec p n k` is one of the extra generators of `Esub`. -/
private theorem Vvec_mem_Esub_cmp {R : Type u} [Ring R]
    [MulSemiringAction (Multiplicative ℤ) R] (p : SkewL R) (n : ℕ) {k : ℤ} (hk0 : k < 0)
    (hk : -(upDeg p : ℤ) ≤ k) : Vvec p n k ∈ Esub p n := by
  have hpos : 0 ≤ -k - 1 := by omega
  have hlt : -k - 1 < (upDeg p : ℤ) := by omega
  have hnat : (-k - 1).toNat < upDeg p := (Int.toNat_lt hpos).mpr hlt
  let j : Fin (upDeg p) := ⟨(-k - 1).toNat, hnat⟩
  have hjv : (((j : ℕ)) : ℤ) = -k - 1 := Int.toNat_of_nonneg hpos
  have hgen : (fun s : Fin (n + 1) => Emat p n j s) ∈ Esub p n :=
    Submodule.subset_span (Set.mem_range_self j)
  rw [Vvec_eq_cvec_Tpow_cmp]
  have heq : cvec R n (Tpow k * p) = fun s => Emat p n j s := by
    have hk' : k = -((((j : ℕ)) : ℤ) + 1) := by omega
    rw [hk']
    rfl
  rw [heq]
  exact hgen

/-- Every `Vvec p n k` lies in the span of the rows of `Cmat p n` together with the extra
generators. -/
private theorem Vvec_mem_Msub_cmp {R : Type u} [Ring R]
    [MulSemiringAction (Multiplicative ℤ) R] (p : SkewL R)
    (hp : ∀ k : ℤ, k < 0 → coeffElt p k = 0) (n : ℕ) (k : ℤ) :
    Vvec p n k ∈ Msub p n := by
  rw [Msub]
  rcases lt_or_ge k 0 with hk | hk
  · by_cases h2 : -(upDeg p : ℤ) ≤ k
    · exact Submodule.mem_sup.mpr ⟨0, Submodule.zero_mem _, Vvec p n k,
        Vvec_mem_Esub_cmp p n hk h2, by rw [zero_add]⟩
    · have h2' : k < -(upDeg p : ℤ) := not_le.mp h2
      rw [Vvec_eq_zero_of_lt_neg_upDeg_cmp p n h2']
      exact Submodule.zero_mem _
  · exact Submodule.mem_sup.mpr ⟨Vvec p n k, Vvec_mem_Crows_cmp p hp n hk,
      (0 : Fin (n + 1) → R), Submodule.zero_mem _, by rw [add_zero]⟩

/-- The degree filtration `degPart R (genIdeal p) n` is contained in the span of the rows of
`Cmat p n` together with the extra generators. -/
private theorem degPart_le_Msub_cmp {R : Type u} [Ring R]
    [MulSemiringAction (Multiplicative ℤ) R] (p : SkewL R)
    (hp : ∀ k : ℤ, k < 0 → coeffElt p k = 0) (n : ℕ) :
    degPart R (genIdeal p) n ≤ Msub p n := by
  rw [degPart]
  refine Submodule.span_le.mpr ?_
  rintro v ⟨f, hfI, hfneg, rfl⟩
  obtain ⟨q, rfl⟩ := hfI
  rw [Msub]
  have hexp : cvec R n (q * p) =
      ∑ v ∈ Finset.Icc (-(lowDeg q : ℤ)) (upDeg q : ℤ), (coeffElt q v) • Vvec p n v := by
    funext s
    show coeffElt (q * p) (((s : ℕ)) : ℤ) =
      (∑ v ∈ Finset.Icc (-(lowDeg q : ℤ)) (upDeg q : ℤ), (coeffElt q v) • Vvec p n v) s
    rw [coeffElt_mul_cmp q p (((s : ℕ)) : ℤ) le_rfl le_rfl]
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [Pi.smul_apply, smul_eq_mul, Vvec]
  rw [hexp]
  exact Submodule.sum_mem _ (fun v hv => Submodule.smul_mem _ _
    (Vvec_mem_Msub_cmp p hp n v))

/-- The row span of `Cmat p n` (`Cmat p n r s = (ofAdd r) • coeffElt p (s - r)`, i.e. row `r`
is the coefficient vector of `t^r * p` in degrees `0..n`) and the degree filtration
`degPart R (genIdeal p) n` differ in dimension by at most `upDeg p`.

PROOF SKETCH.  First conjunct: every row `r` of `Cmat p n` (with `r ≤ n`) is
`cvec R n (t^r * p)` (`coeffElt_powT_mul`), and `t^r * p ∈ genIdeal p` (take `q = t^r`) is
polynomial (`hp`), so the rows lie in `degPart R (genIdeal p) n`; hence
`rk (Cmat p n) = rdim rk (span of the rows) ≤ rdim rk (degPart … ) ≤ rdim (…) + upDeg p`
(`rdim_eq_rk_rows`).

Second conjunct: for `f = q * p ∈ genIdeal p` (with `q ∈ SkewL R`) and `s : Fin (n+1)`,
the coefficient identity `coeffElt (q*p) s = ∑_k coeffElt q k * ((ofAdd k) • coeffElt p (s-k))`
(`coeffElt_mul`, restricted to the support of `q`) expresses `cvec R n f` as a combination of
the vectors `cvec R n (t^k * p)`; those with `k ∈ [0, n]` are the rows of `Cmat` and those with
`k < 0` vanish for `k < -(upDeg p)` (`coeffElt p` vanishes above `upDeg p`, `hp` below `0`),
leaving at most `upDeg p` extra generators
(`cvec R n (t^{-1} p), …, cvec R n (t^{-upDeg p} p)`).  So
`degPart R (genIdeal p) n ≤ (row span of Cmat) ⊔ E` with `rdim E ≤ upDeg p`
(the span of at most `upDeg p` vectors has `rdim ≤ upDeg p`, since
`rdim (span (range v)) = rk (matrix of v) ≤ l` via `rdim_eq_rk_rows` and `RankAPI.rk_le_left`).
Use `rdim_sup_le` to finish. -/
theorem CmatDegPartCompare {R : Type u} [Ring R] [VonNeumannRegularRing R]
    [MulSemiringAction (Multiplicative ℤ) R] (rk : SylvesterRank R)
    (p : SkewL R) (hp : ∀ k : ℤ, k < 0 → coeffElt p k = 0) (n : ℕ) :
    (rk.rk (n + 1) (n + 1) (Cmat p n) ≤ rdim rk (degPart R (genIdeal p) n) + (upDeg p : ℝ)) ∧
      (rdim rk (degPart R (genIdeal p) n) ≤ rk.rk (n + 1) (n + 1) (Cmat p n) + (upDeg p : ℝ)) := by
  refine ⟨?_, ?_⟩
  · -- First conjunct: the rows of `Cmat p n` lie in `degPart R (genIdeal p) n`.
    have hrows : rk.rk (n + 1) (n + 1) (Cmat p n) = rdim rk (Crows p n) := by
      rw [Crows]
      exact (rdim_eq_rk_rows rk (Cmat p n)).symm
    rw [hrows]
    have hmono := rdim_mono rk (Crows_le_degPart p hp n)
    have hup : (0 : ℝ) ≤ (upDeg p : ℝ) := Nat.cast_nonneg _
    linarith
  · -- Second conjunct: `degPart R (genIdeal p) n` sits inside `Crows p n ⊔ Esub p n`.
    have hM : rdim rk (degPart R (genIdeal p) n) ≤ rdim rk (Msub p n) :=
      rdim_mono rk (degPart_le_Msub_cmp p hp n)
    have hC : rdim rk (Crows p n) = rk.rk (n + 1) (n + 1) (Cmat p n) := by
      rw [Crows]
      exact rdim_eq_rk_rows rk (Cmat p n)
    have hsup : rdim rk (Msub p n) ≤ rdim rk (Crows p n) + rdim rk (Esub p n) := by
      rw [Msub]
      exact rdim_sup_le rk (Crows p n) (Esub p n)
    have hE := rdim_Esub_le rk p n
    rw [hC] at hsup
    linarith

end Work.ORHughesFree.NaturalExtension
