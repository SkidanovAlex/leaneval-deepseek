import Submission.ZagierHoffmanProof.AmbField
import Submission.ZagierHoffmanProof.TmApply
import Submission.Commons.LinearAlgebra.Matrix.exists_maximalRank_kernel_fintype

/-!
# The `K^{perf}` → `K` descent of Dac §5.2 / Chang Prop. 4.3.1

(NOTE: this is `AbpDescent`; the module `Submission.ZagierHoffmanProof.Descent` is the unrelated
Anderson–Thakur Frobenius-descent file.)

This file develops the algebraic and analytic parts of the descent step of the proof of Theorem B:
starting from a `K^{perf}`-linear relation between the values `𝓛(t;Q)(θ)` of a single weight, one
produces a `K`-linear relation.

The mathematical input is the ABP criterion with `K^{perf}`-coefficients
(`ABP_criterion_kperf`), applied to the merged `t`-motive of Dac §5.1:

* `tm_second_relation` — the "second relation" `B̃ = Q·P^{(1)} - Q^{(1)}·(P·A)` of Dac §5.2,
  with `B̃_{t₀} = 0` for any coordinate `t₀` whose column of `A` is `e_{t₀}`;
* `descent_sparse` — the sparsification of `∑_t B̃_t·ψ_t^{(1)} = 0` at the points `θ^{q^N}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
open Polynomial Matrix Finset
open scoped WithZero Topology Classical

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-! ## §1. The second relation (Dac §5.2) -/

section SecondRelation

variable {K : Type*} [Field K] {q : ℕ} [FrobPow K q]

/-- The "second relation" of Dac §5.2.  If `P` annihilates a solution `ψ` of `ψ = A ψ^{(1)}` and
`t₀` is a coordinate whose column of `A` is `e_{t₀}`, then with `Q := P_{t₀}` the row vector

  `B̃_j = Q·P_j^{(1)} - Q^{(1)}·(P·A)_j`

satisfies `B̃_{t₀} = 0` and `∑_j B̃_j·ψ_j^{(1)} = 0`. -/
theorem tm_second_relation {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι (Polynomial K)} {ψ : ι → PowerSeries K}
    (hfe : ψ = ((coeHom (K := K)).mapMatrix A).mulVec (frobTwistVec (q := q) 1 ψ))
    {P : ι → Polynomial K} (hP : ∑ j, coeHom (K := K) (P j) * ψ j = 0)
    (t₀ : ι) (hcol : ∀ i, A i t₀ = if i = t₀ then 1 else 0) :
    (∑ j, coeHom (K := K) (P t₀ * polyTwist (q := q) 1 (P j)
        - polyTwist (q := q) 1 (P t₀) * ∑ i, P i * A i j) * frobTwist (R := K) (p := q) 1 (ψ j)
      = 0) ∧
    (P t₀ * polyTwist (q := q) 1 (P t₀)
        - polyTwist (q := q) 1 (P t₀) * ∑ i, P i * A i t₀ = 0) := by
  classical
  have hψ : ∀ i, ψ i = ∑ j, (coeHom (K := K) (A i j))
      * frobTwist (R := K) (p := q) 1 (ψ j) := by
    intro i
    have h := congrFun hfe i
    simpa only [Matrix.mulVec_apply_eq_sum, RingHom.mapMatrix_apply, Matrix.map_apply,
      frobTwistVec_apply, coeHom_apply] using h
  -- (1) the twist of `hP`
  have hPt : (∑ j, frobTwist (R := K) (p := q) 1 (coeHom (K := K) (P j))
      * frobTwist (R := K) (p := q) 1 (ψ j)) = 0 := by
    have h := congrArg (frobTwist (R := K) (p := q) 1) hP
    rw [frobTwist_zero, frobTwist_sum] at h
    simpa only [frobTwist_mul] using h
  -- (2) the second summand `∑_j (∑_i P_i A_{ij}) ψ_j^{(1)}` vanishes
  have h2 : (∑ j, coeHom (K := K) (∑ i, P i * A i j)
      * frobTwist (R := K) (p := q) 1 (ψ j)) = 0 := by
    have h1 : (∑ j, coeHom (K := K) (∑ i, P i * A i j)
        * frobTwist (R := K) (p := q) 1 (ψ j))
        = ∑ j, (∑ i, coeHom (K := K) (P i) * coeHom (K := K) (A i j))
            * frobTwist (R := K) (p := q) 1 (ψ j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul]
    rw [h1]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm, ← hP]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hψ i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  refine ⟨?_, ?_⟩
  · have hmain : ∀ j : ι, coeHom (K := K) (P t₀ * polyTwist (q := q) 1 (P j)
        - polyTwist (q := q) 1 (P t₀) * ∑ i, P i * A i j)
        * frobTwist (R := K) (p := q) 1 (ψ j)
        = coeHom (K := K) (P t₀) * (frobTwist (R := K) (p := q) 1 (coeHom (K := K) (P j))
            * frobTwist (R := K) (p := q) 1 (ψ j))
          - coeHom (K := K) (polyTwist (q := q) 1 (P t₀))
            * (coeHom (K := K) (∑ i, P i * A i j) * frobTwist (R := K) (p := q) 1 (ψ j)) := by
      intro j
      simp only [map_sub, map_mul, coe_polyTwist]
      ring_nf
    rw [Finset.sum_congr rfl (fun j _ => hmain j), Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hPt, h2]
    ring
  · have hsum : (∑ i, P i * A i t₀) = P t₀ := by
      rw [Finset.sum_eq_single t₀]
      · rw [hcol t₀, if_pos rfl, mul_one]
      · intro i _ hi
        rw [hcol i, if_neg hi, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ t₀) h
    rw [hsum]
    ring

end SecondRelation

/-! ## §2. The sparsification of the second relation at the points `θ^{q^N}` -/

section Sparse

variable {γ : ℚᵐ⁰} {w₀ : ℕ} {ω : PowerSeries (Ambient F)}
  {S : Finset (List (ℕ × Polynomial (Ambient F)))}

lemma evalSeriesGen_zero_amb (c : Ambient F) :
    evalSeriesGen (0 : PowerSeries (Ambient F)) c = 0 := by
  rw [evalSeriesGen_def]
  simp

/-- **Sparsification of the second relation.**  If `B` satisfies
`∑_t B_t·(𝓛(t)·ω^{w₀-w(t)})^{(1)} = 0` as a power series, then at every point `θ^{q^N}` (`N ≥ 1`)
only the entries of weight `w₀` survive, because `ω^{(1)}` has a zero at each `θ^{q^k}`. -/
theorem descent_sparse (hγ0 : 0 < γ) (hγ : γ < 1) (harch : GammaArchimedean ℚᵐ⁰)
    (hq : 2 ≤ Nat.card F) (hωse : GSuperEntire γ ω)
    (hΩ1 : ∀ j : ℕ, 2 ≤ j → evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω)
      ((ambTheta F) ^ (Nat.card F) ^ j) = 0)
    (hLse : ∀ t : ↥(tmI S), GSuperEntire γ (tmL (Nat.card F) ω t.1))
    (hMZ : ∀ (t : ↥(tmI S)) (k : ℕ),
      evalSeriesGen (tmL (Nat.card F) ω t.1) ((ambTheta F) ^ (Nat.card F ^ k))
        = (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ k))
    (hw : ∀ t : ↥(tmI S), tmWeight t.1 ≤ w₀)
    {B : ↥(tmI S) → Polynomial (Ambient F)}
    (hrel : (∑ t ∈ (Finset.univ : Finset ↥(tmI S)), coeHom (K := Ambient F) (B t)
      * (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
        * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w₀ - tmWeight t.1))) = 0) :
    ∀ N : ℕ, 2 ≤ N → (∑ t ∈ Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w₀),
      (B t).eval ((ambTheta F) ^ (Nat.card F) ^ N)
        * (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ N)) = 0 := by
  classical
  have hΩse : GSuperEntire γ (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) :=
    hωse.frobTwist hγ.le 1
  intro N hN
  -- (1) evaluate the relation at `θ ^ q ^ N`
  have hsuper : ∀ t ∈ (Finset.univ : Finset ↥(tmI S)),
      GSuperEntire γ (coeHom (K := Ambient F) (B t)
        * (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
          * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w₀ - tmWeight t.1))) := by
    intro t _
    have h1 : GSuperEntire γ (coeHom (K := Ambient F) (B t)) :=
      GSuperEntire.polynomial hγ0 hγ.le (B t)
    have h2 : GSuperEntire γ
        (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)) :=
      (hLse t).frobTwist hγ.le 1
    have h3 : GSuperEntire γ
        ((frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w₀ - tmWeight t.1)) :=
      hΩse.pow hγ.le _
    have h23 : GSuperEntire γ
        (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
          * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w₀ - tmWeight t.1)) :=
      GSuperEntire.mul (f := frobTwist (R := Ambient F) (p := Nat.card F) 1
          (tmL (Nat.card F) ω t.1))
        (g := (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w₀ - tmWeight t.1))
        hγ.le h2 h3
    exact GSuperEntire.mul (f := coeHom (K := Ambient F) (B t))
      (g := frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
        * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w₀ - tmWeight t.1))
      hγ.le h1 h23
  have h0 : evalSeriesGen (K := Ambient F) (Γ₀ := ℚᵐ⁰)
      (∑ t ∈ (Finset.univ : Finset ↥(tmI S)), coeHom (K := Ambient F) (B t)
        * (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
          * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w₀ - tmWeight t.1)))
      ((ambTheta F) ^ (Nat.card F) ^ N) = 0 := by
    rw [hrel, evalSeriesGen_zero_amb]
  rw [evalSeriesGen_finset_sum (K := Ambient F) (Γ₀ := ℚᵐ⁰) hγ harch _ _ hsuper] at h0
  -- (2) compute each term
  have hcompute : ∀ t : ↥(tmI S),
      evalSeriesGen (coeHom (K := Ambient F) (B t)
        * (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
          * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w₀ - tmWeight t.1)))
        ((ambTheta F) ^ (Nat.card F) ^ N)
      = (B t).eval ((ambTheta F) ^ (Nat.card F) ^ N)
        * (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ N)
        * (evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω)
            ((ambTheta F) ^ (Nat.card F) ^ N)) ^ (w₀ - tmWeight t.1) := by
    intro t
    have htw : evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) 1
        (tmL (Nat.card F) ω t.1)) ((ambTheta F) ^ (Nat.card F) ^ N)
        = (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ N) := by
      have hqN : (Nat.card F) ^ (N - 1) * Nat.card F = (Nat.card F) ^ N := by
        conv_rhs => rw [← Nat.sub_add_cancel (show 1 ≤ N by omega)]
        rw [pow_succ]
      have hp : ((ambTheta F) ^ (Nat.card F ^ (N - 1))) ^ (Nat.card F)
          = (ambTheta F) ^ (Nat.card F) ^ N := by
        rw [← pow_mul, hqN]
      have h := evalSeriesGen_frobTwist hγ harch (Nat.card F) (hLse t)
        ((ambTheta F) ^ (Nat.card F ^ (N - 1))) 1
      rw [pow_one] at h
      rw [hp, hMZ t (N - 1), ← pow_mul, hqN] at h
      exact h
    rw [show coeHom (K := Ambient F) (B t)
        * (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
          * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w₀ - tmWeight t.1))
        = coeHom (K := Ambient F) (B t)
            * frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
          * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w₀ - tmWeight t.1) by ring]
    simp only [coeHom_apply]
    rw [evalSeriesGen_mul hγ harch
        (GSuperEntire.mul hγ.le
          (GSuperEntire.polynomial hγ0 hγ.le (B t)) ((hLse t).frobTwist hγ.le 1))
        (hΩse.pow hγ.le _) _,
      evalSeriesGen_mul hγ harch
        (GSuperEntire.polynomial hγ0 hγ.le (B t)) ((hLse t).frobTwist hγ.le 1) _,
      evalSeriesGen_polynomial, htw, evalSeriesGen_pow hγ harch hΩse _ _]
  rw [Finset.sum_congr rfl (fun t _ => hcompute t)] at h0
  -- (3) only the entries of weight `w₀` survive
  have hzero : ∀ t ∈ (Finset.univ : Finset ↥(tmI S)),
      t ∉ Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w₀) →
      ((B t).eval ((ambTheta F) ^ (Nat.card F) ^ N)
        * (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ N)
        * (evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω)
            ((ambTheta F) ^ (Nat.card F) ^ N)) ^ (w₀ - tmWeight t.1)) = 0 := by
    intro t _ ht
    have hne : tmWeight t.1 ≠ w₀ := fun h => ht (Finset.mem_filter.mpr ⟨Finset.mem_univ t, h⟩)
    have hlt : tmWeight t.1 < w₀ := lt_of_le_of_ne (hw t) hne
    rw [hΩ1 N hN, zero_pow (by omega : w₀ - tmWeight t.1 ≠ 0), mul_zero]
  have hpt : ∀ t ∈ Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w₀),
      (B t).eval ((ambTheta F) ^ (Nat.card F) ^ N)
        * (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ N)
      = (B t).eval ((ambTheta F) ^ (Nat.card F) ^ N)
        * (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ N)
        * (evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω)
            ((ambTheta F) ^ (Nat.card F) ^ N)) ^ (w₀ - tmWeight t.1) := by
    intro t ht
    have hwt : tmWeight t.1 = w₀ := (Finset.mem_filter.mp ht).2
    rw [hwt, Nat.sub_self, pow_zero, mul_one]
  rw [show (∑ t ∈ Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w₀),
        (B t).eval ((ambTheta F) ^ (Nat.card F) ^ N)
          * (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ N))
      = ∑ t ∈ Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w₀),
        ((B t).eval ((ambTheta F) ^ (Nat.card F) ^ N)
          * (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ N)
          * (evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω)
              ((ambTheta F) ^ (Nat.card F) ^ N)) ^ (w₀ - tmWeight t.1))
      from Finset.sum_congr rfl hpt]
  rw [Finset.sum_subset (Finset.filter_subset _ _) hzero]
  exact h0

end Sparse
