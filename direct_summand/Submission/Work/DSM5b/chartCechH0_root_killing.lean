import Mathlib
import Submission.Work.DSMap.Mix2
import Submission.Work.DSM5b.rootKillTransport
import Submission.Work.DSM5b.chartCech_cycle_iff_pairwise
import Submission.Work.DSM5b.glue_witness_mem
import Submission.Work.DSM5b.locRes_eq_zero_imp_pow_mul_eq_zero

namespace Work.DSM5b

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
universe a

/-- In a reduced ring, `T ^ N * x = 0` implies `T * x = 0`. -/
theorem mul_eq_zero_of_pow_mul_eq_zero_of_isReduced {A : Type a} [CommRing A] [IsReduced A]
    (T x : A) (N : ℕ) (h : T ^ N * x = 0) : T * x = 0 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    rw [pow_zero, one_mul] at h
    rw [h, mul_zero]
  · have hnil : IsNilpotent (T * x) := by
      refine ⟨N, ?_⟩
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, (Nat.succ_pred_eq_of_pos hN).symm⟩
      have hsplit : x ^ (M + 1) = x ^ M * x := by rw [pow_succ']; ring
      calc (T * x) ^ (M + 1) = T ^ (M + 1) * x ^ (M + 1) := by rw [mul_pow]
        _ = T ^ (M + 1) * (x ^ M * x) := by rw [hsplit]
        _ = (T ^ (M + 1) * x) * x ^ M := by ring
        _ = 0 := by rw [h, zero_mul]
    exact IsReduced.eq_zero _ hnil

/-- **The `p`-th power trick.**  In a localisation of a perfect ring of characteristic the prime
`p`, an element whose `p ^ n`-th power lies in the image of `R` already lies in the image of `R`:
`x = (x ^ (p ^ n)) ^ (1/p^n)`, and `p`-th roots in such a localisation are unique. -/
theorem algebraMap_of_pow_mem (p : ℕ) [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p]
    [PerfectRing R p] (f : R) (x : Localization.Away f) (n : ℕ) (r : R)
    (h : x ^ (p ^ n) = algebraMap R (Localization.Away f) r) :
    ∃ r' : R, x = algebraMap R (Localization.Away f) r' := by
  refine ⟨((frobeniusEquiv R p).symm)^[n] r, ?_⟩
  set y : Localization.Away f := algebraMap R (Localization.Away f)
    (((frobeniusEquiv R p).symm)^[n] r) with hy
  have hroot : ∀ m : ℕ, (((frobeniusEquiv R p).symm)^[m] r) ^ (p ^ m) = r := by
    intro m
    induction m with
    | zero => rw [Function.iterate_zero, id_eq, pow_zero, pow_one]
    | succ m ih =>
        have hstep : (frobeniusEquiv R p).symm (((frobeniusEquiv R p).symm^[m]) r) ^ p =
            ((frobeniusEquiv R p).symm^[m]) r :=
          frobenius_apply_frobeniusEquiv_symm R p (((frobeniusEquiv R p).symm^[m]) r)
        rw [Function.iterate_succ_apply', pow_succ, mul_comm, pow_mul, hstep, ih]
  have hpow : x ^ (p ^ n) = y ^ (p ^ n) := by
    rw [hy, ← map_pow, hroot n, ← h]
  have key : ∀ m : ℕ, x ^ (p ^ m) = y ^ (p ^ m) → x = y := by
    intro m
    induction m with
    | zero => intro hm; simpa using hm
    | succ m ih =>
        intro hm
        exact ih (Work.DSM5b.Work.DSM5b.pow_injective_away p f (by simpa [pow_succ, pow_mul] using hm))
  exact key n hpow

/-- **The `k`-th root killing follows from the zero-th one.** -/
theorem chartCechH0_root_killing_of_zero_level (p : ℕ) [Fact p.Prime] {R : Type a} [CommRing R]
    [CharP R p] [PerfectRing R p] {ι : Type a} [Finite ι] [DecidableEq ι] (t : ι → R) (j₀ : ι)
    (h : ∀ (T : R) (e : ℕ), t j₀ = T ^ e → ∀ (z : (chartCech t).X 0),
      (chartCech t).d 0 1 z = 0 → ∃ w : R, T • z = (chartCoaugW t).hom w)
    (T : R) (e : ℕ) (hj₀ : t j₀ = T ^ e) (k : ℕ) (z : (chartCech t).X 0)
    (hz : (chartCech t).d 0 1 z = 0) :
    ∃ w : R, (frobeniusEquiv R p).symm^[k] T • z = (chartCoaugW t).hom w := by
  have hroot : ((frobeniusEquiv R p).symm^[k] T) ^ (p ^ k) = T := by
    have h1 : ∀ n : ℕ, ((frobeniusEquiv R p).symm^[n] T) ^ (p ^ n) = T := by
      intro n
      induction n with
      | zero => rw [Function.iterate_zero, id_eq, pow_zero, pow_one]
      | succ n ih =>
          have hstep : (frobeniusEquiv R p).symm (((frobeniusEquiv R p).symm^[n]) T) ^ p =
              ((frobeniusEquiv R p).symm^[n]) T :=
            frobenius_apply_frobeniusEquiv_symm R p (((frobeniusEquiv R p).symm^[n]) T)
          rw [Function.iterate_succ_apply', pow_succ, mul_comm, pow_mul, hstep, ih]
    exact h1 k
  refine h ((frobeniusEquiv R p).symm^[k] T) (e * p ^ k) ?_ z hz
  rw [hj₀, mul_comm, pow_mul, hroot]

/-- A perfect ring of prime characteristic is reduced (the Frobenius is injective). -/
theorem isReduced_of_perfectRing (p : ℕ) [Fact p.Prime] (R : Type a) [CommRing R] [CharP R p]
    [PerfectRing R p] : IsReduced R := by
  constructor
  intro x hx
  obtain ⟨n, hn⟩ := hx
  have hge : n ≤ p ^ n := le_of_lt (Nat.lt_pow_self (n := n) (Fact.out : p.Prime).one_lt)
  have hbig : x ^ (p ^ n) = 0 := by
    rw [show (p ^ n : ℕ) = n + (p ^ n - n) from (Nat.add_sub_cancel' hge).symm, pow_add, hn,
      zero_mul]
  have key : ∀ m : ℕ, x ^ (p ^ m) = 0 → x = 0 := by
    intro m
    induction m with
    | zero => intro h; simpa using h
    | succ m ih =>
        intro h
        have h' : (x ^ (p ^ m)) ^ p = 0 := by
          rw [← pow_mul]; exact h
        have h2 : (frobenius R p) (x ^ (p ^ m)) = (frobenius R p) 0 := by
          simp only [frobenius_def, h', zero_pow (Fact.out : p.Prime).ne_zero]
        have h'' : x ^ (p ^ m) = 0 :=
          (PerfectRing.bijective_frobenius (R := R) (p := p)).1 h2
        exact ih h''
  exact key n hbig

/-- The `p ^ k`-th power of the `k`-th `p`-power root of `x` is `x`. -/
theorem frobeniusEquiv_symm_iterate_pow (p : ℕ) [Fact p.Prime] {R : Type a} [CommRing R]
    [CharP R p] [PerfectRing R p] (x : R) (k : ℕ) :
    ((frobeniusEquiv R p).symm^[k] x) ^ (p ^ k) = x := by
  induction k with
  | zero => rw [Function.iterate_zero, id_eq, pow_zero, pow_one]
  | succ k ih =>
      have hstep : (frobeniusEquiv R p).symm ((frobeniusEquiv R p).symm^[k] x) ^ p =
          (frobeniusEquiv R p).symm^[k] x := frobenius_apply_frobeniusEquiv_symm R p _
      rw [Function.iterate_succ_apply', pow_succ, mul_comm, pow_mul, hstep, ih]

/-- **The tower step**: `(ϖ (k+1)) ^ p = ϖ k`. -/
theorem frobeniusEquiv_symm_iterate_succ_pow (p : ℕ) [Fact p.Prime] {R : Type a} [CommRing R]
    [CharP R p] [PerfectRing R p] (x : R) (k : ℕ) :
    ((frobeniusEquiv R p).symm^[k + 1] x) ^ p = (frobeniusEquiv R p).symm^[k] x := by
  rw [Function.iterate_succ_apply']
  exact frobenius_apply_frobeniusEquiv_symm R p _

/-- **The `T`-torsion principle.**  In a reduced ring of characteristic `p`, anything killed by `T`
is killed by *every* `p`-power root of `T`. -/
theorem varpi_mul_eq_zero_of_mul_eq_zero (p : ℕ) [Fact p.Prime] {R : Type a} [CommRing R]
    [CharP R p] [PerfectRing R p] (T x : R) (k : ℕ) (h : T * x = 0) :
    (frobeniusEquiv R p).symm^[k] T * x = 0 := by
  have hred : IsReduced R := isReduced_of_perfectRing p R
  have hp1 : 1 ≤ p ^ k := pow_pos (Fact.out : p.Prime).pos k
  have hT : ∀ m : ℕ, T * x ^ (m + 1) = 0 := by
    intro m
    induction m with
    | zero => simpa using h
    | succ m ih => rw [pow_succ', ← mul_assoc, h, zero_mul]
  have hpow : ((frobeniusEquiv R p).symm^[k] T * x) ^ (p ^ k) = 0 := by
    rw [mul_pow, frobeniusEquiv_symm_iterate_pow,
      show p ^ k = (p ^ k - 1) + 1 from (Nat.sub_add_cancel hp1).symm]
    exact hT (p ^ k - 1)
  exact hred.eq_zero _ ⟨p ^ k, hpow⟩

/-- **The `T`-torsion principle in a reduced `R`-algebra** (the form needed for the chart rings):
`T x = 0 ⟹ ϖ k · x = 0`. -/
theorem algebraMap_varpi_mul_eq_zero_of_mul_eq_zero (p : ℕ) [Fact p.Prime] {R : Type a}
    [CommRing R] [CharP R p] [PerfectRing R p] {A : Type a} [CommRing A] [Algebra R A] [IsReduced A]
    (T : R) (x : A) (k : ℕ) (h : algebraMap R A T * x = 0) :
    algebraMap R A ((frobeniusEquiv R p).symm^[k] T) * x = 0 := by
  have hp1 : 1 ≤ p ^ k := pow_pos (Fact.out : p.Prime).pos k
  have hT : ∀ m : ℕ, algebraMap R A T * x ^ (m + 1) = 0 := by
    intro m
    induction m with
    | zero => simpa using h
    | succ m ih => rw [pow_succ', ← mul_assoc, h, zero_mul]
  have hpow : (algebraMap R A ((frobeniusEquiv R p).symm^[k] T) * x) ^ (p ^ k) = 0 := by
    rw [mul_pow, ← map_pow, frobeniusEquiv_symm_iterate_pow,
      show p ^ k = (p ^ k - 1) + 1 from (Nat.sub_add_cancel hp1).symm]
    exact hT (p ^ k - 1)
  exact IsReduced.eq_zero _ ⟨p ^ k, hpow⟩

/-- Products of reduced rings are reduced. -/
instance instIsReducedPi {ι : Type a} {A : ι → Type a} [∀ i, CommRing (A i)]
    [∀ i, IsReduced (A i)] : IsReduced (∀ i, A i) := by
  constructor
  intro x hx
  funext i
  obtain ⟨n, hn⟩ := hx
  exact IsReduced.eq_zero (x i) ⟨n, by simpa using congrFun hn i⟩

section ChartReduced

variable {W : Type a} [CommRing W] {ι : Type a} [DecidableEq ι]

/-- Chart rings of a reduced ring are reduced (they are subalgebras of localisations). -/
instance instIsReducedChartRing [IsReduced W] (t : ι → W) (S : Finset ι) :
    IsReduced ↥(chartRing t S) := by
  constructor
  intro x hx
  exact Subtype.ext (IsReduced.eq_zero _
    (hx.map (algebraMap ↥(chartRing t S) (Localization.Away (tS t S)))))

end ChartReduced

section Kernel

variable {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι]

/-- If a power of `tS t ({i} ∪ {j₀})` kills `x` in the localisation `R_{t i}`, then `T` kills `x`
in the honest chart ring `R[t_k/t_i]`. -/
theorem chartRing_T_mul_eq_zero_of_chartPow_mul_eq_zero (p : ℕ) [Fact p.Prime] {R : Type a}
    [CommRing R] [CharP R p] [PerfectRing R p] {ι : Type a} [DecidableEq ι] (t : ι → R) (T : R)
    (j₀ : ι) (e : ℕ) (hj₀ : t j₀ = T ^ e) {i : ι} (x : ↥(chartRing t {i}))
    (hx : ∃ n : ℕ, algebraMap R (Localization.Away (tS t {i})) ((tS t ({i} ∪ {j₀})) ^ n) *
        (x : Localization.Away (tS t {i})) = 0) :
    algebraMap R ↥(chartRing t {i}) T * x = 0 := by
  classical
  haveI hredR : IsReduced R := isReduced_of_perfectRing p R
  haveI hred : IsReduced ↥(chartRing t {i}) := instIsReducedChartRing t {i}
  obtain ⟨n, hn⟩ := hx
  have key : (algebraMap R ↥(chartRing t {i}) (tS t {j₀})) ^ n * x = 0 := by
    by_cases hij : i = j₀
    · -- then `{i} ∪ {j₀} = {j₀}`
      have hU : ({i} : Finset ι) ∪ {j₀} = {j₀} := by
        rw [hij, Finset.union_self]
      rw [hU, map_pow] at hn
      apply Subtype.coe_injective
      push_cast
      exact hn
    · have hprod : tS t ({i} ∪ {j₀}) = tS t {i} * tS t {j₀} := by
        rw [tS, tS, tS,
          Finset.prod_union (Finset.disjoint_singleton_left.mpr (by simpa using hij))]
      have hn' : (algebraMap R (Localization.Away (tS t {i})) (tS t {i})) ^ n *
          ((algebraMap R (Localization.Away (tS t {i})) (tS t {j₀})) ^ n *
            (x : Localization.Away (tS t {i}))) = 0 := by
        rw [hprod, map_pow, map_mul, mul_pow, mul_assoc] at hn
        exact hn
      have ha : IsUnit ((algebraMap R (Localization.Away (tS t {i})) (tS t {i})) ^ n) :=
        (IsLocalization.Away.algebraMap_isUnit (tS t {i})).pow n
      have hcancel : (algebraMap R (Localization.Away (tS t {i})) (tS t {j₀})) ^ n *
          (x : Localization.Away (tS t {i})) = 0 :=
        (IsUnit.mul_right_eq_zero ha).mp hn'
      apply Subtype.coe_injective
      push_cast
      exact hcancel
  -- move to the localisation, where `tS t {j₀} = t j₀ = T ^ e` can be rewritten freely
  have keyLoc : (algebraMap R (Localization.Away (tS t {i})) (tS t {j₀})) ^ n *
      (x : Localization.Away (tS t {i})) = 0 := by
    have h : (((algebraMap R ↥(chartRing t {i}) (tS t {j₀})) ^ n * x : ↥(chartRing t {i})) :
        Localization.Away (tS t {i})) = 0 := by
      rw [key, Subalgebra.coe_zero]
    simpa only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap] using h
  rw [show tS t {j₀} = t j₀ from by simp [tS], hj₀, ← map_pow, ← pow_mul, map_pow] at keyLoc
  have key2 : (algebraMap R ↥(chartRing t {i}) T) ^ (e * n) * x = 0 := by
    apply Subtype.coe_injective
    simpa only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap,
      Subalgebra.coe_zero] using keyLoc
  exact mul_eq_zero_of_pow_mul_eq_zero_of_isReduced _ x (e * n) key2

end Kernel

section Square

variable {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι]

/-- **The squared root killing**, conditional on the "descent" hypothesis: every `T`-torsion `0`-cycle
whose `j₀`-component vanishes is already in the image of the coaugmentation.

`R` is perfect of characteristic `p`, `t : ι → R` finite, `T ∈ R` with `t j₀ = T ^ e`.  Then every
`0`-cycle `z` becomes, after multiplication by the *square* of `ϖ k = T ^ (1/p^k)`, the image of an
element of `R`. -/
theorem chartCechH0_root_killing_sq_of_descent (p : ℕ) [Fact p.Prime] (R : Type a) [CommRing R]
    [CharP R p] [PerfectRing R p] {ι : Type a} [Finite ι] [DecidableEq ι] (t : ι → R) (T : R)
    (j₀ : ι) (e : ℕ) (hj₀ : t j₀ = T ^ e)
    (hdesc : ∀ (i : ι) (x : ↥(chartRing t {i})),
      ccRestr t (Finset.subset_union_left : ({i} : Finset ι) ⊆ {i} ∪ {j₀}) x = 0 →
      algebraMap R ↥(chartRing t {i}) T * x = 0)
    (z : (chartCech t).X 0) (hz : (chartCech t).d 0 1 z = 0) (k : ℕ) :
    ∃ w : R, ((frobeniusEquiv R p).symm^[k] T) ^ 2 • z = (chartCoaugW t).hom w := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  haveI hredR : IsReduced R := isReduced_of_perfectRing p R
  obtain ⟨e0, hcoaug, hcyc⟩ := chartCech_cycle_iff_pairwise (W := R) t
  set y : ∀ i : ι, ↥(chartRing t {i}) := e0 z with hy
  have hyc : ∀ i j : ι,
      locRes t (Finset.subset_union_left : ({i} : Finset ι) ⊆ {i} ∪ {j})
          ((y i : chartRing t {i}) : Localization.Away (tS t {i}))
        = locRes t (Finset.subset_union_right : ({j} : Finset ι) ⊆ {i} ∪ {j})
          ((y j : chartRing t {j}) : Localization.Away (tS t {j})) := (hcyc z).mp hz
  obtain ⟨r, hr⟩ := glue_witness_mem p t T j₀ e hj₀ y hyc k
  set c : R := (frobeniusEquiv R p).symm^[k] T with hc
  -- the error term in the `i`-th chart vanishes on the overlap `{i} ∪ {j₀}`
  have hres : ∀ i : ι, ccRestr t (Finset.subset_union_left : ({i} : Finset ι) ⊆ {i} ∪ {j₀})
      (algebraMap R ↥(chartRing t {i}) c * y i - algebraMap R ↥(chartRing t {i}) r) = 0 := by
    intro i
    by_cases hij : i = j₀
    · subst hij
      have h0 : algebraMap R ↥(chartRing t {i}) c * y i - algebraMap R ↥(chartRing t {i}) r = 0 := by
        rw [← Algebra.smul_def, hr, sub_self]
      rw [h0, map_zero]
    · have hcc : ccRestr t (Finset.subset_union_left : ({i} : Finset ι) ⊆ {i} ∪ {j₀}) (y i)
          = ccRestr t (Finset.subset_union_right : ({j₀} : Finset ι) ⊆ {i} ∪ {j₀}) (y j₀) := by
        apply Subtype.ext
        rw [ccRestr_coe, ccRestr_coe]
        exact hyc i j₀
      have hzj : algebraMap R ↥(chartRing t {j₀}) c * y j₀ - algebraMap R ↥(chartRing t {j₀}) r = 0 := by
        rw [← Algebra.smul_def, hr, sub_self]
      calc ccRestr t (Finset.subset_union_left : ({i} : Finset ι) ⊆ {i} ∪ {j₀})
            (algebraMap R ↥(chartRing t {i}) c * y i - algebraMap R ↥(chartRing t {i}) r)
          = algebraMap R ↥(chartRing t ({i} ∪ {j₀})) c *
              ccRestr t (Finset.subset_union_left : ({i} : Finset ι) ⊆ {i} ∪ {j₀}) (y i)
            - algebraMap R ↥(chartRing t ({i} ∪ {j₀})) r := by
              simp only [map_sub, map_mul, AlgHom.commutes]
        _ = algebraMap R ↥(chartRing t ({i} ∪ {j₀})) c *
              ccRestr t (Finset.subset_union_right : ({j₀} : Finset ι) ⊆ {i} ∪ {j₀}) (y j₀)
            - algebraMap R ↥(chartRing t ({i} ∪ {j₀})) r := by rw [hcc]
        _ = ccRestr t (Finset.subset_union_right : ({j₀} : Finset ι) ⊆ {i} ∪ {j₀})
              (algebraMap R ↥(chartRing t {j₀}) c * y j₀ - algebraMap R ↥(chartRing t {j₀}) r) := by
              simp only [map_sub, map_mul, AlgHom.commutes]
        _ = 0 := by rw [hzj, map_zero]
  -- hence `T` kills each error term
  have hTx : ∀ i : ι, algebraMap R ↥(chartRing t {i}) T *
      (algebraMap R ↥(chartRing t {i}) c * y i - algebraMap R ↥(chartRing t {i}) r) = 0 :=
    fun i => hdesc i _ (hres i)
  -- and then `ϖ k` kills it as well
  have hcx : ∀ i : ι, algebraMap R ↥(chartRing t {i}) c *
      (algebraMap R ↥(chartRing t {i}) c * y i - algebraMap R ↥(chartRing t {i}) r) = 0 := by
    intro i
    haveI hred : IsReduced ↥(chartRing t {i}) := instIsReducedChartRing t {i}
    have h := algebraMap_varpi_mul_eq_zero_of_mul_eq_zero p T
      (algebraMap R ↥(chartRing t {i}) c * y i - algebraMap R ↥(chartRing t {i}) r) k (hTx i)
    rwa [← hc] at h
  -- consequently `c ^ 2 • y i = algebraMap (c * r)`
  have hfinal : ∀ i : ι, c ^ 2 • y i = algebraMap R ↥(chartRing t {i}) (c * r) := by
    intro i
    have h2 := hcx i
    have hsplit : algebraMap R ↥(chartRing t {i}) c *
        (algebraMap R ↥(chartRing t {i}) c * y i) =
        algebraMap R ↥(chartRing t {i}) c * algebraMap R ↥(chartRing t {i}) r := by
      have hExp : algebraMap R ↥(chartRing t {i}) c *
          (algebraMap R ↥(chartRing t {i}) c * y i - algebraMap R ↥(chartRing t {i}) r) =
          algebraMap R ↥(chartRing t {i}) c * (algebraMap R ↥(chartRing t {i}) c * y i)
            - algebraMap R ↥(chartRing t {i}) c * algebraMap R ↥(chartRing t {i}) r := by ring
      rw [hExp] at h2
      exact sub_eq_zero.mp h2
    rw [Algebra.smul_def, map_pow]
    calc algebraMap R ↥(chartRing t {i}) c ^ 2 * y i
        = algebraMap R ↥(chartRing t {i}) c * (algebraMap R ↥(chartRing t {i}) c * y i) := by ring
      _ = algebraMap R ↥(chartRing t {i}) c * algebraMap R ↥(chartRing t {i}) r := hsplit
      _ = algebraMap R ↥(chartRing t {i}) (c * r) := by rw [map_mul]
  refine ⟨c * r, ?_⟩
  apply e0.injective
  funext i
  rw [map_smul]
  change c ^ 2 • e0 z i = e0 ((chartCoaugW t).hom (c * r)) i
  rw [← hy, hfinal i, hcoaug]

end Square

/-- **The honest (unperfected) chart Čech complex has `ϖ k`-almost surjective `H⁰`.**

`R` is perfect of characteristic `p`, `t : ι → R` is a finite family, `T ∈ R` and `t j₀ = T ^ e`.
For `S : Finset ι`, `chartRing t S = R[t_k/t_i : i ∈ S, k] ⊆ R_{t_S}` is the *honest* blowup chart
ring of `Bl_{(t)} Spec R` (frozen definition in `DSMap.Mix2`), and

`chartCech t = Č({D(t i)}, chartRing)`,  `chartCoaugW t : R ⟶ (chartCech t).X 0`

is its Čech complex and coaugmentation (also frozen, in `DSMap.Mix2`).

CLAIM: every `0`-cycle `y` of `chartCech t` becomes, after multiplication by the `p`-power root
`ϖ k = T ^ (1/p^k)` of `T`, the image of an element of `R`:
`∃ w, ϖ k • y = (chartCoaugW t).hom w`.

This is the *honest* form of the `H⁰`-half of the frozen node `DSMap.Mix2.area_M5b`; the perfected
form (`Work.DSM5b.perfChartH0_root_killing`) follows from this statement by Frobenius/root
bookkeeping of the perfected charts, so this statement is the mathematical heart.

Route: after inverting `ϖ k` the `t i` generate the unit ideal of `R[1/ϖ k]`, and the localised
complex is the Čech complex of the covering family `{D(t i)}` of `Spec R[1/ϖ k]`, whose `H⁰` is
`R[1/ϖ k]` by the sheaf condition; clearing denominators gives *power* killing `∃ M, ∃ w,
(ϖ k)^M • y = e w`.  The upgrade to a single factor is done in two steps.  Write `ϖ k` additively
in the exponent of `T`.

* *Squared killing* (`chartCechH0_root_killing_sq_of_descent`): the engine applied to the `j₀`-chart
  (whose generators are `t_l / T^e`, so that `T^e • (t_l/T^e) = t_l`) together with the integrality
  of the components of a cycle gives, for every level `j`, a witness `r` with `ϖ j • y_{j₀} =
  e(r)`; the error `x_i = ϖ j • y_i - e(r)` in the `i`-th chart then vanishes on the overlap
  `{i, j₀}`, hence is `T`-torsion, hence killed by `ϖ j`.  So `(ϖ j)^2 • z = e (ϖ j · r)`.
* *Level shift*: apply the squared killing at level `k + 1` to the cycle `(ϖ (k+1))^(p-2) • z`.
  Since `(ϖ (k+1))^p = ϖ k`, this yields exactly `ϖ k • z = e w`.

`[Finite ι]` is unused but harmless; `j₀ : ι` makes `ι` nonempty. -/
theorem chartCechH0_root_killing (p : ℕ) [Fact p.Prime] (R : Type a) [CommRing R] [CharP R p]
    [PerfectRing R p] {ι : Type a} [Finite ι] [DecidableEq ι] (t : ι → R) (T : R) (j₀ : ι) (e : ℕ)
    (hj₀ : t j₀ = T ^ e) (k : ℕ)
    (z : (chartCech t).X 0)
    (hz : (chartCech t).d 0 1 z = 0) :
    ∃ w : R, (frobeniusEquiv R p).symm^[k] T • z = (chartCoaugW t).hom w := by
  classical
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  -- the descent hypothesis of the squared killing: a `T`-torsion `0`-cycle with vanishing
  -- `j₀`-component is in the image of the coaugmentation
  have hdesc : ∀ (i : ι) (x : ↥(chartRing t {i})),
      ccRestr t (Finset.subset_union_left : ({i} : Finset ι) ⊆ {i} ∪ {j₀}) x = 0 →
      algebraMap R ↥(chartRing t {i}) T * x = 0 := by
    intro i x hx
    refine chartRing_T_mul_eq_zero_of_chartPow_mul_eq_zero p t T j₀ e hj₀ x ?_
    have hx0 : locRes t (Finset.subset_union_left : ({i} : Finset ι) ⊆ {i} ∪ {j₀})
        (x : Localization.Away (tS t {i})) = 0 := by
      have h1 : ((ccRestr t (Finset.subset_union_left : ({i} : Finset ι) ⊆ {i} ∪ {j₀}) x :
          ↥(chartRing t ({i} ∪ {j₀}))) : Localization.Away (tS t ({i} ∪ {j₀}))) = 0 := by
        rw [hx, Subalgebra.coe_zero]
      rwa [ccRestr_coe] at h1
    exact locRes_eq_zero_imp_pow_mul_eq_zero t _ _ hx0
  -- the squared killing, at level `k + 1`, applied to the multiple `(ϖ (k+1))^(p-2) • z`
  have hz' : (chartCech t).d 0 1 (((frobeniusEquiv R p).symm^[k + 1] T) ^ (p - 2) • z) = 0 := by
    rw [map_smul, hz, smul_zero]
  obtain ⟨w, hw⟩ := chartCechH0_root_killing_sq_of_descent p R t T j₀ e hj₀ hdesc
    (((frobeniusEquiv R p).symm^[k + 1] T) ^ (p - 2) • z) hz' (k + 1)
  refine ⟨w, ?_⟩
  have hstep : ((frobeniusEquiv R p).symm^[k + 1] T) ^ 2 •
        (((frobeniusEquiv R p).symm^[k + 1] T) ^ (p - 2) • z)
      = (frobeniusEquiv R p).symm^[k] T • z := by
    rw [smul_smul, ← pow_add, Nat.add_sub_cancel' hp2,
      frobeniusEquiv_symm_iterate_succ_pow p T k]
  rw [← hstep]
  exact hw

end Work.DSM5b
