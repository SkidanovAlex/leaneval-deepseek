import Submission.Contracts
import Submission.SerreExample
import Submission.SerrePotentialIcc
import Mathlib.Tactic

/-!
# Weak lower bound for the weighted n-norm of nonzero integer polynomials

For every nonzero integer polynomial `Q` of degree `≤ n`, the weighted
`n`-norm is not too small:

    wnorm n (zmap Q) ≥ n^{−C·n}        (some absolute C > 0, all n ≥ 2)

where `wnorm k P := sup_{x ∈ [aSerre,bSerre]} w(x)^k·|P(x)|` with
`w = weight muSerre > 0` bounded away from 0 on the interval
(`weight` is continuous and positive on `Icc aSerre bSerre`; we only need a
crude `weight muSerre x ≥ c0 > 0` for all x in the interval).

This is used by `lem:second_squeeze` (Smith GON.tex) in the case `k = 0`:
there `Q_0 = G·S_0` with `deg S_0 = 0`, and the needed lower bound
`wnorm n (zmap Q_0) ≥ n^{−C·n}` follows from the present lemma applied to the
integer polynomial `G`.

## Proof roadmap (crude grid argument — plenty of slack)

1. **Unweighted lower bound on an interval.**  Show first: there is an
   absolute `A > 0` with
   `sup_{x ∈ [aSerre,bSerre]} |Q(x)| ≥ n^{−A·n}` for every nonzero integer
   `Q` with `natDegree Q ≤ n` and `n ≥ 2`.
   Route: fix an integer scale `r ≥ 0` and consider the grid points
   `x_m = m/2^r` inside `[aSerre, bSerre]` (with `m : ℤ`, or equivalently a
   Finset of naturals in `[⌈aSerre·2^r⌉, ⌊bSerre·2^r⌋]`).  For each such
   `x_m`: `Q(x_m)·(2^r)^n ∈ ℤ` (expand `Q(Σ c_j x^j)`; since `x_m = m/2^r`
   and `Q ∈ ℤ[X]` with `natDegree ≤ n`, `(2^r)^n·Q(m/2^r) = Σ_j c_j·m^j·(2^r)^{n−j}`
   is an integer), so if `Q(x_m) ≠ 0` then `|Q(x_m)| ≥ (2^r)^{−n}`.
   Choose `r` so that the grid has MORE THAN `n` points (the number of grid
   points is at least `(bSerre − aSerre)·2^r − 2 ≥ 4.3·2^r − 2`; pick
   `2^r` of size `≈ n`); since `Q` has at most `n` roots, at least one grid
   point is not a root, giving `sup ≥ (2^r)^{−n} ≥ n^{−A·n}` for some
   absolute `A` (absorb the `(4.3)`-type constants and the small-`n` cases
   by taking `A` large enough; e.g. `2^r ≤ n+3`-type estimates).
   Simplification: you may pick the grid step `1/N` with `N = n + 4` or
   `N = 2^⌈log2 n⌉`-type — ANY concrete choice that yields `sup ≥ n^{−A·n}`
   with absolute `A` is fine.

2. **Weighted version.**  `weight muSerre` is positive and continuous on
   `Icc aSerre bSerre`, so `min_{x ∈ Icc} weight muSerre x =: cw > 0`
   (compactness + positivity; alternatively use the explicit formula
   `weight muSerre x = exp(serreConstant)·x^{−γ}` from
   `Submission.SerrePotentialIcc.weight_serre_on_Icc`, valid on the interval,
   whose minimum over the interval is attained at `x = bSerre` and equals a
   positive constant).  Then
   `wnorm n (zmap Q) ≥ (min over interval of weight^n)·sup|Q| ≥ (cw)^n·n^{−A·n}`.
   Since `cw > 0` is fixed, absorb `(cw)^n` into the constant: `(cw)^n·n^{−A·n}
   ≥ n^{−C·n}` for an absolute `C` (take `C > A` plus a term for `|log cw|`).
   Handle the finitely many small `n` (e.g. `n < n0`) by taking `C` large.

You may add helpers. Axioms ⊆ {propext, Quot.sound, Classical.choice}.
Do not import `Submission.*` modules beyond those in the header (Contracts is
needed for `wnorm`/`zmap`; SerreExample/SerrePotentialIcc for the constants
and the weight positivity; all PROVED).  Deliver exactly `wnorm_lower` below.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace Submission.WnormLower

open Submission.Contracts
open Submission.SerreExample

/-! ## Small helpers -/

/-- Mapping an integer polynomial to `ℝ` is injective, so a nonzero integer
polynomial maps to a nonzero real polynomial. -/
lemma zmap_ne_zero {Q : Polynomial ℤ} (hQ : Q ≠ 0) : zmap Q ≠ 0 := by
  intro h
  apply hQ
  have hmapinj : Function.Injective (Polynomial.map (Int.castRingHom ℝ)) :=
    Polynomial.map_injective _ Int.cast_injective
  exact hmapinj (by simpa [zmap, algebraMap_int_eq] using h)

/-- The algebra map `ℤ → ℝ` is injective. -/
lemma algebraMap_int_real_injective : Function.Injective (algebraMap ℤ ℝ) := by
  intro a b h
  exact_mod_cast (Int.cast_injective h)

/-- Degree is preserved by mapping to `ℝ`. -/
lemma zmap_natDegree (Q : Polynomial ℤ) : (zmap Q).natDegree = Q.natDegree := by
  unfold zmap
  exact Polynomial.natDegree_map_eq_of_injective algebraMap_int_real_injective Q

/-- **Weight is bounded below on the interval by a positive constant**:
the continuous positive weight attains its minimum on the compact interval. -/
lemma exists_weight_lower_bound :
    ∃ c0 : ℝ, 0 < c0 ∧
      ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → c0 ≤ WeightedNorm.weight muSerre x := by
  let f : ℝ → ℝ := fun x => WeightedNorm.weight muSerre x
  have hcont : ContinuousOn f (Set.Icc aSerre bSerre) := by
    simpa [f, muSerre] using WeightedNorm.weight_continuous_on_Icc
  have hcomp : IsCompact (Set.Icc aSerre bSerre) := by
    exact CompactIccSpace.isCompact_Icc
  have hne : (Set.Icc aSerre bSerre).Nonempty := by
    refine ⟨aSerre, ?_⟩
    exact ⟨le_rfl, a_le_b⟩
  rcases hcomp.exists_isMinOn hne hcont with ⟨x0, hx0, hmin⟩
  refine ⟨f x0, ?_, ?_⟩
  · dsimp [f]
    exact WeightedNorm.weight_pos muSerre x0
  · intro x hx
    dsimp [f]
    exact hmin hx

/-- The set whose supremum defines `wnorm n (zmap Q)` is bounded above. -/
lemma wnorm_set_bddAbove (n : ℕ) (Q : Polynomial ℤ) :
    BddAbove ((fun x : ℝ => (WeightedNorm.weight muSerre x) ^ n * |(zmap Q).eval x|) ''
      Set.Icc aSerre bSerre) := by
  have hfun : (fun x : ℝ => (WeightedNorm.weight muSerre x) ^ n * |(zmap Q).eval x|)
      = (fun x : ℝ => (WeightedNorm.weight muSerre x) ^ n * |Polynomial.aeval x Q|) := by
    funext x
    rw [show Polynomial.aeval x Q = (zmap Q).eval x by
      rw [Polynomial.aeval_def]
      unfold zmap
      rw [Polynomial.eval_map]]
  rw [hfun]
  simpa [muSerre] using (WeightedNorm.weightedSup_bounded n Q)

/-! ## The grid -/

/-- There are at least `n+1` naturals `m` with `m/n ∈ [aSerre,bSerre]`
(we use the points `(m : ℝ)/(n:ℝ)` with `m` between `⌊a·n⌋+1` and `⌊b·n⌋`). -/
lemma grid_count (n : ℕ) (hn : 2 ≤ n) :
    n + 1 ≤
      (Finset.Icc (Nat.floor (aSerre * (n : ℝ)) + 1) (Nat.floor (bSerre * (n : ℝ)))).card := by
  let fa : ℕ := Nat.floor (aSerre * (n : ℝ))
  let hi : ℕ := Nat.floor (bSerre * (n : ℝ))
  have hnR0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hapos : 0 ≤ aSerre * (n : ℝ) := mul_nonneg aSerre_pos.le hnR0
  have hflb : (bSerre * (n : ℝ)) - 1 ≤ (Nat.floor (bSerre * (n : ℝ)) : ℝ) := by
    have h := Nat.lt_floor_add_one (bSerre * (n : ℝ))
    linarith
  have hfla : (Nat.floor (aSerre * (n : ℝ)) : ℝ) ≤ aSerre * (n : ℝ) := Nat.floor_le hapos
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlen : 4 ≤ bSerre - aSerre := le_of_lt cap_gt_one
  have hlen_mul : 4 * (n : ℝ) ≤ (bSerre - aSerre) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right hlen hnR0
  have hdiff : (n : ℝ) + 1 ≤ (hi : ℝ) - (fa : ℝ) := by
    dsimp [hi, fa]
    have h1 : (Nat.floor (bSerre * (n : ℝ)) : ℝ) - (Nat.floor (aSerre * (n : ℝ)) : ℝ) ≥
        (bSerre * (n : ℝ)) - 1 - aSerre * (n : ℝ) := by linarith
    calc
      (n : ℝ) + 1 ≤ (bSerre - aSerre) * (n : ℝ) - 1 := by nlinarith [hlen_mul, hn2]
      _ = (bSerre * (n : ℝ)) - 1 - aSerre * (n : ℝ) := by ring
      _ ≤ (Nat.floor (bSerre * (n : ℝ)) : ℝ) - (Nat.floor (aSerre * (n : ℝ)) : ℝ) := by linarith
  have hdiff2 : (fa : ℝ) + (n : ℝ) + 1 ≤ (hi : ℝ) := by
    dsimp [hi, fa] at hdiff ⊢
    linarith
  have hinat : fa + (n + 1) ≤ hi := by
    exact_mod_cast hdiff2
  have htarget : n + 1 ≤ (Finset.Icc (fa + 1) hi).card := by
    rw [Nat.card_Icc]
    omega
  simpa [fa, hi] using htarget

/-- Every grid point `m/n` lies in the Serre interval. -/
lemma grid_point_mem (n m : ℕ) (hn : 2 ≤ n)
    (hm : m ∈ Finset.Icc (Nat.floor (aSerre * (n : ℝ)) + 1) (Nat.floor (bSerre * (n : ℝ)))) :
    (m : ℝ) / (n : ℝ) ∈ Set.Icc aSerre bSerre := by
  have hnpos : 0 < (n : ℝ) := by
    have h1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  have hlo : m ≥ Nat.floor (aSerre * (n : ℝ)) + 1 := (Finset.mem_Icc.mp hm).1
  have hhi : m ≤ Nat.floor (bSerre * (n : ℝ)) := (Finset.mem_Icc.mp hm).2
  constructor
  · have hle : (Nat.floor (aSerre * (n : ℝ)) : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hlo
    have hgt : aSerre * (n : ℝ) < (Nat.floor (aSerre * (n : ℝ)) : ℝ) + 1 := by
      simpa using (Nat.lt_floor_add_one (aSerre * (n : ℝ)))
    have hmgt : aSerre * (n : ℝ) < (m : ℝ) := lt_of_lt_of_le hgt hle
    rw [le_div_iff₀ hnpos]
    exact le_of_lt hmgt
  · have hle2 : (m : ℝ) ≤ (Nat.floor (bSerre * (n : ℝ)) : ℝ) := by exact_mod_cast hhi
    have hflb : (Nat.floor (bSerre * (n : ℝ)) : ℝ) ≤ bSerre * (n : ℝ) :=
      Nat.floor_le (mul_nonneg bSerre_pos.le (by exact_mod_cast (Nat.zero_le n)))
    have hmle : (m : ℝ) ≤ bSerre * (n : ℝ) := le_trans hle2 hflb
    rw [div_le_iff₀ hnpos]
    exact hmle

/-- At the grid points the scaled evaluations are integers:
`(n:ℝ)^n · (zmap Q).eval((m:ℝ)/(n:ℝ))` is the image of an integer
(`n^i·Q(m/n)` clears denominators because `natDegree Q ≤ n`). -/
lemma zmap_eval_mul_pow_int (Q : Polynomial ℤ) (n m : ℕ) (hn : 1 ≤ n)
    (hdeg : Q.natDegree ≤ n) :
    ∃ z : ℤ, (z : ℝ) = ((n : ℝ) ^ n) * (zmap Q).eval ((m : ℝ) / (n : ℝ)) := by
  let x : ℝ := (m : ℝ) / (n : ℝ)
  have hevP : (zmap Q).eval x =
      ∑ i ∈ Finset.range (Q.natDegree + 1), ((Q.coeff i : ℝ) * (x ^ i)) := by
    unfold zmap
    rw [Polynomial.eval_map]
    rw [Polynomial.eval₂_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    rfl
  have hnRne : (n : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hn))
  have hterm : ∀ i ∈ Finset.range (Q.natDegree + 1),
      ((n : ℝ) ^ n) * ((Q.coeff i : ℝ) * (x ^ i)) =
        (Q.coeff i : ℝ) * (m : ℝ) ^ i * (n : ℝ) ^ (n - i) := by
    intro i hi
    have hi_le : i ≤ n := by
      have hi' : i < Q.natDegree + 1 := Finset.mem_range.mp hi
      omega
    calc
      ((n : ℝ) ^ n) * ((Q.coeff i : ℝ) * (x ^ i))
          = (Q.coeff i : ℝ) * (((n : ℝ) ^ n) * (((m : ℝ) / (n : ℝ)) ^ i)) := by
            dsimp [x]
            ring
      _ = (Q.coeff i : ℝ) * ((m : ℝ) ^ i * (n : ℝ) ^ (n - i)) := by
            congr 1
            calc
              ((n : ℝ) ^ n) * (((m : ℝ) / (n : ℝ)) ^ i)
                  = (n : ℝ) ^ n * ((m : ℝ) ^ i / (n : ℝ) ^ i) := by rw [div_pow]
              _ = (n : ℝ) ^ (n - i) * (n : ℝ) ^ i * ((m : ℝ) ^ i / (n : ℝ) ^ i) := by
                    congr 1
                    rw [← pow_add, Nat.sub_add_cancel hi_le]
              _ = (m : ℝ) ^ i * (n : ℝ) ^ (n - i) := by
                    field_simp [pow_ne_zero i hnRne, hnRne]
      _ = (Q.coeff i : ℝ) * (m : ℝ) ^ i * (n : ℝ) ^ (n - i) := by ring
  let z : ℤ := ∑ i ∈ Finset.range (Q.natDegree + 1),
      Q.coeff i * (m : ℤ) ^ i * (n : ℤ) ^ (n - i)
  refine ⟨z, ?_⟩
  calc
    (z : ℝ) = ∑ i ∈ Finset.range (Q.natDegree + 1),
        (((Q.coeff i * (m : ℤ) ^ i * (n : ℤ) ^ (n - i)) : ℤ) : ℝ) := by
          dsimp [z]
          rw [Int.cast_sum]
    _ = ∑ i ∈ Finset.range (Q.natDegree + 1),
        (Q.coeff i : ℝ) * (m : ℝ) ^ i * (n : ℝ) ^ (n - i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Int.cast_mul, Int.cast_mul, Int.cast_pow, Int.cast_pow]
          norm_num
    _ = ∑ i ∈ Finset.range (Q.natDegree + 1),
        ((n : ℝ) ^ n) * ((Q.coeff i : ℝ) * (x ^ i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact (hterm i hi).symm
    _ = ((n : ℝ) ^ n) *
        (∑ i ∈ Finset.range (Q.natDegree + 1), ((Q.coeff i : ℝ) * (x ^ i))) := by
          rw [Finset.mul_sum]
    _ = ((n : ℝ) ^ n) * (zmap Q).eval x := by rw [hevP]

/-- Some grid point is not a root of `Q` (there are more grid points than
`natDegree` allows roots). -/
lemma grid_good (n : ℕ) (hn : 2 ≤ n) (Q : Polynomial ℤ) (hQ : Q ≠ 0)
    (hdeg : Q.natDegree ≤ n) :
    ∃ m : ℕ,
      m ∈ Finset.Icc (Nat.floor (aSerre * (n : ℝ)) + 1) (Nat.floor (bSerre * (n : ℝ))) ∧
        (zmap Q).eval ((m : ℝ) / (n : ℝ)) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  let P : Polynomial ℝ := zmap Q
  have hP : P ≠ 0 := by
    dsimp [P]
    exact zmap_ne_zero hQ
  have hdegP : P.natDegree ≤ n := by
    calc
      P.natDegree = Q.natDegree := by
        dsimp [P]
        exact zmap_natDegree Q
      _ ≤ n := hdeg
  have hMcard : n + 1 ≤
      (Finset.Icc (Nat.floor (aSerre * (n : ℝ)) + 1) (Nat.floor (bSerre * (n : ℝ)))).card :=
    grid_count n hn
  let M : Finset ℕ := Finset.Icc (Nat.floor (aSerre * (n : ℝ)) + 1) (Nat.floor (bSerre * (n : ℝ)))
  have hMcard2 : n + 1 ≤ M.card := by
    simpa [M] using hMcard
  let S : Finset ℝ := M.image (fun m : ℕ => (m : ℝ) / (n : ℝ))
  have hSmem_root : ∀ y ∈ S, P.IsRoot y := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨m, hm, rfl⟩
    have hev : P.eval ((m : ℝ) / (n : ℝ)) = 0 := by
      dsimp [P]
      exact h m hm
    exact hev
  have hSmem : ∀ y ∈ S, y ∈ P.roots := by
    intro y hy
    exact (Polynomial.mem_roots hP).mpr (hSmem_root y hy)
  have hSsub : S ⊆ P.roots.toFinset := by
    intro y hy
    exact Multiset.mem_toFinset.mpr (hSmem y hy)
  have hcard1 : S.card ≤ P.roots.card := by
    exact le_trans (Finset.card_le_card hSsub) (Multiset.toFinset_card_le P.roots)
  have hcard2 : P.roots.card ≤ n := by
    calc
      P.roots.card ≤ P.natDegree := Polynomial.card_roots' P
      _ ≤ n := hdegP
  have hS_eq : S.card = M.card := by
    refine Finset.card_image_of_injOn ?_
    intro m hm m' hm' hEq
    have hdn : (n : ℝ) ≠ 0 := by
      exact_mod_cast (by omega : n ≠ 0)
    have hcross : (m : ℝ) = (m' : ℝ) := by
      field_simp [hdn] at hEq
      exact hEq
    exact_mod_cast hcross
  omega

/-- **Unweighted lower bound on the interval**: some grid point satisfies
`|Q(x)| ≥ n^{−n}`, in particular the sup norm is at least `n^{−n}`. -/
lemma grid_lower (n : ℕ) (hn : 2 ≤ n) (Q : Polynomial ℤ) (hQ : Q ≠ 0)
    (hdeg : Q.natDegree ≤ n) :
    ∃ x : ℝ, x ∈ Set.Icc aSerre bSerre ∧ (((n : ℝ) ^ n)⁻¹) ≤ |(zmap Q).eval x| := by
  rcases grid_good n hn Q hQ hdeg with ⟨m, hmM, hne0⟩
  refine ⟨(m : ℝ) / (n : ℝ), grid_point_mem n m hn hmM, ?_⟩
  rcases zmap_eval_mul_pow_int Q n m (by omega) hdeg with ⟨z, hz⟩
  have hz_ne : z ≠ 0 := by
    intro hz0
    apply hne0
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hz0' : ((n : ℝ) ^ n) * (zmap Q).eval ((m : ℝ) / (n : ℝ)) = 0 := by
      rw [← hz]
      norm_num [hz0]
    have hprod : (n : ℝ) ^ n ≠ 0 := pow_ne_zero n hnR
    exact (mul_eq_zero.mp hz0').resolve_left hprod
  have hzabs : 1 ≤ |(z : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hz_ne)
  have habs : |((n : ℝ) ^ n) * (zmap Q).eval ((m : ℝ) / (n : ℝ))| =
      ((n : ℝ) ^ n) * |(zmap Q).eval ((m : ℝ) / (n : ℝ))| := by
    rw [abs_mul]
    rw [abs_of_nonneg (pow_nonneg (by exact_mod_cast (Nat.zero_le n)) n)]
  have hmain : 1 ≤ (n : ℝ) ^ n * |(zmap Q).eval ((m : ℝ) / (n : ℝ))| := by
    calc
      1 ≤ |(z : ℝ)| := hzabs
      _ = |((n : ℝ) ^ n) * (zmap Q).eval ((m : ℝ) / (n : ℝ))| := by rw [← hz]
      _ = (n : ℝ) ^ n * |(zmap Q).eval ((m : ℝ) / (n : ℝ))| := habs
  have hpowpos : 0 < (n : ℝ) ^ n := by
    have hnpos : 0 < (n : ℝ) := by
      have h1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
      linarith
    exact pow_pos hnpos n
  have hY : 0 ≤ ((n : ℝ) ^ n)⁻¹ := inv_nonneg.mpr (le_of_lt hpowpos)
  have hmul := mul_le_mul_of_nonneg_right hmain hY
  calc
    ((n : ℝ) ^ n)⁻¹ = 1 * ((n : ℝ) ^ n)⁻¹ := by rw [one_mul]
    _ ≤ ((n : ℝ) ^ n * |(zmap Q).eval ((m : ℝ) / (n : ℝ))|) * ((n : ℝ) ^ n)⁻¹ := by
          simpa using hmul
    _ = |(zmap Q).eval ((m : ℝ) / (n : ℝ))| := by
          have hpowne : (n : ℝ) ^ n ≠ 0 := pow_ne_zero n (by exact_mod_cast (by omega : n ≠ 0))
          field_simp [hpowne]

/-! ## The weighted lower bound on the whole norm -/

/-- Combining the grid point bound with `weight ≥ c0`:
`wnorm n (zmap Q) ≥ c0^n · n^{−n}`. -/
lemma wnorm_grid_lower {c0 : ℝ} {n : ℕ} {Q : Polynomial ℤ} (hc0 : 0 < c0)
    (hwb : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → c0 ≤ WeightedNorm.weight muSerre x)
    (hn : 2 ≤ n) (hQ : Q ≠ 0) (hdeg : Q.natDegree ≤ n) :
    c0 ^ n * (((n : ℝ) ^ n)⁻¹) ≤ wnorm n (zmap Q) := by
  rcases grid_lower n hn Q hQ hdeg with ⟨x, hx, hgrid⟩
  have hwle : c0 ≤ WeightedNorm.weight muSerre x := hwb x hx
  have hc0pow : c0 ^ n ≤ (WeightedNorm.weight muSerre x) ^ n :=
    pow_le_pow_left₀ hc0.le hwle n
  have hc0n_nonneg : 0 ≤ c0 ^ n := pow_nonneg hc0.le n
  have hw_nonneg : 0 ≤ (WeightedNorm.weight muSerre x) ^ n :=
    pow_nonneg (WeightedNorm.weight_pos muSerre x).le n
  have hinv_nonneg : 0 ≤ ((n : ℝ) ^ n)⁻¹ :=
    inv_nonneg.mpr (pow_nonneg (by exact_mod_cast (Nat.zero_le n)) n)
  have hprod : c0 ^ n * (((n : ℝ) ^ n)⁻¹) ≤
      (WeightedNorm.weight muSerre x) ^ n * |(zmap Q).eval x| := by
    exact mul_le_mul hc0pow hgrid hinv_nonneg hw_nonneg
  have hmem : (WeightedNorm.weight muSerre x) ^ n * |(zmap Q).eval x| ∈
      ((fun x : ℝ => (WeightedNorm.weight muSerre x) ^ n * |(zmap Q).eval x|) ''
        Set.Icc aSerre bSerre) :=
    ⟨x, hx, rfl⟩
  have hbdd : BddAbove
      ((fun x : ℝ => (WeightedNorm.weight muSerre x) ^ n * |(zmap Q).eval x|) ''
        Set.Icc aSerre bSerre) :=
    wnorm_set_bddAbove n Q
  have hsup : (WeightedNorm.weight muSerre x) ^ n * |(zmap Q).eval x| ≤ wnorm n (zmap Q) := by
    dsimp [wnorm]
    exact le_csSup hbdd hmem
  exact le_trans hprod hsup

/-! ## Absorbing the fixed positive constant into `n^{−C·n}` -/

/-- Archimedean choice of `m` with `c0 ≥ (1/2)^m`. -/
lemma exists_two_pow_inv_le {c0 : ℝ} (hc0 : 0 < c0) :
    ∃ m : ℕ, 1 ≤ m ∧ ((2 : ℝ) ^ m)⁻¹ ≤ c0 := by
  have hpos : 0 < 1 / c0 := one_div_pos.mpr hc0
  rcases exists_nat_gt (1 / c0) with ⟨t, ht⟩
  refine ⟨t, ?_, ?_⟩
  · have htR : (0 : ℝ) < (t : ℝ) := lt_of_lt_of_le hpos (le_of_lt ht)
    have ht' : 0 < t := by exact_mod_cast htR
    omega
  · have hnat : t < 2 ^ t := Nat.lt_two_pow_self
    have hnatR : (t : ℝ) < ((2 ^ t : ℕ) : ℝ) := by exact_mod_cast hnat
    have hEq : ((2 ^ t : ℕ) : ℝ) = (2 : ℝ) ^ t := by
      rw [Nat.cast_pow]
      norm_num
    have hlt : 1 / c0 < (2 : ℝ) ^ t := lt_trans ht (by simpa [hEq] using hnatR)
    have h1c : 1 < (2 : ℝ) ^ t * c0 := by
      have hm := mul_lt_mul_of_pos_right hlt hc0
      have hc : (1 / c0) * c0 = 1 := by field_simp [hc0.ne']
      rwa [hc] at hm
    have h2t : 0 < (2 : ℝ) ^ t := pow_pos (by norm_num) t
    have hfin : ((2 : ℝ) ^ t)⁻¹ < c0 := by
      have hm := mul_lt_mul_of_pos_left h1c (inv_pos.mpr h2t)
      have htwo_ne : (2 : ℝ) ^ t ≠ 0 := pow_ne_zero t (by norm_num)
      calc
        ((2 : ℝ) ^ t)⁻¹ = ((2 : ℝ) ^ t)⁻¹ * 1 := by rw [mul_one]
        _ < ((2 : ℝ) ^ t)⁻¹ * ((2 : ℝ) ^ t * c0) := hm
        _ = c0 := by
          rw [← mul_assoc, inv_mul_cancel₀ htwo_ne, one_mul]
    exact le_of_lt hfin

/-- Pure power comparison: for `c0 ≥ 2^{−m}` and `n ≥ 2`,
`n^{−(m+2)n} ≤ c0^n·n^{−n}`. -/
lemma natural_pow_compare {c0 : ℝ} {m n : ℕ} (_hm : 1 ≤ m) (hn : 2 ≤ n)
    (hcm : ((2 : ℝ) ^ m)⁻¹ ≤ c0) :
    ((n : ℝ) ^ ((m + 2) * n))⁻¹ ≤ c0 ^ n * ((n : ℝ) ^ n)⁻¹ := by
  have hnRpos : 0 < (n : ℝ) := by
    have h1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnRne : (n : ℝ) ≠ 0 := ne_of_gt hnRpos
  have hc0pos : 0 < c0 := lt_of_lt_of_le (inv_pos.mpr (pow_pos (by norm_num : (0 : ℝ) < 2) m)) hcm
  -- c0^n ≥ (2^{m·n})⁻¹:
  have hpow_c0 : ((2 : ℝ) ^ m)⁻¹ ^ n ≤ c0 ^ n :=
    pow_le_pow_left₀ (inv_nonneg.mpr (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) m)) hcm n
  have hc0n : ((2 : ℝ) ^ (m * n))⁻¹ ≤ c0 ^ n := by
    calc
      ((2 : ℝ) ^ (m * n))⁻¹ = ((2 : ℝ) ^ m)⁻¹ ^ n := by
        rw [inv_pow, ← pow_mul]
      _ ≤ c0 ^ n := hpow_c0
  -- nR^{(m+1)n} ≥ 2^{m·n}:
  have hmn : m * n ≤ (m + 1) * n := by
    calc
      m * n ≤ m * n + n := Nat.le_add_right _ _
      _ = (m + 1) * n := by ring
  have hbig : (2 : ℝ) ^ (m * n) ≤ (n : ℝ) ^ ((m + 1) * n) := by
    calc
      (2 : ℝ) ^ (m * n) ≤ (2 : ℝ) ^ ((m + 1) * n) := by
        apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        exact hmn
      _ ≤ (n : ℝ) ^ ((m + 1) * n) := by
        exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hn2 ((m + 1) * n)
  have htwo_ne : (2 : ℝ) ^ (m * n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hmain : 1 ≤ c0 ^ n * (n : ℝ) ^ ((m + 1) * n) := by
    have hmul := mul_le_mul hc0n hbig (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) (pow_nonneg hc0pos.le n)
    simpa [inv_mul_cancel₀ htwo_ne] using hmul
  -- divide by nR^{(m+1)n}:
  have hXpos : 0 < (n : ℝ) ^ ((m + 1) * n) := pow_pos hnRpos _
  have hXinv : ((n : ℝ) ^ ((m + 1) * n))⁻¹ ≤ c0 ^ n := by
    have hm2 := mul_le_mul_of_nonneg_right hmain (inv_nonneg.mpr (le_of_lt hXpos))
    calc
      ((n : ℝ) ^ ((m + 1) * n))⁻¹ = 1 * ((n : ℝ) ^ ((m + 1) * n))⁻¹ := by rw [one_mul]
      _ ≤ (c0 ^ n * (n : ℝ) ^ ((m + 1) * n)) * ((n : ℝ) ^ ((m + 1) * n))⁻¹ := by
        simpa using hm2
      _ = c0 ^ n := by
        field_simp [pow_ne_zero ((m + 1) * n) hnRne]
  -- final assembly: nR^{((m+2)n)}⁻¹ = nR^{((m+1)n)}⁻¹·(nR^n)⁻¹ ≤ c0^n·(nR^n)⁻¹:
  have hmm : (m + 1) * n + n = (m + 2) * n := by ring
  calc
    ((n : ℝ) ^ ((m + 2) * n))⁻¹ = ((n : ℝ) ^ ((m + 1) * n + n))⁻¹ := by
      rw [← hmm]
    _ = ((n : ℝ) ^ ((m + 1) * n) * (n : ℝ) ^ n)⁻¹ := by rw [pow_add]
    _ = ((n : ℝ) ^ ((m + 1) * n))⁻¹ * ((n : ℝ) ^ n)⁻¹ := mul_inv _ _
    _ ≤ c0 ^ n * ((n : ℝ) ^ n)⁻¹ := by
      apply mul_le_mul_of_nonneg_right hXinv
      exact inv_nonneg.mpr (pow_nonneg (by exact_mod_cast (Nat.zero_le n)) n)

/-- The same inequality with the real-power exponent `n^{−((m:ℝ)+2)·n}`. -/
lemma real_pow_compare {c0 : ℝ} {m n : ℕ} (_hm : 1 ≤ m) (hn : 2 ≤ n)
    (hcm : ((2 : ℝ) ^ m)⁻¹ ≤ c0) :
    (n : ℝ) ^ (-(((m : ℝ) + 2) * (n : ℝ))) ≤ c0 ^ n * ((n : ℝ) ^ n)⁻¹ := by
  have hE : -(((m : ℝ) + 2) * (n : ℝ)) = -(((m + 2) * n : ℕ) : ℝ) := by
    norm_num [Nat.cast_mul]
  rw [hE]
  rw [Real.rpow_neg]
  · rw [Real.rpow_natCast]
    exact natural_pow_compare _hm hn hcm
  · exact_mod_cast (Nat.zero_le n)

/-- MAIN RESULT: weak lower bound. -/
theorem wnorm_lower : ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 2 ≤ n → ∀ Q : Polynomial ℤ, Q ≠ 0 → Q.natDegree ≤ n →
      (n : ℝ) ^ (-C * (n : ℝ)) ≤ wnorm n (zmap Q) := by
  rcases exists_weight_lower_bound with ⟨c0, hc0, hwb⟩
  rcases exists_two_pow_inv_le hc0 with ⟨m, hm1, hcm⟩
  refine ⟨(m : ℝ) + 2, ?_, ?_⟩
  · positivity
  · intro n hn Q hQ hdeg
    have hw : c0 ^ n * (((n : ℝ) ^ n)⁻¹) ≤ wnorm n (zmap Q) :=
      wnorm_grid_lower hc0 hwb hn hQ hdeg
    have hmain : (n : ℝ) ^ (-(((m : ℝ) + 2) * (n : ℝ))) ≤ wnorm n (zmap Q) :=
      le_trans (real_pow_compare hm1 hn hcm) hw
    have hE : -((m : ℝ) + 2) * (n : ℝ) = -(((m : ℝ) + 2) * (n : ℝ)) := by ring
    rwa [hE]

end Submission.WnormLower
