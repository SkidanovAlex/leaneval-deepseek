import Mathlib
import Submission.Work.WilE4.CAD.Proj
import Submission.Work.WilE4.CAD.signConst_data
import Submission.Work.WilE4.CAD.Minors
import Submission.Work.WilE4.Poly.spec_pderiv
import Submission.Work.WilE4.CAD.threshold_along_tendsto
import Submission.Work.WilE4.CAD.type_local
import Submission.Work.WilE4.CAD.realized_of_tendsto_bdd_good
import Submission.Work.WilE4.CAD.realized_of_tendsto_unbdd_good
import Submission.Work.WilE4.CAD.cell_preconnected
import Submission.Work.WilE4.CAD.realized_const_on_preconnected_good
import Submission.Work.WilE4.CAD.seq_bounded
import Submission.Work.WilE4.CAD.seq_cluster_data

/-!
# Sequential closedness of the realised-sign-vector set (Sylvester-minor data)

`seq_closed_minor`: if a sign vector `v'` is realised at every point of a sequence `x n ∈ C`
converging to `x₀ ∈ C`, and on `C` the signs of all coefficients (up to degree `D`) and of *all*
submatrix determinants of the Sylvester matrices of pairs of specialisations are constant, then
`v'` is realised at `x₀`.

## Structure of the argument

Split on the behaviour of the witnesses `t n` realising `v'` at `x n`:

* **Unbounded witnesses** (`realized_of_frequently_unbounded`): if `|t n|` is frequently
  arbitrarily large, the sign vector realised at `(x n, t n)` is determined by the leading
  coefficients and the degrees — data whose signs are constant on `C` — hence is also realised at
  `x₀` by a sufficiently large argument.  Uses `threshold_along_tendsto` plus the constancy of the
  `natDegree` and of the leading coefficient's sign on `C` (both consequences of `hcoeff`).

* **Bounded witnesses**: extract a convergent subsequence `t n → t*`, so that
  `t* ∈ pcellCl (F x₀) v'` (the closed sign-condition set of `Fibre.lean`).  The remaining point is
  that no *additional* member may vanish at `(x₀, t*)`: a member `f i` with `f i (x₀, t*) = 0` and
  `v' i ≠ 0` forces two root branches to collide at `(x₀, t*)`, which makes a Sylvester minor
  vanish at `x₀` and hence (by `hmin`, since both `x₀, x n ∈ C`) at every point of `C`.  Repeatedly
  applying this "detection" to the cofactors of the colliding branches exhibits a Sylvester minor
  that vanishes at `x₀` without vanishing identically — contradicting `hmin`.

## Status

The two lemmas `realized_of_frequently_unbounded` (unbounded witnesses) and
`seq_closed_minor_of_good` (non-degenerate family, via `realized_of_tendsto_good`) are proved here.
The bounded, degenerate case requires the classical Lazard/McCallum *delineability* theory
(subresultant / Sturm data): the present data (`hmin`) contains the principal subresultant
coefficients, but formalising the correspondence "signs of the subresultants determine the real
root structure" is a substantial development, and is the only missing ingredient of the proof
below.
-/

namespace Work.WilE4.CAD

open Classical Filter
open scoped Topology
open MvPolynomial Polynomial
open Work.WilE4 (spec)

set_option maxHeartbeats 2000000

/-- `hcoeff` stated with the bound `D` gives `CoeffConst`. -/
theorem coeffConst_of_hcoeff {m k : ℕ} {P : Fin k → MvPolynomial (Fin (m + 1)) ℝ} {D : ℕ}
    (hD : ∀ i : Fin k, (P i).degreeOf (Fin.last m) ≤ D) {C : Set (Fin m → ℝ)}
    (hcoeff : ∀ i : Fin k, ∀ j : ℕ, j ≤ D → ∀ x ∈ C, ∀ x' ∈ C,
      SignType.sign ((spec (P i) x).coeff j) = SignType.sign ((spec (P i) x').coeff j)) :
    CoeffConst P C :=
  fun i j hj x hx x' hx' => hcoeff i j (le_trans hj (hD i)) x hx x' hx'

/-- The `natDegree` of the specialisation of a member is constant on `C`. -/
theorem natDegree_spec_const_of_hcoeff {m k : ℕ} {P : Fin k → MvPolynomial (Fin (m + 1)) ℝ}
    {D : ℕ} (hD : ∀ i : Fin k, (P i).degreeOf (Fin.last m) ≤ D) {C : Set (Fin m → ℝ)}
    (hcoeff : ∀ i : Fin k, ∀ j : ℕ, j ≤ D → ∀ x ∈ C, ∀ x' ∈ C,
      SignType.sign ((spec (P i) x).coeff j) = SignType.sign ((spec (P i) x').coeff j)) :
    ∀ i : Fin k, ∀ x ∈ C, ∀ x' ∈ C,
      (spec (P i) x).natDegree = (spec (P i) x').natDegree :=
  fun i x hx x' hx' => natDegree_spec_const (coeffConst_of_hcoeff hD hcoeff) hx hx'

/-- The sign of the leading coefficient of the specialisation of a member is constant on `C`. -/
theorem leadingCoeff_sign_const_of_hcoeff {m k : ℕ}
    {P : Fin k → MvPolynomial (Fin (m + 1)) ℝ} {D : ℕ}
    (hD : ∀ i : Fin k, (P i).degreeOf (Fin.last m) ≤ D) {C : Set (Fin m → ℝ)}
    (hcoeff : ∀ i : Fin k, ∀ j : ℕ, j ≤ D → ∀ x ∈ C, ∀ x' ∈ C,
      SignType.sign ((spec (P i) x).coeff j) = SignType.sign ((spec (P i) x').coeff j)) :
    ∀ i : Fin k, ∀ x ∈ C, ∀ x' ∈ C,
      SignType.sign ((spec (P i) x).leadingCoeff)
        = SignType.sign ((spec (P i) x').leadingCoeff) := by
  intro i x hx x' hx'
  have hnd := natDegree_spec_const_of_hcoeff hD hcoeff i x hx x' hx'
  have hle : (spec (P i) x').natDegree ≤ D :=
    (natDegree_spec_le (P i) x').trans (hD i)
  rw [← Polynomial.coeff_natDegree (p := spec (P i) x),
    ← Polynomial.coeff_natDegree (p := spec (P i) x'), hnd]
  exact (hcoeff i _ hle x' hx' x hx).symm

/-- **Unbounded witnesses.**  If `v'` is realised at `(x n, t n)` with `|t n|` frequently
arbitrarily large, then `v'` is realised at `x₀` (by a large argument). -/
theorem realized_of_frequently_unbounded {m k : ℕ} (P : Fin k → MvPolynomial (Fin (m + 1)) ℝ)
    {d : Fin k → ℕ} {C : Set (Fin m → ℝ)}
    (hdeg : ∀ i : Fin k, ∀ x ∈ C, (spec (P i) x).natDegree = d i)
    (hlc : ∀ i : Fin k, ∀ x ∈ C, ∀ x' ∈ C,
      SignType.sign ((spec (P i) x).leadingCoeff)
        = SignType.sign ((spec (P i) x').leadingCoeff))
    (hzero : ∀ i : Fin k, ∀ x ∈ C, ∀ x' ∈ C, (spec (P i) x = 0 ↔ spec (P i) x' = 0))
    {x : ℕ → Fin m → ℝ} (hxC : ∀ n, x n ∈ C) {x₀ : Fin m → ℝ} (hx₀ : x₀ ∈ C)
    (hlim : Tendsto x atTop (nhds x₀))
    {v' : Fin k → SignType} {w : ℕ → ℝ}
    (hwv : ∀ n, ∀ i, SignType.sign ((spec (P i) (x n)).eval (w n)) = v' i)
    (hunb : ∀ M : ℝ, ∃ᶠ n in atTop, M < |w n|) :
    ∃ t : ℝ, ∀ i, SignType.sign ((spec (P i) x₀).eval t) = v' i := by
  classical
  have hthr : ∀ i : Fin k, ∃ R > 0,
      (∀ y : ℝ, R ≤ |y| → SignType.sign ((spec (P i) x₀).eval y)
          = SignType.sign ((spec (P i) x₀).coeff (d i)) * SignType.sign y ^ (d i)) ∧
      (∀ᶠ n in atTop, ∀ y : ℝ, R ≤ |y| →
          SignType.sign ((spec (P i) (x n)).eval y)
            = SignType.sign ((spec (P i) (x n)).coeff (d i)) * SignType.sign y ^ (d i)) :=
    fun i => threshold_along_tendsto (Q := fun y => spec (P i) y) (x₀ := x₀) (a := x) (d := d i)
      (continuous_spec_coeff (P i)) hlim (hdeg i x₀ hx₀) (fun n => hdeg i (x n) (hxC n))
  choose R hRpos hR using hthr
  have hRle : ∀ i, R i ≤ 1 + ∑ i, R i := by
    intro i
    have h2 : R i ≤ ∑ j, R j :=
      Finset.single_le_sum (fun j _ => le_of_lt (hRpos j)) (Finset.mem_univ i)
    linarith
  set M : ℝ := 1 + ∑ i, R i with hMdef
  have hMpos : 0 < M := by
    have h0 : 0 ≤ ∑ i, R i := Finset.sum_nonneg fun i _ => le_of_lt (hRpos i)
    rw [hMdef]; linarith
  have hsgn : ∀ i, ∀ᶠ n in atTop,
      SignType.sign ((spec (P i) (x n)).coeff (d i))
        = SignType.sign ((spec (P i) x₀).coeff (d i)) := by
    intro i
    by_cases hz : (spec (P i) x₀) = 0
    · have hd0 : d i = 0 := by rw [← hdeg i x₀ hx₀, hz, Polynomial.natDegree_zero]
      filter_upwards with n
      have h1 : (spec (P i) (x n)).coeff (d i) = 0 := by
        rw [hd0, (hzero i (x n) (hxC n) x₀ hx₀).mpr hz]; simp
      have h2 : (spec (P i) x₀).coeff (d i) = 0 := by rw [hd0, hz]; simp
      rw [h1, h2]
    · filter_upwards [hlim.eventually (eventually_sign_eq_of_ne_zero
        (continuous_spec_coeff (P i) (d i)).continuousAt (by
          rw [show (spec (P i) x₀).coeff (d i) = (spec (P i) x₀).leadingCoeff from by
            rw [← hdeg i x₀ hx₀, Polynomial.coeff_natDegree]]
          exact Polynomial.leadingCoeff_ne_zero.mpr hz))] with n hn
      simpa using hn
  have hev : ∀ᶠ n in atTop,
      (∀ i, SignType.sign ((spec (P i) (x n)).coeff (d i))
        = SignType.sign ((spec (P i) x₀).coeff (d i))) ∧
      (∀ i, ∀ y : ℝ, M ≤ |y| →
        SignType.sign ((spec (P i) (x n)).eval y)
          = SignType.sign ((spec (P i) (x n)).coeff (d i)) * SignType.sign y ^ (d i)) :=
    ((Filter.eventually_all).mpr hsgn).and
      ((Filter.eventually_all).mpr fun i => (hR i).2.mono fun n hn y hy =>
        hn y (le_trans (hRle i) hy))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨n₀, hw₀, hn₀⟩ : ∃ n, M < |w n| ∧ N ≤ n :=
    ((hunb M).and_eventually (Filter.eventually_atTop.mpr ⟨N, fun _ hn => hn⟩)).exists
  obtain ⟨hsgn₀, hform₀⟩ := hN n₀ hn₀
  have hwne : w n₀ ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hw₀; linarith
  rcases lt_or_gt_of_ne hwne with hneg | hpos
  · refine ⟨-M, fun i => ?_⟩
    have habs : M ≤ |-M| := by rw [abs_neg, abs_of_pos hMpos]
    have h1 : SignType.sign ((spec (P i) x₀).eval (-M))
        = SignType.sign ((spec (P i) x₀).coeff (d i)) * SignType.sign (-M) ^ (d i) :=
      (hR i).1 (-M) (le_trans (hRle i) habs)
    have h2 : v' i = SignType.sign ((spec (P i) x₀).coeff (d i))
        * SignType.sign (-M) ^ (d i) := by
      rw [← hwv n₀ i, hform₀ i (w n₀) (le_of_lt hw₀), hsgn₀ i, sign_neg hneg,
        show SignType.sign (-M) = -1 from sign_neg (by linarith : -M < 0)]
    rw [h1, h2]
  · refine ⟨M, fun i => ?_⟩
    have habs : M ≤ |M| := by rw [abs_of_pos hMpos]
    have h1 : SignType.sign ((spec (P i) x₀).eval M)
        = SignType.sign ((spec (P i) x₀).coeff (d i)) * SignType.sign M ^ (d i) :=
      (hR i).1 M (le_trans (hRle i) habs)
    have h2 : v' i = SignType.sign ((spec (P i) x₀).coeff (d i)) * SignType.sign M ^ (d i) := by
      rw [← hwv n₀ i, hform₀ i (w n₀) (le_of_lt hw₀), hsgn₀ i, sign_pos hpos, sign_pos hMpos]
    rw [h1, h2]

/-- **The "good" case.**  If the non-degeneracy conditions `Good` hold at `x₀` and at every
`x n` (with the degree function `d`), the conclusion follows from `realized_of_tendsto_good`. -/
theorem seq_closed_minor_of_good {m k : ℕ} (P : Fin k → MvPolynomial (Fin (m + 1)) ℝ)
    (d : Fin k → ℕ) {x : ℕ → Fin m → ℝ} {x₀ : Fin m → ℝ} (hlim : Tendsto x atTop (nhds x₀))
    (hgoodn : ∀ n, Good (fun i => MvPolynomial.rename (Work.WilE4.rot m) (P i)) d (x n))
    (hgood₀ : Good (fun i => MvPolynomial.rename (Work.WilE4.rot m) (P i)) d x₀)
    {v' : Fin k → SignType}
    (hv : ∀ n, ∃ t : ℝ, ∀ i, SignType.sign ((spec (P i) (x n)).eval t) = v' i) :
    ∃ t : ℝ, ∀ i, SignType.sign ((spec (P i) x₀).eval t) = v' i :=
  realized_of_tendsto_good (P := fun i => MvPolynomial.rename (Work.WilE4.rot m) (P i))
    (d := d) hgood₀ hlim hgoodn (v := v') hv

theorem seq_closed_minor {m k : ℕ} (P : Fin k → MvPolynomial (Fin (m + 1)) ℝ) (D : ℕ)
    (hD : ∀ i : Fin k, (P i).degreeOf (Fin.last m) ≤ D)
    (hclosed : ∀ i : Fin k, ∃ j : Fin k, P j = MvPolynomial.pderiv (Fin.last m) (P i))
    (C : Set (Fin m → ℝ))
    (hcoeff : ∀ i : Fin k, ∀ j : ℕ, j ≤ D → ∀ x ∈ C, ∀ x' ∈ C,
      SignType.sign ((Work.WilE4.spec (P i) x).coeff j) = SignType.sign ((Work.WilE4.spec (P i) x').coeff j))
    (hmin : PscSignConst P C)
    (v' : Fin k → SignType)
    (x : ℕ → Fin m → ℝ) (hxC : ∀ n, x n ∈ C) {x₀ : Fin m → ℝ} (hx₀ : x₀ ∈ C)
    (hlim : Filter.Tendsto x Filter.atTop (nhds x₀))
    (hv : ∀ n, ∃ t : ℝ, ∀ i, SignType.sign ((Work.WilE4.spec (P i) (x n)).eval t) = v' i) :
    ∃ t : ℝ, ∀ i, SignType.sign ((Work.WilE4.spec (P i) x₀).eval t) = v' i := by
  classical
  choose t ht using hv
  by_cases hunb : ∀ M : ℝ, ∃ᶠ n in Filter.atTop, M < |t n|
  · -- unbounded witnesses
    exact realized_of_frequently_unbounded P (d := fun i => (spec (P i) x₀).natDegree)
      (fun i x hx => natDegree_spec_const_of_hcoeff hD hcoeff i x hx x₀ hx₀)
      (leadingCoeff_sign_const_of_hcoeff hD hcoeff)
      (fun i x hx x' hx' => spec_eq_zero_iff_on_C hD hcoeff hx hx') hxC hx₀ hlim ht hunb
  · -- bounded witnesses: pass to a convergent subsequence
    push_neg at hunb
    obtain ⟨M, hM⟩ := hunb
    have hfreq : ∃ᶠ n in Filter.atTop, t n ∈ Set.Icc (-M) M :=
      (hM.mono fun n hn => abs_le.mp hn).frequently
    obtain ⟨t₀, -, φ, hφmono, hφlim⟩ :=
      (isCompact_Icc : IsCompact (Set.Icc (-M) M)).tendsto_subseq' hfreq
    set x' : ℕ → Fin m → ℝ := fun n => x (φ n) with hx'def
    set t' : ℕ → ℝ := fun n => t (φ n) with ht'def
    have hxC' : ∀ n, x' n ∈ C := fun n => hxC (φ n)
    have hlim' : Filter.Tendsto x' Filter.atTop (nhds x₀) := hlim.comp hφmono.tendsto_atTop
    have ht'mem : ∀ n, ∀ i : Fin k,
        SignType.sign ((Work.WilE4.spec (P i) (x' n)).eval (t' n)) = v' i :=
      fun n i => ht (φ n) i
    have htlim' : Filter.Tendsto t' Filter.atTop (nhds t₀) := hφlim
    obtain ⟨ρ, hρ, hz, hzlim, hzdisk, hzroot, hzuniq, hmult, hε⟩ :=
      cluster_data P D hD hclosed C hcoeff hmin v' x' hxC' hx₀ hlim' t' ht'mem htlim'
    exact seq_closed_bounded P D hD C hcoeff v' x' hxC' hx₀ hlim' t' ht'mem htlim' hρ hz hzlim
      hzdisk hzroot hzuniq hmult hε

end Work.WilE4.CAD
