import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.CSq_le_ENormSq
import Submission.Work.Diff.STE.bessel_fourierCoeff
import Submission.Work.Diff.STE.ENormSq_seriesFun_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Galerkin projection does not increase the energy

For a smooth `1`-periodic matrix-valued function `u` on the flat torus, the Fourier series of the
box-truncated Fourier coefficients has no larger `H^k` energy than `u` itself:

  `ENormSqFull k (seriesFunM (projBox N (fourierCoeffM u))) ≤ ENormSqFull k u`.

Since `ENormSqFull k v = ENormSqM k v + ENormSqM 0 v` is the sum over the entries `(i,j)` of
`ENormSq k (v · i j) + ENormSq 0 (v · i j)`, everything is entrywise.  For a single entry
`f = fun x => u x i j` the projected series is `seriesFun c` with
`c m = if m ∈ box n N then fourierCoeff f m else 0`, and the claim reduces to the truncation
statement

  `ENormSq k (seriesFun c) ≤ ENormSq k f`  (`ENormSq_seriesFun_of_support_le`).

Its proof is Parseval plus Bessel, with no loss:

* for every multi-index `l : Fin k → ι` of derivative directions, term by term differentiation
  gives `∂^l (seriesFun c) = seriesFun (dmulV (List.ofFn l) c)`, hence, by Parseval for the
  `ℓ¹` family `dmulV (List.ofFn l) c` (which is finitely supported),
  `∫ ‖∂^l (seriesFun c)‖² = Σ_m ‖dmulV (List.ofFn l) c m‖² = Σ_{m ∈ box} ‖dmulV (List.ofFn l) c m‖²`;
* on the box the coefficient of `dmulV (List.ofFn l) c` is `∏_i (2π m_{l i}) · û(m)`, i.e. the
  Fourier coefficient of `∂^l f` (`fourierCoeff_pdVec_normSq`), so the finite sum is exactly
  `Σ_{m ∈ box} ‖\widehat{∂^l f}(m)‖²`, a subsum of the full `ℓ²` norm of the Fourier coefficients
  of `∂^l f`;
* Bessel's inequality for the continuous function `∂^l f` bounds that by `∫ ‖∂^l f‖²`.

Summing over `l` gives the claim.
-/

namespace Work.Diff.STE.flat

open MeasureTheory BigOperators
open scoped ComplexConjugate

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Finitely supported families are summable -/

/-- A family vanishing off a finite set is summable. -/
lemma summable_of_forall_notMem_eq_zero {ι' : Type*} {E : Type*} [NormedAddCommGroup E]
    [CompleteSpace E] (s : Finset ι') {c : ι' → E} (hc : ∀ m, m ∉ s → c m = 0) :
    Summable c := by
  refine Summable.of_norm_bounded_eventually (summable_zero (α := ℝ)) ?_
  rw [Filter.eventually_cofinite]
  refine s.finite_toSet.subset fun m hm => ?_
  by_contra hms
  exact hm (by rw [hc m hms, norm_zero])

/-! ## The multiplier of an iterated derivative, with an `Fin`-indexed product -/

/-- The product of the multiplier factors over the list `List.ofFn l` is the product over
`Fin k`. -/
lemma prod_map_ofFn {k : ℕ} (l : Fin k → ι) (g : ι → ℂ) :
    ((List.ofFn l).map g).prod = ∏ i : Fin k, g (l i) := by
  rw [List.map_ofFn, List.prod_ofFn]
  rfl

/-- The squared norm of a single derivative multiplier `2πi m_{l i}`. -/
lemma norm_sq_dmul_factor {k : ℕ} (l : Fin k → ι) (m : ι → ℤ) (i : Fin k) :
    ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I * (((m (l i) : ℤ)) : ℂ)‖ ^ 2
      = (2 * Real.pi * (((m (l i) : ℤ)) : ℝ)) ^ 2 := by
  have h : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (((m (l i) : ℤ)) : ℂ)
      = (((2 * Real.pi * (((m (l i) : ℤ)) : ℝ)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, ← Complex.normSq_eq_norm_sq, Complex.normSq_mul, Complex.normSq_I, mul_one,
    Complex.normSq_ofReal]
  ring

/-- The squared norm of the iterated multiplier `∏_i 2πi m_{l i}` is the product of the squared
real multipliers, i.e. exactly the weight appearing in `fourierCoeff_pdVec_normSq`. -/
lemma norm_sq_prod_dmul_ofFn {k : ℕ} (l : Fin k → ι) (m : ι → ℤ) :
    ‖∏ i : Fin k, (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (((m (l i) : ℤ)) : ℂ)‖ ^ 2
      = ∏ i : Fin k, (2 * Real.pi * (((m (l i) : ℤ)) : ℝ)) ^ 2 := by
  rw [norm_prod, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun i _ => norm_sq_dmul_factor l m i

/-- **The norm of the iterated derivative multiplier.**  For the coefficient family of the
iterated derivative `∂^l`, the squared modulus of the `m`-th coefficient is the product of the
squared real multipliers times the squared modulus of `c m`. -/
lemma norm_sq_dmulV_ofFn {k : ℕ} (l : Fin k → ι) (c : (ι → ℤ) → ℂ) (m : ι → ℤ) :
    ‖dmulV (List.ofFn l) c m‖ ^ 2
      = (∏ i : Fin k, (2 * Real.pi * (((m (l i) : ℤ)) : ℝ)) ^ 2) * ‖c m‖ ^ 2 := by
  have hprod : ((List.ofFn l).map
        (fun i : ι => (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((m i : ℤ) : ℂ))).prod
      = ∏ i : Fin k, (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (((m (l i) : ℤ)) : ℂ) :=
    prod_map_ofFn l _
  rw [dmulV, hprod, norm_mul, mul_pow, norm_sq_prod_dmul_ofFn]

/-! ## The truncation inequality for one entry -/

/-- **Truncating the Fourier coefficients to a finite set never increases the `H^k` energy.**
If `c` is supported in the finite set `s` and agrees there with the Fourier coefficients of a
`Cᵏ`, `1`-periodic function `f`, then `ENormSq k (seriesFun c) ≤ ENormSq k f`.

No constant is lost: the truncated series is a partial sum of the various `ℓ²` norms of the
Fourier coefficients of the derivatives `∂^l f`, and Bessel's inequality bounds each of those by
the corresponding `L²` norm. -/
theorem ENormSq_seriesFun_of_support_le {k : ℕ} (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ k f)
    (hper : Periodic1 f) (s : Finset (ι → ℤ)) (c : (ι → ℤ) → ℂ)
    (hc : ∀ m, m ∉ s → c m = 0) (hcf : ∀ m ∈ s, c m = fourierCoeff f m) :
    ENormSq k (seriesFun c) ≤ ENormSq k f := by
  -- the family `c` and all its weightings are finitely supported
  have hcsum : ∀ N : ℕ, Summable (fun m : ι → ℤ => (wt m) ^ N * ‖c m‖) := by
    intro N
    refine summable_of_forall_notMem_eq_zero s fun m hm => ?_
    rw [hc m hm, norm_zero, mul_zero]
  have hd : ∀ l : Fin k → ι, ∀ m, m ∉ s → dmulV (List.ofFn l) c m = 0 :=
    fun l m hm => by rw [dmulV, hc m hm, mul_zero]
  simp only [ENormSq]
  refine Finset.sum_le_sum fun l _ => ?_
  have hpd : pdVec k l (seriesFun c) = seriesFun (dmulV (List.ofFn l) c) :=
    funext fun x => pdList_seriesFun (List.ofFn l) c hcsum x
  have hsum_d : Summable (fun m : ι → ℤ => ‖dmulV (List.ofFn l) c m‖) :=
    summable_of_forall_notMem_eq_zero s fun m hm => by rw [hd l m hm, norm_zero]
  have hbessel := bessel_continuous (pdVec k l f) (continuous_pdVec k l f hf)
  rw [hpd, ens_integral_normSq_seriesFun (dmulV (List.ofFn l) c) hsum_d]
  rw [tsum_eq_sum (f := fun m : ι → ℤ => ‖dmulV (List.ofFn l) c m‖ ^ 2) (s := s)
    (fun m hm => by rw [hd l m hm]; norm_num)]
  calc ∑ m ∈ s, ‖dmulV (List.ofFn l) c m‖ ^ 2
      = ∑ m ∈ s, ‖fourierCoeff (pdVec k l f) m‖ ^ 2 := by
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [norm_sq_dmulV_ofFn l c m, hcf m hm, ← fourierCoeff_pdVec_normSq k l f hf hper m]
    _ ≤ ∑' m : ι → ℤ, ‖fourierCoeff (pdVec k l f) m‖ ^ 2 :=
        hbessel.1.sum_le_tsum s fun m _ => sq_nonneg _
    _ ≤ ∫ x in unitCube, ‖pdVec k l f x‖ ^ 2 := hbessel.2

/-! ## Bookkeeping for the matrix-valued torus -/

/-- The entries of a smooth matrix-valued function are smooth.  (`private`: a sibling module
declares the same name.) -/
private lemma contDiff_entry {n : ℕ} (u : Flat.Torus n) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (i j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => u x i j) :=
  contDiff_pi.mp (contDiff_pi.mp hu i) j

/-- The entries of a `1`-periodic matrix-valued function are `1`-periodic.  (`private`: a sibling
module declares the same name.) -/
private lemma periodic1_entry {n : ℕ} (u : Flat.Torus n) (hper : Periodic1 u) (i j : Fin n) :
    Periodic1 (fun x : Fin n → ℝ => u x i j) :=
  fun e x => congrFun (congrFun (hper e x) i) j

/-- The `(i,j)`-entry of the truncated Fourier series of `u` is the Fourier series of the
truncated Fourier coefficients of the entry `fun x => u x i j`. -/
lemma seriesFunM_projBox_apply {n : ℕ} (u : Flat.Torus n) (N : ℕ) (i j : Fin n) :
    (fun x : Fin n → ℝ => Flat.seriesFunM (Flat.projBox N (Flat.fourierCoeffM u)) x i j)
      = seriesFun (fun m : Fin n → ℤ =>
          if m ∈ Flat.box n N then fourierCoeff (fun x : Fin n → ℝ => u x i j) m else 0) := by
  funext x
  rw [Flat.seriesFunM_apply]
  congr 1
  funext m
  by_cases h : m ∈ Flat.box n N <;> simp [Flat.projBox, h]

/-- Comparison of the matrix energies through the entries. -/
lemma ENormSqM_le_of_entry {n : ℕ} (k : ℕ) {v w : Flat.Torus n}
    (h : ∀ i j : Fin n, ENormSq k (fun x : Fin n → ℝ => v x i j)
      ≤ ENormSq k (fun x : Fin n → ℝ => w x i j)) :
    Flat.ENormSqM k v ≤ Flat.ENormSqM k w := by
  simp only [Flat.ENormSqM]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j

/-! ## The target -/

theorem ENormSq_projBox_fourierCoeff_le {n : ℕ} (u : Work.Diff.STE.Flat.Torus n)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hper : Work.Diff.STE.Periodic1 u) (k N : ℕ) :
    Work.Diff.STE.Flat.ENormSqFull k
        (Work.Diff.STE.Flat.seriesFunM (Work.Diff.STE.Flat.projBox N
          (Work.Diff.STE.Flat.fourierCoeffM u)))
      ≤ Work.Diff.STE.Flat.ENormSqFull k u := by
  have hmain : ∀ (j : ℕ) (i t : Fin n),
      ENormSq j (fun x : Fin n → ℝ =>
          Flat.seriesFunM (Flat.projBox N (Flat.fourierCoeffM u)) x i t)
        ≤ ENormSq j (fun x : Fin n → ℝ => u x i t) := by
    intro j i t
    rw [seriesFunM_projBox_apply u N i t]
    exact ENormSq_seriesFun_of_support_le (fun x : Fin n → ℝ => u x i t)
      ((contDiff_entry u hu i t).of_le (by exact_mod_cast le_top))
      (periodic1_entry u hper i t) (Flat.box n N) _
      (fun m hm => by simp [hm])
      (fun m hm => by simp [hm])
  simp only [Flat.ENormSqFull]
  exact add_le_add (ENormSqM_le_of_entry k fun i j => hmain k i j)
    (ENormSqM_le_of_entry 0 fun i j => hmain 0 i j)

end

end Work.Diff.STE.flat
