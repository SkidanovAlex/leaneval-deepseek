import Mathlib
import Submission.Vdw.CaseIIClasses
-- import Submission.Commons.NumberTheory.NumberField.ncard_norm_le
import Submission.Commons.NumberTheory.NumberField.abs_discr_le_two_house_pow
import Submission.Commons.NumberTheory.NumberField.discr_rpow_div_two_le_house
import Submission.Commons.NumberTheory.NumberField.abs_norm_eq_abs_coeff_zero_minpoly
import Submission.Commons.NumberTheory.NumberField.ncard_mahler_le
import Submission.Commons.NumberTheory.NumberField.prod_max_one_normAtPlace_le
import Submission.Commons.NumberTheory.Polynomial.mapMahlerMeasure_int_le
import Submission.Commons.NumberTheory.NumberField.ncard_polys_mahler_le
import Submission.Vdw.FinalEndpoints
import Submission.Vdw.PrimeDegreePrimitive

open Polynomial Filter Asymptotics
open scoped BigOperators
open Function
open scoped NumberField
open vanDerWaerdenConjecture

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The Lemke Oliver–Thorne per-field fibre bound, proved

`CaseIIClasses.PerFieldFibreBound n` is the input of Bhargava's Case-II analysis
that a *fixed* degree-`n` field `K` is cut out by at most
`≪ H (log H)^{n-1} |Disc K|^{-1/(n(n-1))}` monic degree-`n` polynomials of height
`≤ H`.  The cited source is Lemke Oliver–Thorne, *Upper bounds on polynomials
with small Galois group*, Mathematika 66 (2020); the aim of this file is to
discharge that input from the elementary counting bound
`Commons.NumberTheory.NumberField.ncard_norm_le` together with the
Ellenberg–Venkatesh height bound.

The essential inputs are

* `ncard_norm_le` — the number of `α ∈ 𝓞 K` with `α ∉ ℤ` and
  `|Norm α| ≤ B` is `≪ B (1 + log B)^{n-1} / λ`, where `λ` is (a lower bound
  for) the smallest house of a non-rational integral element of `K`;
* `abs_discr_le_two_house_pow` — for a generator `α` of `K`,
  `|Disc K| ≤ (2 · house α)^{n(n-1)}`, i.e. `λ ≫ |Disc K|^{1/(n(n-1))}`
  provided every non-rational element of `K` generates `K`.

The latter hypothesis always holds in prime degree, so the per-field fibre
bound is unconditional there.
-/

namespace Submission.Vdw

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-! ## Prime degree: every non-rational element generates -/

/-- In prime degree every element outside the prime field generates the field. -/
theorem adjoin_eq_top_of_prime_finrank (hp : Nat.Prime (Module.finrank ℚ K)) {α : K}
    (hα : α ∉ Set.range (algebraMap ℚ K)) :
    Algebra.adjoin ℚ ({α} : Set K) = ⊤ := by
  rw [← IntermediateField.adjoin_eq_top_iff]
  set F : IntermediateField ℚ K := IntermediateField.adjoin ℚ ({α} : Set K)
  have hmem : α ∈ F := IntermediateField.mem_adjoin_simple_self ℚ α
  have hne : F ≠ ⊥ := by
    intro h
    apply hα
    have h1 : α ∈ (⊥ : IntermediateField ℚ K) := by rw [← h]; exact hmem
    rw [IntermediateField.mem_bot] at h1
    exact h1
  have h2 : 2 ≤ Module.finrank ℚ ↥F := by
    by_contra h
    have h1 : Module.finrank ℚ ↥F = 1 := by
      have := Module.finrank_pos (R := ℚ) (M := ↥F)
      omega
    exact hne (IntermediateField.finrank_eq_one_iff.mp h1)
  have htower : Module.finrank ℚ ↥F * Module.finrank (↥F) K = Module.finrank ℚ K :=
    Module.finrank_mul_finrank ℚ ↥F K
  have hdvd : Module.finrank ℚ ↥F ∣ Module.finrank ℚ K := ⟨Module.finrank (↥F) K, htower.symm⟩
  have hfeq : Module.finrank ℚ ↥F = Module.finrank ℚ K := by
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · omega
    · exact h1
  have hFK : Module.finrank (↥F) K = 1 := by
    have h3 : Module.finrank ℚ ↥F * Module.finrank (↥F) K = Module.finrank ℚ ↥F := by
      rw [htower, hfeq]
    exact Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := ℚ) (M := ↥F)) (by rw [h3, mul_one])
  have htop : F.toSubmodule = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    exact hfeq
  ext x
  constructor
  · intro _; trivial
  · intro _
    have hx : x ∈ F.toSubmodule := by rw [htop]; exact Submodule.mem_top
    exact hx


/-! ## The Ellenberg–Venkatesh height bound

For a generator `α` of `K` we have `|Disc K| ≤ (2 · house α)^{n(n-1)}`; in prime
degree every element outside `ℤ` is a generator, so the quantity
`|Disc K|^{1/(n(n-1))}/2` is a lower bound for the house of every non-rational
integral element.  This is the `λ` of the counting bound `ncard_norm_le`. -/

/-- An integral element of a number field that is rational lies in `ℤ`. -/
theorem isIntegral_rat_coe_mem_intRange {q : ℚ} (h : IsIntegral ℤ (algebraMap ℚ K q)) :
    q ∈ Set.range (algebraMap ℤ ℚ) := by
  have hinj : Function.Injective (algebraMap ℚ K) := (algebraMap ℚ K).injective
  exact IsIntegralClosure.isIntegral_iff.mp ((isIntegral_algebraMap_iff hinj).mp h)

/-- **Ellenberg–Venkatesh, prime degree.**  In prime degree every non-rational
integral element has house at least `|Disc K|^{1/(n(n-1))}/2`. -/
theorem discr_rpow_div_two_le_house_of_prime (hp : Nat.Prime (Module.finrank ℚ K))
    {α : 𝓞 K} (hα : ((α : K)) ∉ Set.range (algebraMap ℤ K)) :
    |((NumberField.discr K : ℤ) : ℝ)| ^
        (1 / ((Module.finrank ℚ K : ℝ) * ((Module.finrank ℚ K : ℝ) - 1))) / 2
      ≤ NumberField.house ((α : K)) := by
  set n := Module.finrank ℚ K with hn
  have hn2 : 2 ≤ n := hp.two_le
  have hn0 : 0 < n := by omega
  have hint : IsIntegral ℤ ((α : K)) := NumberField.RingOfIntegers.isIntegral_coe α
  -- `(α : K)` is not rational
  have hrat : ((α : K)) ∉ Set.range (algebraMap ℚ K) := by
    rintro ⟨q, hq⟩
    apply hα
    have hqi : q ∈ Set.range (algebraMap ℤ ℚ) :=
      @isIntegral_rat_coe_mem_intRange K _ _ q (hq ▸ hint)
    obtain ⟨m, hm⟩ := hqi
    refine ⟨m, ?_⟩
    rw [← hq, ← hm]
    exact IsScalarTower.algebraMap_apply ℤ ℚ K m
  have hgen : Algebra.adjoin ℚ ({((α : K))} : Set K) = ⊤ :=
    adjoin_eq_top_of_prime_finrank hp hrat
  have hdisc := Commons.NumberTheory.NumberField.abs_discr_le_two_house_pow
    (K := K) (n := n) hn.symm hgen hint
  -- take the `1/(n(n-1))`-th power
  have hkpos : 0 < n * (n - 1) := by
    have : 1 ≤ n - 1 := by omega
    positivity
  have hcast : ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    have h1 : 1 ≤ n := by omega
    push_cast [Nat.cast_sub h1]
    ring
  have hexp : (0 : ℝ) ≤ 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
    have h1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    positivity
  have h2h : (0 : ℝ) ≤ 2 * NumberField.house ((α : K)) := by
    have := NumberField.house_nonneg ((α : K)); linarith
  have hstep := Real.rpow_le_rpow (abs_nonneg _) hdisc hexp
  have hrw : ((2 * NumberField.house ((α : K))) ^ (n * (n - 1))) ^
        (1 / ((n : ℝ) * ((n : ℝ) - 1))) = 2 * NumberField.house ((α : K)) := by
    rw [← Real.rpow_natCast (2 * NumberField.house ((α : K))) (n * (n - 1)), hcast,
      ← Real.rpow_mul h2h]
    have hne2 : (n : ℝ) - 1 ≠ 0 := by
      have h1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
      linarith
    have hne1 : (n : ℝ) ≠ 0 := by positivity
    have : (n : ℝ) * ((n : ℝ) - 1) * (1 / ((n : ℝ) * ((n : ℝ) - 1))) = 1 := by
      field_simp
    rw [this, Real.rpow_one]
  rw [hrw] at hstep
  linarith [hstep]


/-! ## The discriminant is at least `2` in degree `≥ 2` -/

/-- A number field of degree `≥ 2` has `|Disc| ≥ 2` (Minkowski). -/
theorem two_le_abs_discr (hn : 2 ≤ Module.finrank ℚ K) :
    2 ≤ |((NumberField.discr K : ℤ) : ℝ)| := by
  have h1 : 1 < Module.finrank ℚ K := by omega
  have h := NumberField.abs_discr_ge (K := K) h1
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hbase : (1 : ℝ) < 3 * Real.pi / 4 := by linarith
  have hmono : (3 * Real.pi / 4) ^ 2 ≤ (3 * Real.pi / 4) ^ Module.finrank ℚ K :=
    pow_le_pow_right₀ hbase.le hn
  have hsq : (2 : ℝ) ≤ (4 / 9 : ℝ) * (3 * Real.pi / 4) ^ 2 := by
    nlinarith [sq_nonneg (Real.pi - 3), hpi]
  have hstep : (4 / 9 : ℝ) * (3 * Real.pi / 4) ^ 2
      ≤ (4 / 9 : ℝ) * (3 * Real.pi / 4) ^ Module.finrank ℚ K :=
    mul_le_mul_of_nonneg_left hmono (by norm_num)
  have h' : (4 / 9 : ℝ) * (3 * Real.pi / 4) ^ Module.finrank ℚ K
      ≤ |((NumberField.discr K : ℤ) : ℝ)| := by
    simpa only [Int.cast_abs] using h
  exact hsq.trans (hstep.trans h')

/-! ## Auxiliary identifications -/

/-- The field of a monic degree-`n` polynomial has degree `n`. -/
theorem finrank_Kpoly {n : ℕ} {f : ℤ[X]} (hm : f.Monic) (hd : f.natDegree = n)
    [Fact (Irreducible (f.map φℚ))] : Module.finrank ℚ (Kpoly f) = n := by
  have hf0 : f.map φℚ ≠ 0 := (hm.map φℚ).ne_zero
  have hnd : (f.map φℚ).natDegree = f.natDegree := by
    refine Polynomial.natDegree_map_of_leadingCoeff_ne_zero φℚ ?_
    rw [hm.leadingCoeff]
    exact one_ne_zero
  rw [PowerBasis.finrank (AdjoinRoot.powerBasis hf0), AdjoinRoot.powerBasis_dim hf0, hnd, hd]

/-- The field discriminant of a region member as a real number, in terms of the
field discriminant of the corresponding number field. -/
theorem fieldDiscExp_coe {f : ℤ[X]} [Fact (Irreducible (f.map φℚ))] :
    ((fieldDiscExp f Fact.out : ℕ) : ℝ) = |((NumberField.discr (Kpoly f) : ℤ) : ℝ)| := by
  show ((fieldDisc (f := f) : ℕ) : ℝ) = _
  rw [fieldDisc, Nat.cast_natAbs, Int.cast_abs]

/-! ## The Mahler measure of a box member is `≤ (n+1) H` -/

/-- The coefficients of a member of the box are bounded by `H` (the leading
coefficient is `1 ≤ H`). -/
theorem coeff_abs_le_of_mem_Box {n H : ℕ} (hH : 1 ≤ H) {f : ℤ[X]} (hf : f ∈ Box n H) :
    ∀ i, |((f.coeff i : ℤ) : ℝ)| ≤ (H : ℝ) := by
  intro i
  rcases lt_trichotomy i n with hi | hi | hi
  · have h1 := hf.2.2 i hi
    have h2 : |(f.coeff i : ℤ)| ≤ (H : ℤ) := by exact_mod_cast h1
    rw [← Int.cast_abs]
    exact_mod_cast h2
  · rw [hi]
    have hlead : f.coeff n = 1 := by
      rw [← Polynomial.natDegree_eq_of_degree_eq_some hf.2.1, Polynomial.coeff_natDegree]
      exact hf.1.leadingCoeff
    rw [hlead]
    simp only [Int.cast_one, abs_one]
    exact_mod_cast hH
  · have h0 : f.coeff i = 0 := Polynomial.coeff_eq_zero_of_degree_lt (by
      rw [hf.2.1]; exact WithBot.coe_lt_coe.mpr hi)
    rw [h0]
    simp only [Int.cast_zero, abs_zero]
    exact_mod_cast (Nat.zero_le H)

/-- The Mahler measure of a member of the box is at most `(n+1)·H`. -/
theorem mapMahlerMeasure_le_of_mem_Box {n H : ℕ} (hH : 1 ≤ H) {f : ℤ[X]} (hf : f ∈ Box n H) :
    Polynomial.mapMahlerMeasure f (Int.castRingHom ℂ) ≤ ((n : ℝ) + 1) * H := by
  have h : Polynomial.mapMahlerMeasure f (Int.castRingHom ℂ) ≤ ((f.natDegree : ℝ) + 1) * H :=
    Commons.NumberTheory.Polynomial.mapMahlerMeasure_int_le f (H : ℝ)
      (by positivity) (coeff_abs_le_of_mem_Box hH hf)
  have hdeg : f.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some hf.2.1
  rwa [hdeg] at h

/-! ## The final real-arithmetic comparison -/

theorem perFieldFibre_arith {n H N : ℕ} (hn : 1 ≤ n) (hN : N = n) (hH : 2 ≤ H) {Y D Lam cn : ℝ}
    (hY : Y = ((n : ℝ) + 1) * H) (hLam : D ^ (1 / ((n : ℝ) * ((n : ℝ) - 1))) / 2 ≤ Lam)
    (hD : 0 < D) (hcn : cn = 1 + (1 + Real.log ((n : ℝ) + 1)) / Real.log 2) :
    (100000 : ℝ) ^ N * Y * (1 + Real.log Y) ^ (N - 1) / Lam ≤
      ((100000 : ℝ) ^ n * ((n : ℝ) + 1) * cn ^ (n - 1) * 2) * (H : ℝ) *
        (Real.log (H : ℝ)) ^ (n - 1) * D ^ (-(1 / ((n : ℝ) * ((n : ℝ) - 1)))) := by
  have hHR : (2 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hlogH : 0 < Real.log (H : ℝ) := Real.log_pos (by linarith)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogHge : Real.log 2 ≤ Real.log (H : ℝ) := Real.log_le_log (by norm_num) hHR
  have hlognpos : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hhunnonneg : 0 ≤ 1 + Real.log ((n : ℝ) + 1) := by linarith
  have hlogYnonneg : 0 ≤ Real.log Y := by
    apply Real.log_nonneg
    rw [hY]
    have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ ((n : ℝ) + 1) * H := mul_le_mul h1 (by linarith) (by norm_num) (by positivity)
  have hkey : 1 + Real.log Y ≤ cn * Real.log (H : ℝ) := by
    have hsplit : Real.log Y = Real.log ((n : ℝ) + 1) + Real.log (H : ℝ) := by
      rw [hY, Real.log_mul (by positivity) (by positivity)]
    rw [hsplit, hcn]
    have h1 : (1 + Real.log ((n : ℝ) + 1)) ≤
        (1 + Real.log ((n : ℝ) + 1)) / Real.log 2 * Real.log (H : ℝ) := by
      calc (1 + Real.log ((n : ℝ) + 1))
          = (1 + Real.log ((n : ℝ) + 1)) / Real.log 2 * Real.log 2 := by
            rw [div_mul_cancel₀ _ hlog2pos.ne']
        _ ≤ (1 + Real.log ((n : ℝ) + 1)) / Real.log 2 * Real.log (H : ℝ) :=
            mul_le_mul_of_nonneg_left hlogHge (by positivity)
    linarith
  have hpow : (1 + Real.log Y) ^ (N - 1) ≤ cn ^ (n - 1) * (Real.log (H : ℝ)) ^ (n - 1) := by
    have hN1 : N - 1 = n - 1 := by omega
    rw [hN1, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hkey _
  have hDp : 0 < D ^ (1 / ((n : ℝ) * ((n : ℝ) - 1))) := Real.rpow_pos_of_pos hD _
  have hLampos : 0 < Lam := lt_of_lt_of_le (by linarith) hLam
  have hDnat : D ^ (-(1 / ((n : ℝ) * ((n : ℝ) - 1))))
      = (D ^ (1 / ((n : ℝ) * ((n : ℝ) - 1))))⁻¹ := by
    rw [Real.rpow_neg hD.le]
  have h100 : (100000 : ℝ) ^ N = (100000 : ℝ) ^ n := by rw [hN]
  have hnum : (100000 : ℝ) ^ N * Y * (1 + Real.log Y) ^ (N - 1)
      ≤ (100000 : ℝ) ^ n * (((n : ℝ) + 1) * H) *
          (cn ^ (n - 1) * (Real.log (H : ℝ)) ^ (n - 1)) := by
    rw [hY] at hpow
    rw [h100, hY]
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hcnpos : 0 < cn := by
    rw [hcn]
    have h1 : (0 : ℝ) < 1 + Real.log ((n : ℝ) + 1) := by linarith
    have h2 : (0 : ℝ) < (1 + Real.log ((n : ℝ) + 1)) / Real.log 2 := div_pos h1 hlog2pos
    linarith
  have hnumpos : 0 ≤ (100000 : ℝ) ^ n * (((n : ℝ) + 1) * H) *
      (cn ^ (n - 1) * (Real.log (H : ℝ)) ^ (n - 1)) := by positivity
  have hDp2 : 0 < D ^ (1 / ((n : ℝ) * ((n : ℝ) - 1))) / 2 := by linarith
  refine (div_le_div₀ hnumpos hnum hDp2 hLam).trans (le_of_eq ?_)
  rw [hDnat]
  field_simp

/-! ## The per-field fibre bound for a region whose members generate -/

/-- **The Lemke Oliver–Thorne per-field fibre bound**, from the hypothesis
that every non-rational element of the field of a region member generates
that field.  In prime degree this hypothesis is automatic
(`adjoin_eq_top_of_prime_finrank`); in general it follows from the primitivity
of the Galois group (`PerFieldFibreAll.adjoin_eq_top_of_galPrimitive`). -/
theorem perFieldFibreBound_of_region_gen (n : ℕ) (hn : 3 ≤ n)
    (hgen : ∀ (H : ℕ) (f : ↥(SubcaseI_P2 n H)),
      ∀ α : Kpoly (f : ℤ[X]), α ∉ Set.range (algebraMap ℚ (Kpoly (f : ℤ[X]))) →
        Algebra.adjoin ℚ ({α} : Set (Kpoly (f : ℤ[X]))) = ⊤) :
    PerFieldFibreBound n (by omega : 1 ≤ n) := by
  classical
  have hn1 : 1 ≤ n := by omega
  set cn : ℝ := 1 + (1 + Real.log ((n : ℝ) + 1)) / Real.log 2 with hcndef
  have hcn1 : 1 ≤ cn := by
    rw [hcndef]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hnum : 0 < 1 + Real.log ((n : ℝ) + 1) := by
      have : 0 < Real.log ((n : ℝ) + 1) :=
        Real.log_pos (by
          have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
          linarith)
      linarith
    have := div_pos hnum hlog2
    linarith
  refine ⟨(100000 : ℝ) ^ n * ((n : ℝ) + 1) * cn ^ (n - 1) * 2, by positivity, ?_⟩
  intro H q
  set f₀ : ↥(SubcaseI_P2 n H) := Quotient.out q with hf₀
  haveI hFact : Fact (Irreducible (((f₀ : ℤ[X])).map φℚ)) :=
    ⟨subcaseI_P2_irreducible n H hn1 f₀⟩
  have hbox₀ : (f₀ : ℤ[X]) ∈ Box n H := subcaseI_P2_subset_Box n H f₀.2
  have hdeg₀ : ((f₀ : ℤ[X])).natDegree = n :=
    Polynomial.natDegree_eq_of_degree_eq_some hbox₀.2.1
  have hfin₀ : Module.finrank ℚ (Kpoly (f₀ : ℤ[X])) = n := finrank_Kpoly hbox₀.1 hdeg₀
  by_cases hH : H ≤ 1
  · -- no class survives: the discriminant is at least `2`
    exfalso
    obtain ⟨-, h, hb⟩ := f₀.2
    haveI : Fact (Irreducible (((f₀ : ℤ[X])).map φℚ)) := ⟨h⟩
    have h2 : (2 : ℝ) ≤ ((fieldDiscExp (f₀ : ℤ[X]) h : ℕ) : ℝ) := by
      have hdisc := two_le_abs_discr (K := Kpoly (f₀ : ℤ[X])) (by rw [hfin₀]; omega)
      rw [fieldDiscExp_coe (f := (f₀ : ℤ[X]))]
      exact hdisc
    have hHpow : (H : ℝ) ^ (2 + 1 / (n : ℝ)) ≤ 1 := by
      refine Real.rpow_le_one (by positivity) ?_ (by positivity)
      exact_mod_cast hH
    linarith
  · push_neg at hH
    have hH1 : 1 ≤ H := by omega
    have hH2 : (2 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
    -- notations
    set Y : ℝ := ((n : ℝ) + 1) * H with hYdef
    have hY1 : 1 ≤ Y := by
      have h2 : (1 : ℝ) ≤ ((n : ℝ) + 1) := by
        have := Nat.cast_nonneg (α := ℝ) n
        linarith
      have h3 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ ((n : ℝ) + 1) * H := mul_le_mul h2 h3 (by norm_num) (by positivity)
    set D : ℝ := |((NumberField.discr (Kpoly (f₀ : ℤ[X])) : ℤ) : ℝ)| with hDdef
    have hDpos : 0 < D := by
      rw [hDdef]
      have hne : NumberField.discr (Kpoly (f₀ : ℤ[X])) ≠ 0 :=
        NumberField.discr_ne_zero _
      have h1 : (0 : ℤ) < |NumberField.discr (Kpoly (f₀ : ℤ[X]))| := abs_pos.mpr hne
      exact_mod_cast h1
    set Lam : ℝ := max 1 (D ^ (1 / ((n : ℝ) * ((n : ℝ) - 1))) / 2) with hLamdef
    have hLam1 : 1 ≤ Lam := le_max_left _ _
    have hLamge : D ^ (1 / ((n : ℝ) * ((n : ℝ) - 1))) / 2 ≤ Lam := le_max_right _ _
    set S : Set ℤ[X] :=
      Subtype.val '' {f : ↥(SubcaseI_P2 n H) |
        Quotient.mk (fieldIsoSetoid n H hn1) f = q} with hSdef
    have hcard : (Nat.card {f : ↥(SubcaseI_P2 n H) //
        Quotient.mk (fieldIsoSetoid n H hn1) f = q} : ℝ) = (S.ncard : ℝ) := by
      show (Nat.card ↥({f : ↥(SubcaseI_P2 n H) |
        Quotient.mk (fieldIsoSetoid n H hn1) f = q}) : ℝ) = (S.ncard : ℝ)
      rw [hSdef, Set.ncard_image_of_injective _ Subtype.val_injective, Nat.card_coe_set_eq]
    have hcount : (S.ncard : ℝ) ≤
        (100000 : ℝ) ^ (Module.finrank ℚ (Kpoly (f₀ : ℤ[X]))) * Y *
          (1 + Real.log Y) ^ (Module.finrank ℚ (Kpoly (f₀ : ℤ[X])) - 1) / Lam := by
      have h := Commons.NumberTheory.NumberField.ncard_polys_mahler_le
        (K := Kpoly (f₀ : ℤ[X])) (hn := by rw [hfin₀]; omega) (Y := Y) (lam := Lam)
        (hY := hY1) (hlam := hLam1) ?_ S ?_
      · exact h
      · -- the separation hypothesis
        intro α hα
        refine max_le ?_ ?_
        · -- `1 ≤ house α`
          exact NumberField.one_le_house_of_isIntegral
            (NumberField.RingOfIntegers.isIntegral_coe α) (by
              intro h0; exact hα (by rw [h0]; exact ⟨0, by simp⟩))
        · -- the Ellenberg–Venkatesh bound
          have h := Commons.NumberTheory.NumberField.discr_rpow_div_two_le_house
            (K := Kpoly (f₀ : ℤ[X])) (N := n) hfin₀ (by omega)
            (fun β hβ => hgen H f₀ β hβ) hα
          rw [← hDdef] at h
          exact h
      · -- the hypotheses on the class
        intro f hf
        rw [hSdef] at hf
        obtain ⟨g, hg, rfl⟩ := hf
        haveI : Fact (Irreducible (((g : ℤ[X])).map φℚ)) :=
          ⟨subcaseI_P2_irreducible n H hn1 g⟩
        have hbox : (g : ℤ[X]) ∈ Box n H := subcaseI_P2_subset_Box n H g.2
        refine ⟨hbox.1, ?_, ?_, ?_, ?_⟩
        · show (g : ℤ[X]).natDegree = Module.finrank ℚ (Kpoly (f₀ : ℤ[X]))
          have hnd : (g : ℤ[X]).natDegree = n :=
            Polynomial.natDegree_eq_of_degree_eq_some hbox.2.1
          rw [hnd, hfin₀]
        · exact subcaseI_P2_irreducible n H hn1 g
        · -- the two fields are isomorphic
          have h1 : Quotient.mk (fieldIsoSetoid n H hn1) g =
              Quotient.mk (fieldIsoSetoid n H hn1) f₀ := by
            rw [hf₀, hg]
            exact (Quotient.out_eq q).symm
          exact Quotient.exact h1
        · -- the Mahler measure
          exact mapMahlerMeasure_le_of_mem_Box hH1 hbox
    -- the discriminant of the class
    have hclassDisc : (classDisc n H hn1 q : ℝ) = D := by
      rw [hDdef, classDisc_out n H hn1 q]
      show (subcaseI_P2_disc n H f₀ : ℝ) = _
      rw [subcaseI_P2_disc]
      exact fieldDiscExp_coe (f := (f₀ : ℤ[X]))
    have hH2 : 2 ≤ H := by omega
    have hmain := perFieldFibre_arith (n := n) (H := H)
      (N := Module.finrank ℚ (Kpoly (f₀ : ℤ[X]))) hn1 hfin₀ hH2 hYdef hLamge hDpos hcndef
    rw [← hclassDisc] at hmain
    exact (le_of_eq hcard).trans (hcount.trans hmain)


/-- **The Lemke Oliver–Thorne per-field fibre bound is a theorem in prime
degree** (where every non-rational element generates, so
`perFieldFibreBound_of_region_gen` applies). -/
theorem perFieldFibreBound_prime (n : ℕ) (hn : 3 ≤ n) (hp : Nat.Prime n) :
    PerFieldFibreBound n (by omega : 1 ≤ n) :=
  perFieldFibreBound_of_region_gen n hn fun H f α hα => by
    haveI : Fact (Irreducible (((f : ℤ[X])).map φℚ)) :=
      ⟨subcaseI_P2_irreducible n H (by omega) f⟩
    have hbox : (f : ℤ[X]) ∈ Box n H := subcaseI_P2_subset_Box n H f.2
    have hfin : Module.finrank ℚ (Kpoly (f : ℤ[X])) = n :=
      finrank_Kpoly hbox.1 (Polynomial.natDegree_eq_of_degree_eq_some hbox.2.1)
    refine adjoin_eq_top_of_prime_finrank ?_ hα
    rw [hfin]; exact hp

/-! ## Endpoints: the per-field input discharged in prime degree -/

/-- **The challenge theorem in prime degree from the field count alone**: with
the Lemke Oliver–Thorne per-field fibre bound now proved, the only remaining
input is the number of degree-`n` fields of bounded discriminant. -/
theorem theorem_1_of_fieldCountBound_of_prime (n : ℕ) (hn : 3 ≤ n) (hp : Nat.Prime n)
    (β : ℝ) (hβ : 1 / ((n : ℝ) * ((n : ℝ) - 1)) < β)
    (hexp : 1 + (2 + 4 / (weylM n : ℝ)) * (β - 1 / ((n : ℝ) * ((n : ℝ) - 1)))
      < (n : ℝ) - 1)
    (hSC : FieldCountBound n (by omega : 1 ≤ n) β)
    (h4 : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_field_inputs n hn β hβ hexp (perFieldFibreBound_prime n hn hp) hSC h4

/-- **Degree 3**: the challenge theorem from the count of cyclic cubic fields
(`β = 1/2`) alone — the per-field fibre bound is now a theorem, and `3` is prime
so the imprimitive input is vacuous. -/
theorem theorem_1_of_cubic_fieldCount (hSC : FieldCountBound 3 (by omega : 1 ≤ 3) (1 / 2)) :
    (fun H : ℕ => (E 3 H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (3 - 1) : ℝ)) :=
  theorem_1_of_fieldCountBound_of_prime 3 (by omega) (by norm_num) (1 / 2) (by norm_num)
    weylM_exponent_three hSC (ImprimitiveBad_isBigO_of_prime 3 (by norm_num))

/-- **Degree 5**: the challenge theorem from the exact quintic field count
(`β = 1`) alone. -/
theorem theorem_1_of_quintic_fieldCount (hSC : FieldCountBound 5 (by omega : 1 ≤ 5) 1) :
    (fun H : ℕ => (E 5 H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (5 - 1) : ℝ)) :=
  theorem_1_of_fieldCountBound_of_prime 5 (by omega) (by norm_num) 1 (by norm_num)
    weylM_exponent_five hSC (ImprimitiveBad_isBigO_of_prime 5 (by norm_num))

/-- **Prime degrees `n ≥ 7`**: the challenge theorem from Schmidt's field count
(`β = (n+2)/4`) alone. -/
theorem theorem_1_of_schmidt_of_prime (n : ℕ) (hn : 7 ≤ n) (hp : Nat.Prime n)
    (hSC : FieldCountBound n (by omega : 1 ≤ n) (((n : ℝ) + 2) / 4)) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  have hβ : 1 / ((n : ℝ) * ((n : ℝ) - 1)) < ((n : ℝ) + 2) / 4 := by
    have hnR : (7 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
    rw [div_lt_iff₀ hden]
    nlinarith
  exact theorem_1_of_fieldCountBound_of_prime n (by omega) hp (((n : ℝ) + 2) / 4) hβ
    (weylM_exponent_schmidt n (by omega)) hSC (ImprimitiveBad_isBigO_of_prime n hp)

end

end Submission.Vdw
