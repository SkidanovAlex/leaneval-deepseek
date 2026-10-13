import Mathlib
import Submission.Work.DSM5b.CycleDefs
import Submission.Work.DSM5b.component_isIntegral_pairwise
import Submission.Work.DSM5b.varpi_smul_eq_algebraMap_of_integral
import Submission.Work.DSM5b.chartRing_gen_mul_eq

namespace Work.DSM5b

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

universe a

set_option maxHeartbeats 1600000

/-- A perfect ring of prime characteristic is reduced (its Frobenius is bijective, hence
injective, and a nilpotent has a vanishing `p ^ m`-th power for large `m`). -/
private theorem isReduced_of_perfectRing_glue (p : ℕ) [Fact p.Prime] (R : Type a) [CommRing R]
    [CharP R p] [PerfectRing R p] : IsReduced R := by
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

/-- **The monic relation in `Fin`-indexed form.**  An element `h` integral over `R` satisfies a
monic relation whose non-leading coefficients are read as an `R`-valued function on `Fin s`, with
`s` the degree: `h ^ s = ∑_{i < s} (algebraMap c i) * h ^ i`.  (For the degenerate case `s = 0`
— `h = 1 = 0` — both sides collapse and the relation still holds.) -/
private lemma exists_fin_monic_relation_of_isIntegral_glue {R A : Type a} [CommRing R]
    [CommRing A] [Algebra R A] {h : A} (hh : IsIntegral R h) :
    ∃ (s : ℕ) (c : Fin s → R), h ^ s = ∑ i : Fin s, algebraMap R A (c i) * h ^ (i : ℕ) := by
  obtain ⟨p, hpmonic, hpeval⟩ := hh
  refine ⟨p.natDegree, fun i => -p.coeff (i : ℕ), ?_⟩
  have key : ∑ i ∈ Finset.range (p.natDegree + 1), algebraMap R A (p.coeff i) * h ^ i = 0 := by
    rw [← Polynomial.eval₂_eq_sum_range, hpeval]
  rw [Finset.sum_range_succ, hpmonic.coeff_natDegree, map_one, one_mul] at key
  have hneg : h ^ p.natDegree = - ∑ i ∈ Finset.range p.natDegree,
      algebraMap R A (p.coeff i) * h ^ i := by
    rw [add_comm] at key
    exact eq_neg_of_add_eq_zero_left key
  rw [hneg]
  rw [Fin.sum_univ_eq_sum_range (fun j => algebraMap R A (-p.coeff j) * h ^ j) p.natDegree]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_neg, neg_mul]

/-- **`y` is a polynomial in the chart generators.**  If `u₀ l` are the generators of the
`j₀`-chart supplied by `chartRing_gen_mul_eq` (so that `u₀ l * algebraMap (t j₀) = algebraMap (t l)`),
then every element of the chart ring — in particular `y` — is a polynomial in the `u₀ l`, reindexed
along any equivalence `ι ≃ Fin m`. -/
private lemma exists_aeval_eq_chartRing_singleton_glue {R : Type a} [CommRing R] {ι : Type a}
    [DecidableEq ι] (t : ι → R) (j₀ : ι) {m : ℕ} (σ : ι ≃ Fin m)
    (u₀ : ι → ↥(chartRing t {j₀}))
    (hu₀ : ∀ l : ι, ((u₀ l : ↥(chartRing t {j₀})) : Localization.Away (tS t {j₀}))
        * algebraMap R (Localization.Away (tS t {j₀})) (t j₀)
      = algebraMap R (Localization.Away (tS t {j₀})) (t l))
    (y : ↥(chartRing t {j₀})) :
    ∃ C : MvPolynomial (Fin m) R,
      MvPolynomial.aeval (fun a => u₀ (σ.symm a)) C = y := by
  -- `algebraMap (t j₀)` is a unit of the localisation `R_{t j₀}`, so the equation
  -- `u l * algebraMap (t j₀) = algebraMap (t l)` determines `u l` uniquely.
  have hunit : IsUnit (algebraMap R (Localization.Away (tS t {j₀})) (t j₀)) := by
    rw [show t j₀ = tS t {j₀} from (tS_singleton_eq t j₀).symm]
    exact IsLocalization.Away.algebraMap_isUnit (tS t {j₀})
  -- hence the defining generators of the chart ring are exactly the `u₀ l`
  have hgens : chartGens t {j₀} ⊆
      Set.range (fun a : Fin m => (u₀ (σ.symm a) : Localization.Away (tS t {j₀}))) := by
    intro w hw
    obtain ⟨i, hi, k, hk⟩ := hw
    rw [Finset.mem_singleton] at hi
    subst hi
    refine ⟨σ k, ?_⟩
    simp only [Equiv.symm_apply_apply]
    apply IsUnit.mul_right_cancel hunit
    rw [hu₀ k, hk]
  have hle : Algebra.adjoin R (chartGens t {j₀}) ≤
      Algebra.adjoin R (Set.range (fun a : Fin m =>
        (u₀ (σ.symm a) : Localization.Away (tS t {j₀})))) :=
    Algebra.adjoin_le (fun w hw => Algebra.subset_adjoin (hgens hw))
  obtain ⟨C, hC⟩ : ∃ C : MvPolynomial (Fin m) R,
      MvPolynomial.aeval (fun a : Fin m => (u₀ (σ.symm a) : Localization.Away (tS t {j₀}))) C
        = (y : Localization.Away (tS t {j₀})) := by
    have hmem : (y : Localization.Away (tS t {j₀})) ∈
        Algebra.adjoin R (Set.range (fun a : Fin m =>
          (u₀ (σ.symm a) : Localization.Away (tS t {j₀})))) :=
      hle y.2
    rw [Algebra.adjoin_range_eq_range_aeval] at hmem
    exact (AlgHom.mem_range _).mp hmem
  refine ⟨C, ?_⟩
  -- compare the two `aeval`s along the inclusion `↥A → R_{t j₀}`
  apply Subtype.ext
  change (Subalgebra.val (chartRing t {j₀})) (MvPolynomial.aeval (fun a => u₀ (σ.symm a)) C)
    = (Subalgebra.val (chartRing t {j₀})) y
  have h : (Subalgebra.val (chartRing t {j₀})) (MvPolynomial.aeval (fun a => u₀ (σ.symm a)) C)
      = (MvPolynomial.aeval (fun a : Fin m =>
          (u₀ (σ.symm a) : Localization.Away (tS t {j₀})))) C := by
    have h2 := congrArg (fun g => g C)
      (MvPolynomial.comp_aeval (fun a : Fin m => u₀ (σ.symm a))
        (Subalgebra.val (chartRing t {j₀})))
    change ((Subalgebra.val (chartRing t {j₀})).comp
        (MvPolynomial.aeval fun a => u₀ (σ.symm a))) C
      = (MvPolynomial.aeval fun a : Fin m =>
          ((u₀ (σ.symm a) : ↥(chartRing t {j₀})) : Localization.Away (tS t {j₀}))) C
    exact h2
  rw [h]
  exact hC

/-- **The `j₀`-chart witness of a compatible family.** For `R` perfect of characteristic `p`, `t : ι → R` finite, `T ∈ R` with `t j₀ = T ^ e`, and `y` the coordinates of a `0`-cycle of the honest chart Čech complex (i.e. pairwise compatible), the `j₀`-component of `ϖ k • y` is already the image of an element of `R`. This is the `j₀`-chart half of the target `Work.DSM5b.chartCechH0_root_killing`, obtained from the engine `Work.DSM5b.varpi_smul_eq_algebraMap_of_integral` (with `A := chartRing t {j₀}`, `u l := t l / T ^ e` so that `T ^ e * u l = algebraMap (t l)`, which holds because of `hj₀`, and `h := y j₀`, which is a polynomial in the `u l` since `chartRing t {j₀} = Algebra.adjoin R {u l}`) together with the integrality of the components (`Work.DSM5b.component_isIntegral_pairwise`, which supplies the monic relation). Note `Work.DSM5b.chartRing_gen_mul_eq t j₀ l` provides `u l` with `u l * algebraMap (t j₀) = algebraMap (t l)` and `tS t {j₀} = t j₀`; the engine is stated for `Fin m`, so it must be transferred along an equivalence `ι ≃ Fin (Fintype.card ι)`. This covers only the `j₀`-chart (see `NOTES_chartCechH0_root_killing.md` §5, Finding 14: it does not by itself finish the target). -/
theorem glue_witness_mem (p : ℕ) [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p]
    [PerfectRing R p] {ι : Type a} [Finite ι] [DecidableEq ι] (t : ι → R) (T : R) (j₀ : ι) (e : ℕ)
    (hj₀ : t j₀ = T ^ e) (y : ∀ i : ι, ↥(chartRing t {i}))
    (hy : ∀ i j : ι,
      locRes t (Finset.subset_union_left : ({i} : Finset ι) ⊆ {i} ∪ {j})
          ((y i : chartRing t {i}) : Localization.Away (tS t {i}))
        = locRes t (Finset.subset_union_right : ({j} : Finset ι) ⊆ {i} ∪ {j})
          ((y j : chartRing t {j}) : Localization.Away (tS t {j})))
    (k : ℕ) :
    ∃ r' : R, (frobeniusEquiv R p).symm^[k] T • y j₀
      = algebraMap R ↥(chartRing t {j₀}) r' := by
  classical
  -- `R` is perfect, hence reduced; the `j₀`-chart ring, a subalgebra of a localisation, inherits
  -- reducedness.
  haveI hR : IsReduced R := isReduced_of_perfectRing_glue p R
  haveI hA : IsReduced ↥(chartRing t {j₀}) := by
    constructor
    intro x hx
    exact Subtype.ext (IsReduced.eq_zero _
      (hx.map (algebraMap ↥(chartRing t {j₀}) (Localization.Away (tS t {j₀})))))
  -- reindex `ι` by `Fin (Fintype.card ι)` so that the engine applies
  letI : Fintype ι := Fintype.ofFinite ι
  let σ : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  -- the generators `u₀ l = t l / t j₀ = t l / T ^ e` of the `j₀`-chart
  choose u₀ hu₀ using fun l : ι => chartRing_gen_mul_eq t j₀ l
  -- `y j₀` is a polynomial in the generators
  obtain ⟨C, hC⟩ := exists_aeval_eq_chartRing_singleton_glue t j₀ σ u₀ hu₀ (y j₀)
  -- `y j₀` is integral over `R` (the components of a `0`-cycle are), producing the monic relation
  obtain ⟨s, c, hmon⟩ := exists_fin_monic_relation_of_isIntegral_glue
    (component_isIntegral_pairwise p t T j₀ e hj₀ y hy j₀)
  -- `T ^ e • u₀ l = algebraMap (t l)`, i.e. the engine's hypothesis `hu`
  have hu' : ∀ a : Fin (Fintype.card ι),
      T ^ e • u₀ (σ.symm a) = algebraMap R ↥(chartRing t {j₀}) (t (σ.symm a)) := by
    intro a
    apply Subtype.ext
    rw [Algebra.smul_def, Subalgebra.coe_mul, Subalgebra.coe_algebraMap,
      Subalgebra.coe_algebraMap]
    have h := hu₀ (σ.symm a)
    rw [hj₀] at h
    rw [mul_comm, h]
  -- run the Frobenius/integrality engine
  obtain ⟨r', hr'⟩ := varpi_smul_eq_algebraMap_of_integral (A := ↥(chartRing t {j₀})) p
    (fun a : Fin (Fintype.card ι) => u₀ (σ.symm a))
    (fun a : Fin (Fintype.card ι) => t (σ.symm a))
    T e hu' (y j₀) C hC C.totalDegree le_rfl c hmon k
  exact ⟨r', hr'⟩

end Work.DSM5b
