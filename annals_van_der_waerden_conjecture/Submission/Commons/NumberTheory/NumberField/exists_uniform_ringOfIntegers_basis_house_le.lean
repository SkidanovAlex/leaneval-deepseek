import Mathlib
import Submission.Commons.Lattice.SuccessiveMinima.Basic
import Submission.Commons.Lattice.SuccessiveMinima.exact_realization
import Submission.Commons.Lattice.SuccessiveMinima.positive
import Submission.Commons.Lattice.Minkowski.minkowski_second_upper_measure
import Submission.Commons.Lattice.Minkowski.bounded_basis_of_bounded_realizers
import Submission.Commons.Lattice.Minkowski.bounded_basis_of_bounded_realizers_innerProductSpace
import Submission.Commons.Lattice.Minkowski.flag_basis
import Submission.Commons.FieldTheory.span_top_of_pair_mul_of_linIndependent
import Submission.Commons.LinearAlgebra.Module.exists_independent_subfamily_of_span_top
import Submission.Commons.LinearAlgebra.Independence.discrete_basis_values_linIndep_general
import Submission.Commons.Algebra.Nat.two_mul_div_two_succ_gt
import Submission.Commons.Algebra.Nat.le_two_mul_of_le_div_two
import Submission.Commons.Algebra.Nat.div_two_succ_le
import Submission.Commons.Analysis.InnerProductSpace.EuclideanSpace_coord_le_norm
import Submission.Commons.NumberTheory.NumberField.mixedEmbedding_linearIndependent_of_linearIndependent
import Submission.Commons.Algebra.BigOperators.pow_le_prod_of_mono_succ
import Submission.Commons.NumberTheory.NumberField.one_le_rootDiscr
import Submission.Commons.NumberTheory.NumberField.mixedEmbedding_basis_values_linearIndependent
import Submission.Commons.NumberTheory.NumberField.basis_house_le_one_of_finrank_eq_one

/-!
# A uniform `ℤ`-basis of the ring of integers with small house

There is an absolute constant `c` such that for every number field `K` the ring of
integers `𝓞 K` admits a `ℤ`-basis whose elements have house bounded by
`(finrank)^c · (rootDiscr)^c`.

Proof outline:
1. realise `𝓞 K` as the lattice `L := mixedEmbedding.integerLattice K` in the mixed
   space with its sup norm;
2. Minkowski's second theorem bounds the first `m := ⌈(n+1)/2⌉` successive minima by
   `16 · rootDiscr`; exact realisation turns them into small lattice vectors;
3. pairwise products of these vectors span the full rank; a spanning family contains a
   basis, giving `n` `ℤ`-independent small realisers;
4. `bounded_basis_of_bounded_realizers_innerProductSpace` upgrades bounded realisers to a
   bounded `ℤ`-basis of the whole Euclidean lattice;
5. `house ≤ ‖·‖` and a large `c` give the statement.
-/

noncomputable section

open scoped NumberField BigOperators NNReal ENNReal Classical
open NumberField NumberField.mixedEmbedding MeasureTheory Set Filter Metric Submodule

namespace Commons.NumberTheory.NumberField

namespace SmallBasis

open NumberField.mixedEmbedding

/-- The image of the ring of integers of `K` in the sup-norm mixed space. -/
abbrev SupLattice (K : Type*) [Field K] [NumberField K] : Submodule ℤ (mixedSpace K) :=
  mixedEmbedding.integerLattice K

/-- The image of the ring of integers of `K` in the Euclidean mixed space. -/
abbrev EucLattice (K : Type*) [Field K] [NumberField K] : Submodule ℤ (euclidean.mixedSpace K) :=
  euclidean.integerLattice K

/-- The degree of `K`. -/
abbrev deg (K : Type*) [Field K] [NumberField K] : ℕ := Module.finrank ℚ K

/-- Number of real (resp. complex) places. -/
abbrev r1 (K : Type*) [Field K] [NumberField K] : ℕ := InfinitePlace.nrRealPlaces K
abbrev r2 (K : Type*) [Field K] [NumberField K] : ℕ := InfinitePlace.nrComplexPlaces K

/-- The `i`-th successive minimum of the sup lattice. -/
abbrev lam (K : Type*) [Field K] [NumberField K] (i : ℕ) : ℝ :=
  Commons.Lattice.SuccessiveMinima.successiveMinimum (SupLattice K) i

/-- The `ℤ`-rank of the lattice is the degree. -/
lemma finrank_SupLattice (K : Type*) [Field K] [NumberField K] :
    Module.finrank ℤ (SupLattice K) = deg K := by
  dsimp [SupLattice, deg]
  rw [ZLattice.rank ℝ, NumberField.mixedEmbedding.finrank]

/-- The `ℤ`-rank of the Euclidean lattice is the degree. -/
lemma finrank_EucLattice (K : Type*) [Field K] [NumberField K] :
    Module.finrank ℤ (EucLattice K) = deg K := by
  dsimp [EucLattice, deg]
  rw [ZLattice.rank ℝ, euclidean.finrank]

lemma mem_integerLattice (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) :
    mixedEmbedding K (a : K) ∈ mixedEmbedding.integerLattice K := by
  rw [NumberField.mixedEmbedding.integerLattice, LinearMap.mem_range]
  exact ⟨a, rfl⟩

/-- Every element of the sup lattice is the mixed embedding of an integral element. -/
lemma supLattice_eq_mixedEmbedding (K : Type*) [Field K] [NumberField K] (v : SupLattice K) :
    ∃ a : 𝓞 K, mixedEmbedding K (a : K) = (v : mixedSpace K) := by
  classical
  have hmem : (v : mixedSpace K) ∈ SupLattice K := v.2
  change (v : mixedSpace K) ∈ mixedEmbedding.integerLattice K at hmem
  rw [NumberField.mixedEmbedding.integerLattice, LinearMap.mem_range] at hmem
  rcases hmem with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  change (mixedEmbedding K) ((algebraMap (𝓞 K) K) a) = (v : mixedSpace K)
  simpa using ha

/-- The element of the sup-norm lattice associated with `a ∈ 𝓞 K`. -/
def supOf (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) : SupLattice K :=
  ⟨mixedEmbedding K (a : K), mem_integerLattice K a⟩

/-- The element of the Euclidean lattice associated with `a ∈ 𝓞 K`. -/
def eucOf (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) : EucLattice K :=
  ⟨(euclidean.toMixed K).symm (mixedEmbedding K (a : K)), by
    rw [EucLattice, euclidean.integerLattice, ZLattice.comap, Submodule.mem_comap]
    exact mem_integerLattice K a⟩

@[simp] lemma supOf_coe (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) :
    ((supOf K a : SupLattice K) : mixedSpace K) = mixedEmbedding K (a : K) := rfl

@[simp] lemma eucOf_coe (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) :
    ((eucOf K a : EucLattice K) : euclidean.mixedSpace K) =
      (euclidean.toMixed K).symm (mixedEmbedding K (a : K)) := rfl

/-- `house a ≤ ‖mixedEmbedding a‖` (sup norm on the mixed space). -/
lemma house_le_sup_mixed (K : Type*) [Field K] [NumberField K] (a : K) :
    NumberField.house a ≤ ‖mixedEmbedding K a‖ := by
  classical
  rw [NumberField.house]
  rw [NumberField.canonicalEmbedding.norm_le_iff]
  intro φ
  rw [← (NumberField.InfinitePlace.apply φ a)]
  rw [← NumberField.mixedEmbedding.normAtPlace_apply (InfinitePlace.mk φ) a]
  rw [NumberField.mixedEmbedding.norm_eq_sup'_normAtPlace]
  exact Finset.le_sup' (s := Finset.univ)
    (f := fun w : InfinitePlace K => NumberField.mixedEmbedding.normAtPlace w (mixedEmbedding K a))
    (Finset.mem_univ (InfinitePlace.mk φ))

/-- `house` of an integral element is at most the sup-norm of its lattice point. -/
lemma house_le_supOf (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) :
    NumberField.house (a : K) ≤ ‖((supOf K a : SupLattice K) : mixedSpace K)‖ := by
  simpa using house_le_sup_mixed K (a : K)

/-- Every nonzero element of the sup lattice has norm at least `1`. -/
lemma sup_lattice_norm_ge_one (K : Type*) [Field K] [NumberField K]
    {v : SupLattice K} (hv : v ≠ 0) : (1 : ℝ) ≤ ‖(v : mixedSpace K)‖ := by
  classical
  rcases supLattice_eq_mixedEmbedding K v with ⟨a, ha⟩
  have ha0 : (a : K) ≠ 0 := by
    intro h
    apply hv
    apply Subtype.ext
    simpa [h] using ha.symm
  have hhouse : (1 : ℝ) ≤ NumberField.house (a : K) := by
    exact NumberField.one_le_house_of_isIntegral (α := (a : K)) a.2 ha0
  rw [← ha]
  exact hhouse.trans (house_le_sup_mixed K (a : K))

/-- Successive minima of the sup lattice are at least `1`. -/
lemma successiveMinimum_ge_one (K : Type*) [Field K] [NumberField K] (i : ℕ) (hi0 : 0 < i)
    (hi : i ≤ deg K) :
    (1 : ℝ) ≤ lam K i := by
  classical
  have hS : (Commons.Lattice.SuccessiveMinima.successiveMinimumSet (SupLattice K) i).Nonempty := by
    exact Commons.Lattice.SuccessiveMinima.nonempty_successiveMinimumSet (SupLattice K) i
      (by simpa [finrank_SupLattice] using hi)
  exact Commons.Lattice.SuccessiveMinima.successiveMinimum_ge_of_forall_ne_zero_norm_ge
    (SupLattice K) 1 hi0 hS (by intro v hv; exact sup_lattice_norm_ge_one K hv)

/-- Successive minima are nondecreasing in the index. -/
lemma mono_lam (K : Type*) [Field K] [NumberField K] {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ deg K) : lam K i ≤ lam K j := by
  classical
  rw [← finrank_SupLattice K] at hj
  exact Commons.Lattice.SuccessiveMinima.successiveMinimum_mono (SupLattice K) hij hj

/-- covolume of the sup lattice, exact formula. -/
lemma covolume_SupLattice (K : Type*) [Field K] [NumberField K] :
    ZLattice.covolume (SupLattice K) =
      (2 : ℝ)⁻¹ ^ r2 K * Real.sqrt |(NumberField.discr K : ℤ)| := by
  classical
  dsimp [SupLattice, r2]
  exact NumberField.mixedEmbedding.covolume_integerLattice K

/-- The closed unit sup-ball has volume at least `2^r1 · π^r2`. -/
lemma volume_sup_closedBall_ge (K : Type*) [Field K] [NumberField K] :
    ((2 : ℝ) ^ r1 K * Real.pi ^ r2 K) ≤
      ENNReal.toReal (volume (Metric.closedBall (0 : mixedSpace K) 1)) := by
  classical
  let f : InfinitePlace K → ℝ≥0 := fun _ => 1
  have hsub : convexBodyLT K f ⊆ Metric.closedBall (0 : mixedSpace K) 1 := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    rw [NumberField.mixedEmbedding.norm_eq_sup'_normAtPlace]
    refine Finset.sup'_le Finset.univ_nonempty (fun w : InfinitePlace K => NumberField.mixedEmbedding.normAtPlace w x) ?_
    intro w hw
    have hxw : NumberField.mixedEmbedding.normAtPlace w x ≤ (f w : ℝ) := by
      dsimp [convexBodyLT] at hx
      rcases hx with ⟨hx1, hx2⟩
      by_cases hwreal : w.IsReal
      · rw [NumberField.mixedEmbedding.normAtPlace_apply_of_isReal hwreal]
        have hm := (Set.mem_pi.mp hx1) ⟨w, hwreal⟩ (Set.mem_univ _)
        rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hm
        exact le_of_lt (by simpa [f] using hm)
      · rw [NumberField.mixedEmbedding.normAtPlace_apply_of_isComplex (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hwreal)]
        have hm := (Set.mem_pi.mp hx2) ⟨w, (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hwreal)⟩ (Set.mem_univ _)
        rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hm
        exact le_of_lt (by simpa [f] using hm)
    simpa [f] using hxw
  have hmono : volume (convexBodyLT K f) ≤ volume (Metric.closedBall (0 : mixedSpace K) 1) :=
    measure_mono hsub
  have hvol : ENNReal.toReal (volume (convexBodyLT K f)) = (2 : ℝ) ^ r1 K * Real.pi ^ r2 K := by
    rw [NumberField.mixedEmbedding.convexBodyLT_volume]
    simp [f, convexBodyLTFactor, r1, r2]
  have htop : volume (Metric.closedBall (0 : mixedSpace K) 1) ≠ ⊤ := by
    exact (IsCompact.measure_lt_top (isCompact_closedBall (0 : mixedSpace K) 1)).ne
  rw [← hvol]
  exact ENNReal.toReal_mono htop hmono

/-- Minkowski's second theorem: product of successive minima × ball volume ≤ `2^(2n) covol`. -/
lemma prod_lam_vol_le (K : Type*) [Field K] [NumberField K] :
    (∏ j : Fin (deg K), lam K (j.val + 1)) *
        ENNReal.toReal (volume (Metric.closedBall (0 : mixedSpace K) 1)) ≤
      (2 : ℝ) ^ (2 * deg K) * ZLattice.covolume (SupLattice K) := by
  classical
  have hd : 0 < deg K := by dsimp [deg]; exact Module.finrank_pos (R := ℚ) (M := K)
  have hfin : Module.finrank ℤ (SupLattice K) = deg K := finrank_SupLattice K
  simpa [SupLattice] using
    (Commons.Lattice.Minkowski.minkowski_second_upper_measure (d := deg K) hd
      (E := mixedSpace K) (L := SupLattice K) hfin)

/-- product of all successive minima `≤ 2^(2n) · sqrt |discr|`. -/
lemma prod_lam_le (K : Type*) [Field K] [NumberField K] :
    (∏ j : Fin (deg K), lam K (j.val + 1)) ≤
      (2 : ℝ) ^ (2 * deg K) * Real.sqrt |(NumberField.discr K : ℤ)| := by
  classical
  have hvol1 : (1 : ℝ) ≤ ENNReal.toReal (volume (Metric.closedBall (0 : mixedSpace K) 1)) := by
    have h11 : (1 : ℝ) ≤ 2 ^ r1 K * Real.pi ^ r2 K := by
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ r1 K := one_le_pow₀ (by norm_num)
      have hpi : (1 : ℝ) ≤ Real.pi ^ r2 K := one_le_pow₀ (le_trans (by norm_num : (1 : ℝ) ≤ 2) Real.two_le_pi)
      simpa using (mul_le_mul h2 hpi (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ (2 : ℝ) ^ r1 K))
    exact h11.trans (volume_sup_closedBall_ge K)
  let P := ∏ j : Fin (deg K), lam K (j.val + 1)
  have hP0 : 0 ≤ P := by
    dsimp [P]
    refine Finset.prod_nonneg ?_
    intro j hj
    exact Commons.Lattice.SuccessiveMinima.successiveMinimum_nonneg (SupLattice K) (j.val + 1)
      (by calc j.val + 1 ≤ deg K := Nat.succ_le_of_lt j.isLt
               _ = Module.finrank ℤ (SupLattice K) := (finrank_SupLattice K).symm)
  have hle : P ≤ P * ENNReal.toReal (volume (Metric.closedBall (0 : mixedSpace K) 1)) := by
    exact le_mul_of_one_le_right hP0 hvol1
  calc
    P ≤ P * ENNReal.toReal (volume (Metric.closedBall (0 : mixedSpace K) 1)) := hle
    _ ≤ (2 : ℝ) ^ (2 * deg K) * ZLattice.covolume (SupLattice K) := by
      simpa [P] using prod_lam_vol_le K
    _ ≤ (2 : ℝ) ^ (2 * deg K) * Real.sqrt |(NumberField.discr K : ℤ)| := by
      rw [covolume_SupLattice]
      have hsmall : (2 : ℝ)⁻¹ ^ r2 K * Real.sqrt |(NumberField.discr K : ℤ)| ≤
          Real.sqrt |(NumberField.discr K : ℤ)| := by
        have hpow : (2 : ℝ)⁻¹ ^ r2 K ≤ 1 := pow_le_one₀ (by positivity) (by norm_num)
        exact (mul_le_mul_of_nonneg_right hpow (Real.sqrt_nonneg _)).trans_eq (one_mul _)
      exact mul_le_mul_of_nonneg_left hsmall (pow_nonneg (by norm_num) _)

/-- `λᵢ ^ (n+1-i) ≤ product of all successive minima`. -/
lemma lam_pow_le_prod (K : Type*) [Field K] [NumberField K]
    (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ deg K) :
    lam K i ^ (deg K + 1 - i) ≤ ∏ j : Fin (deg K), lam K (j.val + 1) := by
  classical
  exact Commons.Algebra.BigOperators.pow_le_prod_of_mono_succ (n := deg K) (i := i)
    (fun j => lam K j) hi1 hin
    (by intro j hj; exact Commons.Lattice.SuccessiveMinima.successiveMinimum_nonneg (SupLattice K) j (hj.trans (finrank_SupLattice K).symm.le))
    (by intro j hj hji; exact mono_lam K hji hj)
    (by intro j h1j hji; exact successiveMinimum_ge_one K j (by omega) (by omega))

/-- The discriminant is a nonzero integer, so `|discr| ≥ 1`. -/
lemma discr_abs_ge_one (K : Type*) [Field K] [NumberField K] :
    (1 : ℝ) ≤ |(NumberField.discr K : ℤ)| := by
  have hne : NumberField.discr K ≠ 0 := NumberField.discr_ne_zero K
  have hz : (1 : ℤ) ≤ |NumberField.discr K| := Int.one_le_abs hne
  have hzR : (1 : ℝ) ≤ |((NumberField.discr K : ℤ) : ℝ)| := by
    have hc : ((1 : ℤ) : ℝ) ≤ ((|NumberField.discr K| : ℤ) : ℝ) := by exact_mod_cast hz
    simpa [Int.cast_abs] using hc
  simpa using hzR

/-- `rootDiscr = |discr|^(1/n)`. -/
lemma rootDiscr_eq_rpow (K : Type*) [Field K] [NumberField K] :
    NumberField.rootDiscr K =
      |(NumberField.discr K : ℤ)| ^ ((deg K : ℝ)⁻¹) := by
  classical
  dsimp [deg]
  rw [NumberField.rootDiscr_def]

/-- For `e ≥ n/2`, `√|discr| ≤ rootDiscr^e`. -/
lemma sqrt_disc_le_rootDiscr_pow (K : Type*) [Field K] [NumberField K]
    (e : ℕ) (he2 : deg K ≤ 2 * e) :
    Real.sqrt |(NumberField.discr K : ℤ)| ≤ NumberField.rootDiscr K ^ e := by
  classical
  let n := deg K
  let d : ℝ := |(NumberField.discr K : ℤ)|
  have hd0 : 0 ≤ d := by dsimp [d]; exact abs_nonneg _
  have hd1 : 1 ≤ d := by simpa [d] using discr_abs_ge_one K
  have hn0nat : 0 < n := by
    dsimp [n, deg]
    exact Module.finrank_pos (R := ℚ) (M := K)
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn0nat
  have hs : Real.sqrt d = d ^ (1 / (2 : ℝ)) := Real.sqrt_eq_rpow d
  have hnat : n ≤ 2 * e := by simpa [n] using he2
  have hle12 : (1 / (2 : ℝ)) ≤ (e : ℝ) / (n : ℝ) := by
    rw [le_div_iff₀' hn0]
    have hne2 : (n : ℝ) ≤ (2 * e : ℕ) := by exact_mod_cast hnat
    norm_num at hne2
    nlinarith
  have hpow : d ^ (1 / (2 : ℝ)) ≤ d ^ ((e : ℝ) / (n : ℝ)) := Real.rpow_le_rpow_of_exponent_le hd1 hle12
  have hR : NumberField.rootDiscr K = d ^ ((n : ℝ)⁻¹) := by
    simpa [d, n] using rootDiscr_eq_rpow K
  -- d^(e/n) = (d^(1/n))^e
  have heq : d ^ ((e : ℝ) / (n : ℝ)) = (d ^ ((n : ℝ)⁻¹)) ^ e := by
    rw [div_eq_mul_inv]
    rw [mul_comm (e : ℝ) ((n : ℝ)⁻¹)]
    rw [Real.rpow_mul hd0]
    rw [Real.rpow_natCast]
  calc
    Real.sqrt d = d ^ (1 / (2 : ℝ)) := hs
    _ ≤ d ^ ((e : ℝ) / (n : ℝ)) := hpow
    _ = (d ^ ((n : ℝ)⁻¹)) ^ e := heq
    _ = NumberField.rootDiscr K ^ e := by rw [hR]

/-- For `i` with `2·i ≤ deg K + 2`, `λᵢ ≤ 16 · rootDiscr`. -/
lemma lam_le_16root (K : Type*) [Field K] [NumberField K]
    (i : ℕ) (hi0 : 0 < i) (him : 2 * i ≤ deg K + 2) :
    lam K i ≤ 16 * NumberField.rootDiscr K := by
  classical
  let n := deg K
  let R := NumberField.rootDiscr K
  let e := n + 1 - i
  have hR0 : 0 ≤ R := le_of_lt (lt_of_lt_of_le zero_lt_one (one_le_rootDiscr K))
  have hR1 : 1 ≤ R := one_le_rootDiscr K
  have hnpos : 1 ≤ deg K := by
    dsimp [deg]
    exact Nat.succ_le_of_lt (Module.finrank_pos (R := ℚ) (M := K))
  have hin : i ≤ n := by
    dsimp [n]
    by_cases hd : deg K ≤ 1
    · omega
    · omega
  have he0 : 0 < e := by dsimp [e]; omega
  have he2 : n ≤ 2 * e := by
    dsimp [n, e]
    omega
  have hlam0 : 0 ≤ lam K i := by
    exact Commons.Lattice.SuccessiveMinima.successiveMinimum_nonneg (SupLattice K) i
      (hin.trans (finrank_SupLattice K).symm.le)
  have h16R0 : 0 ≤ 16 * R := by positivity
  have hsqrt : Real.sqrt |(NumberField.discr K : ℤ)| ≤ R ^ e := by
    simpa [n, R, e] using sqrt_disc_le_rootDiscr_pow K e he2
  have h16pow : (2 : ℝ) ^ (2 * n) ≤ (16 : ℝ) ^ e := by
    have h2n4e : 2 * n ≤ 4 * e := by dsimp [n, e]; omega
    have h1 : (2 : ℝ) ^ (2 * n) ≤ (2 : ℝ) ^ (4 * e) := pow_le_pow_right₀ (by norm_num) h2n4e
    have h2 : (2 : ℝ) ^ (4 * e) = (16 : ℝ) ^ e := by
      symm
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num]
      rw [pow_mul]
    simpa [h2] using h1
  have hY : lam K i ^ e ≤ (2 : ℝ) ^ (2 * n) * Real.sqrt |(NumberField.discr K : ℤ)| := by
    calc
      lam K i ^ e ≤ ∏ j : Fin n, lam K (j.val + 1) := by
        simpa [n, e] using lam_pow_le_prod K i hi0 hin
      _ ≤ (2 : ℝ) ^ (2 * n) * Real.sqrt |(NumberField.discr K : ℤ)| := by
        simpa [n] using prod_lam_le K
  have hYle : (2 : ℝ) ^ (2 * n) * Real.sqrt |(NumberField.discr K : ℤ)| ≤ (16 * R) ^ e := by
    have hA : (2 : ℝ) ^ (2 * n) ≤ (16 : ℝ) ^ e := h16pow
    have hB : Real.sqrt |(NumberField.discr K : ℤ)| ≤ R ^ e := hsqrt
    have hB0 : 0 ≤ Real.sqrt |(NumberField.discr K : ℤ)| := Real.sqrt_nonneg _
    have hB' : 0 ≤ (16 : ℝ) ^ e := by positivity
    have hm := mul_le_mul hA hB hB0 hB'
    -- (16)^e * R^e = (16*R)^e
    rw [← mul_pow] at hm
    exact hm
  have hmain : lam K i ^ e ≤ (16 * R) ^ e := le_trans hY hYle
  exact (pow_le_pow_iff_left₀ hlam0 h16R0 (by omega : e ≠ 0)).mp hmain

/-- Exact realisers of the first `⌈(n+1)/2⌉` successive minima, bounded by `16 · rootDiscr`. -/
lemma exists_realizers (K : Type*) [Field K] [NumberField K] :
    ∃ v : Fin ((deg K + 2) / 2) → SupLattice K,
      LinearIndependent ℝ (fun j : Fin ((deg K + 2) / 2) => (v j : mixedSpace K)) ∧
      ∀ j : Fin ((deg K + 2) / 2),
        ‖(v j : mixedSpace K)‖ ≤ 16 * NumberField.rootDiscr K := by
  classical
  let m : ℕ := (deg K + 2) / 2
  have hdeg1 : 1 ≤ deg K := by
    dsimp [deg]
    exact Nat.succ_le_of_lt (Module.finrank_pos (R := ℚ) (M := K))
  have hmdeg : m ≤ deg K := by
    dsimp [m]
    exact Commons.Algebra.Nat.div_two_succ_le hdeg1
  obtain ⟨v0, hLI, hbd⟩ := Commons.Lattice.SuccessiveMinima.exact_realization
    (E := mixedSpace K) (L := SupLattice K) (m := deg K) (finrank_SupLattice K)
  let w : Fin m → SupLattice K := fun j => v0 (Fin.castLE hmdeg j)
  refine ⟨w, ?_, ?_⟩
  · -- subfamily of an ℝ-independent family is independent
    have hw : (fun j : Fin m => (w j : mixedSpace K)) =
        (fun j : Fin m => (v0 (Fin.castLE hmdeg j) : mixedSpace K)) := rfl
    rw [hw]
    exact hLI.comp (Fin.castLE hmdeg) (Fin.castLE_injective hmdeg)
  · intro j
    have hj1 : 0 < j.val + 1 := by omega
    have hj2 : 2 * (j.val + 1) ≤ deg K + 2 := by
      have ha : j.val + 1 ≤ (deg K + 2) / 2 := by
        have : j.val < m := j.isLt
        dsimp [m] at this
        omega
      exact Commons.Algebra.Nat.le_two_mul_of_le_div_two (deg K) (j.val + 1) ha
    calc
      ‖(w j : mixedSpace K)‖ ≤ lam K (j.val + 1) := by
        exact hbd (Fin.castLE hmdeg j)
      _ ≤ 16 * NumberField.rootDiscr K := lam_le_16root K (j.val + 1) hj1 hj2

/-- The underlying ring-of-integers elements of the realisers are `ℚ`-independent. -/
lemma exists_realizer_elements (K : Type*) [Field K] [NumberField K] :
    ∃ a : Fin ((deg K + 2) / 2) → 𝓞 K,
      LinearIndependent ℚ (fun j : Fin ((deg K + 2) / 2) => (a j : K)) ∧
      ∀ j : Fin ((deg K + 2) / 2),
        ‖mixedEmbedding K ((a j : K) : K)‖ ≤ 16 * NumberField.rootDiscr K := by
  classical
  let m : ℕ := (deg K + 2) / 2
  obtain ⟨v, hLI, hbd⟩ := exists_realizers K
  have haux : ∀ j : Fin m, ∃ a : 𝓞 K, mixedEmbedding K (a : K) = (v j : mixedSpace K) := by
    intro j
    exact supLattice_eq_mixedEmbedding K (v j)
  let a : Fin m → 𝓞 K := fun j => Classical.choose (haux j)
  refine ⟨a, ?_, ?_⟩
  ·
    have hfam : (fun j : Fin m => mixedEmbedding K ((a j : 𝓞 K) : K)) =
        (fun j : Fin m => (v j : mixedSpace K)) := by
      funext j
      exact Classical.choose_spec (haux j)
    have hLI_img : LinearIndependent ℝ (fun j : Fin m => mixedEmbedding K ((a j : 𝓞 K) : K)) := by
      rw [hfam]
      exact hLI
    exact Commons.NumberTheory.NumberField.mixedEmbedding_linearIndependent_of_linearIndependent (a := fun j : Fin m => (a j : K)) hLI_img
  · intro j
    have hch := Classical.choose_spec (haux j)
    calc
      ‖mixedEmbedding K ((a j : 𝓞 K) : K)‖ = ‖(v j : mixedSpace K)‖ := by rw [hch]
      _ ≤ 16 * NumberField.rootDiscr K := hbd j

/-- Multiplication in the mixed space is bounded by products of sup norms (product norm
inequality, per-place). -/
lemma sup_norm_mul_le (K : Type*) [Field K] [NumberField K] (a b : K) :
    ‖mixedEmbedding K (a * b)‖ ≤ ‖mixedEmbedding K a‖ * ‖mixedEmbedding K b‖ := by
  classical
  rw [NumberField.mixedEmbedding.norm_eq_sup'_normAtPlace]
  refine Finset.sup'_le Finset.univ_nonempty (fun w : InfinitePlace K => NumberField.mixedEmbedding.normAtPlace w (mixedEmbedding K (a * b))) ?_
  intro w hw
  rw [NumberField.mixedEmbedding.normAtPlace_apply]
  -- w (a*b) = (w a) * (w b) since w is a multiplicative absolute value
  calc
    w (a * b) = (w a) * (w b) := by
      let σ := NumberField.InfinitePlace.embedding w
      have hσ : NumberField.InfinitePlace.mk σ = w := NumberField.InfinitePlace.mk_embedding w
      rw [← hσ]
      rw [NumberField.InfinitePlace.apply σ (a * b)]
      rw [map_mul, Complex.norm_mul]
      rw [← NumberField.InfinitePlace.apply σ a, ← NumberField.InfinitePlace.apply σ b]
    _ ≤ ‖mixedEmbedding K a‖ * ‖mixedEmbedding K b‖ := by
      -- w a ≤ sup a and w b ≤ sup b; both nonneg
      have hwa : w a ≤ ‖mixedEmbedding K a‖ := by
        rw [NumberField.mixedEmbedding.norm_eq_sup'_normAtPlace]
        have h1 : NumberField.mixedEmbedding.normAtPlace w (mixedEmbedding K a) ≤
            Finset.univ.sup' Finset.univ_nonempty
              (fun w' : InfinitePlace K => NumberField.mixedEmbedding.normAtPlace w' (mixedEmbedding K a)) :=
          Finset.le_sup' (s := Finset.univ)
            (f := fun w' : InfinitePlace K => NumberField.mixedEmbedding.normAtPlace w' (mixedEmbedding K a))
            (Finset.mem_univ w)
        rwa [NumberField.mixedEmbedding.normAtPlace_apply] at h1
      have hwb : w b ≤ ‖mixedEmbedding K b‖ := by
        rw [NumberField.mixedEmbedding.norm_eq_sup'_normAtPlace]
        have h1 : NumberField.mixedEmbedding.normAtPlace w (mixedEmbedding K b) ≤
            Finset.univ.sup' Finset.univ_nonempty
              (fun w' : InfinitePlace K => NumberField.mixedEmbedding.normAtPlace w' (mixedEmbedding K b)) :=
          Finset.le_sup' (s := Finset.univ)
            (f := fun w' : InfinitePlace K => NumberField.mixedEmbedding.normAtPlace w' (mixedEmbedding K b))
            (Finset.mem_univ w)
        rwa [NumberField.mixedEmbedding.normAtPlace_apply] at h1
      exact mul_le_mul hwa hwb (by positivity) (by positivity)

/-- Products of realisers span `K` over `ℚ`; extract `deg` independent products with a
sup-norm bound. -/
lemma exists_basis_products (K : Type*) [Field K] [NumberField K] :
    ∃ x : Fin (deg K) → 𝓞 K,
      LinearIndependent ℚ (fun j : Fin (deg K) => (x j : K)) ∧
      ∀ j : Fin (deg K),
        ‖mixedEmbedding K ((x j : K) : K)‖ ≤ (16 * NumberField.rootDiscr K) ^ 2 := by
  classical
  let m : ℕ := (deg K + 2) / 2
  obtain ⟨a, hLIa, hbd⟩ := exists_realizer_elements K
  -- a : Fin m → 𝓞 K, ℚ-independent, with sup-norm ≤ 16R
  have hspan : Submodule.span ℚ (Set.range (fun p : Fin m × Fin m => ((a p.1 : 𝓞 K) * (a p.2 : 𝓞 K) : K))) = ⊤ := by
    exact Commons.FieldTheory.span_top_of_pair_mul_of_linIndependent (F := ℚ) (K := K) (m := m)
      (fun j : Fin m => (a j : K)) (by simpa using hLIa)
      (by
        -- 2m > deg
        have hgt : deg K < 2 * m := by
          dsimp [m]
          exact Commons.Algebra.Nat.two_mul_div_two_succ_gt (deg K)
        -- show m + m > deg: m+m = 2m
        simpa [two_mul] using hgt)
  -- R3 extraction: get ℚ-basis t : Fin deg → Fin m × Fin m
  obtain ⟨t, hLIt⟩ := Commons.LinearAlgebra.Module.exists_independent_subfamily_of_span_top
    (F := ℚ) (V := K) (ι := Fin m × Fin m)
    (fun p : Fin m × Fin m => ((a p.1 : 𝓞 K) * (a p.2 : 𝓞 K) : K)) hspan
  let x : Fin (deg K) → 𝓞 K := fun j => ((a (t j).1 : 𝓞 K) * (a (t j).2 : 𝓞 K))
  refine ⟨x, ?_, ?_⟩
  · simpa [x] using hLIt
  · intro j
    -- ‖mixed(x j)‖ ≤ ‖mixed(a t1)‖·‖mixed(a t2)‖ ≤ (16R)²
    calc
      ‖mixedEmbedding K ((x j : 𝓞 K) : K)‖ ≤ ‖mixedEmbedding K ((a (t j).1 : 𝓞 K) : K)‖ *
          ‖mixedEmbedding K ((a (t j).2 : 𝓞 K) : K)‖ := by
        dsimp [x]
        simpa using sup_norm_mul_le K ((a (t j).1 : 𝓞 K) : K) ((a (t j).2 : 𝓞 K) : K)
      _ ≤ (16 * NumberField.rootDiscr K) * (16 * NumberField.rootDiscr K) := by
        have hR0 : 0 ≤ 16 * NumberField.rootDiscr K := by nlinarith [one_le_rootDiscr K]
        exact mul_le_mul (hbd (t j).1) (hbd (t j).2) (by positivity) hR0
      _ = (16 * NumberField.rootDiscr K) ^ 2 := by ring

/-- Norm-square identity for the Euclidean mixed space. -/
lemma euc_norm_sq (K : Type*) [Field K] [NumberField K] (y : euclidean.mixedSpace K) :
    ‖y‖ ^ 2 = ‖y.fst‖ ^ 2 + ‖y.snd‖ ^ 2 := by
  classical
  have h1 : ‖y‖ ^ 2 = inner ℝ y y := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  have h2 : inner ℝ y y = inner ℝ y.fst y.fst + inner ℝ y.snd y.snd := by
    simp [inner]
  have h3f : inner ℝ y.fst y.fst = ‖y.fst‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  have h3s : inner ℝ y.snd y.snd = ‖y.snd‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  rw [h1, h2, h3f, h3s]

lemma fst_le_euc (K : Type*) [Field K] [NumberField K] (y : euclidean.mixedSpace K) :
    ‖y.fst‖ ≤ ‖y‖ := by
  classical
  have h := euc_norm_sq K y
  have hsq : ‖y.fst‖ ^ 2 ≤ ‖y‖ ^ 2 := by nlinarith
  have h := sq_le_sq.mp hsq
  simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] using h

lemma snd_le_euc (K : Type*) [Field K] [NumberField K] (y : euclidean.mixedSpace K) :
    ‖y.snd‖ ≤ ‖y‖ := by
  classical
  have h := euc_norm_sq K y
  have hsq : ‖y.snd‖ ^ 2 ≤ ‖y‖ ^ 2 := by nlinarith
  have h := sq_le_sq.mp hsq
  simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] using h

/-- Euclidean norm of an element in the Euclidean mixed space is at least its sup-norm image. -/
lemma sup_norm_le_euc_norm (K : Type*) [Field K] [NumberField K] (y : euclidean.mixedSpace K) :
    ‖(euclidean.toMixed K) y‖ ≤ ‖y‖ := by
  classical
  rw [NumberField.mixedEmbedding.norm_eq_sup'_normAtPlace]
  refine Finset.sup'_le Finset.univ_nonempty (fun w : InfinitePlace K => NumberField.mixedEmbedding.normAtPlace w (euclidean.toMixed K y)) ?_
  intro w hw
  by_cases hwr : w.IsReal
  · have h1 : NumberField.mixedEmbedding.normAtPlace w (euclidean.toMixed K y) ≤ ‖y.fst‖ := by
      rw [NumberField.mixedEmbedding.normAtPlace_apply_of_isReal hwr]
      have heq : (euclidean.toMixed K y).1 ⟨w, hwr⟩ = y.fst ⟨w, hwr⟩ := by
        simp [euclidean.toMixed, WithLp.linearEquiv]
      rw [heq]
      have hc := Commons.Analysis.InnerProductSpace.EuclideanSpace_coord_le_norm
        (a := y.fst) (i := ⟨w, hwr⟩) (𝕜 := ℝ)
      simpa using hc
    exact h1.trans (fst_le_euc K y)
  · have hwc : w.IsComplex := NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hwr
    have h1 : NumberField.mixedEmbedding.normAtPlace w (euclidean.toMixed K y) ≤ ‖y.snd‖ := by
      rw [NumberField.mixedEmbedding.normAtPlace_apply_of_isComplex hwc]
      have heq : (euclidean.toMixed K y).2 ⟨w, hwc⟩ = y.snd ⟨w, hwc⟩ := by
        simp [euclidean.toMixed, WithLp.linearEquiv]
      rw [heq]
      have hc := Commons.Analysis.InnerProductSpace.EuclideanSpace_coord_le_norm
        (a := y.snd) (i := ⟨w, hwc⟩) (𝕜 := ℂ)
      simpa using hc
    exact h1.trans (snd_le_euc K y)

/-- Sup norm `≤` Euclidean norm up to factor `√n`. -/
lemma euc_norm_le_sqrt_mul_sup (K : Type*) [Field K] [NumberField K] (y : euclidean.mixedSpace K) :
    ‖y‖ ≤ (Real.sqrt (deg K)) * ‖(euclidean.toMixed K) y‖ := by
  classical
  let s : ℝ := ‖(euclidean.toMixed K) y‖
  have hsplit : ‖y‖ ^ 2 = ‖y.fst‖ ^ 2 + ‖y.snd‖ ^ 2 := euc_norm_sq K y
  have hs0 : 0 ≤ s := norm_nonneg _
  have hcoord_real (w : {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w}) :
      |(y.fst w : ℝ)| ≤ s := by
    dsimp [s]
    rw [NumberField.mixedEmbedding.norm_eq_sup'_normAtPlace]
    have h1 : NumberField.mixedEmbedding.normAtPlace w.1 (euclidean.toMixed K y) ≤
        Finset.univ.sup' Finset.univ_nonempty
          (fun w' : InfinitePlace K => NumberField.mixedEmbedding.normAtPlace w' (euclidean.toMixed K y)) :=
      Finset.le_sup' (s := Finset.univ)
        (f := fun w' : InfinitePlace K => NumberField.mixedEmbedding.normAtPlace w' (euclidean.toMixed K y))
        (Finset.mem_univ w.1)
    rw [NumberField.mixedEmbedding.normAtPlace_apply_of_isReal w.2] at h1
    have heq : (euclidean.toMixed K y).1 ⟨w.1, w.2⟩ = y.fst w := by
      simp [euclidean.toMixed, WithLp.linearEquiv]
    rwa [heq] at h1
  have hcoord_cplx (w : {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsComplex w}) :
      ‖(y.snd w : ℂ)‖ ≤ s := by
    dsimp [s]
    rw [NumberField.mixedEmbedding.norm_eq_sup'_normAtPlace]
    have h1 : NumberField.mixedEmbedding.normAtPlace w.1 (euclidean.toMixed K y) ≤
        Finset.univ.sup' Finset.univ_nonempty
          (fun w' : InfinitePlace K => NumberField.mixedEmbedding.normAtPlace w' (euclidean.toMixed K y)) :=
      Finset.le_sup' (s := Finset.univ)
        (f := fun w' : InfinitePlace K => NumberField.mixedEmbedding.normAtPlace w' (euclidean.toMixed K y))
        (Finset.mem_univ w.1)
    rw [NumberField.mixedEmbedding.normAtPlace_apply_of_isComplex w.2] at h1
    have heq : (euclidean.toMixed K y).2 ⟨w.1, w.2⟩ = y.snd w := by
      simp [euclidean.toMixed, WithLp.linearEquiv]
    rwa [heq] at h1
  have hfst : ‖y.fst‖ ^ 2 ≤ (Fintype.card {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w} : ℝ) * s ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq (y.fst)]
    calc
      (∑ w : {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w}, (y.fst w) ^ 2) ≤
          ∑ w : {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w}, s ^ 2 := by
        refine Finset.sum_le_sum ?_
        intro w hw
        have ha : |(y.fst w : ℝ)| ≤ s := hcoord_real w
        exact sq_le_sq.mpr (by simpa [abs_of_nonneg hs0] using ha)
      _ = (Fintype.card {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w} : ℝ) * s ^ 2 := by simp
  have hsnd : ‖y.snd‖ ^ 2 ≤ (Fintype.card {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsComplex w} : ℝ) * s ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq (y.snd)]
    calc
      (∑ w : {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsComplex w}, ‖(y.snd w)‖ ^ 2) ≤
          ∑ w : {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsComplex w}, s ^ 2 := by
        refine Finset.sum_le_sum ?_
        intro w hw
        have ha : ‖(y.snd w : ℂ)‖ ≤ s := hcoord_cplx w
        exact sq_le_sq.mpr (by simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hs0] using ha)
      _ = (Fintype.card {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsComplex w} : ℝ) * s ^ 2 := by simp
  have hcard :
      (Fintype.card {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w} : ℝ) +
        (Fintype.card {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsComplex w} : ℝ) ≤
      (Module.finrank ℚ K : ℝ) := by
    have hsum : InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K ≤ Module.finrank ℚ K := by
      have hmain := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
      omega
    have hrc : Fintype.card {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w} =
        InfinitePlace.nrRealPlaces K := rfl
    have hcc : Fintype.card {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsComplex w} =
        InfinitePlace.nrComplexPlaces K := rfl
    rw [hrc, hcc]
    exact_mod_cast hsum
  have hmain : ‖y‖ ^ 2 ≤ (Module.finrank ℚ K : ℝ) * s ^ 2 := by
    calc
      ‖y‖ ^ 2 = ‖y.fst‖ ^ 2 + ‖y.snd‖ ^ 2 := hsplit
      _ ≤ (Fintype.card {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w} : ℝ) * s ^ 2 +
          (Fintype.card {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsComplex w} : ℝ) * s ^ 2 := by
        nlinarith [hfst, hsnd, sq_nonneg s]
      _ = ((Fintype.card {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w} : ℝ) +
          (Fintype.card {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsComplex w} : ℝ)) * s ^ 2 := by ring
      _ ≤ (Module.finrank ℚ K : ℝ) * s ^ 2 := by
        exact mul_le_mul_of_nonneg_right hcard (sq_nonneg s)
  have hsqrt : (Real.sqrt (Module.finrank ℚ K : ℝ) * s) ^ 2 =
      (Module.finrank ℚ K : ℝ) * s ^ 2 := by
    calc
      (Real.sqrt (Module.finrank ℚ K : ℝ) * s) ^ 2 = Real.sqrt (Module.finrank ℚ K : ℝ) ^ 2 * s ^ 2 := by ring
      _ = (Module.finrank ℚ K : ℝ) * s ^ 2 := by
        rw [Real.sq_sqrt (by positivity : 0 ≤ (Module.finrank ℚ K : ℝ))]
  have htarget : ‖y‖ ^ 2 ≤ (Real.sqrt (Module.finrank ℚ K : ℝ) * s) ^ 2 := by
    rw [hsqrt]
    exact hmain
  have h := sq_le_sq.mp htarget
  simpa [deg, abs_of_nonneg (norm_nonneg _), abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hs0)] using h

/-- The image of a small sup element is a small Euclidean element. -/
lemma eucOf_norm_le (K : Type*) [Field K] [NumberField K] (x : 𝓞 K)
    (hx : ‖mixedEmbedding K ((x : K) : K)‖ ≤ 16 * NumberField.rootDiscr K) :
    ‖((eucOf K x : EucLattice K) : euclidean.mixedSpace K)‖ ≤
      Real.sqrt (deg K) * (16 * NumberField.rootDiscr K) := by
  classical
  have h := euc_norm_le_sqrt_mul_sup K (y := ((eucOf K x : EucLattice K) : euclidean.mixedSpace K))
  calc
    ‖((eucOf K x : EucLattice K) : euclidean.mixedSpace K)‖
        ≤ Real.sqrt (deg K) *
            ‖(euclidean.toMixed K) ((eucOf K x : EucLattice K) : euclidean.mixedSpace K)‖ := h
    _ ≤ Real.sqrt (deg K) * (16 * NumberField.rootDiscr K) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        calc
          ‖(euclidean.toMixed K) ((eucOf K x : EucLattice K) : euclidean.mixedSpace K)‖
              = ‖mixedEmbedding K ((x : K) : K)‖ := by
                rw [eucOf_coe]
                rw [(euclidean.toMixed K).apply_symm_apply]
          _ ≤ 16 * NumberField.rootDiscr K := hx

/-- Independent small products in the Euclidean lattice (realisers for the bounded-basis
step). -/
lemma exists_realizers_euc (K : Type*) [Field K] [NumberField K] :
    ∃ v : Fin (deg K) → EucLattice K,
      LinearIndependent ℝ (fun j : Fin (deg K) => (v j : euclidean.mixedSpace K)) ∧
      ∀ j : Fin (deg K),
        ‖(v j : euclidean.mixedSpace K)‖ ≤
          Real.sqrt (deg K) * (16 * NumberField.rootDiscr K) ^ 2 := by
  classical
  obtain ⟨x, hxLI, hxbd⟩ := exists_basis_products K
  let v : Fin (deg K) → EucLattice K := fun j => eucOf K (x j)
  have hpt (j : Fin (deg K)) :
      (euclidean.toMixed K) ((v j : EucLattice K) : euclidean.mixedSpace K) =
        NumberField.mixedEmbedding K ((x j : 𝓞 K) : K) := by
    dsimp [v]
    simp [eucOf]
  refine ⟨v, ?_, ?_⟩
  · -- linear independence over ℝ in the Euclidean space
    have hLIimg : LinearIndependent ℝ
        (fun j : Fin (deg K) => NumberField.mixedEmbedding K ((x j : 𝓞 K) : K)) :=
      Commons.NumberTheory.NumberField.mixedEmbedding_basis_values_linearIndependent
        (K := K) (x := fun j : Fin (deg K) => x j) hxLI
    let f : euclidean.mixedSpace K →ₗ[ℝ] mixedSpace K := (euclidean.toMixed K).toLinearMap
    have hfker : LinearMap.ker f = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      simpa [f] using (euclidean.toMixed K).injective
    have hcomp : LinearIndependent ℝ
        (fun j : Fin (deg K) => f ((v j : EucLattice K) : euclidean.mixedSpace K)) := by
      have hfv : (fun j : Fin (deg K) => f ((v j : EucLattice K) : euclidean.mixedSpace K)) =
          (fun j : Fin (deg K) => NumberField.mixedEmbedding K ((x j : 𝓞 K) : K)) := by
        funext j
        dsimp [v, f]
        simp [eucOf]
      rwa [hfv]
    exact (LinearMap.linearIndependent_iff
      (v := fun j : Fin (deg K) => ((v j : EucLattice K) : euclidean.mixedSpace K))
      f hfker).mp hcomp
  · intro j
    have hj := euc_norm_le_sqrt_mul_sup K
      (y := ((v j : EucLattice K) : euclidean.mixedSpace K))
    calc
      ‖((v j : EucLattice K) : euclidean.mixedSpace K)‖
          ≤ Real.sqrt (deg K) *
              ‖(euclidean.toMixed K) ((v j : EucLattice K) : euclidean.mixedSpace K)‖ := hj
      _ = Real.sqrt (deg K) * ‖NumberField.mixedEmbedding K ((x j : 𝓞 K) : K)‖ := by
            rw [hpt j]
      _ ≤ Real.sqrt (deg K) * (16 * NumberField.rootDiscr K) ^ 2 := by
            exact mul_le_mul_of_nonneg_left (hxbd j) (Real.sqrt_nonneg _)

/-- A `ℤ`-basis of the Euclidean lattice with controlled norm. -/
lemma exists_euc_basis_bounded (K : Type*) [Field K] [NumberField K] :
    ∃ b : Module.Basis (Fin (deg K)) ℤ (EucLattice K),
      ∀ i : Fin (deg K),
        ‖((b i : EucLattice K) : euclidean.mixedSpace K)‖ ≤
          (2 * (deg K : ℝ) + 1) * (Real.sqrt (deg K) * (16 * NumberField.rootDiscr K) ^ 2) := by
  classical
  obtain ⟨v, hvLI, hvR⟩ := exists_realizers_euc K
  let R : ℝ := Real.sqrt (deg K) * (16 * NumberField.rootDiscr K) ^ 2
  have hR0 : 0 ≤ R := by
    dsimp [R]
    positivity
  obtain ⟨b, hb⟩ := Commons.Lattice.Minkowski.bounded_basis_of_bounded_realizers_innerProductSpace
      (E := euclidean.mixedSpace K) (L := EucLattice K) (m := deg K)
      (finrank_EucLattice K) v hvLI R hR0 hvR
  refine ⟨b, ?_⟩
  intro i
  simpa [R] using hb i

/-- Every Euclidean lattice element is the image of a unique integral element. -/
lemma eucLattice_exists (K : Type*) [Field K] [NumberField K] (y : EucLattice K) :
    ∃ a : 𝓞 K, mixedEmbedding K (a : K) = euclidean.toMixed K (y : euclidean.mixedSpace K) := by
  classical
  have hyy : (y : euclidean.mixedSpace K) ∈ euclidean.integerLattice K := y.2
  change (y : euclidean.mixedSpace K) ∈
    ZLattice.comap ℝ (mixedEmbedding.integerLattice K) (euclidean.toMixed K).toLinearMap at hyy
  simp [ZLattice.comap, Submodule.mem_comap] at hyy
  exact hyy

/-- Map a Euclidean lattice element back to `𝓞 K`. -/
def ofEuc (K : Type*) [Field K] [NumberField K] (y : EucLattice K) : 𝓞 K :=
  Classical.choose (eucLattice_exists K y)

/-- The defining property of `ofEuc`. -/
lemma ofEuc_spec (K : Type*) [Field K] [NumberField K] (y : EucLattice K) :
    mixedEmbedding K ((ofEuc K y : 𝓞 K) : K) =
      euclidean.toMixed K (y : euclidean.mixedSpace K) :=
  Classical.choose_spec (eucLattice_exists K y)

@[simp] lemma ofEuc_eucOf (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) :
    ofEuc K (eucOf K a) = a := by
  classical
  -- mixed embedding is injective
  have h1 : mixedEmbedding K ((ofEuc K (eucOf K a) : 𝓞 K) : K) =
      mixedEmbedding K (a : K) := by
    rw [ofEuc_spec]
    simp [eucOf]
  exact Subtype.ext (NumberField.mixedEmbedding_injective K h1)

lemma eucOf_ofEuc (K : Type*) [Field K] [NumberField K] (y : EucLattice K) :
    eucOf K (ofEuc K y) = y := by
  classical
  apply Subtype.ext
  change (euclidean.toMixed K).symm
      (mixedEmbedding K ((ofEuc K y : 𝓞 K) : K)) = (y : euclidean.mixedSpace K)
  rw [ofEuc_spec]
  exact (euclidean.toMixed K).toLinearEquiv.symm_apply_apply (y : euclidean.mixedSpace K)

/-- The `ℤ`-linear equivalence between `𝓞 K` and the Euclidean lattice. -/
def eucLatticeEquiv (K : Type*) [Field K] [NumberField K] : 𝓞 K ≃ₗ[ℤ] EucLattice K where
  toFun := eucOf K
  invFun := ofEuc K
  left_inv := by intro a; exact ofEuc_eucOf K a
  right_inv := by intro y; exact eucOf_ofEuc K y
  map_add' := by
    intro a b
    apply Subtype.ext
    apply (euclidean.toMixed K).injective
    simp [eucOf, map_add]
  map_smul' := by
    intro z a
    apply Subtype.ext
    apply (euclidean.toMixed K).injective
    -- toMixed (z • y) = z • (toMixed y), and toMixed (toMixed.symm x) = x
    calc
      (euclidean.toMixed K) ((euclidean.toMixed K).symm (mixedEmbedding K (((z : ℤ) • a : 𝓞 K) : K)))
          = mixedEmbedding K (((z : ℤ) • a : 𝓞 K) : K) := by
            rw [(euclidean.toMixed K).apply_symm_apply]
      _ = (euclidean.toMixed K) (((z : ℤ) • eucOf K a : EucLattice K) : euclidean.mixedSpace K) := by
            -- reduce the scalar action on the lattice to a scalar action in the ambient space
            rw [show (((z : ℤ) • eucOf K a : EucLattice K) : euclidean.mixedSpace K) =
                (z : ℤ) • ((eucOf K a : EucLattice K) : euclidean.mixedSpace K) by simp]
            rw [map_zsmul]
            rw [eucOf_coe]
            rw [(euclidean.toMixed K).apply_symm_apply]
            simp

/-- A ℤ-basis of the Euclidean lattice is (via the bijection) a ℤ-basis of `𝓞 K`. -/
lemma basis_of_euc_basis (K : Type*) [Field K] [NumberField K]
    (b : Module.Basis (Fin (deg K)) ℤ (EucLattice K)) :
    ∃ B : Module.Basis (Fin (deg K)) ℤ (𝓞 K),
      ∀ i : Fin (deg K), ((B i : 𝓞 K) : K) = (ofEuc K (b i) : K) := by
  classical
  let e : 𝓞 K ≃ₗ[ℤ] EucLattice K := eucLatticeEquiv K
  let B : Module.Basis (Fin (deg K)) ℤ (𝓞 K) := b.map e.symm
  refine ⟨B, ?_⟩
  intro i
  -- B i = e.symm (b i) = ofEuc (b i) (the inverse function of e is ofEuc)
  have hsymm : e.symm (b i) = ofEuc K (b i) := by
    rfl
  calc
    ((B i : 𝓞 K) : K) = ((e.symm (b i) : 𝓞 K) : K) := by rfl
    _ = (ofEuc K (b i) : K) := by rw [hsymm]

/-- house of a basis element is bounded by its sup norm. -/
lemma house_basis_le (K : Type*) [Field K] [NumberField K]
    (B : Module.Basis (Fin (deg K)) ℤ (𝓞 K)) {R : ℝ} (hR0 : 0 ≤ R)
    (hB : ∀ i : Fin (deg K),
      ‖(euclidean.toMixed K) ((eucOf K (B i)) : euclidean.mixedSpace K)‖ ≤ R) :
    ∀ i : Fin (deg K), NumberField.house ((B i : 𝓞 K) : K) ≤ R := by
  intro i
  have h1 : NumberField.house ((B i : 𝓞 K) : K) ≤
      ‖mixedEmbedding K ((B i : 𝓞 K) : K)‖ := house_le_sup_mixed K ((B i : 𝓞 K) : K)
  have h2 : mixedEmbedding K ((B i : 𝓞 K) : K) =
      euclidean.toMixed K ((eucOf K (B i)) : euclidean.mixedSpace K) := by
    simp [eucOf]
  calc
    NumberField.house ((B i : 𝓞 K) : K) ≤ ‖mixedEmbedding K ((B i : 𝓞 K) : K)‖ := h1
    _ = ‖(euclidean.toMixed K) ((eucOf K (B i)) : euclidean.mixedSpace K)‖ := by rw [h2]
    _ ≤ R := hB i

/-- The final numerical inequality: for a degree `≥ 2` field of root discriminant `Δ ≥ 1`,
the bound produced by the bounded-basis argument is dominated by `n ^ 2000 * Δ ^ 2000`. -/
lemma basis_house_final_ineq (n Δ : ℝ) (hn : 2 ≤ n) (hΔ : 1 ≤ Δ) :
    (2 * n + 1) * (Real.sqrt n * (16 * Δ) ^ 2) ≤
      n ^ (2000 : ℝ) * Δ ^ (2000 : ℝ) := by
  have hn0 : 0 < n := by linarith
  have hn1 : 1 ≤ n := by linarith
  have hΔ0 : 0 ≤ Δ := le_trans zero_le_one hΔ
  have h2nΔ : (2 : ℝ) ≤ n * Δ := by
    have := mul_le_mul hn hΔ (by norm_num : (0:ℝ) ≤ 1) (by linarith : (0:ℝ) ≤ n)
    simpa using this
  have hfac : (2 * n + 1) * Real.sqrt n ≤ 3 * n * n := by
    have h1 : (2 * n + 1) ≤ 3 * n := by linarith
    have h2 : Real.sqrt n ≤ n := by
      have hsq : (Real.sqrt n) ^ 2 ≤ n ^ 2 := by
        rw [Real.sq_sqrt (le_of_lt hn0)]
        nlinarith
      have h := sq_le_sq.mp hsq
      simpa [abs_of_nonneg (Real.sqrt_nonneg n), abs_of_nonneg (le_of_lt hn0)] using h
    have h3 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg n
    nlinarith [h1, h2, h3, hn1]
  have hstep1 : (2 * n + 1) * (Real.sqrt n * (16 * Δ) ^ 2) ≤ 768 * (n * Δ) ^ 2 := by
    have h16 : (16 * Δ) ^ 2 = 256 * Δ ^ 2 := by ring
    rw [h16]
    have hR : 0 ≤ 256 * Δ ^ 2 := by positivity
    have hre : (2 * n + 1) * (Real.sqrt n * (256 * Δ ^ 2)) =
        ((2 * n + 1) * Real.sqrt n) * (256 * Δ ^ 2) := by ring
    rw [hre]
    calc ((2 * n + 1) * Real.sqrt n) * (256 * Δ ^ 2)
        ≤ (3 * n * n) * (256 * Δ ^ 2) := mul_le_mul_of_nonneg_right hfac hR
      _ = 768 * (n * Δ) ^ 2 := by ring
  have h768 : (768 : ℝ) ≤ (n * Δ) ^ (1998 : ℝ) := by
    have h1 : (768 : ℝ) ≤ (2 : ℝ) ^ (10 : ℝ) := by
      rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    have h2 : (2 : ℝ) ^ (10 : ℝ) ≤ (2 : ℝ) ^ (1998 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have h3 : (2 : ℝ) ^ (1998 : ℝ) ≤ (n * Δ) ^ (1998 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) h2nΔ (by norm_num)
    exact h1.trans (h2.trans h3)
  have hmain : 768 * (n * Δ) ^ 2 ≤ (n * Δ) ^ (2000 : ℝ) := by
    have hpos : 0 < n * Δ := by positivity
    have he : (n * Δ) ^ (2000 : ℝ) = (n * Δ) ^ (2 : ℝ) * (n * Δ) ^ (1998 : ℝ) := by
      rw [← Real.rpow_add hpos]; norm_num
    rw [he, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h2 : (0 : ℝ) ≤ (n * Δ) ^ 2 := by positivity
    nlinarith [h768, h2]
  calc (2 * n + 1) * (Real.sqrt n * (16 * Δ) ^ 2) ≤ 768 * (n * Δ) ^ 2 := hstep1
    _ ≤ (n * Δ) ^ (2000 : ℝ) := hmain
    _ = n ^ (2000 : ℝ) * Δ ^ (2000 : ℝ) := by rw [Real.mul_rpow hn0.le hΔ0]

end SmallBasis

/-- The main theorem: a uniform bound on a basis of the ring of integers. -/
theorem exists_uniform_ringOfIntegers_basis_house_le :
    ∃ c : ℝ, 0 < c ∧
      ∀ (K : Type*) [Field K] [NumberField K],
        ∃ b : Module.Basis (Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K)) ℤ
            (NumberField.RingOfIntegers K),
          ∀ i, NumberField.house ((b i : NumberField.RingOfIntegers K) : K) ≤
            (Module.finrank ℚ K : ℝ) ^ c * NumberField.rootDiscr K ^ c := by
  classical
  refine ⟨(2000 : ℝ), by norm_num, ?_⟩
  intro K hF hN
  letI : Field K := hF
  letI : NumberField K := hN
  by_cases hdeg1 : Module.finrank ℚ K = 1
  · -- degree one: the ring of integers is `ℤ`, so `{±1}` is a basis of house `1`
    obtain ⟨b, hb⟩ :=
      Commons.NumberTheory.NumberField.basis_house_le_one_of_finrank_eq_one K hdeg1
    refine ⟨b, ?_⟩
    intro i
    have hpow : ((Module.finrank ℚ K : ℝ)) ^ (2000 : ℝ) = 1 := by
      rw [hdeg1]
      simp
    have hΔc : (1 : ℝ) ≤ NumberField.rootDiscr K ^ (2000 : ℝ) := by
      have := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) (one_le_rootDiscr K)
        (by norm_num : (0 : ℝ) ≤ 2000)
      simpa using this
    calc NumberField.house ((b i : NumberField.RingOfIntegers K) : K) ≤ 1 := hb i
      _ ≤ (Module.finrank ℚ K : ℝ) ^ (2000 : ℝ) * NumberField.rootDiscr K ^ (2000 : ℝ) := by
          rw [hpow, one_mul]; exact hΔc
  · have hdeg2 : 2 ≤ SmallBasis.deg K := by
      have h1 : 1 ≤ SmallBasis.deg K := by
        dsimp [SmallBasis.deg]
        exact Nat.succ_le_of_lt (Module.finrank_pos (R := ℚ) (M := K))
      have hne : SmallBasis.deg K ≠ 1 := fun h => hdeg1 h
      omega
    obtain ⟨b0, hb0⟩ := SmallBasis.exists_euc_basis_bounded K
    obtain ⟨B, hB⟩ := SmallBasis.basis_of_euc_basis K b0
    set R : ℝ := (2 * (SmallBasis.deg K : ℝ) + 1) *
        (Real.sqrt (SmallBasis.deg K) * (16 * NumberField.rootDiscr K) ^ 2) with hRdef
    have hR0 : 0 ≤ R := by
      rw [hRdef]; positivity
    have hBval : ∀ i : Fin (SmallBasis.deg K), B i = SmallBasis.ofEuc K (b0 i) :=
      fun i => Subtype.ext (hB i)
    have hEuc : ∀ i : Fin (SmallBasis.deg K), SmallBasis.eucOf K (B i) = b0 i := by
      intro i
      rw [hBval i, SmallBasis.eucOf_ofEuc]
    have hBsup : ∀ i : Fin (SmallBasis.deg K),
        ‖(euclidean.toMixed K) ((SmallBasis.eucOf K (B i)) : euclidean.mixedSpace K)‖ ≤ R := by
      intro i
      rw [hEuc i]
      calc ‖(euclidean.toMixed K) ((b0 i : SmallBasis.EucLattice K) : euclidean.mixedSpace K)‖
          ≤ ‖((b0 i : SmallBasis.EucLattice K) : euclidean.mixedSpace K)‖ :=
            SmallBasis.sup_norm_le_euc_norm K _
        _ ≤ R := by rw [hRdef]; exact hb0 i
    have hhouse : ∀ i : Fin (SmallBasis.deg K),
        NumberField.house ((B i : 𝓞 K) : K) ≤ R :=
      SmallBasis.house_basis_le K B hR0 hBsup
    have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = SmallBasis.deg K := by
      dsimp [SmallBasis.deg]
      rw [← Module.finrank_eq_card_chooseBasisIndex ℤ (𝓞 K)]
      exact NumberField.RingOfIntegers.rank K
    let eqv : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Fin (SmallBasis.deg K) :=
      Fintype.equivFinOfCardEq hcard
    refine ⟨B.reindex eqv.symm, ?_⟩
    intro i
    have hval : (B.reindex eqv.symm) i = B (eqv i) := by
      rw [Module.Basis.reindex_apply]
      simp
    rw [hval]
    refine (hhouse (eqv i)).trans ?_
    have hn2R : (2 : ℝ) ≤ (SmallBasis.deg K : ℝ) := by exact_mod_cast hdeg2
    have hfin := SmallBasis.basis_house_final_ineq (SmallBasis.deg K : ℝ) (NumberField.rootDiscr K)
      hn2R (one_le_rootDiscr K)
    simpa [SmallBasis.deg, hRdef] using hfin

end Commons.NumberTheory.NumberField
