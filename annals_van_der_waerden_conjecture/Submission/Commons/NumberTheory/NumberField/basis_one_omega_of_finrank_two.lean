import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.NumberTheory.Niven
import Mathlib.NumberTheory.NumberField.Basic

/-!
# The ring of integers of a quadratic number field has `{1, ω}` as a `ℤ`-basis

For a number field `K` with `Module.finrank ℚ K = 2`, the ring of integers `NumberField.RingOfIntegers K`
has a `ℤ`-basis whose first element is `1`, i.e. `NumberField.RingOfIntegers K = ℤ ⊕ ℤω` for a suitable `ω`.

The mathematical content is the statement that `(1 : NumberField.RingOfIntegers K)` is a *primitive* element of
the free `ℤ`-module `NumberField.RingOfIntegers K`: writing `1 = a • e 0 + b • e 1` in an arbitrary `ℤ`-basis `e`
of `NumberField.RingOfIntegers K`, the two integers `a, b` are coprime (Bézout), and then the pair
`(e 0, e 1)` may be replaced by the unimodular pair `(1, -t • e 0 + s • e 1)`,
where `a * s + b * t = 1`.
-/

namespace Commons.NumberTheory.NumberField

/-- **Extending a primitive vector of a rank-two free module to a basis.**

Let `e` be a basis of an `R`-module `M` indexed by `Fin 2` and let `x : M` have
coordinates `a = (e.repr x) 0`, `b = (e.repr x) 1`.  If `a` and `b` admit a Bézout
relation `a * s + b * t = 1`, then `x` is the first element of some `R`-basis of `M`.
Concretely, `{x, -t • e 0 + s • e 1}` is such a basis. -/
theorem exists_basis_zero_eq {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (e : Module.Basis (Fin 2) R M) (x : M) (s t : R)
    (hst : (e.repr x) 0 * s + (e.repr x) 1 * t = 1) :
    ∃ b : Module.Basis (Fin 2) R M, b 0 = x := by
  classical
  set a : R := (e.repr x) 0 with ha
  set b : R := (e.repr x) 1 with hb
  have hst' : a * s + b * t = 1 := by rw [ha, hb]; exact hst
  have hx : x = a • e 0 + b • e 1 := by
    have h := Module.Basis.sum_repr e x
    rw [Fin.sum_univ_two] at h
    rw [← ha, ← hb] at h
    exact h.symm
  let v1 : M := -t • e 0 + s • e 1
  let w : Fin 2 → M := ![x, v1]
  have hc0 : (e.repr v1) 0 = -t := by
    simp only [v1]
    simp [Module.Basis.repr_self, Finsupp.single_eq_same, Finsupp.single_eq_of_ne]
  have hc1 : (e.repr v1) 1 = s := by
    simp only [v1]
    simp [Module.Basis.repr_self, Finsupp.single_eq_same, Finsupp.single_eq_of_ne]
  have hli : LinearIndependent R w := by
    have hw : w = ![x, v1] := rfl
    rw [hw, LinearIndependent.pair_iff]
    intro c0 c1 h
    have hcc0 : c0 * a + c1 * (-t) = 0 := by
      have hco := congrArg (e.coord 0) h
      simp only [map_add, map_smul, map_zero, Module.Basis.coord_apply, smul_eq_mul] at hco
      rw [hc0, ← ha] at hco
      exact hco
    have hcc1 : c0 * b + c1 * s = 0 := by
      have hco := congrArg (e.coord 1) h
      simp only [map_add, map_smul, map_zero, Module.Basis.coord_apply, smul_eq_mul] at hco
      rw [hc1, ← hb] at hco
      exact hco
    refine ⟨?_, ?_⟩
    · have h0 : c0 * a = c1 * t := by linear_combination hcc0
      have h1 : c0 * b = -(c1 * s) := by linear_combination hcc1
      calc c0 = c0 * (a * s + b * t) := by rw [hst', mul_one]
        _ = (c0 * a) * s + (c0 * b) * t := by ring
        _ = (c1 * t) * s + (-(c1 * s)) * t := by rw [h0, h1]
        _ = 0 := by ring
    · have h0s : c1 * t = c0 * a := by linear_combination -hcc0
      have h1s : c1 * s = -(c0 * b) := by linear_combination hcc1
      calc c1 = c1 * (a * s + b * t) := by rw [hst', mul_one]
        _ = a * (c1 * s) + b * (c1 * t) := by ring
        _ = a * (-(c0 * b)) + b * (c0 * a) := by rw [h1s, h0s]
        _ = 0 := by ring
  have hmem0 : e 0 ∈ Submodule.span R (Set.range w) := by
    have he0 : s • w 0 - b • w 1 = e 0 := by
      rw [show w 0 = x from rfl, show w 1 = -t • e 0 + s • e 1 from rfl, hx]
      have : s • (a • e 0 + b • e 1) - b • (-t • e 0 + s • e 1)
          = (a * s + b * t) • e 0 := by module
      rw [this, hst', one_smul]
    rw [← he0]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ s (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ b (Submodule.subset_span ⟨1, rfl⟩))
  have hmem1 : e 1 ∈ Submodule.span R (Set.range w) := by
    have he1 : t • w 0 + a • w 1 = e 1 := by
      rw [show w 0 = x from rfl, show w 1 = -t • e 0 + s • e 1 from rfl, hx]
      have : t • (a • e 0 + b • e 1) + a • (-t • e 0 + s • e 1)
          = (a * s + b * t) • e 1 := by module
      rw [this, hst', one_smul]
    rw [← he1]
    exact Submodule.add_mem _ (Submodule.smul_mem _ t (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ a (Submodule.subset_span ⟨1, rfl⟩))
  have hsp : ⊤ ≤ Submodule.span R (Set.range w) := by
    rw [← Module.Basis.span_eq e]
    apply Submodule.span_le.mpr
    rw [Set.range_subset_iff]
    exact Fin.forall_fin_two.mpr ⟨hmem0, hmem1⟩
  refine ⟨Module.Basis.mk hli hsp, ?_⟩
  rw [Module.Basis.mk_apply]
  rfl

/-- **`1` is the first element of a `ℤ`-basis of the ring of integers of a quadratic
number field.**

If `Module.finrank ℚ K = 2`, then `NumberField.RingOfIntegers K` is a free `ℤ`-module of rank two and `(1 : NumberField.RingOfIntegers K)`
is a primitive element of it: for any `ℤ`-basis `e`, the coordinates `a, b` of `1` are
coprime, because `(d : ℤ) • y = 1` with `d = gcd a b` exhibits `y` as a rational
algebraic integer, forcing `d = 1`.  Bézout's identity and `exists_basis_zero_eq` then
produce the required basis `{1, ω}`. -/
theorem basis_one_omega_of_finrank_two {K : Type*} [Field K] [NumberField K]
    (h : Module.finrank ℚ K = 2) :
    ∃ b : Module.Basis (Fin 2) ℤ (NumberField.RingOfIntegers K), b 0 = 1 := by
  have hrank : Module.finrank ℤ (NumberField.RingOfIntegers K) = 2 := by
    rw [NumberField.RingOfIntegers.rank]; exact h
  let e : Module.Basis (Fin 2) ℤ (NumberField.RingOfIntegers K) := Module.finBasisOfFinrankEq ℤ (NumberField.RingOfIntegers K) hrank
  let a : ℤ := (e.repr (1 : NumberField.RingOfIntegers K)) 0
  let b : ℤ := (e.repr (1 : NumberField.RingOfIntegers K)) 1
  have h1 : a • e 0 + b • e 1 = (1 : NumberField.RingOfIntegers K) := by
    have hh := Module.Basis.sum_repr e (1 : NumberField.RingOfIntegers K)
    rw [Fin.sum_univ_two] at hh
    exact hh
  set d : ℕ := a.gcd b with hddef
  obtain ⟨a', ha'⟩ := Int.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ := Int.gcd_dvd_right a b
  rw [← hddef] at ha' hb'
  let y : NumberField.RingOfIntegers K := a' • e 0 + b' • e 1
  have hy : (d : ℤ) • y = (1 : NumberField.RingOfIntegers K) := by
    rw [smul_add, smul_smul, smul_smul]
    rw [ha'.symm, hb'.symm]
    exact h1
  have hInt : IsIntegral ℤ (y : K) :=
    (IsIntegralClosure.isIntegral_iff (R := ℤ)).mpr ⟨y, rfl⟩
  have hyK : (d : K) * (y : K) = 1 := by
    have hh := congrArg (algebraMap (NumberField.RingOfIntegers K) K) hy
    simp only [map_one] at hh
    simpa using hh
  have hd0nat : d ≠ 0 := by
    intro h0
    have hz : a = 0 ∧ b = 0 := Int.gcd_eq_zero_iff.mp h0
    have : (1 : NumberField.RingOfIntegers K) = 0 := by rw [← h1, hz.1, hz.2]; simp
    exact one_ne_zero this
  have hq : ∃ q : ℚ, (y : K) = (q : K) := by
    refine ⟨(d : ℚ)⁻¹, ?_⟩
    have hdy : (y : K) = (d : K)⁻¹ := eq_inv_of_mul_eq_one_right hyK
    rw [hdy, show (d : K) = ((d : ℚ) : K) from by push_cast; ring]
    rw [← Rat.cast_inv]
  obtain ⟨k, hk⟩ := (IsIntegral.exists_int_iff_exists_rat hInt).mp hq
  have hdk : (d : ℤ) * k = 1 := by
    have hh := hyK
    rw [show (y : K) = (k : K) from hk] at hh
    have h2 : (((d : ℤ) * k : ℤ) : K) = ((1 : ℤ) : K) := by
      push_cast
      exact hh
    exact Int.cast_injective h2
  have hd1 : d = 1 := by
    have hnat : d * k.natAbs = 1 := by
      have hh := congrArg Int.natAbs hdk
      simpa [Int.natAbs_mul, Int.natAbs_natCast] using hh
    exact Nat.dvd_one.mp ⟨k.natAbs, hnat.symm⟩
  have hgcdZ : ((a.gcd b : ℕ) : ℤ) = 1 := by
    rw [← hddef]
    exact_mod_cast hd1
  have hbez : a * Int.gcdA a b + b * Int.gcdB a b = 1 := by
    have hh := Int.gcd_eq_gcd_ab a b
    rw [hgcdZ] at hh
    exact hh.symm
  refine exists_basis_zero_eq e (1 : NumberField.RingOfIntegers K) (Int.gcdA a b) (Int.gcdB a b) ?_
  exact hbez

end Commons.NumberTheory.NumberField