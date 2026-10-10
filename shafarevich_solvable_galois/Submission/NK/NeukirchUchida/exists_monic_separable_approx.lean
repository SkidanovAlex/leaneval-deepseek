import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.RingTheory.Polynomial.Resultant.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Approximation of a monic separable polynomial by one with coefficients in a dense subfield

Let `K` be a field, `L` a normed field and `Algebra K L` an algebra structure whose structure
map `algebraMap K L` has dense range.  Then any monic separable polynomial `f` over `L` can be
approximated coefficient-wise (within any prescribed `ε > 0`) by a monic separable polynomial
`g` over `K` of the *same* degree.

The proof is the standard "genericity of separability" argument:

* Writing `f = X ^ n + ∑_{i < n} f_i X ^ i` with `n = f.natDegree`, the coefficient family
  `a ↦ coeffPoly n a = X ^ n + ∑_{i < n} a_i X ^ i` is a monic polynomial of degree `n`
  for every `a : Fin n → L`.
* The map `a ↦ resultant (coeffPoly n a) (coeffPoly n a).derivative n (n - 1)` is a polynomial
  function of `a` (concretely, it is `MvPolynomial.eval a` of a fixed multivariate polynomial),
  hence continuous; by `MvPolynomial.continuous_eval`.
* Since `f` is separable and monic, that resultant does not vanish at the coefficient vector of
  `f`, so it stays non-zero in a whole neighbourhood of that vector.
* Finally, for a monic `p` of degree `n`, the non-vanishing of
  `resultant p p' n (n - 1)` is equivalent to `p.Separable`.
* Density of `range (algebraMap K L)` then supplies a coefficient vector with entries in the
  image of `K` lying in that neighbourhood (and within `ε` of the coefficients of `f`), and the
  corresponding polynomial over `K` is the required `g`.

The hypothesis `hsmall` (existence of an element whose image has norm in `(0,1)`) is not needed
for the argument; the statement is proved for arbitrary dense `algebraMap K L`.
-/

namespace NK.NeukirchUchida

namespace MonicSepApprox

open Polynomial Filter

/-- The monic polynomial `X ^ n + ∑_{i < n} a i * X ^ i` over `R`, parametrised by its
coefficients below the top degree. -/
noncomputable def coeffPoly (n : ℕ) {R : Type*} [CommSemiring R] (a : Fin n → R) : Polynomial R :=
  X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ)

/-- The "universal" version of `coeffPoly`, over the multivariate polynomial ring whose
variables are the coefficients. -/
noncomputable def genPoly (n : ℕ) (R : Type*) [CommSemiring R] :
    Polynomial (MvPolynomial (Fin n) R) :=
  X ^ n + ∑ i : Fin n, C (MvPolynomial.X i) * X ^ (i : ℕ)

/-- `coeffPoly` commutes with coefficient extension. -/
lemma coeffPoly_map {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) {n : ℕ}
    (a : Fin n → R) : (coeffPoly n a).map φ = coeffPoly n fun i => φ (a i) := by
  simp [coeffPoly, Polynomial.map_add, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X]

/-- `coeffPoly` is obtained from the universal polynomial by specialising the coefficients. -/
lemma coeffPoly_genPoly {R : Type*} [CommSemiring R] {n : ℕ} (a : Fin n → R) :
    coeffPoly n a = (genPoly n R).map (MvPolynomial.eval a) := by
  simp [coeffPoly, genPoly, Polynomial.map_add, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]

/-- The coefficients of `coeffPoly` below the top degree. -/
lemma coeffPoly_coeff_lt {R : Type*} [CommSemiring R] {n : ℕ} (a : Fin n → R) {k : ℕ}
    (hk : k < n) : (coeffPoly n a).coeff k = a ⟨k, hk⟩ := by
  rw [coeffPoly, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff]
  have hsum : (∑ i : Fin n, (C (a i) * X ^ (i : ℕ)).coeff k) = a ⟨k, hk⟩ := by
    rw [Finset.sum_eq_single ⟨k, hk⟩]
    · simp
    · intro b _ hb
      rw [Polynomial.coeff_C_mul_X_pow, if_neg]
      intro h
      exact hb (Fin.ext h.symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsum, if_neg (by omega : ¬ k = n), zero_add]

/-- The top coefficient of `coeffPoly`. -/
lemma coeffPoly_coeff_self {R : Type*} [CommSemiring R] {n : ℕ} (a : Fin n → R) :
    (coeffPoly n a).coeff n = 1 := by
  rw [coeffPoly, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff]
  have hsum : (∑ i : Fin n, (C (a i) * X ^ (i : ℕ)).coeff n) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [Polynomial.coeff_C_mul_X_pow, if_neg]
    intro h
    have := i.isLt; omega
  rw [hsum, if_pos rfl, add_zero]

/-- The coefficients of `coeffPoly` above the top degree. -/
lemma coeffPoly_coeff_gt {R : Type*} [CommSemiring R] {n : ℕ} (a : Fin n → R) {k : ℕ}
    (hk : n < k) : (coeffPoly n a).coeff k = 0 := by
  rw [coeffPoly, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff]
  have hsum : (∑ i : Fin n, (C (a i) * X ^ (i : ℕ)).coeff k) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [Polynomial.coeff_C_mul_X_pow, if_neg]
    intro h
    have := i.isLt; omega
  rw [hsum, if_neg (by omega : ¬ k = n), add_zero]

lemma coeffPoly_natDegree {R : Type*} [CommSemiring R] [Nontrivial R] {n : ℕ} (a : Fin n → R) :
    (coeffPoly n a).natDegree = n := by
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_
    (by rw [coeffPoly_coeff_self]; exact one_ne_zero)
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  exact coeffPoly_coeff_gt a hN

lemma coeffPoly_monic {R : Type*} [CommSemiring R] [Nontrivial R] {n : ℕ} (a : Fin n → R) :
    (coeffPoly n a).Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, coeffPoly_natDegree]
  exact coeffPoly_coeff_self a

/-- A monic polynomial of degree `n` is recovered from its coefficients by `coeffPoly`. -/
lemma coeffPoly_of_monic {R : Type*} [CommSemiring R] {n : ℕ} {f : Polynomial R} (hf : f.Monic)
    (hn : f.natDegree = n) : coeffPoly n (fun i => f.coeff i) = f := by
  apply Polynomial.ext
  intro k
  rcases lt_trichotomy k n with hk | hk | hk
  · rw [coeffPoly_coeff_lt _ hk]
  · rw [hk, coeffPoly_coeff_self, ← hn, hf.coeff_natDegree]
  · rw [coeffPoly_coeff_gt _ hk, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

/-- For a monic `p`, the resultant of `p` and `p'` with the (explicit) size parameters
`(p.natDegree, p.natDegree - 1)` agrees with the standard resultant (which uses
`p.derivative.natDegree` as second size). -/
lemma resultant_deriv_eq_default {L : Type*} [Field L] {p : Polynomial L} (hp : p.Monic) :
    p.resultant p.derivative p.natDegree (p.natDegree - 1) = p.resultant p.derivative := by
  rcases eq_or_ne p.natDegree 0 with h0 | h0
  · rw [Polynomial.eq_one_of_monic_natDegree_zero hp h0]
    simp
  · rw [show p.natDegree - 1 = p.derivative.natDegree +
        (p.natDegree - 1 - p.derivative.natDegree) by
      have := Polynomial.natDegree_derivative_le p; omega]
    rw [Polynomial.resultant_add_right_deg p p.derivative p.natDegree p.derivative.natDegree
        (p.natDegree - 1 - p.derivative.natDegree) (le_refl _), hp.coeff_natDegree, one_pow, one_mul]

/-- For a monic polynomial over a field, separability is equivalent to the non-vanishing of the
resultant of the polynomial with its derivative, with the explicit size parameters
`(p.natDegree, p.natDegree - 1)`. -/
lemma resultant_deriv_ne_zero_iff_separable {L : Type*} [Field L] {p : Polynomial L}
    (hp : p.Monic) :
    p.resultant p.derivative p.natDegree (p.natDegree - 1) ≠ 0 ↔ p.Separable := by
  rw [resultant_deriv_eq_default hp, Polynomial.separable_def]
  exact (isUnit_iff_ne_zero (a := p.resultant p.derivative)).symm.trans
    (Polynomial.isUnit_resultant_iff_isCoprime (f := p) (g := p.derivative) hp)

/-- The `(n, n - 1)`-resultant of the parametrised monic polynomial `coeffPoly n a`. -/
noncomputable def Rs (L : Type*) [CommRing L] (n : ℕ) (a : Fin n → L) : L :=
  (coeffPoly n a).resultant (coeffPoly n a).derivative n (n - 1)

/-- `Rs` is the evaluation of a fixed multivariate polynomial in the coefficients, hence it is a
polynomial function of `a`. -/
lemma Rs_eq_eval (L : Type*) [CommRing L] (n : ℕ) :
    Rs L n = fun a : Fin n → L =>
      MvPolynomial.eval a (Polynomial.resultant (genPoly n L) (genPoly n L).derivative n (n - 1)) := by
  funext a
  simp only [Rs]
  rw [coeffPoly_genPoly]
  rw [Polynomial.derivative_map, Polynomial.resultant_map_map]

lemma continuous_Rs (L : Type*) [NormedField L] (n : ℕ) : Continuous (Rs L n) := by
  rw [Rs_eq_eval]
  exact MvPolynomial.continuous_eval _

/-- If a continuous function on `Fin n → L` does not vanish at `a₀`, then it does not vanish on a
coordinate-wise neighbourhood of `a₀`. -/
lemma exists_delta_coord {n : ℕ} {L : Type*} [NormedField L]
    {F : (Fin n → L) → L} (hF : Continuous F) {a₀ : Fin n → L} (hne : F a₀ ≠ 0) :
    ∃ δ > 0, ∀ a : Fin n → L, (∀ i, ‖a i - a₀ i‖ < δ) → F a ≠ 0 := by
  have hU : {a : Fin n → L | F a ≠ 0} ∈ nhds a₀ :=
    hF.continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds hne)
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨δ / 2, half_pos hδpos, fun a ha => ?_⟩
  apply hδ
  rw [Metric.mem_ball, dist_eq_norm]
  have hle : ‖a - a₀‖ ≤ δ / 2 := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    simpa using (ha i).le
  linarith

end MonicSepApprox

open MonicSepApprox

theorem exists_monic_separable_approx {K L : Type*} [Field K] [NormedField L] [Algebra K L]
    (hd : DenseRange (algebraMap K L))
    (hsmall : ∃ c : K, 0 < ‖algebraMap K L c‖ ∧ ‖algebraMap K L c‖ < 1)
    {f : Polynomial L} (hf : f.Monic) (hsep : f.Separable) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Polynomial K, g.Monic ∧ g.Separable ∧ f.natDegree = g.natDegree ∧
      ∀ n : ℕ, ‖(g.map (algebraMap K L)).coeff n - f.coeff n‖ < ε := by
  by_cases hdeg : f.natDegree = 0
  · -- `f` is the constant polynomial `1`
    refine ⟨1, Polynomial.monic_one, ?_, ?_, ?_⟩
    · rw [Polynomial.separable_def, Polynomial.derivative_one]
      exact isCoprime_one_left
    · rw [hdeg, Polynomial.natDegree_one]
    · intro m
      have hf1 : f = 1 := Polynomial.eq_one_of_monic_natDegree_zero hf hdeg
      rw [hf1, Polynomial.map_one]
      simp [hε]
  · set n := f.natDegree with hn_def
    have hn1 : 1 ≤ n := by omega
    -- the coefficient vector of `f` is a zero of nothing: the resultant is non-zero there
    have hpoly : coeffPoly n (fun i => f.coeff i) = f := coeffPoly_of_monic hf hn_def.symm
    have hRs_ne : Rs L n (fun i => f.coeff i) ≠ 0 := by
      rw [Rs, hpoly, hn_def, resultant_deriv_eq_default hf]
      exact Polynomial.resultant_ne_zero f f.derivative hsep
    -- hence a whole coordinate-neighbourhood of it stays in the separable locus
    obtain ⟨δ, hδpos, hδ⟩ := exists_delta_coord (continuous_Rs L n) hRs_ne
    have hmin : 0 < min (δ / 2) ε := lt_min (half_pos hδpos) hε
    -- pick coefficients in the image of `K`, close to those of `f` and inside the neighbourhood
    choose k hk using fun i : Fin n => hd.exists_dist_lt (f.coeff i) hmin
    set a' : Fin n → L := fun i => algebraMap K L (k i) with ha'_def
    have hcl : ∀ i : Fin n, ‖a' i - f.coeff i‖ < min (δ / 2) ε := fun i => by
      have h := hk i
      simp only [ha'_def] at h ⊢
      rw [dist_comm, dist_eq_norm] at h
      exact h
    have ha'_ne : Rs L n a' ≠ 0 := hδ a'
      (fun i => lt_trans (lt_of_lt_of_le (hcl i) (min_le_left _ _)) (half_lt_self hδpos))
    have hmap : (coeffPoly n k).map (algebraMap K L) = coeffPoly n a' := by
      simp only [ha'_def]
      exact coeffPoly_map (algebraMap K L) k
    refine ⟨coeffPoly n k, coeffPoly_monic k, ?_, ?_, ?_⟩
    · -- separability of the approximating polynomial, reflected along `algebraMap K L`
      have hres : (coeffPoly n k).resultant (coeffPoly n k).derivative n (n - 1) ≠ 0 := by
        intro h0
        apply ha'_ne
        rw [Rs, ← hmap]
        rw [Polynomial.derivative_map, Polynomial.resultant_map_map, h0, map_zero]
      rw [← resultant_deriv_ne_zero_iff_separable (coeffPoly_monic k), coeffPoly_natDegree]
      exact hres
    · exact (coeffPoly_natDegree k).symm
    · -- coefficient-wise closeness
      intro m
      rw [hmap]
      rcases lt_trichotomy m n with hm | hm | hm
      · rw [coeffPoly_coeff_lt _ hm]
        have h := hcl ⟨m, hm⟩
        simp only [ha'_def] at h
        exact lt_of_lt_of_le h (min_le_right _ _)
      · rw [hm, coeffPoly_coeff_self]
        have hfn : f.coeff n = 1 := by rw [hn_def]; exact hf.coeff_natDegree
        rw [hfn, sub_self, norm_zero]
        exact hε
      · rw [coeffPoly_coeff_gt _ hm, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), sub_zero,
          norm_zero]
        exact hε

end NK.NeukirchUchida
