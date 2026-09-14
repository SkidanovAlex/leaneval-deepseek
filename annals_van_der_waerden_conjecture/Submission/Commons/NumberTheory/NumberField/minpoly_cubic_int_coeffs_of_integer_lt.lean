import Mathlib
import Submission.Commons.NumberTheory.NumberField.nrComplexPlaces_eq_one_of_finrank_three_of_discr_neg

open Polynomial
open scoped ComplexConjugate
open IntermediateField

namespace Commons.NumberTheory.NumberField

theorem minpoly_cubic_int_coeffs_of_integer_lt {K : Type*} [Field K] [NumberField K]
    (hfin : Module.finrank ℚ K = 3) (hneg : NumberField.discr K < 0)
    {α : NumberField.RingOfIntegers K} (hα0 : α ≠ 0)
    (hreal : ∀ w : NumberField.InfinitePlace K, w.IsReal → (w α : ℝ) < 1)
    (hcomplex : ∀ w : NumberField.InfinitePlace K, ¬ w.IsReal → (w α : ℝ) < Real.sqrt 3) :
    ∃ a b c : ℤ,
      minpoly ℚ (α : K) = Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ) ∧
      |a| ≤ 4 ∧ |b| ≤ 6 ∧ (c = -2 ∨ c = -1 ∨ c = 1 ∨ c = 2) ∧
      ∃ r z : ℂ, r.im = 0 ∧ z.im ≠ 0 ∧
        Polynomial.aeval (r : ℂ) (Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
          Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ)) = 0 ∧
        Polynomial.aeval (z : ℂ) (Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
          Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ)) = 0 ∧
        ‖r‖ < 1 ∧ ‖z‖ < Real.sqrt 3 := by
  classical
  let x : K := (α : K)
  have hx0 : x ≠ 0 := by
    dsimp [x]
    exact NumberField.RingOfIntegers.coe_ne_zero_iff.mpr hα0
  have hintZ : IsIntegral ℤ x := by
    dsimp [x]
    exact NumberField.RingOfIntegers.isIntegral_coe α
  have hintQ : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  obtain ⟨wr, hwr⟩ : ∃ w : NumberField.InfinitePlace K, w.IsReal := by
    classical
    have hpos : 0 < NumberField.InfinitePlace.nrRealPlaces K := by
      exact NumberField.InfinitePlace.nrRealPlaces_pos_of_odd_finrank (by rw [hfin]; norm_num)
    have hcard : 0 < Fintype.card {w : NumberField.InfinitePlace K // w.IsReal} := by
      simpa [NumberField.InfinitePlace.nrRealPlaces] using hpos
    have hne : Nonempty {w : NumberField.InfinitePlace K // w.IsReal} := by
      exact Fintype.card_pos_iff.mp hcard
    obtain ⟨w, hw⟩ := hne
    exact ⟨w, hw⟩
  obtain ⟨wc, hwc⟩ : ∃ w : NumberField.InfinitePlace K, w.IsComplex := by
    classical
    have hnr : NumberField.InfinitePlace.nrComplexPlaces K = 1 := by
      exact Commons.NumberTheory.NumberField.nrComplexPlaces_eq_one_of_finrank_three_of_discr_neg hfin hneg
    have hcard : 0 < Fintype.card {w : NumberField.InfinitePlace K // w.IsComplex} := by
      change 0 < NumberField.InfinitePlace.nrComplexPlaces K
      rw [hnr]
      norm_num
    have hne : Nonempty {w : NumberField.InfinitePlace K // w.IsComplex} := by
      exact Fintype.card_pos_iff.mp hcard
    obtain ⟨w, hw⟩ := hne
    exact ⟨w, hw⟩
  let σ : K →+* ℂ := wr.embedding
  let τ : K →+* ℂ := wc.embedding
  let r : ℂ := σ x
  let z : ℂ := τ x
  let zc : ℂ := star z
  have hσreal : NumberField.ComplexEmbedding.IsReal σ := by
    dsimp [σ]
    exact NumberField.InfinitePlace.isReal_iff.mp hwr
  have hτ_notreal : ¬ NumberField.ComplexEmbedding.IsReal τ := by
    dsimp [τ]
    exact NumberField.InfinitePlace.isComplex_iff.mp hwc
  -- x is not rational, so minpoly has degree 3 and x generates K
  have hx_not_rat : x ∉ Set.range (algebraMap ℚ K) := by
    intro hxrat
    rcases hxrat with ⟨q, hq⟩
    have hqint : IsIntegral ℤ q := by
      refine (isIntegral_algebraMap_iff (algebraMap ℚ K).injective).mp ?_
      rw [hq]
      exact hintZ
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := ℤ) (K := ℚ) hqint
    have hn0 : n ≠ 0 := by
      intro hn0
      apply hx0
      rw [← hq, ← hn, hn0]
      simp
    have hw_abs_lt : |(n : ℝ)| < 1 := by
      have hlt := hreal wr hwr
      have hx_eq : x = algebraMap ℤ K n := by
        rw [← hq, ← hn]
        simp
      have hlt_x : (wr x : ℝ) < 1 := by simpa [x] using hlt
      rw [hx_eq] at hlt_x
      change (wr (algebraMap ℤ K n) : ℝ) < 1 at hlt_x
      have hnorm : (wr (algebraMap ℤ K n) : ℝ) = |(n : ℝ)| := by
        rw [← NumberField.InfinitePlace.norm_embedding_eq wr (algebraMap ℤ K n)]
        simp [Complex.norm_intCast]
      exact hnorm ▸ hlt_x
    have hlt_int : (|n| : ℤ) < 1 := by
      exact_mod_cast hw_abs_lt
    have hnat_lt : n.natAbs < 1 := by
      rw [Int.abs_eq_natAbs] at hlt_int
      exact_mod_cast hlt_int
    omega
  have hdegQ : (minpoly ℚ x).natDegree = 3 := by
    have hdvd : (minpoly ℚ x).natDegree ∣ 3 := by
      simpa [hfin] using minpoly.degree_dvd (K := ℚ) (L := K) (x := x) hintQ
    have h2le : 2 ≤ (minpoly ℚ x).natDegree := by
      exact (minpoly.two_le_natDegree_iff hintQ).2 hx_not_rat
    have hle3 : (minpoly ℚ x).natDegree ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases (minpoly ℚ x).natDegree
    · norm_num at hdvd
    · rfl
  have hgen_int : ℚ⟮x⟯ = ⊤ := by
    have hfin_adjoin : Module.finrank ℚ ℚ⟮x⟯ = 3 := by
      rw [IntermediateField.adjoin.finrank hintQ, hdegQ]
    exact IntermediateField.eq_of_le_of_finrank_eq (K := ℚ) (L := K) (F := ℚ⟮x⟯) (E := ⊤) le_top
      (by simpa [hfin, IntermediateField.finrank_top'] using hfin_adjoin)
  have hadjoin_alg : Algebra.adjoin ℚ ({x} : Set K) = ⊤ := by
    have hxalg : IsAlgebraic ℚ x := (Algebra.IsIntegral.isIntegral x).isAlgebraic
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hxalg]
    exact congrArg IntermediateField.toSubalgebra hgen_int
  -- root data
  have hr_im : r.im = 0 := by
    have hconj : (NumberField.ComplexEmbedding.conjugate σ) x = σ x := by
      simpa using (RingHom.congr_fun hσreal x)
    exact Complex.conj_eq_iff_im.mp (by
      simpa [r, σ, NumberField.ComplexEmbedding.conjugate_coe_eq] using hconj)
  have hz_im : z.im ≠ 0 := by
    intro hzim
    have hconj : star (τ x) = τ x := (Complex.conj_eq_iff_im).2 hzim
    have hτ_eq_alg : τ.toRatAlgHom = (NumberField.ComplexEmbedding.conjugate τ).toRatAlgHom := by
      apply AlgHom.ext_of_adjoin_eq_top hadjoin_alg
      intro y hy
      have hyx : y = x := by simpa using hy
      subst y
      simpa [τ, NumberField.ComplexEmbedding.conjugate_coe_eq] using hconj.symm
    have hτ_eq_ring : τ = NumberField.ComplexEmbedding.conjugate τ := by
      ext y
      have hy := congrArg (fun f : K →ₐ[ℚ] ℂ => f y) hτ_eq_alg
      simpa [τ] using hy
    apply hτ_notreal
    exact NumberField.ComplexEmbedding.isReal_iff.mpr hτ_eq_ring.symm
  have hz0 : z ≠ 0 := by
    dsimp [z, τ]
    simpa [z, τ] using (RingHom.injective (NumberField.InfinitePlace.embedding wc)).ne hx0
  have hr_norm : ‖r‖ < 1 := by
    have hlt := hreal wr hwr
    dsimp [r, σ]
    change ‖(NumberField.InfinitePlace.embedding wr) x‖ < 1
    rw [NumberField.InfinitePlace.norm_embedding_eq]
    exact hlt
  have hz_norm : ‖z‖ < Real.sqrt 3 := by
    have hwc_notreal_place : ¬ wc.IsReal := NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hwc
    have hlt := hcomplex wc hwc_notreal_place
    dsimp [z, τ]
    change ‖(NumberField.InfinitePlace.embedding wc) x‖ < Real.sqrt 3
    rw [NumberField.InfinitePlace.norm_embedding_eq]
    exact hlt
  -- integer coefficients
  let g : Polynomial ℤ := minpoly ℤ x
  let a : ℤ := g.coeff 2
  let b : ℤ := g.coeff 1
  let c : ℤ := g.coeff 0
  have hminmap : minpoly ℚ x = g.map (algebraMap ℤ ℚ) := by
    dsimp [g]
    exact minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hintZ
  have hmonicG : g.Monic := by
    dsimp [g]
    exact minpoly.monic hintZ
  have hdegG : g.natDegree = 3 := by
    rw [← (minpoly.monic hintZ).natDegree_map (algebraMap ℤ ℚ), ← hminmap]
    exact hdegQ
  have hpolyQ : minpoly ℚ x = Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ) := by
    have ha : g.coeff 2 = a := rfl
    have hb : g.coeff 1 = b := rfl
    have hc : g.coeff 0 = c := rfl
    have hg3 : g.coeff 3 = 1 := by
      rw [← hmonicG.coeff_natDegree, hdegG]
    have hgpoly : g.map (algebraMap ℤ ℚ) = Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ) := by
      ext n
      by_cases hn : n < 4
      · interval_cases n
        · rw [Polynomial.coeff_map, hc]
          have htarget : (Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
              Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ)).coeff 0 = (c : ℚ) := by
            simp only [Polynomial.coeff_add]
            rw [Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
            norm_num
          rw [htarget]
          norm_num
        · rw [Polynomial.coeff_map, hb]
          have htarget : (Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
              Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ)).coeff 1 = (b : ℚ) := by
            simp only [Polynomial.coeff_add]
            rw [Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
            norm_num
          rw [htarget]
          norm_num
        · rw [Polynomial.coeff_map, ha]
          have htarget : (Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
              Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ)).coeff 2 = (a : ℚ) := by
            simp only [Polynomial.coeff_add]
            rw [Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
            norm_num
          rw [htarget]
          norm_num
        · rw [Polynomial.coeff_map, hg3]
          have htarget : (Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
              Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ)).coeff 3 = 1 := by
            simp only [Polynomial.coeff_add]
            rw [Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
            norm_num
          rw [htarget]
          norm_num
      · have hgn : g.coeff n = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          rw [hdegG]
          omega
        have htarget : (Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
            Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ)).coeff n = 0 := by
          simp only [Polynomial.coeff_add]
          rw [Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
          simp [show n ≠ 3 by omega, show n ≠ 2 by omega, show n ≠ 1 by omega, show n ≠ 0 by omega]
        rw [Polynomial.coeff_map, hgn, htarget]
        norm_num
    exact hminmap.trans hgpoly
  -- complex polynomial and roots
  let fQ : Polynomial ℚ := minpoly ℚ x
  let fℂ : Polynomial ℂ := fQ.map (algebraMap ℚ ℂ)
  have hmonicC : fℂ.Monic := by
    dsimp [fℂ, fQ]
    exact (minpoly.monic hintQ).map (algebraMap ℚ ℂ)
  have hdegC : fℂ.natDegree = 3 := by
    dsimp [fℂ, fQ]
    rw [← hdegQ]
    exact (minpoly.monic hintQ).natDegree_map (algebraMap ℚ ℂ)
  have hsplit : fℂ.Splits := IsAlgClosed.splits fℂ
  have hcardroots : fℂ.roots.card = 3 := by
    exact hsplit.natDegree_eq_card_roots ▸ hdegC
  have hroot_aeval_σ : Polynomial.aeval r fQ = 0 := by
    dsimp [fQ, r, σ]
    simpa using (minpoly.aeval_algHom ℚ wr.embedding.toRatAlgHom x :
      Polynomial.aeval (wr.embedding.toRatAlgHom x) (minpoly ℚ x) = 0)
  have hroot_aeval_τ : Polynomial.aeval z fQ = 0 := by
    dsimp [fQ, z, τ]
    simpa using (minpoly.aeval_algHom ℚ wc.embedding.toRatAlgHom x :
      Polynomial.aeval (wc.embedding.toRatAlgHom x) (minpoly ℚ x) = 0)
  have hroot_aeval_τc : Polynomial.aeval zc fQ = 0 := by
    dsimp [fQ, zc, z, τ]
    simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using
      (minpoly.aeval_algHom ℚ (NumberField.ComplexEmbedding.conjugate wc.embedding).toRatAlgHom x :
        Polynomial.aeval ((NumberField.ComplexEmbedding.conjugate wc.embedding).toRatAlgHom x) (minpoly ℚ x) = 0)
  have hr_mem : r ∈ fℂ.roots := by
    have hroot : Polynomial.eval r fℂ = 0 := by
      dsimp [fℂ, fQ]
      rw [Polynomial.eval_map_algebraMap]
      exact hroot_aeval_σ
    rw [Polynomial.mem_roots]
    · exact hroot
    · dsimp [fℂ, fQ]
      exact (minpoly.monic hintQ).map (algebraMap ℚ ℂ) |>.ne_zero
  have hz_mem : z ∈ fℂ.roots := by
    have hroot : Polynomial.eval z fℂ = 0 := by
      dsimp [fℂ, fQ]
      rw [Polynomial.eval_map_algebraMap]
      exact hroot_aeval_τ
    rw [Polynomial.mem_roots]
    · exact hroot
    · dsimp [fℂ, fQ]
      exact (minpoly.monic hintQ).map (algebraMap ℚ ℂ) |>.ne_zero
  have hzc_mem : zc ∈ fℂ.roots := by
    have hroot : Polynomial.eval zc fℂ = 0 := by
      dsimp [fℂ, fQ]
      rw [Polynomial.eval_map_algebraMap]
      exact hroot_aeval_τc
    rw [Polynomial.mem_roots]
    · exact hroot
    · dsimp [fℂ, fQ]
      exact (minpoly.monic hintQ).map (algebraMap ℚ ℂ) |>.ne_zero
  have hroots : fℂ.roots = ({r, z, zc} : Multiset ℂ) := by
    have hz_ne_zc : z ≠ zc := by
      intro h
      apply hz_im
      exact Complex.conj_eq_iff_im.mp (by simpa [zc] using h.symm)
    have hr_ne_z : r ≠ z := by
      intro h
      have : r.im = z.im := by rw [h]
      rw [hr_im] at this
      exact hz_im this.symm
    have hr_ne_zc : r ≠ zc := by
      intro h
      have hzc_im : zc.im = 0 := by rw [← h, hr_im]
      have hz_im0 : z.im = 0 := by
        have : zc.im = - z.im := by simp [zc]
        linarith
      exact hz_im hz_im0
    rcases Multiset.exists_cons_of_mem hr_mem with ⟨t, ht⟩
    have hz' : z ∈ t := by
      rw [ht] at hz_mem
      simpa [hr_ne_z.symm] using hz_mem
    rcases Multiset.exists_cons_of_mem hz' with ⟨u, hu⟩
    have hzc' : zc ∈ u := by
      rw [ht, hu] at hzc_mem
      simp only [Multiset.mem_cons] at hzc_mem
      rcases hzc_mem with h | h | h
      · exact False.elim (hr_ne_zc h.symm)
      · exact False.elim (hz_ne_zc h.symm)
      · exact h
    have hu_card : u.card = 1 := by
      have hroots_card : (r ::ₘ z ::ₘ u).card = 3 := by
        simpa [ht, hu] using hcardroots
      simp at hroots_card
      omega
    rcases Multiset.card_eq_one.mp hu_card with ⟨a, ha⟩
    have ha_val : a = zc := by
      rw [ha] at hzc'
      simp only [Multiset.mem_singleton] at hzc'
      exact hzc'.symm
    rw [ht, hu, ha, ha_val]
    rfl
  have hprod : fℂ = (({r, z, zc} : Multiset ℂ).map (fun t => Polynomial.X - Polynomial.C t)).prod := by
    rw [hsplit.eq_prod_roots_of_monic hmonicC, hroots]
  have hprod3 : (({r, z, zc} : Multiset ℂ).map (fun t => Polynomial.X - Polynomial.C t)).prod =
      (Polynomial.X - Polynomial.C r) * (Polynomial.X - Polynomial.C z) * (Polynomial.X - Polynomial.C zc) := by
    simp [Multiset.map_cons, Multiset.prod_cons, mul_assoc]
  have hcubic : fℂ = (Polynomial.X - Polynomial.C r) * (Polynomial.X - Polynomial.C z) * (Polynomial.X - Polynomial.C zc) :=
    hprod.trans hprod3
  have hcoeff2_roots : fℂ.coeff 2 = -(r + z + zc) := by
    rw [hcubic, Cubic.prod_X_sub_C_eq, Cubic.coeff_eq_b]
  have hcoeff1_roots : fℂ.coeff 1 = r * z + r * zc + z * zc := by
    rw [hcubic, Cubic.prod_X_sub_C_eq, Cubic.coeff_eq_c]
  have hcoeff0_roots : fℂ.coeff 0 = -(r * z * zc) := by
    rw [hcubic, Cubic.prod_X_sub_C_eq, Cubic.coeff_eq_d]
  -- coefficients as integers
  have hcoeff2Q : fQ.coeff 2 = (a : ℚ) := by
    dsimp [fQ]
    rw [hminmap, Polynomial.coeff_map]
    rfl
  have hcoeff1Q : fQ.coeff 1 = (b : ℚ) := by
    dsimp [fQ]
    rw [hminmap, Polynomial.coeff_map]
    rfl
  have hcoeff0Q : fQ.coeff 0 = (c : ℚ) := by
    dsimp [fQ]
    rw [hminmap, Polynomial.coeff_map]
    rfl
  have hcoeff2C : fℂ.coeff 2 = ((fQ.coeff 2 : ℚ) : ℂ) := by
    dsimp [fℂ]
    rw [Polynomial.coeff_map]
    rfl
  have hcoeff1C : fℂ.coeff 1 = ((fQ.coeff 1 : ℚ) : ℂ) := by
    dsimp [fℂ]
    rw [Polynomial.coeff_map]
    rfl
  have hcoeff0C : fℂ.coeff 0 = ((fQ.coeff 0 : ℚ) : ℂ) := by
    dsimp [fℂ]
    rw [Polynomial.coeff_map]
    rfl
  have ha_comp : ((a : ℚ) : ℂ) = -(r + z + zc) := by
    rw [← hcoeff2Q, ← hcoeff2C, hcoeff2_roots]
  have hb_comp : ((b : ℚ) : ℂ) = r * z + r * zc + z * zc := by
    rw [← hcoeff1Q, ← hcoeff1C, hcoeff1_roots]
  have hc_comp : ((c : ℚ) : ℂ) = -(r * z * zc) := by
    rw [← hcoeff0Q, ← hcoeff0C, hcoeff0_roots]
  -- norm inequalities for roots
  have hsqrt_lt_two : Real.sqrt 3 < 2 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hsum_a_lt : ‖r + z + zc‖ < 5 := by
    have hzc_norm : ‖zc‖ = ‖z‖ := by simp [zc]
    have h1 : ‖r + z + zc‖ ≤ ‖r + z‖ + ‖zc‖ := norm_add_le _ _
    have h2 : ‖r + z‖ ≤ ‖r‖ + ‖z‖ := norm_add_le _ _
    nlinarith
  have hprod_b_lt : ‖r * z + r * zc + z * zc‖ < 7 := by
    have hzc_norm : ‖zc‖ = ‖z‖ := by simp [zc]
    have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hz_nn : 0 ≤ ‖z‖ := norm_nonneg _
    have hprod1 : ‖r‖ * ‖z‖ < Real.sqrt 3 := by
      have h1 : ‖r‖ * ‖z‖ < 1 * ‖z‖ := by
        simpa [mul_comm] using (mul_lt_mul_iff_left₀ hz_pos).2 hr_norm
      have h2 : 1 * ‖z‖ < Real.sqrt 3 := by simpa using hz_norm
      linarith
    have hzsq : ‖z‖ * ‖z‖ < 3 := by
      have hpow : ‖z‖ ^ 2 < (Real.sqrt 3) ^ 2 := pow_lt_pow_left₀ hz_norm hz_nn (by norm_num : (2 : ℕ) ≠ 0)
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] at hpow
      simpa [pow_two] using hpow
    have h1 : ‖r * z + r * zc + z * zc‖ ≤ ‖r * z + r * zc‖ + ‖z * zc‖ := norm_add_le _ _
    have h2 : ‖r * z + r * zc‖ ≤ ‖r * z‖ + ‖r * zc‖ := norm_add_le _ _
    have hm1 : ‖r * z‖ = ‖r‖ * ‖z‖ := norm_mul _ _
    have hm2 : ‖r * zc‖ = ‖r‖ * ‖zc‖ := norm_mul _ _
    have hm3 : ‖z * zc‖ = ‖z‖ * ‖zc‖ := norm_mul _ _
    have hb_le : ‖r * z + r * zc + z * zc‖ ≤ ‖r‖ * ‖z‖ + ‖r‖ * ‖z‖ + ‖z‖ * ‖z‖ := by
      nlinarith [h1, h2, hm1, hm2, hm3, hzc_norm]
    nlinarith
  have hprod_c_lt : ‖r * z * zc‖ < 3 := by
    have hzc_norm : ‖zc‖ = ‖z‖ := by simp [zc]
    have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hz_nn : 0 ≤ ‖z‖ := norm_nonneg _
    have hzsq_pos : 0 < ‖z‖ * ‖z‖ := mul_pos hz_pos hz_pos
    have hzsq : ‖z‖ * ‖z‖ < 3 := by
      have hpow : ‖z‖ ^ 2 < (Real.sqrt 3) ^ 2 := pow_lt_pow_left₀ hz_norm hz_nn (by norm_num : (2 : ℕ) ≠ 0)
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] at hpow
      simpa [pow_two] using hpow
    have hnorm : ‖r * z * zc‖ = ‖r‖ * (‖z‖ * ‖z‖) := by
      rw [norm_mul, norm_mul, hzc_norm]
      ring
    have hlt : ‖r‖ * (‖z‖ * ‖z‖) < 1 * 3 := by
      exact mul_lt_mul hr_norm hzsq.le hzsq_pos (by norm_num)
    rw [hnorm]
    simpa using hlt
  have ha_abs_real : |(a : ℝ)| < 5 := by
    have hnorm_eq : ‖((a : ℚ) : ℂ)‖ = |(a : ℝ)| := by norm_num
    rw [← hnorm_eq]
    rw [ha_comp]
    change ‖-(r + z + zc)‖ < 5
    rw [norm_neg]
    exact hsum_a_lt
  have hb_abs_real : |(b : ℝ)| < 7 := by
    have hnorm_eq : ‖((b : ℚ) : ℂ)‖ = |(b : ℝ)| := by norm_num
    rw [← hnorm_eq]
    rw [hb_comp]
    exact hprod_b_lt
  have hc_abs_real : |(c : ℝ)| < 3 := by
    have hnorm_eq : ‖((c : ℚ) : ℂ)‖ = |(c : ℝ)| := by norm_num
    rw [← hnorm_eq]
    rw [hc_comp]
    change ‖-(r * z * zc)‖ < 3
    rw [norm_neg]
    exact hprod_c_lt
  have ha_le : |a| ≤ 4 := by
    have hlt_int : (|a| : ℤ) < 5 := by exact_mod_cast ha_abs_real
    omega
  have hb_le : |b| ≤ 6 := by
    have hlt_int : (|b| : ℤ) < 7 := by exact_mod_cast hb_abs_real
    omega
  have hc0 : c ≠ 0 := by
    intro hc0
    have hf0 : fQ.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hintQ hx0
    apply hf0
    rw [hcoeff0Q, hc0]
    norm_num
  have hc_cases : c = -2 ∨ c = -1 ∨ c = 1 ∨ c = 2 := by
    have hc_lt : (c : ℝ) < 3 := lt_of_le_of_lt (le_abs_self _) hc_abs_real
    have hc_gt : - (c : ℝ) < 3 := lt_of_le_of_lt (neg_le_abs _) hc_abs_real
    have hc_le : c ≤ 2 := by
      have : (c : ℤ) < 3 := by exact_mod_cast hc_lt
      omega
    have hc_ge : -2 ≤ c := by
      have : - (c : ℤ) < 3 := by exact_mod_cast hc_gt
      omega
    omega
  -- roots of displayed polynomial
  have hroot_r_disp : Polynomial.aeval (r : ℂ) (Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ)) = 0 := by
    rw [← hpolyQ]
    exact hroot_aeval_σ
  have hroot_z_disp : Polynomial.aeval (z : ℂ) (Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ)) = 0 := by
    rw [← hpolyQ]
    exact hroot_aeval_τ
  refine ⟨a, b, c, hpolyQ, ha_le, hb_le, hc_cases, ?_⟩
  refine ⟨r, z, hr_im, hz_im, hroot_r_disp, hroot_z_disp, hr_norm, hz_norm⟩

end Commons.NumberTheory.NumberField
