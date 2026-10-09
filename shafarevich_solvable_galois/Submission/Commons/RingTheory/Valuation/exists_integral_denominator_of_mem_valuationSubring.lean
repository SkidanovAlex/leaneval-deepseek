import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.LocalSubring
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Commons.RingTheory.Valuation

open ValuationSubring

/-- If `W.comap (algebraMap F L) = O` then the valuations `O.valuation` and `W.valuation`
are compatible along `algebraMap F L`. -/
private lemma hasExtension_of_comap_eq {F L : Type*} [Field F] [Field L] [Algebra F L]
    (O : ValuationSubring F) (W : ValuationSubring L) (hW : W.comap (algebraMap F L) = O) :
    O.valuation.HasExtension W.valuation := by
  refine Valuation.HasExtension.ofComapInteger ?_
  rw [ValuationSubring.integer_valuation W, ValuationSubring.integer_valuation O, ← hW]
  rfl

theorem exists_integral_denominator_of_mem_valuationSubring {F L : Type*} [Field F] [Field L]
    [Algebra F L] [FiniteDimensional F L] (O : ValuationSubring F) (W : ValuationSubring L)
    (hW : W.comap (algebraMap F L) = O) {x : L} (hx : x ∈ W) :
    ∃ b : L, IsIntegral (Subring.map (algebraMap F L) O.toSubring) b ∧
      W.valuation b = 1 ∧ IsIntegral (Subring.map (algebraMap F L) O.toSubring) (b * x) := by
  classical
  haveI hExt : O.valuation.HasExtension W.valuation := hasExtension_of_comap_eq O W hW
  set A : Subring L := Subring.map (algebraMap F L) O.toSubring with hA
  have hAW : A ≤ W.toSubring := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Subring.mem_map.mp hy
    have hzO : z ∈ O := (ValuationSubring.mem_toSubring O z).mp hz
    rw [ValuationSubring.mem_toSubring]
    exact ValuationSubring.mem_comap.mp (by rw [hW]; exact hzO)
  -- integrality criterion via the intersection of the valuation subrings containing `A`
  have key_int : ∀ y : L, (∀ V : ValuationSubring L, A ≤ V.toSubring → y ∈ V) → IsIntegral A y := by
    intro y hy
    rw [← mem_integralClosure_iff, ← Subalgebra.mem_toSubring]
    have hii : (integralClosure A L).toSubring
        = ⨅ V : {V : ValuationSubring L // A ≤ V.toSubring}, V.1.toSubring := by
      have h := iInf_valuationSubring_superset (K := L) (s := (A : Set L))
      rw [Subring.closure_eq] at h
      exact h.symm
    rw [hii, Subring.mem_iInf]
    intro V
    exact hy V.1 V.2
  -- main construction
  have hxalg : IsIntegral F x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  set f : Polynomial F := minpoly F x with hfdef
  have hfm : f.Monic := minpoly.monic hxalg
  have hfne : f ≠ 0 := hfm.ne_zero
  have haeval : Polynomial.aeval x f = 0 := by rw [hfdef]; exact minpoly.aeval F x
  set n : ℕ := f.natDegree with hndef
  set φ : ℕ → O.ValueGroup := fun i => O.valuation (f.coeff i) with hφdef
  have hsupp : f.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, Polynomial.support_eq_empty]; exact hfne
  obtain ⟨iM, hiM_supp, hiM_max⟩ := Finset.exists_max_image f.support φ hsupp
  set M : O.ValueGroup := φ iM with hMdef
  set Smax : Finset ℕ := f.support.filter (fun i => φ i = M) with hSmaxdef
  have hSmax_ne : Smax.Nonempty := ⟨iM, Finset.mem_filter.mpr ⟨hiM_supp, rfl⟩⟩
  set s : ℕ := Smax.max' hSmax_ne with hsdef
  have hs_Smax : s ∈ Smax := Finset.max'_mem Smax hSmax_ne
  have hs_mem : s ∈ f.support := (Finset.mem_filter.mp hs_Smax).1
  have hs_phi : φ s = M := (Finset.mem_filter.mp hs_Smax).2
  have hs_le_n : s ≤ n := by
    rw [hndef]; exact Polynomial.le_natDegree_of_mem_supp _ hs_mem
  have hcs_ne : f.coeff s ≠ 0 := Polynomial.mem_support_iff.mp hs_mem
  have hφs_ne : φ s ≠ 0 := by
    rw [hφdef]; exact (Valuation.ne_zero_iff _).mpr hcs_ne
  have hφs_pos : (0 : O.ValueGroup) < φ s := lt_of_le_of_ne' zero_le hφs_ne
  have hmax : ∀ i ∈ f.support, φ i ≤ φ s := by
    intro i hi; rw [hs_phi]; exact hiM_max i hi
  have hmax_all : ∀ i, φ i ≤ φ s := by
    intro i
    by_cases hi : i ∈ f.support
    · exact hmax i hi
    · rw [Polynomial.mem_support_iff, not_not] at hi
      have : O.valuation (f.coeff i) = 0 := by rw [hi, Valuation.map_zero]
      show φ i ≤ φ s
      rw [hφdef]
      rw [show (fun i => O.valuation (f.coeff i)) i = 0 from this]
      exact zero_le
  have hstrict : ∀ i ∈ f.support, s < i → φ i < φ s := by
    intro i hi hsi
    refine lt_of_le_of_ne (hmax i hi) fun heq => ?_
    have : i ∈ Smax := Finset.mem_filter.mpr ⟨hi, by rw [heq, hs_phi]⟩
    exact absurd (Finset.le_max' Smax i this) (not_le.mpr hsi)
  -- coefficients `d`
  set d : ℕ → F := fun i => (f.coeff s)⁻¹ * f.coeff i with hddef
  set D : ℕ → L := fun i => algebraMap F L (d i) with hDdef
  have hd_s : d s = 1 := by
    show (f.coeff s)⁻¹ * f.coeff s = 1
    exact inv_mul_cancel₀ hcs_ne
  have hd_mem : ∀ i, d i ∈ O := by
    intro i
    rw [← ValuationSubring.valuation_le_one_iff]
    rw [hddef, Valuation.map_mul, Valuation.map_inv]
    have h : O.valuation (f.coeff i) ≤ O.valuation (f.coeff s) := hmax_all i
    calc (O.valuation (f.coeff s))⁻¹ * O.valuation (f.coeff i)
        ≤ (O.valuation (f.coeff s))⁻¹ * O.valuation (f.coeff s) := mul_le_mul_right h _
      _ = 1 := inv_mul_cancel₀ hφs_ne
  have hd_lt : ∀ i, s < i → O.valuation (d i) < 1 := by
    intro i hsi
    rw [hddef, Valuation.map_mul, Valuation.map_inv]
    have h : O.valuation (f.coeff i) < O.valuation (f.coeff s) := by
      by_cases hi : i ∈ f.support
      · exact hstrict i hi hsi
      · rw [Polynomial.mem_support_iff, not_not] at hi
        rw [hi, Valuation.map_zero]
        exact lt_of_lt_of_le hφs_pos (le_of_eq (hφdef ▸ rfl))
    calc (O.valuation (f.coeff s))⁻¹ * O.valuation (f.coeff i)
        < (O.valuation (f.coeff s))⁻¹ * O.valuation (f.coeff s) :=
          mul_lt_mul_of_pos_left h (inv_pos.mpr hφs_pos)
      _ = 1 := inv_mul_cancel₀ hφs_ne
  have hD_lt : ∀ i, s < i → W.valuation (D i) < 1 := by
    intro i hsi
    have h := hd_lt i hsi
    show W.valuation (algebraMap F L (d i)) < 1
    exact (Valuation.HasExtension.val_map_lt_one_iff (O.valuation) (W.valuation) (d i)).mpr h
  -- the total relation with the scaled coefficients
  have hsum_f : ∑ i ∈ Finset.range (n + 1), (algebraMap F L (f.coeff i)) * x ^ i = 0 := by
    have h1 : ∑ i ∈ Finset.range (n + 1), (algebraMap F L (f.coeff i)) * x ^ i
        = Polynomial.eval₂ (algebraMap F L) x f := by
      rw [Polynomial.eval₂_eq_sum_range, hndef]
    rw [h1, ← Polynomial.aeval_def]
    exact haeval
  have hscaled : ∀ i, D i = (algebraMap F L (f.coeff s))⁻¹ * (algebraMap F L (f.coeff i)) := by
    intro i
    show algebraMap F L ((f.coeff s)⁻¹ * f.coeff i) = _
    rw [map_mul, map_inv₀]
  have hsum : ∑ i ∈ Finset.range (n + 1), D i * x ^ i = 0 := by
    have h2 : ∑ i ∈ Finset.range (n + 1), D i * x ^ i
        = (algebraMap F L (f.coeff s))⁻¹ *
          ∑ i ∈ Finset.range (n + 1), (algebraMap F L (f.coeff i)) * x ^ i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hscaled i]; ring
    rw [h2, hsum_f, mul_zero]
  -- `a`
  set a : L := ∑ j ∈ Finset.range (n + 1 - s), D (s + j) * x ^ j with hadef
  have hsplit : ∑ i ∈ Finset.range (n + 1), D i * x ^ i
      = (∑ i ∈ Finset.range s, D i * x ^ i) + x ^ s * a := by
    have h := Finset.sum_range_add (fun i => D i * x ^ i) s (n + 1 - s)
    rw [Nat.add_sub_of_le (by omega)] at h
    rw [h, hadef, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [pow_add]; ring
  have hrel : x ^ s * a = - ∑ i ∈ Finset.range s, D i * x ^ i := by
    have h := hsplit
    rw [hsum] at h
    linear_combination -h
  -- value of `a` at `W`
  have hval : W.valuation a = 1 := by
    have hN : n + 1 - s = (n - s) + 1 := by omega
    have key : a = 1 + ∑ j ∈ Finset.range (n - s), D (s + (j + 1)) * x ^ (j + 1) := by
      rw [hadef, hN, Finset.sum_range_succ']
      rw [show D (s + 0) * x ^ (0 : ℕ) = 1 from by
        show algebraMap F L (d s) * x ^ (0 : ℕ) = 1
        rw [hd_s, map_one, pow_zero, mul_one]]
      ring
    rw [key]
    refine Valuation.map_one_add_of_lt _ ?_
    refine Valuation.map_sum_lt' _ zero_lt_one (fun j _ => ?_)
    rw [Valuation.map_mul, Valuation.map_pow]
    calc W.valuation (D (s + (j + 1))) * W.valuation x ^ (j + 1)
        ≤ W.valuation (D (s + (j + 1))) * 1 :=
          mul_le_mul_right (pow_le_one₀ (zero_le) ((ValuationSubring.valuation_le_one_iff W x).mpr hx)) _
      _ = W.valuation (D (s + (j + 1))) := mul_one _
      _ < 1 := hD_lt (s + (j + 1)) (by omega)
  -- hence `s ≥ 1`
  have hs_ge_one : 1 ≤ s := by
    by_contra hs
    rw [not_le, Nat.lt_one_iff] at hs
    have haz : a = 0 := by
      have h := hrel
      rw [hs, pow_zero, one_mul] at h
      rw [h]; simp
    rw [haz, Valuation.map_zero] at hval
    exact zero_ne_one hval
  -- integrality of `a` and `a*x` at every valuation subring containing `A`
  have hplace : ∀ V : ValuationSubring L, A ≤ V.toSubring → a ∈ V ∧ a * x ∈ V := by
    intro V hV
    have hDV : ∀ i, V.valuation (D i) ≤ 1 := by
      intro i
      exact (ValuationSubring.valuation_le_one_iff V (D i)).mpr
        (ValuationSubring.mem_toSubring V (D i) |>.mp <| hV <| Subring.mem_map.mpr
          ⟨d i, (ValuationSubring.mem_toSubring O (d i)).mpr (hd_mem i), rfl⟩)
    rcases lt_or_ge (1 : V.ValueGroup) (V.valuation x) with hvx | hvx
    · -- `1 < V.valuation x`
      have hsum_le : V.valuation (∑ i ∈ Finset.range s, D i * x ^ i) ≤ V.valuation x ^ (s - 1) := by
        refine Valuation.map_sum_le _ (fun i hi => ?_)
        rw [Finset.mem_range] at hi
        rw [Valuation.map_mul, Valuation.map_pow]
        calc V.valuation (D i) * V.valuation x ^ i
            ≤ 1 * V.valuation x ^ i := mul_le_mul_left (hDV i) _
          _ = V.valuation x ^ i := one_mul _
          _ ≤ V.valuation x ^ (s - 1) := pow_le_pow_right₀ hvx.le (by omega)
      have hrelV : V.valuation x ^ s * V.valuation a
          = V.valuation (∑ i ∈ Finset.range s, D i * x ^ i) := by
        have h := congrArg V.valuation hrel
        rw [Valuation.map_mul, Valuation.map_neg, Valuation.map_pow] at h
        simpa using h
      have hxpow : (0 : V.ValueGroup) < V.valuation x ^ s := pow_pos (lt_trans zero_lt_one hvx) s
      have hax_le : V.valuation (a * x) ≤ 1 := by
        refine (mul_le_mul_iff_of_pos_left hxpow).mp ?_
        rw [mul_one, Valuation.map_mul]
        calc V.valuation x ^ s * (V.valuation a * V.valuation x)
            = (V.valuation x ^ s * V.valuation a) * V.valuation x := (mul_assoc _ _ _).symm
          _ ≤ V.valuation x ^ (s - 1) * V.valuation x := by
              rw [hrelV]; exact mul_le_mul_left hsum_le _
          _ = V.valuation x ^ s := by rw [← pow_succ, Nat.sub_add_cancel hs_ge_one]
      have ha1 : V.valuation a ≤ 1 := by
        have h2 : V.valuation a * V.valuation x ≤ 1 := by
          rw [← Valuation.map_mul]; exact hax_le
        calc V.valuation a = V.valuation a * 1 := (mul_one _).symm
          _ ≤ V.valuation a * V.valuation x := mul_le_mul_right hvx.le _
          _ ≤ 1 := h2
      exact ⟨(ValuationSubring.valuation_le_one_iff V a).mp ha1,
             (ValuationSubring.valuation_le_one_iff V (a * x)).mp hax_le⟩
    · -- `V.valuation x ≤ 1`
      have ha1 : V.valuation a ≤ 1 := by
        rw [hadef]
        refine Valuation.map_sum_le _ (fun j _ => ?_)
        rw [Valuation.map_mul, Valuation.map_pow]
        calc V.valuation (D (s + j)) * V.valuation x ^ j
            ≤ V.valuation (D (s + j)) * 1 := mul_le_mul_right (pow_le_one₀ (zero_le) hvx) _
          _ = V.valuation (D (s + j)) := mul_one _
          _ ≤ 1 := hDV (s + j)
      have hax1 : V.valuation (a * x) ≤ 1 := by
        rw [Valuation.map_mul]
        calc V.valuation a * V.valuation x ≤ 1 * V.valuation x := mul_le_mul_left ha1 _
          _ ≤ 1 * 1 := mul_le_mul_right hvx _
          _ = 1 := one_mul 1
      exact ⟨(ValuationSubring.valuation_le_one_iff V a).mp ha1,
             (ValuationSubring.valuation_le_one_iff V (a * x)).mp hax1⟩
  refine ⟨a, key_int a (fun V hV => (hplace V hV).1), hval, ?_⟩
  exact key_int (a * x) (fun V hV => (hplace V hV).2)

end Commons.RingTheory.Valuation