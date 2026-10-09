import Mathlib
import Submission.Commons.RingTheory.Henselian.exists_mul_of_residue_map_eq_mul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Henselian

open Polynomial

theorem coeff_mem_of_irreducible_of_henselian_alt {K : Type*} [Field K] (V : ValuationSubring K)
    [HenselianLocalRing V] {f : Polynomial K} (hf : f.Monic) (hirr : Irreducible f)
    (h0 : f.coeff 0 ∈ V) : ∀ i, f.coeff i ∈ V := by
  by_contra hcon
  push Not at hcon
  obtain ⟨j, hj⟩ := hcon
  set v := V.valuation with hv
  have hjval : 1 < v (f.coeff j) := by
    rw [← not_le]
    intro hle
    exact hj ((ValuationSubring.valuation_le_one_iff V (f.coeff j)).mp hle)
  set n := f.natDegree with hn
  have hjle : j ≤ n := by
    by_contra hle
    push Not at hle
    have hz : f.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hz, map_zero] at hjval
    exact absurd hjval (not_lt.mpr zero_le_one)
  obtain ⟨i₀, hi₀mem, hi₀max⟩ :=
    Finset.exists_max_image (Finset.range (n+1)) (fun i => v (f.coeff i)) ⟨0, by simp⟩
  set M := v (f.coeff i₀) with hM
  have hMgt : 1 < M := lt_of_lt_of_le hjval (hi₀max j (Finset.mem_range.mpr (by omega)))
  have hMpos : 0 < M := lt_trans zero_lt_one hMgt
  have hMne : M ≠ 0 := ne_of_gt hMpos
  have hleM : ∀ i, v (f.coeff i) ≤ M := by
    intro i
    by_cases hi : i ≤ n
    · exact hi₀max i (Finset.mem_range.mpr (by omega))
    · push Not at hi
      have hz : f.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hz, map_zero]
      exact le_of_lt hMpos
  -- I and t
  set I := (Finset.range (n+1)).filter (fun i => v (f.coeff i) = M) with hI
  have hIne : I.Nonempty := ⟨i₀, by rw [hI]; exact Finset.mem_filter.mpr ⟨hi₀mem, hM.symm⟩⟩
  set t := I.max' hIne with ht
  have htI : t ∈ I := Finset.max'_mem I hIne
  have htmin : ∀ i ∈ I, i ≤ t := fun i hi => Finset.le_max' I i hi
  have hvt : v (f.coeff t) = M := (Finset.mem_filter.mp htI).2
  have htle : t ≤ n := by
    have := (Finset.mem_filter.mp htI).1
    simp only [Finset.mem_range] at this
    omega
  have htne0 : t ≠ 0 := by
    intro h0t
    have : 0 ∈ I := by rw [h0t] at htI; exact htI
    have hv0 : v (f.coeff 0) = M := (Finset.mem_filter.mp this).2
    have hle : v (f.coeff 0) ≤ 1 := (ValuationSubring.valuation_le_one_iff V _).mpr h0
    rw [hv0] at hle
    exact absurd hle (not_le.mpr hMgt)
  have htltn : t < n := by
    refine lt_of_le_of_ne htle ?_
    intro htn
    have : n ∈ I := by rw [← htn]; exact htI
    have hvn : v (f.coeff n) = M := (Finset.mem_filter.mp this).2
    have hnc : f.coeff n = 1 := by rw [hn]; exact hf.coeff_natDegree
    rw [hnc, map_one] at hvn
    exact absurd hvn (ne_of_lt hMgt)
  have htne : f.coeff t ≠ 0 := by
    intro h; rw [h, map_zero] at hvt; exact hMne hvt.symm
  -- define D and P
  set D := (f.coeff t)⁻¹ with hD
  have hstep : ∀ i, v (D * f.coeff i) = M⁻¹ * v (f.coeff i) := by
    intro i
    rw [map_mul, hD, map_inv₀, hvt]
  have hcoeffmem : ∀ i, D * f.coeff i ∈ V := by
    intro i
    rw [← ValuationSubring.valuation_le_one_iff V]
    rw [hstep i]
    rw [inv_mul_le_iff₀ hMpos, mul_one]
    exact hleM i
  obtain ⟨P, hPcoeff⟩ : ∃ P : Polynomial V, ∀ i, ((P.coeff i : V) : K) = D * f.coeff i := by
    classical
    let gfun : ℕ → V := fun i => ⟨D * f.coeff i, hcoeffmem i⟩
    have hout : ∀ a, gfun a ≠ 0 → a ∈ Finset.range (n+1) := by
      intro a ha
      rw [Finset.mem_range]
      by_contra h
      push Not at h
      have hz : f.coeff a = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      exact ha (Subtype.ext (by simp [gfun, hz]))
    refine ⟨Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff
      (Finsupp.onFinset (Finset.range (n+1)) gfun hout)), ?_⟩
    intro i
    rw [Polynomial.coeff_ofFinsupp, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.onFinset_apply]
  have hP_v : ∀ i, v ((P.coeff i : V) : K) = M⁻¹ * v (f.coeff i) := by
    intro i; rw [hPcoeff i]; exact hstep i
  have hPmap : P.map (algebraMap V K) = Polynomial.C D * f := by
    ext i
    rw [Polynomial.coeff_map, Polynomial.coeff_C_mul]
    exact hPcoeff i
  -- residue facts
  have hQt : (P.map (IsLocalRing.residue V)).coeff t = 1 := by
    rw [Polynomial.coeff_map]
    have hcoefft : P.coeff t = 1 := by
      apply Subtype.ext
      rw [hPcoeff t, hD]
      exact inv_mul_cancel₀ htne
    rw [hcoefft, map_one]
  have hQzero : ∀ i, t < i → (P.map (IsLocalRing.residue V)).coeff i = 0 := by
    intro i hi
    rw [Polynomial.coeff_map, IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff, hP_v i]
    have hlt : v (f.coeff i) < M := by
      by_cases hin : i ≤ n
      · refine lt_of_le_of_ne (hleM i) ?_
        intro heq
        have hiI : i ∈ I := by
          rw [hI]; exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), heq⟩
        have := htmin i hiI
        omega
      · push Not at hin
        have hz : f.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        rw [hz, map_zero]; exact hMpos
    rw [inv_mul_lt_iff₀ hMpos, mul_one]
    exact hlt
  have hQdeg : (P.map (IsLocalRing.residue V)).natDegree = t := by
    refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      exact hQzero N hN
    · rw [hQt]; exact one_ne_zero
  have hQmonic : (P.map (IsLocalRing.residue V)).Monic := by
    unfold Polynomial.Monic Polynomial.leadingCoeff
    rw [hQdeg, hQt]
  -- Hensel step: lift the factorisation `map residue P = map residue P * 1` of `P`.
  obtain ⟨f₁, f₂, hf₁monic, hf₁map, hf₂map, hPprod⟩ :=
    Commons.RingTheory.Henselian.exists_mul_of_residue_map_eq_mul (A := V)
      (f := P) (g := Polynomial.map (IsLocalRing.residue V) P) (h := 1)
      hQmonic Polynomial.monic_one isCoprime_one_right (by rw [mul_one])
  -- degrees
  have hf₁deg : f₁.natDegree = t := by
    rw [← hf₁monic.natDegree_map (IsLocalRing.residue V), hf₁map, hQdeg]
  have hDne : D ≠ 0 := by rw [hD]; exact inv_ne_zero htne
  have hPdeg : P.natDegree = n := by
    refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      apply Subtype.ext
      rw [hPcoeff N, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
      rfl
    · intro hc
      have hz : ((P.coeff n : V) : K) = 0 := by rw [hc]; rfl
      rw [hPcoeff n] at hz
      have hnc : f.coeff n = 1 := by rw [hn]; exact hf.coeff_natDegree
      rw [hnc, mul_one] at hz
      exact hDne hz
  have hf₂ne : f₂ ≠ 0 := by
    intro h; rw [h, mul_zero] at hPprod
    have : P = 0 := hPprod
    rw [this] at hPdeg
    simp at hPdeg
    omega
  have hf₁ne : f₁ ≠ 0 := hf₁monic.ne_zero
  have hf₂deg : f₂.natDegree = n - t := by
    have := Polynomial.natDegree_mul hf₁ne hf₂ne
    rw [← hPprod, hPdeg, hf₁deg] at this
    omega
  -- conclude factorisation of f in K[X]
  have hmul : Polynomial.C D * f = f₁.map (algebraMap V K) * f₂.map (algebraMap V K) := by
    rw [← hPmap, hPprod, Polynomial.map_mul]
  have hDinv : D⁻¹ = f.coeff t := by rw [hD]; exact inv_inv _
  have hf_eq : f = (Polynomial.C (f.coeff t) * f₁.map (algebraMap V K)) * f₂.map (algebraMap V K) := by
    have h3 : Polynomial.C D⁻¹ * (Polynomial.C D * f) = f := by
      rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hDne, Polynomial.C_1, one_mul]
    calc f = Polynomial.C D⁻¹ * (Polynomial.C D * f) := h3.symm
      _ = Polynomial.C D⁻¹ * (f₁.map (algebraMap V K) * f₂.map (algebraMap V K)) := by
            rw [hmul]
      _ = (Polynomial.C (f.coeff t) * f₁.map (algebraMap V K)) * f₂.map (algebraMap V K) := by
            rw [hDinv, mul_assoc]
  have hunit_or := hirr.isUnit_or_isUnit hf_eq
  rcases hunit_or with hu | hu
  · have : (Polynomial.C (f.coeff t) * f₁.map (algebraMap V K)).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [Polynomial.natDegree_C_mul htne,
      Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective V K) f₁, hf₁deg] at this
    omega
  · have : (f₂.map (algebraMap V K)).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective V K) f₂, hf₂deg] at this
    omega


end Commons.RingTheory.Henselian
