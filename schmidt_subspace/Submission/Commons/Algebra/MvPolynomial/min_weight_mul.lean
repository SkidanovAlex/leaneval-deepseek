import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.SimpleRing.Principal

open scoped BigOperators
open _root_.MvPolynomial

namespace Commons.Algebra.MvPolynomial

/-- The set of weights of the monomials in the support of `P`, written with the additive weight
`Finsupp.weight w`, coincides with the image of the support under `Finsupp.weight w`. -/
private lemma weightSet_eq {K : Type*} [CommSemiring K] {σ : Type*} (w : σ → ℝ)
    (P : MvPolynomial σ K) :
    {t : ℝ | ∃ m ∈ P.support, t = Finsupp.weight w m}
      = Finsupp.weight w '' (P.support : Set (σ →₀ ℕ)) := by
  ext t
  constructor <;> rintro ⟨m, hm, rfl⟩ <;> exact ⟨m, hm, rfl⟩

/-- For the weight `w m = ∑ i, m i / r i`, the minimum of `w` over the support of a product of
nonzero polynomials is the sum of the minima over the two factors. -/
theorem min_weight_mul {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    (r : σ → ℕ) (R S : MvPolynomial σ K) (hR : R ≠ 0) (hS : S ≠ 0) :
    sInf {t : ℝ | ∃ m ∈ (R * S).support, t = ∑ i, (m i : ℝ) / (r i : ℝ)}
      = sInf {t : ℝ | ∃ m ∈ R.support, t = ∑ i, (m i : ℝ) / (r i : ℝ)}
      + sInf {t : ℝ | ∃ m ∈ S.support, t = ∑ i, (m i : ℝ) / (r i : ℝ)} := by
  classical
  -- The weight `∑ i, m i / r i` is the additive weight `Finsupp.weight w` for `w i = (r i)⁻¹`.
  set w : σ → ℝ := fun i => (r i : ℝ)⁻¹ with hw
  have hwt : ∀ m : σ →₀ ℕ, (∑ i, (m i : ℝ) / (r i : ℝ)) = Finsupp.weight w m := by
    intro m
    rw [Finsupp.weight_eq_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [nsmul_eq_mul, div_eq_mul_inv]
  simp only [hwt]
  rw [weightSet_eq (w := w) (R * S), weightSet_eq (w := w) R, weightSet_eq (w := w) S]
  -- Rewrite each weight set as the image of a support under `Finsupp.weight w`.
  set A : Set ℝ := Finsupp.weight w '' (R.support : Set (σ →₀ ℕ)) with hA
  set B : Set ℝ := Finsupp.weight w '' (S.support : Set (σ →₀ ℕ)) with hB
  set C : Set ℝ := Finsupp.weight w '' ((R * S).support : Set (σ →₀ ℕ)) with hC
  change sInf C = sInf A + sInf B
  have hRne : R.support.Nonempty := MvPolynomial.support_nonempty.mpr hR
  have hSne : S.support.Nonempty := MvPolynomial.support_nonempty.mpr hS
  have hRS : R * S ≠ 0 := mul_ne_zero hR hS
  have hRSne : (R * S).support.Nonempty := MvPolynomial.support_nonempty.mpr hRS
  have hAne : A.Nonempty := by rw [hA]; exact Set.Nonempty.image (Finsupp.weight w) hRne
  have hBne : B.Nonempty := by rw [hB]; exact Set.Nonempty.image (Finsupp.weight w) hSne
  have hCne : C.Nonempty := by rw [hC]; exact Set.Nonempty.image (Finsupp.weight w) hRSne
  have hAfin : A.Finite := by
    rw [hA]; exact (Finset.finite_toSet R.support).image (Finsupp.weight w)
  have hBfin : B.Finite := by
    rw [hB]; exact (Finset.finite_toSet S.support).image (Finsupp.weight w)
  have hCfin : C.Finite := by
    rw [hC]; exact (Finset.finite_toSet (R * S).support).image (Finsupp.weight w)
  -- `sInf A` is attained at some monomial of `R`.
  have hαmem : sInf A ∈ A := hAne.csInf_mem hAfin
  rw [hA] at hαmem
  obtain ⟨mR, hmR, hmRw⟩ := hαmem
  have hβmem : sInf B ∈ B := hBne.csInf_mem hBfin
  rw [hB] at hβmem
  obtain ⟨mS, hmS, hmSw⟩ := hβmem
  -- The lowest-weight parts of `R` and of `S`.
  set IR : MvPolynomial σ K := weightedHomogeneousComponent w (sInf A) R with hIRdef
  set IS : MvPolynomial σ K := weightedHomogeneousComponent w (sInf B) S with hISdef
  have hIRne : IR ≠ 0 := by
    intro hzero
    have hcoeff : IR.coeff mR ≠ 0 := by
      rw [hIRdef, MvPolynomial.coeff_weightedHomogeneousComponent, if_pos hmRw]
      exact MvPolynomial.mem_support_iff.mp hmR
    rw [hzero, MvPolynomial.coeff_zero] at hcoeff
    exact hcoeff rfl
  have hISne : IS ≠ 0 := by
    intro hzero
    have hcoeff : IS.coeff mS ≠ 0 := by
      rw [hISdef, MvPolynomial.coeff_weightedHomogeneousComponent, if_pos hmSw]
      exact MvPolynomial.mem_support_iff.mp hmS
    rw [hzero, MvPolynomial.coeff_zero] at hcoeff
    exact hcoeff rfl
  have hprod : IR * IS ≠ 0 := mul_ne_zero hIRne hISne
  have hIRhom : IsWeightedHomogeneous w IR (sInf A) := by
    rw [hIRdef]; exact weightedHomogeneousComponent_isWeightedHomogeneous (sInf A) R
  have hIShom : IsWeightedHomogeneous w IS (sInf B) := by
    rw [hISdef]; exact weightedHomogeneousComponent_isWeightedHomogeneous (sInf B) S
  have hhom : IsWeightedHomogeneous w (IR * IS) (sInf A + sInf B) := hIRhom.mul hIShom
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hprod
  have hwd : Finsupp.weight w d = sInf A + sInf B := hhom (MvPolynomial.mem_support_iff.mp hd)
  -- The coefficient of `d` in `R * S` and in `IR * IS` agree (no cancellation).
  have hwt_eq : (R * S).coeff d = (IR * IS).coeff d := by
    rw [MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxadd : x.1 + x.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    rw [hIRdef, hISdef]
    rw [MvPolynomial.coeff_weightedHomogeneousComponent,
        MvPolynomial.coeff_weightedHomogeneousComponent]
    by_cases hR0 : R.coeff x.1 = 0
    · simp [hR0]
    by_cases hS0 : S.coeff x.2 = 0
    · simp [hS0]
    have hle1 : sInf A ≤ Finsupp.weight w x.1 :=
      csInf_le hAfin.bddBelow (by rw [hA]; exact ⟨x.1, MvPolynomial.mem_support_iff.mpr hR0, rfl⟩)
    have hle2 : sInf B ≤ Finsupp.weight w x.2 :=
      csInf_le hBfin.bddBelow (by rw [hB]; exact ⟨x.2, MvPolynomial.mem_support_iff.mpr hS0, rfl⟩)
    have hsumw : Finsupp.weight w x.1 + Finsupp.weight w x.2 = sInf A + sInf B := by
      rw [← map_add, hxadd, hwd]
    have hw1 : Finsupp.weight w x.1 = sInf A := by linarith
    have hw2 : Finsupp.weight w x.2 = sInf B := by linarith
    rw [if_pos hw1, if_pos hw2]
  have hdRS : d ∈ (R * S).support := by
    rw [MvPolynomial.mem_support_iff, hwt_eq]
    exact MvPolynomial.mem_support_iff.mp hd
  -- Upper bound: `d` attains the value `sInf A + sInf B`.
  have hupper : sInf C ≤ sInf A + sInf B := by
    have hmem : Finsupp.weight w d ∈ C := by rw [hC]; exact ⟨d, hdRS, rfl⟩
    calc sInf C ≤ Finsupp.weight w d := csInf_le hCfin.bddBelow hmem
      _ = sInf A + sInf B := hwd
  -- Lower bound: every monomial of `R * S` has weight at least `sInf A + sInf B`.
  have hlower : sInf A + sInf B ≤ sInf C := by
    refine le_csInf hCne fun t ht => ?_
    rw [hC] at ht
    obtain ⟨m, hm, rfl⟩ := ht
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp (MvPolynomial.support_mul R S hm)
    have hle1 : sInf A ≤ Finsupp.weight w a :=
      csInf_le hAfin.bddBelow (by rw [hA]; exact ⟨a, ha, rfl⟩)
    have hle2 : sInf B ≤ Finsupp.weight w b :=
      csInf_le hBfin.bddBelow (by rw [hB]; exact ⟨b, hb, rfl⟩)
    have hmw : Finsupp.weight w m = Finsupp.weight w a + Finsupp.weight w b := by
      rw [← hab, map_add]
    rw [hmw]
    exact add_le_add hle1 hle2
  exact le_antisymm hupper hlower

end Commons.Algebra.MvPolynomial