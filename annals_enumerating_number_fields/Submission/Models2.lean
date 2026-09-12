import ChallengeDeps
import Submission.Models
import Submission.Commons.NumberTheory.NumberField.small_algebraic_model
import Submission.Commons.NumberTheory.NumberField.one_le_rootDiscr
import Submission.Commons.RingTheory.Jacobian.localization_quotient_jacobian_isField
import Submission.Commons.RingTheory.Ideal.mem_minimalPrimes_of_localization_iso_field
import Submission.Commons.Algebra.MvPolynomial.finite_bounded_polys

open AlgebraicGeometry Module NumberField Real Scheme
open _root_.EnumeratingNumberFields
open _root_.EnumeratingNumberFields.NumberFieldOfBoundedDiscriminant
  _root_.EnumeratingNumberFields.NumberFieldOfDegree

set_option autoImplicit false

namespace Submission.Models2

noncomputable section

/-- Mapping coefficients does not increase the total degree. -/
lemma totalDegree_map_le' {R S σ : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (p : MvPolynomial σ R) : ((p.map f).totalDegree) ≤ p.totalDegree := by
  rw [MvPolynomial.totalDegree, MvPolynomial.totalDegree]
  exact Finset.sup_mono (MvPolynomial.support_map_subset f p)

/-- Polynomials in `r` variables over `ℤ` of degree ≤ `d` with coefficients bounded by `K₀`. -/
def PolySub (K₀ r d : ℕ) : Type :=
  {E : MvPolynomial (Fin r) ℤ // E.totalDegree ≤ d ∧ ∀ μ, |E.coeff μ| ≤ (K₀ : ℤ)}

instance (K₀ r d : ℕ) : Finite (PolySub K₀ r d) :=
  Commons.Algebra.MvPolynomial.finite_bounded_polys r d K₀

instance (K₀ r d : ℕ) : Fintype (PolySub K₀ r d) := Fintype.ofFinite _

/-- A model code: parameters `r, d` (valid: `(d+r).choose r ≤ M₀`) and a bounded polynomial
for each equation. -/
def CodesT (K₀ R₀ M₀ : ℕ) : Type :=
  Σ rd : {p : Fin (R₀ + 1) × Fin (R₀ + 1) // (p.1.val + p.2.val).choose p.1.val ≤ M₀},
    (Fin rd.1.1.val → PolySub K₀ rd.1.1.val rd.1.2.val)

instance (K₀ R₀ M₀ : ℕ) : Fintype (CodesT K₀ R₀ M₀) := by
  dsimp only [CodesT]; infer_instance

/-- The number of equations coded by `c`. -/
abbrev codeR {K₀ R₀ M₀ : ℕ} (c : CodesT K₀ R₀ M₀) : ℕ := c.1.1.1.val

/-- The degree bound coded by `c`. -/
abbrev codeD {K₀ R₀ M₀ : ℕ} (c : CodesT K₀ R₀ M₀) : ℕ := c.1.1.2.val

/-- The coordinate ring of the model coded by `c`. -/
def codeQuot (K₀ R₀ M₀ : ℕ) (c : CodesT K₀ R₀ M₀) : Type :=
  (MvPolynomial (Fin c.1.1.1.val) ℚ) ⧸
    Ideal.span (Set.range fun i => ((c.2 i).1).map (algebraMap ℤ ℚ))

instance (K₀ R₀ M₀ : ℕ) (c : CodesT K₀ R₀ M₀) : CommRing (codeQuot K₀ R₀ M₀ c) := by
  dsimp only [codeQuot]; infer_instance

instance (K₀ R₀ M₀ : ℕ) (c : CodesT K₀ R₀ M₀) : IsNoetherianRing (codeQuot K₀ R₀ M₀ c) := by
  dsimp only [codeQuot]
  exact Ideal.Quotient.isNoetherianRing _

/-- Codes together with a minimal prime of their coordinate ring. -/
def DomainT (K₀ R₀ M₀ : ℕ) : Type :=
  Σ c : CodesT K₀ R₀ M₀,
    {𝔭 : Ideal (codeQuot K₀ R₀ M₀ c) //
      𝔭 ∈ Ideal.minimalPrimes (⊥ : Ideal (codeQuot K₀ R₀ M₀ c))}

instance (K₀ R₀ M₀ : ℕ) (c : CodesT K₀ R₀ M₀) :
    Finite {𝔭 : Ideal (codeQuot K₀ R₀ M₀ c) //
      𝔭 ∈ Ideal.minimalPrimes (⊥ : Ideal (codeQuot K₀ R₀ M₀ c))} :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing (codeQuot K₀ R₀ M₀ c) ⊥).to_subtype

instance (K₀ R₀ M₀ : ℕ) : Finite (DomainT K₀ R₀ M₀) := by
  dsimp only [DomainT]; infer_instance

/-- Abstract counting step for Theorem 2, with the two counting inputs as hypotheses. -/
theorem theorem_2_of_model
    (hmodel : Submission.Models.ModelStatement)
    (hana : ∀ (Q₁ : ℝ), 0 < Q₁ → ∃ Q : ℝ, Q > 0 ∧ ∀ n : ℕ, Q ≤ n → ∀ H : ℕ, 1 ≤ H →
      ((Nat.ceil (Q₁ * Real.log n) + 1 : ℕ) : ℝ) ^ 2
        * (((2 * Nat.ceil (((n : ℝ) * (H : ℝ) ^ ((n : ℝ))⁻¹) ^ (Q₁ * Real.log n)) + 3 : ℕ)) : ℝ)
            ^ (Nat.ceil (Q₁ * Real.log n) * Nat.ceil (Q₁ * (n : ℝ) * Real.log n))
        * ((Nat.ceil (Q₁ * Real.log n) : ℕ) : ℝ) ^ (Nat.ceil (Q₁ * Real.log n))
        ≤ (n : ℝ) ^ (Q * (n : ℝ) * (Real.log n) ^ 3) * (H : ℝ) ^ (Q * (Real.log n) ^ 3))
    (hcard : ∀ (r d K₀ : ℕ),
      Nat.card {E : MvPolynomial (Fin r) ℤ // E.totalDegree ≤ d ∧ ∀ μ, |E.coeff μ| ≤ (K₀ : ℤ)}
        ≤ (2 * K₀ + 2) ^ ((d + r).choose r))
    (hbez : ∀ {k : Type} [Field k] {r : ℕ} (f : Fin r → MvPolynomial (Fin r) k),
      Nat.card {p : Ideal (MvPolynomial (Fin r) k ⧸ Ideal.span (Set.range f)) //
        p ∈ Ideal.minimalPrimes (⊥ : Ideal (MvPolynomial (Fin r) k ⧸ Ideal.span (Set.range f)))}
        ≤ ∏ i, (f i).totalDegree.max 1) :
    ∃ Q > 0, ∀ n ≥ Q, ∀ H ≥ 1,
      (Nat.card (NumberFieldOfBoundedDiscriminantUpToIsomorphism n H) : ℝ) ≤
        (n : ℝ) ^ (Q * (n : ℝ) * (Real.log n) ^ 3) * (H : ℝ) ^ (Q * (Real.log n) ^ 3) := by
  obtain ⟨Q₁, hQ₁pos, hQ₁⟩ := hmodel
  obtain ⟨Qa, hQapos, hQabound⟩ := hana (Q₁ : ℝ) (by exact_mod_cast hQ₁pos)
  let C : ℕ := Nat.ceil (Real.exp (1 / (Q₁ : ℝ)))
  let Qn : ℕ := max Q₁ (max (Nat.ceil Qa) (max C 3))
  have hQnpos : 0 < Qn := by
    have : 1 ≤ C := by
      have h1 : (1 : ℝ) ≤ Real.exp (1 / (Q₁ : ℝ)) := by
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        positivity
      have := Nat.le_ceil (Real.exp (1 / (Q₁ : ℝ)))
      have : (1 : ℝ) ≤ (C : ℝ) := by simpa [C] using le_trans h1 this
      exact_mod_cast this
    omega
  refine ⟨Qn, hQnpos, ?_⟩
  intro n hn H hH
  have hmax : Qn ≤ n := hn
  have hnQ₁ : Q₁ ≤ n := le_trans (le_max_left _ _) hmax
  have hmax0 : max (Nat.ceil Qa) (max C 3) ≤ n := le_trans (le_max_right _ _) hmax
  have hmax1 : Nat.ceil Qa ≤ n := le_trans (le_max_left _ _) hmax0
  have hmax2 : max C 3 ≤ n := le_trans (le_max_right _ _) hmax0
  have hnC : C ≤ n := le_trans (le_max_left _ _) hmax2
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hmax2
  have hnQa : Qa ≤ (n : ℝ) := by
    have := Nat.le_ceil Qa
    have h2 : ((Nat.ceil Qa : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmax1
    linarith
  have hnC' : (C : ℕ) ≤ n := hnC
  have hCR : Real.exp (1 / (Q₁ : ℝ)) ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hnC')
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : (1 : ℕ) ≤ n := by omega
    exact_mod_cast this
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hH1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  let R₀ : ℕ := Nat.ceil ((Q₁ : ℝ) * Real.log n)
  let M₀ : ℕ := Nat.ceil ((Q₁ : ℝ) * (n : ℝ) * Real.log n)
  let K₀ : ℕ := Nat.ceil (((n : ℝ) * (H : ℝ) ^ ((n : ℝ))⁻¹) ^ ((Q₁ : ℝ) * Real.log n))
  have hlog1 : (1 : ℝ) ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hnpos]
    have h3e : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_three
    have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
    linarith
  have hlog0 : 0 ≤ Real.log n := by linarith
  have hQ₁log : 1 ≤ (Q₁ : ℝ) * Real.log n := by
    have hlog_inv : 1 / (Q₁ : ℝ) ≤ Real.log n := by
      calc 1 / (Q₁ : ℝ) = Real.log (Real.exp (1 / (Q₁ : ℝ))) := (Real.log_exp _).symm
        _ ≤ Real.log n := Real.log_le_log (Real.exp_pos _) hCR
    have hQ₁posR : (0 : ℝ) < (Q₁ : ℝ) := by exact_mod_cast hQ₁pos
    have hmul := mul_le_mul_of_nonneg_left hlog_inv (le_of_lt hQ₁posR)
    have hone : (Q₁ : ℝ) * (1 / (Q₁ : ℝ)) = 1 := by field_simp
    rwa [hone] at hmul
  have hR₀1 : 1 ≤ R₀ := by
    have h := Nat.le_ceil ((Q₁ : ℝ) * Real.log n)
    have : (1 : ℝ) ≤ (R₀ : ℝ) := by simpa [R₀] using le_trans hQ₁log h
    exact_mod_cast this
  -- Main counting bound
  have hmain : (Nat.card (NumberFieldOfBoundedDiscriminantUpToIsomorphism n H) : ℝ) ≤
      ((R₀ + 1 : ℕ) : ℝ) ^ 2 * ((2 * K₀ + 3 : ℕ) : ℝ) ^ (R₀ * M₀)
        * ((R₀ : ℕ) : ℝ) ^ R₀ := by
    classical
    -- Coefficient bound transfer: rootDiscr ≤ H^{1/n}
    have hroot (K' : Type) [Field K'] [NumberField K'] (hfin : Module.finrank ℚ K' = n)
        (hdisc : |NumberField.discr K'| ≤ (H : ℤ)) :
        NumberField.rootDiscr K' ≤ (H : ℝ) ^ ((n : ℝ))⁻¹ := by
      rw [NumberField.rootDiscr_def]
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hexp : 0 ≤ ((Module.finrank ℚ K' : ℝ))⁻¹ := by positivity
      have h1 : ((|NumberField.discr K'| : ℤ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast hdisc
      rw [hfin] at hexp ⊢
      exact Real.rpow_le_rpow (by positivity) h1 hexp
    by_cases hne : Nonempty (NumberFieldOfBoundedDiscriminantUpToIsomorphism n H)
    · -- surjection from the code/prime pairs onto the quotient
      let P : DomainT K₀ R₀ M₀ → Prop := fun x => ∃ K : NumberFieldOfBoundedDiscriminant n H,
          Nonempty (K ≃+* (codeQuot K₀ R₀ M₀ x.1 ⧸ x.2.1))
      let G : DomainT K₀ R₀ M₀ → NumberFieldOfBoundedDiscriminantUpToIsomorphism n H :=
        fun x => if h : P x then Quot.mk _ (Classical.choose h) else Classical.choice hne
      have hsurjG : Function.Surjective G := by
        intro q
        let K := Quot.out q
        have hKq : Quot.mk _ K = q := Quot.out_eq q
        haveI : NumberField K.carrier := K.numberField
        obtain ⟨r, d, hr, hd, hbinom, E, hdeg, hcoeff, φ, hsurjφ, hE0, hunit⟩ :=
          hQ₁ n hnQ₁ K.carrier K.degree
        have hrR : r ≤ R₀ := by
          have h := Nat.le_ceil ((Q₁ : ℝ) * Real.log n)
          have h2 : (r : ℝ) ≤ (R₀ : ℝ) := by simpa [R₀] using le_trans hr h
          exact_mod_cast h2
        have hdR : d ≤ R₀ := by
          have h := Nat.le_ceil ((Q₁ : ℝ) * Real.log n)
          have h2 : (d : ℝ) ≤ (R₀ : ℝ) := by simpa [R₀] using le_trans hd h
          exact_mod_cast h2
        have hcoeff' : ∀ i μ, |(E i).coeff μ| ≤ (K₀ : ℤ) := by
          intro i μ
          have h1 := hcoeff i μ
          have hrd := hroot K.carrier K.degree K.discr
          have hbase : (n : ℝ) * NumberField.rootDiscr K.carrier
              ≤ (n : ℝ) * (H : ℝ) ^ ((n : ℝ))⁻¹ := by
            have := mul_le_mul_of_nonneg_left hrd (by positivity : (0 : ℝ) ≤ (n : ℝ))
            linarith
          have hexp : 0 ≤ (Q₁ : ℝ) * Real.log n := by
            have h1 : (0 : ℝ) < (Q₁ : ℝ) := by exact_mod_cast hQ₁pos
            have h2 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
            positivity
          have h2 : ((n : ℝ) * NumberField.rootDiscr K.carrier) ^ ((Q₁ : ℝ) * Real.log n)
              ≤ ((n : ℝ) * (H : ℝ) ^ ((n : ℝ))⁻¹) ^ ((Q₁ : ℝ) * Real.log n) :=
            Real.rpow_le_rpow (by
              have h1 : (0 : ℝ) ≤ NumberField.rootDiscr K.carrier := by
                rw [NumberField.rootDiscr_def]; positivity
              positivity) hbase hexp
          have h3 : ((n : ℝ) * (H : ℝ) ^ ((n : ℝ))⁻¹) ^ ((Q₁ : ℝ) * Real.log n) ≤ (K₀ : ℝ) := by
            have := Nat.le_ceil (((n : ℝ) * (H : ℝ) ^ ((n : ℝ))⁻¹) ^ ((Q₁ : ℝ) * Real.log n))
            simpa [K₀] using this
          have h4 : ((|(E i).coeff μ| : ℤ) : ℝ) ≤ (K₀ : ℝ) := le_trans h1 (le_trans h2 h3)
          exact_mod_cast h4
        have hrR' : r < R₀ + 1 := by omega
        have hdR' : d < R₀ + 1 := by omega
        have hvalid : (r + d).choose r ≤ M₀ := by
          have h1 : ((d + r).choose r : ℝ) ≤ (M₀ : ℝ) := by
            have := Nat.le_ceil ((Q₁ : ℝ) * (n : ℝ) * Real.log n)
            simpa [M₀] using le_trans hbinom this
          have h2 : ((r + d).choose r : ℝ) ≤ (M₀ : ℝ) := by
            rwa [Nat.add_comm r d]
          exact_mod_cast h2
        let c : CodesT K₀ R₀ M₀ :=
          ⟨⟨(⟨r, hrR'⟩, ⟨d, hdR'⟩), hvalid⟩, fun i => ⟨E i, hdeg i, hcoeff' i⟩⟩
        have hker : Ideal.span (Set.range fun i => (E i).map (algebraMap ℤ ℚ))
            ≤ RingHom.ker (φ : MvPolynomial (Fin r) ℚ →+* K.carrier) := by
          rw [Ideal.span_le]
          rintro _ ⟨i, rfl⟩
          exact hE0 i
        let ψ : codeQuot K₀ R₀ M₀ c →+* K.carrier :=
          Ideal.Quotient.lift (Ideal.span (Set.range fun i => (E i).map (algebraMap ℤ ℚ)))
            (φ : MvPolynomial (Fin r) ℚ →+* K.carrier)
            (fun a ha => RingHom.mem_ker.mp (hker ha))
        have hψsurj : Function.Surjective ψ := by
          intro y
          obtain ⟨p, hp⟩ := hsurjφ y
          exact ⟨Ideal.Quotient.mk _ p, by
            change Ideal.Quotient.lift _ (φ : MvPolynomial (Fin r) ℚ →+* K.carrier) _ (Ideal.Quotient.mk _ p) = y
            rw [Ideal.Quotient.lift_mk]
            exact hp⟩
        have hmax : (RingHom.ker ψ).IsMaximal := RingHom.ker_isMaximal_of_surjective ψ hψsurj
        haveI : (RingHom.ker ψ).IsPrime := hmax.isPrime
        have hiso : Nonempty (@Localization.AtPrime _ _ (RingHom.ker ψ) hmax.isPrime ≃+* K.carrier) :=
          Commons.RingTheory.Jacobian.localization_quotient_jacobian_isField
            (fun i => (E i).map (algebraMap ℤ ℚ)) K.carrier ψ hψsurj (by
              have hunit' : IsUnit (φ (Matrix.det fun i j => MvPolynomial.pderiv j ((E i).map (algebraMap ℤ ℚ)))) := hunit
              convert hunit' using 2
              change ψ (Ideal.Quotient.mk _ (Matrix.det fun i j => MvPolynomial.pderiv j ((E i).map (algebraMap ℤ ℚ)))) = _
              rw [show ψ (Ideal.Quotient.mk _ (Matrix.det fun i j => MvPolynomial.pderiv j ((E i).map (algebraMap ℤ ℚ))))
                = φ (Matrix.det fun i j => MvPolynomial.pderiv j ((E i).map (algebraMap ℤ ℚ))) from by
                  change Ideal.Quotient.lift _ (φ : MvPolynomial (Fin r) ℚ →+* K.carrier) _ (Ideal.Quotient.mk _ _) = _
                  rw [Ideal.Quotient.lift_mk]; rfl])
        have hmin : RingHom.ker ψ ∈ Ideal.minimalPrimes (⊥ : Ideal (codeQuot K₀ R₀ M₀ c)) :=
          Commons.RingTheory.Ideal.mem_minimalPrimes_of_localization_iso_field (RingHom.ker ψ) hiso
        -- the isomorphism K ≃+* codeQuot ⧸ ker ψ
        have hisoK : Nonempty (K ≃+* (codeQuot K₀ R₀ M₀ c ⧸ RingHom.ker ψ)) :=
          ⟨(RingHom.quotientKerEquivOfSurjective hψsurj).symm⟩
        refine ⟨⟨c, ⟨RingHom.ker ψ, hmin⟩⟩, ?_⟩
        -- image computation
        have hcond : P ⟨c, ⟨RingHom.ker ψ, hmin⟩⟩ := ⟨K, hisoK⟩
        dsimp only [P] at hcond
        show (if h : P ⟨c, ⟨RingHom.ker ψ, hmin⟩⟩ then
            Quot.mk _ (Classical.choose h) else Classical.choice hne) = q
        rw [dif_pos hcond]
        refine Eq.trans ?_ hKq
        apply Quot.sound
        -- the chosen field is isomorphic to K
        have hch : Nonempty ((Classical.choose hcond : NumberFieldOfBoundedDiscriminant n H)
            ≃+* (codeQuot K₀ R₀ M₀ c ⧸ RingHom.ker ψ)) := Classical.choose_spec hcond
        exact ⟨hch.some.trans hisoK.some.symm⟩
      haveI : Fintype (DomainT K₀ R₀ M₀) := Fintype.ofFinite _
      have hcard_le : Nat.card (NumberFieldOfBoundedDiscriminantUpToIsomorphism n H)
          ≤ Nat.card (DomainT K₀ R₀ M₀) := Nat.card_le_card_of_surjective G hsurjG
      have hdomain : (Nat.card (DomainT K₀ R₀ M₀) : ℝ) ≤
          ((R₀ + 1 : ℕ) : ℝ) ^ 2 * ((2 * K₀ + 3 : ℕ) : ℝ) ^ (R₀ * M₀)
            * ((R₀ : ℕ) : ℝ) ^ R₀ := by
        have hfiber (c : CodesT K₀ R₀ M₀) :
            Nat.card {𝔭 : Ideal (codeQuot K₀ R₀ M₀ c) //
                𝔭 ∈ Ideal.minimalPrimes (⊥ : Ideal (codeQuot K₀ R₀ M₀ c))} ≤ R₀ ^ R₀ := by
          have h1 := hbez (k := ℚ) (r := c.1.1.1.val)
            (fun i => ((c.2 i).1).map (algebraMap ℤ ℚ))
          have h2 : ∀ i, (((c.2 i).1).map (algebraMap ℤ ℚ)).totalDegree.max 1 ≤ R₀ := by
            intro i
            have hdeg : (((c.2 i).1).map (algebraMap ℤ ℚ)).totalDegree ≤ (c.2 i).1.totalDegree :=
              totalDegree_map_le' (algebraMap ℤ ℚ) (c.2 i).1
            have hd : (c.2 i).1.totalDegree ≤ c.1.1.2.val := (c.2 i).2.1
            have hdR'' : c.1.1.2.val ≤ R₀ := by
              have : c.1.1.2.val < R₀ + 1 := c.1.1.2.isLt
              omega
            exact max_le (le_trans hdeg (le_trans hd hdR'')) hR₀1
          calc Nat.card {𝔭 : Ideal (codeQuot K₀ R₀ M₀ c) //
                𝔭 ∈ Ideal.minimalPrimes (⊥ : Ideal (codeQuot K₀ R₀ M₀ c))}
              ≤ ∏ i, (((c.2 i).1).map (algebraMap ℤ ℚ)).totalDegree.max 1 := h1
            _ ≤ ∏ _i : Fin c.1.1.1.val, R₀ := by
                apply Finset.prod_le_prod
                · intro i _; exact Nat.zero_le _
                · intro i _; exact h2 i
            _ = R₀ ^ c.1.1.1.val := by
                rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            _ ≤ R₀ ^ R₀ := by
                apply Nat.pow_le_pow_right (by omega : 0 < R₀)
                have : c.1.1.1.val < R₀ + 1 := c.1.1.1.isLt
                omega
        have hcodes : Nat.card (CodesT K₀ R₀ M₀) ≤ (R₀ + 1) ^ 2 * (2 * K₀ + 2) ^ (M₀ * R₀) := by
          rw [show Nat.card (CodesT K₀ R₀ M₀) =
              ∑ rd : {p : Fin (R₀ + 1) × Fin (R₀ + 1) // (p.1.val + p.2.val).choose p.1.val ≤ M₀},
                Nat.card (Fin rd.1.1.val → PolySub K₀ rd.1.1.val rd.1.2.val) from Nat.card_sigma]
          calc ∑ rd : {p : Fin (R₀ + 1) × Fin (R₀ + 1) // (p.1.val + p.2.val).choose p.1.val ≤ M₀},
                Nat.card (Fin rd.1.1.val → PolySub K₀ rd.1.1.val rd.1.2.val)
              ≤ ∑ _rd : {p : Fin (R₀ + 1) × Fin (R₀ + 1) // (p.1.val + p.2.val).choose p.1.val ≤ M₀},
                (2 * K₀ + 2) ^ (M₀ * R₀) := by
                apply Finset.sum_le_sum
                intro rd _
                rw [Nat.card_fun, Nat.card_fin]
                calc Nat.card (PolySub K₀ rd.1.1.val rd.1.2.val) ^ rd.1.1.val
                    ≤ ((2 * K₀ + 2) ^ ((rd.1.2.val + rd.1.1.val).choose rd.1.1.val)) ^ rd.1.1.val :=
                      Nat.pow_le_pow_left (hcard _ _ _) _
                  _ = (2 * K₀ + 2) ^ (((rd.1.2.val + rd.1.1.val).choose rd.1.1.val) * rd.1.1.val) := by
                      rw [pow_mul]
                  _ ≤ (2 * K₀ + 2) ^ (M₀ * R₀) := by
                      apply Nat.pow_le_pow_right (by omega)
                      have hv : (rd.1.1.val + rd.1.2.val).choose rd.1.1.val ≤ M₀ := rd.2
                      have hr : rd.1.1.val ≤ R₀ := by
                        have : rd.1.1.val < R₀ + 1 := rd.1.1.isLt; omega
                      have hm : (rd.1.1.val + rd.1.2.val).choose rd.1.1.val ≤ M₀ := hv
                      calc ((rd.1.2.val + rd.1.1.val).choose rd.1.1.val) * rd.1.1.val
                          = ((rd.1.1.val + rd.1.2.val).choose rd.1.1.val) * rd.1.1.val := by
                            rw [Nat.add_comm rd.1.2.val rd.1.1.val]
                        _ ≤ M₀ * R₀ := Nat.mul_le_mul hm hr
            _ = Nat.card {p : Fin (R₀ + 1) × Fin (R₀ + 1) // (p.1.val + p.2.val).choose p.1.val ≤ M₀}
                  * (2 * K₀ + 2) ^ (M₀ * R₀) := by
                rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
                rfl
            _ ≤ (R₀ + 1) ^ 2 * (2 * K₀ + 2) ^ (M₀ * R₀) := by
                have hsub : Nat.card {p : Fin (R₀ + 1) × Fin (R₀ + 1) //
                    (p.1.val + p.2.val).choose p.1.val ≤ M₀} ≤ (R₀ + 1) ^ 2 := by
                  calc Nat.card {p : Fin (R₀ + 1) × Fin (R₀ + 1) // (p.1.val + p.2.val).choose p.1.val ≤ M₀}
                      ≤ Nat.card (Fin (R₀ + 1) × Fin (R₀ + 1)) :=
                        Nat.card_le_card_of_injective (fun a : {p : Fin (R₀ + 1) × Fin (R₀ + 1) //
                            (p.1.val + p.2.val).choose p.1.val ≤ M₀} => a.1)
                          (fun a b h => Subtype.ext h)
                    _ = (R₀ + 1) ^ 2 := by rw [Nat.card_prod, Nat.card_fin]; ring
                exact Nat.mul_le_mul_right _ hsub
        have hnat : Nat.card (DomainT K₀ R₀ M₀)
            ≤ (R₀ + 1) ^ 2 * (2 * K₀ + 2) ^ (M₀ * R₀) * R₀ ^ R₀ := by
          rw [show Nat.card (DomainT K₀ R₀ M₀) =
              ∑ c : CodesT K₀ R₀ M₀, Nat.card {𝔭 : Ideal (codeQuot K₀ R₀ M₀ c) //
                𝔭 ∈ Ideal.minimalPrimes (⊥ : Ideal (codeQuot K₀ R₀ M₀ c))} from Nat.card_sigma]
          calc ∑ c : CodesT K₀ R₀ M₀, Nat.card {𝔭 : Ideal (codeQuot K₀ R₀ M₀ c) //
                𝔭 ∈ Ideal.minimalPrimes (⊥ : Ideal (codeQuot K₀ R₀ M₀ c))}
              ≤ ∑ _c : CodesT K₀ R₀ M₀, R₀ ^ R₀ := Finset.sum_le_sum (fun c _ => hfiber c)
            _ = Nat.card (CodesT K₀ R₀ M₀) * R₀ ^ R₀ := by
                rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
                rfl
            _ ≤ ((R₀ + 1) ^ 2 * (2 * K₀ + 2) ^ (M₀ * R₀)) * R₀ ^ R₀ :=
                Nat.mul_le_mul_right _ hcodes
        calc (Nat.card (DomainT K₀ R₀ M₀) : ℝ)
            ≤ (((R₀ + 1) ^ 2 * (2 * K₀ + 2) ^ (M₀ * R₀) * R₀ ^ R₀ : ℕ) : ℝ) := by
              exact_mod_cast hnat
          _ = ((R₀ + 1 : ℕ) : ℝ) ^ 2 * ((2 * K₀ + 2 : ℕ) : ℝ) ^ (R₀ * M₀) * ((R₀ : ℕ) : ℝ) ^ R₀ := by
              push_cast [Nat.mul_comm M₀ R₀]
              rfl
          _ ≤ ((R₀ + 1 : ℕ) : ℝ) ^ 2 * ((2 * K₀ + 3 : ℕ) : ℝ) ^ (R₀ * M₀) * ((R₀ : ℕ) : ℝ) ^ R₀ := by
              gcongr
              · omega

      exact le_trans (by exact_mod_cast hcard_le) hdomain
    · haveI : IsEmpty (NumberFieldOfBoundedDiscriminantUpToIsomorphism n H) :=
        not_nonempty_iff.mp hne
      rw [show Nat.card (NumberFieldOfBoundedDiscriminantUpToIsomorphism n H) = 0 from
        Nat.card_eq_zero.mpr (Or.inl inferInstance)]
      simp only [Nat.cast_zero]
      positivity
  refine le_trans hmain ?_
  have h1 := hQabound n hnQa H hH
  have hQale : Qa ≤ (Qn : ℝ) := by
    have h1 : Qa ≤ (Nat.ceil Qa : ℕ) := Nat.le_ceil Qa
    have h2 : ((Nat.ceil Qa : ℕ) : ℝ) ≤ (Qn : ℝ) := by
      have h3 : Nat.ceil Qa ≤ Qn :=
        le_trans (le_max_left _ _) (le_max_right _ _)
      exact_mod_cast h3
    linarith
  have hexp1 : Qa * (n : ℝ) * (Real.log n) ^ 3 ≤ (Qn : ℝ) * (n : ℝ) * (Real.log n) ^ 3 := by
    have h3 : (0 : ℝ) ≤ (Real.log n) ^ 3 := by positivity
    have h2 : Qa * (n : ℝ) ≤ (Qn : ℝ) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hQale (le_of_lt hnpos)
    exact mul_le_mul_of_nonneg_right h2 h3
  have hexp2 : Qa * (Real.log n) ^ 3 ≤ (Qn : ℝ) * (Real.log n) ^ 3 :=
    mul_le_mul_of_nonneg_right hQale (by positivity)
  refine le_trans h1 (mul_le_mul ?_ ?_ (by positivity) (by positivity))
  · exact Real.rpow_le_rpow_of_exponent_le hn1 hexp1
  · exact Real.rpow_le_rpow_of_exponent_le hH1 hexp2
end

end Submission.Models2
