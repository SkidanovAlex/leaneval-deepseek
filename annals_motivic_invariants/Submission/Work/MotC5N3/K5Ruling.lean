import Mathlib
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotC5N3.ASrulTheta_ker_le
import Submission.Work.MotC5N3.sAS2_ne_zero_gen
import Submission.Work.MotC5N3.fwVecAS2_three_notMem_x_gen
import Submission.Work.MotC5N3.RulingX2.X2_notMem_radical_generic
import Submission.Work.MotC5N3.RulingCert.ASrulTheta_sAS2_gen
import Submission.Work.MotC5N3.ASrulTheta_rangeClosure
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC5N3

/-- **K5 of the AS branch**: the source ruling quintic `sAS2 a b g` is ruled over the residual curve
of the Artin–Schreier Klein datum `(a, b, g)`.

Content: for `K` of characteristic `5`, `a b g : K` with `a * b ≠ 0`, `a ^ 2 - a * b - b ^ 2 ≠ 0`
and `g ∉ ℘(K)`, every height-one prime `x` containing `sAS2 a b g` but *not* `fwVecAS2 a b g 0` (the
"residual" branch of the ruling, as opposed to the "junk" branch) has residue field
`K`-isomorphic to the fraction field of the coordinate ring of the residual curve
`K[X₀,X₁,X₂] / √(ZIAS a b g)`.

The proof is the generic `a * b ≠ 0` assembly of `Work.MotC5N3.ASRulingMainV2Hab`, with the three
currently-open inputs supplied by the modules
`Work.MotC5N3.RulingX2.X2_notMem_radical_generic` (`X 2 ∉ √(ZIAS a b g)`, giving `ε ≠ 0`),
`Work.MotC5N3.RulingCert.ASrulTheta_sAS2_gen` (`θ (sAS2 a b g) = 0`) and
`Work.MotC5N3.ASrulTheta_rangeClosure` (the range closure, through
`Work.MotAS.ASRulV3.rangeClosureAS`), and with the kernel
computation taken from the proved `Work.MotC5N3.ASrulTheta_ker_le`. -/
theorem K5Ruling (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hab : a * b ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g)
    (x : Work.MotA.polySpec K 3) (hcoh : Order.coheight x = 1)
    (hx : Work.MotAS.sAS2 a b g ∈ x.asIdeal)
    (hfw : Work.MotAS.fwVecAS2 a b g 0 ∉ x.asIdeal)
    (hDZ : IsDomain (MvPolynomial (Fin 3) K ⧸
      Ideal.radical (Work.MotAS.ZIAS a b g))) :
    Nonempty (Work.MotV.resF K x ≃ₐ[K]
      FractionRing (Polynomial (MvPolynomial (Fin 3) K ⧸
        Ideal.radical (Work.MotAS.ZIAS a b g)))) := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  haveI hxp : x.asIdeal.IsPrime := x.isPrime
  have ha0 : a ≠ 0 := fun h => hab (by rw [h, zero_mul])
  have hb0 : b ≠ 0 := fun h => hab (by rw [h, mul_zero])
  have h2ab : 2 * a - b ≠ 0 := by
    intro h
    apply ha
    have e : a ^ 2 - a * b - b ^ 2 = (3 * a + b) * (2 * a - b) - 5 * a ^ 2 := by ring
    rw [e, h, h5]
    first | refl_ring1 | ring
  have hb2a : b ≠ 2 * a := (sub_ne_zero.mp h2ab).symm
  have hg0 : g ≠ 0 := fun h => hg ⟨0, by rw [h]; ring⟩
  have ha2b : a + 2 * b ≠ 0 := by
    intro h
    apply ha
    have e : a ^ 2 - a * b - b ^ 2 = (a + 2 * b) * (a - 3 * b) + 5 * b ^ 2 := by ring
    rw [e, h, h5]
    first | refl_ring1 | ring
  haveI hDZ' : IsDomain (Work.MotC5N3.ASrulA a b g) := hDZ
  -- ## the normalising element `ε = ASrulEpsA a b g` is nonzero, from `X 2 ∉ √(ZIAS a b g)`
  have hε : Work.MotC5N3.ASrulEpsA a b g ≠ 0 := by
    have hX2 : (MvPolynomial.X 2 : MvPolynomial (Fin 3) K) ∉
        Ideal.radical (Work.MotAS.ZIAS a b g) :=
      Work.MotC5N3.RulingX2.X2_notMem_radical_generic K a b g ha hab hg
    have hmkX2 : Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g))
        (MvPolynomial.X 2 : MvPolynomial (Fin 3) K) ≠ 0 := fun h0 =>
      hX2 (Ideal.Quotient.eq_zero_iff_mem.mp h0)
    have h4 : Work.MotAS.ASRul.kbRw a b g 4
        = MvPolynomial.C (a + 2 * b) ^ 2 * MvPolynomial.C (2 * a - b)
            * (MvPolynomial.X 2) ^ 2 := by
      simp only [Work.MotAS.ASRul.kbRw, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
    rw [Work.MotC5N3.ASrulEpsA, h4]
    simp only [map_mul, map_pow]
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ?_) ?_) (pow_ne_zero 2 hmkX2)
    · intro h0
      have h1 : (algebraMap K (Work.MotC5N3.ASrulA a b g) (a + 2 * b)) = 0 := by
        simpa only [MvPolynomial.C_eq_algebraMap, Ideal.Quotient.mk_algebraMap] using h0
      exact ha2b ((algebraMap K (Work.MotC5N3.ASrulA a b g)).injective (by rw [h1, map_zero]))
    · intro h0
      have h1 : (algebraMap K (Work.MotC5N3.ASrulA a b g) (2 * a - b)) = 0 := by
        simpa only [MvPolynomial.C_eq_algebraMap, Ideal.Quotient.mk_algebraMap] using h0
      exact h2ab ((algebraMap K (Work.MotC5N3.ASrulA a b g)).injective (by rw [h1, map_zero]))
  -- ## the four ingredients
  have hsAS2ne : Work.MotAS.sAS2 a b g ≠ 0 := Work.MotC5N3.sAS2_ne_zero_gen K a b g ha
  have h3 : Work.MotAS.fwVecAS2 a b g 3 ∉ x.asIdeal :=
    Work.MotC5N3.fwVecAS2_three_notMem_x_gen K a b g ha hg x hcoh hx
  have hsAS2mem : Work.MotAS.sAS2 a b g ∈ RingHom.ker (Work.MotC5N3.ASrulTheta a b g hDZ) :=
    RingHom.mem_ker.mpr (Work.MotC5N3.RulingCert.ASrulTheta_sAS2_gen K a b g hDZ hε ha0 hb0 hb2a hg0)
  have hker_le : RingHom.ker (Work.MotC5N3.ASrulTheta a b g hDZ) ≤ x.asIdeal :=
    Work.MotC5N3.ASrulTheta_ker_le K a b g hDZ hε ha hab hg x hcoh hx hfw h3
  have hθ0 : Work.MotC5N3.ASrulTheta a b g hDZ (Work.MotAS.fwVecAS2 a b g 0) ≠ 0 :=
    fun h0 => hfw (hker_le (RingHom.mem_ker.mpr h0))
  -- ## the kernel is `x`
  haveI hdomL : IsDomain
      (Localization.Away (Polynomial.C (Work.MotC5N3.ASrulEpsA a b g))) :=
    IsLocalization.isDomain_localization
      (M := Submonoid.powers (Polynomial.C (Work.MotC5N3.ASrulEpsA a b g)))
      (Submonoid.powers_le.mpr
        (mem_nonZeroDivisors_iff_ne_zero.mpr (Polynomial.C_ne_zero.mpr hε)))
  haveI hprim : (RingHom.ker (Work.MotC5N3.ASrulTheta a b g hDZ)).IsPrime :=
    RingHom.ker_isPrime _
  have hheight : x.asIdeal.height = 1 :=
    (AlgebraicGeometry.idealHeight_eq_coheight (CommRingCat.of (MvPolynomial (Fin 3) K)) x).trans
      hcoh
  have hker_theta : RingHom.ker (Work.MotC5N3.ASrulTheta a b g hDZ) = x.asIdeal := by
    have hqne : RingHom.ker (Work.MotC5N3.ASrulTheta a b g hDZ) ≠ ⊥ := by
      intro hbot
      exact hsAS2ne (Ideal.mem_bot.mp (hbot ▸ hsAS2mem))
    have hqht : ((1 : ℕ) : ℕ∞) ≤ (RingHom.ker (Work.MotC5N3.ASrulTheta a b g hDZ)).height := by
      have hb : (⊥ : Ideal (MvPolynomial (Fin 3) K)) <
          RingHom.ker (Work.MotC5N3.ASrulTheta a b g hDZ) := bot_lt_iff_ne_bot.mpr hqne
      have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hb
      rwa [Ideal.height_bot, zero_add] at h1
    by_contra hne
    have hlt : RingHom.ker (Work.MotC5N3.ASrulTheta a b g hDZ) < x.asIdeal :=
      lt_of_le_of_ne hker_le hne
    have h1 : (RingHom.ker (Work.MotC5N3.ASrulTheta a b g hDZ)).height + 1 ≤ x.asIdeal.height :=
      Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rw [hheight] at h1
    have h2 : ((1 : ℕ) : ℕ∞) + 1 ≤ ((1 : ℕ) : ℕ∞) := le_trans (add_le_add hqht le_rfl) h1
    exact absurd h2 (by decide)
  -- ## assembly
  obtain ⟨e1⟩ : Nonempty (Work.MotV.resF K x ≃ₐ[K]
      FractionRing (Work.MotC5N3.ASrulTheta a b g hDZ).range) := by
    refine ⟨?_⟩
    show FractionRing (MvPolynomial (Fin 3) K ⧸ x.asIdeal) ≃ₐ[K]
      FractionRing (Work.MotC5N3.ASrulTheta a b g hDZ).range
    rw [show x.asIdeal = RingHom.ker (Work.MotC5N3.ASrulTheta a b g hDZ) from hker_theta.symm]
    refine IsFractionRing.algEquivOfAlgEquiv (R := K)
      (A := MvPolynomial (Fin 3) K ⧸
        RingHom.ker (Work.MotC5N3.ASrulTheta a b g hDZ))
      (B := ↥(Work.MotC5N3.ASrulTheta a b g hDZ).range) ?_
    exact (AlgHom.ker_rangeRestrict (Work.MotC5N3.ASrulTheta a b g hDZ)).symm ▸
      Ideal.quotientKerAlgEquivOfSurjective
        (AlgHom.rangeRestrict_surjective (Work.MotC5N3.ASrulTheta a b g hDZ))
  obtain ⟨e2⟩ := Work.MotC5N3.ASrulTheta_rangeClosure K a b g hDZ hε ha0 hb0 hb2a hg0 hθ0
  exact ⟨e1.trans e2⟩

end Work.MotC5N3
