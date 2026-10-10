import Mathlib
import Submission.Work.MotK.TGen.ZpgPsiDefs
import Submission.Work.MotK.TGen.ZpgPsiKillAll
import Submission.Work.MotK.TGen.ZpgWbarNeZero
import Submission.Work.MotK.TGen.ZpgEIrreducible
import Submission.Work.MotK.TGen.ZTwistDivGeomCerts
import Submission.Work.MotK.TGen.ZpgI4SatW
import Submission.Work.MotK.TGen.KerZpgPsiSat

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# `Work.MotK.TGen.ZTwistChartFracMain`

The assembly of `Work.MotK.TGen.ZTwistChartFrac` (see `NOTE_ZTwistChartFracMain_route.md`): the
chart `y₀ = 1` of the twisted Klein curve is birational to the plane model `V(zpgE a b h)`.

The inputs: `ZpgEIrreducible` (so `ZP = K[X₀,X₁]/(zpgE)` is a domain), `ZpgWbarNeZero`,
`ZpgPsiKillAll` (the graph map kills the five chart quadrics), and the two saturation statements
`KerZpgPsiSaturation` (the kernel of `zpgPsi` lies in the `zpgW4`-saturation of the chart ideal)
and `ZpgI4SatW` (that saturation lies in the radical).  Consequently
`ker zpgPsi = radical (zpgI4)`, and the assembly is the one of `ZPlaneModel`.
-/

set_option maxHeartbeats 4000000
set_option autoImplicit false

namespace Work.MotK.TGen

open MvPolynomial

/-- The embedding of the plane coordinates into the chart: `X₀ ↦ X 0`, `X₁ ↦ X 2`. -/
noncomputable def zpgEmb4 (K : Type) [Field K] : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 4) K :=
  MvPolynomial.aeval ![X 0, X 2]

theorem zpgEmb4_zpgE (K : Type) [Field K] (a b h : K) :
    zpgEmb4 K (zpgE a b h) = zpgE4 a b h := by
  simp only [zpgEmb4, zpgE, zpgE4, MvPolynomial.aeval_X, MvPolynomial.aeval_C, map_add, map_sub,
    map_mul, map_pow, map_neg, map_ofNat, MvPolynomial.algebraMap_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one]

theorem ZTwistChartFracMain (K : Type) [Field K] (a b h : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0)
    (hirr : Irreducible (Work.MotK.TwCensus.ZElim2 a b h)) :
    Nonempty (FractionRing (MvPolynomial (Fin 4) K ⧸
        Ideal.radical (Work.MotK.TGen.zpgI4 a b h)) ≃ₐ[K]
      FractionRing (MvPolynomial (Fin 2) K ⧸ Ideal.span {Work.MotK.TGen.zpgE a b h})) := by
  classical
  -- `zpgE` is irreducible and nonzero, so `ZP` is a domain
  have hEne : zpgE a b h ≠ 0 := by
    intro h0
    have hc : MvPolynomial.constantCoeff (zpgE a b h) = 0 := by rw [h0, map_zero]
    rw [zpgE] at hc
    simp only [map_add, map_mul, map_pow, MvPolynomial.constantCoeff_C,
      MvPolynomial.constantCoeff_X] at hc
    exact (mul_ne_zero (pow_ne_zero 3 ha) (pow_ne_zero 6 hb)) (by simpa using hc)
  have hzE : Irreducible (zpgE a b h) := ZpgEIrreducible K a b h ha hb hh hirr
  have hprime : (Ideal.span {zpgE a b h}).IsPrime :=
    (Ideal.span_singleton_prime hEne).mpr (UniqueFactorizationMonoid.irreducible_iff_prime.mp hzE)
  haveI hdomA : IsDomain (ZP K a b h) := Ideal.Quotient.isDomain _
  -- the image of `W` in `ZPF` is nonzero
  have hW : algebraMap (MvPolynomial (Fin 2) K) (ZPF K a b h) (zpgW a b h) ≠ 0 := by
    intro hz
    have hz' : algebraMap (ZP K a b h) (ZPF K a b h)
        (algebraMap (MvPolynomial (Fin 2) K) (ZP K a b h) (zpgW a b h)) = 0 := hz
    have h0 : algebraMap (MvPolynomial (Fin 2) K) (ZP K a b h) (zpgW a b h) = 0 :=
      IsFractionRing.injective (ZP K a b h) (ZPF K a b h) (by rw [map_zero]; exact hz')
    exact ZpgWbarNeZero K a b h hb (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  have hWbar : zpgWbar K a b h ≠ 0 := by
    rw [zpgWbar_eq_algebraMap]; exact hW
  -- the two inclusions computing `ker zpgPsi`
  have hI_le : zpgI4 a b h ≤ RingHom.ker (zpgPsi K a b h) := by
    rw [zpgI4, Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    exact ZpgPsiKillAll K a b h ha hb hh hW k
  have hker_le : RingHom.ker (zpgPsi K a b h) ≤ Ideal.radical (zpgI4 a b h) := by
    intro u hu
    exact ZpgI4SatW K a b h ha hb hh u (KerZpgPsiSat K a b h ha hb hh hWbar u hu)
  have hker_ge : Ideal.radical (zpgI4 a b h) ≤ RingHom.ker (zpgPsi K a b h) := by
    intro x hx
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hx
    exact (RingHom.ker_isPrime (zpgPsi K a b h)).mem_of_pow_mem n (hI_le hn)
  have hker : RingHom.ker (zpgPsi K a b h) = Ideal.radical (zpgI4 a b h) :=
    le_antisymm hker_le hker_ge
  have hpr : (Ideal.radical (zpgI4 a b h)).IsPrime :=
    hker ▸ RingHom.ker_isPrime (zpgPsi K a b h)
  haveI hdomR : IsDomain (MvPolynomial (Fin 4) K ⧸ Ideal.radical (zpgI4 a b h)) :=
    Ideal.Quotient.isDomain _
  refine ⟨?_⟩
  let R := MvPolynomial (Fin 4) K ⧸ Ideal.radical (zpgI4 a b h)
  let Φ : R →ₐ[K] ZPF K a b h :=
    Ideal.Quotient.liftₐ _ (zpgPsi K a b h) (fun x hx => by
      have h1 : x ∈ RingHom.ker (zpgPsi K a b h) := hker.symm ▸ hx
      exact (RingHom.mem_ker (f := zpgPsi K a b h)).mp h1)
  have hΦmk : ∀ f : MvPolynomial (Fin 4) K, Φ (Ideal.Quotient.mk _ f) = zpgPsi K a b h f := by
    intro f
    change (Ideal.Quotient.lift (Ideal.radical (zpgI4 a b h))
      (↑(zpgPsi K a b h) : MvPolynomial (Fin 4) K →+* ZPF K a b h) _)
        (Ideal.Quotient.mk _ f) = (zpgPsi K a b h) f
    rfl
  have hΦinj : Function.Injective Φ := by
    intro x y hxy
    obtain ⟨fx, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨fy, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hΦmk, hΦmk] at hxy
    have hmem : fx - fy ∈ Ideal.radical (zpgI4 a b h) := by
      rw [← hker, RingHom.mem_ker, map_sub, hxy, sub_self]
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  let e : FractionRing R →ₐ[K] ZPF K a b h :=
    IsFractionRing.liftAlgHom (R := K) (A := R) (K := FractionRing R) (L := ZPF K a b h)
      (g := Φ) hΦinj
  have he_apply : ∀ x : R, e (algebraMap R (FractionRing R) x) = Φ x := fun x =>
    IsFractionRing.lift_algebraMap hΦinj x
  have hinj_e : Function.Injective ⇑e := by
    intro x y hxy
    have hmem : x - y ∈ RingHom.ker e := by
      rw [RingHom.mem_ker, map_sub, hxy, sub_self]
    have hbot : RingHom.ker e = ⊥ := by
      rcases Ideal.eq_bot_or_top (RingHom.ker e) with h' | h'
      · exact h'
      · exfalso
        have h1 : (1 : FractionRing R) ∈ RingHom.ker e := by rw [h']; trivial
        exact one_ne_zero (by rw [← map_one e]; exact RingHom.mem_ker.mp h1)
    rw [hbot] at hmem
    exact sub_eq_zero.mp hmem
  -- the composite `ZP → R → ZPF` is the structure map
  let f₀ : MvPolynomial (Fin 2) K →ₐ[K] R :=
    (Ideal.Quotient.mkₐ K (Ideal.radical (zpgI4 a b h))).comp (zpgEmb4 K)
  have hf₀ : f₀ (zpgE a b h) = 0 := by
    have h1 : f₀ (zpgE a b h) = Ideal.Quotient.mk _ (zpgE4 a b h) := by
      simp only [f₀, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, zpgEmb4_zpgE]
    rw [h1, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.le_radical (ZTwistDivGeomCerts K a b h).2.1
  let Φ₀ : ZP K a b h →ₐ[K] R :=
    Ideal.Quotient.liftₐ (Ideal.span {zpgE a b h}) f₀ (by
      intro x hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hx
      rw [map_mul, hf₀, zero_mul])
  have hψemb : ∀ p : MvPolynomial (Fin 2) K,
      zpgPsi K a b h (zpgEmb4 K p)
        = algebraMap (ZP K a b h) (ZPF K a b h) (Ideal.Quotient.mk _ p) := by
    intro p
    have hhom : (zpgPsi K a b h).comp (zpgEmb4 K)
        = (IsScalarTower.toAlgHom K (ZP K a b h) (ZPF K a b h)).comp
            (Ideal.Quotient.mkₐ K (Ideal.span {zpgE a b h})) := by
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i
      · simp [zpgEmb4, zpgx]
      · simp [zpgEmb4, zpgz]
    exact congrArg (fun g : MvPolynomial (Fin 2) K →ₐ[K] ZPF K a b h => g p) hhom
  have hΦemb : ∀ p : MvPolynomial (Fin 2) K,
      Φ (Φ₀ (Ideal.Quotient.mk _ p))
        = algebraMap (ZP K a b h) (ZPF K a b h) (Ideal.Quotient.mk _ p) := by
    intro p
    have h1 : Φ₀ (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (zpgEmb4 K p) := rfl
    rw [h1, hΦmk, hψemb p]
  have hsurj_e : Function.Surjective ⇑e := by
    intro z
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors (ZP K a b h)) z
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨q, hq⟩ := Ideal.Quotient.mk_surjective (s : ZP K a b h)
    have hsq : algebraMap (ZP K a b h) (ZPF K a b h) (s : ZP K a b h) ≠ 0 := by
      intro h0
      have hs0 : (s : ZP K a b h) = 0 :=
        IsFractionRing.injective (ZP K a b h) (ZPF K a b h) (by rw [h0, map_zero])
      exact one_ne_zero ((mem_nonZeroDivisors_iff.mp s.2).1 (1 : ZP K a b h) (by rw [hs0, zero_mul]))
    refine ⟨algebraMap R (FractionRing R) (Φ₀ (Ideal.Quotient.mk _ p))
      * (algebraMap R (FractionRing R) (Φ₀ (Ideal.Quotient.mk _ q)))⁻¹, ?_⟩
    have hY1 : e (algebraMap R (FractionRing R) (Φ₀ (Ideal.Quotient.mk _ p)))
        = algebraMap (ZP K a b h) (ZPF K a b h) x := by
      rw [he_apply, hΦemb, hp]
    have hY2 : e (algebraMap R (FractionRing R) (Φ₀ (Ideal.Quotient.mk _ q)))
        = algebraMap (ZP K a b h) (ZPF K a b h) (s : ZP K a b h) := by
      rw [he_apply, hΦemb, hq]
    have hY2ne : e (algebraMap R (FractionRing R) (Φ₀ (Ideal.Quotient.mk _ q))) ≠ 0 := by
      rw [hY2]; exact hsq
    have hY2ne' : algebraMap R (FractionRing R) (Φ₀ (Ideal.Quotient.mk _ q)) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hY2ne
      exact hY2ne rfl
    have key : e (algebraMap R (FractionRing R) (Φ₀ (Ideal.Quotient.mk _ p))
          * (algebraMap R (FractionRing R) (Φ₀ (Ideal.Quotient.mk _ q)))⁻¹)
        * e (algebraMap R (FractionRing R) (Φ₀ (Ideal.Quotient.mk _ q)))
        = z * e (algebraMap R (FractionRing R) (Φ₀ (Ideal.Quotient.mk _ q))) := by
      rw [← map_mul, mul_assoc, inv_mul_cancel₀ hY2ne', mul_one, hY1, hY2, ← hs]
    exact mul_right_cancel₀ hY2ne key
  refine AlgEquiv.ofBijective e ?_
  exact ⟨hinj_e, hsurj_e⟩

end Work.MotK.TGen
