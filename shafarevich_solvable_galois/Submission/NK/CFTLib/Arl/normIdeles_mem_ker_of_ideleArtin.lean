import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.CFTLib.Arl.artinSym_normIdeleHom_ideleOfPrime_eq_one
import Submission.NK.CFTLib.Arl.artinSym_spanSingleton_eq_one_of_mem_congruence
import Submission.NK.CFTLib.Arl.exists_monoidHom_ideleArtin
import Submission.NK.CFTLib.ArtinReciprocityIdeal.Conductor
import Submission.NK.CFTLib.ArtinReciprocityIdeal.frobAtPrime_prod_relNorm_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The idèlic Artin map kills the idèlic norms

Let `L / K` be a finite abelian extension of number fields, `M > 0` a modulus such that every prime
of `K` not dividing `(M)` is unramified in `L`, and assume the ideal-theoretic Artin reciprocity law
at modulus `M` (`NK.CFTLib.artinKillsPrincipal K L M`).  For a congruence subgroup `U ≤ 𝕀 K` of
modulus `M` and an adjustment `hadj`, the idèlic Artin map is

`ideleArtin x = artinSym (idealOf (x · bₓ)),  x · bₓ ∈ U`.

The main result is that it kills the idèlic norms:

* `NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin`:
  `ideleArtin (N_{L/K} y) = 1` for every `y ∈ 𝕀 L`.

The proof has three parts.

* The reciprocity law makes `ideleArtin` multiplicative and trivial on the principal idèles
  (`Crux`, from `artinSym_spanSingleton_eq_one_of_mem_congruence`).
* Adjusting `y` inside `L` by a principal idèle puts `N_{L/K} y` into the congruence subgroup of
  `K` (`hadjN`); this makes `1` a valid adjustment, and the value of `ideleArtin` is a *function of
  the fractional ideal* of the adjusted norm idèle.
* `artinSym_idealOf_normIdeleHom_eq_one_of_mem` is the classical "Artin symbol kills norms"
  computation: the `𝔭`-adic exponent of `idealOf (N w)` is `∑_{𝔓 | 𝔭} f(𝔓|𝔭) · v_𝔓(w)`
  (`NK.CFTLib.Arl.exp_normIdeleHom_eq_sum_aux`).  At a prime `𝔭 | (M)` the congruence
  `N w ≡ 1 mod (M)` forces the exponent to vanish
  (`NK.CFTLib.Arl.exp_eq_zero_of_mem_congruence`), while at `𝔭 ∤ (M)` every `𝔓 | 𝔭` is
  unramified and the chosen Frobenius `Frob_𝔭` has order the inertia degree `f(𝔓|𝔭)`
  (`NK.Chebotarev.IsFrobAtOrderOfEqInertiaDeg`), so `Frob_𝔭 ^ (f(𝔓|𝔭) · v_𝔓(w)) = 1`.
  Hence every factor of the Artin symbol is `1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped NumberField RestrictedProduct nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.Arl

open NK.GlobalCFT

/-! ## The local unit at a prime of the modulus -/

/-- **Congruence to `1` modulo `(M)` at a prime `𝔮` makes the component a local unit.**

More precisely the `𝔮`-adic exponent of an idèle in the congruence subgroup of modulus `M`
vanishes at every prime `𝔮` containing `(M)`: the component is `≡ 1 mod (M)`, hence a unit. -/
theorem exp_eq_zero_of_mem_congruence {K : Type*} [Field K] [NumberField K]
    (M : ℕ) (U : Subgroup (Idele K))
    (hU : NK.CFTLib.Arl.IsCongruenceSubgroup (K := K) M U)
    (x : Idele K) (hx : x ∈ U)
    (𝔮 : HeightOneSpectrum (𝓞 K)) (h𝔮 : (M : 𝓞 K) ∈ 𝔮.asIdeal) :
    Idele.exp 𝔮 x = 0 := by
  have hcong := ((hU.1 x).mp hx).1 𝔮 h𝔮
  have hlt : Valued.v (R := 𝔮.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (((x (Place.ofFinite 𝔮)) : 𝔮.adicCompletion K) - 1) < 1 :=
    lt_of_le_of_lt hcong (val_natCast_lt_one 𝔮 M h𝔮)
  have hval : Valued.v (R := 𝔮.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (((x (Place.ofFinite 𝔮)) : 𝔮.adicCompletion K)) = 1 := by
    have h := Valuation.map_add_eq_of_lt_left
      (v := Valued.v (R := 𝔮.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)))
      (x := (1 : 𝔮.adicCompletion K))
      (y := ((x (Place.ofFinite 𝔮)) : 𝔮.adicCompletion K) - 1) (by simpa using hlt)
    rw [map_one, show (1 : 𝔮.adicCompletion K) +
      (((x (Place.ofFinite 𝔮)) : 𝔮.adicCompletion K) - 1) =
        ((x (Place.ofFinite 𝔮)) : 𝔮.adicCompletion K) from by ring] at h
    exact h
  have hmem : x (Place.ofFinite 𝔮) ∈ Place.localUnits K (Place.ofFinite 𝔮) :=
    (Place.mem_localUnits_ofFinite_iff_valued_eq_one).mpr hval
  exact Idele.exp_eq_zero_of_mem_localUnits hmem

/-! ## A power of one element over a finite integer sum -/

/-- Powers of one element add over a finite sum of integer exponents: if `x ^ (f i) = 1` for all
`i ∈ s` then `x ^ (∑ i ∈ s, f i) = 1`. -/
theorem zpow_sum_eq_one_of {G : Type*} [Group G] {ι : Type*} (x : G) (s : Finset ι) (f : ι → ℤ)
    (h : ∀ i ∈ s, x ^ (f i) = 1) : x ^ (∑ i ∈ s, f i) = 1 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, zpow_add, h a (Finset.mem_insert_self a s), one_mul]
      exact ih fun i hi => h i (Finset.mem_insert_of_mem hi)

/-! ## The Artin symbol of a norm ideal -/

/-- **The Artin symbol kills the ideal of an idèlic norm which is congruent to `1` modulo `(M)`.**

Let `L / K` be a finite abelian extension of number fields, `M > 0` a modulus such that every prime
of `K` not dividing `(M)` is unramified in `L`, `U` a congruence subgroup of modulus `M`, and
`w ∈ 𝕀 L` an idèle whose norm `N_{L/K} w` lies in `U`.  Then the Artin symbol of the fractional
ideal of `N_{L/K} w` is trivial.

Indeed the `𝔭`-adic exponent of that ideal is `∑_{𝔓 | 𝔭} f(𝔓|𝔭) · v_𝔓(w)`.  At a prime `𝔭 | (M)`
the congruence `N w ≡ 1 mod (M)` forces the exponent to vanish; at `𝔭 ∤ (M)` the prime `𝔭` is
unramified, the Artin symbol of `𝔭` has order the inertia degree `f(𝔓|𝔭)`, and the Frobenius
factor is trivial. -/
theorem artinSym_idealOf_normIdeleHom_eq_one_of_mem {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a) (M : ℕ) (hM : 0 < M)
    (hramM : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (M : 𝓞 K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) = 1)
    (U : Subgroup (Idele K))
    (hU : NK.CFTLib.Arl.IsCongruenceSubgroup (K := K) M U)
    (w : Idele L) (hw : Idele.normIdeleHom K L w ∈ U) :
    artinSym (K := K) (L := L) hcomm
      (Idele.idealOf (Idele.normIdeleHom K L w)) = 1 := by
  classical
  letI := galCommMonoid hcomm
  -- unramifiedness of the primes above `𝔭 ∤ (M)`, in terms of `ramificationIdx`
  have hunr : ∀ (𝔭 : HeightOneSpectrum (𝓞 K)), (M : 𝓞 K) ∉ 𝔭.asIdeal →
      ∀ 𝔓 : HeightOneSpectrum (𝓞 L), 𝔓.asIdeal.LiesOver 𝔭.asIdeal →
        𝔓.asIdeal.ramificationIdx (𝓞 K) = 1 := by
    intro 𝔭 h𝔭 𝔓 h𝔓
    letI hMSA : MulSemiringAction (Gal(L/K)) (𝓞 L) :=
      IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
    haveI hGG : IsGaloisGroup (Gal(L/K)) (𝓞 K) (𝓞 L) :=
      IsGaloisGroup.of_isFractionRing (Gal(L/K)) (𝓞 K) (𝓞 L) K L
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 K) (B := 𝓞 L) 𝔭.asIdeal 𝔓.asIdeal
      (Gal(L/K))]
    exact hramM 𝔭 h𝔭
  -- the exponent vector of the ideal of the idèlic norm
  have hcount : ∀ 𝔭 : HeightOneSpectrum (𝓞 K),
      exps (Idele.idealOf (Idele.normIdeleHom K L w)) 𝔭
        = ∑ 𝔓 ∈ Place.primesOverFinite (K := K) (L := L) 𝔭,
            ((𝔓.asIdeal.inertiaDeg (𝓞 K) : ℤ) * FractionalIdeal.count L 𝔓 (Idele.idealOf w)) := by
    intro 𝔭
    rw [exps_apply, Idele.count_idealOf, NK.CFTLib.Arl.exp_normIdeleHom_eq_sum_aux K L w 𝔭]
    exact Finset.sum_congr rfl fun 𝔓 _ => by rw [Idele.count_idealOf]
  -- each Frobenius power occurring in the Artin symbol is trivial
  have hterm : ∀ 𝔭 : HeightOneSpectrum (𝓞 K),
      (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭)
        ^ (exps (Idele.idealOf (Idele.normIdeleHom K L w)) 𝔭) = 1 := by
    intro 𝔭
    by_cases h𝔭 : (M : 𝓞 K) ∈ 𝔭.asIdeal
    · -- `𝔭 | (M)`: the exponent vanishes
      rw [exps_apply, Idele.count_idealOf,
        exp_eq_zero_of_mem_congruence M U hU (Idele.normIdeleHom K L w) hw 𝔭 h𝔭, zpow_zero]
    · -- `𝔭 ∤ (M)`: unramified, and the Frobenius has order the inertia degree
      rw [hcount 𝔭]
      refine zpow_sum_eq_one_of _ _ _ fun 𝔓 h𝔓 => ?_
      have hLies : 𝔓.asIdeal.LiesOver 𝔭.asIdeal :=
        (Place.mem_primesOverFinite (K := K) (L := L) (Q := 𝔭) (q := 𝔓)).mp h𝔓
      obtain ⟨P, hP, hPFrob⟩ := NK.Chebotarev.isFrobAtPrime_frobAtPrime hcomm 𝔭
        (fun 𝔓 h => hunr 𝔭 h𝔭 𝔓 h)
      have hfrob : NK.Chebotarev.IsFrobAt 𝔓
          (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) :=
        isFrobAt_of_isFrobAt_any_primeOver hcomm hP hLies hPFrob
      have horder : orderOf (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭)
          = 𝔓.asIdeal.inertiaDeg (𝓞 K) :=
        NK.Chebotarev.IsFrobAtOrderOfEqInertiaDeg hLies (hunr 𝔭 h𝔭 𝔓 hLies) hfrob
      rw [zpow_mul, zpow_natCast, ← horder, pow_orderOf_eq_one, one_zpow]
  -- the Artin symbol is the product of these powers
  have hprod : (exps (Idele.idealOf (Idele.normIdeleHom K L w))).prod
      (fun (𝔭 : HeightOneSpectrum (𝓞 K)) (e : ℤ) =>
        (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) ^ e) = 1 := by
    rw [Finsupp.prod_congr (f := exps (Idele.idealOf (Idele.normIdeleHom K L w)))
      (g1 := fun (𝔭 : HeightOneSpectrum (𝓞 K)) (e : ℤ) =>
        (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) ^ e)
      (g2 := fun (_ : HeightOneSpectrum (𝓞 K)) (_ : ℤ) => (1 : Gal(L/K)))
      (fun 𝔭 _ => hterm 𝔭)]
    rw [Finsupp.prod_of_support_subset (exps (Idele.idealOf (Idele.normIdeleHom K L w)))
      (fun _ h => h) (fun (_ : HeightOneSpectrum (𝓞 K)) (_ : ℤ) => (1 : Gal(L/K)))
      (fun _ _ => rfl)]
    exact Finset.prod_eq_one fun _ _ => rfl
  unfold artinSym
  exact hprod

/-! ## The main theorem -/

/-- **The idèlic Artin map kills the idèlic norms.**  Let `L / K` be a finite abelian extension of
number fields, `M > 0` a modulus whose support contains the ramified primes, `hprincM` the
ideal-theoretic reciprocity law at modulus `M`, `U ≤ 𝕀 K` a congruence subgroup of modulus `M`
with adjustment `hadj`, and assume that every norm idèle can be adjusted by a principal idèle into
`U` (`hadjN`).  Then the idèlic Artin map `ideleArtin` kills `N_{L/K} y` for every `y ∈ 𝕀 L`. -/
theorem normIdeles_mem_ker_of_ideleArtin {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a) (M : ℕ) (hM : 0 < M)
    (hramM : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (M : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprincM : NK.CFTLib.artinKillsPrincipal K L M)
    (U : Subgroup (NK.GlobalCFT.Idele K))
    (hU : NK.CFTLib.Arl.IsCongruenceSubgroup (K := K) M U)
    (hadj : ∀ x : NK.GlobalCFT.Idele K, ∃ b : Kˣ,
      x * NK.GlobalCFT.Idele.principalIdele K b ∈ U)
    (hadjN : ∀ y : NK.GlobalCFT.Idele L, ∃ d : Lˣ,
      NK.GlobalCFT.Idele.normIdeleHom K L
        (y * NK.GlobalCFT.Idele.principalIdele L d) ∈ U)
    (y : NK.GlobalCFT.Idele L) :
    NK.CFTLib.Arl.ideleArtin (K := K) (L := L) hcomm U hadj
      (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1 := by
  classical
  -- the reciprocity law in idèlic form: `artinSym` kills the principal idèles of `U`
  have hcrux : Crux (K := K) (L := L) hcomm U := fun b hb =>
    artinSym_spanSingleton_eq_one_of_mem_congruence (K := K) (L := L) hcomm M hM hramM hprincM
      U hU b hb
  -- the adjustments
  obtain ⟨e, he⟩ := hadjN y
  have hb : Idele.normIdeleHom K L y
      * Idele.principalIdele K (adjust U hadj (Idele.normIdeleHom K L y)) ∈ U :=
    adjust_spec U hadj _
  -- the two adjusted idèles differ by the principal idèle `c`
  set c : Kˣ := adjust U hadj (Idele.normIdeleHom K L y)
    * (Units.map (Algebra.norm K) e)⁻¹ with hc
  have hid : Idele.normIdeleHom K L y
        * Idele.principalIdele K (adjust U hadj (Idele.normIdeleHom K L y))
      = Idele.normIdeleHom K L (y * Idele.principalIdele L e) * Idele.principalIdele K c := by
    rw [map_mul, Idele.normIdeleHom_principalIdele, hc, map_mul, map_inv]
    rw [mul_assoc, mul_left_comm (Idele.principalIdele K (Units.map (Algebra.norm K) e))
      (Idele.principalIdele K (adjust U hadj (Idele.normIdeleHom K L y))), mul_inv_cancel, mul_one]
  have hcU : Idele.principalIdele K c ∈ U := by
    have h1 : (Idele.normIdeleHom K L y
        * Idele.principalIdele K (adjust U hadj (Idele.normIdeleHom K L y)))
        * (Idele.normIdeleHom K L (y * Idele.principalIdele L e))⁻¹ ∈ U :=
      U.mul_mem hb (U.inv_mem he)
    have h2 : (Idele.normIdeleHom K L y
        * Idele.principalIdele K (adjust U hadj (Idele.normIdeleHom K L y)))
        * (Idele.normIdeleHom K L (y * Idele.principalIdele L e))⁻¹
        = Idele.principalIdele K c := by
      rw [hid]
      rw [mul_comm (Idele.normIdeleHom K L (y * Idele.principalIdele L e))
          (Idele.principalIdele K c),
        mul_assoc, mul_inv_cancel, mul_one]
    rwa [h2] at h1
  -- the Artin symbol of the adjusted norm is trivial
  have hkey : artinSym (K := K) (L := L) hcomm
      (Idele.idealOf (Idele.normIdeleHom K L (y * Idele.principalIdele L e))) = 1 :=
    artinSym_idealOf_normIdeleHom_eq_one_of_mem (K := K) (L := L) hcomm M hM hramM U hU _ he
  calc ideleArtin (K := K) (L := L) hcomm U hadj (Idele.normIdeleHom K L y)
      = artinSym (K := K) (L := L) hcomm
          (Idele.idealOf (Idele.normIdeleHom K L y
            * Idele.principalIdele K (adjust U hadj (Idele.normIdeleHom K L y)))) := rfl
    _ = artinSym (K := K) (L := L) hcomm
          (Idele.idealOf (Idele.normIdeleHom K L (y * Idele.principalIdele L e))
            * FractionalIdeal.spanSingleton (𝓞 K)⁰ (c : K)) := by
        rw [hid, Idele.idealOf_mul, Idele.idealOf_principalIdele]
    _ = artinSym (K := K) (L := L) hcomm
          (Idele.idealOf (Idele.normIdeleHom K L (y * Idele.principalIdele L e)))
        * artinSym (K := K) (L := L) hcomm
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ (c : K)) :=
        artinSym_mul (K := K) (L := L) hcomm (Idele.idealOf_ne_zero _)
          (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero c))
    _ = 1 := by rw [hkey, hcrux c hcU, mul_one]

end NK.CFTLib.Arl
