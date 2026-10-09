import Mathlib
import Submission.NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFT.Norm.globalCFT_localNorm_mem_localUnits
import Submission.NK.GlobalCFT.Norm.globalCFT_abs_normIdeleHom
import Submission.Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow

/-!
# The local–global principle for norms of idèles, without Galois hypotheses

For a finite extension `L / K` of number fields (no Galois hypothesis), the group of norms of
idèles `N_{L/K} 𝕀_L ≤ 𝕀_K` consists exactly of the idèles all of whose components are local norms.

The proof follows the Galois case (`NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm`), but the
step at a place `Q` of `K` where the extension is unramified and the idèle is a local unit cannot
use the surjectivity of the local norm on units (which is only available under a Galois
hypothesis).  Instead we use the following observation: if `q | Q` has ramification index one, the
image of a uniformiser `π_Q` of `K_Q` in `L_q` is a uniformiser of `L_q`, so the norm of a chosen
local preimage `z_q` can be adjusted by a power of `π_Q` with no error term:

  `z_q = u_q · (π_Q)^{m_q}` with `u_q ∈ 𝒪_qˣ` and `m_q = log v(z_q)`,

whence `N(z_q) = N(u_q) · π_Q^{m_q · f_q}`.  Summing over the fibre of `Q` and using
`v_Q(N z_q) = f_q · v_{L_q}(z_q)`, the exponents cancel (`∑_q m_q f_q = 0`), so the component
`x_Q = ∏_{q | Q} N(z_q)` is a product of norms of *local units*.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open scoped NumberField RestrictedProduct WithZero
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

attribute [local instance] Classical.propDecidable

noncomputable section

namespace NK.CFTLib.IdeleHasse

open NK.GlobalCFT
open NK.GlobalCFTdeep.SecondInequality.KummerCase

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-! ## The uniformiser of the completion at a finite place -/

/-- The Henselian uniformiser of the completion `K_Q` at a finite place `Q`, as a unit of `K_Q`. -/
noncomputable def unifUnit (Q : HeightOneSpectrum (𝓞 K)) : (Q.adicCompletion K)ˣ :=
  Units.mk0 (Commons.RingTheory.Henselian.uniformizer (R := 𝓞 K) (K := K) Q :
      Q.adicCompletion K)
    (by
      have h := Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one (K := K) Q
      intro h0
      rw [h0, map_zero] at h
      exact WithZero.exp_ne_zero h.symm)

theorem val_unifUnit (Q : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((unifUnit (K := K) Q : (Q.adicCompletion K)ˣ) : Q.adicCompletion K) =
      WithZero.exp (-1 : ℤ) := by
  rw [unifUnit, Units.val_mk0]
  exact Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one (K := K) Q

/-! ## The correction at a single place of `L` -/

/-- The exponent by which the chosen local preimage at `q` is adjusted: the logarithm of its
valuation. -/
noncomputable def unitExp (z : 𝕀[L]) (q : HeightOneSpectrum (𝓞 L)) : ℤ :=
  WithZero.log (Valued.v ((z (Place.ofFinite q) : (q.adicCompletion L)ˣ) : q.adicCompletion L))

/-- The chosen local preimage at `q` divided by the appropriate power of the image of the
uniformiser of `K_Q`: a local unit. -/
noncomputable def unitPartOf (z : 𝕀[L]) (Q : HeightOneSpectrum (𝓞 K))
    (q : HeightOneSpectrum (𝓞 L)) (hq : q.asIdeal.LiesOver Q.asIdeal) : (q.adicCompletion L)ˣ := by
  classical
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    (Commons.RingTheory.Henselian.adicCompletionMap Q q hq).toAlgebra
  exact z (Place.ofFinite q) *
    (Units.map (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom
      (unifUnit (K := K) Q)) ^ (unitExp z q)

/-- The value of the adjusted local preimage is a unit. -/
theorem val_unitPartOf (z : 𝕀[L]) (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (he : q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    Valued.v ((unitPartOf z Q q hq : (q.adicCompletion L)ˣ) : q.adicCompletion L) = 1 := by
  classical
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    (Commons.RingTheory.Henselian.adicCompletionMap Q q hq).toAlgebra
  have hvz : Valued.v ((z (Place.ofFinite q) : (q.adicCompletion L)ˣ) : q.adicCompletion L)
      = WithZero.exp (unitExp z q) := by
    rw [unitExp]
    exact (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr (Units.ne_zero _))).symm
  have hπ : Valued.v (algebraMap (Q.adicCompletion K) (q.adicCompletion L)
        ((unifUnit (K := K) Q : (Q.adicCompletion K)ˣ) : Q.adicCompletion K)) =
      WithZero.exp (-1 : ℤ) := by
    have halg : (algebraMap (Q.adicCompletion K) (q.adicCompletion L)) =
        Commons.RingTheory.Henselian.adicCompletionMap Q q hq := RingHom.algebraMap_toAlgebra _
    rw [halg, Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow Q q hq,
      val_unifUnit Q, he, pow_one]
  have hunit : ((unitPartOf z Q q hq : (q.adicCompletion L)ˣ) : q.adicCompletion L) =
      ((z (Place.ofFinite q) : (q.adicCompletion L)ˣ) : q.adicCompletion L) *
        ((Units.map (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom
          (unifUnit (K := K) Q) : (q.adicCompletion L)ˣ) : q.adicCompletion L) ^ (unitExp z q) := by
    rw [unitPartOf, Units.val_mul, Units.val_zpow_eq_zpow_val]
  have himg : ((Units.map (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom
        (unifUnit (K := K) Q) : (q.adicCompletion L)ˣ) : q.adicCompletion L) =
      algebraMap (Q.adicCompletion K) (q.adicCompletion L)
        ((unifUnit (K := K) Q : (Q.adicCompletion K)ˣ) : Q.adicCompletion K) := by
    rw [Units.coe_map]
    rfl
  rw [hunit, himg, Valuation.map_mul, map_zpow₀, hπ, hvz, ← WithZero.exp_zsmul,
    ← WithZero.exp_add, show unitExp z q + unitExp z q • (-1 : ℤ) = 0 by ring, WithZero.exp_zero]

/-- The adjusted local preimage is a local unit. -/
theorem unitPartOf_mem_localUnits (z : 𝕀[L]) (Q : HeightOneSpectrum (𝓞 K))
    (q : HeightOneSpectrum (𝓞 L)) (hq : q.asIdeal.LiesOver Q.asIdeal)
    (he : q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    unitPartOf z Q q hq ∈ Place.localUnits L (Place.ofFinite q) := by
  rw [Place.mem_localUnits_ofFinite_iff_valued_eq_one]
  exact val_unitPartOf z Q q hq he

/-! ## The auxiliary idèle attached to a finite place of `K` -/

/-- Values of the auxiliary idèle attached to a finite place `Q` of `K`: at a place of `L` above
`Q` the adjusted local preimage, and `1` elsewhere. -/
noncomputable def unitIdeleFun (z : 𝕀[L]) (Q : HeightOneSpectrum (𝓞 K)) :
    (w : Place L) → (Place.localField L w)ˣ :=
  fun w => match w with
    | Sum.inl _ => 1
    | Sum.inr q =>
        if hq : q.asIdeal.LiesOver Q.asIdeal then unitPartOf z Q q hq else 1

@[simp] theorem unitIdeleFun_ofInfinite (z : 𝕀[L]) (Q : HeightOneSpectrum (𝓞 K))
    (w : InfinitePlace L) : unitIdeleFun z Q (Place.ofInfinite w) = 1 := rfl

theorem unitIdeleFun_ofFinite (z : 𝕀[L]) (Q : HeightOneSpectrum (𝓞 K))
    (q : HeightOneSpectrum (𝓞 L)) :
    unitIdeleFun z Q (Place.ofFinite q) =
      (if hq : q.asIdeal.LiesOver Q.asIdeal then unitPartOf z Q q hq else 1) := rfl

/-- The auxiliary values are invariant under replacing `Q` by an equal place. -/
theorem unitIdeleFun_apply_eq_of_prime_eq {z : 𝕀[L]} {Q Q' : HeightOneSpectrum (𝓞 K)}
    (h : Q = Q') (w : Place L) : unitIdeleFun z Q w = unitIdeleFun z Q' w := by
  subst h
  rfl

/-- The auxiliary values are local units, provided the extension is unramified at all places
above `Q`. -/
theorem unitIdeleFun_mem_localUnits {z : 𝕀[L]} {Q : HeightOneSpectrum (𝓞 K)}
    (hunr : ∀ q : HeightOneSpectrum (𝓞 L), q.asIdeal.LiesOver Q.asIdeal →
      q.asIdeal.ramificationIdx (𝓞 K) = 1) (w : Place L) :
    unitIdeleFun z Q w ∈ Place.localUnits L w := by
  classical
  cases w with
  | inl w' => exact Subgroup.mem_top _
  | inr q =>
      by_cases hq : q.asIdeal.LiesOver Q.asIdeal
      · rw [unitIdeleFun_ofFinite, dif_pos hq]
        exact unitPartOf_mem_localUnits z Q q hq (hunr q hq)
      · rw [unitIdeleFun_ofFinite, dif_neg hq]
        exact Subgroup.one_mem _

/-- The auxiliary values form an idèle. -/
theorem unitIdeleFun_eventually_mem_localUnits {z : 𝕀[L]} {Q : HeightOneSpectrum (𝓞 K)}
    (hunr : ∀ q : HeightOneSpectrum (𝓞 L), q.asIdeal.LiesOver Q.asIdeal →
      q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    ∀ᶠ w in Filter.cofinite, unitIdeleFun z Q w ∈ Place.localUnits L w := by
  rw [Filter.eventually_cofinite]
  exact Set.finite_empty.subset (fun w hw => hw (unitIdeleFun_mem_localUnits hunr w))

/-- The auxiliary idèle attached to the finite place `Q`. -/
noncomputable def unitIdeleOf (z : 𝕀[L]) (Q : HeightOneSpectrum (𝓞 K))
    (hunr : ∀ q : HeightOneSpectrum (𝓞 L), q.asIdeal.LiesOver Q.asIdeal →
      q.asIdeal.ramificationIdx (𝓞 K) = 1) : 𝕀[L] :=
  ⟨unitIdeleFun z Q, unitIdeleFun_eventually_mem_localUnits hunr⟩

/-- A choice of a local preimage of `x` at every place of `K`, for a proof that `x` is locally a
norm everywhere. -/
noncomputable def preimageIdele (x : 𝕀[K])
    (h : ∀ v : Place K, ∃ y : 𝕀[L], x v = Idele.normIdeleFun K L y v) (v : Place K) : 𝕀[L] :=
  (h v).choose

theorem preimageIdele_spec (x : 𝕀[K])
    (h : ∀ v : Place K, ∃ y : 𝕀[L], x v = Idele.normIdeleFun K L y v) (v : Place K) :
    x v = Idele.normIdeleFun K L (preimageIdele x h v) v :=
  (h v).choose_spec

/-! ## The norm of the adjusted local preimage -/

/-- The norm of the adjusted local preimage is the norm of the chosen preimage times a power of
the base uniformiser. -/
theorem localNormFinite_unitPartOf (z : 𝕀[L]) (Q : HeightOneSpectrum (𝓞 K))
    (q : HeightOneSpectrum (𝓞 L)) (hq : q.asIdeal.LiesOver Q.asIdeal)
    (he : q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    Place.localNormFinite q Q hq (unitPartOf z Q q hq) =
      Place.localNormFinite q Q hq (z (Place.ofFinite q)) *
        (unifUnit (K := K) Q) ^ (unitExp z q * (q.asIdeal.inertiaDeg (𝓞 K) : ℤ)) := by
  classical
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    (Commons.RingTheory.Henselian.adicCompletionMap Q q hq).toAlgebra
  have hkey : ∀ x : (Q.adicCompletion K)ˣ,
      Place.localNormFinite q Q hq
          (Units.map (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom x) =
        x ^ (q.asIdeal.inertiaDeg (𝓞 K) : ℤ) := by
    intro x
    have hfr : Module.finrank (Q.adicCompletion K) (q.adicCompletion L) =
        q.asIdeal.inertiaDeg (𝓞 K) := by
      have h := Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
        Q q hq
      rw [he, one_mul] at h
      exact h.symm
    have hstep : Place.localNormFinite q Q hq
        (Units.map (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom x) =
        x ^ (Module.finrank (Q.adicCompletion K) (q.adicCompletion L) : ℤ) := by
      refine Units.ext ?_
      rw [Units.val_zpow_eq_zpow_val]
      show (Algebra.norm (Q.adicCompletion K)
          (algebraMap (Q.adicCompletion K) (q.adicCompletion L) (x : Q.adicCompletion K))) =
        (x : Q.adicCompletion K) ^ (Module.finrank (Q.adicCompletion K) (q.adicCompletion L) : ℤ)
      rw [Algebra.norm_algebraMap, zpow_natCast]
    rw [hstep, hfr]
  have hunit : unitPartOf z Q q hq =
      z (Place.ofFinite q) *
        (Units.map (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom
          (unifUnit (K := K) Q)) ^ (unitExp z q) := by
    rw [unitPartOf]
  rw [hunit, map_mul, map_zpow, hkey]
  congr 1
  rw [← zpow_mul]
  congr 1
  ring

/-! ## The auxiliary values -/

/-- The auxiliary values at a place of `L` which lies above no bad place of `K`: the adjusted unit
parts of the chosen local preimages. -/
noncomputable def unitAtGood (x : 𝕀[K])
    (h : ∀ v : Place K, ∃ y : 𝕀[L], x v = Idele.normIdeleFun K L y v) :
    (w : Place L) → (Place.localField L w)ˣ :=
  fun w => match w with
    | Sum.inl _ => 1
    | Sum.inr q =>
        unitIdeleFun (preimageIdele x h
            (Place.ofFinite (HeightOneSpectrum.under (𝓞 K) q)))
          (HeightOneSpectrum.under (𝓞 K) q) (Place.ofFinite q)

@[simp] theorem unitAtGood_ofInfinite (x : 𝕀[K])
    (h : ∀ v : Place K, ∃ y : 𝕀[L], x v = Idele.normIdeleFun K L y v)
    (w : InfinitePlace L) : unitAtGood x h (Place.ofInfinite w) = 1 := rfl

theorem unitAtGood_ofFinite (x : 𝕀[K])
    (h : ∀ v : Place K, ∃ y : 𝕀[L], x v = Idele.normIdeleFun K L y v)
    (q : HeightOneSpectrum (𝓞 L)) :
    unitAtGood x h (Place.ofFinite q) =
      unitIdeleFun (preimageIdele x h
          (Place.ofFinite (HeightOneSpectrum.under (𝓞 K) q)))
        (HeightOneSpectrum.under (𝓞 K) q) (Place.ofFinite q) := rfl

/-- Values of the auxiliary idèle: the chosen local preimage at a bad place, the adjusted unit
parts at the remaining places. -/
noncomputable def auxIdeleFun (x : 𝕀[K])
    (h : ∀ v : Place K, ∃ y : 𝕀[L], x v = Idele.normIdeleFun K L y v) :
    (w : Place L) → (Place.localField L w)ˣ :=
  fun w => if _ : placeUnder K L w ∈ badSet (K := K) (L := L) x then
      (preimageIdele x h (placeUnder K L w)) w
    else unitAtGood x h w

theorem auxIdeleFun_of_mem_badSet {x : 𝕀[K]}
    {h : ∀ v : Place K, ∃ y : 𝕀[L], x v = Idele.normIdeleFun K L y v} {w : Place L}
    (hbad : placeUnder K L w ∈ badSet (K := K) (L := L) x) :
    auxIdeleFun x h w = preimageIdele x h (placeUnder K L w) w := by
  dsimp only [auxIdeleFun]
  rw [dif_pos hbad]

theorem auxIdeleFun_of_not_mem_badSet {x : 𝕀[K]}
    {h : ∀ v : Place K, ∃ y : 𝕀[L], x v = Idele.normIdeleFun K L y v} {w : Place L}
    (hbad : placeUnder K L w ∉ badSet (K := K) (L := L) x) :
    auxIdeleFun x h w = unitAtGood x h w := by
  dsimp only [auxIdeleFun]
  rw [dif_neg hbad]

/-! ## The exponent sum vanishes -/

/-- The valuation of the local norm of a unit is the inertia degree-th power of its valuation. -/
theorem val_localNormFinite_eq_pow (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (x : (q.adicCompletion L)ˣ) :
    Valued.v ((Place.localNormFinite q Q hq x : (Q.adicCompletion K)ˣ) : Q.adicCompletion K) =
      (Valued.v ((x : (q.adicCompletion L)ˣ) : q.adicCompletion L)) ^
        (q.asIdeal.inertiaDeg (𝓞 K)) := by
  classical
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    (Commons.RingTheory.Henselian.adicCompletionMap Q q hq).toAlgebra
  have h1 : ((Place.localNormFinite q Q hq x : (Q.adicCompletion K)ˣ) : Q.adicCompletion K) =
      Algebra.norm (Q.adicCompletion K) ((x : (q.adicCompletion L)ˣ) : q.adicCompletion L) := rfl
  rw [h1]
  exact NK.GlobalCFT.Norm.globalCFT_val_norm_adicCompletion_eq_pow_inertiaDeg Q q hq x

/-- The product of `WithZero.exp` of a family of integers is the exponential of the sum. -/
theorem prod_exp_eq_exp_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    (∏ i ∈ s, WithZero.exp (f i)) = WithZero.exp (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, WithZero.exp_add]

/-- A product of powers of a group element is the power of the sum of the exponents. -/
theorem prod_zpow_eq_zpow_sum {ι G : Type*} [CommGroup G] (a : G)
    (s : Finset ι) (f : ι → ℤ) :
    (∏ i ∈ s, a ^ f i) = a ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add]

/-- The exponents coming from the fibre of `Q` sum to zero. -/
theorem sum_unitExp_mul_inertiaDeg_eq_zero (z : 𝕀[L]) (Q : HeightOneSpectrum (𝓞 K))
    (hQ : Idele.normIdeleFun K L z (Place.ofFinite Q) ∈ Place.localUnits K (Place.ofFinite Q)) :
    ∑ x ∈ (Place.primesOverFinite (K := K) (L := L) Q).attach,
      unitExp z x.1 * (x.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) = 0 := by
  classical
  have hv : Valued.v ((Idele.normIdeleFun K L z (Place.ofFinite Q) : (Q.adicCompletion K)ˣ) :
      Q.adicCompletion K) = 1 :=
    (Place.mem_localUnits_ofFinite_iff_valued_eq_one).mp hQ
  have hprod : Valued.v ((Idele.normIdeleFun K L z (Place.ofFinite Q) : (Q.adicCompletion K)ˣ) :
        Q.adicCompletion K) =
      WithZero.exp (∑ x ∈ (Place.primesOverFinite (K := K) (L := L) Q).attach,
        unitExp z x.1 * (x.1.asIdeal.inertiaDeg (𝓞 K) : ℤ)) := by
    rw [Idele.normIdeleFun_ofFinite, Units.coe_prod, map_prod]
    rw [Finset.prod_congr rfl (fun x _ => ?_), prod_exp_eq_exp_sum]
    have hq' : x.1.asIdeal.LiesOver Q.asIdeal :=
      (Place.mem_primesOverFinite (K := K) (L := L) (Q := Q) (q := x.1)).mp x.2
    have hz : Valued.v ((z (Place.ofFinite x.1) : (x.1.adicCompletion L)ˣ) :
        x.1.adicCompletion L) = WithZero.exp (unitExp z x.1) := by
      rw [unitExp]
      exact (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr (Units.ne_zero _))).symm
    rw [val_localNormFinite_eq_pow Q x.1 hq' (z (Place.ofFinite x.1)), hz, ← WithZero.exp_nsmul]
    congr 1
    rw [nsmul_eq_mul, mul_comm]
  rw [hv] at hprod
  have h0 : (0 : ℤ) = ∑ x ∈ (Place.primesOverFinite (K := K) (L := L) Q).attach,
      unitExp z x.1 * (x.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) :=
    WithZero.exp_inj.mp (by rw [WithZero.exp_zero, hprod])
  exact h0.symm

/-! ## The fibre computation -/

/-- **The fibre computation.**  If `Q` is a finite place of `K` at which the extension is
unramified and the norm of `z` at `Q` is a local unit, then replacing the local preimages by
their adjusted unit parts does not change the norm at `Q`. -/
theorem normIdeleFun_unitIdeleOf (z : 𝕀[L]) (Q : HeightOneSpectrum (𝓞 K))
    (hunr : ∀ q : HeightOneSpectrum (𝓞 L), q.asIdeal.LiesOver Q.asIdeal →
      q.asIdeal.ramificationIdx (𝓞 K) = 1)
    (hQ : Idele.normIdeleFun K L z (Place.ofFinite Q) ∈ Place.localUnits K (Place.ofFinite Q)) :
    Idele.normIdeleFun K L (unitIdeleOf z Q hunr) (Place.ofFinite Q) =
      Idele.normIdeleFun K L z (Place.ofFinite Q) := by
  classical
  have hsum := sum_unitExp_mul_inertiaDeg_eq_zero z Q hQ
  have hL : Idele.normIdeleFun K L (unitIdeleOf z Q hunr) (Place.ofFinite Q) =
      ∏ x ∈ (Place.primesOverFinite (K := K) (L := L) Q).attach,
        Place.localNormFinite x.1 Q
          ((Place.mem_primesOverFinite (K := K) (L := L) (Q := Q) (q := x.1)).mp x.2)
          (unitPartOf z Q x.1
            ((Place.mem_primesOverFinite (K := K) (L := L) (Q := Q) (q := x.1)).mp x.2)) := by
    rw [Idele.normIdeleFun_ofFinite]
    refine Finset.prod_congr rfl fun x _ => ?_
    have hq' : x.1.asIdeal.LiesOver Q.asIdeal :=
      (Place.mem_primesOverFinite (K := K) (L := L) (Q := Q) (q := x.1)).mp x.2
    congr 1
    show unitIdeleFun z Q (Place.ofFinite x.1) = unitPartOf z Q x.1 hq'
    rw [unitIdeleFun_ofFinite, dif_pos hq']
  have hR : Idele.normIdeleFun K L z (Place.ofFinite Q) =
      ∏ x ∈ (Place.primesOverFinite (K := K) (L := L) Q).attach,
        Place.localNormFinite x.1 Q
          ((Place.mem_primesOverFinite (K := K) (L := L) (Q := Q) (q := x.1)).mp x.2)
          (z (Place.ofFinite x.1)) := by
    rw [Idele.normIdeleFun_ofFinite]
  rw [hL, hR]
  rw [Finset.prod_congr rfl (fun x _ =>
    localNormFinite_unitPartOf z Q x.1
      ((Place.mem_primesOverFinite (K := K) (L := L) (Q := Q) (q := x.1)).mp x.2)
      (hunr x.1 ((Place.mem_primesOverFinite (K := K) (L := L) (Q := Q) (q := x.1)).mp x.2)))]
  rw [Finset.prod_mul_distrib, prod_zpow_eq_zpow_sum, hsum, zpow_zero, mul_one]

/-! ## The main theorem -/

theorem mem_normImage_iff_localNorm_of_finiteDimensional {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (x : NK.GlobalCFT.Idele K) :
    x ∈ NK.GlobalCFT.Idele.normImage K L ↔
      ∀ v : NK.GlobalCFT.Place K, ∃ y : NK.GlobalCFT.Idele L,
        x v = NK.GlobalCFT.Idele.normIdeleFun K L y v := by
  classical
  constructor
  · rintro ⟨y, hy⟩ v
    exact ⟨y, hy v⟩
  · intro h
    rw [Idele.mem_normImage]
    have hyval_mem : ∀ᶠ w in Filter.cofinite, auxIdeleFun x h w ∈ Place.localUnits L w := by
      rw [Filter.eventually_cofinite]
      refine Set.Finite.subset (finite_placeUnder_mem_of_finset (K := K) (L := L)
        (badSet (K := K) (L := L) x)) ?_
      intro w hw
      simp only [Set.mem_ofPred_eq] at hw ⊢
      by_contra hbad
      have hfin : Place.IsFinite w :=
        (Place.isFinite_of_liesOver (liesOver_placeUnder (K := K) (L := L) w)).mpr (by
          by_contra h
          exact hbad (mem_badSet_of_isInfinite (K := K) (L := L) (x := x)
            (v := placeUnder K L w) (Classical.not_not.mp h)))
      obtain ⟨q, rfl⟩ := Place.isFinite_iff.mp hfin
      have hbad' : Place.ofFinite (HeightOneSpectrum.under (𝓞 K) q) ∉
          badSet (K := K) (L := L) x := by
        rwa [placeUnder_ofFinite] at hbad
      refine hw ?_
      rw [auxIdeleFun_of_not_mem_badSet hbad, unitAtGood_ofFinite]
      exact unitIdeleFun_mem_localUnits (z := preimageIdele x h
          (Place.ofFinite (HeightOneSpectrum.under (𝓞 K) q)))
        (Q := HeightOneSpectrum.under (𝓞 K) q)
        (fun q' hq' => by
          by_contra hne
          exact hbad' (mem_badSet_of_ramificationIdx_ne_one hq' hne))
        (Place.ofFinite q)
    let y : 𝕀[L] := ⟨auxIdeleFun x h, hyval_mem⟩
    refine ⟨y, fun v => ?_⟩
    rcases v with w | Q
    · -- archimedean place: always in `badSet`
      have hv : Place.ofInfinite w ∈ badSet (K := K) (L := L) x :=
        mem_badSet_of_isInfinite (K := K) (L := L) (x := x) (v := Place.ofInfinite w)
          (Place.isInfinite_ofInfinite w)
      have hc : ∀ w' : Place L, Place.LiesOver w' (Place.ofInfinite w) →
          y w' = preimageIdele x h (Place.ofInfinite w) w' := by
        intro w' hw'
        have hplace : placeUnder K L w' = Place.ofInfinite w := placeUnder_eq_of_liesOver hw'
        change auxIdeleFun x h w' = _
        rw [auxIdeleFun_of_mem_badSet (by rw [hplace]; exact hv), hplace]
      rw [normIdeleFun_congr_of_liesOver (y := y)
        (y' := preimageIdele x h (Place.ofInfinite w)) hc]
      exact preimageIdele_spec x h (Place.ofInfinite w)
    · by_cases hQ : Place.ofFinite Q ∈ badSet (K := K) (L := L) x
      · -- the extension is (possibly) ramified at `Q`
        have hc : ∀ w' : Place L, Place.LiesOver w' (Place.ofFinite Q) →
            y w' = preimageIdele x h (Place.ofFinite Q) w' := by
          intro w' hw'
          have hplace : placeUnder K L w' = Place.ofFinite Q := placeUnder_eq_of_liesOver hw'
          change auxIdeleFun x h w' = _
          rw [auxIdeleFun_of_mem_badSet (by rw [hplace]; exact hQ), hplace]
        rw [normIdeleFun_congr_of_liesOver (y := y)
          (y' := preimageIdele x h (Place.ofFinite Q)) hc]
        exact preimageIdele_spec x h (Place.ofFinite Q)
      · -- the good case
        have hunr : ∀ q : HeightOneSpectrum (𝓞 L), q.asIdeal.LiesOver Q.asIdeal →
            q.asIdeal.ramificationIdx (𝓞 K) = 1 := by
          intro q hq
          by_contra hne
          exact hQ (mem_badSet_of_ramificationIdx_ne_one hq hne)
        have hQmem : Idele.normIdeleFun K L (preimageIdele x h (Place.ofFinite Q)) (Place.ofFinite Q) ∈
            Place.localUnits K (Place.ofFinite Q) := by
          rw [← preimageIdele_spec x h (Place.ofFinite Q)]
          by_contra hmem
          exact hQ (mem_badSet_of_not_mem_localUnits (K := K) (L := L) hmem)
        have hc : ∀ w' : Place L, Place.LiesOver w' (Place.ofFinite Q) →
            y w' = unitIdeleFun (preimageIdele x h (Place.ofFinite Q)) Q w' := by
          intro w' hw'
          have hfin : Place.IsFinite w' :=
            (Place.isFinite_of_liesOver hw').mpr (Place.isFinite_ofFinite Q)
          obtain ⟨q, rfl⟩ := Place.isFinite_iff.mp hfin
          have hq : q.asIdeal.LiesOver Q.asIdeal := by
            rcases (Place.liesOver_iff (Place.ofFinite q) (Place.ofFinite Q)).mp hw' with
              ⟨w'', v', h1, -, -⟩ | ⟨q', Q', h1, h2, h3⟩
            · exact absurd h1 (by simp)
            · obtain rfl := Place.ofFinite_inj.mp h1
              obtain rfl := Place.ofFinite_inj.mp h2
              exact h3
          have hprime : HeightOneSpectrum.under (𝓞 K) q = Q :=
            HeightOneSpectrum.ext (by rw [HeightOneSpectrum.under_asIdeal, hq.over])
          have hbadq : placeUnder K L (Place.ofFinite q) ∉
              badSet (K := K) (L := L) x := by
            rw [placeUnder_ofFinite, hprime]
            exact hQ
          have hpre : preimageIdele x h (Place.ofFinite (HeightOneSpectrum.under (𝓞 K) q)) =
              preimageIdele x h (Place.ofFinite Q) :=
            congrArg (preimageIdele x h) (by rw [hprime])
          change auxIdeleFun x h (Place.ofFinite q) = _
          rw [auxIdeleFun_of_not_mem_badSet hbadq, unitAtGood_ofFinite, hpre,
            unitIdeleFun_apply_eq_of_prime_eq hprime (Place.ofFinite q)]
        have hcongr := normIdeleFun_congr_of_liesOver (y := y)
          (y' := unitIdeleOf (preimageIdele x h (Place.ofFinite Q)) Q hunr) hc
        refine (preimageIdele_spec x h (Place.ofFinite Q)).trans ?_
        exact ((normIdeleFun_unitIdeleOf (preimageIdele x h (Place.ofFinite Q)) Q hunr hQmem).symm).trans
          hcongr.symm

end NK.CFTLib.IdeleHasse
