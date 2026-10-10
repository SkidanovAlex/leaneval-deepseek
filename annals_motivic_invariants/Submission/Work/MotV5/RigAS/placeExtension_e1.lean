import Mathlib
import Submission.Work.MotV5.RigAS.PlaceData
import Submission.Work.MotV5.RigAS.kleinResidue
import Submission.Work.MotV5.RigAS.GaloisTrue.galois
import Submission.Work.MotV5.Nodes.fifthPowAtPoles_AS
import Submission.Work.MotV5.Nodes.valuationSubringLyingOver
import Submission.Work.MotV5.Nodes.UEPR.countL
import Submission.Work.MotV5.Nodes.UEPR.bridge
import Submission.Work.MotV5.Nodes.UEPR.residue_trivial
import Submission.Work.MotV5.Nodes.UEPR.map_maximalIdeal_eq_of_ramificationIdx_eq_one
import Submission.Work.MotV5.Nodes.poleFibre_asTwist
import Submission.Work.MotV5.GenAux_asTwistFieldTrue_finrank_and_isSeparable
import Submission.Work.MotV5.RigAS.ValuationAux.val_eq_of_ring_stable
import Submission.Work.MotV5.RigAS.ValuationAux.val_mem_of_localPole
import Submission.Work.MotV5.RigAS.ValuationAux.localPole_of_ramificationIdx_eq_one
import Submission.Work.MotV5.RigAS.ValuationAux.valuation_extends_zhat_pow
import Submission.Work.MotV5.RigAS.kleinResidue_of_hsub
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option autoImplicit false

namespace Work.MotV5.RigAS

open scoped WithZero

/-! # The local place extension with ramification index `1`

The target is `Work.MotV5.RigAS.placeExtension_e1`.  The proof has the following shape.

Let `F = asTwistFieldTrue D g τ σS`, `L = asFieldL D g`, and `σ' = twistSigmaL D g τ σS σ h`
(the twisted action, of order `5` on `L`, with fixed field `F`).

1. Take a `WithZero (Multiplicative ℤ)`-valued prolongation `w` of `v` to `L`: by
   `valuation_extends_zhat_pow` there are `E ≥ 1` and `w` with `w (algebraMap F L x) = (v x) ^ E`;
   in particular `w` has the same valuation ring as `v` on `F` (`hsub`).
2. Let `P` be the centre of `w` on the integral closure `B = ⟥O_v, L⟧` (`bridge`), with
   `e := P.ramificationIdx`, `f := P.inertiaDeg`, `N := #{primes over m_A}`.  By `countL`,
   `N * (e * f) = [L : F] = 5`.
3. `e = 1`: otherwise `e = 5`, so `N = f = 1`; then `w` is the unique prolongation of its ring, hence
   is `σ'`-stable, and the Klein argument exhibits `z` with `w z ≤ 1` and `w (σ' z - z) = 1`, while
   `f = 1` together with `residue_trivial` forces `w (σ' z - z) < 1` — a contradiction.
4. With `e = 1`, the value group of `w` is computed by the values on `F`
   (`localPole_of_ramificationIdx_eq_one` + `val_mem_of_localPole`).
5. The valuation `V` is then defined by `V x := v y` for any `y` with `w (algebraMap F L y) = w x`;
   the order relation transfers from `w` along the order-isomorphism `x ↦ x ^ E`, so all the
   valuation axioms for `V` follow from those for `w`, and `V` extends `v` with the same value
   group. -/

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-- **The main theorem.** -/
theorem placeExtension_e1 (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : RatFunc 𝕜) (hg : g = Work.MotV.fAS 𝕜 ∨ g = 2 • Work.MotV.fAS 𝕜) (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D) (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D) (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜) (h : Work.MotV5.ASTwistData 𝕜 D g τ σS σ) (v : Valuation ↥(Work.MotV5.asTwistFieldTrue D g τ σS) (WithZero (Multiplicative ℤ))) (htriv : Work.MotV.TrivOn 𝕜 v) (ht : 1 < v (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) RatFunc.X)) : ∃ V : Valuation ↥(Work.MotV5.asFieldL D g) (WithZero (Multiplicative ℤ)), Work.MotV5.RigAS.IsPlaceExtension D g τ σS σ h v V := by
  classical
  -- ## 0. The `F`-algebra structure on `L`
  have hFL : Work.MotV5.asTwistFieldTrue D g τ σS ≤ Work.MotV5.asFieldL D g :=
    Work.MotV5.asTwistFieldTrue_le_asFieldL D g τ σS
  letI : Algebra ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) :=
    ((Subfield.inclusion hFL :
        ↥((Work.MotV5.asTwistFieldTrue D g τ σS).toSubfield) →+*
          ↥((Work.MotV5.asFieldL D g).toSubfield))).toAlgebra
  have halg : ∀ x : ↥(Work.MotV5.asTwistFieldTrue D g τ σS),
      algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) x
        = twistIncl D g τ σS x := fun _ => Subtype.ext rfl
  haveI hgal : IsGalois ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) :=
    Work.MotV5.RigAS.GaloisTrue.galois 𝕜 D g τ σS σ h
  have hfr : (Work.MotV5.asTwistFieldTrue D g τ σS).relfinrank (Work.MotV5.asFieldL D g) = 5 :=
    (Work.MotV5.GenAux_asTwistFieldTrue_finrank_and_isSeparable 𝕜 D g τ σS
      h.h5L h.hneL h.hpres).1
  have hfin : Module.finrank ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g)
      = 5 := by
    have h2 : Module.finrank ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
        ↥(IntermediateField.extendScalars hFL) = 5 := by
      rw [← IntermediateField.relfinrank_eq_finrank_of_le hFL]
      exact hfr
    exact h2
  haveI hFD : FiniteDimensional ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
      ↥(Work.MotV5.asFieldL D g) :=
    FiniteDimensional.of_finrank_pos (by rw [hfin]; norm_num)
  have hvnt : v.IsNontrivial := Valuation.IsNontrivial_iff_exists_one_lt.mpr ⟨_, ht⟩
  -- ## 1. A `WithZero (Multiplicative ℤ)`-valued prolongation `w` of `v` to `L`
  obtain ⟨E, hE1, w, hwext⟩ :=
    Work.MotV5.RigAS.ValuationAux.valuation_extends_zhat_pow
      (F := ↥(Work.MotV5.asTwistFieldTrue D g τ σS))
      (L := ↥(Work.MotV5.asFieldL D g)) v
  have hEnz : E ≠ 0 := by omega
  have hsub : ∀ x : ↥(Work.MotV5.asTwistFieldTrue D g τ σS),
      w (algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) x) ≤ 1
        ↔ v x ≤ 1 := by
    intro x
    rw [hwext x]
    exact pow_le_one_iff_of_nonneg bot_le hEnz
  -- the order relation transfers through the `E`-th power
  have hpoweq : ∀ a b : ↥(Work.MotV5.asTwistFieldTrue D g τ σS),
      v a ≤ v b ↔ w (algebraMap _ _ a) ≤ w (algebraMap _ _ b) := by
    intro a b
    rw [hwext a, hwext b]
    constructor
    · intro hab
      exact pow_le_pow_left₀ bot_le hab E
    · intro hab
      by_contra hcon
      have hlt : v b < v a := lt_of_not_ge hcon
      have h2 : (v b) ^ E < (v a) ^ E := pow_lt_pow_left₀ hlt bot_le hEnz
      exact absurd hab (not_le.mpr h2)
  -- ## 2. The centre of `w`, and the counting identity `N * (e * f) = 5`
  haveI hBfr : IsFractionRing
      ↥(integralClosure ↥(v.valuationSubring) ↥(Work.MotV5.asFieldL D g))
      ↥(Work.MotV5.asFieldL D g) :=
    IsIntegralClosure.isFractionRing_of_finite_extension ↥(v.valuationSubring)
      ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) _
  haveI hBfin : Module.Finite ↥(v.valuationSubring)
      ↥(integralClosure ↥(v.valuationSubring) ↥(Work.MotV5.asFieldL D g)) :=
    IsIntegralClosure.finite ↥(v.valuationSubring)
      ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) _
  obtain ⟨P, hPprime, hPlies, hPc, hbridge⟩ :=
    Work.MotV5.Nodes.UEPR.bridge v hvnt w hsub
  haveI := hPprime
  haveI := hPlies
  have hcount : ((IsLocalRing.maximalIdeal ↥(v.valuationSubring)).primesOver
        ↥(integralClosure ↥(v.valuationSubring) ↥(Work.MotV5.asFieldL D g))).ncard
      * (P.ramificationIdx ↥(v.valuationSubring) * P.inertiaDeg ↥(v.valuationSubring)) = 5 := by
    rw [Work.MotV5.Nodes.UEPR.countL v hvnt P, hfin]
  -- ## 3. The ramification index at `P` is `1`
  have he1 : P.ramificationIdx ↥(v.valuationSubring) = 1 := by
    by_contra he
    have hdvd : P.ramificationIdx ↥(v.valuationSubring) ∣ 5 :=
      ⟨((IsLocalRing.maximalIdeal ↥(v.valuationSubring)).primesOver
          ↥(integralClosure ↥(v.valuationSubring) ↥(Work.MotV5.asFieldL D g))).ncard
        * P.inertiaDeg ↥(v.valuationSubring), by rw [← hcount]; ring⟩
    have he5 : P.ramificationIdx ↥(v.valuationSubring) = 5 := by
      rcases (by norm_num : Nat.Prime 5).eq_one_or_self_of_dvd _ hdvd with h1 | h5
      · exact absurd h1 he
      · exact h5
    have hNf : ((IsLocalRing.maximalIdeal ↥(v.valuationSubring)).primesOver
          ↥(integralClosure ↥(v.valuationSubring) ↥(Work.MotV5.asFieldL D g))).ncard
        * P.inertiaDeg ↥(v.valuationSubring) = 1 := by
      have h5' : 5 * (((IsLocalRing.maximalIdeal ↥(v.valuationSubring)).primesOver
            ↥(integralClosure ↥(v.valuationSubring) ↥(Work.MotV5.asFieldL D g))).ncard
          * P.inertiaDeg ↥(v.valuationSubring)) = 5 := by
        have h1 : 5 * (((IsLocalRing.maximalIdeal ↥(v.valuationSubring)).primesOver
              ↥(integralClosure ↥(v.valuationSubring) ↥(Work.MotV5.asFieldL D g))).ncard
            * P.inertiaDeg ↥(v.valuationSubring))
            = ((IsLocalRing.maximalIdeal ↥(v.valuationSubring)).primesOver
                ↥(integralClosure ↥(v.valuationSubring) ↥(Work.MotV5.asFieldL D g))).ncard
              * (P.ramificationIdx ↥(v.valuationSubring)
                * P.inertiaDeg ↥(v.valuationSubring)) := by
          rw [he5]; ring
        rw [h1, hcount]
      have h5m : 5 * (((IsLocalRing.maximalIdeal ↥(v.valuationSubring)).primesOver
            ↥(integralClosure ↥(v.valuationSubring) ↥(Work.MotV5.asFieldL D g))).ncard
          * P.inertiaDeg ↥(v.valuationSubring)) = 5 * 1 := by
        rw [mul_one]; exact h5'
      exact Nat.mul_left_cancel (n := 5) (by norm_num) h5m
    have hN1 : ((IsLocalRing.maximalIdeal ↥(v.valuationSubring)).primesOver
          ↥(integralClosure ↥(v.valuationSubring) ↥(Work.MotV5.asFieldL D g))).ncard = 1 :=
      (Nat.eq_one_of_mul_eq_one_right hNf)
    have hf1 : P.inertiaDeg ↥(v.valuationSubring) = 1 := (Nat.eq_one_of_mul_eq_one_left hNf)
    -- `σ'` fixes `F` pointwise
    have hσfix : ∀ x : ↥(Work.MotV5.asTwistFieldTrue D g τ σS),
        twistSigmaL D g τ σS σ h (twistIncl D g τ σS x) = twistIncl D g τ σS x := by
      intro x
      apply Subtype.ext
      show Work.MotV5.asTwistAction D τ σS (x : Work.MotV.Om D) = (x : Work.MotV.Om D)
      have hx := Work.MotV5.asTwistFieldTrue_le_asTwistFieldFix D g τ σS x.2
      rw [Work.MotV5.asTwistFieldFix, IntermediateField.mem_fixedField_iff] at hx
      have h3 := hx (Work.MotV5.asTwistAction D τ σS) (Subgroup.mem_zpowers _)
      simpa [AlgEquiv.smul_def] using h3
    -- `N = 1` forces `w` to be `σ'`-stable
    have hstab : ∀ x : ↥(Work.MotV5.asFieldL D g),
        w (twistSigmaL D g τ σS σ h x) = w x := by
      set w' : Valuation ↥(Work.MotV5.asFieldL D g) (WithZero (Multiplicative ℤ)) :=
        Valuation.comap (twistSigmaL D g τ σS σ h :
          ↥(Work.MotV5.asFieldL D g) →+* ↥(Work.MotV5.asFieldL D g)) w with hw'def
      have hsub' : ∀ x : ↥(Work.MotV5.asTwistFieldTrue D g τ σS),
          w' (algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
                ↥(Work.MotV5.asFieldL D g) x) ≤ 1 ↔ v x ≤ 1 := by
        intro x
        have hφ' : (twistSigmaL D g τ σS σ h :
              ↥(Work.MotV5.asFieldL D g) →+* ↥(Work.MotV5.asFieldL D g))
            (algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
              ↥(Work.MotV5.asFieldL D g) x)
            = algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
              ↥(Work.MotV5.asFieldL D g) x := by
          rw [halg x]
          exact hσfix x
        rw [hw'def, Valuation.comap_apply, hφ']
        exact hsub x
      obtain ⟨P', hP'prime, hP'lies, hP'c, hbridge'⟩ :=
        Work.MotV5.Nodes.UEPR.bridge v hvnt w' hsub'
      haveI := hP'prime
      haveI := hP'lies
      have hPmem : P ∈ (IsLocalRing.maximalIdeal ↥(v.valuationSubring)).primesOver
          ↥(integralClosure ↥(v.valuationSubring) ↥(Work.MotV5.asFieldL D g)) :=
        ⟨hPprime, hPlies⟩
      have hP'mem : P' ∈ (IsLocalRing.maximalIdeal ↥(v.valuationSubring)).primesOver
          ↥(integralClosure ↥(v.valuationSubring) ↥(Work.MotV5.asFieldL D g)) :=
        ⟨hP'prime, hP'lies⟩
      have hPP' : P = P' := by
        obtain ⟨Q, hQ⟩ := Set.ncard_eq_one.mp hN1
        have h1 : P = Q := by
          have hmem : P ∈ ({Q} : Set (Ideal
              ↥(integralClosure ↥(v.valuationSubring) ↥(Work.MotV5.asFieldL D g)))) :=
            hQ ▸ hPmem
          simpa using hmem
        have h2 : P' = Q := by
          have hmem : P' ∈ ({Q} : Set (Ideal
              ↥(integralClosure ↥(v.valuationSubring) ↥(Work.MotV5.asFieldL D g)))) :=
            hQ ▸ hP'mem
          simpa using hmem
        rw [h1, h2]
      have hring : w'.valuationSubring.toSubring = w.valuationSubring.toSubring := by
        subst hPP'
        rw [hbridge', hbridge]
      have hφ : ∀ x : ↥(Work.MotV5.asFieldL D g),
          w (twistSigmaL D g τ σS σ h x) ≤ 1 ↔ w x ≤ 1 := by
        intro x
        have hx1 : (w (twistSigmaL D g τ σS σ h x) ≤ 1) ↔ x ∈ w.valuationSubring := by
          rw [show w (twistSigmaL D g τ σS σ h x) = w' x from rfl]
          rw [← Valuation.mem_valuationSubring_iff, ← ValuationSubring.mem_toSubring,
            ← ValuationSubring.mem_toSubring, hring]
        have hx2 : (w x ≤ 1) ↔ x ∈ w.valuationSubring :=
          (Valuation.mem_valuationSubring_iff w x).symm
        rw [hx1, hx2]
      exact Work.MotV5.RigAS.ValuationAux.val_eq_of_ring_stable w
        (twistSigmaL D g τ σS σ h) hφ
    -- the Klein argument gives a non-trivial residue action
    obtain ⟨z, hz1, hz2⟩ :=
      Work.MotV5.RigAS.kleinResidue_of_hsub 𝕜 D hD g τ σS σ h v w htriv
        (fun x => by rw [← halg x]; exact hsub x) hstab
    -- while `f = 1` forces the residue action to be trivial, via `residue_trivial`
    have hres := Work.MotV5.Nodes.UEPR.residue_trivial v hvnt w hsub P hPc hbridge hf1
    obtain ⟨c, hc⟩ := hres z hz1
    have hkey : w (twistSigmaL D g τ σS σ h z - z) < 1 := by
      have hsplit : twistSigmaL D g τ σS σ h z - z
          = twistSigmaL D g τ σS σ h
              (z - algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
                ↥(Work.MotV5.asFieldL D g) c)
            - (z - algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
                ↥(Work.MotV5.asFieldL D g) c) := by
        have h1 : twistSigmaL D g τ σS σ h
              (algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
                ↥(Work.MotV5.asFieldL D g) c)
            = algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
              ↥(Work.MotV5.asFieldL D g) c := by
          rw [halg c]
          exact hσfix c
        simp only [map_sub, h1]
        refl_ring1
      rw [hsplit]
      refine lt_of_le_of_lt (Valuation.map_sub w _ _) ?_
      rw [hstab, max_self]
      exact hc.2
    rw [hz2] at hkey
    exact absurd hkey (lt_irrefl 1)
  -- ## 4. The value group of `w` is generated by the values on `F`
  have hI : ∀ x : ↥(Work.MotV5.asFieldL D g), w x < 1 →
      ∃ a : ↥(Work.MotV5.asTwistFieldTrue D g τ σS),
        w (algebraMap _ _ a) < 1 ∧ w x ≤ w (algebraMap _ _ a) :=
    Work.MotV5.RigAS.ValuationAux.localPole_of_ramificationIdx_eq_one
      v w hsub P hPc hbridge he1
  have hval := Work.MotV5.RigAS.ValuationAux.val_mem_of_localPole w hI
  -- ## 5. The construction of `V`
  let yOf : (x : ↥(Work.MotV5.asFieldL D g)) → x ≠ 0 →
      ↥(Work.MotV5.asTwistFieldTrue D g τ σS) := fun x hx => Classical.choose (hval x hx)
  have hyOf_spec : ∀ (x : ↥(Work.MotV5.asFieldL D g)) (hx : x ≠ 0),
      w (algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g)
        (yOf x hx)) = w x :=
    fun x hx => (Classical.choose_spec (hval x hx)).2
  have hyOf_ne : ∀ (x : ↥(Work.MotV5.asFieldL D g)) (hx : x ≠ 0), yOf x hx ≠ 0 :=
    fun x hx => (Classical.choose_spec (hval x hx)).1
  have hval_eq_of_w_eq : ∀ a b : ↥(Work.MotV5.asTwistFieldTrue D g τ σS),
      w (algebraMap _ _ a) = w (algebraMap _ _ b) → v a = v b :=
    fun a b hab => le_antisymm ((hpoweq a b).mpr (le_of_eq hab))
      ((hpoweq b a).mpr (le_of_eq hab.symm))
  have hval_one_of_w_one : ∀ a : ↥(Work.MotV5.asTwistFieldTrue D g τ σS),
      w (algebraMap _ _ a) = 1 → v a = 1 := by
    intro a ha
    have h1 := hval_eq_of_w_eq a 1 (by rw [ha, map_one, map_one])
    rwa [map_one] at h1
  let Vfun : ↥(Work.MotV5.asFieldL D g) → WithZero (Multiplicative ℤ) :=
    fun x => if hx : x = 0 then 0 else v (yOf x hx)
  have hVfun_ne : ∀ (x : ↥(Work.MotV5.asFieldL D g)) (hx : x ≠ 0),
      Vfun x = v (yOf x hx) := by
    intro x hx
    simp only [Vfun, dif_neg hx]
  have hVfun_eq_zero : ∀ x : ↥(Work.MotV5.asFieldL D g), Vfun x = 0 ↔ x = 0 := by
    intro x
    constructor
    · intro h0
      by_contra hx
      have h1 : v (yOf x hx) = 0 := by rw [← hVfun_ne x hx]; exact h0
      exact (Valuation.ne_zero_iff v).mpr (hyOf_ne x hx) h1
    · intro hx
      rw [hx]
      exact dif_pos rfl
  have hVfun_ord : ∀ x y : ↥(Work.MotV5.asFieldL D g), Vfun x ≤ Vfun y ↔ w x ≤ w y := by
    intro x y
    by_cases hx : x = 0
    · rw [hx, show Vfun 0 = 0 from dif_pos rfl, map_zero]
      exact ⟨fun _ => bot_le, fun _ => bot_le⟩
    by_cases hy : y = 0
    · rw [hy, show Vfun 0 = 0 from dif_pos rfl, map_zero]
      constructor
      · intro h
        exact absurd ((hVfun_eq_zero x).mp (le_antisymm h bot_le)) hx
      · intro h
        have hx0 : x = 0 := by
          by_contra hx'
          exact (Valuation.ne_zero_iff w).mpr hx' (le_antisymm h bot_le)
        rw [hx0, show Vfun 0 = 0 from dif_pos rfl]
    calc Vfun x ≤ Vfun y
        ↔ v (yOf x hx) ≤ v (yOf y hy) := by rw [hVfun_ne x hx, hVfun_ne y hy]
      _ ↔ w (algebraMap _ _ (yOf x hx)) ≤ w (algebraMap _ _ (yOf y hy)) := hpoweq _ _
      _ ↔ w x ≤ w y := by rw [hyOf_spec x hx, hyOf_spec y hy]
  have hTw_ne_of : ∀ x : ↥(Work.MotV5.asTwistFieldTrue D g τ σS), x ≠ 0 →
      twistIncl D g τ σS x ≠ 0 := by
    intro x hx h0
    exact hx (Subtype.ext (by
      have h1 := congrArg (fun z : ↥(Work.MotV5.asFieldL D g) => (z : Work.MotV.Om D)) h0
      rwa [twistIncl_coe] at h1))
  have hTw_zero : twistIncl D g τ σS (0 : ↥(Work.MotV5.asTwistFieldTrue D g τ σS)) = 0 := by
    apply Subtype.ext
    rw [twistIncl_coe]
    simp
  refine ⟨{ toFun := Vfun
            map_zero' := dif_pos rfl
            map_one' := ?_
            map_mul' := ?_
            map_add_le_max' := ?_ }, ?_, ?_⟩
  · -- `V 1 = 1`
    change Vfun 1 = 1
    rw [hVfun_ne 1 one_ne_zero]
    have hw1 : w (algebraMap _ _ (yOf 1 one_ne_zero)) = 1 := by
      rw [hyOf_spec 1 one_ne_zero, map_one]
    exact hval_one_of_w_one _ hw1
  · -- multiplicativity
    intro x y
    change Vfun (x * y) = Vfun x * Vfun y
    by_cases hx : x = 0
    · subst hx; simp [Vfun]
    by_cases hy : y = 0
    · subst hy; simp [Vfun]
    have hxy : x * y ≠ 0 := mul_ne_zero hx hy
    rw [hVfun_ne (x * y) hxy, hVfun_ne x hx, hVfun_ne y hy,
      ← Valuation.map_mul v (yOf x hx) (yOf y hy)]
    refine hval_eq_of_w_eq _ _ ?_
    have h1 : w (algebraMap _ _ (yOf (x * y) hxy)) = w (x * y) := hyOf_spec (x * y) hxy
    have h2 : w (algebraMap _ _ (yOf x hx * yOf y hy)) = w (x * y) := by
      rw [map_mul, Valuation.map_mul, hyOf_spec x hx, hyOf_spec y hy,
        ← Valuation.map_mul w x y]
    rw [h1, h2]
  · -- the ultrametric inequality
    intro x y
    change Vfun (x + y) ≤ max (Vfun x) (Vfun y)
    have hw : w (x + y) ≤ max (w x) (w y) := Valuation.map_add_le_max' w x y
    rw [le_max_iff]
    rcases max_choice (w x) (w y) with hm | hm
    · exact Or.inl ((hVfun_ord (x + y) x).mpr (by rw [hm] at hw; exact hw))
    · exact Or.inr ((hVfun_ord (x + y) y).mpr (by rw [hm] at hw; exact hw))
  · -- `V` extends `v`
    intro x
    change Vfun (twistIncl D g τ σS x) = v x
    by_cases hx : x = 0
    · subst hx
      rw [hTw_zero, show Vfun 0 = 0 from dif_pos rfl, map_zero]
    · rw [hVfun_ne _ (hTw_ne_of x hx)]
      refine hval_eq_of_w_eq _ x ?_
      rw [hyOf_spec (twistIncl D g τ σS x) (hTw_ne_of x hx), halg x]
  · -- the value group of `V` agrees with the values on `F`
    intro x hx
    change ∃ y : ↥(Work.MotV5.asTwistFieldTrue D g τ σS),
      y ≠ 0 ∧ Vfun (twistIncl D g τ σS y) = Vfun x
    refine ⟨yOf x hx, hyOf_ne x hx, ?_⟩
    rw [hVfun_ne x hx]
    have hne : twistIncl D g τ σS (yOf x hx) ≠ 0 := hTw_ne_of _ (hyOf_ne x hx)
    rw [hVfun_ne _ hne]
    refine hval_eq_of_w_eq _ _ ?_
    rw [hyOf_spec _ hne, halg (yOf x hx)]

end Work.MotV5.RigAS
