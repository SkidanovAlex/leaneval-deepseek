import Mathlib
import Submission.Work.SSGRoute.E7bDefs
import Submission.Work.SSGRoute.rightDetect_pgroup
import Submission.Work.SSGRoute.detect_h_trivial
import Submission.Work.SSGRoute.decompK_restrict_surjective
import Submission.Work.SSGRoute.ext_two_trivial_ptors
import Submission.Work.SSGRoute.local_pTorsion_card
import Submission.Work.SSGRoute.local_duality_ext
import Submission.Work.SSGRoute.extH_natCard_smul_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Y4: right detection when `D_w` is a `p`-group

This node is a pure assembly.  It feeds the abstract strong-induction theorem
`Work.SSGRoute.rightDetect_pgroup` (X2) with the four arithmetic/cardinality inputs that hold in the
local situation:

* `hf` — the restriction `D_{w'} → D_w` of decomposition groups is surjective
  (`Work.SSGRoute.decompK_restrict_surjective`, Y2);
* `hT` — `|H²(D_{w'}, L_{w'}ˣ)[p]| = p` (`Work.SSGRoute.local_pTorsion_card`);
* `hE2`/`hE2card` — `Ext²_{D_w}(𝔽_p, K_wˣ)` is finite of cardinality `≤ p`
  (`Work.SSGRoute.ext_two_trivial_ptors`, X3), whose hypotheses are Hilbert 90
  (`Work.SSGRoute.hilbert90_localUnits_extH`) and `PTorsLE p (H²(D_w,K_wˣ))`: when `p ∣ |D_w|` this
  is again `Work.SSGRoute.local_pTorsion_card`, and when `p ∤ |D_w|` every `p`-torsion class is
  killed (`|D_w| • x = 0` by `Work.SSGRoute.extH_natCard_smul_eq_zero`, `p • x = 0` by hypothesis,
  coprime);
* `hbase` — the base case `M = 𝔽_p` (`Work.SSGRoute.detect_h_trivial`, Y1).
-/

namespace Work.SSGRoute

set_option linter.style.haveILetI false

open SSGRoute.PTExt CategoryTheory

/-- **The `p`-torsion of `H²(D, A)` is at most `p` when `D` is a `p`-group with `p ∤ |D|`.**
The two annihilators `p` and `|D|` are coprime, so Bézout forces every `p`-torsion class to vanish. -/
private theorem ptors_le_of_not_dvd_card (p : ℕ) [Fact p.Prime] {D : Type} [Group D]
    [Fintype D] (A : Rep Coeff D) (hpD : ¬ p ∣ Nat.card D) : PTorsLE p (extH A 2) := by
  have hcop : Nat.Coprime p (Nat.card D) :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpD
  have hbez : (p : ℤ) * (Nat.gcdA p (Nat.card D))
      + (Nat.card D : ℤ) * (Nat.gcdB p (Nat.card D)) = 1 := by
    have h := Nat.gcd_eq_gcd_ab p (Nat.card D)
    rw [hcop.gcd_eq_one, Nat.cast_one] at h
    linarith [h]
  have hzero : ∀ y : extH A 2, p • y = 0 → y = 0 := by
    intro y hy
    have hDy : Nat.card D • y = 0 := extH_natCard_smul_eq_zero A (n := 2) (by norm_num) y
    have hy' : (p : ℤ) • y = 0 := by
      rw [Nat.cast_smul_eq_nsmul ℤ p]; exact hy
    have hDy' : (Nat.card D : ℤ) • y = 0 := by
      rw [Nat.cast_smul_eq_nsmul ℤ (Nat.card D)]; exact hDy
    calc y = (1 : ℤ) • y := (one_smul _ _).symm
      _ = ((p : ℤ) * (Nat.gcdA p (Nat.card D))
            + (Nat.card D : ℤ) * (Nat.gcdB p (Nat.card D))) • y := by rw [hbez]
      _ = (Nat.gcdA p (Nat.card D)) • ((p : ℤ) • y)
            + (Nat.gcdB p (Nat.card D)) • ((Nat.card D : ℤ) • y) := by
            rw [add_smul, mul_smul, mul_smul,
              smul_comm (p : ℤ) (Nat.gcdA p (Nat.card D)) y,
              smul_comm (Nat.card D : ℤ) (Nat.gcdB p (Nat.card D)) y]
      _ = 0 := by rw [hy', hDy']; simp
  haveI : Subsingleton {x : extH A 2 // p • x = 0} :=
    ⟨fun a b => Subtype.ext (by rw [hzero a.1 a.2, hzero b.1 b.2])⟩
  refine ⟨Finite.of_subsingleton, ?_⟩
  haveI : Fintype {x : extH A 2 // p • x = 0} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  exact le_trans (Fintype.card_le_one_iff_subsingleton.mpr inferInstance)
    (by have := (Fact.out : p.Prime).two_le; omega)

/-- **The `p`-torsion of `H²(D, A)` has at most `p` elements.**  When `p ∣ |D|` the local input
`Work.SSGRoute.local_pTorsion_card` applies; otherwise `D` carries no `p`-torsion (`IsPGroup`
forces `|D| = 1`, and in any case `ptors_le_of_not_dvd_card` finishes). -/
theorem pTorsLE_extH_two (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) :
    PTorsLE p (extH (localUnitsK (k := k) w) 2) := by
  by_cases hdiv : p ∣ Nat.card (decompK (k := k) w)
  · have hcard := local_pTorsion_card p k K w hdiv
    refine ⟨(Nat.card_ne_zero.mp (by rw [hcard]; exact (Fact.out : p.Prime).ne_zero)).2, ?_⟩
    exact le_of_eq hcard
  · haveI : Fintype (decompK (k := k) w) := Fintype.ofFinite _
    exact ptors_le_of_not_dvd_card p (localUnitsK (k := k) w) hdiv

/-- **Y4 (E7b(ii) when `D_w` is a `p`-group).**  Right detection at every level with
`p ∣ |D_{w'}|`, for every finite `p`-torsion `D_w`-module `N`.  Assembly of
`Work.SSGRoute.rightDetect_pgroup` with: `hf` from `Work.SSGRoute.decompK_restrict_surjective`;
`hT` from `Work.SSGRoute.local_pTorsion_card`; `hE2` from `Work.SSGRoute.ext_two_trivial_ptors`
+ `Work.SSGRoute.hilbert90_localUnits_extH` + `local_pTorsion_card` at the base level (or, when
`p ∤ |D_w|`, `H²(D_w, K_wˣ)[p] = 0`); `hbase` from `Work.SSGRoute.detect_h_trivial`. -/
theorem local_detect_h_pgroup (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (hD : IsPGroup p (decompK (k := k) w))
    (N : Rep Coeff (decompK (k := k) w)) [Finite N] (hN : ∀ n : N, p • n = 0)
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L]
    (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (ι : Rep.res f (localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k L w')
    (hι : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
      ι.hom (Additive.ofMul u) =
        Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u))
    (hp : p ∣ Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w')) :
    RightDetect f ι N := by
  haveI : Finite (MulAction.stabilizer (L ≃ₐ[k] L) w') := inferInstance
  haveI : Finite (decompK (k := k) w) := inferInstance
  have hsurj : Function.Surjective f :=
    decompK_restrict_surjective k K w L w' hw' f hf
  have hH1 : Subsingleton (extH (localUnitsK (k := k) w) 1) :=
    hilbert90_localUnits_extH k K w
  have hT2 : PTorsLE p (extH (localUnitsK (k := k) w) 2) :=
    pTorsLE_extH_two p k K w
  have hE2 := ext_two_trivial_ptors p (localUnitsK (k := k) w) hH1 hT2
  have hT : Nat.card {x : extH (NK.HassePrinciple.localUnitsRep k L w') 2 // p • x = 0} = p :=
    local_pTorsion_card p k L w' hp
  exact rightDetect_pgroup p hD f hsurj ι hT hE2.1 hE2.2
    (detect_h_trivial p k K w L w' hw' f hf ι hι hp) N hN

end Work.SSGRoute
