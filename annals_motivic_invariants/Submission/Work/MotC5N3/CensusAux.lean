import Mathlib
import ChallengeDeps
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotC5N3.AK
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotAS.CensusAS2Aux

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The generic AS census: interface and assembly

This module is the `K`-generic form of the corrected AS census of
`Submission/Work/MotAS/CensusAS2.lean` (the `RatFunc 𝕜` form), i.e. of node `G-LK` of
`MOTIVIC_CHAR5_N3_LEAD.md` §3.

The census `CensusAS2Gen K D hD g` is the *same* eleven-conjunct statement with

* `RatFunc 𝕜 ↦ K`, `Work.MotAS.aK D ↦ Work.MotC5N3.aK K D`, `Work.MotAS.bK D ↦ Work.MotC5N3.bK K D`,
* the class `Work.MotV.fAS 𝕜 ↦ g`,
* the explicit twist field `Work.MotAS.twistFieldAS D g ↦ Work.MotC5N3.twistFieldAS D g`
  (`Submission/Work/MotC5N3/Defs.lean`);

its conjuncts are supplied by

| conjunct | to be supplied by |
|---|---|
| `hpr`, `hht`, `hres` | `Work.MotC5N3.censusAS2_class_sdual` |
| `hS` | `Work.MotC5N3.censusAS2_class_sAS` |
| `linAS2` clause | `censusAS2_linAS` (below, from `a² − ab − b² ≠ 0`) |
| `cubAS2` clause | `censusAS2_cubAS_of_bwVec4` (below) |
| `fwVecAS2 · 0` junk | `Work.MotC5N3.JunkFwVec0` |
| `bwVecAS2 · 4` junk | `Work.MotC5N3.JunkBwVec4` |
| `FdivAS2 ≠ 0` | `FdivAS2_ne_zero_of` (below) |
| `GdivAS2 ≠ 0` | `GdivAS2_ne_zero_of` (below) |
| the chart isomorphism | `Work.MotC5N3.chartIsoAS2` |

**Everything else in the census is already generic** in the coordinates `(a, b, g)` and lives in
`Submission/Work/MotAS/{CensusAS2,CensusAS2Aux}.lean`, which this module imports: the chart data
`tchart`, `pAS0`, `fwVecAS2`, `bwVecAS2`, `linAS2`, `sAS2`, `cubAS2`, `sdualAS2`, `FdivAS2`,
`GdivAS2`, the identities `linAS2_eq_const`, `bwVecAS2_four_eq`, `cubAS2_eq`, and the
`FambAS2_eq`/`GambAS2_eq` factorisations.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.MotC5N3

open MvPolynomial

variable {𝕜 : Type} [Field 𝕜]

/-! ## §1 The polar factor `linAS2` is a unit -/

/-- `576` is `1` in `MvPolynomial (Fin 3) K` in characteristic `5`. -/
theorem num_576 (K : Type) [CommRing K] [CharP K 5] :
    (576 : MvPolynomial (Fin 3) K) = 1 := by
  have h2 : (576 : MvPolynomial (Fin 3) K) = C ((576 : ℕ) : K) := (map_natCast C 576).symm
  have h : ((576 : ℕ) : K) = 1 := by
    rw [show (576 : ℕ) = 5 * 115 + 1 from by norm_num, Nat.cast_add, Nat.cast_mul,
      CharP.cast_eq_zero K 5, zero_mul, zero_add, Nat.cast_one]
  rw [h2, h, map_one]

/-- `2` is a unit of `MvPolynomial (Fin 3) K` in characteristic `5` (its inverse is `288`). -/
theorem isUnit_two_poly (K : Type) [CommRing K] [CharP K 5] :
    IsUnit (2 : MvPolynomial (Fin 3) K) := by
  refine ⟨⟨2, 288, ?_, ?_⟩, rfl⟩
  · rw [show (2 * 288 : MvPolynomial (Fin 3) K) = 576 by norm_num, num_576 K]
  · rw [show (288 * 2 : MvPolynomial (Fin 3) K) = 576 by norm_num, num_576 K]

/-- `C c` is a unit as soon as `c ≠ 0`. -/
theorem isUnit_C {K : Type} [Field K] {c : K} (hc : c ≠ 0) :
    IsUnit (C c : MvPolynomial (Fin 3) K) :=
  ⟨⟨C c, C c⁻¹, by rw [← map_mul, mul_inv_cancel₀ hc, map_one],
    by rw [← map_mul, inv_mul_cancel₀ hc, map_one]⟩, rfl⟩

/-- **`linAS2 a b` is a unit** whenever `a ^ 2 - a * b - b ^ 2 ≠ 0` (it is the constant
`-2 (a² − ab − b²)`).  Generic form of `Work.MotAS.isUnit_linAS2`. -/
theorem isUnit_linAS2 {K : Type} [Field K] [CharP K 5] (a b : K)
    (hab : a ^ 2 - a * b - b ^ 2 ≠ 0) : IsUnit (Work.MotAS.linAS2 a b) := by
  rw [Work.MotAS.linAS2_eq_const]
  have hfac : (C a ^ 2 - C a * C b - C b ^ 2 : MvPolynomial (Fin 3) K)
      = C (a ^ 2 - a * b - b ^ 2) := by
    rw [map_sub, map_sub, map_mul, map_pow, map_pow]
  rw [hfac]
  exact (isUnit_two_poly K).neg.mul (isUnit_C hab)

/-- **The `linAS2` clause of the census is vacuous**: the polar factor is a unit, hence lies in no
proper prime ideal.  Generic form of `Work.MotAS.censusAS2_linAS`. -/
theorem censusAS2_linAS {K : Type} [Field K] [CharP K 5] (a b : K)
    (hab : a ^ 2 - a * b - b ^ 2 ≠ 0) :
    ∀ x : Work.MotA.polySpec K 3, Order.coheight x = 1 →
      Work.MotAS.linAS2 a b ∈ x.asIdeal → Work.MotV.JunkClass K x := by
  intro x _ hx
  exact absurd (Ideal.eq_top_of_isUnit_mem x.asIdeal hx (isUnit_linAS2 a b hab)) x.isPrime.ne_top

/-- **The `cubAS2` clause follows from the `bwVecAS2 · 4` clause.**  Generic form of
`Work.MotAS.censusAS2_cubAS_of_bwVec4`. -/
theorem censusAS2_cubAS_of_bwVec4 {K : Type} [Field K] [CharP K 5] (a b g : K)
    (hab : a ^ 2 - a * b - b ^ 2 ≠ 0)
    (hbw : ∀ x : Work.MotA.polySpec K 3, Order.coheight x = 1 →
      Work.MotAS.bwVecAS2 a b g 4 ∈ x.asIdeal → Work.MotV.JunkClass K x) :
    ∀ x : Work.MotA.polySpec K 3, Order.coheight x = 1 →
      Work.MotAS.cubAS2 a b g ∈ x.asIdeal → Work.MotV.JunkClass K x := by
  intro x hx hxc
  haveI : x.asIdeal.IsPrime := x.2
  rw [Work.MotAS.cubAS2_eq] at hxc
  rcases x.2.mem_or_mem hxc with h | h
  · exact absurd (Ideal.eq_top_of_isUnit_mem x.asIdeal h (isUnit_linAS2 a b hab)) x.isPrime.ne_top
  · exact hbw x hx h

/-- **The source divisor `FdivAS2` is nonzero** once the two non-unit factors are.  Generic form of
`Work.MotAS.FdivAS2_ne_zero_of`. -/
theorem FdivAS2_ne_zero_of {K : Type} [Field K] [CharP K 5] (a b g : K)
    (hab : a ^ 2 - a * b - b ^ 2 ≠ 0)
    (hfw : Work.MotAS.fwVecAS2 a b g 0 ≠ 0) (hs : Work.MotAS.sAS2 a b g ≠ 0) :
    Work.MotAS.FdivAS2 a b g ≠ 0 := by
  rw [Work.MotAS.FdivAS2]
  exact mul_ne_zero (mul_ne_zero (isUnit_linAS2 a b hab).ne_zero hs) hfw

/-- **The target divisor `GdivAS2` is nonzero** once the two non-unit factors are.  Generic form of
`Work.MotAS.GdivAS2_ne_zero_of`. -/
theorem GdivAS2_ne_zero_of {K : Type} [Field K] [CharP K 5] (a b g : K)
    (hab : a ^ 2 - a * b - b ^ 2 ≠ 0)
    (hbw : Work.MotAS.bwVecAS2 a b g 4 ≠ 0) (hsd : Work.MotAS.sdualAS2 a b g ≠ 0) :
    Work.MotAS.GdivAS2 a b g ≠ 0 := by
  rw [Work.MotAS.GdivAS2, Work.MotAS.cubAS2_eq]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (isUnit_linAS2 a b hab).ne_zero hbw) hsd) hbw

/-- `sdualAS2 a b g ≠ 0` from `Ideal.height (span {sdualAS2 a b g}) = 1`.  Generic form of
`Work.MotAS.sdualAS2_ne_zero_of_height`. -/
theorem sdualAS2_ne_zero_of_height {K : Type} [Field K] [CharP K 5] (a b g : K)
    (hht : Ideal.height (Ideal.span {Work.MotAS.sdualAS2 a b g}) = 1) :
    Work.MotAS.sdualAS2 a b g ≠ 0 := by
  intro h0
  rw [h0] at hht
  have hbot : (Ideal.span {(0 : MvPolynomial (Fin 3) K)} : Ideal (MvPolynomial (Fin 3) K))
      = ⊥ := Ideal.span_singleton_eq_bot.mpr rfl
  rw [hbot, Ideal.height_bot] at hht
  exact one_ne_zero hht.symm

/-! ## §2 The generic census

`CensusAS2Gen K D hD g` is `Work.MotAS.CensusAS2 D hD` with the base field `K` in place of
`RatFunc 𝕜`, the class `g` in place of `Work.MotV.fAS 𝕜`, and `Work.MotC5N3.twistFieldAS` in place
of `Work.MotAS.twistFieldAS`. -/

/-- **The generic AS census**: the eleven conjuncts of the corrected AS chart, over an arbitrary
`𝕜`-algebra field `K` of characteristic `5`. -/
def CensusAS2Gen (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜] [Algebra 𝕜 K]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K) : Prop :=
  ∃ (hpr : (Ideal.span {Work.MotAS.sdualAS2 (aK K D) (bK K D) g} :
      Ideal (MvPolynomial (Fin 3) K)).IsPrime),
    Ideal.height (Ideal.span {Work.MotAS.sdualAS2 (aK K D) (bK K D) g}) = 1 ∧
    Nonempty (Work.MotV.resF K
        ⟨Ideal.span {Work.MotAS.sdualAS2 (aK K D) (bK K D) g}, hpr⟩ ≃ₐ[K]
      RatFunc ↥(twistFieldAS D g)) ∧
  (∀ x : Work.MotA.polySpec K 3, Order.coheight x = 1 →
      Work.MotAS.sAS2 (aK K D) (bK K D) g ∈ x.asIdeal →
    Nonempty (Work.MotV.resF K x ≃ₐ[K] RatFunc ↥(twistFieldAS D (2 • g))) ∨
      Work.MotV.JunkClass K x) ∧
  (∀ x : Work.MotA.polySpec K 3, Order.coheight x = 1 →
      Work.MotAS.linAS2 (aK K D) (bK K D) ∈ x.asIdeal → Work.MotV.JunkClass K x) ∧
  (∀ x : Work.MotA.polySpec K 3, Order.coheight x = 1 →
      Work.MotAS.cubAS2 (aK K D) (bK K D) g ∈ x.asIdeal →
        Work.MotV.JunkClass K x) ∧
  (∀ x : Work.MotA.polySpec K 3, Order.coheight x = 1 →
      Work.MotAS.fwVecAS2 (aK K D) (bK K D) g 0 ∈ x.asIdeal →
        Work.MotV.JunkClass K x) ∧
  (∀ x : Work.MotA.polySpec K 3, Order.coheight x = 1 →
      Work.MotAS.bwVecAS2 (aK K D) (bK K D) g 4 ∈ x.asIdeal →
        Work.MotV.JunkClass K x) ∧
  Work.MotAS.FdivAS2 (aK K D) (bK K D) g ≠ 0 ∧
  Work.MotAS.GdivAS2 (aK K D) (bK K D) g ≠ 0 ∧
  Nonempty (Localization.Away (Work.MotAS.FdivAS2 (aK K D) (bK K D) g) ≃ₐ[K]
    Localization.Away (Work.MotAS.GdivAS2 (aK K D) (bK K D) g))

/-- **The generic census implies the generic certificate**, by the *same* eleven-tuple
construction as `Work.MotAS.linkCertAS_of_censusAS2`. -/
theorem linkCertAS_of_censusAS2_gen (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜]
    [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K)
    (hc : CensusAS2Gen K D hD g) :
    Nonempty (Work.MotV.LinkCert K ↥(twistFieldAS D g) ↥(twistFieldAS D (2 • g))) := by
  obtain ⟨hpr, hht, hres, hS, hLin, hCub, hFw, hBw, hFne, hGne, hΦ⟩ := hc
  have hcoh : ∀ x : Work.MotA.polySpec K 3, Order.coheight x = 1 →
      Ideal.height x.asIdeal = 1 := fun x hx =>
    (AlgebraicGeometry.idealHeight_eq_coheight
      (CommRingCat.of (MvPolynomial (Fin 3) K)) x).trans hx
  let zP : Work.MotA.polySpec K 3 :=
    ⟨Ideal.span {Work.MotAS.sdualAS2 (aK K D) (bK K D) g}, hpr⟩
  have hzP_ht : Order.coheight zP = 1 := by
    rw [← AlgebraicGeometry.idealHeight_eq_coheight
      (CommRingCat.of (MvPolynomial (Fin 3) K)) zP]
    exact hht
  refine ⟨{ F := Work.MotAS.FdivAS2 (aK K D) (bK K D) g
            G := Work.MotAS.GdivAS2 (aK K D) (bK K D) g
            hF := hFne
            hG := hGne
            Φ := Classical.choice hΦ
            zP := zP
            zP_ht := hzP_ht
            zP_mem := ?_
            zP_res := hres
            G_other := ?_
            F_all := ?_ }⟩
  · have hmul : Work.MotAS.cubAS2 (aK K D) (bK K D) g
        * Work.MotAS.sdualAS2 (aK K D) (bK K D) g
        * Work.MotAS.bwVecAS2 (aK K D) (bK K D) g 4
        ∈ Ideal.span {Work.MotAS.sdualAS2 (aK K D) (bK K D) g} :=
      Ideal.mul_mem_right _ _
        (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    exact hmul
  · intro x hcx hxG hxne
    haveI hxprime : x.asIdeal.IsPrime := x.2
    have hxG' : Work.MotAS.cubAS2 (aK K D) (bK K D) g
        * Work.MotAS.sdualAS2 (aK K D) (bK K D) g
        * Work.MotAS.bwVecAS2 (aK K D) (bK K D) g 4 ∈ x.asIdeal := hxG
    have h1 : Work.MotAS.cubAS2 (aK K D) (bK K D) g
        * Work.MotAS.sdualAS2 (aK K D) (bK K D) g ∈ x.asIdeal
        ∨ Work.MotAS.bwVecAS2 (aK K D) (bK K D) g 4 ∈ x.asIdeal :=
      hxprime.mem_or_mem hxG'
    rcases h1 with hcs | hbw
    · have h2 : Work.MotAS.cubAS2 (aK K D) (bK K D) g ∈ x.asIdeal
          ∨ Work.MotAS.sdualAS2 (aK K D) (bK K D) g ∈ x.asIdeal :=
        hxprime.mem_or_mem hcs
      rcases h2 with hc | hs
      · exact hCub x hcx hc
      · exact absurd (PrimeSpectrum.ext
          (Work.MotK.CensusPrime.eq_span_of_height_one _ hpr hht x.asIdeal (hcoh x hcx) hs)) hxne
    · exact hBw x hcx hbw
  · intro x hcx hxF
    haveI hxprime : x.asIdeal.IsPrime := x.2
    have hxF' : Work.MotAS.linAS2 (aK K D) (bK K D) * Work.MotAS.sAS2 (aK K D) (bK K D) g
        * Work.MotAS.fwVecAS2 (aK K D) (bK K D) g 0 ∈ x.asIdeal := hxF
    have h1 : Work.MotAS.linAS2 (aK K D) (bK K D) * Work.MotAS.sAS2 (aK K D) (bK K D) g
          ∈ x.asIdeal
        ∨ Work.MotAS.fwVecAS2 (aK K D) (bK K D) g 0 ∈ x.asIdeal :=
      hxprime.mem_or_mem hxF'
    rcases h1 with hls | hfw
    · have h2 : Work.MotAS.linAS2 (aK K D) (bK K D) ∈ x.asIdeal
          ∨ Work.MotAS.sAS2 (aK K D) (bK K D) g ∈ x.asIdeal :=
        hxprime.mem_or_mem hls
      rcases h2 with hl | hs
      · exact Or.inr (hLin x hcx hl)
      · exact hS x hcx hs
    · exact Or.inr (hFw x hcx hfw)

end Work.MotC5N3
