/-
# `Work.FIArea6Hecke.R.heckeZFRrealAxisP_of_psiReal`

**Lemma 16.1 (*FI*, Landau–Siegel) on the real axis, with the hypothesis "`ψ` is real" in the
correct (primary) form.**

`ZFRStatementDefs.ZFRrealAxis ε` is the Siegel input for strict characters `χ` modulo `4d` whose
Größencharacter `ψ_{χ,m}(z) = χ(z)(z/|z|)^m` is real on *all* of `ℤ[i]` (`PsiReal`); the target of
this file is the same statement `ZFRrealAxisP ε` for the weaker, correct hypothesis
`PsiRealPrimary`, i.e. realness on the *primary* elements only — exactly the values that the Hecke
eigenvalues `λ(n) = Σ_{z primary, |z|²=n} ψ(z)`, and hence the `L`-series, see.

The reduction has three steps.

* **`m = 0`** (`zpr_m_eq_zero_of_psiRealPrimary`).  Realness of `ψ` on the primary elements at the
  single point `z = 1 + 4d·i` (primary, and a unit modulo `4d`, so that periodicity of `χ` gives
  `χ z = χ 1 = 1`) forces `m = 0`, by the root-of-unity argument of `R/m_eq_zero_of_psiReal`.

* **The real partner `χ'(z) = χ(primAssoc z)`** (`R/chiPrimeDefs`, on the units modulo `4d` and `0`
  off them).  With `m = 0`, `PsiRealPrimary χ 0` says `χ` is real on the primary elements, and then
  `χ'` is a *real valued* strict character modulo `4d` with the same Hecke eigenvalues, hence the
  same `L`-series (`zpr_chiPrime_strict_real_series`).  The arithmetic content is the *periodicity*
  of `χ'` modulo `4d`: for odd `z` one has `primAssoc z = z·star(primaryUnit z)`
  (`zpr_primAssoc_eq_mul_star_primaryUnit`), the normalising unit depends only on the class modulo
  `4d` (`FIArea5/S16Hecke/twistAux.primaryUnit_periodic`), and `χ` itself is periodic modulo `4d`.

* **Transfer of the zero-free region.**  Given an entire completion `Λ` of `(d, χ, 0)`, the
  nontriviality hypothesis needed in order to complete the pair `(d, χ', 0)` is *forced*: if
  `ψ_{χ',0}` were `1` on the primary units then `Λ` would be an entire completion of the
  trivial-character pair, which is impossible (`R/noCompletion_of_primaryTrivial`).  So
  `R/heckeCompletionImprimitive` produces an entire `Λ'` completing `(d, χ', 0)`, the Siegel input
  `ZFRrealAxis ε` applies to *that* pair (it is a `PsiReal` pair), and the two `L`-values agree on
  the half-plane `re s > 0` (`zpr_lval_eq_of_same_series`, the identity theorem for entire
  completions of the same `L`-series).  Shrinking `c` to `min c 1` puts the region inside
  `re s > 0`, where that identification is available.

The analytic `zpr_`-lemmas are copies of `R/lvalSameSeries.analyticOn_heckeArch_pos` and
`R/lvalSameSeries.lval_eq_of_same_series` (via `R/zerosInStrip.eqOn_of_agrees_halfplane`), and the
arithmetic `zpr_`-lemmas are the `SelfDual`-free parts of `R/chiPrimeSelfDual` and
`R/selfDualRealTransfer`; both are re-proved here because those modules sit *above*
`R/logDerivCore`, which imports this file, so they cannot be imported here.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.ZFRStatementDefs
import Submission.Work.FIArea6Hecke.R.exists_realCharacter_agreeing_on_primary
import Submission.Work.FIArea6Hecke.R.chiPrimeDefs
import Submission.Work.FIArea6Hecke.R.chiPrimeAgree
import Submission.Work.FIArea6Hecke.R.m_eq_zero_of_psiReal
import Submission.Work.FIArea6Hecke.R.heckeStripNearOne
import Submission.Work.FIArea6Hecke.R.heckeCompletionImprimitive
import Submission.Work.FIArea6Hecke.R.noCompletion_of_primaryTrivial
import Submission.Work.FIArea6Hecke.R.LamOneNeZeroDefs
import Submission.Work.FIArea5.S16Hecke.twistAux
import Submission.Work.FIArea6Hecke.area5_6_of_S16Core
import Submission.Work.FIArea4.GaussMoebiusCore

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators Topology

noncomputable section

/-! ## 1. The arithmetic core: the real partner of a character real on the primary elements -/

/-- **A unit modulo `4d` has odd norm**: `IsUnitMod4d d z` says that `gnorm z` is coprime to `4d`,
in particular odd. -/
theorem zpr_odd_gnorm_of_isUnitMod4d {d : ℕ} (hd : 1 ≤ d) {z : GaussianInt}
    (hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z) : Odd (Work.FIPlan.gnorm z) := by
  have hNe : NeZero (4 * d) := ⟨by omega⟩
  haveI := hNe
  have hcop : (Work.FIPlan.gnorm z).Coprime (4 * d) :=
    (Work.FIArea6Hecke.GaussUnit.isUnitMod4d_iff_coprime (d := d) z).mp hz
  rw [← Nat.not_even_iff_odd]
  intro h2
  have h2' : 2 ∣ Work.FIPlan.gnorm z := even_iff_two_dvd.mp h2
  have h4d : 2 ∣ 4 * d := dvd_mul_of_dvd_left (by norm_num : (2 : ℕ) ∣ 4) d
  have hgcd : 2 ∣ Nat.gcd (Work.FIPlan.gnorm z) (4 * d) := Nat.dvd_gcd h2' h4d
  rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at hgcd
  norm_num at hgcd

/-- A unit modulo `4d` is *odd* in the sense of `isOddG`. -/
theorem zpr_isOddG_of_isUnitMod4d {d : ℕ} (hd : 1 ≤ d) {z : GaussianInt}
    (hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z) : Work.FIArea5.S16Hecke.isOddG z :=
  (Work.FIArea5.S16Hecke.GaussBasic.isOddG_iff_odd z).mpr
    ((Work.FIArea5.S16Hecke.odd_gnorm_iff z).mp (zpr_odd_gnorm_of_isUnitMod4d hd hz))

/-- `u · star u = 1` for the four units of `ℤ[i]`. -/
theorem zpr_star_mul_self_of_mem_units4 {u : GaussianInt}
    (hu : u ∈ Work.FIArea5.S16Hecke.units4) : u * star u = 1 := by
  rw [Work.FIArea5.S16Hecke.mem_units4_iff] at hu
  rcases hu with rfl | rfl | rfl | rfl <;> decide

/-- `star u · u = 1` for the four units of `ℤ[i]`. -/
theorem zpr_mul_star_comm_of_mem_units4 {u : GaussianInt}
    (hu : u ∈ Work.FIArea5.S16Hecke.units4) : star u * u = 1 := by
  rw [mul_comm]; exact zpr_star_mul_self_of_mem_units4 hu

/-- **The primary associate is the `(1+i)³`-normalisation of `z`.**  For an odd `z` the unique
unit `u ∈ μ₄` with `u ≡ z (mod (1+i)³)` (`Work.FIArea5.S16Hecke.primaryUnit`) satisfies
`z · star u = primAssoc z`: writing `z = a·p` with `a ∈ μ₄` and `p` primary, one gets `star a = a⁻¹`
and `z·star a = p`. -/
theorem zpr_primAssoc_eq_mul_star_primaryUnit {z : GaussianInt}
    (hz : Work.FIArea5.S16Hecke.isOddG z) :
    Work.FIArea4.primAssoc z = z * star (Work.FIArea5.S16Hecke.primaryUnit z) := by
  obtain ⟨a, ha, p, hp, hzp⟩ := Work.FIArea5.S16Hecke.exists_unit_primary z hz
  have hpu : Work.FIArea5.S16Hecke.primaryUnit z = a := by
    refine Work.FIArea5.S16Hecke.primaryUnit_eq_of_dvd ha ?_
    have h1 : Work.FIArea5.S16Hecke.c3 ∣ p - 1 :=
      Work.FIArea5.S16Hecke.c3_dvd_sub_one_of_isPrimary hp
    have h2 : z - a = a * (p - 1) := by rw [hzp]; ring
    rw [h2]
    exact dvd_mul_of_dvd_right h1 a
  have hsa : a * star a = 1 := zpr_star_mul_self_of_mem_units4 ha
  have hzp' : z * star a = p := by
    rw [hzp]
    calc (a * p) * star a = p * (a * star a) := by ring
      _ = p := by rw [hsa, mul_one]
  have hprim : Work.FIPlan.IsPrimary (z * star (Work.FIArea5.S16Hecke.primaryUnit z)) := by
    rw [hpu, hzp']; exact hp
  have hodd : Odd (Work.FIPlan.gnorm z) := Work.FIArea5.S16Hecke.isOddG_gnorm_odd z hz
  have hz0 : z ≠ 0 := ne_zero_of_odd_gnorm hodd
  have hassoc : Associated (z * star (Work.FIArea5.S16Hecke.primaryUnit z)) z := by
    rw [hpu]
    obtain ⟨u, hu⟩ := Work.FIArea5.S16Hecke.isUnit_of_mem_units4 ha
    refine ⟨u, ?_⟩
    rw [hu]
    calc z * star a * a = z * (star a * a) := by ring
      _ = z := by rw [zpr_mul_star_comm_of_mem_units4 ha, mul_one]
  exact (primAssoc_unique_of_odd hz0 hodd hassoc hprim).symm

/-- **`χ'(z) = χ (primAssoc z)` is periodic modulo `4d`.**  For units `z ≡ w (mod 4d)` the
normalising units `primaryUnit z = primaryUnit w` agree
(`Work.FIArea5.S16Hecke.primaryUnit_periodic`), so
`χ (primAssoc z) = χ z · χ (star u) = χ w · χ (star u) = χ (primAssoc w)`. -/
theorem zpr_chiPrime_periodic {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi) :
    ∀ z w : GaussianInt, Work.FIArea6Hecke.fourDZFR d ∣ (z - w) →
      chiPrime d chi z = chiPrime d chi w := by
  intro z w hzw
  by_cases hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z
  · have hw : Work.FIArea5.S16Hecke.IsUnitMod4d d w :=
      (Work.FIArea6Hecke.isUnitMod4d_congr' hzw).mp hz
    have hoddz : Work.FIArea5.S16Hecke.isOddG z := zpr_isOddG_of_isUnitMod4d hd hz
    have hoddw : Work.FIArea5.S16Hecke.isOddG w := zpr_isOddG_of_isUnitMod4d hd hw
    have hpuz : Work.FIArea5.S16Hecke.primaryUnit z = Work.FIArea5.S16Hecke.primaryUnit w :=
      Work.FIArea5.S16Hecke.primaryUnit_periodic hzw
    rw [chiPrime_of_unit hz, chiPrime_of_unit hw,
      zpr_primAssoc_eq_mul_star_primaryUnit hoddz,
      zpr_primAssoc_eq_mul_star_primaryUnit hoddw, hpuz,
      hchi.1.2.1, hchi.1.2.1, hchi.1.2.2.2.1 z w hzw]
  · have hw : ¬ Work.FIArea5.S16Hecke.IsUnitMod4d d w :=
      fun h => hz ((Work.FIArea6Hecke.isUnitMod4d_congr' hzw).mpr h)
    rw [chiPrime_of_not_unit hz, chiPrime_of_not_unit hw]

/-- **`chiPrime d χ` is a character modulo `4d`** (in the sense of `Work.FITop3.IsCharMod4d`). -/
theorem zpr_chiPrime_isCharMod4d {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi) :
    Work.FITop3.IsCharMod4d d (chiPrime d chi) := by
  have hper := zpr_chiPrime_periodic hd hchi
  obtain ⟨⟨h1, hmul, hb, _hper, _hzero⟩, _hoff⟩ := hchi
  refine ⟨?_, ?_, ?_, hper, ?_⟩
  · rw [chiPrime_of_unit (Work.FIArea6Hecke.isUnitMod4d_one d),
      Work.FIArea4.primAssoc_eq_self Work.FIArea5.S16Hecke.isPrimary_one, h1]
  · intro z w
    by_cases hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z
    · by_cases hw : Work.FIArea5.S16Hecke.IsUnitMod4d d w
      · rw [chiPrime_of_unit (Work.FIArea6Hecke.isUnitMod4d_mul_iff.mpr ⟨hz, hw⟩),
          chiPrime_of_unit hz, chiPrime_of_unit hw,
          primAssoc_mul_odd (zpr_odd_gnorm_of_isUnitMod4d hd hz)
            (zpr_odd_gnorm_of_isUnitMod4d hd hw)]
        exact hmul _ _
      · rw [chiPrime_of_not_unit hw, mul_zero,
          chiPrime_of_not_unit (fun h => hw (Work.FIArea6Hecke.isUnitMod4d_mul_iff.mp h).2)]
    · rw [chiPrime_of_not_unit hz, zero_mul,
        chiPrime_of_not_unit (fun h => hz (Work.FIArea6Hecke.isUnitMod4d_mul_iff.mp h).1)]
  · intro z
    by_cases hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z
    · rw [chiPrime_of_unit hz]; exact hb (Work.FIArea4.primAssoc z)
    · rw [chiPrime_of_not_unit hz]; simp
  · intro z hz
    exact chiPrime_of_not_unit (Work.FIArea6Hecke.not_isUnitMod4d_of_dvd hd hz)

/-- **`chiPrime d χ` is real valued when `χ` is real on the primary elements**: on a unit `z` its
value is `χ (primAssoc z)`, and `primAssoc z` is primary. -/
theorem zpr_chiPrime_real {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hreal : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z → star (chi z) = chi z) :
    ∀ z : GaussianInt, star (chiPrime d chi z) = chiPrime d chi z := by
  intro z
  by_cases hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z
  · rw [chiPrime_of_unit hz]
    have hodd := zpr_odd_gnorm_of_isUnitMod4d hd hz
    exact hreal _ (Work.FIArea4.primAssoc_primary (ne_zero_of_odd_gnorm hodd) hodd)
  · rw [chiPrime_of_not_unit hz]; simp

/-- **The L-series of `chiPrime d χ` is that of `χ`**: `χ'` agrees with `χ` on the primary elements
(primary units via `primAssoc z = z`, primary non-units because both vanish there by strictness),
and the Hecke eigenvalues only see the primary values. -/
theorem zpr_chiPrime_heckeLSeries {d : ℕ} {chi : GaussianInt → ℂ}
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi) :
    Work.FIArea5.S16Hecke.heckeLSeries (chiPrime d chi) 0
      = Work.FIArea5.S16Hecke.heckeLSeries chi 0 := by
  have hlam : ∀ n : ℕ, Work.FIArea5.S16Hecke.heckeLam (chiPrime d chi) 0 n
      = Work.FIArea5.S16Hecke.heckeLam chi 0 n := by
    intro n
    refine heckeLam_eq_of_primary_agree (chi := chiPrime d chi) (chi' := chi) (k := 0) ?_ n
    intro z hzp
    by_cases hzu : Work.FIArea5.S16Hecke.IsUnitMod4d d z
    · exact chiPrime_eq_chi_of_primary hzp hzu
    · rw [chiPrime_of_not_unit hzu, hchi.2 z hzu]
  unfold Work.FIArea5.S16Hecke.heckeLSeries
  exact funext (fun s => LSeries_congr (fun {n} _ => hlam n) s)

/-- **The transfer package**: a strict character `χ` modulo `4d` which is real on the primary
elements has a real-valued strict partner `chiPrime d χ` with the same `L`-series. -/
theorem zpr_chiPrime_strict_real_series {d : ℕ} {chi : GaussianInt → ℂ}
    (hd : 1 ≤ d) (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hreal : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z → star (chi z) = chi z) :
    Work.FIArea5.S16Hecke.IsCharMod4dStrict d (chiPrime d chi) ∧
      (∀ z : GaussianInt, star (chiPrime d chi z) = chiPrime d chi z) ∧
      Work.FIArea5.S16Hecke.heckeLSeries (chiPrime d chi) 0
        = Work.FIArea5.S16Hecke.heckeLSeries chi 0 :=
  ⟨⟨zpr_chiPrime_isCharMod4d hd hchi, fun z hz => chiPrime_of_not_unit hz⟩,
    zpr_chiPrime_real hd hreal, zpr_chiPrime_heckeLSeries hchi⟩

/-- **Realness on the primary elements forces the weight `m` to vanish** (test point `1 + 4d·i`).

The test point `z = 1 + 4d·i` is primary, is a unit modulo `4d` (as `4d ∣ z - 1`), and by
periodicity of the strict character `χ z = χ 1 = 1`; realness of `ψ_{χ,m}(z) = (z/|z|)^m` there gives
`(z/z̄)^m = 1`, so `w := z/z̄ = (1+4d·i)/(1-4d·i) ∈ ℚ(i)` is a root of unity, hence one of `±1, ±i`
(`R/rootOfUnityRatIsFourth`) — but it has both coordinates nonzero. -/
theorem zpr_m_eq_zero_of_psiRealPrimary {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi) {m : ℤ}
    (h : Work.FIArea6Hecke.R.PsiRealPrimary chi m) : m = 0 := by
  by_contra hm0
  obtain ⟨hchar, _⟩ := hchi
  obtain ⟨h1, _, _, hper, _⟩ := hchar
  -- the test point `z = 1 + 4d·i`, which is `≡ 1` modulo `4d`
  set z : GaussianInt := ⟨1, ((4*d:ℕ):ℤ)⟩ with hz
  have hdiv : (((4 * d : ℕ) : ℤ) : GaussianInt) ∣ (z - 1) := by
    rw [hz, Zsqrtd.intCast_dvd]
    exact ⟨dvd_zero _, by simpa using dvd_refl ((4 * d : ℕ) : ℤ)⟩
  have hchiz : chi z = 1 := (hper z 1 hdiv).trans h1
  have hZval : z.toComplex = (1:ℂ) + ((4*d:ℕ):ℂ) * Complex.I := by
    rw [hz, GaussianInt.toComplex_def']
    push_cast
    ring
  have hpsi : Work.FIArea5.S16Hecke.psi chi m z =
      (z.toComplex / ((Real.sqrt (Work.FIPlan.gnorm z : ℝ)) : ℂ)) ^ m := by
    rw [Work.FIArea5.S16Hecke.psi, hchiz, one_mul]
  -- `z` is primary
  have hzp : Work.FIPlan.IsPrimary z := by
    rw [hz]
    refine ⟨⟨0, by norm_num⟩, ⟨2*d, by push_cast; ring⟩, ?_⟩
    rw [Int.modEq_iff_dvd]
    exact ⟨-d, by push_cast; ring⟩
  have hreal : star ((z.toComplex / ((Real.sqrt (Work.FIPlan.gnorm z : ℝ)) : ℂ)) ^ m) =
      (z.toComplex / ((Real.sqrt (Work.FIPlan.gnorm z : ℝ)) : ℂ)) ^ m := by
    have h' := h z hzp
    rwa [hpsi] at h'
  have hc : star ((Real.sqrt (Work.FIPlan.gnorm z : ℝ)) : ℂ) =
      ((Real.sqrt (Work.FIPlan.gnorm z : ℝ)) : ℂ) := by simp
  have hZ0 : z.toComplex ≠ 0 := by
    rw [hZval]
    intro hh
    have := congrArg Complex.re hh
    simp at this
  have hc0 : ((Real.sqrt (Work.FIPlan.gnorm z : ℝ)) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    intro hh
    have h2 : ‖z.toComplex‖ = 0 := by
      rw [Work.FIArea5.S16Hecke.norm_toComplex, hh]
    exact hZ0 (norm_eq_zero.mp h2)
  -- `(z/z̄)^m = 1`
  have hw1 : (z.toComplex / star z.toComplex) ^ m = 1 :=
    zpow_div_conj_eq_one_of_star_eq hc hc0 hZ0 hreal
  have hn : 0 < m.natAbs := Int.natAbs_pos.mpr hm0
  have hwn : (z.toComplex / star z.toComplex) ^ m.natAbs = 1 :=
    zpow_eq_one_natAbs_of_zpow_eq_one hw1
  have hw : z.toComplex / star z.toComplex =
      ((1:ℂ) + ((4*d:ℕ):ℂ) * Complex.I) /
        star ((1:ℂ) + ((4*d:ℕ):ℂ) * Complex.I) := by
    rw [hZval]
  rw [hw] at hwn
  -- `z/z̄` is a root of unity with rational coordinates, hence one of `1, -1, i, -i`
  obtain ⟨a, b, hre, him, ha0, hb0⟩ := div_conj_one_add_4di_rat d hd
  rcases rootOfUnityRatIsFourth
      (((1:ℂ) + ((4*d:ℕ):ℂ) * Complex.I) /
        star ((1:ℂ) + ((4*d:ℕ):ℂ) * Complex.I))
      a b hre him m.natAbs hn hwn with h' | h' | h' | h'
  · exact hb0 (by
      have hzero : (b:ℝ) = 0 := by rw [← him, h']; simp
      exact_mod_cast hzero)
  · exact hb0 (by
      have hzero : (b:ℝ) = 0 := by rw [← him, h']; simp
      exact_mod_cast hzero)
  · exact ha0 (by
      have hzero : (a:ℝ) = 0 := by rw [← hre, h']; simp
      exact_mod_cast hzero)
  · exact ha0 (by
      have hzero : (a:ℝ) = 0 := by rw [← hre, h']; simp
      exact_mod_cast hzero)

/-! ## 2. The analytic core: the identity theorem on a half-plane, and transport of `Lval` -/

/-- **The identity theorem on a half-plane**: two functions analytic on `{re s > T}`, agreeing on
the sub-half-plane `{re s > T'}` with `T ≤ T'`, agree on `{re s > T}`. -/
lemma zpr_eqOn_of_agrees_halfplane {F G : ℂ → ℂ} {T T' : ℝ} (hTT : T ≤ T')
    (hF : AnalyticOn ℂ F {z : ℂ | T < z.re}) (hG : AnalyticOn ℂ G {z : ℂ | T < z.re})
    (h : ∀ s : ℂ, T' < s.re → F s = G s) :
    ∀ s : ℂ, T < s.re → F s = G s := by
  set U : Set ℂ := {z : ℂ | T < z.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconv : Convex ℝ U := by
    have h := (convex_Ioi T).linear_preimage (Complex.reCLM : ℂ →ₗ[ℝ] ℝ)
    have h2 : (Complex.reCLM : ℂ →ₗ[ℝ] ℝ) ⁻¹' (Set.Ioi T) = U := by
      ext z; simp [hU]
    rwa [h2] at h
  have hUpre : IsPreconnected U := hUconv.isPreconnected
  have hF' : AnalyticOnNhd ℂ F U := hF.differentiableOn.analyticOnNhd hUopen
  have hG' : AnalyticOnNhd ℂ G U := hG.differentiableOn.analyticOnNhd hUopen
  have hz₀ : (((T' + 1 : ℝ)) : ℂ) ∈ U := by
    rw [hU, Set.mem_ofPred_eq, Complex.ofReal_re]; linarith
  have hev : F =ᶠ[𝓝 (((T' + 1 : ℝ)) : ℂ)] G := by
    have hmem : {z : ℂ | T' < z.re} ∈ 𝓝 (((T' + 1 : ℝ)) : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
        rw [Set.mem_ofPred_eq, Complex.ofReal_re]; linarith)
    exact Filter.eventually_of_mem hmem (fun z hz => h z hz)
  intro s hs
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hF' hG' hUpre hz₀ hev hs

/-- `heckeArch d m` is analytic on the half-plane `re s > 0`. -/
theorem zpr_analyticOn_heckeArch_pos (d : ℕ) (hd : 1 ≤ d) (m : ℤ) :
    AnalyticOn ℂ (Work.FITop4.Bridge.heckeArch d m) {z : ℂ | 0 < z.re} := by
  refine DifferentiableOn.analyticOn (fun w hw => ?_)
    (isOpen_lt continuous_const Complex.continuous_re)
  exact (Work.FIArea6Hecke.R.heckeArch_differentiableAt_of_pos hd m hw).differentiableWithinAt

/-- **Transport of the `L`-value between two entire completions with the same `L`-series.**  If
`Lam` is entire and completes `(χ, m)` and `Lam'` is entire and completes `(χ', 0)` with
`L(·,χ') = L(·,χ, m)`, then `Lval d m Lam = Lval d 0 Lam'` on the half-plane `re s > 0`: both sides
are analytic there and agree on `re s > 1 + |m|/2`. -/
theorem zpr_lval_eq_of_same_series {d : ℕ} {chi chi' : GaussianInt → ℂ} {m : ℤ}
    {Lam Lam' : ℂ → ℂ} (hd : 1 ≤ d)
    (hAn : AnalyticOn ℂ Lam Set.univ) (hAn' : AnalyticOn ℂ Lam' Set.univ)
    (hagr : ∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
      Lam s = Work.FITop4.Bridge.heckeArch d m s *
        Work.FIArea5.S16Hecke.heckeLSeries chi m s)
    (hagr' : ∀ s : ℂ, 1 < s.re →
      Lam' s = Work.FITop4.Bridge.heckeArch d 0 s *
        Work.FIArea5.S16Hecke.heckeLSeries chi' 0 s)
    (hL : Work.FIArea5.S16Hecke.heckeLSeries chi' 0
      = Work.FIArea5.S16Hecke.heckeLSeries chi m) :
    ∀ w : ℂ, 0 < w.re → Work.FIArea6Hecke.Lval d m Lam w
      = Work.FIArea6Hecke.Lval d 0 Lam' w := by
  have hF : AnalyticOn ℂ (fun w => Lam w / Work.FITop4.Bridge.heckeArch d m w)
      {z : ℂ | 0 < z.re} :=
    AnalyticOn.div (hAn.mono (Set.subset_univ _)) (zpr_analyticOn_heckeArch_pos d hd m)
      (fun w hw => Work.FIArea6Hecke.heckeArch_ne_zero_of_pos_re hd m hw)
  have hG : AnalyticOn ℂ (fun w => Lam' w / Work.FITop4.Bridge.heckeArch d 0 w)
      {z : ℂ | 0 < z.re} :=
    AnalyticOn.div (hAn'.mono (Set.subset_univ _)) (zpr_analyticOn_heckeArch_pos d hd 0)
      (fun w hw => Work.FIArea6Hecke.heckeArch_ne_zero_of_pos_re hd 0 hw)
  refine zpr_eqOn_of_agrees_halfplane
    (F := fun w => Lam w / Work.FITop4.Bridge.heckeArch d m w)
    (G := fun w => Lam' w / Work.FITop4.Bridge.heckeArch d 0 w) (T := 0)
    (T' := max 1 (1 + |(m : ℝ)| / 2)) (le_trans zero_le_one (le_max_left _ _)) hF hG ?_
  intro s hs
  have hs1 : 1 < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hs2 : 1 + |(m : ℝ)| / 2 < s.re := lt_of_le_of_lt (le_max_right _ _) hs
  have hs0 : 0 < s.re := lt_trans one_pos hs1
  rw [hagr s hs2, hagr' s hs1, hL]
  rw [mul_div_cancel_left₀ _ (Work.FIArea6Hecke.heckeArch_ne_zero_of_pos_re hd m hs0),
    mul_div_cancel_left₀ _ (Work.FIArea6Hecke.heckeArch_ne_zero_of_pos_re hd 0 hs0)]

/-! ## 3. The target -/

theorem heckeZFRrealAxisP_of_psiReal (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4)
    (h : Work.FIArea6Hecke.R.ZFRrealAxis ε) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ), 1 ≤ d →
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        AnalyticOn ℂ Lam Set.univ →
        (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
          Lam s = Work.FITop4.Bridge.heckeArch d m s *
            Work.FIArea5.S16Hecke.heckeLSeries chi m s) →
        Work.FIArea6Hecke.R.PsiRealPrimary chi m →
        ∀ s : ℂ, s.im = 0 →
          1 - c / (d : ℝ) ^ ε < s.re → s.re ≤ 2 →
          Work.FIArea6Hecke.Lval d m Lam s ≠ 0 := by
  obtain ⟨c, hcpos, hreg⟩ := h
  refine ⟨min c 1, lt_min hcpos one_pos, ?_⟩
  intro d chi m Lam hd hchi hAn hagr hrp s hsim hs1 hs2
  -- ## Step 1: `PsiRealPrimary` forces the weight `m` to vanish
  have hm0 : m = 0 := zpr_m_eq_zero_of_psiRealPrimary hd hchi hrp
  subst hm0
  -- ## Step 2: the real partner `chiPrime d chi`
  have hpru : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z → star (chi z) = chi z := by
    intro z hzp
    have h' := hrp z hzp
    have hpsi : Work.FIArea5.S16Hecke.psi chi 0 z = chi z := by
      rw [Work.FIArea5.S16Hecke.psi, zpow_zero, mul_one]
    rw [hpsi] at h'
    exact h'
  obtain ⟨hchi', hreal', hLser⟩ : Work.FIArea5.S16Hecke.IsCharMod4dStrict d (chiPrime d chi) ∧
      (∀ z : GaussianInt, star (chiPrime d chi z) = chiPrime d chi z) ∧
      Work.FIArea5.S16Hecke.heckeLSeries (chiPrime d chi) 0
        = Work.FIArea5.S16Hecke.heckeLSeries chi 0 :=
    zpr_chiPrime_strict_real_series hd hchi hpru
  -- ## Step 3: complete the real pair and transport the region
  -- the completion of `(d, chiPrime d chi, 0)` exists: `ψ` is nontrivial on the primary units,
  -- since otherwise `Λ` itself would be an entire completion of the trivial character pair
  have hne : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
      Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧
      Work.FIArea5.S16Hecke.psi (chiPrime d chi) 0 z ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    refine noCompletion_of_primaryTrivial d (chiPrime d chi) 0 hd hchi' ?_
      ⟨Lam, hAn, ?_⟩
    · intro z hzp hzu
      exact hcon z hzp hzu
    · intro t ht
      rw [hagr t ht, hLser]
  obtain ⟨Lam', hAn', hagr'⟩ := heckeCompletionImprimitive d (chiPrime d chi) 0 hd hchi' hne
  -- the transferred pair is `PsiReal`
  have hPsiReal' : Work.FIArea6Hecke.R.PsiReal (chiPrime d chi) 0 :=
    Work.FIArea6Hecke.R.psiReal_zero_iff.mpr hreal'
  -- the region `1 - min c 1 / d^ε < s.re` sits inside `re s > 0`
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdε : (1 : ℝ) ≤ (d : ℝ) ^ ε := by
    rw [← Real.one_rpow ε]
    exact Real.rpow_le_rpow (by norm_num) hd1 hε.le
  have hden : (0 : ℝ) < (d : ℝ) ^ ε := lt_of_lt_of_le one_pos hdε
  have hdiv1 : min c 1 / (d : ℝ) ^ ε ≤ 1 := by
    rw [div_le_one hden]
    exact le_trans (min_le_right _ _) hdε
  have hs1c : 1 - c / (d : ℝ) ^ ε < s.re := by
    have hle : min c 1 / (d : ℝ) ^ ε ≤ c / (d : ℝ) ^ ε :=
      div_le_div_of_nonneg_right (min_le_left _ _) hden.le
    linarith
  have hs0 : 0 < s.re := by linarith
  -- the Siegel input applies to the real pair
  have hfin : Work.FIArea6Hecke.Lval d 0 Lam' s ≠ 0 :=
    hreg d (chiPrime d chi) 0 Lam' hd hchi' hAn' hagr' hPsiReal' s hsim hs1c hs2
  -- and the two `L`-values agree on `re s > 0`
  have hEq : Work.FIArea6Hecke.Lval d 0 Lam s = Work.FIArea6Hecke.Lval d 0 Lam' s :=
    zpr_lval_eq_of_same_series hd hAn hAn' hagr
      (fun t ht => hagr' t (by simpa using ht)) hLser s hs0
  rw [hEq]
  exact hfin

end

end Work.FIArea6Hecke.R
