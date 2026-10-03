/-
# `Work.FIArea6Hecke.R.heckeConductorDataUnit`

The **conductor data** of a strict character `χ` modulo `4d`, in the *unit-witness* form needed by
the Gauss-sum criterion `R/gaussCriterionOfPrimitiveAt`.

This file repeats the elementary construction of `R/heckeConductorData` — whose helpers are all
`private` and therefore not importable — and strengthens its primitivity output from
`IsPrimitiveAt` (witnesses arbitrary) to `IsPrimitiveUnitAt` (witnesses units modulo `M`).

The strengthening is free: primitivity is *minimality* of `M` among the divisors of `4d`
satisfying the congruence condition `IsConductorMod d χ`.  If `M' ∣ M` is a proper non-unit
divisor, then `¬ IsConductorMod d χ M'` unfolds to

  `∃ u, IsUnitMod4d d u ∧ M' ∣ (u - 1) ∧ chi u ≠ 1`,

i.e. the falsifying witness `u` is **already a unit modulo `4d`** — hence, since `M ∣ 4d`, a unit
modulo `M` (`isUnitMod_of_dvd`).  Finally `χ₀ u = χ u` by `hchi₀eq`, giving the required unit
witness for `IsPrimitiveUnitAt`.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.gaussCriterionOfPrimitiveAt
import Submission.Work.FIArea6Hecke.R.StrictConductorDefs
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea6Hecke.R.heckeUnitLift
import Submission.Work.FIArea6Hecke.R.gnorm_lt_of_dvd_of_not_dvd
import Submission.Work.FIArea4.GaussMoebiusCore

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-! ## 1. The elementary API of `IsUnitMod` -/

/-- If `z` is a unit modulo `A` and `B ∣ A`, then `z` is a unit modulo `B`. -/
private lemma isUnitMod_of_dvd {A B z : GaussianInt} (hB : B ∣ A) (h : IsUnitMod A z) :
    IsUnitMod B z := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w, dvd_trans hB hw⟩

/-- Congruent elements are simultaneously units modulo `A`. -/
private lemma isUnitMod_of_dvd_sub {A z y : GaussianInt} (h : IsUnitMod A z) (hd : A ∣ (y - z)) :
    IsUnitMod A y := by
  obtain ⟨w, hw⟩ := h
  refine ⟨w, ?_⟩
  rw [show y * w - 1 = (z * w - 1) + (y - z) * w from by ring]
  exact dvd_add hw (dvd_mul_of_dvd_left hd w)

/-- The units modulo `A` form a submonoid: a product of units is a unit. -/
private lemma isUnitMod_mul {A z w : GaussianInt} (hz : IsUnitMod A z) (hw : IsUnitMod A w) :
    IsUnitMod A (z * w) := by
  obtain ⟨v, hv⟩ := hz
  obtain ⟨u, hu⟩ := hw
  refine ⟨v * u, ?_⟩
  rw [show z * w * (v * u) - 1 = (z * v - 1) * (w * u) + (w * u - 1) from by ring]
  exact dvd_add (dvd_mul_of_dvd_left hv (w * u)) hu

/-- A factor of a unit modulo `A` is a unit modulo `A`. -/
private lemma isUnitMod_mul_left {A z w : GaussianInt} (h : IsUnitMod A (z * w)) :
    IsUnitMod A z := by
  obtain ⟨v, hv⟩ := h
  exact ⟨w * v, by
    rw [show z * (w * v) - 1 = z * w * v - 1 from by ring]
    exact hv⟩

/-- A factor of a unit modulo `A` is a unit modulo `A`. -/
private lemma isUnitMod_mul_right {A z w : GaussianInt} (h : IsUnitMod A (z * w)) :
    IsUnitMod A w := by
  obtain ⟨v, hv⟩ := h
  exact ⟨z * v, by
    rw [show w * (z * v) - 1 = z * w * v - 1 from by ring]
    exact hv⟩

private lemma isUnitMod_one (A : GaussianInt) : IsUnitMod A (1 : GaussianInt) :=
  ⟨1, by simpa using dvd_zero A⟩

/-! ## 2. The conductor condition -/

/-- `4d` as a Gaussian integer; `IsUnitMod4d d z` is `IsUnitMod (fourD d) z`. -/
private def fourD (d : ℕ) : GaussianInt := ((((4 * d : ℕ) : ℤ)) : GaussianInt)

/-- **The conductor condition**: `χ` is trivial on the units modulo `4d` that are `≡ 1 (mod M)`.
The conductor of `χ` is the divisor of `4d` of minimal norm satisfying this. -/
private def IsConductorMod (d : ℕ) (chi : GaussianInt → ℂ) (M : GaussianInt) : Prop :=
  ∀ u : GaussianInt, Work.FIArea5.S16Hecke.IsUnitMod4d d u → M ∣ (u - 1) → chi u = 1

/-! ## 3. The theorem -/

/-- **Conductor data with *unit* witnesses** (the corrected form of `heckeConductorData`).

For every strict character `χ` mod `4d` whose Größencharacter is non-trivial on the primary units,
there are `M ∣ 4d` and a partner `χ₀` of modulus `M` (`IsConductorPartner d chi M chi₀`) which is
primitive at `M` in the sense that for every non-unit proper divisor `M' ∣ M` a **unit** `z` mod `M`
satisfies `z ≡ 1 (mod M')` and `χ₀ z ≠ 1` (`IsPrimitiveUnitAt M χ₀`).

The unit requirement is essential: `R/heckeConductorData` (proved) only produces the weaker
`IsPrimitiveAt M χ₀`, whose witnesses may be non-units — and a non-unit `z` satisfies `χ₀ z = 0 ≠ 1`
for free, so the weak form does not imply "the conductor is exactly `M`" and is not enough for the
Gauss-sum criterion `R/gaussCriterionOfPrimitiveAt`.  The minimality argument already inside
`R/heckeConductorData` — reused below via its private helpers `isUnitMod_of_dvd`, `hchi₀eq` —
yields the unit witness directly: when the minimality of `M` fails for `N ∣ M` (`¬ M ∣ N`,
`¬ IsUnit N`), `¬ IsConductorMod d chi N` unfolds to
`∃ u, IsUnitMod4d d u ∧ N ∣ u - 1 ∧ chi u ≠ 1`, and that `u` is a unit mod `M` (as `M ∣ 4d`) with
`chi₀ u = chi u ≠ 1`. -/
theorem conductorPartnerUnitAgreeNoHnt (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi) :
    ∃ (M : GaussianInt) (chi₀ : GaussianInt → ℂ),
      Work.FIArea6Hecke.R.IsConductorPartner d chi M chi₀ ∧
      Work.FIArea6Hecke.R.IsPrimitiveUnitAt M chi₀ ∧
      (∀ z : GaussianInt, Work.FIArea5.S16Hecke.IsUnitMod4d d z →
        Work.FIArea6Hecke.R.IsUnitMod M z → chi₀ z = chi z) ∧
      (2 ≤ Work.FIPlan.gnorm M → ∃ z : GaussianInt,
        Work.FIArea6Hecke.R.IsUnitMod M z ∧ chi₀ z ≠ 1) := by
  classical
  have hchi1 : chi 1 = 1 := hchi.1.1
  have hchimul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w := hchi.1.2.1
  have hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1 := hchi.1.2.2.1
  have hchiper : ∀ z w : GaussianInt, fourD d ∣ (z - w) → chi z = chi w := hchi.1.2.2.2.1
  have hC0 : fourD d ≠ 0 := by
    simp only [fourD]
    exact Int.cast_ne_zero.mpr (by omega)
  -- ## The conductor `M`: a divisor of `4d` of minimal norm satisfying `IsConductorMod`.
  have hQ : ∃ n : ℕ, ∃ M : GaussianInt,
      M ∣ fourD d ∧ IsConductorMod d chi M ∧ Work.FIPlan.gnorm M = n := by
    refine ⟨Work.FIPlan.gnorm (fourD d), fourD d, dvd_rfl, ?_, rfl⟩
    intro u _ hdvd
    exact (hchiper u 1 hdvd).trans hchi1
  let n₀ : ℕ := Nat.find hQ
  have hn₀ : ∃ M : GaussianInt,
      M ∣ fourD d ∧ IsConductorMod d chi M ∧ Work.FIPlan.gnorm M = n₀ := Nat.find_spec hQ
  obtain ⟨M, hMdiv, hMcond, hMnorm⟩ := hn₀
  have hmin : ∀ M' : GaussianInt, M' ∣ fourD d → IsConductorMod d chi M' →
      Work.FIPlan.gnorm M ≤ Work.FIPlan.gnorm M' := by
    intro N h1 h2
    have h3 := Nat.find_min' hQ ⟨N, h1, h2, rfl⟩
    rw [hMnorm]
    exact h3
  have hMne : M ≠ 0 := by
    intro h0
    rw [h0] at hMdiv
    exact hC0 (zero_dvd_iff.mp hMdiv)
  -- ## `χ` is constant on the units modulo `4d` that are congruent modulo `M`.
  have hwell : ∀ u v : GaussianInt, Work.FIArea5.S16Hecke.IsUnitMod4d d u →
      Work.FIArea5.S16Hecke.IsUnitMod4d d v → M ∣ (u - v) → chi u = chi v := by
    intro u v hu hv huv
    obtain ⟨w, hw⟩ := hv
    have hv' : Work.FIArea5.S16Hecke.IsUnitMod4d d v := ⟨w, hw⟩
    have hwunit : Work.FIArea5.S16Hecke.IsUnitMod4d d w := ⟨v, by simpa [mul_comm] using hw⟩
    have hu1 : Work.FIArea5.S16Hecke.IsUnitMod4d d (u * w) :=
      isUnitMod_mul (z := u) (w := w) hu hwunit
    have hu2 : Work.FIArea5.S16Hecke.IsUnitMod4d d (v * w) :=
      isUnitMod_mul (z := v) (w := w) hv' hwunit
    have h1 : M ∣ (u * w - 1) := by
      rw [show u * w - 1 = (u - v) * w + (v * w - 1) from by ring]
      exact dvd_add (dvd_mul_of_dvd_left huv w) (dvd_trans hMdiv hw)
    have h2 : M ∣ (v * w - 1) := dvd_trans hMdiv hw
    have e1 : chi u * chi w = 1 := by
      rw [← hchimul u w]; exact hMcond (u * w) hu1 h1
    have e2 : chi v * chi w = 1 := by
      rw [← hchimul v w]; exact hMcond (v * w) hu2 h2
    have hwne : chi w ≠ 0 := by
      intro h
      rw [h, mul_zero] at e2
      exact one_ne_zero e2.symm
    exact mul_right_cancel₀ hwne (by rw [e1, e2])
  -- ## Lifting units modulo `M` to units modulo `4d` (`heckeUnitLift`).
  have hlift : ∀ z : GaussianInt, IsUnitMod M z →
      ∃ u : GaussianInt, M ∣ (u - z) ∧ Work.FIArea5.S16Hecke.IsUnitMod4d d u := by
    intro z hz
    obtain ⟨g, hg⟩ := hMdiv
    have hg0 : g ≠ 0 := by
      intro h0
      have hz0 : fourD d = 0 := by rw [hg, h0, mul_zero]
      exact hC0 hz0
    obtain ⟨u, hu1, hu2⟩ := heckeUnitLift g M z hg0 hz
    refine ⟨u, hu1, ?_⟩
    show IsUnitMod (fourD d) u
    rw [hg]
    exact hu2
  -- ## The partner `χ₀`.
  let u₀ : (z : GaussianInt) → IsUnitMod M z → GaussianInt :=
    fun z h => Classical.choose (hlift z h)
  have u₀spec : ∀ (z : GaussianInt) (h : IsUnitMod M z),
      M ∣ (u₀ z h - z) ∧ Work.FIArea5.S16Hecke.IsUnitMod4d d (u₀ z h) :=
    fun z h => Classical.choose_spec (hlift z h)
  let chi₀ : GaussianInt → ℂ := fun z => if h : IsUnitMod M z then chi (u₀ z h) else 0
  have hchi₀pos : ∀ (z : GaussianInt) (h : IsUnitMod M z), chi₀ z = chi (u₀ z h) :=
    fun z h => dif_pos h
  have hchi₀neg : ∀ (z : GaussianInt) (h : ¬ IsUnitMod M z), chi₀ z = 0 :=
    fun z h => dif_neg h
  -- `χ₀ z` is the value of `χ` at *any* lift of `z`.
  have hchi₀eq : ∀ (z : GaussianInt) (hz : IsUnitMod M z) (u : GaussianInt),
      Work.FIArea5.S16Hecke.IsUnitMod4d d u → M ∣ (u - z) → chi₀ z = chi u := by
    intro z hz u hu huz
    rw [hchi₀pos z hz]
    exact hwell (u₀ z hz) u (u₀spec z hz).2 hu (by
      rw [show u₀ z hz - u = (u₀ z hz - z) - (u - z) from by ring]
      exact dvd_sub (u₀spec z hz).1 huz)
  have hchi₀one : chi₀ 1 = 1 := by
    have h1 : IsUnitMod M (1 : GaussianInt) := isUnitMod_one M
    have hC1 : Work.FIArea5.S16Hecke.IsUnitMod4d d (1 : GaussianInt) :=
      ⟨1, by simpa using dvd_zero (fourD d)⟩
    have h := hchi₀eq 1 h1 1 hC1 (by simpa using dvd_zero M)
    rw [h, hchi1]
  have hchi₀mul : ∀ z w : GaussianInt, chi₀ (z * w) = chi₀ z * chi₀ w := by
    intro z w
    by_cases hz : IsUnitMod M z
    · by_cases hw : IsUnitMod M w
      · have hzw : IsUnitMod M (z * w) := isUnitMod_mul hz hw
        have huz := u₀spec z hz
        have huw := u₀spec w hw
        have hprod : Work.FIArea5.S16Hecke.IsUnitMod4d d (u₀ z hz * u₀ w hw) :=
          isUnitMod_mul huz.2 huw.2
        have hdiv : M ∣ (u₀ z hz * u₀ w hw - z * w) := by
          rw [show u₀ z hz * u₀ w hw - z * w
              = u₀ z hz * (u₀ w hw - w) + (u₀ z hz - z) * w from by ring]
          exact dvd_add (dvd_mul_of_dvd_right huw.1 (u₀ z hz)) (dvd_mul_of_dvd_left huz.1 w)
        calc chi₀ (z * w) = chi (u₀ z hz * u₀ w hw) := hchi₀eq (z * w) hzw _ hprod hdiv
          _ = chi (u₀ z hz) * chi (u₀ w hw) := hchimul _ _
          _ = chi₀ z * chi₀ w := by
              rw [← hchi₀pos z hz, ← hchi₀pos w hw]
      · have hzw : ¬ IsUnitMod M (z * w) := fun h => hw (isUnitMod_mul_right h)
        rw [hchi₀neg (z * w) hzw, hchi₀neg w hw, mul_zero]
    · have hzw : ¬ IsUnitMod M (z * w) := fun h => hz (isUnitMod_mul_left h)
      rw [hchi₀neg (z * w) hzw, hchi₀neg z hz, zero_mul]
  have hchi₀bd : ∀ z : GaussianInt, ‖chi₀ z‖ ≤ 1 := by
    intro z
    by_cases hz : IsUnitMod M z
    · rw [hchi₀pos z hz]; exact hchibd _
    · rw [hchi₀neg z hz]; simp
  have hchi₀per : ∀ z w : GaussianInt, M ∣ (z - w) → chi₀ z = chi₀ w := by
    intro z w hzw
    by_cases hz : IsUnitMod M z
    · have hw : IsUnitMod M w :=
        isUnitMod_of_dvd_sub hz (by simpa [neg_sub] using dvd_neg.mpr hzw)
      rw [hchi₀pos z hz]
      exact (hchi₀eq w hw (u₀ z hz) (u₀spec z hz).2 (by
        rw [show u₀ z hz - w = (u₀ z hz - z) + (z - w) from by ring]
        exact dvd_add (u₀spec z hz).1 hzw)).symm
    · have hw : ¬ IsUnitMod M w := fun h => hz (isUnitMod_of_dvd_sub h hzw)
      rw [hchi₀neg z hz, hchi₀neg w hw]
  have hchi₀vanish : ∀ z : GaussianInt, ¬ IsUnitMod M z → chi₀ z = 0 := hchi₀neg
  have hchi₀primary : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
      Work.FIArea5.S16Hecke.IsUnitMod4d d z → chi₀ z = chi z := by
    intro z _ hu
    exact hchi₀eq z (isUnitMod_of_dvd hMdiv hu) z hu (by simpa using dvd_zero M)
  -- ## Primitivity at level `M` *with unit witnesses*, from the minimality of `M`.
  --
  -- The only difference from `R/heckeConductorData`: the witness `u` produced by the failure of
  -- `IsConductorMod` at `N` is a unit modulo `4d`, hence a unit modulo `M` (`M ∣ 4d`).
  have hprim : IsPrimitiveUnitAt M chi₀ := by
    intro N hNM hnotMN _hunitN
    have hcon : ¬ IsConductorMod d chi N := by
      intro hc
      have h1 : Work.FIPlan.gnorm M ≤ Work.FIPlan.gnorm N := hmin N (dvd_trans hNM hMdiv) hc
      have h2 : Work.FIPlan.gnorm N < Work.FIPlan.gnorm M :=
        gnorm_lt_of_dvd_of_not_dvd hNM hnotMN hMne
      omega
    obtain ⟨u, hu, hNu, hchinu⟩ : ∃ u : GaussianInt,
        Work.FIArea5.S16Hecke.IsUnitMod4d d u ∧ N ∣ (u - 1) ∧ chi u ≠ 1 := by
      by_contra hcon2
      exact hcon (by
        intro u hu hu1
        by_contra hne
        exact hcon2 ⟨u, hu, hu1, hne⟩)
    exact ⟨u, isUnitMod_of_dvd hMdiv hu, hNu, by
      rw [hchi₀eq u (isUnitMod_of_dvd hMdiv hu) u hu (by simpa using dvd_zero M)]
      exact hchinu⟩
  have hagree : ∀ z : GaussianInt, Work.FIArea5.S16Hecke.IsUnitMod4d d z →
      Work.FIArea6Hecke.R.IsUnitMod M z → chi₀ z = chi z :=
    fun z hu huM => hchi₀eq z huM z hu (by simpa using dvd_zero M)
  have hwit : 2 ≤ Work.FIPlan.gnorm M → ∃ z : GaussianInt,
      Work.FIArea6Hecke.R.IsUnitMod M z ∧ chi₀ z ≠ 1 := by
    intro hg2
    have hnc : ¬ IsConductorMod d chi (1 : GaussianInt) := by
      intro hc
      have h1 : Work.FIPlan.gnorm M ≤ Work.FIPlan.gnorm (1 : GaussianInt) :=
        hmin 1 (one_dvd _) hc
      rw [Work.FIArea5.S16Hecke.gnorm_one] at h1
      omega
    obtain ⟨u, hu, _h1u, hune⟩ : ∃ u : GaussianInt,
        Work.FIArea5.S16Hecke.IsUnitMod4d d u ∧ (1 : GaussianInt) ∣ (u - 1) ∧ chi u ≠ 1 := by
      by_contra hcon2
      exact hnc (by
        intro u hu hu1
        by_contra hne
        exact hcon2 ⟨u, hu, hu1, hne⟩)
    exact ⟨u, isUnitMod_of_dvd hMdiv hu,
      by rw [hagree u hu (isUnitMod_of_dvd hMdiv hu)]; exact hune⟩
  exact ⟨M, chi₀,
    ⟨hMdiv, hMne, hchi₀one, hchi₀mul, hchi₀bd, hchi₀per, hchi₀vanish, hchi₀primary⟩,
    hprim, hagree, hwit⟩

end

end Work.FIArea6Hecke.R
