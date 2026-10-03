import Mathlib
import Submission.Work.FIArea6Hecke.R2.Defs
import Submission.Work.FIArea6Hecke.CGD.CrsCalculus
import Submission.Work.FIArea6Hecke.CGD.ChiUnits
import Submission.Work.FIArea6Hecke.R2.GsUnitK

set_option autoImplicit false

namespace Work.FIArea6Hecke.R2

open scoped BigOperators
open Work.FIArea6Hecke.R

noncomputable section


/-! ## Two auxiliary facts about `ℤ[i]`

Both are proved here for self-containedness; they are the only "number-theoretic" inputs of the
argument, the rest being the algebra of the character sums. -/

/-- **A proper non-unit divisor of `M` adapted to a non-unit `a`.**

If `M ≠ 0`, `a` is not a unit modulo `M`, and `M ∤ a`, then `c := M / gcd(M,a)` (i.e. `M = d * c`
with `d = gcd(M,a)`) satisfies `c ∣ M`, `¬ M ∣ c`, `¬ IsUnit c` and `M ∣ c * a`:

* `d := gcd (M,a)` is a non-unit, since `d` a unit would give `1 = M*x + a*y` (Bézout), hence
  `M ∣ a*y - 1`, i.e. `IsUnitMod M a`;
* `M = d * c` with `d` a non-unit and `M ≠ 0` gives `¬ M ∣ c` (else `d` would be a unit);
* `¬ IsUnit c` follows from `¬ M ∣ a`: a unit `c` would give `M ∣ d ∣ a`;
* `d ∣ a` gives `M = c * d ∣ c * a`. -/
private lemma exists_divisor_of_not_dvd (M a : GaussianInt) (hM : M ≠ 0)
    (ha : ¬ IsUnitMod M a) (hMa : ¬ M ∣ a) :
    ∃ c : GaussianInt, c ∣ M ∧ ¬ M ∣ c ∧ ¬ IsUnit c ∧ M ∣ c * a := by
  classical
  have hgnonunit : ¬ IsUnit (EuclideanDomain.gcd M a) := by
    intro hgunit
    obtain ⟨g', hg'⟩ := (isUnit_iff_exists_inv).mp hgunit
    have hbez := EuclideanDomain.gcd_eq_gcd_ab M a
    have h1 : M * (EuclideanDomain.gcdA M a * g')
        + a * (EuclideanDomain.gcdB M a * g') = 1 := by
      calc M * (EuclideanDomain.gcdA M a * g') + a * (EuclideanDomain.gcdB M a * g')
          = (M * EuclideanDomain.gcdA M a + a * EuclideanDomain.gcdB M a) * g' := by ring
        _ = EuclideanDomain.gcd M a * g' := by rw [← hbez]
        _ = 1 := hg'
    refine ha ⟨EuclideanDomain.gcdB M a * g', -(EuclideanDomain.gcdA M a * g'), ?_⟩
    have h2 : a * (EuclideanDomain.gcdB M a * g')
        = 1 - M * (EuclideanDomain.gcdA M a * g') :=
      eq_sub_of_add_eq (by rw [add_comm]; exact h1)
    rw [h2]; ring
  obtain ⟨c, hc⟩ := EuclideanDomain.gcd_dvd_left M a
  refine ⟨c, ⟨EuclideanDomain.gcd M a, hc.trans (mul_comm (EuclideanDomain.gcd M a) c)⟩, ?_, ?_, ?_⟩
  · intro hMc
    obtain ⟨h, hh⟩ := hMc
    have hcancel : (1 : GaussianInt) = EuclideanDomain.gcd M a * h := by
      have h1 : M * 1 = M * (EuclideanDomain.gcd M a * h) := by
        calc M * 1 = M := by rw [mul_one]
          _ = EuclideanDomain.gcd M a * c := hc
          _ = EuclideanDomain.gcd M a * (M * h) := by rw [hh]
          _ = M * (EuclideanDomain.gcd M a * h) := by ring
      exact mul_left_cancel₀ hM h1
    exact hgnonunit ((isUnit_iff_exists_inv).mpr ⟨h, hcancel.symm⟩)
  · intro hcunit
    apply hMa
    obtain ⟨c', hc'⟩ := (isUnit_iff_exists_inv).mp hcunit
    obtain ⟨η', hη'⟩ := EuclideanDomain.gcd_dvd_right M a
    have hgM : EuclideanDomain.gcd M a = M * c' := by
      calc EuclideanDomain.gcd M a = EuclideanDomain.gcd M a * 1 := by rw [mul_one]
        _ = EuclideanDomain.gcd M a * (c * c') := by rw [hc']
        _ = (EuclideanDomain.gcd M a * c) * c' := by ring
        _ = M * c' := by rw [← hc]
    refine ⟨c' * η', ?_⟩
    rw [hη', hgM]; ring
  · obtain ⟨η', hη'⟩ := EuclideanDomain.gcd_dvd_right M a
    refine ⟨η', ?_⟩
    rw [hη']
    calc c * (EuclideanDomain.gcd M a * η')
        = (EuclideanDomain.gcd M a * c) * η' := by ring
      _ = M * η' := by rw [← hc]

/-- **The additive character of frequency `M * star a` is unchanged under `s ↦ s * z` when
`M ∣ (z - 1) * a`.**

`ekern_smul_star_k` turns `ekern M (M * star a) x` into `ekern M M (x * a)`; then
`s * z = s + s * (z - 1)` and `(z - 1) * a = M * c` reduce the shift factor to
`ekern M M (M * (s * c)) = 1` by `ekern_one_of_dvd_mul`. -/
private lemma ekern_mul_shift (M a z s : GaussianInt) (hM : M ≠ 0) (hza : M ∣ (z - 1) * a) :
    ekern M (M * star a) (s * z) = ekern M (M * star a) s := by
  have hsz : s * z = s + s * (z - 1) := by ring
  rw [hsz, ekern_add_right]
  have h1 : ekern M (M * star a) (s * (z - 1)) = 1 := by
    rw [ekern_smul_star_k M a (s * (z - 1))]
    obtain ⟨c, hc⟩ := hza
    have h2 : s * (z - 1) * a = M * (s * c) := by
      rw [show s * (z - 1) * a = s * ((z - 1) * a) by ring, hc]
      ring
    rw [h2]
    exact ekern_one_of_dvd_mul M M (M * (s * c)) hM dvd_rfl ⟨s * c, rfl⟩
  rw [h1, mul_one]

/-! ## Periodicity of the Gauss-sum weight modulo `M` -/

/-- The weight `s ↦ chi s * ekern M (M * star a) s` of the Gauss sum `Gs M chi S a` is
`M`-periodic: both factors are (`chi` by definition of a character mod `M`, `ekern M (M * star a)`
because `M ∣ M * star a`). -/
lemma weight_periodic_mod (M a : GaussianInt) (chi : GaussianInt → ℂ)
    (hchi : IsCharModStrict M chi) (hM : M ≠ 0) {x y : GaussianInt} (hxy : M ∣ x - y) :
    chi x * ekern M (M * star a) x = chi y * ekern M (M * star a) y := by
  have h1 : chi x = chi y := hchi.2.2.2.1 x y hxy
  have h2 : ekern M (M * star a) x = ekern M (M * star a) y := by
    have hx : x = y + (x - y) := by ring
    rw [hx, ekern_add_of_dvd M (M * star a) y (x - y) hM (dvd_mul_right M (star a)) hxy]
  rw [h1, h2]

/-! ## The reindexing identity -/

/-- **The reindexing identity.**  If `z` is a unit modulo `M`, `chi z ≠ 1`, and `M ∣ (z-1)·a`,
then the substitution `s ↦ s·z` (a bijection of the complete residue system `S`) multiplies the
weight by `chi z` and leaves the additive character `ekern M (M * star a)` unchanged:

  `Gs M chi S a = chi z * Gs M chi S a`.

Since `S.image (· * z)` is again a complete residue system mod `M` (`CrsCalculus`), and the weight
is `M`-periodic, the sum over `S` equals the sum over the dilated system, which is
`∑_{s ∈ S} chi (s·z) · ekern M (M * star a) (s·z) = chi z · ∑_{s ∈ S} chi s · ekern M (M * star a) s`
by multiplicativity of `chi` and `GsNonunitShift`. -/
theorem Gs_eq_mul_self_of_witness (M : GaussianInt) (hM : M ≠ 0)
    (hg : 2 ≤ Work.FIPlan.gnorm M) (S : Finset GaussianInt) (hS : IsCRS M S)
    (chi : GaussianInt → ℂ) (hchi : IsCharModStrict M chi) (a z : GaussianInt)
    (hzunit : IsUnitMod M z) (hza : M ∣ (z - 1) * a) :
    Gs M chi S a = chi z * Gs M chi S a := by
  classical
  have hz0 : z ≠ 0 := Work.FIArea6Hecke.CGD.unit_ne_zero_of_IsUnitMod M z hg hzunit
  -- the weight
  have hper : ∀ x y : GaussianInt, M ∣ x - y →
      chi x * ekern M (M * star a) x = chi y * ekern M (M * star a) y :=
    fun x y hxy => weight_periodic_mod M a chi hchi hM hxy
  -- multiplication by the unit `z` reindexes the complete residue system `S`
  have hT : IsCRS M (S.image (fun s => s * z)) :=
    (Work.FIArea6Hecke.CGD.CrsCalculus M S S hS hS
      (fun s => chi s * ekern M (M * star a) s) hper).2.2.1 z hzunit hz0
  have hAE := Work.FIArea6Hecke.CGD.CrsCalculus M S (S.image (fun s => s * z)) hS hT
    (fun s => chi s * ekern M (M * star a) s) hper
  have hreindex : (∑ s ∈ S, chi s * ekern M (M * star a) s)
      = ∑ s ∈ S, chi (s * z) * ekern M (M * star a) (s * z) := by
    rw [hAE.1, hAE.2.2.2.2 z hz0]
  -- the dilated weight is `chi z` times the original one
  have hterm : ∀ s : GaussianInt, chi (s * z) * ekern M (M * star a) (s * z)
      = chi z * (chi s * ekern M (M * star a) s) := by
    intro s
    rw [hchi.2.1 s z, ekern_mul_shift M a z s hM hza]
    ring
  calc Gs M chi S a
      = ∑ s ∈ S, chi s * ekern M (M * star a) s := rfl
    _ = ∑ s ∈ S, chi (s * z) * ekern M (M * star a) (s * z) := hreindex
    _ = ∑ s ∈ S, chi z * (chi s * ekern M (M * star a) s) := Finset.sum_congr rfl
          (fun s _ => hterm s)
    _ = chi z * ∑ s ∈ S, chi s * ekern M (M * star a) s :=
          (Finset.mul_sum S (fun s => chi s * ekern M (M * star a) s) (chi z)).symm
    _ = chi z * Gs M chi S a := rfl

/-! ## Vanishing -/

/-- **Vanishing of the Gauss sum in the presence of a unitary witness.**

If `z` is a unit modulo `M` with `chi z ≠ 1` and `M ∣ (z-1)·a`, then `Gs M chi S a = 0`: the
reindexing identity `Gs = chi z · Gs` (`Gs_eq_mul_self_of_witness`) gives
`(1 - chi z) · Gs = 0`, and `1 - chi z ≠ 0`. -/
theorem Gs_eq_zero_of_witness (M : GaussianInt) (hM : M ≠ 0)
    (hg : 2 ≤ Work.FIPlan.gnorm M) (S : Finset GaussianInt) (hS : IsCRS M S)
    (chi : GaussianInt → ℂ) (hchi : IsCharModStrict M chi) (a z : GaussianInt)
    (hzunit : IsUnitMod M z) (hzchi : chi z ≠ 1) (hza : M ∣ (z - 1) * a) :
    Gs M chi S a = 0 := by
  have hkey := Gs_eq_mul_self_of_witness M hM hg S hS chi hchi a z hzunit hza
  have hfac : (1 - chi z) * Gs M chi S a = 0 := by
    calc (1 - chi z) * Gs M chi S a
        = Gs M chi S a - chi z * Gs M chi S a := by ring
      _ = 0 := sub_eq_zero.mpr hkey
  exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr (Ne.symm hzchi))

/-- For `a` **not** a unit modulo `M`, the Gauss sum `Gs M chi S a` vanishes.

Strategy.  `¬ IsUnitMod M a` gives `¬ IsCoprime M a` (from `M ∣ a * w - 1` one gets
`(-w) * M + ? * a = 1`), hence `d := gcd M a` is a non-unit with `d ∣ M` and `d ∣ a`; write
`M = d * M'`.  If `M'` is a unit then `M ∣ a`, and the witness `z` of `hnt` satisfies
`M ∣ (z - 1) * a`.  Otherwise `M'` is a non-unit and `M ∤ M'` (`M = d * M'` with `d` a non-unit and
`M ≠ 0`), so `hprim M' ...` gives a unit `z` modulo `M` with `M' ∣ z - 1` and `chi z ≠ 1`; then
`M ∣ (z - 1) * a` as well.  In both cases reindex the sum over the complete residue system `S` by
`s ↦ crsRep M S hS (z * s)` (a bijection of `S` because `z` is a unit modulo `M`, using
`crsRep_dvd`/`eq_of_mem_of_dvd`): `chi` becomes `chi z * chi s`, while the kernel
`ekern M (M * star a)` is unchanged because
`gdot (z * s) (M * star a) - gdot s (M * star a) = Re((z - 1) * s * star M * a)` is divisible by
`gnorm M` as soon as `M ∣ (z - 1) * a`.  Hence `Gs M chi S a = chi z * Gs M chi S a`, and
`chi z ≠ 1` forces `Gs M chi S a = 0`. -/
theorem GsNonunitK (M : GaussianInt) (hM : M ≠ 0) (hg : 2 ≤ Work.FIPlan.gnorm M)
    (S : Finset GaussianInt) (hS : Work.FIArea6Hecke.R.IsCRS M S)
    (chi : GaussianInt → ℂ) (hchi : Work.FIArea6Hecke.R.IsCharModStrict M chi)
    (hprim : Work.FIArea6Hecke.R.IsPrimitiveCharAt M chi)
    (hnt : ∃ z : GaussianInt, Work.FIArea6Hecke.R.IsUnitMod M z ∧ chi z ≠ 1)
    (a : GaussianInt) (ha : ¬ Work.FIArea6Hecke.R.IsUnitMod M a) :
    Work.FIArea6Hecke.R.Gs M chi S a = 0 := by
  obtain ⟨z, hzunit, hzchi⟩ := hnt
  by_cases hMa : M ∣ a
  · -- `M ∣ a`: the witness `z` of `hnt` already has `M ∣ (z - 1) * a`
    exact Gs_eq_zero_of_witness M hM hg S hS chi hchi a z hzunit hzchi
      (dvd_mul_of_dvd_right hMa (z - 1))
  · -- `M ∤ a`: take a proper non-unit divisor `c ∣ M` with `M ∣ c * a` and use primitivity
    obtain ⟨c, hcdvd, hcnotdvd, hcnotunit, hca⟩ := exists_divisor_of_not_dvd M a hM ha hMa
    obtain ⟨z', hz'unit, hz'sub, hz'chi⟩ := hprim c hcdvd hcnotdvd hcnotunit
    obtain ⟨m, hm⟩ := hz'sub
    obtain ⟨k, hk⟩ := hca
    refine Gs_eq_zero_of_witness M hM hg S hS chi hchi a z' hz'unit hz'chi ?_
    refine ⟨k * m, ?_⟩
    have h1 : (z' - 1) * a = c * a * m := by rw [hm]; ring
    rw [h1, hk]; ring

end

end Work.FIArea6Hecke.R2
