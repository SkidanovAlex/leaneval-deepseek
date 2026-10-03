/-
# `Submission.Work.FIArea7.prop232Defs` — vocabulary for *FI* Proposition 23.2

Literal forms (23.11)/(23.12) of *FI* Prop. 23.2 bound the special linear forms
`L(N) = Σ_{n ≤ N} λ(mn)` and `L∗(N) = Σ_{n ≤ N, (n,m)=1} λ(mn)` in the quadratic eigenvalues
(23.1).  This file collects the objects that the proof introduces:

* `primarySet M` — the primary Gaussian integers of norm `M` (the `w` of the decomposition
  `λ(mn) = Σ∧_{ww̄=m} ψ(w) Σ∧_{zz̄=n, (z,w)=1} ψ(z)[wz]`, *FI* Prop. 23.2);
* `KStarDiscZ N w k chi` — verbatim the disc form `Σ∧_{z : |z|² ≤ N, (z,w)=1} ψ(z)[wz]` of
  *FI* (22.2)/(22.4) (written over the box `gBox (√N)` together with the condition `|z|² ≤ N`);
* `KStarDisc N w k chi` — the same sum split into the fibres `Re z = r`, each fibre being a
  symmetric interval of `s` of the exact length forced by `r² + s² ≤ N`; this is the form in which
  the disc version of Prop. 22.1 is a statement about `KInnerStar` at a *varying* radius.  The two
  agree: `KStarDiscZ_eq_KStarDisc`;
* `msmooth m k` — "`k` is supported on the prime divisors of `m`", the index set of the expansion
  `L(N) = Σ_{k | m^∞} L∗`-type `(N/k)` with modulus `mk` which gives (23.11) from (23.12).

Also proved here: multiplicativity of the Grössencharacter (17.17) on coprime arguments, the
elementary facts about `primarySet`, and `KStarDiscZ = KStarDisc`.
-/
import Mathlib
import Submission.Work.FIArea7.Classical172Defs
import Submission.Work.FIArea7.KStarDefs

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Primary elements of a given norm -/

/-- The primary Gaussian integers of norm `N` (a subset of the box `gBox N`, which contains every
`z` with `|z|² = N`). -/
def primarySet (N : ℕ) : Finset GaussianInt :=
  (Work.FIPlan.gBox (N : ℤ)).filter (fun z => Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z = N)

/-- Membership in `primarySet`. -/
lemma mem_primarySet {N : ℕ} {z : GaussianInt} :
    z ∈ primarySet N ↔ Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z = N := by
  rw [primarySet, Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨mem_gBox_of_gnorm_eq h.2, h⟩⟩

/-- A primary Gaussian integer has odd norm. -/
lemma odd_gnorm_of_isPrimary {z : GaussianInt} (hz : Work.FIPlan.IsPrimary z) :
    Odd (Work.FIPlan.gnorm z) := by
  obtain ⟨hr, hs, _⟩ := hz
  have hcast : ((Work.FIPlan.gnorm z : ℤ)).natAbs = Work.FIPlan.gnorm z := Int.natAbs_natCast _
  rw [← hcast, Int.natAbs_odd, Work.FIArea7.norm_eq]
  simpa only [pow_two] using (hr.mul hr).add_even (hs.mul_right z.im)

/-- Every element of `primarySet N` has norm `N`. -/
lemma gnorm_of_mem_primarySet {N : ℕ} {z : GaussianInt} (hz : z ∈ primarySet N) :
    Work.FIPlan.gnorm z = N := (mem_primarySet.mp hz).2

/-- Every element of `primarySet N` is primary. -/
lemma isPrimary_of_mem_primarySet {N : ℕ} {z : GaussianInt} (hz : z ∈ primarySet N) :
    Work.FIPlan.IsPrimary z := (mem_primarySet.mp hz).1

/-! ## 2. Multiplicativity of the Grössencharacter on coprime arguments -/

/-- **(17.17) is multiplicative on coprime arguments.**  `ψ(z) = χ(z)(z/|z|)^k` multiplies over a
coprime factorisation because `χ` does (hypothesis) and because
`(wz)/|wz| = (w/|w|)(z/|z|)` for nonzero `w, z`. -/
lemma grossenChar_mul_of_coprime {chi : GaussianInt → ℂ} {k : ℤ}
    (hmul : ∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2)
    {w z : GaussianInt} (hw : w ≠ 0) (hz : z ≠ 0) (hcop : IsCoprime w z) :
    grossenChar chi k (w * z) = grossenChar chi k w * grossenChar chi k z := by
  have h1 : (w * z).toComplex = w.toComplex * z.toComplex := map_mul _ _ _
  have hn : ‖w.toComplex * z.toComplex‖ = ‖w.toComplex‖ * ‖z.toComplex‖ := norm_mul _ _
  rw [grossenChar, grossenChar, grossenChar, h1, hmul w z hcop, hn,
    show (((‖w.toComplex‖ * ‖z.toComplex‖ : ℝ)) : ℂ)
      = ((‖w.toComplex‖ : ℝ) : ℂ) * ((‖z.toComplex‖ : ℝ) : ℂ) from Complex.ofReal_mul _ _]
  have key : w.toComplex * z.toComplex /
        (((‖w.toComplex‖ : ℝ) : ℂ) * ((‖z.toComplex‖ : ℝ) : ℂ))
      = (w.toComplex / ((‖w.toComplex‖ : ℝ) : ℂ)) *
        (z.toComplex / ((‖z.toComplex‖ : ℝ) : ℂ)) := by
    field_simp
  rw [key, mul_zpow]
  ring

/-! ## 3. The disc form of `K∗` (22.2) -/

/-- The disc form of `K∗` (22.2), verbatim: `Σ∧_{z ∈ gBox √N, |z|² ≤ N, (z,w)=1} ψ(z)[wz]`. -/
def KStarDiscZ (N : ℕ) (w : GaussianInt) (k : ℤ) (chi : GaussianInt → ℂ) : ℂ :=
  ∑ z ∈ (Work.FIPlan.gBox ((Nat.sqrt N : ℕ) : ℤ)).filter
      (fun z => Work.FIPlan.gnorm z ≤ N ∧ Work.FIPlan.IsPrimary z ∧ IsCoprime z w),
    grossenChar chi k z * JKSym (w * z)

/-- The disc form of `K∗` (22.2), split into the fibres `Re z = r`: for `|r| ≤ √N` the fibre is
`KInnerStar (⌊√(N - r²)⌋) w k χ r`, i.e. the symmetric interval of `s` cut out by `r² + s² ≤ N`. -/
def KStarDisc (N : ℕ) (w : GaussianInt) (k : ℤ) (chi : GaussianInt → ℂ) : ℂ :=
  ∑ r ∈ Finset.Icc (-(Nat.sqrt N : ℤ)) (Nat.sqrt N : ℤ),
    KInnerStar ((Nat.sqrt (N - r.natAbs ^ 2) : ℕ) : ℤ) w k chi r

/-- `(r,s) ∈ gBox R` iff both coordinates lie in `Icc (-R) R`. -/
lemma mem_gBox_mk_iff {R : ℤ} {r s : ℤ} :
    (⟨r, s⟩ : GaussianInt) ∈ Work.FIPlan.gBox R ↔
      r ∈ Finset.Icc (-R) R ∧ s ∈ Finset.Icc (-R) R := by
  rw [Work.FIPlan.gBox, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, hpe⟩
    have h1 : p.1 = r := by simpa using congrArg Zsqrtd.re hpe
    have h2 : p.2 = s := by simpa using congrArg Zsqrtd.im hpe
    obtain ⟨h1', h2'⟩ := Finset.mem_product.mp hp
    exact ⟨h1 ▸ h1', h2 ▸ h2'⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(r, s), Finset.mem_product.mpr ⟨h1, h2⟩, rfl⟩

/-- `|r + is|² = r² + s²` on the absolute values. -/
lemma gnorm_mk_eq (r s : ℤ) :
    Work.FIPlan.gnorm (⟨r, s⟩ : GaussianInt) = r.natAbs ^ 2 + s.natAbs ^ 2 := by
  rw [Work.FIPlan.gnorm, GaussianInt.natAbs_norm_eq]
  simp only [pow_two]

/-- `r² ≤ N` for `|r| ≤ √N`. -/
lemma sqrt_sq_le_of_mem_Icc {N : ℕ} {r : ℤ}
    (hr : r ∈ Finset.Icc (-(Nat.sqrt N : ℤ)) (Nat.sqrt N : ℤ)) : r.natAbs ^ 2 ≤ N := by
  rw [Finset.mem_Icc] at hr
  have h1 : r.natAbs ≤ Nat.sqrt N := by omega
  calc r.natAbs ^ 2 ≤ (Nat.sqrt N) ^ 2 := Nat.pow_le_pow_left h1 2
    _ ≤ N := by simpa [pow_two] using Nat.sqrt_le N

/-- The disc condition `r² + s² ≤ N` is `|s| ≤ ⌊√(N - r²)⌋`. -/
lemma gnorm_mk_le_iff {N : ℕ} {r : ℤ} (hr : r.natAbs ^ 2 ≤ N) (s : ℤ) :
    Work.FIPlan.gnorm (⟨r, s⟩ : GaussianInt) ≤ N ↔
      s.natAbs ≤ Nat.sqrt (N - r.natAbs ^ 2) := by
  rw [gnorm_mk_eq, Nat.le_sqrt, ← pow_two]
  omega

/-- The disc sum `K∗` is the sum over its fibres `Re z = r`. -/
lemma KStarDiscZ_eq_KStarDisc (N : ℕ) (w : GaussianInt) (k : ℤ) (chi : GaussianInt → ℂ) :
    KStarDiscZ N w k chi = KStarDisc N w k chi := by
  set R : ℤ := (Nat.sqrt N : ℤ) with hRdef
  set Sr : ℤ → ℤ := fun r => ((Nat.sqrt (N - r.natAbs ^ 2) : ℕ) : ℤ) with hSrdef
  have key : ∀ r ∈ Finset.Icc (-R) R,
      (Finset.Icc (-R) R).filter (fun s => Work.FIPlan.gnorm (⟨r, s⟩ : GaussianInt) ≤ N ∧
          Work.FIPlan.IsPrimary (⟨r, s⟩ : GaussianInt) ∧ IsCoprime (⟨r, s⟩ : GaussianInt) w)
        = (Finset.Icc (-(Sr r)) (Sr r)).filter
            (fun s => Work.FIPlan.IsPrimary (⟨r, s⟩ : GaussianInt) ∧
              IsCoprime (⟨r, s⟩ : GaussianInt) w) := by
    intro r hr
    have hr2 : r.natAbs ^ 2 ≤ N := by
      rw [hRdef] at hr
      exact sqrt_sq_le_of_mem_Icc hr
    have hSrle : Sr r ≤ R := by
      have h2 : (((N - r.natAbs ^ 2).sqrt : ℕ) : ℤ) ≤ ((N.sqrt : ℕ) : ℤ) := by
        exact_mod_cast Nat.sqrt_le_sqrt (Nat.sub_le N (r.natAbs ^ 2))
      simpa only [hSrdef, hRdef] using h2
    have hiff : ∀ s : ℤ,
        Work.FIPlan.gnorm (⟨r, s⟩ : GaussianInt) ≤ N ↔ ((s.natAbs : ℕ) : ℤ) ≤ Sr r := by
      intro s
      have h1 : ((s.natAbs : ℕ) : ℤ) ≤ Sr r ↔ s.natAbs ≤ Nat.sqrt (N - r.natAbs ^ 2) := by
        rw [hSrdef]
        exact Nat.cast_le
      rw [h1]
      exact gnorm_mk_le_iff hr2 s
    ext s
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, hg, h3, h4⟩
      have hs : ((s.natAbs : ℕ) : ℤ) ≤ Sr r := (hiff s).mp hg
      exact ⟨⟨by omega, by omega⟩, h3, h4⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨by omega, by omega⟩, (hiff s).mpr (by omega), h3, h4⟩
  calc KStarDiscZ N w k chi
      = ∑ z ∈ (Work.FIPlan.gBox R).filter (fun z => Work.FIPlan.gnorm z ≤ N ∧
            Work.FIPlan.IsPrimary z ∧ IsCoprime z w),
          grossenChar chi k z * JKSym (w * z) := by rw [KStarDiscZ, hRdef]
    _ = ∑ p ∈ (Finset.Icc (-R) R ×ˢ Finset.Icc (-R) R).filter
            (fun p : ℤ × ℤ => Work.FIPlan.gnorm (⟨p.1, p.2⟩ : GaussianInt) ≤ N ∧
              Work.FIPlan.IsPrimary (⟨p.1, p.2⟩ : GaussianInt) ∧
              IsCoprime (⟨p.1, p.2⟩ : GaussianInt) w),
          grossenChar chi k (⟨p.1, p.2⟩ : GaussianInt) * JKSym (w * (⟨p.1, p.2⟩ : GaussianInt)) := by
        rw [Work.FIPlan.gBox, Finset.filter_image,
          Finset.sum_image (fun a _ b _ hab => Work.FIPlan.gaussMk_injective hab)]
        rfl
    _ = ∑ r ∈ Finset.Icc (-R) R, ∑ s ∈ Finset.Icc (-R) R,
          (if Work.FIPlan.gnorm (⟨r, s⟩ : GaussianInt) ≤ N ∧
              Work.FIPlan.IsPrimary (⟨r, s⟩ : GaussianInt) ∧
              IsCoprime (⟨r, s⟩ : GaussianInt) w
            then grossenChar chi k (⟨r, s⟩ : GaussianInt) * JKSym (w * (⟨r, s⟩ : GaussianInt))
            else 0) := by
        rw [Finset.sum_filter, Finset.sum_product]
    _ = ∑ r ∈ Finset.Icc (-R) R, KInnerStar (Sr r) w k chi r := by
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [← Finset.sum_filter, key r hr, Finset.sum_filter, KInnerStar]
        rfl
    _ = KStarDisc N w k chi := by rw [KStarDisc, hRdef, hSrdef]

/-! ## 4. `m`-smooth numbers -/

/-- `k` is supported on the prime divisors of `m` (`k | m^∞`). -/
def msmooth (m k : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ k → p ∣ m

end

end Work.FIArea7
