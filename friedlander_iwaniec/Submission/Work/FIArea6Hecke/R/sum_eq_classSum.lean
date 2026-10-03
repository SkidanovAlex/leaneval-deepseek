import Mathlib
import Submission.Work.FIArea6Hecke.R.DiscDefs
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea6Hecke.R.HeckeDiscRed
import Submission.Work.FIArea5.S16Hecke.isPrimary_iff_coset
import Submission.Work.FIArea5.S16Hecke.primaryAux

namespace Work.FIArea6Hecke.R

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary facts about the square box `gsBox`, the reduction `red`, and the primary
condition

The disc sum `discSum X χ = Σ_{z primary, |z|² ≤ X} χ(z)` is a sum over the square box
`gBox ⌈X⌉₊`, while the class decomposition is indexed by the primary residues `Pset d` in the
square box `gsBox (4d) = {0,…,4d-1}²`.  The lemmas below provide exactly the interface used by the
main proof:

* `mem_gsBox_iff` — coordinates of a point of `gsBox N`;
* `red_mem_gsBox` — the reduction `red d z = z mod 4d` lies in `gsBox (4d)`;
* `red_dvd` — `4d ∣ z - red d z`;
* `isPrimary_of_dvd_sub` — the primary condition is a congruence condition modulo `(1+i)³`, and
  `(1+i)³ ∣ 4d`, so it is preserved by `z ↦ z + 4dℤ[i]`;
* `red_rep` — **the reduction is the unique representative modulo `4d` of a primary element in
  `Pset d`.** -/

/-- Coordinates of a point of the square box `gsBox N = {0,…,N-1}²`. -/
private lemma mem_gsBox_iff {N : ℕ} {z : GaussianInt} :
    z ∈ gsBox N ↔ 0 ≤ z.re ∧ z.re < (N : ℤ) ∧ 0 ≤ z.im ∧ z.im < (N : ℤ) := by
  rw [gsBox, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [Finset.product_eq_sprod, Finset.mem_product] at hp
    obtain ⟨h1, h2⟩ := hp
    rw [Finset.mem_range] at h1 h2
    have h1' : (p.1 : ℤ) < (N : ℤ) := by exact_mod_cast h1
    have h2' : (p.2 : ℤ) < (N : ℤ) := by exact_mod_cast h2
    exact ⟨by simp, by simpa using h1', by simp, by simpa using h2'⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨(z.re.toNat, z.im.toNat), ?_, ?_⟩
    · rw [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨by omega, by omega⟩
    · refine Zsqrtd.ext ?_ ?_
      · simpa using Int.toNat_of_nonneg h1
      · simpa using Int.toNat_of_nonneg h3

/-- A point of `gsBox (4d)` is a point of the symmetric box `gBox (4d - 1)` with non-negative
coordinates. -/
private lemma mem_gsBox_gBox {d : ℕ} (hd : 1 ≤ d) {z : GaussianInt}
    (h : z ∈ gsBox (4 * d)) :
    z ∈ Work.FIPlan.gBox (((4 * d : ℕ) : ℤ) - 1) ∧ 0 ≤ z.re ∧ 0 ≤ z.im := by
  obtain ⟨hre0, hreL, him0, himL⟩ := mem_gsBox_iff.mp h
  have hD1 : (0 : ℤ) ≤ ((4 * d : ℕ) : ℤ) - 1 := by
    have h1 : (1 : ℤ) ≤ ((4 * d : ℕ) : ℤ) := by
      have : 1 ≤ 4 * d := by omega
      exact_mod_cast this
    omega
  refine ⟨?_, hre0, him0⟩
  rw [Work.FIArea5.S16Hecke.mem_gBox_iff, Finset.mem_Icc, Finset.mem_Icc]
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

/-- The reduction `red d z` lies in the square box `gsBox (4d)`. -/
private lemma red_mem_gsBox {d : ℕ} (hd : 1 ≤ d) (z : GaussianInt) :
    red d z ∈ gsBox (4 * d) := by
  rw [mem_gsBox_iff]
  have hN : (0 : ℤ) < ((4 * d : ℕ) : ℤ) := by
    have h1 : 1 ≤ 4 * d := by omega
    exact_mod_cast h1
  exact ⟨Int.emod_nonneg _ (ne_of_gt hN), Int.emod_lt_of_pos _ hN,
    Int.emod_nonneg _ (ne_of_gt hN), Int.emod_lt_of_pos _ hN⟩

/-- `4d ∣ z - red d z`: the reduction only changes the class modulo `4d`. -/
private lemma red_dvd (d : ℕ) (z : GaussianInt) :
    ((((4 * d : ℕ) : ℤ)) : GaussianInt) ∣ z - red d z := by
  have h := Work.FIArea6Hecke.R.red_sub_dvd d z
  simpa [neg_sub] using (dvd_neg.mpr h)

/-- `(1+i)^3 = -2+2i` generates the lattice of the primary coset, in divisibility form: `z` is
primary if and only if `(1+i)^3 ∣ z - 1`. -/
private lemma isPrimary_iff_dvd_cube (z : GaussianInt) :
    Work.FIPlan.IsPrimary z ↔ ((1 + (⟨0, 1⟩ : GaussianInt)) ^ 3) ∣ (z - 1) := by
  rw [Work.FIArea5.S16Hecke.isPrimary_iff_coset z]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w, by ring⟩
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    have h : z = ((1 + (⟨0, 1⟩ : GaussianInt)) ^ 3) * w + 1 := sub_eq_iff_eq_add.mp hw
    rw [h]; ring

/-- **The primary condition is a congruence condition modulo `4d`**: since `(1+i)³ ∣ 4d`
(`one_add_I_cube_dvd_fourD`), an element congruent to a primary element modulo `4d` is primary. -/
private lemma isPrimary_of_dvd_sub {d : ℕ} {z p : GaussianInt}
    (hp : Work.FIPlan.IsPrimary p)
    (h : ((((4 * d : ℕ) : ℤ)) : GaussianInt) ∣ z - p) : Work.FIPlan.IsPrimary z := by
  have hc : ((1 + (⟨0, 1⟩ : GaussianInt)) ^ 3)
      ∣ ((((4 * d : ℕ) : ℤ)) : GaussianInt) := one_add_I_cube_dvd_fourD d
  have hz : ((1 + (⟨0, 1⟩ : GaussianInt)) ^ 3) ∣ z - p := hc.trans h
  have hp' := (isPrimary_iff_dvd_cube p).mp hp
  rw [isPrimary_iff_dvd_cube z]
  have heq : z - 1 = (p - 1) + (z - p) := by ring
  rw [heq]
  exact dvd_add hp' hz

/-- **The reduction is the unique representative in `Pset d` of the class modulo `4d` of a
primary element.** -/
private lemma red_rep {d : ℕ} (hd : 1 ≤ d) {z : GaussianInt} (hz : Work.FIPlan.IsPrimary z) :
    red d z ∈ Pset d ∧
      ((((4 * d : ℕ) : ℤ)) : GaussianInt) ∣ z - red d z ∧
      ∀ p ∈ Pset d, ((((4 * d : ℕ) : ℤ)) : GaussianInt) ∣ z - p → p = red d z := by
  have hredP : Work.FIPlan.IsPrimary (red d z) :=
    isPrimary_of_dvd_sub hz (Work.FIArea6Hecke.R.red_sub_dvd d z)
  have hredBox : red d z ∈ gsBox (4 * d) := red_mem_gsBox hd z
  have hreddvd : ((((4 * d : ℕ) : ℤ)) : GaussianInt) ∣ z - red d z := red_dvd d z
  have hN : (((4 * d : ℕ) : ℤ)) ≠ 0 := by
    have h1 : 1 ≤ 4 * d := by omega
    have h2 : (0 : ℤ) < ((4 * d : ℕ) : ℤ) := by exact_mod_cast h1
    omega
  refine ⟨?_, hreddvd, ?_⟩
  · rw [Pset, Finset.mem_filter]
    exact ⟨hredBox, hredP⟩
  · intro p hp hpdvd
    rw [Pset, Finset.mem_filter] at hp
    obtain ⟨hpbox, hpprim⟩ := hp
    obtain ⟨hpbox', hpre, hpim⟩ := mem_gsBox_gBox hd hpbox
    refine Work.FIArea6Hecke.R.box_eq_of_dvd_sub d hd hpbox'
      (Work.FIArea6Hecke.R.red_mem_gBox d hd z) hpre hpim
      (Int.emod_nonneg _ hN) (Int.emod_nonneg _ hN) ?_
    have h1 : ((((4 * d : ℕ) : ℤ)) : GaussianInt) ∣ p - z :=
      by simpa [neg_sub] using (dvd_neg.mpr hpdvd)
    have heq : p - red d z = (p - z) + (z - red d z) := by ring
    rw [heq]
    exact dvd_add h1 hreddvd

/-! ## The box `gBox ⌈X⌉₊` contains every Gaussian integer of norm `≤ X` -/

/-- Every Gaussian integer with `|z|² ≤ X` lies in the box `gBox ⌈X⌉₊` (for `X ≥ 1`). -/
private lemma mem_gBox_of_norm_le {X : ℝ} (hX : 1 ≤ X) {z : GaussianInt}
    (h : (Work.FIPlan.gnorm z : ℝ) ≤ X) : z ∈ Work.FIPlan.gBox ⌈X⌉₊ := by
  refine Work.FIArea5.S16Hecke.mem_gBox_of_gnorm_le (R := ((⌈X⌉₊ : ℕ) : ℤ)) ?_ ?_
  · have h1 : (1 : ℝ) ≤ ((⌈X⌉₊ : ℕ) : ℝ) := le_trans hX (Nat.le_ceil X)
    have h1' : (1 : ℤ) ≤ ((⌈X⌉₊ : ℕ) : ℤ) := by exact_mod_cast h1
    omega
  · have h2 : ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ ((⌈X⌉₊ : ℕ) : ℝ) := le_trans h (Nat.le_ceil X)
    exact_mod_cast h2

/-! ## The class count as a cardinality of a finite set -/

/-- `classCount d p X` is the cardinality of the set of points of the box `gBox ⌈X⌉₊` that are
congruent to `p` modulo `4d` and have norm `≤ X`. -/
private lemma classCount_eq_card (d : ℕ) (p : GaussianInt) {X : ℝ} (hX : 1 ≤ X) :
    classCount d p X
      = ((Work.FIPlan.gBox ⌈X⌉₊).filter (fun z =>
          ((((4 * d : ℕ) : ℤ)) : GaussianInt) ∣ z - p
            ∧ (Work.FIPlan.gnorm z : ℝ) ≤ X)).card := by
  have hset : {z : GaussianInt | ((((4 * d : ℕ) : ℤ)) : GaussianInt) ∣ z - p
        ∧ (Work.FIPlan.gnorm z : ℝ) ≤ X}
      = ↑((Work.FIPlan.gBox ⌈X⌉₊).filter (fun z =>
          ((((4 * d : ℕ) : ℤ)) : GaussianInt) ∣ z - p
            ∧ (Work.FIPlan.gnorm z : ℝ) ≤ X)) := by
    ext z
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨mem_gBox_of_norm_le hX h2, h1, h2⟩
    · rintro ⟨-, h1, h2⟩
      exact ⟨h1, h2⟩
  rw [classCount, hset, Set.ncard_coe_finset]

/-! ## The main theorem -/

/-- **The disc sum is the class decomposition over the primary residues modulo `4d`.**

Every primary `z` with `|z|² ≤ X` is congruent modulo `4d` to exactly one element of `Pset d`,
namely its reduction `red d z`; conversely every point of `Pset d` is primary, so its class modulo
`4d` consists of primary elements only.  Since a strict character `χ` of modulus `4d` is constant
on classes and each class `p` contributes `classCount d p X` points, the disc sum splits as
`∑_{p ∈ Pset d} χ(p) · classCount d p X`. -/
theorem sum_eq_classSum {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi) {X : ℝ} (hX : 1 ≤ X) :
    Work.FIArea6Hecke.R.discSum X chi
      = ∑ p ∈ Work.FIArea6Hecke.R.Pset d,
          chi p * ((Work.FIArea6Hecke.R.classCount d p X : ℕ) : ℂ) := by
  classical
  have hper : ∀ z w : GaussianInt,
      ((((4 * d : ℕ) : ℤ)) : GaussianInt) ∣ z - w → chi z = chi w := hchi.1.2.2.2.1
  -- the disc sum, as a sum over the primary points of the box
  set S : Finset GaussianInt := (Work.FIPlan.gBox ⌈X⌉₊).filter
    (fun z => Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ X) with hS
  have hL : discSum X chi = ∑ z ∈ S, chi z := by
    rw [hS]
    unfold discSum
    rw [Finset.sum_filter]
  rw [hL]
  -- each primary point contributes to exactly one class `p ∈ Pset d`
  have hstep : ∀ z ∈ S,
      (∑ p ∈ Pset d, (if ((((4 * d : ℕ) : ℤ)) : GaussianInt) ∣ z - p
        then chi p else 0)) = chi z := by
    intro z hz
    rw [hS, Finset.mem_filter] at hz
    obtain ⟨-, hzprim, -⟩ := hz
    have hrep := red_rep hd hzprim
    have hsing : (Pset d).filter
        (fun p => ((((4 * d : ℕ) : ℤ)) : GaussianInt) ∣ z - p) = {red d z} :=
      Finset.eq_singleton_iff_unique_mem.mpr
        ⟨Finset.mem_filter.mpr ⟨hrep.1, hrep.2.1⟩,
          fun x hx => hrep.2.2 x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2⟩
    rw [← Finset.sum_filter, hsing, Finset.sum_singleton]
    exact (hper z (red d z) hrep.2.1).symm
  calc ∑ z ∈ S, chi z
      = ∑ z ∈ S, ∑ p ∈ Pset d,
          (if ((((4 * d : ℕ) : ℤ)) : GaussianInt) ∣ z - p then chi p else 0) :=
        Finset.sum_congr rfl (fun z hz => (hstep z hz).symm)
    _ = ∑ p ∈ Pset d, ∑ z ∈ S,
          (if ((((4 * d : ℕ) : ℤ)) : GaussianInt) ∣ z - p then chi p else 0) :=
        Finset.sum_comm
    _ = ∑ p ∈ Pset d, chi p * ((classCount d p X : ℕ) : ℂ) := by
        refine Finset.sum_congr rfl (fun p hp => ?_)
        have hpP : Work.FIPlan.IsPrimary p := by
          rw [Pset, Finset.mem_filter] at hp
          exact hp.2
        have hTeq : S.filter (fun z => ((((4 * d : ℕ) : ℤ)) : GaussianInt) ∣ z - p)
            = (Work.FIPlan.gBox ⌈X⌉₊).filter (fun z =>
                ((((4 * d : ℕ) : ℤ)) : GaussianInt) ∣ z - p
                  ∧ (Work.FIPlan.gnorm z : ℝ) ≤ X) := by
          rw [hS]
          ext z
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨⟨hzbox, -, hznorm⟩, hzdvd⟩
            exact ⟨hzbox, hzdvd, hznorm⟩
          · rintro ⟨hzbox, hzdvd, hznorm⟩
            exact ⟨⟨hzbox, isPrimary_of_dvd_sub hpP hzdvd, hznorm⟩, hzdvd⟩
        rw [← Finset.sum_filter, hTeq, Finset.sum_const, nsmul_eq_mul,
          classCount_eq_card d p hX, mul_comm]

end

end Work.FIArea6Hecke.R
