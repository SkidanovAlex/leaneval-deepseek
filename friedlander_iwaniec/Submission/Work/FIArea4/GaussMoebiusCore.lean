/-
# Core API for the Möbius-type indicator of coprimality in `ℤ[i]`

This module collects the elementary arithmetic of `ℤ[i]` needed by
`Work.FIArea4.gaussMoebius_coprime_indicator`:

* a (noncomputable) `NormalizationMonoid` structure on `GaussianInt`, giving access to
  `UniqueFactorizationMonoid.normalizedFactors`;
* the notion of primary associate `primAssoc z` (`z` with `Odd (gnorm z)` has a unique primary
  associate, `Commons.NumberTheory.GaussianInt.primary_associate_exists_unique`);
* the auxiliary box membership facts;
* the main computation `sum_primaryDivs_eq`: for `g ≠ 0` of odd norm, the sum of
  `moebius` over the primary divisors of `g` is `1` if `g` is a unit and `0` otherwise.
-/
import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Commons.NumberTheory.GaussianInt.primary_associate_exists_unique

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

open Zsqrtd

/-! ## 0. A `NormalizationMonoid` structure on `ℤ[i]` -/

noncomputable instance instNormalizationMonoidGaussianInt : NormalizationMonoid GaussianInt :=
  Classical.choice (inferInstance : Nonempty (NormalizationMonoid GaussianInt))

/-! ## 1. Elementary API of `gnorm` -/

theorem gnorm_zero : Work.FIPlan.gnorm (0 : GaussianInt) = 0 := by
  simp [Work.FIPlan.gnorm, Zsqrtd.norm_zero]

theorem gnorm_mul (z w : GaussianInt) :
    Work.FIPlan.gnorm (z * w) = Work.FIPlan.gnorm z * Work.FIPlan.gnorm w := by
  simp only [Work.FIPlan.gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

theorem gnorm_one : Work.FIPlan.gnorm (1 : GaussianInt) = 1 := by
  simp [Work.FIPlan.gnorm, Zsqrtd.norm_def]

theorem gnorm_eq_zero {z : GaussianInt} : Work.FIPlan.gnorm z = 0 ↔ z = 0 := by
  rw [Work.FIPlan.gnorm, Int.natAbs_eq_zero, GaussianInt.norm_eq_zero]

theorem gnorm_ne_zero {z : GaussianInt} (hz : z ≠ 0) : Work.FIPlan.gnorm z ≠ 0 :=
  fun h => hz (gnorm_eq_zero.mp h)

theorem gnorm_pos {z : GaussianInt} (hz : z ≠ 0) : 0 < Work.FIPlan.gnorm z :=
  Nat.pos_of_ne_zero (gnorm_ne_zero hz)

theorem gnorm_eq_coords (z : GaussianInt) :
    (Work.FIPlan.gnorm z : ℤ) = z.re ^ 2 + z.im ^ 2 := by
  have h : z.norm = z.re ^ 2 + z.im ^ 2 := by rw [Zsqrtd.norm_def]; ring
  have h2 : (0 : ℤ) ≤ z.re ^ 2 + z.im ^ 2 := by positivity
  rw [Work.FIPlan.gnorm, h, Int.natAbs_of_nonneg h2]

theorem gnorm_dvd {w g : GaussianInt} (h : w ∣ g) : Work.FIPlan.gnorm w ∣ Work.FIPlan.gnorm g := by
  obtain ⟨k, rfl⟩ := h
  rw [gnorm_mul]
  exact dvd_mul_right _ _

theorem gnorm_finset_prod (T : Finset GaussianInt) :
    Work.FIPlan.gnorm (T.prod id) = ∏ p ∈ T, Work.FIPlan.gnorm p := by
  induction T using Finset.induction with
  | empty => simp [gnorm_one]
  | insert a T ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, gnorm_mul, ih]
      rfl

theorem abs_le_sq (a : ℤ) : |a| ≤ a ^ 2 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · have h1 : (1 : ℤ) ≤ |a| := Int.one_le_abs ha
    have h2 : |a| * 1 ≤ |a| * |a| := mul_le_mul_of_nonneg_left h1 (abs_nonneg a)
    calc |a| = |a| * 1 := (mul_one _).symm
      _ ≤ |a| * |a| := h2
      _ = a ^ 2 := by rw [abs_mul_abs_self, pow_two]

/-! ## 2. Primary elements -/

theorem isPrimary_one : Work.FIPlan.IsPrimary (1 : GaussianInt) := by
  refine ⟨?_, ?_, ?_⟩
  · exact odd_one
  · refine ⟨0, ?_⟩
    show (1 : GaussianInt).im = 0 + 0
    rw [show (1 : GaussianInt).im = 0 from rfl]
    ring
  · exact Int.ModEq.refl 0

theorem isPrimary_mul {z w : GaussianInt} (hz : Work.FIPlan.IsPrimary z)
    (hw : Work.FIPlan.IsPrimary w) : Work.FIPlan.IsPrimary (z * w) := by
  obtain ⟨hzo, hze, hzc⟩ := hz
  obtain ⟨hwo, hwe, hwc⟩ := hw
  have hre : (z * w).re = z.re * w.re - z.im * w.im := by rw [Zsqrtd.re_mul]; ring
  have him : (z * w).im = z.re * w.im + z.im * w.re := by rw [Zsqrtd.im_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [hre]; exact (hzo.mul hwo).sub_even (hze.mul_right w.im)
  · rw [him]; exact (hwe.mul_left z.re).add (hze.mul_right w.re)
  · rw [him, hre]
    have L1 : z.re * w.im ≡ z.re * (w.re - 1) [ZMOD 4] := Int.ModEq.mul_left z.re hwc
    have L2 : z.im * w.re ≡ (z.re - 1) * w.re [ZMOD 4] := Int.ModEq.mul_right w.re hzc
    have hmid : z.re * (w.re - 1) + (z.re - 1) * w.re
        ≡ (z.re * w.re - (z.re - 1) * (w.re - 1)) - 1 [ZMOD 4] := by
      rw [Int.modEq_iff_dvd]
      obtain ⟨k, hk⟩ := hzo
      obtain ⟨l, hl⟩ := hwo
      use -2 * k * l
      rw [hk, hl]; ring
    have hR : z.re * w.re - z.im * w.im - 1
        ≡ z.re * w.re - (z.re - 1) * (w.re - 1) - 1 [ZMOD 4] :=
      ((Int.ModEq.refl (z.re * w.re)).sub (Int.ModEq.mul hzc hwc)).sub (Int.ModEq.refl 1)
    exact (L1.add L2).trans (hmid.trans hR.symm)

theorem isPrimary_ne_zero {z : GaussianInt} (hz : Work.FIPlan.IsPrimary z) : z ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := hz.1
  rw [h] at hk
  rw [show (0 : GaussianInt).re = 0 from rfl] at hk
  omega

theorem isPrimary_odd_gnorm {z : GaussianInt} (hz : Work.FIPlan.IsPrimary z) :
    Odd (Work.FIPlan.gnorm z) := by
  obtain ⟨h1, h2, -⟩ := hz
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  rw [Work.FIPlan.gnorm]
  refine Int.natAbs_odd.mpr ?_
  have hcoords : z.norm = z.re ^ 2 + z.im ^ 2 := by rw [Zsqrtd.norm_def]; ring
  rw [hcoords, ha, hb]
  exact ⟨2 * a ^ 2 + 2 * a + 2 * b ^ 2, by ring⟩

/-! ## 3. The primary associate -/

theorem existsUnique_primary_assoc {z : GaussianInt} (hz : z ≠ 0)
    (hodd : Odd (Work.FIPlan.gnorm z)) :
    ∃! w : GaussianInt, Associated w z ∧ Work.FIPlan.IsPrimary w := by
  obtain ⟨w, ⟨hw1, hw2, hw3, hw4⟩, huniq⟩ :=
    Commons.NumberTheory.GaussianInt.primary_associate_exists_unique hz hodd
  refine ⟨w, ⟨hw1, hw2, hw3, ?_⟩, ?_⟩
  · refine (ZMod.intCast_eq_intCast_iff w.im (w.re - 1) 4).mp ?_
    push_cast
    exact hw4
  · intro y hy
    refine huniq y ⟨hy.1, hy.2.1, hy.2.2.1, ?_⟩
    have h := (ZMod.intCast_eq_intCast_iff y.im (y.re - 1) 4).mpr hy.2.2.2
    push_cast at h
    exact h

noncomputable def primAssoc (z : GaussianInt) : GaussianInt :=
  if h : z ≠ 0 ∧ Odd (Work.FIPlan.gnorm z) then
    Classical.choose (existsUnique_primary_assoc h.1 h.2)
  else z

theorem primAssoc_associated {z : GaussianInt} (hz : z ≠ 0)
    (hodd : Odd (Work.FIPlan.gnorm z)) : Associated (primAssoc z) z := by
  rw [primAssoc, dif_pos ⟨hz, hodd⟩]
  exact (Classical.choose_spec (existsUnique_primary_assoc hz hodd)).1.1

theorem primAssoc_primary {z : GaussianInt} (hz : z ≠ 0)
    (hodd : Odd (Work.FIPlan.gnorm z)) : Work.FIPlan.IsPrimary (primAssoc z) := by
  rw [primAssoc, dif_pos ⟨hz, hodd⟩]
  exact (Classical.choose_spec (existsUnique_primary_assoc hz hodd)).1.2

theorem gnorm_eq_of_associated {x y : GaussianInt} (h : Associated x y) :
    Work.FIPlan.gnorm x = Work.FIPlan.gnorm y := by
  obtain ⟨u, hu⟩ := h
  have hu1 : Work.FIPlan.gnorm (↑u : GaussianInt) = 1 :=
    Zsqrtd.norm_eq_one_iff.mpr (Units.isUnit u)
  rw [← hu, gnorm_mul, hu1, mul_one]

theorem gnorm_primAssoc {z : GaussianInt} (hz : z ≠ 0) (hodd : Odd (Work.FIPlan.gnorm z)) :
    Work.FIPlan.gnorm (primAssoc z) = Work.FIPlan.gnorm z :=
  gnorm_eq_of_associated (primAssoc_associated hz hodd)

theorem primAssoc_ne_zero {z : GaussianInt} (hz : z ≠ 0) (hodd : Odd (Work.FIPlan.gnorm z)) :
    primAssoc z ≠ 0 := by
  intro h
  have h1 : Work.FIPlan.gnorm (primAssoc z) = Work.FIPlan.gnorm z := gnorm_primAssoc hz hodd
  rw [h, gnorm_zero] at h1
  exact gnorm_ne_zero hz h1.symm

theorem primAssoc_eq_self {z : GaussianInt} (hz : Work.FIPlan.IsPrimary z) : primAssoc z = z := by
  rw [primAssoc, dif_pos ⟨isPrimary_ne_zero hz, isPrimary_odd_gnorm hz⟩]
  exact ((Classical.choose_spec (existsUnique_primary_assoc (isPrimary_ne_zero hz)
    (isPrimary_odd_gnorm hz))).2 z ⟨Associated.refl z, hz⟩).symm

theorem primAssoc_eq_of_associated {x y : GaussianInt} (hx : x ≠ 0)
    (hox : Odd (Work.FIPlan.gnorm x)) (hy : y ≠ 0) (hoy : Odd (Work.FIPlan.gnorm y))
    (h : Associated x y) : primAssoc x = primAssoc y := by
  conv_rhs => rw [primAssoc, dif_pos ⟨hy, hoy⟩]
  exact (Classical.choose_spec (existsUnique_primary_assoc hy hoy)).2 (primAssoc x)
    ⟨(primAssoc_associated hx hox).trans h, primAssoc_primary hx hox⟩

/-! ## 4. Box membership -/

theorem mem_gBox {R : ℤ} {z : GaussianInt} :
    z ∈ Work.FIPlan.gBox R ↔ -R ≤ z.re ∧ z.re ≤ R ∧ -R ≤ z.im ∧ z.im ≤ R := by
  show z ∈ (((Finset.Icc (-R) R) ×ˢ (Finset.Icc (-R) R)).image
      (fun p : ℤ × ℤ => (⟨p.1, p.2⟩ : GaussianInt))) ↔
      -R ≤ z.re ∧ z.re ≤ R ∧ -R ≤ z.im ∧ z.im ≤ R
  rw [Finset.mem_image]
  constructor
  · rintro ⟨p, hp, hpe⟩
    rw [Finset.mem_product] at hp
    obtain ⟨h1, h2⟩ := hp
    rw [Finset.mem_Icc] at h1 h2
    rw [← hpe]
    exact ⟨h1.1, h1.2, h2.1, h2.2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨(z.re, z.im), by
      rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, by rfl⟩

theorem primaryDivisor_mem_gBox {g w : GaussianInt} (hg : g ≠ 0) (hwdvd : w ∣ g)
    (hprim : Work.FIPlan.IsPrimary w) :
    w ∈ Work.FIPlan.gBox ((Work.FIPlan.gnorm g : ℕ) : ℤ) := by
  have hgpos : 0 < Work.FIPlan.gnorm g := gnorm_pos hg
  have hle : Work.FIPlan.gnorm w ≤ Work.FIPlan.gnorm g :=
    Nat.le_of_dvd hgpos (gnorm_dvd hwdvd)
  have hle' : (Work.FIPlan.gnorm w : ℤ) ≤ (Work.FIPlan.gnorm g : ℤ) := by exact_mod_cast hle
  have hcoords_w : (Work.FIPlan.gnorm w : ℤ) = w.re ^ 2 + w.im ^ 2 := gnorm_eq_coords w
  have hre : |w.re| ≤ (Work.FIPlan.gnorm g : ℤ) := by
    have h1 : w.re ^ 2 ≤ (Work.FIPlan.gnorm w : ℤ) := by
      rw [hcoords_w]; nlinarith [sq_nonneg w.im]
    have h2 : |w.re| ≤ w.re ^ 2 := abs_le_sq w.re
    linarith
  have him : |w.im| ≤ (Work.FIPlan.gnorm g : ℤ) := by
    have h1 : w.im ^ 2 ≤ (Work.FIPlan.gnorm w : ℤ) := by
      rw [hcoords_w]; nlinarith [sq_nonneg w.re]
    have h2 : |w.im| ≤ w.im ^ 2 := abs_le_sq w.im
    linarith
  rw [mem_gBox]
  obtain ⟨h1, h2⟩ := abs_le.mp hre
  obtain ⟨h3, h4⟩ := abs_le.mp him
  exact ⟨h1, h2, h3, h4⟩

/-! ## 5. `normalizedFactors` of products of subsets -/

theorem multiset_toFinset_mono {s t : Multiset GaussianInt} (h : s ≤ t) :
    s.toFinset ⊆ t.toFinset := by
  intro x hx
  rw [Multiset.mem_toFinset] at hx ⊢
  exact Multiset.count_pos.mp
    (lt_of_lt_of_le (Multiset.count_pos.mpr hx) (Multiset.count_le_of_le x h))

theorem toFinset_val_of_nodup {s : Multiset GaussianInt} (h : s.Nodup) : s.toFinset.val = s :=
  (congrArg Finset.val (Multiset.toFinset_eq h)).symm

theorem nf_eq_singleton {g p : GaussianInt}
    (hp : p ∈ UniqueFactorizationMonoid.normalizedFactors g) :
    UniqueFactorizationMonoid.normalizedFactors p = {p} := by
  have hpirr := (UniqueFactorizationMonoid.prime_of_normalized_factor p hp).irreducible
  rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hpirr,
    UniqueFactorizationMonoid.normalize_normalized_factor p hp]

theorem nf_prod_finset_of_subset {g : GaussianInt} {T : Finset GaussianInt}
    (hT : T ⊆ (UniqueFactorizationMonoid.normalizedFactors g).toFinset) :
    UniqueFactorizationMonoid.normalizedFactors (T.prod id) = T.val := by
  have h0 : (0 : GaussianInt) ∉ T.val := by
    intro h
    have hmem : (0 : GaussianInt) ∈ T := by simpa using h
    exact (UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors
      (Multiset.mem_toFinset.mp (hT hmem))) rfl
  rw [← Finset.prod_val T,
    UniqueFactorizationMonoid.normalizedFactors_multiset_prod T.val h0]
  have hmap : Multiset.map UniqueFactorizationMonoid.normalizedFactors T.val
      = Multiset.map (fun p => ({p} : Multiset GaussianInt)) T.val := by
    refine Multiset.map_congr rfl (fun p hp => ?_)
    exact nf_eq_singleton (Multiset.mem_toFinset.mp (hT (by simpa using hp)))
  rw [hmap, Multiset.sum_map_singleton]

theorem odd_gnorm_of_dvd_odd {p g : GaussianInt} (hpdvd : p ∣ g)
    (hg : Odd (Work.FIPlan.gnorm g)) : Odd (Work.FIPlan.gnorm p) := by
  by_contra hcon
  have hev : Even (Work.FIPlan.gnorm p) := Nat.not_odd_iff_even.mp hcon
  obtain ⟨k, hk⟩ := gnorm_dvd hpdvd
  rw [hk] at hg
  exact (Nat.not_even_iff_odd.mpr hg) (hev.mul_right k)

/-! ## 6. The main computation -/

theorem sum_primaryDivs_eq (g : GaussianInt) (hg : g ≠ 0) (hodd : Odd (Work.FIPlan.gnorm g)) :
    (∑ w ∈ (Work.FIPlan.gBox ((Work.FIPlan.gnorm g : ℕ) : ℤ)).filter
        (fun w => w ∣ g ∧ Work.FIPlan.IsPrimary w),
      (UniqueFactorizationMonoid.moebius w : ℂ)) = if IsUnit g then 1 else 0 := by
  classical
  set B : ℤ := ((Work.FIPlan.gnorm g : ℕ) : ℤ) with hB
  set M : Multiset GaussianInt := UniqueFactorizationMonoid.normalizedFactors g with hM
  have hstep1 :
      (∑ w ∈ (Work.FIPlan.gBox B).filter (fun w => w ∣ g ∧ Work.FIPlan.IsPrimary w),
        (UniqueFactorizationMonoid.moebius w : ℂ))
      = ∑ w ∈ ((Work.FIPlan.gBox B).filter (fun w => w ∣ g ∧ Work.FIPlan.IsPrimary w)).filter
            (fun w => Squarefree w),
          (UniqueFactorizationMonoid.moebius w : ℂ) := by
    conv_rhs => rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    by_cases h : Squarefree w
    · simp [h]
    · simp [h]
  have hstep2 :
      (∑ w ∈ ((Work.FIPlan.gBox B).filter (fun w => w ∣ g ∧ Work.FIPlan.IsPrimary w)).filter
            (fun w => Squarefree w),
          (UniqueFactorizationMonoid.moebius w : ℂ))
      = ∑ T ∈ M.toFinset.powerset, ((-1 : ℂ) ^ T.card) := by
    refine Finset.sum_bij'
      (fun w _ => (UniqueFactorizationMonoid.normalizedFactors w).toFinset)
      (fun T _ => primAssoc (T.prod id)) ?_ ?_ ?_ ?_ ?_
    · -- membership of the image in the powerset
      intro w hw
      simp only [Finset.mem_filter] at hw
      obtain ⟨⟨hwB, hwdvd, hwprim⟩, hwsq⟩ := hw
      have hw0 : w ≠ 0 := isPrimary_ne_zero hwprim
      have hle : UniqueFactorizationMonoid.normalizedFactors w
          ≤ UniqueFactorizationMonoid.normalizedFactors g :=
        (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hw0 hg).mp hwdvd
      rw [Finset.mem_powerset, hM]
      exact multiset_toFinset_mono hle
    · -- membership of the inverse image
      intro T hT
      rw [Finset.mem_powerset] at hT
      have hT' : T ⊆ (UniqueFactorizationMonoid.normalizedFactors g).toFinset := by
        rw [← hM]; exact hT
      have hpodd : ∀ p ∈ (UniqueFactorizationMonoid.normalizedFactors g).toFinset,
          Odd (Work.FIPlan.gnorm p) := by
        intro p hp
        exact odd_gnorm_of_dvd_odd
          (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hp))
          hodd
      have hx0 : T.prod id ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro p hp
        exact UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors
          (Multiset.mem_toFinset.mp (hT' hp))
      have hxodd : Odd (Work.FIPlan.gnorm (T.prod id)) := by
        rw [gnorm_finset_prod]
        exact Finset.prod_induction (fun p => Work.FIPlan.gnorm p) (fun m => Odd m)
          (fun a b ha hb => ha.mul hb) odd_one (fun x hx => hpodd x (hT' hx))
      have hxnf : UniqueFactorizationMonoid.normalizedFactors (primAssoc (T.prod id)) = T.val := by
        rw [Associated.normalizedFactors_eq (primAssoc_associated hx0 hxodd)]
        exact nf_prod_finset_of_subset hT'
      have hxprim : Work.FIPlan.IsPrimary (primAssoc (T.prod id)) := primAssoc_primary hx0 hxodd
      have hTM : T.val ≤ M := by
        have h1 : T.val ≤ M.toFinset.val := Finset.val_le_iff.mpr hT
        have h2 : M.toFinset.val = M.dedup := Multiset.toFinset_val M
        exact h1.trans (h2.le.trans (Multiset.dedup_le M))
      have hxdvd : primAssoc (T.prod id) ∣ g :=
        (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
          (primAssoc_ne_zero hx0 hxodd) hg).mpr (by rw [hxnf]; rw [← hM]; exact hTM)
      have hxsq : Squarefree (primAssoc (T.prod id)) :=
        (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
          (primAssoc_ne_zero hx0 hxodd)).mpr (by rw [hxnf]; exact T.nodup)
      simp only [Finset.mem_filter]
      exact ⟨⟨primaryDivisor_mem_gBox hg hxdvd hxprim, hxdvd, hxprim⟩, hxsq⟩
    · -- left inverse
      intro w hw
      simp only [Finset.mem_filter] at hw
      obtain ⟨⟨hwB, hwdvd, hwprim⟩, hwsq⟩ := hw
      have hw0 : w ≠ 0 := isPrimary_ne_zero hwprim
      have hwodd : Odd (Work.FIPlan.gnorm w) := isPrimary_odd_gnorm hwprim
      have hnodup : (UniqueFactorizationMonoid.normalizedFactors w).Nodup :=
        (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hw0).mp hwsq
      have hval : (UniqueFactorizationMonoid.normalizedFactors w).toFinset.val
          = UniqueFactorizationMonoid.normalizedFactors w := toFinset_val_of_nodup hnodup
      have hx0 : (UniqueFactorizationMonoid.normalizedFactors w).toFinset.prod id ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro p hp
        exact UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors
          (Multiset.mem_toFinset.mp hp)
      have hassoc : Associated ((UniqueFactorizationMonoid.normalizedFactors w).toFinset.prod id) w := by
        rw [← Finset.prod_val, hval]
        exact UniqueFactorizationMonoid.prod_normalizedFactors hw0
      have hxodd : Odd (Work.FIPlan.gnorm
          ((UniqueFactorizationMonoid.normalizedFactors w).toFinset.prod id)) := by
        rw [gnorm_eq_of_associated hassoc]
        exact hwodd
      rw [primAssoc_eq_of_associated hx0 hxodd hw0 hwodd hassoc, primAssoc_eq_self hwprim]
    · -- right inverse
      intro T hT
      rw [Finset.mem_powerset] at hT
      have hT' : T ⊆ (UniqueFactorizationMonoid.normalizedFactors g).toFinset := by
        rw [← hM]; exact hT
      have hpodd : ∀ p ∈ (UniqueFactorizationMonoid.normalizedFactors g).toFinset,
          Odd (Work.FIPlan.gnorm p) := by
        intro p hp
        exact odd_gnorm_of_dvd_odd
          (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hp))
          hodd
      have hx0 : T.prod id ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro p hp
        exact UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors
          (Multiset.mem_toFinset.mp (hT' hp))
      have hxodd : Odd (Work.FIPlan.gnorm (T.prod id)) := by
        rw [gnorm_finset_prod]
        exact Finset.prod_induction (fun p => Work.FIPlan.gnorm p) (fun m => Odd m)
          (fun a b ha hb => ha.mul hb) odd_one (fun x hx => hpodd x (hT' hx))
      show (UniqueFactorizationMonoid.normalizedFactors (primAssoc (T.prod id))).toFinset = T
      rw [Associated.normalizedFactors_eq (primAssoc_associated hx0 hxodd),
        nf_prod_finset_of_subset hT']
      exact Finset.val_toFinset T
    · -- the summands agree
      intro w hw
      simp only [Finset.mem_filter] at hw
      obtain ⟨⟨hwB, hwdvd, hwprim⟩, hwsq⟩ := hw
      have hw0 : w ≠ 0 := isPrimary_ne_zero hwprim
      have hnodup : (UniqueFactorizationMonoid.normalizedFactors w).Nodup :=
        (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hw0).mp hwsq
      have hcard : (UniqueFactorizationMonoid.normalizedFactors w).toFinset.card
          = (UniqueFactorizationMonoid.factors w).card := by
        rw [Multiset.toFinset_card_of_nodup hnodup]
        exact Multiset.card_map _ _
      rw [Squarefree.moebius_eq hwsq, hcard]
      push_cast
      rfl
  have hstep3 : (∑ T ∈ M.toFinset.powerset, ((-1 : ℂ) ^ T.card))
      = if IsUnit g then 1 else 0 := by
    have hM0 : M.toFinset = ∅ ↔ IsUnit g := by
      rw [Multiset.toFinset_eq_empty, hM, UniqueFactorizationMonoid.normalizedFactors_eq_zero_iff hg]
    have h1 : (∑ T ∈ M.toFinset.powerset, ((-1 : ℂ) ^ T.card))
        = ∏ p ∈ M.toFinset, (1 + (-1 : ℂ)) := by
      rw [Finset.prod_one_add]
      refine Finset.sum_congr rfl (fun T _ => ?_)
      rw [Finset.prod_const]
    have h2 : (∏ p ∈ M.toFinset, (1 + (-1 : ℂ)))
        = if M.toFinset = ∅ then (1 : ℂ) else 0 := by
      rw [show (1 + (-1 : ℂ)) = 0 by ring, Finset.prod_const]
      by_cases h : M.toFinset = ∅
      · rw [h]; simp
      · rw [if_neg h]
        exact zero_pow (fun hc => h (Finset.card_eq_zero.mp hc))
    rw [h1, h2]
    by_cases h : IsUnit g
    · rw [if_pos (hM0.mpr h), if_pos h]
    · rw [if_neg (fun hc => h (hM0.mp hc)), if_neg h]
  rw [hstep1, hstep2, hstep3]

theorem filter_primaryDivs_eq {g : GaussianInt} (hg : g ≠ 0) (hodd : Odd (Work.FIPlan.gnorm g))
    {B : ℤ} (hB : (Work.FIPlan.gnorm g : ℤ) ≤ B) :
    (Work.FIPlan.gBox B).filter (fun w => w ∣ g ∧ Work.FIPlan.IsPrimary w)
      = (Work.FIPlan.gBox ((Work.FIPlan.gnorm g : ℕ) : ℤ)).filter
          (fun w => w ∣ g ∧ Work.FIPlan.IsPrimary w) := by
  apply Finset.ext
  intro w
  rw [Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨hw, hdvd, hprim⟩
    exact ⟨primaryDivisor_mem_gBox hg hdvd hprim, hdvd, hprim⟩
  · rintro ⟨hw, hdvd, hprim⟩
    refine ⟨?_, hdvd, hprim⟩
    rw [mem_gBox] at hw ⊢
    obtain ⟨h1, h2, h3, h4⟩ := hw
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem sum_primaryDivs_eq_of_le (g : GaussianInt) (hg : g ≠ 0)
    (hodd : Odd (Work.FIPlan.gnorm g)) {B : ℤ} (hB : (Work.FIPlan.gnorm g : ℤ) ≤ B) :
    (∑ w ∈ (Work.FIPlan.gBox B).filter (fun w => w ∣ g ∧ Work.FIPlan.IsPrimary w),
      (UniqueFactorizationMonoid.moebius w : ℂ)) = if IsUnit g then 1 else 0 := by
  rw [filter_primaryDivs_eq hg hodd hB]
  exact sum_primaryDivs_eq g hg hodd

end

end Work.FIArea4
