import Mathlib
import Submission.Work.DSEQP.vanishing_ideal_chart
import Submission.Work.DSEQP.chart_transport_gen

namespace Work.DSEQP

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

set_option linter.style.haveILetI false

/-!
# `Work.DSEQP.vanishing_ideal_chart_monomial`

The chart-saturation statement of `vanishing_ideal_chart`, generalised from a single variable
`X j` to an arbitrary product `∏_{k ∈ T} X k` of variables (`T` a nonempty finset).

The proof is the same argument as in `vanishing_ideal_chart`, with the degree-`1` element
`X j` replaced by an arbitrary homogeneous element `F ∈ 𝒜 d` (`d > 0`): one clears the
denominator of `z` (`z = a/F^{k₀}`), shows that for every chart `D₊(X j')` some multiple
`a F^m / (X j')^{(k₀+m)d}` lies in the chart ideal, and then pads all these exponents up to a
common `M`.  The auxiliary inputs are the generalised chart transport
(`Work.DSEQP.chart_transport_gen`) and the generalised "swap" identity `away_mk_swap_gen`
below, replacing `away_mk_swap` of `vanishing_ideal_chart`.
-/

section Helpers

variable {S : Type*} [CommRing S] {σ : Type*} [SetLike σ S] [AddSubgroupClass σ S]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- Congruence of `Away.mk` in the degree witness of the base element. -/
lemma away_mk_congr_deg {f : S} {d₁ d₂ : ℕ} (p₁ : f ∈ 𝒜 d₁) (p₂ : f ∈ 𝒜 d₂) (n : ℕ) (x : S)
    (h₁ : x ∈ 𝒜 (n • d₁)) (h₂ : x ∈ 𝒜 (n • d₂)) :
    Away.mk 𝒜 p₁ n x h₁ = Away.mk 𝒜 p₂ n x h₂ := by
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, Away.val_mk]

/-- Powers of `Away.mk` for a base element of arbitrary degree. -/
lemma away_mk_pow_gen {f : S} {d : ℕ} (hf : f ∈ 𝒜 d) (k : ℕ) (a : S) (ha : a ∈ 𝒜 (k • d))
    (n : ℕ) :
    (Away.mk 𝒜 hf k a ha) ^ n =
      Away.mk 𝒜 hf (n * k) (a ^ n)
        (by simpa only [smul_eq_mul, mul_assoc] using SetLike.pow_mem_graded n ha) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact ((away_mk_congr hf (show 0 * k = 0 by simp) (show a ^ 0 = f ^ 0 by simp) _ _).trans
      (away_mk_self hf 0)).symm
  | succ n ih =>
    rw [pow_succ, ih,
      away_mk_mul hf (n * k) k (a ^ n) a
        (by simpa only [smul_eq_mul, mul_assoc] using SetLike.pow_mem_graded n ha) ha]
    refine away_mk_congr hf ?_ ?_ _ _
    · ring
    · rw [pow_succ]

/-- The generalised `away_mk_swap` of `vanishing_ideal_chart`: in `Away 𝒜 (F * G)`, with
`F ∈ 𝒜 d` and `G ∈ 𝒜 1`, the fraction `(a F^{k d})/(FG)^{k d}` equals `F^{k(d+1)}/(FG)^{k d}`
times the fraction `(a G^k)/(FG)^k`. -/
lemma away_mk_swap_gen {F G : S} {d : ℕ} (hF : F ∈ 𝒜 d) (hG : G ∈ 𝒜 1) (k : ℕ) (a : S)
    (ha : a ∈ 𝒜 (k * d)) :
    Away.mk 𝒜 (SetLike.mul_mem_graded hF hG) (k * d) (a * F ^ (k * d))
        (by
          convert SetLike.mul_mem_graded ha (SetLike.pow_mem_graded (k*d) hF) using 1
          simp only [smul_eq_mul]
          ring_nf) =
      Away.mk 𝒜 (SetLike.mul_mem_graded hF hG) (k * d) (F ^ (k * (d + 1)))
        (by
          convert SetLike.pow_mem_graded (k*(d+1)) hF using 1
          simp only [smul_eq_mul]
          ring_nf) *
      Away.mk 𝒜 (SetLike.mul_mem_graded hF hG) k (a * G ^ k)
        (by
          convert SetLike.mul_mem_graded ha (SetLike.pow_mem_graded k hG) using 1
          simp only [smul_eq_mul]
          ring_nf) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, Away.val_mk, Away.val_mk, Away.val_mk, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  rw [mul_pow]
  ring

/-- `awayMap` of `Away.mk`, in a normalisation where the degree witness is the canonical one for
`F * G ∈ 𝒜 (d + e)` (rather than the one produced by `awayMap_mk`). -/
lemma awayMap_mk_rfl {f g : S} {d e : ℕ} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e) (n : ℕ) (a : S)
    (ha : a ∈ 𝒜 (n • d)) :
    awayMap 𝒜 hg (show f * g = f * g from rfl) (Away.mk 𝒜 hf n a ha) =
      Away.mk 𝒜 (SetLike.mul_mem_graded hf hg) n (a * g ^ n)
        (by
          convert SetLike.mul_mem_graded ha (SetLike.pow_mem_graded n hg) using 1
          simp only [smul_eq_mul]
          ring_nf) := by
  simp only [HomogeneousLocalization.awayMap_mk]

/-- `awayMap` of `Away.mk` in the "other" direction (source chart `g`, extra element `f`). -/
lemma awayMap_mk_comm {f g : S} {d e : ℕ} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e) (n : ℕ) (a : S)
    (ha : a ∈ 𝒜 (n • e)) :
    awayMap 𝒜 hf (show f * g = g * f from mul_comm f g) (Away.mk 𝒜 hg n a ha) =
      Away.mk 𝒜 (SetLike.mul_mem_graded hf hg) n (a * f ^ n)
        (by
          convert SetLike.mul_mem_graded ha (SetLike.pow_mem_graded n hf) using 1
          simp only [smul_eq_mul]
          ring_nf) := by
  rw [HomogeneousLocalization.awayMap_mk]
  exact away_mk_congr_deg _ _ _ _ _ _

end Helpers

section Main

variable (A : Type*) [CommRing A] (n : ℕ) (X : Scheme)
  (i : X ⟶ AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin n) A))
  [AlgebraicGeometry.IsClosedImmersion i]

/-- `vanishing_ideal_chart` with the degree-`1` chart element `X j` replaced by an arbitrary
homogeneous element `F ∈ 𝒜 d`, `d > 0`. -/
theorem vanishing_ideal_chart_gen
    (F : MvPolynomial (Fin n) A) (d : ℕ) (hd : 0 < d)
    (hF : F ∈ MvPolynomial.homogeneousSubmodule (Fin n) A d)
    (z : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin n) A) F)
    (hz : Ideal.Quotient.mk (i.ker.ideal
        ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) A) F,
          Proj.isAffineOpen_basicOpen _ F hF hd⟩)
        ((Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin n) A) F hF hd).hom z) = 0) :
    ∃ (k : ℕ) (g : MvPolynomial (Fin n) A)
      (hg : g ∈ MvPolynomial.homogeneousSubmodule (Fin n) A (k * d)),
      (∀ j' : Fin n, Ideal.Quotient.mk (i.ker.ideal
          ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) A) (MvPolynomial.X j'),
            Proj.isAffineOpen_basicOpen _ (MvPolynomial.X j') (MvPolynomial.isHomogeneous_X A j') (by norm_num)⟩)
          ((Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin n) A) (MvPolynomial.X j')
            (MvPolynomial.isHomogeneous_X A j') (by norm_num)).hom
            (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin n) A)
              (MvPolynomial.isHomogeneous_X A j') (k * d) g (by simpa using hg))) = 0) ∧
      z = HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin n) A)
            hF k g (by simpa using hg) := by
  have hzI : (CommRingCat.Hom.hom (Proj.basicOpenIsoAway (StdGrading A n) F hF hd).hom) z ∈
      i.ker.ideal ⟨Proj.basicOpen (StdGrading A n) F,
        Proj.isAffineOpen_basicOpen (StdGrading A n) F hF hd⟩ :=
    (Ideal.Quotient.eq_zero_iff_mem).mp hz
  obtain ⟨k₀, a, ha, hzeq⟩ := HomogeneousLocalization.Away.mk_surjective (StdGrading A n) hF z
  have hmem_ha : ∀ m : ℕ, a * F ^ m ∈ (StdGrading A n) (((k₀ + m) * d) • (1:ℕ)) := by
    intro m
    rw [show ((k₀ + m) * d) • (1:ℕ) = (k₀ + m) * d from by simp only [smul_eq_mul, mul_one]]
    convert SetLike.mul_mem_graded ha (SetLike.pow_mem_graded m hF) using 1
    simp only [smul_eq_mul]
    ring_nf
  have hFd : F ∈ (StdGrading A n) (d • (1:ℕ)) := by
    simpa only [smul_eq_mul, mul_one] using hF
  have hpow_wit : ∀ k : ℕ, F ^ k ∈ (StdGrading A n) ((k * d) • (1:ℕ)) := by
    intro k
    simpa only [smul_eq_mul, mul_one, mul_assoc] using SetLike.pow_mem_graded k hFd
  -- for every chart `D₊(X j')` there is an exponent `m` with `a F^m / (X j')^{(k₀+m)d}` in the
  -- chart ideal
  have hmain : ∀ j' : Fin n, ∃ m : ℕ,
      Away.mk (StdGrading A n) (MvPolynomial.isHomogeneous_X A j') ((k₀ + m) * d) (a * F ^ m)
        (hmem_ha m) ∈
        (i.ker.ideal ⟨Proj.basicOpen (StdGrading A n) (MvPolynomial.X j'),
          Proj.isAffineOpen_basicOpen (StdGrading A n) (MvPolynomial.X j')
            (MvPolynomial.isHomogeneous_X A j') (by norm_num)⟩).comap
          (CommRingCat.Hom.hom (Proj.basicOpenIsoAway (StdGrading A n) (MvPolynomial.X j')
            (MvPolynomial.isHomogeneous_X A j') (by norm_num)).hom) := by
    intro j'
    have hG : MvPolynomial.X j' ∈ StdGrading A n 1 := MvPolynomial.isHomogeneous_X A j'
    have hx : F * MvPolynomial.X j' = MvPolynomial.X j' * F := mul_comm F (MvPolynomial.X j')
    have hFG : F * MvPolynomial.X j' ∈ StdGrading A n (d + 1) := SetLike.mul_mem_graded hF hG
    have htrans := chart_transport_gen (𝒜 := StdGrading A n) (i := i) (F := F)
      (G := MvPolynomial.X j') (d := d) (e := 1) hd (by norm_num) hF hG
    have hzmap : (awayMap (StdGrading A n) hG
          (show F * MvPolynomial.X j' = F * MvPolynomial.X j' from rfl)) z ∈
        (((i.ker.ideal ⟨Proj.basicOpen (StdGrading A n) (MvPolynomial.X j'),
            Proj.isAffineOpen_basicOpen (StdGrading A n) (MvPolynomial.X j') hG (by norm_num)⟩).comap
          (CommRingCat.Hom.hom (Proj.basicOpenIsoAway (StdGrading A n) (MvPolynomial.X j')
            hG (by norm_num)).hom)).map (awayMap (StdGrading A n) hF hx)) := by
      have h1 : (awayMap (StdGrading A n) hG
            (show F * MvPolynomial.X j' = F * MvPolynomial.X j' from rfl)) z ∈
          (((i.ker.ideal ⟨Proj.basicOpen (StdGrading A n) F,
            Proj.isAffineOpen_basicOpen (StdGrading A n) F hF hd⟩).comap
            (CommRingCat.Hom.hom (Proj.basicOpenIsoAway (StdGrading A n) F hF hd).hom)).map
            (awayMap (StdGrading A n) hG
              (show F * MvPolynomial.X j' = F * MvPolynomial.X j' from rfl))) :=
        Ideal.mem_map_of_mem _ (Ideal.mem_comap.mpr hzI)
      rwa [htrans] at h1
    have hmem_ha' : a ∈ (StdGrading A n) ((k₀ * d) • (1:ℕ)) := by
      simpa only [smul_eq_mul, mul_one] using ha
    have hswap : (awayMap (StdGrading A n) hF hx)
          (Away.mk (StdGrading A n) hG (k₀ * d) a hmem_ha') =
        Away.mk (StdGrading A n) hFG (k₀ * d) (F ^ (k₀ * (d + 1)))
          (by
            convert SetLike.pow_mem_graded (k₀ * (d+1)) hF using 1
            simp only [smul_eq_mul]
            ring_nf) *
        ((awayMap (StdGrading A n) hG
          (show F * MvPolynomial.X j' = F * MvPolynomial.X j' from rfl)) z) := by
      rw [awayMap_mk_comm hF hG (k₀ * d) a hmem_ha', ← hzeq, awayMap_mk_rfl hF hG k₀ a ha]
      exact away_mk_swap_gen hF hG k₀ a ha
    have hmem : (awayMap (StdGrading A n) hF hx)
          (Away.mk (StdGrading A n) hG (k₀ * d) a hmem_ha') ∈
        (((i.ker.ideal ⟨Proj.basicOpen (StdGrading A n) (MvPolynomial.X j'),
            Proj.isAffineOpen_basicOpen (StdGrading A n) (MvPolynomial.X j') hG (by norm_num)⟩).comap
          (CommRingCat.Hom.hom (Proj.basicOpenIsoAway (StdGrading A n) (MvPolynomial.X j')
            hG (by norm_num)).hom)).map (awayMap (StdGrading A n) hF hx)) := by
      rw [hswap]
      exact Ideal.mul_mem_left _ _ hzmap
    letI : Algebra (Away (StdGrading A n) (MvPolynomial.X j'))
        (Away (StdGrading A n) (F * MvPolynomial.X j')) :=
      (awayMap (StdGrading A n) hF hx).toAlgebra
    haveI : IsLocalization.Away (Away.isLocalizationElem hG hF)
        (Away (StdGrading A n) (F * MvPolynomial.X j')) :=
      Away.isLocalization_mul (hf := hG) (hg := hF) (hx := hx) (hd := by norm_num)
    obtain ⟨m, hm⟩ := exists_pow_mul_mem_of_algebraMap_mem_map
      (R := Away (StdGrading A n) (MvPolynomial.X j'))
      (S' := Away (StdGrading A n) (F * MvPolynomial.X j'))
      (Away.isLocalizationElem hG hF)
      (I := (i.ker.ideal ⟨Proj.basicOpen (StdGrading A n) (MvPolynomial.X j'),
        Proj.isAffineOpen_basicOpen (StdGrading A n) (MvPolynomial.X j') hG (by norm_num)⟩).comap
        (CommRingCat.Hom.hom (Proj.basicOpenIsoAway (StdGrading A n) (MvPolynomial.X j')
          hG (by norm_num)).hom))
      (v := Away.mk (StdGrading A n) hG (k₀ * d) a hmem_ha') hmem
    refine ⟨m, ?_⟩
    have ht : Away.isLocalizationElem hG hF =
        Away.mk (StdGrading A n) hG d (F ^ 1) (by simpa using hF) := rfl
    have hpow1 : (F ^ 1) ^ m ∈ (StdGrading A n) ((m * d) • (1:ℕ)) := by
      rw [pow_one]; exact hpow_wit m
    have hfin : (Away.isLocalizationElem hG hF) ^ m *
          Away.mk (StdGrading A n) hG (k₀ * d) a hmem_ha' =
        Away.mk (StdGrading A n) hG ((k₀ + m) * d) (a * F ^ m) (hmem_ha m) := by
      rw [ht, away_mk_pow_gen hG d (F ^ 1) (by simpa using hF) m,
          away_mk_mul hG (m * d) (k₀ * d) ((F ^ 1) ^ m) a hpow1 hmem_ha']
      refine away_mk_congr hG ?_ ?_ _ _
      · ring
      · rw [pow_one, mul_comm]
    rw [← hfin]
    exact hm
  choose m hm using hmain
  let M := Finset.univ.sup m
  refine ⟨k₀ + M, a * F ^ M, ?_, ?_, ?_⟩
  · simpa only [smul_eq_mul] using mem_add_smul_pow hF ha M
  · intro j'
    refine (Ideal.Quotient.eq_zero_iff_mem).mpr ?_
    rw [← Ideal.mem_comap]
    have hmle : m j' ≤ M := by
      show m j' ≤ Finset.univ.sup m
      exact Finset.le_sup (Finset.mem_univ j')
    have hG : MvPolynomial.X j' ∈ StdGrading A n 1 := MvPolynomial.isHomogeneous_X A j'
    have hpad : Away.mk (StdGrading A n) hG ((k₀ + M) * d) (a * F ^ M) (hmem_ha M) =
        Away.mk (StdGrading A n) hG ((k₀ + m j') * d) (a * F ^ (m j')) (hmem_ha (m j')) *
          (Away.mk (StdGrading A n) hG d F hFd) ^ (M - m j') := by
      rw [away_mk_pow_gen hG d F hFd (M - m j'),
          away_mk_mul hG ((k₀ + m j') * d) ((M - m j') * d) (a * F ^ (m j')) (F ^ (M - m j'))
            (hmem_ha (m j')) (hpow_wit (M - m j'))]
      refine away_mk_congr hG ?_ ?_ _ _
      · rw [← add_mul]
        congr 1
        omega
      · rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hmle]
    rw [hpad]
    exact Ideal.mul_mem_right _ _ (hm j')
  · exact hzeq.symm.trans (away_mk_pad hF k₀ M a ha)

end Main

theorem vanishing_ideal_chart_monomial (A : Type*) [CommRing A] (n : ℕ) (X : Scheme)
    (i : X ⟶ AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin n) A))
    [AlgebraicGeometry.IsClosedImmersion i] (T : Finset (Fin n)) (hT : T.Nonempty)
    (hf : (∏ k ∈ T, MvPolynomial.X k) ∈ MvPolynomial.homogeneousSubmodule (Fin n) A T.card)
    (z : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin n) A)
          (∏ k ∈ T, MvPolynomial.X k))
    (hz : Ideal.Quotient.mk (i.ker.ideal
        ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) A) (∏ k ∈ T, MvPolynomial.X k),
          Proj.isAffineOpen_basicOpen _ _ hf (Finset.card_pos.mpr hT)⟩)
        ((Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin n) A) (∏ k ∈ T, MvPolynomial.X k)
          hf (Finset.card_pos.mpr hT)).hom z) = 0) :
    ∃ (k : ℕ) (g : MvPolynomial (Fin n) A)
      (hg : g ∈ MvPolynomial.homogeneousSubmodule (Fin n) A (k * T.card)),
      (∀ j' : Fin n, Ideal.Quotient.mk (i.ker.ideal
          ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) A) (MvPolynomial.X j'),
            Proj.isAffineOpen_basicOpen _ _ (MvPolynomial.isHomogeneous_X A j') (by norm_num)⟩)
          ((Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin n) A) (MvPolynomial.X j')
            (MvPolynomial.isHomogeneous_X A j') (by norm_num)).hom
            (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin n) A)
              (MvPolynomial.isHomogeneous_X A j') (k * T.card) g (by simpa using hg))) = 0) ∧
      z = HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin n) A)
            hf k g (by simpa using hg) := by
  exact vanishing_ideal_chart_gen A n X i (∏ k ∈ T, MvPolynomial.X k) T.card
    (Finset.card_pos.mpr hT) hf z hz

end Work.DSEQP
