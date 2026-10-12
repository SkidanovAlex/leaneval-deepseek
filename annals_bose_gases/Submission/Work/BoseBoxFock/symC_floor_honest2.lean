import ChallengeDeps
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseBoxFock.KzOpC_floor_window
import Submission.Work.BoseBoxFock.KzOpC_real
import Submission.Work.BoseBoxFock.gaugeC_symC
import Submission.Work.BoseBoxFock.phi_split_toCFock
import Submission.Work.BoseBoxFock.symDiscrep
import Submission.Work.BoseBoxFock.symR_floor_gen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {m : ℕ} [NeZero m]

/-! ## 1. The gauge: pointwise form, support, isometry -/

/-- **The pointwise form of the gauge on the `Finsupp` model**: the coefficient of the
monomial `β` is multiplied by `u ^ (−(Σ β))`. -/
lemma gaugeF_apply_pt {X : Type*} [DecidableEq X] (u : ℂ) (f : (X →₀ ℕ) →₀ ℂ) (β : X →₀ ℕ) :
    (gaugeF X u f) β = u ^ (-(((β.sum fun _ k => k) : ℕ) : ℤ)) * f β := by
  induction f using Finsupp.induction_linear with
  | zero => simp [gaugeF]
  | single γ c =>
      rw [gaugeF_single]
      by_cases h : γ = β
      · subst h
        simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, one_mul,
          mul_comm]
      · rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne (Ne.symm h),
          Finsupp.single_eq_of_ne (Ne.symm h)]
        simp
  | add f g hf hg =>
      rw [map_add, Finsupp.add_apply, hf, hg, Finsupp.add_apply, mul_add]

/-- The gauge does not spread the support. -/
lemma gaugeF_support_subset {X : Type*} [DecidableEq X] (u : ℂ) (f : (X →₀ ℕ) →₀ ℂ) :
    (gaugeF X u f).support ⊆ f.support := by
  intro β hβ
  rw [Finsupp.mem_support_iff] at hβ ⊢
  intro h0
  exact hβ (by rw [gaugeF_apply_pt, h0, mul_zero])

/-- `gaugeC u` as a `toCFock`-conjugate of `gaugeF u`. -/
lemma gaugeC_toCFock {X : Type*} [DecidableEq X] (u : ℂ) (f : (X →₀ ℕ) →₀ ℂ) :
    gaugeC X u (toCFock X f) = toCFock X (gaugeF X u f) := by
  simp [gaugeC]

/-- **The gauge preserves the window degrees.**  If the coordinates of `w` are supported in
degrees `≤ K`, the same holds for `gaugeC u w`. -/
lemma degree_gaugeC_le (u : ℂ) (K : ℕ) (w : cfock (Excited m))
    (hdeg : ∀ β ∈ ((toCFock (Excited m)).symm w).support, Finsupp.degree β ≤ K) :
    ∀ β ∈ ((toCFock (Excited m)).symm (gaugeC (Excited m) u w)).support,
      Finsupp.degree β ≤ K := by
  obtain ⟨f, rfl⟩ := (toCFock (Excited m)).surjective w
  simp only [LinearEquiv.symm_apply_apply] at hdeg
  rw [gaugeC_toCFock, LinearEquiv.symm_apply_apply]
  exact fun β hβ => hdeg β (gaugeF_support_subset u f hβ)

/-- For `u` of unit modulus, `conj (u ^ n) * u ^ n = 1`. -/
lemma conj_zpow_mul_zpow {u : ℂ} (hu : u * starRingEnd ℂ u = 1) (n : ℤ) :
    (starRingEnd ℂ) (u ^ n) * u ^ n = 1 := by
  have hns : Complex.normSq u = 1 := by
    have h1 : ((Complex.normSq u : ℝ) : ℂ) = 1 := by
      rw [← Complex.mul_conj]; exact hu
    exact Complex.ofReal_inj.mp h1
  have hnorm : ‖u‖ = 1 := by
    have h := Complex.normSq_eq_norm_sq u
    rw [hns] at h
    nlinarith [norm_nonneg u]
  have h1 : (starRingEnd ℂ) (u ^ n) * u ^ n = ((Complex.normSq (u ^ n) : ℝ) : ℂ) := by
    rw [mul_comm]; exact Complex.mul_conj _
  rw [h1, Complex.normSq_eq_norm_sq, norm_zpow, hnorm, one_zpow]
  norm_num

/-- **The gauge is isometric** (`gaugeC u` is diagonal in the occupation basis with entries
of modulus one whenever `u * conj u = 1`). -/
theorem gaugeC_inner_iso (u : ℂ) (hu : u * starRingEnd ℂ u = 1)
    (v w : cfock (Excited m)) :
    inner ℂ (gaugeC (Excited m) u v) (gaugeC (Excited m) u w) = inner ℂ v w := by
  obtain ⟨f, rfl⟩ := (toCFock (Excited m)).surjective v
  obtain ⟨g, rfl⟩ := (toCFock (Excited m)).surjective w
  rw [gaugeC_toCFock, gaugeC_toCFock, inner_toCFock, inner_toCFock]
  rw [Finset.sum_subset (gaugeF_support_subset u f)
      (fun α _ hα => by rw [Finsupp.notMem_support_iff.mp hα]; simp)]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [gaugeF_apply_pt, gaugeF_apply_pt, map_mul]
  have h := conj_zpow_mul_zpow hu (-(((β.sum fun _ k => k) : ℕ) : ℤ))
  calc (starRingEnd ℂ) (u ^ (-(((β.sum fun _ k => k) : ℕ) : ℤ))) * (starRingEnd ℂ) (f β)
        * (u ^ (-(((β.sum fun _ k => k) : ℕ) : ℤ)) * g β)
      = (starRingEnd ℂ) (f β) * g β
        * ((starRingEnd ℂ) (u ^ (-(((β.sum fun _ k => k) : ℕ) : ℤ)))
            * u ^ (-(((β.sum fun _ k => k) : ℕ) : ℤ))) := by ring
    _ = (starRingEnd ℂ) (f β) * g β := by rw [h, mul_one]

/-! ## 2. The gauge commutes with the number operators -/

/-- `u * conj u = 1` forces `u ≠ 0`. -/
lemma ne_zero_of_mul_conj {u : ℂ} (hu : u * starRingEnd ℂ u = 1) : u ≠ 0 := by
  intro h
  rw [h, zero_mul] at hu
  exact zero_ne_one hu

/-- **The gauge commutes with the excited number `n₊`.** -/
theorem gaugeC_nPlusC (u : ℂ) (hu : u * starRingEnd ℂ u = 1) :
    ∀ w : cfock (Excited m),
      gaugeC (Excited m) u (nPlusC (m := m) w) = nPlusC (m := m) (gaugeC (Excited m) u w) := by
  have hu0 := ne_zero_of_mul_conj hu
  have h := gaugeWt_finset_smul (X := Excited m) (Finset.univ : Finset (Excited m))
    (fun _ : Excited m => (1 : ℂ))
    (fun l : Excited m => (creC (Excited m) l).comp (annC (Excited m) l))
    (fun l _ => gaugeWt_comp hu0 (gaugeWt_creC u hu0 l) (gaugeWt_annC u hu0 l))
  intro w
  simpa [nPlusC, GaugeWt, Finset.sum_apply] using h w

/-- **The gauge commutes with the χ-number `n₊^χ`.** -/
theorem gaugeC_nPlusChi {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (u : ℂ) (hu : u * starRingEnd ℂ u = 1) (f : Mode → Fin m → ℝ) :
    ∀ w : cfock (Excited m),
      gaugeC (Excited m) u (nPlusChi (m := m) f w)
        = nPlusChi (m := m) f (gaugeC (Excited m) u w) := by
  have hu0 := ne_zero_of_mul_conj hu
  have h := gaugeWt_finset_smul (X := Excited m) (Finset.univ : Finset Mode)
    (fun _ : Mode => (1 : ℂ))
    (fun k : Mode => nOpC (f k))
    (fun k _ => by
      have h1 : nOpC (f k) = (creOfE (f k)).comp (annOfE (f k)) := rfl
      rw [h1]
      exact gaugeWt_comp hu0 (gaugeWt_creOfE hu0 (f k)) (gaugeWt_annOfE hu0 (f k)))
  intro w
  simpa [nPlusChi, GaugeWt] using h w

/-! ## 3. The excited number as the degree-weighted ℓ²-form -/

/-- **`n₊` in coordinates**: for a spectator vector whose coordinates are supported in
degrees `≤ K`, the quadratic form of `n₊` is at most `K` times the squared norm. -/
lemma inner_nPlusC_toCFock_le (K : ℕ) (f : (Excited m →₀ ℕ) →₀ ℂ)
    (hdeg : ∀ β ∈ f.support, Finsupp.degree β ≤ K) :
    (inner ℂ (toCFock (Excited m) f) (nPlusC (m := m) (toCFock (Excited m) f))).re
      ≤ (K : ℝ) * ‖toCFock (Excited m) f‖ ^ 2 := by
  have hkey : ∀ β : Excited m →₀ ℕ,
      (f.sum (fun β' c' => ((((Finsupp.degree β' : ℕ) : ℝ)) : ℂ) • Finsupp.single β' c')) β
        = ((((Finsupp.degree β : ℕ) : ℝ)) : ℂ) * f β :=
    fun β => NWindowLift.sum_smul_single_apply _ f β
  have hcongr : (∑ α ∈ f.support, (starRingEnd ℂ) (f α) *
        (f.sum (fun β' c' => ((((Finsupp.degree β' : ℕ) : ℝ)) : ℂ) • Finsupp.single β' c')) α)
      = ∑ β ∈ f.support, (starRingEnd ℂ) (f β)
          * (((((Finsupp.degree β : ℕ) : ℝ)) : ℂ) * f β) :=
    Finset.sum_congr rfl fun β _ => by rw [hkey]
  rw [nPlusC_toCFock, inner_toCFock, hcongr, normSq_toCFock, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun β hβ => ?_
  have hterm : ((starRingEnd ℂ) (f β) * (((((Finsupp.degree β : ℕ) : ℝ)) : ℂ) * f β)).re
      = ((Finsupp.degree β : ℕ) : ℝ) * ((f β).re ^ 2 + (f β).im ^ 2) := by
    have h2 : (starRingEnd ℂ) (f β) * (((((Finsupp.degree β : ℕ) : ℝ)) : ℂ) * f β)
        = (((((Finsupp.degree β : ℕ) : ℝ) * Complex.normSq (f β) : ℝ)) : ℂ) := by
      have h1 : (starRingEnd ℂ) (f β) * (f β) = ((Complex.normSq (f β) : ℝ) : ℂ) := by
        rw [mul_comm]; exact Complex.mul_conj _
      push_cast
      rw [← h1]
      ring
    rw [h2, Complex.ofReal_re, Complex.normSq_apply]
    ring
  rw [hterm]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdeg β hβ) (by positivity)


/-! ## 4. From a support-degree bound to the algebraic window decomposition -/

/-- The degree-`j` part of the spectator coordinates is an `n₊`-eigenvector of eigenvalue
`j` (the `Finsupp`-model form of `n₊` being the total degree). -/
lemma nPlusC_filter_eigen (j : ℕ) (f : (Excited m →₀ ℕ) →₀ ℂ) :
    nPlusC (m := m) (toCFock (Excited m) (f.filter (fun β => Finsupp.degree β = j)))
      = (j : ℝ) • toCFock (Excited m) (f.filter (fun β => Finsupp.degree β = j)) := by
  set g : (Excited m →₀ ℕ) →₀ ℂ := f.filter (fun β => Finsupp.degree β = j) with hg
  have hkey : g.sum (fun β c => ((((Finsupp.degree β : ℕ) : ℝ)) : ℂ) • Finsupp.single β c)
      = (((j : ℝ)) : ℂ) • g := by
    ext β
    rw [NWindowLift.sum_smul_single_apply, Finsupp.smul_apply, smul_eq_mul, hg,
      Finsupp.filter_apply]
    by_cases hβ : Finsupp.degree β = j
    · rw [hβ]
    · rw [if_neg hβ]; ring
  rw [nPlusC_toCFock, hkey, map_smul]
  exact Complex.coe_smul (j : ℝ) (toCFock (Excited m) g)

/-- **A support-degree bound gives FS's window decomposition.**  If the coordinates of `x`
are supported in degrees `≤ ⌊M⌋₊`, the graded pieces of the coordinates form an
`n₊`-eigenvector decomposition of `x` with eigenvalues `j ≤ ⌊M⌋₊`. -/
lemma eigen_decomp_of_degree (M : ℝ) (x : cfock (Excited m))
    (hdeg : ∀ β ∈ ((toCFock (Excited m)).symm x).support, Finsupp.degree β ≤ ⌊M⌋₊) :
    ∃ φ : ℕ → cfock (Excited m),
      (∀ j : ℕ, nPlusC (m := m) (φ j) = (j : ℝ) • φ j)
        ∧ x = ∑ j ∈ Finset.range (⌊M⌋₊ + 1), φ j := by
  refine ⟨fun j => toCFock (Excited m) (((toCFock (Excited m)).symm x).filter
      (fun β => Finsupp.degree β = j)), fun j => nPlusC_filter_eigen j _, ?_⟩
  have hsum : ((toCFock (Excited m)).symm x)
      = ∑ j ∈ Finset.range (⌊M⌋₊ + 1),
          ((toCFock (Excited m)).symm x).filter (fun β => Finsupp.degree β = j) := by
    ext β
    rw [Finsupp.finsetSum_apply]
    simp only [Finsupp.filter_apply]
    rw [Finset.sum_ite_eq]
    by_cases hmem : Finsupp.degree β ∈ Finset.range (⌊M⌋₊ + 1)
    · rw [if_pos hmem]
    · rw [if_neg hmem]
      by_contra hf
      have hge : ⌊M⌋₊ + 1 ≤ Finsupp.degree β := by
        rw [Finset.mem_range] at hmem; omega
      have h1 : Finsupp.degree β ≤ ⌊M⌋₊ := hdeg β (Finsupp.mem_support_iff.mpr hf)
      omega
  have hcon := congrArg (toCFock (Excited m)) hsum
  simpa [map_sum] using hcon

/-! ## 5. The real/imaginary split of the `KzOpC` quadratic form -/

/-- `BNHHon` is a real operator. -/
lemma isRealMap_BNHHon (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    IsRealMap (BNHHon v h fc fu HM μ) := by
  unfold BNHHon
  refine IsRealMap.smul_real (by norm_num : ((1 / 32 : ℂ)).im = 0) ?_
  refine IsRealMap.sum _ _ (fun k _ => ?_)
  exact IsRealMap.ofReal_smul (isRealMap_nOpC ((HM μ).f k))

/-- **The real/imaginary split of a window vector for `KzOpC`.**  Explicitly,
`x` and `y` are the vectors whose coordinates are the real and the imaginary parts of the
coordinates of `w`. -/
lemma KzOpC_split_re_im (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) (μ ρ : ℝ) (K : ℕ)
    (w : cfock (Excited (HM μ).m))
    (hdeg : ∀ β ∈ ((toCFock (Excited (HM μ).m)).symm w).support,
      Finsupp.degree β ≤ K) :
    ∃ x y : cfock (Excited (HM μ).m),
      (∀ β : Excited (HM μ).m →₀ ℕ,
          ((toCFock (Excited (HM μ).m)).symm x β).im = 0)
      ∧ (∀ β : Excited (HM μ).m →₀ ℕ,
          ((toCFock (Excited (HM μ).m)).symm y β).im = 0)
      ∧ (∀ β ∈ ((toCFock (Excited (HM μ).m)).symm x).support, Finsupp.degree β ≤ K)
      ∧ (∀ β ∈ ((toCFock (Excited (HM μ).m)).symm y).support, Finsupp.degree β ≤ K)
      ∧ w = x + Complex.I • y
      ∧ ‖w‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2
      ∧ (inner ℂ w (KzOpC (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
            (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).E
            (8 * Real.pi * BoseGases.a v) ρ w)).re
          = (inner ℂ x (KzOpC (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
                (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).E
                (8 * Real.pi * BoseGases.a v) ρ x)).re
            + (inner ℂ y (KzOpC (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
                (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).E
                (8 * Real.pi * BoseGases.a v) ρ y)).re := by
  set f : (Excited (HM μ).m →₀ ℕ) →₀ ℂ := (toCFock (Excited (HM μ).m)).symm w with hf
  set zr : (Excited (HM μ).m →₀ ℕ) →₀ ℂ :=
    f.mapRange (fun z : ℂ => (((z.re : ℝ)) : ℂ)) (by simp) with hzr
  set zi : (Excited (HM μ).m →₀ ℕ) →₀ ℂ :=
    f.mapRange (fun z : ℂ => (((z.im : ℝ)) : ℂ)) (by simp) with hzi
  have hzr_apply : ∀ β, zr β = (((f β).re : ℝ) : ℂ) := fun β => by
    rw [hzr, Finsupp.mapRange_apply]
  have hzi_apply : ∀ β, zi β = (((f β).im : ℝ) : ℂ) := fun β => by
    rw [hzi, Finsupp.mapRange_apply]
  have hzr_supp : zr.support ⊆ f.support := by
    intro β hβ
    rw [Finsupp.mem_support_iff] at hβ ⊢
    intro h0
    exact hβ (by rw [hzr_apply, h0]; simp)
  have hzi_supp : zi.support ⊆ f.support := by
    intro β hβ
    rw [Finsupp.mem_support_iff] at hβ ⊢
    intro h0
    exact hβ (by rw [hzi_apply, h0]; simp)
  have hwf : w = toCFock (Excited (HM μ).m) f := by
    rw [hf]
    exact (LinearEquiv.apply_symm_apply (toCFock (Excited (HM μ).m)) w).symm
  have hzr_re : ∀ β, (zr β).re = (f β).re := fun β => by
    rw [hzr_apply, Complex.ofReal_re]
  have hzi_re : ∀ β, (zi β).re = (f β).im := fun β => by
    rw [hzi_apply, Complex.ofReal_re]
  have hzr_im : ∀ β, (zr β).im = 0 := fun β => by
    rw [hzr_apply, Complex.ofReal_im]
  have hzi_im : ∀ β, (zi β).im = 0 := fun β => by
    rw [hzi_apply, Complex.ofReal_im]
  refine ⟨toCFock (Excited (HM μ).m) zr, toCFock (Excited (HM μ).m) zi,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro β
    rw [LinearEquiv.symm_apply_apply, hzr_apply]
    simp
  · intro β
    rw [LinearEquiv.symm_apply_apply, hzi_apply]
    simp
  · intro β hβ
    rw [LinearEquiv.symm_apply_apply] at hβ
    exact hdeg β (hzr_supp hβ)
  · intro β hβ
    rw [LinearEquiv.symm_apply_apply] at hβ
    exact hdeg β (hzi_supp hβ)
  · rw [hwf]
    have hcoord : f = zr + Complex.I • zi := by
      ext β
      rw [Finsupp.add_apply, Finsupp.smul_apply, hzr_apply, hzi_apply, smul_eq_mul]
      exact (Complex.re_add_im (f β)).symm.trans (by ring)
    rw [hcoord, map_add, map_smul]
  · rw [hwf, normSq_toCFock_sum f f.support (Finset.Subset.refl _),
      normSq_toCFock_sum zr f.support hzr_supp, normSq_toCFock_sum zi f.support hzi_supp,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [hzr_re, hzi_re, hzr_im, hzi_im]
    ring
  · have hA : IsRealMap (KzOpC (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
        (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).E
        (8 * Real.pi * BoseGases.a v) ρ) :=
      KzOpC_real _ _ _ _ _ _ _ (isRealMap_BNHHon v h fc fu HM μ)
    rw [hwf, quadForm_re_expansion _ hA f f.support (Finset.Subset.refl _),
      quadForm_re_expansion _ hA zr f.support hzr_supp,
      quadForm_re_expansion _ hA zi f.support hzi_supp,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    simp only [hzr_re, hzi_re, hzr_im, hzi_im]
    ring

/-! ## 6. Gauge weights of the honest spectator words -/

/-- `nOpC φ = creOfE φ ∘ annOfE φ` has gauge weight `0`. -/
lemma gaugeWt_nOpC (u : ℂ) (hu : u ≠ 0) (φ : Fin m → ℝ) : GaugeWt u (nOpC φ) 0 := by
  have h1 : nOpC φ = (creOfE φ).comp (annOfE φ) := rfl
  rw [h1]
  exact gaugeWt_comp hu (gaugeWt_creOfE hu φ) (gaugeWt_annOfE hu φ)

/-- `BNHHon` is gauge-invariant (it is a weighted sum of the `nOpC`'s). -/
lemma gaugeC_BNHHon (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (u : ℂ) (hu : u * starRingEnd ℂ u = 1) :
    ∀ w : cfock (Excited (HM μ).m),
      gaugeC (Excited (HM μ).m) u (BNHHon v h fc fu HM μ w)
        = BNHHon v h fc fu HM μ (gaugeC (Excited (HM μ).m) u w) := by
  have hu0 := ne_zero_of_mul_conj hu
  have hwt : GaugeWt u (BNHHon v h fc fu HM μ) 0 := by
    unfold BNHHon
    exact gaugeWt_smul (gaugeWt_finset_smul _ _ _
      (fun k _ => gaugeWt_nOpC u hu0 ((HM μ).f k))) _
  intro w
  have h := hwt w
  simpa [GaugeWt] using h


theorem symC_floor_honest2 (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    (μ C Kw : ℝ) (hμ : 0 < μ) (hC : 0 ≤ C) (hKw : 0 ≤ Kw)
    (hM0 : 0 ≤ Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
    (henv : Work.BoseBoxFock.EnvFactsAt v h fc fu HM μ C)
    (hWω : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
      |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega k| ≤ Kw)
    (hχb : (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChiSq s ^ 2) ≤ 48 / Real.pi)
    (hχ2 : (∑ k : Work.BoseBoxFock.Lab (HM μ).N,
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChi k ^ 2) ≤ 1)
    (hBes : ∀ x : Work.BoseB4.cfock (Work.BoseB4.Excited (HM μ).m),
        (inner ℂ x (Work.BoseBoxFock.nPlusChi (m := (HM μ).m) (HM μ).f x)).re
          ≤ (48 / Real.pi) * (inner ℂ x (Work.BoseBoxFock.nPlusC (m := (HM μ).m) x)).re)
    (n : ℕ) (hn : (n : ℝ) ≤ 2 * μ * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.ell ^ 3)
    (Ψ : Work.BoseB4.RealFock (HM μ).m)
    (hWin : Work.BoseBoxFock.ExcWindow
      (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ) n Ψ) :
    ∀ z : ℂ,
      ((⨅ (ρ : {ρ : ℝ // 0 ≤ ρ}),
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).valFS ρ.1)
          - (4 * Work.BoseBoxFock.cHCF (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                (8 * Real.pi * BoseGases.a v) * ‖z‖ ^ 2
             + 4 * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
                 * (|(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 0|
                     * Real.sqrt ((48 / Real.pi) * (Work.BoseBox.bigM
                         (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ))
                   + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega0
                     * Real.sqrt ((48 / Real.pi) * (Work.BoseBox.bigM
                         (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)))
                 * ‖z‖
             + (|2 * Work.BoseBoxFock.cHCF (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                     (8 * Real.pi * BoseGases.a v) + μ * (8 * Real.pi * BoseGases.a v)|
                 + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
                   * (2 * C * BoseGases.a v
                       + |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 0
                           + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega0|)
                   * ((48 / Real.pi) * (Work.BoseBox.bigM
                       (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)))))
        * ‖Work.BoseB4.Phi (Work.BoseB4.split Ψ) z‖ ^ 2
      ≤ (∑ i ∈ Finset.range 25,
          z ^ (Work.BoseBoxFock.pvecF i) * (starRingEnd ℂ z) ^ (Work.BoseBoxFock.qvecF i) *
            inner ℂ (Work.BoseB4.Phi (Work.BoseB4.split Ψ) z)
              (Work.BoseBoxFock.KvecHon v h fc fu HM μ i
                (Work.BoseB4.Phi (Work.BoseB4.split Ψ) z))).re := by
  intro z
  let u : ℂ := if z = 0 then 1 else z / ((‖z‖ : ℝ) : ℂ)
  have hudef : u = if z = 0 then 1 else z / ((‖z‖ : ℝ) : ℂ) := rfl
  have hzu : z = ((‖z‖ : ℝ) : ℂ) * u := by
    rw [hudef]
    by_cases hz : z = 0
    · rw [if_pos hz, hz, norm_zero, Complex.ofReal_zero, zero_mul]
    · rw [if_neg hz]
      have h0 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by
        simpa [Complex.ofReal_eq_zero] using norm_ne_zero_iff.mpr hz
      rw [← mul_div_assoc, mul_div_cancel_left₀ z h0]
  have hu : u * starRingEnd ℂ u = 1 := by
    rw [hudef]
    by_cases hz : z = 0
    · rw [if_pos hz]; simp
    · rw [if_neg hz]
      have hns : Complex.normSq (z / ((‖z‖ : ℝ) : ℂ)) = 1 := by
        rw [Complex.normSq_div, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq]
        field_simp
      rw [Complex.mul_conj, hns, Complex.ofReal_one]
  have henv0 := henv
  obtain ⟨hell, hell_eq, hmu_eq, -, -, -, hW1le, hWωle, hω0, -, hωval, hcH, hW1par, hWωpar,
    hτpar, hχpar⟩ := henv0
  obtain ⟨f, hf, hfdeg⟩ := phi_split_toCFock (m := (HM μ).m) hWin z
  have hdegvz : ∀ β ∈ ((toCFock (Excited (HM μ).m)).symm (Phi (split Ψ) z)).support,
      Finsupp.degree β ≤ ⌊Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v))
        (BoseGases.a v) μ⌋₊ := by
    intro β hβ
    rw [hf] at hβ
    simp only [LinearEquiv.symm_apply_apply] at hβ
    exact hfdeg β hβ
  have hKvz : (inner ℂ (Phi (split Ψ) z)
        (nPlusC (m := (HM μ).m) (Phi (split Ψ) z))).re
      ≤ Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ
        * ‖Phi (split Ψ) z‖ ^ 2 := by
    have h2 := inner_nPlusC_toCFock_le (m := (HM μ).m)
      ⌊Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ⌋₊ f hfdeg
    rw [← hf] at h2
    exact le_trans h2 (mul_le_mul_of_nonneg_right (Nat.floor_le hM0) (sq_nonneg _))
  let w : cfock (Excited (HM μ).m) := gaugeC (Excited (HM μ).m) u (Phi (split Ψ) z)
  have hwdef : w = gaugeC (Excited (HM μ).m) u (Phi (split Ψ) z) := rfl
  have hdegw : ∀ β ∈ ((toCFock (Excited (HM μ).m)).symm w).support,
      Finsupp.degree β ≤ ⌊Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v))
        (BoseGases.a v) μ⌋₊ :=
    degree_gaugeC_le u _ (Phi (split Ψ) z) hdegvz
  have hwnorm : ‖w‖ ^ 2 = ‖Phi (split Ψ) z‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ) w,
      norm_sq_eq_re_inner (𝕜 := ℂ) (Phi (split Ψ) z)]
    exact congrArg Complex.re (gaugeC_inner_iso u hu (Phi (split Ψ) z) (Phi (split Ψ) z))
  have hKplus : (inner ℂ w (nPlusC (m := (HM μ).m) w)).re
      ≤ Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ
        * ‖w‖ ^ 2 := by
    have hgap : (inner ℂ w (nPlusC (m := (HM μ).m) w)).re
        = (inner ℂ (Phi (split Ψ) z)
            (nPlusC (m := (HM μ).m) (Phi (split Ψ) z))).re := by
      rw [hwdef, ← gaugeC_nPlusC (m := (HM μ).m) u hu (Phi (split Ψ) z)]
      exact congrArg Complex.re (gaugeC_inner_iso u hu (Phi (split Ψ) z)
        (nPlusC (m := (HM μ).m) (Phi (split Ψ) z)))
    rw [hgap, hwnorm]
    exact hKvz
  have hKc : (inner ℂ w (nPlusChi (m := (HM μ).m) (HM μ).f w)).re
      ≤ ((48 / Real.pi) * Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v))
          (BoseGases.a v) μ) * ‖w‖ ^ 2 := by
    have h1 := hBes w
    have h2 : (48 / Real.pi) * (inner ℂ w (nPlusC (m := (HM μ).m) w)).re
        ≤ (48 / Real.pi) * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v))
            (BoseGases.a v) μ * ‖w‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hKplus (by positivity)
    refine le_trans h1 ?_
    rw [mul_assoc]
    exact h2
  have hsym : (inner ℂ (Phi (split Ψ) z)
        (symC (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
          ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
          (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) z (Phi (split Ψ) z))).re
      = (inner ℂ w (symR (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
          ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
          (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) ‖z‖ w)).re := by
    have h1 : gaugeC (Excited (HM μ).m) u
        (symC (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
          ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
          (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v)
          (((‖z‖ : ℝ) : ℂ) * u) (Phi (split Ψ) z))
        = symR (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
          ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
          (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) ‖z‖
          (gaugeC (Excited (HM μ).m) u (Phi (split Ψ) z)) :=
      gaugeC_symC _ _ _ _ _ _ _ u hu (gaugeC_BNHHon v h fc fu HM μ u hu) _
    rw [← hzu] at h1
    rw [hwdef, ← h1]
    exact congrArg Complex.re (gaugeC_inner_iso u hu (Phi (split Ψ) z)
      (symC (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
        ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
        (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) z
        (Phi (split Ψ) z))).symm
  have hsum : (inner ℂ (Phi (split Ψ) z)
        (symC (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
          ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
          (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) z (Phi (split Ψ) z))).re
      = (∑ i ∈ Finset.range 25, z ^ (pvecF i) * (starRingEnd ℂ z) ^ (qvecF i) *
          inner ℂ (Phi (split Ψ) z)
            (KvecHon v h fc fu HM μ i (Phi (split Ψ) z))).re := by
    congr 1
    simp only [symC, KvecHon]
    rw [LinearMap.sum_apply, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply, inner_smul_right]
  have hρ : 0 ≤ ‖z‖ ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3 :=
    div_nonneg (sq_nonneg _) (pow_nonneg (le_of_lt hell) 3)
  obtain ⟨x, y, hxre, hyre, hxdeg, hydeg, hwxy, hwnormxy, hquad⟩ :=
    KzOpC_split_re_im v h fc fu HM μ
      (‖z‖ ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3)
      ⌊Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ⌋₊
      w hdegw
  have hdecx := eigen_decomp_of_degree (HonestBoxFam v h fc fu HM μ).E.bigM x hxdeg
  have hdecy := eigen_decomp_of_degree (HonestBoxFam v h fc fu HM μ).E.bigM y hydeg
  have hflx : (⨅ (ρ' : {ρ : ℝ // 0 ≤ ρ}),
        (HonestBoxFam v h fc fu HM μ).valFS ρ'.1) * ‖x‖ ^ 2
      ≤ (inner ℂ x (KzOpC (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
          (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).E
          (8 * Real.pi * BoseGases.a v)
          (‖z‖ ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3) x)).re :=
    KzOpC_floor_window v h hv hvrad hR hv_supp hav fc fu HM μ C Kw (48 / Real.pi)
      (‖z‖ ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3) hμ hC hρ hKw (by positivity)
      henv hWω hχb x hxre hdecx
  have hfly : (⨅ (ρ' : {ρ : ℝ // 0 ≤ ρ}),
        (HonestBoxFam v h fc fu HM μ).valFS ρ'.1) * ‖y‖ ^ 2
      ≤ (inner ℂ y (KzOpC (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
          (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).E
          (8 * Real.pi * BoseGases.a v)
          (‖z‖ ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3) y)).re :=
    KzOpC_floor_window v h hv hvrad hR hv_supp hav fc fu HM μ C Kw (48 / Real.pi)
      (‖z‖ ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3) hμ hC hρ hKw (by positivity)
      henv hWω hχb y hyre hdecy
  have hfloor : (⨅ (ρ' : {ρ : ℝ // 0 ≤ ρ}),
        (HonestBoxFam v h fc fu HM μ).valFS ρ'.1) * ‖w‖ ^ 2
      ≤ (inner ℂ w (KzOpC (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
          (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).E
          (8 * Real.pi * BoseGases.a v)
          (‖z‖ ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3) w)).re := by
    rw [hwnormxy, hquad]
    linarith [hflx, hfly]
  have hWsup : ∀ k : Lab (HM μ).N,
      |(HonestBoxFam v h fc fu HM μ).E.W1 k + (HonestBoxFam v h fc fu HM μ).E.W1omega k|
        ≤ 2 * C * BoseGases.a v := by
    intro k
    calc |(HonestBoxFam v h fc fu HM μ).E.W1 k + (HonestBoxFam v h fc fu HM μ).E.W1omega k|
        ≤ |(HonestBoxFam v h fc fu HM μ).E.W1 k|
          + |(HonestBoxFam v h fc fu HM μ).E.W1omega k| := abs_add_le _ _
      _ ≤ C * BoseGases.a v + C * BoseGases.a v := add_le_add (hW1le k) (hWωle k)
      _ = 2 * C * BoseGases.a v := by ring
  have hdisc : ∀ r : ℝ, 0 ≤ r →
      symR (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
          ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
          (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) r
        - KzOpC (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
          (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).E
          (8 * Real.pi * BoseGases.a v) (r ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3)
      = ((r ^ 2 : ℝ) : ℂ) • D2F (HM μ).f (HonestBoxFam v h fc fu HM μ).E
          (8 * Real.pi * BoseGases.a v)
        + ((r : ℝ) : ℂ) • D1F (HM μ).f (HM μ).g (HonestBoxFam v h fc fu HM μ).E
        + D0F (HM μ).f (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) :=
    fun r hr => symDiscrep (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
      ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
      (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).E
      (8 * Real.pi * BoseGases.a v) hell rfl hτpar hχpar hW1par hWωpar hωval r hr
  have hSym := symR_floor_gen (f := (HM μ).f) (g := (HM μ).g) (BNH := BNHHon v h fc fu HM μ)
    (PHs := (HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
    (F := (HonestBoxFam v h fc fu HM μ).F) (E := (HonestBoxFam v h fc fu HM μ).E)
    (gHat0 := 8 * Real.pi * BoseGases.a v) (hℓ := hell) (hPH := rfl) (hcH := hcH)
    (hω0 := hω0) (hφ := (HM μ).hf0)
    (hgonb := fun s hs t ht => (HM μ).hg s t (Finset.mem_erase.mp hs).1
      (Finset.mem_erase.mp ht).1)
    (hdisc := hdisc)
    (K := Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
    (Kc := (48 / Real.pi) * Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v))
      (BoseGases.a v) μ)
    (Kχb := 48 / Real.pi) (Wsup := 2 * C * BoseGases.a v) (hK0 := hM0)
    (hKc0 := mul_nonneg (by positivity) hM0) (hKχb0 := by positivity) (hWsup := hWsup)
    (hχ2 := hχ2) (hχ2b := hχb)
  have hSymr := hSym ‖z‖ (norm_nonneg z) w hKc hKplus
  have hsplit : (inner ℂ w (symR (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
        ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
        (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) ‖z‖ w)).re
      = (inner ℂ w (KzOpC (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
            (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).E
            (8 * Real.pi * BoseGases.a v)
            (‖z‖ ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3) w)).re
        + (inner ℂ w (((symR (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
              ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
              (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) ‖z‖)
            - KzOpC (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
              (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).E
              (8 * Real.pi * BoseGases.a v)
              (‖z‖ ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3)) w)).re := by
    have h2 : symR (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
          ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
          (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) ‖z‖ w
        = KzOpC (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
            (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).E
            (8 * Real.pi * BoseGases.a v)
            (‖z‖ ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3) w
          + ((symR (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
                ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
                (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) ‖z‖
              - KzOpC (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
                (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).E
                (8 * Real.pi * BoseGases.a v)
                (‖z‖ ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3)) w) := by
      rw [LinearMap.sub_apply]
      abel
    rw [h2, inner_add_right, Complex.add_re]
  have hforms :
      4 * Work.BoseBoxFock.cHCF (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
            (8 * Real.pi * BoseGases.a v) * ‖z‖ ^ 2
          + 4 * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
              * (|(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 0|
                  * Real.sqrt ((48 / Real.pi) * (Work.BoseBox.bigM
                      (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ))
                + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega0
                  * Real.sqrt ((48 / Real.pi) * (Work.BoseBox.bigM
                      (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)))
              * ‖z‖
          + (|2 * Work.BoseBoxFock.cHCF (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                    (8 * Real.pi * BoseGases.a v)
                + μ * (8 * Real.pi * BoseGases.a v)|
              + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
                * (2 * C * BoseGases.a v
                    + |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 0
                        + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega0|)
                * ((48 / Real.pi) * (Work.BoseBox.bigM
                    (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)))
      = 4 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) * ‖z‖ ^ 2
          + 4 * i3F (HonestBoxFam v h fc fu HM μ).E
              * (|(HonestBoxFam v h fc fu HM μ).E.W1 0|
                  * Real.sqrt ((48 / Real.pi) * (Work.BoseBox.bigM
                      (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ))
                + (HonestBoxFam v h fc fu HM μ).E.W1omega0
                  * Real.sqrt ((48 / Real.pi) * (Work.BoseBox.bigM
                      (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)))
              * ‖z‖
          + (|2 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v)
                + (HonestBoxFam v h fc fu HM μ).E.mu * (8 * Real.pi * BoseGases.a v)|
              + i3F (HonestBoxFam v h fc fu HM μ).E
                * (2 * C * BoseGases.a v
                    + |(HonestBoxFam v h fc fu HM μ).E.W1 0
                        + (HonestBoxFam v h fc fu HM μ).E.W1omega0|)
                * ((48 / Real.pi) * (Work.BoseBox.bigM
                    (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ))) := by
    rw [show i3F (HonestBoxFam v h fc fu HM μ).E
        = (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ)) from rfl, hmu_eq]
  have hkey : ((⨅ (ρ' : {ρ : ℝ // 0 ≤ ρ}),
        (HonestBoxFam v h fc fu HM μ).valFS ρ'.1) - (4 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) * ‖z‖ ^ 2
          + 4 * (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
              * (|(HonestBoxFam v h fc fu HM μ).E.W1 0|
                  * Real.sqrt ((48 / Real.pi) * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ))
                + (HonestBoxFam v h fc fu HM μ).E.W1omega0
                  * Real.sqrt ((48 / Real.pi) * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)))
              * ‖z‖
          + (|2 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v)
                + μ * (8 * Real.pi * BoseGases.a v)|
              + (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
                * (2 * C * BoseGases.a v
                    + |(HonestBoxFam v h fc fu HM μ).E.W1 0
                        + (HonestBoxFam v h fc fu HM μ).E.W1omega0|)
                * ((48 / Real.pi) * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ))))) * ‖w‖ ^ 2
      ≤ (inner ℂ w (symR (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
          ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
          (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) ‖z‖ w)).re := by
    rw [hsplit]
    have h2 : -((4 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) * ‖z‖ ^ 2
          + 4 * (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
              * (|(HonestBoxFam v h fc fu HM μ).E.W1 0|
                  * Real.sqrt ((48 / Real.pi) * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ))
                + (HonestBoxFam v h fc fu HM μ).E.W1omega0
                  * Real.sqrt ((48 / Real.pi) * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)))
              * ‖z‖
          + (|2 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v)
                + μ * (8 * Real.pi * BoseGases.a v)|
              + (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
                * (2 * C * BoseGases.a v
                    + |(HonestBoxFam v h fc fu HM μ).E.W1 0
                        + (HonestBoxFam v h fc fu HM μ).E.W1omega0|)
                * ((48 / Real.pi) * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ))))) * ‖w‖ ^ 2 ≤ (inner ℂ w (((symR (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
            ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
            (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) ‖z‖)
          - KzOpC (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
            (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).E
            (8 * Real.pi * BoseGases.a v)
            (‖z‖ ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3)) w)).re := by
      have h1 := hSymr
      dsimp only [Work.BoseBoxFock.i3F] at h1
      rw [hmu_eq] at h1
      exact h1
    have hsum2 := add_le_add hfloor h2
    have hL : ((⨅ (ρ' : {ρ : ℝ // 0 ≤ ρ}),
        (HonestBoxFam v h fc fu HM μ).valFS ρ'.1) - (4 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) * ‖z‖ ^ 2
          + 4 * (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
              * (|(HonestBoxFam v h fc fu HM μ).E.W1 0|
                  * Real.sqrt ((48 / Real.pi) * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ))
                + (HonestBoxFam v h fc fu HM μ).E.W1omega0
                  * Real.sqrt ((48 / Real.pi) * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)))
              * ‖z‖
          + (|2 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v)
                + μ * (8 * Real.pi * BoseGases.a v)|
              + (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
                * (2 * C * BoseGases.a v
                    + |(HonestBoxFam v h fc fu HM μ).E.W1 0
                        + (HonestBoxFam v h fc fu HM μ).E.W1omega0|)
                * ((48 / Real.pi) * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ))))) * ‖w‖ ^ 2
        = (⨅ (ρ' : {ρ : ℝ // 0 ≤ ρ}),
        (HonestBoxFam v h fc fu HM μ).valFS ρ'.1) * ‖w‖ ^ 2 + (-(4 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) * ‖z‖ ^ 2
          + 4 * (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
              * (|(HonestBoxFam v h fc fu HM μ).E.W1 0|
                  * Real.sqrt ((48 / Real.pi) * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ))
                + (HonestBoxFam v h fc fu HM μ).E.W1omega0
                  * Real.sqrt ((48 / Real.pi) * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)))
              * ‖z‖
          + (|2 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v)
                + μ * (8 * Real.pi * BoseGases.a v)|
              + (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
                * (2 * C * BoseGases.a v
                    + |(HonestBoxFam v h fc fu HM μ).E.W1 0
                        + (HonestBoxFam v h fc fu HM μ).E.W1omega0|)
                * ((48 / Real.pi) * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ))))) * ‖w‖ ^ 2 := by ring
    rw [hL]
    exact hsum2
  rw [← hwnorm, ← hsum, hsym]
  exact hkey
