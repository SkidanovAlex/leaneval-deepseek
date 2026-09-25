import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.CR.Flat.Holder.Bilinear
import Submission.Work.CR.Flat.Holder.hSN_bilinear_le
import Submission.Work.CR.Flat.Holder.holderNorm_smul

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Final

/-! ## Auxiliary lemmas on the `C^{k,α}` norms

The estimates in this file are all of the "one factor is small in sup norm, the other is
`C^2`" shape: `Lcoef A w j z = (i/2) · (dw)_z (A z e_j)` is a *bilinear* expression in
`z ↦ (dw)_z` and `z ↦ A z e_j`, so the Leibniz bounds for `iDN`/`hSN` of `Work.CR.Flat.Holder`
apply, and all that is needed on top is the bookkeeping which reads the two hypotheses on `A`
(sup norm `≤ ε` and Hölder seminorm `≤ ε`) as bounds on `iDN 0`, `iDN 1`, `hSN 0`, `hSN 1`. -/

private lemma holderNorm_congr {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {k : ℕ} {α : ℝ} {f g : X → ℂ} {Ω : Set X} (h : ∀ x ∈ Ω, f x = g x) :
    Work.CR.Flat.holderNorm k α f Ω = Work.CR.Flat.holderNorm k α g Ω := by
  unfold Work.CR.Flat.holderNorm
  refine Finset.sum_congr rfl fun i _ => ?_
  show Work.CR.Flat.Holder.iDN i f Ω + Work.CR.Flat.Holder.hSN i α f Ω
      = Work.CR.Flat.Holder.iDN i g Ω + Work.CR.Flat.Holder.hSN i α g Ω
  rw [Work.CR.Flat.Holder.iDN_congr h, Work.CR.Flat.Holder.hSN_congr h]

/-- A pointwise sup bound gives a bound on the `C^0` sup-norm. -/
private lemma iDN_zero_le_of_bound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {φ : X → E} {Ω : Set X} {ε : ℝ}
    (h : ∀ x ∈ Ω, ‖φ x‖ ≤ ε) :
    Work.CR.Flat.Holder.iDN 0 φ Ω ≤ ENNReal.ofReal ε := by
  rw [Work.CR.Flat.Holder.iDN_zero_deriv]
  exact iSup₂_le fun x hx => ENNReal.ofReal_le_ofReal (h x hx)

/-- A pointwise Hölder bound gives a bound on the `C^{0,α}` Hölder seminorm. -/
private lemma hSN_zero_le_of_holder {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {φ : X → E} {Ω : Set X} {α ε : ℝ}
    (hα0 : 0 < α) (h : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖φ x - φ y‖ ≤ ε * ‖x - y‖ ^ α) :
    Work.CR.Flat.Holder.hSN 0 α φ Ω ≤ ENNReal.ofReal ε := by
  rw [Work.CR.Flat.Holder.hSN_zero_deriv]
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have ht : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos hpos α
  rw [div_le_iff₀ ht]
  exact h x hx y hy

/-- On an open set, the sup norm of the first derivative is controlled by the sup norm of the
honest derivative. -/
private lemma iDN_one_le_of_fderiv_bound {n : ℕ} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    {v : (Fin n → ℂ) → (Fin n → ℂ)} {ε : ℝ} (h : ∀ z ∈ Ω, ‖fderiv ℝ v z‖ ≤ ε) :
    Work.CR.Flat.Holder.iDN 1 v Ω ≤ ENNReal.ofReal ε := by
  rw [← Work.CR.Flat.Holder.iDN_fderivWithin 0 v Ω hΩ.uniqueDiffOn]
  exact iDN_zero_le_of_bound fun z hz => by
    rw [fderivWithin_of_isOpen hΩ hz]
    exact h z hz

/-- On an open set, the `C^{1,α}` Hölder seminorm is controlled by the Hölder seminorm of the
honest derivative. -/
private lemma hSN_one_le_of_fderiv_holder {n : ℕ} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    {α : ℝ} (hα0 : 0 < α) {v : (Fin n → ℂ) → (Fin n → ℂ)} {ε : ℝ}
    (h : ∀ z ∈ Ω, ∀ z' ∈ Ω, ‖fderiv ℝ v z - fderiv ℝ v z'‖ ≤ ε * ‖z - z'‖ ^ α) :
    Work.CR.Flat.Holder.hSN 1 α v Ω ≤ ENNReal.ofReal ε := by
  rw [← Work.CR.Flat.Holder.hSN_fderivWithin 0 α v Ω hΩ.uniqueDiffOn]
  exact hSN_zero_le_of_holder hα0 fun z hz z' hz' => by
    rw [fderivWithin_of_isOpen hΩ hz, fderivWithin_of_isOpen hΩ hz']
    exact h z hz z' hz'

/-- The Leibniz bound for the `C^i` sup-norm of `x ↦ (f x) (g x)`, in the concrete
situation of this file. -/
private lemma iDN_clm_apply_le {n : ℕ}
    {f : (Fin n → ℂ) → ((Fin n → ℂ) →L[ℝ] ℂ)} {g : (Fin n → ℂ) → (Fin n → ℂ)}
    {Ω : Set (Fin n → ℂ)} (i : ℕ)
    (hf : ContDiffOn ℝ (i : ℕ∞) f Ω) (hg : ContDiffOn ℝ (i : ℕ∞) g Ω)
    (hΩ : UniqueDiffOn ℝ Ω) :
    Work.CR.Flat.Holder.iDN i (fun x => (f x) (g x)) Ω ≤
      ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
        (Work.CR.Flat.Holder.iDN j f Ω * Work.CR.Flat.Holder.iDN (i - j) g Ω) := by
  have hfun : (fun x => (ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ ℂ)) (f x) (g x))
      = fun x => (f x) (g x) := by
    funext x; rfl
  have hB : ‖(ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ ℂ) :
      ((Fin n → ℂ) →L[ℝ] ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℂ)‖ ≤ 1 := by
    simp only [ContinuousLinearMap.opNorm_flip, ContinuousLinearMap.apply]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
    simp only [ContinuousLinearMap.coe_id', id, one_mul]
    rfl
  have h := Work.CR.Flat.Holder.iDN_bilinear_le
    (ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ ℂ)) i hf hg hΩ
  rw [hfun] at h
  refine h.trans ?_
  calc ENNReal.ofReal ‖(ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ ℂ) :
        ((Fin n → ℂ) →L[ℝ] ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℂ)‖ * _ ≤ 1 * _ :=
        mul_le_mul_left (ENNReal.ofReal_le_one.mpr hB) _
    _ = _ := one_mul _

/-- The Leibniz bound for the `C^{i,α}` Hölder seminorm of `x ↦ (f x) (g x)`, in the concrete
situation of this file. -/
private lemma hSN_clm_apply_le {n : ℕ}
    {f : (Fin n → ℂ) → ((Fin n → ℂ) →L[ℝ] ℂ)} {g : (Fin n → ℂ) → (Fin n → ℂ)}
    {Ω : Set (Fin n → ℂ)} (i : ℕ) (α : ℝ)
    (hf : ContDiffOn ℝ (i : ℕ∞) f Ω) (hg : ContDiffOn ℝ (i : ℕ∞) g Ω)
    (hΩ : UniqueDiffOn ℝ Ω) :
    Work.CR.Flat.Holder.hSN i α (fun x => (f x) (g x)) Ω ≤
      ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
        (Work.CR.Flat.Holder.hSN j α f Ω * Work.CR.Flat.Holder.iDN (i - j) g Ω
          + Work.CR.Flat.Holder.iDN j f Ω * Work.CR.Flat.Holder.hSN (i - j) α g Ω) := by
  have hfun : (fun x => (ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ ℂ)) (f x) (g x))
      = fun x => (f x) (g x) := by
    funext x; rfl
  have hB : ‖(ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ ℂ) :
      ((Fin n → ℂ) →L[ℝ] ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℂ)‖ ≤ 1 := by
    simp only [ContinuousLinearMap.opNorm_flip, ContinuousLinearMap.apply]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
    simp only [ContinuousLinearMap.coe_id', id, one_mul]
    rfl
  have h := Work.CR.Flat.Holder.hSN_bilinear_le i α
    (ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ ℂ)) hf hg hΩ
  rw [hfun] at h
  refine h.trans ?_
  calc ENNReal.ofReal ‖(ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ ℂ) :
        ((Fin n → ℂ) →L[ℝ] ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℂ)‖ * _ ≤ 1 * _ :=
        mul_le_mul_left (ENNReal.ofReal_le_one.mpr hB) _
    _ = _ := one_mul _

/-- `∑_{j ≤ i} i.choose j = 2^i`, for the binomial coefficients. -/
private lemma choose_sum_eq (i : ℕ) :
    (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞)) = ENNReal.ofReal ((2:ℝ)^i) := by
  rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat,
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2)]

theorem Lcoef_holderNorm_one {n : ℕ} {α : ℝ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hα0 : 0 < α) (hα1 : α < 1) : ∃ C : ℝ, 0 < C ∧ ∀ (A : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)) (ε : ℝ),
    0 ≤ ε → (∀ j : Fin n, ContDiffOn ℝ 1 (fun z => A z (Pi.single j 1)) (Work.NN.Final.pd n ρ 4)) →
    (∀ j : Fin n, Work.NN.Final.VecHolder (fun z => A z (Pi.single j 1)) α ε (Work.NN.Final.pd n ρ 4)) →
    (∀ j : Fin n, Work.NN.Final.VecHolder (fun z => fderiv ℝ (fun z' => A z' (Pi.single j 1)) z) α ε (Work.NN.Final.pd n ρ 4)) →
    ∀ (w : (Fin n → ℂ) → ℂ),
    ContDiffOn ℝ 2 w (Work.NN.Final.pd n ρ 4) → ∀ j : Fin n,
    Work.CR.Flat.holderNorm 1 α (fun z => Work.NN.Core.Lcoef A w j z) (Work.NN.Final.pd n ρ 4)
      ≤ ENNReal.ofReal (C * ε) * Work.CR.Flat.holderNorm 2 α w (Work.NN.Final.pd n ρ 4) := by
  refine ⟨6, by norm_num, ?_⟩
  intro A ε hε hAcont hAv hAdv w hw j
  set Ω : Set (Fin n → ℂ) := Work.NN.Final.pd n ρ 4 with hΩdef
  have hΩopen : IsOpen Ω := by rw [hΩdef]; exact Work.NN.Final.isOpen_pd ρ 4
  have hΩ : UniqueDiffOn ℝ Ω := hΩopen.uniqueDiffOn
  set E : ℝ≥0∞ := ENNReal.ofReal ε with hEdef
  set H : ℝ≥0∞ := Work.CR.Flat.holderNorm 2 α w Ω with hHdef
  set g : (Fin n → ℂ) → (Fin n → ℂ) := fun z => A z (Pi.single j 1) with hgdef
  set f : (Fin n → ℂ) → ((Fin n → ℂ) →L[ℝ] ℂ) := fun z => fderivWithin ℝ w Ω z with hfdef
  set F : (Fin n → ℂ) → ℂ := fun z => (fderivWithin ℝ w Ω z) (A z (Pi.single j 1)) with hFdef
  have hFfg : F = fun z => f z (g z) := by rw [hFdef, hfdef, hgdef]
  -- per-order bounds for `w`
  have hNw : ∀ l ≤ 2, Work.CR.Flat.Holder.iDN l w Ω ≤ H := fun l hl => by
    rw [hHdef]; exact Work.CR.Flat.iterDerivNorm_le_holderNorm 2 α w Ω hl
  have hNsw : ∀ l ≤ 2, Work.CR.Flat.Holder.hSN l α w Ω ≤ H := fun l hl => by
    rw [hHdef]; exact Work.CR.Flat.holderSeminorm_le_holderNorm 2 α w Ω hl
  -- continuity of the two factors
  have hg_cont : ∀ i : ℕ, i ≤ 1 → ContDiffOn ℝ (i : ℕ∞) g Ω := fun i hi => by
    rw [hgdef, hΩdef]
    exact (hAcont j).of_le (by exact_mod_cast hi)
  have hf_cont : ∀ i : ℕ, i ≤ 1 → ContDiffOn ℝ (i : ℕ∞) f Ω := fun i hi => by
    rw [hfdef]
    exact hw.fderivWithin hΩ (Nat.cast_le.mpr (by omega : i + 1 ≤ 2))
  -- the bounds coming from the two `VecHolder` hypotheses
  have hVsup : ∀ z ∈ Ω, ‖A z (Pi.single j 1)‖ ≤ ε := fun z hz => (hAv j).1 z hz
  have hVhold : ∀ z ∈ Ω, ∀ z' ∈ Ω,
      ‖A z (Pi.single j 1) - A z' (Pi.single j 1)‖ ≤ ε * ‖z - z'‖ ^ α :=
    fun z hz z' hz' => (hAv j).2 z hz z' hz'
  have hDVsup : ∀ z ∈ Ω, ‖fderiv ℝ g z‖ ≤ ε := fun z hz => (hAdv j).1 z hz
  have hDVhold : ∀ z ∈ Ω, ∀ z' ∈ Ω, ‖fderiv ℝ g z - fderiv ℝ g z'‖ ≤ ε * ‖z - z'‖ ^ α :=
    fun z hz z' hz' => (hAdv j).2 z hz z' hz'
  have hgn_idn : ∀ l ≤ 1, Work.CR.Flat.Holder.iDN l g Ω ≤ E := by
    intro l hl
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · rw [hEdef]; exact iDN_zero_le_of_bound hVsup
    · rw [hEdef]; exact iDN_one_le_of_fderiv_bound hΩopen hDVsup
  have hgn_hsn : ∀ l ≤ 1, Work.CR.Flat.Holder.hSN l α g Ω ≤ E := by
    intro l hl
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · rw [hEdef]; exact hSN_zero_le_of_holder hα0 hVhold
    · rw [hEdef]; exact hSN_one_le_of_fderiv_holder hΩopen hα0 hDVhold
  -- the Leibniz bounds
  have hidnF : ∀ i ≤ 1, Work.CR.Flat.Holder.iDN i F Ω ≤ ENNReal.ofReal 2 * (H * E) := by
    intro i hi
    have h := iDN_clm_apply_le (f := f) (g := g) i (hf_cont i hi) (hg_cont i hi) hΩ
    rw [hFfg]
    refine h.trans ?_
    calc ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
            (Work.CR.Flat.Holder.iDN j f Ω * Work.CR.Flat.Holder.iDN (i - j) g Ω)
        ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) * (H * E) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hjle : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have h1 : Work.CR.Flat.Holder.iDN j f Ω ≤ H := by
            rw [hfdef, Work.CR.Flat.Holder.iDN_fderivWithin j w Ω hΩ]
            exact hNw (j + 1) (by omega)
          have h2 : Work.CR.Flat.Holder.iDN (i - j) g Ω ≤ E := hgn_idn (i - j) (by omega)
          gcongr
      _ = (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞)) * (H * E) := by rw [Finset.sum_mul]
      _ = ENNReal.ofReal ((2:ℝ)^i) * (H * E) := by rw [choose_sum_eq]
      _ ≤ ENNReal.ofReal 2 * (H * E) := by
          refine mul_le_mul_left ?_ _
          refine ENNReal.ofReal_le_ofReal ?_
          simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hi
  have hhsnF : ∀ i ≤ 1, Work.CR.Flat.Holder.hSN i α F Ω ≤ ENNReal.ofReal 4 * (H * E) := by
    intro i hi
    have h := hSN_clm_apply_le (f := f) (g := g) i α (hf_cont i hi) (hg_cont i hi) hΩ
    rw [hFfg]
    refine h.trans ?_
    have h2i : ENNReal.ofReal ((2:ℝ)^i) ≤ ENNReal.ofReal 2 := by
      refine ENNReal.ofReal_le_ofReal ?_
      simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hi
    calc ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
            (Work.CR.Flat.Holder.hSN j α f Ω * Work.CR.Flat.Holder.iDN (i - j) g Ω
              + Work.CR.Flat.Holder.iDN j f Ω * Work.CR.Flat.Holder.hSN (i - j) α g Ω)
        ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) * (H * E + H * E) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hjle : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have h1 : Work.CR.Flat.Holder.hSN j α f Ω ≤ H := by
            rw [hfdef, Work.CR.Flat.Holder.hSN_fderivWithin j α w Ω hΩ]
            exact hNsw (j + 1) (by omega)
          have h2 : Work.CR.Flat.Holder.iDN (i - j) g Ω ≤ E := hgn_idn (i - j) (by omega)
          have h3 : Work.CR.Flat.Holder.iDN j f Ω ≤ H := by
            rw [hfdef, Work.CR.Flat.Holder.iDN_fderivWithin j w Ω hΩ]
            exact hNw (j + 1) (by omega)
          have h4 : Work.CR.Flat.Holder.hSN (i - j) α g Ω ≤ E := hgn_hsn (i - j) (by omega)
          gcongr
      _ = (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞)) * (H * E + H * E) := by
          rw [Finset.sum_mul]
      _ = ENNReal.ofReal ((2:ℝ)^i) * (H * E + H * E) := by rw [choose_sum_eq]
      _ = ENNReal.ofReal ((2:ℝ)^i) * (H * E) + ENNReal.ofReal ((2:ℝ)^i) * (H * E) := by
          rw [mul_add]
      _ ≤ ENNReal.ofReal 2 * (H * E) + ENNReal.ofReal 2 * (H * E) :=
          add_le_add (mul_le_mul_left h2i _) (mul_le_mul_left h2i _)
      _ = ENNReal.ofReal 4 * (H * E) := by
          rw [← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
          norm_num
  have hFsum : Work.CR.Flat.holderNorm 1 α F Ω ≤ ENNReal.ofReal 12 * (H * E) := by
    rw [Work.CR.Flat.holderNorm]
    rw [show (1 + 1 : ℕ) = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
    have h0 := add_le_add (hidnF 0 (by norm_num)) (hhsnF 0 (by norm_num))
    have h1' := add_le_add (hidnF 1 le_rfl) (hhsnF 1 le_rfl)
    refine (add_le_add h0 h1').trans ?_
    rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  -- the coefficient is a scalar multiple of `F` on `Ω`
  have hcoef : ∀ z ∈ Ω, Work.NN.Core.Lcoef A w j z = ((Complex.I / 2) • F) z := by
    intro z hz
    rw [hFdef, Work.NN.Core.Lcoef, Pi.smul_apply, smul_eq_mul,
      ← fderivWithin_of_isOpen hΩopen hz]
  have hF_cont : ContDiffOn ℝ 1 F Ω := by
    rw [hFfg]
    exact ContDiffOn.clm_apply (hf_cont 1 le_rfl) (hg_cont 1 le_rfl)
  have hsmul : Work.CR.Flat.holderNorm 1 α (fun z => (Complex.I / 2) • F z) Ω
      = ENNReal.ofReal (1/2) * Work.CR.Flat.holderNorm 1 α F Ω := by
    rw [show (fun z => (Complex.I / 2) • F z) = (Complex.I / 2) • F from rfl]
    rw [Work.CR.Flat.Holder.holderNorm_smul (Complex.I / 2) hF_cont hΩ,
      show ‖(Complex.I / 2 : ℂ)‖ = 1/2 from by rw [norm_div, Complex.norm_I]; norm_num]
  calc Work.CR.Flat.holderNorm 1 α (fun z => Work.NN.Core.Lcoef A w j z) Ω
      = Work.CR.Flat.holderNorm 1 α (fun z => (Complex.I / 2) • F z) Ω :=
        holderNorm_congr hcoef
    _ = ENNReal.ofReal (1/2) * Work.CR.Flat.holderNorm 1 α F Ω := hsmul
    _ ≤ ENNReal.ofReal (1/2) * (ENNReal.ofReal 12 * (H * E)) := mul_le_mul_right hFsum _
    _ = ENNReal.ofReal (6 * ε) * H := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
        have h612 : (1/2:ℝ) * 12 = 6 := by norm_num
        rw [h612, hEdef, mul_comm H (ENNReal.ofReal ε), ← mul_assoc,
          ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 6)]

end Work.NN.Final
