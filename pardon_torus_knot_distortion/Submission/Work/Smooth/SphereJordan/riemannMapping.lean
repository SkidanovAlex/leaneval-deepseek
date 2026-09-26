import Mathlib
import Submission.Work.Smooth.SphereJordan.montel
import Submission.Work.Smooth.SphereJordan.hurwitz
import Submission.Work.Smooth.SphereJordan.exists_seed
import Submission.Work.Smooth.SphereJordan.PDU.Mobius
import Submission.Work.Smooth.SphereJordan.PDU.Root

/-!
# The Riemann mapping theorem

An open, non-empty, simply connected proper subset `U ⊆ ℂ` admits a bijective holomorphic map
onto the open unit disc.  The proof is the classical extremal (Koebe) argument:

* `exists_seed` produces a holomorphic injection `U → 𝔻` with nowhere vanishing derivative;
* composing with a disc automorphism normalises it to send a fixed `p ∈ U` to `0`;
* one maximises `‖deriv g p‖` over all injective holomorphic `g : U → 𝔻` with `g p = 0`
  (the value is finite by Cauchy's estimate, positive by the seed);
* Montel's theorem gives a locally uniform limit `G` of a maximising sequence, Hurwitz's theorem
  makes `G` injective, and the maximum modulus principle upgrades `‖G‖ ≤ 1` to `‖G‖ < 1`;
* `G` is surjective, because a point `a ∈ 𝔻 \ G '' U` would allow the "square root trick":
  `φ_a ∘ G` has a holomorphic square root `h` on `U`, and `φ_{h p} ∘ h` is an admissible map with
  strictly larger `‖deriv · p‖`, contradicting extremality of `G`.
-/

namespace Work.Smooth.SphereJordan

open Set Metric Filter
open scoped Topology

set_option linter.style.haveILetI false

/-- Every simply connected subset of `ℂ` is preconnected. -/
lemma isPreconnected_of_isSimplyConnected {U : Set ℂ} (h : IsSimplyConnected U) :
    IsPreconnected U := by
  rw [isPreconnected_iff_preconnectedSpace]
  haveI : SimplyConnectedSpace U := h
  infer_instance

/-- A holomorphic function which is bounded by `1` on an open (pre)connected domain and whose
derivative at one point does not vanish maps the domain into the open unit ball. -/
lemma mapsTo_ball_of_norm_le_one {U : Set ℂ} (hUo : IsOpen U) (hUp : IsPreconnected U)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) (hle : ∀ z ∈ U, ‖g z‖ ≤ 1)
    {p : ℂ} (hp : p ∈ U) (hderiv : deriv g p ≠ 0) :
    Set.MapsTo g U (Metric.ball (0 : ℂ) 1) := by
  intro z hz
  by_contra h
  rw [mem_ball_zero_iff, not_lt] at h
  have hz1 : ‖g z‖ = 1 := le_antisymm (hle z hz) h
  have hmax : IsMaxOn (fun w => ‖g w‖) U z := by
    intro w hw
    calc ‖g w‖ ≤ 1 := hle w hw
      _ = ‖g z‖ := hz1.symm
  have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hUp hUo hg hz hmax
  have hev : g =ᶠ[𝓝 p] (fun _ => g z) := by
    filter_upwards [hUo.mem_nhds hp] with w hw
    exact heq hw
  have h0 : deriv g p = 0 := by rw [hev.deriv_eq, deriv_const]
  exact hderiv h0

/-- **The normalised seed map.**  For an open, simply connected, proper `U ⊆ ℂ` and any `p ∈ U`
there is a holomorphic injection `U → 𝔻` sending `p` to `0` with non-zero derivative at `p`. -/
lemma exists_admissible_seed {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    (hU : U ≠ Set.univ) {p : ℂ} (hp : p ∈ U) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ Set.MapsTo g U (Metric.ball (0 : ℂ) 1) ∧
      Set.InjOn g U ∧ g p = 0 ∧ deriv g p ≠ 0 := by
  obtain ⟨f, hfmap, hfinj, hfderiv⟩ := exists_seed hUo hUc hU
  set b : ℂ := f p with hb
  have hb_lt : ‖b‖ < 1 := by
    rw [hb]
    simpa [mem_ball_zero_iff] using hfmap hp
  refine ⟨fun z => (f z - b) / (1 - star b * f z), ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hz1 : ‖f z‖ < 1 := by simpa [mem_ball_zero_iff] using hfmap hz
    have hne : (1 : ℂ) - star b * f z ≠ 0 := (unitDisc_mobius_map b (f z) hb_lt hz1).1
    have hdz : DifferentiableAt ℂ f z := differentiableAt_of_deriv_ne_zero (hfderiv z hz)
    have hψ : DifferentiableAt ℂ (fun w : ℂ => (w - b) / (1 - star b * w)) (f z) :=
      (unitDisc_mobius_hasDerivAt b (f z) hne).differentiableAt
    exact (hψ.comp z hdz).differentiableWithinAt
  · intro z hz
    have hz1 : ‖f z‖ < 1 := by simpa [mem_ball_zero_iff] using hfmap hz
    exact mem_ball_zero_iff.mpr (unitDisc_mobius_map b (f z) hb_lt hz1).2
  · intro z hz w hw heq
    have hz1 : ‖f z‖ < 1 := by simpa [mem_ball_zero_iff] using hfmap hz
    have hw1 : ‖f w‖ < 1 := by simpa [mem_ball_zero_iff] using hfmap hw
    exact hfinj hz hw (unitDisc_mobius_inj b (f z) (f w) hb_lt hz1 hw1 heq)
  · simp [hb]
  · intro hzero
    have hz1 : ‖f p‖ < 1 := by simpa [mem_ball_zero_iff] using hfmap hp
    have hne : (1 : ℂ) - star b * f p ≠ 0 := (unitDisc_mobius_map b (f p) hb_lt hz1).1
    have hdz : DifferentiableAt ℂ f p := differentiableAt_of_deriv_ne_zero (hfderiv p hp)
    have hchain := (unitDisc_mobius_hasDerivAt b (f p) hne).comp p hdz.hasDerivAt
    have hd : deriv ((fun w : ℂ => (w - b) / (1 - star b * w)) ∘ f) p ≠ 0 := by
      rw [hchain.deriv]
      refine mul_ne_zero ?_ (hfderiv p hp)
      rw [div_ne_zero_iff]
      refine ⟨?_, pow_ne_zero 2 hne⟩
      intro h
      have hnr : Complex.normSq b = 1 := by
        have h1 : (1 : ℝ) - Complex.normSq b = 0 := by
          have := congrArg Complex.re h
          simpa using this
        linarith
      rw [Complex.normSq_eq_norm_sq] at hnr
      nlinarith [norm_nonneg b, hb_lt]
    exact hd (by simpa only [Function.comp_def] using hzero)

/-- **The square-root ("surjectivity") step of the Riemann mapping theorem.**
If `G : U → 𝔻` is injective, holomorphic, sends `p` to `0` and has non-zero derivative at `p`,
and if `a ∈ 𝔻` is not in the image of `G`, then there is an injective holomorphic `g : U → 𝔻`
with `g p = 0` and `‖deriv G p‖ < ‖deriv g p‖`.

Proof: `φ_a ∘ G` is holomorphic, maps into `𝔻` and vanishes nowhere, so on the simply connected
domain `U` it has a holomorphic square root `h` with `h '' U ⊆ 𝔻`.  Then `g := φ_{h p} ∘ h` is
admissible, and differentiating `h² = φ_a ∘ G` gives
`deriv g p = ((1+‖a‖)/(2‖h p‖)) · deriv G p` with multiplier `> 1`. -/
lemma exists_admissible_of_not_surj {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    {G : ℂ → ℂ} {p : ℂ} (hp : p ∈ U)
    (hG : DifferentiableOn ℂ G U) (hGmap : Set.MapsTo G U (Metric.ball (0 : ℂ) 1))
    (hGinj : Set.InjOn G U) (hGp : G p = 0) (hGderiv : deriv G p ≠ 0)
    {a : ℂ} (ha : a ∈ Metric.ball (0 : ℂ) 1) (hnot : a ∉ G '' U) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ Set.MapsTo g U (Metric.ball (0 : ℂ) 1) ∧
      Set.InjOn g U ∧ g p = 0 ∧ ‖deriv G p‖ < ‖deriv g p‖ := by
  classical
  have ha_lt : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  have ha_ne : a ≠ 0 := by
    intro h
    exact hnot ⟨p, hp, by rw [h, hGp]⟩
  have hGa : ∀ z ∈ U, G z ≠ a := fun z hz h => hnot ⟨z, hz, h⟩
  set ψ : ℂ → ℂ := fun w => (w - a) / (1 - star a * w) with hψ
  set F : ℂ → ℂ := fun z => ψ (G z) with hF
  have hGball : ∀ z ∈ U, ‖G z‖ < 1 := fun z hz => mem_ball_zero_iff.mp (hGmap hz)
  have hGat : ∀ z ∈ U, DifferentiableAt ℂ G z := fun z hz => hG.differentiableAt (hUo.mem_nhds hz)
  have hFdiff : DifferentiableOn ℂ F U := by
    intro z hz
    have hne : (1 : ℂ) - star a * G z ≠ 0 := (unitDisc_mobius_map a (G z) ha_lt (hGball z hz)).1
    have hψd : DifferentiableAt ℂ ψ (G z) := by
      rw [hψ]
      exact (unitDisc_mobius_hasDerivAt a (G z) hne).differentiableAt
    have hcomp : DifferentiableWithinAt ℂ (ψ ∘ G) U z :=
      (hψd.comp z (hGat z hz)).differentiableWithinAt
    rw [hF]
    simpa only [Function.comp_def] using hcomp
  have hFmap : Set.MapsTo F U (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have h := (unitDisc_mobius_map a (G z) ha_lt (hGball z hz)).2
    rw [hF, mem_ball_zero_iff]
    simpa only [hψ] using h
  have hFne : ∀ z ∈ U, F z ≠ 0 := by
    intro z hz h
    have h' : (G z - a) / (1 - star a * G z) = 0 := by
      rw [hF, hψ] at h
      simpa only using h
    have hne := (unitDisc_mobius_map a (G z) ha_lt (hGball z hz)).1
    rcases div_eq_zero_iff.mp h' with h1 | h1
    · exact hGa z hz (sub_eq_zero.mp h1)
    · exact hne h1
  have hFinj : Set.InjOn F U := by
    intro z hz w hw h
    have h' : (G z - a) / (1 - star a * G z) = (G w - a) / (1 - star a * G w) := by
      rw [hF, hψ] at h
      simpa only using h
    exact hGinj hz hw (unitDisc_mobius_inj a (G z) (G w) ha_lt (hGball z hz) (hGball w hw) h')
  obtain ⟨h, hhcont, hh2⟩ :=
    Complex.exists_continuousOn_pow_eq hUc hUo hFdiff.continuousOn
      (by rintro ⟨z, hz, hz0⟩; exact hFne z hz hz0) two_ne_zero
  have hheq : ∀ z ∈ U, h z ^ 2 = F z := fun z _ => hh2 z
  have hhne : ∀ z ∈ U, h z ≠ 0 := by
    intro z hz hz0
    have hthis := hheq z hz
    rw [hz0] at hthis
    simp at hthis
    exact hFne z hz hthis.symm
  have hhdiff : DifferentiableOn ℂ h U :=
    differentiableOn_of_pow_eq hUo (by norm_num) hFdiff hhcont hhne hheq
  have hhmap : Set.MapsTo h U (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    rw [mem_ball_zero_iff]
    have h2 : ‖h z‖ ^ 2 = ‖F z‖ := by rw [← norm_pow, hheq z hz]
    have hlt : ‖F z‖ < 1 := mem_ball_zero_iff.mp (hFmap hz)
    nlinarith [norm_nonneg (h z)]
  have hhinj : Set.InjOn h U := by
    intro z hz w hw hzw
    apply hFinj hz hw
    rw [← hheq z hz, ← hheq w hw, hzw]
  set b : ℂ := h p with hb
  have hb_lt : ‖b‖ < 1 := by rw [hb]; exact mem_ball_zero_iff.mp (hhmap hp)
  have hb2 : b ^ 2 = -a := by
    have h1 : b ^ 2 = F p := by rw [hb]; exact hheq p hp
    rw [h1, hF]
    simp only [hGp]
    rw [hψ]
    simp
  have hb_ne : b ≠ 0 := by
    intro h0
    have : a = 0 := by
      have hh := hb2
      rw [h0] at hh
      simpa using hh.symm
    exact ha_ne this
  have hbsq : ‖b‖ ^ 2 = ‖a‖ := by
    calc ‖b‖ ^ 2 = ‖b ^ 2‖ := (norm_pow b 2).symm
      _ = ‖-a‖ := by rw [hb2]
      _ = ‖a‖ := norm_neg a
  set ψb : ℂ → ℂ := fun w => (w - b) / (1 - star b * w) with hψb
  refine ⟨fun z => ψb (h z), ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hne : (1 : ℂ) - star b * h z ≠ 0 :=
      (unitDisc_mobius_map b (h z) hb_lt (mem_ball_zero_iff.mp (hhmap hz))).1
    have hψd : DifferentiableAt ℂ ψb (h z) := by
      rw [hψb]
      exact (unitDisc_mobius_hasDerivAt b (h z) hne).differentiableAt
    have hcomp : DifferentiableWithinAt ℂ (ψb ∘ h) U z :=
      (hψd.comp z (hhdiff.differentiableAt (hUo.mem_nhds hz))).differentiableWithinAt
    simpa only [Function.comp_def] using hcomp
  · intro z hz
    exact mem_ball_zero_iff.mpr
      (unitDisc_mobius_map b (h z) hb_lt (mem_ball_zero_iff.mp (hhmap hz))).2
  · intro z hz w hw heq
    have heq' : (h z - b) / (1 - star b * h z) = (h w - b) / (1 - star b * h w) := by
      rw [hψb] at heq
      simpa only using heq
    exact hhinj hz hw (unitDisc_mobius_inj b (h z) (h w) hb_lt
      (mem_ball_zero_iff.mp (hhmap hz)) (mem_ball_zero_iff.mp (hhmap hw)) heq')
  · rw [hψb]
    simp [hb]
  · -- the derivative comparison
    have hh_at : HasDerivAt h (deriv h p) p := (hhdiff.differentiableAt (hUo.mem_nhds hp)).hasDerivAt
    have hG_at : HasDerivAt G (deriv G p) p := (hGat p hp).hasDerivAt
    -- (a) derivative of `F = ψ ∘ G` at `p`
    have hne_psi : (1 : ℂ) - star a * G p ≠ 0 :=
      (unitDisc_mobius_map a (G p) ha_lt (hGball p hp)).1
    have hcoef : ((1 - ((Complex.normSq a : ℝ) : ℂ)) / (1 - star a * G p) ^ 2)
        = ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) := by
      rw [hGp, mul_zero, sub_zero, one_pow, div_one, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    have hF_at : HasDerivAt F (((1 - ((Complex.normSq a : ℝ) : ℂ))
        / (1 - star a * G p) ^ 2) * deriv G p) p := by
      have hcomp := (unitDisc_mobius_hasDerivAt a (G p) hne_psi).comp p hG_at
      rw [hF, hψ]
      exact hcomp
    have hderivF_G : deriv F p = ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) * deriv G p := by
      rw [hF_at.deriv, hcoef]
    -- (b) `deriv F p = 2 b h'(p)`
    have hevFh : F =ᶠ[𝓝 p] ((fun w : ℂ => w ^ 2) ∘ h) := by
      filter_upwards [hUo.mem_nhds hp] with z hz
      show F z = ((fun w : ℂ => w ^ 2) ∘ h) z
      rw [Function.comp_apply]
      exact (hheq z hz).symm
    have hderivh : deriv ((fun w : ℂ => w ^ 2) ∘ h) p = 2 * h p * deriv h p := by
      have hpow : HasDerivAt (fun w : ℂ => w ^ 2) (2 * h p ^ (2 - 1)) (h p) :=
        hasDerivAt_pow 2 (h p)
      have hcomp := hpow.comp p hh_at
      have := hcomp.deriv
      simpa using this
    have hderivF_h : deriv F p = (2 * b) * deriv h p := by
      rw [hevFh.deriv_eq, hderivh, ← hb]
    -- (c) `deriv g p = (1 - ‖a‖)⁻¹ h'(p)`
    have hcoefb : ((1 - ((Complex.normSq b : ℝ) : ℂ)) / (1 - star b * h p) ^ 2)
        = (((1 - ‖a‖)⁻¹ : ℝ) : ℂ) := by
      have hbsq' : Complex.normSq b = ‖a‖ := by
        rw [Complex.normSq_eq_norm_sq]; exact hbsq
      have hxeq : (1 : ℂ) - ((‖a‖ : ℝ) : ℂ) = ((1 - ‖a‖ : ℝ) : ℂ) := by
        rw [Complex.ofReal_sub, Complex.ofReal_one]
      have hx : ((1 - ‖a‖ : ℝ) : ℂ) ≠ 0 := by
        rw [Complex.ofReal_ne_zero]; linarith
      rw [← hb, star_mul_self_eq b, hbsq', hxeq, Complex.ofReal_inv]
      field_simp
    have hψb_at : HasDerivAt ψb (((1 - ((Complex.normSq b : ℝ) : ℂ))
        / (1 - star b * h p) ^ 2)) (h p) := by
      rw [hψb]
      exact unitDisc_mobius_hasDerivAt b (h p)
        (unitDisc_mobius_map b (h p) hb_lt (mem_ball_zero_iff.mp (hhmap hp))).1
    have hderivg_h : deriv (fun z => ψb (h z)) p = (((1 - ‖a‖)⁻¹ : ℝ) : ℂ) * deriv h p := by
      have hcomp := hψb_at.comp p hh_at
      have := hcomp.deriv
      rw [hcoefb] at this
      simpa only [Function.comp_def] using this
    -- the comparison
    have hmain : (2 * b) * deriv (fun z => ψb (h z)) p = ((1 + ‖a‖ : ℝ) : ℂ) * deriv G p := by
      have hcast : (((1 - ‖a‖)⁻¹ : ℝ) : ℂ) * ((1 - ‖a‖ ^ 2 : ℝ) : ℂ)
          = ((1 + ‖a‖ : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul]
        congr 1
        have h1 : (1 : ℝ) - ‖a‖ ≠ 0 := by linarith
        field_simp
        ring
      calc (2 * b) * deriv (fun z => ψb (h z)) p
          = (2 * b) * ((((1 - ‖a‖)⁻¹ : ℝ) : ℂ) * deriv h p) := by rw [hderivg_h]
        _ = (((1 - ‖a‖)⁻¹ : ℝ) : ℂ) * ((2 * b) * deriv h p) := by ring
        _ = (((1 - ‖a‖)⁻¹ : ℝ) : ℂ) * deriv F p := by rw [← hderivF_h]
        _ = (((1 - ‖a‖)⁻¹ : ℝ) : ℂ) * (((1 - ‖a‖ ^ 2 : ℝ) : ℂ) * deriv G p) := by
              rw [hderivF_G]
        _ = ((((1 - ‖a‖)⁻¹ : ℝ) : ℂ) * ((1 - ‖a‖ ^ 2 : ℝ) : ℂ)) * deriv G p := by ring
        _ = ((1 + ‖a‖ : ℝ) : ℂ) * deriv G p := by rw [hcast]
    have hnorm : (2 * ‖b‖) * ‖deriv (fun z => ψb (h z)) p‖ = (1 + ‖a‖) * ‖deriv G p‖ := by
      have hn := congrArg norm hmain
      have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
      have hc : ‖(((1 + ‖a‖ : ℝ)) : ℂ)‖ = 1 + ‖a‖ :=
        (RCLike.norm_ofReal (K := ℂ) (1 + ‖a‖)).trans (abs_of_nonneg (by positivity))
      rw [norm_mul, norm_mul, norm_mul, h2, hc] at hn
      exact hn
    have h2b : 0 < 2 * ‖b‖ := by
      have : 0 < ‖b‖ := norm_pos_iff.mpr hb_ne
      linarith
    have hcmp : 2 * ‖b‖ < 1 + ‖a‖ := by
      have hsp : 0 < (1 - ‖a‖) ^ 2 := pow_pos (by linarith) 2
      have h4 : (2 * ‖b‖) ^ 2 < (1 + ‖a‖) ^ 2 := by nlinarith [hbsq, hsp]
      have := sq_lt_sq.mp h4
      rwa [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at this
    have hMpos : 0 < ‖deriv G p‖ := norm_pos_iff.mpr hGderiv
    have hnum : (2 * ‖b‖) * ‖deriv G p‖ < (1 + ‖a‖) * ‖deriv G p‖ :=
      mul_lt_mul_of_pos_right hcmp hMpos
    have hlt' : (2 * ‖b‖) * ‖deriv G p‖ < (2 * ‖b‖) * ‖deriv (fun z => ψb (h z)) p‖ := by
      rw [hnorm]
      exact hnum
    exact lt_of_mul_lt_mul_left hlt' (le_of_lt h2b)

/-- The class of *admissible* competitors in the extremal argument: holomorphic maps of `U` into
the open unit disc which are injective on `U` and send `p` to `0`. -/
def IsAdmissible (U : Set ℂ) (p : ℂ) (g : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ g U ∧ Set.MapsTo g U (Metric.ball (0 : ℂ) 1) ∧ Set.InjOn g U ∧ g p = 0

/-- **The extremal function of the Riemann mapping theorem.**  For an open, preconnected, simply
connected proper `U ⊆ ℂ` and `p ∈ U` there is an admissible `G` which maximises `‖deriv g p‖`
among all admissible `g`, and whose derivative at `p` does not vanish. -/
lemma exists_extremal {U : Set ℂ} (hUo : IsOpen U) (hUp : IsPreconnected U)
    (hUc : IsSimplyConnected U) (hU : U ≠ Set.univ) {p : ℂ} (hp : p ∈ U) :
    ∃ G : ℂ → ℂ, IsAdmissible U p G ∧ deriv G p ≠ 0 ∧
      ∀ g : ℂ → ℂ, IsAdmissible U p g → ‖deriv g p‖ ≤ ‖deriv G p‖ := by
  classical
  obtain ⟨ρ, hρpos, hρsub⟩ : ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall p ρ ⊆ U := by
    obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hUo.mem_nhds hp)
    exact ⟨r / 2, by linarith, (Metric.closedBall_subset_ball (by linarith)).trans hrU⟩
  set S : Set ℝ := {t | ∃ g : ℂ → ℂ, IsAdmissible U p g ∧ t = ‖deriv g p‖} with hS
  have hSne : S.Nonempty := by
    obtain ⟨g, hg1, hg2, hg3, hg4, -⟩ := exists_admissible_seed hUo hUc hU hp
    exact ⟨‖deriv g p‖, g, ⟨hg1, hg2, hg3, hg4⟩, rfl⟩
  have hSbdd : BddAbove S := by
    refine ⟨1 / ρ, fun t ht => ?_⟩
    obtain ⟨g, ⟨hd, hm, -, -⟩, rfl⟩ := ht
    exact norm_deriv_le_one hd (fun z hz => le_of_lt (mem_ball_zero_iff.mp (hm hz))) hρpos hρsub
  set M : ℝ := sSup S with hM
  have hMub : ∀ t ∈ S, t ≤ M := fun t ht => le_csSup hSbdd ht
  have hMpos : 0 < M := by
    obtain ⟨g, hg1, hg2, hg3, hg4, hg5⟩ := exists_admissible_seed hUo hUc hU hp
    have hmem : ‖deriv g p‖ ∈ S := ⟨g, ⟨hg1, hg2, hg3, hg4⟩, rfl⟩
    have hle := hMub ‖deriv g p‖ hmem
    have hpos : 0 < ‖deriv g p‖ := norm_pos_iff.mpr hg5
    linarith
  have hsep : ∀ n : ℕ, ∃ g : ℂ → ℂ, IsAdmissible U p g ∧ M - 1 / ((n : ℝ) + 1) < ‖deriv g p‖ := by
    intro n
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hlt : M - 1 / ((n : ℝ) + 1) < sSup S := by rw [← hM]; linarith
    obtain ⟨t, ht, hlt2⟩ := (lt_csSup_iff hSbdd hSne).mp hlt
    obtain ⟨g, hg, rfl⟩ := ht
    exact ⟨g, hg, hlt2⟩
  choose u huadm huclose using hsep
  have hu_le : ∀ n, ‖deriv (u n) p‖ ≤ M := fun n => hMub _ ⟨u n, huadm n, rfl⟩
  have htend : Tendsto (fun n : ℕ => ‖deriv (u n) p‖) atTop (𝓝 M) := by
    have h1 : Tendsto (fun n : ℕ => M - 1 / ((n : ℝ) + 1)) atTop (𝓝 M) := by
      have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hsub : Tendsto (fun _ : ℕ => M) atTop (𝓝 M) := tendsto_const_nhds
      simpa using hsub.sub h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds
      (fun n => le_of_lt (huclose n)) hu_le
  obtain ⟨φ, hφ, G, hGdiff, hGtlu⟩ := montel hUo u (fun n => (huadm n).1)
    (fun n z hz => le_of_lt (mem_ball_zero_iff.mp ((huadm n).2.1 hz)))
  have hGp : G p = 0 := by
    have ht := hGtlu.tendsto_at hp
    have h0 : Tendsto (fun n => u (φ n) p) atTop (𝓝 (0 : ℂ)) :=
      tendsto_const_nhds.congr' (Eventually.of_forall fun n => ((huadm (φ n)).2.2.2).symm)
    exact tendsto_nhds_unique ht h0
  have hGle : ∀ z ∈ U, ‖G z‖ ≤ 1 := by
    intro z hz
    have ht : Tendsto (fun n => ‖u (φ n) z‖) atTop (𝓝 ‖G z‖) := (hGtlu.tendsto_at hz).norm
    exact le_of_tendsto ht
      (Eventually.of_forall fun n => le_of_lt (mem_ball_zero_iff.mp ((huadm (φ n)).2.1 hz)))
  have hnormM : ‖deriv G p‖ = M := by
    have h1 : Tendsto (fun n => ‖deriv (u (φ n)) p‖) atTop (𝓝 M) := htend.comp hφ.tendsto_atTop
    have h2 : Tendsto (fun n => ‖deriv (u (φ n)) p‖) atTop (𝓝 ‖deriv G p‖) := by
      have ht := (hGtlu.deriv (Eventually.of_forall fun n => (huadm (φ n)).1) hUo).tendsto_at hp
      simpa only [Function.comp_apply] using ht.norm
    exact tendsto_nhds_unique h2 h1
  have hGderiv : deriv G p ≠ 0 := by
    rw [← norm_pos_iff, hnormM]
    exact hMpos
  have hGinj : Set.InjOn G U := by
    rcases hurwitz hUo hUp (fun n => (huadm (φ n)).1) hGdiff
      (fun n => (huadm (φ n)).2.2.1) hGtlu with h | ⟨c, hc⟩
    · exact h
    · exfalso
      have hev : G =ᶠ[𝓝 p] (fun _ => c) := by
        filter_upwards [hUo.mem_nhds hp] with z hz
        exact hc z hz
      have h0 : deriv G p = 0 := by rw [hev.deriv_eq, deriv_const]
      exact hGderiv h0
  have hGmap : Set.MapsTo G U (Metric.ball (0 : ℂ) 1) :=
    mapsTo_ball_of_norm_le_one hUo hUp hGdiff hGle hp hGderiv
  refine ⟨G, ⟨hGdiff, hGmap, hGinj, hGp⟩, hGderiv, ?_⟩
  intro g hg
  rw [hnormM]
  exact hMub _ ⟨g, hg, rfl⟩

/-- **The Riemann mapping theorem** (existence form): an open, non-empty, simply connected proper
subset `U ⊆ ℂ` admits a bijective holomorphic map onto the open unit disc. -/
theorem riemannMapping {U : Set ℂ} (hUo : IsOpen U) (hUne : U.Nonempty) (hUc : IsSimplyConnected U)
    (hU : U ≠ Set.univ) :
    ∃ g : ℂ → ℂ, Set.BijOn g U (Metric.ball (0 : ℂ) 1) ∧ DifferentiableOn ℂ g U := by
  obtain ⟨p, hp⟩ := hUne
  have hUp : IsPreconnected U := isPreconnected_of_isSimplyConnected hUc
  obtain ⟨G, ⟨hGdiff, hGmap, hGinj, hGp⟩, hGderiv, hGmax⟩ :=
    exists_extremal hUo hUp hUc hU hp
  refine ⟨G, ⟨hGmap, hGinj, ?_⟩, hGdiff⟩
  intro a ha
  by_contra hnot
  obtain ⟨g, hgd, hgm, hgi, hgp, hlt⟩ :=
    exists_admissible_of_not_surj hUo hUc hp hGdiff hGmap hGinj hGp hGderiv ha hnot
  exact (not_le.mpr hlt) (hGmax g ⟨hgd, hgm, hgi, hgp⟩)

end Work.Smooth.SphereJordan
