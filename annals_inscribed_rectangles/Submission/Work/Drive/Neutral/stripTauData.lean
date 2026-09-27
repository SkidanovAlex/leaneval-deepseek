import Mathlib
import Submission.Work.Drive.cone_chain
import Submission.Work.Drive.stripConfigInterface
import Submission.Work.Drive.exists_secant_dir_contDiff
import Submission.Work.Drive.stripChartSmooth
import Submission.Work.Drive.stripChartExt
import Submission.Work.Drive.exists_contMDiffAt_chordDir_sq

/-!
# The `τ = s²` data of the configuration strip

The configuration strip of a smooth plane curve is the image of the chord family
`s ↦ {γ (exp (σ+s)), γ (exp (σ-s))}`; its capping data (radius, disk coordinate, squared unit chord
direction) is **even** in the opening parameter `s`, so it is a smooth function of `τ = s²` — and
only of `τ`: the map `(σ,s) ↦ data(σ,s)` has rank one at `s = 0`, because it is invariant under
`(σ,s) ↦ (σ,-s)` while fixing the diagonal pointwise, so *no* chart of the strip built from the two
endpoint parameters can be immersive there.  The honest chart of the closed configuration Möbius band
therefore uses `τ = s²` as the transverse coordinate, which is why the even-factorisation lemma
(`Work.Drive.exists_contDiffOn_even_comp_sqrt`) is needed.

This file provides that data, in the coordinates of `Work.Drive.stripR`/`stripD`/`chordUnitDir`, and
proves exactly what the `τ`-chart has to know:

* smoothness in `(σ, s)`: `contDiff_symmMid`, `contDiff_symmChordC`, `contDiff_symmA`,
  `contDiff_symmR`, `contDiff_symmD`, `contDiff_symmWC`, and `contDiffAt_symmE` at the diagonal;
* evenness in `s`: `symmMid_neg`, `symmChordC_neg`, `symmA_neg`, `symmR_neg`, `symmD_neg`,
  `symmWC_neg`, `symmE_neg`, `symmData_neg` (the hypothesis of the even-factorisation lemma);
* the side conditions of the configuration piece: `symmR_pos`, `symmD_norm_le_one`, `symmE_norm`;
* the identification with the strip of `Work.Drive.stripChart`: `symmR_eq_stripR`, `symmD_eq_stripD`
  and `symmE_eq_chordUnitDir_sq`.

The direction is computed from the **divided difference** `Work.Drive.secantW (curve γ)` rather than
from the chord itself: `dirC` of the chord is discontinuous at the diagonal (`dirC 0 = 0`, whereas the
limit is the tangent direction), while the *squared* unit direction of the divided difference extends
smoothly, with diagonal value the squared tangent direction.
-/

set_option autoImplicit false
noncomputable section

namespace Work.Drive.Neutral

open Manifold
open scoped Manifold ContDiff Topology
open Classical
open Submission.Configuration Submission.Geometry Submission.Collision

variable {γ : Circle → ℝ × ℝ}

/-- Complexification of a plane vector, with the **Euclidean** norm. -/
def symmC (v : ℝ × ℝ) : ℂ := ⟨v.1, v.2⟩

lemma norm_symmC (v : ℝ × ℝ) : ‖symmC v‖ = eucNorm v := normC_eq_eucNorm v

lemma symmC_smul (c : ℝ) (v : ℝ × ℝ) : symmC (c • v) = (c : ℂ) * symmC v := by
  refine Complex.ext ?_ ?_ <;> simp [symmC]

lemma symmC_neg (v : ℝ × ℝ) : symmC (-v) = -symmC v := by
  refine Complex.ext ?_ ?_ <;> simp [symmC]

lemma symmC_eq_zero_iff {v : ℝ × ℝ} : symmC v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have h1 : v.1 = 0 := by simpa [symmC] using congrArg Complex.re h
    have h2 : v.2 = 0 := by simpa [symmC] using congrArg Complex.im h
    exact Prod.ext h1 h2
  · rintro rfl
    exact Complex.ext (by simp [symmC]) (by simp [symmC])

lemma chordC_eq_symmC (γ : Circle → ℝ × ℝ) (p : ℝ × ℝ) :
    chordC γ p = symmC (γ (Circle.exp p.1) - γ (Circle.exp p.2)) := rfl

lemma chordC_swap (γ : Circle → ℝ × ℝ) (a b : ℝ) :
    chordC γ (b, a) = -chordC γ (a, b) := by
  rw [chordC_eq_symmC, chordC_eq_symmC, ← symmC_neg]
  congr 1
  ext <;> simp

/-! ## The data of the symmetric chord family -/

/-- The midpoint of the symmetric chord family at parameters `(σ, s)`. -/
def symmMid (γ : Circle → ℝ × ℝ) (σ s : ℝ) : ℝ × ℝ :=
  (curve γ (σ + s) + curve γ (σ - s)) / 2

/-- The chord of the symmetric family, as a complex number. -/
def symmChordC (γ : Circle → ℝ × ℝ) (σ s : ℝ) : ℂ := chordC γ (σ + s, σ - s)

/-- The squared capping radius of the symmetric family. -/
def symmA (γ : Circle → ℝ × ℝ) (σ s : ℝ) : ℝ :=
  (symmMid γ σ s).1 ^ 2 + (symmMid γ σ s).2 ^ 2 + Complex.normSq (symmChordC γ σ s)

/-- The capping radius of the symmetric family. -/
def symmR (γ : Circle → ℝ × ℝ) (σ s : ℝ) : ℝ := Real.sqrt (symmA γ σ s)

/-- The disk coordinate of the symmetric family. -/
def symmD (γ : Circle → ℝ × ℝ) (σ s : ℝ) : ℂ :=
  (((symmMid γ σ s).1 : ℂ) + ((symmMid γ σ s).2 : ℂ) * Complex.I) / ((symmR γ σ s : ℝ) : ℂ)

/-- The divided difference of the symmetric family, complexified. -/
def symmWC (γ : Circle → ℝ × ℝ) (σ s : ℝ) : ℂ := symmC (secantW (curve γ) (σ + s, σ - s))

/-- The squared unit chord direction of the symmetric family (the doubled direction of the
configuration), computed from the divided difference so that it extends smoothly to `s = 0`. -/
def symmE (γ : Circle → ℝ × ℝ) (σ s : ℝ) : ℂ :=
  (symmWC γ σ s * (((1 : ℝ) / ‖symmWC γ σ s‖ : ℝ) : ℂ)) ^ 2

/-- The capping data of the symmetric family. -/
def symmData (γ : Circle → ℝ × ℝ) (q : ℝ × ℝ) : ℝ × ℂ × ℂ :=
  (symmR γ q.1 q.2, symmD γ q.1 q.2, symmE γ q.1 q.2)

/-! ## Evenness in the opening parameter -/

lemma symmMid_neg (γ : Circle → ℝ × ℝ) (σ s : ℝ) : symmMid γ σ (-s) = symmMid γ σ s := by
  unfold symmMid
  rw [show σ + -s = σ - s from by ring, show σ - -s = σ + s from by ring, add_comm]

lemma symmChordC_neg (γ : Circle → ℝ × ℝ) (σ s : ℝ) :
    symmChordC γ σ (-s) = -symmChordC γ σ s := by
  unfold symmChordC
  rw [show σ + -s = σ - s from by ring, show σ - -s = σ + s from by ring]
  exact chordC_swap γ (σ + s) (σ - s)

lemma symmA_neg (γ : Circle → ℝ × ℝ) (σ s : ℝ) : symmA γ σ (-s) = symmA γ σ s := by
  simp only [symmA, symmMid_neg, symmChordC_neg, Complex.normSq_neg]

lemma symmR_neg (γ : Circle → ℝ × ℝ) (σ s : ℝ) : symmR γ σ (-s) = symmR γ σ s := by
  simp only [symmR, symmA_neg]

lemma symmD_neg (γ : Circle → ℝ × ℝ) (σ s : ℝ) : symmD γ σ (-s) = symmD γ σ s := by
  simp only [symmD, symmMid_neg, symmR_neg]

/-- The divided difference is symmetric in its two arguments. -/
lemma secantW_comm {F : ℝ → ℝ × ℝ} (hF : ContDiff ℝ 1 F) (a b : ℝ) :
    secantW F (a, b) = secantW F (b, a) := by
  rcases eq_or_ne a b with hab | hab
  · rw [hab]
  · have h1 : F a - F b = (a - b) • secantW F (a, b) := sub_eq_smul_secantW hF a b
    have h2 : F b - F a = (b - a) • secantW F (b, a) := sub_eq_smul_secantW hF b a
    have h3 : F b - F a = -(F a - F b) := by abel
    rw [h3, h1, show b - a = -(a - b) from by ring, neg_smul] at h2
    have h4 : (a - b) • secantW F (a, b) = (a - b) • secantW F (b, a) := neg_injective h2
    have h5 := congrArg (fun z : ℝ × ℝ => (a - b)⁻¹ • z) h4
    simp only [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hab), one_smul] at h5
    exact h5

lemma symmWC_neg (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (σ s : ℝ) : symmWC γ σ (-s) = symmWC γ σ s := by
  have hcurve : ContDiff ℝ 1 (curve γ) := contDiff_curve γ hγ
  unfold symmWC
  rw [show σ + -s = σ - s from by ring, show σ - -s = σ + s from by ring,
    secantW_comm hcurve (σ - s) (σ + s)]

lemma symmE_neg (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (σ s : ℝ) : symmE γ σ (-s) = symmE γ σ s := by
  simp only [symmE, symmWC_neg hγ]

lemma symmData_neg (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (σ s : ℝ) : symmData γ (σ, -s) = symmData γ (σ, s) := by
  simp only [symmData, symmR_neg, symmD_neg, symmE_neg hγ]

/-! ## Smoothness of the data -/

lemma contDiff_curve_top (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (curve γ) :=
  contMDiff_iff_contDiff.mp (hγ.contMDiff.comp contMDiff_circleExp)

lemma contDiff_symmC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (symmC : ℝ × ℝ → ℂ) := by
  have h : symmC = fun v : ℝ × ℝ => (v.1 : ℂ) + (v.2 : ℂ) * Complex.I := by
    funext v
    refine Complex.ext ?_ ?_ <;> simp [symmC]
  rw [h]
  exact ((Complex.ofRealCLM.contDiff.comp contDiff_fst).add
    ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const))

lemma contDiff_normSq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Complex.normSq : ℂ → ℝ) := by
  have h : (Complex.normSq : ℂ → ℝ) = fun z : ℂ => z.re ^ 2 + z.im ^ 2 := by
    funext z
    simp only [Complex.normSq_apply, sq]
  rw [h]
  exact (Complex.reCLM.contDiff.pow 2).add (Complex.imCLM.contDiff.pow 2)

lemma contDiff_symmMid (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => symmMid γ q.1 q.2) := by
  have hbase := contDiff_curve_top hγ
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => curve γ (q.1 + q.2)) :=
    hbase.comp (by fun_prop)
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => curve γ (q.1 - q.2)) :=
    hbase.comp (by fun_prop)
  have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => (1 / 2 : ℝ) • (curve γ (q.1 + q.2) + curve γ (q.1 - q.2))) :=
    ContDiff.const_smul (1 / 2 : ℝ) (h1.add h2)
  have heq : (fun q : ℝ × ℝ => symmMid γ q.1 q.2)
      = fun q : ℝ × ℝ => (1 / 2 : ℝ) • (curve γ (q.1 + q.2) + curve γ (q.1 - q.2)) := by
    funext q
    simp only [symmMid]
    refine Prod.ext ?_ ?_ <;> simp <;> ring
  rw [heq]
  exact h3

lemma contDiff_symmChordC (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => symmChordC γ q.1 q.2) := by
  have hbase := contDiff_curve_top hγ
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => curve γ (q.1 + q.2)) :=
    hbase.comp (by fun_prop)
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => curve γ (q.1 - q.2)) :=
    hbase.comp (by fun_prop)
  have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => symmC (γ (Circle.exp (q.1 + q.2)) - γ (Circle.exp (q.1 - q.2)))) :=
    contDiff_symmC.comp (h1.sub h2)
  simpa only [symmChordC, chordC_eq_symmC] using h3

lemma contDiff_symmA (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => symmA γ q.1 q.2) := by
  have hm := contDiff_symmMid hγ
  have hc := contDiff_symmChordC hγ
  have hsum : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ =>
      (symmMid γ q.1 q.2).1 ^ 2 + (symmMid γ q.1 q.2).2 ^ 2
        + Complex.normSq (symmChordC γ q.1 q.2)) :=
    ((hm.fst.pow 2).add (hm.snd.pow 2)).add (contDiff_normSq.comp hc)
  simpa only [symmA] using hsum

lemma symmA_nonneg (γ : Circle → ℝ × ℝ) (σ s : ℝ) : 0 ≤ symmA γ σ s := by
  have h1 : 0 ≤ (symmMid γ σ s).1 ^ 2 + (symmMid γ σ s).2 ^ 2 := by positivity
  have h2 : 0 ≤ Complex.normSq (symmChordC γ σ s) := Complex.normSq_nonneg _
  simp only [symmA]
  linarith

/-- **The squared capping radius of the symmetric family never vanishes** (as soon as the curve is an
embedding missing the origin): a vanishing would force the two endpoints of the chord to have the same
image and the midpoint to be `0`. -/
lemma symmA_ne_zero (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (σ s : ℝ) : symmA γ σ s ≠ 0 := by
  intro h
  have hchord : symmChordC γ σ s = 0 := by
    have h2 : Complex.normSq (symmChordC γ σ s) = 0 := by
      have h1 : 0 ≤ (symmMid γ σ s).1 ^ 2 + (symmMid γ σ s).2 ^ 2 := by positivity
      have h3 : 0 ≤ Complex.normSq (symmChordC γ σ s) := Complex.normSq_nonneg _
      simp only [symmA] at h
      linarith
    exact Complex.normSq_eq_zero.mp h2
  have heq : γ (Circle.exp (σ + s)) = γ (Circle.exp (σ - s)) := by
    have h4 : symmC (γ (Circle.exp (σ + s)) - γ (Circle.exp (σ - s))) = 0 := by
      simpa only [symmChordC, chordC_eq_symmC] using hchord
    exact sub_eq_zero.mp (symmC_eq_zero_iff.mp h4)
  have hmid : symmMid γ σ s = 0 := by
    have h1 : (symmMid γ σ s).1 = 0 := by
      have h2 : 0 ≤ Complex.normSq (symmChordC γ σ s) := Complex.normSq_nonneg _
      simp only [symmA] at h
      nlinarith [sq_nonneg (symmMid γ σ s).1, sq_nonneg (symmMid γ σ s).2]
    have h2 : (symmMid γ σ s).2 = 0 := by
      have h3 : 0 ≤ Complex.normSq (symmChordC γ σ s) := Complex.normSq_nonneg _
      simp only [symmA] at h
      nlinarith [sq_nonneg (symmMid γ σ s).1, sq_nonneg (symmMid γ σ s).2]
    exact Prod.ext h1 h2
  have hzero : γ (Circle.exp (σ + s)) = 0 := by
    have hthis := hmid
    simp only [symmMid, curve] at hthis
    rw [heq, add_self_div_two_prod] at hthis
    rw [heq]
    exact hthis
  exact hγne _ hzero

lemma contDiff_symmR (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => symmR γ q.1 q.2) := by
  have hA := contDiff_symmA hγ
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => Real.sqrt (symmA γ q.1 q.2)) :=
    hA.sqrt (fun q => symmA_ne_zero hγ hγne q.1 q.2)
  simpa only [symmR] using h

lemma contDiff_symmD (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => symmD γ q.1 q.2) := by
  have hm := contDiff_symmMid hγ
  have hr := contDiff_symmR hγ hγne
  have hnum : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => ((symmMid γ q.1 q.2).1 : ℂ) + ((symmMid γ q.1 q.2).2 : ℂ) * Complex.I) :=
    ((Complex.ofRealCLM.contDiff.comp hm.fst).add
      ((Complex.ofRealCLM.contDiff.comp hm.snd).mul contDiff_const))
  have hden : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => ((symmR γ q.1 q.2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hr
  have hne : ∀ q : ℝ × ℝ, ((symmR γ q.1 q.2 : ℝ) : ℂ) ≠ 0 := fun q => by
    intro h
    have hsq : symmR γ q.1 q.2 = 0 := Complex.ofReal_eq_zero.mp h
    rw [symmR] at hsq
    have hle : symmA γ q.1 q.2 ≤ 0 := Real.sqrt_eq_zero'.mp hsq
    exact symmA_ne_zero hγ hγne q.1 q.2 (le_antisymm hle (symmA_nonneg γ q.1 q.2))
  have heq : (fun q : ℝ × ℝ => symmD γ q.1 q.2)
      = fun q : ℝ × ℝ => (((symmMid γ q.1 q.2).1 : ℂ) + ((symmMid γ q.1 q.2).2 : ℂ) * Complex.I)
          * ((((symmR γ q.1 q.2 : ℝ)) : ℂ))⁻¹ := by
    funext q
    simp only [symmD, div_eq_mul_inv]
  rw [heq]
  exact hnum.mul (hden.inv hne)

lemma symmWC_zero (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (σ : ℝ) : symmWC γ σ 0 = symmC (deriv (curve γ) σ) := by
  simp only [symmWC, add_zero, sub_zero, secantW_self]

lemma contDiff_symmWC (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => symmWC γ q.1 q.2) := by
  have hcurve := contDiff_curve_top hγ
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (secantW (curve γ)) := contDiff_secantW hcurve
  have hpair : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => (q.1 + q.2, q.1 - q.2)) := by fun_prop
  have heq : (fun q : ℝ × ℝ => symmWC γ q.1 q.2)
      = fun q : ℝ × ℝ => symmC (secantW (curve γ) (q.1 + q.2, q.1 - q.2)) := by
    funext q
    simp only [symmWC]
  rw [heq]
  exact contDiff_symmC.comp (hs.comp hpair)

lemma symmWC_zero_ne_zero (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (σ : ℝ) : symmWC γ σ 0 ≠ 0 := by
  rw [symmWC_zero hγ σ]
  intro h
  exact curve_deriv_ne_zero γ hγ σ (symmC_eq_zero_iff.mp h)

lemma contDiffAt_symmE (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (σ₀ : ℝ) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => symmE γ q.1 q.2) (σ₀, 0) := by
  have hwc := contDiff_symmWC hγ
  have hne : symmWC γ σ₀ 0 ≠ 0 := symmWC_zero_ne_zero hγ σ₀
  have hnorm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => ‖symmWC γ q.1 q.2‖) (σ₀, 0) :=
    ContDiffAt.norm ℂ hwc.contDiffAt hne
  have hdiv : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => (1 : ℝ) / ‖symmWC γ q.1 q.2‖) (σ₀, 0) :=
    ContDiffAt.div (f := fun _ : ℝ × ℝ => (1 : ℝ)) contDiffAt_const hnorm
      (norm_ne_zero_iff.mpr hne)
  have hmul : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => symmWC γ q.1 q.2 * (((1 : ℝ) / ‖symmWC γ q.1 q.2‖ : ℝ) : ℂ)) (σ₀, 0) :=
    hwc.contDiffAt.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp (σ₀, 0) hdiv)
  simpa only [symmE] using hmul.pow 2

/-! ## The data of the symmetric family is the data of the chord `(σ+s, σ-s)` -/

lemma symmA_eq_stripA (γ : Circle → ℝ × ℝ) (σ s : ℝ) :
    symmA γ σ s = stripA γ (mk2 (σ + s) (σ - s)) := by
  simp only [symmA, stripA, symmMid, stripMid, symmChordC, stripChord, curve, mk2_apply_zero,
    mk2_apply_one]

lemma symmMid_eq_stripMid (γ : Circle → ℝ × ℝ) (σ s : ℝ) :
    symmMid γ σ s = stripMid γ (mk2 (σ + s) (σ - s)) := by
  simp only [symmMid, stripMid, curve, mk2_apply_zero, mk2_apply_one]

lemma symmR_eq_stripR (γ : Circle → ℝ × ℝ) (σ s : ℝ) :
    symmR γ σ s = stripR γ (mk2 (σ + s) (σ - s)) := by
  rw [symmR, stripR, symmA_eq_stripA]

lemma symmD_eq_stripD (γ : Circle → ℝ × ℝ) (σ s : ℝ) :
    symmD γ σ s = stripD γ (mk2 (σ + s) (σ - s)) := by
  simp only [symmD, stripD, symmMid_eq_stripMid, symmR_eq_stripR]

lemma symmR_pos (hγne : ∀ x : Circle, γ x ≠ 0) (σ s : ℝ) : 0 < symmR γ σ s := by
  rw [symmR_eq_stripR]
  exact stripR_pos hγne _

lemma symmD_norm_le_one (γ : Circle → ℝ × ℝ) (σ s : ℝ) : ‖symmD γ σ s‖ ≤ 1 := by
  rw [symmD_eq_stripD]
  exact stripD_le_one γ _

lemma symmE_norm (γ : Circle → ℝ × ℝ) (σ s : ℝ) (h : symmWC γ σ s ≠ 0) :
    ‖symmE γ σ s‖ = 1 := by
  have hne : ‖symmWC γ σ s‖ ≠ 0 := norm_ne_zero_iff.mpr h
  have hpos : 0 ≤ 1 / ‖symmWC γ σ s‖ := div_nonneg zero_le_one (norm_nonneg _)
  simp only [symmE, norm_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos]
  rw [mul_one_div_cancel hne, one_pow]

/-! ## The direction is the square of the undoubled chord direction -/

private lemma mul_one_div_norm_eq_div (z : ℂ) :
    z * (((1 : ℝ) / ‖z‖ : ℝ) : ℂ) = z / ((‖z‖ : ℝ) : ℂ) := by
  rw [div_eq_mul_inv]
  congr 1
  rw [Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_inv, one_mul]

private lemma div_norm_sq_eq_div_conj (z : ℂ) (hz : z ≠ 0) :
    (z / ((‖z‖ : ℝ) : ℂ)) ^ 2 = z / star z := by
  have hnorm : ((‖z‖ : ℝ) : ℂ) ^ 2 = z * star z := by
    have h1 : ((‖z‖ : ℝ) : ℂ) ^ 2 = ((‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [h1, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj z, starRingEnd_apply]
  have hstar : star z ≠ 0 := by rw [star_ne_zero]; exact hz
  rw [div_pow, hnorm]
  field_simp

private lemma div_star_smul_ofReal (c : ℝ) (w : ℂ) (hc : c ≠ 0) (hw : w ≠ 0) :
    (((c : ℂ) * w) / star ((c : ℂ) * w)) = w / star w := by
  have hc' : ((c : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have hstar : star w ≠ 0 := by rw [star_ne_zero]; exact hw
  rw [star_mul, Complex.star_def, Complex.conj_ofReal, starRingEnd_apply]
  field_simp

/-- **The squared unit chord direction of the symmetric family is the square of the undoubled chord
direction.**  The divided difference `symmWC` is the chord divided by the (real) offset `2s`, so the
two unit directions differ by a real scalar, which does not change the square. -/
lemma symmE_eq_chordUnitDir_sq (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (σ s : ℝ) (hs : s ≠ 0) (h : symmWC γ σ s ≠ 0) :
    symmE γ σ s = (chordUnitDir γ (σ + s, σ - s)) ^ 2 := by
  have hchord : chordC γ (σ + s, σ - s) = ((2 * s : ℝ) : ℂ) * symmWC γ σ s := by
    have hsub : γ (Circle.exp (σ + s)) - γ (Circle.exp (σ - s))
        = ((2 * s : ℝ)) • secantW (curve γ) (σ + s, σ - s) := by
      have h' := sub_eq_smul_secantW (contDiff_curve γ hγ) (σ + s) (σ - s)
      rwa [show σ + s - (σ - s) = 2 * s from by ring] at h'
    rw [chordC_eq_symmC, hsub, symmC_smul, symmWC]
  have hc : (2 * s : ℝ) ≠ 0 := by
    intro hc
    exact hs (by linarith [mul_eq_zero.mp hc])
  have hprod_ne : ((2 * s : ℝ) : ℂ) * symmWC γ σ s ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hc) h
  simp only [chordUnitDir]
  rw [hchord]
  rw [div_norm_sq_eq_div_conj _ hprod_ne, div_star_smul_ofReal (2 * s) (symmWC γ σ s) hc h,
    ← div_norm_sq_eq_div_conj (symmWC γ σ s) h, ← mul_one_div_norm_eq_div]
  simp only [symmE]

end Work.Drive.Neutral
