import Mathlib
import Submission.Work.Mostow.nfDefs

/-!
# The horospherical orthogonal projection `horoProj ξ` in coordinates

For `ξ ∈ Sph n` (so `θ = (ξ,1)` and `η = (ξ,-1)` are the two null vectors spanning `V`),
a hyperboloid point `hlift u` decomposes as

  `hlift u = wvec (wc ξ u) + (⟨hlift u, η⟩/2) θ − (lev ξ u/2) η`,

i.e. into its `V^⊥`-part `(wc ξ u, 0)`, where `wc ξ u = u − ⟪u,ξ⟫ξ` is the flat coordinate
of `u` on the horosphere at `ξ`, and its `V`-part.  Consequently the orthogonal projection
`horoProj ξ` onto `V^⊥` extracts exactly the flat coordinate, and on `V^⊥` — where `mform`
coincides with the Euclidean form — it is the identity.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

@[simp] lemma hspat_wvec (y : E n) : hspat (wvec y) = y := rfl

@[simp] lemma htime_wvec (y : E n) : htime (wvec y) = 0 := rfl

/-- `mform` of `(y,0)` against an arbitrary vector is the Euclidean pairing of `y` with the
spatial part. -/
lemma mform_wvec_left (y : E n) (x : Fin n ⊕ Fin 1 → ℝ) :
    mform (wvec y) x = inner ℝ y (hspat x) := by
  rw [mform_eq]; simp

theorem nfHoroProj {n : ℕ} {ξ : Submission.Mostow.E n} (hξ : ξ ∈ Submission.Mostow.Sph n) :
    (∀ u : Submission.Mostow.E n,
      Submission.Mostow.hlift u =
        Work.Mostow.wvec (Work.Mostow.wc ξ u)
          + (Work.Mostow.mform (Submission.Mostow.hlift u) (Work.Mostow.horoEta ξ) / 2) •
              Work.Mostow.theta ξ
          - (Work.Mostow.lev ξ u / 2) • Work.Mostow.horoEta ξ) ∧
    (∀ u : Submission.Mostow.E n,
      Work.Mostow.horoProj ξ (Submission.Mostow.hlift u) = Work.Mostow.wvec (Work.Mostow.wc ξ u)) ∧
    (∀ u : Submission.Mostow.E n,
      Work.Mostow.hspat (Work.Mostow.horoProj ξ (Submission.Mostow.hlift u)) =
        Work.Mostow.wc ξ u) ∧
    (∀ y : Submission.Mostow.E n, inner ℝ y ξ = 0 →
      Work.Mostow.horoProj ξ (Work.Mostow.wvec y) = Work.Mostow.wvec y) ∧
    (∀ y : Submission.Mostow.E n,
      Work.Mostow.mform (Work.Mostow.wvec y) (Work.Mostow.theta ξ) = inner ℝ y ξ) ∧
    (∀ y z : Submission.Mostow.E n, inner ℝ y ξ = 0 → inner ℝ z ξ = 0 →
      Work.Mostow.mform (Work.Mostow.wvec y) (Work.Mostow.wvec z) = inner ℝ y z) ∧
    (∀ S : Fin n ⊕ Fin 1 → ℝ, Work.Mostow.horoProj ξ S = S →
      inner ℝ (Work.Mostow.hspat S) ξ = 0) := by
  -- (1) the decomposition of `hlift u` along `V ⊕ V^⊥`
  have h1 : ∀ u : E n, hlift u
      = wvec (wc ξ u) + (mform (hlift u) (horoEta ξ) / 2) • theta ξ
        - (lev ξ u / 2) • horoEta ξ := by
    intro u
    rw [mform_hlift_eta]
    ext z
    rcases z with i | j
    · simp only [hlift, wvec, wc, theta, horoEta, lev, tpart, Sum.elim_inl, Pi.add_apply,
        Pi.sub_apply, Pi.smul_apply, WithLp.ofLp_sub, WithLp.ofLp_smul]
      ring
    · fin_cases j
      simp only [hlift, wvec, wc, theta, horoEta, lev, tpart, Sum.elim_inr, Pi.add_apply,
        Pi.sub_apply, Pi.smul_apply, WithLp.ofLp_sub, WithLp.ofLp_smul]
      ring
  -- (2) the projection of `hlift u` is the flat coordinate
  have h2 : ∀ u : E n, horoProj ξ (hlift u) = wvec (wc ξ u) := by
    intro u
    rw [horoProj, mform_hlift_theta', mform_hlift_eta]
    ext z
    rcases z with i | j
    · simp only [hlift, wvec, wc, theta, horoEta, tpart, Sum.elim_inl, Pi.sub_apply,
        Pi.smul_apply, WithLp.ofLp_sub, WithLp.ofLp_smul]
      ring
    · fin_cases j
      simp only [hlift, wvec, wc, theta, horoEta, tpart, Sum.elim_inr, Pi.sub_apply,
        Pi.smul_apply, WithLp.ofLp_sub, WithLp.ofLp_smul]
      ring
  -- (4) `horoProj` is the identity on `ξ^⊥ ⊕ {0}`
  have h4 : ∀ y : E n, inner ℝ y ξ = 0 → horoProj ξ (wvec y) = wvec y := by
    intro y hy
    rw [horoProj, mform_wvec_left y (theta ξ), mform_wvec_left y (horoEta ξ),
      hspat_theta, hspat_horoEta, hy]
    simp
  -- (5) `mform` of `(y,0)` against `θ`
  have h5 : ∀ y : E n, mform (wvec y) (theta ξ) = inner ℝ y ξ := by
    intro y
    rw [mform_wvec_left, hspat_theta]
  -- (6) on `V^⊥` the Minkowski form is the Euclidean form
  have h6 : ∀ y z : E n, inner ℝ y ξ = 0 → inner ℝ z ξ = 0 →
      mform (wvec y) (wvec z) = inner ℝ y z := by
    intro y z _ _
    rw [mform_wvec_left, hspat_wvec]
  -- (7) a fixed vector of `horoProj ξ` is orthogonal to `ξ`
  have h7 : ∀ S : Fin n ⊕ Fin 1 → ℝ, horoProj ξ S = S → inner ℝ (hspat S) ξ = 0 := by
    intro S hS
    have ht : htime S = 0 := htime_eq_zero_of_horoProj ξ hξ hS
    have hm : mform S (theta ξ) = 0 := by
      have hh := mform_horoProj_theta ξ hξ S
      rwa [hS] at hh
    rw [mform_eq, hspat_theta, htime_theta, ht] at hm
    simpa using hm
  exact ⟨h1, h2, fun u => by rw [h2 u, hspat_wvec], h4, h5, h6, h7⟩

end

end Work.Mostow
