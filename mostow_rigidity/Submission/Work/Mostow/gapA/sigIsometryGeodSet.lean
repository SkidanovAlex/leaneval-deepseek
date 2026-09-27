import Mathlib
import Submission.Work.Mostow.gapA.tubeDefs

/-!
# `sig` is an arc-length coordinate on the geodesic `geodSet a b`

`Work.Mostow.gapA.sig a b u = (β_b u − β_a u)/2` is the Busemann coordinate along the
geodesic with endpoints `a ≠ b` in `Sph 3`.  On the geodesic itself it is an arc-length
coordinate, so it is an isometry of the geodesic with the Euclidean line:

`hdist u v = |sig a b u − sig a b v|` for `u, v ∈ geodSet a b`.

The proof is a computation in the hyperboloid model.  Writing `L = gcL a b` and
`Lu = lev a u` (so that `u ∈ geodSet a b ↔ Lu · Lv = L`, `mem_geodSet_iff`), an element of
the geodesic has `hlift u = gcA • nvec a + gcB • nvec b` (`geodSet_lift_span`), whence

`mink (hlift u) (hlift v) = (gcA u · gcB v + gcB u · gcA v) · (⟪a,b⟫ − 1)`

and, because `gcA u = lev b u /(2L) = 1/(2 Lu)`, `gcB u = lev a u /(2L) = Lu/(2L)`,

`−mink (hlift u) (hlift v) = (Lv/Lu + Lu/Lv)/2 = cosh (hdist u v)`.

On the other hand `sig a b u = log L / 2 − log Lu`, so
`sig a b u − sig a b v = log (Lv/Lu)` and `cosh (sig a b u − sig a b v) = (Lv/Lu + Lu/Lv)/2`
as well.  Hence `cosh (hdist u v) = cosh (sig a b u − sig a b v)`, and `arcosh ∘ cosh = |·|`.
-/

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-- `busemann` is the logarithm of the horospherical level `lev`. -/
lemma sig_busemann_log (ξ u : E 3) : busemann ξ u = Real.log (lev ξ u) := rfl

/-- On the geodesic `geodSet a b`, the Busemann coordinate `sig a b ·` is
`log (gcL a b) / 2 − log (lev a ·)`. -/
lemma sig_eq_of_mem (a b u : E 3) (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b)
    (hu : u ∈ geodSet a b) :
    sig a b u = Real.log (gcL a b) / 2 - Real.log (lev a u) := by
  have hLu : lev a u * lev b u = gcL a b := (mem_geodSet_iff a b ha hb u).mp hu
  have hLpos : 0 < gcL a b := gcL_pos a b ha hb hab
  have hLu_ne : lev a u ≠ 0 := ne_of_gt (lev_pos a ha u)
  have hbu : lev b u = gcL a b / lev a u := by
    rw [eq_div_iff hLu_ne, mul_comm]; exact hLu
  have hlogb : Real.log (lev b u) = Real.log (gcL a b) - Real.log (lev a u) := by
    rw [hbu, Real.log_div (ne_of_gt hLpos) hLu_ne]
  simp only [sig, sig_busemann_log, hlogb]
  ring

/-- On the geodesic, `hdist` agrees with the difference of the Busemann coordinates:
`cosh (hdist u v) = cosh (sig a b u − sig a b v)`. -/
lemma cosh_hdist_eq_cosh_sig (a b u v : E 3) (ha : a ∈ Sph 3) (hb : b ∈ Sph 3)
    (hab : a ≠ b) (hu : u ∈ geodSet a b) (hv : v ∈ geodSet a b) :
    Real.cosh (hdist u v) = Real.cosh (sig a b u - sig a b v) := by
  have hLu : lev a u * lev b u = gcL a b := (mem_geodSet_iff a b ha hb u).mp hu
  have hLv : lev a v * lev b v = gcL a b := (mem_geodSet_iff a b ha hb v).mp hv
  have hLpos : 0 < gcL a b := gcL_pos a b ha hb hab
  have hLu_ne : lev a u ≠ 0 := ne_of_gt (lev_pos a ha u)
  have hLv_ne : lev a v ≠ 0 := ne_of_gt (lev_pos a ha v)
  have hbu : lev b u = gcL a b / lev a u := by
    rw [eq_div_iff hLu_ne, mul_comm]; exact hLu
  have hbv : lev b v = gcL a b / lev a v := by
    rw [eq_div_iff hLv_ne, mul_comm]; exact hLv
  have h2L : inner ℝ a b - 1 = -(2 * gcL a b) := by have := two_gcL a b; linarith
  -- the Minkowski pairing of the two hyperboloid points
  have hexp : mink (hlift u) (hlift v)
      = (gcA a b u * gcB a b v + gcB a b u * gcA a b v) * (inner ℝ a b - 1) := by
    rw [geodSet_lift_span a b ha hb hab hu, geodSet_lift_span a b ha hb hab hv, mink_expand2,
      mink_nvec_self' ha, mink_nvec_self' hb, mink_nvec_nvec' a b, mink_nvec_nvec' b a,
      real_inner_comm b a]
    ring
  have hkey : (gcA a b u * gcB a b v + gcB a b u * gcA a b v) * (inner ℝ a b - 1)
      = -((lev a v / lev a u + lev a u / lev a v) / 2) := by
    simp only [gcA, gcB, hbu, hbv, h2L]
    field_simp
  have hcoshdist : Real.cosh (hdist u v) = (lev a v / lev a u + lev a u / lev a v) / 2 := by
    rw [cosh_hdist']
    have hml := mink_hlift_hlift (n := 3) u v
    linarith
  have hsigu := sig_eq_of_mem a b u ha hb hab hu
  have hsigv := sig_eq_of_mem a b v ha hb hab hv
  have hsub : sig a b u - sig a b v = Real.log (lev a v) - Real.log (lev a u) := by
    rw [hsigu, hsigv]; ring
  have hposuv : 0 < lev a v / lev a u := div_pos (lev_pos a ha v) (lev_pos a ha u)
  have hcoshsig : Real.cosh (sig a b u - sig a b v)
      = (lev a v / lev a u + lev a u / lev a v) / 2 := by
    rw [hsub, ← Real.log_div hLv_ne hLu_ne, Real.cosh_log hposuv]
    field_simp
  rw [hcoshdist, hcoshsig]

/-- On the geodesic with endpoints `a ≠ b`, `sig a b ·` is an arc-length coordinate:
the hyperbolic distance of two of its points is the absolute difference of their
coordinates. -/
theorem sigIsometryGeodSet (hA : Submission.Mostow.POActionProp 3)
    (hI : Submission.Mostow.HypIsometryProp 3)
    (a b : Submission.Mostow.E 3) (ha : a ∈ Submission.Mostow.Sph 3) (hb : b ∈ Submission.Mostow.Sph 3)
    (hab : a ≠ b) :
    ∀ u v : Submission.Mostow.E 3, u ∈ Work.Mostow.geodSet a b → v ∈ Work.Mostow.geodSet a b →
      Submission.Mostow.hdist u v = |Work.Mostow.gapA.sig a b u - Work.Mostow.gapA.sig a b v| := by
  intro u v hu hv
  calc hdist u v = Real.arcosh (Real.cosh (hdist u v)) :=
        (Real.arcosh_cosh (hdist_nonneg' u v)).symm
    _ = Real.arcosh (Real.cosh (sig a b u - sig a b v)) := by
        rw [cosh_hdist_eq_cosh_sig a b u v ha hb hab hu hv]
    _ = |sig a b u - sig a b v| := arcosh_cosh_abs' _

end

end Work.Mostow.gapA
