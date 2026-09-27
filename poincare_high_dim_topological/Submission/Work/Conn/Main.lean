import Mathlib
import Submission.Work.Conn.Basic
import Submission.Work.Conn.Approx.exists_contDiff_near
import Submission.Work.Conn.Sard.exists_sphere_notMem_range

/-!
# Connectivity of spheres: `πₖ(𝕊ⁿ) = 0` for `k < n`

The main result of this file is `Work.Conn.nullhomotopic_sphere_of_lt`: every continuous map
`𝕊ᵏ → 𝕊ⁿ` with `k < n` is null-homotopic.

The proof has two analytic inputs, isolated here as explicit hypotheses of the auxiliary theorem
`Work.Conn.nullhomotopic_sphere_of_lt_aux` so that the homotopy-theoretic part can be verified
independently of them:

* `Approx` : every continuous `𝕊ᵏ → ℝᵐ` is uniformly approximated by the restriction of a smooth
  ambient map (`Work.Conn.Approx.exists_contDiff_near`);
* `Sard` : Sard's theorem in the form "the normalised image of such a smooth map misses a point"
  (`Work.Conn.Sard.exists_sphere_notMem_range`).

Given those, the argument is: approximate `f` by a smooth `P` with `3/4 ≤ ‖P x‖ ≤ 5/4` on `𝕊ᵏ`
(so the normalisation `g x = ‖P x‖⁻¹ • P x` is a well defined map `𝕊ᵏ → 𝕊ⁿ`); `g` misses a point
of `𝕊ⁿ`, hence is null-homotopic; and `f` is homotopic to `g` because `f x` and `g x` are at
distance `< 1/2`, so never antipodal.
-/

open Metric (sphere closedBall)
open ContinuousMap

namespace Work.Conn

variable {k n : ℕ}

/-- Elementary real identity used in `nullhomotopic_sphere_of_lt_aux`. -/
theorem abs_one_sub_inv_mul (r : ℝ) (hr : 0 < r) : |1 - r⁻¹| * r = |r - 1| := by
  have h : (1 - r⁻¹) * r = r - 1 := by
    field_simp
  calc |1 - r⁻¹| * r = |1 - r⁻¹| * |r| := by rw [abs_of_pos hr]
    _ = |(1 - r⁻¹) * r| := (abs_mul _ _).symm
    _ = |r - 1| := by rw [h]

/-- **`πₖ(𝕊ⁿ) = 0` for `k < n`**, in the form in which the two analytic ingredients are explicit
hypotheses (see the module docstring). -/
theorem nullhomotopic_sphere_of_lt_aux
    (approx : ∀ (k m : ℕ) (f : C(Sph k, EuclideanSpace ℝ (Fin m))) {ε : ℝ}, 0 < ε →
      ∃ P : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin m),
        ContDiff ℝ ⊤ P ∧ ∀ x : Sph k, dist (P x) (f x) < ε)
    (sard : ∀ {k n : ℕ}, k < n →
      ∀ {P : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (n + 1))},
      ContDiff ℝ ⊤ P → (∀ x : Sph k, (3 : ℝ) / 4 ≤ ‖P x‖) →
      (∀ x : Sph k, ‖P x‖ ≤ (5 : ℝ) / 4) →
      ∃ q : Sph n, ∀ x : Sph k, (‖P x‖)⁻¹ • P x ≠ (q : EuclideanSpace ℝ (Fin (n + 1))))
    (hkn : k < n) (f : C(Sph k, Sph n)) : f.Nullhomotopic := by
  let f' : C(Sph k, EuclideanSpace ℝ (Fin (n + 1))) :=
    ⟨fun x => (f x : EuclideanSpace ℝ (Fin (n + 1))),
      continuous_subtype_val.comp f.continuous⟩
  obtain ⟨P, hP, hPnear⟩ := approx k (n + 1) f' (ε := 1 / 4) (by norm_num)
  have hclose : ∀ x : Sph k, dist (P x) (f x : EuclideanSpace ℝ (Fin (n + 1))) < 1 / 4 :=
    fun x => hPnear x
  -- upper and lower bounds for `‖P x‖` on the sphere
  have hub : ∀ x : Sph k, ‖P x‖ < (5 : ℝ) / 4 := by
    intro x
    have h1 : ‖P x‖ ≤ ‖P x - (f x : EuclideanSpace ℝ (Fin (n + 1)))‖ +
        ‖(f x : EuclideanSpace ℝ (Fin (n + 1)))‖ := by
      calc ‖P x‖ = ‖(P x - (f x : EuclideanSpace ℝ (Fin (n + 1)))) +
            (f x : EuclideanSpace ℝ (Fin (n + 1)))‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    have h2 : ‖P x - (f x : EuclideanSpace ℝ (Fin (n + 1)))‖ < 1 / 4 := by
      simpa [dist_eq_norm] using hclose x
    rw [norm_coe_Sph] at h1
    linarith
  have hlb : ∀ x : Sph k, (3 : ℝ) / 4 < ‖P x‖ := by
    intro x
    have h1 : ‖(f x : EuclideanSpace ℝ (Fin (n + 1)))‖ ≤
        ‖(f x : EuclideanSpace ℝ (Fin (n + 1))) - P x‖ + ‖P x‖ := by
      calc ‖(f x : EuclideanSpace ℝ (Fin (n + 1)))‖ =
            ‖((f x : EuclideanSpace ℝ (Fin (n + 1))) - P x) + P x‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    have h2 : ‖(f x : EuclideanSpace ℝ (Fin (n + 1))) - P x‖ < 1 / 4 := by
      simpa [dist_eq_norm, norm_sub_rev] using hclose x
    rw [norm_coe_Sph] at h1
    linarith
  -- the Sard input: the normalised map misses a point
  obtain ⟨q, hq⟩ := sard hkn hP (fun x => (hlb x).le) (fun x => (hub x).le)
  -- the normalised map
  have hPne : ∀ x : Sph k, P x ≠ 0 := fun x => by
    intro hzero
    have := hlb x
    rw [hzero, norm_zero] at this
    norm_num at this
  let G : Sph k → EuclideanSpace ℝ (Fin (n + 1)) := fun x => (‖P x‖)⁻¹ • P x
  have hGmem : ∀ x : Sph k, G x ∈ Sph n := fun x => mem_Sph_iff.mpr (norm_inv_norm_smul (hPne x))
  have hGcont : Continuous G := by
    have hc : Continuous fun x : Sph k => ‖P x‖ := hP.continuous.norm.comp continuous_subtype_val
    exact (hc.inv₀ (fun x => norm_ne_zero_iff.mpr (hPne x))).smul
      (hP.continuous.comp continuous_subtype_val)
  let g : C(Sph k, Sph n) := ⟨fun x => ⟨G x, hGmem x⟩, Continuous.subtype_mk hGcont hGmem⟩
  have hgcoe : ∀ x : Sph k, (g x : EuclideanSpace ℝ (Fin (n + 1))) = G x := fun x => rfl
  -- `g` misses `q`, hence is null-homotopic
  have hg_null : g.Nullhomotopic :=
    nullhomotopic_of_ne g q (fun x hx => hq x (by simpa [hgcoe, G] using congrArg Subtype.val hx))
  -- `f` and `g` are never antipodal
  have hfg : f.Homotopic g := by
    refine homotopic_of_antipodalFree fun x => ?_
    intro hanti
    have hanti' : (f x : EuclideanSpace ℝ (Fin (n + 1))) = -G x := by simpa [hgcoe] using hanti
    have hdist : ‖(f x : EuclideanSpace ℝ (Fin (n + 1))) - G x‖ = 2 := by
      have : (f x : EuclideanSpace ℝ (Fin (n + 1))) - G x =
          (2 : ℝ) • (f x : EuclideanSpace ℝ (Fin (n + 1))) := by
        rw [hanti', two_smul]
        abel
      rw [this, norm_smul, Real.norm_eq_abs, norm_coe_Sph]
      norm_num
    have hubd : ‖(f x : EuclideanSpace ℝ (Fin (n + 1))) - P x‖ < 1 / 4 := by
      rw [← dist_eq_norm, dist_comm]
      exact hclose x
    have hPgd : ‖P x - G x‖ = |‖P x‖ - 1| := by
      have hr : (0 : ℝ) < ‖P x‖ := lt_trans (by norm_num) (hlb x)
      have hsub : P x - G x = (1 - (‖P x‖)⁻¹) • P x := by
        rw [show G x = (‖P x‖)⁻¹ • P x from rfl, sub_smul, one_smul]
      rw [hsub, norm_smul, Real.norm_eq_abs]
      exact abs_one_sub_inv_mul (‖P x‖) hr
    have hPg1 : |‖P x‖ - 1| < 1 / 4 := by
      have h3 : |‖P x‖ - 1| ≤ ‖P x - (f x : EuclideanSpace ℝ (Fin (n + 1)))‖ := by
        simpa using abs_norm_sub_norm_le (P x) (f x : EuclideanSpace ℝ (Fin (n + 1)))
      have h4 : ‖P x - (f x : EuclideanSpace ℝ (Fin (n + 1)))‖ < 1 / 4 := by
        simpa [dist_eq_norm] using hclose x
      linarith
    have htri : ‖(f x : EuclideanSpace ℝ (Fin (n + 1))) - G x‖ ≤
        ‖(f x : EuclideanSpace ℝ (Fin (n + 1))) - P x‖ + ‖P x - G x‖ := by
      calc ‖(f x : EuclideanSpace ℝ (Fin (n + 1))) - G x‖ =
            ‖((f x : EuclideanSpace ℝ (Fin (n + 1))) - P x) + (P x - G x)‖ := by
            rw [show (f x : EuclideanSpace ℝ (Fin (n + 1))) - G x =
              ((f x : EuclideanSpace ℝ (Fin (n + 1))) - P x) + (P x - G x) by abel]
        _ ≤ _ := norm_add_le _ _
    rw [hPgd] at htri
    linarith
  obtain ⟨y, hy⟩ := hg_null
  exact ⟨y, hfg.trans hy⟩

/-- **`πₖ(𝕊ⁿ) = 0` for `k < n`.**  Every continuous map `𝕊ᵏ → 𝕊ⁿ` with `k < n` is
null-homotopic.

Informally: approximate `f` by the restriction of a smooth `P : ℝᵏ⁺¹ → ℝⁿ⁺¹` within `1/4`, so
that `3/4 ≤ ‖P x‖ ≤ 5/4` on `𝕊ᵏ`; the normalisation `g x = ‖P x‖⁻¹ • P x` is a map `𝕊ᵏ → 𝕊ⁿ`
which misses a point of `𝕊ⁿ` (Sard, codimension `n - k ≥ 1`), hence is null-homotopic, and `f`
is homotopic to `g` because antipodal-free maps into a sphere are homotopic. -/
theorem nullhomotopic_sphere_of_lt {k n : ℕ} (hkn : k < n) (f : C(Sph k, Sph n)) :
    f.Nullhomotopic :=
  nullhomotopic_sphere_of_lt_aux
    (fun k m f ε hε => Approx.exists_contDiff_near k m f hε)
    (fun hkn P hP hlo hhi => Sard.exists_sphere_notMem_range hkn hP hlo hhi)
    hkn f

end Work.Conn
