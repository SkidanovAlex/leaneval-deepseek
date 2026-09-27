import Mathlib
import Submission.Work.Mostow.HLBasics

/-!
# Escape of the free ray to a boundary point from every compact set

Let `Γ ≤ PO n 1`, `ζ ∈ Sph n`, and suppose the `Γ`-orbit of the base point misses the horoball
`horoball ζ s` (i.e. `busemann ζ (γ • 0) ≥ s` for every `γ ∈ Γ`).  Then the `Γ`-orbit of the
geodesic ray `t ↦ sinh t • ζ` issued from `0` towards `ζ` escapes every compact subset of `ℍⁿ`
as `t → ∞`, uniformly over `Γ`.

The mechanism is elementary.  Write `p_t = sinh t • ζ`, so that `busemann ζ p_t = -t`
(`busemann_ray_sinh`), and recall that the Busemann function is `1`-Lipschitz
(`BusemannLipschitz`).  Hence for every point `v`

`busemann ζ v + t ≤ |busemann ζ v - busemann ζ p_t| ≤ hdist v p_t`.

Given `γ ∈ Γ` put `v = γ⁻¹ • 0`; the freeness hypothesis gives `busemann ζ v ≥ s`, and applying the
isometry `γ⁻¹` to the pair `(γ • p_t, 0)` gives `hdist (γ • p_t) 0 = hdist v p_t`.  Therefore

`hdist 0 (γ • p_t) = hdist v p_t ≥ busemann ζ v + t ≥ s + t`,

so `γ • p_t` leaves the ball of radius `R` around `0` as soon as `t > R - s`, whenever `K` is
contained in that ball (`exists_hdist_bound_of_compact`).

## Contents

* `busemann_ray_sinh` — `busemann ζ (sinh t • ζ) = -t` for `ζ ∈ Sph n`;
* `exists_hdist_bound_of_compact` — a compact set is at bounded hyperbolic distance from `0`;
* `busemann_add_le_hdist_ray` — `busemann ζ v + t ≤ hdist v (sinh t • ζ)`;
* `escape_of_horoball` — the requested statement.
-/

namespace Work.Mostow

open LeanEval.Geometry.MostowRigidity Submission.Mostow

noncomputable section

variable {n : ℕ}

/-- The Busemann function along the ray issued from the base point towards `ζ`. -/
lemma busemann_ray_sinh (ζ : E n) (hζ : ζ ∈ Sph n) (t : ℝ) :
    busemann ζ (Real.sinh t • ζ) = -t := by
  have hnorm : ‖ζ‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hζ
  have h1 : tpart (Real.sinh t • ζ) = Real.cosh t := tpart_sinh_smul ζ t hnorm
  have h2 : inner ℝ (Real.sinh t • ζ) ζ = Real.sinh t := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hnorm]; ring
  rw [busemann, h1, h2, Real.cosh_sub_sinh, Real.log_exp]

/-- A compact set lies at bounded hyperbolic distance from the base point. -/
lemma exists_hdist_bound_of_compact (hI : HypIsometryProp n) (K : Set (E n)) (hK : IsCompact K) :
    ∃ R : ℝ, ∀ u ∈ K, hdist (0 : E n) u ≤ R := by
  have hcont : ContinuousOn (fun x : E n => hdist (0 : E n) x) K :=
    ((HypIsoData.ofProp hI).continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
  obtain ⟨M, hM⟩ := hK.bddAbove_image hcont
  exact ⟨M, fun x hx => hM ⟨x, hx, rfl⟩⟩

/-- Distance lower bound along the ray towards `ζ`: hop on the horospheres. -/
lemma busemann_add_le_hdist_ray (ζ : E n) (hζ : ζ ∈ Sph n) (v : E n) (t : ℝ) :
    busemann ζ v + t ≤ hdist v (Real.sinh t • ζ) := by
  have h := BusemannLipschitz n ζ hζ v (Real.sinh t • ζ)
  rw [busemann_ray_sinh ζ hζ t] at h
  have h' : |busemann ζ v + t| ≤ hdist v (Real.sinh t • ζ) := by
    simpa only [sub_eq_add_neg, neg_neg] using h
  exact le_trans (le_abs_self _) h'

/-- **Escape from compact sets along a free ray.**  If no `Γ`-translate of the base point lies in
the horoball `horoball ζ s`, then the `Γ`-orbit of the ray `t ↦ sinh t • ζ` escapes every compact
set as `t → ∞`, uniformly in `Γ`. -/
theorem escape_of_horoball (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (ζ : E n) (hζ : ζ ∈ Sph n) (s : ℝ)
    (hfree : ∀ γ : Γ, (γ : PO n 1) • (0 : E n) ∉ horoball ζ s)
    (K : Set (E n)) (hK : IsCompact K) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∀ γ : Γ, (γ : PO n 1) • (Real.sinh t • ζ) ∉ K := by
  obtain ⟨R, hR⟩ := exists_hdist_bound_of_compact hI K hK
  have hsym : ∀ u v : E n, hdist u v = hdist v u := hI.2.1
  have hiso : ∀ (g : PO n 1) (u v : E n), hdist (g • u) (g • v) = hdist u v := hI.2.2.2.2.2.2.1
  have hcomp : ∀ (g h : PO n 1) (u : E n), (g * h) • u = g • (h • u) := hA.2.2.2.2.1
  have hone : ∀ u : E n, (1 : PO n 1) • u = u := hA.2.2.2.1
  refine ⟨R - s + 1, fun t ht γ => ?_⟩
  intro hmem
  -- the inverse translate of the base point and its Busemann level
  have hbus : s ≤ busemann ζ (((γ⁻¹ : Γ) : PO n 1) • (0 : E n)) := by
    have h := hfree γ⁻¹
    rw [horoball] at h
    exact not_lt.mp h
  -- the inverse translate brings the ray point back to the ray
  have hfix : ((γ⁻¹ : Γ) : PO n 1) • ((γ : PO n 1) • (Real.sinh t • ζ)) = Real.sinh t • ζ := by
    rw [← hcomp]
    have h1 : (((γ⁻¹ : Γ) : PO n 1)) * ((γ : Γ) : PO n 1) = 1 := by simp
    rw [h1, hone]
  -- hyperbolic distance is invariant
  have hisostep : hdist ((γ : PO n 1) • (Real.sinh t • ζ)) (0 : E n)
      = hdist (((γ⁻¹ : Γ) : PO n 1) • (0 : E n)) (Real.sinh t • ζ) := by
    calc hdist ((γ : PO n 1) • (Real.sinh t • ζ)) (0 : E n)
        = hdist (((γ⁻¹ : Γ) : PO n 1) • ((γ : PO n 1) • (Real.sinh t • ζ)))
            (((γ⁻¹ : Γ) : PO n 1) • (0 : E n)) := (hiso _ _ _).symm
      _ = hdist (Real.sinh t • ζ) (((γ⁻¹ : Γ) : PO n 1) • (0 : E n)) := by rw [hfix]
      _ = hdist (((γ⁻¹ : Γ) : PO n 1) • (0 : E n)) (Real.sinh t • ζ) := hsym _ _
  have hRle : hdist (0 : E n) ((γ : PO n 1) • (Real.sinh t • ζ)) ≤ R := hR _ hmem
  rw [hsym (0 : E n) ((γ : PO n 1) • (Real.sinh t • ζ)), hisostep] at hRle
  have hkey : busemann ζ (((γ⁻¹ : Γ) : PO n 1) • (0 : E n)) + t
      ≤ hdist (((γ⁻¹ : Γ) : PO n 1) • (0 : E n)) (Real.sinh t • ζ) :=
    busemann_add_le_hdist_ray ζ hζ _ t
  linarith [hbus, hkey, hRle, ht]

end

end Work.Mostow
