/-
Copyright: subproject `Submission/Work/FatouParabolic2/` of `mandelbar_not_path_connected`.
-/
import Mathlib
import Submission.Work.FatouParabolic2.AffineConj
import Submission.Work.FatouParabolic2.Defs
import Submission.Work.FatouParabolic2.aff_iterate_conj
import Submission.Work.FatouParabolic2.aff_enters_Pa

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology
open Filter Set

namespace Work.FatouParabolic2

noncomputable section

/-- The one-step conjugacy: on the ball where the affine chart `aff z₀ lam` relates `f` and `F`,
the chart intertwines a single application of `f` with a single application of `F`. -/
theorem aff_transport_step {f F : ℂ → ℂ} {z₀ lam : ℂ} {r : ℝ} {A : Set ℂ}
    (hlam : lam ≠ 0) (hA : A ⊆ Metric.ball 0 r)
    (hconj : ∀ u : ℂ, u ∈ Metric.ball 0 r → f u = (F (z₀ + lam * u) - z₀) / lam)
    {u : ℂ} (hu : u ∈ A) :
    F (aff z₀ lam u) = aff z₀ lam (f u) := by
  rw [← aff_affInv z₀ lam hlam (F (aff z₀ lam u))]
  congr 1
  exact (hconj u (hA hu)).symm

/-- **Transport of petal data along an affine chart.**  Let `pd` be petal data for the fixed
point `0` of `f`, whose petal lies in the ball `Metric.ball 0 r`, and suppose that on that ball the
germ `f` is the affine conjugate of `F` at `z₀` with scale `lam ≠ 0`:
`f u = (F (z₀ + lam * u) - z₀) / lam`.  Then `F` has petal data at `z₀`, with petal
`(fun u => z₀ + lam * u) '' pd.Pa` and Fatou coordinate `fun z => pd.φa ((z - z₀) / lam)`.

Every field transports: openness and preconnectedness of the petal under the affine
homeomorphism; `z₀ ∉ Pa` because `0 ∉ pd.Pa`; invariance, the convergence of orbits to `z₀` and
the Abel equation along the conjugacy (all iterates of the point stay in `ball 0 r ∪ pd.Pa`);
`enters`: given `F^n z → z₀` never equal to `z₀`, put `u_n := (F^n z - z₀) / lam`; for `n` large
`‖u_n‖ < r` and `f u_n = u_{n+1}` (the conjugacy), so the `f`-orbit of some `u_N` converges to `0`
without attaining it and `pd.enters_Pa` produces an iterate in `pd.Pa`; injectivity and
holomorphy of the coordinate are inherited from `pd` composed with the affine bijection, and the
strip-image property is `pd.image_strip` read through the bijection. -/
theorem transport_petalData {f F : ℂ → ℂ} {z₀ lam : ℂ} {r : ℝ}
    (pd : PetalData f 0) (hlam : lam ≠ 0) (hPa : pd.Pa ⊆ Metric.ball 0 r)
    (hconj : ∀ u : ℂ, u ∈ Metric.ball 0 r → f u = (F (z₀ + lam * u) - z₀) / lam) :
    ∃ pd' : PetalData F z₀, pd'.Pa = (fun u : ℂ => z₀ + lam * u) '' pd.Pa ∧
      pd'.φa = fun z : ℂ => pd.φa ((z - z₀) / lam) := by
  refine ⟨{ Pa := aff z₀ lam '' pd.Pa
            φa := fun z : ℂ => pd.φa (affInv z₀ lam z)
            isOpen_Pa := ?_
            isPreconnected_Pa := ?_
            z₀_not_mem := ?_
            mapsTo_Pa := ?_
            tendsto_Pa := ?_
            enters_Pa := ?_
            φa_diff := ?_
            φa_shift := ?_
            φa_inj := ?_
            image_strip := ?_ }, rfl, rfl⟩
  · -- the petal is the preimage of the original petal under the continuous inverse chart
    rw [aff_image_eq_preimage z₀ lam hlam]
    exact pd.isOpen_Pa.preimage (continuous_affInv z₀ lam)
  · -- preconnectedness is preserved by the continuous chart
    exact pd.isPreconnected_Pa.image (aff z₀ lam) (continuous_aff z₀ lam).continuousOn
  · -- `z₀` is not in the petal because `0` is not in `pd.Pa`
    intro h
    rw [mem_aff_image_iff z₀ lam hlam pd.Pa z₀, affInv_self] at h
    exact pd.z₀_not_mem h
  · -- forward invariance, through the one-step conjugacy
    rintro z ⟨u, hu, rfl⟩
    exact ⟨f u, pd.mapsTo_Pa hu, (aff_transport_step hlam hPa hconj hu).symm⟩
  · -- orbits in the petal converge to `z₀`
    rintro z ⟨u, hu, rfl⟩
    have hiter := aff_iterate_conj hlam hPa hconj pd.mapsTo_Pa hu
    have h : Tendsto (fun n : ℕ => aff z₀ lam (f^[n] u)) atTop (𝓝 z₀) := by
      have h0 : Tendsto (aff z₀ lam) (𝓝 (0 : ℂ)) (𝓝 z₀) := by
        simpa using (continuous_aff z₀ lam).tendsto 0
      exact h0.comp (pd.tendsto_Pa u hu)
    simpa only [hiter] using h
  · -- the `enters` property transports
    intro z hz hne
    exact aff_enters_Pa pd hlam hPa hconj hz hne
  · -- differentiability of the coordinate, composed with the inverse chart
    have h1 : DifferentiableOn ℂ (affInv z₀ lam) (aff z₀ lam '' pd.Pa) :=
      (differentiable_affInv z₀ lam).differentiableOn
    have h2 : MapsTo (affInv z₀ lam) (aff z₀ lam '' pd.Pa) pd.Pa :=
      fun z hz => (mem_aff_image_iff z₀ lam hlam pd.Pa z).mp hz
    exact pd.φa_diff.comp h1 h2
  · -- the Abel equation, read through the conjugacy
    rintro z ⟨u, hu, rfl⟩
    show pd.φa (affInv z₀ lam (F (aff z₀ lam u))) =
      pd.φa (affInv z₀ lam (aff z₀ lam u)) + 1
    rw [aff_transport_step hlam hPa hconj hu]
    simp only [affInv_aff z₀ lam hlam]
    exact pd.φa_shift u hu
  · -- injectivity of the coordinate
    rintro z1 hz1 z2 hz2 heq
    obtain ⟨u1, hu1, rfl⟩ := hz1
    obtain ⟨u2, hu2, rfl⟩ := hz2
    have heq' : pd.φa (affInv z₀ lam (aff z₀ lam u1)) =
        pd.φa (affInv z₀ lam (aff z₀ lam u2)) := heq
    rw [affInv_aff z₀ lam hlam, affInv_aff z₀ lam hlam] at heq'
    exact congrArg (aff z₀ lam) (pd.φa_inj hu1 hu2 heq')
  · -- the strip-image property is inherited verbatim
    intro B hB
    obtain ⟨C, hC⟩ := pd.image_strip B hB
    refine ⟨C, fun τ hτ hτB => ?_⟩
    obtain ⟨u, hu, hφ⟩ := hC τ hτ hτB
    exact ⟨aff z₀ lam u, ⟨u, hu, rfl⟩, by rw [affInv_aff z₀ lam hlam]; exact hφ⟩

end

end Work.FatouParabolic2
