import Mathlib

/-!
# The cut plane: complement of finitely many rays pointing away from 0

For a complex number `c ≠ 0` define the *ray* away from the origin

    ray c := {t • c : ℂ | t : ℝ, 1 ≤ t}

(the half line starting at `c` and going in the direction of `c`, away from
`0`).  For a finite set `C` of such points, the *cut plane* is the complement
of the union of these rays:

    cutPlane C := {w : ℂ | ∀ c ∈ C, w ∉ ray c}

This is the domain on which the square root `√G` of the engine's polynomial
`G(w) = ∏ (1 - z² w)(1 - z⁴ w)` will be continued: all roots of `G` (the
points `1/z²`, `1/z⁴`) lie on the rays, so `G` does not vanish on
`cutPlane C`, and `0 ∈ cutPlane C`.

## The key topological fact: `cutPlane C` is simply connected

`cutPlane C` is *star-shaped with respect to `0`*: if `w ∉ ray c` and
`0 ≤ t ≤ 1`, then `t • w ∉ ray c` as well.  Indeed, if `t • w = s • c` with
`s ≥ 1` and `t ∈ (0, 1]`, then `w = (s / t) • c` with `s / t ≥ 1`, so
`w ∈ ray c`; and if `t = 0` then `s • c = 0`, forcing `c = 0`.  Since a
star-shaped (nonempty) set is contractible
(`StarConvex.contractibleSpace`) and a contractible space is simply connected
(`SimplyConnectedSpace.ofContractible`), we get
`IsSimplyConnected (cutPlane C)`.

We also record that `0 ∈ cutPlane C` (needs `c ≠ 0` for every `c ∈ C`),
that `cutPlane C` is open (finite union of closed rays), and that some ball
around `0` is contained in `cutPlane C` (each ray starts at distance `‖c‖`
from `0`).

## The role of this module in the engine

`Submission.Continuation.sqrt_continuation` turns any open simply connected
`U ∋ 0` with a ball around `0` on which `G` is nonvanishing into the
holomorphic square root with integer Taylor coefficients.  This module
supplies the domain: with `C` the finite set of roots of `G`, the
`cutPlane C` above has exactly those properties.  (The remaining input --
`G ≠ 0` on `cutPlane C` -- needs the product formula for `G`, proved in a
later module.)

You may add helper lemmas.  Do NOT change the statements of the declarations
below.  No sorries may remain in this file.
-/

noncomputable section

open scoped Real Topology

namespace Submission.Rays

/-- The ray `{t • c | t ≥ 1}` starting at `c ≠ 0` and pointing away from `0`. -/
def ray (c : ℂ) : Set ℂ := {w : ℂ | ∃ t : ℝ, 1 ≤ t ∧ w = t • c}

/-- The complement of the union of the rays over a finite set `C`:
`{w | ∀ c ∈ C, w ∉ ray c}`. -/
def cutPlane (C : Finset ℂ) : Set ℂ := {w : ℂ | ∀ c ∈ C, w ∉ ray c}

/-- If `c ≠ 0` then `0` is not on the ray `ray c`. -/
lemma zero_not_mem_ray {c : ℂ} (hc : c ≠ 0) : (0 : ℂ) ∉ ray c := by
  intro h
  rcases h with ⟨t, ht, hz⟩
  have ht0 : t ≠ 0 := by
    intro ht0
    subst t
    norm_num at ht
  have hsmul : t • (c : ℂ) = 0 := by simpa using hz.symm
  exact hc ((smul_eq_zero.mp hsmul).resolve_left ht0)

/-- The origin lies in the cut plane (when no `c` is `0`). -/
lemma zero_mem_cutPlane {C : Finset ℂ} (hC0 : ∀ c ∈ C, c ≠ 0) :
    (0 : ℂ) ∈ cutPlane C := by
  rw [cutPlane]
  exact fun c hc => zero_not_mem_ray (hC0 c hc)

/-- Each ray is closed. -/
lemma isClosed_ray (c : ℂ) : IsClosed (ray c) := by
  by_cases hc : c = 0
  · subst c
    have h : ray (0 : ℂ) = ({0} : Set ℂ) := by
      ext w
      constructor
      · rintro ⟨t, ht, hz⟩
        simp at hz
        exact hz
      · rintro rfl
        exact ⟨1, le_rfl, by simp⟩
    rw [h]
    exact isClosed_singleton
  · let T : Set ℂ := {z : ℂ | z.im = 0} ∩ {z : ℂ | (1 : ℝ) ≤ z.re}
    have hTclosed : IsClosed T := by
      have hA : IsClosed {z : ℂ | z.im = 0} := isClosed_singleton.preimage Complex.continuous_im
      have hB : IsClosed {z : ℂ | (1 : ℝ) ≤ z.re} := isClosed_Ici.preimage Complex.continuous_re
      exact hA.inter hB
    have hiff : ∀ w : ℂ, w ∈ ray c ↔ (w / c).im = 0 ∧ (1 : ℝ) ≤ (w / c).re := by
      intro w
      constructor
      · rintro ⟨t, ht, hz⟩
        have hdiv : w / c = (t : ℂ) := by
          rw [hz]
          have htc : t • c = (t : ℂ) * c := by rfl
          rw [htc]
          exact (div_eq_iff hc).2 rfl
        constructor
        · simp [hdiv]
        · rw [hdiv]
          simpa [ht]
      · rintro ⟨him, hge⟩
        let t : ℝ := (w / c).re
        have hwdiv : w / c = (t : ℂ) := by
          apply Complex.ext <;> simp [t, him]
        have hw : w = (t : ℂ) * c := by
          have h := congrArg (fun z : ℂ => z * c) hwdiv
          rwa [div_mul_cancel₀ w hc] at h
        refine ⟨t, ?_, ?_⟩
        · simpa [t] using hge
        · simpa using hw
    rw [show ray c = (fun w : ℂ => w / c) ⁻¹' T by
      ext w
      simp [T, hiff w]]
    exact hTclosed.preimage (continuous_id.div continuous_const (fun _ => hc))

/-- The cut plane is open (finite intersection of complements of closed rays). -/
lemma isOpen_cutPlane (C : Finset ℂ) : IsOpen (cutPlane C) := by
  classical
  induction C using Finset.induction with
  | empty =>
      simpa [cutPlane] using (isOpen_univ : IsOpen (univ : Set ℂ))
  | @insert c C' hcnotin ih =>
      have hEq : cutPlane (insert c C') = cutPlane C' ∩ (ray c)ᶜ := by
        ext w
        simp [cutPlane, and_comm]
      rw [hEq]
      exact ih.inter (isClosed_ray c).isOpen_compl

/-- The cut plane is star-shaped with respect to `0`. -/
lemma starConvex_cutPlane {C : Finset ℂ} (hC0 : ∀ c ∈ C, c ≠ 0) :
    StarConvex ℝ (0 : ℂ) (cutPlane C) := by
  intro w hw a b ha hb hab
  rw [smul_zero, zero_add]
  rw [cutPlane]
  intro c hc
  intro hmem
  rcases hmem with ⟨s, hs1, hseq⟩
  by_cases hb0 : b = 0
  · have hzero : s • (c : ℂ) = 0 := by
      have := hseq.symm
      simpa [hb0] using this
    have hs0 : s ≠ 0 := by linarith
    exact (hC0 c hc) ((smul_eq_zero.mp hzero).resolve_left hs0)
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hb_le_one : b ≤ 1 := by linarith
    have hw_eq : w = (b⁻¹ * s) • c := by
      have h := congrArg (fun z : ℂ => b⁻¹ • z) hseq
      rwa [smul_smul, smul_smul, inv_mul_cancel₀ hb0, one_smul] at h
    have hge : (1 : ℝ) ≤ b⁻¹ * s := by
      have hone : (1 : ℝ) ≤ s / b := (one_le_div hbpos).2 (le_trans hb_le_one hs1)
      rwa [div_eq_mul_inv, mul_comm] at hone
    exact (hw c hc) ⟨b⁻¹ * s, hge, hw_eq⟩

/-- **The cut plane is simply connected** (star-shaped, hence contractible,
hence simply connected). -/
theorem isSimplyConnected_cutPlane {C : Finset ℂ} (hC0 : ∀ c ∈ C, c ≠ 0) :
    IsSimplyConnected (cutPlane C) := by
  have hne : (cutPlane C).Nonempty := ⟨(0 : ℂ), zero_mem_cutPlane hC0⟩
  haveI : ContractibleSpace (cutPlane C) := (starConvex_cutPlane hC0).contractibleSpace hne
  change SimplyConnectedSpace (cutPlane C)
  infer_instance

/-- A ball around the origin is contained in the cut plane. -/
theorem exists_ball_subset_cutPlane {C : Finset ℂ} (hC0 : ∀ c ∈ C, c ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball (0 : ℂ) ρ ⊆ cutPlane C := by
  exact (Metric.isOpen_iff.mp (isOpen_cutPlane C) (0 : ℂ) (zero_mem_cutPlane hC0))

end Submission.Rays

end
