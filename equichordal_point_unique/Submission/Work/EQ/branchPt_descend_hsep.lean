import Mathlib
import Submission.Work.EQ.bp_aux
import Submission.Work.EQ.branchPt_germ_stabiliser
import Submission.Work.Topology.meromorphicAt_rotation_eventually_eq

open Filter _root_.Topology
open Complex Metric

namespace Work.EQ

/-- **Separation for the descended branch.**

If `β` is the descent of the branch `σ` along a primitive `d`-th root of unity `ω` of maximal order
`d` (`hmax` says that every rotation preserving the germ of `σ` has `d`-th power one, and `hinv`
that `ω` preserves it on the whole branch disc), then no rotation `ω' ≠ 1` with
`(ω') ^ (2 ^ N / d) = 1` has collisions with `β` accumulating at `0`: there is a punctured disc on
which `β (ω' t) ≠ β t`.

Route: if not, then by `Work.Topology.meromorphicAt_rotation_eventually_eq` applied to each of the
finitely many coordinates of `β`, the identity `β (ω' t) = β t` holds on a punctured disc; choosing
`τ` with `τ ^ d = ω'` and using `β (t ^ d) = branchPt σ t` gives `Work.EQ.GermInv a c u₀ R σ τ`,
so `τ ^ d = 1` by `hmax`, whence `ω' = 1`, a contradiction. -/
theorem branchPt_descend_hsep {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ}
    (hR : 0 < R) (hc : AnalyticOnNhd ℂ c (Metric.ball u₀ R)) {σ : Fin N → Bool}
    {d : ℕ} (hd : 0 < d) (hdvd : d ∣ 2 ^ N) {ω : ℂ} (hω : ω ^ d = 1)
    (hprim : ∀ m : ℕ, 0 < m → m < d → ω ^ m ≠ 1)
    (hmax : ∀ τ : ℂ, Work.EQ.GermInv a c u₀ R σ τ → τ ^ d = 1)
    (hinv : ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < Work.EQ.rhoFin' a c u₀ R N →
      Work.EQ.branchPt a c u₀ R σ (ω * t) = Work.EQ.branchPt a c u₀ R σ t)
    {β : ℂ → Fin (N + 1) → ℂ × ℂ}
    (han : ∀ j, AnalyticOnNhd ℂ (fun s => β s j)
      (Metric.ball (0 : ℂ) ((Work.EQ.rhoFin' a c u₀ R N) ^ d) \ {0}))
    (hmer : ∀ j, MeromorphicAt (fun s => β s j) 0)
    (hβ : ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < Work.EQ.rhoFin' a c u₀ R N →
      β (t ^ d) = Work.EQ.branchPt a c u₀ R σ t) :
    ∀ ω' : ℂ, ω' ^ (2 ^ N / d) = 1 → ω' ≠ 1 →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ (Work.EQ.rhoFin' a c u₀ R N) ^ d ∧
        ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < δ → β (ω' * t) ≠ β t := by
  classical
  intro ω' hω' hω'ne
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ δ, 0 < δ → δ ≤ ρ ^ d → ∃ t, 0 < ‖t‖ ∧ ‖t‖ < δ ∧ β (ω' * t) = β t`.
  have hρ : 0 < rhoFin' a c u₀ R N := rhoFin'_pos hR hc
  have hρd : 0 < (rhoFin' a c u₀ R N) ^ d := pow_pos hρ d
  have hkpos : 0 < 2 ^ N / d := Nat.div_pos (Nat.le_of_dvd (by positivity) hdvd) hd
  have hω'0 : ω' ≠ 0 := by
    intro h0
    rw [h0, zero_pow hkpos.ne'] at hω'
    exact one_ne_zero hω'.symm
  -- Collisions accumulate at `0` (at *every* scale, not just below `ρ ^ d`).
  have hacc : ∀ δ : ℝ, 0 < δ → ∃ s : ℂ, 0 < ‖s‖ ∧ ‖s‖ < δ ∧ β (ω' * s) = β s := by
    intro δ hδ
    obtain ⟨t, ht0, htlt, heq⟩ :=
      hcon (min δ ((rhoFin' a c u₀ R N) ^ d)) (lt_min hδ hρd) (min_le_right _ _)
    exact ⟨t, ht0, lt_of_lt_of_le htlt (min_le_left _ _), heq⟩
  -- Coordinatewise meromorphy at `0` of the descent `β`.
  have hmer1 : ∀ j : Fin (N+1), MeromorphicAt (fun s => (β s j).1) 0 := by
    intro j
    obtain ⟨n, hn⟩ := hmer j
    refine ⟨n, ?_⟩
    have h1' : AnalyticAt ℂ (fun z : ℂ => z ^ n • (β z j).1) 0 :=
      AnalyticAt.comp (x := (0:ℂ)) (g := fun p : ℂ × ℂ => p.1)
        (f := fun z : ℂ => z ^ n • β z j) analyticAt_fst (by simpa using hn)
    simpa [sub_zero] using h1'
  have hmer2 : ∀ j : Fin (N+1), MeromorphicAt (fun s => (β s j).2) 0 := by
    intro j
    obtain ⟨n, hn⟩ := hmer j
    refine ⟨n, ?_⟩
    have h1' : AnalyticAt ℂ (fun z : ℂ => z ^ n • (β z j).2) 0 :=
      AnalyticAt.comp (x := (0:ℂ)) (g := fun p : ℂ × ℂ => p.2)
        (f := fun z : ℂ => z ^ n • β z j) analyticAt_snd (by simpa using hn)
    simpa [sub_zero] using h1'
  -- Each coordinate of `β` agrees with its rotation on a punctured disc.
  have hfst : ∀ j : Fin (N+1), ∃ δ : ℝ, 0 < δ ∧
      ∀ s : ℂ, 0 < ‖s‖ → ‖s‖ < δ → (β (ω' * s) j).1 = (β s j).1 := by
    intro j
    obtain ⟨δ, hδ, hδeq⟩ :=
      Work.Topology.meromorphicAt_rotation_eventually_eq hω'0 (hmer1 j) (by
        intro δ hδ
        obtain ⟨s, hs0, hslt, heq⟩ := hacc δ hδ
        exact ⟨s, hs0, hslt, by show (β (ω' * s) j).1 = (β s j).1; rw [heq]⟩)
    exact ⟨δ, hδ, hδeq⟩
  have hsnd : ∀ j : Fin (N+1), ∃ δ : ℝ, 0 < δ ∧
      ∀ s : ℂ, 0 < ‖s‖ → ‖s‖ < δ → (β (ω' * s) j).2 = (β s j).2 := by
    intro j
    obtain ⟨δ, hδ, hδeq⟩ :=
      Work.Topology.meromorphicAt_rotation_eventually_eq hω'0 (hmer2 j) (by
        intro δ hδ
        obtain ⟨s, hs0, hslt, heq⟩ := hacc δ hδ
        exact ⟨s, hs0, hslt, by show (β (ω' * s) j).2 = (β s j).2; rw [heq]⟩)
    exact ⟨δ, hδ, hδeq⟩
  -- Combine the two components at each level.
  have hJ : ∀ j : Fin (N+1), ∃ δ : ℝ, 0 < δ ∧
      (∀ s : ℂ, 0 < ‖s‖ → ‖s‖ < δ → (β (ω' * s) j).1 = (β s j).1) ∧
      (∀ s : ℂ, 0 < ‖s‖ → ‖s‖ < δ → (β (ω' * s) j).2 = (β s j).2) := by
    intro j
    obtain ⟨δ1, hδ1, he1⟩ := hfst j
    obtain ⟨δ2, hδ2, he2⟩ := hsnd j
    exact ⟨min δ1 δ2, lt_min hδ1 hδ2,
      fun s hs0 hslt => he1 s hs0 (lt_of_lt_of_le hslt (min_le_left _ _)),
      fun s hs0 hslt => he2 s hs0 (lt_of_lt_of_le hslt (min_le_right _ _))⟩
  -- Combine the finitely many levels.
  obtain ⟨δβ, hδβ0, hδβeq⟩ : ∃ δ : ℝ, 0 < δ ∧
      ∀ s : ℂ, 0 < ‖s‖ → ‖s‖ < δ → β (ω' * s) = β s := by
    refine ⟨(Finset.univ : Finset (Fin (N+1))).inf' Finset.univ_nonempty
      (fun j => (hJ j).choose), ?_, ?_⟩
    · exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun j _ => (hJ j).choose_spec.1)
    · intro s hs0 hslt
      funext j
      obtain ⟨h1, h2⟩ := (hJ j).choose_spec.2
      exact Prod.ext (h1 s hs0 (lt_of_lt_of_le hslt (Finset.inf'_le _ (Finset.mem_univ j))))
        (h2 s hs0 (lt_of_lt_of_le hslt (Finset.inf'_le _ (Finset.mem_univ j))))
  -- A `d`-th root `τ` of `ω'` (`ω'` is nonzero since it is a positive power of `1`).
  obtain ⟨τ, hτ⟩ : ∃ τ : ℂ, τ ^ d = ω' :=
    ⟨ω' ^ ((d : ℂ)⁻¹), Complex.cpow_nat_inv_pow ω' hd.ne'⟩
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    rw [zero_pow hd.ne'] at hτ
    exact hω'0 hτ.symm
  -- `τ` preserves the germ of the branch.
  have hgerm : GermInv a c u₀ R σ τ := by
    refine ⟨min (rhoFin' a c u₀ R N) (min ((rhoFin' a c u₀ R N) / (1 + ‖τ‖)) (min 1 δβ)),
      lt_min hρ (lt_min (div_pos hρ (by positivity)) (lt_min one_pos hδβ0)),
      min_le_left _ _, ?_⟩
    intro t ht0 htlt
    have htρ : ‖t‖ < rhoFin' a c u₀ R N := lt_of_lt_of_le htlt (min_le_left _ _)
    have hlt2 : ‖t‖ < min ((rhoFin' a c u₀ R N) / (1 + ‖τ‖)) (min 1 δβ) :=
      lt_of_lt_of_le htlt (min_le_right _ _)
    have hτtρ : ‖τ * t‖ < rhoFin' a c u₀ R N := by
      rw [norm_mul]
      have h1 : ‖t‖ < (rhoFin' a c u₀ R N) / (1 + ‖τ‖) :=
        lt_of_lt_of_le hlt2 (min_le_left _ _)
      have hτpos : 0 < ‖τ‖ := norm_pos_iff.mpr hτ0
      calc ‖τ‖ * ‖t‖ < ‖τ‖ * ((rhoFin' a c u₀ R N) / (1 + ‖τ‖)) :=
              mul_lt_mul_of_pos_left h1 hτpos
        _ = (rhoFin' a c u₀ R N) * (‖τ‖ / (1 + ‖τ‖)) := by ring
        _ < (rhoFin' a c u₀ R N) * 1 := by
              refine mul_lt_mul_of_pos_left ?_ hρ
              rw [div_lt_one (by positivity)]
              linarith [norm_nonneg τ]
        _ = rhoFin' a c u₀ R N := mul_one _
    have hτt0 : 0 < ‖τ * t‖ := by
      rw [norm_mul]
      exact mul_pos (norm_pos_iff.mpr hτ0) (norm_pos_iff.mpr (norm_ne_zero_iff.mp ht0.ne'))
    have htpow0 : 0 < ‖t ^ d‖ := by rw [norm_pow]; positivity
    have htpowlt : ‖t ^ d‖ < δβ := by
      rw [norm_pow]
      have h1 : ‖t‖ < 1 :=
        lt_of_lt_of_le hlt2 (le_trans (min_le_right _ _) (min_le_left _ _))
      have h2 : ‖t‖ < δβ :=
        lt_of_lt_of_le hlt2 (le_trans (min_le_right _ _) (min_le_right _ _))
      calc ‖t‖ ^ d ≤ ‖t‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg t) h1.le (by omega)
        _ = ‖t‖ := pow_one _
        _ < δβ := h2
    calc branchPt a c u₀ R σ (τ * t)
        = β ((τ * t) ^ d) := (hβ (τ * t) hτt0 hτtρ).symm
      _ = β (ω' * t ^ d) := by rw [mul_pow, hτ]
      _ = β (t ^ d) := hδβeq (t ^ d) htpow0 htpowlt
      _ = branchPt a c u₀ R σ t := hβ t ht0 htρ
  have hτd : τ ^ d = 1 := hmax τ hgerm
  exact hω'ne (by rw [← hτ, hτd])

end Work.EQ
