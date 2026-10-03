import Mathlib

/-!
# The punctured disc is connected

Mathlib has `isConnected_ball` and `isPathConnected_ball` but nothing for a ball with its centre
removed, and that little lemma is exactly what the "plane criterion for unbounded domains" needs
(removing an interior point of a connected set leaves it connected — hence the complement of the
Möbius image of a domain can stay connected).

The proof has no point-set content: `{z : 0 < ‖z - c‖ ∧ ‖z - c‖ < r}` is the image of the connected
set `(0,r) × ℝ` under the continuous map `(s,t) ↦ ↑s · exp (↑t * I) + c`, using the polar form
`Complex.norm_mul_exp_arg_mul_I`.
-/

open Set Metric
open scoped Topology

namespace Work.Analysis.Complex

noncomputable section

/-- **The punctured disc at `c` is connected.** -/
theorem isConnected_punctured_ball_at (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IsConnected {z : ℂ | 0 < ‖z - c‖ ∧ ‖z - c‖ < r} := by
  have hcont : Continuous fun q : ℝ × ℝ => (q.1 : ℂ) * Complex.exp ((q.2 : ℂ) * Complex.I) + c := by
    fun_prop
  have himg : (fun q : ℝ × ℝ => (q.1 : ℂ) * Complex.exp ((q.2 : ℂ) * Complex.I) + c) ''
        ((Set.Ioo (0 : ℝ) r) ×ˢ (Set.univ : Set ℝ))
      = {z : ℂ | 0 < ‖z - c‖ ∧ ‖z - c‖ < r} := by
    ext z
    constructor
    · rintro ⟨⟨s, t⟩, ⟨hs, -⟩, rfl⟩
      simp only [Set.mem_ofPred_eq]
      have h1 : ((s : ℂ) * Complex.exp ((t : ℂ) * Complex.I) + c) - c
          = (s : ℂ) * Complex.exp ((t : ℂ) * Complex.I) := by ring
      rw [h1, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs.1]
      exact hs
    · intro hz
      refine ⟨(‖z - c‖, (z - c).arg), ⟨⟨hz.1, hz.2⟩, Set.mem_univ _⟩, ?_⟩
      have h := Complex.norm_mul_exp_arg_mul_I (z - c)
      show (‖z - c‖ : ℂ) * Complex.exp ((z - c).arg * Complex.I) + c = z
      rw [h]
      ring
  rw [← himg]
  exact ((isConnected_Ioo hr).prod isConnected_univ).image _ hcont.continuousOn

/-! ## Removing an interior point -/

/-- The two-piece contradiction used in `isConnected_diff_singleton_of_mem_interior`: if the
punctured disc around `p` lies in the piece `u`, and the piece `(F \ {p}) ∩ v` is nonempty, then the
closed pieces `u`, `v` cannot separate `F \ {p}`. -/
private lemma no_separation_of_diff_singleton {F : Set ℂ} (hF : IsConnected F) {p : ℂ} {r : ℝ}
    (hr : 0 < r) (hball : ball p r ⊆ F) {u v : Set ℂ} (hucl : IsClosed u) (hvcl : IsClosed v)
    (hsub : F \ {p} ⊆ u ∪ v) (hdisj : (F \ {p}) ∩ (u ∩ v) = ∅)
    (hpb : ∀ z : ℂ, 0 < ‖z - p‖ → ‖z - p‖ < r → z ∈ u)
    (hBne : ((F \ {p}) ∩ v).Nonempty) : False := by
  have hpb_sub : {z : ℂ | 0 < ‖z - p‖ ∧ ‖z - p‖ < r} ⊆ F := fun z hz =>
    hball (by rw [mem_ball, dist_eq_norm]; exact hz.2)
  have hpbd : ∀ z : ℂ, 0 < ‖z - p‖ → ‖z - p‖ < r → z ∈ F \ {p} := fun z h1 h2 =>
    ⟨hpb_sub ⟨h1, h2⟩, fun h => absurd h1 (by rw [h]; simp)⟩
  set A : Set ℂ := (F \ {p}) ∩ u with hAdef
  set B : Set ℂ := (F \ {p}) ∩ v with hBdef
  have hpbA : {z : ℂ | 0 < ‖z - p‖ ∧ ‖z - p‖ < r} ⊆ A := fun z hz =>
    ⟨hpbd z hz.1 hz.2, hpb z hz.1 hz.2⟩
  -- `p` is a limit point of the punctured disc, hence of `A`
  have hp_pb : p ∈ closure {z : ℂ | 0 < ‖z - p‖ ∧ ‖z - p‖ < r} := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨p + ((min r ε / 2 : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
    · have h1 : (p + ((min r ε / 2 : ℝ) : ℂ)) - p = ((min r ε / 2 : ℝ) : ℂ) := by ring
      have h2 : 0 < min r ε / 2 := half_pos (lt_min hr hε)
      rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h2]
      linarith [min_le_left r ε]
    · have h1 : (p + ((min r ε / 2 : ℝ) : ℂ)) - p = ((min r ε / 2 : ℝ) : ℂ) := by ring
      have h2 : 0 < min r ε / 2 := half_pos (lt_min hr hε)
      rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h2]
      nlinarith [min_le_left r ε, hr]
    · have h2 : 0 < min r ε / 2 := half_pos (lt_min hr hε)
      have h3 : dist p (p + ((min r ε / 2 : ℝ) : ℂ)) = min r ε / 2 := by
        rw [dist_eq_norm]
        have h4 : p - (p + ((min r ε / 2 : ℝ) : ℂ)) = -((min r ε / 2 : ℝ) : ℂ) := by ring
        rw [h4, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h2]
      rw [h3]
      nlinarith [min_le_right r ε, hε]
  have hpA : p ∈ closure A := closure_mono hpbA hp_pb
  -- `B` stays at distance `≥ r` from `p`
  have hBfar : ∀ z ∈ B, r ≤ ‖z - p‖ := by
    intro z hz
    by_contra h
    push Not at h
    have hz0 : 0 < ‖z - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun hzp => hz.1.2 hzp))
    exact (Set.eq_empty_iff_forall_notMem.mp hdisj) z ⟨hz.1, ⟨hpb z hz0 h, hz.2⟩⟩
  have hpB : p ∉ closure B := by
    intro hpcl
    obtain ⟨z, hzB, hzd⟩ := Metric.mem_closure_iff.mp hpcl (r / 2) (half_pos hr)
    have hzr : ‖z - p‖ < r := by
      have h1 : ‖z - p‖ = dist p z := by rw [← dist_eq_norm z p, dist_comm]
      rw [h1]
      linarith
    exact absurd (hBfar z hzB) (by linarith)
  -- `A` and `B` are separated
  have hAdisj : A ∩ closure B = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
    have hzv : z ∈ v := (hvcl.closure_subset_iff).mpr (fun w hw => hw.2) hz.2
    exact (Set.eq_empty_iff_forall_notMem.mp hdisj) z ⟨hz.1.1, ⟨hz.1.2, hzv⟩⟩
  have hBdisj : B ∩ closure A = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
    have hzu : z ∈ u := (hucl.closure_subset_iff).mpr (fun w hw => hw.2) hz.2
    exact (Set.eq_empty_iff_forall_notMem.mp hdisj) z ⟨hz.1.1, ⟨hzu, hz.1.2⟩⟩
  have hFsub : F ⊆ closure A ∪ closure B := by
    intro z hz
    by_cases hzp : z = p
    · exact Or.inl (hzp ▸ hpA)
    · rcases hsub ⟨hz, hzp⟩ with h | h
      · exact Or.inl (subset_closure ⟨⟨hz, hzp⟩, h⟩)
      · exact Or.inr (subset_closure ⟨⟨hz, hzp⟩, h⟩)
  have hFdisj : F ∩ (closure A ∩ closure B) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
    rcases hz with ⟨hzF, hzA, hzB⟩
    by_cases hzp : z = p
    · exact hpB (hzp ▸ hzB)
    · rcases hsub ⟨hzF, hzp⟩ with h | h
      · exact (Set.eq_empty_iff_forall_notMem.mp hAdisj) z ⟨⟨⟨hzF, hzp⟩, h⟩, hzB⟩
      · exact (Set.eq_empty_iff_forall_notMem.mp hBdisj) z ⟨⟨⟨hzF, hzp⟩, h⟩, hzA⟩
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hF.2)
      (closure A) (closure B) isClosed_closure isClosed_closure hFsub hFdisj with h | h
  · exact (Set.eq_empty_iff_forall_notMem.mp hBdisj) hBne.choose
      ⟨hBne.choose_spec, h hBne.choose_spec.1.1⟩
  · obtain ⟨w, hw⟩ := (isConnected_punctured_ball_at p hr).nonempty.mono hpbA
    exact (Set.eq_empty_iff_forall_notMem.mp hAdisj) w ⟨hw, h hw.1.1⟩

/-- **Removing an interior point of a connected set in `ℂ` keeps it connected.** -/
theorem isConnected_diff_singleton_of_mem_interior {F : Set ℂ} (hF : IsConnected F) {p : ℂ}
    (hp : p ∈ interior F) : IsConnected (F \ {p}) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hp)
  have hballF : ball p r ⊆ F := fun z hz => interior_subset (hball hz)
  have hpb : {z : ℂ | 0 < ‖z - p‖ ∧ ‖z - p‖ < r} ⊆ F \ {p} := by
    intro z hz
    refine ⟨hballF (by rw [mem_ball, dist_eq_norm]; exact hz.2), ?_⟩
    intro hzp
    exact absurd hz.1 (by rw [hzp]; simp)
  refine ⟨(isConnected_punctured_ball_at p hr).nonempty.mono hpb, ?_⟩
  by_contra hcon
  rw [isPreconnected_iff_subset_of_disjoint_closed] at hcon
  push Not at hcon
  obtain ⟨u, v, hucl, hvcl, hsub, hdisj, hnu, hnv⟩ := hcon
  have hpbuv : {z : ℂ | 0 < ‖z - p‖ ∧ ‖z - p‖ < r} ⊆ u ∪ v := fun z hz => hsub (hpb hz)
  have hpbd : {z : ℂ | 0 < ‖z - p‖ ∧ ‖z - p‖ < r} ∩ (u ∩ v) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
    exact (Set.eq_empty_iff_forall_notMem.mp hdisj) z ⟨hpb hz.1, hz.2⟩
  have hBne : ((F \ {p}) ∩ v).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hnu fun x hx => by
      rcases hsub hx with hxu | hxv
      · exact hxu
      · exact absurd ⟨hx, hxv⟩ ((Set.eq_empty_iff_forall_notMem.mp h) x)
  have hAne : ((F \ {p}) ∩ u).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hnv fun x hx => by
      rcases hsub hx with hxu | hxv
      · exact absurd ⟨hx, hxu⟩ ((Set.eq_empty_iff_forall_notMem.mp h) x)
      · exact hxv
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp
      (isConnected_punctured_ball_at p hr).2) u v hucl hvcl hpbuv hpbd with hpu | hpv
  · exact no_separation_of_diff_singleton hF hr hballF hucl hvcl hsub hdisj
      (fun z h1 h2 => hpu ⟨h1, h2⟩) hBne
  · refine no_separation_of_diff_singleton (u := v) (v := u) hF hr hballF hvcl hucl ?_ ?_
      (fun z h1 h2 => hpv ⟨h1, h2⟩) hAne
    · intro z hz
      rcases hsub hz with h | h
      · exact Or.inr h
      · exact Or.inl h
    · rw [Set.inter_comm v u]
      exact hdisj

end

end Work.Analysis.Complex
