import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.immediateBasin_has_critval
import Submission.Work.Horn.exists_ball_injOn_and_mapsTo
import Submission.Work.Horn.fiber_finite
import Submission.Work.Horn.exists_pos_le_half_dist
import Submission.Work.Horn.eventually_ncard_eq_of_local_trivialization
import Submission.Unif.Commons.Analysis.Complex.exists_two_preimages_near_of_deriv_eq_zero
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.isPreconnected_diff_singleton_of_isOpen

/-!
# Shishikura Prop. 5.3: a proper holomorphic self-map of a domain whose only critical point
is `c` has at least two preimages of every regular value `a ≠ f c`.

`B ⊆ ℂ` is open and connected, `f` holomorphic on `B` with `f '' B ⊆ B`, and the preimage of every
compact subset of `B` is compact (properness of `f : B → B`).  If `c ∈ B` is the only critical point
of `f` and `f` is not locally constant at `c`, then every `a ∈ B` with `a ≠ f c` is taken at least
twice on `B`.

The proof is the elementary "degree is locally constant" argument, with no Riemann-surface theory:

* `fiber_finite`: every fibre `B ∩ f ⁻¹' {w}` (`w ∈ B`) is finite — it is compact by properness and
  discrete because `f` is nowhere locally constant on the connected `B`.
* `exists_ball_injOn_and_mapsTo`: off the unique critical point, `f` is a local biholomorphism,
  so at each preimage `x` of `w₀ ≠ f c` there is a ball on which `f` is injective and whose image
  covers a neighbourhood of `w₀`.
* `exists_pos_le_half_dist` supplies pairwise disjointness of the balls.
* `eventually_ncard_eq_of_local_trivialization`: consequence — the fibre cardinal `w ↦ #(B ∩ f ⁻¹' {w})`
  is locally constant at every `w₀ ∈ B`, `w₀ ≠ f c`.
* Since `B ∖ {f c}` is preconnected (removing a point from an open preconnected subset of `ℂ` does
  not disconnect it) the fibre cardinal is constant on `B ∖ {f c}`.
* `Commons.Analysis.Complex.exists_two_preimages_near_of_deriv_eq_zero` (branch point at the
  critical point) exhibits a value `w` arbitrarily close to `f c` with two distinct preimages; the
  constancy of the fibre cardinal transports this to `a`.
-/

namespace Work.Horn

theorem two_preimages_of_regular_value {B : Set ℂ} {f : ℂ → ℂ} {c : ℂ}
    (hB : IsOpen B) (hconn : IsConnected B) (hf : DifferentiableOn ℂ f B)
    (hmap : Set.MapsTo f B B)
    (hprop : ∀ L ⊆ B, IsCompact L → IsCompact (B ∩ f ⁻¹' L))
    (hcB : c ∈ B) (hc : deriv f c = 0)
    (huniq : ∀ z ∈ B, deriv f z = 0 → z = c)
    (hnc : ¬ ∀ᶠ z in nhds c, f z = f c)
    {a : ℂ} (haB : a ∈ B) (ha : a ≠ f c) :
    ∃ x ∈ B, ∃ y ∈ B, x ≠ y ∧ f x = a ∧ f y = a := by
  have hpre : IsPreconnected B := hconn.isPreconnected
  have hcont : ContinuousOn f B := hf.continuousOn
  -- The fibre cardinal is locally constant away from the critical value.
  have hlocconst : ∀ w₀ ∈ B \ {f c},
      ∀ᶠ w in nhds w₀, (B ∩ f ⁻¹' {w}).ncard = (B ∩ f ⁻¹' {w₀}).ncard := by
    intro w₀ hw₀mem
    obtain ⟨hw₀B, hw₀ne⟩ := hw₀mem
    have hw₀ne' : w₀ ≠ f c := by simpa using hw₀ne
    have hfin : (B ∩ f ⁻¹' {w₀}).Finite := fiber_finite hB hpre hf hcB hnc hprop hw₀B
    set S : Finset ℂ := hfin.toFinset with hSdef
    have hS : ∀ z : ℂ, z ∈ (S : Set ℂ) ↔ z ∈ B ∧ f z = w₀ := by
      intro z
      rw [hSdef, Finset.mem_coe, hfin.mem_toFinset]
      simp [Set.mem_inter_iff, Set.mem_preimage]
    have hcardS : S.card = (B ∩ f ⁻¹' {w₀}).ncard := by
      rw [hSdef]
      exact (Set.ncard_eq_toFinset_card _ hfin).symm
    obtain ⟨m, hmpos, hmle⟩ := exists_pos_le_half_dist S
    -- At every preimage of `w₀`, `f` is a local biholomorphism, with an explicit ball.
    have hpoint : ∀ x : ℂ, ∃ ρ : ℝ, ∃ δ : ℝ, (x ∈ S → 0 < ρ ∧ ρ < m x ∧ 0 < δ ∧
        Metric.ball x ρ ⊆ B ∧ Set.InjOn f (Metric.ball x ρ) ∧
        ∀ w : ℂ, ‖w - w₀‖ < δ → ∃ u ∈ Metric.ball x ρ, f u = w) := by
      intro x
      by_cases hx : x ∈ S
      · have hxB : x ∈ B := ((hS x).mp hx).1
        have hfx : f x = w₀ := ((hS x).mp hx).2
        have hne : deriv f x ≠ 0 := by
          intro h0
          have hxc : x = c := huniq x hxB h0
          have : w₀ = f c := by rw [← hfx, hxc]
          exact hw₀ne' this
        obtain ⟨ρ, hρpos, hρlt, δ, hδpos, hsub, hinj, hloc⟩ :=
          exists_ball_injOn_and_mapsTo hB hf hxB hne (hmpos x hx)
        exact ⟨ρ, δ, fun _ => by
          refine ⟨hρpos, hρlt, hδpos, hsub, hinj, ?_⟩
          rw [← hfx]
          exact hloc⟩
      · exact ⟨1, 1, fun h => absurd h hx⟩
    choose ρ δ hspec using hpoint
    have hρpos : ∀ x ∈ S, 0 < ρ x := fun x hx => (hspec x hx).1
    have hρltm : ∀ x ∈ S, ρ x < m x := fun x hx => (hspec x hx).2.1
    have hδpos : ∀ x ∈ S, 0 < δ x := fun x hx => (hspec x hx).2.2.1
    have hρsub : ∀ x ∈ S, Metric.ball x (ρ x) ⊆ B := fun x hx => (hspec x hx).2.2.2.1
    have hinj : ∀ x ∈ S, Set.InjOn f (Metric.ball x (ρ x)) :=
      fun x hx => (hspec x hx).2.2.2.2.1
    have hloc : ∀ x ∈ S, ∀ w : ℂ, ‖w - w₀‖ < δ x → ∃ u ∈ Metric.ball x (ρ x), f u = w :=
      fun x hx => (hspec x hx).2.2.2.2.2
    have hdisj : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
        Disjoint (Metric.ball x (ρ x)) (Metric.ball y (ρ y)) := by
      intro x hx y hy hxy
      refine Metric.ball_disjoint_ball ?_
      have h1 : ρ x < m x := hρltm x hx
      have h2 : ρ y < m y := hρltm y hy
      have h3 : m x ≤ dist x y / 2 := hmle x hx y hy hxy
      have h4 : m y ≤ dist x y / 2 := by
        have := hmle y hy x hx (Ne.symm hxy)
        rwa [dist_comm y x] at this
      linarith
    filter_upwards
      [eventually_ncard_eq_of_local_trivialization hB hcont hprop hw₀B S hS ρ hρpos hρsub
        hdisj hinj δ hδpos hloc] with w hw
    rw [hw, hcardS]
  -- `B ∖ {f c}` is preconnected, so the fibre cardinal is constant on it.
  have hpcn : IsPreconnected (B \ {f c}) :=
    Work.SimplyConnected.ABS.isPreconnected_diff_singleton_of_isOpen (U := B) (x := f c) hB hpre
      (hmap hcB)
  -- A value near the critical value with (at least) two preimages.
  obtain ⟨ε, hεpos, hεball⟩ : ∃ ε > 0, Metric.ball c ε ⊆ B := by
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hB c hcB
    exact ⟨r, hr, hrsub⟩
  have hana : AnalyticAt ℂ f c := hf.analyticAt (hB.mem_nhds hcB)
  obtain ⟨w, hwne, hwlt, x₀, y₀, hx₀y₀, hx₀lt, hy₀lt, hfx₀, hfy₀⟩ :=
    Commons.Analysis.Complex.exists_two_preimages_near_of_deriv_eq_zero hana hc hnc hεpos
  have hx₀B : x₀ ∈ B := hεball (by rw [Metric.mem_ball, dist_eq_norm]; exact hx₀lt)
  have hy₀B : y₀ ∈ B := hεball (by rw [Metric.mem_ball, dist_eq_norm]; exact hy₀lt)
  have hwB : w ∈ B := by rw [← hfx₀]; exact hmap hx₀B
  have hwmem : w ∈ B \ {f c} := ⟨hwB, by simpa using hwne⟩
  have hamem : a ∈ B \ {f c} := ⟨haB, by simpa using ha⟩
  have hkey : (B ∩ f ⁻¹' {a}).ncard = (B ∩ f ⁻¹' {w}).ncard :=
    hpcn.induction₂ (fun u v => (B ∩ f ⁻¹' {u}).ncard = (B ∩ f ⁻¹' {v}).ncard)
      (fun u hu => ((hlocconst u hu).filter_mono nhdsWithin_le_nhds).mono (fun v hv => hv.symm))
      (fun u v t _ _ _ h1 h2 => h1.trans h2)
      (fun u v _ _ h1 => h1.symm) hamem hwmem
  have hfinw : (B ∩ f ⁻¹' {w}).Finite := fiber_finite hB hpre hf hcB hnc hprop hwB
  have h2w : 2 ≤ (B ∩ f ⁻¹' {w}).ncard := by
    have h1 : 1 < hfinw.toFinset.card := by
      apply Finset.one_lt_card.mpr
      exact ⟨x₀, (hfinw.mem_toFinset).mpr ⟨hx₀B, by simpa using hfx₀⟩,
             y₀, (hfinw.mem_toFinset).mpr ⟨hy₀B, by simpa using hfy₀⟩, hx₀y₀⟩
    rw [Set.ncard_eq_toFinset_card _ hfinw]
    omega
  have h2a : 2 ≤ (B ∩ f ⁻¹' {a}).ncard := by rw [hkey]; exact h2w
  have hfina : (B ∩ f ⁻¹' {a}).Finite := fiber_finite hB hpre hf hcB hnc hprop haB
  have h1a : 1 < hfina.toFinset.card := by
    rw [Set.ncard_eq_toFinset_card _ hfina] at h2a
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h1a
  rw [Set.Finite.mem_toFinset] at hx hy
  exact ⟨x, hx.1, y, hy.1, hxy, by simpa using hx.2, by simpa using hy.2⟩

end Work.Horn
