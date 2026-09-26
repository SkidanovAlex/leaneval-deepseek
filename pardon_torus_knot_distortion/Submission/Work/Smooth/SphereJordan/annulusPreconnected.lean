import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.annulus_of_planeHypothesis

/-!
# The open annulus between a curve and the boundary circle is preconnected

For a simple closed plane curve `γ` whose trace lies in the open unit disc and a Schoenflies datum
`S` for it, the region

`Metric.ball (0 : ℂ) 1 \ closure S.V`

between `γ` and the boundary circle is preconnected.

Since `S.U = (closure S.V)ᶜ`, this set is `S.U ∩ ball 0 1`, i.e. the complement of the closed disc
`K = closure S.V` inside the open unit disc.  Writing `Z = Kᶜ = S.U` for the (preconnected)
unbounded side and `C = {z | 1 ≤ ‖z‖}` for the closed complement of the open unit disc, we have
`Z = (Z ∩ ball 0 1) ∪ C`, and `C` is closed, nonempty and disjoint from `Y := Z ∩ ball 0 1`.

The proof is a separation argument.  If closed `u`, `v` cover `Y` and meet only outside `Y`, the
part `Y ∩ v` is disjoint from any preconnected `R ⊆ Y` that happens to lie in `u`.  Choosing
`R = {t ≤ ‖z‖ < 1}` for `t` with `K ⊆ {‖z‖ < t}` and `t < 1` (which exists because `K` is compact
and contained in the open ball) makes `Y ∩ v` lie in `{‖z‖ < t}`, hence at positive distance from
`C`.  Then `closure (Y ∩ v)` and `closure (Y ∩ u) ∪ C` are closed sets covering the preconnected
`Z` with empty intersection on `Z`; the first cannot contain `Z` (it misses the point `1 ∈ C`), so
`Z` is contained in the second, and since `closure (Y ∩ u) ⊆ u` and `Y ∩ C = ∅` this gives
`Y ⊆ u`.  The symmetric argument gives `Y ⊆ v` when `R ⊆ v`.

Only the Jordan *separation* contained in the datum `S` is used — no Schoenflies theorem for other
curves — which is why the statement carries no `PlaneHypothesis`.
-/

namespace Work.Smooth.SphereJordan

open Set

noncomputable section

/-- **The open shell** `{t ≤ ‖z‖ < 1}` (`0 < t < 1`) is preconnected: it is the image of the
preconnected `[t, 1) × S¹` under `(r, w) ↦ r • w`. -/
theorem isPreconnected_shell {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    IsPreconnected {z : ℂ | t ≤ ‖z‖ ∧ ‖z‖ < 1} := by
  have hsp : IsPreconnected (Metric.sphere (0 : ℂ) 1) := isPreconnected_sphere_one
  have hI : IsPreconnected (Set.Ico t 1) := isPreconnected_Ico
  have hprod : IsPreconnected (Set.Ico t 1 ×ˢ Metric.sphere (0 : ℂ) 1) := hI.prod hsp
  have himg : IsPreconnected ((fun p : ℝ × ℂ => p.1 • p.2) ''
      (Set.Ico t 1 ×ˢ Metric.sphere (0 : ℂ) 1)) :=
    hprod.image _ (continuous_fst.smul continuous_snd).continuousOn
  have hset : (fun p : ℝ × ℂ => p.1 • p.2) '' (Set.Ico t 1 ×ˢ Metric.sphere (0 : ℂ) 1)
      = {z : ℂ | t ≤ ‖z‖ ∧ ‖z‖ < 1} := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨hp1, hp2⟩ := hp
      have hp0 : (0 : ℝ) < p.1 := lt_of_lt_of_le ht hp1.1
      have hpw : ‖p.2‖ = 1 := by
        have h := Metric.mem_sphere.mp hp2
        rwa [dist_eq_norm, sub_zero] at h
      change t ≤ ‖p.1 • p.2‖ ∧ ‖p.1 • p.2‖ < 1
      rw [norm_smul, Real.norm_of_nonneg hp0.le, hpw, mul_one]
      exact hp1
    · intro hz
      rw [Set.mem_ofPred_eq] at hz
      obtain ⟨hz1, hz2⟩ := hz
      have hz0 : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le ht hz1
      refine ⟨(‖z‖, z / (↑‖z‖ : ℂ)), ⟨⟨hz1, hz2⟩, ?_⟩, ?_⟩
      · rw [Metric.mem_sphere, dist_eq_norm, sub_zero, div_eq_mul_inv, norm_mul, norm_inv,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz0]
        field_simp
      · show (‖z‖ : ℝ) • (z / (↑‖z‖ : ℂ)) = z
        have hzc : (↑‖z‖ : ℂ) ≠ 0 := by
          rw [Complex.ofReal_ne_zero]; exact ne_of_gt hz0
        rw [Complex.real_smul, div_eq_mul_inv]
        field_simp
  rw [← hset]
  exact himg

/-- **Separation step.**  Let `Z = Y ∪ C` be preconnected with `C` closed, nonempty and disjoint
from `Y`.  If closed `u`, `v` cover `Y` with `Y ∩ u ∩ v = ∅`, and if `closure (Y ∩ v)` avoids `C`,
then `Y ⊆ u`.

The two closed sets `closure (Y ∩ v)` and `closure (Y ∩ u) ∪ C` cover `Z` and meet only outside
`Z`: a point of `closure (Y ∩ u) ∩ closure (Y ∩ v)` lying in `Y` would lie in `u ∩ v ∩ Y`, while a
point of `closure (Y ∩ v) ∩ C` is excluded by hypothesis.  Preconnectedness of `Z` then puts `Z` in
one of them; the first contains no point of `C`, so the second contains `Z`, and
`Y ⊆ closure (Y ∩ u) ⊆ u`. -/
theorem subset_left_of_separation (Z Y C u v : Set ℂ)
    (hCcl : IsClosed C) (hCne : C.Nonempty) (hYC : Disjoint Y C) (hZY : Z = Y ∪ C)
    (hZ : IsPreconnected Z) (hu : IsClosed u) (hv : IsClosed v)
    (huv : Y ⊆ u ∪ v) (huvd : Y ∩ (u ∩ v) = ∅)
    (hsep : closure (Y ∩ v) ∩ C = ∅) :
    Y ⊆ u := by
  have hclu : closure (Y ∩ u) ⊆ u := closure_minimal Set.inter_subset_right hu
  have hclv : closure (Y ∩ v) ⊆ v := closure_minimal Set.inter_subset_right hv
  have hZsub : Z ⊆ closure (Y ∩ v) ∪ (closure (Y ∩ u) ∪ C) := by
    rw [hZY]
    intro z hz
    rw [Set.mem_union] at hz
    rcases hz with hzY | hzC
    · rcases huv hzY with h | h
      · exact Or.inr (Or.inl (subset_closure ⟨hzY, h⟩))
      · exact Or.inl (subset_closure ⟨hzY, h⟩)
    · exact Or.inr (Or.inr hzC)
  have hZdisj : Z ∩ (closure (Y ∩ v) ∩ (closure (Y ∩ u) ∪ C)) = ∅ := by
    rw [← Set.subset_empty_iff]
    rintro z ⟨hzZ, hzA, hzB⟩
    rcases hzB with hzB | hzC
    · by_cases hzY : z ∈ Y
      · have hzu : z ∈ u := hclu hzB
        have hzv : z ∈ v := hclv hzA
        have hmem : z ∈ Y ∩ (u ∩ v) := ⟨hzY, hzu, hzv⟩
        rw [huvd] at hmem
        exact hmem
      · have hzC' : z ∈ C := by
          rw [hZY] at hzZ
          rcases hzZ with h | h
          · exact absurd h hzY
          · exact h
        have hmem : z ∈ closure (Y ∩ v) ∩ C := ⟨hzA, hzC'⟩
        rw [hsep] at hmem
        exact hmem
    · have hmem : z ∈ closure (Y ∩ v) ∩ C := ⟨hzA, hzC⟩
      rw [hsep] at hmem
      exact hmem
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hZ)
      (closure (Y ∩ v)) (closure (Y ∩ u) ∪ C) isClosed_closure
      (isClosed_closure.union hCcl) hZsub hZdisj with hZA | hZB
  · exfalso
    obtain ⟨z, hzC⟩ := hCne
    have hmem : z ∈ closure (Y ∩ v) ∩ C := ⟨hZA (by rw [hZY]; exact Or.inr hzC), hzC⟩
    rw [hsep] at hmem
    exact hmem
  · intro z hzY
    have hzZ : z ∈ Z := by rw [hZY]; exact Or.inl hzY
    rcases hZB hzZ with h | h
    · exact hclu h
    · exact absurd h (Set.disjoint_left.mp hYC hzY)

/-- **The complement of a set contained in a smaller closed ball, inside the open unit disc, is
preconnected whenever its complement in the plane is.**  If `K ⊆ {‖z‖ ≤ s}` with `s < 1` and `Kᶜ`
is preconnected, then so is `Metric.ball (0 : ℂ) 1 \ K`. -/
theorem isPreconnected_ball_sdiff_of_preconnected_compl {K : Set ℂ}
    (hK : ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ K ⊆ Metric.closedBall (0 : ℂ) s)
    (hZ : IsPreconnected Kᶜ) :
    IsPreconnected (Metric.ball (0 : ℂ) 1 \ K) := by
  obtain ⟨s, -, hs1, hKs⟩ := hK
  set t : ℝ := max ((s + 1) / 2) (1 / 2) with htdef
  have hst : s < t := by
    have h1 : s < (s + 1) / 2 := by linarith
    have h2 : (s + 1) / 2 ≤ t := le_max_left _ _
    linarith
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have ht1 : t < 1 := max_lt (by linarith) (by norm_num)
  have hKt : K ⊆ {z : ℂ | ‖z‖ < t} := by
    intro z hz
    have h1 : ‖z‖ ≤ s := by
      have h := hKs hz
      rwa [Metric.mem_closedBall, dist_zero_right] at h
    change ‖z‖ < t
    linarith
  set C : Set ℂ := {z : ℂ | 1 ≤ ‖z‖} with hCdef
  set Y : Set ℂ := Metric.ball (0 : ℂ) 1 \ K with hYdef
  have hYmem : ∀ z : ℂ, z ∈ Y ↔ ‖z‖ < 1 ∧ z ∉ K := by
    intro z
    rw [hYdef, Set.mem_sdiff, Metric.mem_ball, dist_zero_right]
  have hCcl : IsClosed C := by
    rw [hCdef]
    exact isClosed_le continuous_const continuous_norm
  have hCne : C.Nonempty := ⟨1, by rw [hCdef]; simp⟩
  have hYC : Disjoint Y C := by
    rw [Set.disjoint_left]
    intro z hzY hzC
    have hz1 : (1 : ℝ) ≤ ‖z‖ := hzC
    exact absurd hz1 (not_le.mpr ((hYmem z).mp hzY).1)
  have hZY : Kᶜ = Y ∪ C := by
    ext z
    constructor
    · intro hz
      by_cases h : ‖z‖ < 1
      · exact Or.inl ((hYmem z).mpr ⟨h, hz⟩)
      · exact Or.inr (by rw [hCdef]; exact not_lt.mp h)
    · intro hz
      rw [Set.mem_union] at hz
      rcases hz with hzY | hzC
      · exact ((hYmem z).mp hzY).2
      · have h2 : (1 : ℝ) ≤ ‖z‖ := hzC
        intro hzK
        have h1 : ‖z‖ < t := hKt hzK
        linarith
  set R : Set ℂ := {z : ℂ | t ≤ ‖z‖ ∧ ‖z‖ < 1} with hRdef
  have hRpre : IsPreconnected R := isPreconnected_shell ht0 ht1
  have hRY : R ⊆ Y := by
    intro z hz
    rw [hRdef] at hz
    exact (hYmem z).mpr ⟨hz.2, fun hzK => absurd (hKt hzK) (not_lt.mpr hz.1)⟩
  have hYRmem : ∀ z : ℂ, z ∈ Y → z ∈ R ∨ ‖z‖ < t := by
    intro z hzY
    by_cases h : ‖z‖ < t
    · exact Or.inr h
    · exact Or.inl (by rw [hRdef]; exact ⟨not_lt.mp h, ((hYmem z).mp hzY).1⟩)
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv huv huvd
  have hRuv : R ⊆ u ∪ v := Subset.trans hRY huv
  have hRuvd : R ∩ (u ∩ v) = ∅ := by
    rw [← Set.subset_empty_iff]
    rintro z ⟨hzR, hzu, hzv⟩
    have hmem : z ∈ Y ∩ (u ∩ v) := ⟨hRY hzR, hzu, hzv⟩
    rw [huvd] at hmem
    exact hmem
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hRpre) u v hu hv hRuv hRuvd with hRu | hRv
  · refine Or.inl (subset_left_of_separation _ Y C u v hCcl hCne hYC hZY hZ hu hv huv huvd ?_)
    rw [← Set.subset_empty_iff]
    rintro z ⟨hzA, hzC⟩
    have hz1 : (1 : ℝ) ≤ ‖z‖ := hzC
    have hsub : Y ∩ v ⊆ Metric.closedBall (0 : ℂ) t := by
      rintro w ⟨hwY, hwv⟩
      rcases hYRmem w hwY with hwR | hw
      · exfalso
        have hmem : w ∈ Y ∩ (u ∩ v) := ⟨hwY, hRu hwR, hwv⟩
        rw [huvd] at hmem
        exact hmem
      · rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt hw
    have hzA2 : z ∈ Metric.closedBall (0 : ℂ) t :=
      closure_minimal hsub Metric.isClosed_closedBall hzA
    rw [Metric.mem_closedBall, dist_zero_right] at hzA2
    linarith
  · refine Or.inr (subset_left_of_separation _ Y C v u hCcl hCne hYC hZY hZ hv hu ?_ ?_ ?_)
    · intro z hz
      rcases huv hz with h | h
      · exact Or.inr h
      · exact Or.inl h
    · simpa only [Set.inter_comm u v] using huvd
    · rw [← Set.subset_empty_iff]
      rintro z ⟨hzA, hzC⟩
      have hz1 : (1 : ℝ) ≤ ‖z‖ := hzC
      have hsub : Y ∩ u ⊆ Metric.closedBall (0 : ℂ) t := by
        rintro w ⟨hwY, hwu⟩
        rcases hYRmem w hwY with hwR | hw
        · exfalso
          have hmem : w ∈ Y ∩ (u ∩ v) := ⟨hwY, hwu, hRv hwR⟩
          rw [huvd] at hmem
          exact hmem
        · rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt hw
      have hzA2 : z ∈ Metric.closedBall (0 : ℂ) t :=
        closure_minimal hsub Metric.isClosed_closedBall hzA
      rw [Metric.mem_closedBall, dist_zero_right] at hzA2
      linarith

/-- **The unbounded side is the complement of the closed disc** bounded by the curve. -/
theorem compl_closure_V_eq_unboundedSide {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    S.U = (closure S.V)ᶜ := by
  ext z
  constructor
  · intro hzU hzcl
    have hsub : S.V ⊆ S.Uᶜ :=
      fun y hyV hyU => Set.disjoint_left.mp S.toPlaneSeparation.disjoint_UV hyU hyV
    have hcl : closure S.V ⊆ S.Uᶜ :=
      closure_minimal hsub S.toPlaneSeparation.isOpen_U.isClosed_compl
    exact hcl hzcl hzU
  · intro hzcl
    have hzV : z ∉ S.V := fun hV => hzcl (subset_closure hV)
    have hzT : z ∉ γ.trace := by
      rintro ⟨θ, hθ⟩
      exact hzcl (by
        rw [← S.range_e]
        exact ⟨circlePoint θ, (S.boundary θ).trans hθ⟩)
    have hall : z ∈ S.U ∪ S.V := by
      rw [S.toPlaneSeparation.union_eq]
      exact hzT
    exact hall.resolve_right hzV

/-- **Compactness input**: a compact set contained in the open unit disc is contained in a closed
ball of radius `< 1`. -/
theorem exists_closedBall_superset_of_isCompact {K : Set ℂ} (hKc : IsCompact K)
    (hK : K ⊆ Metric.ball (0 : ℂ) 1) :
    ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ K ⊆ Metric.closedBall (0 : ℂ) s := by
  by_cases hne : K.Nonempty
  · obtain ⟨z₀, hz₀, hmax⟩ := hKc.exists_isMaxOn hne continuous_norm.continuousOn
    refine ⟨‖z₀‖, norm_nonneg z₀, ?_, ?_⟩
    · have h := hK hz₀
      rwa [Metric.mem_ball, dist_zero_right] at h
    · intro z hz
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hmax hz
  · exact ⟨0, le_refl 0, one_pos, fun z hz => absurd ⟨z, hz⟩ hne⟩

/-- **The annulus between a curve inside the open unit disc and the boundary circle is
preconnected.** -/
theorem annulusPreconnected {γ : Work.Smooth.Jordan.PlaneCurve} (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    IsPreconnected (Metric.ball (0 : ℂ) 1 \ closure S.V) := by
  have hKc : IsCompact (closure S.V) := by
    rw [← S.range_e]
    exact isCompact_range S.e.continuous
  have hK : closure S.V ⊆ Metric.ball (0 : ℂ) 1 := fun z hz => by
    have h := Work.Smooth.SphereJordan.closure_V_subset_openBall S hball hz
    rwa [Metric.mem_ball, dist_zero_right]
  have hZ : IsPreconnected ((closure S.V)ᶜ) := by
    rw [← compl_closure_V_eq_unboundedSide S]
    exact S.toPlaneSeparation.preconn_U
  exact isPreconnected_ball_sdiff_of_preconnected_compl
    (exists_closedBall_superset_of_isCompact hKc hK) hZ

end

end Work.Smooth.SphereJordan
