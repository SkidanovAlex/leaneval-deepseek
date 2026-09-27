import Mathlib
import Submission.Work.Analysis.Complex.punctured_ball_connected

/-!
# Removing finitely many points from a connected open subset of a Riemann surface

This file proves `Work.Drive.isPreconnected_sdiff_finite`: if `U` is an open preconnected subset of
a surface `X` (a space charted over `ℂ`, Hausdorff) and `F` is finite, then `U \ F` is still
preconnected.

The proof is the classical one.  In a locally path connected space a preconnected open set is
path connected, and a surface has no separating points: around every point `p` there are
arbitrarily small punctured neighbourhoods `N \ {p}` which are path connected (they are
homeomorphic to a punctured disc in `ℂ`).  Hence the *path component* of a point `x` of
`U \ {p}` is open in `X` and its complement in `U \ {p}` is open as well; the two open sets
`A ∪ {p}` (resp. `A`) and `(U \ {p}) \ A` (resp. `((U \ {p}) \ A) ∪ {p}`) then contradict the
preconnectedness of `U` unless `A = U \ {p}`.  Iterating (removing one point at a time, by Finset
induction) gives the statement for finite `F`.
-/

open Set Metric

namespace Work.Drive

/-- **A punctured disc in `ℂ` is path connected.**  The set `{z | 0 < ‖z - c‖ ∧ ‖z - c‖ < r}` is
open and connected (this is `Work.Analysis.Complex.isConnected_punctured_ball_at`), hence path
connected because `ℂ` is locally path connected. -/
theorem isPathConnected_ball_sdiff_singleton (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IsPathConnected (Metric.ball c r \ {c}) := by
  have hset : Metric.ball c r \ {c} = {z : ℂ | 0 < ‖z - c‖ ∧ ‖z - c‖ < r} := by
    ext z
    rw [Set.mem_sdiff, Metric.mem_ball, dist_eq_norm, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨norm_pos_iff.mpr (sub_ne_zero.mpr h2), h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, sub_ne_zero.mp (norm_ne_zero_iff.mp (ne_of_gt h1))⟩
  rw [hset]
  have hcont : Continuous fun z : ℂ => ‖z - c‖ :=
    continuous_norm.comp (continuous_id.sub continuous_const)
  exact (IsOpen.isConnected_iff_isPathConnected
      ((isOpen_lt continuous_const hcont).inter (isOpen_lt hcont continuous_const))).mp
    (Work.Analysis.Complex.isConnected_punctured_ball_at c hr)

/-- **Small punctured neighbourhoods of a point of a surface are path connected.**  For `U` open,
`p ∈ U`, there is an open `N` with `p ∈ N ⊆ U` and `N \ {p}` path connected: take `N` the
preimage under a chart at `p` of a small disc around the image of `p`. -/
theorem exists_open_sdiff_singleton_pathConnected {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] {p : X} {U : Set X} (hU : IsOpen U) (hp : p ∈ U) :
    ∃ N : Set X, IsOpen N ∧ p ∈ N ∧ N ⊆ U ∧ IsPathConnected (N \ {p}) := by
  let e := chartAt ℂ p
  have hpsrc : p ∈ e.source := mem_chart_source ℂ p
  have hmem : e p ∈ e '' (e.source ∩ U) := ⟨p, ⟨hpsrc, hp⟩, rfl⟩
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp (e.isOpen_image_source_inter hU) (e p) hmem
  refine ⟨e.source ∩ e ⁻¹' Metric.ball (e p) r, e.isOpen_inter_preimage Metric.isOpen_ball,
    ⟨hpsrc, Metric.mem_ball_self hr⟩, ?_, ?_⟩
  · rintro y ⟨hysrc, hyb⟩
    obtain ⟨x, ⟨hxsrc, hxU⟩, hxe⟩ := hrsub hyb
    have hxy : x = y := by rw [← e.left_inv hxsrc, hxe, e.left_inv hysrc]
    rwa [← hxy]
  · have hballsub : Metric.ball (e p) r ⊆ e.target := fun w hw => by
      obtain ⟨x, ⟨hxsrc, -⟩, hxe⟩ := hrsub hw
      rw [← hxe]
      exact e.map_source hxsrc
    have hset : (e.source ∩ e ⁻¹' Metric.ball (e p) r) \ {p}
        = e.symm '' (Metric.ball (e p) r \ {e p}) := by
      ext y
      constructor
      · rintro ⟨⟨hysrc, hyb⟩, hyp⟩
        exact ⟨e y, ⟨hyb, fun hey => hyp (e.injOn hysrc hpsrc hey)⟩, e.left_inv hysrc⟩
      · rintro ⟨w, ⟨hwb, hwp⟩, rfl⟩
        refine ⟨⟨e.map_target (hballsub hwb), ?_⟩, fun h => hwp ?_⟩
        · show e (e.symm w) ∈ Metric.ball (e p) r
          rw [e.right_inv (hballsub hwb)]
          exact hwb
        · show w = e p
          rw [← h]
          exact (e.right_inv (hballsub hwb)).symm
    rw [hset]
    exact (isPathConnected_ball_sdiff_singleton (e p) hr).image'
      (e.continuousOn_symm.mono (fun w hw => hballsub hw.1))

/-- **Removing one point from an open preconnected subset of a surface leaves it preconnected.** -/
theorem isPreconnected_sdiff_singleton {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] {U : Set X} (hUo : IsOpen U) (hUc : IsPreconnected U) (p : X) :
    IsPreconnected (U \ {p}) := by
  classical
  have hLPC : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  rcases eq_empty_or_nonempty (U \ {p}) with hV0 | ⟨x, hxV0⟩
  · rw [hV0]
    exact isPreconnected_empty
  · set V : Set X := U \ {p} with hVdef
    have hxV : x ∈ V := hxV0
    have hxU : x ∈ U := hxV0.1
    have hxp : x ≠ p := by simpa using hxV0.2
    have hVopen : IsOpen V := hUo.sdiff isClosed_singleton
    have hAopen : IsOpen (pathComponentIn V x) := hVopen.pathComponentIn x
    have hAsubV : pathComponentIn V x ⊆ V := pathComponentIn_subset
    have hxAsub : x ∈ pathComponentIn V x := mem_pathComponentIn_self hxV
    have hApath : IsPathConnected (pathComponentIn V x) := isPathConnected_pathComponentIn hxV
    have hBopen : IsOpen (V \ pathComponentIn V x) := by
      rw [isOpen_iff_mem_nhds]
      rintro y ⟨hyV, hyA⟩
      obtain ⟨s, ⟨hso, hys, hspc⟩, hsV⟩ :=
        (isOpen_isPathConnected_basis y).mem_iff.mp (hVopen.mem_nhds hyV)
      refine Filter.mem_of_superset (hso.mem_nhds hys) fun z hzs =>
        ⟨hsV hzs, fun hzA => hyA ?_⟩
      show JoinedIn V x y
      exact (show JoinedIn V x z from hzA).trans
        (JoinedIn.symm (show JoinedIn V y z from (hspc.joinedIn y hys z hzs).mono hsV))
    by_cases hpU : p ∈ U
    · obtain ⟨N, hNo, hpN, hNU, hNpath⟩ :=
        exists_open_sdiff_singleton_pathConnected hUo hpU
      have hNsubV : N \ {p} ⊆ V := fun z ⟨hzN, hzp⟩ => ⟨hNU hzN, hzp⟩
      by_cases hcase : (pathComponentIn V x ∩ (N \ {p})).Nonempty
      · -- `N ∖ {p}` meets the path component of `x`, hence lies inside it
        obtain ⟨w, hwA, hwN⟩ := hcase
        have hNsubA : N \ {p} ⊆ pathComponentIn V x := fun z hz => by
          show JoinedIn V x z
          exact (show JoinedIn V x w from hwA).trans
            (show JoinedIn V w z from (hNpath.joinedIn w hwN z hz).mono hNsubV)
        have hAuopen : IsOpen (pathComponentIn V x ∪ {p}) := by
          have hEq : pathComponentIn V x ∪ {p} = pathComponentIn V x ∪ N := by
            ext z
            constructor
            · rintro (hzA | hzp)
              · exact Or.inl hzA
              · exact Or.inr (hzp ▸ hpN)
            · rintro (hzA | hzN)
              · exact Or.inl hzA
              · by_cases hzp : z = p
                · exact Or.inr hzp
                · exact Or.inl (hNsubA ⟨hzN, hzp⟩)
          rw [hEq]
          exact hAopen.union hNo
        have hcover : U ⊆ (pathComponentIn V x ∪ {p}) ∪ (V \ pathComponentIn V x) := by
          intro y hy
          by_cases hyp : y = p
          · exact Or.inl (Or.inr hyp)
          · have hyV : y ∈ V := ⟨hy, hyp⟩
            by_cases hyA : y ∈ pathComponentIn V x
            · exact Or.inl (Or.inl hyA)
            · exact Or.inr ⟨hyV, hyA⟩
        have hdisj : U ∩ ((pathComponentIn V x ∪ {p}) ∩ (V \ pathComponentIn V x)) = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          rintro y ⟨-, hyu, hyB⟩
          rcases hyu with hyA | hyp
          · exact hyB.2 hyA
          · exact hyB.1.2 hyp
        rcases (isPreconnected_iff_subset_of_disjoint.mp hUc) (pathComponentIn V x ∪ {p})
          (V \ pathComponentIn V x) hAuopen hBopen hcover hdisj with h | h
        · have hVsubA : V ⊆ pathComponentIn V x := fun z hz =>
            (h hz.1).elim id (fun hzp => absurd hzp hz.2)
          have hAV : pathComponentIn V x = V := Subset.antisymm hAsubV hVsubA
          rw [← hAV]
          exact hApath.isConnected.isPreconnected
        · exact absurd (h hxU) (fun hx => hx.2 hxAsub)
      · -- `N ∖ {p}` misses the path component of `x`, hence lies in its complement
        have hNsubB : N \ {p} ⊆ V \ pathComponentIn V x := fun z hz =>
          ⟨hNsubV hz, fun hzA => hcase ⟨z, hzA, hz⟩⟩
        have hBpopen : IsOpen ((V \ pathComponentIn V x) ∪ {p}) := by
          have hEq : (V \ pathComponentIn V x) ∪ {p} = (V \ pathComponentIn V x) ∪ N := by
            ext z
            constructor
            · rintro (hzB | hzp)
              · exact Or.inl hzB
              · exact Or.inr (hzp ▸ hpN)
            · rintro (hzB | hzN)
              · exact Or.inl hzB
              · by_cases hzp : z = p
                · exact Or.inr hzp
                · exact Or.inl (hNsubB ⟨hzN, hzp⟩)
          rw [hEq]
          exact hBopen.union hNo
        have hcover : U ⊆ pathComponentIn V x ∪ ((V \ pathComponentIn V x) ∪ {p}) := by
          intro y hy
          by_cases hyp : y = p
          · exact Or.inr (Or.inr hyp)
          · have hyV : y ∈ V := ⟨hy, hyp⟩
            by_cases hyA : y ∈ pathComponentIn V x
            · exact Or.inl hyA
            · exact Or.inr (Or.inl ⟨hyV, hyA⟩)
        have hdisj : U ∩ (pathComponentIn V x ∩ ((V \ pathComponentIn V x) ∪ {p})) = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          rintro y ⟨-, hyA, hyu⟩
          rcases hyu with hyB | hyp
          · exact hyB.2 hyA
          · exact (hAsubV hyA).2 hyp
        rcases (isPreconnected_iff_subset_of_disjoint.mp hUc) (pathComponentIn V x)
          ((V \ pathComponentIn V x) ∪ {p}) hAopen hBpopen hcover hdisj with h | h
        · have hVsubA : V ⊆ pathComponentIn V x := fun z hz => h hz.1
          have hAV : pathComponentIn V x = V := Subset.antisymm hAsubV hVsubA
          rw [← hAV]
          exact hApath.isConnected.isPreconnected
        · exact absurd (h hxU) (by
            rintro (hx | hxp')
            · exact hx.2 hxAsub
            · exact hxp hxp')
    · -- `p ∉ U`, so `U \ {p} = U`
      have hVU : V = U := by
        rw [hVdef]
        ext z
        simp only [Set.mem_sdiff, Set.mem_singleton_iff]
        exact ⟨fun hz => hz.1, fun hz => ⟨hz, fun h => hpU (h ▸ hz)⟩⟩
      rw [hVU]
      exact hUc

/-- **Removing finitely many points from an open preconnected subset of a surface leaves it
preconnected.** -/
theorem isPreconnected_sdiff_finite {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    {U : Set X} (hUo : IsOpen U) (hUc : IsPreconnected U) (F : Set X) (hF : F.Finite) :
    IsPreconnected (U \ F) := by
  classical
  have key : ∀ (s : Finset X) (U : Set X), IsOpen U → IsPreconnected U →
      IsPreconnected (U \ (s : Set X)) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro U h1 h2
      simpa using h2
    · intro p t hpt ih U h1 h2
      have hstep : U \ ((insert p t : Finset X) : Set X) = (U \ {p}) \ (t : Set X) := by
        ext z
        simp only [Set.mem_sdiff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_insert]
        tauto
      rw [hstep]
      exact ih (U \ {p}) (h1.sdiff isClosed_singleton)
        (isPreconnected_sdiff_singleton h1 h2 p)
  have hkey := key hF.toFinset U hUo hUc
  rwa [hF.coe_toFinset] at hkey

end Work.Drive
