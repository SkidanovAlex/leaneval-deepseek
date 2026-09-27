import Mathlib
import Submission.Work.Engulf.Basic

open Set Metric PL

namespace Work.Engulf.Aux

/-- **Glueing step.**  A function that is locally `ψ`-affine (with values in the open unit cube)
at every point of a nonempty convex set `C ⊆ ℝ^N`, where `ψ` is injective on the open unit cube,
is globally `ψ`-affine on `C`: a single affine map `A` with `A z ∈ openCube 1` and
`f z = ψ (A z)` for all `z ∈ C`.

(Proof: at every `z ∈ C` there is a local affine map `A_z` valid on `C ∩ ball z δ_z`, and these
glue because two of them that overlap agree on their overlap by injectivity of `ψ` on the cube.
Two such maps agreeing on a relatively open subset of the convex `C` agree on `C` (their
difference of linear parts vanishes on a relative neighbourhood, whose segments with any point of
`C` fill in the missing directions), so the class of `z ↦ A_z` is simultaneously open and closed
in the preconnected space `C`.) -/
theorem locally_affine_of_convex {n N : ℕ} {M : Type*} [TopologicalSpace M]
    (ψ : PL.E n → M)
    (hinj : ∀ x ∈ PL.openCube (n := n) 1, ∀ y ∈ PL.openCube (n := n) 1, ψ x = ψ y → x = y)
    {C : Set (PL.E N)} (hC : Convex ℝ C) (hne : C.Nonempty) (f : PL.E N → M)
    (hloc : ∀ y ∈ C, ∃ δ > 0, ∃ A : PL.E N →ᵃ[ℝ] PL.E n,
      ∀ z ∈ C ∩ Metric.ball y δ, A z ∈ PL.openCube (n := n) 1 ∧ f z = ψ (A z)) :
    ∃ A : PL.E N →ᵃ[ℝ] PL.E n, ∀ z ∈ C, A z ∈ PL.openCube (n := n) 1 ∧ f z = ψ (A z) := by
  classical
  choose d hd A hA using fun y : C => hloc y y.2
  -- value of an affine map from its value and linear part at a base point
  have hpt : ∀ (B : PL.E N →ᵃ[ℝ] PL.E n) (w z : PL.E N), B z = B.linear (z - w) + B w := by
    intro B w z
    conv_lhs => rw [← sub_add_cancel z w]
    rw [← vadd_eq_add, AffineMap.map_vadd, vadd_eq_add]
  have hmt : ∀ (B : PL.E N →ᵃ[ℝ] PL.E n) (w z : PL.E N) (t : ℝ),
      B (w + t • (z - w)) = t • (B.linear (z - w)) + B w := by
    intro B w z t
    conv_lhs => rw [add_comm]
    rw [← vadd_eq_add, AffineMap.map_vadd, map_smul, vadd_eq_add]
  -- two local maps whose balls meet at a point of `C` have the same value there
  have agree : ∀ (y y' : C) (z : PL.E N), z ∈ C → z ∈ Metric.ball (y : PL.E N) (d y) →
      z ∈ Metric.ball (y' : PL.E N) (d y') → A y z = A y' z := by
    intro y y' z hz hzy hzy'
    have h1 : A y z ∈ PL.openCube (n := n) 1 := (hA y z ⟨hz, hzy⟩).1
    have h2 : A y' z ∈ PL.openCube (n := n) 1 := (hA y' z ⟨hz, hzy'⟩).1
    have h3 : ψ (A y z) = ψ (A y' z) :=
      ((hA y z ⟨hz, hzy⟩).2).symm.trans ((hA y' z ⟨hz, hzy'⟩).2)
    exact hinj (A y z) h1 (A y' z) h2 h3
  -- ... hence they agree on all of `C`
  have small : ∀ (y y' : C) (z : PL.E N), (C ∩ Metric.ball (y : PL.E N) (d y) ∩
      Metric.ball (y' : PL.E N) (d y')).Nonempty → z ∈ C → A y z = A y' z := by
    intro y y' z hW hz
    obtain ⟨w, ⟨⟨hwC, hwy⟩, hwy'⟩⟩ := hW
    have hw : A y w = A y' w := agree y y' w hwC hwy hwy'
    have hN : (Metric.ball (y : PL.E N) (d y) ∩ Metric.ball (y' : PL.E N) (d y')) ∈
        nhds w :=
      Filter.inter_mem (Metric.isOpen_ball.mem_nhds hwy) (Metric.isOpen_ball.mem_nhds hwy')
    have hcm : Continuous fun t : ℝ => w + t • (z - w) := by fun_prop
    have hmemC : ∀ t : ℝ, 0 < t → t ≤ 1 → w + t • (z - w) ∈ C := by
      intro t ht0 ht1
      have heq : w + t • (z - w) = (1 - t) • w + t • z := by
        rw [smul_sub, sub_smul, one_smul]; abel
      rw [heq]
      exact hC hwC hz (by linarith) (by linarith) (by ring)
    have hpos : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), 0 < t := self_mem_nhdsWithin
    have hle1 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), t ≤ 1 :=
      ((eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds).mono
        (fun t ht => le_of_lt ht)
    have hevC : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), w + t • (z - w) ∈ C :=
      (hpos.and hle1).mono (fun t ht => hmemC t ht.1 ht.2)
    have hcont : Filter.Tendsto (fun t : ℝ => w + t • (z - w)) (nhds (0 : ℝ)) (nhds w) := by
      have h := hcm.continuousAt (x := 0)
      simp only [ContinuousAt] at h
      simpa using h
    have hevN : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), w + t • (z - w) ∈
        (Metric.ball (y : PL.E N) (d y) ∩ Metric.ball (y' : PL.E N) (d y')) :=
      (hcont.eventually hN).filter_mono nhdsWithin_le_nhds
    obtain ⟨t, ⟨⟨ht0, _⟩, ⟨htC, htN⟩⟩⟩ := ((hpos.and hle1).and (hevC.and hevN)).exists
    have hgt : A y (w + t • (z - w)) = A y' (w + t • (z - w)) :=
      agree y y' _ htC htN.1 htN.2
    have hsmul : t • ((A y).linear (z - w)) = t • ((A y').linear (z - w)) := by
      have h1 : t • ((A y).linear (z - w)) + A y w =
          t • ((A y').linear (z - w)) + A y' w := by
        rw [← hmt (A y) w z t, ← hmt (A y') w z t]
        exact hgt
      rw [hw] at h1
      exact add_right_cancel h1
    have hL : (A y).linear (z - w) = (A y').linear (z - w) := by
      have h0 : t • ((A y).linear (z - w) - (A y').linear (z - w)) = 0 := by
        rw [smul_sub, hsmul, sub_self]
      rcases smul_eq_zero.mp h0 with hh | hh
      · exact absurd hh (ne_of_gt ht0)
      · exact sub_eq_zero.mp hh
    rw [hpt (A y) w z, hpt (A y') w z, hL, hw]
  -- the class of a base point
  obtain ⟨y₀, hy₀⟩ := hne
  let y0 : C := ⟨y₀, hy₀⟩
  let P : C → Prop := fun y => ∀ z ∈ C, A y z = A y0 z
  have hmono : ∀ (y y' : C), dist (y' : PL.E N) (y : PL.E N) < d y → (P y' ↔ P y) := by
    intro y y' hdist
    have hW : (C ∩ Metric.ball (y : PL.E N) (d y) ∩
        Metric.ball (y' : PL.E N) (d y')).Nonempty :=
      ⟨y', ⟨⟨y'.2, by simpa using hdist⟩, by simpa using hd y'⟩⟩
    have hkey : ∀ z ∈ C, A y z = A y' z := fun z hz => small y y' z hW hz
    exact ⟨fun hy' z hz => (hkey z hz).trans (hy' z hz),
      fun hy z hz => (hkey z hz).symm.trans (hy z hz)⟩
  have hopen : IsOpen {y : C | P y} := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    refine Filter.mem_of_superset (ball_mem_nhds y (hd y)) ?_
    intro y' hy'
    have hdist : dist (y' : PL.E N) (y : PL.E N) < d y := by
      rw [← Subtype.dist_eq]; exact hy'
    exact (hmono y y' hdist).2 hy
  have hclosed : IsClosed {y : C | P y} := by
    rw [← isOpen_compl_iff]
    rw [isOpen_iff_mem_nhds]
    intro y hy
    refine Filter.mem_of_superset (ball_mem_nhds y (hd y)) ?_
    intro y' hy'
    have hdist : dist (y' : PL.E N) (y : PL.E N) < d y := by
      rw [← Subtype.dist_eq]; exact hy'
    intro hy'P
    exact hy ((hmono y y' hdist).1 hy'P)
  have hpre : IsPreconnected (univ : Set C) := by
    haveI : PreconnectedSpace C := isPreconnected_iff_preconnectedSpace.mp hC.isPreconnected
    exact isPreconnected_univ
  have hsub := IsPreconnected.subset_or_subset (s := (univ : Set C))
    (u := {y : C | P y}) (v := {y : C | P y}ᶜ) hopen hclosed.isOpen_compl
    disjoint_compl_right (by intro x _; simp) hpre
  rcases hsub with hsub | hsub
  · refine ⟨A y0, ?_⟩
    intro z hz
    have hP : P ⟨z, hz⟩ := hsub (mem_univ _)
    have hzeq : A ⟨z, hz⟩ z = A y0 z := hP z hz
    have hz' := hA ⟨z, hz⟩ z (by refine ⟨hz, ?_⟩; simpa using hd ⟨z, hz⟩)
    rwa [hzeq] at hz'
  · exact absurd (fun (z : PL.E N) (hz : z ∈ C) => rfl) (hsub (mem_univ y0))

/-- **`exists_subdiv_affine`** (contract §8, aux Hx2c; revised after review): from a `SmoothChart` (local `ψ`-affinity near every point of the frozen faces inside the `3/4`-cube), continuity of `f`, and the *carrier* property of the subdivision, one gets whole-face `ψ`-affinity for every fine face inside `L` whose `f`-image lies in the `3/4`-cube and which meets `f⁻¹(ψ '' closedCube β)`, for `β < 3/4`.  This is the step feeding `PlApproxFrozenForm` in `E4a`.  Suggested proof: by `hcarrier` the fine face `s` lies in a coarse face `σ` with `PL.simp σ ⊆ L`; every point `z` of the convex set `PL.simp s` has `f z ∈ ψ''closedCube (3/4)`, so the `SmoothChart` clause applied to `(σ, z)` gives local `ψ`-linearity of `f` at `z` on a neighbourhood inside `PL.simp s` (because `PL.simp s ⊆ PL.simp σ`); glue the local affine maps along overlaps (`ψ` is injective on `openCube 1`) and apply the convexity/segment argument `Engulf/Aux/exists_affine_of_locally_affine` to `ψ⁻¹ ∘ f` on the convex set `PL.simp s`. -/
theorem exists_subdiv_affine {n p N : ℕ} {M : Type*} [MetricSpace M] {X : Set M} {Γ : PL.Cx N}
    {L : Set (PL.E N)} {f : PL.E N → M} (S : Work.Engulf.SubdivTools N) (ψ : PL.CubeChart n M)
    (hΓ : Γ.faces.Finite) (hL : Work.Engulf.IsSubSp Γ L) (hf : ContinuousOn f Γ.space)
    (h : Work.Engulf.SmoothChart p X Γ L f ψ)
    (hcarrier : ∀ r (s' : Finset (PL.E N)), s' ∈ (S.sdIter r Γ hΓ).faces → PL.simp s' ⊆ L →
      ∃ s ∈ Γ.faces, PL.simp s' ⊆ PL.simp s ∧ PL.simp s ⊆ L)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < 3 / 4) :
    ∃ r, ∀ r' ≥ r, ∀ s ∈ (S.sdIter r' Γ hΓ).faces, PL.simp s ⊆ L →
      f '' PL.simp s ⊆ ψ.toFun '' PL.closedCube (3 / 4 : ℝ) →
      (∃ x ∈ PL.simp s, f x ∈ ψ.toFun '' PL.closedCube β) →
      Work.Engulf.LinIn ψ f (PL.simp s) := by
  classical
  -- `ψ` is injective on the open unit cube
  have hinj : ∀ x ∈ PL.openCube (n := n) 1, ∀ y ∈ PL.openCube (n := n) 1,
      ψ.toFun x = ψ.toFun y → x = y := by
    intro x hx y hy hxy
    have h := ψ.emb.injective
      (show (PL.openCube (n := n) 1).domRestrict ψ.toFun ⟨x, hx⟩ =
        (PL.openCube (n := n) 1).domRestrict ψ.toFun ⟨y, hy⟩ from hxy)
    exact congrArg Subtype.val h
  -- the statement holds for every level of the subdivision, so `r := 0` works
  refine ⟨0, ?_⟩
  intro r' _ s hs hsL hfs _
  rcases Set.eq_empty_or_nonempty (PL.simp s) with hC | hne
  · refine ⟨0, ?_⟩
    intro z hz
    rw [hC] at hz
    exact absurd hz (Set.notMem_empty z)
  · -- the fine face `s` sits in a coarse frozen face `σ`
    obtain ⟨σ, hσ, hss, hσL⟩ := hcarrier r' s hs hsL
    have hloc : ∀ y ∈ PL.simp s, ∃ δ > 0, ∃ A : PL.E N →ᵃ[ℝ] PL.E n,
        ∀ z ∈ PL.simp s ∩ Metric.ball y δ, A z ∈ PL.openCube (n := n) 1 ∧
          f z = ψ.toFun (A z) := by
      intro y hy
      obtain ⟨δ, hδ, A, hA⟩ := h.2 σ hσ hσL y (hss hy) (hfs ⟨y, hy, rfl⟩)
      exact ⟨δ, hδ, A, fun z hz => hA z ⟨hss hz.1, hz.2⟩⟩
    obtain ⟨A, hA⟩ := locally_affine_of_convex ψ.toFun hinj (convex_simp s) hne f hloc
    exact ⟨A, hA⟩

end Work.Engulf.Aux
