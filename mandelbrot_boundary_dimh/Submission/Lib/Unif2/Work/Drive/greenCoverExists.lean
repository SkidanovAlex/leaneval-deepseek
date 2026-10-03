import Mathlib
import Submission.Lib.Unif2.Work.Drive.greenCover
import Submission.Lib.Unif2.Work.Kernel.GreenCoverTools
import Submission.Lib.Unif2.Work.Analysis.RiemannSurface.chartBall_open

/-!
# Existence of the chart-ball cover data `Work.Drive.GreenCover`

`Work.Drive.exists_greenCover`: for an open `Ω` with a prescribed open `U` whose closure is compact
and contained in `Ω`, and two distinct points `a, b ∈ U`, there is a finite chart-ball cover
carrying

* nonnegative weights `ψ i`, smooth (in every chart), summing to `1` on `U`, supported in the chart
  balls of radius `s i` which lie in `Ω`;
* bumps `β i ≡ 1` on `tsupport (ψ i)`, supported in the chart ball of radius `σ i`;
* `s i < σ i < ρ i`, the `ρ i`-balls inside `Ω` and their model balls inside the chart targets;
* the two distinguished charts `ia` (centred at `a`, `y ia = a`) and `ib` (centred at `b`), with
  `a ∉ tsupport (ψ i)`/`a ∉ tsupport (β i)` for `i ≠ ia` and likewise for `b`.

The construction is the same as that of `Work.Kernel.exists_greenCover` (which produces the
`K`-based sibling structure), with the compact set `K := closure U`; the only extra content is that
the two pole charts are *centred* at the poles (`y ia = a`, `y ib = b`), and that the `C¹`-in-chart
regularity of the weights and bumps — the fields `hψc1`, `hβc1` of the structure — is supplied from
the smoothness of the partition of unity (`contDiffAt_comp_symm_of_contMDiff`).

All chart balls are written with `Submission.chartBall` (source intersected in): `chartAt ℂ` is
total and its junk values off the source would otherwise falsify the containments (see
`Submission/Work/Kernel/NOTES_greenCover_REPAIRED.md` and the machine-checked refutation in
`Scratch/kernel/greenCover_refute.lean`).
-/

open Set Metric
open scoped Manifold Topology

set_option linter.style.haveILetI false

noncomputable section

namespace Work.Drive

/-- **The chart representative of a smooth function is `C¹` at every point of the chart.**  This is
`Work.Kernel.chartDiff_of_contMDiff` with the differentiability sharpened to `ContDiffAt ℝ 1`, which
is what the fields `hψc1`, `hβc1` of `Work.Drive.GreenCover` ask. -/
theorem contDiffAt_comp_symm_of_contMDiff {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℝ ℂ) ⊤ X] {f : X → ℝ}
    (hf : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    {c : OpenPartialHomeomorph X ℂ} (hc : c ∈ atlas ℂ X) {x : X} (hx : x ∈ c.source) :
    ContDiffAt ℝ 1 (f ∘ c.symm) (c x) := by
  have hG : HasGroupoid X
      (contDiffGroupoid ((⊤ : ℕ∞) : WithTop ℕ∞) (modelWithCornersSelf ℝ ℂ)) := inferInstance
  have hcmax : c ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ ℂ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) X := by
    intro e' he'
    exact ⟨hG.compatible hc he', hG.compatible he' hc⟩
  have hwit := (contMDiffWithinAt_iff_source_of_mem_maximalAtlas (I := modelWithCornersSelf ℝ ℂ)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (s := Set.univ) hcmax hx).mp
      ((hf.contMDiffAt (x := x)).contMDiffWithinAt)
  simp only [show ((modelWithCornersSelf ℝ ℂ : ModelWithCorners ℝ ℂ ℂ) : ℂ → ℂ) = id from rfl,
    show (((modelWithCornersSelf ℝ ℂ : ModelWithCorners ℝ ℂ ℂ).symm : ℂ → ℂ)) = id from rfl,
    OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply,
    Function.comp_id, Set.range_id, Set.inter_univ, Set.preimage_univ] at hwit
  rw [contMDiffWithinAt_univ] at hwit
  rw [contMDiffAt_iff_contDiffAt] at hwit
  exact hwit.of_le (by simp)

/-- **Existence of the cover data.** -/
theorem exists_greenCover {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [SecondCountableTopology X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω U : Set X} (hΩo : IsOpen Ω) (hUo : IsOpen U) (hUc : IsCompact (closure U))
    (hUΩ : closure U ⊆ Ω) {a b : X} (hab : a ≠ b) (haU : a ∈ U) (hbU : b ∈ U)
    (ra rb : ℝ) (hra : 0 < ra) (hrb : 0 < rb) :
    ∃ (ι : Type) (_ : Fintype ι) (E : GreenCover ι Ω a b U),
      E.ρ E.ia ≤ ra ∧ E.ρ E.ib ≤ rb := by
  classical
  haveI : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  haveI : SigmaCompactSpace X := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : IsManifold (modelWithCornersSelf ℝ ℂ) (⊤ : WithTop ℕ∞) X :=
    Work.SimplyConnected.ABS.isManifold_self_model_real_infty
  have hKc : IsCompact (closure U) := hUc
  have hKΩ : closure U ⊆ Ω := hUΩ
  have haK : a ∈ closure U := subset_closure haU
  have hbK : b ∈ closure U := subset_closure hbU
  -- radii of the two pole charts, each with room inside `Ω` away from the other pole
  obtain ⟨εa₀, hεa₀pos, hεa₀tgt, hεa₀Ω⟩ := Work.Kernel.exists_chartBall_subset (O := Ω \ {b})
    (hΩo.sdiff isClosed_singleton) ⟨hKΩ haK, by simpa using hab⟩
  obtain ⟨εb₀, hεb₀pos, hεb₀tgt, hεb₀Ω⟩ := Work.Kernel.exists_chartBall_subset (O := Ω \ {a})
    (hΩo.sdiff isClosed_singleton) ⟨hKΩ hbK, by simpa using Ne.symm hab⟩
  -- the radii of the two pole charts are additionally controlled by `ra`, `rb` (the caller needs
  -- the pole chart's `ρ`-radius to lie inside the logarithmic-expansion radius of the Green function)
  set εa : ℝ := min εa₀ ra with hεadef
  set εb : ℝ := min εb₀ rb with hεbdef
  have hεapos : 0 < εa := lt_min hεa₀pos hra
  have hεbpos : 0 < εb := lt_min hεb₀pos hrb
  have hεatgt : Metric.ball ((chartAt ℂ a) a) εa ⊆ (chartAt ℂ a).target :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hεa₀tgt
  have hεbtgt : Metric.ball ((chartAt ℂ b) b) εb ⊆ (chartAt ℂ b).target :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hεb₀tgt
  have hεaΩ : Submission.chartBall (chartAt ℂ a) ((chartAt ℂ a) a) εa ⊆ Ω \ {b} :=
    fun x hx => hεa₀Ω ⟨hx.1, Metric.ball_subset_ball (min_le_left _ _) hx.2⟩
  have hεbΩ : Submission.chartBall (chartAt ℂ b) ((chartAt ℂ b) b) εb ⊆ Ω \ {a} :=
    fun x hx => hεb₀Ω ⟨hx.1, Metric.ball_subset_ball (min_le_left _ _) hx.2⟩
  set Ua : Set X := Submission.chartBall (chartAt ℂ a) ((chartAt ℂ a) a) (εa / 4) with hUa
  have hUaopen : IsOpen Ua := Submission.chartBall_isOpen _ _ _
  have haUa : a ∈ Ua := Submission.mem_chartBall.mpr ⟨mem_chart_source ℂ a, by
    rw [Metric.mem_ball, dist_self]; linarith⟩
  set Ub : Set X := Submission.chartBall (chartAt ℂ b) ((chartAt ℂ b) b) (εb / 4) with hUb
  have hUbopen : IsOpen Ub := Submission.chartBall_isOpen _ _ _
  have hbUb : b ∈ Ub := Submission.mem_chartBall.mpr ⟨mem_chart_source ℂ b, by
    rw [Metric.mem_ball, dist_self]; linarith⟩
  set S : Set X := closure U \ (Ua ∪ Ub) with hS
  have hSc : IsCompact S := hKc.diff (hUaopen.union hUbopen)
  have hex : ∀ y : X, ∃ ε : ℝ, y ∈ S → 0 < ε ∧
      Metric.ball ((chartAt ℂ y) y) ε ⊆ (chartAt ℂ y).target ∧
      Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) ε ⊆ Ω \ ({a, b} : Set X) := by
    intro y
    by_cases hy : y ∈ S
    · have hyO : y ∈ Ω \ ({a, b} : Set X) := by
        refine ⟨hKΩ hy.1, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun hya => hy.2 (Or.inl (hya ▸ haUa)), fun hyb => hy.2 (Or.inr (hyb ▸ hbUb))⟩
      obtain ⟨ε, h1, h2, h3⟩ := Work.Kernel.exists_chartBall_subset
        (O := Ω \ ({a, b} : Set X))
        (hΩo.sdiff (isClosed_singleton.union isClosed_singleton)) hyO
      exact ⟨ε, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨1, fun h => absurd h hy⟩
  choose eps heps using hex
  have hcover : S ⊆ ⋃ y : ↥S, Submission.chartBall (chartAt ℂ ((y : ↥S) : X))
      ((chartAt ℂ ((y : ↥S) : X)) ((y : ↥S) : X)) (eps ((y : ↥S) : X) / 4) := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Submission.mem_chartBall.mpr ⟨mem_chart_source ℂ x, ?_⟩⟩
    rw [Metric.mem_ball, dist_self]
    have := (heps x hx).1
    linarith
  obtain ⟨t, ht⟩ := hSc.elim_finite_subcover
    (fun y : ↥S => Submission.chartBall (chartAt ℂ ((y : ↥S) : X))
      ((chartAt ℂ ((y : ↥S) : X)) ((y : ↥S) : X)) (eps ((y : ↥S) : X) / 4))
    (fun y => Submission.chartBall_isOpen _ _ _) hcover
  -- reindex the finite set by `Fin t.card` so that the index type lives in `Type`
  let xt : Fin t.card → X := fun j => (((Finset.equivFin t).symm j : ↥t) : X)
  have hxtS : ∀ j : Fin t.card, xt j ∈ S := by
    intro j
    have h1 : ((((Finset.equivFin t).symm j : ↥t).1 : X)) ∈ S :=
      ((Finset.equivFin t).symm j : ↥t).1.2
    simp only [xt]; exact h1
  have hxt_apply : ∀ (y : ↥S) (hy : y ∈ t), xt (Finset.equivFin t ⟨y, hy⟩) = (y : X) := by
    intro y hy
    simp only [xt, Equiv.symm_apply_apply]
  -- the index type and the radii
  set xv : Option (Option (Fin t.card)) → X := fun i => match i with
    | none => a
    | some none => b
    | some (some j) => xt j with hxv
  set εv : Option (Option (Fin t.card)) → ℝ := fun i => match i with
    | none => εa
    | some none => εb
    | some (some j) => eps (xt j) with hεv
  set sv : Option (Option (Fin t.card)) → ℝ := fun i => εv i / 4 with hsv
  set σv : Option (Option (Fin t.card)) → ℝ := fun i => εv i / 2 with hσv
  set ρv : Option (Option (Fin t.card)) → ℝ := εv with hρv
  have hεvpos : ∀ i, 0 < εv i := by
    rintro (_ | (_ | j))
    · exact hεapos
    · exact hεbpos
    · exact (heps (xt j) (hxtS j)).1
  have hsvpos : ∀ i, 0 < sv i := fun i => by
    have := hεvpos i; simp only [hsv]; linarith
  have hsvσv : ∀ i, sv i < σv i := fun i => by
    have := hεvpos i; simp only [hsv, hσv]; linarith
  have hσvρv : ∀ i, σv i < ρv i := fun i => by
    have := hεvpos i; simp only [hσv, hρv]; linarith
  have htgtv : ∀ i, Metric.ball ((chartAt ℂ (xv i)) (xv i)) (ρv i) ⊆ (chartAt ℂ (xv i)).target := by
    rintro (_ | (_ | j))
    · simpa [hxv, hρv, hεv] using hεatgt
    · simpa [hxv, hρv, hεv] using hεbtgt
    · simpa [hxv, hρv, hεv] using (heps (xt j) (hxtS j)).2.1
  have hballΩv : ∀ i, Submission.chartBall (chartAt ℂ (xv i)) ((chartAt ℂ (xv i)) (xv i)) (ρv i) ⊆ Ω := by
    rintro (_ | (_ | j))
    · intro x hx
      have hx' : x ∈ Submission.chartBall (chartAt ℂ a) ((chartAt ℂ a) a) εa := by
        simpa [hxv, hρv, hεv] using hx
      exact (hεaΩ hx').1
    · intro x hx
      have hx' : x ∈ Submission.chartBall (chartAt ℂ b) ((chartAt ℂ b) b) εb := by
        simpa [hxv, hρv, hεv] using hx
      exact (hεbΩ hx').1
    · intro x hx
      have hx' : x ∈ Submission.chartBall (chartAt ℂ (xt j)) ((chartAt ℂ (xt j)) (xt j)) (eps (xt j)) := by
        simpa [hxv, hρv, hεv] using hx
      exact (heps (xt j) (hxtS j)).2.2 hx' |>.1
  have hscover : closure U ⊆ ⋃ i : Option (Option (Fin t.card)),
      Submission.chartBall (chartAt ℂ (xv i)) ((chartAt ℂ (xv i)) (xv i)) (sv i) := by
    intro x hx
    by_cases hxUa : x ∈ Ua
    · exact Set.mem_iUnion.mpr ⟨none, by simpa [hUa, hxv, hsv, hεv] using hxUa⟩
    · by_cases hxUb : x ∈ Ub
      · exact Set.mem_iUnion.mpr ⟨some none, by simpa [hUb, hxv, hsv, hεv] using hxUb⟩
      · have hxS : x ∈ S := by
          refine ⟨hx, ?_⟩
          simp only [Set.mem_union, not_or]
          exact ⟨hxUa, hxUb⟩
        obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp (ht hxS)
        refine Set.mem_iUnion.mpr ⟨some (some (Finset.equivFin t ⟨y, hyt⟩)), ?_⟩
        have hxj : xt (Finset.equivFin t ⟨y, hyt⟩) = (y : X) := hxt_apply y hyt
        simpa [hxv, hsv, hεv, hxj] using hxy
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ ℂ) hKc.isClosed
    (fun i : Option (Option (Fin t.card)) =>
      Submission.chartBall (chartAt ℂ (xv i)) ((chartAt ℂ (xv i)) (xv i)) (sv i))
    (fun i => Submission.chartBall_isOpen _ _ _) hscover
  have hβex : ∀ i : Option (Option (Fin t.card)), ∃ β : X → ℝ,
      ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
        ((⊤ : ℕ∞) : WithTop ℕ∞) β ∧
      (∀ x ∈ Submission.chartClosedBall (chartAt ℂ (xv i)) ((chartAt ℂ (xv i)) (xv i)) (sv i),
        β x = 1) ∧
      tsupport β ⊆
        Submission.chartBall (chartAt ℂ (xv i)) ((chartAt ℂ (xv i)) (xv i)) (σv i) := by
    intro i
    refine Work.Kernel.exists_contMDiff_eq_one_of_isClosed_subset_isOpen ?_
      (Submission.chartBall_isOpen _ _ _) ?_
    · refine Submission.isClosed_chartClosedBall ?_
      exact (Metric.closedBall_subset_ball (hsvσv i)).trans
        ((Metric.ball_subset_ball (hσvρv i).le).trans (htgtv i))
    · intro x hx
      exact ⟨hx.1, Metric.closedBall_subset_ball (hsvσv i) hx.2⟩
  choose βv hβv using hβex
  -- the partition-of-unity fields
  have hψnonneg : ∀ i (x : X), 0 ≤ f i x := fun i x => f.nonneg i x
  have hψsupp : ∀ i, tsupport (fun x => f i x) ⊆
      Submission.chartBall (chartAt ℂ (xv i)) ((chartAt ℂ (xv i)) (xv i)) (sv i) :=
    fun i => hf i
  have hsumv : ∀ x ∈ closure U, ∑ i, f i x = 1 := by
    intro x hx
    have h1 := SmoothPartitionOfUnity.sum_finsupport' f x hx (Finset.subset_univ (f.finsupport x))
    simpa using h1
  have hψdiff : ∀ k i, Work.Drive.ChartDiff (chartAt ℂ (xv k)) (fun x => f i x) Ω :=
    fun k i => Work.Kernel.chartDiff_of_contMDiff (f i).contMDiff (chart_mem_atlas ℂ (xv k)) Ω
  -- the two poles
  have hya : xv none = a := rfl
  have hyb : xv (some none) = b := rfl
  have hClosed_sub_ball : ∀ i, Submission.chartClosedBall (chartAt ℂ (xv i)) ((chartAt ℂ (xv i)) (xv i)) (σv i)
      ⊆ Submission.chartBall (chartAt ℂ (xv i)) ((chartAt ℂ (xv i)) (xv i)) (εv i) := by
    intro i x hx
    obtain ⟨hs, hb⟩ := Submission.mem_chartClosedBall.mp hx
    refine Submission.mem_chartBall.mpr ⟨hs, ?_⟩
    rw [hσv] at hb
    exact Metric.closedBall_subset_ball (by linarith [hεvpos i]) hb
  -- supports inside the closed `σ`-discs
  have hψ_closed : ∀ i, tsupport (fun x => f i x) ⊆
      Submission.chartClosedBall (chartAt ℂ (xv i)) ((chartAt ℂ (xv i)) (xv i)) (σv i) := by
    intro i x hx
    obtain ⟨hs, hb⟩ := hψsupp i hx
    exact ⟨hs, (Metric.closedBall_subset_closedBall (hsvσv i).le)
      (Metric.ball_subset_closedBall hb)⟩
  have hψ_closed_s : ∀ i, tsupport (fun x => f i x) ⊆
      Submission.chartClosedBall (chartAt ℂ (xv i)) ((chartAt ℂ (xv i)) (xv i)) (sv i) := by
    intro i x hx
    obtain ⟨hs, hb⟩ := hψsupp i hx
    exact ⟨hs, Metric.ball_subset_closedBall hb⟩
  have hβ_closed : ∀ i, tsupport (βv i) ⊆
      Submission.chartClosedBall (chartAt ℂ (xv i)) ((chartAt ℂ (xv i)) (xv i)) (σv i) := by
    intro i x hx
    obtain ⟨hs, hb⟩ := (hβv i).2.2 hx
    exact ⟨hs, Metric.ball_subset_closedBall hb⟩
  -- the poles avoid the other charts
  have ha_nmem_closed : ∀ i, i ≠ none → a ∉ Submission.chartClosedBall (chartAt ℂ (xv i))
      ((chartAt ℂ (xv i)) (xv i)) (σv i) := by
    rintro (_ | (_ | j)) hi
    · exact absurd rfl hi
    · intro hmem
      have hmem' : a ∈ Submission.chartBall (chartAt ℂ b) ((chartAt ℂ b) b) εb := by
        simpa [hxv, hεv] using hClosed_sub_ball (some none) hmem
      exact (hεbΩ hmem').2 rfl
    · intro hmem
      have hmem' : a ∈ Submission.chartBall (chartAt ℂ (xt j)) ((chartAt ℂ (xt j)) (xt j)) (eps (xt j)) := by
        simpa [hxv, hεv] using hClosed_sub_ball (some (some j)) hmem
      exact ((heps (xt j) (hxtS j)).2.2 hmem').2 (by simp)
  have hb_nmem_closed : ∀ i, i ≠ some none → b ∉ Submission.chartClosedBall (chartAt ℂ (xv i))
      ((chartAt ℂ (xv i)) (xv i)) (σv i) := by
    rintro (_ | (_ | j)) hi
    · intro hmem
      have hmem' : b ∈ Submission.chartBall (chartAt ℂ a) ((chartAt ℂ a) a) εa := by
        simpa [hxv, hεv] using hClosed_sub_ball none hmem
      exact (hεaΩ hmem').2 rfl
    · exact absurd rfl hi
    · intro hmem
      have hmem' : b ∈ Submission.chartBall (chartAt ℂ (xt j)) ((chartAt ℂ (xt j)) (xt j)) (eps (xt j)) := by
        simpa [hxv, hεv] using hClosed_sub_ball (some (some j)) hmem
      exact ((heps (xt j) (hxtS j)).2.2 hmem').2 (by simp)
  have hρianone : ρv none ≤ ra := by
    show εa ≤ ra
    rw [hεadef]; exact min_le_right _ _
  have hρibnone : ρv (some none) ≤ rb := by
    show εb ≤ rb
    rw [hεbdef]; exact min_le_right _ _
  refine ⟨Option (Option (Fin t.card)), inferInstance,
    { y := xv, s := sv, σ := σv, ρ := ρv, ψ := fun i x => f i x, β := βv, ia := none,
      ib := some none, hya := hya, hyb := hyb, hΩo := hΩo, hUo := hUo, hUΩ := fun x hx => hUΩ (subset_closure hx),
      haU := haU, hbU := hbU, hspos := hsvpos, hsσ := hsvσv, hσρ := hσvρv, htgt := htgtv,
      hballΩ := hballΩv, hballsrc := fun i => Set.inter_subset_left, hψnonneg := hψnonneg,
      hψsupp := hψsupp, hψsrc := fun i => (hψsupp i).trans Set.inter_subset_left,
      hψdiff := hψdiff,
      hψc1 := fun k i x hx => contDiffAt_comp_symm_of_contMDiff (f i).contMDiff
        (chart_mem_atlas ℂ (xv k)) hx,
      hsum := fun x hx => hsumv x (subset_closure hx),
      ha_nmem := fun i hi hmem => ha_nmem_closed i hi (hψ_closed i hmem),
      hb_nmem := fun i hi hmem => hb_nmem_closed i hi (hψ_closed i hmem),
      hβone := fun i x hx => (hβv i).2.1 x (hψ_closed_s i hx),
      hβsupp := fun i => (hβv i).2.2, hβsrc := fun i => (hβv i).2.2.trans Set.inter_subset_left,
      hβdiff := fun k i => Work.Kernel.chartDiff_of_contMDiff (hβv i).1 (chart_mem_atlas ℂ (xv k)) Ω,
      hβc1 := fun k i x hx => contDiffAt_comp_symm_of_contMDiff (hβv i).1
        (chart_mem_atlas ℂ (xv k)) hx,
      hβ_a_nmem := fun i hi hmem => ha_nmem_closed i hi (hβ_closed i hmem),
      hβ_b_nmem := fun i hi hmem => hb_nmem_closed i hi (hβ_closed i hmem) }, ?_, ?_⟩
  · show ρv none ≤ ra
    exact hρianone
  · show ρv (some none) ≤ rb
    exact hρibnone

end Work.Drive
