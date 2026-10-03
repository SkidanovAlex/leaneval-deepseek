import Mathlib
import Submission.Lib.Unif2.Work.Kernel.GreenCover
import Submission.Lib.Unif2.Work.Kernel.GreenCoverTools
import Submission.Lib.Unif2.Work.Drive.greenCoverExists
import Submission.Lib.Unif2.Work.Analysis.RiemannSurface.exists_chartBall_smoothPartitionOfUnity
import Submission.Lib.Unif2.Work.Analysis.Harmonic.integral_inner_gradient_eq_zero

/-!
# Existence of the chart-ball cover data, with the pole charts centred at the poles

This is `Work.Kernel.exists_greenCover` with four extra conjuncts: the two distinguished charts are
*centred* at the poles (`E.y E.ia = a`, `E.y E.ib = b`) and their `ρ`-radii are bounded by prescribed
positive numbers.  The centredness is what makes the logarithmic expansion
`Work.SimplyConnected.ABS.localPoleExpansion_of_hasLogPoleOn` (available in the chart `chartAt ℂ a`)
applicable to the pole chart of the cover.

# Existence of the chart-ball cover data (`Work.Kernel.GreenCover`)

`Work.Kernel.exists_greenCover`: for a compact `K` inside an open `Ω` of a second countable complex
one-manifold and two distinct points `a, b ∈ K`, there is a finite chart-ball cover carrying

* nonnegative weights `ψ i` summing to `1` on `K`, supported in the chart balls of radius `s i`;
* bumps `β i ≡ 1` on the *closed* chart discs of radius `s i`, supported in the chart balls of
  radius `σ i`;
* `s i < σ i < ρ i`, with the `ρ i`-balls inside `Ω` and their model balls inside the chart targets;

and with `a` (resp. `b`) in the `s ia`-ball (resp. `s ib`-ball) of *its* chart only (the `σ`-discs of
all other charts avoid it).

The construction is the standard one (compare `Submission/Work/Drive/energyGreenCover.lean`, which
proves the analogue without bumps and up to a different index universe):

* `K` minus a small ball around each pole is compact and is covered by finitely many chart balls, each
  with room inside `Ω ∖ {a, b}`; the two poles get one chart each, centred at the pole, with room
  inside `Ω ∖ {other pole}`;
* the charts are reindexed by `Fin t.card`, so the index type lives in `Type` (as the statement asks);
* `ψ` is a smooth partition of unity subordinate to the *small* balls, on the *real* model
  (`Work.SimplyConnected.ABS.isManifold_self_model_real_infty`) — Mathlib's
  `SmoothPartitionOfUnity.exists_isSubordinate`;
* each `β i` is a smooth bump `≡ 1` on the closed chart disc and supported in the open chart ball,
  produced by `Work.Kernel.exists_contMDiff_eq_one_of_isClosed_subset_isOpen` (whose topological
  support bound comes from the partition-of-unity machinery, so that no closure of a chart ball is
  ever needed);
* every differentiability requirement is `Work.Kernel.chartDiff_of_contMDiff`.

All the chart balls are written as `Submission.chartBall` / `Submission.chartClosedBall`, i.e. with the
chart source intersected in: the values of `chartAt` off its source are junk and would otherwise
falsify the statements (see the module docstring of `Submission/Work/Kernel/GreenCover.lean` and the
machine-checked refutation in `Scratch/kernel/greenCover_refute.lean`).
-/

open Set Metric
open scoped Manifold Topology

set_option linter.style.haveILetI false

namespace Work.Kernel

theorem exists_greenCover_centred {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [SecondCountableTopology X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω K : Set X} (hΩo : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) {a b : X} (hab : a ≠ b)
    (ha : a ∈ K) (hb : b ∈ K) (ra rb : ℝ) (hra : 0 < ra) (hrb : 0 < rb) :
    ∃ (ι : Type) (_ : Fintype ι) (E : Work.Kernel.GreenCover ι Ω K a b),
      E.y E.ia = a ∧ E.y E.ib = b ∧ E.ρ E.ia ≤ ra ∧ E.ρ E.ib ≤ rb ∧
      (∀ k i, ∀ x ∈ (chartAt ℂ (E.y k)).source,
        ContDiffAt ℝ 1 ((E.ψ i) ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x)) ∧
      (∀ k i, ∀ x ∈ (chartAt ℂ (E.y k)).source,
        ContDiffAt ℝ 1 ((E.β i) ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x)) := by
  classical
  -- the ambient structure: locally compact and σ-compact (for the partition of unity), and smooth
  -- over the real model (the complex `C¹` structure is smooth; `Work.SimplyConnected.ABS`)
  haveI : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  haveI : SigmaCompactSpace X := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : IsManifold (modelWithCornersSelf ℝ ℂ) (⊤ : WithTop ℕ∞) X :=
    Work.SimplyConnected.ABS.isManifold_self_model_real_infty
  -- radii of the two pole charts, each with room inside `Ω` away from the other pole
  obtain ⟨εa₀, hεa₀pos, hεa₀tgt, hεa₀Ω⟩ := Work.Kernel.exists_chartBall_subset (O := Ω \ {b})
    (hΩo.sdiff isClosed_singleton) ⟨hKΩ ha, by simpa using hab⟩
  obtain ⟨εb₀, hεb₀pos, hεb₀tgt, hεb₀Ω⟩ := Work.Kernel.exists_chartBall_subset (O := Ω \ {a})
    (hΩo.sdiff isClosed_singleton) ⟨hKΩ hb, by simpa using Ne.symm hab⟩
  -- the two pole radii, capped by the prescribed `ra`, `rb`
  set εa : ℝ := min εa₀ ra with hεa_def
  set εb : ℝ := min εb₀ rb with hεb_def
  have hεapos : 0 < εa := lt_min hεa₀pos hra
  have hεbpos : 0 < εb := lt_min hεb₀pos hrb
  have hεatgt : Metric.ball ((chartAt ℂ a) a) εa ⊆ (chartAt ℂ a).target :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hεa₀tgt
  have hεbtgt : Metric.ball ((chartAt ℂ b) b) εb ⊆ (chartAt ℂ b).target :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hεb₀tgt
  have chartBall_mono' : ∀ {c : OpenPartialHomeomorph X ℂ} {w : ℂ} {r r' : ℝ}, r' ≤ r →
      Submission.chartBall c w r' ⊆ Submission.chartBall c w r := by
    intro c w r r' h x hx
    exact ⟨hx.1, Metric.ball_subset_ball h hx.2⟩
  have hεaΩ : Submission.chartBall (chartAt ℂ a) ((chartAt ℂ a) a) εa ⊆ Ω \ {b} :=
    (chartBall_mono' (min_le_left _ _)).trans hεa₀Ω
  have hεbΩ : Submission.chartBall (chartAt ℂ b) ((chartAt ℂ b) b) εb ⊆ Ω \ {a} :=
    (chartBall_mono' (min_le_left _ _)).trans hεb₀Ω
  set Ua : Set X := Submission.chartBall (chartAt ℂ a) ((chartAt ℂ a) a) (εa / 4) with hUa
  have hUaopen : IsOpen Ua := Submission.chartBall_isOpen _ _ _
  have haUa : a ∈ Ua := Submission.mem_chartBall.mpr ⟨mem_chart_source ℂ a, by
    rw [Metric.mem_ball, dist_self]; linarith⟩
  set Ub : Set X := Submission.chartBall (chartAt ℂ b) ((chartAt ℂ b) b) (εb / 4) with hUb
  have hUbopen : IsOpen Ub := Submission.chartBall_isOpen _ _ _
  have hbUb : b ∈ Ub := Submission.mem_chartBall.mpr ⟨mem_chart_source ℂ b, by
    rw [Metric.mem_ball, dist_self]; linarith⟩
  set S : Set X := K \ (Ua ∪ Ub) with hS
  have hSc : IsCompact S := hK.diff (hUaopen.union hUbopen)
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
  have hscover : K ⊆ ⋃ i : Option (Option (Fin t.card)),
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
    (modelWithCornersSelf ℝ ℂ) hK.isClosed
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
    refine exists_contMDiff_eq_one_of_isClosed_subset_isOpen ?_ (Submission.chartBall_isOpen _ _ _) ?_
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
  have hsumv : ∀ x ∈ K, ∑ i, f i x = 1 := by
    intro x hx
    have h1 := SmoothPartitionOfUnity.sum_finsupport' f x hx (Finset.subset_univ (f.finsupport x))
    simpa using h1
  have hψdiff : ∀ k i, Work.Drive.ChartDiff (chartAt ℂ (xv k)) (fun x => f i x) Ω :=
    fun k i => chartDiff_of_contMDiff (f i).contMDiff (chart_mem_atlas ℂ (xv k)) Ω
  -- the two poles
  have ha_mem : a ∈ Submission.chartBall (chartAt ℂ (xv none)) ((chartAt ℂ (xv none)) (xv none))
      (sv none) := by
    simpa [hUa, hxv, hsv, hεv] using haUa
  have hb_mem : b ∈ Submission.chartBall (chartAt ℂ (xv (some none)))
      ((chartAt ℂ (xv (some none))) (xv (some none))) (sv (some none)) := by
    simpa [hUb, hxv, hsv, hεv] using hbUb
  have hClosed_sub_ball : ∀ i, Submission.chartClosedBall (chartAt ℂ (xv i)) ((chartAt ℂ (xv i)) (xv i)) (σv i)
      ⊆ Submission.chartBall (chartAt ℂ (xv i)) ((chartAt ℂ (xv i)) (xv i)) (εv i) := by
    intro i x hx
    obtain ⟨hs, hb⟩ := Submission.mem_chartClosedBall.mp hx
    refine Submission.mem_chartBall.mpr ⟨hs, ?_⟩
    rw [hσv] at hb
    exact Metric.closedBall_subset_ball (by linarith [hεvpos i]) hb
  have ha_nmem : ∀ i, i ≠ none → a ∉ Submission.chartClosedBall (chartAt ℂ (xv i))
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
  have hb_nmem : ∀ i, i ≠ some none → b ∉ Submission.chartClosedBall (chartAt ℂ (xv i))
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
  have hβone : ∀ i, ∀ x ∈ Submission.chartClosedBall (chartAt ℂ (xv i)) ((chartAt ℂ (xv i)) (xv i)) (sv i),
      βv i x = 1 := fun i => (hβv i).2.1
  have hβsupp : ∀ i, tsupport (βv i) ⊆
      Submission.chartBall (chartAt ℂ (xv i)) ((chartAt ℂ (xv i)) (xv i)) (σv i) :=
    fun i => (hβv i).2.2
  have hβdiff : ∀ k i, Work.Drive.ChartDiff (chartAt ℂ (xv k)) (βv i) Ω :=
    fun k i => chartDiff_of_contMDiff (hβv i).1 (chart_mem_atlas ℂ (xv k)) Ω
  refine ⟨Option (Option (Fin t.card)), inferInstance,
    ⟨xv, sv, σv, ρv, fun i x => f i x, βv, none, some none, hsvpos, hsvσv, hσvρv, htgtv, hballΩv,
      hψnonneg, hψsupp, hsumv, hψdiff, ha_mem, ha_nmem, hb_mem, hb_nmem, hβone, hβsupp, hβdiff⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · show ρv none ≤ ra
    exact min_le_right _ _
  · show ρv (some none) ≤ rb
    exact min_le_right _ _
  · intro k i x hx
    exact Work.Drive.contDiffAt_comp_symm_of_contMDiff (f i).contMDiff
      (chart_mem_atlas ℂ (xv k)) hx
  · intro k i x hx
    exact Work.Drive.contDiffAt_comp_symm_of_contMDiff (hβv i).1
      (chart_mem_atlas ℂ (xv k)) hx

end Work.Kernel
