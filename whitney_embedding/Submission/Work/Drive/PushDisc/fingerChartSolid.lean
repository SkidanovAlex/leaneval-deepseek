import Mathlib
import Submission.Work.Drive.PushDisc.lensWiringDefs
import Submission.Work.Drive.PushDisc.lensWiringConfig
import Submission.Work.Drive.PushDisc.exists_chart_of_arc
import Submission.Work.Drive.PushDisc.asymSignTransport
import Submission.Work.Drive.PushDisc.smoothChartOfInjOnImmersion

/-!
# `Work.Drive.PushDisc.fingerChartSolid` (D5): the finger's `(x,v)`-chart with its window

The structure `Work.Drive.PushDisc.LWFingerChart` is the finger's chart: an `OpenPartialHomeomorph`
of `M` into `ℝ^{k+1}` which straightens the second bigon arc `γ₂` onto the segment
`t ↦ (2t-1, 0)`, whose source lies in `W` and avoids `p₁, q₁`, **and whose target contains a window**
`{|x| ≤ X' , ‖v‖ ≤ r}` (`X' > 1`, `r > 0`).

Everything is built from the proved brick `Work.Drive.PushDisc.exists_chart_of_arc` (which supplies
the chart, the source inside `W` and the arc row), plus two small steps:

* `exists_window_of_chart`: **a window is automatic** for any partial homeomorphism whose target
  contains the straight segment.  The target is open, so the set of admissible `x` is an open
  neighbourhood of `[-1,1]`, giving `X' > 1`; the segment is compact, so a thickening of it (hence
  the thin window) still lies in the target.  No geometry is used — only openness and compactness.
* the shrink `c ↦ c.restrOpen S` with `S = {p₁}ᶜ ∩ {q₁}ᶜ`, which removes `p₁` and `q₁` from the
  source while keeping the arc row (`c` and `c.restrOpen S` are the *same function*, and the arc
  misses `p₁` and `q₁` by `hγdisj`).

The remaining bookkeeping is the type equality `k' + 1 = k + 1` between the index returned by
`exists_chart_of_arc` (called at `n = k+1`) and `k`; `splitE_cast_eq` converts the transported arc
row into the exact form demanded by `LWFingerChart`.
-/

open scoped ContDiff Manifold
open Set Metric

namespace Work.Drive.PushDisc

/-- `splitE k` as a continuous linear map (used only to bound it in the window argument). -/
noncomputable def splitEM (k : ℕ) :
    (ℝ × EuclideanSpace ℝ (Fin k)) →L[ℝ] EuclideanSpace ℝ (Fin (k + 1)) :=
  LinearMap.toContinuousLinearMap (splitE k :
    (ℝ × EuclideanSpace ℝ (Fin k)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (k + 1)))

@[simp] theorem splitEM_apply (k : ℕ) (t : ℝ × EuclideanSpace ℝ (Fin k)) :
    splitEM k t = splitE k t := rfl

/-- The cast bookkeeping of `exists_chart_of_arc`: for `hk : k' + 1 = k + 1`, the transported
straight point `hk ▸ splitE k' (a, 0)` is the straight point `splitE k (a, 0)`.  (`Nat.succ.inj`
forces `k' = k`, after which the cast is the identity on the common type `ℝ^{k+1}`.) -/
theorem splitE_cast_eq {k k' : ℕ} (hk : k' + 1 = k + 1) (a : ℝ) :
    hk ▸ (splitE k' (a, (0 : EuclideanSpace ℝ (Fin k')))) =
      splitE k (a, (0 : EuclideanSpace ℝ (Fin k))) := by
  have h : k' = k := Nat.succ.inj hk
  subst h
  simp

/-- **The window of a chart whose target contains a straight segment.**

If the target of `c` contains the image `{splitE k (x, 0) | |x| ≤ 1}` of `[-1,1]` (which is what the
arc row of a finger chart supplies), then it contains a *window* `{|x| ≤ X' , ‖v‖ ≤ r}` of the
straight line, for some `X' > 1` and `r > 0`.  The proof is purely topological:

* the set of admissible `x` is open (preimage of the open target) and contains `[-1,1]`, so it
  contains `[-X', X']` for some `X' > 1`;
* the straight segment over `[-X', X']` is compact and inside the target, so (`cthickening`) a
  thickening of it is inside the target; the window is contained in that thickening because
  `splitE k` is a continuous linear map. -/
theorem exists_window_of_chart {k : ℕ} {M : Type*} [TopologicalSpace M]
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    (γ : ℝ → M)
    (hsrc : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ c.source)
    (hval : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      c (γ t) = splitE k (((2 : ℝ) * t - 1), 0)) :
    ∃ X' r : ℝ, 1 < X' ∧ 0 < r ∧ ∀ p : ℝ × EuclideanSpace ℝ (Fin k),
      |p.1| ≤ X' → ‖p.2‖ ≤ 1 → splitE k (p.1, r • p.2) ∈ c.target := by
  classical
  -- ## the straight segment lies in the target (from the arc row)
  have hseg : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → splitE k (x, 0) ∈ c.target := by
    intro x hx
    have ht : (x + 1) / 2 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h1 : c (γ ((x + 1) / 2)) = splitE k (x, 0) := by
      rw [hval ((x + 1) / 2) ht, show (2 : ℝ) * ((x + 1) / 2) - 1 = x from by ring]
    rw [← h1]
    exact c.map_source (hsrc _ ht)
  -- ## the set of admissible `x` is open
  have hcont : Continuous (fun x : ℝ =>
      splitE k (x, (0 : EuclideanSpace ℝ (Fin k)))) :=
    (splitEM k).continuous.comp (continuous_id.prodMk continuous_const)
  have hSopen : IsOpen ((fun x : ℝ =>
      splitE k (x, (0 : EuclideanSpace ℝ (Fin k)))) ⁻¹' c.target) :=
    c.open_target.preimage hcont
  have hIcc : Set.Icc (-1 : ℝ) 1 ⊆
      ((fun x : ℝ => splitE k (x, (0 : EuclideanSpace ℝ (Fin k)))) ⁻¹' c.target) :=
    fun x hx => hseg x hx
  obtain ⟨δ, hδpos, hδsub⟩ := IsCompact.exists_cthickening_subset_open isCompact_Icc hSopen hIcc
  -- ## the window's `x`-range, slightly longer than the segment
  set X' : ℝ := 1 + δ / 2 with hX'def
  have hX'1 : 1 < X' := by rw [hX'def]; linarith
  have hX'mem : ∀ x ∈ Set.Icc (-X') X', x ∈ Metric.cthickening δ (Set.Icc (-1 : ℝ) 1) := by
    intro x hx
    rcases le_or_gt x (-1) with hle | hlt
    · refine Metric.mem_cthickening_of_dist_le x (-1) δ _ (by norm_num) ?_
      rw [Real.dist_eq, abs_of_nonpos (by linarith)]
      rw [hX'def] at hx; linarith [hx.1]
    rcases le_or_gt (1 : ℝ) x with hle1 | hlt1
    · refine Metric.mem_cthickening_of_dist_le x 1 δ _ (by norm_num) ?_
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]
      rw [hX'def] at hx; linarith [hx.2]
    · refine Metric.mem_cthickening_of_dist_le x x δ _ ⟨le_of_lt hlt, le_of_lt hlt1⟩ ?_
      rw [dist_self]
      exact hδpos.le
  have hX'sub : ∀ x ∈ Set.Icc (-X') X', splitE k (x, 0) ∈ c.target :=
    fun x hx => hδsub (hX'mem x hx)
  -- ## the segment over `[-X', X']` is compact, so a thickening of it is still in the target
  set K : Set (EuclideanSpace ℝ (Fin (k + 1))) :=
    (fun x : ℝ => splitE k (x, (0 : EuclideanSpace ℝ (Fin k)))) '' Set.Icc (-X') X' with hKdef
  have hKcpt : IsCompact K := isCompact_Icc.image hcont
  have hKsub : K ⊆ c.target := by
    rintro y ⟨x, hx, rfl⟩
    exact hX'sub x hx
  obtain ⟨δ', hδ'pos, hδ'sub⟩ := IsCompact.exists_cthickening_subset_open hKcpt c.open_target hKsub
  -- ## the window is contained in that thickening
  set r : ℝ := δ' / (2 * (‖splitEM k‖ + 1)) with hrdef
  have hrpos : 0 < r := by rw [hrdef]; positivity
  refine ⟨X', r, hX'1, hrpos, ?_⟩
  intro p hp1 hp2
  have hdiff : splitEM k (p.1, r • p.2) - splitEM k (p.1, (0 : EuclideanSpace ℝ (Fin k))) =
      splitEM k ((0 : ℝ), r • p.2) := by
    rw [← map_sub]
    congr 1
    ext <;> simp
  have hdist : dist (splitEM k (p.1, r • p.2))
      (splitEM k (p.1, (0 : EuclideanSpace ℝ (Fin k)))) ≤ δ' := by
    rw [dist_eq_norm, hdiff]
    have hC : (0 : ℝ) ≤ ‖splitEM k‖ := norm_nonneg _
    calc ‖splitEM k ((0 : ℝ), r • p.2)‖ ≤ ‖splitEM k‖ * ‖((0 : ℝ), r • p.2)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖splitEM k‖ * ‖r • p.2‖ := by rw [Prod.norm_mk]; simp
      _ ≤ ‖splitEM k‖ * r := by
          have hrle : ‖r • p.2‖ ≤ r := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos]
            nlinarith [hp2, hrpos.le]
          exact mul_le_mul_of_nonneg_left hrle hC
      _ ≤ δ' := by
          have hr2 : (‖splitEM k‖ + 1) * r = δ' / 2 := by
            rw [hrdef]; field_simp
          nlinarith [hr2, hC, hrpos.le, hδ'pos.le]
  have hdist2 : dist (splitE k (p.1, r • p.2))
      (splitE k (p.1, (0 : EuclideanSpace ℝ (Fin k)))) ≤ δ' := by
    simpa using hdist
  exact hδ'sub (Metric.mem_cthickening_of_dist_le _ _ δ' K ⟨p.1, abs_le.mp hp1, rfl⟩ hdist2)

theorem fingerChartSolid {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (C : Work.Drive.PushDisc.LWConfig (k + 1) M) :
    Nonempty (Work.Drive.PushDisc.LWFingerChart k M C) := by
  classical
  -- ## 1. the endpoints of the first arc lie off the second arc
  have hp₁arc : C.p₁ ∉ C.γ₂ '' Set.Icc (0 : ℝ) 1 := by
    rintro ⟨t, ht, ht1⟩
    have h0 : C.γ₁ 0 = C.γ₂ t := by rw [C.hγ₁0, ht1]
    rcases C.hγdisj 0 (by norm_num) t ht h0 with ⟨_, ht0⟩ | ⟨h10, _⟩
    · exact C.hp₁p₂ (by rw [← ht1, ht0, C.hγ₂0])
    · exact absurd h10 (by norm_num)
  have hq₁arc : C.q₁ ∉ C.γ₂ '' Set.Icc (0 : ℝ) 1 := by
    rintro ⟨t, ht, ht1⟩
    have h0 : C.γ₁ 1 = C.γ₂ t := by rw [C.hγ₁1, ht1]
    rcases C.hγdisj 1 (by norm_num) t ht h0 with ⟨h01, _⟩ | ⟨_, ht1'⟩
    · exact absurd h01 (by norm_num)
    · exact C.hq₁q₂ (by rw [← ht1, ht1', C.hγ₂1])
  -- ## 2. the clean chart of the arc (proved brick), in the disjunct order it wants
  have hclean' : ∀ y z : M, y ∈ C.W → z ∈ C.W → C.f y = C.f z →
      y = z ∨ (y = C.p₂ ∧ z = C.p₁) ∨ (y = C.p₁ ∧ z = C.p₂) ∨
        (y = C.q₂ ∧ z = C.q₁) ∨ (y = C.q₁ ∧ z = C.q₂) := by
    intro y z hy hz hyz
    rcases C.hclean y z hy hz hyz with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  obtain ⟨k', hk, c, hcsmooth, hcsrc, hcarc, harc_raw⟩ :=
    exists_chart_of_arc (n := k + 1) C.hn C.f C.hf C.himm C.W C.hWopen C.hWcpt
      C.p₁ C.p₂ C.q₁ C.q₂ C.hW₂ C.hW₄ C.hp₁p₂.symm C.hfp.symm hclean' C.hsep
      C.γ₂ C.hγ₂ C.hγ₂0 C.hγ₂1 C.hγW₂ C.hγ₂inj C.hγ₂smooth C.hγ₂imm hp₁arc hq₁arc
  -- the arc row in the exact form demanded below (the index `k'` is `k` on the nose)
  have harc : ∀ t ∈ Set.Icc (0 : ℝ) 1, c (C.γ₂ t) = splitE k (((2 : ℝ) * t - 1), 0) :=
    fun t ht => (harc_raw t ht).trans (splitE_cast_eq hk (2 * t - 1))
  -- ## 3. shrink the source so that it misses `p₁` and `q₁`
  set S : Set M := {C.p₁}ᶜ ∩ {C.q₁}ᶜ with hSdef
  have hSopen : IsOpen S := isOpen_compl_singleton.inter isOpen_compl_singleton
  set c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))) :=
    c.restrOpen S hSopen with hc'def
  have hc'src : c'.source = c.source ∩ S := by
    rw [hc'def]
    exact OpenPartialHomeomorph.restrOpen_source c S hSopen
  have hc'fun : ⇑c' = ⇑c := by
    rw [hc'def]
    exact OpenPartialHomeomorph.coe_restrOpen c hSopen
  have hc'symm : ⇑c'.symm = ⇑c.symm := by
    rw [hc'def]
    exact OpenPartialHomeomorph.coe_restrOpen_symm c hSopen
  have hp₁c : C.p₁ ∉ c'.source := by
    rw [hc'src]
    rintro ⟨-, h2, -⟩
    exact h2 rfl
  have hq₁c : C.q₁ ∉ c'.source := by
    rw [hc'src]
    rintro ⟨-, -, h2⟩
    exact h2 rfl
  have hsrc' : c'.source ⊆ C.W := by
    rw [hc'src]
    exact fun x hx => hcsrc hx.1
  have harc' : C.γ₂ '' Set.Icc (0 : ℝ) 1 ⊆ c'.source := by
    rintro y ⟨t, ht, rfl⟩
    rw [hc'src]
    exact ⟨hcarc ⟨t, ht, rfl⟩, (fun h => hp₁arc ⟨t, ht, h⟩), (fun h => hq₁arc ⟨t, ht, h⟩)⟩
  have hval' : ∀ t ∈ Set.Icc (0 : ℝ) 1, c' (C.γ₂ t) = splitE k (((2 : ℝ) * t - 1), 0) := by
    intro t ht
    rw [hc'fun]
    exact harc t ht
  -- ## 4. the shrunk chart is still a smooth chart
  have hcsmooth' : Work.Whitney.IsSmoothChart c' := by
    constructor
    · have hsub : c'.source ⊆ c.source := by rw [hc'src]; exact inter_subset_left
      have h := hcsmooth.1.mono hsub
      simpa [hc'fun] using h
    · have htsub : c'.target ⊆ c.target := by
        rw [hc'def]
        show ((c.restrOpen S hSopen).toPartialEquiv).target ⊆ c.target
        rw [OpenPartialHomeomorph.restrOpen_toPartialEquiv, PartialEquiv.restr_target]
        exact inter_subset_left
      have h := hcsmooth.2.mono htsub
      simpa [hc'symm] using h
  -- ## 5. the window is free
  obtain ⟨X', r, hX', hr, hwin⟩ :=
    exists_window_of_chart c' C.γ₂ (fun t ht => harc' ⟨t, ht, rfl⟩) hval'
  -- ## 6. assemble the finger chart
  exact ⟨{ c := c'
           hcsmooth := hcsmooth'
           hcsrc := hsrc'
           hcarc := harc'
           hp₁c := hp₁c
           hq₁c := hq₁c
           harc₂ := hval'
           X' := X'
           hX' := hX'
           r := r
           hr := hr
           hwin := hwin }⟩

end Work.Drive.PushDisc
