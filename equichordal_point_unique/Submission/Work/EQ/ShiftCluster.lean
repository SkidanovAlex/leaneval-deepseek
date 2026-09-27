import Mathlib
import Submission.Work.EQ.TorusZ
import Submission.Work.EQ.TorusZ_basics
import Submission.Work.Topology.not_countable_clusterSet

/-!
# The shifted cluster set of a path in `ℂ*` is uncountable

Rychlik's Theorems 8 and 11 use the following fact.  Let `u : ℝ → ℂ*` be continuous on `(-∞,1)`
with no limit in `ℂ*` at `1⁻`, and let `r₁ ≤ λ r₂`.  Then the set of `z` in the annulus
`{r₁ ≤ ‖z‖ ≤ r₂}` which are limits of shifted values `λ^{p_k} u(s_k)` (`s_k → 1⁻`, `p_k : ℤ`) is
uncountable (Rychlik (140)).

The proof: the image `Φ` of `u` in the torus `ℂ*/λ^ℤ` is continuous; if `Φ` converged then `u`
would converge in `ℂ*` (coverings do not create limits), so by `not_countable_clusterSet` the
cluster set of `Φ` in the compact torus is uncountable.  Every cluster point `t` of `Φ` is the
image of a point `z` of the shifted cluster set: choose radii `s_k → 1⁻` with `Φ(s_k) → t`,
normalise each `u(s_k)` into the compact annulus by a power of `λ`, and pass to a convergent
subsequence.
-/

noncomputable section

open Filter Set _root_.Topology

namespace Work.EQ

/-- The "metric" ball around a point of `ℂ*`, computed in `ℂ`.  Note that `ℂ*` itself carries no
metric structure; this describes a basis of neighbourhoods of `y` (the topology of `ℂˣ` is the
one induced by the inclusion into `ℂ`). -/
def ballU (y : ℂˣ) (δ : ℝ) : Set ℂˣ := {z : ℂˣ | ‖(z : ℂ) - (y : ℂ)‖ < δ}

theorem isOpen_ballU (y : ℂˣ) (δ : ℝ) : IsOpen (ballU y δ) := by
  have hcont : Continuous fun z : ℂˣ => ‖(z : ℂ) - (y : ℂ)‖ := by fun_prop
  exact isOpen_lt hcont continuous_const

/-- `Units.mk0` is continuous on the nonzero complex numbers. -/
theorem continuous_unitsMk0 : Continuous fun z : {z : ℂ // z ≠ 0} => Units.mk0 z.1 z.2 := by
  refine (IsInducing.continuous_iff (show IsInducing (Units.val : ℂˣ → ℂ) from
    Units.isEmbedding_val₀.isInducing)).mpr ?_
  have h : ((Units.val : ℂˣ → ℂ) ∘ fun z : {z : ℂ // z ≠ 0} => Units.mk0 z.1 z.2)
      = Subtype.val := by
    funext z
    exact Units.val_mk0 z.2
  rw [h]
  exact continuous_subtype_val

/-- The composite `ℂ* ↪ ℂ → ℂ*/λ^ℤ` read through the subtype of nonzero complex numbers. -/
theorem mk_unitsMk0 (l : ℝ) (u : ℂˣ) :
    (QuotientGroup.mk (Units.mk0 ((u : ℂ)) (Units.ne_zero u)) : TorusZ l)
      = QuotientGroup.mk u :=
  congrArg (fun v : ℂˣ => (QuotientGroup.mk v : TorusZ l))
    (Units.ext (by rw [Units.val_mk0]))

/-- A closed annulus in `ℂ*` with `0 < r₁` is compact. -/
theorem isCompact_annulus {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) : IsCompact (annulus r₁ r₂ : Set ℂˣ) := by
  have hset : ((Units.val : ℂˣ → ℂ) '' (annulus r₁ r₂ : Set ℂˣ))
      = {w : ℂ | r₁ ≤ ‖w‖ ∧ ‖w‖ ≤ r₂} := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hz.1, hz.2⟩
    · intro hw
      have hwne : w ≠ 0 := by
        rintro rfl
        simp only [Set.mem_setOf_eq, norm_zero] at hw
        exact absurd hw.1 (not_le.mpr hr₁)
      exact ⟨Units.mk0 w hwne, by rw [mem_annulus, Units.val_mk0]; exact hw, Units.val_mk0 _⟩
  have hclosed : IsClosed (((Units.val : ℂˣ → ℂ) '' (annulus r₁ r₂ : Set ℂˣ)) : Set ℂ) := by
    rw [hset]
    exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  have hbdd : Bornology.IsBounded (((Units.val : ℂˣ → ℂ) '' (annulus r₁ r₂ : Set ℂˣ))
      : Set ℂ) := by
    rw [isBounded_iff_forall_norm_le]
    exact ⟨max r₂ 0, fun w hw => by
      obtain ⟨z, hz, rfl⟩ := hw
      exact le_trans hz.2 (le_max_left _ _)⟩
  have hc : IsCompact (((Units.val : ℂˣ → ℂ) '' (annulus r₁ r₂ : Set ℂˣ)) : Set ℂ) :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbdd⟩
  exact (IsEmbedding.isCompact_iff
    (show IsEmbedding (Units.val : ℂˣ → ℂ) from Units.isEmbedding_val₀)).mpr hc

/-- **The shifted cluster set is uncountable (Rychlik (140)).** -/
theorem not_countable_shiftClusterSet {l r₁ r₂ : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (hr₁ : 0 < r₁)
    (hr : r₁ ≤ l * r₂) {u : ℝ → ℂ} (hne : ∀ s ∈ Set.Iio (1 : ℝ), u s ≠ 0)
    (hcont : ContinuousOn u (Set.Iio (1 : ℝ)))
    (hnolim : ¬ ∃ z : ℂ, z ≠ 0 ∧ Tendsto u (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds z)) :
    ¬ Set.Countable {z : ℂ | r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂ ∧
        ∃ s : ℕ → ℝ, Tendsto s atTop (nhdsWithin 1 (Set.Iio (1 : ℝ))) ∧
        ∃ p : ℕ → ℤ, Tendsto (fun k => (l : ℂ) ^ (p k) * u (s k)) atTop (nhds z)} := by
  intro hcount
  -- the `ℂ*`-valued path underlying `u`
  let ũ : ℝ → ℂˣ := fun s => if h : s ∈ Set.Iio (1 : ℝ) then Units.mk0 (u s) (hne s h) else 1
  have hũval : ∀ s ∈ Set.Iio (1 : ℝ), (ũ s : ℂ) = u s := by
    intro s hs
    simp only [ũ, dif_pos hs]
    exact Units.val_mk0 _
  have hũcont : ContinuousOn ũ (Set.Iio (1 : ℝ)) := by
    have h1 : Continuous (fun s : ↥(Set.Iio (1 : ℝ)) => Units.mk0 (u s) (hne s s.2)) :=
      continuous_unitsMk0.comp ((hcont.comp_continuous continuous_subtype_val
        (fun x => x.2)).subtype_mk (fun x => hne x x.2))
    refine (continuousOn_iff_continuous_domRestrict).mpr ?_
    exact h1.congr (fun s => by simp only [Set.domRestrict, ũ, dif_pos s.2])
  have hũlim : ¬ ∃ z : ℂˣ, Tendsto ũ (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds z) := by
    rintro ⟨z, hz⟩
    refine hnolim ⟨(z : ℂ), Units.ne_zero z, ?_⟩
    refine Tendsto.congr' ?_ (((Units.continuous_val :
      Continuous fun w : ℂˣ => (w : ℂ)).tendsto z).comp hz)
    filter_upwards [self_mem_nhdsWithin] with s hs
    simpa only [Function.comp_apply] using hũval s hs
  set Φ : ℝ → TorusZ l := fun s => (QuotientGroup.mk (ũ s) : TorusZ l) with hΦdef
  have hΦcont : ContinuousOn Φ (Set.Iio (1 : ℝ)) :=
    (QuotientGroup.continuous_mk (N := Subgroup.zpowers (lamU l))).continuousOn.comp hũcont
      (fun _ _ => Set.mem_univ _)
  have hΦlim : ¬ ∃ t : TorusZ l, Tendsto Φ (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds t) := by
    rintro ⟨t, ht⟩
    exact hũlim (exists_tendsto_of_tendsto_mk hl0 hl1 hũcont (by simpa [hΦdef] using ht))
  haveI hT2 : T2Space (TorusZ l) := TorusZ_t2Space hl0 hl1
  haveI hCpt : CompactSpace (TorusZ l) := TorusZ_compactSpace hl0 hl1
  set Zc : Set ℂˣ := (fun w : ℂˣ => (w : ℂ)) ⁻¹' {z : ℂ | r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂ ∧
      ∃ s : ℕ → ℝ, Tendsto s atTop (nhdsWithin 1 (Set.Iio (1 : ℝ))) ∧
      ∃ p : ℕ → ℤ, Tendsto (fun k => (l : ℂ) ^ (p k) * u (s k)) atTop (nhds z)} with hZcdef
  have hZCcount : Zc.Countable := by
    rw [hZcdef]
    exact hcount.preimage (f := fun w : ℂˣ => (w : ℂ)) (fun a b h => Units.ext h)
  -- `Units.mk0`-based neighbourhoods of a point of the torus
  have hcontψ : Continuous fun z : {z : ℂ // z ≠ 0} =>
      (QuotientGroup.mk (Units.mk0 z.1 z.2) : TorusZ l) :=
    (QuotientGroup.continuous_mk (N := Subgroup.zpowers (lamU l))).comp continuous_unitsMk0
  have hsub : {t : TorusZ l | MapClusterPt t (nhdsWithin 1 (Set.Iio (1 : ℝ))) Φ} ⊆
      (QuotientGroup.mk : ℂˣ → TorusZ l) '' Zc := by
    intro t ht
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective t
    have hbase : ∀ k : ℕ, ∃ r : ℝ, r ∈ Set.Ioo (1 - 1 / ((k : ℝ) + 1)) 1 ∧
        Φ r ∈ (QuotientGroup.mk : ℂˣ → TorusZ l) '' ballU y (1 / ((k : ℝ) + 1)) := by
      intro k
      have hI : Set.Ioo (1 - 1 / ((k : ℝ) + 1)) 1 ∈ nhdsWithin 1 (Set.Iio (1 : ℝ)) :=
        Work.Topology.Ioo_mem_nhdsWithin_Iio_one k
      have hcl : t ∈ closure (Φ '' Set.Ioo (1 - 1 / ((k : ℝ) + 1)) 1) :=
        clusterPt_iff_forall_mem_closure.mp ht _ (Filter.image_mem_map hI)
      have hVopen : IsOpen ((QuotientGroup.mk : ℂˣ → TorusZ l) '' ballU y (1 / ((k : ℝ) + 1))) :=
        (QuotientGroup.isOpenMap_coe (N := Subgroup.zpowers (lamU l))) _ (isOpen_ballU y _)
      have htV : t ∈ (QuotientGroup.mk : ℂˣ → TorusZ l) '' ballU y (1 / ((k : ℝ) + 1)) :=
        ⟨y, by
          show ‖(y : ℂ) - (y : ℂ)‖ < 1 / ((k : ℝ) + 1)
          rw [sub_self, norm_zero]
          exact one_div_pos.mpr (by positivity), hy⟩
      obtain ⟨x, hxV, hxcl⟩ := mem_closure_iff.mp hcl _ hVopen htV
      obtain ⟨r, hrI, rfl⟩ := hxcl
      exact ⟨r, hrI, hxV⟩
    choose s hs1 hsV using hbase
    have hslim : Tendsto s atTop (nhdsWithin 1 (Set.Iio (1 : ℝ))) := by
      rw [Filter.tendsto_def]
      intro U hU
      obtain ⟨n, hn⟩ := Work.Topology.exists_Ioo_subset_of_mem_nhdsWithin_Iio_one hU
      filter_upwards [eventually_ge_atTop n] with k hk
      refine hn ⟨?_, (hs1 k).2⟩
      have hle : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        linarith
      linarith [(hs1 k).1]
    have hΦs : Tendsto (fun k => Φ (s k)) atTop (nhds t) := by
      have hwit : ∀ k : ℕ, ∃ w : ℂˣ, w ∈ ballU y (1 / ((k : ℝ) + 1)) ∧
          (QuotientGroup.mk w : TorusZ l) = Φ (s k) := fun k => hsV k
      choose w hw1 hw2 using hwit
      have hwt : Tendsto (fun k => ((w k : ℂˣ) : ℂ)) atTop (nhds (y : ℂ)) := by
        have hbd : ∀ k : ℕ, ‖((w k : ℂˣ) : ℂ) - (y : ℂ)‖ ≤ 1 / ((k : ℝ) + 1) := by
          intro k
          have h := hw1 k
          simp only [ballU] at h
          exact le_of_lt h
        have hzero : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (nhds 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        exact tendsto_iff_norm_sub_tendsto_zero.mpr
          (squeeze_zero (fun k => norm_nonneg _) hbd hzero)
      have hsuby : Tendsto (fun k => (⟨((w k : ℂˣ) : ℂ), Units.ne_zero (w k)⟩ :
          {z : ℂ // z ≠ 0})) atTop (nhds ⟨(y : ℂ), Units.ne_zero y⟩) :=
        tendsto_subtype_rng.mpr hwt
      have h4 : Tendsto (fun k => (QuotientGroup.mk (w k) : TorusZ l)) atTop
          (nhds (QuotientGroup.mk y : TorusZ l)) := by
        have h5 := (hcontψ.tendsto ⟨(y : ℂ), Units.ne_zero y⟩).comp hsuby
        rw [mk_unitsMk0 l y] at h5
        refine Tendsto.congr' ?_ h5
        filter_upwards with k
        exact mk_unitsMk0 l (w k)
      rw [hy] at h4
      exact Tendsto.congr' (Eventually.of_forall fun k => hw2 k) h4
    -- normalise the path into the annulus and extract a convergent subsequence in `ℂ`
    have hnorm : ∀ k : ℕ, ∃ n : ℤ, ((lamU l) ^ n * ũ (s k) : ℂˣ) ∈ annulus r₁ r₂ := fun k =>
      TorusZ_zpow_mem_annulus hl0 hl1 hr₁ hr (ũ (s k))
    choose p hp using hnorm
    have hK : IsCompact {w : ℂ | r₁ ≤ ‖w‖ ∧ ‖w‖ ≤ r₂} := by
      refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
      · exact (isClosed_le continuous_const continuous_norm).inter
          (isClosed_le continuous_norm continuous_const)
      · rw [isBounded_iff_forall_norm_le]
        exact ⟨max r₂ 0, fun w hw => le_trans hw.2 (le_max_left _ _)⟩
    have hmem : ∀ k : ℕ, ((((lamU l) ^ (p k) * ũ (s k) : ℂˣ)) : ℂ)
        ∈ {w : ℂ | r₁ ≤ ‖w‖ ∧ ‖w‖ ≤ r₂} := by
      intro k
      have h := hp k
      rw [mem_annulus] at h
      exact h
    obtain ⟨z', hz'K, φ, hφmono, hφlim⟩ :=
      hK.tendsto_subseq (x := fun k => ((((lamU l) ^ (p k) * ũ (s k) : ℂˣ)) : ℂ)) hmem
    have hz'K' : r₁ ≤ ‖z'‖ ∧ ‖z'‖ ≤ r₂ := hz'K
    have hz'ne : z' ≠ 0 := by
      intro h
      rw [h, norm_zero] at hz'K'
      linarith [hz'K'.1]
    have hslimalong : Tendsto (fun k => s (φ k)) atTop (nhdsWithin 1 (Set.Iio (1 : ℝ))) :=
      hslim.comp hφmono.tendsto_atTop
    have hconv : Tendsto (fun k => (l : ℂ) ^ (p (φ k)) * u (s (φ k))) atTop (nhds z') := by
      refine Tendsto.congr' ?_ hφlim
      filter_upwards [hslimalong.eventually self_mem_nhdsWithin] with k hk
      show ((((lamU l) ^ (p (φ k)) * ũ (s (φ k)) : ℂˣ)) : ℂ)
        = (l : ℂ) ^ (p (φ k)) * u (s (φ k))
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, lamU_coe (ne_of_gt hl0),
        hũval (s (φ k)) hk]
    refine ⟨Units.mk0 z' hz'ne, ?_, ?_⟩
    · -- the unit lies over a point of the set in the statement
      show (Units.mk0 z' hz'ne : ℂ) ∈ {z : ℂ | r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂ ∧
          ∃ s : ℕ → ℝ, Tendsto s atTop (nhdsWithin 1 (Set.Iio (1 : ℝ))) ∧
          ∃ p : ℕ → ℤ, Tendsto (fun k => (l : ℂ) ^ (p k) * u (s k)) atTop (nhds z)}
      rw [Units.val_mk0]
      exact ⟨hz'K'.1, hz'K'.2, s ∘ φ, hslimalong, p ∘ φ, hconv⟩
    · -- its image in the torus is the cluster point
      have hsub2 : Tendsto (fun k => (⟨((((lamU l) ^ (p (φ k)) * ũ (s (φ k)) : ℂˣ)) : ℂ),
          Units.ne_zero _⟩ : {w : ℂ // w ≠ 0})) atTop (nhds ⟨z', hz'ne⟩) :=
        tendsto_subtype_rng.mpr hφlim
      have h5 := (hcontψ.tendsto ⟨z', hz'ne⟩).comp hsub2
      have h6 : Tendsto (fun k => Φ (s (φ k))) atTop
          (nhds (QuotientGroup.mk (Units.mk0 z' hz'ne))) := by
        refine Tendsto.congr' ?_ h5
        filter_upwards with k
        show (QuotientGroup.mk (Units.mk0 ((((lamU l) ^ (p (φ k)) * ũ (s (φ k)) : ℂˣ)) : ℂ)
          (Units.ne_zero _)) : TorusZ l) = Φ (s (φ k))
        rw [mk_unitsMk0 l, mk_zpow_mul, hΦdef]
      exact tendsto_nhds_unique h6 (hΦs.comp hφmono.tendsto_atTop)
  exact (Work.Topology.not_countable_clusterSet hΦcont hΦlim)
    (Set.Countable.mono hsub (hZCcount.image _))

end Work.EQ
