import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.twoLanes_of_canalData
import Submission.Work.Drive.trailStDef
import Submission.Work.Drive.exists_reparamLand
import Submission.Work.Drive.Rays.rayStraighteningTarget
import Submission.Work.Drive.clipArc
import Submission.Work.Drive.clipArcImage
import Submission.Work.Drive.rayBricks

/-!
# The piece engine and the base state of the trail recursion

`Work.Drive.buildPiece` (the arc in an open preconnected region, with the rootedness row) and
`Work.Drive.baseSt` (the state with `k = 0`), split out of `Drive/trailRay.lean` so that the
recursion assembly can import them without the step-theorem file.
-/

namespace Work.Drive

open Set Filter
open scoped Topology Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (Work.Noncompact.CompressionTube.MC n)
    Work.Noncompact.CompressionTube.smoothOrder M] [T2Space M] [SecondCountableTopology M]

variable {W : Set M} {ρ : ℝ → M}

section Engine

variable {ρ : ℝ → M}

/-- **The piece engine.**  In an open preconnected region `U ⊆ W`, from a point `p` with a
prescribed straight chart germ direction `v` and a far point `ρ T ∈ U` which is not a return of
`ρ` to `p` beyond `T`, build a piece `Q` from `p` to `ρ τ'`, where `τ'` is the *last* visit of `ρ`
to the image of `Q`; `Q` carries the prescribed initial germ and a straight terminal germ, and `ρ`
avoids `Q`'s image after `τ'`. -/
theorem buildPiece (hn : 2 ≤ n) (hρ : Continuous ρ)
    (hρesc : ∀ K : Set M, IsCompact K → ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ρ t ∉ K)
    {U : Set M} (hUo : IsOpen U) (hUpc : IsPreconnected U)
    {p : M} (hp : p ∈ U) {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M) (hpc : p ∈ c.source)
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ≠ 0)
    (hger : ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t → t ≤ e → c.symm (c p + t • v) ∈ U)
    {T : ℝ} (hy : ρ T ∈ U) (hpq : ρ T ≠ p)
    (hTp : ∀ t : ℝ, T ≤ t → ρ t ≠ p) :
    ∃ (Q : ℝ → M) (x' : M) (τ' : ℝ)
      (c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (w' : EuclideanSpace ℝ (Fin n)) (eout ein ρD : ℝ),
      Q 0 = p ∧ Q 1 = x' ∧ x' = ρ τ' ∧ T ≤ τ' ∧
      ContMDiff Work.Noncompact.CompressionTube.MCreal (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder Q ∧
      (∀ t : ℝ, Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n) Q t)) ∧
      Set.InjOn Q (Set.Icc (0:ℝ) 1) ∧ Q '' Set.Icc (0:ℝ) 1 ⊆ U ∧
      0 < ein ∧ (∀ t : ℝ, 0 ≤ t → t ≤ ein → Q t = c.symm (c p + t • v)) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ ein → c p + t • v ∈ c.target) ∧
      0 < ρD ∧ c.symm '' Metric.ball (c p) ρD ⊆ U ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → Q t ∈ c.symm '' Metric.ball (c p) ρD →
        ∃ s : ℝ, 0 ≤ s ∧ Q t = c.symm (c p + s • v) ∧ c p + s • v ∈ c.target) ∧
      0 < eout ∧ w' ≠ 0 ∧
      c' ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder M ∧ x' ∈ c'.source ∧
      (∀ t : ℝ, 1 - eout ≤ t → t ≤ 1 → Q t = c'.symm (c' x' + (t - 1) • w')) ∧
      (∀ t : ℝ, 1 - eout ≤ t → t ≤ 1 → c' x' + (t - 1) • w' ∈ c'.target) ∧
      (∀ t : ℝ, τ' < t → ρ t ∉ Q '' Set.Icc (0:ℝ) 1) := by
  classical
  obtain ⟨α, ε, _c₁, _wv, _eout₁, ρin, _ρout, hα0, hα1, hαsm, hαimm, hαinj, hαU, hε0, hε1,
    hαger, hαtgt, _heout₁0, _heout₁1, _hwv, _hc₁, _hqc₁, _hαterm, _hαttgt, hρin0, hαclamp,
    _hρout0, _hαclampout⟩ :=
    Work.Noncompact.CompressionTube.exists_mid_piece (n := n) (M := M) (hn := hn) hUo hUpc hp
      hy (Ne.symm hpq) hc hpc hv hger
  have hKc : IsCompact (α '' Set.Icc (0:ℝ) 1) := isCompact_Icc.image hαsm.continuous
  have hTK : ρ T ∈ α '' Set.Icc (0:ℝ) 1 := by
    rw [← hα1]; exact ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
  obtain ⟨τ', hTτ', hτρ, hτ'max⟩ := Work.Drive.exists_lastVisit hρ hρesc hKc hTK
  set x' : M := ρ τ' with hx'def
  have hx'K : x' ∈ α '' Set.Icc (0:ℝ) 1 := hτρ
  obtain ⟨s, hsIcc, hsx⟩ := hx'K
  have hs0 : 0 < s := by
    rcases lt_or_eq_of_le hsIcc.1 with h | h
    · exact h
    · exfalso
      have hxp : ρ τ' = p := by rw [← hx'def, ← hsx, h.symm, hα0]
      exact hTp τ' hTτ' hxp
  have hs1 : s ≤ 1 := hsIcc.2
  obtain ⟨Q, e', c', w', eout, hQ0, hQ1, hQsub, hQsm, hQimm, hQinj, he'0, hQgerm, hQtgt,
    heout0, hw', hc', hx'c', hQterm, hQttgt⟩ :=
    Work.Drive.clipArcImage (n := n) (hn := hn) hαsm hαimm hαinj hc hv hε0
      (fun t ht0 ht => by rw [hα0]; exact hαger t ht0 ht)
      (fun t ht0 ht => by rw [hα0]; exact hαtgt t ht0 ht) hs0 hs1
  obtain ⟨r₃, hr₃0, _hr₃tgt, hr₃U, -⟩ :=
    exists_chartBall_small (ι := Empty) (T := fun _ => (∅ : Set M)) hpc
      (fun i => isEmptyElim i) (fun i => isEmptyElim i) (U := U) hUo hp
  have hvisit : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 →
      Q t ∈ c.symm '' Metric.ball (c p) (min r₃ ρin) →
      ∃ s : ℝ, 0 ≤ s ∧ Q t = c.symm (c p + s • v) ∧ c p + s • v ∈ c.target := by
    intro t ht hmem
    obtain ⟨u, hu, huy⟩ := hQsub ⟨t, ht, rfl⟩
    have hmemU : α u ∈ c.symm '' Metric.ball (c p) (min r₃ ρin) := by rw [huy]; exact hmem
    have hmemρ : α u ∈ c.symm '' Metric.ball (c p) ρin :=
      Set.image_mono (Metric.ball_subset_ball (min_le_right _ _)) hmemU
    have huε : u ∈ Set.Icc (0:ℝ) ε := hαclamp u hu hmemρ
    exact ⟨u, huε.1, by rw [huy.symm, hαger u huε.1 huε.2], hαtgt u huε.1 huε.2⟩
  refine ⟨Q, x', τ', c', w', eout, min e' ε, min r₃ ρin,
    by rw [hQ0, hα0], by rw [hQ1, hsx], hx'def, hTτ', hQsm, hQimm, hQinj, ?_,
    lt_min he'0 hε0, ?_, ?_, lt_min hr₃0 hρin0, ?_, hvisit, heout0, hw', hc',
    (by rw [← hsx]; exact hx'c'),
    (by intro t ht1 ht2; rw [← hsx]; exact hQterm t ht1 ht2),
    (by intro t ht1 ht2; rw [← hsx]; exact hQttgt t ht1 ht2), ?_⟩
  · -- `Q '' Icc ⊆ U`
    rintro y ⟨t, ht, rfl⟩
    obtain ⟨u, hu, huy⟩ := hQsub ⟨t, ht, rfl⟩
    exact huy ▸ hαU u hu
  · -- the initial germ
    refine fun t ht0 ht => ?_
    rw [hQgerm t ht0 (ht.trans (min_le_left _ _)), hα0]
  · -- the initial target row
    refine fun t ht0 ht => ?_
    rw [← hα0]
    exact hQtgt t ht0 (ht.trans (min_le_left _ _))
  · -- the ball is inside `U`
    exact (Set.image_mono (Metric.ball_subset_ball (min_le_left _ _))).trans hr₃U
  · intro t ht hmem
    exact hτ'max t ht (hQsub hmem)

end Engine

section State

/-- **The base state**: the first piece, from `ρ 0` to the last visit of `ρ` to its own image. -/
theorem baseSt (hn : 2 ≤ n) (hW : IsOpen W) (hρ : Continuous ρ)
    (hρW : ∀ t : ℝ, 0 ≤ t → ρ t ∈ W)
    (hρesc : ∀ K : Set M, IsCompact K → ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ρ t ∉ K)
    (Kex : CompactExhaustion M) :
    ∃ B : St (n := n) (M := M) W ρ Kex, B.k = 0 := by
  classical
  haveI : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  let c₀ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) (ρ 0)
  have hc₀ : c₀ ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M :=
    IsManifold.chart_mem_maximalAtlas (ρ 0)
  have hρ0src : ρ 0 ∈ c₀.source := mem_chart_source _ _
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin n))
  obtain ⟨τp, _, _, hτpmax⟩ :=
    Work.Drive.exists_lastVisit hρ hρesc (K := {ρ 0}) isCompact_singleton (t := 0) (by simp)
  set T : ℝ := max (max (τp + 1) (escK Kex ρ hρesc 2)) 0 with hTdef
  have hTτp : τp < T := lt_of_lt_of_le (by linarith) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hTesc : escK Kex ρ hρesc 2 ≤ T := le_trans (le_max_right _ _) (le_max_left _ _)
  have hT0 : 0 ≤ T := le_max_right _ _
  have hρT_W : ρ T ∈ W := hρW T hT0
  have hTp : ∀ t : ℝ, T ≤ t → ρ t ≠ ρ 0 := by
    intro t ht hcon
    exact hτpmax t (lt_of_lt_of_le hTτp ht) (by simpa using hcon)
  set C : Set M := connectedComponentIn W (ρ T) with hCdef
  have hCpc : IsPreconnected C := isPreconnected_connectedComponentIn
  have hCW : C ⊆ W := connectedComponentIn_subset W (ρ T)
  have hρ0C : ρ 0 ∈ C := by
    have hpc : IsPreconnected (ρ '' Set.Icc (0:ℝ) T) :=
      isPreconnected_Icc.image ρ hρ.continuousOn
    have hsub : ρ '' Set.Icc (0:ℝ) T ⊆ W := by
      rintro y ⟨t, ht, rfl⟩
      exact hρW t ht.1
    exact hpc.subset_connectedComponentIn ⟨T, ⟨hT0, le_rfl⟩, rfl⟩ hsub
      ⟨0, ⟨le_rfl, hT0⟩, rfl⟩
  obtain ⟨r₀, hr₀0, hr₀tgt, hr₀W, -⟩ :=
    exists_chartBall_small (ι := Empty) (T := fun _ => (∅ : Set M)) hρ0src
      (fun i => isEmptyElim i) (fun i => isEmptyElim i) (U := W) hW (hρW 0 le_rfl)
  set D : Set M := c₀.symm '' Metric.ball (c₀ (ρ 0)) r₀ with hDdef
  have hDpc : IsPreconnected D :=
    Metric.isPreconnected_ball.image c₀.symm (c₀.continuousOn_symm.mono hr₀tgt)
  have hρ0D : ρ 0 ∈ D := ⟨c₀ (ρ 0), Metric.mem_ball_self hr₀0, c₀.left_inv hρ0src⟩
  set U : Set M := C ∪ D with hUdef
  have hUo : IsOpen U :=
    (hW.connectedComponentIn).union
      (c₀.isOpen_image_symm_of_subset_target Metric.isOpen_ball hr₀tgt)
  have hUpc : IsPreconnected U := IsPreconnected.union (ρ 0) hρ0C hρ0D hCpc hDpc
  have hUW : U ⊆ W := by
    intro y hy
    rw [hUdef] at hy
    rcases hy with h | h
    · exact hCW h
    · exact hr₀W h
  have hger : ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t → t ≤ e →
      c₀.symm (c₀ (ρ 0) + t • v) ∈ U := by
    have h1 : ContinuousAt (fun t : ℝ => c₀ (ρ 0) + t • v) 0 :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
    have h2 : c₀ (ρ 0) + (0:ℝ) • v ∈ c₀.target := by
      simpa using c₀.map_source hρ0src
    have hcont : ContinuousAt (fun t : ℝ => c₀.symm (c₀ (ρ 0) + t • v)) 0 :=
      ContinuousAt.comp (f := fun t : ℝ => c₀ (ρ 0) + t • v)
        (x := (0 : ℝ))
        (c₀.continuousOn_symm.continuousAt (c₀.open_target.mem_nhds h2)) h1
    have hDo : IsOpen D :=
      c₀.isOpen_image_symm_of_subset_target Metric.isOpen_ball hr₀tgt
    have hnhds : (fun t : ℝ => c₀.symm (c₀ (ρ 0) + t • v)) ⁻¹' D ∈ nhds (0 : ℝ) := by
      have hval : (fun t : ℝ => c₀.symm (c₀ (ρ 0) + t • v)) 0 = ρ 0 := by
        simp only [zero_smul, add_zero]
        exact c₀.left_inv hρ0src
      refine hcont ?_
      rw [hval]
      exact hDo.mem_nhds hρ0D
    obtain ⟨e, he0, he⟩ := Metric.mem_nhds_iff.mp hnhds
    refine ⟨e / 2, by linarith, fun t ht0 ht => ?_⟩
    have hb : t ∈ Metric.ball (0:ℝ) e := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht0]
      linarith
    have hD : c₀.symm (c₀ (ρ 0) + t • v) ∈ D := Set.mem_preimage.mp (he hb)
    rw [hUdef]; exact Or.inr hD
  obtain ⟨Q, x', τ', c', w', eout, einB, ρDB, hQ0, hQ1, hx'eq, hTτ', hQsm, hQimm, hQinj, hQU,
    heinB0, hQgerm, hQtgt, hρDB0, _hballU, _hvisitB, heout0, hw', hc', hx'c', hQterm, hQttgt,
    hQlast⟩ :=
    buildPiece (n := n) (M := M) hn hρ hρesc hUo hUpc (Or.inl hρ0C) hc₀ hρ0src hv hger
      (Or.inl (mem_connectedComponentIn (x := ρ T) (F := W) hρT_W))
      (fun hcon => hTp T le_rfl hcon) hTp
  have hx'W : x' ∈ W := by rw [hx'eq]; exact hρW τ' (le_trans hT0 hTτ')
  have hx'lev : x' ∉ Kex 2 := by
    rw [hx'eq]
    exact escK_spec Kex ρ hρesc 2 (le_trans hTesc hTτ')
  have hlev2 : ∀ t : ℝ, τ' < t → ρ t ∉ Kex 2 :=
    fun t ht => escK_spec Kex ρ hρesc 2 (le_trans (le_trans hTesc hTτ') ht.le)
  obtain ⟨r₁, hr₁0, hr₁tgt, hclamp₁⟩ := exists_clampBall hQsm.continuous hQ1 hQinj hx'c' heout0
  obtain ⟨r₂, hr₂0, hr₂tgt, hballW₂, hballlev₂⟩ :=
    exists_chartBall_small (ι := Unit) (T := fun _ => Kex 2) hx'c'
      (fun _ => (Kex.isCompact 2).isClosed) (fun _ => hx'lev) (U := W) hW hx'W
  refine ⟨{
    k := 0
    P := fun _ => Q
    x := x'
    τ := τ'
    c := c'
    w := w'
    e := eout
    r := min r₁ r₂
    cIn := c₀
    wIn := v
    eIn := einB
    hx := hx'eq
    hτ0 := le_trans hT0 hTτ'
    hw := hw'
    he := heout0
    hr := lt_min hr₁0 hr₂0
    hrtgt := fun z hz => hr₁tgt (Metric.ball_subset_ball (min_le_left _ _) hz)
    hwIn := hv
    heIn := heinB0
    hc := hc'
    hcIn := hc₀
    hxc := hx'c'
    hger := hQterm
    htgt := hQttgt
    hgerIn := fun t ht0 ht => by
      rw [hQgerm t ht0 ht, hQ0]
    hclamp := fun t ht hmem =>
      hclamp₁ t ht (Set.image_mono (Metric.ball_subset_ball (min_le_left _ _)) hmem)
    hballW := fun y hy => by
      obtain ⟨z, hz, rfl⟩ := hy
      exact hballW₂ ⟨z, Metric.ball_subset_ball (min_le_right _ _) hz, rfl⟩
    hballlev := Set.disjoint_of_subset_left
      (Set.image_mono (Metric.ball_subset_ball (min_le_right _ _))) (hballlev₂ ())
    hballold := fun j hj => absurd hj (Nat.not_lt_zero j)
    hPsm := fun j hj => by
      have : j = 0 := Nat.le_zero.mp hj
      subst this
      exact hQsm
    hPimm := fun j hj t ht => by
      have : j = 0 := Nat.le_zero.mp hj
      subst this
      exact hQimm t
    hPinj := fun j hj => by
      have : j = 0 := Nat.le_zero.mp hj
      subst this
      exact hQinj
    hPjun := fun j hj => absurd hj (Nat.not_lt_zero j)
    hPW := fun j hj => by
      have : j = 0 := Nat.le_zero.mp hj
      subst this
      exact fun y hy => hUW (hQU hy)
    hPlev := fun j hj hj0 => absurd hj0 (by omega)
    hPsep := fun j l hj hl => absurd hl (by omega)
    hclean := fun j hj => by
      rw [Set.disjoint_left]
      rintro y ⟨t, ht, rfl⟩ hy
      exact hQlast t ht hy
    hlev := hlev2
    hxlev := hx'lev
    c₀ := c₀
    u₀ := v
    e₀ := einB
    hP0 := hQ0
    hc₀ := hc₀
    hu₀ := hv
    he₀ := heinB0
    hρ0₀ := hρ0src
    hgerm₀ := fun t ht0 ht => hQgerm t ht0 ht }, rfl⟩

end State

end Work.Drive
