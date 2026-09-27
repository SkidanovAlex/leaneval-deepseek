import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation

/-!
# The trail-recursion state (`Work.Drive.St`) and its small tools

Split out of `Drive/trailRay.lean` so that the step engine can be stated without importing the
recursion file.  Contains `escK`, the chart-ball/clamp-ball tools and the state structure.
-/

namespace Work.Drive

open Set Filter
open scoped Topology Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (Work.Noncompact.CompressionTube.MC n)
    Work.Noncompact.CompressionTube.smoothOrder M] [T2Space M] [SecondCountableTopology M]

/-- An escape time for the exhaustion member `Kex m`: beyond it the path `ρ` never visits `Kex m`. -/
noncomputable def escK (Kex : CompactExhaustion M) (ρ : ℝ → M)
    (hρesc : ∀ K : Set M, IsCompact K → ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ρ t ∉ K) : ℕ → ℝ :=
  Nat.rec (Classical.choose (hρesc (Kex 0) (Kex.isCompact 0)))
    (fun n ih => max ih (Classical.choose (hρesc (Kex (n + 1)) (Kex.isCompact (n + 1)))))

theorem escK_zero (Kex : CompactExhaustion M) (ρ : ℝ → M)
    (hρesc : ∀ K : Set M, IsCompact K → ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ρ t ∉ K) :
    escK Kex ρ hρesc 0 = Classical.choose (hρesc (Kex 0) (Kex.isCompact 0)) := rfl

theorem escK_succ (Kex : CompactExhaustion M) (ρ : ℝ → M)
    (hρesc : ∀ K : Set M, IsCompact K → ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ρ t ∉ K) (m : ℕ) :
    escK Kex ρ hρesc (m + 1)
      = max (escK Kex ρ hρesc m)
        (Classical.choose (hρesc (Kex (m + 1)) (Kex.isCompact (m + 1)))) := rfl

theorem escK_mono (Kex : CompactExhaustion M) (ρ : ℝ → M)
    (hρesc : ∀ K : Set M, IsCompact K → ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ρ t ∉ K) :
    Monotone (escK Kex ρ hρesc) := by
  intro m l hml
  induction hml with
  | refl => exact le_rfl
  | @step l _ ih =>
      exact ih.trans (by rw [escK_succ]; exact le_max_left _ _)

theorem escK_spec (Kex : CompactExhaustion M) (ρ : ℝ → M)
    (hρesc : ∀ K : Set M, IsCompact K → ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ρ t ∉ K)
    (m : ℕ) {t : ℝ} (ht : escK Kex ρ hρesc m ≤ t) : ρ t ∉ Kex m := by
  induction m generalizing t with
  | zero =>
      rw [escK_zero] at ht
      exact Classical.choose_spec (hρesc (Kex 0) (Kex.isCompact 0)) t ht
  | succ n ih =>
      rw [escK_succ] at ht
      exact Classical.choose_spec (hρesc (Kex (n + 1)) (Kex.isCompact (n + 1))) t
        (le_trans (le_max_right _ _) ht)

variable {W : Set M} {ρ : ℝ → M}

/-- **A chart ball at a point, small enough to be inside a prescribed open set and to avoid a
finite family of prescribed closed sets not containing the point.** -/
theorem exists_chartBall_small {ι : Type*} [Finite ι]
    {x : M} {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} (hxc : x ∈ c.source)
    {T : ι → Set M} (hT : ∀ i, IsClosed (T i)) (hxT : ∀ i, x ∉ T i)
    {U : Set M} (hUo : IsOpen U) (hxU : x ∈ U) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (c x) r ⊆ c.target ∧
      c.symm '' Metric.ball (c x) r ⊆ U ∧
      (∀ i, Disjoint (c.symm '' Metric.ball (c x) r) (T i)) := by
  classical
  have hx'tgt : c x ∈ c.target := c.map_source hxc
  have hclosed : IsClosed (⋃ i, T i) := isClosed_iUnion_of_finite fun i => hT i
  have hxnot : x ∉ ⋃ i, T i := by
    intro h
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
    exact hxT i hi
  have hnhds : U ∩ (⋃ i, T i)ᶜ ∈ 𝓝 x :=
    Filter.inter_mem (hUo.mem_nhds hxU) (hclosed.isOpen_compl.mem_nhds hxnot)
  have hcont : ContinuousAt (fun z : EuclideanSpace ℝ (Fin n) => c.symm z) (c x) :=
    c.continuousOn_symm.continuousAt (c.open_target.mem_nhds hx'tgt)
  have hcx : c.symm (c x) = x := c.left_inv hxc
  have hnhds' : U ∩ (⋃ i, T i)ᶜ ∈ 𝓝 (c.symm (c x)) := by rw [hcx]; exact hnhds
  set f : EuclideanSpace ℝ (Fin n) → M := fun z => c.symm z with hfdef
  have hpre : f ⁻¹' (U ∩ (⋃ i, T i)ᶜ) ∩ c.target ∈ 𝓝 (c x) :=
    Filter.inter_mem (hcont hnhds') (c.open_target.mem_nhds hx'tgt)
  obtain ⟨r, hrpos, hr⟩ := Metric.mem_nhds_iff.mp hpre
  have hball : ∀ z ∈ Metric.ball (c x) r, f z ∈ U ∩ (⋃ i, T i)ᶜ := fun z hz => (hr hz).1
  have hbtgt : Metric.ball (c x) r ⊆ c.target := fun z hz => (hr hz).2
  refine ⟨r, hrpos, hbtgt, ?_, ?_⟩
  · rintro y ⟨z, hz, rfl⟩
    exact (hball z hz).1
  · intro i
    rw [Set.disjoint_left]
    rintro y ⟨z, hz, rfl⟩ hyi
    exact (hball z hz).2 (Set.mem_iUnion.mpr ⟨i, hyi⟩)


/-- **A small chart ball at the terminal point of a piece, inside which the only visits of the
piece happen on the terminal window.** -/
theorem exists_clampBall {Q : ℝ → M} (hQc : Continuous Q) {x' : M} (hQ1 : Q 1 = x')
    (hQinj : Set.InjOn Q (Set.Icc (0:ℝ) 1))
    {c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} (hx'c' : x' ∈ c'.source)
    {e' : ℝ} (he' : 0 < e') :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (c' x') r ⊆ c'.target ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → Q t ∈ c'.symm '' Metric.ball (c' x') r → 1 - e' ≤ t) := by
  classical
  have hA : IsCompact (Q '' Set.Icc (0:ℝ) (1 - e')) :=
    isCompact_Icc.image hQc
  have hxA : x' ∉ Q '' Set.Icc (0:ℝ) (1 - e') := by
    rintro ⟨t, ht, ht'⟩
    have h1 : t = 1 := hQinj ⟨ht.1, le_trans ht.2 (by linarith)⟩ ⟨zero_le_one, le_rfl⟩
      (by rw [ht', hQ1])
    linarith [ht.2]
  obtain ⟨r, hr0, hrtgt, hAcom, _⟩ :=
    exists_chartBall_small (ι := Empty) (T := fun _ => (∅ : Set M)) hx'c'
      (fun i => isEmptyElim i) (fun i => isEmptyElim i)
      (U := (Q '' Set.Icc (0:ℝ) (1 - e'))ᶜ) hA.isClosed.isOpen_compl hxA
  refine ⟨r, hr0, hrtgt, ?_⟩
  intro t ht hmem
  by_contra hcon
  push_neg at hcon
  exact hAcom hmem ⟨t, ⟨ht.1, le_of_lt hcon⟩, rfl⟩

/-- **The state of the trail recursion.**  `P j` for `j ≤ k` are the pieces built so far; `x` is the
terminal junction of `P k`, `τ` its time, `(c, w, e, r)` the terminal germ data of `P k` there
(germ window, chart-target row, clamp radius) and `(cIn, wIn, eIn)` the initial germ data of `P k`
at its start.  The invariants are: `ρ` avoids every piece and the level `Kex (k+2)` after `τ`; the
piece `P j` (`1 ≤ j`) avoids `Kex (j+1)`; and the pieces meet only at the junctions. -/
structure St (W : Set M) (ρ : ℝ → M) (Kex : CompactExhaustion M) where
  k : ℕ
  P : ℕ → ℝ → M
  x : M
  τ : ℝ
  c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))
  w : EuclideanSpace ℝ (Fin n)
  e : ℝ
  r : ℝ
  cIn : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))
  wIn : EuclideanSpace ℝ (Fin n)
  eIn : ℝ
  hx : x = ρ τ
  hτ0 : 0 ≤ τ
  hw : w ≠ 0
  he : 0 < e
  hr : 0 < r
  hrtgt : Metric.ball (c x) r ⊆ c.target
  hwIn : wIn ≠ 0
  heIn : 0 < eIn
  hc : c ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
    Work.Noncompact.CompressionTube.smoothOrder M
  hcIn : cIn ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
    Work.Noncompact.CompressionTube.smoothOrder M
  hxc : x ∈ c.source
  hger : ∀ t : ℝ, 1 - e ≤ t → t ≤ 1 → P k t = c.symm (c x + (t - 1) • w)
  htgt : ∀ t : ℝ, 1 - e ≤ t → t ≤ 1 → c x + (t - 1) • w ∈ c.target
  hgerIn : ∀ t : ℝ, 0 ≤ t → t ≤ eIn → P k t = cIn.symm (cIn (P k 0) + t • wIn)
  hclamp : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → P k t ∈ c.symm '' Metric.ball (c x) r → 1 - e ≤ t
  hballW : c.symm '' Metric.ball (c x) r ⊆ W
  hballlev : Disjoint (c.symm '' Metric.ball (c x) r) (Kex (k + 2))
  hballold : ∀ j : ℕ, j < k →
    Disjoint (c.symm '' Metric.ball (c x) r) (P j '' Set.Icc (0:ℝ) 1)
  hPsm : ∀ j : ℕ, j ≤ k → ContMDiff Work.Noncompact.CompressionTube.MCreal
    (Work.Noncompact.CompressionTube.MC n) Work.Noncompact.CompressionTube.smoothOrder (P j)
  hPimm : ∀ j : ℕ, j ≤ k → ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 →
    Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n) (P j) t)
  hPinj : ∀ j : ℕ, j ≤ k → Set.InjOn (P j) (Set.Icc (0:ℝ) 1)
  hPjun : ∀ j : ℕ, j < k → P j 1 = P (j + 1) 0
  hPW : ∀ j : ℕ, j ≤ k → P j '' Set.Icc (0:ℝ) 1 ⊆ W
  hPlev : ∀ j : ℕ, 1 ≤ j → j ≤ k → Disjoint (P j '' Set.Icc (0:ℝ) 1) (Kex (j + 1))
  hPsep : ∀ j l : ℕ, j < l → l ≤ k →
    P j '' Set.Icc (0:ℝ) 1 ∩ P l '' Set.Icc (0:ℝ) 1 ⊆ {P j 1}
  hclean : ∀ j : ℕ, j ≤ k → Disjoint (ρ '' Set.Ioi τ) (P j '' Set.Icc (0:ℝ) 1)
  hlev : ∀ t : ℝ, τ < t → ρ t ∉ Kex (k + 2)
  hxlev : x ∉ Kex (k + 2)
  c₀ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))
  u₀ : EuclideanSpace ℝ (Fin n)
  e₀ : ℝ
  hP0 : P 0 0 = ρ 0
  hc₀ : c₀ ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
    Work.Noncompact.CompressionTube.smoothOrder M
  hu₀ : u₀ ≠ 0
  he₀ : 0 < e₀
  hρ0₀ : ρ 0 ∈ c₀.source
  hgerm₀ : ∀ t : ℝ, 0 ≤ t → t ≤ e₀ → P 0 t = c₀.symm (c₀ (ρ 0) + t • u₀)


end Work.Drive
