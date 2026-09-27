import Mathlib
import Submission.Work.SimplyConnected.ABS.globalizedBarrier_dev

/-!
# The clamped local barrier is superharmonic

The documented missing ingredient of the Perron/barrier step (see
`NOTES_session_new_agent.md` in this directory) is: given a *local* barrier `u` at a frontier point
`p` of `Ω`, produce a global superharmonic comparison function.  The classical construction clamps
`u` at a constant outside a neighbourhood of `p`.  This module isolates the point-set half of that
construction, which is where the subtlety lies:

* `clampedB u M W` is `min (u ·) M` on `W` and the constant `M` outside;
* **`clampedB_superharmonicOn`** proves that it is superharmonic on `Ω` as soon as
  `W ⊆ Ω`, `W ⊆ V`, and `M < u x` for every `x ∈ Ω ∩ frontier W` at which `u` is continuous.

The last hypothesis is *pointwise*, so no compactness or uniformity of `u` on `∂W` is needed: at
such a point `x` the openness of `{u > M}` (valid because `u` is continuous at `x`) makes
`clampedB` locally constant `M`.  The three sets `Ω ∩ W`, `Ω \ closure W` and
`interior {u > M}` then cover `Ω` and the localisation lemma
`superharmonicOnX_of_isOpen_cover_dev` concludes.
-/

open Set Filter
open scoped Topology Manifold ContDiff

noncomputable section
open Classical

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-- The clamped barrier: `min (u ·) M` on `W`, the constant `M` outside. -/
def clampedB (u : X → ℝ) (M : ℝ) (W : Set X) : X → ℝ :=
  fun x => if x ∈ W then min (u x) M else M

theorem clampedB_of_mem {u : X → ℝ} {M : ℝ} {W : Set X} {x : X} (hx : x ∈ W) :
    clampedB u M W x = min (u x) M := by unfold clampedB; rw [if_pos hx]

theorem clampedB_of_not_mem {u : X → ℝ} {M : ℝ} {W : Set X} {x : X} (hx : x ∉ W) :
    clampedB u M W x = M := by unfold clampedB; rw [if_neg hx]

theorem clampedB_le {u : X → ℝ} {M : ℝ} {W : Set X} (x : X) : clampedB u M W x ≤ M := by
  unfold clampedB
  by_cases h : x ∈ W
  · rw [if_pos h]; exact min_le_right _ _
  · rw [if_neg h]

theorem clampedB_eq_const_of_gt {u : X → ℝ} {M : ℝ} {W : Set X} {x : X} (hx : M < u x) :
    clampedB u M W x = M := by
  unfold clampedB
  by_cases h : x ∈ W
  · rw [if_pos h, min_eq_right hx.le]
  · rw [if_neg h]

/-! ## Superharmonicity is invariant under changing a function on an open set -/

/-- **Superharmonicity transports across an open set.**  If `u` is superharmonic on the open set
`U` and `v` agrees with `u` pointwise on `U`, then `v` is superharmonic on `U`.  (The pointwise
agreement on `U` is enough: the chart-ball test can always be shrunk to lie inside `U`.) -/
theorem SuperharmonicOnX.congr_of_isOpen {u v : X → ℝ} {U : Set X} (hU : IsOpen U)
    (huv : ∀ x ∈ U, v x = u x) (hu : Submission.SuperharmonicOnX u U) :
    Submission.SuperharmonicOnX v U := by
  obtain ⟨hcont_u, hAt⟩ := hu
  refine ⟨hcont_u.congr huv, fun x hx => ?_⟩
  obtain ⟨hxsrc, ρ, hρ, hρsub, hcont, hmvp⟩ := hAt x hx
  -- shrink the chart ball so that it lies inside `U`
  have hcx : (chartAt ℂ x).symm ((chartAt ℂ x) x) = x := (chartAt ℂ x).left_inv hxsrc
  have hpre : (chartAt ℂ x).symm ⁻¹' U ∈ 𝓝 ((chartAt ℂ x) x) := by
    have h2 : U ∈ 𝓝 ((chartAt ℂ x).symm ((chartAt ℂ x) x)) := by
      rw [hcx]; exact hU.mem_nhds hx
    exact ((chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source hxsrc)).preimage_mem_nhds h2
  obtain ⟨ρ', hρ'pos, hρ'sub⟩ := Metric.mem_nhds_iff.mp hpre
  have hρ''pos : 0 < min ρ ρ' := lt_min hρ hρ'pos
  have hsub'' : Metric.ball ((chartAt ℂ x) x) (min ρ ρ') ⊆ (chartAt ℂ x).target :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hρsub
  have hU'' : Metric.ball ((chartAt ℂ x) x) (min ρ ρ') ⊆ (chartAt ℂ x).symm ⁻¹' U :=
    (Metric.ball_subset_ball (min_le_right _ _)).trans hρ'sub
  rw [Submission.SuperharmonicOnXAt, Submission.SuperharmonicAtChart]
  refine ⟨hxsrc, min ρ ρ', hρ''pos, hsub'', ?_, ?_⟩
  · -- continuity of the pullback of `v`
    refine ContinuousOn.congr (hcont.mono (Metric.ball_subset_ball (min_le_left _ _))) ?_
    intro w hw
    exact huv _ (hU'' hw)
  · -- the circle mean value inequality
    intro p hp r hr hpr
    have hpρ : p ∈ Metric.ball ((chartAt ℂ x) x) ρ :=
      Metric.ball_subset_ball (min_le_left _ _) hp
    have hprρ : Metric.closedBall p r ⊆ Metric.ball ((chartAt ℂ x) x) ρ :=
      hpr.trans (Metric.ball_subset_ball (min_le_left _ _))
    have hpeq : (v ∘ (chartAt ℂ x).symm) p = (u ∘ (chartAt ℂ x).symm) p := huv _ (hU'' hp)
    have hsphere : Set.EqOn (v ∘ (chartAt ℂ x).symm) (u ∘ (chartAt ℂ x).symm)
        (Metric.sphere p |r|) := by
      intro z hz
      have hz' : dist z p ≤ r := by
        have h := Metric.mem_sphere.mp hz
        rw [abs_of_pos hr] at h
        exact h.le
      exact huv _ (hU'' (hpr (Metric.mem_closedBall.mpr hz')))
    rw [hpeq, Real.circleAverage_congr_sphere hsphere]
    exact hmvp p hpρ r hr hprρ

/-! ## The clamped barrier is superharmonic on `Ω` -/

/-- **The clamped local barrier is superharmonic.**  Let `u` be superharmonic on `Ω ∩ V`, let
`W ⊆ Ω`, `W ⊆ V`, and suppose `M < u x` at every point `x ∈ Ω ∩ frontier W` at which `u` is
continuous.  Then `clampedB u M W` is superharmonic on `Ω`.

The hypothesis is *pointwise*, so no compactness or uniformity of `u` on `∂W` is needed: at such a
point `x` the set `interior {u > M}` is an open neighbourhood of `x`, on which `clampedB` is
identically `M`.  The three open sets `Ω ∩ W`, `Ω \ closure W` and `interior {u > M}` cover `Ω`,
and the localisation lemma `superharmonicOnX_of_isOpen_cover_dev` concludes. -/
theorem clampedB_superharmonicOn {u : X → ℝ} {Ω W V : Set X} {M : ℝ}
    (hΩo : IsOpen Ω) (hWo : IsOpen W) (hWΩ : W ⊆ Ω) (hWV : W ⊆ V)
    (hsup : Submission.SuperharmonicOnX u (Ω ∩ V))
    (hcont : ∀ x ∈ Ω ∩ frontier W, ContinuousAt u x)
    (hMin : ∀ x ∈ Ω ∩ frontier W, M < u x) :
    Submission.SuperharmonicOnX (clampedB u M W) Ω := by
  have hWΩV : Ω ∩ W ⊆ Ω ∩ V := fun x hx => ⟨hx.1, hWV hx.2⟩
  have hsupW : Submission.SuperharmonicOnX u (Ω ∩ W) :=
    (Submission.SuperharmonicOnX.mono hsup hWΩV) (hsup.1.mono hWΩV)
  have hminW : Submission.SuperharmonicOnX (fun x => min (u x) M) (Ω ∩ W) :=
    Work.SimplyConnected.ABS.SuperharmonicOnX.inf_const_dev hsupW M
  set U₀ : Set X := Ω ∩ W with hU₀def
  set U₁ : Set X := Ω \ closure W with hU₁def
  set U₂ : Set X := interior {y : X | M < u y} with hU₂def
  have hU₀o : IsOpen U₀ := hΩo.inter hWo
  have hU₁o : IsOpen U₁ := hΩo.sdiff isClosed_closure
  have hU₂o : IsOpen U₂ := by rw [hU₂def]; exact isOpen_interior
  have hA : Submission.SuperharmonicOnX (clampedB u M W) U₀ :=
    Work.SimplyConnected.ABS.SuperharmonicOnX.congr_of_isOpen hU₀o
      (fun x hx => by unfold clampedB; rw [if_pos hx.2]) hminW
  have hB : Submission.SuperharmonicOnX (clampedB u M W) U₁ :=
    Work.SimplyConnected.ABS.SuperharmonicOnX.congr_of_isOpen hU₁o
      (fun x hx => by
        rw [hU₁def] at hx
        unfold clampedB
        rw [if_neg (fun hxW => hx.2 (subset_closure hxW))])
      (superharmonicOnX_const_dev M U₁)
  have hC : Submission.SuperharmonicOnX (clampedB u M W) U₂ := by
    rw [hU₂def]
    exact Work.SimplyConnected.ABS.SuperharmonicOnX.congr_of_isOpen isOpen_interior
      (fun x hx => by
        have hgt : M < u x := interior_subset (s := {y : X | M < u y}) hx
        unfold clampedB
        by_cases h : x ∈ W
        · rw [if_pos h, min_eq_right hgt.le]
        · rw [if_neg h])
      (superharmonicOnX_const_dev M _)
  have hcover : ∀ x ∈ Ω, x ∈ U₀ ∨ x ∈ U₁ ∨ x ∈ U₂ := by
    intro x hxΩ
    by_cases hxW : x ∈ W
    · exact Or.inl ⟨hxΩ, hxW⟩
    · by_cases hxcl : x ∈ closure W
      · have hxfr : x ∈ Ω ∩ frontier W := by
          refine ⟨hxΩ, ?_⟩
          rw [frontier]
          exact ⟨hxcl, fun hxint => hxW (interior_subset hxint)⟩
        have hgt : M < u x := hMin x hxfr
        have hmem : {y : X | M < u y} ∈ 𝓝 x :=
          (hcont x hxfr).preimage_mem_nhds (isOpen_Ioi.mem_nhds hgt)
        have h2 : x ∈ U₂ := by
          rw [hU₂def]
          exact mem_interior_iff_mem_nhds.mpr hmem
        exact Or.inr (Or.inr h2)
      · exact Or.inr (Or.inl ⟨hxΩ, hxcl⟩)
  let Wv : Fin 3 → Set X := ![U₀, U₁, U₂]
  have hWo' : ∀ i, IsOpen (Wv i) := by
    intro i
    fin_cases i
    · simpa [Wv] using hU₀o
    · simpa [Wv] using hU₁o
    · simpa [Wv] using hU₂o
  have hcov' : Ω ⊆ ⋃ i, Wv i := by
    intro x hx
    rcases hcover x hx with h | h | h
    · exact Set.mem_iUnion.mpr ⟨0, by simpa [Wv] using h⟩
    · exact Set.mem_iUnion.mpr ⟨1, by simpa [Wv] using h⟩
    · exact Set.mem_iUnion.mpr ⟨2, by simpa [Wv] using h⟩
  have hV' : ∀ i, Submission.SuperharmonicOnX (clampedB u M W) (Wv i) := by
    intro i
    fin_cases i
    · simpa [Wv] using hA
    · simpa [Wv] using hB
    · simpa [Wv] using hC
  exact Work.SimplyConnected.ABS.superharmonicOnX_of_isOpen_cover_dev hWo' hcov' hV'


/-! ## From a clamp region to a global barrier -/

/-- **The global barrier from a clamp region.**  If `W ⊆ Ω ∩ V` is a neighbourhood of `p` on which
`u` is already small, `u > 0` on `Ω ∩ W`, and `M < u x` at every continuous point of
`Ω ∩ frontier W`, then `β := clampedB u M W` is a global barrier at `p`: superharmonic and
nonnegative on `Ω`, positive off `p`, and tending to `0` at `p`.

This is the assembly step of the barrier globalisation; the geometric input is the choice of `W`
and `M` (in the applications from the engulfing route, `W := Ω ∩ V ∩ {u < M'}` with `M < M'`). -/
theorem exists_globalBarrier_of_clamp {u : X → ℝ} {Ω W V : Set X} {M : ℝ} {p : X}
    (hΩo : IsOpen Ω) (hWo : IsOpen W) (hWΩ : W ⊆ Ω) (hWV : W ⊆ V)
    (hsup : Submission.SuperharmonicOnX u (Ω ∩ V))
    (hcont : ∀ x ∈ Ω ∩ frontier W, ContinuousAt u x)
    (hMpos : 0 < M) (hMin : ∀ x ∈ Ω ∩ frontier W, M < u x)
    (hpos : ∀ x ∈ Ω ∩ W, 0 < u x)
    (hnear : ∀ ε : ℝ, 0 < ε → ∃ N : Set X, N ∈ 𝓝 p ∧ ∀ x ∈ Ω ∩ W ∩ N, u x < ε)
    (hWp : ∀ᶠ x in 𝓝[Ω] p, x ∈ W) :
    ∃ β : X → ℝ, Submission.SuperharmonicOnX β Ω ∧ (∀ x ∈ Ω, 0 ≤ β x) ∧
      (∀ x ∈ Ω, x ≠ p → 0 < β x) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : Set X, N ∈ 𝓝 p ∧ ∀ x ∈ Ω ∩ N, β x < ε) := by
  have hSH : Submission.SuperharmonicOnX (clampedB u M W) Ω :=
    clampedB_superharmonicOn hΩo hWo hWΩ hWV hsup hcont hMin
  -- `p` is a limit of `Ω`-points lying in `W`
  obtain ⟨t₁, ht₁, t₂, ht₂, heq⟩ := Filter.mem_inf_iff.mp hWp
  have ht₂' : Ω ⊆ t₂ := by simpa using ht₂
  have hsubW : ∀ x ∈ Ω ∩ t₁, x ∈ W := by
    intro x hx
    have hmem : x ∈ t₁ ∩ t₂ := ⟨hx.2, ht₂' hx.1⟩
    rw [← heq] at hmem
    exact hmem
  refine ⟨clampedB u M W, hSH, ?_, ?_, ?_⟩
  · intro x hx
    by_cases hxW : x ∈ W
    · rw [clampedB_of_mem hxW]
      exact (lt_min (hpos x ⟨hx, hxW⟩) hMpos).le
    · rw [clampedB_of_not_mem hxW]
      exact hMpos.le
  · intro x hx _
    by_cases hxW : x ∈ W
    · rw [clampedB_of_mem hxW]
      exact lt_min (hpos x ⟨hx, hxW⟩) hMpos
    · rw [clampedB_of_not_mem hxW]
      exact hMpos
  · intro ε hε
    obtain ⟨N₁, hN₁, h₁⟩ := hnear ε hε
    refine ⟨t₁ ∩ N₁, Filter.inter_mem ht₁ hN₁, ?_⟩
    intro x hx
    have hxW : x ∈ W := hsubW x ⟨hx.1, hx.2.1⟩
    rw [clampedB_of_mem hxW]
    exact lt_of_le_of_lt (min_le_left _ _) (h₁ x ⟨⟨hx.1, hxW⟩, hx.2.2⟩)

end Work.SimplyConnected.ABS
