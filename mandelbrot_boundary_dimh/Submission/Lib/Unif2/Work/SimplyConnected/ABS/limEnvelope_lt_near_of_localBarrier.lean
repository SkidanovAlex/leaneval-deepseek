import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.GreenSetupReg
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.MajorantRegDesign
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.limEnvelope_le_smul_of_barrier
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.clampedBarrierDefs
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.globalBarrierOfClampedCollar
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.decayStepInputs
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.clampedBarrierSuperharmonic
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.globalizedBarrier_dev
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.globalBarrierOfLocalBarrierReg
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.farVanishesLocal

open Filter Set
open scoped Topology

namespace Work.SimplyConnected.ABS

/-! ## The clamped barrier and the circle super-mean-value inequality

`Work.SimplyConnected.ABS.clampBarrier u V 1` is `min (u ·) 1` on `V` and the constant `1` outside
`V`.  It is *upper* semicontinuous (`upperSemicontinuousOn_clampBarrier`), and it satisfies the
continuity-free circle **super**-mean-value inequality `CircleSuperMeanValueAtX` at every point of
`Ω ∩ V` and of `Ω \ closure V`.  The two lemmas below prove this; only the remaining case
`Ω ∩ frontier V` is not covered, and there the inequality is genuinely false in general (see
`NOTES_limEnvelope_localBarrier_SESSION7.md`). -/

section ClampMVI

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The library's superharmonicity at a point (which bundles continuity) implies the
continuity-free circle super-mean-value inequality. -/
theorem CircleSuperMeanValueAtX.of_superharmonicOnXAt {v : X → ℝ} {x : X}
    (h : Submission.SuperharmonicOnXAt v x) : CircleSuperMeanValueAtX v x := by
  rw [Submission.SuperharmonicOnXAt, Submission.SuperharmonicAtChart] at h
  obtain ⟨-, ρ, hρ, hsub, -, hmvi⟩ := h
  exact ⟨ρ, hρ, hsub, hmvi⟩

/-- **The clamped barrier satisfies the circle super-mean-value inequality on `Ω ∩ V`.**

Since `x ∈ Ω ∩ V` and `V` is open, the chart ball on which `min (u ·) 1` is superharmonic (a
present of `Submission.SuperharmonicOnX.inf_const_dev`, whose `SuperharmonicAtChart` clause holds
at *every* point of that ball) can be shrunk into `V`, where the clamped barrier agrees with
`min (u ·) 1` — and hence so does every circle inside the shrunk ball. -/
theorem clampBarrier_circleSuperMVI_of_mem {u : X → ℝ} {Ω V : Set X}
    (hVo : IsOpen V) (hu : Submission.SuperharmonicOnX u (Ω ∩ V)) :
    ∀ x ∈ Ω ∩ V, CircleSuperMeanValueAtX (clampBarrier u V 1) x := by
  intro x hx
  have hmin : Submission.SuperharmonicOnX (fun y => min (u y) 1) (Ω ∩ V) := by
    have h := Work.SimplyConnected.ABS.SuperharmonicOnX.inf_const_dev hu 1
    simpa using h
  have hAt : Submission.SuperharmonicOnXAt (fun y => min (u y) 1) x := hmin.2 x hx
  rw [Submission.SuperharmonicOnXAt, Submission.SuperharmonicAtChart] at hAt
  obtain ⟨hxsrc, ρ₀, hρ₀, hsub₀, -, hmvi₀⟩ := hAt
  -- a chart ball around `x` whose image lies in `V`
  have hpre : (chartAt ℂ x).symm ⁻¹' V ∈ 𝓝 ((chartAt ℂ x) x) := by
    have h2 : V ∈ 𝓝 ((chartAt ℂ x).symm ((chartAt ℂ x) x)) := by
      rw [(chartAt ℂ x).left_inv hxsrc]
      exact hVo.mem_nhds hx.2
    exact ((chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source hxsrc)).preimage_mem_nhds h2
  obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨min ρ₀ ρ₁, lt_min hρ₀ hρ₁,
    fun Z hZ => hsub₀ (Metric.ball_subset_ball (min_le_left _ _) hZ), ?_⟩
  intro p hp r hr hpr
  have hp₀ : p ∈ Metric.ball ((chartAt ℂ x) x) ρ₀ := Metric.ball_subset_ball (min_le_left _ _) hp
  have hpr₀ : Metric.closedBall p r ⊆ Metric.ball ((chartAt ℂ x) x) ρ₀ :=
    hpr.trans (Metric.ball_subset_ball (min_le_left _ _))
  have hpr₁ : Metric.closedBall p r ⊆ Metric.ball ((chartAt ℂ x) x) ρ₁ :=
    hpr.trans (Metric.ball_subset_ball (min_le_right _ _))
  have hval : ∀ Z ∈ Metric.closedBall p r,
      clampBarrier u V 1 ((chartAt ℂ x).symm Z) = min (u ((chartAt ℂ x).symm Z)) 1 := by
    intro Z hZ
    exact clampBarrier_of_mem (u := u) (V := V) (C := 1)
      (x := (chartAt ℂ x).symm Z) (hρ₁sub (hpr₁ hZ))
  have hconn : Set.EqOn ((clampBarrier u V 1) ∘ (chartAt ℂ x).symm)
      ((fun y => min (u y) 1) ∘ (chartAt ℂ x).symm) (Metric.sphere p |r|) := by
    intro Z hZ
    exact hval Z (Metric.sphere_subset_closedBall (by simpa only [abs_of_pos hr] using hZ))
  rw [Real.circleAverage_congr_sphere hconn]
  rw [show (clampBarrier u V 1 ∘ (chartAt ℂ x).symm) p
      = min (u ((chartAt ℂ x).symm p)) 1 from hval p (Metric.mem_closedBall_self hr.le)]
  exact hmvi₀ p hp₀ r hr hpr₀

/-- **The clamped barrier satisfies the circle super-mean-value inequality off `closure V`.**

There the clamped barrier is identically `1`, so every circle average is `1` as well. -/
theorem clampBarrier_circleSuperMVI_of_not_mem_closure {u : X → ℝ} {Ω V : Set X} :
    ∀ x ∈ Ω \ closure V, CircleSuperMeanValueAtX (clampBarrier u V 1) x := by
  intro x hx
  have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hpre : (chartAt ℂ x).symm ⁻¹' (closure V)ᶜ ∈ 𝓝 ((chartAt ℂ x) x) := by
    have h2 : (closure V)ᶜ ∈ 𝓝 ((chartAt ℂ x).symm ((chartAt ℂ x) x)) := by
      rw [(chartAt ℂ x).left_inv hxsrc]
      exact isClosed_closure.isOpen_compl.mem_nhds hx.2
    exact ((chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source hxsrc)).preimage_mem_nhds h2
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hpre
  obtain ⟨ρ', hρ', hρ'tgt⟩ := Metric.mem_nhds_iff.mp
    ((chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source hxsrc))
  refine ⟨min ρ ρ', lt_min hρ hρ',
    fun Z hZ => hρ'tgt (Metric.ball_subset_ball (min_le_right _ _) hZ), ?_⟩
  intro p hp r hr hpr
  have hpcl : (chartAt ℂ x).symm p ∈ (closure V)ᶜ :=
    hρsub (Metric.ball_subset_ball (min_le_left _ _) hp)
  have hval : clampBarrier u V 1 ((chartAt ℂ x).symm p) = 1 :=
    clampBarrier_of_not_mem (u := u) (V := V) (C := 1)
      (x := (chartAt ℂ x).symm p) (fun hmem => hpcl (subset_closure hmem))
  have hconn : Set.EqOn ((clampBarrier u V 1) ∘ (chartAt ℂ x).symm)
      (fun _ : ℂ => (1 : ℝ)) (Metric.sphere p |r|) := by
    intro Z hZ
    refine clampBarrier_of_not_mem (u := u) (V := V) (C := 1)
      (x := (chartAt ℂ x).symm Z) (fun hmem => ?_)
    exact hρsub (Metric.ball_subset_ball (min_le_left _ _)
      (hpr (Metric.sphere_subset_closedBall (by simpa only [abs_of_pos hr] using hZ))))
      (subset_closure hmem)
  rw [Real.circleAverage_congr_sphere hconn, Real.circleAverage_const]
  show (1 : ℝ) ≤ clampBarrier u V 1 ((chartAt ℂ x).symm p)
  rw [hval]

/-- The two preceding cases combined. -/
theorem clampBarrier_circleSuperMVI {u : X → ℝ} {Ω V : Set X} (hVo : IsOpen V)
    (hu : Submission.SuperharmonicOnX u (Ω ∩ V)) :
    ∀ x ∈ (Ω ∩ V) ∪ (Ω \ closure V), CircleSuperMeanValueAtX (clampBarrier u V 1) x := by
  intro x hx
  rcases hx with hx | hx
  · exact clampBarrier_circleSuperMVI_of_mem hVo hu x hx
  · exact clampBarrier_circleSuperMVI_of_not_mem_closure x hx

end ClampMVI

/-- **The globalised barrier: the case where the clamp can be performed.**

This is the case of `globalizedBarrier_of_localBarrier` in which the clamp construction is
available: there is an open `W ⊆ U`, `W ⊆ V`, containing the near-`p` part of `U` in the sense of
`∀ᶠ x in 𝓝[U] p, x ∈ W`, with `closure W ⊆ V` (so that `u` is continuous at every point of the
artificial boundary `U ∩ frontier W`), and the *strict* condition `C < u x` holds there.  That
strict condition is exactly what makes the clamped barrier `clampedB u C W` continuous, hence
superharmonic in the library's sense, at `U ∩ frontier W`, so that `clampedB_superharmonicOn`
applies.  The result `β := clampedB u C W` is a barrier on `U` with all four required properties:
it is superharmonic on `U`, nonnegative, `< ε` near `p` (where `β = min (u ·) C` and `u → 0`), and
equal to `C` on a neighbourhood of every point of `frontier U \ frontier Ω`, since that set misses
`closure V ⊇ closure W` by `hVK`. -/
theorem globalizedBarrier_of_localBarrier_of_clampCondition {X : Type*} [TopologicalSpace X]
    [T2Space X] [PreconnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω U : Set X} (hUo : IsOpen U) (hUΩ : U ⊆ Ω)
    {p : X} {V W : Set X} (hVo : IsOpen V) (hpV : p ∈ V)
    {u : X → ℝ} (hu : Submission.SuperharmonicOnX u (Ω ∩ V))
    (hupos : ∀ x ∈ Ω ∩ V, 0 < u x) (hucont : ContinuousOn u V) (hup : u p = 0)
    (hVK : ∀ ζ ∈ frontier U, ζ ∉ frontier Ω → ζ ∉ closure V)
    (hWo : IsOpen W) (hWU : W ⊆ U) (hWV : W ⊆ V) (hWcl : closure W ⊆ V)
    (hWp : ∀ᶠ x in 𝓝[U] p, x ∈ W)
    {C : ℝ} (hC : 0 < C) (hclamp : ∀ x ∈ U ∩ frontier W, C < u x) :
    ∃ β : X → ℝ,
      Submission.SuperharmonicOnX β U ∧
      (∀ x ∈ U, 0 ≤ β x) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : Set X, N ∈ 𝓝 p ∧ ∀ x ∈ U ∩ N, β x < ε) ∧
      (∀ ζ ∈ frontier U, ζ ∉ frontier Ω →
        ∃ W' : Set X, IsOpen W' ∧ ζ ∈ W' ∧ ∀ y ∈ W', β y = C) := by
  have hUV : U ∩ V ⊆ Ω ∩ V := fun x hx => ⟨hUΩ hx.1, hx.2⟩
  have hsup' : Submission.SuperharmonicOnX u (U ∩ V) :=
    (Submission.SuperharmonicOnX.mono hu hUV) (hu.1.mono hUV)
  have hcont' : ∀ x ∈ U ∩ frontier W, ContinuousAt u x := by
    intro x hx
    exact hucont.continuousAt (hVo.mem_nhds (hWcl (frontier_subset_closure hx.2)))
  have hβ : Submission.SuperharmonicOnX (clampedB u C W) U :=
    clampedB_superharmonicOn hUo hWo hWU hWV hsup' hcont' hclamp
  refine ⟨clampedB u C W, hβ, ?_, ?_, ?_⟩
  · intro x hx
    by_cases hxW : x ∈ W
    · rw [clampedB_of_mem hxW]
      exact le_of_lt (lt_min (hupos x ⟨hUΩ hx, hWV hxW⟩) hC)
    · rw [clampedB_of_not_mem hxW]
      exact hC.le
  · intro ε hε
    rw [nhdsWithin] at hWp
    obtain ⟨N₁, hN₁, t₂, ht₂, heq⟩ := Filter.mem_inf_iff.mp hWp
    have hN₁sub : ∀ x ∈ N₁ ∩ U, x ∈ W := by
      intro x hx
      have hx' : x ∈ N₁ ∩ t₂ := ⟨hx.1, (Filter.mem_principal.mp ht₂) hx.2⟩
      rwa [← heq] at hx'
    have huv : ∀ᶠ x in 𝓝 p, u x < ε :=
      (hucont.continuousAt (hVo.mem_nhds hpV)).eventually
        (isOpen_Iio.mem_nhds (by rw [hup]; exact hε))
    obtain ⟨N₂, hN₂, hN₂sub⟩ := Filter.eventually_iff_exists_mem.mp huv
    refine ⟨N₁ ∩ N₂, Filter.inter_mem hN₁ hN₂, ?_⟩
    intro x hx
    have hxW : x ∈ W := hN₁sub x ⟨hx.2.1, hx.1⟩
    rw [clampedB_of_mem hxW]
    exact lt_of_le_of_lt (min_le_left _ _) (hN₂sub x hx.2.2)
  · intro ζ hζ hζfr
    have hζcW : ζ ∉ closure W := fun h =>
      hVK ζ hζ hζfr (subset_closure (hWcl h))
    exact ⟨(closure W)ᶜ, isClosed_closure.isOpen_compl, hζcW,
      fun y hy => clampedB_of_not_mem (fun hyW => hy (subset_closure hyW))⟩

/-- **The far-datum comparison for the limsup Perron envelope.**

Let `K ⊆ frontier U` and suppose the datum satisfies `f ≤ 0` off `K`.  Then

    limEnvelope U f M ≤ M · limEnvelope U 1_K 1    on `U`.

Indeed every member `v` of `limFamily U f M` is bounded by `M`, so `v / M` is a member of
`limFamily U 1_K 1`: it is subharmonic, bounded by `1`, and at a frontier point `ζ` its limsup is at
most `1_K ζ + ε` — for `ζ ∉ K` because `f ζ ≤ 0`, and for `ζ ∈ K` because `v ≤ M` pointwise.

This is the link between the classical far-datum (harmonic-measure) statement and the target: the
right-hand side is the quantity shown to be small near `p` by
`Work.SimplyConnected.ABS.FarLocal.limEnvelope_indicator_far_vanishes`. -/
theorem limEnvelope_le_smul_farEnvelope {X : Type*} [TopologicalSpace X] [T2Space X]
    [PreconnectedSpace X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {U : Set X} (hUo : IsOpen U) {f : X → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hneF : (Submission.limFamily U f M).Nonempty)
    {K : Set X} (hKfr : K ⊆ frontier U)
    (hfK : ∀ ζ ∈ frontier U, ζ ∉ K → f ζ ≤ 0) :
    ∀ x ∈ U, Submission.limEnvelope U f M x ≤
      M * Submission.limEnvelope U (Set.indicator K (fun _ => (1 : ℝ))) 1 x := by
  rcases eq_or_lt_of_le hM with hM0 | hMpos
  · -- `M = 0`: every member is `≤ 0`
    intro x hx
    subst hM0
    rw [zero_mul]
    refine csSup_le ?_ ?_
    · exact (Submission.limFamily_isPerronOn hUo hneF).nonempty.image _
    · rintro y ⟨v, hv, rfl⟩
      exact hv.2.1 x
  · -- the member comparison
    have hmem : ∀ v ∈ Submission.limFamily U f M, ∀ x ∈ U, v x ≤
        M * Submission.limEnvelope U (Set.indicator K (fun _ => (1 : ℝ))) 1 x := by
      intro v hv x hx
      have hdiv : (fun y => v y / M) ∈
          Submission.limFamily U (Set.indicator K (fun _ => (1 : ℝ))) 1 := by
        refine ⟨?_, ?_, ?_⟩
        · have h := Submission.limFamily_subharmonic hv
          simpa only [div_eq_inv_mul] using
            Submission.SubharmonicOnX.const_mul (inv_nonneg.mpr hMpos.le) h
        · intro y
          rw [div_le_one hMpos]
          exact hv.2.1 y
        · intro ζ hζ ε hε
          by_cases hζK : ζ ∈ K
          · -- at a point of `K` the pointwise bound `v ≤ M` already gives the datum `1`
            rw [Set.indicator_of_mem hζK]
            filter_upwards with y
            rw [div_le_iff₀ hMpos]
            nlinarith [hv.2.1 y, hε, hMpos]
          · -- off `K` the limsup condition and `f ≤ 0` give the datum `0`
            have hfz : f ζ ≤ 0 := hfK ζ hζ hζK
            have hεM : 0 < ε * M := mul_pos hε hMpos
            rw [Set.indicator_of_notMem hζK]
            filter_upwards [hv.2.2 ζ hζ (ε * M) hεM] with y hy
            calc v y / M ≤ (f ζ + ε * M) / M := div_le_div_of_nonneg_right hy hMpos.le
              _ = f ζ / M + ε := by field_simp
              _ ≤ 0 + ε := by
                  have h1 : f ζ / M ≤ 0 := div_nonpos_of_nonpos_of_nonneg hfz hMpos.le
                  linarith
      have hle := Submission.limFamily_le_limEnvelope hUo
        ⟨fun _ => 0,
          (Submission.SubharmonicOnX.mono (Submission.subharmonicOnX_const 0)
            (Set.subset_univ U)) continuousOn_const,
          (fun _ => by norm_num), (fun ζ _ ε hε => by
            filter_upwards with y
            have h0 : (0 : ℝ) ≤ Set.indicator K (fun _ => (1 : ℝ)) ζ :=
              Set.indicator_nonneg (fun _ _ => zero_le_one) ζ
            linarith)⟩
        hdiv x hx
      calc v x = M * (v x / M) := by field_simp
        _ ≤ M * Submission.limEnvelope U (Set.indicator K (fun _ => (1 : ℝ))) 1 x :=
            mul_le_mul_of_nonneg_left hle hMpos.le
    -- the envelope is the supremum of its members
    intro x hx
    rw [Submission.limEnvelope, Submission.upperEnvelope]
    refine csSup_le ((Submission.limFamily_isPerronOn hUo hneF).nonempty.image _) ?_
    rintro y ⟨v, hv, rfl⟩
    exact hmem v hv x hx

/-- **The target under the (provable) collar hypothesis.**  If, in addition to the hypotheses of
`limEnvelope_lt_near_of_localBarrier`, there is an open *collar* `S ⊆ U` with `closure S ⊆ V`,
`U ∩ N ⊆ S` for a neighbourhood `N` of `p`, the eventual separation
`∀ ξ ∈ frontier S, ξ ∈ U → ∀ᶠ z in 𝓝[U] ξ, 1 ≤ u z` (plus its pointwise consequence at `ξ`), and
`frontier U \ frontier Ω` disjoint from `closure S`, then the conclusion of the target follows.

The barrier used is the *clamped collar* `β := clampedBarrier u S 1`: it equals `min (u ·) 1` on the
open `S` (where `u` is superharmonic), and the constant `1` on `X \ closure S`; at the collar
`frontier S ∩ U` the eventual separation makes it *locally constant* `1`, so it is superharmonic
there too.  In particular `β ≡ 1` on the neighbourhood `X \ closure S` of `frontier U \ frontier Ω`,
which gives both the lower bound and the continuity needed by
`Submission.limEnvelope_le_smul_of_barrier`.

This isolates the only remaining gap of the target: the existence of such a collar in general
(it fails in the cusp case, e.g. the slit plane). -/
theorem limEnvelope_lt_near_of_localBarrier_of_collar {X : Type*} [TopologicalSpace X] [T2Space X]
    [PreconnectedSpace X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} (hΩo : IsOpen Ω) {U : Set X} (hUo : IsOpen U) (hUΩ : U ⊆ Ω)
    (hcomp : IsCompact (closure U)) (hfrU : (frontier U).Nonempty)
    {f : X → ℝ} {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε)
    (hneF : (Submission.limFamily U f M).Nonempty)
    (hf0 : ∀ ζ ∈ frontier Ω, f ζ ≤ 0)
    {p : X} (hp : p ∈ frontier Ω) (hpU : p ∈ closure U)
    {u : X → ℝ} {V S : Set X} (hVo : IsOpen V) (hpV : p ∈ V)
    (hu : Submission.SuperharmonicOnX u (Ω ∩ V)) (hupos : ∀ x ∈ Ω ∩ V, 0 < u x)
    (hucont : ContinuousOn u V) (hup : u p = 0)
    (hSo : IsOpen S) (hSU : S ⊆ U) (hSV : closure S ⊆ V)
    (hN : ∃ N : Set X, N ∈ nhds p ∧ U ∩ N ⊆ S)
    (hsep : ∀ ξ ∈ frontier S, ξ ∈ U → 1 ≤ u ξ)
    (hcollar : ∀ ξ ∈ frontier S, ξ ∈ U → ∀ᶠ z in nhdsWithin ξ U, 1 ≤ u z)
    (hKdisj : ∀ ζ ∈ frontier U, ζ ∉ frontier Ω → ζ ∉ closure S) :
    ∃ N : Set X, IsOpen N ∧ p ∈ N ∧
      ∀ x ∈ U, x ∈ N → Submission.limEnvelope U f M x < ε := by
  classical
  by_cases hM0 : M = 0
  · refine ⟨Set.univ, isOpen_univ, trivial, fun x hxU _ => ?_⟩
    have hle : Submission.limEnvelope U f M x ≤ M :=
      Submission.IsPerronOn.upperEnvelope_le (Submission.limFamily_isPerronOn hUo hneF) hxU
    have hzero : Submission.limEnvelope U f M x ≤ 0 := by rw [← hM0]; exact hle
    linarith
  · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
    -- **superharmonicity of the clamped collar at every point of `U`**
    have hAt : ∀ x ∈ U, Submission.SuperharmonicOnXAt (clampedBarrier u S 1) x := by
      intro x hxU
      by_cases hxS : x ∈ S
      · have hxV : x ∈ Ω ∩ V := ⟨hUΩ hxU, hSV (subset_closure hxS)⟩
        refine superharmonicOnXAt_congr_gbcc
          (superharmonicOnXAt_inf_const_gbcc (hu.2 x hxV) 1) ?_
        filter_upwards [hSo.mem_nhds hxS] with z hz
        exact (clampedBarrier_of_mem hz).symm
      · by_cases hxcl : x ∈ closure S
        · have hxfr : x ∈ frontier S := ⟨hxcl, by rw [hSo.interior_eq]; exact hxS⟩
          obtain ⟨U₀, hU₀, t, ht, heq⟩ := Filter.mem_inf_iff.mp (hcollar x hxfr hxU)
          have hUsub : ∀ z ∈ U₀, z ∈ U → 1 ≤ u z := by
            intro z hz hzU
            have : z ∈ {z : X | 1 ≤ u z} := by rw [heq]; exact ⟨hz, ht hzU⟩
            exact this
          refine superharmonicOnXAt_congr_gbcc (superharmonicOnXAt_const_gbcc 1 x) ?_
          filter_upwards [hU₀] with z hz
          by_cases hzS : z ∈ S
          · rw [clampedBarrier_of_mem hzS]
            exact (min_eq_right (hUsub z hz (hSU hzS))).symm
          · rw [clampedBarrier_of_not_mem hzS]
        · refine superharmonicOnXAt_congr_gbcc (superharmonicOnXAt_const_gbcc 1 x) ?_
          filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxcl] with z hz
          exact (clampedBarrier_of_not_mem (fun hzS => hz (subset_closure hzS))).symm
    have hβSC : Submission.SuperharmonicOnX (clampedBarrier u S 1) U :=
      ⟨fun x hxU => (Submission.SuperharmonicAtChart.continuousAt (hAt x hxU)).continuousWithinAt,
        hAt⟩
    -- **nonnegativity on `U`**
    have hβ0 : ∀ x ∈ U, 0 ≤ clampedBarrier u S 1 x := by
      intro x hxU
      by_cases hxS : x ∈ S
      · rw [clampedBarrier_of_mem hxS]
        exact le_of_lt (lt_min (hupos x ⟨hUΩ hxU, hSV (subset_closure hxS)⟩) one_pos)
      · rw [clampedBarrier_of_not_mem hxS]; norm_num
    -- **the clamped collar equals `1` off `closure S`**
    have hβone : ∀ y : X, y ∉ closure S → clampedBarrier u S 1 y = 1 := by
      intro y hy
      rw [clampedBarrier_of_not_mem (fun h => hy (subset_closure h))]
    have hKfr : (frontier U \ frontier Ω) ⊆ frontier U := Set.sdiff_subset
    have hKcont : ∀ ζ ∈ frontier U \ frontier Ω, ContinuousAt (clampedBarrier u S 1) ζ := by
      intro ζ hζ
      have hζcl : ζ ∉ closure S := hKdisj ζ hζ.1 hζ.2
      refine (continuousAt_const : ContinuousAt (fun _ : X => (1 : ℝ)) ζ).congr ?_
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hζcl] with y hy
      exact (hβone y hy).symm
    have hmβ : ∀ ζ ∈ frontier U \ frontier Ω, (1 : ℝ) ≤ clampedBarrier u S 1 ζ := by
      intro ζ hζ
      rw [hβone ζ (hKdisj ζ hζ.1 hζ.2)]
    have hf : ∀ ζ ∈ frontier U, ζ ∉ frontier U \ frontier Ω → f ζ ≤ 0 := by
      intro ζ hζU hζ
      by_cases h : ζ ∈ frontier Ω
      · exact hf0 ζ h
      · exact absurd ⟨hζU, h⟩ hζ
    have hcmp := limEnvelope_le_smul_of_barrier hUo hcomp hfrU hM hneF hβSC hβ0
      hKfr hKcont one_pos hmβ hf
    -- **the neighbourhood of `p` on which the collar is small**
    obtain ⟨N₀, hN₀, hN₀sub⟩ := hN
    obtain ⟨N₁, hN₁sub, hN₁open, hpN₁⟩ := mem_nhds_iff.mp hN₀
    have hN₁S : U ∩ N₁ ⊆ S := fun x hx => hN₀sub ⟨hx.1, hN₁sub hx.2⟩
    have hup_cont : ContinuousAt u p := hucont.continuousAt (hVo.mem_nhds hpV)
    have hδ : 0 < min 1 (ε / (M + 1)) := lt_min one_pos (by positivity)
    have hev : ∀ᶠ z in 𝓝 p, u z < min 1 (ε / (M + 1)) :=
      hup_cont.eventually (isOpen_Iio.mem_nhds (by rw [hup]; exact hδ))
    obtain ⟨N₂, hN₂, hN₂sub⟩ := Filter.eventually_iff_exists_mem.mp hev
    obtain ⟨N₃, hN₃sub, hN₃open, hpN₃⟩ := mem_nhds_iff.mp hN₂
    have hN₃u : ∀ z ∈ N₃, u z < min 1 (ε / (M + 1)) := fun z hz => hN₂sub z (hN₃sub hz)
    -- the final neighbourhood: intersect the three
    refine ⟨N₁ ∩ N₃, hN₁open.inter hN₃open, ⟨hpN₁, hpN₃⟩, fun x hxU hxN => ?_⟩
    have hxN₁ : x ∈ N₁ := hxN.1
    have hxN₃ : x ∈ N₃ := hxN.2
    have hxS : x ∈ S := hN₁S ⟨hxU, hxN₁⟩
    have h1 : Submission.limEnvelope U f M x ≤ (M / 1) * clampedBarrier u S 1 x := hcmp x hxU
    have h2 : clampedBarrier u S 1 x < ε / (M + 1) := by
      rw [clampedBarrier_of_mem hxS]
      exact lt_of_le_of_lt (min_le_left _ _) (lt_of_lt_of_le (hN₃u x hxN₃) (min_le_right _ _))
    have h3 : (M / 1) * clampedBarrier u S 1 x < (M / 1) * (ε / (M + 1)) :=
      mul_lt_mul_of_pos_left h2 (by simpa using hMpos)
    have h4 : (M / 1) * (ε / (M + 1)) < ε := by
      rw [div_one]
      have h1 : M * (ε / (M + 1)) = (M * ε) / (M + 1) := by ring
      rw [h1, div_lt_iff₀ (by linarith : (0 : ℝ) < M + 1)]
      nlinarith [hε]
    linarith

/-- **Bouligand's regularity step, in the form used by the region-Perrron construction.**  If `p` is
a frontier point of `Ω` carrying a local barrier, and the boundary data `f` is `≤ 0` on `frontier Ω`,
then the limsup Perron envelope of the region `U` is `< ε` on a neighbourhood of `p` (intersected
with `U`). -/
theorem limEnvelope_lt_near_of_localBarrier {X : Type*} [TopologicalSpace X] [T2Space X]
    [PreconnectedSpace X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} (hΩo : IsOpen Ω) {U : Set X} (hUo : IsOpen U) (hUΩ : U ⊆ Ω)
    (hcomp : IsCompact (closure U)) (hfrU : (frontier U).Nonempty)
    {f : X → ℝ} {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε)
    (hneF : (Submission.limFamily U f M).Nonempty)
    (hf0 : ∀ ζ ∈ frontier Ω, f ζ ≤ 0)
    {p : X} (hp : p ∈ frontier Ω) (hpU : p ∈ closure U)
    (hb : ∃ (u : X → ℝ) (V : Set X), IsOpen V ∧ p ∈ V ∧
      Submission.SuperharmonicOnX u (Ω ∩ V) ∧ (∀ x ∈ Ω ∩ V, 0 < u x) ∧
      ContinuousOn u V ∧ u p = 0 ∧
      (∀ ζ ∈ frontier U, ζ ∉ frontier Ω → ζ ∉ closure V)) :
    ∃ N : Set X, IsOpen N ∧ p ∈ N ∧
      ∀ x ∈ U, x ∈ N → Submission.limEnvelope U f M x < ε := by
  classical
  obtain ⟨u, V, hVo, hpV, hu, hupos, hucont, hup, hVK⟩ := hb
  -- the "far" part of the boundary of `U`: the frontier points outside `V`.  At those the
  -- boundary datum is not controlled, so the Perron envelope has to be estimated there.
  set K : Set X := {ζ : X | ζ ∈ frontier U ∧ ζ ∉ V} with hKdef
  have hKfr : K ⊆ frontier U := fun _ hz => hz.1
  have hKcomp : IsCompact K :=
    hcomp.of_isClosed_subset (isClosed_frontier.inter hVo.isClosed_compl)
      (fun _ hx => frontier_subset_closure hx.1)
  have hpK : p ∉ K := fun h => h.2 hpV
  -- the boundary datum is `≤ 0` at every frontier point of `U` outside `K`
  have hfK : ∀ ζ ∈ frontier U, ζ ∉ K → f ζ ≤ 0 := by
    intro ζ hζU hζK
    have hζV : ζ ∈ V := by
      by_contra hζV
      exact hζK ⟨hζU, hζV⟩
    by_contra hle
    have hζfrΩ : ζ ∈ frontier Ω := by
      by_contra hζfrΩ
      exact hVK ζ hζU hζfrΩ (subset_closure hζV)
    exact absurd (hf0 ζ hζfrΩ) (not_le.mpr (not_le.mp hle))
  -- the comparison of the envelope with the envelope of the indicator of `K`
  have hcmp : ∀ x ∈ U, Submission.limEnvelope U f M x ≤
      M * Submission.limEnvelope U (Set.indicator K (fun _ => (1 : ℝ))) 1 x :=
    limEnvelope_le_smul_farEnvelope hUo hM hneF hKfr hfK
  rcases eq_or_lt_of_le hM with hM0 | hMpos
  · -- `M = 0`: the envelope is nonpositive on `U`
    refine ⟨Set.univ, isOpen_univ, trivial, fun x hxU _ => ?_⟩
    have h1 := hcmp x hxU
    rw [← hM0] at h1 ⊢
    rw [zero_mul] at h1
    linarith
  · -- `M > 0`: intersect with the neighbourhood on which the far envelope is small
    obtain ⟨N₀, hN₀, hN₀sub⟩ :=
      Work.SimplyConnected.ABS.FarLocal.limEnvelope_indicator_far_vanishes hΩo hUo hUΩ hcomp hfrU
        hp hpU hVo hpV hu hupos hucont hup hVK hKfr hKcomp hpK (div_pos hε hMpos)
    obtain ⟨N, hNsub, hNopen, hpN⟩ := mem_nhds_iff.mp hN₀
    refine ⟨N, hNopen, hpN, fun x hxU hxN => ?_⟩
    have h1 := hcmp x hxU
    have h2 : Submission.limEnvelope U (Set.indicator K (fun _ => (1 : ℝ))) 1 x < ε / M :=
      hN₀sub x hxU (hNsub hxN)
    have h3 : M * Submission.limEnvelope U (Set.indicator K (fun _ => (1 : ℝ))) 1 x <
        M * (ε / M) := mul_lt_mul_of_pos_left h2 hMpos
    have h4 : M * (ε / M) = ε := by field_simp
    rw [h4] at h3
    linarith
end Work.SimplyConnected.ABS
