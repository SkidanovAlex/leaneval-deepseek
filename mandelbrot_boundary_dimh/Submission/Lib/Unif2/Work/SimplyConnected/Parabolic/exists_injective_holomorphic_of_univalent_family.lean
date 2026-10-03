import Mathlib
import Submission.Lib.Unif2.Work.Parabolic.Basic
import Submission.Lib.Unif2.Commons.Analysis.Complex.ChartedSpace.isClopen_setOf_eventuallyConst
import Submission.Lib.Unif2.Work.Parabolic.Montel.exists_subseq_tendstoLocallyUniformlyOn_of_eventually_analytic
import Submission.Lib.Unif2.Work.Parabolic.Hurwitz.injOn_of_locallyUniformLimit_open_of_eventually

/-!
# Existence of a global injective holomorphic function from a univalent family

Let `X` be a connected Riemann surface, `x₀ ∈ X`, `Ω : ℕ → Set X` an increasing sequence of open
sets covering `X` with `x₀ ∈ Ω n` for all `n`, and `ψ : ℕ → X → ℂ` a family of functions which are
holomorphic on `Ω n`, injective on `Ω n`, normalised by `ψ n x₀ = 0` and by the chart derivative
`deriv (ψ n ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 1`, and which is uniformly bounded on the
compact subsets of `X`.

Then there is a *global* injective holomorphic `g : X → ℂ` with `g x₀ = 0` and chart derivative `1`
at `x₀`.  This is the classical "normal family" step of the uniformization argument: Montel's
theorem produces a locally uniformly convergent subsequence, whose limit is holomorphic; Hurwitz's
theorem makes the limit injective (the constant alternative is excluded by the normalisation
`g' x₀ = 1`), and Weierstrass' theorem transfers the derivative normalisation to the limit.

The two analytic inputs are proved in the companion modules
`Submission.Work.Parabolic.Montel.exists_subseq_tendstoLocallyUniformlyOn_of_eventually_analytic`
and `Submission.Work.Parabolic.Hurwitz.injOn_of_locallyUniformLimit_open_of_eventually`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Work.SimplyConnected.Parabolic

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## Auxiliary lemmas -/

/-- A holomorphic function on a connected Riemann surface whose chart derivative at `x₀` does not
vanish is nowhere locally constant. -/
theorem not_eventually_eq_nhds_of_deriv_ne_zero {x₀ : X} {g : X → ℂ}
    (hg : Submission.HolomorphicOnX g Set.univ)
    (hder : deriv (g ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) ≠ 0) :
    ∀ x : X, ¬ Filter.Eventually (fun y => g y = g x) (nhds x) := by
  have hcl : IsClopen {x : X | Filter.Eventually (fun y => g y = g x) (nhds x)} :=
    Commons.Analysis.Complex.ChartedSpace.isClopen_setOf_eventuallyConst
      (fun x => hg x (mem_univ x))
  have hx₀ : x₀ ∉ {x : X | Filter.Eventually (fun y => g y = g x) (nhds x)} := by
    intro hconmem
    have hcon : ∀ᶠ y in nhds x₀, g y = g x₀ := hconmem
    apply hder
    have hmem : (chartAt ℂ x₀) x₀ ∈ (chartAt ℂ x₀).target :=
      (chartAt ℂ x₀).map_source (mem_chart_source ℂ x₀)
    have hev : (g ∘ (chartAt ℂ x₀).symm) =ᶠ[nhds ((chartAt ℂ x₀) x₀)] fun _ => g x₀ := by
      have hsymm : (chartAt ℂ x₀).symm ((chartAt ℂ x₀) x₀) = x₀ :=
        (chartAt ℂ x₀).left_inv (mem_chart_source ℂ x₀)
      have hcont : Tendsto (chartAt ℂ x₀).symm (nhds ((chartAt ℂ x₀) x₀))
          (nhds ((chartAt ℂ x₀).symm ((chartAt ℂ x₀) x₀))) :=
        (chartAt ℂ x₀).continuousAt_symm hmem
      rw [hsymm] at hcont
      have h1 : ∀ᶠ z in nhds ((chartAt ℂ x₀) x₀), g ((chartAt ℂ x₀).symm z) = g x₀ :=
        hcont.eventually hcon
      filter_upwards [h1] with z hz using hz
    rw [Filter.EventuallyEq.deriv_eq hev, deriv_const]
  have hempty : {x : X | Filter.Eventually (fun y => g y = g x) (nhds x)} = ∅ := by
    rcases isClopen_iff.mp hcl with h | h
    · exact h
    · exact absurd (by rw [h]; exact mem_univ x₀) hx₀
  intro x hx
  have hxmem : x ∈ {x : X | Filter.Eventually (fun y => g y = g x) (nhds x)} := hx
  rw [hempty] at hxmem
  exact hxmem

/-- **Chart ball of analyticity for an exhaustion.**  If `x ∈ Ω N` and every `ψ n` is holomorphic on
`Ω n`, then there is a chart ball around `x` on which `ψ n` is analytic (in the chart at `x`) for
every `n ≥ N`. -/
theorem exists_chartBall_analytic_of_mem {ψ : ℕ → X → ℂ} {Ω : ℕ → Set X}
    (hΩo : ∀ n, IsOpen (Ω n)) (hmono : ∀ n m, n ≤ m → Ω n ⊆ Ω m)
    (hhol : ∀ n, ∀ y ∈ Ω n, Submission.HolomorphicOnXAt (ψ n) y)
    {x : X} {N : ℕ} (hxN : x ∈ Ω N) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target ∧
      ∀ n, N ≤ n → ∀ z ∈ Metric.ball ((chartAt ℂ x) x) ρ,
        AnalyticAt ℂ (ψ n ∘ (chartAt ℂ x).symm) z := by
  set e := chartAt ℂ x with he
  have hxsrc : x ∈ e.source := mem_chart_source ℂ x
  have hUopen : IsOpen (Ω N ∩ e.source) := (hΩo N).inter e.open_source
  have himg_open : IsOpen (e '' (Ω N ∩ e.source)) :=
    e.isOpen_image_of_subset_source hUopen inter_subset_right
  have hmem_img : e x ∈ e '' (Ω N ∩ e.source) := ⟨x, ⟨hxN, hxsrc⟩, rfl⟩
  obtain ⟨ρ, hρ, hρsub⟩ :=
    Metric.isOpen_iff.mp (himg_open.inter e.open_target) (e x) ⟨hmem_img, e.map_source hxsrc⟩
  refine ⟨ρ, hρ, (fun z hz => (hρsub hz).2), fun n hn z hz => ?_⟩
  have hz' : z ∈ e '' (Ω N ∩ e.source) := (hρsub hz).1
  obtain ⟨w, hw, hwz⟩ := hz'
  have hwsrc : w ∈ e.source := hw.2
  have hsymm : e.symm z = w := by rw [← hwz, e.left_inv hwsrc]
  have hzin : e.symm z ∈ Ω n := by rw [hsymm]; exact hmono N n hn hw.1
  have h1 : Submission.HolomorphicOnXAt (ψ n) (e.symm z) := hhol n (e.symm z) hzin
  have hxsrc' : e.symm z ∈ (chartAt ℂ x).source := by rw [he]; exact e.map_target (hρsub hz).2
  have h2 := (Submission.HolomorphicOnXAt_iff_chart (f := ψ n) hxsrc').mp h1
  have h3 : (chartAt ℂ x) (e.symm z) = z := by rw [← he]; exact e.right_inv (hρsub hz).2
  show AnalyticAt ℂ (ψ n ∘ (chartAt ℂ x).symm) z
  rw [← h3]
  exact h2

/-- **Eventual analyticity on a chart ball.**  Around every point of `X` there is a chart ball on
which the family `ψ` is eventually analytic (in the chart at that point). -/
theorem exists_chartBall_eventually_analyticAt {ψ : ℕ → X → ℂ} {Ω : ℕ → Set X}
    (hΩo : ∀ n, IsOpen (Ω n)) (hmono : ∀ n m, n ≤ m → Ω n ⊆ Ω m)
    (hΩcov : ⋃ n, Ω n = Set.univ)
    (hhol : ∀ n, ∀ y ∈ Ω n, Submission.HolomorphicOnXAt (ψ n) y) (x : X) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target ∧
      ∀ᶠ n in Filter.atTop, ∀ z ∈ Metric.ball ((chartAt ℂ x) x) ρ,
        AnalyticAt ℂ (ψ n ∘ (chartAt ℂ x).symm) z := by
  have hmemN : ∃ N, x ∈ Ω N := by
    have : x ∈ ⋃ n, Ω n := by rw [hΩcov]; exact mem_univ x
    simpa only [mem_iUnion] using this
  obtain ⟨N, hxN⟩ := hmemN
  obtain ⟨ρ, hρ, hsub, hana⟩ := exists_chartBall_analytic_of_mem hΩo hmono hhol hxN
  exact ⟨ρ, hρ, hsub, Filter.eventually_atTop.mpr ⟨N, fun n hn z hz => hana n hn z hz⟩⟩

/-- **Weierstrass transfer of the derivative normalisation.**  If the members of a sequence `F` are
analytic in the chart at `x₀` on an open neighbourhood `V` of the chart image of `x₀`, all with
chart derivative `1` there, and `F` converges locally uniformly on `X` to `g`, then the limit has
chart derivative `1` at `x₀`. -/
theorem deriv_eq_one_of_tendstoLocallyUniformlyOn {F : ℕ → X → ℂ} {g : X → ℂ} {x₀ : X}
    {V : Set ℂ} (hV : IsOpen V) (hc₀ : (chartAt ℂ x₀) x₀ ∈ V)
    (hVsub : V ⊆ (chartAt ℂ x₀).target)
    (hconv : TendstoLocallyUniformlyOn F g Filter.atTop Set.univ)
    (hdiff : ∀ᶠ n in Filter.atTop, DifferentiableOn ℂ (fun z => F n ((chartAt ℂ x₀).symm z)) V)
    (hder : ∀ n, deriv (F n ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 1) :
    deriv (g ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 1 := by
  set e := chartAt ℂ x₀ with he
  have hclose : TendstoLocallyUniformlyOn (fun n => F n ∘ e.symm) (g ∘ e.symm) atTop e.target :=
    hconv.comp e.symm (mapsTo_univ _ _) e.continuousOn_symm
  have hclose' : TendstoLocallyUniformlyOn (fun n => F n ∘ e.symm) (g ∘ e.symm) atTop V :=
    hclose.mono hVsub
  have hderconv := hclose'.deriv (F := fun n => F n ∘ e.symm) hdiff hV
  have hlim := hderconv.tendsto_at hc₀
  simp only [Function.comp_apply] at hlim
  have hconst : (fun n => deriv (F n ∘ e.symm) (e x₀)) = fun _ => (1 : ℂ) :=
    funext fun n => hder n
  rw [hconst] at hlim
  exact tendsto_nhds_unique hlim (tendsto_const_nhds (f := atTop) (x := (1 : ℂ)))

/-! ## The main theorem -/

theorem exists_injective_holomorphic_of_univalent_family {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {x₀ : X}
    {Ω : ℕ → Set X} (hΩo : ∀ n, IsOpen (Ω n)) (hΩm : ∀ n, Ω n ⊆ Ω (n + 1))
    (hΩcov : ⋃ n, Ω n = Set.univ) (hx : ∀ n, x₀ ∈ Ω n)
    {ψ : ℕ → X → ℂ}
    (hhol : ∀ n, ∀ x ∈ Ω n, Submission.HolomorphicOnXAt (ψ n) x)
    (hinj : ∀ n, Set.InjOn (ψ n) (Ω n)) (h0 : ∀ n, ψ n x₀ = 0)
    (hder : ∀ n, deriv (ψ n ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 1)
    (hlocbnd : ∀ (U : Set X), IsOpen U → IsConnected U → x₀ ∈ U → ∀ K : Set X, IsCompact K →
      K ⊆ U → ∃ B : ℝ, ∀ n, ∀ x ∈ K, ‖ψ n x‖ ≤ B) :
    ∃ g : X → ℂ, Submission.HolomorphicOnX g Set.univ ∧ Function.Injective g ∧ g x₀ = 0 ∧
      deriv (g ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 1 := by
  haveI : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  -- monotonicity of the exhaustion
  have hmono : ∀ n m, n ≤ m → Ω n ⊆ Ω m := monotone_nat_of_le_succ hΩm
  -- every point of `X` lies in some member of the exhaustion
  have hmem : ∀ x : X, ∃ N, x ∈ Ω N := fun x => by
    have : x ∈ ⋃ n, Ω n := by rw [hΩcov]; exact mem_univ x
    simpa only [mem_iUnion] using this
  -- uniform boundedness on compact subsets of `X`
  have hbnd : ∀ K : Set X, IsCompact K → ∃ B : ℝ, ∀ᶠ n in Filter.atTop, ∀ x ∈ K, ‖ψ n x‖ ≤ B :=
    fun K hK => by
      obtain ⟨B, hB⟩ := hlocbnd Set.univ isOpen_univ isConnected_univ (mem_univ x₀) K hK
        (subset_univ K)
      exact ⟨B, Eventually.of_forall hB⟩
  -- chart balls of eventual analyticity
  have hball : ∀ x : X, ∃ ρ : ℝ, 0 < ρ ∧
      Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target ∧
      ∀ᶠ n in Filter.atTop, ∀ z ∈ Metric.ball ((chartAt ℂ x) x) ρ,
        AnalyticAt ℂ (ψ n ∘ (chartAt ℂ x).symm) z :=
    fun x => exists_chartBall_eventually_analyticAt hΩo hmono hΩcov hhol x
  -- Montel: extract a locally uniformly convergent subsequence
  obtain ⟨φ, g, hφ, hconv, hgan⟩ :=
    Work.Parabolic.Montel.exists_subseq_tendstoLocallyUniformlyOn_of_eventually_analytic
      (F := ψ) hbnd hball
  have hghol : Submission.HolomorphicOnX g Set.univ := fun x _ => hgan x
  -- the limit vanishes at `x₀`
  have hg0 : g x₀ = 0 := by
    have h1 : Tendsto (fun n => ψ (φ n) x₀) atTop (nhds (g x₀)) := hconv.tendsto_at (mem_univ x₀)
    have h2 : Tendsto (fun n => ψ (φ n) x₀) atTop (nhds 0) := by
      simpa [h0] using tendsto_const_nhds (f := atTop) (x := (0 : ℂ))
    exact tendsto_nhds_unique h1 h2
  -- the chart derivative at `x₀` is inherited by the limit
  have hderg : deriv (g ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 1 := by
    obtain ⟨ρ₀, hρ₀, hsub₀, hana₀⟩ :=
      exists_chartBall_analytic_of_mem hΩo hmono hhol (hx 0)
    refine deriv_eq_one_of_tendstoLocallyUniformlyOn Metric.isOpen_ball
      (Metric.mem_ball_self hρ₀) hsub₀ hconv ?_ (fun n => hder (φ n))
    exact Eventually.of_forall fun n z hz =>
      (hana₀ (φ n) (Nat.zero_le _) z hz).differentiableAt.differentiableWithinAt
  -- the limit is nowhere locally constant
  have hloc : ∀ x : X, ¬ Filter.Eventually (fun y => g y = g x) (nhds x) :=
    not_eventually_eq_nhds_of_deriv_ne_zero hghol (by rw [hderg]; exact one_ne_zero)
  refine ⟨g, hghol, ?_, hg0, hderg⟩
  -- injectivity, by Hurwitz on the exhaustion
  intro a b hab
  obtain ⟨Na, haN⟩ := hmem a
  obtain ⟨Nb, hbN⟩ := hmem b
  set N : ℕ := max Na Nb with hN
  have ha : a ∈ Ω N := hmono Na N (le_max_left _ _) haN
  have hb : b ∈ Ω N := hmono Nb N (le_max_right _ _) hbN
  have hIN : Set.InjOn g (Ω N) := by
    refine Work.Parabolic.Hurwitz.injOn_of_locallyUniformLimit_open_of_eventually (hΩo N) ?_
      (fun x => hgan x) hconv ?_
      (fun x _ => hloc x)
    · refine Filter.eventually_atTop.mpr ⟨N, fun n hn x hxΩ => ?_⟩
      exact hhol (φ n) x (hmono N (φ n) (le_trans hn (hφ.id_le n)) hxΩ)
    · refine Filter.eventually_atTop.mpr ⟨N, fun n hn x hx y hy hxy => ?_⟩
      exact hinj (φ n) (hmono N (φ n) (le_trans hn (hφ.id_le n)) hx)
        (hmono N (φ n) (le_trans hn (hφ.id_le n)) hy) hxy
  exact hIN ha hb hab

end Work.SimplyConnected.Parabolic
