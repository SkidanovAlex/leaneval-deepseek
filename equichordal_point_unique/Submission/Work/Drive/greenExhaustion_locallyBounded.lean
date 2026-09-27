import Mathlib
import Submission.Work.SimplyConnected.ABS.Defs
import Submission.Work.SimplyConnected.ABS.green_reduction.exists_isGreenOn_precompact_superset
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.WeakGreenAt
import Submission.Work.Drive.maxPrincipleTwoPoles
import Submission.Work.Drive.normalizedGreenExhaustion_locallyBounded
import Submission.Commons.Analysis.Complex.Harmonic.annulus_le_boundary

/-!
# The normalised Green functions of an exhaustion are locally bounded off the pole

`Work.Drive.greenExhaustion_locallyBounded`: on a connected, second countable, non-compact Riemann
surface `X` and for points `a ≠ x₁` there is an exhaustion `Ω n` of `X` by nested relatively compact
open sets together with Green functions `G n` of `Ω n` with pole `a`
(`Work.SimplyConnected.ABS.IsGreenOn`, extended by `0` outside `Ω n`), such that for every compact
`K ⊆ X ∖ {a}` the normalised Green functions `G n · - G n x₁` are uniformly bounded on `K`.

`greenExhaustion_data` builds the exhaustion recursively from the compact exhaustion of `X` and the
precompact Green-function regions supplied by
`Work.SimplyConnected.ABS.green_reduction.exists_isGreenOn_precompact_superset`.  The analytic
content is isolated in `Work.Drive.normalizedGreenExhaustion_locallyBounded` (the classical local
boundedness of the normalised Green functions of an exhaustion, for an *arbitrary* exhaustion).
-/

open Filter Set Classical
open scoped Topology Manifold ContDiff

noncomputable section

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ### Two elementary transports -/

/-- **Chart-local congruence of harmonicity.**  If `u` and `v` agree in a neighbourhood of `x`, then
harmonicity of `u` at `x` transfers to `v`. -/
theorem harmonicOnXAt_of_eventuallyEq {u v : X → ℝ} {x : X} (h : v =ᶠ[𝓝 x] u)
    (hu : Submission.HarmonicOnXAt u x) : Submission.HarmonicOnXAt v x := by
  rw [Submission.HarmonicOnXAt] at hu ⊢
  have h1 : v ∘ (chartAt ℂ x).symm =ᶠ[𝓝 ((chartAt ℂ x) x)] u ∘ (chartAt ℂ x).symm := by
    have hsame : 𝓝 ((chartAt ℂ x).symm ((chartAt ℂ x) x)) = 𝓝 x := by
      rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
    have hc : Tendsto (chartAt ℂ x).symm (𝓝 ((chartAt ℂ x) x))
        (𝓝 ((chartAt ℂ x).symm ((chartAt ℂ x) x))) :=
      (chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
    rw [hsame] at hc
    filter_upwards [hc.eventually h] with z hz
    simpa [Function.comp_def] using hz
  exact (InnerProductSpace.harmonicAt_congr_nhds h1).mpr hu

/-- The `0`-extension of a Green function is a Green function. -/
theorem IsGreenOn.zeroExtension {Ω : Set X} (hΩo : IsOpen Ω) {a : X} {E : X → ℝ}
    (hE : Work.SimplyConnected.ABS.IsGreenOn Ω a E) :
    Work.SimplyConnected.ABS.IsGreenOn Ω a (fun x => if x ∈ Ω then E x else 0) := by
  set E' : X → ℝ := fun x => if x ∈ Ω then E x else 0 with hE'def
  have hagg : ∀ x ∈ Ω, E' x = E x := fun x hx => dif_pos hx
  have heq : ∀ x ∈ Ω, E' =ᶠ[𝓝 x] E := by
    intro x hx
    filter_upwards [hΩo.mem_nhds hx] with y hy
    exact dif_pos hy
  obtain ⟨hpos, hharm, hdecay, hpole⟩ := hE
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hxne
    rw [hagg x hx]
    exact hpos x hx hxne
  · intro x hx
    exact harmonicOnXAt_of_eventuallyEq (heq x hx.1) (hharm x hx)
  · intro ε hε
    obtain ⟨K, hK, hKΩ, hlt⟩ := hdecay ε hε
    exact ⟨K, hK, hKΩ, fun x hxΩ hxK => by rw [hagg x hxΩ]; exact hlt x hxΩ hxK⟩
  · obtain ⟨C, V, hV, hCV⟩ := hpole
    exact ⟨C, V, hV, fun x hxV hxΩ hxne => by
      rw [hagg x hxΩ]; exact hCV x hxV hxΩ hxne⟩

/-! ### The exhaustion -/

/-- **One step of the construction of the exhaustion**: a precompact connected open set together with
a Green function with pole `a` on it. -/
structure GreenDatum (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] (a : X) where
  Ω : Set X
  G : X → ℝ
  isOpen_Ω : IsOpen Ω
  isConnected_Ω : IsConnected Ω
  isCompact_closure : IsCompact (closure Ω)
  isGreen : Work.SimplyConnected.ABS.IsGreenOn Ω a G

/-- **The one-step extension**: every compact set is contained in a Green datum's region. -/
theorem exists_greenDatum_superset (hX : ¬ CompactSpace X) (a : X) {K : Set X} (hK : IsCompact K) :
    ∃ D : GreenDatum X a, K ⊆ D.Ω := by
  obtain ⟨Ω, hΩo, hΩc, hΩcomp, hKΩ, _haΩ, E, hE⟩ :=
    Work.SimplyConnected.ABS.green_reduction.exists_isGreenOn_precompact_superset (X := X) hX hK a
  exact ⟨⟨Ω, E, hΩo, hΩc, hΩcomp, hE⟩, hKΩ⟩

/-- **The exhaustion with its Green functions.**  There is a nested exhaustion `Ω n` of `X` by
relatively compact open sets containing `a` and `x₁`, and Green functions `G n` of `Ω n` with pole
`a`, vanishing outside `Ω n`. -/
theorem greenExhaustion_data (hX : ¬ CompactSpace X) (a x₁ : X) :
    ∃ (Ω : ℕ → Set X) (G : ℕ → X → ℝ),
      (∀ n, IsOpen (Ω n)) ∧ (∀ n, IsCompact (closure (Ω n))) ∧
      (∀ n, Ω n ⊆ Ω (n + 1)) ∧ (⋃ n, Ω n) = Set.univ ∧
      (∀ n, a ∈ Ω n) ∧ (∀ n, x₁ ∈ Ω n) ∧
      (∀ n, Work.SimplyConnected.ABS.IsGreenOn (Ω n) a (G n)) ∧
      (∀ n, ∀ x, x ∉ Ω n → G n x = 0) := by
  classical
  haveI : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  haveI : SigmaCompactSpace X := sigmaCompactSpace_of_locallyCompact_secondCountable
  obtain ⟨Kex⟩ : Nonempty (CompactExhaustion X) := inferInstance
  have hKex1 : IsCompact ({a, x₁} : Set X) := by
    rw [Set.pair_comm]
    exact (isCompact_singleton (x := a)).insert x₁
  have hstep : ∀ (n : ℕ) (D : GreenDatum X a),
      ∃ D' : GreenDatum X a, closure D.Ω ∪ Kex (n + 1) ∪ {a, x₁} ⊆ D'.Ω := fun n D =>
    exists_greenDatum_superset (X := X) hX a
      ((D.isCompact_closure.union (Kex.isCompact (n + 1))).union hKex1)
  let step : ℕ → GreenDatum X a → GreenDatum X a := fun n D => Classical.choose (hstep n D)
  have step_spec : ∀ (n : ℕ) (D : GreenDatum X a),
      closure D.Ω ∪ Kex (n + 1) ∪ {a, x₁} ⊆ (step n D).Ω :=
    fun n D => Classical.choose_spec (hstep n D)
  obtain ⟨init, hinit⟩ : ∃ D : GreenDatum X a, Kex 0 ∪ {a, x₁} ⊆ D.Ω :=
    exists_greenDatum_superset (X := X) hX a ((Kex.isCompact 0).union hKex1)
  let D : ℕ → GreenDatum X a := fun n => Nat.rec init (fun k ih => step k ih) n
  have hD : ∀ n : ℕ, D (n + 1) = step n (D n) := by
    intro n
    change Nat.rec init (fun k ih => step k ih) (Nat.succ n) =
      step n (Nat.rec init (fun k ih => step k ih) n)
    rfl
  have ha : ∀ n, a ∈ (D n).Ω := fun n =>
    Nat.rec (hinit (Or.inr (by simp : a ∈ ({a, x₁} : Set X)))) (fun k _ => by
      have h2 := step_spec k (D k) (Or.inr (by simp : a ∈ ({a, x₁} : Set X)))
      rw [← hD k] at h2
      exact h2) n
  have hx : ∀ n, x₁ ∈ (D n).Ω := fun n =>
    Nat.rec (hinit (Or.inr (by simp : x₁ ∈ ({a, x₁} : Set X)))) (fun k _ => by
      have h2 := step_spec k (D k) (Or.inr (by simp : x₁ ∈ ({a, x₁} : Set X)))
      rw [← hD k] at h2
      exact h2) n
  have hnest : ∀ n, (D n).Ω ⊆ (D (n + 1)).Ω := by
    intro n x hx'
    have h2 := step_spec n (D n) (Or.inl (Or.inl (subset_closure hx')))
    rw [← hD n] at h2
    exact h2
  refine ⟨fun n => (D n).Ω, fun n => fun x => if x ∈ (D n).Ω then (D n).G x else 0,
    fun n => (D n).isOpen_Ω, fun n => (D n).isCompact_closure, hnest, ?_, ha, hx, ?_, ?_⟩
  · -- the pieces cover `X`
    refine Set.eq_univ_iff_forall.mpr fun x => ?_
    obtain ⟨r, hr⟩ := Kex.exists_mem x
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · subst h0
      have h1 : Kex 0 ⊆ Kex 1 := (Kex.subset_interior_succ 0).trans interior_subset
      have h2 := step_spec 0 init (Or.inl (Or.inr (h1 hr)))
      rw [← hD 0] at h2
      exact Set.mem_iUnion.mpr ⟨1, h2⟩
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have h2 := step_spec k (D k) (Or.inl (Or.inr hr))
      rw [← hD k] at h2
      exact Set.mem_iUnion.mpr ⟨k + 1, h2⟩
  · intro n
    exact IsGreenOn.zeroExtension (D n).isOpen_Ω (D n).isGreen
  · intro n x hx'
    simp only [hx', ↓reduceIte]

/-! ### The comparison with a weak Green function -/

/-- The frontier of a proper open subset of a preconnected space is nonempty. -/
theorem frontier_nonempty_of_ne_univ [PreconnectedSpace X] {U : Set X} (hU : U ≠ Set.univ)
    (hne : U.Nonempty) : (frontier U).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro h
  rcases (frontier_eq_empty_iff.mp h) with h0 | h0
  · exact hne.ne_empty h0
  · exact hU h0

/-- **Comparison of a Green function with a weak Green function with the same pole.**  If `E` is a
strictly positive harmonic function on `X \ {a}` with a unit logarithmic pole at `a`, then the Green
function of any precompact region `Ω ∋ a` is dominated by `E`. -/
theorem le_of_weakGreen {Ω : Set X} (hΩo : IsOpen Ω) (hΩcomp : IsCompact (closure Ω))
    (hΩne : Ω ≠ Set.univ) {a : X} (ha : a ∈ Ω) {G E : X → ℝ}
    (hG : Work.SimplyConnected.ABS.IsGreenOn Ω a G)
    (hEpos : ∀ x, x ≠ a → 0 < E x) (hEharm : Submission.HarmonicOnX E (Set.univ \ {a}))
    (hEpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {a}) a E) :
    ∀ x ∈ Ω, x ≠ a → G x ≤ E x := by
  classical
  have hfront : (frontier Ω).Nonempty := frontier_nonempty_of_ne_univ hΩne ⟨a, ha⟩
  have hv : Submission.HarmonicOnX (fun z => G z - E z) (Ω \ {a}) := by
    intro z hz
    have hzne : z ≠ a := by simpa using hz.2
    rw [Submission.HarmonicOnXAt]
    have h1 : InnerProductSpace.HarmonicAt (G ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z) := hG.2.1 z hz
    have h2 : InnerProductSpace.HarmonicAt (E ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z) :=
      hEharm z ⟨Set.mem_univ z, hzne⟩
    have h3 := h1.sub h2
    have h4 : (((fun z => G z - E z)) ∘ (chartAt ℂ z).symm)
        = ((G ∘ (chartAt ℂ z).symm) - (E ∘ (chartAt ℂ z).symm)) := rfl
    rw [h4]
    exact h3
  have hbda : ∃ C : ℝ, ∀ᶠ z in 𝓝[Ω \ {a}] a, |G z - E z| ≤ C := by
    obtain ⟨C₁, V₁, hV₁, h₁⟩ := hG.2.2.2
    obtain ⟨C₂, V₂, hV₂, h₂⟩ := hEpole
    refine ⟨C₁ + C₂, ?_⟩
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hV₁, hV₂] with z hz₁ hz₂ hzmem
    have hzΩ : z ∈ Ω := hzmem.1
    have hzne : z ≠ a := by simpa using hzmem.2
    set L : ℝ := Real.log ‖(chartAt ℂ a) z - (chartAt ℂ a) a‖ with hL
    have hb₁ : |G z + L| ≤ C₁ := h₁ z hz₁ hzΩ hzne
    have hb₂ : |E z + L| ≤ C₂ := h₂ z hz₂ ⟨Set.mem_univ z, hzne⟩ hzne
    have hEq : G z - E z = (G z + L) - (E z + L) := by ring
    rw [hEq]
    exact abs_sub_le_iff.mpr ⟨by linarith [(abs_le.mp hb₁).2, (abs_le.mp hb₂).1],
      by linarith [(abs_le.mp hb₂).2, (abs_le.mp hb₁).1]⟩
  have hlim : ∀ ξ ∈ frontier Ω, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in 𝓝[Ω] ξ, (fun z => G z - E z) z ≤ 0 + ε := by
    intro ξ hξ ε hε
    obtain ⟨K, hK, hKΩ, hdec⟩ := hG.2.2.1 (ε / 2) (by linarith)
    have hξK : ξ ∉ K := fun h => hξ.2 (by rw [hΩo.interior_eq]; exact hKΩ h)
    have hKc : ∀ᶠ z in 𝓝 ξ, z ∉ K := hK.isClosed.isOpen_compl.mem_nhds hξK
    have hξa : ξ ≠ a := fun h => hξ.2 (by rw [hΩo.interior_eq, h]; exact ha)
    have hac : ∀ᶠ z in 𝓝 ξ, z ≠ a := isOpen_compl_singleton.mem_nhds (by simpa using hξa)
    filter_upwards [hKc.filter_mono nhdsWithin_le_nhds, hac.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hzK hza hzΩ
    have hzG : G z < ε / 2 := hdec z hzΩ hzK
    have hzne : z ≠ a := hza
    have hzE : 0 ≤ E z := (hEpos z hzne).le
    linarith
  intro x hx hxne
  have h := maxPrincipleTwoPoles (b := a) hΩo ha ha (by simpa using hv) hbda hbda
    hΩcomp hfront hlim
  linarith [h x hx hxne hxne]

/-! ### The case in which a weak Green function exists at the pole -/

/-- **The target, in the case in which a weak Green function exists at `a`.**  Then every Green
function of the exhaustion is dominated by `E` (maximum principle, `le_of_weakGreen`), which gives
`|G n x - G n x₁| ≤ max (sup_K E) (E x₁)`. -/
theorem greenExhaustion_locallyBounded_of_weakGreen (hX : ¬ CompactSpace X) (a x₁ : X)
    (hx₁ : x₁ ≠ a) (h : WeakGreenAt X a) :
    ∃ (Ω : ℕ → Set X) (G : ℕ → X → ℝ),
      (∀ n, IsOpen (Ω n)) ∧ (∀ n, IsCompact (closure (Ω n))) ∧
      (∀ n, Ω n ⊆ Ω (n + 1)) ∧ (⋃ n, Ω n) = Set.univ ∧
      (∀ n, a ∈ Ω n) ∧ (∀ n, x₁ ∈ Ω n) ∧
      (∀ n, Work.SimplyConnected.ABS.IsGreenOn (Ω n) a (G n)) ∧
      (∀ n, ∀ x, x ∉ Ω n → G n x = 0) ∧
      (∀ K : Set X, IsCompact K → K ⊆ Set.univ \ {a} → ∃ C : ℝ, ∀ n, ∀ x ∈ K,
        |G n x - G n x₁| ≤ C) := by
  obtain ⟨Ω, G, h1, h2, h3, h4, h5, h6, h7, h8⟩ := greenExhaustion_data (X := X) hX a x₁
  obtain ⟨E, hEpos, hEharm, hEpole⟩ := h
  have hΩne : ∀ n, Ω n ≠ Set.univ := by
    intro n hn
    refine hX ?_
    rw [← isCompact_univ_iff]
    have h2n : IsCompact (closure (Ω n)) := h2 n
    rwa [hn, closure_univ] at h2n
  refine ⟨Ω, G, h1, h2, h3, h4, h5, h6, h7, h8, ?_⟩
  intro K hK hKsub
  obtain ⟨C₁, hC₁⟩ : ∃ C : ℝ, ∀ x ∈ K, E x ≤ C := by
    by_cases hKne : K.Nonempty
    · have hcont : ContinuousOn E K := fun x hx =>
        (hEharm x ⟨Set.mem_univ x, (hKsub hx).2⟩).continuousAt.continuousWithinAt
      obtain ⟨x₀, _, hmax⟩ := hK.exists_isMaxOn hKne hcont
      exact ⟨E x₀, fun x hx => hmax hx⟩
    · exact ⟨0, fun x hx => absurd ⟨x, hx⟩ hKne⟩
  refine ⟨max C₁ (E x₁), ?_⟩
  intro n x hx
  have hxne : x ≠ a := (hKsub hx).2
  have hGx : G n x ≤ E x := by
    by_cases hxΩ : x ∈ Ω n
    · exact le_of_weakGreen (h1 n) (h2 n) (hΩne n) (h5 n) (h7 n) hEpos hEharm hEpole x hxΩ hxne
    · rw [h8 n x hxΩ]; exact (hEpos x hxne).le
  have hGx' : 0 ≤ G n x := by
    by_cases hxΩ : x ∈ Ω n
    · exact ((h7 n).1 x hxΩ hxne).le
    · rw [h8 n x hxΩ]
  have hGx₁ : G n x₁ ≤ E x₁ := by
    by_cases hxΩ : x₁ ∈ Ω n
    · exact le_of_weakGreen (h1 n) (h2 n) (hΩne n) (h5 n) (h7 n) hEpos hEharm hEpole x₁ hxΩ hx₁
    · rw [h8 n x₁ hxΩ]; exact (hEpos x₁ hx₁).le
  have hGx₁' : 0 ≤ G n x₁ := by
    by_cases hxΩ : x₁ ∈ Ω n
    · exact ((h7 n).1 x₁ hxΩ hx₁).le
    · rw [h8 n x₁ hxΩ]
  rw [abs_le]
  constructor
  · linarith [le_max_right C₁ (E x₁), hGx₁, hGx']
  · linarith [le_max_left C₁ (E x₁), hC₁ x hx, hGx, hGx₁']


/-! ### The target -/

/-- **The normalized Green functions of an exhaustion are locally bounded off the pole.** On a
connected, second countable, non-compact Riemann surface `X` and for points `a ≠ x₁` of `X` there is
an exhaustion `Ω : ℕ → Set X` by nested relatively compact open sets covering `X`, together with
Green functions `G n` of `Ω n` with pole `a` (in the sense of `Work.SimplyConnected.ABS.IsGreenOn`,
extended by `0` outside `Ω n`), such that for every compact `K ⊆ X ∖ {a}` the *normalized* Green
functions `G n · - G n x₁` are uniformly bounded on `K`. -/
theorem greenExhaustion_locallyBounded {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (a x₁ : X) (hx₁ : x₁ ≠ a) :
    ∃ (Ω : ℕ → Set X) (G : ℕ → X → ℝ),
      (∀ n, IsOpen (Ω n)) ∧ (∀ n, IsCompact (closure (Ω n))) ∧
      (∀ n, Ω n ⊆ Ω (n + 1)) ∧ (⋃ n, Ω n) = Set.univ ∧
      (∀ n, a ∈ Ω n) ∧ (∀ n, x₁ ∈ Ω n) ∧
      (∀ n, Work.SimplyConnected.ABS.IsGreenOn (Ω n) a (G n)) ∧
      (∀ n, ∀ x, x ∉ Ω n → G n x = 0) ∧
      (∀ K : Set X, IsCompact K → K ⊆ Set.univ \ {a} → ∃ C : ℝ, ∀ n, ∀ x ∈ K,
        |G n x - G n x₁| ≤ C) := by
  obtain ⟨Ω, G, h1, h2, h3, h4, h5, h6, h7, h8⟩ := greenExhaustion_data (X := X) hX a x₁
  exact ⟨Ω, G, h1, h2, h3, h4, h5, h6, h7, h8,
    normalizedGreenExhaustion_locallyBounded (X := X) (a := a) (x₁ := x₁) hx₁
      h1 h2 h3 h4 h7 h8⟩


end Work.Drive
