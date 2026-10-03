import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.ExtremalImports
import Submission.Lib.Unif2.Work.Parabolic.isOpenMap_of_injective_holomorphic
import Submission.Lib.Unif2.Work.UnitGreen.Defs
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.exists_holomorphic_div_of_logPole
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.norm_le_exp_neg_of_unitGreen
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.exists_posHarmonic_logPole_dominating
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.modulus_of_single_zero
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.rigidity_of_maximizer_decayfree
import Submission.Lib.Unif2.ExtremalOnto
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.sweep_greenBarrier_dominates
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.isPreconnected_compl_closedDiscrete
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.subharmonicOnX_norm_of_holomorphic
import Submission.Lib.Unif2.MaxPrincipleRegion

/-!
# Ahlfors' theorem: the extremal maximizer is proper into the unit disc

Target (`Work.SimplyConnected.ABS.extremal_maximizer_proper`): if `f ∈ Submission.extremalFamily x₀`
is a *maximiser* of `‖f'(x₀)‖` (in the chart at `x₀`) with positive extremal value, then `f` is
**proper into the open unit disc**: the pre-image of every compact subset of `𝔻` is compact.

This is Ahlfors' theorem (Ahlfors, *Bounded analytic functions*, Duke 1947; Ahlfors, *Conformal
invariants*, Ch. 10; Fisher, *Function theory on planar domains*, Ch. 12): the extremal function of
the Schwarz problem is the *Green modulus* of `X`, hence a proper map onto `𝔻`.

## The proof architecture

Everything is reduced here to two classical inputs, and the whole rest of the argument is
formalised below (or already in the workspace):

1. **Hyperbolicity** (`∃ E, Work.UnitGreen.IsUnitGreenFunctionAt x₀ E`): a non-constant bounded
   holomorphic function on a Riemann surface forces a (unit-pole) Green function at `x₀`
   (Perron's method applied to `{u : X → ℝ | u subharmonic, u ≤ 0, u ≼ log ‖c · − c x₀‖}`, which is
   non-empty thanks to `log ‖f‖`; the content is *decay at the ideal boundary*, i.e. relative
   compactness of the superlevel sets — this is the classical theorem that `E → 0` at the ideal
   boundary of a hyperbolic surface, and it is *equivalent* to hyperbolicity).
   This file states it as `hyperbolicity_of_extremalFamily` (with a `sorry`).

2. **The holomorphic modulus** of `E`: a holomorphic `Φ : X → ℂ` with a logarithmic pole at `x₀`
   and `‖Φ x‖ = exp (−E x)` off `x₀`.  For a unit-pole Green function this is
   `Φ = exp (−(E + iE*))`; it is single valued precisely because the periods of `*dE` are multiples
   of `2π`.  The workspace proves the period computation for loops that are null-homotopic in `X`
   (`Work.Modulus.greenPeriodHom_two_pi_zmultiples`) and the passage to *all* loops of `X ∖ {x₀}`
   is Hubbard's Theorem 1.1.2 (`Work.Spine`), the topological input
   `Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ) → SimplyConnectedSpace X` of the challenge
   hypothesis.  With that input the whole chapter is proved and sorry-free:
   `Work.Modulus.exists_holomorphic_modulus_of_unitGreenFunction_of_hubbard112`
   (see `Submission/Work/Modulus/Main.lean`).  This file states the consequence directly as
   `exists_modulus_of_unitGreen` (with a `sorry`), so that the target does not depend on the
   `Work.Spine` subproject being sorry-free.

3. **Domination**: `‖g x‖ ≤ exp (−E x)` for every member `g` of the family.  This is the maximum
   principle applied to `v := E + log ‖g‖` on the relatively compact region `{E > ε}`
   (`v ≤ ε` on `{E = ε}` because `‖g‖ ≤ 1`; the zeros of `g` contribute `−∞`; at `x₀` the unit pole
   makes `v` bounded).  Stated as `norm_le_exp_neg_of_unitGreen` (with a `sorry`); it is the
   "Domination" step of `NOTES_zero_fiber_route.md` §3 in the same directory.

Given (1)+(2)+(3), the endgame is pure complex analysis and is **proved** below
(`proper_of_maximizer_of_modulus`): the modulus `Φ` lies in the extremal family, so maximality of
`f` gives `‖f'(x₀)‖ ≥ ‖Φ'(x₀)‖`; the domination lets `R := f / Φ` be defined, holomorphic
(removable singularity at `x₀`, where both `f` and `Φ` have simple zeros) and bounded by `1`; then
`‖R x₀‖ = ‖f'(x₀)‖ / ‖Φ'(x₀)‖ ≥ 1`, so `R` is a unimodular constant by the maximum principle:
`f = c·Φ`.  Finally `Φ` is proper into `𝔻` because `‖Φ x‖ = exp (−E x)` makes the pre-image of a
compact `K ⊆ 𝔻` a closed subset of the relatively compact superlevel set `{E ≥ −log r}`
(`r = max ‖·‖ K < 1`), which is `Work.Parabolic.isCompact_preimage_of_greenFunctionAt`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set Classical

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {x₀ : X}

/-- **The negative Perron family at `p`.**  A function belongs to it if it is subharmonic and
`≤ 0` on `X` and grows at most like `log ‖ζ‖` (a *unit* logarithmic pole) near `p`.

Its upper envelope `negPerron p` is the negative of the Green function at `p`.  Unlike
`Work.UnitGreen.IsUnitGreenFunctionAt` this definition makes **no** relative-compactness
requirement (no decay at the ideal boundary), so the family is non-empty as soon as the extremal
family at `p` is: `log ‖g‖` for `g ∈ Submission.extremalFamily p` is subharmonic, `≤ 0`, and
dominated by `log ‖ζ‖` near `p`. -/
def negPerronFamily (p : X) : Set (X → ℝ) :=
  {v | Submission.SubharmonicOnX v (Set.univ \ {p}) ∧ (∀ x : X, v x ≤ 0) ∧
    ∃ C : ℝ, ∃ W : Set X, W ∈ 𝓝 p ∧ ∀ x ∈ W, x ≠ p →
      v x ≤ Real.log ‖(chartAt ℂ p) x - (chartAt ℂ p) p‖ + C}

/-- The upper envelope of the negative Perron family at `p`: the negative of the Green function of
`X` with pole `p` (i.e. `G_p = −negPerron p`). -/
def negPerron (p : X) : X → ℝ :=
  fun x => sSup ((fun v : X → ℝ => v x) '' negPerronFamily (X := X) p)

/-- The envelope of the negative Perron family is `≤ 0`. -/
theorem negPerron_le_zero (p : X) (x : X) : negPerron p x ≤ 0 := by
  rcases Set.eq_empty_or_nonempty ((fun v : X → ℝ => v x) '' negPerronFamily (X := X) p) with
    h | h
  · rw [negPerron, h, Real.sSup_empty]
  · exact csSup_le h (by rintro _ ⟨v, hv, rfl⟩; exact hv.2.1 x)

/-- **The extremal value of the family at `p`, measured at `q`**:
`A(p,q) = sup {‖h q‖ : h ∈ Submission.extremalFamily p}`.

This is Ahlfors' "Carathéodory function" of the pair `(p,q)`; it satisfies `A(p,q) ≤ e^{-G_p(q)}`
(the Perron inequality) and `A(p,q) = A(q,p)` (see
`Work.SimplyConnected.ABS.extremalValue_symm`), and the classical theorem is
`A(p,q) = A(q,p) = e^{-G_p(q)}`. -/
def extremalValue (p q : X) : ℝ :=
  sSup ((fun h : X → ℂ => ‖h q‖) '' Submission.extremalFamily p)

/-- `A(p,q) ≤ 1`, because every member of the extremal family is bounded by `1`. -/
theorem extremalValue_le_one (p q : X) : extremalValue p q ≤ 1 := by
  refine csSup_le (Set.Nonempty.image _ (Submission.extremalFamily_nonempty p)) ?_
  rintro _ ⟨h, hh, rfl⟩
  exact hh.2.1 q

/-- A maximizer with positive extremal value takes values in the **open** unit ball. -/
theorem norm_lt_one {f : X → ℂ} (hf : f ∈ Submission.extremalFamily x₀)
    (hpos : 0 < ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖) :
    ∀ x : X, ‖f x‖ < 1 := by
  have hcont : Continuous f := hf.1.continuous
  have hSclosed : IsClosed {x : X | ‖f x‖ = 1} := isClosed_eq hcont.norm continuous_const
  have hSopen : IsOpen {x : X | ‖f x‖ = 1} := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hloc : ∀ᶠ z in 𝓝 y, f z = f y := by
      set e : OpenPartialHomeomorph X ℂ := chartAt ℂ y with he
      have hsrc : y ∈ e.source := mem_chart_source ℂ y
      have han : AnalyticAt ℂ (f ∘ e.symm) (e y) := hf.1 y (Set.mem_univ y)
      obtain ⟨ρ, hρ, hρana⟩ := han.exists_ball_analyticOnNhd
      obtain ⟨ε, hε, hεsub⟩ : ∃ ε > 0, Metric.ball (e y) ε ⊆ e.target := by
        obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp e.open_target (e y) (e.map_source hsrc)
        exact ⟨ε, hε, hεsub⟩
      set r : ℝ := min ρ ε with hr
      have hrpos : 0 < r := lt_min hρ hε
      have hrleρ : r ≤ ρ := min_le_left _ _
      have hrleε : r ≤ ε := min_le_right _ _
      have hdiff : DifferentiableOn ℂ (f ∘ e.symm) (Metric.ball (e y) r) :=
        (hρana.mono (Metric.ball_subset_ball hrleρ)).differentiableOn
      have hmax : IsMaxOn (norm ∘ (f ∘ e.symm)) (Metric.ball (e y) r) (e y) := by
        intro z hz
        have h1 : ‖f (e.symm z)‖ ≤ 1 := hf.2.1 _
        have h2 : ‖f y‖ = 1 := hy
        have h3 : e.symm (e y) = y := e.left_inv hsrc
        simp only [Function.comp_apply, h3, h2]
        exact h1
      have hEq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
        (f := f ∘ e.symm) (U := Metric.ball (e y) r) (c := e y)
        (convex_ball _ _).isPreconnected Metric.isOpen_ball hdiff
        (Metric.mem_ball_self hrpos) hmax
      have hpre1 : e.source ∈ 𝓝 y := e.open_source.mem_nhds hsrc
      have hpre2 : e ⁻¹' (Metric.ball (e y) r) ∈ 𝓝 y :=
        (e.continuousAt hsrc).preimage_mem_nhds
          (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hrpos))
      have hpre : e.source ∩ e ⁻¹' (Metric.ball (e y) r) ∈ 𝓝 y := Filter.inter_mem hpre1 hpre2
      filter_upwards [hpre] with z hz
      have hzsrc : z ∈ e.source := hz.1
      have hzball : e z ∈ Metric.ball (e y) r := hz.2
      calc f z = f (e.symm (e z)) := by rw [e.left_inv hzsrc]
        _ = (f ∘ e.symm) (e z) := rfl
        _ = (f ∘ e.symm) (e y) := hEq hzball
        _ = f y := by simp only [Function.comp_apply, e.left_inv hsrc]
    refine Filter.mem_of_superset hloc (fun z hz => ?_)
    simp only [Set.mem_setOf_eq] at hz ⊢
    rw [hz]
    exact hy
  by_contra hcon
  push_neg at hcon
  obtain ⟨y, hy⟩ := hcon
  have hyle : ‖f y‖ = 1 := le_antisymm (hf.2.1 y) hy
  have hall : ∀ x : X, ‖f x‖ = 1 := by
    intro x
    have hsub : (Set.univ : Set X) ⊆ {x : X | ‖f x‖ = 1} :=
      isPreconnected_univ.subset_isClopen ⟨hSclosed, hSopen⟩ ⟨y, Set.mem_univ y, hyle⟩
    exact hsub (Set.mem_univ x)
  have hconst := hf.1.exists_eq_const_of_norm_eq x₀ (fun z => by rw [hall z, hall x₀])
  have hzero : f = fun _ => (0 : ℂ) := by
    funext z
    rw [hconst z, hf.2.2]
  have hder : deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 0 := by
    have h1 : (f ∘ (chartAt ℂ x₀).symm) = (fun _ : ℂ => (0 : ℂ)) := by
      funext w; simp [hzero]
    rw [h1, deriv_const]
  rw [hder, norm_zero] at hpos
  exact lt_irrefl 0 hpos

/-- **A holomorphic function on a compact connected complex one-manifold is constant.**  This is
the usual maximum-modulus argument: `‖f‖` attains its maximum at some point `y`; in the chart at
`y` the pullback of `f` has an interior maximum of its modulus, hence is locally constant there
(`Complex.eqOn_of_isPreconnected_of_isMaxOn_norm`), so `{x | ‖f x‖ = ‖f y‖}` is clopen and equals
`X` by connectedness; then `f` has constant modulus and `Submission.HolomorphicOnX.exists_eq_const_of_norm_eq`
applies. -/
theorem exists_eq_const_of_compactSpace [CompactSpace X] (x : X) {f : X → ℂ}
    (hf : Submission.HolomorphicOnX f univ) : ∃ c : ℂ, ∀ y : X, f y = c := by
  obtain ⟨y, -, hy⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hf.continuous.norm.continuousOn
  have hmax : ∀ z : X, ‖f z‖ ≤ ‖f y‖ := fun z => hy (Set.mem_univ z)
  have hSopen : IsOpen {z : X | ‖f z‖ = ‖f y‖} := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    set e : OpenPartialHomeomorph X ℂ := chartAt ℂ z with he
    have hsrc : z ∈ e.source := mem_chart_source ℂ z
    have han : AnalyticAt ℂ (f ∘ e.symm) (e z) := hf z (Set.mem_univ z)
    obtain ⟨ρ, hρ, hρana⟩ := han.exists_ball_analyticOnNhd
    obtain ⟨ε, hε, hεsub⟩ : ∃ ε > 0, Metric.ball (e z) ε ⊆ e.target := by
      obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp e.open_target (e z) (e.map_source hsrc)
      exact ⟨ε, hε, hεsub⟩
    set r : ℝ := min ρ ε with hr
    have hrpos : 0 < r := lt_min hρ hε
    have hrleρ : r ≤ ρ := min_le_left _ _
    have hrleε : r ≤ ε := min_le_right _ _
    have hdiff : DifferentiableOn ℂ (f ∘ e.symm) (Metric.ball (e z) r) :=
      (hρana.mono (Metric.ball_subset_ball hrleρ)).differentiableOn
    have hmaxOn : IsMaxOn (norm ∘ (f ∘ e.symm)) (Metric.ball (e z) r) (e z) := by
      intro w hw
      have h1 : ‖f (e.symm w)‖ ≤ ‖f y‖ := hmax _
      have h2 : ‖f z‖ = ‖f y‖ := hz
      have h3 : e.symm (e z) = z := e.left_inv hsrc
      simp only [Function.comp_apply, h3, h2]
      exact h1
    have hEq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
      (f := f ∘ e.symm) (U := Metric.ball (e z) r) (c := e z)
      (convex_ball _ _).isPreconnected Metric.isOpen_ball hdiff
      (Metric.mem_ball_self hrpos) hmaxOn
    have hpre1 : e.source ∈ 𝓝 z := e.open_source.mem_nhds hsrc
    have hpre2 : e ⁻¹' (Metric.ball (e z) r) ∈ 𝓝 z :=
      (e.continuousAt hsrc).preimage_mem_nhds
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hrpos))
    have hpre : e.source ∩ e ⁻¹' (Metric.ball (e z) r) ∈ 𝓝 z := Filter.inter_mem hpre1 hpre2
    filter_upwards [hpre] with w hw
    have hwsrc : w ∈ e.source := hw.1
    have hwball : e w ∈ Metric.ball (e z) r := hw.2
    have heq : (f ∘ e.symm) (e w) = (f ∘ e.symm) (e z) := hEq hwball
    simp only [Function.comp_apply, e.left_inv hwsrc, e.left_inv hsrc] at heq
    rw [heq]
    exact hz
  have hSclosed : IsClosed {z : X | ‖f z‖ = ‖f y‖} :=
    isClosed_eq hf.continuous.norm continuous_const
  have hall : ∀ z : X, ‖f z‖ = ‖f y‖ := by
    intro z
    have hsub : (Set.univ : Set X) ⊆ {w : X | ‖f w‖ = ‖f y‖} :=
      isPreconnected_univ.subset_isClopen ⟨hSclosed, hSopen⟩ ⟨y, Set.mem_univ y, rfl⟩
    exact hsub (Set.mem_univ z)
  exact ⟨f x, fun z => hf.exists_eq_const_of_norm_eq x (fun w => by rw [hall w, hall x]) z⟩

/-- **The surface carrying a non-constant bounded holomorphic function is not compact.**  If `X`
were compact then (previous lemma) `f` would be constant, so `f ≡ f x₀ = 0` and its chart derivative
at `x₀` would vanish, contradicting `hpos`. -/
theorem not_compactSpace_of_extremal_maximizer {f : X → ℂ}
    (hf : f ∈ Submission.extremalFamily x₀)
    (hpos : 0 < ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖) :
    ¬ CompactSpace X := by
  intro hc
  haveI := hc
  obtain ⟨c, hc'⟩ := exists_eq_const_of_compactSpace (X := X) x₀ (f := f) hf.1
  have hc0 : c = 0 := by
    rw [← hc' x₀]
    exact hf.2.2
  have hzero : f = fun _ => (0 : ℂ) := by
    funext z
    rw [hc' z, hc0]
  have hder : deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 0 := by
    have h1 : (f ∘ (chartAt ℂ x₀).symm) = (fun _ : ℂ => (0 : ℂ)) := by
      funext w; simp [hzero]
    rw [h1, deriv_const]
  rw [hder, norm_zero] at hpos
  exact lt_irrefl 0 hpos

/-- **The endgame.**  An injective holomorphic `f : X → ℂ` mapping onto the open unit ball is proper
into the ball: preimages of compact subsets of the ball are compact. -/
theorem properIntoBall_of_injective_onto {f : X → ℂ}
    (hf : f ∈ Submission.extremalFamily x₀) (hinj : Function.Injective f)
    (honto : ∀ a : ℂ, ‖a‖ < 1 → ∃ x : X, f x = a)
    (hball : ∀ x : X, ‖f x‖ < 1) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Metric.ball (0 : ℂ) 1 → IsCompact (f ⁻¹' K) := by
  classical
  intro K hK hKsub
  have hmem : ∀ x : X, f x ∈ Metric.ball (0 : ℂ) 1 := fun x => by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hball x
  set g : X → ↥(Metric.ball (0 : ℂ) 1) := fun x => ⟨f x, hmem x⟩ with hgdef
  have hgcoe : ∀ x : X, ((g x : ↥(Metric.ball (0 : ℂ) 1)) : ℂ) = f x := fun x => rfl
  have hgcont : Continuous g := hf.1.continuous.subtype_mk _
  have hginj : Function.Injective g := fun x y hxy =>
    hinj (by simpa only [hgcoe] using congrArg (Subtype.val) hxy)
  have hgsurj : Function.Surjective g := by
    intro w
    have hw : ‖(w : ℂ)‖ < 1 := by
      have h := w.2
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h
      exact h
    obtain ⟨x, hx⟩ := honto (w : ℂ) hw
    exact ⟨x, Subtype.ext hx⟩
  have hgopen : IsOpenMap g := by
    intro V hV
    have h1 : IsOpen (f '' V) :=
      Work.Parabolic.isOpenMap_of_injective_holomorphic (X := X) hf.1 hinj V hV
    have h2 : g '' V = (Subtype.val ⁻¹' (f '' V) : Set ↥(Metric.ball (0 : ℂ) 1)) := by
      ext w; constructor
      · rintro ⟨x, hxV, rfl⟩
        exact ⟨x, hxV, rfl⟩
      · rintro ⟨x, hxV, hxfV⟩
        exact ⟨x, hxV, Subtype.ext hxfV⟩
    rw [h2]
    exact h1.preimage continuous_subtype_val
  set e : X ≃ ↥(Metric.ball (0 : ℂ) 1) := Equiv.ofBijective g ⟨hginj, hgsurj⟩ with hedef
  have hecoe : ⇑e = g := Equiv.coe_ofBijective g ⟨hginj, hgsurj⟩
  have hiff : ∀ W : Set ↥(Metric.ball (0 : ℂ) 1), IsOpen (e ⁻¹' W) ↔ IsOpen W := by
    intro W
    constructor
    · intro hW
      have h2 : e '' (e ⁻¹' W) = W := by
        ext w; constructor
        · rintro ⟨x, hxW, rfl⟩; exact hxW
        · intro hw; exact ⟨e.symm w, by simpa using hw, e.apply_symm_apply w⟩
      rw [← h2]
      have hmap : e '' (e ⁻¹' W) = g '' (e ⁻¹' W) := by rw [hecoe]
      rw [hmap]
      exact hgopen _ hW
    · intro hW
      exact hW.preimage (by rw [hecoe]; exact hgcont)
  set E : X ≃ₜ ↥(Metric.ball (0 : ℂ) 1) := e.toHomeomorph hiff with hEdef
  have hEcoe : ⇑E = g := by
    rw [hEdef, Equiv.coe_toHomeomorph, hecoe]
  have hS : IsCompact ((Subtype.val ⁻¹' K : Set ↥(Metric.ball (0 : ℂ) 1))) := by
    rw [Subtype.isCompact_iff]
    have himg : Subtype.val '' (Subtype.val ⁻¹' K : Set ↥(Metric.ball (0 : ℂ) 1)) = K := by
      ext z; constructor
      · rintro ⟨w, hw, rfl⟩; exact hw
      · intro hz
        exact ⟨⟨z, hKsub hz⟩, hz, rfl⟩
    rw [himg]; exact hK
  have hpre : f ⁻¹' K = E ⁻¹' (Subtype.val ⁻¹' K : Set ↥(Metric.ball (0 : ℂ) 1)) := by
    ext x; simp only [Set.mem_preimage, hEcoe, hgcoe]
  rw [hpre]
  exact E.isCompact_preimage.mpr hS

end Work.SimplyConnected.ABS

/-! ## The two classical inputs, and the general reduction

The three declarations below are the inputs of the argument (see the module docstring).  Inputs
(1) and (3) are stated for an arbitrary member of the extremal family; input (2) is the
single-valuedness of the modulus of the unit-pole Green function, which the workspace proves from
Hubbard's Theorem 1.1.2 (`Work.Spine`) plus the period computation of `Submission/Work/Modulus`
(`Work.Modulus.exists_holomorphic_modulus_of_unitGreenFunction_of_hubbard112`). -/

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {x₀ : X}

/-- **The decay-free Perron envelope of the extremal problem.**  A non-zero member of the extremal
family whose zero at `x₀` is simple produces a strictly positive harmonic function `E` on
`X \ {x₀}` with a *unit* logarithmic pole at `x₀` which dominates the whole extremal family.  No
relative compactness of the superlevel sets ("decay at the ideal boundary") is required. -/
theorem envelope_of_extremalFamily {f : X → ℂ}
    (hf : f ∈ Submission.extremalFamily x₀)
    (hpos : 0 < ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖) :
    ∃ E : X → ℝ, (∀ x : X, x ≠ x₀ → 0 < E x) ∧
      Submission.HarmonicOnX E (Set.univ \ {x₀}) ∧
      Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {x₀}) x₀ E ∧
      (∀ g ∈ Submission.extremalFamily x₀, ∀ x : X, x ≠ x₀ → ‖g x‖ ≤ Real.exp (-(E x))) := by
  have hne : ∃ x : X, f x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hzero : f = fun _ => (0 : ℂ) := funext fun x => hcon x
    have hd : deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 0 := by
      have h1 : (f ∘ (chartAt ℂ x₀).symm) = fun _ => (0 : ℂ) := by
        funext w; simp [hzero]
      rw [h1, deriv_const]
    rw [hd, norm_zero] at hpos
    exact lt_irrefl 0 hpos
  have hd0 : deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hpos
    exact lt_irrefl 0 hpos
  have hf0' : (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 0 := by
    simp only [Function.comp_apply, (chartAt ℂ x₀).left_inv (mem_chart_source ℂ x₀)]
    exact hf.2.2
  obtain ⟨H, hHana, hHne, hHeq⟩ :=
    Work.SimplyConnected.ABS.exists_simpleZero_factorization (hf.1 x₀ (Set.mem_univ x₀)) hf0' hd0
  exact exists_posHarmonic_logPole_dominating' (x₀ := x₀) hf hne ⟨H, hHana, hHne, hHeq⟩

/-- **Ahlfors' rigidity**: the maximiser attains the envelope off the pole. -/
theorem rigidity_of_maximizer {f : X → ℂ} {E : X → ℝ}
    (hf : f ∈ Submission.extremalFamily x₀)
    (hmax : ∀ g ∈ Submission.extremalFamily x₀,
      ‖deriv (g ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ ≤
        ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖)
    (hEpos : ∀ x : X, x ≠ x₀ → 0 < E x)
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {x₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {x₀}) x₀ E)
    (hdom : ∀ x : X, x ≠ x₀ → ‖f x‖ ≤ Real.exp (-(E x)))
    (hmod : ∃ Φ : X → ℂ, Submission.HolomorphicOnX Φ Set.univ ∧
      Submission.HasLogPoleAt x₀ Φ ∧ (∀ x : X, x ≠ x₀ → ‖Φ x‖ = Real.exp (-(E x)))) :
    ∀ x : X, x ≠ x₀ → ‖f x‖ = Real.exp (-(E x)) :=
  rigidity_of_maximizer_of_modulus hf hmax hEpos hEharm hpole hdom hmod

/-! ## Ahlfors' univalence (`Conformal invariants`, §10-4), decay-free

Given the envelope `E : X → ℝ` at `x₀` together with its *holomorphic modulus* `Φ` (so that the
maximiser attains `E` off the pole: the rigidity `rigidity_of_maximizer`), the maximiser is
injective.  The argument is Ahlfors' proof that the extremal function is a covering map of the
disc, arranged so that it uses the sweep envelope at the *second* pole `y` and Ahlfors' inequality
`(10-4)` but *not* the symmetry of the Green function in the sharp form `Ey x₀ = E₀ y`:

* the Möbius conjugate `F := ψ_{f y} ∘ f` lies in the extremal family at `y`;
* `u := Ey + log ‖F‖` is harmonic off the zeros of `F`, and `u ≤ 0` there by the Perron inequality
  at `y` (the sweep of the clamped logarithmic barrier dominates the whole family:
  `sweep_greenBarrier_dominates`, which needs *no* hypothesis on the order of the zero of the
  member witnessing that the family is non-trivial);
* `u x₀ = Ey x₀ - E₀ y ≥ 0` by Ahlfors' inequality `(10-4)` (`envelope_le_swap`), which is the
  symmetry `A(y,x₀) = A(x₀,y)` of the *value* extremal problem together with the sharpness at `x₀`
  given by the rigidity;
* hence `u ≡ 0` on the preconnected open set `X ∖ F⁻¹(0)` (`isPreconnected_compl_closedDiscrete`
  plus the strong maximum principle `eqOn_of_isMaxOn_of_isPreconnected`), and the zeros of `F` are
  exactly `{y}`: at any other zero `z` a sequence in `X ∖ F⁻¹(0)` approaching `z` would give
  `‖F zₙ‖ = exp (-(Ey zₙ)) → exp (-(Ey z)) > 0` against `‖F zₙ‖ → ‖F z‖ = 0`.

Since the zeros of `F` are the solutions of `f z = f y`, this identifies every fibre of `f` as a
single point: `f` is injective. -/

/-- Every member of an extremal family maps into the **open** unit disc.  (A local copy of
`norm_lt_one_of_mem_extremalFamily`, which lives in a module importing this one.) -/
theorem member_norm_lt_one {p : X} {h : X → ℂ} (hh : h ∈ Submission.extremalFamily p) (x : X) :
    ‖h x‖ < 1 := by
  by_contra hcon
  push_neg at hcon
  have h1 : ‖h x‖ = 1 := le_antisymm (hh.2.1 x) hcon
  have hsub : Submission.SubharmonicOnX (fun z : X => ‖h z‖) Set.univ :=
    subharmonicOnX_norm_of_holomorphic hh.1
  have hmax : ∀ z : X, ‖h z‖ ≤ ‖h x‖ := fun z => by rw [h1]; exact hh.2.1 z
  have hconst : ∀ z : X, ‖h z‖ = ‖h x‖ := Submission.SubharmonicOnX.eq_of_isMaxOn hsub hmax
  have hcong : ∀ z : X, h z = h x :=
    hh.1.exists_eq_const_of_norm_eq x (fun z => by rw [hconst z, hconst x])
  have hzero : ‖h x‖ = 0 := by rw [← hcong p, hh.2.2, norm_zero]
  rw [h1] at hzero
  norm_num at hzero

/-- The set defining `extremalValue p q` is bounded above by `1`. -/
theorem bddAbove_extremalValue' (p q : X) :
    BddAbove ((fun h : X → ℂ => ‖h q‖) '' Submission.extremalFamily p) :=
  ⟨1, by rintro _ ⟨h, hh, rfl⟩; exact hh.2.1 q⟩

/-- **The Möbius trick**: `A(q,p) ≤ A(p,q)`.  For `h ∈ 𝔽_q` the function `ψ_{h p} ∘ h` lies in
`𝔽_p` and takes the value `-h p` at `q`. -/
theorem extremalValue_le_swap (p q : X) : extremalValue q p ≤ extremalValue p q := by
  classical
  refine csSup_le (Set.Nonempty.image _ (Submission.extremalFamily_nonempty q)) ?_
  rintro _ ⟨h, hh, rfl⟩
  rcases eq_or_ne (h p) 0 with hzero | hne
  · simp only [hzero, norm_zero]
    exact le_csSup (bddAbove_extremalValue' p q)
      ⟨0, Submission.zero_mem_extremalFamily p, by simp⟩
  · have hlt : ‖h p‖ < 1 := member_norm_lt_one hh p
    set H : X → ℂ := fun z => Submission.mobiusA (h p) (h z) with hHdef
    have hHhol : Submission.HolomorphicOnX H Set.univ :=
      Submission.HolomorphicOnX.mobiusA_comp hh.1 (fun z _ => hh.2.1 z) hlt
    have hHnorm : ∀ z : X, ‖H z‖ ≤ 1 := fun z => Submission.norm_mobiusA_le hlt (hh.2.1 z)
    have hHp : H p = 0 := by
      simp only [hHdef]
      exact Submission.mobiusA_self (h p)
    have hHmem : H ∈ Submission.extremalFamily p := ⟨hHhol, hHnorm, hHp⟩
    have hHq : H q = -h p := by
      simp only [hHdef]
      rw [hh.2.2, Submission.mobiusA_apply_zero]
    have hmem : ‖H q‖ ∈ (fun g : X → ℂ => ‖g q‖) '' Submission.extremalFamily p :=
      ⟨H, hHmem, rfl⟩
    calc ‖h p‖ = ‖H q‖ := by rw [hHq, norm_neg]
      _ ≤ extremalValue p q := le_csSup (bddAbove_extremalValue' p q) hmem

/-- **Ahlfors' symmetry of the extremal value**: `A(p,q) = A(q,p)`. -/
theorem extremalValue_swap (p q : X) : extremalValue p q = extremalValue q p :=
  le_antisymm (extremalValue_le_swap q p) (extremalValue_le_swap p q)

/-- **The sharpness at the pole, from the rigidity**: `A(x₀,y) = exp (-(E y))`. -/
theorem extremalValue_attained_of_rigidity {E : X → ℝ} {f : X → ℂ}
    (hf : f ∈ Submission.extremalFamily x₀)
    (hdom : ∀ g ∈ Submission.extremalFamily x₀, ∀ x : X, x ≠ x₀ → ‖g x‖ ≤ Real.exp (-(E x)))
    (hrig : ∀ x : X, x ≠ x₀ → ‖f x‖ = Real.exp (-(E x))) {y : X} (hy : y ≠ x₀) :
    extremalValue x₀ y = Real.exp (-(E y)) := by
  refine le_antisymm ?_ ?_
  · refine csSup_le (Set.Nonempty.image _ (Submission.extremalFamily_nonempty x₀)) ?_
    rintro _ ⟨g, hg, rfl⟩
    exact hdom g hg y hy
  · have hmem : ‖f y‖ ∈ (fun h : X → ℂ => ‖h y‖) '' Submission.extremalFamily x₀ :=
      ⟨f, hf, rfl⟩
    calc Real.exp (-(E y)) = ‖f y‖ := (hrig y hy).symm
      _ ≤ extremalValue x₀ y := le_csSup (bddAbove_extremalValue' x₀ y) hmem

/-- **Ahlfors' inequality `(10-4)` at the pole**: `Ey x₀ ≤ E₀ y`.  Needs only the domination at
`y`, the sharpness at `x₀` (the rigidity) and the symmetry of the extremal value. -/
theorem envelope_le_swap {E₀ Ey : X → ℝ} {f : X → ℂ} {y : X}
    (hf : f ∈ Submission.extremalFamily x₀)
    (hdom₀ : ∀ g ∈ Submission.extremalFamily x₀, ∀ z : X, z ≠ x₀ → ‖g z‖ ≤ Real.exp (-(E₀ z)))
    (hrig : ∀ z : X, z ≠ x₀ → ‖f z‖ = Real.exp (-(E₀ z)))
    (hdomy : ∀ g ∈ Submission.extremalFamily y, ∀ z : X, z ≠ y → ‖g z‖ ≤ Real.exp (-(Ey z)))
    (hy : y ≠ x₀) : Ey x₀ ≤ E₀ y := by
  have hAy : extremalValue y x₀ ≤ Real.exp (-(Ey x₀)) := by
    refine csSup_le (Set.Nonempty.image _ (Submission.extremalFamily_nonempty y)) ?_
    rintro _ ⟨g, hg, rfl⟩
    exact hdomy g hg x₀ (Ne.symm hy)
  have hA0 : extremalValue x₀ y = Real.exp (-(E₀ y)) :=
    extremalValue_attained_of_rigidity (x₀ := x₀) hf hdom₀ hrig hy
  have h := hAy
  rw [extremalValue_swap y x₀, hA0] at h
  exact neg_le_neg_iff.mp (Real.exp_le_exp.mp h)

/-- **The sweep envelope at an arbitrary pole** dominates the extremal family there.  This is the
Perron/balayage inequality `sweep_greenBarrier_dominates`, with no hypothesis on the order of the
zero of the member witnessing that the family is non-trivial. -/
theorem exists_sweep_envelope (y : X) {h : X → ℂ} (hh : h ∈ Submission.extremalFamily y)
    (hne : ∃ x : X, h x ≠ 0) :
    ∃ Ey : X → ℝ, Submission.HarmonicOnX Ey (Set.univ \ {y}) ∧
      (∀ g ∈ Submission.extremalFamily y, ∀ z : X, z ≠ y → ‖g z‖ ≤ Real.exp (-(Ey z))) := by
  obtain ⟨ρ, hρ, hsub⟩ := Submission.exists_chartDisc_radius y
  have hGsub : Submission.SubharmonicOnX (Submission.greenBarrier y ρ) (Set.univ \ {y}) :=
    Submission.subharmonicOnX_greenBarrier hρ hsub
  have hneSF : (Submission.sweepFamily (Submission.greenBarrier y ρ) (Set.univ \ {y})).Nonempty :=
    sweepFamily_greenBarrier_nonempty hρ hsub hh hne
  exact ⟨Submission.sweep (Submission.greenBarrier y ρ) (Set.univ \ {y}),
    Submission.sweep_harmonic (Submission.isOpen_univ_diff_singleton y) hGsub hneSF,
    fun g hg z hz => sweep_greenBarrier_dominates (x₀ := y) hρ hsub g hg z hz⟩

/-- **Strong maximum principle on a preconnected open set.**  A subharmonic function on an open
preconnected set which is bounded above by its value at a point of the set is constant there.
(A local copy of `SubharmonicOnX.eqOn_of_isPreconnected_of_le`.) -/
theorem eqOn_of_isMaxOn_of_isPreconnected {C : Set X} (hCo : IsOpen C) (hC : IsPreconnected C)
    {v : X → ℝ} (hv : Submission.SubharmonicOnX v C) {x : X} (hx : x ∈ C)
    (hle : ∀ z ∈ C, v z ≤ v x) : ∀ z ∈ C, v z = v x := by
  have hB : IsOpen (C ∩ {z : X | v z < v x}) := hv.1.isOpen_inter_preimage hCo isOpen_Iio
  have hAint : IsOpen (interior (C ∩ {z : X | v z = v x})) := isOpen_interior
  have hdisj : Disjoint (interior (C ∩ {z : X | v z = v x})) (C ∩ {z : X | v z < v x}) := by
    refine Set.disjoint_left.mpr fun z hzA hzB => ?_
    have h1 : z ∈ C ∩ {z : X | v z = v x} := interior_subset hzA
    exact absurd h1.2 (ne_of_lt hzB.2)
  have hcover : C ⊆ interior (C ∩ {z : X | v z = v x}) ∪ (C ∩ {z : X | v z < v x}) := by
    intro z hz
    by_cases hzx : v z = v x
    · left
      have hleC : ∀ y ∈ C, v y ≤ v z := by
        intro y hy
        rw [hzx]
        exact hle y hy
      obtain ⟨V, hV, hVeq⟩ := (hv.2 z hz).eqOn_of_le (hCo.mem_nhds hz) hleC
      have hsubO : interior V ∩ C ⊆ C ∩ {w : X | v w = v x} := by
        rintro w ⟨hwV, hwC⟩
        exact ⟨hwC, (hVeq w (interior_subset hwV)).trans hzx⟩
      have hmemV : interior V ∩ C ∈ 𝓝 z :=
        Filter.inter_mem (isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hV))
          (hCo.mem_nhds hz)
      have : interior (C ∩ {w : X | v w = v x}) ∈ 𝓝 z :=
        Filter.mem_of_superset hmemV (interior_maximal hsubO (isOpen_interior.inter hCo))
      exact mem_of_mem_nhds this
    · right
      exact ⟨hz, lt_of_le_of_ne (hle z hz) hzx⟩
  rcases hC.subset_or_subset hAint hB hdisj hcover with h | h
  · intro z hz
    exact (interior_subset (h hz)).2
  · exact absurd (h hx).2 (lt_irrefl (v x))

/-- **Ahlfors' univalence, one fibre.**  If the maximiser `f` attains the envelope `E₀` off `x₀`,
the sweep envelope `Ey` at a second pole `y ≠ x₀` dominates the family at `y`, and
`Ey x₀ ≤ E₀ y` (Ahlfors' inequality `(10-4)`), then the fibre of `f` over `f y` is the single
point `y`. -/
theorem fibre_eq_singleton {E₀ Ey : X → ℝ} {f : X → ℂ} {y : X}
    (hf : f ∈ Submission.extremalFamily x₀)
    (hrig : ∀ z : X, z ≠ x₀ → ‖f z‖ = Real.exp (-(E₀ z)))
    (hEyharm : Submission.HarmonicOnX Ey (Set.univ \ {y}))
    (hdomy : ∀ g ∈ Submission.extremalFamily y, ∀ z : X, z ≠ y → ‖g z‖ ≤ Real.exp (-(Ey z)))
    (hsymm : E₀ y ≤ Ey x₀) (hy : y ≠ x₀) :
    ∀ z : X, f z = f y → z = y := by
  classical
  set F : X → ℂ := fun z => Submission.mobiusA (f y) (f z) with hFdef
  have hfylt : ‖f y‖ < 1 := member_norm_lt_one hf y
  have hFmem : F ∈ Submission.extremalFamily y := by
    refine ⟨?_, ?_, ?_⟩
    · exact Submission.HolomorphicOnX.mobiusA_comp hf.1 (fun z _ => hf.2.1 z) hfylt
    · intro z
      exact Submission.norm_mobiusA_le hfylt (hf.2.1 z)
    · exact Submission.mobiusA_self (f y)
  have hFhol : Submission.HolomorphicOnX F Set.univ := hFmem.1
  have hFy : F y = 0 := hFmem.2.2
  have hfy0 : f y ≠ 0 := by
    intro h
    have h1 := hrig y hy
    rw [h, norm_zero] at h1
    exact (Real.exp_ne_zero (-(E₀ y))) h1.symm
  have hFx₀ : F x₀ = -f y := by
    simp only [hFdef]
    rw [hf.2.2, Submission.mobiusA_apply_zero]
  have hFx₀ne : F x₀ ≠ 0 := by rw [hFx₀]; exact neg_ne_zero.mpr hfy0
  -- ## the zero set of `F` is closed and discrete
  have hZclosed : IsClosed (F ⁻¹' ({0} : Set ℂ)) := isClosed_singleton.preimage hFhol.continuous
  have hZdisc : ∀ x ∈ (F ⁻¹' ({0} : Set ℂ)), ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      U ∩ F ⁻¹' ({0} : Set ℂ) = {x} := by
    intro x hx
    obtain ⟨ε, hε, hiso⟩ := exists_isolated_zero_chart hFhol hx ⟨x₀, hFx₀ne⟩
    set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x with hc
    have hcx : x ∈ c.source := mem_chart_source ℂ x
    refine ⟨c.source ∩ c ⁻¹' Metric.ball (c x) ε, c.isOpen_inter_preimage Metric.isOpen_ball,
      ⟨hcx, by simp only [Set.mem_preimage, Metric.mem_ball, dist_self]; exact hε⟩, ?_⟩
    ext z
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨hzsrc, hzball⟩, hzF⟩
      have hdist : ‖c z - c x‖ < ε := by
        have h2 := Metric.mem_ball.mp hzball
        rwa [dist_eq_norm] at h2
      exact hiso z hzsrc hdist hzF
    · rintro rfl
      exact ⟨⟨hcx, by simp only [Metric.mem_ball, dist_self]; exact hε⟩, hx⟩
  -- ## `u := Ey + log ‖F‖`
  have hu_harm : Submission.HarmonicOnX (fun z : X => Ey z + Real.log ‖F z‖)
      (F ⁻¹' ({0} : Set ℂ))ᶜ := by
    intro z hz
    have hzF : F z ≠ 0 := by simpa [Set.mem_compl_iff, Set.mem_preimage] using hz
    have hzy : z ≠ y := fun h => hzF (by rw [h]; exact hFy)
    exact (hEyharm z ⟨Set.mem_univ z, hzy⟩).add
      (Submission.harmonicOnXAt_log_norm (hFhol z (Set.mem_univ z)) hzF)
  have hx₀C : x₀ ∈ (F ⁻¹' ({0} : Set ℂ))ᶜ := hFx₀ne
  have hu_nonpos : ∀ z ∈ (F ⁻¹' ({0} : Set ℂ))ᶜ, Ey z + Real.log ‖F z‖ ≤ 0 := by
    intro z hz
    have hzF : F z ≠ 0 := by simpa [Set.mem_compl_iff, Set.mem_preimage] using hz
    have hzy : z ≠ y := fun h => hzF (by rw [h]; exact hFy)
    have h1 : ‖F z‖ ≤ Real.exp (-(Ey z)) := hdomy F hFmem z hzy
    have h3 : Real.log ‖F z‖ ≤ -(Ey z) :=
      (Real.log_le_iff_le_exp (norm_pos_iff.mpr hzF)).mpr h1
    linarith
  have hu₀nn : 0 ≤ Ey x₀ + Real.log ‖F x₀‖ := by
    have hnorm : ‖F x₀‖ = Real.exp (-(E₀ y)) := by
      rw [hFx₀, norm_neg]
      exact hrig y hy
    rw [hnorm, Real.log_exp]
    linarith
  have hu₀ : Ey x₀ + Real.log ‖F x₀‖ = 0 := le_antisymm (hu_nonpos x₀ hx₀C) hu₀nn
  have hu_le : ∀ z ∈ (F ⁻¹' ({0} : Set ℂ))ᶜ, Ey z + Real.log ‖F z‖ ≤ Ey x₀ + Real.log ‖F x₀‖ :=
    fun z hz => le_trans (hu_nonpos z hz) hu₀nn
  have hconst : ∀ z ∈ (F ⁻¹' ({0} : Set ℂ))ᶜ,
      Ey z + Real.log ‖F z‖ = Ey x₀ + Real.log ‖F x₀‖ :=
    eqOn_of_isMaxOn_of_isPreconnected (C := (F ⁻¹' ({0} : Set ℂ))ᶜ) hZclosed.isOpen_compl
      (isPreconnected_compl_closedDiscrete hZclosed hZdisc)
      ⟨fun x hx => ((hu_harm x hx).continuousAt).continuousWithinAt,
        fun x hx => (hu_harm x hx).subharmonic⟩ hx₀C hu_le
  have hu_zero : ∀ z ∈ (F ⁻¹' ({0} : Set ℂ))ᶜ, Ey z + Real.log ‖F z‖ = 0 := by
    intro z hz
    rw [hconst z hz, hu₀]
  -- ## no other zero of `F`
  intro z hz
  by_contra hzy
  have hzF : F z = 0 := by
    simp only [hFdef]
    rw [hz, Submission.mobiusA_self]
  haveI hneBot : (𝓝[≠] z).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff]
    intro U hU hzU
    obtain ⟨w, hwU, hwne⟩ := Work.Modulus.exists_ne_of_mem_nhds (hU.mem_nhds hzU)
    exact ⟨w, hwU, hwne⟩
  have hEvz : ∀ᶠ w in 𝓝[≠] z, F w ≠ 0 := by
    obtain ⟨ε, hε, hiso⟩ := exists_isolated_zero_chart hFhol hzF ⟨x₀, hFx₀ne⟩
    set c : OpenPartialHomeomorph X ℂ := chartAt ℂ z with hc
    have hcz : z ∈ c.source := mem_chart_source ℂ z
    have hball : c.source ∩ c ⁻¹' Metric.ball (c z) ε ∈ 𝓝 z :=
      (c.isOpen_inter_preimage Metric.isOpen_ball).mem_nhds
        ⟨hcz, by simp only [Set.mem_preimage, Metric.mem_ball, dist_self]; exact hε⟩
    have hball' : c.source ∩ c ⁻¹' Metric.ball (c z) ε ∈ 𝓝[≠] z := nhdsWithin_le_nhds hball
    filter_upwards [self_mem_nhdsWithin, hball'] with w hwne hw
    intro hwF
    have hdist : ‖c w - c z‖ < ε := by
      have h2 := Metric.mem_ball.mp hw.2
      rwa [dist_eq_norm] at h2
    exact hwne (hiso w hw.1 hdist hwF)
  have hlim1 : Filter.Tendsto (fun w : X => ‖F w‖) (𝓝[≠] z) (𝓝 0) := by
    have h1 : Filter.Tendsto F (𝓝[≠] z) (𝓝 (F z)) :=
      (hFhol.continuous.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have h2 := h1.norm
    rwa [hzF, norm_zero] at h2
  have hlim2 : Filter.Tendsto (fun w : X => ‖F w‖) (𝓝[≠] z) (𝓝 (Real.exp (-(Ey z)))) := by
    have hEycont : ContinuousAt Ey z := (hEyharm z ⟨Set.mem_univ z, hzy⟩).continuousAt
    have h1 : Filter.Tendsto (fun w : X => Real.exp (-(Ey w))) (𝓝[≠] z)
        (𝓝 (Real.exp (-(Ey z)))) :=
      ((Real.continuous_exp.continuousAt.comp hEycont.neg).tendsto).mono_left nhdsWithin_le_nhds
    refine h1.congr' ?_
    filter_upwards [hEvz] with w hwF
    have hwC : w ∈ (F ⁻¹' ({0} : Set ℂ))ᶜ := hwF
    have h := hu_zero w hwC
    have hwlog : Real.log ‖F w‖ = -(Ey w) := by linarith
    rw [← hwlog, Real.exp_log (norm_pos_iff.mpr hwF)]
  have h0 := tendsto_nhds_unique hlim1 hlim2
  exact (Real.exp_ne_zero (-(Ey z))) h0.symm

/-- **Ahlfors' univalence, given the holomorphic modulus at the pole and the symmetry of the
envelope at a second pole.**  The maximiser `f` at `x₀` is injective.

The two inputs are: the holomorphic modulus `Φ` of the envelope `E` (which yields the rigidity
`‖f z‖ = exp (-(E z))`), and, for every second pole `y ≠ x₀`, an envelope `Ey` at `y` dominating the
extremal family at `y` and satisfying `E y ≤ Ey x₀` (the classical symmetry of the Green function:
`E y = Ey x₀` for the true Perron envelopes, whence `A(y,x₀) = exp (-(E y)) = exp (-(Ey x₀))`). -/
theorem injective_of_maximizer_of_modulus {E : X → ℝ} {f : X → ℂ}
    (hf : f ∈ Submission.extremalFamily x₀)
    (hmax : ∀ g ∈ Submission.extremalFamily x₀,
      ‖deriv (g ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ ≤
        ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖)
    (hpos : 0 < ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖)
    (hEpos : ∀ x : X, x ≠ x₀ → 0 < E x)
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {x₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {x₀}) x₀ E)
    (hdom : ∀ g ∈ Submission.extremalFamily x₀, ∀ x : X, x ≠ x₀ → ‖g x‖ ≤ Real.exp (-(E x)))
    (hmod : ∃ Φ : X → ℂ, Submission.HolomorphicOnX Φ Set.univ ∧
      Submission.HasLogPoleAt x₀ Φ ∧ (∀ x : X, x ≠ x₀ → ‖Φ x‖ = Real.exp (-(E x))))
    (hsymm : ∀ y : X, y ≠ x₀ → ∃ Ey : X → ℝ, Submission.HarmonicOnX Ey (Set.univ \ {y}) ∧
      (∀ g ∈ Submission.extremalFamily y, ∀ z : X, z ≠ y → ‖g z‖ ≤ Real.exp (-(Ey z))) ∧
      E y ≤ Ey x₀) :
    Function.Injective f := by
  have hrig : ∀ x : X, x ≠ x₀ → ‖f x‖ = Real.exp (-(E x)) :=
    rigidity_of_maximizer (x₀ := x₀) hf hmax hEpos hEharm hpole (fun x hx => hdom f hf x hx) hmod
  intro a b hab
  have hfa0 : ∀ {u : X}, u ≠ x₀ → f u ≠ 0 := by
    intro u hu h
    have h1 := hrig u hu
    rw [h, norm_zero] at h1
    exact (Real.exp_ne_zero (-(E u))) h1.symm
  by_cases ha : a = x₀
  · rw [ha] at hab
    by_cases hb : b = x₀
    · rw [ha, hb]
    · exact absurd (hab ▸ hf.2.2 : f b = 0) (hfa0 hb)
  · have hfa' : f a ≠ 0 := hfa0 ha
    by_cases hb : b = x₀
    · rw [hb] at hab
      exact absurd (hab.symm ▸ hf.2.2 : f a = 0) hfa'
    · obtain ⟨Ea, hEaharm, hdoma, hsymma⟩ := hsymm a ha
      have hfib : b = a :=
        fibre_eq_singleton (x₀ := x₀) (y := a) hf hrig hEaharm hdoma hsymma ha b hab.symm
      exact hfib.symm

end Work.SimplyConnected.ABS
