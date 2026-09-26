import Mathlib
import Submission.Work.InnermostDisk.Defs
import Submission.Work.TorusCover.Main
import Submission.Work.InnermostDisk.not_isEssential_of_comp

/-!
# Loops inside the image of a simple inessential loop are inessential

Let `F = P.carrier` be a parametrised torus.  This file proves

`Work.InnermostDisk.not_isEssential_of_range_subset_isSimple`:

if `c` is a *simple* closed curve of `F` and `γ` is a closed curve of `F` whose image is
contained in the image of `c`, then `γ` is inessential as soon as `c` is.

The mathematical content is that a simple closed curve of `F` with vanishing winding vector
is null-homotopic, and that every loop inside the image of `c` is a reparametrisation of `c`:
`γ = c ∘ φ` for a continuous `φ : ℝ → ℝ` which advances by an integer number of periods over
one period, so `γ` is a "multiple cover" of a null-homotopic loop, hence null-homotopic.

Formally the reparametrising map `φ` is produced by covering-space path lifting
(`IsCoveringMap.existsUnique_continuousMap_lifts`), applied to the covering map

`Set.rangeFactorization c.γ : ℝ → Set.range c.γ`

of the circle `Set.range c.γ` by the line `ℝ`, which is constructed here from scratch
(`isCoveringMap_rangeFactorization`): the parametrisation of the circle is a quotient map
(its restriction to the compact fundamental interval `[0, 2π]` is surjective onto the circle),
its fibres are exactly the orbits of the free action of `ℤ` on `ℝ` by `k +ᵥ t = t + 2πk`, and
the translates of a ball of radius `π` are pairwise disjoint because distinct periods are at
distance at least `2π`.  Everything is then an instance of
`Topology.IsQuotientMap.isCoveringMapOn_of_vadd_disjoint`, exactly as for the parametrisation
of the torus itself in `Submission/Work/TorusCover/isCoveringMap_psiMapToRange.lean`.

The final step is the elementary reparametrisation lemma
`Work.InnermostDisk.not_isEssential_of_comp`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.InnermostDisk

noncomputable section

/-! ## The `2πℤ`-action on the line

The additive group `ℤ` acts on `ℝ` by `k +ᵥ t = t + 2πk`.  This is the deck transformation
group of the covering `ℝ → circle` given by a simple `2π`-periodic parametrisation. -/

local instance instVAddIntTwoPi : VAdd ℤ ℝ := ⟨fun k t => t + (k : ℝ) * (2 * Real.pi)⟩

local instance instAddActionIntTwoPi : AddAction ℤ ℝ where
  zero_vadd t := by
    show t + ((0 : ℤ) : ℝ) * (2 * Real.pi) = t
    simp
  add_vadd a b t := by
    show t + ((a + b : ℤ) : ℝ) * (2 * Real.pi) =
      (t + (b : ℝ) * (2 * Real.pi)) + (a : ℝ) * (2 * Real.pi)
    push_cast
    ring

local instance instContinuousConstVAddIntTwoPi : ContinuousConstVAdd ℤ ℝ where
  continuous_const_vadd k := by
    show Continuous fun t : ℝ => t + (k : ℝ) * (2 * Real.pi)
    fun_prop

/-! ## Shifting a real number into a fundamental period -/

/-- Every real number can be shifted by an integer multiple of `2π` into the fundamental
interval `[0, 2π)`. -/
theorem exists_int_shift_mem_Ico (x : ℝ) :
    ∃ k : ℤ, x + (k : ℝ) * (2 * Real.pi) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨-⌊x / (2 * Real.pi)⌋, ?_⟩
  have hx : x + ((-⌊x / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) =
      (2 * Real.pi) * Int.fract (x / (2 * Real.pi)) := by
    rw [Int.fract]; push_cast; field_simp; ring
  rw [Set.mem_Ico, hx]
  constructor
  · exact mul_nonneg (le_of_lt hπ) (Int.fract_nonneg _)
  · have h1 := Int.fract_lt_one (x / (2 * Real.pi))
    nlinarith [Real.pi_pos]

/-- **The fibres of a simple `2π`-periodic circle parametrisation.**  Two parameters give the
same point of the circle exactly when they differ by an integer multiple of `2π`.

The direction `⇐` is periodicity; for `⇒` both parameters are shifted into the fundamental
period `[0, 2π)`, where the parametrisation is injective by simplicity. -/
theorem eq_iff_sub_int_mul_two_pi {f : ℝ → R3} (hper : ∀ t : ℝ, f (t + 2 * Real.pi) = f t)
    (hinj : Set.InjOn f (Set.Ico (0 : ℝ) (2 * Real.pi))) (s s' : ℝ) :
    f s = f s' ↔ ∃ k : ℤ, s = s' + (k : ℝ) * (2 * Real.pi) := by
  have hp : Function.Periodic f (2 * Real.pi) := hper
  constructor
  · intro h
    obtain ⟨j, hj⟩ := exists_int_shift_mem_Ico s
    obtain ⟨j', hj'⟩ := exists_int_shift_mem_Ico s'
    have hsj : f (s + (j : ℝ) * (2 * Real.pi)) = f s := (hp.int_mul j) s
    have hs'j : f (s' + (j' : ℝ) * (2 * Real.pi)) = f s' := (hp.int_mul j') s'
    have hin : s + (j : ℝ) * (2 * Real.pi) = s' + (j' : ℝ) * (2 * Real.pi) :=
      hinj hj hj' (by rw [hsj, hs'j, h])
    refine ⟨j' - j, ?_⟩
    push_cast
    linear_combination hin
  · rintro ⟨k, rfl⟩
    exact (hp.int_mul k) s'

/-! ## A simple circle parametrisation is a covering map onto its image -/

/-- **A simple `2π`-periodic map of the line is a covering map onto its image.**

The image of `f` is a circle: `f` is a quotient map onto `Set.range f` (its restriction to the
compact fundamental interval is onto), its fibres are the orbits of the action of `ℤ` on `ℝ` by
`k +ᵥ t = t + 2πk` (`eq_iff_sub_int_mul_two_pi`), and the translates of a ball of radius `π`
are disjoint because two distinct periods are at distance at least `2π`.  Hence every point is
evenly covered. -/
theorem isCoveringMap_rangeFactorization {f : ℝ → R3} (hcont : Continuous f)
    (hper : ∀ t : ℝ, f (t + 2 * Real.pi) = f t)
    (hinj : Set.InjOn f (Set.Ico (0 : ℝ) (2 * Real.pi))) :
    IsCoveringMap (Set.rangeFactorization f) := by
  classical
  have hcontΨ : Continuous (Set.rangeFactorization f) :=
    hcont.subtype_mk fun t => Set.mem_range_self t
  have hsurjΨ : Function.Surjective (Set.rangeFactorization f) :=
    Set.rangeFactorization_surjective
  haveI : CompactSpace (Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  -- the fundamental interval maps onto the circle
  have hsurjBox : Function.Surjective
      ((Set.rangeFactorization f) ∘ (Subtype.val : Set.Icc (0 : ℝ) (2 * Real.pi) → ℝ)) := by
    intro y
    obtain ⟨x, hx⟩ := y.2
    obtain ⟨k, hk⟩ := Work.TorusCover.exists_int_shift_mem_Icc x
    refine ⟨⟨x + (k : ℝ) * (2 * Real.pi), hk⟩, ?_⟩
    show Set.rangeFactorization f (x + (k : ℝ) * (2 * Real.pi)) = y
    have hp : Function.Periodic f (2 * Real.pi) := hper
    have hq : f (x + (k : ℝ) * (2 * Real.pi)) = f x := (hp.int_mul k) x
    exact Subtype.ext (hq.trans hx)
  have hquotBox : Topology.IsQuotientMap
      ((Set.rangeFactorization f) ∘ (Subtype.val : Set.Icc (0 : ℝ) (2 * Real.pi) → ℝ)) :=
    Topology.IsQuotientMap.of_surjective_continuous hsurjBox (hcontΨ.comp continuous_subtype_val)
  have hcoind : Topology.IsCoinducing (Set.rangeFactorization f) :=
    Topology.IsCoinducing.of_comp continuous_subtype_val hcontΨ hquotBox.isCoinducing
  have hquotΨ : Topology.IsQuotientMap (Set.rangeFactorization f) := ⟨hcoind, hsurjΨ⟩
  -- the fibres are the orbits of the period action
  have hfib : ∀ {e₁ e₂ : ℝ}, f e₁ = f e₂ ↔ ∃ k : ℤ, e₂ + (k : ℝ) * (2 * Real.pi) = e₁ := by
    intro e₁ e₂
    rw [eq_iff_sub_int_mul_two_pi hper hinj e₁ e₂]
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k, hk.symm⟩
    · rintro ⟨k, hk⟩; exact ⟨k, hk.symm⟩
  have horbit : ∀ {e₁ e₂ : ℝ},
      Set.rangeFactorization f e₁ = Set.rangeFactorization f e₂ ↔ e₁ ∈ AddAction.orbit ℤ e₂ := by
    intro e₁ e₂
    rw [AddAction.mem_orbit_iff, Subtype.ext_iff]
    exact hfib
  -- disjointness of the translates: the ball of radius `π`
  have hdisj : ∀ e : ℝ, ∃ U ∈ nhds e, ∀ g : ℤ,
      ((fun x => g +ᵥ x) '' U ∩ U).Nonempty → g +ᵥ e = e := by
    intro e
    refine ⟨Metric.ball e Real.pi, Metric.ball_mem_nhds e Real.pi_pos, ?_⟩
    intro g hne
    obtain ⟨x, hx1, hx2⟩ := hne
    obtain ⟨y, hyU, hyx⟩ := hx1
    have hxy : x = y + (g : ℝ) * (2 * Real.pi) := hyx.symm
    have hlt : dist x y < 2 * Real.pi := by
      have h1 : dist x e < Real.pi := Metric.mem_ball.mp hx2
      have h2 : dist y e < Real.pi := Metric.mem_ball.mp hyU
      calc dist x y ≤ dist x e + dist e y := dist_triangle x e y
        _ < 2 * Real.pi := by
            rw [dist_comm e y]; linarith
    have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
    have hd : dist x y = |(g : ℝ)| * (2 * Real.pi) := by
      rw [hxy, Real.dist_eq, add_sub_cancel_left, abs_mul, abs_of_pos hπ]
    have hg1 : |(g : ℝ)| < 1 :=
      lt_of_mul_lt_mul_right (by rw [hd] at hlt; linarith [hlt])
        (le_of_lt hπ)
    have hg0 : g = 0 := by
      have h := abs_lt.mp hg1
      have h1 : g < (1 : ℤ) := by exact_mod_cast h.2
      have h2 : (-1 : ℤ) < g := by exact_mod_cast h.1
      omega
    show g +ᵥ e = e
    rw [hg0]
    simp
  -- the stabilisers are trivial
  have hstab : ∀ e : ℝ, AddAction.stabilizer ℤ e = ⊥ := by
    intro e
    rw [AddSubgroup.eq_bot_iff_forall]
    intro g hg
    show g = 0
    rw [AddAction.mem_stabilizer_iff] at hg
    have hge : e + (g : ℝ) * (2 * Real.pi) = e := hg
    have h0 : (g : ℝ) * (2 * Real.pi) = 0 := by linarith
    have h1 : (g : ℝ) = 0 := (mul_eq_zero.mp h0).resolve_right (by positivity)
    exact_mod_cast h1
  refine isCoveringMap_iff_isCoveringMapOn_univ.mpr ?_
  have h := Topology.IsQuotientMap.isCoveringMapOn_of_vadd_disjoint
    (f := Set.rangeFactorization f) (G := ℤ) hquotΨ horbit hdisj
  have hsetEq : {e : ℝ | AddAction.stabilizer ℤ e = ⊥} = Set.univ := by
    ext e; simp [hstab e]
  rwa [hsetEq, Set.image_univ_of_surjective hsurjΨ] at h

/-! ## The target -/

/-- **A loop contained in the image of a simple inessential loop is inessential.**

Let `γ`, `c` be closed curves of the torus `F = P.carrier`, with `c` simple and `γ` ranging in
the image of `c`.  Then `¬ IsEssential P c` implies `¬ IsEssential P γ`.

Since `c` is simple, the map `Set.rangeFactorization c.γ : ℝ → Set.range c.γ` is a covering map
(`isCoveringMap_rangeFactorization`); lifting `γ : ℝ → Set.range c.γ` through it gives a
continuous `φ : ℝ → ℝ` with `γ = c ∘ φ`.  Simplicity of `c` also shows that `φ` advances by an
integer multiple of `2π` over one period, so `γ` is a reparametrisation of `c` and
`Work.InnermostDisk.not_isEssential_of_comp` applies. -/
theorem not_isEssential_of_range_subset_isSimple {P : Work.CoreTopology.ParamTorus}
    {γ c : Work.CoreTopology.ClosedCurve P} (hc : Work.CoreTopology.IsSimple P c)
    (hsub : Set.range γ.γ ⊆ Set.range c.γ)
    (hcine : ¬ Work.CoreTopology.IsEssential P c) :
    ¬ Work.CoreTopology.IsEssential P γ := by
  have hcov : IsCoveringMap (Set.rangeFactorization c.γ) :=
    isCoveringMap_rangeFactorization c.cont c.periodic hc
  -- `γ`, viewed as a curve in the circle `Set.range c.γ`
  let γbar : C(ℝ, Set.range c.γ) :=
    ⟨fun t => ⟨γ.γ t, hsub ⟨t, rfl⟩⟩, γ.cont.subtype_mk fun t => hsub ⟨t, rfl⟩⟩
  obtain ⟨s₀, hs₀⟩ := hsub ⟨0, rfl⟩
  -- lift it through the covering by the line
  obtain ⟨φ, ⟨-, hφ⟩, -⟩ := hcov.existsUnique_continuousMap_lifts γbar 0 s₀ (by
    show Set.rangeFactorization c.γ s₀ = γbar 0
    exact Subtype.ext hs₀)
  have hcomp : ∀ t : ℝ, γ.γ t = c.γ (φ t) := by
    intro t
    exact (congrArg Subtype.val (congr_fun hφ t)).symm
  -- the lift advances by a constant integer multiple of `2π` over one period
  have hd : ∀ t : ℝ, ∃ k : ℤ,
      φ (t + 2 * Real.pi) - φ t = (k : ℝ) * (2 * Real.pi) := by
    intro t
    have h1 : c.γ (φ (t + 2 * Real.pi)) = c.γ (φ t) := by
      rw [← hcomp (t + 2 * Real.pi), ← hcomp t, γ.periodic t]
    obtain ⟨k, hk⟩ :=
      (eq_iff_sub_int_mul_two_pi c.periodic (show Set.InjOn c.γ (Set.Ico 0 (2 * Real.pi))
        from hc) (φ (t + 2 * Real.pi)) (φ t)).mp h1
    exact ⟨k, by linarith⟩
  obtain ⟨k, hk⟩ := Work.CoreTopology.LiftOf.continuous_int_multiple_const
    (fun t : ℝ => φ (t + 2 * Real.pi) - φ t)
    ((φ.continuous.comp (continuous_id.add continuous_const)).sub φ.continuous) hd
  exact not_isEssential_of_comp (φ : ℝ → ℝ) φ.continuous k (fun t => by linarith [hk t])
    hcomp hcine

end

end Work.InnermostDisk
