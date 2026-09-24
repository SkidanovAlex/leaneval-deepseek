import Mathlib
import Submission.Work.SimplyConnected.ABS.GreenSetupReg
import Submission.Work.SimplyConnected.ABS.clampedBarrierSuperharmonic
import Submission.Work.SimplyConnected.Perron.coherentSubharmonicBarrier

/-!
# The globalized barrier: a local barrier at a frontier point gives a global one

The target `Work.SimplyConnected.Perron.globalizedBarrier` is the classical statement that a
*local barrier* at a frontier point `p` of an open set `Ω` in a Riemann surface forces a *global*
barrier: a superharmonic `β ≥ 0` on `Ω`, continuous there, `β p = 0`, strictly positive on
`Ω \ {p}`, and tending to `0` at `p`.

## The classical proof (Bouligand; source: O. Ivrii, *Perron's Method*, "Bouligand's Lemma")

Write `b := -u`, which is *subharmonic* on `Ω ∩ V`, strictly negative, continuous on `V` and
`b → 0` at `p` — the classical *weak local barrier* in subharmonic form.

* **Bouligand's Lemma 2** (Ivrii, op. cit.): for every `ε > 0` and every neighbourhood `N'` of `p`
  there is a *subharmonic* `b_ε` on `Ω` with `b_ε < 0`, `b_ε ≤ 0`, `b_ε ≤ -1` on `Ω \ N'` and
  `liminf_{z→p} b_ε(z) ≥ -ε`.  The proof is the Poisson/harmonic-measure construction of Ivrii:
  a "tent" function `g` over the set where `u` is small on the collar `Ω ∩ ∂Δ` is extended
  harmonically to the chart disc `Δ` and glued, after clamping at `-1`, to `-1` outside `Δ`.

* **Coherence.**  Applying the lemma to the nested chart balls
  `N'_n := chartBall c a (1/(n+1))` and to `ε := 1/(n+1)` gives a sequence `b_n`; its *finite
  maxima* `B_n := max(-1, b_0, …, b_{n-1})` are subharmonic and *eventually constant on each of
  the open sets* `Ω ∩ {‖c· - a‖ > 1/(k+1)}` and `Ω \ closure (chartBall c a 1)`, which cover `Ω`.
  Hence the pointwise limit `b := ⋁_n B_n` is subharmonic on `Ω` (locality of subharmonicity on an
  open cover) and inherits the *exact* decay `b → 0` at `p` from
  `liminf (sup_n B_n) ≥ sup_n liminf B_n ≥ sup_n (-(1/(n+1))) = 0`.

* **Conclusion.**  `β := min(-b, 1)` is superharmonic on `Ω`, nonnegative, positive off `p`, and
  tends to `0` at `p`; `β p := 0` is then set by hand (`p ∉ Ω` because `Ω` is open).

The two elementary steps above (`subharmonicOnX_max`, `subharmonicOnX_of_isOpen_cover`,
`SubharmonicOnX.congr_of_isOpen`, and the assembly `globalizedBarrier_of_coherent`) are proved
here; the single classical input is isolated as `bouligandStrongGlobalBarrier`.
-/

namespace Work.SimplyConnected.Perron

open Filter Set
open scoped Topology

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## Elementary closure properties of subharmonic functions -/

omit [T2Space X] in
/-- **The pointwise maximum of two subharmonic functions is subharmonic** (duality with the
minimum of superharmonic functions). -/
theorem subharmonicOnX_max {u v : X → ℝ} {U : Set X} (hu : Submission.SubharmonicOnX u U)
    (hv : Submission.SubharmonicOnX v U) :
    Submission.SubharmonicOnX (fun x => max (u x) (v x)) U := by
  have h1 : Submission.SuperharmonicOnX (fun x => min (-u x) (-v x)) U := hu.neg.min hv.neg
  have h2 : Submission.SubharmonicOnX (fun x => -(min (-u x) (-v x))) U := h1.neg
  have heq : (fun x => -(min (-u x) (-v x))) = fun x => max (u x) (v x) := by
    funext x
    rw [min_neg_neg]
    simp
  rwa [heq] at h2

omit [T2Space X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- **Locality of subharmonicity**: it suffices to cover the set by open sets on which the
function is subharmonic. -/
theorem subharmonicOnX_of_isOpen_cover {u : X → ℝ} {U : Set X} {ι : Type*}
    {V : ι → Set X} (hVo : ∀ i, IsOpen (V i)) (hcov : U ⊆ ⋃ i, V i)
    (hV : ∀ i, Submission.SubharmonicOnX u (V i)) :
    Submission.SubharmonicOnX u U := by
  constructor
  · intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcov hx)
    exact ((hV i).1.continuousAt ((hVo i).mem_nhds hxi)).continuousWithinAt
  · intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcov hx)
    exact (hV i).2 x hxi

/-- **Subharmonicity depends only on the germ on an open set.** -/
theorem SubharmonicOnX.congr_of_isOpen {u v : X → ℝ} {U : Set X} (hU : IsOpen U)
    (huv : ∀ x ∈ U, v x = u x) (hu : Submission.SubharmonicOnX u U) :
    Submission.SubharmonicOnX v U := by
  have hneg : Submission.SuperharmonicOnX (fun x => -u x) U := hu.neg
  have hneg' : Submission.SuperharmonicOnX (fun x => -v x) U :=
    Work.SimplyConnected.ABS.SuperharmonicOnX.congr_of_isOpen hU
      (fun x hx => by rw [huv x hx]) hneg
  simpa using hneg'.neg

/-! ## The final assembly: a coherent subharmonic barrier gives the target -/

/-- **From a coherent subharmonic barrier to the global barrier.**  A subharmonic `b < 0` on `Ω`
with `b → 0` at `p` yields the target: `β := min (-b) 1` is superharmonic, nonnegative, positive
off `p`, bounded by `1`, and tends to `0` at `p`; the value at `p` is then prescribed by hand
(`p ∉ Ω` since `Ω` is open and `p ∈ frontier Ω`). -/
theorem globalizedBarrier_of_coherent {Ω : Set X} {p : X} (hΩo : IsOpen Ω) (hp : p ∈ frontier Ω)
    (hb : ∃ b : X → ℝ, Submission.SubharmonicOnX b Ω ∧ (∀ x ∈ Ω, b x < 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : Set X, N ∈ nhds p ∧ ∀ x ∈ Ω ∩ N, -ε < b x)) :
    ∃ β : X → ℝ, Submission.SuperharmonicOnX β Ω ∧ (∀ x ∈ Ω, 0 ≤ β x) ∧ β p = 0 ∧
      ContinuousOn β Ω ∧ (∀ x ∈ Ω, x ≠ p → 0 < β x) ∧
      (∀ ε : ℝ, 0 < ε → ∃ V : Set X, V ∈ nhds p ∧ ∀ x ∈ Ω ∩ V, β x < ε) := by
  classical
  obtain ⟨b, hbsub, hbneg, hbdecay⟩ := hb
  have hpΩ : p ∉ Ω := by
    have h2 := hp
    rw [frontier, hΩo.interior_eq] at h2
    exact h2.2
  have hsup : Submission.SuperharmonicOnX (fun x => -b x) Ω := hbsub.neg
  have hmin : Submission.SuperharmonicOnX (fun x => min (-b x) 1) Ω :=
    Work.SimplyConnected.ABS.SuperharmonicOnX.inf_const_dev hsup 1
  have hsupβ : Submission.SuperharmonicOnX (fun x => if x = p then 0 else min (-b x) 1) Ω := by
    refine Work.SimplyConnected.ABS.SuperharmonicOnX.congr_of_isOpen hΩo ?_ hmin
    intro x hx
    have hxp : x ≠ p := fun h => hpΩ (h ▸ hx)
    simp [hxp]
  refine ⟨fun x => if x = p then 0 else min (-b x) 1, hsupβ, ?_, ?_, hsupβ.1, ?_, ?_⟩
  · intro x hx
    have hxp : x ≠ p := fun h => hpΩ (h ▸ hx)
    simp only [hxp, if_false]
    exact le_of_lt (lt_min (neg_pos.mpr (hbneg x hx)) one_pos)
  · simp
  · intro x hx hxp
    simp only [hxp, if_false]
    exact lt_min (neg_pos.mpr (hbneg x hx)) one_pos
  · intro ε hε
    have hε' : 0 < min ε 1 := lt_min hε one_pos
    obtain ⟨N, hN, hNsub⟩ := hbdecay (min ε 1) hε'
    refine ⟨N, hN, fun x hx => ?_⟩
    have hxp : x ≠ p := fun h => hpΩ (h ▸ hx.1)
    have h1 : -b x < ε := by
      have h3 : -b x < min ε 1 := by linarith [hNsub x hx]
      exact lt_of_lt_of_le h3 (min_le_left ε 1)
    simp only [hxp, if_false]
    exact lt_of_le_of_lt (min_le_left (-b x) 1) h1

/-! ## The target -/

theorem globalizedBarrier {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} (hΩo : IsOpen Ω) {p : X} (hp : p ∈ frontier Ω)
    (hb : ∃ (u : X → ℝ) (V : Set X), IsOpen V ∧ p ∈ V ∧
      Submission.SuperharmonicOnX u (Ω ∩ V) ∧ (∀ x ∈ Ω ∩ V, 0 < u x) ∧
      ContinuousOn u V ∧ u p = 0) :
    ∃ β : X → ℝ, Submission.SuperharmonicOnX β Ω ∧ (∀ x ∈ Ω, 0 ≤ β x) ∧ β p = 0 ∧
      ContinuousOn β Ω ∧ (∀ x ∈ Ω, x ≠ p → 0 < β x) ∧
      (∀ ε : ℝ, 0 < ε → ∃ V : Set X, V ∈ nhds p ∧ ∀ x ∈ Ω ∩ V, β x < ε) := by
  obtain ⟨u, V, hVo, hpV, hsup, hpos, hcont, hup⟩ := hb
  exact globalizedBarrier_of_coherent hΩo hp
    (coherentSubharmonicBarrier hΩo hp hVo hpV hsup hpos hcont hup)

end Work.SimplyConnected.Perron
