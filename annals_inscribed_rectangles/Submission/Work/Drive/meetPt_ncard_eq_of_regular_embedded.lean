import Mathlib
import Submission.Work.Drive.meetBoxEngine

namespace Work.Drive

open Filter
open scoped Topology ContDiff

noncomputable section

/-! ## The loop-vs-`3`-chain count at a *seam* angle: the parameterisation-free count is locally constant

The setting is that of `Work.Drive.meetBox`: `L : ℝ → E` is a *loop* (its parameter is a circle: the
hypothesis `hper` says `L` is `1`-periodic) and `D u : ℝ³ → E` is a family of `3`-chains whose
parameter is a *quotient* of the box (the hypothesis `hbox`: every value of `D u` is attained on
`unitBox 2`).  The meet set is

> `meetBox L (D u) = {p ∈ [0,1] × unitBox 2 | L p.1 = D u p.2}`

and the count we want to control is the **geometric** one, `#(L '' meetBox)`, i.e. the number of
distinct values of `L` on the meet set — equivalently the number of distinct *points of `E`* lying on
both the loop and the chain.  This file proves its local constancy in `u` at a base configuration whose
meets are finite and transverse and whose only self-coincidences of the loop are the periodicity ones
(`hinj`) — the version needed at the angles where a meet sits on a seam, where the naive count of
parameter pairs jumps (see `HN4_SEAM_DEFECT.md`).

The proof is the standard transversality argument (implicit function theorem + compactness), carried out
on the *geometric* (parameterisation-free) count: the local solutions `ψ_ξ` of the family at the base
meets are unique in their balls, every meet of `D u` near `u = 0` is one of them, and the values
`L (ψ_ξ u).1` depend on `ξ` only through the *class* `[ξ]` of the base meet under
`ξ ~ η ↔ L ξ.1 = L η.1` (they agree on a class by the periodicity + uniqueness, and differ across
classes by continuity).  On the base configuration the classes are exactly the geometric meets. -/

/-- **Ranges with the same fibres have the same number of elements.** -/
theorem ncard_range_eq_of_fiber {α β : Type*} {f g : α → β}
    (h : ∀ x y, f x = f y ↔ g x = g y) : (Set.range f).ncard = (Set.range g).ncard := by
  classical
  refine Set.ncard_congr (fun (y : β) (hy : y ∈ Set.range f) => g (Classical.choose hy))
    ?_ ?_ ?_
  · intro y hy
    exact ⟨Classical.choose hy, rfl⟩
  · intro a b ha hb hab
    have h1 : f (Classical.choose ha) = a := Classical.choose_spec ha
    have h2 : f (Classical.choose hb) = b := Classical.choose_spec hb
    have h3 : f (Classical.choose ha) = f (Classical.choose hb) := (h _ _).mpr hab
    rw [h1, h2] at h3
    exact h3
  · intro b hb
    obtain ⟨x, rfl⟩ := hb
    refine ⟨f x, ⟨x, rfl⟩, ?_⟩
    exact (h _ x).mp (Classical.choose_spec (show f x ∈ Set.range f from ⟨x, rfl⟩))

/-- **Upper semicontinuity of the loop-vs-chain meet set** (the version of
`Work.Drive.eventually_meetBox_cover` with the *unused* interiority hypothesis removed: with the
*closed* box the compactness argument needs no interiority, only that the meet set of `D 0` is where the
limit lands). -/
theorem eventually_meetBox_cover_noInterior {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : ℝ → E} {D : ℝ → EuclideanSpace ℝ (Fin 3) → E}
    (hcont : Continuous (fun q : ℝ × (ℝ × EuclideanSpace ℝ (Fin 3)) => L q.2.1 - D q.1 q.2.2))
    {δ : meetBox L (D 0) → ℝ} (hδ : ∀ ξ, 0 < δ ξ) :
    ∀ᶠ s in nhds (0 : ℝ), ∀ p ∈ meetBox L (D s),
      ∃ ξ : meetBox L (D 0), ‖p - ξ.1‖ < δ ξ := by
  have key : ∃ ε > 0, ∀ s, |s| < ε → ∀ p ∈ meetBox L (D s),
      ∃ ξ : meetBox L (D 0), ‖p - ξ.1‖ < δ ξ := by
    by_contra hcon
    push Not at hcon
    have hseq : ∀ k : ℕ, ∃ s : ℝ, ∃ p : ℝ × EuclideanSpace ℝ (Fin 3),
        |s| < 1 / ((k : ℝ) + 1) ∧ p ∈ meetBox L (D s) ∧
        ∀ ξ : meetBox L (D 0), δ ξ ≤ ‖p - ξ.1‖ := by
      intro k
      obtain ⟨s, hs, p, hp, hfar⟩ := hcon (1 / ((k : ℝ) + 1)) (by positivity)
      exact ⟨s, p, hs, hp, hfar⟩
    choose s p hs hp hfar using hseq
    have hst : Tendsto s atTop (nhds (0 : ℝ)) := by
      refine squeeze_zero_norm' (a := fun k : ℕ => 1 / ((k : ℝ) + 1)) ?_
        tendsto_one_div_add_atTop_nhds_zero_nat
      exact Eventually.of_forall fun k => le_of_lt (hs k)
    have hpm : ∀ k, p k ∈ Set.Icc (0 : ℝ) 1 ×ˢ Submission.Drive.unitBox 2 := fun k => by
      obtain ⟨ht, hv, -⟩ := mem_meetBox.mp (hp k)
      exact ⟨ht, hv⟩
    obtain ⟨a, ha, φ, hφ, hpt⟩ :=
      (isCompact_Icc.prod (isCompact_unitBox 2)).tendsto_subseq hpm
    have hpair : Tendsto (fun k : ℕ => (s (φ k), p (φ k))) atTop (nhds ((0 : ℝ), a)) :=
      (hst.comp hφ.tendsto_atTop).prodMk_nhds hpt
    have hzero : L a.1 - D 0 a.2 = 0 := by
      have h1 : Tendsto (fun k : ℕ => L (p (φ k)).1 - D (s (φ k)) (p (φ k)).2) atTop
          (nhds (L a.1 - D 0 a.2)) :=
        (hcont.continuousAt (x := ((0 : ℝ), a))).tendsto.comp hpair
      have h2 : Tendsto (fun k : ℕ => L (p (φ k)).1 - D (s (φ k)) (p (φ k)).2) atTop
          (nhds (0 : E)) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards with k
        exact (sub_eq_zero.mpr (mem_meetBox.mp (hp (φ k))).2.2).symm
      exact tendsto_nhds_unique h1 h2
    have hLa : L a.1 = D 0 a.2 := sub_eq_zero.mp hzero
    have hamem : a ∈ meetBox L (D 0) := ⟨ha.1, ha.2, hLa⟩
    have hfar' : ∀ k, δ ⟨a, hamem⟩ ≤ ‖p (φ k) - a‖ := fun k => by
      simpa using hfar (φ k) ⟨a, hamem⟩
    have hev : ∀ᶠ k in atTop, ‖p (φ k) - a‖ < δ ⟨a, hamem⟩ :=
      hpt.eventually (Metric.ball_mem_nhds a (hδ ⟨a, hamem⟩))
    obtain ⟨k, hk⟩ := hev.exists
    exact absurd hk (not_lt.mpr (hfar' k))
  obtain ⟨ε, hε, hval⟩ := key
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with s hs
  refine hval s ?_
  have : dist s 0 < ε := by simpa [Metric.mem_ball] using hs
  rwa [Real.dist_eq, sub_zero] at this

/-- **The number of distinct loop points at which a loop meets a `3`-chain is locally constant**, at
*every* configuration whose meets are finite and transverse, the chain's image being covered by the box
(`hbox`) and the loop being embedded modulo its period (`hper`, `hinj`).

Compared with `Work.Drive.meetPt_ncard_eq_of_regular` there is no interiority hypothesis: the loop's
seam `t = 0 ≡ 1` and the chain's box seam are both quotients, and both are handled *geometrically* —
the seam meet is the same geometric point before and after, so it does not change the count. -/
theorem meetPt_ncard_eq_of_regular_embedded {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (L : ℝ → E) (D : ℝ → EuclideanSpace ℝ (Fin 3) → E)
    (hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) L)
    (hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => D q.1 q.2))
    (hper : ∀ s : ℝ, L (s + 1) = L s)
    (hbox : ∀ (u : ℝ) (x : EuclideanSpace ℝ (Fin 3)),
      ∃ x' ∈ Submission.Drive.unitBox 2, D u x' = D u x)
    (hfin : (Work.Drive.meetBox L (D 0)).Finite)
    (hdim : Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin 3)) = Module.finrank ℝ E)
    (hreg : ∀ p : ℝ × EuclideanSpace ℝ (Fin 3), p ∈ Work.Drive.meetBox L (D 0) →
      Function.Surjective
        (fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => L q.1 - D 0 q.2) p))
    (hinj : ∀ p : ℝ × EuclideanSpace ℝ (Fin 3), p ∈ Work.Drive.meetBox L (D 0) →
      ∀ q : ℝ × EuclideanSpace ℝ (Fin 3), q ∈ Work.Drive.meetBox L (D 0) →
      L p.1 = L q.1 → D 0 p.2 = D 0 q.2 →
      (∃ k : ℤ, q.1 = p.1 + (k : ℝ)) ∧ q.2 = p.2) :
    ∀ᶠ u in nhds (0 : ℝ),
      (Set.range (fun p : Work.Drive.meetBox L (D u) => L p.1.1)).ncard =
        (Set.range (fun p : Work.Drive.meetBox L (D 0) => L p.1.1)).ncard := by
  classical
  haveI : Finite ↥(Work.Drive.meetBox L (D 0)) := hfin.to_subtype
  -- ## 1. the periodicity of `L` in integer form, and its normalisation by `Int.fract`
  have hperP : Function.Periodic L 1 := hper
  have hperInt : ∀ (k : ℤ) (t : ℝ), L (t + (k : ℝ)) = L t := by
    intro k t
    simpa using hperP.int_mul k t
  have hLfract : ∀ t : ℝ, L (Int.fract t) = L t := by
    intro t
    have h := hperInt ⌊t⌋ (Int.fract t)
    have h2 : Int.fract t + ((⌊t⌋ : ℤ) : ℝ) = t := Int.fract_add_floor t
    rw [h2] at h
    exact h.symm
  -- ## 2. the local solution of the family at every base meet
  have hloc : ∀ ξ : ↥(Work.Drive.meetBox L (D 0)),
      ∃ (ε δ : ℝ) (ψ : ℝ → ℝ × EuclideanSpace ℝ (Fin 3)),
        0 < ε ∧ 0 < δ ∧ ψ 0 = ξ.1 ∧ Tendsto ψ (nhds (0 : ℝ)) (nhds ξ.1) ∧
        (∀ s, |s| < ε → ‖ψ s - ξ.1‖ < δ ∧ L (ψ s).1 - D s (ψ s).2 = 0) ∧
        (∀ s, |s| < ε → ∀ x, ‖x - ξ.1‖ < δ → L x.1 - D s x.2 = 0 → x = ψ s) := by
    intro ξ
    have hG : ContDiff ℝ Ctop
        (fun p : ℝ × (ℝ × EuclideanSpace ℝ (Fin 3)) => L p.2.1 - D p.1 p.2.2) := by fun_prop
    have hξ0 : (fun x : ℝ × EuclideanSpace ℝ (Fin 3) => L x.1 - D 0 x.2) ξ.1 = 0 :=
      sub_eq_zero.mpr (mem_meetBox.mp ξ.2).2.2
    exact exists_local_solution_of_surjective (fun s x => L x.1 - D s x.2) hG hdim hξ0
      (hreg ξ.1 ξ.2)
  choose ε₀ δ₀ ψ₀ hε₀ hδ₀ hψ₀ hcont₀ hmain₀ huniq₀ using hloc
  -- ## 3. the eventual properties of the family of branches
  have hEv1 : ∀ᶠ s in nhds (0 : ℝ), ∀ ξ : ↥(Work.Drive.meetBox L (D 0)), |s| < ε₀ ξ := by
    rw [Filter.eventually_all]
    intro ξ
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (hε₀ ξ)] with s hs
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
    exact hs
  have hEv2 : ∀ᶠ s in nhds (0 : ℝ), ∀ p : ↥(Work.Drive.meetBox L (D 0)) ×
      ↥(Work.Drive.meetBox L (D 0)), ‖ψ₀ p.1 s - p.1.1‖ < min (δ₀ p.1) (δ₀ p.2) := by
    rw [Filter.eventually_all]
    intro p
    have hpos : 0 < min (δ₀ p.1) (δ₀ p.2) := lt_min (hδ₀ p.1) (hδ₀ p.2)
    filter_upwards [(hcont₀ p.1).eventually (Metric.ball_mem_nhds p.1.1 hpos)] with s hs
    simpa [dist_eq_norm] using hs
  have hEv3 : ∀ᶠ s in nhds (0 : ℝ), ∀ p : ↥(Work.Drive.meetBox L (D 0)) ×
      ↥(Work.Drive.meetBox L (D 0)),
      L p.1.1.1 ≠ L p.2.1.1 → L (ψ₀ p.1 s).1 ≠ L (ψ₀ p.2 s).1 := by
    rw [Filter.eventually_all]
    intro p
    by_cases hp : L p.1.1.1 = L p.2.1.1
    · exact Eventually.of_forall fun s h => absurd hp h
    · have hfst : Tendsto (fun s : ℝ => (ψ₀ p.1 s).1) (nhds (0 : ℝ)) (nhds p.1.1.1) :=
        (continuous_fst.continuousAt.tendsto).comp (hcont₀ p.1)
      have hsnd : Tendsto (fun s : ℝ => (ψ₀ p.2 s).1) (nhds (0 : ℝ)) (nhds p.2.1.1) :=
        (continuous_fst.continuousAt.tendsto).comp (hcont₀ p.2)
      have h1 : Tendsto (fun s : ℝ => L (ψ₀ p.1 s).1) (nhds (0 : ℝ)) (nhds (L p.1.1.1)) :=
        (hL.continuous.tendsto p.1.1.1).comp hfst
      have h2 : Tendsto (fun s : ℝ => L (ψ₀ p.2 s).1) (nhds (0 : ℝ)) (nhds (L p.2.1.1)) :=
        (hL.continuous.tendsto p.2.1.1).comp hsnd
      have hsub := h1.sub h2
      have hne : L p.1.1.1 - L p.2.1.1 ≠ 0 := sub_ne_zero.mpr hp
      filter_upwards [hsub.eventually_ne hne] with s hs
      exact fun _ => sub_ne_zero.mp hs
  -- ## 4. the compactness cover
  have hcont : Continuous
      (fun q : ℝ × (ℝ × EuclideanSpace ℝ (Fin 3)) => L q.2.1 - D q.1 q.2.2) := by fun_prop
  have hcover : ∀ᶠ s in nhds (0 : ℝ), ∀ p ∈ Work.Drive.meetBox L (D s),
      ∃ ξ : ↥(Work.Drive.meetBox L (D 0)), ‖p - ξ.1‖ < δ₀ ξ / 2 :=
    eventually_meetBox_cover_noInterior hcont (fun ξ => by linarith [hδ₀ ξ])
  -- ## 5. the assembly
  filter_upwards [hEv1, hEv2, hEv3, hcover] with s hs1 hs2 hs3 hscover
  have hrange : Set.range (fun p : ↥(Work.Drive.meetBox L (D s)) => L p.1.1) =
      Set.range (fun ξ : ↥(Work.Drive.meetBox L (D 0)) => L (ψ₀ ξ s).1) := by
    ext v
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨ξ, hξ⟩ := hscover p.1 p.2
      have hp : p.1 = ψ₀ ξ s := huniq₀ ξ s (hs1 ξ) p.1
        (lt_of_lt_of_le hξ (by linarith [hδ₀ ξ]))
        (sub_eq_zero.mpr (mem_meetBox.mp p.2).2.2)
      exact ⟨ξ, by show L (ψ₀ ξ s).1 = L p.1.1; rw [← hp]⟩
    · rintro ⟨ξ, rfl⟩
      obtain ⟨x', hx'mem, hx'⟩ := hbox s (ψ₀ ξ s).2
      have hmeet : L (ψ₀ ξ s).1 = D s (ψ₀ ξ s).2 := sub_eq_zero.mp (hmain₀ ξ s (hs1 ξ)).2
      refine ⟨⟨(Int.fract (ψ₀ ξ s).1, x'), ?_⟩, hLfract (ψ₀ ξ s).1⟩
      rw [mem_meetBox]
      exact ⟨⟨Int.fract_nonneg _, le_of_lt (Int.fract_lt_one _)⟩, hx'mem,
        (hLfract (ψ₀ ξ s).1).trans (hmeet.trans hx'.symm)⟩
  have hfib : ∀ ξ η : ↥(Work.Drive.meetBox L (D 0)),
      (L (ψ₀ ξ s).1 = L (ψ₀ η s).1 ↔ L ξ.1.1 = L η.1.1) := by
    intro ξ η
    constructor
    · intro h
      by_contra hne
      exact hs3 (ξ, η) hne h
    · intro h
      have hD0 : D 0 ξ.1.2 = D 0 η.1.2 := by
        rw [← (mem_meetBox.mp ξ.2).2.2, h, (mem_meetBox.mp η.2).2.2]
      obtain ⟨⟨k, hk⟩, hx2⟩ := hinj ξ.1 ξ.2 η.1 η.2 h hD0
      have hnorm : ψ₀ ξ s + ((k : ℝ), (0 : EuclideanSpace ℝ (Fin 3))) - η.1 = ψ₀ ξ s - ξ.1 := by
        ext <;> simp [hk, hx2] <;> ring
      have hsol : L (ψ₀ ξ s + ((k : ℝ), (0 : EuclideanSpace ℝ (Fin 3)))).1 -
          D s (ψ₀ ξ s + ((k : ℝ), (0 : EuclideanSpace ℝ (Fin 3)))).2 = 0 := by
        have e1 : (ψ₀ ξ s + ((k : ℝ), (0 : EuclideanSpace ℝ (Fin 3)))).1 = (ψ₀ ξ s).1 + (k : ℝ) :=
          rfl
        have e2 : (ψ₀ ξ s + ((k : ℝ), (0 : EuclideanSpace ℝ (Fin 3)))).2 = (ψ₀ ξ s).2 := by simp
        rw [e1, e2, hperInt k (ψ₀ ξ s).1]
        exact (hmain₀ ξ s (hs1 ξ)).2
      have hshift : ψ₀ ξ s + ((k : ℝ), (0 : EuclideanSpace ℝ (Fin 3))) = ψ₀ η s :=
        huniq₀ η s (hs1 η) _ (by rw [hnorm]; exact lt_of_lt_of_le (hs2 (ξ, η)) (min_le_right _ _))
          hsol
      have hval : L (ψ₀ η s).1 = L (ψ₀ ξ s).1 := by
        rw [← hshift]
        show L (ψ₀ ξ s + ((k : ℝ), (0 : EuclideanSpace ℝ (Fin 3)))).1 = L (ψ₀ ξ s).1
        rw [show (ψ₀ ξ s + ((k : ℝ), (0 : EuclideanSpace ℝ (Fin 3)))).1 =
          (ψ₀ ξ s).1 + (k : ℝ) from rfl, hperInt k (ψ₀ ξ s).1]
      exact hval.symm
  rw [hrange]
  exact ncard_range_eq_of_fiber (fun ξ η => hfib ξ η)

end

end Work.Drive
