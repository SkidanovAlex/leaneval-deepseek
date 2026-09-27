import Mathlib
import Submission.Work.Drive.localConstancy_oneThree
import Submission.Work.Drive.Interfaces

/-!
# The meet count of a loop with a `3`-chain: the local constancy engine

The design's side value (`Submission/Work/Drive/sideCountDefs.lean`) is the parity of the number of
meets of a *loop* (`coreLoop Q`, `1` parameter) with a *`3`-chain* (the clamped sweep, `3` parameters)
in the `4`-manifold `CappingSpace`:

> `coreSideCount Q c P = #(coreMeet Q c P)`,  `coreMeet ⊆ [0,1] × unitBox 2`.

The parameter box is `4`-dimensional, so generic meets are *isolated* points.  This file provides the
analytic engine that makes the parity of that count **locally constant in a deformation parameter**:
if at the base parameter every meet is *interior* in the box and *regular* (the derivative of the
difference map is surjective — the system being square, bijective), then the number of meets is
constant for nearby parameters.

It is the `(1,3)`-dimensional analogue of the arc engine `Work.Drive.eventually_ncard_meetI_eq`
(`Submission/Work/Drive/arcMeet.lean`), and it is proved the same way (implicit function theorem for
the square family `Work.Drive.exists_local_solution_of_surjective`, separation of the finite base meet
set, compactness cover of the box).  Its *use* by the chain route requires the meets to avoid the box
faces: see `Submission/Work/Drive/HN4_SEAM_DEFECT.md` for why (the box parametrisation counts the loop
seam and the chain seam twice, and the interiority hypothesis is exactly what excludes that).
-/

namespace Work.Drive

open Filter
open scoped Topology ContDiff

noncomputable section

/-- **The meet set of a loop with a `3`-chain** over the parameter box `[0,1] × unitBox 2`. -/
def meetBox {E : Type*} (L : ℝ → E) (D : EuclideanSpace ℝ (Fin 3) → E) :
    Set (ℝ × EuclideanSpace ℝ (Fin 3)) :=
  {p | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ Submission.Drive.unitBox 2 ∧ L p.1 = D p.2}

@[simp] lemma mem_meetBox {E : Type*} {L : ℝ → E} {D : EuclideanSpace ℝ (Fin 3) → E}
    {p : ℝ × EuclideanSpace ℝ (Fin 3)} :
    p ∈ meetBox L D ↔ p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ Submission.Drive.unitBox 2 ∧
      L p.1 = D p.2 :=
  Iff.rfl

/-- The dimension of the parameter box `ℝ × ℝ³` is `4`. -/
lemma finrank_prod_fin3 : Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin 3)) = 4 := by
  rw [Module.finrank_prod, finrank_euclideanSpace_fin]
  norm_num

/-- **Upper semicontinuity of the loop-vs-chain meet set.**  With the *closed* box, for `s → 0` every
meet point of `D s` is close to a meet point of `D 0`; the interiority hypothesis rules out the box
boundary. -/
theorem eventually_meetBox_cover {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : ℝ → E} {D : ℝ → EuclideanSpace ℝ (Fin 3) → E}
    (hcont : Continuous (fun q : ℝ × (ℝ × EuclideanSpace ℝ (Fin 3)) => L q.2.1 - D q.1 q.2.2))
    (hint : ∀ p : ℝ × EuclideanSpace ℝ (Fin 3), p.1 ∈ Set.Icc (0 : ℝ) 1 →
      p.2 ∈ Submission.Drive.unitBox 2 → L p.1 = D 0 p.2 →
      p.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ ∀ i : Fin 3, p.2 i ∈ Set.Ioo (0 : ℝ) 1)
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

/-- A radius in which both coordinates of the box stay in the *closed* box, from the strict
interiority of a point. -/
theorem exists_box_radius (ξ : ℝ × EuclideanSpace ℝ (Fin 3))
    (h1 : ξ.1 ∈ Set.Ioo (0 : ℝ) 1) (h2 : ∀ i : Fin 3, ξ.2 i ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ × EuclideanSpace ℝ (Fin 3), ‖x - ξ‖ < r →
      x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ x.2 ∈ Submission.Drive.unitBox 2 := by
  set S : Finset ℝ := {ξ.1, 1 - ξ.1, ξ.2 0, 1 - ξ.2 0, ξ.2 1, 1 - ξ.2 1, ξ.2 2, 1 - ξ.2 2}
    with hSdef
  have hmem : ∀ y ∈ S, 0 < y := by
    intro y hy
    rw [hSdef] at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1.1
    · linarith [h1.2]
    · exact (h2 0).1
    · linarith [(h2 0).2]
    · exact (h2 1).1
    · linarith [(h2 1).2]
    · exact (h2 2).1
    · linarith [(h2 2).2]
  have hne : S.Nonempty := ⟨ξ.1, by rw [hSdef]; simp⟩
  set m : ℝ := S.min' hne with hmdef
  have hmpos : 0 < m := by
    rw [hmdef]
    exact hmem _ (Finset.min'_mem S hne)
  have hle : ∀ y ∈ S, m ≤ y := fun y hy => by
    rw [hmdef]; exact Finset.min'_le S y hy
  have hhalf : m / 2 ≤ m := by linarith
  refine ⟨m / 2, by linarith, ?_⟩
  intro x hx
  have hfst : |x.1 - ξ.1| ≤ ‖x - ξ‖ := by simpa using norm_fst_le (x - ξ)
  have hsnd : ‖x.2 - ξ.2‖ ≤ ‖x - ξ‖ := by simpa using norm_snd_le (x - ξ)
  have hb1 : |x.1 - ξ.1| < m / 2 := lt_of_le_of_lt hfst hx
  have hb1' := abs_lt.mp hb1
  have h1m : m ≤ ξ.1 := hle ξ.1 (by rw [hSdef]; simp)
  have h2m : m ≤ 1 - ξ.1 := hle (1 - ξ.1) (by rw [hSdef]; simp)
  refine ⟨⟨by linarith [hb1'.1, h1m, hhalf], by linarith [hb1'.2, h2m, hhalf]⟩, ?_⟩
  intro i
  have hcoord : |x.2 i - ξ.2 i| ≤ ‖x.2 - ξ.2‖ := by
    simpa using PiLp.norm_apply_le (p := 2) (x.2 - ξ.2) i
  have hbi : |x.2 i - ξ.2 i| < m / 2 := lt_of_le_of_lt (le_trans hcoord hsnd) hx
  have hbi' := abs_lt.mp hbi
  have h3m : m ≤ ξ.2 i := by
    fin_cases i
    · exact hle (ξ.2 0) (by rw [hSdef]; simp)
    · exact hle (ξ.2 1) (by rw [hSdef]; simp)
    · exact hle (ξ.2 2) (by rw [hSdef]; simp)
  have h4m : m ≤ 1 - ξ.2 i := by
    fin_cases i
    · exact hle (1 - ξ.2 0) (by rw [hSdef]; simp)
    · exact hle (1 - ξ.2 1) (by rw [hSdef]; simp)
    · exact hle (1 - ξ.2 2) (by rw [hSdef]; simp)
  exact ⟨by linarith [hbi'.1, h3m, hhalf], by linarith [hbi'.2, h4m, hhalf]⟩

/-- **The loop-vs-`3`-chain engine: local constancy of the number of meets.**  `L` is a loop (a curve
of the model space, `1` parameter), each `D s` a `3`-chain (three parameters), `(s,q) ↦ L q.1 − D s q.2`
is smooth, the meet set of `D 0` is finite, every meet point of `D 0` is *interior* in the box (both
the loop parameter and all three chain parameters strictly inside) and *regular* (the derivative of the
difference map at the meet is surjective; the box and the target having the same dimension, this is the
transversality of the loop with the chain).  Then the number of meet points is constant for `s` near
`0`. -/
theorem eventually_ncard_meetBox_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (L : ℝ → E) (D : ℝ → EuclideanSpace ℝ (Fin 3) → E)
    (hL : ContDiff ℝ Ctop L)
    (hD : ContDiff ℝ Ctop (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => D q.1 q.2))
    (hfin : (meetBox L (D 0)).Finite)
    (hint : ∀ p : ℝ × EuclideanSpace ℝ (Fin 3), p.1 ∈ Set.Icc (0 : ℝ) 1 →
      p.2 ∈ Submission.Drive.unitBox 2 → L p.1 = D 0 p.2 →
      p.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ ∀ i : Fin 3, p.2 i ∈ Set.Ioo (0 : ℝ) 1)
    (hdim : Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin 3)) = Module.finrank ℝ E)
    (hreg : ∀ p : ℝ × EuclideanSpace ℝ (Fin 3), p.1 ∈ Set.Icc (0 : ℝ) 1 →
      p.2 ∈ Submission.Drive.unitBox 2 → L p.1 = D 0 p.2 →
      Function.Surjective
        (fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => L q.1 - D 0 q.2) p)) :
    ∀ᶠ s in nhds (0 : ℝ),
      (meetBox L (D s)).ncard = (meetBox L (D 0)).ncard := by
  classical
  have hG : ContDiff ℝ Ctop
      (fun q : ℝ × (ℝ × EuclideanSpace ℝ (Fin 3)) => L q.2.1 - D q.1 q.2.2) := by fun_prop
  haveI : Finite (meetBox L (D 0)) := hfin.to_subtype
  haveI : Fintype (meetBox L (D 0)) := hfin.fintype
  -- local solutions at each meet of the base chain
  have hloc : ∀ ξ : meetBox L (D 0), ∃ (ε δ : ℝ) (ψ : ℝ → ℝ × EuclideanSpace ℝ (Fin 3)),
      0 < ε ∧ 0 < δ ∧ ψ 0 = ξ.1 ∧ Tendsto ψ (nhds (0 : ℝ)) (nhds ξ.1) ∧
      (∀ s, |s| < ε → ‖ψ s - ξ.1‖ < δ ∧ L (ψ s).1 - D s (ψ s).2 = 0) ∧
      (∀ s, |s| < ε → ∀ x, ‖x - ξ.1‖ < δ → L x.1 - D s x.2 = 0 → x = ψ s) := by
    intro ξ
    have hξ0 : (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => L q.1 - D 0 q.2) ξ.1 = 0 :=
      sub_eq_zero.mpr ξ.2.2.2
    exact exists_local_solution_of_surjective (fun s q => L q.1 - D s q.2) hG hdim hξ0
      (hreg ξ.1 ξ.2.1 ξ.2.2.1 ξ.2.2.2)
  choose ε₀ δ₀ ψ₀ hε₀ hδ₀ hψ₀ hcont₀ hmain₀ huniq₀ using hloc
  obtain ⟨ρ, hρpos, hρ⟩ := exists_pos_le_dist_of_finite hfin
  -- a radius inside the *open* box at each meet point
  have hff : ∀ ξ : meetBox L (D 0), ∃ r : ℝ, 0 < r ∧
      ∀ x : ℝ × EuclideanSpace ℝ (Fin 3), ‖x - ξ.1‖ < r →
        x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ x.2 ∈ Submission.Drive.unitBox 2 :=
    fun ξ => exists_box_radius ξ.1 (hint ξ.1 ξ.2.1 ξ.2.2.1 ξ.2.2.2).1
      (hint ξ.1 ξ.2.1 ξ.2.2.1 ξ.2.2.2).2
  choose rf hrfpos hrf using hff
  set δZ : meetBox L (D 0) → ℝ := fun ξ => min (δ₀ ξ) (min (rf ξ) ρ) with hδZdef
  have hδZval : ∀ ξ, δZ ξ = min (δ₀ ξ) (min (rf ξ) ρ) := fun ξ => rfl
  have hδZpos : ∀ ξ, 0 < δZ ξ := by
    intro ξ; rw [hδZval]; exact lt_min (hδ₀ ξ) (lt_min (hrfpos ξ) hρpos)
  have hδZ_le_δ₀ : ∀ ξ, δZ ξ ≤ δ₀ ξ := fun ξ =>
    (le_of_eq (hδZval ξ)).trans (min_le_left _ _)
  have hδZ_le_rf : ∀ ξ, δZ ξ ≤ rf ξ := fun ξ =>
    (le_of_eq (hδZval ξ)).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδZ_le_ρ : ∀ ξ, δZ ξ ≤ ρ := fun ξ =>
    (le_of_eq (hδZval ξ)).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hevA : ∀ᶠ s in nhds (0 : ℝ), ∀ ξ : meetBox L (D 0),
      ‖ψ₀ ξ s - ξ.1‖ < δZ ξ ∧ L (ψ₀ ξ s).1 - D s (ψ₀ ξ s).2 = 0 := by
    rw [Filter.eventually_all]
    intro ξ
    have h1 : ∀ᶠ s in nhds (0 : ℝ), |s| < ε₀ ξ := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (hε₀ ξ)] with s hs
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
      exact hs
    have h2 : ∀ᶠ s in nhds (0 : ℝ), ‖ψ₀ ξ s - ξ.1‖ < δZ ξ := by
      have hc := (hcont₀ ξ).eventually (Metric.ball_mem_nhds ξ.1 (hδZpos ξ))
      filter_upwards [hc] with s hs
      simpa [dist_eq_norm] using hs
    filter_upwards [h1, h2] with s hs1 hs2
    exact ⟨hs2, (hmain₀ ξ s hs1).2⟩
  have hevB : ∀ᶠ s in nhds (0 : ℝ), ∀ p ∈ meetBox L (D s),
      ∃ ξ : meetBox L (D 0), ‖p - ξ.1‖ < δZ ξ :=
    eventually_meetBox_cover hG.continuous hint hδZpos
  have hevC : ∀ᶠ s in nhds (0 : ℝ), ∀ ξ : meetBox L (D 0),
      ∀ x : ℝ × EuclideanSpace ℝ (Fin 3), ‖x - ξ.1‖ < δZ ξ →
      L x.1 - D s x.2 = 0 → x = ψ₀ ξ s := by
    rw [Filter.eventually_all]
    intro ξ
    have h1 : ∀ᶠ s in nhds (0 : ℝ), |s| < ε₀ ξ := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (hε₀ ξ)] with s hs
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
      exact hs
    filter_upwards [h1] with s hs1 x hx hx0
    exact huniq₀ ξ s hs1 x (lt_of_lt_of_le hx (hδZ_le_δ₀ ξ)) hx0
  filter_upwards [hevA, hevB, hevC] with s hA hB hC
  set Ψ : meetBox L (D 0) → ℝ × EuclideanSpace ℝ (Fin 3) := fun ξ => ψ₀ ξ s with hΨdef
  have hΨval : ∀ ξ : meetBox L (D 0), Ψ ξ = ψ₀ ξ s := fun ξ => rfl
  have hΨmem : ∀ ξ : meetBox L (D 0), Ψ ξ ∈ meetBox L (D s) := by
    intro ξ
    have hfr := hrf ξ (Ψ ξ) (lt_of_lt_of_le (hA ξ).1 (hδZ_le_rf ξ))
    exact ⟨hfr.1, hfr.2, sub_eq_zero.mp (hA ξ).2⟩
  have hΨinj : Function.Injective Ψ := by
    intro ξ η hξη
    by_contra hne
    have hd : ξ.1 ≠ η.1 := fun h => hne (Subtype.ext h)
    have h1 : ‖Ψ ξ - ξ.1‖ < δZ ξ := (hA ξ).1
    have h2 : ‖Ψ η - η.1‖ < δZ η := (hA η).1
    have h3 : 2 * ρ ≤ ‖ξ.1 - η.1‖ := hρ ξ.1 ξ.2 η.1 η.2 hd
    have h4 : ‖ξ.1 - η.1‖ ≤ ‖Ψ ξ - ξ.1‖ + ‖Ψ η - η.1‖ := by
      have hsub : ξ.1 - η.1 = (ξ.1 - Ψ ξ) + (Ψ ξ - η.1) := by abel
      calc ‖ξ.1 - η.1‖ = ‖(ξ.1 - Ψ ξ) + (Ψ ξ - η.1)‖ := by rw [hsub]
        _ ≤ ‖ξ.1 - Ψ ξ‖ + ‖Ψ ξ - η.1‖ := norm_add_le _ _
        _ = ‖Ψ ξ - ξ.1‖ + ‖Ψ η - η.1‖ := by rw [norm_sub_rev, hξη]
    have h5 : δZ ξ + δZ η ≤ 2 * ρ := by linarith [hδZ_le_ρ ξ, hδZ_le_ρ η]
    linarith
  have hΨsurj : ∀ x ∈ meetBox L (D s), ∃ ξ : meetBox L (D 0), Ψ ξ = x := by
    intro x hx
    obtain ⟨ξ, hdist⟩ := hB x hx
    refine ⟨ξ, ?_⟩
    rw [hΨval ξ]
    exact (hC ξ x hdist (sub_eq_zero.mpr hx.2.2)).symm
  let Φ : meetBox L (D 0) → meetBox L (D s) := fun ξ => ⟨Ψ ξ, hΨmem ξ⟩
  have hΦinj : Function.Injective Φ := by
    intro ξ η h
    exact hΨinj (congrArg Subtype.val h)
  have hΦsurj : Function.Surjective Φ := by
    intro x
    obtain ⟨ξ, hξ⟩ := hΨsurj x.1 x.2
    exact ⟨ξ, Subtype.ext hξ⟩
  have hcard : Nat.card (meetBox L (D s)) = Nat.card (meetBox L (D 0)) :=
    Nat.card_congr (Equiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩).symm
  have hfinS : Finite (meetBox L (D s)) := Finite.of_surjective Φ hΦsurj
  have hfS : (meetBox L (D s)).Finite := Set.finite_coe_iff.mp hfinS
  haveI : Fintype (meetBox L (D s)) := hfS.fintype
  have hA' : (meetBox L (D s)).ncard = Nat.card (meetBox L (D s)) := by
    rw [Set.ncard_eq_toFinset_card _ hfS, hfS.card_toFinset, Fintype.card_eq_nat_card]
  have hB' : (meetBox L (D 0)).ncard = Nat.card (meetBox L (D 0)) := by
    rw [Set.ncard_eq_toFinset_card _ hfin, hfin.card_toFinset, Fintype.card_eq_nat_card]
  exact hA'.trans (hcard.trans hB'.symm)

/-- **The parity (`ZMod 2`) form of the loop-vs-`3`-chain engine.**  This is the shape of the
locality `hn4` of the route's count. -/
theorem eventually_zmod2_ncard_meetBox_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (L : ℝ → E) (D : ℝ → EuclideanSpace ℝ (Fin 3) → E)
    (hL : ContDiff ℝ Ctop L)
    (hD : ContDiff ℝ Ctop (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => D q.1 q.2))
    (hfin : (meetBox L (D 0)).Finite)
    (hint : ∀ p : ℝ × EuclideanSpace ℝ (Fin 3), p.1 ∈ Set.Icc (0 : ℝ) 1 →
      p.2 ∈ Submission.Drive.unitBox 2 → L p.1 = D 0 p.2 →
      p.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ ∀ i : Fin 3, p.2 i ∈ Set.Ioo (0 : ℝ) 1)
    (hdim : Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin 3)) = Module.finrank ℝ E)
    (hreg : ∀ p : ℝ × EuclideanSpace ℝ (Fin 3), p.1 ∈ Set.Icc (0 : ℝ) 1 →
      p.2 ∈ Submission.Drive.unitBox 2 → L p.1 = D 0 p.2 →
      Function.Surjective
        (fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => L q.1 - D 0 q.2) p)) :
    ∀ᶠ s in nhds (0 : ℝ),
      (((meetBox L (D s)).ncard : ℕ) : ZMod 2) = (((meetBox L (D 0)).ncard : ℕ) : ZMod 2) := by
  filter_upwards [eventually_ncard_meetBox_eq L D hL hD hfin hint hdim hreg] with s hs
  rw [hs]

/-- **The meet set may be computed in a chart** (the analogue of `Work.Drive.meetI_chart` for the
`(1,3)` layout): for a chart `e` of a `4`-manifold and coordinate expressions `L'`, `D'`, the meet set
of the corresponding curves of the manifold is the *same set of parameter pairs* as the meet set of the
coordinate expressions, because `e.symm` is injective on the target. -/
theorem meetBox_chart {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 4)))
    (L' : ℝ → EuclideanSpace ℝ (Fin 4)) (D' : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hL : Set.range L' ⊆ e.target) (hD : Set.range D' ⊆ e.target) :
    meetBox (fun t : ℝ => e.symm (L' t)) (fun x => e.symm (D' x)) = meetBox L' D' := by
  ext p
  rw [mem_meetBox, mem_meetBox]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    have h := congrArg e h3
    rwa [e.right_inv (hL (Set.mem_range_self p.1)),
      e.right_inv (hD (Set.mem_range_self p.2))] at h
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by rw [h3]⟩

end

end Work.Drive
