import Mathlib
import Submission.Work.Drive.meetBoxEngine
import Submission.Work.Drive.T6GenAtDefs
import Submission.Work.Drive.goodPair_pertChart_isOpen

/-!
# The meet-box clauses: from a base parameter to a neighbourhood

The design's transport bundle `Work.Drive.T6GenAtDBox` contains two clauses which quantify over the
*parameter-dependent* meet set `coreMeet Q_t c P_t`:

> `∀ q ∈ coreMeet Q_t c P_t, <condition at q>`

(one with `<condition>` = `GoodLoopChain (diamLoop Q_t q.1) (sweep_t)`, one with `<condition>` =
`DiamFamRegBox ...`).  The meet set moves with the parameter `t`, so the conjunction over it is *not* a
pointwise condition; the way to prove that such a clause is open is

* the **compactness cover** `Work.Drive.eventually_meetBox_cover_par_diag`: every meet at a nearby
  parameter is close to a meet at the base parameter (the meet set is upper semicontinuous),
* together with the **pointwise openness** of the condition, at each *base* meet, *as a function of the
  parameter and of the loop's angle*.

This file contains the two generic lemmas performing that combination:

* `Work.Drive.eventually_forall_meetBox_of_eventually` — the abstract statement: for a family
  `(L p, D p)` of loops/chains with `(p, q) ↦ (L p q.1, D p q.2)` continuous, if a predicate
  `Prop p θ` (θ = the loop's angle) is a neighbourhood property at every base meet, then the
  `∀ q ∈ meetBox (L p) (D p)` clause holds for `p` near the base parameter;
* `Work.Drive.eventually_good_meetBox_at` — the base point form of
  `Work.Drive.eventually_good_meetBox` (which is stated at the parameter `0`).

Both are sorry-free.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- **A meet-box clause is a neighbourhood property of the parameter.**  Let `(L p, D p)` be a family
of loops (`L p : ℝ → CappingSpace`) and of `3`-chains (`D p : 𝔼³ → CappingSpace`), continuous in the
pair `(p, q) ↦ (L p q.1, D p q.2)`.  If a predicate `Prop p θ` of the parameter and of the *loop angle*
holds in a neighbourhood of `(p₀, ξ.1)` for every base meet `ξ ∈ meetBox (L p₀) (D p₀)`, then the
clause `∀ q ∈ meetBox (L p) (D p), R p q.1` holds for all `p` near `p₀`.

The proof is the standard compactness/contradiction argument: a sequence `p n → p₀` violating the
clause produces meet points `q n` in the compact box, whose subsequential limit is a meet at `p₀`, at
which `Prop` is eventually true — contradicting the violation.  The base meet set need not be finite. -/
theorem eventually_forall_meetBox_of_eventually (p₀ : P)
    {L : P → ℝ → CappingSpace} {D : P → EuclideanSpace ℝ (Fin 3) → CappingSpace}
    (hc : Continuous (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => (L q.1 q.2.1, D q.1 q.2.2)))
    (R : P → ℝ → Prop)
    (hprop : ∀ ξ ∈ meetBox (L p₀) (D p₀), ∀ᶠ z in 𝓝 ((p₀, ξ.1) : P × ℝ), R z.1 z.2) :
    ∀ᶠ p in 𝓝 p₀, ∀ q ∈ meetBox (L p) (D p), R p q.1 := by
  classical
  rw [Metric.eventually_nhds_iff]
  by_contra hcon
  push_neg at hcon
  have hseq : ∀ n : ℕ, ∃ x : P, dist x p₀ < 1 / ((n : ℝ) + 1) ∧
      ∃ q : ℝ × EuclideanSpace ℝ (Fin 3), q ∈ meetBox (L x) (D x) ∧ ¬ R x q.1 :=
    fun n => hcon (1 / ((n : ℝ) + 1)) (by positivity)
  choose p hp using hseq
  choose q hq using fun n => (hp n).2
  -- the parameters converge to `p₀`
  have hpt : Tendsto p atTop (𝓝 p₀) := by
    have hsub : Tendsto (fun n : ℕ => p n - p₀) atTop (𝓝 (0 : P)) := by
      refine squeeze_zero_norm' (a := fun n : ℕ => 1 / ((n : ℝ) + 1)) (Eventually.of_forall ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      intro n
      rw [← dist_eq_norm]
      exact le_of_lt (hp n).1
    have h2 : Tendsto (fun n : ℕ => (p n - p₀) + p₀) atTop (𝓝 ((0 : P) + p₀)) :=
      hsub.add tendsto_const_nhds
    simpa using h2
  -- the meet points lie in the compact box: extract a convergent subsequence
  have hqbox : ∀ n : ℕ, q n ∈ Set.Icc (0 : ℝ) 1 ×ˢ Submission.Drive.unitBox 2 := fun n =>
    ⟨(mem_meetBox.mp (hq n).1).1, (mem_meetBox.mp (hq n).1).2.1⟩
  obtain ⟨a, ha, φ, hφ, hqa⟩ :=
    (isCompact_Icc.prod (isCompact_unitBox 2)).tendsto_subseq hqbox
  have hpφ : Tendsto (fun k : ℕ => p (φ k)) atTop (𝓝 p₀) := hpt.comp hφ.tendsto_atTop
  -- the limit point is a meet at the base parameter
  have hpair : Tendsto (fun k : ℕ => (p (φ k), q (φ k))) atTop (𝓝 (p₀, a)) :=
    hpφ.prodMk_nhds hqa
  have hLa : L p₀ a.1 = D p₀ a.2 := by
    have h1 : Tendsto (fun k : ℕ => L (p (φ k)) (q (φ k)).1) atTop (𝓝 (L p₀ a.1)) :=
      ((continuous_fst.comp hc).continuousAt (x := (p₀, a))).tendsto.comp hpair
    have h2 : Tendsto (fun k : ℕ => D (p (φ k)) (q (φ k)).2) atTop (𝓝 (D p₀ a.2)) :=
      ((continuous_snd.comp hc).continuousAt (x := (p₀, a))).tendsto.comp hpair
    have h3 : (fun k : ℕ => D (p (φ k)) (q (φ k)).2)
        = fun k : ℕ => L (p (φ k)) (q (φ k)).1 := by
      funext k
      exact (mem_meetBox.mp (hq (φ k)).1).2.2.symm
    exact tendsto_nhds_unique h1 (h3 ▸ h2)
  have hamem : a ∈ meetBox (L p₀) (D p₀) := ⟨ha.1, ha.2, hLa⟩
  -- but the predicate holds eventually near that base meet, and the pair converges to it
  have hev : ∀ᶠ z in 𝓝 ((p₀, a.1) : P × ℝ), R z.1 z.2 := hprop a hamem
  have hpair2 : Tendsto (fun k : ℕ => ((p (φ k), (q (φ k)).1) : P × ℝ)) atTop
      (𝓝 ((p₀, a.1) : P × ℝ)) := by
    have hcont : Continuous (fun z : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => (z.1, z.2.1)) := by
      fun_prop
    exact (hcont.tendsto (p₀, a)).comp hpair
  obtain ⟨k, hk⟩ := (hpair2.eventually hev).exists
  exact (hq (φ k)).2 hk

/-- **The base-point form of `Work.Drive.eventually_good_meetBox`**: goodness of the meet set of a
loop/chain family is a *neighbourhood* property of the family parameter (the original statement is at
the parameter `0`; here the base parameter is arbitrary). -/
theorem eventually_good_meetBox_at [FiniteDimensional ℝ P] (p₀ : P)
    (L : P → ℝ → CappingSpace) (D : P → EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (hL : ContMDiff (𝓘(ℝ, P × ℝ)) (𝓡 4) Ctop (fun q : P × ℝ => L q.1 q.2))
    (hD : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 3) => D q.1 q.2))
    (h : GoodLoopChain (L p₀) (D p₀)) :
    ∀ᶠ p in 𝓝 p₀, GoodLoopChain (L p) (D p) := by
  have hL' : ContMDiff (𝓘(ℝ, P × ℝ)) (𝓡 4) Ctop
      (fun q : P × ℝ => L (p₀ + q.1) q.2) := by
    have hs : ContMDiff (𝓘(ℝ, P × ℝ)) (𝓘(ℝ, P × ℝ)) Ctop (fun q : P × ℝ => (p₀ + q.1, q.2)) := by
      rw [contMDiff_iff_contDiff]
      fun_prop
    exact hL.comp hs
  have hD' : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 3) => D (p₀ + q.1) q.2) := by
    have hs : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3)))
        (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3))) Ctop
        (fun q : P × EuclideanSpace ℝ (Fin 3) => (p₀ + q.1, q.2)) := by
      rw [contMDiff_iff_contDiff]
      fun_prop
    exact hD.comp hs
  have hbase : GoodLoopChain (L (p₀ + 0)) (D (p₀ + 0)) := by simpa using h
  have hev := eventually_good_meetBox (P := P) (fun u : P => L (p₀ + u))
    (fun u : P => D (p₀ + u)) hL' hD' hbase.1 hbase.2.1 hbase.2.2
  have htend : Tendsto (fun p : P => p - p₀) (𝓝 p₀) (𝓝 (0 : P)) := by
    simpa using (continuous_sub_right p₀).tendsto p₀
  refine (htend.eventually hev).mono fun p hp => ?_
  have : p₀ + (p - p₀) = p := by abel
  rwa [this] at hp

end

end Work.Drive
