import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.H0_path_limit
import Submission.Work.EQ.H0_structure
import Submission.Work.EQ.countable_puncture_psi1_limits
import Submission.Work.EQ.tail_uniform_of_isPreconnected
import Submission.Work.EQ.H0_tail_bounded
import Submission.Work.EQ.Refl.path_lift_component
import Submission.Work.EQ.Refl.component_projection_cocountable
import Submission.Work.EQ.tailP_dichotomy_on_preconnected
import Submission.Work.EQ.tailB_dichotomy_on_preconnected
import Submission.Work.EQ.annulus_path_avoiding_countable

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/EQ/DESIGN_LA.md (the lead's closing route for exists_compact_regular_cycle's limit_analysis; the fan-rigidity chain and la_witness route are retired).

# regComp_lift_over_annulus (1.5–3k)

**Claim.** Let `S` be a regular component and `q ∈ S` a chain over the open annulus
`r₁ < |z| < r₂`. For every `z` in the annulus outside a fixed countable set `P`, `S` has a chain
over `z` whose floored forward and backward tails equal those of `q`.

**Imports:** `Submission.Work.EQ.CycleDefs,Submission.Work.EQ.H0_path_limit,Submission.Work.EQ.H0_structure,Submission.Work.EQ.countable_puncture_psi1_limits,Submission.Work.EQ.tail_uniform_of_isPreconnected,Submission.Work.EQ.H0_tail_bounded`

**Route.**
1. **`P`** is the set of `ψ₁`-limits of genuine punctures with finite `ψ₂`-limit. It is countable
   by `countable_puncture_psi1_limits` (proved).
2. **Path lifting.** Let `T` be the connected component of `S ∩ ψ₁⁻¹(A°)` containing `q`. The set
   `A° ∖ P` is path-connected (an annulus minus a countable set). Lift a path from `ψ₁ q` to `z`:
   * the set of parameters where the lift exists is open (local sections, `H0_structure`);
   * it is closed: at the supremum, `ψ₁ → γ(t*)` and `ψ₂ = c/ψ₁` converges, so
     `H0_path_limit` (use the `Iio` form) gives convergence in `H0`, or a punctured chart. That
     chart is genuine, and its `ψ₂`-limit is finite (it is meromorphic with a finite limit along
     the path), so `γ(t*) ∈ P`, which is excluded.
3. **Floored tails are constant on `T`.** `T` is preconnected, `|ψ₁| ≤ r₂` and
   `|ψ₂| ≤ B/r₁`. The clopen argument in the proof of `tail_uniform_of_isPreconnected` shows that
   for `n ≥ n₀(r₂, B/r₁)` the property "principal from `n`" is either true on all of `T` or on none
   of it. Factor that argument out as a lemma.

**Risk: medium.** Path lifting from a maximal-lift argument is the fiddly part; `H0_path_limit_Iio`
and `Work.Covering` already contain similar arguments.

PROOF IMPLEMENTED HERE (2026-09-26).  The two analytic inputs of the sketch are the two
dichotomies `Work.EQ.tailP_dichotomy_on_preconnected` / `Work.EQ.tailB_dichotomy_on_preconnected`
(the clopen argument of `tail_uniform_of_isPreconnected`, made uniform in the base point), the
annulus path `Work.EQ.annulus_path_avoiding_countable`, and the completed path lifting
`Work.EQ.Refl.path_lift_component` (uniqueness + step-up + step-close, via `H0_path_limit_Iio`).
The obstruction set is `Work.EQ.Refl.GenuinePunctureValues a h`; the only point needing care is a
*starting* parameter outside it, which is obtained from the analytic local section at `q`
(`H0_structure`), shrunk so that its image stays in the annulus: this gives `p' = f u₁ ∈ T` with
`ψ₁ p' = u₁ ∉ P`, and the path is lifted from `p'`.  Every punctured chart has a finite
`ψ₂`-limit (`Refl.tendsto_psi2_of_isPuncturedChart`), which is what converts `z ∉ P` into the
"no genuine chart is met" hypothesis of the path-lifting theorem.  The lifted endpoint `G 1` lies
in the same component `T` of `S ∩ ψ₁⁻¹(A°)` as `q`, so the two dichotomies give the coincidence of
the floored tails.
-/

namespace Work.EQ

open Filter _root_.Topology

/-- **Chains of a regular component over every parameter of an annulus, with the same
tails.** There is a countable set `P` (the `ψ₁`-limits of genuine punctures) such that for an
open annulus `r₁ < ‖z‖ < r₂` and a bound `B` on the value, a floor `n₀` exists with the
following property. For every regular component `S` of value `c` with `‖c‖ ≤ B`, every chain
`q ∈ S` over the annulus and every `z` in the annulus outside `P`, there is a chain `q' ∈ S`
with `ψ₁ q' = z` whose forward and backward tails are principal from exactly the same depths
`≥ n₀` as those of `q`. Proof sketch: path lifting in the component of `S` over the annulus,
using `H0_path_limit`, plus the clopen argument of `tail_uniform_of_isPreconnected`. -/
theorem regComp_lift_over_annulus {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ P : Set ℂ, P.Countable ∧ ∀ {r₁ r₂ B : ℝ}, 0 < r₁ → r₁ < r₂ → ∃ n₀ : ℕ,
      ∀ {S : Set ChainData} {c : ℂ}, IsRegComp a h S c → ‖c‖ ≤ B →
      ∀ q ∈ S, r₁ < ‖q.2.1‖ → ‖q.2.1‖ < r₂ →
      ∀ z : ℂ, r₁ < ‖z‖ → ‖z‖ < r₂ → z ∉ P →
        ∃ q' ∈ S, q'.2.1 = z ∧ ∀ n : ℕ, n₀ ≤ n →
          ((∀ m : ℕ, n ≤ m → q.1 (m : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ m * q.2.1)) ↔
            (∀ m : ℕ, n ≤ m →
              q'.1 (m : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ m * q'.2.1))) ∧
          ((∀ m : ℕ, n ≤ m →
              q.1 (-(m : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ m * q.2.2)) ↔
            (∀ m : ℕ, n ≤ m →
              q'.1 (-(m : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ m * q'.2.2))) := by
  classical
  -- the obstruction set: the `ψ₁`-values of genuine punctures, with a finite `ψ₂`-limit
  obtain hcountP : (Refl.GenuinePunctureValues a h).Countable :=
    countable_puncture_psi1_limits ha0 ha1 hh
  refine ⟨Refl.GenuinePunctureValues a h, hcountP, ?_⟩
  intro r₁ r₂ B hr₁ hr₁₂
  -- the two uniform floors, one for each tail
  obtain ⟨nP, hnP⟩ :=
    tailP_dichotomy_on_preconnected ha0 ha1 hh (B := r₂) (le_of_lt (lt_trans hr₁ hr₁₂))
  obtain ⟨nB, hnB⟩ :=
    tailB_dichotomy_on_preconnected ha0 ha1 hh (B := max 0 (B / r₁)) (le_max_left _ _)
  refine ⟨max nP nB, ?_⟩
  intro S c hS hc q hqS hq₁ hq₂ z hz₁ hz₂ hzP
  -- ## the local analytic section of `ψ₁` at `q`, shrunk into the annulus
  obtain ⟨hSsub, ⟨p, hp, hSp⟩, hSval⟩ := hS
  have hqH : q ∈ H0 a h := hSsub hqS
  obtain ⟨-, hsect, -, -⟩ := H0_structure ha0 ha1 hh
  obtain ⟨ρ, hρpos, f, hf0, hfmem, hfan, hfan2, -⟩ := hsect q hqH
  have hcontf : ContinuousOn f (Metric.ball q.2.1 ρ) :=
    ContinuousOn.prodMk (continuousOn_pi' fun n => (hfan n).continuousOn)
      (ContinuousOn.prodMk (continuousOn_id.congr (fun u hu => (hfmem u hu).2))
        hfan2.continuousOn)
  set ρ' : ℝ := min ρ (min ((‖q.2.1‖ - r₁) / 2) ((r₂ - ‖q.2.1‖) / 2)) with hρ'def
  have hρ'pos : 0 < ρ' := by
    rw [hρ'def]
    exact lt_min hρpos (lt_min (by linarith) (by linarith))
  have hρ'le : ρ' ≤ ρ := by rw [hρ'def]; exact min_le_left _ _
  have hρ'₁ : ρ' ≤ (‖q.2.1‖ - r₁) / 2 := by
    rw [hρ'def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρ'₂ : ρ' ≤ (r₂ - ‖q.2.1‖) / 2 := by
    rw [hρ'def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hballρ : Metric.ball q.2.1 ρ' ⊆ Metric.ball q.2.1 ρ := Metric.ball_subset_ball hρ'le
  have hballA : ∀ u ∈ Metric.ball q.2.1 ρ', r₁ < ‖u‖ ∧ ‖u‖ < r₂ := by
    intro u hu
    rw [Metric.mem_ball, dist_eq_norm] at hu
    have hu' : ‖u - q.2.1‖ < ρ' := hu
    constructor
    · have htri : ‖q.2.1‖ ≤ ‖u‖ + ‖u - q.2.1‖ := by
        have h := norm_add_le (q.2.1 - u) u
        have heq : q.2.1 - u + u = q.2.1 := by ring
        rw [heq, norm_sub_rev, add_comm] at h
        exact h
      have h3 := hρ'₁
      linarith
    · have htri : ‖u‖ ≤ ‖q.2.1‖ + ‖u - q.2.1‖ := by
        have h := norm_add_le q.2.1 (u - q.2.1)
        have heq : q.2.1 + (u - q.2.1) = u := by ring
        rwa [heq] at h
      have h3 := hρ'₂
      linarith
  -- ## the component of `q` over the annulus
  set A : Set ChainData := {x : ChainData | r₁ < ‖x.2.1‖ ∧ ‖x.2.1‖ < r₂} with hAdef
  set T : Set ChainData := connectedComponentIn (S ∩ A) q with hTdef
  have hTincl : T ⊆ S ∩ A := connectedComponentIn_subset (S ∩ A) q
  have hqT : q ∈ T := mem_connectedComponentIn ⟨hqS, hq₁, hq₂⟩
  have hTpre : IsPreconnected T := isPreconnected_connectedComponentIn
  have hTH : T ⊆ H0 a h := fun x hx => hSsub (hTincl hx).1
  -- ## the section image lies in `S` and in the annulus
  have hccq : connectedComponentIn (H0 a h) q = S := by
    have h : q ∈ connectedComponentIn (H0 a h) p := hSp ▸ hqS
    exact (connectedComponentIn_eq h).symm.trans hSp.symm
  have hpre : IsPreconnected (f '' Metric.ball q.2.1 ρ') :=
    (Metric.isPreconnected_ball (x := q.2.1) (r := ρ')).image f (hcontf.mono hballρ)
  have himgS : f '' Metric.ball q.2.1 ρ' ⊆ S := by
    have hsub : f '' Metric.ball q.2.1 ρ' ⊆ connectedComponentIn (H0 a h) q :=
      hpre.subset_connectedComponentIn ⟨q.2.1, Metric.mem_ball_self hρ'pos, hf0⟩
        (by rintro _ ⟨u, hu, rfl⟩; exact (hfmem u (hballρ hu)).1)
    rw [hccq] at hsub
    exact hsub
  have himgA : f '' Metric.ball q.2.1 ρ' ⊆ A := by
    rintro _ ⟨u, hu, rfl⟩
    simp only [hAdef, Set.mem_ofPred_eq]
    rw [(hfmem u (hballρ hu)).2]
    exact hballA u hu
  -- ## a starting parameter outside the obstruction set
  obtain ⟨u₁, hu₁ball, hu₁notP, hu₁ne⟩ : ∃ u₁ : ℂ, u₁ ∈ Metric.ball q.2.1 ρ' ∧
      u₁ ∉ Refl.GenuinePunctureValues a h ∧ u₁ ≠ 0 := by
    obtain ⟨u, hu⟩ := Refl.exists_mem_ball_notMem (x := q.2.1) hρ'pos
      (hcountP.union (Set.countable_singleton 0))
    exact ⟨u, hu.1, fun hc => hu.2 (Or.inl hc), fun hc => hu.2 (Or.inr (by simpa using hc))⟩
  set p' : ChainData := f u₁ with hp'def
  have hp'psi : p'.2.1 = u₁ := (hfmem u₁ (hballρ hu₁ball)).2
  have hp'H0 : p' ∈ H0 a h := (hfmem u₁ (hballρ hu₁ball)).1
  have hp'S : p' ∈ S := himgS ⟨u₁, hu₁ball, rfl⟩
  have hp'T : p' ∈ T := by
    have hsub : f '' Metric.ball q.2.1 ρ' ⊆ T :=
      hpre.subset_connectedComponentIn ⟨q.2.1, Metric.mem_ball_self hρ'pos, hf0⟩
        (fun x hx => ⟨himgS hx, himgA hx⟩)
    exact hsub ⟨u₁, hu₁ball, rfl⟩
  have hccp' : connectedComponentIn (H0 a h) p' = S := by
    have h : p' ∈ connectedComponentIn (H0 a h) p := hSp ▸ hp'S
    exact (connectedComponentIn_eq h).symm.trans hSp.symm
  -- ## a path in the annulus from `u₁` to `z`, avoiding the obstruction set
  obtain ⟨g, hgcont, hg0, hg1, hgA, hgP⟩ :=
    annulus_path_avoiding_countable hcountP hr₁ hr₁₂ (hballA u₁ hu₁ball).1
      (hballA u₁ hu₁ball).2 hz₁ hz₂ hzP
  have hg0' : g 0 = p'.2.1 := by rw [hg0, hp'psi]
  have hgne : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t ≠ 0 := by
    intro t ht h0
    have := (hgA t ht).1
    rw [h0, norm_zero] at this
    linarith
  have hgnotP : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t ∉ Refl.GenuinePunctureValues a h := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0, hg0]; exact hu₁notP
    · rcases eq_or_lt_of_le ht.2 with h1 | h1
      · rw [h1, hg1]; exact hzP
      · exact hgP t ⟨h0, h1⟩
  have hgen : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ (e : ℂ → ChainData) (k : ℕ),
      IsPuncturedChart a h e (g t) k →
        ∃ q' ∈ H0 a h, Tendsto e (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds q') := by
    intro t ht e k he
    by_contra hno
    obtain ⟨v, hv⟩ := Refl.tendsto_psi2_of_isPuncturedChart ha0 ha1 hh he
    exact hgnotP t ht ⟨e, v, k, he, hno, hv⟩
  have hval : ∀ x ∈ connectedComponentIn (H0 a h) p', x.2.1 * x.2.2 = c := by
    intro x hx
    rw [hccp'] at hx
    exact hSval x hx
  -- ## lift the path
  obtain ⟨G, hGcont, hG0, hGm⟩ :=
    Refl.path_lift_component ha0 ha1 hh hp'H0 hval hg0' hgcont hgne hgen
  have hGimgS : G '' Set.Icc (0 : ℝ) 1 ⊆ S := by
    have hmem : G '' Set.Icc (0 : ℝ) 1 ⊆ connectedComponentIn (H0 a h) p' :=
      (isPreconnected_Icc.image G hGcont).subset_connectedComponentIn
        ⟨0, ⟨le_rfl, zero_le_one⟩, hG0⟩
        (by rintro _ ⟨t, ht, rfl⟩; exact (hGm t ht).1)
    exact hmem.trans (le_of_eq hccp')
  have hG1S : G 1 ∈ S := hGimgS ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
  have hG1T : G 1 ∈ T := by
    have hmem : G '' Set.Icc (0 : ℝ) 1 ⊆ connectedComponentIn (S ∩ A) p' :=
      (isPreconnected_Icc.image G hGcont).subset_connectedComponentIn
        ⟨0, ⟨le_rfl, zero_le_one⟩, hG0⟩
        (by
          rintro _ ⟨t, ht, rfl⟩
          refine ⟨hGimgS ⟨t, ht, rfl⟩, ?_⟩
          simp only [hAdef, Set.mem_ofPred_eq]
          rw [(hGm t ht).2]
          exact hgA t ht)
    have heq : connectedComponentIn (S ∩ A) p' = T := (connectedComponentIn_eq hp'T).symm
    exact (hmem.trans (le_of_eq heq)) ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
  have hG1psi : (G 1).2.1 = z := by
    rw [(hGm 1 ⟨zero_le_one, le_rfl⟩).2, hg1]
  -- ## the two floors coincide on `T`
  have hBT₁ : ∀ x ∈ T, ‖x.2.1‖ ≤ r₂ := by
    intro x hx
    exact le_of_lt (hTincl hx).2.2
  have hB0 : 0 ≤ B := le_trans (norm_nonneg c) hc
  have hBT₂ : ∀ x ∈ T, ‖x.2.2‖ ≤ max 0 (B / r₁) := by
    intro x hx
    obtain ⟨hxS, hx1, hx2⟩ := hTincl hx
    have hxne : x.2.1 ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hx1
      linarith
    have hxval : x.2.2 = c / x.2.1 := by
      rw [eq_div_iff hxne, mul_comm]
      exact hSval x hxS
    rw [hxval, norm_div]
    calc ‖c‖ / ‖x.2.1‖ ≤ B / ‖x.2.1‖ := div_le_div_of_nonneg_right hc (norm_nonneg _)
      _ ≤ B / r₁ := div_le_div_of_nonneg_left hB0 hr₁ hx1.le
      _ ≤ max 0 (B / r₁) := le_max_right _ _
  refine ⟨G 1, hG1S, hG1psi, ?_⟩
  intro n hn
  have hdP := hnP n (le_trans (le_max_left _ _) hn) T hTpre hTH hBT₁
  have hdB := hnB n (le_trans (le_max_right _ _) hn) T hTpre hTH hBT₂
  constructor
  · rcases hdP with h | h
    · exact iff_of_true (h q hqT) (h (G 1) hG1T)
    · exact iff_of_false (fun hh => h q hqT hh) (fun hh => h (G 1) hG1T hh)
  · rcases hdB with h | h
    · exact iff_of_true (h q hqT) (h (G 1) hG1T)
    · exact iff_of_false (fun hh => h q hqT hh) (fun hh => h (G 1) hG1T hh)

end Work.EQ
