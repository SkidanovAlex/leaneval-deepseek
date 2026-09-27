import Mathlib
import Submission.Work.EKLComp.ErgMax.Basic
import Submission.Work.EKLComp.ErgMax.avg_a0
import Submission.Work.EKLComp.ErgMax.ent_avg

/-!
# `ErgMax.ent_avg_clause`

Variant of `ErgMax.ent_avg` in which the two entropy clauses of the frozen
`P_EntropyBasics` are supplied in the unbundled form `E2c` (conjugacy) and `E3c`
(affinity) defined in `ErgMax.Basic`.

The argument is identical to the one in `ErgMax.ent_avg`: every grid element
`g = aDiag (shift N i j)` commutes with `a₀`, hence `act g` conjugates `act a₀` with
itself and (E2) gives `ent ((act g)_* ν) (act a₀) = ent ν (act a₀)`; affinity (E3),
iterated over the `N⁴` terms, gives the same for the uniform average.
-/

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

namespace Work.EKLComp.ErgMax

open Work.EKLContract

set_option linter.style.haveILetI false

variable {X : Type} [MeasurableSpace X]

/-- **Entropy of a uniform finite average**, from clause (E3) alone.

If `μ` is a finite family of probability measures, all of them preserved by a measurable
`T` and all with the same entropy `e`, then the uniform average `(♯s)⁻¹ • ∑_{i ∈ s} μ i`
again has entropy `e` with respect to `T`.  This is the iterated form of the affinity of
entropy, clause (E3) of `P_EntropyBasics` in its unbundled form `E3c`.

The proof is the one of `ErgMax.ent_uniform_avg_finset`, with the single appeal to (E3)
replaced by `hE3`; the two measure-theoretic helpers
`measurePreserving_smul_finsetSum` and `measure_univ_inv_card_smul_finsetSum` are imported
unchanged from `ErgMax.ent_avg`. -/
theorem ent_uniform_avg_finset_clause {ι : Type*} (hE3 : E3c) (T : X → X)
    (hT : Measurable T) (e : ENNReal) :
    ∀ (s : Finset ι), s.Nonempty → ∀ (μ : ι → Measure X),
      (∀ i ∈ s, IsProbabilityMeasure (μ i)) → (∀ i ∈ s, MeasurePreserving T (μ i) (μ i)) →
      (∀ i ∈ s, ent (μ i) T = e) →
      ent (((s.card : ℕ) : ENNReal)⁻¹ • ∑ i ∈ s, μ i) T = e := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro hs
    exact (Finset.not_nonempty_empty hs).elim
  | insert a s ha ih =>
    intro hs μ hprob hmp he
    rcases Finset.eq_empty_or_nonempty s with hs0 | hs'
    · -- `s` is empty: the average is the single measure `μ a`.
      subst hs0
      rw [Finset.card_insert_of_notMem ha, Finset.card_empty, Finset.sum_insert ha,
        Finset.sum_empty, add_zero]
      simpa using he a (Finset.mem_insert_self a ∅)
    · -- `s` is nonempty: split off the term `μ a`.
      have hprob_s : ∀ i ∈ s, IsProbabilityMeasure (μ i) :=
        fun i hi => hprob i (Finset.mem_insert_of_mem hi)
      have hmp_s : ∀ i ∈ s, MeasurePreserving T (μ i) (μ i) :=
        fun i hi => hmp i (Finset.mem_insert_of_mem hi)
      have he_s : ∀ i ∈ s, ent (μ i) T = e := fun i hi => he i (Finset.mem_insert_of_mem hi)
      have hmass : (((s.card : ℕ) : ENNReal)⁻¹ • ∑ i ∈ s, μ i) Set.univ = 1 :=
        measure_univ_inv_card_smul_finsetSum s μ hs' hprob_s
      have hQprob : IsProbabilityMeasure (((s.card : ℕ) : ENNReal)⁻¹ • ∑ i ∈ s, μ i) := ⟨hmass⟩
      have hpa : IsProbabilityMeasure (μ a) := hprob a (Finset.mem_insert_self a s)
      have hmpQ : MeasurePreserving T (((s.card : ℕ) : ENNReal)⁻¹ • ∑ i ∈ s, μ i)
          (((s.card : ℕ) : ENNReal)⁻¹ • ∑ i ∈ s, μ i) :=
        measurePreserving_smul_finsetSum T hT s μ _ hmp_s
      have hIH : ent (((s.card : ℕ) : ENNReal)⁻¹ • ∑ i ∈ s, μ i) T = e :=
        ih hs' μ hprob_s hmp_s he_s
      -- abbreviations: `Q` the average over `s`, `M = ♯s + 1`, `c = M⁻¹`
      set Q : Measure X := ((s.card : ℕ) : ENNReal)⁻¹ • ∑ i ∈ s, μ i with hQ
      set M : ENNReal := ((s.card : ℕ) : ENNReal) + 1 with hM
      set c : ENNReal := M⁻¹ with hc
      have hM0 : M ≠ 0 := by rw [hM]; positivity
      have hMtop : M ≠ ⊤ := by rw [hM]; simp
      have hmul : M * c = 1 := by rw [hc]; exact ENNReal.mul_inv_cancel hM0 hMtop
      have hc_le : c ≤ 1 := by
        rw [hc]; exact ENNReal.inv_le_one.mpr (by rw [hM]; simp)
      have hcne : c ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hc_le
      -- `c + ♯s * c = 1`, i.e. `1 - c = ♯s * c`
      have hone : c + ((s.card : ℕ) : ENNReal) * c = 1 := by
        have key : ((1 : ENNReal) + ((s.card : ℕ) : ENNReal)) * c = 1 := by
          rw [add_comm, ← hM, hmul]
        rwa [add_mul, one_mul] at key
      have hsub : (1 : ENNReal) - c = ((s.card : ℕ) : ENNReal) * c := by
        refine ENNReal.sub_eq_of_eq_add hcne ?_
        rw [← hone, add_comm]
      -- the coefficient of `Q` collapses back to `c`
      have hscalar : (((s.card : ℕ) : ENNReal) * c) * (((s.card : ℕ) : ENNReal)⁻¹) = c := by
        have hm0 : ((s.card : ℕ) : ENNReal) ≠ 0 := by
          rw [Nat.cast_ne_zero]; exact Finset.card_ne_zero.mpr hs'
        have hmtop : ((s.card : ℕ) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
        rw [mul_assoc, mul_comm c (((s.card : ℕ) : ENNReal)⁻¹), ← mul_assoc,
          ENNReal.mul_inv_cancel hm0 hmtop, one_mul]
      -- the average over `insert a s` is the convex combination `c • μ a + (1 - c) • Q`
      have hmeas : c • (μ a + ∑ i ∈ s, μ i) = c • μ a + (1 - c) • Q := by
        rw [smul_add, hsub, hQ, smul_smul, hscalar]
      have hkey : ent (c • μ a + (1 - c) • Q) T = c * ent (μ a) T + (1 - c) * ent Q T :=
        hE3 (μ a) hpa Q hQprob T c hc_le hT (hmp a (Finset.mem_insert_self a s)) hmpQ
      rw [Finset.card_insert_of_notMem ha, Finset.sum_insert ha, Nat.cast_add, Nat.cast_one]
      have hcM : (((s.card : ℕ) : ENNReal) + 1)⁻¹ = c := by rw [hc, hM]
      rw [hcM, hmeas, hkey, he a (Finset.mem_insert_self a s), hIH, hsub, ← add_mul, hone,
        one_mul]

/-- **`ErgMax.ent_avg_clause`**: the `A⁺`-average `avg ν N` has the same `a₀`-entropy as `ν`,
using only clauses (E2) and (E3) of `P_EntropyBasics` in the unbundled form `E2c`, `E3c`.

Each of the `N⁴` grid points `g = aDiag (shift N i j)` commutes with `a₀ = aDiag ![-2,1,1]`
(diagonal matrices commute), so `act g` is a measurable bijection conjugating `act a₀` with
itself; clause (E2) gives `ent ((act g)_* ν) (act a₀) = ent ν (act a₀)`, and clause (E3)
(affinity), iterated by `ent_uniform_avg_finset_clause`, gives the same for the uniform
average. -/
theorem ent_avg_clause (hE2 : Work.EKLComp.ErgMax.E2c) (hE3 : Work.EKLComp.ErgMax.E3c)
    (ν : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure ν]
    (hmp : MeasureTheory.MeasurePreserving (Work.EKLComp.ErgMax.act Work.EKLContract.a0) ν ν)
    {N : ℕ} (hN : 1 ≤ N) :
    Work.EKLContract.ent (Work.EKLComp.ErgMax.avg ν N)
        (Work.EKLComp.ErgMax.act Work.EKLContract.a0) =
      Work.EKLContract.ent ν (Work.EKLComp.ErgMax.act Work.EKLContract.a0) := by
  classical
  have hN0 : N ≠ 0 := by omega
  have hpos : 1 ≤ n N := by
    show 0 < n N
    simp only [n]
    exact Nat.mul_pos hN hN
  haveI : Nonempty (Fin (n N) × Fin (n N)) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  rw [avg_def]
  set e : ENNReal := ent ν (act a0) with he
  set μ : Fin (n N) × Fin (n N) → Measure X3 :=
    fun x => ν.map (act (aDiag (shift N x.1 x.2))) with hμ
  have hprob : ∀ x, IsProbabilityMeasure (μ x) := fun x =>
    show IsProbabilityMeasure (ν.map _) from inferInstance
  have hpres : ∀ x, MeasurePreserving (act a0) (μ x) (μ x) := fun x =>
    ⟨measurable_act a0, map_act_a0_of_comm hmp (act_aDiag_shift_comm_a0 N x.1 x.2)⟩
  -- (E2): conjugating `act a₀` by the commuting `act (aDiag (shift N i j))`
  have hent : ∀ x, ent (μ x) (act a0) = e := fun x => by
    have hg : Measurable (act (aDiag (shift N x.1 x.2))) := measurable_act _
    refine hE2 ν ‹IsProbabilityMeasure ν› (act a0) (act (aDiag (shift N x.1 x.2)))
      (act ((aDiag (shift N x.1 x.2))⁻¹)) (measurable_act a0) hg (measurable_act _) hmp
      ?_ ?_ ?_
    · intro y
      simp only [act_apply]
      rw [← mul_smul, inv_mul_cancel, one_smul]
    · intro y
      simp only [act_apply]
      rw [← mul_smul, mul_inv_cancel, one_smul]
    · intro y
      exact congrFun (act_aDiag_shift_comm_a0 N x.1 x.2) y
  have hmain := ent_uniform_avg_finset_clause hE3 (act a0) (measurable_act a0) e
    (Finset.univ : Finset (Fin (n N) × Fin (n N))) Finset.univ_nonempty μ
    (fun x _ => hprob x) (fun x _ => hpres x) (fun x _ => hent x)
  -- match the index set `Fin (n N) × Fin (n N)` against the double sum in `avg_def`
  have hcard : (((Finset.univ : Finset (Fin (n N) × Fin (n N))).card : ℕ) : ENNReal)
      = ((n N * n N : ℕ) : ENNReal) := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  have hsum : (∑ x ∈ (Finset.univ : Finset (Fin (n N) × Fin (n N))), μ x)
      = ∑ i : Fin (n N), ∑ j : Fin (n N), ν.map (act (aDiag (shift N i j))) := by
    rw [hμ, ← Finset.univ_product_univ, Finset.sum_product]
  rw [hcard, hsum] at hmain
  exact hmain

end Work.EKLComp.ErgMax
