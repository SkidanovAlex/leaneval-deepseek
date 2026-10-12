import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.slotProj_peel_ae
import Submission.Work.MB.slotProj1_idem_weak
import Submission.Work.MB.slotProj_mb_weak
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.MB

/-- The empty slot projection is the identity (the integral over the empty fibre space is the
constant state). -/
theorem slotProj_empty_weak {m N : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (Φ : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ) :
    Work.BoseBoxFock.slotProj e (∅ : Finset (Fin N)) Φ = Φ := by
  rw [Work.BoseBoxFock.slotProj_eq_slotInt_fun]
  exact Work.BoseBoxFock.slotInt_empty e Φ

/-- **The composition law of the slot projections, at the weak mode hypotheses.**

With `slotProj e S Φ x = ∫ z : (↥S → E3), (∏ i, PV e (x i.1) (z i)) * Φ (updateFinset x S z)`
(`Work.BoseBoxFock.SlotProjDefs`), the slot projections compose:
`slotProj e S (slotProj e T Φ) = slotProj e (S ∪ T) Φ`.  The modes are only regular in the weak
sense (measurable, *everywhere* bounded, supported in the box `boxL ℓ`) and the state only
measurable and everywhere bounded — no `Continuous` and no `HasCompactSupport`, so the strong
`Work.BoseBoxFock.slotInt_comp` does not apply (its hypotheses are unsatisfiable at the honest
modes).

Proof sketch (mirror of `Work.BoseBoxFock.slotInt_comp`).  Induct on `S`.
* `S = ∅`: `Work.BoseBoxFock.slotInt_empty` (`slotProj e ∅ Ψ = Ψ`).
* `S = insert u S'` with `hu : u ∉ S'`: write `insert u S' = S' ∪ {u}` and peel the slot `u`
  off the *outer* projection applied to the state `slotProj e T Φ` with the weak peel
  `Work.BoseBoxFock.slotProj_peel_bdd` (`slotProj e (insert i U) g = slotProj1 e i (slotProj e U g)`
  for `g` measurable and everywhere bounded; it needs only `MemLp ⊤` modes and box support —
  obtain `MemLp (e l) ⊤` from `hmeas`, `hbdE`, `hsupp` via `MeasureTheory.MemLp.of_bound` /
  `memLp_top_of_bound`).  This requires `slotProj e T Φ` measurable and everywhere bounded, i.e.
  `Work.MB.slotProj_mb_weak`.  Then use the induction hypothesis at `S'`, and conclude by cases:
  - `u ∈ T`: `(S' ∪ {u}) ∪ T = S' ∪ T`; the extra `slotProj1 e u` is absorbed by
    `slotProj e (S' ∪ T) Φ`.  Absorption is the peel at `U := (S' ∪ T).erase u` (whose
    complement condition `u ∉ U` holds) followed by the idempotence
    `Work.MB.slotProj1_idem_weak` applied to the state `slotProj e U Φ`
    (measurable and everywhere bounded, again by `Work.MB.slotProj_mb_weak`) — exactly as
    `Work.BoseBoxFock.slotProj1_slotInt_self` does in the strong case.
  - `u ∉ T`: `(S' ∪ {u}) ∪ T = (S' ∪ T) ∪ {u}`, so the peel applies *in reverse*
    (`← Work.BoseBoxFock.slotProj_peel_bdd` at `S' ∪ T`).
-/
theorem slotProj_comp_weak {m N : ℕ} {ℓ : ℝ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (S T : Finset (Fin N)) {Φ : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ}
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) :
    Work.BoseBoxFock.slotProj e S (Work.BoseBoxFock.slotProj e T Φ)
      = Work.BoseBoxFock.slotProj e (S ∪ T) Φ := by
  classical
  -- an everywhere bound for the state, and `MemLp ⊤` for the modes
  have hCΦ : ∀ y : Fin N → EuclideanSpace ℝ (Fin 3), ‖Φ y‖ ≤ hΦb.choose := hΦb.choose_spec
  have hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) := fun l =>
    MeasureTheory.memLp_top_of_bound (hmeas l).aestronglyMeasurable _
      (Filter.Eventually.of_forall (hbdE l).choose_spec)
  -- **Absorption**: projecting an already projected slot changes nothing.  Peel the slot `u`
  -- off `slotProj e U Φ` (`U = (U.erase u) ∪ {u}` since `u ∈ U`) and use the idempotence of
  -- `slotProj1` on the state `slotProj e (U.erase u) Φ`.
  have habsorb : ∀ (U : Finset (Fin N)) (u : Fin N), u ∈ U →
      Work.BoseBoxFock.slotProj1 e u (Work.BoseBoxFock.slotProj e U Φ)
        = Work.BoseBoxFock.slotProj e U Φ := by
    intro U u hu
    have hu' : u ∉ U.erase u := Finset.notMem_erase u U
    obtain ⟨hsm, C, hsb⟩ :=
      Work.MB.slotProj_mb_weak hmeas hbdE hsupp (U.erase u) hΦm hΦb
    have hpeel : Work.BoseBoxFock.slotProj e U Φ
        = Work.BoseBoxFock.slotProj1 e u (Work.BoseBoxFock.slotProj e (U.erase u) Φ) := by
      have h := Work.BoseBoxFock.slotProj_peel_bdd hbdd hsupp hu' hΦm hCΦ
      rw [Finset.insert_erase hu] at h
      exact h
    rw [hpeel]
    exact Work.MB.slotProj1_idem_weak hmeas hbdE hsupp horth hsm ⟨C, hsb⟩ u
  -- the induction on `S` (the state `Φ` and the set `T` are fixed)
  induction S using Finset.induction_on with
  | empty =>
      rw [Finset.empty_union]
      exact slotProj_empty_weak e (Work.BoseBoxFock.slotProj e T Φ)
  | insert u S' hu ih =>
      obtain ⟨hsm, C, hsb⟩ := Work.MB.slotProj_mb_weak hmeas hbdE hsupp T hΦm hΦb
      -- peel the slot `u` off the *outer* projection applied to the state `slotProj e T Φ`
      rw [Work.BoseBoxFock.slotProj_peel_bdd hbdd hsupp hu hsm hsb, ih]
      by_cases huT : u ∈ T
      · -- `u ∈ T`: `(insert u S') ∪ T = S' ∪ T`, and the extra slot is absorbed
        have hset : insert u S' ∪ T = S' ∪ T := by
          rw [Finset.insert_union,
            Finset.insert_eq_self.mpr (Finset.mem_union_right S' huT)]
        rw [hset]
        exact habsorb (S' ∪ T) u (Finset.mem_union_right S' huT)
      · -- `u ∉ T`: `(insert u S') ∪ T = insert u (S' ∪ T)`, so the peel applies in reverse
        have hnotin : u ∉ S' ∪ T := by
          simp only [Finset.mem_union, not_or]
          exact ⟨hu, huT⟩
        have hset : insert u S' ∪ T = insert u (S' ∪ T) := Finset.insert_union u S' T
        rw [hset, ← Work.BoseBoxFock.slotProj_peel_bdd hbdd hsupp hnotin hΦm hCΦ]

end Work.MB
