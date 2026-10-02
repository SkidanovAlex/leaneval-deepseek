/-
# ELNest — the level-1 `u`-pair co-lands (the level-`1` nest at `z₁`)

`Work.ELNest.uuPair_lands`: from the co-landing of the pair `uuChain 10 = uPair` (the `u`-pair
itself) and the `c`-side condition `hcv` at every one of the ten steps of the certificate chain
`Cert.uuChain`, conclude that the level-1 `u`-pair `uuChain 0 = (U1, U1p)` co-lands.

This is the exact analogue of `Work.ELNest.uPair_lands` (the level-0 statement), one level
deeper in the nest at the parabolic point `z₁`: the certificate chain `Cert.uuChain` is the
`T`-preimage chain of the chain `Cert.uChain`, with `uuChain 10 = uChain 0`.

The combinatorial content is the certificate of `Submission/Work/ELPull/Cert/{Data,Checks}.lean`:

* each `Cert.uuChainArc i` is one of the two **unwrapped** arcs of the pair `uuChain (i+1)`
  (`uuChainArc_isUnwrappedQ` below, a finite rational computation), and
* `uuChain i` is the pair of the `T`-preimage arc `Cert.uuChainArc i`
  (`Cert.uuChain_step i : IsPB1StepQ (uuChainArc i) (uuChain i)`).

So each step `i` is exactly one application of the one-step pull-back engine `Work.ELPull.pb1Top`
(König's lemma for the two rays above a ray), and the ten steps are assembled by the reverse
induction `Fin.reverseInduction` on the chain `uuChain : Fin 11 → ℚ × ℚ`.

`hcv` is the side condition of the certificate (the critical value `c` lies on the far side of
each chain arc); `hbase` is the level-`0` co-landing at `uuChain 10 = (β₀, β₀')`.
-/
import Mathlib
import Submission.Work.ELNest.uPair_lands
import Submission.Work.ELPull.pb1Top
import Submission.Work.ELPull.Cert.Checks

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELNest

open Work.ELPull

/-! ## 1. The rational certificate for the arcs of the level-1 `u`-chain -/

/-- **The certificate for the arcs of the level-1 `u`-chain**: `Cert.uuChainArc i` is one of the
two unwrapped arcs of the pair `Cert.uuChain i.succ`, and the two angles of that pair are
distinct (so the arc is non-degenerate). -/
theorem uuChainArc_isUnwrappedQ (i : Fin 10) :
    IsUnwrappedArcQ (Cert.uuChain i.succ) (Cert.uuChainArc i) ∧
      Work.ELPull.arcLenQ (Cert.uuChain i.succ).1 (Cert.uuChain i.succ).2 ≠ 0 := by
  fin_cases i <;> refine ⟨?_, ?_⟩ <;> norm_num [IsUnwrappedArcQ, Work.ELPull.arcLenQ]

/-- The PB1 steps of the level-1 `u`-chain, indexed in the form used by the reverse
induction. -/
theorem uuChain_step' (i : Fin 10) :
    IsPB1StepQ (Cert.uuChainArc i) (Cert.uuChain i.castSucc) := by
  have h : (⟨i.1, by omega⟩ : Fin 11) = i.castSucc := Fin.ext rfl
  rw [← h]
  exact Cert.uuChain_step i

/-! ## 2. The level-1 `u`-pair co-lands -/

theorem uuPair_lands {c : ℂ} (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar)
    (hN : Work.ELPull.DynB c)
    (hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c))
    (htop : Work.ELPull.PB1Top hN)
    (hbase : ∃ y : ℂ, Work.ELPull.LandsN hN ((Work.ELPull.Cert.uuChain 10).1 : ℝ) y ∧
      Work.ELPull.LandsN hN ((Work.ELPull.Cert.uuChain 10).2 : ℝ) y)
    (hcv : ∀ (i : Fin 10) (Q : Work.ELPull.CoPair hN),
      Q.a = ((Work.ELPull.Cert.uuChain i.succ).1 : ℝ) →
      Q.b = ((Work.ELPull.Cert.uuChain i.succ).2 : ℝ) →
      c ∈ Work.ELPull.arcSide hN Q ((Work.ELPull.Cert.uuChainArc i).2 : ℝ)
        ((Work.ELPull.Cert.uuChainArc i).1 : ℝ)) :
    ∃ y : ℂ, Work.ELPull.LandsN hN ((Work.ELPull.Cert.uuChain 0).1 : ℝ) y ∧
      Work.ELPull.LandsN hN ((Work.ELPull.Cert.uuChain 0).2 : ℝ) y := by
  -- one pull-back step of the chain
  have hstep : ∀ i : Fin 10,
      (∃ y : ℂ, LandsN hN ((Cert.uuChain i.succ).1 : ℝ) y ∧
        LandsN hN ((Cert.uuChain i.succ).2 : ℝ) y) →
      (∃ y : ℂ, LandsN hN ((Cert.uuChain i.castSucc).1 : ℝ) y ∧
        LandsN hN ((Cert.uuChain i.castSucc).2 : ℝ) y) := by
    intro i hPi
    obtain ⟨y, hy1, hy2⟩ := hPi
    -- the co-landing pair at level `i+1`
    let Q : CoPair hN :=
      ⟨((Cert.uuChain i.succ).1 : ℝ), ((Cert.uuChain i.succ).2 : ℝ), y, hy1, hy2⟩
    -- the certificate: `uuChainArc i` is an unwrapped arc of `Q`
    have hcert := uuChainArc_isUnwrappedQ i
    have hI : IsUnwrappedArcOf Q
        (((Cert.uuChainArc i).1 : ℝ), ((Cert.uuChainArc i).2 : ℝ)) :=
      isUnwrappedArcOf_of_isUnwrappedArcQ (Q := Q) (P := Cert.uuChain i.succ)
        (I := Cert.uuChainArc i) rfl rfl hcert.1
    have hab : arcLen Q.a Q.b ≠ 0 :=
      arcLen_ne_zero_of_arcLenQ_ne_zero (Q := Q) (P := Cert.uuChain i.succ) rfl rfl hcert.2
    have hcvQ : c ∈ arcSide hN Q
        (((Cert.uuChainArc i).1 : ℝ), ((Cert.uuChainArc i).2 : ℝ)).2
        (((Cert.uuChainArc i).1 : ℝ), ((Cert.uuChainArc i).2 : ℝ)).1 := hcv i Q rfl rfl
    -- the pair at level `i` is the pair of the `T`-preimage arc of `uuChainArc i`
    have hstepR : IsPB1Step
        (((Cert.uuChainArc i).1 : ℝ), ((Cert.uuChainArc i).2 : ℝ))
        (((Cert.uuChain i.castSucc).1 : ℝ), ((Cert.uuChain i.castSucc).2 : ℝ)) :=
      (uuChain_step' i).to_real
    obtain ⟨k, hk⟩ := exists_isPreimageArcPair_of_isPB1Step hstepR
    -- the one-step pull-back
    obtain ⟨y', _, hl1, hl2⟩ := pb1Top hc hN hφ htop Q hab
      (((Cert.uuChainArc i).1 : ℝ), ((Cert.uuChainArc i).2 : ℝ)) hI hcvQ k
    exact ⟨y', (landsN_of_isPreimageArcPair hk hl1 hl2).1,
      (landsN_of_isPreimageArcPair hk hl1 hl2).2⟩
  -- the ten steps, from `uuChain 10` down to `uuChain 0`
  have hbase' : ∃ y : ℂ, LandsN hN ((Cert.uuChain (Fin.last 10)).1 : ℝ) y ∧
      LandsN hN ((Cert.uuChain (Fin.last 10)).2 : ℝ) y := hbase
  have key := Fin.reverseInduction (motive := fun j : Fin 11 => ∃ y : ℂ,
      LandsN hN ((Cert.uuChain j).1 : ℝ) y ∧ LandsN hN ((Cert.uuChain j).2 : ℝ) y) hbase' hstep
  simpa using key 0

end Work.ELNest
