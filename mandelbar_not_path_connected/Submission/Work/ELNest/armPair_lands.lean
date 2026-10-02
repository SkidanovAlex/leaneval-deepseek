/-
# ELNest — the three arm pairs co-land at level `0`

`Work.ELNest.armPair_lands`: from the co-landing of the level-`6` pairs of the three arm chains
`Cert.armChainA`, `Cert.armChainB`, `Cert.armChainC` (together with the `c`-side condition `hcv`
at every one of the six steps of each chain) conclude that the three level-`0` arm pairs
`Cert.armChainA 0`, `Cert.armChainB 0`, `Cert.armChainC 0` co-land.

This is the exact arm-chain counterpart of `Work.ELNest.uPair_lands` (the `u`-chain has ten
steps, the three arm chains have six each): the combinatorial content is the certificate of
`Submission/Work/ELPull/Cert/Data.lean` and `Checks.lean`

* each `Cert.armChainXArc i` is one of the two **unwrapped** arcs of the pair
  `Cert.armChainX i.succ` (`armChainXArc_isUnwrappedQ` below, a finite rational computation), and
* `Cert.armChainX i` is the pair of the `T`-preimage arc `Cert.armChainXArc i`
  (`Cert.armChainX_step i : IsPB1StepQ (armChainXArc i) (armChainX i)`).

So each step is one application of the one-step pull-back engine `Work.ELPull.pb1Top` (König's
lemma for the two rays above a ray), and the six steps are assembled by the reverse induction
`Fin.reverseInduction` on the chain `armChainX : Fin 7 → ℚ × ℚ`.  The chains share the whole
argument, so it is stated once as `chainPair_lands` (for an abstract chain
`P : Fin (n+1) → ℚ × ℚ` with arcs `I : Fin n → ℚ × ℚ`) and instantiated three times.
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

/-! ## 1. The rational certificate for the arcs of the three arm chains -/

/-- The certificate for the arcs of the `armChainA` chain: `Cert.armChainAArc i` is one of the
two unwrapped arcs of the pair `Cert.armChainA i.succ` (and the arc is non-degenerate). -/
theorem armChainAArc_isUnwrappedQ (i : Fin 6) :
    IsUnwrappedArcQ (Cert.armChainA i.succ) (Cert.armChainAArc i) ∧
      arcLenQ (Cert.armChainA i.succ).1 (Cert.armChainA i.succ).2 ≠ 0 := by
  fin_cases i <;> refine ⟨?_, ?_⟩ <;> norm_num [IsUnwrappedArcQ, arcLenQ]

/-- The certificate for the arcs of the `armChainB` chain. -/
theorem armChainBArc_isUnwrappedQ (i : Fin 6) :
    IsUnwrappedArcQ (Cert.armChainB i.succ) (Cert.armChainBArc i) ∧
      arcLenQ (Cert.armChainB i.succ).1 (Cert.armChainB i.succ).2 ≠ 0 := by
  fin_cases i <;> refine ⟨?_, ?_⟩ <;> norm_num [IsUnwrappedArcQ, arcLenQ]

/-- The certificate for the arcs of the `armChainC` chain. -/
theorem armChainCArc_isUnwrappedQ (i : Fin 6) :
    IsUnwrappedArcQ (Cert.armChainC i.succ) (Cert.armChainCArc i) ∧
      arcLenQ (Cert.armChainC i.succ).1 (Cert.armChainC i.succ).2 ≠ 0 := by
  fin_cases i <;> refine ⟨?_, ?_⟩ <;> norm_num [IsUnwrappedArcQ, arcLenQ]

/-! ## 2. The chain lemma -/

/-- **A PB1 chain co-lands.**  Given an angle chain `P : Fin (n+1) → ℚ × ℚ`, a chain of arcs
`I : Fin n → ℚ × ℚ` such that `I i` is an (unwrapped, non-degenerate) arc of `P i.succ` and
`P i.castSucc` is the pair of its `k`-th `T`-preimage (`IsPB1StepQ (I i) (P i.castSucc)`), and
the side condition `hcv` at every step, the co-landing of the top pair `P (Fin.last n)` pulls
back along the chain to the co-landing of `P 0`.

Each step is one application of `Work.ELPull.pb1Top` (the two rays above a ray co-land); the
steps are assembled with `Fin.reverseInduction`. -/
theorem chainPair_lands {c : ℂ} (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar)
    (hN : Work.ELPull.DynB c)
    (hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c))
    (htop : Work.ELPull.PB1Top hN)
    {n : ℕ} (P : Fin (n + 1) → ℚ × ℚ) (I : Fin n → ℚ × ℚ)
    (hbase : ∃ y : ℂ, LandsN hN ((P (Fin.last n)).1 : ℝ) y ∧
      LandsN hN ((P (Fin.last n)).2 : ℝ) y)
    (hunw : ∀ i : Fin n, IsUnwrappedArcQ (P i.succ) (I i) ∧
      arcLenQ (P i.succ).1 (P i.succ).2 ≠ 0)
    (hstep : ∀ i : Fin n, IsPB1StepQ (I i) (P i.castSucc))
    (hcv : ∀ (i : Fin n) (Q : CoPair hN), Q.a = ((P i.succ).1 : ℝ) →
      Q.b = ((P i.succ).2 : ℝ) →
      c ∈ arcSide hN Q ((I i).2 : ℝ) ((I i).1 : ℝ)) :
    ∃ y : ℂ, LandsN hN ((P 0).1 : ℝ) y ∧ LandsN hN ((P 0).2 : ℝ) y := by
  -- one pull-back step of the chain
  have hstep' : ∀ i : Fin n,
      (∃ y : ℂ, LandsN hN ((P i.succ).1 : ℝ) y ∧
        LandsN hN ((P i.succ).2 : ℝ) y) →
      (∃ y : ℂ, LandsN hN ((P i.castSucc).1 : ℝ) y ∧
        LandsN hN ((P i.castSucc).2 : ℝ) y) := by
    intro i hPi
    obtain ⟨y, hy1, hy2⟩ := hPi
    -- the co-landing pair at level `i+1`
    let Q : CoPair hN :=
      ⟨((P i.succ).1 : ℝ), ((P i.succ).2 : ℝ), y, hy1, hy2⟩
    -- the certificate: `I i` is an unwrapped arc of `Q`
    have hcert := hunw i
    have hI : IsUnwrappedArcOf Q (((I i).1 : ℝ), ((I i).2 : ℝ)) :=
      isUnwrappedArcOf_of_isUnwrappedArcQ (Q := Q) (P := P i.succ) (I := I i) rfl rfl hcert.1
    have hab : arcLen Q.a Q.b ≠ 0 :=
      arcLen_ne_zero_of_arcLenQ_ne_zero (Q := Q) (P := P i.succ) rfl rfl hcert.2
    have hcvQ : c ∈ arcSide hN Q ((I i).2 : ℝ) ((I i).1 : ℝ) := hcv i Q rfl rfl
    -- the pair at level `i` is the pair of the `T`-preimage arc `I i`
    have hstepR : IsPB1Step
        (((I i).1 : ℝ), ((I i).2 : ℝ))
        (((P i.castSucc).1 : ℝ), ((P i.castSucc).2 : ℝ)) :=
      (hstep i).to_real
    obtain ⟨k, hk⟩ := exists_isPreimageArcPair_of_isPB1Step hstepR
    -- the one-step pull-back
    obtain ⟨y', _, hl1, hl2⟩ := pb1Top hc hN hφ htop Q hab
      (((I i).1 : ℝ), ((I i).2 : ℝ)) hI hcvQ k
    exact ⟨y', (landsN_of_isPreimageArcPair hk hl1 hl2).1,
      (landsN_of_isPreimageArcPair hk hl1 hl2).2⟩
  -- the `n` steps, from `P (Fin.last n)` down to `P 0`
  have key := Fin.reverseInduction (motive := fun j : Fin (n + 1) => ∃ y : ℂ,
      LandsN hN ((P j).1 : ℝ) y ∧ LandsN hN ((P j).2 : ℝ) y) hbase hstep'
  simpa using key 0

/-! ## 3. The three arm pairs co-land -/

theorem armPair_lands {c : ℂ} (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar)
    (hN : Work.ELPull.DynB c)
    (hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c))
    (htop : Work.ELPull.PB1Top hN)
    (hbaseA : ∃ y : ℂ, Work.ELPull.LandsN hN ((Work.ELPull.Cert.armChainA 6).1 : ℝ) y ∧
      Work.ELPull.LandsN hN ((Work.ELPull.Cert.armChainA 6).2 : ℝ) y)
    (hbaseB : ∃ y : ℂ, Work.ELPull.LandsN hN ((Work.ELPull.Cert.armChainB 6).1 : ℝ) y ∧
      Work.ELPull.LandsN hN ((Work.ELPull.Cert.armChainB 6).2 : ℝ) y)
    (hbaseC : ∃ y : ℂ, Work.ELPull.LandsN hN ((Work.ELPull.Cert.armChainC 6).1 : ℝ) y ∧
      Work.ELPull.LandsN hN ((Work.ELPull.Cert.armChainC 6).2 : ℝ) y)
    (hcvA : ∀ (i : Fin 6) (Q : Work.ELPull.CoPair hN),
      Q.a = ((Work.ELPull.Cert.armChainA i.succ).1 : ℝ) →
      Q.b = ((Work.ELPull.Cert.armChainA i.succ).2 : ℝ) →
      c ∈ Work.ELPull.arcSide hN Q ((Work.ELPull.Cert.armChainAArc i).2 : ℝ)
        ((Work.ELPull.Cert.armChainAArc i).1 : ℝ))
    (hcvB : ∀ (i : Fin 6) (Q : Work.ELPull.CoPair hN),
      Q.a = ((Work.ELPull.Cert.armChainB i.succ).1 : ℝ) →
      Q.b = ((Work.ELPull.Cert.armChainB i.succ).2 : ℝ) →
      c ∈ Work.ELPull.arcSide hN Q ((Work.ELPull.Cert.armChainBArc i).2 : ℝ)
        ((Work.ELPull.Cert.armChainBArc i).1 : ℝ))
    (hcvC : ∀ (i : Fin 6) (Q : Work.ELPull.CoPair hN),
      Q.a = ((Work.ELPull.Cert.armChainC i.succ).1 : ℝ) →
      Q.b = ((Work.ELPull.Cert.armChainC i.succ).2 : ℝ) →
      c ∈ Work.ELPull.arcSide hN Q ((Work.ELPull.Cert.armChainCArc i).2 : ℝ)
        ((Work.ELPull.Cert.armChainCArc i).1 : ℝ)) :
    (∃ y : ℂ, Work.ELPull.LandsN hN ((Work.ELPull.Cert.armChainA 0).1 : ℝ) y ∧
      Work.ELPull.LandsN hN ((Work.ELPull.Cert.armChainA 0).2 : ℝ) y) ∧
    (∃ y : ℂ, Work.ELPull.LandsN hN ((Work.ELPull.Cert.armChainB 0).1 : ℝ) y ∧
      Work.ELPull.LandsN hN ((Work.ELPull.Cert.armChainB 0).2 : ℝ) y) ∧
    (∃ y : ℂ, Work.ELPull.LandsN hN ((Work.ELPull.Cert.armChainC 0).1 : ℝ) y ∧
      Work.ELPull.LandsN hN ((Work.ELPull.Cert.armChainC 0).2 : ℝ) y) := by
  refine ⟨?_, ?_, ?_⟩
  · exact chainPair_lands hc hN hφ htop Cert.armChainA Cert.armChainAArc hbaseA
      armChainAArc_isUnwrappedQ (fun i => Cert.armChainA_step i) hcvA
  · exact chainPair_lands hc hN hφ htop Cert.armChainB Cert.armChainBArc hbaseB
      armChainBArc_isUnwrappedQ (fun i => Cert.armChainB_step i) hcvB
  · exact chainPair_lands hc hN hφ htop Cert.armChainC Cert.armChainCArc hbaseC
      armChainCArc_isUnwrappedQ (fun i => Cert.armChainC_step i) hcvC

end Work.ELNest
