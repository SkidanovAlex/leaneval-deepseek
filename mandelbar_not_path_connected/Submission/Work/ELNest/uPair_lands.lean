/-
# ELNest — the `u`-pair co-lands (the level-`0` base case of the nest at `z₁`)

`Work.ELNest.uPair_lands`: from the co-landing of the pair `uChain 10 = P₄` (the α-pair of the
fourth critical-orbit point `f⁴ z₁`) and the `c`-side condition `hcv` at every one of the ten
steps of the certificate chain `Cert.uChain`, conclude that the `u`-pair `uChain 0 = (U0, U0p)`
co-lands.

The combinatorial content is the certificate of `Submission/Work/ELPull/Cert/Data.lean`:

* each `Cert.uChainArc i` is one of the two **unwrapped** arcs of the pair `uChain (i+1)`
  (`uChainArc_isUnwrappedQ` below, a finite rational computation), and
* `uChain i` is the pair of the `T`-preimage arc `Cert.uChainArc i`
  (`Cert.uChain_step i : IsPB1StepQ (uChainArc i) (uChain i)`).

So each step `i` is exactly one application of the one-step pull-back engine `Work.ELPull.pb1Top`
(König's lemma for the two rays above a ray), and the ten steps are assembled by the reverse
induction `Fin.reverseInduction` on the chain `uChain : Fin 11 → ℚ × ℚ`.

`hcv` is the side condition of the certificate (C9: the critical value `c` lies on the far side
of each chain arc; it is discharged from the L-wake and the certificate's rational data); `hbase`
is the level-`0` co-landing at `P₄ = (821/1023, 326/1023)`.
-/
import Mathlib
import Submission.Work.ELPull.pb1Top
import Submission.Work.ELPull.Cert.Checks
import Submission.Work.ELPull.Cert.Data
import Submission.Work.ELTop.landsN_map

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELNest

open Work.ELPull

/-! ## 1. The rational certificate for the arcs of the `u`-chain -/

/-- The rational version of `IsUnwrappedArcOf`: `I` is one of the two unwrapped arcs `(a, a+1)` of
the pair `P`. -/
def IsUnwrappedArcQ (P I : ℚ × ℚ) : Prop :=
  (I.1 = P.1 ∧ I.2 = P.1 + Work.ELPull.arcLenQ P.1 P.2) ∨
    (I.1 = P.2 ∧ I.2 = P.2 + Work.ELPull.arcLenQ P.2 P.1)

/-- **The certificate for the arcs of the `u`-chain**: `Cert.uChainArc i` is one of the two
unwrapped arcs of the pair `Cert.uChain i.succ`, and the two angles of that pair are distinct
(so the arc is non-degenerate). -/
theorem uChainArc_isUnwrappedQ (i : Fin 10) :
    IsUnwrappedArcQ (Cert.uChain i.succ) (Cert.uChainArc i) ∧
      Work.ELPull.arcLenQ (Cert.uChain i.succ).1 (Cert.uChain i.succ).2 ≠ 0 := by
  fin_cases i <;> refine ⟨?_, ?_⟩ <;>
    norm_num [IsUnwrappedArcQ, Work.ELPull.arcLenQ]

/-! ## 2. Transfer of the certificate to the real angles of the landing pairs -/

/-- The rational certificate is an `IsUnwrappedArcOf` statement for the real angles of any
co-landing pair with the prescribed angles. -/
theorem isUnwrappedArcOf_of_isUnwrappedArcQ {c : ℂ} {hN : Work.ELPull.DynB c} {Q : CoPair hN}
    {P I : ℚ × ℚ} (ha : Q.a = (P.1 : ℝ)) (hb : Q.b = (P.2 : ℝ)) (h : IsUnwrappedArcQ P I) :
    Work.ELPull.IsUnwrappedArcOf Q ((I.1 : ℝ), (I.2 : ℝ)) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inl ⟨?_, ?_⟩
    · rw [h1, ha]
    · show ((I.2 : ℚ) : ℝ) = Q.a + arcLen Q.a Q.b
      rw [h2, ha, hb]
      push_cast
      rw [Work.ELPull.arcLenQ_cast]
  · refine Or.inr ⟨?_, ?_⟩
    · rw [h1, hb]
    · show ((I.2 : ℚ) : ℝ) = Q.b + arcLen Q.b Q.a
      rw [h2, hb, ha]
      push_cast
      rw [Work.ELPull.arcLenQ_cast]

/-- The two angles of a pair of the chain are distinct modulo `1`, so the arc length does not
vanish. -/
theorem arcLen_ne_zero_of_arcLenQ_ne_zero {c : ℂ} {hN : Work.ELPull.DynB c} {Q : CoPair hN}
    {P : ℚ × ℚ} (ha : Q.a = (P.1 : ℝ)) (hb : Q.b = (P.2 : ℝ))
    (h : Work.ELPull.arcLenQ P.1 P.2 ≠ 0) : arcLen Q.a Q.b ≠ 0 := by
  rw [ha, hb, Work.ELPull.arcLenQ_cast]
  exact_mod_cast h

/-! ## 3. Two elementary steps -/

/-- A pair of preimage rays of an arc: the landing points of the two preimage rays are the
landing points of the two angles of the pair, in either order. -/
theorem landsN_of_isPreimageArcPair {c : ℂ} {hN : Work.ELPull.DynB c} {I Q : ℝ × ℝ} {k : Fin 2}
    {y : ℂ} (h : IsPreimageArcPair k I Q) (h1 : LandsN hN (preArc k I).1 y)
    (h2 : LandsN hN (preArc k I).2 y) : LandsN hN Q.1 y ∧ LandsN hN Q.2 y := by
  rcases h with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact ⟨by rw [e1]; exact h1, by rw [e2]; exact h2⟩
  · exact ⟨by rw [e2]; exact h2, by rw [e1]; exact h1⟩

/-- The index of the preimage arc behind an `IsPB1Step`. -/
theorem exists_isPreimageArcPair_of_isPB1Step {I Q : ℝ × ℝ} (h : IsPB1Step I Q) :
    ∃ k : Fin 2, IsPreimageArcPair k I Q :=
  h.elim (fun h0 => ⟨(0 : Fin 2), h0⟩) (fun h1 => ⟨(1 : Fin 2), h1⟩)

/-! ## 4. The `u`-pair co-lands -/

theorem uPair_lands {c : ℂ} (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar)
    (hN : Work.ELPull.DynB c)
    (hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c))
    (htop : Work.ELPull.PB1Top hN)
    (hbase : ∃ y : ℂ, Work.ELPull.LandsN hN ((Work.ELPull.Cert.uChain 10).1 : ℝ) y ∧
      Work.ELPull.LandsN hN ((Work.ELPull.Cert.uChain 10).2 : ℝ) y)
    (hcv : ∀ (i : Fin 10) (Q : Work.ELPull.CoPair hN),
      Q.a = ((Work.ELPull.Cert.uChain i.succ).1 : ℝ) →
      Q.b = ((Work.ELPull.Cert.uChain i.succ).2 : ℝ) →
      c ∈ Work.ELPull.arcSide hN Q ((Work.ELPull.Cert.uChainArc i).2 : ℝ)
        ((Work.ELPull.Cert.uChainArc i).1 : ℝ)) :
    ∃ y : ℂ, Work.ELPull.LandsN hN ((Work.ELPull.Cert.U0 : ℚ) : ℝ) y ∧
      Work.ELPull.LandsN hN ((Work.ELPull.Cert.U0p : ℚ) : ℝ) y := by
  -- one pull-back step of the chain
  have hstep : ∀ i : Fin 10,
      (∃ y : ℂ, LandsN hN ((Cert.uChain i.succ).1 : ℝ) y ∧
        LandsN hN ((Cert.uChain i.succ).2 : ℝ) y) →
      (∃ y : ℂ, LandsN hN ((Cert.uChain i.castSucc).1 : ℝ) y ∧
        LandsN hN ((Cert.uChain i.castSucc).2 : ℝ) y) := by
    intro i hPi
    obtain ⟨y, hy1, hy2⟩ := hPi
    -- the co-landing pair at level `i+1`
    let Q : CoPair hN :=
      ⟨((Cert.uChain i.succ).1 : ℝ), ((Cert.uChain i.succ).2 : ℝ), y, hy1, hy2⟩
    -- the certificate: `uChainArc i` is an unwrapped arc of `Q`
    have hcert := uChainArc_isUnwrappedQ i
    have hI : IsUnwrappedArcOf Q
        (((Cert.uChainArc i).1 : ℝ), ((Cert.uChainArc i).2 : ℝ)) :=
      isUnwrappedArcOf_of_isUnwrappedArcQ (Q := Q) (P := Cert.uChain i.succ)
        (I := Cert.uChainArc i) rfl rfl hcert.1
    have hab : arcLen Q.a Q.b ≠ 0 :=
      arcLen_ne_zero_of_arcLenQ_ne_zero (Q := Q) (P := Cert.uChain i.succ) rfl rfl hcert.2
    have hcvQ : c ∈ arcSide hN Q
        (((Cert.uChainArc i).1 : ℝ), ((Cert.uChainArc i).2 : ℝ)).2
        (((Cert.uChainArc i).1 : ℝ), ((Cert.uChainArc i).2 : ℝ)).1 := hcv i Q rfl rfl
    -- the pair at level `i` is the pair of the `T`-preimage arc of `uChainArc i`
    have hstepR : IsPB1Step
        (((Cert.uChainArc i).1 : ℝ), ((Cert.uChainArc i).2 : ℝ))
        (((Cert.uChain i.castSucc).1 : ℝ), ((Cert.uChain i.castSucc).2 : ℝ)) :=
      (Cert.uChain_step i).to_real
    obtain ⟨k, hk⟩ := exists_isPreimageArcPair_of_isPB1Step hstepR
    -- the one-step pull-back
    obtain ⟨y', _, hl1, hl2⟩ := pb1Top hc hN hφ htop Q hab
      (((Cert.uChainArc i).1 : ℝ), ((Cert.uChainArc i).2 : ℝ)) hI hcvQ k
    exact ⟨y', (landsN_of_isPreimageArcPair hk hl1 hl2).1,
      (landsN_of_isPreimageArcPair hk hl1 hl2).2⟩
  -- the ten steps, from `uChain 10` down to `uChain 0`
  have hbase' : ∃ y : ℂ, LandsN hN ((Cert.uChain (Fin.last 10)).1 : ℝ) y ∧
      LandsN hN ((Cert.uChain (Fin.last 10)).2 : ℝ) y := hbase
  have key := Fin.reverseInduction (motive := fun j : Fin 11 => ∃ y : ℂ,
      LandsN hN ((Cert.uChain j).1 : ℝ) y ∧ LandsN hN ((Cert.uChain j).2 : ℝ) y) hbase' hstep
  simpa using key 0

end Work.ELNest
