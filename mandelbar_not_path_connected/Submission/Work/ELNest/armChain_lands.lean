import Mathlib
import Submission.Work.ELNest.ArmChain
import Submission.Work.ELPull.pb1Top

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELNest

open Work.ELPull

/-! ## Elementary facts about one step of an arm chain

The arm chains `armPairOf near k p` of `ArmChain.lean` are built exactly as the nest chain
`nestPair` of `Chain.lean`: one step feeds the near or far unwrapped arc `armArcOf near j p` of
the current pair `p` to `pb1Top` and takes the pair of its `k j`-th counterclockwise `T`-preimage
arc `preArc (k j) (armArcOf near j p)`.  Consequently the two facts recorded for `nestStep` in
`nestChain_lands.lean` apply verbatim: the arc `armArcOf near j p` is one of the two unwrapped
arcs of any pair with angles `p.1`, `p.2`, and one step preserves the non-vanishing of the arc
length.  We only need to name the `Work.EL`/`Work.ELPull` coincidence of `arcLen`. -/

/-- One arm step is the pair of the `k j`-th `T`-preimage arc of `armArcOf near j p`. -/
lemma armStepOf_eq_preArc (near : ℕ → Bool) (k : ℕ → Fin 2) (j : ℕ) (p : ℝ × ℝ) :
    armStepOf near k j p = Work.ELPull.preArc (k j) (armArcOf near j p) := rfl

/-- The arc length of a `T`-preimage arc is the arc length of the (unwrapped) image arc, halved. -/
lemma arcLen_preArc_eq' (k : Fin 2) (I : ℝ × ℝ) :
    Work.ELPull.arcLen (Work.ELPull.preArc k I).1 (Work.ELPull.preArc k I).2
      = Int.fract ((I.2 - I.1) / 2) := by
  unfold Work.ELPull.arcLen Work.ELPull.preArc
  rw [Work.ELPull.fract_fract_sub]
  congr 1
  ring

/-- `armArcOf near j p` is one of the two unwrapped arcs of any pair whose angles are `p.1`, `p.2`. -/
lemma isUnwrappedArcOf_armArcOf {c : ℂ} {hN : Work.ELPull.DynB c} (Q : Work.ELPull.CoPair hN)
    (near : ℕ → Bool) (j : ℕ) (p : ℝ × ℝ) (ha : Q.a = p.1) (hb : Q.b = p.2) :
    Work.ELPull.IsUnwrappedArcOf Q (armArcOf near j p) := by
  unfold armArcOf
  split_ifs with h
  · exact Or.inr ⟨hb.symm, by rw [hb, ha]; exact rfl⟩
  · exact Or.inl ⟨ha.symm, by rw [ha, hb]; exact rfl⟩

/-- `Int.fract` does not vanish after negating the argument. -/
lemma fract_ne_zero_swap {a b : ℝ} (h : Int.fract (b - a) ≠ 0) : Int.fract (a - b) ≠ 0 := by
  intro hh
  apply h
  rw [Int.fract_eq_zero_iff] at hh ⊢
  rcases hh with ⟨n, hn⟩
  exact ⟨-n, by push_cast; linarith [hn]⟩

/-- Halving a number of the open unit interval keeps `Int.fract` away from `0`. -/
lemma fract_half_ne_zero {g : ℝ} (h0 : 0 < g) (h1 : g < 1) : Int.fract (g / 2) ≠ 0 := by
  rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  linarith

/-- One arm step preserves the non-vanishing of the arc length. -/
lemma armStepOf_arcLen_ne_zero (near : ℕ → Bool) (k : ℕ → Fin 2) (j : ℕ) (p : ℝ × ℝ)
    (hp : Work.ELPull.arcLen p.1 p.2 ≠ 0) :
    Work.ELPull.arcLen (armStepOf near k j p).1 (armStepOf near k j p).2 ≠ 0 := by
  have hp' : Int.fract (p.2 - p.1) ≠ 0 := hp
  rw [armStepOf_eq_preArc, arcLen_preArc_eq']
  unfold armArcOf
  split_ifs with h
  · simp only [Work.EL.arcLen]
    rw [show p.2 + Int.fract (p.1 - p.2) - p.2 = Int.fract (p.1 - p.2) by ring]
    exact fract_half_ne_zero
      (lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm (fract_ne_zero_swap (a := p.1) (b := p.2) hp')))
      (Int.fract_lt_one _)
  · simp only [Work.EL.arcLen]
    rw [show p.1 + Int.fract (p.2 - p.1) - p.1 = Int.fract (p.2 - p.1) by ring]
    exact fract_half_ne_zero
      (lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hp'))
      (Int.fract_lt_one _)

/-! ## The arm chain lands -/

/-- **One arm chain of six steps co-lands.**  Given a co-landing pair with angles `p0` and
`arcLen p0.1 p0.2 ≠ 0`, the six steps of the arm chain `armPairOf near k p0` pull the co-landing
forward along the `T`-preimage arcs prescribed by the chain, provided at every step `t < 6` the
critical value `c` lies on the `(armArcOf near (5 - t) (armPairOf near k p0 t)).2`-side of the
current pair (the certificate `P6` of `armPair_lands`). -/
theorem armChainAux {c : ℂ} (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar)
    (hN : Work.ELPull.DynB c)
    (hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c))
    (htop : Work.ELPull.PB1Top hN)
    (near : ℕ → Bool) (k : ℕ → Fin 2) (p0 : ℝ × ℝ) {y : ℂ}
    (h1 : Work.ELPull.LandsN hN p0.1 y) (h2 : Work.ELPull.LandsN hN p0.2 y)
    (hnd : Work.ELPull.arcLen p0.1 p0.2 ≠ 0)
    (hcv : ∀ (t : ℕ) (Q : Work.ELPull.CoPair hN), t < 6 →
      Q.a = (armPairOf near k p0 t).1 → Q.b = (armPairOf near k p0 t).2 →
      c ∈ Work.ELPull.arcSide hN Q
        (armArcOf near (5 - t) (armPairOf near k p0 t)).2
        (armArcOf near (5 - t) (armPairOf near k p0 t)).1) :
    ∃ y' : ℂ, Work.ELPull.LandsN hN (armPairOf near k p0 6).1 y' ∧
      Work.ELPull.LandsN hN (armPairOf near k p0 6).2 y' := by
  have key : ∀ t : ℕ, t ≤ 6 →
      (∃ y : ℂ, Work.ELPull.LandsN hN (armPairOf near k p0 t).1 y ∧
        Work.ELPull.LandsN hN (armPairOf near k p0 t).2 y) ∧
      Work.ELPull.arcLen (armPairOf near k p0 t).1 (armPairOf near k p0 t).2 ≠ 0 := by
    intro t
    induction t with
    | zero => intro _; exact ⟨⟨y, h1, h2⟩, hnd⟩
    | succ t ih =>
      intro hts
      obtain ⟨⟨yt, hyt1, hyt2⟩, hgt⟩ := ih (Nat.le_of_succ_le hts)
      have htlt : t < 6 := hts
      -- the co-landing pair at step `t`
      let Q : Work.ELPull.CoPair hN :=
        ⟨(armPairOf near k p0 t).1, (armPairOf near k p0 t).2, yt, hyt1, hyt2⟩
      have hQa : Q.a = (armPairOf near k p0 t).1 := rfl
      have hQb : Q.b = (armPairOf near k p0 t).2 := rfl
      have hneQ : Work.ELPull.arcLen Q.a Q.b ≠ 0 := by rw [hQa, hQb]; exact hgt
      have hIu : Work.ELPull.IsUnwrappedArcOf Q
          (armArcOf near (5 - t) (armPairOf near k p0 t)) :=
        isUnwrappedArcOf_armArcOf Q near (5 - t) (armPairOf near k p0 t) hQa hQb
      have hcvQ : c ∈ Work.ELPull.arcSide hN Q
          (armArcOf near (5 - t) (armPairOf near k p0 t)).2
          (armArcOf near (5 - t) (armPairOf near k p0 t)).1 :=
        hcv t Q htlt hQa hQb
      -- the one-step pull-back
      obtain ⟨y', _, hl1, hl2⟩ :=
        Work.ELPull.pb1Top hc hN hφ htop Q hneQ
          (armArcOf near (5 - t) (armPairOf near k p0 t)) hIu hcvQ (k (5 - t))
      have hstep : armPairOf near k p0 (t + 1) =
          Work.ELPull.preArc (k (5 - t))
            (armArcOf near (5 - t) (armPairOf near k p0 t)) := rfl
      refine ⟨⟨y', ?_, ?_⟩, ?_⟩
      · rw [hstep]; exact hl1
      · rw [hstep]; exact hl2
      · rw [hstep]
        exact armStepOf_arcLen_ne_zero near k (5 - t) (armPairOf near k p0 t) hgt
  obtain ⟨⟨y', hy1, hy2⟩, _⟩ := key 6 (le_refl 6)
  exact ⟨y', hy1, hy2⟩

theorem armChain_lands {c : ℂ} (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar)
    (hN : Work.ELPull.DynB c)
    (hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c))
    (htop : Work.ELPull.PB1Top hN)
    (aA bA aB bB aC bC : ℝ) {yA yB yC : ℂ}
    (hA : Work.ELPull.LandsN hN aA yA) (hAz : Work.ELPull.LandsN hN bA yA)
    (hB : Work.ELPull.LandsN hN aB yB) (hBz : Work.ELPull.LandsN hN bB yB)
    (hC : Work.ELPull.LandsN hN aC yC) (hCz : Work.ELPull.LandsN hN bC yC)
    (hndA : Work.EL.arcLen aA bA ≠ 0) (hndB : Work.EL.arcLen aB bB ≠ 0)
    (hndC : Work.EL.arcLen aC bC ≠ 0)
    (hcvA : ∀ (t : ℕ) (Q : Work.ELPull.CoPair hN), t < 6 →
      Q.a = (Work.ELNest.armPairOf Work.ELNest.nearA Work.ELNest.kA (aA, bA) t).1 →
      Q.b = (Work.ELNest.armPairOf Work.ELNest.nearA Work.ELNest.kA (aA, bA) t).2 →
      c ∈ Work.ELPull.arcSide hN Q
        (Work.ELNest.armArcOf Work.ELNest.nearA (5 - t)
          (Work.ELNest.armPairOf Work.ELNest.nearA Work.ELNest.kA (aA, bA) t)).2
        (Work.ELNest.armArcOf Work.ELNest.nearA (5 - t)
          (Work.ELNest.armPairOf Work.ELNest.nearA Work.ELNest.kA (aA, bA) t)).1)
    (hcvB : ∀ (t : ℕ) (Q : Work.ELPull.CoPair hN), t < 6 →
      Q.a = (Work.ELNest.armPairOf Work.ELNest.nearB Work.ELNest.kB (aB, bB) t).1 →
      Q.b = (Work.ELNest.armPairOf Work.ELNest.nearB Work.ELNest.kB (aB, bB) t).2 →
      c ∈ Work.ELPull.arcSide hN Q
        (Work.ELNest.armArcOf Work.ELNest.nearB (5 - t)
          (Work.ELNest.armPairOf Work.ELNest.nearB Work.ELNest.kB (aB, bB) t)).2
        (Work.ELNest.armArcOf Work.ELNest.nearB (5 - t)
          (Work.ELNest.armPairOf Work.ELNest.nearB Work.ELNest.kB (aB, bB) t)).1)
    (hcvC : ∀ (t : ℕ) (Q : Work.ELPull.CoPair hN), t < 6 →
      Q.a = (Work.ELNest.armPairOf Work.ELNest.nearC Work.ELNest.kC (aC, bC) t).1 →
      Q.b = (Work.ELNest.armPairOf Work.ELNest.nearC Work.ELNest.kC (aC, bC) t).2 →
      c ∈ Work.ELPull.arcSide hN Q
        (Work.ELNest.armArcOf Work.ELNest.nearC (5 - t)
          (Work.ELNest.armPairOf Work.ELNest.nearC Work.ELNest.kC (aC, bC) t)).2
        (Work.ELNest.armArcOf Work.ELNest.nearC (5 - t)
          (Work.ELNest.armPairOf Work.ELNest.nearC Work.ELNest.kC (aC, bC) t)).1) :
    (∃ y : ℂ, Work.ELPull.LandsN hN
        (Work.ELNest.armPairOf Work.ELNest.nearA Work.ELNest.kA (aA, bA) 6).1 y ∧
      Work.ELPull.LandsN hN
        (Work.ELNest.armPairOf Work.ELNest.nearA Work.ELNest.kA (aA, bA) 6).2 y) ∧
    (∃ y : ℂ, Work.ELPull.LandsN hN
        (Work.ELNest.armPairOf Work.ELNest.nearB Work.ELNest.kB (aB, bB) 6).1 y ∧
      Work.ELPull.LandsN hN
        (Work.ELNest.armPairOf Work.ELNest.nearB Work.ELNest.kB (aB, bB) 6).2 y) ∧
    (∃ y : ℂ, Work.ELPull.LandsN hN
        (Work.ELNest.armPairOf Work.ELNest.nearC Work.ELNest.kC (aC, bC) 6).1 y ∧
      Work.ELPull.LandsN hN
        (Work.ELNest.armPairOf Work.ELNest.nearC Work.ELNest.kC (aC, bC) 6).2 y) := by
  refine ⟨?_, ?_, ?_⟩
  · exact armChainAux hc hN hφ htop nearA kA (aA, bA) hA hAz hndA hcvA
  · exact armChainAux hc hN hφ htop nearB kB (aB, bB) hB hBz hndB hcvB
  · exact armChainAux hc hN hφ htop nearC kC (aC, bC) hC hCz hndC hcvC

end Work.ELNest
