import Mathlib
import Submission.Work.ELNest.Chain
import Submission.Work.ELPull.pb1Top

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.ELNest

open Work.ELPull

/-! ## Two elementary facts about `nestStep`

`nestStep j p` is by construction the pair of the two endpoints of the `k`-th
counterclockwise `T`-preimage arc `preArc (nestK j) (nestArc j p)` of the unwrapped arc
`nestArc j p`.  We record this identification, together with the two arithmetic facts the
chain of pull-backs needs: `nestArc j p` is one of the two *unwrapped* arcs of the pair `p`,
and the arc length of `nestStep j p` does not vanish whenever that of `p` does not. -/

/-- The arc length of a `T`-preimage arc is the arc length of the (unwrapped) image arc,
halved. -/
lemma arcLen_preArc_eq (k : Fin 2) (I : ℝ × ℝ) :
    Work.ELPull.arcLen (Work.ELPull.preArc k I).1 (Work.ELPull.preArc k I).2
      = Int.fract ((I.2 - I.1) / 2) := by
  unfold Work.ELPull.arcLen Work.ELPull.preArc
  rw [Work.ELPull.fract_fract_sub]
  congr 1
  ring

/-- The arc length of one step of the nest chain: the arc of `nestStep j p` is the (unwrapped)
far or near arc of `p`, halved, depending on the residue of `j` modulo `5`. -/
lemma arcLen_nestStep (j : ℕ) (p : ℝ × ℝ) :
    Work.ELPull.arcLen (nestStep j p).1 (nestStep j p).2 =
      (if j % 5 = 3 ∨ j % 5 = 4 then Work.ELPull.arcLen p.2 p.1
        else Work.ELPull.arcLen p.1 p.2) / 2 := by
  have hstep : nestStep j p = Work.ELPull.preArc (nestK j) (nestArc j p) := rfl
  rw [hstep, arcLen_preArc_eq]
  by_cases h : j % 5 = 3 ∨ j % 5 = 4
  · rw [if_pos h]
    have hI : nestArc j p = (p.2, p.2 + Work.ELPull.arcLen p.2 p.1) := by
      unfold nestArc; rw [if_pos h]; rfl
    rw [hI]
    rw [show p.2 + Work.ELPull.arcLen p.2 p.1 - p.2 = Work.ELPull.arcLen p.2 p.1 by ring]
    exact Int.fract_eq_self.mpr
      ⟨by unfold Work.ELPull.arcLen; linarith [Int.fract_nonneg (p.1 - p.2)],
       by unfold Work.ELPull.arcLen; linarith [Int.fract_lt_one (p.1 - p.2)]⟩
  · rw [if_neg h]
    have hI : nestArc j p = (p.1, p.1 + Work.ELPull.arcLen p.1 p.2) := by
      unfold nestArc; rw [if_neg h]; rfl
    rw [hI]
    rw [show p.1 + Work.ELPull.arcLen p.1 p.2 - p.1 = Work.ELPull.arcLen p.1 p.2 by ring]
    exact Int.fract_eq_self.mpr
      ⟨by unfold Work.ELPull.arcLen; linarith [Int.fract_nonneg (p.2 - p.1)],
       by unfold Work.ELPull.arcLen; linarith [Int.fract_lt_one (p.2 - p.1)]⟩

/-- The two arc lengths of a pair are simultaneously zero: `arcLen b a ≠ 0` if
`arcLen a b ≠ 0` (the real-argument form of `arcLen_swap_ne_zero`). -/
lemma arcLen_swap_ne_zero' (a b : ℝ) (h : Work.ELPull.arcLen a b ≠ 0) :
    Work.ELPull.arcLen b a ≠ 0 := by
  unfold Work.ELPull.arcLen at h ⊢
  rw [show a - b = -(b - a) by ring, Int.fract_neg h]
  intro hh; have := Int.fract_lt_one (b - a); linarith

/-- One step of the nest chain preserves the non-degeneracy of the arc length. -/
lemma arcLen_nestStep_ne_zero (j : ℕ) (p : ℝ × ℝ)
    (hp : Work.ELPull.arcLen p.1 p.2 ≠ 0) :
    Work.ELPull.arcLen (nestStep j p).1 (nestStep j p).2 ≠ 0 := by
  rw [arcLen_nestStep]
  by_cases h : j % 5 = 3 ∨ j % 5 = 4
  · rw [if_pos h]
    intro hh
    exact arcLen_swap_ne_zero' p.1 p.2 hp (by linarith)
  · rw [if_neg h]
    intro hh
    exact hp (by linarith)

/-- `nestArc j p` is one of the two unwrapped arcs of any pair whose angles are `p.1`, `p.2`. -/
lemma isUnwrappedArcOf_nestArc {c : ℂ} {hN : Work.ELPull.DynB c} (Q : CoPair hN) (j : ℕ)
    (p : ℝ × ℝ) (ha : Q.a = p.1) (hb : Q.b = p.2) :
    Work.ELPull.IsUnwrappedArcOf Q (nestArc j p) := by
  unfold nestArc
  split_ifs with h
  · exact Or.inr ⟨hb.symm, by rw [hb, ha]; rfl⟩
  · exact Or.inl ⟨ha.symm, by rw [ha, hb]; rfl⟩

/-- **The nest chain lands.**  Starting from a co-landing pair with angles `(a, b)` (with
`arcLen a b ≠ 0`), each of the ten steps of the nest chain `nestPair (a, b) ·` pulls the
co-landing back along the `T`-preimage arc prescribed by the certificate, provided the critical
value `c` lies on the far side of the arc used at every step (`hcv`).  After ten steps the pair
`nestPair (a, b) 10` co-lands. -/
theorem nestChain_lands {c : ℂ} (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar)
    (hN : Work.ELPull.DynB c)
    (hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c))
    (htop : Work.ELPull.PB1Top hN) (a b : ℝ) {y : ℂ}
    (hy : Work.ELPull.LandsN hN a y) (hyb : Work.ELPull.LandsN hN b y)
    (hab : Work.EL.arcLen a b ≠ 0)
    (hcv : ∀ (t : ℕ) (Q : Work.ELPull.CoPair hN), t < 10 →
      Q.a = (Work.ELNest.nestPair (a, b) t).1 → Q.b = (Work.ELNest.nestPair (a, b) t).2 →
      c ∈ Work.ELPull.arcSide hN Q (Work.ELNest.nestArc (9 - t) (Work.ELNest.nestPair (a, b) t)).2
        (Work.ELNest.nestArc (9 - t) (Work.ELNest.nestPair (a, b) t)).1) :
    ∃ y' : ℂ, Work.ELPull.LandsN hN (Work.ELNest.nestPair (a, b) 10).1 y' ∧
      Work.ELPull.LandsN hN (Work.ELNest.nestPair (a, b) 10).2 y' := by
  have hab' : Work.ELPull.arcLen a b ≠ 0 := hab
  -- the co-landing at every step, together with the non-degeneracy of the arc length
  have key : ∀ t : ℕ, t ≤ 10 →
      (∃ y : ℂ, LandsN hN (nestPair (a, b) t).1 y ∧ LandsN hN (nestPair (a, b) t).2 y) ∧
        Work.ELPull.arcLen (nestPair (a, b) t).1 (nestPair (a, b) t).2 ≠ 0 := by
    intro t
    induction t with
    | zero =>
      intro _
      exact ⟨⟨y, hy, hyb⟩, hab'⟩
    | succ t ih =>
      intro hts
      obtain ⟨⟨yt, hyt1, hyt2⟩, hgt⟩ := ih (Nat.le_of_succ_le hts)
      have htlt : t < 10 := hts
      -- the co-landing pair at step `t`
      let Q : CoPair hN :=
        ⟨(nestPair (a, b) t).1, (nestPair (a, b) t).2, yt, hyt1, hyt2⟩
      have hQa : Q.a = (nestPair (a, b) t).1 := rfl
      have hQb : Q.b = (nestPair (a, b) t).2 := rfl
      have hneQ : Work.ELPull.arcLen Q.a Q.b ≠ 0 := by rw [hQa, hQb]; exact hgt
      have hIu : Work.ELPull.IsUnwrappedArcOf Q (nestArc (9 - t) (nestPair (a, b) t)) :=
        isUnwrappedArcOf_nestArc Q (9 - t) (nestPair (a, b) t) hQa hQb
      have hcvQ : c ∈ Work.ELPull.arcSide hN Q (nestArc (9 - t) (nestPair (a, b) t)).2
          (nestArc (9 - t) (nestPair (a, b) t)).1 := hcv t Q htlt hQa hQb
      obtain ⟨y', _, hl1, hl2⟩ :=
        Work.ELPull.pb1Top hc hN hφ htop Q hneQ (nestArc (9 - t) (nestPair (a, b) t))
          hIu hcvQ (nestK (9 - t))
      have hstep : nestPair (a, b) (t + 1) =
          Work.ELPull.preArc (nestK (9 - t)) (nestArc (9 - t) (nestPair (a, b) t)) := rfl
      have hpair : nestPair (a, b) (t + 1) = nestStep (9 - t) (nestPair (a, b) t) := rfl
      refine ⟨⟨y', ?_, ?_⟩, ?_⟩
      · rw [hstep]; exact hl1
      · rw [hstep]; exact hl2
      · rw [hpair]
        exact arcLen_nestStep_ne_zero (9 - t) (nestPair (a, b) t) hgt
  obtain ⟨⟨y', hy1, hy2⟩, _⟩ := key 10 (le_refl 10)
  exact ⟨y', hy1, hy2⟩

end Work.ELNest
