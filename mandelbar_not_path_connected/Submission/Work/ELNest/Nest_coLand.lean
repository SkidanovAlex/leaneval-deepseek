/-
# EL nest, part 7 (N1): co-landing of the nest pairs at `z₁` for all levels

The first clause of the contract's N1: the rays `βₙ` and `βₙ'` of the nest at `z₁` co-land, for
every `n`.  The level-`0` case is `uPair_lands` (the certificate C5 chain from the pair at `f⁴z₁`
down to the `u`-pair); every further level is one application of the certified pull-back chain
`nestChain_lands` with the angle identification `nestPair_nest`.
-/
import Mathlib
import Submission.Work.ELNest.Chain
import Submission.Work.ELNest.uPair_lands
import Submission.Work.ELNest.Exists
import Submission.Work.ELNest.nestChain_lands
import Submission.Work.ELNest.nestPair_nest
import Submission.Work.ELNest.bAng_range
import Submission.Work.ELPull.pb1Top

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Topology Function
open scoped Topology ComplexConjugate

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELNest

open Work.EL

/-- The rays of angle `θ` and `θ + 1` are the same ray. -/
theorem landsN_add_one {c : ℂ} {hN : Work.ELPull.DynB c} {θ : ℝ} {y : ℂ}
    (h : Work.ELPull.LandsN hN θ y) : Work.ELPull.LandsN hN (θ + 1) y := by
  have hfun : (fun t : ℝ => hN.rayPt (θ + 1) t) = (fun t : ℝ => hN.rayPt θ t) := by
    funext t
    simpa using Work.ELPull.rayPt_add_int' hN θ t 1
  rw [Work.ELPull.LandsN] at h ⊢
  rwa [hfun]

/-- The two nest angles at level `n` are distinct modulo `1`, so the chain is non-degenerate. -/
theorem bAng_arcLen_ne_zero (n : ℕ) : Work.EL.arcLen (bAng n) (bAng' n) ≠ 0 := by
  have h1 : bAng n < alpha1 := (bAng_range n).1.2
  have h2 : alpha2 < bAng' n := (bAng_range n).2.1
  have h3 : alpha1 < alpha2 := by norm_num [alpha1, alpha2]
  have hpos : 0 < bAng' n - bAng n := by linarith
  have hb0 : 0 < bAng n := (bAng_range n).1.1
  have hlt : bAng' n - bAng n < 1 := by
    have : bAng' n < 1 := by
      have := (bAng_range n).2.2
      have hb : beta0' < 1 := by norm_num [beta0']
      linarith
    linarith
  have hf : Int.fract (bAng' n - bAng n) = bAng' n - bAng n :=
    Int.fract_eq_self.mpr ⟨le_of_lt hpos, hlt⟩
  rw [Work.EL.arcLen, hf]
  exact ne_of_gt hpos

/-- **One step of the nest**: the co-landing of the level-`n` pair yields the co-landing of the
level-`n+1` pair, by the certified chain. -/
theorem nest_step {c : ℂ} (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar)
    (hN : Work.ELPull.DynB c)
    (hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c))
    (htop : Work.ELPull.PB1Top hN) (n : ℕ) {y : ℂ}
    (hy : Work.ELPull.LandsN hN (bAng n) y) (hy' : Work.ELPull.LandsN hN (bAng' n) y)
    (hcv : ∀ (t : ℕ) (Q : Work.ELPull.CoPair hN), t < 10 →
      Q.a = (nestPair (bAng n, bAng' n) t).1 → Q.b = (nestPair (bAng n, bAng' n) t).2 →
      c ∈ Work.ELPull.arcSide hN Q (nestArc (9 - t) (nestPair (bAng n, bAng' n) t)).2
        (nestArc (9 - t) (nestPair (bAng n, bAng' n) t)).1) :
    ∃ y' : ℂ, Work.ELPull.LandsN hN (bAng (n + 1)) y' ∧
      Work.ELPull.LandsN hN (bAng' (n + 1)) y' := by
  obtain ⟨y', h1, h2⟩ :=
    nestChain_lands hc hN hφ htop (bAng n) (bAng' n) hy hy' (bAng_arcLen_ne_zero n) hcv
  rw [nestPair_nest n] at h1 h2
  exact ⟨y', h1, h2⟩

/-- **N1, co-landing for all levels** (in the orientation of the certificate chain). -/
theorem nest_coLands {c : ℂ} (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar)
    (hN : Work.ELPull.DynB c)
    (hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c))
    (htop : Work.ELPull.PB1Top hN)
    (hbase : ∃ y : ℂ, Work.ELPull.LandsN hN (bAng 0) y ∧ Work.ELPull.LandsN hN (bAng' 0) y)
    (hcv : ∀ (n t : ℕ) (Q : Work.ELPull.CoPair hN), t < 10 →
      Q.a = (nestPair (bAng n, bAng' n) t).1 → Q.b = (nestPair (bAng n, bAng' n) t).2 →
      c ∈ Work.ELPull.arcSide hN Q (nestArc (9 - t) (nestPair (bAng n, bAng' n) t)).2
        (nestArc (9 - t) (nestPair (bAng n, bAng' n) t)).1) :
    ∀ n : ℕ, ∃ y : ℂ, Work.ELPull.LandsN hN (bAng n) y ∧ Work.ELPull.LandsN hN (bAng' n) y := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
    obtain ⟨y, h1, h2⟩ := ih
    exact nest_step hc hN hφ htop n h1 h2 (hcv n)

/-- **N1, in the form of the interface**: for every `n` the rays of angles `βₙ'` and `βₙ + 1`
(the two angles of the level-`n` pair `NestData.Qp n`) co-land. -/
theorem nest_pair_coLands {c : ℂ} (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar)
    (hN : Work.ELPull.DynB c)
    (hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c))
    (htop : Work.ELPull.PB1Top hN)
    (hbase : ∃ y : ℂ, Work.ELPull.LandsN hN (bAng 0) y ∧ Work.ELPull.LandsN hN (bAng' 0) y)
    (hcv : ∀ (n t : ℕ) (Q : Work.ELPull.CoPair hN), t < 10 →
      Q.a = (nestPair (bAng n, bAng' n) t).1 → Q.b = (nestPair (bAng n, bAng' n) t).2 →
      c ∈ Work.ELPull.arcSide hN Q (nestArc (9 - t) (nestPair (bAng n, bAng' n) t)).2
        (nestArc (9 - t) (nestPair (bAng n, bAng' n) t)).1) :
    ∀ n : ℕ, ∃ y : ℂ, Work.ELPull.LandsN hN (bAng' n) y ∧
      Work.ELPull.LandsN hN (bAng n + 1) y := by
  intro n
  obtain ⟨y, h1, h2⟩ := nest_coLands hc hN hφ htop hbase hcv n
  exact ⟨y, h2, landsN_add_one h1⟩

/-- The level-`0` pair of the chain is the `u`-pair, whose co-landing is `uPair_lands`. -/
theorem bAng_zero_base : Work.ELNest.bAng' 0 = Work.ELNest.beta0' := bAng_zero

theorem bAng_zero_val : Work.ELNest.bAng 0 = Work.ELNest.beta0 := by simp [bAng]

/-- **N1, co-landing for all levels, with the level-`0` input discharged**: given the
hypotheses of `uPair_lands` (the certificate C5 chain from the pair at `f⁴z₁`) and the side
conditions of the nest chain at every level, the pairs `(βₙ', βₙ + 1)` of the nest at `z₁`
co-land for every `n`. -/
theorem nest_pair_coLands_of_uPair {c : ℂ} (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar)
    (hN : Work.ELPull.DynB c)
    (hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c))
    (htop : Work.ELPull.PB1Top hN)
    (hbase₀ : ∃ y : ℂ, Work.ELPull.LandsN hN ((Work.ELPull.Cert.uChain 10).1 : ℝ) y ∧
      Work.ELPull.LandsN hN ((Work.ELPull.Cert.uChain 10).2 : ℝ) y)
    (hcv₀ : ∀ (i : Fin 10) (Q : Work.ELPull.CoPair hN),
      Q.a = ((Work.ELPull.Cert.uChain i.succ).1 : ℝ) →
      Q.b = ((Work.ELPull.Cert.uChain i.succ).2 : ℝ) →
      c ∈ Work.ELPull.arcSide hN Q ((Work.ELPull.Cert.uChainArc i).2 : ℝ)
        ((Work.ELPull.Cert.uChainArc i).1 : ℝ))
    (hcv : ∀ (n t : ℕ) (Q : Work.ELPull.CoPair hN), t < 10 →
      Q.a = (nestPair (bAng n, bAng' n) t).1 → Q.b = (nestPair (bAng n, bAng' n) t).2 →
      c ∈ Work.ELPull.arcSide hN Q (nestArc (9 - t) (nestPair (bAng n, bAng' n) t)).2
        (nestArc (9 - t) (nestPair (bAng n, bAng' n) t)).1) :
    ∀ n : ℕ, ∃ y : ℂ, Work.ELPull.LandsN hN (bAng' n) y ∧
      Work.ELPull.LandsN hN (bAng n + 1) y := by
  obtain ⟨y, hy, hy'⟩ := uPair_lands hc hN hφ htop hbase₀ hcv₀
  have hU0 : ((Work.ELPull.Cert.U0 : ℚ) : ℝ) = bAng 0 := by
    simp only [Work.ELPull.Cert.U0, Work.ELPull.qq, bAng_zero_val, beta0]
    norm_num
  have hU0p : ((Work.ELPull.Cert.U0p : ℚ) : ℝ) = bAng' 0 := by
    simp only [Work.ELPull.Cert.U0p, Work.ELPull.qq, bAng_zero_base, beta0']
    norm_num
  exact nest_pair_coLands hc hN hφ htop ⟨y, hU0 ▸ hy, hU0p ▸ hy'⟩ hcv

end Work.ELNest
