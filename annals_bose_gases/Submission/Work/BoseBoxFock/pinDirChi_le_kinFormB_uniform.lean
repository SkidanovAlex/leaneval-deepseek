import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.pairRowS2Bound
import Submission.Work.BoseBoxFock.pinDirChiExp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-!
# `Work.BoseBoxFock.pinDirChi_le_kinFormB_uniform`

The *uniform-in-`n`* form of `Work.BoseBoxFock.pinDirChi_le_kinFormB`: the constant `C` can be
chosen uniformly in the particle number `n` and in the box state `Φ`.

The proof is the slot assembly of `Work.BoseBoxFock.pinDirChiExp`, which is the same assembly as
`Work.BoseBoxFock.pinDirChi_le_kinFormB` with the constant exposed.  The only point that matters
for uniformity is that the whole constant is built from data of the *box parameters*
`(ℓ, d, s, εT, b)` alone: in particular the bound `D` on the derivative of the window
`chiScale ℓ` is extracted once, from `Work.BSKinetic.exists_chiScale_bound` at
`ℓ = sideAt μ (a v)`, *before* the particle number is introduced.  The one-body Dirichlet
constant `4 + 16·κ·chiPlateau² + 24·D²`, with `κ = (1−εT)(2sℓ)⁻² + εT(2dsℓ)⁻²`, is then
independent of `n` and of `Φ`, and dominates the slot-`(i,j)` summands of `pinDirChi` slot by
slot.

The state-level bookkeeping (`normB` being the box `L²`-mass, the sum over the `n` slots) is the
identification `Work.BoseBoxFix.normB v μ n Φ = Work.BoseKinLoc.sqNormB n ℓ Φ`.
-/

theorem pinDirChi_le_kinFormB_uniform {v : ℝ³ → ℝ}
    {h : Work.UBB.ScatSol v} {μ : ℝ} (hav : 0 < BoseGases.a v) (hμ : 0 < μ)
    (hd : 0 < (Work.BoseBox.paramsAt μ (BoseGases.a v)).d)
    (hs : 0 < (Work.BoseBox.paramsAt μ (BoseGases.a v)).s)
    (hb : 0 ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).b)
    (hεT0 : 0 ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT)
    (hεT1 : (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ)
      (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
      Work.BoseBoxFock.pinDirChi (Work.BoseBox.sideAt μ (BoseGases.a v))
          (fun x => ((Φ x : ℝ) : ℂ))
        ≤ C * (Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
              (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
              (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
              (Work.BoseBox.paramsAt μ (BoseGases.a v)).b
              (Φ : Submission.BoseGases.X n → ℝ)
            + (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) := by
  -- abbreviations for the box data (`set` also rewrites them in the goal)
  set ℓ : ℝ := Work.BoseBox.sideAt μ (BoseGases.a v) with hℓdef
  set d : ℝ := (Work.BoseBox.paramsAt μ (BoseGases.a v)).d with hddef
  set s : ℝ := (Work.BoseBox.paramsAt μ (BoseGases.a v)).s with hsdef
  set εT : ℝ := (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT with hεTdef
  set b : ℝ := (Work.BoseBox.paramsAt μ (BoseGases.a v)).b with hbdef
  have hℓ : 0 < ℓ := by rw [hℓdef]; exact Work.BoseBox.sideAt_pos hμ hav
  have hd' : 0 < d := by rw [hddef]; exact hd
  have hs' : 0 < s := by rw [hsdef]; exact hs
  have hb' : 0 ≤ b := by rw [hbdef]; exact hb
  have hεT0' : 0 ≤ εT := by rw [hεTdef]; exact hεT0
  have hεT1' : εT ≤ 1 := by rw [hεTdef]; exact hεT1
  -- the derivative bound of the window: extracted once, at `ℓ` only (no dependence on `n`)
  obtain ⟨C₀, D, hC₀0, hD0, hC₀bd, hDbd⟩ :=
    Work.BSKinetic.exists_chiScale_bound (s := ℓ) (ne_of_gt hℓ)
  -- the constant is nonnegative in each of its summands
  have hκ : 0 ≤ (1 - εT) * ((2 * (s * ℓ))⁻¹) ^ 2 + εT * ((2 * (d * s * ℓ))⁻¹) ^ 2 := by
    have h1 : 0 ≤ 1 - εT := by linarith
    exact add_nonneg (mul_nonneg h1 (sq_nonneg _)) (mul_nonneg hεT0' (sq_nonneg _))
  have hCpos : 0 < 4 + 16 * ((1 - εT) * ((2 * (s * ℓ))⁻¹) ^ 2
        + εT * ((2 * (d * s * ℓ))⁻¹) ^ 2) * Work.BoseFixB1S.chiPlateau ^ 2 + 24 * D ^ 2 := by
    nlinarith [mul_nonneg hκ (sq_nonneg Work.BoseFixB1S.chiPlateau), sq_nonneg D]
  refine ⟨_, hCpos, ?_⟩
  intro n Φ
  -- the slot assembly with the explicit, `n`-independent constant
  have hΦ := pinDirChiExp (n := n) (l := ℓ) (d := d) (s := s) (εT := εT) (b := b) (D := D)
    hℓ hd' hs' hb' hεT0' hεT1' hD0 hDbd Φ
  -- `normB` is the box `L²`-mass at the sliding box
  rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB, ← hℓdef]
  exact hΦ

end Work.BoseBoxFock
