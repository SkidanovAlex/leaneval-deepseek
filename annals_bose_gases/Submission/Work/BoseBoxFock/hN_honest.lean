import Mathlib
import Submission.Work.BoseBoxFock.KzOpC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.BoseBoxFock.hN_honest` — the total-number row `T.N` under `split`

The honest datum's `TildeData.N` is the *total* number operator `totNumOp m` of the
mode lattice (`tildeDataHon`).  This module transports it through
`Work.BoseB4.split` into the ⟨condensate | spectators⟩ picture: with
`N = n₀ + n₊` (`n₀ = a₀†a₀` on the condensate coordinate, `n₊` the excited number),

    `split (N y) = (a₀†a₀ + 1 ⊗ n₊) (split y)`.

In the anti-normal (`monoOp`) shape used by the `thm:Kafz` dictionary, that is the
statement proved here:

    `split (N y) = (monoOp 1 1 1 + monoOp 0 0 (nPlusC − 1)) (split y)`,

the `−1` being the vacuum commutator `a₀a₀† = a₀†a₀ + 1` (`monoOp_11_00_numOp`).

## Route

* `hN_split_n0` — `split ∘ n₀ = numOp ∘ split` (the condensate row);
* `hN_split_gap` — `split ((N − n₀) x) = lift nPlusC (split x)` (`split_gap`'s `c = 1`);
* `hN_split_totNumOp` — the two added: `split (N x) = (numOp + lift nPlusC) (split x)`;
* `hN_monoOp11_eq` / `hN_monoOp00_sub` — `monoOp 1 1 1 = numOp + 1` and
  `monoOp 0 0 A = lift A` (hence `monoOp 0 0 (nPlusC − 1) = lift nPlusC − 1`);
* `hN_op_identity` — the two anti-normal slots reassemble into `numOp + lift nPlusC`;
* `hN_honest` — `HonestBoxFam`'s `T.N` is `totNumOp m` definitionally, so the
  transport applies.
-/

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Additivity of `lift` in the negative direction -/

/-- The levelwise lift is subtractive in the spectator operator. -/
lemma hN_lift_sub {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (B B' : E →ₗ[ℂ] E) :
    Work.BoseB4.lift (B - B') = Work.BoseB4.lift B - Work.BoseB4.lift B' := by
  ext Ψ n
  simp

/-- The levelwise lift is compatible with negation. -/
lemma hN_lift_neg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (B : E →ₗ[ℂ] E) : Work.BoseB4.lift (-B) = -Work.BoseB4.lift B := by
  ext Ψ n
  simp

/-! ## The two anti-normal slots with the identity spectator -/

/-- `monoOp 1 1 1 = numOp + 1`, i.e. `a₀a₀† = a₀†a₀ + 1`
(equivalently `Work.BoseB4.monoOp_11_00_numOp` with `B = 1`, `lift 1 = 1`). -/
lemma hN_monoOp11_eq {m : ℕ} [NeZero m] :
    Work.BoseB4.monoOp 1 1 (1 : Work.BoseB4.cfock (Work.BoseB4.Excited m) →ₗ[ℂ]
        Work.BoseB4.cfock (Work.BoseB4.Excited m))
      = Work.BoseB4.numOp + 1 := by
  have h := Work.BoseB4.monoOp_11_00_numOp (m := m)
    (1 : Work.BoseB4.cfock (Work.BoseB4.Excited m) →ₗ[ℂ]
      Work.BoseB4.cfock (Work.BoseB4.Excited m))
  have h2 : Work.BoseB4.numOp ∘ₗ Work.BoseB4.lift
      (1 : Work.BoseB4.cfock (Work.BoseB4.Excited m) →ₗ[ℂ]
        Work.BoseB4.cfock (Work.BoseB4.Excited m))
      = Work.BoseB4.numOp := by
    rw [Work.BoseB4.split_Hmu_lift_one, comp_one_self]
  simp only [Work.BoseB4.monoOp_zero_zero, hN_lift_neg, Work.BoseB4.split_Hmu_lift_one, h2] at h
  have h3 := congrArg (fun f => f + 1) h
  simp only [add_assoc, neg_add_cancel, add_zero] at h3
  exact h3

/-- `monoOp 0 0 (A − 1) = lift A − 1` (`lift` is additive and `lift 1 = 1`). -/
lemma hN_monoOp00_sub {m : ℕ} [NeZero m]
    (A : Work.BoseB4.cfock (Work.BoseB4.Excited m) →ₗ[ℂ]
      Work.BoseB4.cfock (Work.BoseB4.Excited m)) :
    Work.BoseB4.monoOp 0 0 (A - 1) = Work.BoseB4.lift A - 1 := by
  rw [Work.BoseB4.monoOp_zero_zero, hN_lift_sub, Work.BoseB4.split_Hmu_lift_one]

/-- The anti-normal reassembly of the target's right-hand side. -/
lemma hN_op_identity {m : ℕ} [NeZero m] :
    (Work.BoseB4.monoOp 1 1 (1 : Work.BoseB4.cfock (Work.BoseB4.Excited m) →ₗ[ℂ]
        Work.BoseB4.cfock (Work.BoseB4.Excited m))
      + Work.BoseB4.monoOp 0 0 ((nPlusC (m := m)) - 1))
    = Work.BoseB4.numOp + Work.BoseB4.lift (nPlusC (m := m)) := by
  rw [hN_monoOp11_eq, hN_monoOp00_sub]
  abel

/-! ## The total number operator under `split` -/

/-- The condensate row: `split ∘ n₀ = numOp ∘ split`. -/
lemma hN_split_n0 {m : ℕ} [NeZero m] (x : Work.BoseB4.RealFock m) :
    Work.BoseB4.split (n0 x) = Work.BoseB4.numOp (Work.BoseB4.split x) := by
  show Work.BoseB4.split ((Work.BoseB4.cre m 0) ((Work.BoseB4.ann m 0) x))
      = Work.BoseB4.numOp (Work.BoseB4.split x)
  rw [split_cre_zero, split_ann_zero]
  rfl

/-- The excited row: `split ((N − n₀) x) = lift n₊ (split x)`. -/
lemma hN_split_gap {m : ℕ} [NeZero m] (x : Work.BoseB4.RealFock m) :
    Work.BoseB4.split ((Work.BoseB4.totNumOp m - n0
        : Work.BoseB4.RealFock m →ₗ[ℝ] Work.BoseB4.RealFock m) x)
      = Work.BoseB4.lift (nPlusC (m := m)) (Work.BoseB4.split x) := by
  have h := split_gap (m := m) (1 : ℝ) x
  rw [one_smul] at h
  rw [h, one_smul, Work.BoseB4.monoOp_zero_zero]
  rfl

/-- **The total number operator under `split`**: `N = n₀ + n₊`. -/
lemma hN_split_totNumOp {m : ℕ} [NeZero m] (x : Work.BoseB4.RealFock m) :
    Work.BoseB4.split (Work.BoseB4.totNumOp m x)
      = (Work.BoseB4.numOp (E := Work.BoseB4.cfock (Work.BoseB4.Excited m))
          + Work.BoseB4.lift (nPlusC (m := m))) (Work.BoseB4.split x) := by
  have hdecomp : Work.BoseB4.totNumOp m x
      = n0 x + (Work.BoseB4.totNumOp m - n0
          : Work.BoseB4.RealFock m →ₗ[ℝ] Work.BoseB4.RealFock m) x := by
    rw [LinearMap.sub_apply]
    abel
  rw [hdecomp, map_add, hN_split_n0, hN_split_gap, LinearMap.add_apply]

/-! ## The requested row -/

theorem hN_honest (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ) :
    ∀ y : Work.BoseB4.RealFock (HM μ).m,
      Work.BoseB4.split ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.N y)
        = (Work.BoseB4.monoOp 1 1
              (1 : Work.BoseB4.cfock (Work.BoseB4.Excited (HM μ).m) →ₗ[ℂ]
                Work.BoseB4.cfock (Work.BoseB4.Excited (HM μ).m))
            + Work.BoseB4.monoOp 0 0
                ((Work.BoseBoxFock.nPlusC (m := (HM μ).m))
                  - (1 : Work.BoseB4.cfock (Work.BoseB4.Excited (HM μ).m) →ₗ[ℂ]
                      Work.BoseB4.cfock (Work.BoseB4.Excited (HM μ).m))))
          (Work.BoseB4.split y) := by
  intro y
  -- `HonestBoxFam`'s `TildeData` has `N = totNumOp m` definitionally
  show Work.BoseB4.split (Work.BoseB4.totNumOp (HM μ).m y)
      = (Work.BoseB4.monoOp 1 1
              (1 : Work.BoseB4.cfock (Work.BoseB4.Excited (HM μ).m) →ₗ[ℂ]
                Work.BoseB4.cfock (Work.BoseB4.Excited (HM μ).m))
            + Work.BoseB4.monoOp 0 0
                ((Work.BoseBoxFock.nPlusC (m := (HM μ).m))
                  - (1 : Work.BoseB4.cfock (Work.BoseB4.Excited (HM μ).m) →ₗ[ℂ]
                      Work.BoseB4.cfock (Work.BoseB4.Excited (HM μ).m))))
          (Work.BoseB4.split y)
  rw [hN_split_totNumOp y, hN_op_identity]

end Work.BoseBoxFock
