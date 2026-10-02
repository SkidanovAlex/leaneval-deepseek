/-
# `armC_W0`: the arm-`C` chains pull back the arc `W₀ = (α₁, α₂)`

The chains of `Work.ELNest.ArmChain` are the recursive pull-backs of the three level-`n` arm pairs
of the `b₂`-nest.  At step `t` of the arm-`C` chain (`armPairOf nearC kC (armC1 n, armC2 n) t`,
`t < 6`) the next preimage arc fed to `pb1Top` is `armArcOf nearC (5 - t) p`, and the `hcvC` field
of `ChainInputs` (see `NOTES_LEAD_mandelbar_hcv.md` §3) needs the *orientation* statement

  `W₀ = (α₁, α₂) ⊆ J = (I.2, I.1)`,   `I = armArcOf nearC (5 - t) p`,

i.e. that the arc `W₀` cut out by the two root-portrait angles `α₁ = 371/1023`,
`α₂ = 404/1023` lies in the arc which is **not** pulled back by the chain step.

**Proof.**  `armArcOf_J` reduces `InArc θ I.2 I.1` to `InArc θ p.2 p.1` (far arc) or
`InArc θ p.1 p.2` (near arc), the two endpoints being congruent mod `1` to the two endpoints of
`p` (`InArc_add_int_pair` and `Int.fract_add_floor`).  The six pairs of the arm-`C` chain are the
affine families `armPairC_t` in `y = 64⁻ⁿ ∈ (0,1]` (`armC1_closed`, `armC2_closed` and the step
lemmas `armStep_*` of `Work.ELNest.armChain_nest`), and for each of the six rows of the table of
`NOTES_LEAD_mandelbar_hcv.md` §3.2 (arm C, lifts `k = 1` at `t = 2` and `k = 0` otherwise) the
single lemma `W0_sub_of_lift` checks

  `p ≤ α₁ + k`  and  `α₂ + k ≤ p + arcLen p q`

with `linarith`, `arcLen` being the explicit affine expression provided by `Int.fract_eq_iff`.
-/
import Mathlib
import Submission.Work.ELAssembly.Chains
import Submission.Work.ELNest.ArmChain

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology ComplexConjugate

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELAssembly

namespace CW0

open Work.EL Work.ELNest

/-! ## The six arm-`C` states, in closed form -/

/-- The level-`n` arm-`C` pair `(armC1 n, armC2 n)`. -/
def st0 (y : ℝ) : ℝ × ℝ := ((37:ℝ)/63 + ((4624:ℝ)/21483)*y, (22:ℝ)/63 - ((656:ℝ)/21483)*y)

/-- The arm-`C` state `V1` at step `1`. -/
def st1 (y : ℝ) : ℝ × ℝ := ((52:ℝ)/63 + ((328:ℝ)/21483)*y, (13:ℝ)/63 - ((2312:ℝ)/21483)*y)

/-- The arm-`C` state `T0` at step `2`. -/
def st2 (y : ℝ) : ℝ × ℝ := ((25:ℝ)/63 + ((1156:ℝ)/21483)*y, (37:ℝ)/63 - ((164:ℝ)/21483)*y)

/-- The arm-`C` state `U1` at step `3`. -/
def st3 (y : ℝ) : ℝ × ℝ := ((13:ℝ)/63 + ((82:ℝ)/21483)*y, (19:ℝ)/63 - ((578:ℝ)/21483)*y)

/-- The arm-`C` state `S0` at step `4`. -/
def st4 (y : ℝ) : ℝ × ℝ := ((22:ℝ)/63 + ((289:ℝ)/21483)*y, (25:ℝ)/63 - ((41:ℝ)/21483)*y)

/-- The arm-`C` state `S1` at step `5`. -/
def st5 (y : ℝ) : ℝ × ℝ := ((52:ℝ)/63 - ((289:ℝ)/42966)*y, (19:ℝ)/63 + ((41:ℝ)/42966)*y)

/-! ## Pure facts about the cyclic arc -/

/-- `InArc` only sees its three arguments modulo `1`. -/
theorem InArc_add_int_pair (θ a b : ℝ) (m m' : ℤ) :
    Work.EL.InArc θ (a + (m:ℝ)) (b + (m':ℝ)) ↔ Work.EL.InArc θ a b := by
  unfold Work.EL.InArc Work.EL.arcLen
  rw [show θ - (a + (m:ℝ)) = (θ - a) + ((-m : ℤ) : ℝ) by push_cast; ring, Int.fract_add_intCast,
      show b + (m':ℝ) - (a + (m:ℝ)) = (b - a) + ((m' - m : ℤ) : ℝ) by push_cast; ring,
      Int.fract_add_intCast]

/-- **The lift criterion.**  If the closed arc `[p, p + arcLen p q]` (unwrapped) contains
`[α₁ + k, α₂ + k]` for some integer `k`, then it contains the open arc `W₀ = (α₁, α₂)`. -/
theorem W0_sub_of_lift (k : ℤ) {p q : ℝ} (h1 : p ≤ Work.EL.alpha1 + (k : ℝ))
    (h2 : Work.EL.alpha2 + (k : ℝ) ≤ p + Work.EL.arcLen p q) :
    ∀ θ : ℝ, Work.EL.InArc θ Work.EL.alpha1 Work.EL.alpha2 → Work.EL.InArc θ p q := by
  intro θ ⟨hθ1, hθ2⟩
  have hlen : Work.EL.arcLen Work.EL.alpha1 Work.EL.alpha2 = Work.EL.alpha2 - Work.EL.alpha1 := by
    rw [Work.EL.arcLen, Work.EL.alpha1, Work.EL.alpha2, Int.fract_eq_iff]
    exact ⟨by norm_num, by norm_num, 0, by norm_num⟩
  set f : ℝ := Int.fract (θ - Work.EL.alpha1) with hf
  have hf2 : f < Work.EL.alpha2 - Work.EL.alpha1 := by
    rw [hf]; rw [hlen] at hθ2; exact hθ2
  set θ' : ℝ := Work.EL.alpha1 + (k : ℝ) + f with hθ'
  have hθ'lo : p < θ' := by rw [hθ']; linarith
  have hθ'hi : θ' < p + Work.EL.arcLen p q := by rw [hθ']; linarith
  have hlt1 : Work.EL.arcLen p q < 1 := Work.EL.arcLen_lt_one p q
  have hfrac : Int.fract (θ - p) = Int.fract (θ' - p) := by
    have hm : θ = θ' + ((⌊θ - Work.EL.alpha1⌋ - k : ℤ) : ℝ) := by
      rw [hθ', hf]
      have := Int.fract_add_floor (θ - Work.EL.alpha1)
      push_cast
      linarith
    rw [hm, show θ' + ((⌊θ - Work.EL.alpha1⌋ - k : ℤ) : ℝ) - p
        = (θ' - p) + ((⌊θ - Work.EL.alpha1⌋ - k : ℤ) : ℝ) by ring, Int.fract_add_intCast]
  have hself : Int.fract (θ' - p) = θ' - p :=
    Int.fract_eq_self.mpr ⟨le_of_lt (by linarith), by linarith⟩
  exact ⟨by rw [hfrac, hself]; linarith, by rw [hfrac, hself]; linarith⟩

/-- The arc `J = (I.2, I.1)` of `I = armArcOf near j p` is `(p.2, p.1)` for the far arc and
`(p.1, p.2)` for the near arc. -/
theorem armArcOf_J (near : ℕ → Bool) (j : ℕ) (p : ℝ × ℝ) (θ : ℝ) :
    Work.EL.InArc θ (armArcOf near j p).2 (armArcOf near j p).1 ↔
      (if near j then Work.EL.InArc θ p.1 p.2 else Work.EL.InArc θ p.2 p.1) := by
  by_cases h : near j = true
  · rw [if_pos h, armArcOf, if_pos h]
    show Work.EL.InArc θ (p.2 + Int.fract (p.1 - p.2)) p.2 ↔ Work.EL.InArc θ p.1 p.2
    exact Work.ELPull.InArc_congr (θ := θ) (a := p.2 + Int.fract (p.1 - p.2)) (b := p.2)
      (a' := p.1) (b' := p.2) ⟨0, by push_cast; ring⟩
      ⟨-(⌊p.1 - p.2⌋), by push_cast; linarith [Int.fract_add_floor (p.1 - p.2)]⟩
      ⟨0, by push_cast; ring⟩
  · rw [if_neg h, armArcOf, if_neg h]
    show Work.EL.InArc θ (p.1 + Int.fract (p.2 - p.1)) p.1 ↔ Work.EL.InArc θ p.2 p.1
    exact Work.ELPull.InArc_congr (θ := θ) (a := p.1 + Int.fract (p.2 - p.1)) (b := p.1)
      (a' := p.2) (b' := p.1) ⟨0, by push_cast; ring⟩
      ⟨-(⌊p.2 - p.1⌋), by push_cast; linarith [Int.fract_add_floor (p.2 - p.1)]⟩
      ⟨0, by push_cast; ring⟩

/-! ## The six pairs of the arm-`C` chain, as functions of `y = 64⁻ⁿ` -/

lemma armPairC_0 (n : ℕ) : armPairOf nearC kC (armC1 n, armC2 n) 0 = st0 ((64:ℝ)^n)⁻¹ := by
  rw [armC1_closed n, armC2_closed n]
  rfl

lemma armPairC_1 (n : ℕ) : armPairOf nearC kC (armC1 n, armC2 n) 1 = st1 ((64:ℝ)^n)⁻¹ := by
  have hy : (0:ℝ) < ((64:ℝ)^n)⁻¹ := by positivity
  have hy1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  change armStepOf nearC kC 5 (armPairOf nearC kC (armC1 n, armC2 n) 0) = st1 ((64:ℝ)^n)⁻¹
  rw [armPairC_0 n]
  exact armStep_C0_V1 nearC kC 5 (by decide) (by norm_num [kC]) _ hy hy1

lemma armPairC_2 (n : ℕ) : armPairOf nearC kC (armC1 n, armC2 n) 2 = st2 ((64:ℝ)^n)⁻¹ := by
  have hy : (0:ℝ) < ((64:ℝ)^n)⁻¹ := by positivity
  have hy1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  change armStepOf nearC kC 4 (armPairOf nearC kC (armC1 n, armC2 n) 1) = st2 ((64:ℝ)^n)⁻¹
  rw [armPairC_1 n]
  exact armStep_V1_B0 nearC kC 4 (by decide) (by norm_num [kC]) _ hy hy1

lemma armPairC_3 (n : ℕ) : armPairOf nearC kC (armC1 n, armC2 n) 3 = st3 ((64:ℝ)^n)⁻¹ := by
  have hy : (0:ℝ) < ((64:ℝ)^n)⁻¹ := by positivity
  have hy1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  change armStepOf nearC kC 3 (armPairOf nearC kC (armC1 n, armC2 n) 2) = st3 ((64:ℝ)^n)⁻¹
  rw [armPairC_2 n]
  exact armStep_B0_U1 nearC kC 3 (by decide) (by norm_num [kC]) _ hy hy1

lemma armPairC_4 (n : ℕ) : armPairOf nearC kC (armC1 n, armC2 n) 4 = st4 ((64:ℝ)^n)⁻¹ := by
  have hy : (0:ℝ) < ((64:ℝ)^n)⁻¹ := by positivity
  have hy1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  change armStepOf nearC kC 2 (armPairOf nearC kC (armC1 n, armC2 n) 3) = st4 ((64:ℝ)^n)⁻¹
  rw [armPairC_3 n]
  exact armStep_U1_A0 nearC kC 2 (by decide) (by norm_num [kC]) _ hy hy1

lemma armPairC_5 (n : ℕ) : armPairOf nearC kC (armC1 n, armC2 n) 5 = st5 ((64:ℝ)^n)⁻¹ := by
  have hy : (0:ℝ) < ((64:ℝ)^n)⁻¹ := by positivity
  have hy1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  change armStepOf nearC kC 1 (armPairOf nearC kC (armC1 n, armC2 n) 4) = st5 ((64:ℝ)^n)⁻¹
  rw [armPairC_4 n]
  exact armStep_A0_S1 nearC kC 1 (by decide) (by norm_num [kC]) _ hy hy1

/-! ## The six rows of the arm-`C` table

The arc `J` of the step is `(p.2, p.1)` for the far arc (rows `t = 0,1,2,3,5`) and `(p.1, p.2)`
for the near arc (row `t = 4`); the lift is `k = 1` only at `t = 2`, else `k = 0`. -/

/-- Row `t = 0`: the far arc of the level-`n` arm-`C` pair itself. -/
lemma W0_st0 (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) : ∀ θ : ℝ,
    Work.EL.InArc θ Work.EL.alpha1 Work.EL.alpha2 → Work.EL.InArc θ (st0 y).2 (st0 y).1 := by
  intro θ hθ
  have harc : Work.EL.arcLen (st0 y).2 (st0 y).1 = (5:ℝ)/21 + ((5280:ℝ)/21483) * y := by
    rw [Work.EL.arcLen, Int.fract_eq_iff]
    refine ⟨?_, ?_, 0, ?_⟩
    · linarith
    · linarith
    · rw [st0]; dsimp only; push_cast; ring
  refine W0_sub_of_lift 0 ?_ ?_ θ hθ
  · rw [Work.EL.alpha1, Int.cast_zero, add_zero, st0]; dsimp only; linarith
  · rw [harc, Work.EL.alpha2, Int.cast_zero, add_zero, st0]; dsimp only; linarith

/-- Row `t = 1`. -/
lemma W0_st1 (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) : ∀ θ : ℝ,
    Work.EL.InArc θ Work.EL.alpha1 Work.EL.alpha2 → Work.EL.InArc θ (st1 y).2 (st1 y).1 := by
  intro θ hθ
  have harc : Work.EL.arcLen (st1 y).2 (st1 y).1 = (13:ℝ)/21 + ((2640:ℝ)/21483) * y := by
    rw [Work.EL.arcLen, Int.fract_eq_iff]
    refine ⟨?_, ?_, 0, ?_⟩
    · linarith
    · linarith
    · rw [st1]; dsimp only; push_cast; ring
  refine W0_sub_of_lift 0 ?_ ?_ θ hθ
  · rw [Work.EL.alpha1, Int.cast_zero, add_zero, st1]; dsimp only; linarith
  · rw [harc, Work.EL.alpha2, Int.cast_zero, add_zero, st1]; dsimp only; linarith

/-- Row `t = 2` (the only row with lift `k = 1`). -/
lemma W0_st2 (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) : ∀ θ : ℝ,
    Work.EL.InArc θ Work.EL.alpha1 Work.EL.alpha2 → Work.EL.InArc θ (st2 y).2 (st2 y).1 := by
  intro θ hθ
  have harc : Work.EL.arcLen (st2 y).2 (st2 y).1 = (17:ℝ)/21 + ((1320:ℝ)/21483) * y := by
    rw [Work.EL.arcLen, Int.fract_eq_iff]
    refine ⟨?_, ?_, -1, ?_⟩
    · linarith
    · linarith
    · rw [st2]; dsimp only; push_cast; ring
  refine W0_sub_of_lift 1 ?_ ?_ θ hθ
  · rw [Work.EL.alpha1, Int.cast_one, st2]; dsimp only; linarith
  · rw [harc, Work.EL.alpha2, Int.cast_one, st2]; dsimp only; linarith

/-- Row `t = 3`. -/
lemma W0_st3 (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) : ∀ θ : ℝ,
    Work.EL.InArc θ Work.EL.alpha1 Work.EL.alpha2 → Work.EL.InArc θ (st3 y).2 (st3 y).1 := by
  intro θ hθ
  have harc : Work.EL.arcLen (st3 y).2 (st3 y).1 = (19:ℝ)/21 + ((660:ℝ)/21483) * y := by
    rw [Work.EL.arcLen, Int.fract_eq_iff]
    refine ⟨?_, ?_, -1, ?_⟩
    · linarith
    · linarith
    · rw [st3]; dsimp only; push_cast; ring
  refine W0_sub_of_lift 0 ?_ ?_ θ hθ
  · rw [Work.EL.alpha1, Int.cast_zero, add_zero, st3]; dsimp only; linarith
  · rw [harc, Work.EL.alpha2, Int.cast_zero, add_zero, st3]; dsimp only; linarith

/-- Row `t = 4`: the near arc; here `p = (α₁, α₂)` is reached exactly at `n = 0`. -/
lemma W0_st4 (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) : ∀ θ : ℝ,
    Work.EL.InArc θ Work.EL.alpha1 Work.EL.alpha2 → Work.EL.InArc θ (st4 y).1 (st4 y).2 := by
  intro θ hθ
  have harc : Work.EL.arcLen (st4 y).1 (st4 y).2 = (1:ℝ)/21 - ((330:ℝ)/21483) * y := by
    rw [Work.EL.arcLen, Int.fract_eq_iff]
    refine ⟨?_, ?_, 0, ?_⟩
    · linarith
    · linarith
    · rw [st4]; dsimp only; push_cast; ring
  refine W0_sub_of_lift 0 ?_ ?_ θ hθ
  · rw [Work.EL.alpha1, Int.cast_zero, add_zero, st4]; dsimp only; linarith
  · rw [harc, Work.EL.alpha2, Int.cast_zero, add_zero, st4]; dsimp only; linarith

/-- Row `t = 5`. -/
lemma W0_st5 (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) : ∀ θ : ℝ,
    Work.EL.InArc θ Work.EL.alpha1 Work.EL.alpha2 → Work.EL.InArc θ (st5 y).2 (st5 y).1 := by
  intro θ hθ
  have harc : Work.EL.arcLen (st5 y).2 (st5 y).1 = (11:ℝ)/21 - ((330:ℝ)/42966) * y := by
    rw [Work.EL.arcLen, Int.fract_eq_iff]
    refine ⟨?_, ?_, 0, ?_⟩
    · linarith
    · linarith
    · rw [st5]; dsimp only; push_cast; ring
  refine W0_sub_of_lift 0 ?_ ?_ θ hθ
  · rw [Work.EL.alpha1, Int.cast_zero, add_zero, st5]; dsimp only; linarith
  · rw [harc, Work.EL.alpha2, Int.cast_zero, add_zero, st5]; dsimp only; linarith

end CW0

theorem armC_W0 {c : ℂ} (n t : ℕ) (ht : t < 6) : ∀ θ : ℝ, Work.EL.InArc θ Work.EL.alpha1 Work.EL.alpha2 → Work.EL.InArc θ (Work.ELNest.armArcOf Work.ELNest.nearC (5 - t) (Work.ELNest.armPairOf Work.ELNest.nearC Work.ELNest.kC (Work.ELNest.armC1 n, Work.ELNest.armC2 n) t)).2 (Work.ELNest.armArcOf Work.ELNest.nearC (5 - t) (Work.ELNest.armPairOf Work.ELNest.nearC Work.ELNest.kC (Work.ELNest.armC1 n, Work.ELNest.armC2 n) t)).1 := by
  intro θ hθ
  have hy : (0:ℝ) < ((64:ℝ)^n)⁻¹ := by positivity
  have hy1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  interval_cases t
  · rw [CW0.armPairC_0 n, CW0.armArcOf_J, if_neg (by decide)]
    exact CW0.W0_st0 _ hy hy1 θ hθ
  · rw [CW0.armPairC_1 n, CW0.armArcOf_J, if_neg (by decide)]
    exact CW0.W0_st1 _ hy hy1 θ hθ
  · rw [CW0.armPairC_2 n, CW0.armArcOf_J, if_neg (by decide)]
    exact CW0.W0_st2 _ hy hy1 θ hθ
  · rw [CW0.armPairC_3 n, CW0.armArcOf_J, if_neg (by decide)]
    exact CW0.W0_st3 _ hy hy1 θ hθ
  · rw [CW0.armPairC_4 n, CW0.armArcOf_J, if_pos (by decide)]
    exact CW0.W0_st4 _ hy hy1 θ hθ
  · rw [CW0.armPairC_5 n, CW0.armArcOf_J, if_neg (by decide)]
    exact CW0.W0_st5 _ hy hy1 θ hθ

end Work.ELAssembly
