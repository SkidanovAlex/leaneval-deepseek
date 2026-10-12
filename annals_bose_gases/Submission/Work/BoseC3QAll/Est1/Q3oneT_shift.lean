import Mathlib.Tactic.Module
import Mathlib.Data.Real.Basic
import Submission.Work.BoseC3QAll.Est1.Algebra
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.Est1.Q3oneT_shift` — piece A of `eq:EstimateQ3Tilde1`

FS `eq:CentralEstimateOfQ31` (`lem:EstimatesOnQ3-js`'s first piece): the cubic
word `Q₃⁽¹⁾` of `lem:EstimatesOnQ3-js` is

  `Q₃⁽¹⁾ = Σ_{k∈P_H} (b_k†Y_k + Y_k†b_k) + R1`,

where `Y_k` is the shift of `Est1.Defs` (`Y_k = (z/ℓ³)Σ_{s∈P_L}γ_{sk}b_{s-k}†Ã_s`)
and `R1` is the leftover (`T₁(k)` plus the comm part of `T₂`).

The computation is the continuation of the one in `Est1.Algebra`:

* expanding `b_k†Y_k` and `Y_k†b_k` in the `(s,k)` summands produces, besides the
  two *shifts of the words* of `Q₃⁽¹⁾`, the two new words `S1`, `S2`
  (`b_k†b_{s-k}†ã_{-s}†` and `ã_{-s}b_{s-k}b_k`) with the weight `β_{sk}`;
* the squeezed commutators `word_cre`, `word_ann` rewrite `S1`, `S2` as the
  reindexed `b†b†`/`bb` words of `Q₃⁽¹⁾` (`Q1b(-s,-k)`, `Q1bDag(-s,-k)`) plus
  the linear corrections `κA`, `κB`, `κC`;
* those corrections cancel *exactly* against the summands of `R1`;
* finally the two `β`-terms of `Q₃⁽¹⁾` are reindexed by `(s,k) ↦ (-s,-k)`
  (`sum_excited_PHset_neg`, with `gA_bA_neg` for the invariance of the weight,
  which needs the evenness of `f_L`, `Ŵ₁`, `α`).

Everything is pure operator algebra on `F.H →ₗ[ℝ] F.H`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseC3QAll

namespace Est1

open Work.BoseB7

/-! ## 1. The four words of the computation -/

/-- `b_k†Y_k` after expanding the shift: the creation word `b_k†(b_{s-k}†ã_s)` plus
`β_{sk}` times `S1`, as a function of `(s,k)`. -/
def Wcre {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (s k : Mode) : F.H →ₗ[ℝ] F.H :=
  F.bOpDag E.alpha k ∘ₗ (F.bOpDag E.alpha (s - k) ∘ₗ T.ta s) + (bA E s k) • S1 F T E s k

/-- `Y_k†b_k` after expanding the shift: the annihilation word `(ã_{-s}†b_{s-k})b_k`
plus `β_{sk}` times `S2`, as a function of `(s,k)`. -/
def Wann {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (s k : Mode) : F.H →ₗ[ℝ] F.H :=
  T.taDag s ∘ₗ (F.bOp E.alpha (s - k) ∘ₗ F.bOp E.alpha k) + (bA E s k) • S2 F T E s k

/-- The `(s,k)` summand of `R1`. -/
def R1s {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (s k : Mode) : F.H →ₗ[ℝ] F.H :=
  (kB T E s k) • (F.bOpDag E.alpha k + F.bOp E.alpha k)
    + (kA T E s k) • (F.bOpDag E.alpha (s - k) + F.bOp E.alpha (s - k))
    - (kC E s k) • (T.taDag (-s) + T.ta (-s))

/-- The `(s,k)` summand of `Q₃⁽¹⁾`, split into its four words. -/
def Qpre {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (s k : Mode) : F.H →ₗ[ℝ] F.H :=
  (gA E s k) • Q1a F T E s k + (gA E s k * bA E s k) • Q1b F T E s k
    + (gA E s k) • Q1aDag F T E s k + (gA E s k * bA E s k) • Q1bDag F T E s k

/-- The normal form reached by `Σ_k(b_k†Y_k + Y_k†b_k) + R1`: the `(s,k)` summand of
`Q₃⁽¹⁾` with its two `β`-words reindexed by `(s,k) ↦ (-s,-k)`. -/
def Qsub {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (s k : Mode) : F.H →ₗ[ℝ] F.H :=
  (gA E s k) • Q1a F T E s k
    + (gA E s k * bA E s k) •
        (T.taDag (-s) ∘ₗ (F.bOpDag E.alpha (s - k) ∘ₗ F.bOpDag E.alpha k))
    + (gA E s k) • Q1aDag F T E s k
    + (gA E s k * bA E s k) • (F.bOp E.alpha k ∘ₗ (F.bOp E.alpha (s - k) ∘ₗ T.ta (-s)))

/-! ## 2. The squeezed commutators read backwards -/

/-- `S1` expanded along `word_cre`: `b_k†b_{s-k}†ã_{-s}†` is the reindexed `b†b†` word
of `Q₃⁽¹⁾` plus the linear corrections `κB`, `κA`, `κC`. -/
theorem S1_expand {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : FockData Mode} (T : TildeData F) (E : Q3Env Mode) (h : SubstHypG F T E) (s k : Mode)
    (hfL : E.fL s ≠ 0) (hkPH : k ∈ F.PHset E) (hW : E.W1 k ≠ 0) :
    S1 F T E s k
      = T.taDag (-s) ∘ₗ (F.bOpDag E.alpha (s - k) ∘ₗ F.bOpDag E.alpha k)
        - (kB T E s k) • F.bOpDag E.alpha k - (kA T E s k) • F.bOpDag E.alpha (s - k)
        + (kC E s k) • T.taDag (-s) := by
  have hw := word_cre T E h s k hfL hkPH hW
  rw [hw]
  module

/-- `S2` expanded along `word_ann`. -/
theorem S2_expand {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : FockData Mode} (T : TildeData F) (E : Q3Env Mode) (h : SubstHypG F T E) (s k : Mode)
    (hfL : E.fL s ≠ 0) (hkPH : k ∈ F.PHset E) (hW : E.W1 k ≠ 0) :
    S2 F T E s k
      = F.bOp E.alpha k ∘ₗ (F.bOp E.alpha (s - k) ∘ₗ T.ta (-s))
        - (kB T E s k) • F.bOp E.alpha k - (kA T E s k) • F.bOp E.alpha (s - k)
        + (kC E s k) • T.ta (-s) := by
  have hw := word_ann T E h s k hfL hkPH hW
  rw [hw]
  module

/-! ## 3. Expanding `b_k†Y_k` and `Y_k†b_k` -/

/-- One summand of `Σ_k b_k†Y_k`. -/
theorem bOpDag_shift {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : FockData Mode} (T : TildeData F) (E : Q3Env Mode) (k : Mode) :
    F.bOpDag E.alpha k ∘ₗ shift F T E k
      = (E.z / E.ell ^ 3) • ∑ s ∈ excited Mode, (gA E s k) • Wcre F T E s k := by
  rw [shift, LinearMap.comp_smul, comp_sum_lm]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  rw [LinearMap.comp_smul]
  congr 1
  simp only [Wcre, Atil, S1, LinearMap.comp_add, LinearMap.comp_smul]

/-- One summand of `Σ_k Y_k†b_k`. -/
theorem shiftDag_bOp {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : FockData Mode} (T : TildeData F) (E : Q3Env Mode) (k : Mode) :
    shiftDag F T E k ∘ₗ F.bOp E.alpha k
      = (E.z / E.ell ^ 3) • ∑ s ∈ excited Mode, (gA E s k) • Wann F T E s k := by
  rw [shiftDag, LinearMap.smul_comp, sum_comp_lm]
  rfl

/-- The whole creation half `Σ_k b_k†Y_k`. -/
theorem sum_bOpDag_shift {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : FockData Mode} (T : TildeData F) (E : Q3Env Mode) :
    (∑ k ∈ F.PHset E, F.bOpDag E.alpha k ∘ₗ shift F T E k)
      = (E.z / E.ell ^ 3) •
          ∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, (gA E s k) • Wcre F T E s k := by
  rw [Finset.sum_congr rfl (fun k _ => bOpDag_shift T E k)]
  rw [← Finset.smul_sum, Finset.sum_comm]

/-- The whole annihilation half `Σ_k Y_k†b_k`. -/
theorem sum_shiftDag_bOp {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : FockData Mode} (T : TildeData F) (E : Q3Env Mode) :
    (∑ k ∈ F.PHset E, shiftDag F T E k ∘ₗ F.bOp E.alpha k)
      = (E.z / E.ell ^ 3) •
          ∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, (gA E s k) • Wann F T E s k := by
  rw [Finset.sum_congr rfl (fun k _ => shiftDag_bOp T E k)]
  rw [← Finset.smul_sum, Finset.sum_comm]

/-- `R1` in its `(s,k)`-split form. -/
theorem R1_eq {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : FockData Mode} (T : TildeData F) (E : Q3Env Mode) :
    R1 F T E = (E.z / E.ell ^ 3) •
      ∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, (gA E s k * bA E s k) • R1s F T E s k := by
  simp only [R1, R1s]

/-! ## 4. The pointwise combination: shift words and `R1` give the reindexed words -/

/-- The `(s,k)` summand of `Σ_k(b_k†Y_k + Y_k†b_k) + R1` is the reindexed `(s,k)` summand
of `Q₃⁽¹⁾`: the `S1`/`S2` corrections and the `R1`-summand cancel exactly. -/
theorem W_combine {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : FockData Mode} (T : TildeData F) (E : Q3Env Mode) (h : SubstHypG F T E) (s k : Mode)
    (hfL : E.fL s ≠ 0) (hkPH : k ∈ F.PHset E) (hW : E.W1 k ≠ 0) :
    (gA E s k) • Wcre F T E s k + (gA E s k) • Wann F T E s k
        + (gA E s k * bA E s k) • R1s F T E s k = Qsub F T E s k := by
  simp only [Wcre, Wann, R1s, Qsub, Q1a, Q1aDag,
    S1_expand T E h s k hfL hkPH hW, S2_expand T E h s k hfL hkPH hW,
    smul_add, smul_sub, smul_smul]
  ext x
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply]
  module

/-- The sums: `Σ_k(b_k†Y_k + Y_k†b_k) + R1 = zℓ⁻³Σ_{s,k}Qsub`. -/
theorem sum_W_eq_sum_Qsub {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : FockData Mode} (T : TildeData F) (E : Q3Env Mode) (h : SubstHypG F T E) :
    (∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, (gA E s k) • Wcre F T E s k)
        + (∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, (gA E s k) • Wann F T E s k)
        + (∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, (gA E s k * bA E s k) • R1s F T E s k)
      = ∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, Qsub F T E s k := by
  rw [Finset.sum_congr rfl
    (fun s _ => Finset.sum_congr rfl (fun k hk =>
      show Qsub F T E s k
        = (gA E s k) • Wcre F T E s k + (gA E s k) • Wann F T E s k
          + (gA E s k * bA E s k) • R1s F T E s k from by
        by_cases hf : E.fL s = 0
        · simp only [Qsub, gA, hf, zero_mul, zero_smul, add_zero, zero_add]
        by_cases hW : E.W1 k = 0
        · simp only [Qsub, Wcre, Wann, R1s, gA, hW, mul_zero, zero_mul, zero_smul,
            add_zero, zero_add]
        · exact (W_combine T E h s k hf hk hW).symm))]
  simp only [Finset.sum_add_distrib]

/-! ## 5. `Q₃⁽¹⁾` in the split form -/

/-- `Q₃⁽¹⁾` as the double sum of its `(s,k)` summands. -/
theorem Q3oneT_eq_sum_Qpre {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : FockData Mode} (T : TildeData F) (E : Q3Env Mode) :
    T.Q3oneT E = (E.z / E.ell ^ 3) • ∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, Qpre F T E s k := by
  rw [Work.BoseB7A.TildeData.Q3oneT]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro k _
  simp only [Qpre, Q1a, Q1b, Q1aDag, Q1bDag, gA, bA, smul_add, smul_smul]

/-! ## 6. The reindexing `(s,k) ↦ (-s,-k)` of the two `β`-terms -/

/-- The `Q1b`-term of `Q₃⁽¹⁾` reindexed. -/
theorem sum_Q1b_reindex {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : FockData Mode} (T : TildeData F) (E : Q3Env Mode)
    (hfL : ∀ s : Mode, E.fL (-s) = E.fL s) (hW1 : ∀ s : Mode, E.W1 (-s) = E.W1 s)
    (hα : ∀ s : Mode, E.alpha (-s) = E.alpha s) :
    (∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, (gA E s k * bA E s k) • Q1b F T E s k)
      = ∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, (gA E s k * bA E s k) •
          (T.taDag (-s) ∘ₗ (F.bOpDag E.alpha (s - k) ∘ₗ F.bOpDag E.alpha k)) := by
  have h := sum_excited_PHset_neg (F := F) E (fun s k => (gA E s k * bA E s k) • Q1b F T E s k)
  simp only [gA_bA_neg E hfL hW1 hα, Q1b_neg] at h
  exact h.symm

/-- The `Q1bDag`-term of `Q₃⁽¹⁾` reindexed. -/
theorem sum_Q1bDag_reindex {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : FockData Mode} (T : TildeData F) (E : Q3Env Mode)
    (hfL : ∀ s : Mode, E.fL (-s) = E.fL s) (hW1 : ∀ s : Mode, E.W1 (-s) = E.W1 s)
    (hα : ∀ s : Mode, E.alpha (-s) = E.alpha s) :
    (∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, (gA E s k * bA E s k) • Q1bDag F T E s k)
      = ∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, (gA E s k * bA E s k) •
          (F.bOp E.alpha k ∘ₗ (F.bOp E.alpha (s - k) ∘ₗ T.ta (-s))) := by
  have h := sum_excited_PHset_neg (F := F) E (fun s k => (gA E s k * bA E s k) • Q1bDag F T E s k)
  simp only [gA_bA_neg E hfL hW1 hα, Q1bDag_neg] at h
  exact h.symm

/-- The reindexing identity: the `(s,k)` summand of `Q₃⁽¹⁾` and its reindexed normal form
have the same double sum. -/
theorem sum_Qpre_eq_sum_Qsub {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : FockData Mode} (T : TildeData F) (E : Q3Env Mode)
    (hfL : ∀ s : Mode, E.fL (-s) = E.fL s) (hW1 : ∀ s : Mode, E.W1 (-s) = E.W1 s)
    (hα : ∀ s : Mode, E.alpha (-s) = E.alpha s) :
    (∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, Qpre F T E s k)
      = ∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, Qsub F T E s k := by
  simp only [Qpre, Qsub, Finset.sum_add_distrib]
  rw [sum_Q1b_reindex T E hfL hW1 hα, sum_Q1bDag_reindex T E hfL hW1 hα]

/-! ## 7. The assembly: piece A of `eq:EstimateQ3Tilde1` -/

/-- The right-hand side of the decomposition, in normal form. -/
theorem sum_shift_add_R1 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : FockData Mode} (T : TildeData F) (E : Q3Env Mode) (h : SubstHypG F T E) :
    (∑ k ∈ F.PHset E, (F.bOpDag E.alpha k ∘ₗ shift F T E k
        + shiftDag F T E k ∘ₗ F.bOp E.alpha k)) + R1 F T E
      = (E.z / E.ell ^ 3) • ∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, Qsub F T E s k := by
  rw [Finset.sum_add_distrib, R1_eq, sum_bOpDag_shift, sum_shiftDag_bOp]
  simp only [← smul_add]
  rw [sum_W_eq_sum_Qsub T E h]

/-- **Piece A (the algebra).**  FS `eq:CentralEstimateOfQ31`: the cubic word
`Q₃⁽¹⁾` is the sum over `k ∈ P_H` of `b_k†Y_k + Y_k†b_k` (with the shift `Y_k` of
`Est1.Defs`) plus the leftover `R1` (FS's `T₁(k)` and the comm part of `T₂`).

The hypotheses `hfL`, `hW1` (evenness of `f_L`, `Ŵ₁`) are fields of `Q3KernelFSAll`;
they enter through the reindexing `(s,k) ↦ (-s,-k)`. -/
theorem Q3oneT_shift {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : Work.BoseB7.FockData Mode} (T : Work.BoseC3QAll.TildeData F) (E : Work.BoseB7.Q3Env Mode)
    (h : Work.BoseC3QAll.SubstHypG F T E) (hfL : ∀ s : Mode, E.fL (-s) = E.fL s)
    (hW1 : ∀ s : Mode, E.W1 (-s) = E.W1 s) :
    T.Q3oneT E
      = (∑ k ∈ F.PHset E, (F.bOpDag E.alpha k ∘ₗ Work.BoseC3QAll.Est1.shift F T E k
          + Work.BoseC3QAll.Est1.shiftDag F T E k ∘ₗ F.bOp E.alpha k))
        + Work.BoseC3QAll.Est1.R1 F T E := by
  rw [sum_shift_add_R1 T E h, Q3oneT_eq_sum_Qpre T E,
    sum_Qpre_eq_sum_Qsub T E hfL hW1 h.alpha_even]

end Est1

end Work.BoseC3QAll
