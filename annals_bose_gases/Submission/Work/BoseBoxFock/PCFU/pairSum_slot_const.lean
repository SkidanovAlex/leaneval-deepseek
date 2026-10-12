import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.ChWordChains
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBoxFock.PCFU.pairSum_slot_const`

The **bosonic pair-sum collapse for the cubic dictionary's alias slots**.

The four channel chains of `PCFU.ChWordChains` produce, per *ordered* pair `(i,j)` of distinct
particle labels, the two alias slots `chSlotAB i j Θ` and `chSlotCD i j Θ`.  Each of the eight
slot integrals (`chAslot`, `chAimg`, `chBslot`, `chBimg`, `chCslot`, `chCimg`, `chDslot`,
`chDimg`) is built from the two slots `(i,j)`, from the permutation invariant state `Θ`, and from
slot operators (`aP ℓ i`, `aQ ℓ i`, `lowSlot … j`) together with the translation invariant kernels
(`KfrU`, `KχfrU`, `W1fun`, `chiLam`, `lowKer`, `latVec`).  Relabelling the particles therefore
transports the whole integrand:

    ∫ x, I_{i j} (actPerm n σ x) = ∫ x, I_{σ i, σ j} x ,

because (i) `actPerm n σ : x ↦ (k ↦ x (σ k))` preserves the Lebesgue measure on the
configuration space `X n = Fin n → ℝ³` (`Work.TrialState.Basic.measurePreserving_actPerm`),
(ii) `Θ ∘ actPerm n σ = Θ` (bosonic symmetry), and (iii) the slot operators are equivariant
(`Work.BoseFixB2.Sector.aP_actPerm`, `aQ_actPerm`, `actPerm_update`, and the `lowSlot` transport
`lowSlot_actPerm` below).

Since `S_n` acts transitively on the *ordered* pairs of distinct labels, every summand of the pair
sum takes the same value, and

    ∑_{p ∈ pairSet n} chSlotAB(p) = n(n−1)·chSlotAB(0,1)     (and the same for `chSlotCD`),

the cardinality of the ordered off-diagonal being `n(n−1)` (`Finset.offDiag_card`).

No integrability, measurability or boundedness of the integrands is needed: the change of
variables for the Bochner integral (with its junk-value `0`) holds for *arbitrary* functions
(`MeasureTheory.MeasurePreserving.integral_comp` with a `MeasurableEmbedding`), and the pointwise
identities below are equalities of integrands as values of `ℂ`.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The relabelling toolkit

All four lemmas below are pure algebra of `Function.update` and of the two slot operators; no
analysis and no integrability. -/

/-- Writing `u` into slot `j` of the relabelled configuration `actPerm n σ x` is the same as
writing `u` into slot `σ j` of `x` and then relabelling.  (The reverse of
`Work.BoseFixB2.Sector.actPerm_update`, in the direction in which it is used as a rewrite rule.) -/
lemma update_actPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Submission.BoseGases.X n)
    (j : Fin n) (u : E3) :
    Function.update (Submission.BoseGases.actPerm n σ x) j u
      = Submission.BoseGases.actPerm n σ (Function.update x (σ j) u) :=
  (Work.BoseFixB2.Sector.actPerm_update σ x j u).symm

/-- **The `lowSlot` transport.**  The low-momentum slot operator at slot `j` of the relabelled
configuration is the slot operator at slot `σ j` of the transported state:
`lowSlot fc κ ℓ j G (actPerm σ x) = lowSlot fc κ ℓ (σ j) (G ∘ actPerm σ) x`. -/
lemma lowSlot_actPerm {n : ℕ} (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ)
    (σ : Equiv.Perm (Fin n)) (j : Fin n) (G : Submission.BoseGases.X n → ℝ)
    (x : Submission.BoseGases.X n) :
    Work.BoseBoxFix.lowSlot fc κ ℓ j G (Submission.BoseGases.actPerm n σ x)
      = Work.BoseBoxFix.lowSlot fc κ ℓ (σ j)
          (fun w => G (Submission.BoseGases.actPerm n σ w)) x := by
  have h1 : (Submission.BoseGases.actPerm n σ x) j = x (σ j) := rfl
  have h2 : (fun z => G (Function.update (Submission.BoseGases.actPerm n σ x) j z))
      = fun z => G (Submission.BoseGases.actPerm n σ (Function.update x (σ j) z)) := by
    funext z
    rw [Work.BoseFixB2.Sector.actPerm_update]
  simp only [Work.BoseBoxFix.lowSlot]
  rw [h1, h2]

/-- **The `aQ_j ∘ aP_i` transport.**  For a permutation invariant state `Θ`,
`aQ ℓ j (aP ℓ i Θ) ∘ actPerm n σ = aQ ℓ (σ j) (aP ℓ (σ i) Θ)`. -/
lemma aQ_aP_actPerm {n : ℕ} {Θ : Submission.BoseGases.X n → ℝ}
    (hΘ : Submission.BoseGases.PermInvariant n Θ) (ℓ : ℝ) (σ : Equiv.Perm (Fin n))
    (i j : Fin n) :
    (fun w => Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
        (Submission.BoseGases.actPerm n σ w))
      = Submission.BoseGases.aQ ℓ (σ j) (Submission.BoseGases.aP ℓ (σ i) Θ) := by
  have hfun : (fun y : Submission.BoseGases.X n => Θ (Submission.BoseGases.actPerm n σ y)) = Θ := by
    funext y; exact hΘ σ y
  have h1 : (fun w => Submission.BoseGases.aP ℓ i Θ (Submission.BoseGases.actPerm n σ w))
      = Submission.BoseGases.aP ℓ (σ i) Θ := by
    rw [Work.BoseFixB2.Sector.aP_actPerm ℓ σ i Θ, hfun]
  rw [Work.BoseFixB2.Sector.aQ_actPerm ℓ σ j (Submission.BoseGases.aP ℓ i Θ), h1]

/-- Pointwise form of `aQ_aP_actPerm`. -/
lemma aQ_aP_actPerm_apply {n : ℕ} {Θ : Submission.BoseGases.X n → ℝ}
    (hΘ : Submission.BoseGases.PermInvariant n Θ) (ℓ : ℝ) (σ : Equiv.Perm (Fin n))
    (i j : Fin n) (w : Submission.BoseGases.X n) :
    Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
        (Submission.BoseGases.actPerm n σ w)
      = Submission.BoseGases.aQ ℓ (σ j) (Submission.BoseGases.aP ℓ (σ i) Θ) w :=
  congrFun (aQ_aP_actPerm hΘ ℓ σ i j) w

/-! ## 2. The eight slot integrals are equivariant under relabelling -/

/-- Relabelling equivariance of the `(A)`-channel alias slot. -/
theorem chAslot_actPerm {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (Θ : Submission.BoseGases.X n → ℝ)
    (hΘ : Submission.BoseGases.PermInvariant n Θ) (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    chAslot v h fc fu μ N (σ i) (σ j) Θ = chAslot v h fc fu μ N i j Θ := by
  simp only [chAslot]
  conv_rhs => rw [← MeasureTheory.MeasurePreserving.integral_comp
      (Work.TrialState.Basic.measurePreserving_actPerm n σ)
      (Work.TrialState.Basic.measurableEmbedding_actPerm σ) _]
  apply integral_congr_ae
  filter_upwards with x
  simp only [hΘ σ x, lowSlot_actPerm, aQ_aP_actPerm hΘ, Submission.BoseGases.actPerm]

/-- Relabelling equivariance of the `(A)`-channel lattice-image slot. -/
theorem chAimg_actPerm {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (Θ : Submission.BoseGases.X n → ℝ)
    (hΘ : Submission.BoseGases.PermInvariant n Θ) (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    chAimg v h fc fu μ N (σ i) (σ j) Θ = chAimg v h fc fu μ N i j Θ := by
  simp only [chAimg]
  conv_rhs => rw [← MeasureTheory.MeasurePreserving.integral_comp
      (Work.TrialState.Basic.measurePreserving_actPerm n σ)
      (Work.TrialState.Basic.measurableEmbedding_actPerm σ) _]
  apply integral_congr_ae
  filter_upwards with x
  simp only [hΘ σ x, update_actPerm, aQ_aP_actPerm_apply hΘ, Submission.BoseGases.actPerm]

/-- Relabelling equivariance of the `(B)`-channel alias slot. -/
theorem chBslot_actPerm {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (Θ : Submission.BoseGases.X n → ℝ)
    (hΘ : Submission.BoseGases.PermInvariant n Θ) (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    chBslot v h fc fu μ N (σ i) (σ j) Θ = chBslot v h fc fu μ N i j Θ := by
  simp only [chBslot]
  conv_rhs => rw [← MeasureTheory.MeasurePreserving.integral_comp
      (Work.TrialState.Basic.measurePreserving_actPerm n σ)
      (Work.TrialState.Basic.measurableEmbedding_actPerm σ) _]
  apply integral_congr_ae
  filter_upwards with x
  simp only [hΘ σ x, lowSlot_actPerm, aQ_aP_actPerm hΘ, Submission.BoseGases.actPerm]

/-- Relabelling equivariance of the `(B)`-channel lattice-image slot. -/
theorem chBimg_actPerm {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (Θ : Submission.BoseGases.X n → ℝ)
    (hΘ : Submission.BoseGases.PermInvariant n Θ) (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    chBimg v h fc fu μ N (σ i) (σ j) Θ = chBimg v h fc fu μ N i j Θ := by
  simp only [chBimg]
  conv_rhs => rw [← MeasureTheory.MeasurePreserving.integral_comp
      (Work.TrialState.Basic.measurePreserving_actPerm n σ)
      (Work.TrialState.Basic.measurableEmbedding_actPerm σ) _]
  apply integral_congr_ae
  filter_upwards with x
  simp only [hΘ σ x, update_actPerm, aQ_aP_actPerm_apply hΘ, Submission.BoseGases.actPerm]

/-- Relabelling equivariance of the `(C)`-channel alias slot. -/
theorem chCslot_actPerm {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (Θ : Submission.BoseGases.X n → ℝ)
    (hΘ : Submission.BoseGases.PermInvariant n Θ) (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    chCslot v h fc fu μ N (σ i) (σ j) Θ = chCslot v h fc fu μ N i j Θ := by
  simp only [chCslot]
  conv_rhs => rw [← MeasureTheory.MeasurePreserving.integral_comp
      (Work.TrialState.Basic.measurePreserving_actPerm n σ)
      (Work.TrialState.Basic.measurableEmbedding_actPerm σ) _]
  apply integral_congr_ae
  filter_upwards with x
  simp only [hΘ σ x, update_actPerm, lowSlot_actPerm, aQ_aP_actPerm hΘ,
    Submission.BoseGases.actPerm]

/-- Relabelling equivariance of the `(C)`-channel lattice-image slot. -/
theorem chCimg_actPerm {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (Θ : Submission.BoseGases.X n → ℝ)
    (hΘ : Submission.BoseGases.PermInvariant n Θ) (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    chCimg v h fc fu μ N (σ i) (σ j) Θ = chCimg v h fc fu μ N i j Θ := by
  simp only [chCimg]
  conv_rhs => rw [← MeasureTheory.MeasurePreserving.integral_comp
      (Work.TrialState.Basic.measurePreserving_actPerm n σ)
      (Work.TrialState.Basic.measurableEmbedding_actPerm σ) _]
  apply integral_congr_ae
  filter_upwards with x
  simp only [hΘ σ x, update_actPerm, aQ_aP_actPerm_apply hΘ, Submission.BoseGases.actPerm]

/-- Relabelling equivariance of the `(D)`-channel alias slot. -/
theorem chDslot_actPerm {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (Θ : Submission.BoseGases.X n → ℝ)
    (hΘ : Submission.BoseGases.PermInvariant n Θ) (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    chDslot v h fc fu μ N (σ i) (σ j) Θ = chDslot v h fc fu μ N i j Θ := by
  simp only [chDslot]
  conv_rhs => rw [← MeasureTheory.MeasurePreserving.integral_comp
      (Work.TrialState.Basic.measurePreserving_actPerm n σ)
      (Work.TrialState.Basic.measurableEmbedding_actPerm σ) _]
  apply integral_congr_ae
  filter_upwards with x
  simp only [hΘ σ x, update_actPerm, lowSlot_actPerm, aQ_aP_actPerm hΘ,
    Submission.BoseGases.actPerm]

/-- Relabelling equivariance of the `(D)`-channel lattice-image slot. -/
theorem chDimg_actPerm {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (Θ : Submission.BoseGases.X n → ℝ)
    (hΘ : Submission.BoseGases.PermInvariant n Θ) (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    chDimg v h fc fu μ N (σ i) (σ j) Θ = chDimg v h fc fu μ N i j Θ := by
  simp only [chDimg]
  conv_rhs => rw [← MeasureTheory.MeasurePreserving.integral_comp
      (Work.TrialState.Basic.measurePreserving_actPerm n σ)
      (Work.TrialState.Basic.measurableEmbedding_actPerm σ) _]
  apply integral_congr_ae
  filter_upwards with x
  simp only [hΘ σ x, update_actPerm, aQ_aP_actPerm_apply hΘ, Submission.BoseGases.actPerm]

/-! ## 3. The two slot combinations are equivariant, hence independent of the pair -/

/-- Relabelling equivariance of the `(A,B)` alias slot. -/
theorem chSlotAB_actPerm {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (Θ : Submission.BoseGases.X n → ℝ)
    (hΘ : Submission.BoseGases.PermInvariant n Θ) (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    chSlotAB v h fc fu μ N (σ i) (σ j) Θ = chSlotAB v h fc fu μ N i j Θ := by
  simp only [chSlotAB]
  rw [chAslot_actPerm v h fc fu μ N Θ hΘ, chAimg_actPerm v h fc fu μ N Θ hΘ,
    chBslot_actPerm v h fc fu μ N Θ hΘ, chBimg_actPerm v h fc fu μ N Θ hΘ]

/-- Relabelling equivariance of the `(C,D)` alias slot. -/
theorem chSlotCD_actPerm {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (Θ : Submission.BoseGases.X n → ℝ)
    (hΘ : Submission.BoseGases.PermInvariant n Θ) (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    chSlotCD v h fc fu μ N (σ i) (σ j) Θ = chSlotCD v h fc fu μ N i j Θ := by
  simp only [chSlotCD]
  rw [chCslot_actPerm v h fc fu μ N Θ hΘ, chCimg_actPerm v h fc fu μ N Θ hΘ,
    chDslot_actPerm v h fc fu μ N Θ hΘ, chDimg_actPerm v h fc fu μ N Θ hΘ]

/-- **Constancy of the alias slots on the ordered pairs of distinct labels**: the transitivity
of the action of `S_n` on `pairSet n` upgrades the equivariance to the independence of the pair. -/
theorem chSlot_pair_indep {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (Θ : Submission.BoseGases.X n → ℝ)
    (hΘ : Submission.BoseGases.PermInvariant n Θ) {i j i' j' : Fin n}
    (hij : i ≠ j) (hi'j' : i' ≠ j') :
    chSlotAB v h fc fu μ N i j Θ = chSlotAB v h fc fu μ N i' j' Θ
      ∧ chSlotCD v h fc fu μ N i j Θ = chSlotCD v h fc fu μ N i' j' Θ := by
  obtain ⟨σ, h1, h2⟩ :=
    Work.TrialState.Basic.exists_perm_apply_eq_apply_eq (a := i) (b := i') (c := j) (d := j')
      hij hi'j'
  rw [← h1, ← h2]
  exact ⟨(chSlotAB_actPerm v h fc fu μ N Θ hΘ σ i j).symm,
    (chSlotCD_actPerm v h fc fu μ N Θ hΘ σ i j).symm⟩

/-! ## 4. The combinatorial collapse of the pair sum -/

/-- `#(pairSet n) = n(n−1)`: the ordered pairs of distinct labels are the off-diagonal of
`Finset.univ`. -/
lemma pairSet_card_nat (n : ℕ) : (Submission.BoseGases.pairSet n).card = n * (n - 1) := by
  have hset : Submission.BoseGases.pairSet n = (Finset.univ : Finset (Fin n)).offDiag := by
    ext p
    simp [Submission.BoseGases.pairSet, Finset.mem_offDiag]
  rw [hset, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
  exact (Nat.mul_sub_one n n).symm

/-- **The pair-sum collapse.**  If the summand is constant on the ordered pairs of distinct
labels, the sum over `pairSet n` is `n(n−1)` times the value at the pair `(0,1)`. -/
lemma pairSum_const_mul {n : ℕ} (hn : 2 ≤ n) (F : Fin n → Fin n → ℂ)
    (hconst : ∀ i j i' j' : Fin n, i ≠ j → i' ≠ j' → F i j = F i' j') :
    (∑ p ∈ Submission.BoseGases.pairSet n, F p.1 p.2)
      = ((n : ℝ) * ((n : ℝ) - 1)) * F ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
    intro hc
    exact absurd (congrArg Fin.val hc) (by simp)
  have hterm : ∀ p ∈ Submission.BoseGases.pairSet n,
      F p.1 p.2 = F ⟨0, by omega⟩ ⟨1, by omega⟩ := by
    intro p hp
    have hpne : p.1 ≠ p.2 := by simpa [Submission.BoseGases.pairSet] using hp
    exact hconst p.1 p.2 _ _ hpne h01
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  have hcardR : (((Submission.BoseGases.pairSet n).card : ℕ) : ℝ)
      = (n : ℝ) * ((n : ℝ) - 1) := by
    rw [pairSet_card_nat n, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hcardC : ((Submission.BoseGases.pairSet n).card : ℂ)
      = ((n : ℝ) * ((n : ℝ) - 1) : ℂ) := by
    rw [show ((Submission.BoseGases.pairSet n).card : ℂ)
        = ((((Submission.BoseGases.pairSet n).card : ℕ) : ℝ) : ℂ) from
      (Complex.ofReal_natCast _).symm]
    rw [hcardR]
    simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
  rw [hcardC]

/-- **The bosonic pair-sum collapse of the cubic dictionary's alias slots.**  For a permutation
invariant state `Θ` on `n ≥ 2` particles, both slot sums over the ordered pairs of distinct
labels collapse onto `n(n−1)` times the value at the pair `(0,1)`. -/
theorem pairSum_slot_const {n : ℕ} (hn : 2 ≤ n) (v : EuclideanSpace ℝ (Fin 3) → ℝ)
    (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘ : Submission.BoseGases.PermInvariant n Θ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C) :
    (∑ p ∈ Submission.BoseGases.pairSet n,
        Work.BoseBoxFock.PCFU.chSlotAB v h fc fu μ N p.1 p.2 Θ
      = ((n : ℝ) * ((n : ℝ) - 1)) *
          Work.BoseBoxFock.PCFU.chSlotAB v h fc fu μ N ⟨0, by omega⟩ ⟨1, by omega⟩ Θ) ∧
    (∑ p ∈ Submission.BoseGases.pairSet n,
        Work.BoseBoxFock.PCFU.chSlotCD v h fc fu μ N p.1 p.2 Θ
      = ((n : ℝ) * ((n : ℝ) - 1)) *
          Work.BoseBoxFock.PCFU.chSlotCD v h fc fu μ N ⟨0, by omega⟩ ⟨1, by omega⟩ Θ) := by
  refine ⟨?_, ?_⟩
  · exact pairSum_const_mul hn (fun i j => chSlotAB v h fc fu μ N i j Θ)
      (fun i j i' j' hij hi'j' => (chSlot_pair_indep v h fc fu μ N Θ hΘ hij hi'j').1)
  · exact pairSum_const_mul hn (fun i j => chSlotCD v h fc fu μ N i j Θ)
      (fun i j i' j' hij hi'j' => (chSlot_pair_indep v h fc fu μ N Θ hΘ hij hi'j').2)

end Work.BoseBoxFock.PCFU
