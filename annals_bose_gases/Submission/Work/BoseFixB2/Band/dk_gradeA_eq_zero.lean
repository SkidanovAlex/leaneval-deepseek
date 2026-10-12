import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Data.Int.Star
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.Analysis.BoseBand.fsT_fibre_offdiag
import Submission.Work.BoseFixB2.Band.integrableOn_potOnePiece
import Submission.Work.BoseFixB2.Band.integrableOn_potPairPiece
import Submission.Work.BoseFixB2.Band.pairing_potPiece_eq_zero
import Submission.Work.BoseFixB2.DvApriori.dk_gradeA_one_two
import Submission.Work.BoseFixB2.DvApriori.fsT_congr_of_Qfree_eq
import Submission.Work.BoseFixB2.DvApriori.jointProj_aP_eq_self
import Submission.Work.BoseFixB2.Polar.boxFormB_smul
import Submission.Work.BoseFixB2.Polar.polB_bilinear
import Submission.Work.BoseFixB2.Polar.polB_eq_slots
import Submission.Work.BoseKinLoc.Tests.fsT_const
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Band.dk_gradeA_eq_zero` — the band property of FS §6

FS §6 `lem:LocMatrices` uses that the matrix
`𝒜_{ij} = ⟨1_{n₊=i}Φ, H_Λ(μ) 1_{n₊=j}Φ⟩/(‖1_iΦ‖‖1_jΦ‖)` has vanishing supra-diagonals of
order `k ≥ 3`: only `𝒜^{(0)}, 𝒜^{(1)}, 𝒜^{(2)}` are non-zero.  In the corpus vocabulary the
statement is `dk (gradeA …) (fsNn v μ n) (gradePsi …) k = 0` for `3 ≤ k`.

## Route

`dk A nn ψ k = dSup A nn ψ k + dSup A nn ψ (-k)` for `k ≠ 0`, and each **summand**
`star (ψ i) · A i j · ψ j` collapses (via `gradePsi`'s support and `gradeA`'s normalisation,
`DvApriori.term_fwd`) to `polB (secProj i Φ) (secProj j Φ) / normB Φ` as soon as one of the
sector norms vanishes; the whole `dk` is therefore a sum of `polB`-pairings of
**sectors separated by at least three**, each of which vanishes because
`polB` is the polarisation of the box word and the box word is the sum of
* slot-`j` one-body kinetic forms (dialogue in the slot `j`, hence diagonal in the sector
  grading: `flat` slots contribute `0`) and
* a one- and two-slot multiplication (the potential), which can shift the sector by at most
  two.

The two analytic inputs are the four per-slot kinetic off-diagonal lemmas
(`DvApriori/{neu,gap,mom,main}Word_fibre_offdiag`) and the potential band lemma
(`potBil_jointProj_eq_zero`); the file below builds the assembly:
the slot bookkeeping for `fsT`, the sector expansion of `polB`, and the final index
arithmetic.

## The potential band lemma: which hypotheses are needed

The potential part is proved here from scratch as `potBil_jointProj_eq_zero_fs`: the few-slot
decomposition `potWordU_eq_sum` (`Band/PotSplit.lean`) splits `potWordU` into pieces each
depending on at most two configuration variables, the general few-slot orthogonality
`DvApriori.Band.pairing_potPiece_eq_zero` kills each piece against two joint sectors which
differ in at least three slots, and the box integral is distributed over the (finite) sum of
pieces — for which each piece must be `L¹` on the box.  Those integrability inputs are
`Band.integrableOn_potOnePiece` (needs `Integrable (g₀ v h)`, supplied by
`BoseGases.g0_integrable`) and `Band.integrableOn_potPairPiece` (needs `Integrable v`, i.e.
`MemLp v 1`).  The `L¹` hypothesis on `v` is genuinely needed: `potBil` is a *Bochner*
integral, so the identity `∫ (Σ_k W_k) = Σ_k ∫ W_k` requires each summand integrable, and
`IsScatteringSolution` alone does not make `v` thinkable pointwise (it only controls
`v·(1−w)`).
-/

noncomputable section

open MeasureTheory
open scoped Topology BigOperators

namespace Work.BoseFixB2.Band

set_option maxHeartbeats 1000000

/-- `normB` is nonnegative: it is the box integral of a square. -/
theorem normB_nonneg_local {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {n : ℕ}
    (Ψ : Submission.BoseGases.X n → ℝ) : 0 ≤ Work.BoseBoxFix.normB v μ n Ψ := by
  simp only [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
  exact MeasureTheory.integral_nonneg (fun x => sq_nonneg (Ψ x))



open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. `fsT` is blind to constants -/

/-- `fsT` is invariant under adding a constant to its state. -/
theorem fsT_add_const {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) (u : ℝ³)
    {ψ : ℝ³ → ℝ} (hψ : Continuous ψ) (c : ℝ) :
    Work.BoseKinLoc.fsT ℓ d s εT b u (fun z => ψ z + c)
      = Work.BoseKinLoc.fsT ℓ d s εT b u ψ := by
  refine Work.BoseFixB2.DvApriori.fsT_congr_of_Qfree_eq' (u := u) ?_
  funext z
  simp only [Work.BoseKinLoc.Qfree, Work.BSKinetic.bsQ]
  rw [Work.BoseFixB2.Polar.FsTAux.bsMean_add hℓ u hψ continuous_const,
    Work.BoseKinLoc.Tests.bsMean_const hℓ u]
  ring

/-- `fsT` is invariant under subtracting a constant. -/
theorem fsT_sub_const {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) (u : ℝ³)
    {ψ : ℝ³ → ℝ} (hψ : Continuous ψ) (c : ℝ) :
    Work.BoseKinLoc.fsT ℓ d s εT b u (fun z => ψ z - c)
      = Work.BoseKinLoc.fsT ℓ d s εT b u ψ := by
  have := fsT_add_const (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b) hℓ u hψ (-c)
  simpa [sub_eq_add_neg] using this

/-- `fsT` is invariant under `f ↦ -f`. -/
theorem fsT_neg {ℓ d s εT b : ℝ} (u : ℝ³) (f : ℝ³ → ℝ) :
    Work.BoseKinLoc.fsT ℓ d s εT b u (fun z => - f z) = Work.BoseKinLoc.fsT ℓ d s εT b u f := by
  have h := Work.BoseFixB2.Polar.SmulAux.fsT_const_mul (ℓ := ℓ) (d := d) (s := s) (εT := εT)
    (b := b) (c := -1) u f
  simpa using h

/-- `fsT` is invariant under `f ↦ const - f`. -/
theorem fsT_const_sub {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) (u : ℝ³)
    {f : ℝ³ → ℝ} (hf : Continuous f) (c : ℝ) :
    Work.BoseKinLoc.fsT ℓ d s εT b u (fun z => c - f z)
      = Work.BoseKinLoc.fsT ℓ d s εT b u f := by
  have h1 : (fun z : ℝ³ => c - f z) = fun z => (fun z => - f z) z + c := by
    funext z; ring
  have step : Work.BoseKinLoc.fsT ℓ d s εT b u (fun z => (fun z => - f z) z + c)
      = Work.BoseKinLoc.fsT ℓ d s εT b u (fun z => - f z) :=
    fsT_add_const (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b) hℓ u (ψ := fun z => - f z)
      hf.neg c
  rw [h1, step, fsT_neg]

/-! ## 2. Fibres -/

/-- The slot-`j` fibre of a continuous state is continuous. -/
theorem continuous_fibre {N : ℕ} (j : Fin N) {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨ : Continuous Ψ) (x : Submission.BoseGases.X N) :
    Continuous (Work.BoseKinLoc.fibre N j Ψ x) :=
  hΨ.comp (by fun_prop)

/-- The fibre is additive. -/
theorem fibre_add {N : ℕ} (j : Fin N) (A B : Submission.BoseGases.X N → ℝ)
    (x : Submission.BoseGases.X N) :
    Work.BoseKinLoc.fibre N j (fun y => A y + B y) x
      = fun z => Work.BoseKinLoc.fibre N j A x z + Work.BoseKinLoc.fibre N j B x z := by
  funext z; rfl

/-- The fibre is subtractive. -/
theorem fibre_sub {N : ℕ} (j : Fin N) (A B : Submission.BoseGases.X N → ℝ)
    (x : Submission.BoseGases.X N) :
    Work.BoseKinLoc.fibre N j (fun y => A y - B y) x
      = fun z => Work.BoseKinLoc.fibre N j A x z - Work.BoseKinLoc.fibre N j B x z := by
  funext z; rfl

/-- The fibre of a joint sector projection in an absent slot is constant. -/
theorem jointProj_fibre_const {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {S : Finset ℕ} {j : ℕ}
    (hj : j < n) (hjS : j ∉ S) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (x : Submission.BoseGases.X n) (z : ℝ³) :
    (Work.BoseFixB2.jointProj ℓ S Φ) (Function.update x ⟨j, hj⟩ z)
      = (Work.BoseFixB2.jointProj ℓ S Φ) x := by
  have hself := Work.BoseFixB2.DvApriori.jointProj_aP_eq_self (ℓ := ℓ) (S := S) (m := j)
    (Φ := Φ) hℓ hjS hj hΦ
  have hcont : Continuous (Work.BoseFixB2.jointProj ℓ S Φ) :=
    (Work.BoseFixB2.Sector.jointProj_contDiff hℓ S hΦ).continuous
  have hconst := Submission.BoseGases.aP_const_in_coord hℓ ⟨j, hj⟩ hcont x z
  rw [← hself, hconst, hself]
/-! ## 3. The cheap kinetic vanishing -/

/-- **The slot-`j` kinetic bilinear form kills the pairing of two joint sectors when the slot
`j` is absent from one of them.** -/
theorem kinBil_jointProj_eq_zero_of_not_mem {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {S T : Finset ℕ} (hS : S ⊆ Finset.range n) (hT : T ⊆ Finset.range n)
    (hnot : (j : ℕ) ∉ S ∨ (j : ℕ) ∉ T) :
    Work.BoseFixB2.kinBil n ℓ d s εT b j (Work.BoseFixB2.jointProj ℓ S Φ)
      (Work.BoseFixB2.jointProj ℓ T Φ) = 0 := by
  classical
  set ES := Work.BoseFixB2.jointProj ℓ S Φ with hES
  set ET := Work.BoseFixB2.jointProj ℓ T Φ with hET
  have hcS : Continuous ES := (Work.BoseFixB2.Sector.jointProj_contDiff hℓ S hΦ).continuous
  have hcT : Continuous ET := (Work.BoseFixB2.Sector.jointProj_contDiff hℓ T hΦ).continuous
  -- the pointwise identity of the two `fsT` values
  have hpt : ∀ x : Submission.BoseGases.X n,
      Work.BoseKinLoc.fsT ℓ d s εT b 0
        (fun z => Work.BoseKinLoc.fibre n j ES x z + Work.BoseKinLoc.fibre n j ET x z)
      = Work.BoseKinLoc.fsT ℓ d s εT b 0
        (fun z => Work.BoseKinLoc.fibre n j ES x z - Work.BoseKinLoc.fibre n j ET x z) := by
    intro x
    have hfS : Continuous (Work.BoseKinLoc.fibre n j ES x) := continuous_fibre j hcS x
    have hfT : Continuous (Work.BoseKinLoc.fibre n j ET x) := continuous_fibre j hcT x
    rcases hnot with hS' | hT'
    · have hconst : Work.BoseKinLoc.fibre n j ES x = fun _ : ℝ³ => ES x := by
        funext z; exact jointProj_fibre_const hℓ j.isLt hS' hΦ x z
      have h1 : (fun z : ℝ³ => Work.BoseKinLoc.fibre n j ES x z
            + Work.BoseKinLoc.fibre n j ET x z)
          = fun z => Work.BoseKinLoc.fibre n j ET x z + ES x := by
        funext z; rw [congrFun hconst z]; ring
      have h2 : (fun z : ℝ³ => Work.BoseKinLoc.fibre n j ES x z
            - Work.BoseKinLoc.fibre n j ET x z)
          = fun z => ES x - Work.BoseKinLoc.fibre n j ET x z := by
        funext z; rw [congrFun hconst z]
      rw [h1, h2,
        fsT_add_const (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b) hℓ 0
          (ψ := Work.BoseKinLoc.fibre n j ET x) hfT (ES x),
        fsT_const_sub (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b) hℓ 0 hfT (ES x)]
    · have hconst : Work.BoseKinLoc.fibre n j ET x = fun _ : ℝ³ => ET x := by
        funext z; exact jointProj_fibre_const hℓ j.isLt hT' hΦ x z
      have h1 : (fun z : ℝ³ => Work.BoseKinLoc.fibre n j ES x z
            + Work.BoseKinLoc.fibre n j ET x z)
          = fun z => Work.BoseKinLoc.fibre n j ES x z + ET x := by
        funext z; rw [congrFun hconst z]
      have h2 : (fun z : ℝ³ => Work.BoseKinLoc.fibre n j ES x z
            - Work.BoseKinLoc.fibre n j ET x z)
          = fun z => Work.BoseKinLoc.fibre n j ES x z - ET x := by
        funext z; rw [congrFun hconst z]
      rw [h1, h2,
        fsT_add_const (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b) hℓ 0
          (ψ := Work.BoseKinLoc.fibre n j ES x) hfS (ET x),
        fsT_sub_const (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b) hℓ 0 hfS (ET x)]
  -- the integrand vanishes pointwise
  have hzero : ∀ x : Submission.BoseGases.X n,
      Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseFixB2.fsTbil ℓ d s εT b 0
        (Work.BoseKinLoc.fibre n j ES x) (Work.BoseKinLoc.fibre n j ET x) = 0 := by
    intro x
    simp only [Work.BoseFixB2.fsTbil]
    rw [hpt x]
    ring
  unfold Work.BoseFixB2.kinBil
  rw [hES, hET]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hzero),
    MeasureTheory.integral_zero, mul_zero]




/-- `secProj` of a smooth state is smooth. -/
theorem secProj_contDiff_of {ℓ : ℝ} (hℓ : 0 < ℓ) {n k : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.BoseFixB2.secProj ℓ k Φ) := by
  rw [Work.BoseFixB2.secProj, Finset.sum_fn]
  exact ContDiff.sum (fun S _ => Work.BoseFixB2.Sector.jointProj_contDiff hℓ S hΦ)

/-- Additivity of `polB` in its first argument over a finite sum. -/
theorem polB_sum_left {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    {n : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι) (Ψ : ι → Submission.BoseGases.X n → ℝ)
    (Ξ : Submission.BoseGases.X n → ℝ) (hΨ : ∀ i ∈ s, ContDiff ℝ (⊤ : ℕ∞) (Ψ i))
    (hΞ : ContDiff ℝ (⊤ : ℕ∞) Ξ)
    (hw : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.potWordU n v
      (Submission.BoseGases.g0 v h) (Work.BoseFixB2.fsSide v μ) μ 0 x)
      (Submission.BoseGases.abox n (Work.BoseFixB2.fsSide v μ))) :
    Work.BoseFixB2.polB v h μ n (fun x => ∑ i ∈ s, Ψ i x) Ξ
      = ∑ i ∈ s, Work.BoseFixB2.polB v h μ n (Ψ i) Ξ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [Work.BoseFixB2.polB, Finset.sum_empty, Work.BoseFixB2.Polar.PolB.wordB_neg]
  | insert a s ha ih =>
      have hsplit : (fun x => ∑ i ∈ insert a s, Ψ i x)
          = fun x => Ψ a x + ∑ i ∈ s, Ψ i x := by
        funext x; rw [Finset.sum_insert ha]
      have hsum_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ i ∈ s, Ψ i x) := by
        refine ContDiff.sum (fun i hi => ?_)
        exact hΨ i (Finset.mem_insert_of_mem hi)
      have hgoal : Work.BoseFixB2.polB v h μ n (fun x => ∑ i ∈ insert a s, Ψ i x) Ξ
          = Work.BoseFixB2.polB v h μ n (fun x => Ψ a x + ∑ i ∈ s, Ψ i x) Ξ := by
        rw [hsplit]
      rw [hgoal]
      rw [(Work.BoseFixB2.Polar.polB_bilinear (v := v) (h := h) (μ := μ) (n := n)
        (Φ₁ := Ψ a) (Φ₂ := fun x => ∑ i ∈ s, Ψ i x) (Ψ := Ξ)
        (hΨ a (Finset.mem_insert_self a s)) hsum_smooth hΞ hw).1]
      rw [ih (fun i hi => hΨ i (Finset.mem_insert_of_mem hi))]
      rw [Finset.sum_insert ha]

/-- Additivity of `polB` in its second argument over a finite sum. -/
theorem polB_sum_right {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    {n : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι) (Ξ : Submission.BoseGases.X n → ℝ)
    (Ψ : ι → Submission.BoseGases.X n → ℝ) (hΨ : ∀ i ∈ s, ContDiff ℝ (⊤ : ℕ∞) (Ψ i))
    (hΞ : ContDiff ℝ (⊤ : ℕ∞) Ξ)
    (hw : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.potWordU n v
      (Submission.BoseGases.g0 v h) (Work.BoseFixB2.fsSide v μ) μ 0 x)
      (Submission.BoseGases.abox n (Work.BoseFixB2.fsSide v μ))) :
    Work.BoseFixB2.polB v h μ n Ξ (fun x => ∑ i ∈ s, Ψ i x)
      = ∑ i ∈ s, Work.BoseFixB2.polB v h μ n Ξ (Ψ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [Work.BoseFixB2.polB, Finset.sum_empty]
  | insert a s ha ih =>
      have hsplit : (fun x => ∑ i ∈ insert a s, Ψ i x)
          = fun x => Ψ a x + ∑ i ∈ s, Ψ i x := by
        funext x; rw [Finset.sum_insert ha]
      have hsum_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ i ∈ s, Ψ i x) := by
        refine ContDiff.sum (fun i hi => ?_)
        exact hΨ i (Finset.mem_insert_of_mem hi)
      have hgoal : Work.BoseFixB2.polB v h μ n Ξ (fun x => ∑ i ∈ insert a s, Ψ i x)
          = Work.BoseFixB2.polB v h μ n Ξ (fun x => Ψ a x + ∑ i ∈ s, Ψ i x) := by
        rw [hsplit]
      rw [hgoal]
      rw [(Work.BoseFixB2.Polar.polB_bilinear (v := v) (h := h) (μ := μ) (n := n)
        (Φ₁ := Ψ a) (Φ₂ := fun x => ∑ i ∈ s, Ψ i x) (Ψ := Ξ)
        (hΨ a (Finset.mem_insert_self a s)) hsum_smooth hΞ hw).2]
      rw [ih (fun i hi => hΨ i (Finset.mem_insert_of_mem hi))]
      rw [Finset.sum_insert ha]

/-- **The sector expansion of `polB`.**  The pairing of two `n₊`-sectors is the sum of the
pairings of the joint sectors they are built from. -/
theorem polB_secProj_eq_sum {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hℓ : 0 < Work.BoseFixB2.fsSide v μ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hw : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.potWordU n v
      (Submission.BoseGases.g0 v h) (Work.BoseFixB2.fsSide v μ) μ 0 x)
      (Submission.BoseGases.abox n (Work.BoseFixB2.fsSide v μ))) (a b : ℕ) :
    Work.BoseFixB2.polB v h μ n
        (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) a Φ)
        (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) b Φ)
      = ∑ S ∈ (Finset.range n).powersetCard a, ∑ T ∈ (Finset.range n).powersetCard b,
          Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.jointProj (Work.BoseFixB2.fsSide v μ) S Φ)
            (Work.BoseFixB2.jointProj (Work.BoseFixB2.fsSide v μ) T Φ) := by
  classical
  rw [show Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) a Φ
      = fun x => ∑ S ∈ (Finset.range n).powersetCard a,
          Work.BoseFixB2.jointProj (Work.BoseFixB2.fsSide v μ) S Φ x from by
        funext x; simp only [Work.BoseFixB2.secProj, Finset.sum_apply]]
  rw [polB_sum_left (s := (Finset.range n).powersetCard a)
    (Ψ := fun S => Work.BoseFixB2.jointProj (Work.BoseFixB2.fsSide v μ) S Φ)
    (Ξ := Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) b Φ)
    (fun S _ => Work.BoseFixB2.Sector.jointProj_contDiff hℓ S hΦ)
    (secProj_contDiff_of hℓ hΦ) hw]
  refine Finset.sum_congr rfl (fun S hS => ?_)
  rw [show Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) b Φ
      = fun x => ∑ T ∈ (Finset.range n).powersetCard b,
          Work.BoseFixB2.jointProj (Work.BoseFixB2.fsSide v μ) T Φ x from by
        funext x; simp only [Work.BoseFixB2.secProj, Finset.sum_apply]]
  exact polB_sum_right (s := (Finset.range n).powersetCard b)
    (Ξ := Work.BoseFixB2.jointProj (Work.BoseFixB2.fsSide v μ) S Φ)
    (Ψ := fun T => Work.BoseFixB2.jointProj (Work.BoseFixB2.fsSide v μ) T Φ)
    (fun T _ => Work.BoseFixB2.Sector.jointProj_contDiff hℓ T hΦ)
    (Work.BoseFixB2.Sector.jointProj_contDiff hℓ S hΦ) hw

/-! ## 4b. The potential band lemma, assembled from the few-slot pieces -/

/-- **The potential pairing of two joint sectors which differ in at least three slots
vanishes.**  This is the assembly step: `potWordU` splits into its few-slot pieces
(`potWordU_eq_sum`), the pairing is linear in the weight (distributing the box integral over
the finite sums, each summand integrable by `hOneInt`/`hPairInt`), and each few-slot piece
vanishes by the input `hZero` — the general few-slot orthogonality of
`DvApriori.Band.jointProj_pairing_eq_zero_of_free_ne`. -/
theorem potBil_jointProj_eq_zero_of_inputs {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v g : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (hOneInt : ∀ i : Fin N, MeasureTheory.IntegrableOn (potOnePiece N g ℓ i)
      (Submission.BoseGases.abox N ℓ))
    (hPairInt : ∀ p : {p : Fin N × Fin N // p.1 < p.2},
      MeasureTheory.IntegrableOn (potPairPiece N v ℓ p) (Submission.BoseGases.abox N ℓ))
    (hZero : ∀ (A : Finset ℕ) (W : Submission.BoseGases.X N → ℝ), A.card ≤ 2 →
      MeasureTheory.IntegrableOn W (Submission.BoseGases.abox N ℓ) →
      (∀ (j : ℕ) (hj : j < N), j ∉ A →
        ∀ (x : Submission.BoseGases.X N) (z : EuclideanSpace ℝ (Fin 3)),
          W (Function.update x ⟨j, hj⟩ z) = W x) →
      ∀ (Ψ : Submission.BoseGases.X N → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ →
      ∀ (S T : Finset ℕ), S ⊆ Finset.range N → T ⊆ Finset.range N →
        3 ≤ (S \ T).card + (T \ S).card →
        (∫ x in Submission.BoseGases.abox N ℓ,
          Work.BoseFixB2.jointProj ℓ S Ψ x * W x * Work.BoseFixB2.jointProj ℓ T Ψ x) = 0)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {S T : Finset ℕ} (hS : S ⊆ Finset.range N) (hT : T ⊆ Finset.range N)
    (hcard : 3 ≤ (S \ T).card + (T \ S).card) :
    Work.BoseFixB2.potBil N v g ℓ μ (Work.BoseFixB2.jointProj ℓ S Φ)
      (Work.BoseFixB2.jointProj ℓ T Φ) = 0 := by
  classical
  set ES := Work.BoseFixB2.jointProj ℓ S Φ with hES
  set ET := Work.BoseFixB2.jointProj ℓ T Φ with hET
  have hESc : Continuous ES := (Work.BoseFixB2.Sector.jointProj_contDiff hℓ S hΦ).continuous
  have hETc : Continuous ET := (Work.BoseFixB2.Sector.jointProj_contDiff hℓ T hΦ).continuous
  have hCone : ∀ i : Fin N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => ES x * potOnePiece N g ℓ i x * ET x)
      (Submission.BoseGases.abox N ℓ) := fun i =>
    Work.BoseFixB2.DvApriori.Band.integrableOn_mul_of_continuous_of_integrable (n := N) (ℓ := ℓ)
      hℓ hESc hETc (hOneInt i)
  have hCpair : ∀ p : {p : Fin N × Fin N // p.1 < p.2}, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => ES x * potPairPiece N v ℓ p x * ET x)
      (Submission.BoseGases.abox N ℓ) := fun p =>
    Work.BoseFixB2.DvApriori.Band.integrableOn_mul_of_continuous_of_integrable (n := N) (ℓ := ℓ)
      hℓ hESc hETc (hPairInt p)
  -- ## the individual pairings vanish
  have hIone : ∀ i : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ, ES x * potOnePiece N g ℓ i x * ET x) = 0 := by
    intro i
    rw [hES, hET]
    exact hZero {(i : ℕ)} (potOnePiece N g ℓ i) (by simp) (hOneInt i)
      (fun j hj hjA x z => potOnePiece_update_eq (i := i) hj
        (fun hji => hjA (Finset.mem_singleton.mpr hji)) x z) Φ hΦ S T hS hT hcard
  have hIpair : ∀ p : {p : Fin N × Fin N // p.1 < p.2},
      (∫ x in Submission.BoseGases.abox N ℓ, ES x * potPairPiece N v ℓ p x * ET x) = 0 := by
    intro p
    have hneFin : p.1.1 ≠ p.1.2 := ne_of_lt p.2
    have hne : (p.1.1 : ℕ) ≠ (p.1.2 : ℕ) := fun h => hneFin (Fin.ext h)
    rw [hES, hET]
    exact hZero {(p.1.1 : ℕ), (p.1.2 : ℕ)} (potPairPiece N v ℓ p)
      (le_of_eq (Finset.card_pair hne)) (hPairInt p)
      (fun j hj hjA x z => potPairPiece_update_eq (p := p) hj
        (fun h1 => hjA (by rw [Finset.mem_insert, Finset.mem_singleton]; exact Or.inl h1))
        (fun h2 => hjA (by rw [Finset.mem_insert, Finset.mem_singleton]; exact Or.inr h2)) x z)
      Φ hΦ S T hS hT hcard
  -- ## the two blocks of the word, and their integrals
  have hAeq : (fun x : Submission.BoseGases.X N =>
        ES x * ET x * (-μ * (∑ i : Fin N, potOnePiece N g ℓ i x)))
      = fun x => (-μ) * (∑ i : Fin N, ES x * potOnePiece N g ℓ i x * ET x) := by
    funext x
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hBeq : (fun x : Submission.BoseGases.X N =>
        ES x * ET x * (∑ p : {p : Fin N × Fin N // p.1 < p.2}, potPairPiece N v ℓ p x))
      = fun x => ∑ p : {p : Fin N × Fin N // p.1 < p.2},
          ES x * potPairPiece N v ℓ p x * ET x := by
    funext x
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  have hAint : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      ES x * ET x * (-μ * (∑ i : Fin N, potOnePiece N g ℓ i x)))
      (Submission.BoseGases.abox N ℓ) := by
    have h1 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        ∑ i : Fin N, ES x * potOnePiece N g ℓ i x * ET x)
        (Submission.BoseGases.abox N ℓ) :=
      MeasureTheory.integrable_finsetSum Finset.univ (fun i _ => hCone i)
    exact (h1.const_mul (-μ)).congr (Filter.Eventually.of_forall (fun x => (congrFun hAeq x).symm))
  have hBint : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      ES x * ET x * (∑ p : {p : Fin N × Fin N // p.1 < p.2}, potPairPiece N v ℓ p x))
      (Submission.BoseGases.abox N ℓ) := by
    have h1 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        ∑ p : {p : Fin N × Fin N // p.1 < p.2}, ES x * potPairPiece N v ℓ p x * ET x)
        (Submission.BoseGases.abox N ℓ) :=
      MeasureTheory.integrable_finsetSum Finset.univ (fun p _ => hCpair p)
    exact h1.congr (Filter.Eventually.of_forall (fun x => (congrFun hBeq x).symm))
  have hAvalue : (∫ x in Submission.BoseGases.abox N ℓ,
      ES x * ET x * (-μ * (∑ i : Fin N, potOnePiece N g ℓ i x))) = 0 := by
    rw [hAeq, MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum]
    · simp [hIone]
    · exact fun i _ => hCone i
  have hBvalue : (∫ x in Submission.BoseGases.abox N ℓ,
      ES x * ET x * (∑ p : {p : Fin N × Fin N // p.1 < p.2}, potPairPiece N v ℓ p x)) = 0 := by
    rw [hBeq, MeasureTheory.integral_finsetSum]
    · simp [hIpair]
    · exact fun p _ => hCpair p
  -- ## assembly
  have hsplit : (fun x : Submission.BoseGases.X N =>
        ES x * ET x * Work.BoseKinLoc.potWordU N v g ℓ μ 0 x)
      = fun x => ES x * ET x * (-μ * (∑ i : Fin N, potOnePiece N g ℓ i x))
          + ES x * ET x * (∑ p : {p : Fin N × Fin N // p.1 < p.2}, potPairPiece N v ℓ p x) := by
    funext x
    rw [potWordU_eq_sum]
    ring
  rw [Work.BoseFixB2.potBil, hsplit, MeasureTheory.integral_add hAint hBint, hAvalue, hBvalue,
    add_zero]

/-- **The potential band lemma at the FS profile.**  The few-slot pieces of
`potWordU n v (g₀ v h)` are integrable on the box as soon as `v` and `g₀ v h` are `L¹`
(`integrableOn_potOnePiece`, `integrableOn_potPairPiece`), and a weight depending on at most
two slots cannot connect two joint sectors differing in three (`pairing_potPiece_eq_zero`). -/
theorem potBil_jointProj_eq_zero_fs {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {μ ℓ : ℝ} {n : ℕ} (hℓ : 0 < ℓ) (hv : MeasureTheory.Integrable v)
    (hg : MeasureTheory.Integrable (Submission.BoseGases.g0 v h))
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {S T : Finset ℕ} (hS : S ⊆ Finset.range n) (hT : T ⊆ Finset.range n)
    (hcard : 3 ≤ (S \ T).card + (T \ S).card) :
    Work.BoseFixB2.potBil n v (Submission.BoseGases.g0 v h) ℓ μ
      (Work.BoseFixB2.jointProj ℓ S Φ) (Work.BoseFixB2.jointProj ℓ T Φ) = 0 :=
  potBil_jointProj_eq_zero_of_inputs (g := Submission.BoseGases.g0 v h) hℓ
    (fun i => integrableOn_potOnePiece hℓ hg i)
    (fun p => integrableOn_potPairPiece hℓ hv p)
    (fun _A _W hA hWint hWin Ψ hΨ S T hS hT hcard =>
      pairing_potPiece_eq_zero hℓ hA hWint hWin hΨ hS hT hcard)
    hΦ hS hT hcard

/-! ## 5. The sector-level band statement -/

/-- **The band property of the box word at the level of joint sectors.**  The pairing of two
joint sector projections vanishes as soon as the two sectors differ in at least three slots.

* the **kinetic** part: the slot-`j` kinetic form is the identity in the slot `j`; if `j` is
  present in both sectors the requirement belongs to the analytic input
  `DvApriori.{neu,gap,mom,main}Word_fibre_offdiag` (assembled as `fsT_fibre_offdiag`), and if
  `j` is absent from one of the sectors the pairing carries a slot-`j` constant and vanishes
  (`kinBil_jointProj_eq_zero_of_not_mem`, proved above);
* the **potential** part: `potBil_jointProj_eq_zero` (a sum of one- and two-slot
  multiplications, hence band `≤ 2`). -/
theorem polB_jointProj_eq_zero {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {μ : ℝ} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hℓ : 0 < Work.BoseFixB2.fsSide v μ)
    (hv : MeasureTheory.Integrable v) (hg : MeasureTheory.Integrable (Submission.BoseGases.g0 v h))
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) {S T : Finset ℕ} (hS : S ⊆ Finset.range n)
    (hT : T ⊆ Finset.range n) (hcard : 3 ≤ (S \ T).card + (T \ S).card)
    (hw : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.potWordU n v
      (Submission.BoseGases.g0 v h) (Work.BoseFixB2.fsSide v μ) μ 0 x)
      (Submission.BoseGases.abox n (Work.BoseFixB2.fsSide v μ))) :
    Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.jointProj (Work.BoseFixB2.fsSide v μ) S Φ)
      (Work.BoseFixB2.jointProj (Work.BoseFixB2.fsSide v μ) T Φ) = 0 := by
  classical
  set ES := Work.BoseFixB2.jointProj (Work.BoseFixB2.fsSide v μ) S Φ with hES
  set ET := Work.BoseFixB2.jointProj (Work.BoseFixB2.fsSide v μ) T Φ with hET
  have hESc : ContDiff ℝ (⊤ : ℕ∞) ES := Work.BoseFixB2.Sector.jointProj_contDiff hℓ S hΦ
  have hETc : ContDiff ℝ (⊤ : ℕ∞) ET := Work.BoseFixB2.Sector.jointProj_contDiff hℓ T hΦ
  have hST : S ≠ T := by
    intro hEq
    rw [hEq] at hcard
    simp only [Finset.sdiff_self, Finset.card_empty, add_zero] at hcard
    omega
  rw [Work.BoseFixB2.Polar.polB_eq_slots (v := v) (h := h) (μ := μ) (n := n)
    (Φ := ES) (Ψ := ET) hESc hETc hw]
  have hpot : Work.BoseFixB2.potBil n v (Submission.BoseGases.g0 v h)
      (Work.BoseFixB2.fsSide v μ) μ ES ET = 0 := by
    rw [hES, hET]
    exact potBil_jointProj_eq_zero_fs (v := v) (h := h) (μ := μ)
      (ℓ := Work.BoseFixB2.fsSide v μ) (n := n) hℓ hv hg hΦ hS hT hcard
  have hkin : (∑ i : Fin n, Work.BoseFixB2.kinBilFS v μ i ES ET) = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    by_cases hiS : (i : ℕ) ∈ S
    · by_cases hiT : (i : ℕ) ∈ T
      · -- both slots present: the analytic off-diagonal input and the slot glue
        have hchild := Work.Analysis.BoseBand.fsT_fibre_offdiag
          (ℓ := Work.BoseFixB2.fsSide v μ)
          (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
          (s := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)
          (εT := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
          (b := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b)
          hℓ i hΦ hS hT hiS hiT hST
        have hA : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
            Work.BoseKinLoc.indU (Work.BoseFixB2.fsSide v μ) 0 (x i) *
              Work.BoseKinLoc.fsT (Work.BoseFixB2.fsSide v μ)
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b 0
              (Work.BoseKinLoc.fibre n i (fun y => ES y + ET y) x))
            (Submission.BoseGases.abox n (Work.BoseFixB2.fsSide v μ)) :=
          Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth hℓ i (hESc.add hETc)
        rw [Work.BoseFixB2.kinBilFS, Work.BoseFixB2.kinBil]
        simp only [Work.BoseFixB2.fsTbil]
        -- the two fibres written as `fun z => fibre ES x z ± fibre ET x z` are the fibres of
        -- the sum and difference of the two sectors
        have e1 : ∀ x : Submission.BoseGases.X n,
            (fun z : ℝ³ => Work.BoseKinLoc.fibre n i ES x z + Work.BoseKinLoc.fibre n i ET x z)
              = Work.BoseKinLoc.fibre n i (Work.BoseFixB2.jointProj (Work.BoseFixB2.fsSide v μ) S Φ
                  + Work.BoseFixB2.jointProj (Work.BoseFixB2.fsSide v μ) T Φ) x := by
          intro x
          funext z
          simp only [Work.BoseKinLoc.fibre, Pi.add_apply]
          rw [hES, hET]
        have e2 : ∀ x : Submission.BoseGases.X n,
            (fun z : ℝ³ => Work.BoseKinLoc.fibre n i ES x z - Work.BoseKinLoc.fibre n i ET x z)
              = Work.BoseKinLoc.fibre n i (Work.BoseFixB2.jointProj (Work.BoseFixB2.fsSide v μ) S Φ
                  - Work.BoseFixB2.jointProj (Work.BoseFixB2.fsSide v μ) T Φ) x := by
          intro x
          funext z
          simp only [Work.BoseKinLoc.fibre, Pi.sub_apply]
          rw [hES, hET]
        rw [show (∫ x in Submission.BoseGases.abox n (Work.BoseFixB2.fsSide v μ),
              Work.BoseKinLoc.indU (Work.BoseFixB2.fsSide v μ) 0 (x i) *
                ((Work.BoseKinLoc.fsT (Work.BoseFixB2.fsSide v μ)
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b 0
                    (fun z => Work.BoseKinLoc.fibre n i ES x z
                      + Work.BoseKinLoc.fibre n i ET x z)
                  - Work.BoseKinLoc.fsT (Work.BoseFixB2.fsSide v μ)
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b 0
                    (fun z => Work.BoseKinLoc.fibre n i ES x z
                      - Work.BoseKinLoc.fibre n i ET x z)) / 4))
            = (∫ x in Submission.BoseGases.abox n (Work.BoseFixB2.fsSide v μ),
                Work.BoseKinLoc.indU (Work.BoseFixB2.fsSide v μ) 0 (x i) *
                  (Work.BoseKinLoc.fsT (Work.BoseFixB2.fsSide v μ)
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b 0
                    (Work.BoseKinLoc.fibre n i (Work.BoseFixB2.jointProj (Work.BoseFixB2.fsSide v μ) S Φ
                      + Work.BoseFixB2.jointProj (Work.BoseFixB2.fsSide v μ) T Φ) x)
                  - Work.BoseKinLoc.fsT (Work.BoseFixB2.fsSide v μ)
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b 0
                    (Work.BoseKinLoc.fibre n i (Work.BoseFixB2.jointProj (Work.BoseFixB2.fsSide v μ) S Φ
                      - Work.BoseFixB2.jointProj (Work.BoseFixB2.fsSide v μ) T Φ) x))) / 4 from by
          rw [← MeasureTheory.integral_div]
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
          dsimp only
          rw [e1 x, e2 x]
          ring]
        rw [hchild, zero_div, mul_zero]
      · rw [Work.BoseFixB2.kinBilFS, hES, hET]
        exact kinBil_jointProj_eq_zero_of_not_mem (ℓ := Work.BoseFixB2.fsSide v μ) hℓ i hΦ hS hT
          (Or.inr hiT)
    · rw [Work.BoseFixB2.kinBilFS, hES, hET]
      exact kinBil_jointProj_eq_zero_of_not_mem (ℓ := Work.BoseFixB2.fsSide v μ) hℓ i hΦ hS hT
        (Or.inl hiS)
  rw [hkin, hpot, add_zero]

/-! ## 6. The `dk` bookkeeping -/

/-- **The `k`-th diagonal expectation vanishes once the sector-level band statement holds.** -/
theorem dk_eq_zero_of_secProj_band {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {μ : ℝ} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hav : 0 < _root_.BoseGases.a v)
    (hμ : 0 < μ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hpos : 0 < Work.BoseBoxFix.normB v μ n Φ)
    (hband : ∀ a b : ℕ, a ≤ n → b ≤ n → 3 ≤ |(a : ℤ) - (b : ℤ)| →
      Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) a Φ)
        (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) b Φ) = 0)
    {k : ℤ} (hk : 3 ≤ k) :
    Work.UBBInputs3.dk (Work.BoseFixB2.gradeA v h μ n (Work.BoseFixB2.fsSide v μ) Φ)
      (Work.BoseFixB2.fsNn v μ n)
      (Work.BoseFixB2.gradePsi v h μ n (Work.BoseFixB2.fsSide v μ) Φ) k = 0 := by
  have hℓ : 0 < Work.BoseFixB2.fsSide v μ := Work.BoseBox.sideAt_pos hμ hav
  have hk0 : k ≠ 0 := by omega
  have hkm1 : 1 ≤ k.toNat := by omega
  have hkcast : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg (by omega)
  have hk3 : (3 : ℤ) ≤ (k.toNat : ℤ) := by rw [hkcast]; exact hk
  have hfwd := Work.BoseFixB2.DvApriori.dSup_fwd (v := v) (h := h) (μ := μ) (n := n) (Φ := Φ)
    (ℓ := Work.BoseFixB2.fsSide v μ) hℓ hℓ hpos hΦ (m := k.toNat) hkm1
  have hbwd := Work.BoseFixB2.DvApriori.dSup_bwd (v := v) (h := h) (μ := μ) (n := n) (Φ := Φ)
    (ℓ := Work.BoseFixB2.fsSide v μ) hℓ hℓ hpos hΦ (m := k.toNat) hkm1
  have hzero : ∀ t : ℕ, t + k.toNat ≤ n →
      (Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) t Φ)
        (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) (t + k.toNat) Φ)
        / Work.BoseBoxFix.normB v μ n Φ) = 0 := by
    intro t ht
    have hdiff : 3 ≤ |(t : ℤ) - ((t + k.toNat : ℕ) : ℤ)| := by
      rw [Int.natCast_add]
      have hsub : (t : ℤ) - ((t : ℤ) + (k.toNat : ℤ)) = -((k.toNat : ℤ)) := by ring
      rw [hsub, abs_neg, abs_of_nonneg (by exact_mod_cast Nat.zero_le _)]
      exact hk3
    rw [hband t (t + k.toNat) (by omega) ht hdiff, zero_div]
  have h1 : Work.UBBInputs3.dSup (Work.BoseFixB2.gradeA v h μ n (Work.BoseFixB2.fsSide v μ) Φ)
      (Work.BoseFixB2.fsNn v μ n)
      (Work.BoseFixB2.gradePsi v h μ n (Work.BoseFixB2.fsSide v μ) Φ) k = 0 := by
    rw [← hkcast, hfwd]
    refine Finset.sum_eq_zero (fun t ht => ?_)
    rw [Finset.mem_range] at ht
    exact hzero t (by omega)
  have h2 : Work.UBBInputs3.dSup (Work.BoseFixB2.gradeA v h μ n (Work.BoseFixB2.fsSide v μ) Φ)
      (Work.BoseFixB2.fsNn v μ n)
      (Work.BoseFixB2.gradePsi v h μ n (Work.BoseFixB2.fsSide v μ) Φ) (-k) = 0 := by
    rw [show -k = -((k.toNat : ℕ) : ℤ) from by rw [hkcast], hbwd]
    refine Finset.sum_eq_zero (fun t ht => ?_)
    rw [Finset.mem_range] at ht
    exact hzero t (by omega)
  rw [Work.UBBInputs3.dk, if_neg hk0, h1, h2, add_zero]

/-! ## 7. The main theorem -/

theorem dk_gradeA_eq_zero {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hav : 0 < _root_.BoseGases.a v) {μ : ℝ} (hμ : 0 < μ) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (k : ℤ) (hk : 3 ≤ k) : Work.UBBInputs3.dk (Work.BoseFixB2.gradeA v h μ n (Work.BoseFixB2.fsSide v μ) Φ) (Work.BoseFixB2.fsNn v μ n) (Work.BoseFixB2.gradePsi v h μ n (Work.BoseFixB2.fsSide v μ) Φ) k = 0 := by
  have hℓ : 0 < Work.BoseFixB2.fsSide v μ := Work.BoseBox.sideAt_pos hμ hav
  have hv_int : MeasureTheory.Integrable v := MeasureTheory.memLp_one_iff_integrable.mp hv1
  have hg_int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  have hw : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h) (Work.BoseFixB2.fsSide v μ) μ 0 x)
      (Submission.BoseGases.abox n (Work.BoseFixB2.fsSide v μ)) :=
    Work.BoseFixB2.Pot.potWordU_integrable (v := v) h hR hv_supp hv1 (Work.BoseFixB2.fsSide v μ)
  by_cases hpos : 0 < Work.BoseBoxFix.normB v μ n Φ
  · refine dk_eq_zero_of_secProj_band (v := v) (h := h) (μ := μ) (n := n) (Φ := Φ)
      hav hμ hΦ hpos ?_ hk
    intro a b ha hb hab
    rw [polB_secProj_eq_sum (v := v) (h := h) (μ := μ) (n := n) (Φ := Φ) hℓ hΦ hw a b]
    refine Finset.sum_eq_zero (fun S hS => ?_)
    refine Finset.sum_eq_zero (fun T hT => ?_)
    refine polB_jointProj_eq_zero (v := v) (h := h) (μ := μ) (n := n) (Φ := Φ) hℓ hv_int hg_int hΦ
      (Finset.mem_powersetCard.mp hS).1 (Finset.mem_powersetCard.mp hT).1 ?_ hw
    have hScard : S.card = a := (Finset.mem_powersetCard.mp hS).2
    have hTcard : T.card = b := (Finset.mem_powersetCard.mp hT).2
    have h1 : S.card ≤ (S \ T).card + T.card := by
      have hsub : S ⊆ (S \ T) ∪ T := by
        intro x hx
        by_cases hxT : x ∈ T
        · exact Finset.mem_union_right _ hxT
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxT⟩)
      calc S.card ≤ ((S \ T) ∪ T).card := Finset.card_le_card hsub
        _ ≤ (S \ T).card + T.card := Finset.card_union_le _ _
    have h2 : T.card ≤ (T \ S).card + S.card := by
      have hsub : T ⊆ (T \ S) ∪ S := by
        intro x hx
        by_cases hxS : x ∈ S
        · exact Finset.mem_union_right _ hxS
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxS⟩)
      calc T.card ≤ ((T \ S) ∪ S).card := Finset.card_le_card hsub
        _ ≤ (T \ S).card + S.card := Finset.card_union_le _ _
    have hab' : 3 ≤ |(a : ℤ) - (b : ℤ)| := hab
    have : ((3 : ℕ) : ℤ) ≤ ((S \ T).card + (T \ S).card : ℕ) := by
      have habs : |(a : ℤ) - (b : ℤ)| ≤ (((S \ T).card + (T \ S).card : ℕ) : ℤ) := by
        rw [← hScard, ← hTcard]
        have hc1 : ((S \ T).card : ℤ) ≤ (((S \ T).card + (T \ S).card : ℕ) : ℤ) := by
          push_cast; exact le_add_of_nonneg_right (by positivity)
        have hc2 : ((T \ S).card : ℤ) ≤ (((S \ T).card + (T \ S).card : ℕ) : ℤ) := by
          push_cast; exact le_add_of_nonneg_left (by positivity)
        rcases lt_or_ge T.card S.card with hlt | hle
        · -- `T.card < S.card`: the difference is bounded by `(S \ T).card`
          have hle' : (T.card : ℤ) ≤ (S.card : ℤ) := by exact_mod_cast le_of_lt hlt
          have hpos' : 0 ≤ (S.card : ℤ) - (T.card : ℤ) := by linarith
          rw [abs_of_nonneg hpos']
          have h3 : ((S.card : ℤ) - (T.card : ℤ)) ≤ ((S \ T).card : ℤ) := by
            have := h1
            omega
          linarith [hc1]
        · -- `S.card ≤ T.card`
          have hle' : (S.card : ℤ) ≤ (T.card : ℤ) := by exact_mod_cast hle
          have hnonpos : (S.card : ℤ) - (T.card : ℤ) ≤ 0 := by linarith
          rw [abs_of_nonpos hnonpos]
          have h3 : ((T.card : ℤ) - (S.card : ℤ)) ≤ ((T \ S).card : ℤ) := by
            have := h2
            omega
          linarith [hc2]
      omega
    exact_mod_cast this
  · -- vanishing box norm: the norm profile is identically zero
    have hnorm0 : Work.BoseBoxFix.normB v μ n Φ = 0 :=
      le_antisymm (not_lt.mp hpos) (normB_nonneg_local Φ)
    have hzero : Work.BoseFixB2.gradePsi v h μ n (Work.BoseFixB2.fsSide v μ) Φ = 0 := by
      funext i
      by_cases hc : 0 ≤ i ∧ i ≤ (n : ℤ)
      · rw [Work.BoseFixB2.gradePsi, if_pos hc, hnorm0]
        simp
      · rw [Work.BoseFixB2.gradePsi, if_neg hc]
        simp
    rw [hzero]
    have hd : ∀ x : ℤ, Work.UBBInputs3.dSup (Work.BoseFixB2.gradeA v h μ n (Work.BoseFixB2.fsSide v μ) Φ)
        (Work.BoseFixB2.fsNn v μ n) (0 : ℤ → ℂ) x = 0 := by
      intro x
      simp [Work.UBBInputs3.dSup]
    simp only [Work.UBBInputs3.dk]
    split
    · exact hd _
    · rw [hd, hd, add_zero]

end Work.BoseFixB2.Band
