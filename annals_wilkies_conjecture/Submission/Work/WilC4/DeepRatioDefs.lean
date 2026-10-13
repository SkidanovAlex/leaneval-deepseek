/-
  WilC4/DeepRatioDefs : the vocabulary of the *deep-ratio* bound (step 4 of `ULPM_E_DEV.md`,
  the `deep_ratio_scale_bdd` / `deep_ratio_bdd` / `deep_ratio_tight` family).

  ## The mathematical content

  The deep-ratio bound says: at a `β`-deep point `x` of the fibre `f_c` (`IsDeepR B₀ c β x`,
  i.e. the multiplicative window `[x/(2β), 2βx]` misses the breakpoints `B₀_c`), the doubling
  ratio `w = f_c(2x)/f_c(x)` is bounded by `β` for `β ≥ Γ`.

  The design (`ULPM_E_DEV.md`, P2) proves this by contradiction: if for arbitrarily large `β`
  there is a `β`-deep point with `|w| ≥ β`, then the definable *diagonal* function

      Φ(β) := f_c(βx)/f_c(x)      (at a suitably chosen bad point)

  is superpolynomial in `β` (the ratios are `≥ β` on the whole window, so the dyadic telescope
  over `log₂ β` steps gives `Φ(β) ≥ β^{log₂ β}`), contradicting `pb_poly_bound` (the polynomial
  boundedness `hPB` of the family).

  Since the choice of the bad point is not available definably, this file replaces it by a
  *greatest lower bound*: at scale `β` every bad point contributes the number

      max ( f_c(βx)/f_c(x) , f_c(x)/f_c(x/β) ),

  and *every* bad point contributes at least `β^{⌊log₂β⌋}` (either the forward or the backward
  telescoping works, according to the monotonicity direction of the doubling ratio, which is
  supplied by `ULPMStruct`).  So the greatest lower bound `Θ(β)` of these numbers is itself
  `≥ β^{⌊log₂β⌋}`, and `Θ` is a *definable* function of `β` (its graph is the set `DeepThetaG`),
  to which `pb_poly_bound` applies.

  ## What is here

  * `DeepRatSet Y B₀ β` : the set of numbers contributed by the bad points at scale `β`.
  * `DeepThetaG Y B₀`   : the graph of the glb `Θ` of `DeepRatSet Y B₀ β` over `β ≥ 1`.
  * `deepThetaG_functional` : `DeepThetaG` is the graph of a function.

  The definability of `DeepThetaG` (a long quantifier-bookkeeping proof) is proved in
  `Submission/Work/WilC4/deepThetaG_definable.lean`; the lower bound on the glb at dyadic scales
  is proved in the main file `Submission/Work/WilC4/deep_ratio_scale_bdd.lean`.

  ## Hints for the definability proof (`deepThetaG_definable`)

  The template for the quantifier bookkeeping is `Submission/Work/WilC4/DevBdd_definable.lean`
  (and `Submission/Work/WilC4/Diag_definable.lean` / `Submission/Work/WilC4/CandBody_definable.lean`),
  which handle exactly the same atoms.  Two of the pieces are *also* available as separate
  public modules (refactored out of `DevBdd_definable`):

  * `Submission.Work.WilC4.DevDeep_definable` : `DevDeep B` is `∅`-definable (`DevDeepBody` is the
    *deepness* atom `IsDeepR` with the two auxiliary slots `(b, x/(2M))`; the semantic bridge is
    `Work.WilC4.mem_DevDeep_iff`);
  * `Submission.Work.WilC4.DevConc_definable` : the conclusion clause (not needed here);
  * the ratio atom `RatW` is `DevRatWBody`/`DevRatW` in `DevBddDefs.lean`, with the two fibre
    values as slots (the proofs are `private` in `DevBdd_definable.lean`; the short public stub
    `Submission.Work.WilC4.DevRatW_definable` does *not* count as proved as long as its proof
    is still missing).

  The remaining helpers `GrSub_definable`, `GrSub1_definable`, `definable_isDivR`,
  `definable_eval_eq_LRc`, `definable_le_LRc`, `definable_ne_LRc`, `CandBodyDefs.univ_of_empty`,
  `definable_lt_const`, `real_definable_le`, and the final `definable_univ_iff_empty` conversion
  are all public.

  The two outer quantifier blocks (`∀ t ∈ DeepRatSet …`, and `∀ z > y, ∃ t ∈ DeepRatSet …,
  t < z`) are handled exactly like `DiagUpper` / `DiagApprox` in `Diag_definable.lean`, using
  `Set.Definable.forall_of_finite` / `exists_of_finite` with `Fin 1` blocks; there is also the
  general lemma `Work.WilC4.definable_isGLB_family` (`Submission.Work.WilC4.definable_isGLB_family`)
  which packages the glb graph of a definable family in one step.
-/
import Mathlib
import Submission.Work.WilC4.ULPMDev
import Submission.Work.WilC4.ULPMDefs
import Submission.Work.WilC4.DiagDefs

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open Work.WilC4.Route (Gr)

variable {k : ℕ}

/-- The numbers contributed by the bad points at scale `β`: for a `β`-deep point `x > 0` of the
fibre `f_c` whose doubling ratio `w = f_c(2x)/f_c(x)` is `≥ β` in absolute value, the number

    max ( f_c(βx)/f_c(x) , f_c(x)/f_c(x/β) ).

All the fibre values are carried by explicit slots (`y` at `x`, `y₂` at `2x`, `v` at `βx`, `y₀`
at `x/β`), because only the relation `Gr Y` — not the (non-definable) value function `valY` — may
occur in a `Definable` statement.  The quotients are the division relations `IsDivR`. -/
def DeepRatSet (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ)) (β : ℝ) : Set ℝ :=
  {t | ∃ (c : Fin k → ℝ) (x w y y₂ v y₀ A B : ℝ),
      0 < x ∧ IsDeepR B₀ c β x ∧
      Gr Y c x y ∧ y ≠ 0 ∧ Gr Y c (2 * x) y₂ ∧ w * y = y₂ ∧
      (β ≤ w ∨ w ≤ -β) ∧
      Gr Y c (β * x) v ∧ Gr Y c (x / β) y₀ ∧
      IsDivR v y A ∧ IsDivR y y₀ B ∧ t = max A B}

/-- The graph of the glb of `DeepRatSet Y B₀ β` over the scales `β ≥ 1`. -/
def DeepThetaG (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ)) : Set (Fin 2 → ℝ) :=
  {v | 1 ≤ v 0 ∧ IsGLB (DeepRatSet Y B₀ (v 0)) (v 1)}

theorem mem_deepThetaG {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    {v : Fin 2 → ℝ} :
    v ∈ DeepThetaG Y B₀ ↔ 1 ≤ v 0 ∧ IsGLB (DeepRatSet Y B₀ (v 0)) (v 1) := Iff.rfl

theorem mem_deepThetaG_vec {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    {β y : ℝ} :
    ![β, y] ∈ DeepThetaG Y B₀ ↔ 1 ≤ β ∧ IsGLB (DeepRatSet Y B₀ β) y := by
  simp [DeepThetaG]

/-- `DeepThetaG Y B₀` is the graph of a function: the greatest lower bound of a set of reals is
unique. -/
theorem deepThetaG_functional (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ)) :
    ∀ x y y' : ℝ, ![x, y] ∈ DeepThetaG Y B₀ → ![x, y'] ∈ DeepThetaG Y B₀ → y = y' := by
  intro x y y' hy hy'
  rw [mem_deepThetaG_vec] at hy hy'
  exact IsGLB.unique hy.2 hy'.2

end Work.WilC4
