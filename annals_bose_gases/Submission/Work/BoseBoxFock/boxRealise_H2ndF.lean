import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.boxTwin
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.boxRealise_H2ndF` — the box ↔ model dictionary of `H2ndF`

The row-by-row operator identity of FS `lem:2ndQuand`:

    `boxRealise e (d+2) (H2ndF f g NH PHs E gHat0 Ψ) = AVf e f g T_NH PHs E gHat0 d
        (boxRealise e (d+2) Ψ)`

for every model vector `Ψ` of degree `d + 2`, given `NH = dGamma m T_NH`.

The proof is termwise: the expression tree of `H2ndF` is pushed down to its leaves and each
leaf is rewritten by the dictionary lemmas of `Submission/Work/BoseDict/` (collected in
`boxTwin.lean`).

Two technical points are worth recording.

* The model operators `L₀ = ℓ⁻³Ŵ₁(0) n₀ − μŴ₁(0)` and `L₁ = ℓ⁻³Ŵ₁ω(0) n₀` are written in
  `H2ndF` as `let`-bound linear maps.  On the box side the corresponding objects are the
  *functions* `L0box`, `L1box` out of `Xn (d+2) → ℂ`, so the comparison of the two `χ̂`-rows
  must be made with `L₀` still folded: otherwise `(c • n₀ − c' • 1) X` is distributed by
  `LinearMap.sub_apply`, and recombining requires linearity of `boxAnnOf`/`boxCreOf` in the
  state (available only with integrability side conditions).  We therefore introduce the
  *opaque* copies `L0F`, `L1F` of `L0f`, `L1f` — `L0f`, `L1f` are `abbrev`s, so `simp` unfolds
  them, which reintroduces the distribution — and fold the goal into them before pushing the
  state variable in.
* The dictionary lemmas are conditional (they ask that the state have degree `d + 2`), and
  `simp only` cannot discharge such premises.  The leaf rules are therefore instantiated as
  local hypotheses of the proof, with the degree premises discharged by hand.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

open Work.BoseB4 Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

variable {m : ℕ} [NeZero m]

/-! ## 0. Opaque copies of the two `χ̂`-row one-body operators, and leaf helpers -/

/-- The `χ̂`-row operator `L₀ = ℓ⁻³Ŵ₁(0) n₀ − μŴ₁(0)`, as an opaque definition. -/
noncomputable def L0F {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) : RealFock m →ₗ[ℝ] RealFock m :=
  (E.ell ^ (-(3 : ℝ)) * E.W1 0) • n0 - (E.mu * E.W1 0) • (1 : RealFock m →ₗ[ℝ] RealFock m)

/-- The `χ̂²`-row operator `L₁ = ℓ⁻³Ŵ₁ω(0) n₀`, as an opaque definition. -/
noncomputable def L1F {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) : RealFock m →ₗ[ℝ] RealFock m :=
  (E.ell ^ (-(3 : ℝ)) * E.W1omega0) • n0

/-- The defining equation of `L0F` (used in the `←` direction, to fold the goal). -/
theorem L0F_eq {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) : (L0F E : RealFock m →ₗ[ℝ] RealFock m)
      = (E.ell ^ (-(3 : ℝ)) * E.W1 0) • n0
        - (E.mu * E.W1 0) • (1 : RealFock m →ₗ[ℝ] RealFock m) :=
  rfl

/-- The defining equation of `L1F` (used in the `←` direction, to fold the goal). -/
theorem L1F_eq {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) :
    (L1F E : RealFock m →ₗ[ℝ] RealFock m) = (E.ell ^ (-(3 : ℝ)) * E.W1omega0) • n0 :=
  rfl

/-- `L0F` is (definitionally) the `abbrev` `L0f`.  Needed to apply `boxRealise_L0f`, whose
statement is phrased with `L0f` (`rw` cannot match across the `abbrev`). -/
theorem L0F_eq_L0f {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) : (L0F E : RealFock m →ₗ[ℝ] RealFock m) = L0f E := rfl

/-- `L1F` is (definitionally) the `abbrev` `L1f`. -/
theorem L1F_eq_L1f {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) : (L1F E : RealFock m →ₗ[ℝ] RealFock m) = L1f E := rfl

/-- Degrees are preserved by `L0F`. -/
theorem support_deg_L0F {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (E : Work.BoseB7.Q3Env Mode) {d : ℕ} {X : RealFock m}
    (hX : ∀ α ∈ X.support, α.sum (fun _ k => k) = d + 2) :
    ∀ α ∈ (L0F E X).support, α.sum (fun _ k => k) = d + 2 :=
  support_deg_L0f E hX

/-- Degrees are preserved by `L1F`. -/
theorem support_deg_L1F {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (E : Work.BoseB7.Q3Env Mode) {d : ℕ} {X : RealFock m}
    (hX : ∀ α ∈ X.support, α.sum (fun _ k => k) = d + 2) :
    ∀ α ∈ (L1F E X).support, α.sum (fun _ k => k) = d + 2 :=
  support_deg_L1f E hX

/-- The box dictionary for the `nExc` row, in the form in which the push produces it. -/
theorem boxRealise_totNum_sub_n0 {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {d : ℕ} (Ψ : RealFock m) (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d + 2) :
    boxRealise e (d + 2) (totNumOp m Ψ) - boxRealise e (d + 2) (n0 Ψ)
      = boxSlotSum e (boxT0 m) (boxRealise e (d + 2) Ψ) := by
  rw [← map_sub]
  have h1 : ((totNumOp m - n0 : RealFock m →ₗ[ℝ] RealFock m)) Ψ = nExc Ψ := rfl
  rw [← LinearMap.sub_apply, h1, nExc_eq_dGamma_boxT0]
  exact boxRealise_dGamma he hbdd hsupp (boxT0 m) Ψ hΨ

/-- Degrees of the two-letter word `creOf m v (ann m 0 Ψ)` (the argument of the `L0F`/`L1F`
leaves of the `χ̂`-rows). -/
theorem deg_creOf_ann0 {d : ℕ} (v : Fin m → ℝ) (Ψ : RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d + 2) :
    ∀ α ∈ (creOf m v (ann m 0 Ψ)).support, α.sum (fun _ k => k) = d + 2 := by
  have h1 : ∀ β ∈ (ann m 0 Ψ).support, β.sum (fun _ k => k) = d + 1 := by
    rw [ann_eq_annOf_evec0]
    exact annOf_support_degree (evec0 m) Ψ hΨ
  exact creOf_support_degree v (ann m 0 Ψ) h1

/-- Degrees of the two-letter word `creOf m v (annOf m v Ψ)` (the argument of the `L0F`/`L1F`
leaves of the `n₀n₊` row). -/
theorem deg_creOf_annOf {d : ℕ} (v : Fin m → ℝ) (Ψ : RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d + 2) :
    ∀ α ∈ (creOf m v (annOf m v Ψ)).support, α.sum (fun _ k => k) = d + 2 := by
  have h1 : ∀ β ∈ (annOf m v Ψ).support, β.sum (fun _ k => k) = d + 1 :=
    annOf_support_degree v Ψ hΨ
  exact creOf_support_degree v (annOf m v Ψ) h1

/-- A finite sum of vectors all of whose monomials have degree `k` has all its monomials of
degree `k`. -/
theorem support_deg_finsetSum {ι : Type*} (s : Finset ι) (X : ι → RealFock m) {k : ℕ}
    (hX : ∀ i ∈ s, ∀ α ∈ (X i).support, α.sum (fun _ j => j) = k) :
    ∀ α ∈ (∑ i ∈ s, X i).support, α.sum (fun _ j => j) = k := by
  intro α hα
  rw [Finsupp.mem_support_iff, Finsupp.finsetSum_apply] at hα
  have hex : ∃ i ∈ s, X i α ≠ 0 := by
    by_contra h
    push_neg at h
    exact hα (Finset.sum_eq_zero h)
  obtain ⟨i, hi, hne⟩ := hex
  exact hX i hi α (Finsupp.mem_support_iff.mpr hne)

/-- The box dictionary for the two-letter word `creOf m w (ann m 0 Ψ)` (the first halves of
the `χ̂`-rows). -/
theorem boxRealise_creOf_ann0 {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {d : ℕ} (w : Fin m → ℝ) (Ψ : RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d + 2) :
    boxRealise e (d + 2) (creOf m w (ann m 0 Ψ))
      = bW2 e w (evec0 m) d (boxRealise e (d + 2) Ψ) := by
  rw [ann_eq_annOf_evec0]
  exact boxRealise_leaf_bW2 he hbdd hsupp w (evec0 m) Ψ hΨ

/-- The box dictionary for the two-letter word `cre m 0 (annOf m v X)`. -/
theorem boxRealise_cre_annOf {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {d : ℕ} (v : Fin m → ℝ) (X : RealFock m)
    (hX : ∀ α ∈ X.support, α.sum (fun _ k => k) = d + 2) :
    boxRealise e (d + 2) (cre m 0 (annOf m v X))
      = bW2 e (evec0 m) v d (boxRealise e (d + 2) X) := by
  rw [cre_eq_creOf_evec0]
  exact boxRealise_leaf_bW2 he hbdd hsupp (evec0 m) v X hX

/-! ## 1. The operator identity -/

theorem boxRealise_H2ndF {m : ℕ} [NeZero m] {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (he : ∀ l l', (∫ x : Work.BoseDict.Sp, (starRingEnd ℂ) (e l x) * e l' x)
      = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (f g : Mode → Fin m → ℝ) (NH : Work.BoseB4.RealFock m →ₗ[ℝ] Work.BoseB4.RealFock m)
    (T_NH : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (hNH : NH = Work.BoseB4.dGamma m T_NH)
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) (d : ℕ)
    (Ψ : Work.BoseB4.RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d + 2) :
    Work.BoseDict.boxRealise e (d + 2) (Work.BoseBoxFock.H2ndF f g NH PHs E gHat0 Ψ)
      = Work.BoseBoxFock.AVf e f g T_NH PHs E gHat0 d
          (Work.BoseDict.boxRealise e (d + 2) Ψ) := by
  -- ### The leaf dictionary rules, with their degree premises discharged
  have hOB : ∀ w : Fin m → ℝ,
      boxRealise e (d + 2) (creOf m w (annOf m w Ψ))
        = boxSlotSum e (rankOne w) (boxRealise e (d + 2) Ψ) :=
    fun w => boxRealise_leaf_bOB he hbdd hsupp w Ψ hΨ
  have hRow2 : boxRealise e (d + 2) (totNumOp m Ψ) - boxRealise e (d + 2) (n0 Ψ)
      = boxSlotSum e (boxT0 m) (boxRealise e (d + 2) Ψ) :=
    boxRealise_totNum_sub_n0 he hbdd hsupp Ψ hΨ
  have hNHleaf : boxRealise e (d + 2) (dGamma m T_NH Ψ)
      = boxSlotSum e T_NH (boxRealise e (d + 2) Ψ) :=
    boxRealise_dGamma he hbdd hsupp T_NH Ψ hΨ
  have hPair : boxRealise e (d + 2) (cre m 0 (cre m 0 (ann m 0 (ann m 0 Ψ))))
      = bW4 e (evec0 m) (evec0 m) (evec0 m) (evec0 m) d (boxRealise e (d + 2) Ψ) :=
    boxRealise_rowPair00 he hbdd hsupp Ψ hΨ
  have hN0 : boxRealise e (d + 2) (n0 Ψ)
      = boxSlotSum e (rankOne (evec0 m)) (boxRealise e (d + 2) Ψ) :=
    boxRealise_n0 he hbdd hsupp Ψ hΨ
  have hLin1 : ∀ k : Mode,
      boxRealise e (d + 2) (cre m 0 (creOf m (f k) (annOf m (f k) (ann m 0 Ψ))))
        = bW4 e (evec0 m) (f k) (f k) (evec0 m) d (boxRealise e (d + 2) Ψ) :=
    fun k => boxRealise_rowLin1 he hbdd hsupp (f k) Ψ hΨ
  have hBog1 : ∀ k : Mode,
      boxRealise e (d + 2) (cre m 0 (cre m 0 (annOf m (f k) (annOf m (f (-k)) Ψ))))
        = bW4 e (evec0 m) (evec0 m) (f k) (f (-k)) d (boxRealise e (d + 2) Ψ) :=
    fun k => boxRealise_rowBog1 he hbdd hsupp (f k) (f (-k)) Ψ hΨ
  have hBog2 : ∀ k : Mode,
      boxRealise e (d + 2) (creOf m (f k) (creOf m (f (-k)) (ann m 0 (ann m 0 Ψ))))
        = bW4 e (f k) (f (-k)) (evec0 m) (evec0 m) d (boxRealise e (d + 2) Ψ) :=
    fun k => boxRealise_rowBog2 he hbdd hsupp (f k) (f (-k)) Ψ hΨ
  have hW2f : ∀ k : Mode, boxRealise e (d + 2) (creOf m (f k) (ann m 0 Ψ))
      = bW2 e (f k) (evec0 m) d (boxRealise e (d + 2) Ψ) :=
    fun k => boxRealise_creOf_ann0 he hbdd hsupp (f k) Ψ hΨ
  have hW2g : ∀ k : Mode, boxRealise e (d + 2) (creOf m (g k) (ann m 0 Ψ))
      = bW2 e (g k) (evec0 m) d (boxRealise e (d + 2) Ψ) :=
    fun k => boxRealise_creOf_ann0 he hbdd hsupp (g k) Ψ hΨ
  have hL0a : ∀ k : Mode,
      boxRealise e (d + 2) (L0F E (creOf m (f k) (ann m 0 Ψ)))
        = L0box e E d (boxRealise e (d + 2) (creOf m (f k) (ann m 0 Ψ))) :=
    fun k => boxRealise_L0f he hbdd hsupp E (creOf m (f k) (ann m 0 Ψ))
      (deg_creOf_ann0 (f k) Ψ hΨ)
  have hL0b : boxRealise e (d + 2) (L0F E Ψ) = L0box e E d (boxRealise e (d + 2) Ψ) :=
    boxRealise_L0f he hbdd hsupp E Ψ hΨ
  have hL1a : ∀ k : Mode,
      boxRealise e (d + 2) (L1F E (creOf m (g k) (ann m 0 Ψ)))
        = L1box e E d (boxRealise e (d + 2) (creOf m (g k) (ann m 0 Ψ))) :=
    fun k => boxRealise_L1f he hbdd hsupp E (creOf m (g k) (ann m 0 Ψ))
      (deg_creOf_ann0 (g k) Ψ hΨ)
  have hL1b : boxRealise e (d + 2) (L1F E Ψ) = L1box e E d (boxRealise e (d + 2) Ψ) :=
    boxRealise_L1f he hbdd hsupp E Ψ hΨ
  have hW2L0 : ∀ k : Mode,
      boxRealise e (d + 2) (cre m 0 (annOf m (f k) (L0F E Ψ)))
        = bW2 e (evec0 m) (f k) d (boxRealise e (d + 2) (L0F E Ψ)) :=
    fun k => boxRealise_cre_annOf he hbdd hsupp (f k) (L0F E Ψ) (support_deg_L0F E hΨ)
  have hW2L1 : ∀ k : Mode,
      boxRealise e (d + 2) (cre m 0 (annOf m (g k) (L1F E Ψ)))
        = bW2 e (evec0 m) (g k) d (boxRealise e (d + 2) (L1F E Ψ)) :=
    fun k => boxRealise_cre_annOf he hbdd hsupp (g k) (L1F E Ψ) (support_deg_L1F E hΨ)
  have hQ3a : ∀ s k : Mode,
      boxRealise e (d + 2)
          (cre m 0 (creOf m (g s) (annOf m (f (s - k)) (annOf m (f k) Ψ))))
        = bW4 e (evec0 m) (g s) (f (s - k)) (f k) d (boxRealise e (d + 2) Ψ) :=
    fun s k => boxRealise_rowQ3a he hbdd hsupp (g s) (f (s - k)) (f k) Ψ hΨ
  have hQ3b : ∀ s k : Mode,
      boxRealise e (d + 2)
          (creOf m (f k) (creOf m (f (s - k)) (annOf m (g s) (ann m 0 Ψ))))
        = bW4 e (f k) (f (s - k)) (g s) (evec0 m) d (boxRealise e (d + 2) Ψ) :=
    fun s k => boxRealise_rowQ3b he hbdd hsupp (f k) (f (s - k)) (g s) Ψ hΨ
  -- the `n₀n₊` row: `L0F`/`L1F` are applied to the *sum* `∑ k, a_k† a_k Ψ`
  have hL0d : boxRealise e (d + 2) (L0F E (∑ k : Mode, creOf m (f k) (annOf m (f k) Ψ)))
      = L0box e E d (∑ k : Mode, boxSlotSum e (rankOne (f k)) (boxRealise e (d + 2) Ψ)) := by
    rw [L0F_eq_L0f,
      boxRealise_L0f he hbdd hsupp E _
        (support_deg_finsetSum Finset.univ _ (fun k _ => deg_creOf_annOf (f k) Ψ hΨ))]
    congr 1
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => boxRealise_leaf_bOB he hbdd hsupp (f k) Ψ hΨ
  have hL1d : boxRealise e (d + 2) (L1F E (∑ k : Mode, creOf m (f k) (annOf m (f k) Ψ)))
      = L1box e E d (∑ k : Mode, boxSlotSum e (rankOne (f k)) (boxRealise e (d + 2) Ψ)) := by
    rw [L1F_eq_L1f,
      boxRealise_L1f he hbdd hsupp E _
        (support_deg_finsetSum Finset.univ _ (fun k _ => deg_creOf_annOf (f k) Ψ hΨ))]
    congr 1
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => boxRealise_leaf_bOB he hbdd hsupp (f k) Ψ hΨ

  -- ### `boxRealise`-restricted push rules
  -- The generic `map_add`/`map_sum`/… would also distribute the *opaque* `L0F`/`L1F`
  -- (`L0F E (∑ k, X k) ↦ ∑ k, L0F E (X k)`), which would break the comparison with the box
  -- side; restricting them to `boxRealise` keeps the `L0F`-blocks folded.
  have hMapAdd : ∀ X Y : RealFock m,
      boxRealise e (d + 2) (X + Y) = boxRealise e (d + 2) X + boxRealise e (d + 2) Y :=
    fun X Y => map_add _ X Y
  have hMapSub : ∀ X Y : RealFock m,
      boxRealise e (d + 2) (X - Y) = boxRealise e (d + 2) X - boxRealise e (d + 2) Y :=
    fun X Y => map_sub _ X Y
  have hMapSmul : ∀ (r : ℝ) (X : RealFock m),
      boxRealise e (d + 2) (r • X) = r • boxRealise e (d + 2) X :=
    fun r X => map_smul _ r X
  have hMapSum : ∀ (s : Finset Mode) (X : Mode → RealFock m),
      boxRealise e (d + 2) (∑ i ∈ s, X i) = ∑ i ∈ s, boxRealise e (d + 2) (X i) :=
    fun s X => map_sum _ X s

  -- ### Unfold `H2ndF` and fold the two `χ̂`-row operators
  simp only [H2ndF, ← L0F_eq, ← L1F_eq]
  -- ### Push the applied linear maps down to the leaves
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply]
  -- ### Push `boxRealise` (only) inside
  simp only [hMapAdd, hMapSub, hMapSmul, hMapSum]
  -- ### Rewrite the leaves
  simp only [hNH, hRow2]
  simp only [hOB, hNHleaf, hPair, hN0, hLin1, hBog1, hBog2,
    hW2f, hW2g, hL0a, hL0b, hL1a, hL1b, hL0d, hL1d, hW2L0, hW2L1, hQ3a, hQ3b]
  -- ### Push the box side into the same normal form
  simp only [AVf, bOB, bW2, bW4, L0box, L1box, Finset.sum_apply, Pi.smul_apply, Pi.add_apply,
    Pi.sub_apply, Function.comp_apply, id_eq]

end Work.BoseBoxFock
