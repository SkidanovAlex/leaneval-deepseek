import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.boxTwinDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.boxTwin` — the box ↔ model dictionary of `H2ndF` (BF3, stage A)

The row-by-row **operator** identity of FS `lem:2ndQuand`: for every model vector `Ψ` of
degree `d + 2`,

    `boxRealise e (d+2) (H2ndF f g NH PHs E gHat0 Ψ) = AVf e f g T_NH PHs E gHat0 d
        (boxRealise e (d+2) Ψ)`                                          (`boxRealise_H2ndF`)

(given `NH = dGamma m T_NH`), and its pairing consequences

* `cIPn_H2ndF` — the **sesquilinear** dictionary
  `cIPn (d+2) (boxRealise e (d+2) Ψ) (AVf … d (boxRealise e (d+2) Ψ')) = ↑(bomb m Ψ (H2ndF … Ψ'))`,
* `bomb_H2ndF_self` — the diagonal form `bomb m Ψ (H2ndF … Ψ) = re (cIPn …)`.

The proof is termwise: the expression tree of `H2ndF` is pushed down to its leaves, and each
leaf — a ladder word in `ann m 0`, `cre m 0`, `annOf m (f k)`, `creOf m (f k)`, `annOf m (g s)`,
`creOf m (g s)`, a `dGamma`, or a one-particle operator combination `L0`, `L1` — is rewritten by
the on-disk dictionary lemma of `Submission/Work/BoseDict/`:

| leaf | lemma |
|---|---|
| `ann m 0` | `Work.BoseDict.boxRealise_annOf` (after `ann_eq_annOf_evec0`) |
| `cre m 0` | `Work.BoseDict.CreOfAnnAux.boxCreOf_boxRealise` (after `cre_eq_creOf_evec0`) |
| `creOf w ∘ annOf v` | `Work.BoseDict.boxRealise_creOf_annOf` |
| `creOf w₁ ∘ creOf w₂ ∘ annOf v₁ ∘ annOf v₂` | `Work.BoseDict.boxRealise_creOf_creOf_annOf_annOf` |
| `dGamma m T` | `Work.BoseDict.boxRealise_dGamma` |

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

open Work.BoseB4 Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

variable {m : ℕ} [NeZero m] {ℓ : ℝ} {e : Fin m → Sp → ℂ}

/-! ## 1. The leaf dictionary identities -/

/-- **The one-body leaf** (the `creOf w ∘ annOf w` word): the box realisation of the ladder
word is the box slot sum of the rank-one operator `|w⟩⟨w|`. -/
theorem boxRealise_leaf_bOB (he : ∀ l l',
      (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {d : ℕ} (w : Fin m → ℝ) (Ψ : RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d + 2) :
    boxRealise e (d + 2) ((creOf m w).comp (annOf m w) Ψ)
      = boxSlotSum e (rankOne w) (boxRealise e (d + 2) Ψ) := by
  rw [← dGamma_rankOne_eq w]
  exact boxRealise_dGamma he hbdd hsupp (rankOne w) Ψ hΨ

/-- **The two-letter leaf**: the box realisation of `creOf w ∘ annOf v`. -/
theorem boxRealise_leaf_bW2 (he : ∀ l l',
      (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {d : ℕ} (w v : Fin m → ℝ) (Ψ : RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d + 2) :
    boxRealise e (d + 2) ((creOf m w).comp (annOf m v) Ψ)
      = bW2 e w v d (boxRealise e (d + 2) Ψ) := by
  rw [LinearMap.comp_apply]
  exact boxRealise_creOf_annOf (d := d + 1) he hbdd hsupp w v Ψ hΨ

/-- **The four-letter leaf**: the box realisation of `creOf w₁ ∘ creOf w₂ ∘ annOf v₁ ∘ annOf v₂`. -/
theorem boxRealise_leaf_bW4 (he : ∀ l l',
      (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {d : ℕ} (w₁ w₂ v₁ v₂ : Fin m → ℝ) (Ψ : RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d + 2) :
    boxRealise e (d + 2)
        (creOf m w₁ (creOf m w₂ (annOf m v₁ (annOf m v₂ Ψ))))
      = bW4 e w₁ w₂ v₁ v₂ d (boxRealise e (d + 2) Ψ) :=
  boxRealise_creOf_creOf_annOf_annOf he hbdd hsupp w₁ w₂ v₁ v₂ Ψ hΨ

/-- **A `dGamma` leaf** (the `NH` and gap rows). -/
theorem boxRealise_leaf_dGamma (he : ∀ l l',
      (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {d : ℕ} (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (Ψ : RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d + 2) :
    boxRealise e (d + 2) (dGamma m T Ψ) = boxSlotSum e T (boxRealise e (d + 2) Ψ) :=
  boxRealise_dGamma he hbdd hsupp T Ψ hΨ

/-! ## 2. The box realisations of the model rows, in the forms the assembly consumes -/

section Rows

variable {d : ℕ}

/-- **Row 1** (kinetic): the box realisation of `Σ_k τ_k a_k†a_k` is the corresponding sum of
slot sums. -/
theorem boxRealise_rowKin {Mode : Type*} [Fintype Mode] (he : ∀ l l',
      (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (tau : Mode → ℝ) (f : Mode → Fin m → ℝ) (Ψ : RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d + 2) :
    boxRealise e (d + 2) (∑ k : Mode, tau k • (((creOf m (f k)).comp (annOf m (f k))) Ψ))
      = ∑ k : Mode, tau k •
          (bOB e (rankOne (f k)) (d := d) (boxRealise e (d + 2) Ψ)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  congr 1
  exact boxRealise_leaf_bOB he hbdd hsupp (f k) Ψ hΨ

/-- **Row 5** (`n₀`): the box realisation of `n₀ = a₀†a₀`. -/
theorem boxRealise_rowN0 (he : ∀ l l',
      (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (Ψ : RealFock m) (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d + 2) :
    boxRealise e (d + 2) (n0 Ψ)
      = bOB e (rankOne (evec0 m)) (d := d) (boxRealise e (d + 2) Ψ) := by
  rw [n0, LinearMap.comp_apply, cre_eq_creOf_evec0, ann_eq_annOf_evec0]
  exact boxRealise_leaf_bOB he hbdd hsupp (evec0 m) Ψ hΨ

/-- **Row 2** (gap `N − n₀ = nExc`): the box realisation of `nExc = dGamma m (boxT0 m)`. -/
theorem boxRealise_rowGap (he : ∀ l l',
      (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (Ψ : RealFock m) (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d + 2) :
    boxRealise e (d + 2) (nExc Ψ)
      = bOB e (boxT0 m) (d := d) (boxRealise e (d + 2) Ψ) := by
  rw [nExc_eq_dGamma_boxT0]
  exact boxRealise_leaf_dGamma he hbdd hsupp (boxT0 m) Ψ hΨ

/-- **Row 3** (`NH`): given `NH = dGamma m T`, the box realisation is the slot sum of `T`. -/
theorem boxRealise_rowNH (he : ∀ l l',
      (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (NH : RealFock m →ₗ[ℝ] RealFock m) (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (hNH : NH = dGamma m T) (Ψ : RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d + 2) :
    boxRealise e (d + 2) (NH Ψ)
      = bOB e T (d := d) (boxRealise e (d + 2) Ψ) := by
  rw [hNH]
  exact boxRealise_leaf_dGamma he hbdd hsupp T Ψ hΨ

/-- **Row 4** (contact, `a₀†²a₀²`). -/
theorem boxRealise_rowPair00 (he : ∀ l l',
      (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (Ψ : RealFock m) (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d + 2) :
    boxRealise e (d + 2) (cre m 0 (cre m 0 (ann m 0 (ann m 0 Ψ))))
      = bW4 e (evec0 m) (evec0 m) (evec0 m) (evec0 m) d (boxRealise e (d + 2) Ψ) := by
  simp only [cre_eq_creOf_evec0, ann_eq_annOf_evec0]
  exact boxRealise_leaf_bW4 he hbdd hsupp (evec0 m) (evec0 m) (evec0 m) (evec0 m) Ψ hΨ

/-- **Row 6** (`a₀†a_k†a_ka₀`). -/
theorem boxRealise_rowLin1 (he : ∀ l l',
      (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (f : Fin m → ℝ) (Ψ : RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d + 2) :
    boxRealise e (d + 2) (cre m 0 (creOf m f (annOf m f (ann m 0 Ψ))))
      = bW4 e (evec0 m) f f (evec0 m) d (boxRealise e (d + 2) Ψ) := by
  simp only [cre_eq_creOf_evec0, ann_eq_annOf_evec0]
  exact boxRealise_leaf_bW4 he hbdd hsupp (evec0 m) f f (evec0 m) Ψ hΨ

/-- **Row 7a** (Bogoliubov `a₀†a₀†a_ka_{−k}`). -/
theorem boxRealise_rowBog1 (he : ∀ l l',
      (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (f : Fin m → ℝ) (f' : Fin m → ℝ) (Ψ : RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d + 2) :
    boxRealise e (d + 2) (cre m 0 (cre m 0 (annOf m f (annOf m f' Ψ))))
      = bW4 e (evec0 m) (evec0 m) f f' d (boxRealise e (d + 2) Ψ) := by
  simp only [cre_eq_creOf_evec0]
  exact boxRealise_leaf_bW4 he hbdd hsupp (evec0 m) (evec0 m) f f' Ψ hΨ

/-- **Row 7b** (Bogoliubov `a_k†a_{−k}†a₀a₀`). -/
theorem boxRealise_rowBog2 (he : ∀ l l',
      (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (f : Fin m → ℝ) (f' : Fin m → ℝ) (Ψ : RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d + 2) :
    boxRealise e (d + 2) (creOf m f (creOf m f' (ann m 0 (ann m 0 Ψ))))
      = bW4 e f f' (evec0 m) (evec0 m) d (boxRealise e (d + 2) Ψ) := by
  simp only [cre_eq_creOf_evec0, ann_eq_annOf_evec0]
  exact boxRealise_leaf_bW4 he hbdd hsupp f f' (evec0 m) (evec0 m) Ψ hΨ

/-- **Row 11a** (`Q̃₃`: `a₀†a_s†a_{s−k}a_k`). -/
theorem boxRealise_rowQ3a (he : ∀ l l',
      (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (g : Fin m → ℝ) (f₁ : Fin m → ℝ) (f₂ : Fin m → ℝ) (Ψ : RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d + 2) :
    boxRealise e (d + 2) (cre m 0 (creOf m g (annOf m f₁ (annOf m f₂ Ψ))))
      = bW4 e (evec0 m) g f₁ f₂ d (boxRealise e (d + 2) Ψ) := by
  simp only [cre_eq_creOf_evec0, ann_eq_annOf_evec0]
  exact boxRealise_leaf_bW4 he hbdd hsupp (evec0 m) g f₁ f₂ Ψ hΨ

/-- **Row 11b** (`Q̃₃`: `a_k†a_{s−k}†a_sa₀`). -/
theorem boxRealise_rowQ3b (he : ∀ l l',
      (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (f₁ : Fin m → ℝ) (f₂ : Fin m → ℝ) (g : Fin m → ℝ) (Ψ : RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d + 2) :
    boxRealise e (d + 2) (creOf m f₁ (creOf m f₂ (annOf m g (ann m 0 Ψ))))
      = bW4 e f₁ f₂ g (evec0 m) d (boxRealise e (d + 2) Ψ) := by
  simp only [cre_eq_creOf_evec0, ann_eq_annOf_evec0]
  exact boxRealise_leaf_bW4 he hbdd hsupp f₁ f₂ g (evec0 m) Ψ hΨ

end Rows

/-! ## 3. The model operators `L₀`, `L₁` of `H2ndF`, and the degree helpers -/

section RowChi

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- The model operator `L₀ = ℓ⁻³Ŵ₁(0) n₀ − μŴ₁(0)` of `H2ndF`.  An `abbrev` so that it is
definitionally the inline expression occurring in `H2ndF`. -/
noncomputable abbrev L0f (E : Work.BoseB7.Q3Env Mode) : RealFock m →ₗ[ℝ] RealFock m :=
  (E.ell ^ (-(3 : ℝ)) * E.W1 0) • n0 - (E.mu * E.W1 0) • (1 : RealFock m →ₗ[ℝ] RealFock m)

/-- The model operator `L₁ = ℓ⁻³Ŵ₁ω(0) n₀` of `H2ndF`. -/
noncomputable abbrev L1f (E : Work.BoseB7.Q3Env Mode) : RealFock m →ₗ[ℝ] RealFock m :=
  (E.ell ^ (-(3 : ℝ)) * E.W1omega0) • n0

/-- The degree-`k` set is closed under addition. -/
lemma support_deg_add {A B : RealFock m} {k : ℕ}
    (hA : ∀ α ∈ A.support, α.sum (fun _ i => i) = k)
    (hB : ∀ α ∈ B.support, α.sum (fun _ i => i) = k) :
    ∀ α ∈ (A + B).support, α.sum (fun _ i => i) = k := by
  intro γ hγ
  have h : A γ + B γ ≠ 0 := by
    rw [← Finsupp.add_apply]
    exact Finsupp.mem_support_iff.mp hγ
  rcases eq_or_ne (A γ) 0 with h0 | h0
  · exact hB γ (Finsupp.mem_support_iff.mpr (by rwa [h0, zero_add] at h))
  · exact hA γ (Finsupp.mem_support_iff.mpr h0)

/-- The degree-`k` set is closed under scalar multiples. -/
lemma support_deg_smul {A : RealFock m} {c : ℝ} {k : ℕ}
    (hA : ∀ α ∈ A.support, α.sum (fun _ i => i) = k) :
    ∀ α ∈ (c • A).support, α.sum (fun _ i => i) = k := by
  intro γ hγ
  have h : c * A γ ≠ 0 := by
    have h0 := Finsupp.mem_support_iff.mp hγ
    rwa [Finsupp.smul_apply] at h0
  exact hA γ (Finsupp.mem_support_iff.mpr (fun h0 => h (by rw [h0, mul_zero])))

/-- The degree-`k` set is closed under `A ↦ c • A - c' • B`. -/
lemma support_deg_sub_smul {A B : RealFock m} {c c' : ℝ} {k : ℕ}
    (hA : ∀ α ∈ A.support, α.sum (fun _ i => i) = k)
    (hB : ∀ α ∈ B.support, α.sum (fun _ i => i) = k) :
    ∀ α ∈ (c • A - c' • B).support, α.sum (fun _ i => i) = k := by
  have h1 : (c • A - c' • B : RealFock m) = c • A + (-c') • B := by
    rw [sub_eq_add_neg, neg_smul]
  rw [h1]
  exact support_deg_add (support_deg_smul hA) (support_deg_smul hB)

/-- **The `n₀` leaf**: the box realisation of `n₀ X` for any `X` of degree `d + 2`. -/
theorem boxRealise_n0 (he : ∀ l l',
      (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {d : ℕ} (X : RealFock m) (hX : ∀ α ∈ X.support, α.sum (fun _ k => k) = d + 2) :
    boxRealise e (d + 2) (n0 X)
      = boxSlotSum e (rankOne (evec0 m)) (boxRealise e (d + 2) X) := by
  rw [n0, LinearMap.comp_apply, cre_eq_creOf_evec0, ann_eq_annOf_evec0]
  exact boxRealise_leaf_bOB he hbdd hsupp (evec0 m) X hX

/-- **The `L₀` leaf**: `boxRealise (L₀ X) = L0box (boxRealise X)`. -/
theorem boxRealise_L0f (he : ∀ l l',
      (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (E : Work.BoseB7.Q3Env Mode) {d : ℕ} (X : RealFock m)
    (hX : ∀ α ∈ X.support, α.sum (fun _ k => k) = d + 2) :
    boxRealise e (d + 2) (L0f E X) = L0box e E d (boxRealise e (d + 2) X) := by
  rw [L0f, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_sub, map_smul, map_smul,
    boxRealise_n0 he hbdd hsupp X hX]
  rw [L0box]
  rfl

/-- **The `L₁` leaf**: `boxRealise (L₁ X) = L1box (boxRealise X)`. -/
theorem boxRealise_L1f (he : ∀ l l',
      (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (E : Work.BoseB7.Q3Env Mode) {d : ℕ} (X : RealFock m)
    (hX : ∀ α ∈ X.support, α.sum (fun _ k => k) = d + 2) :
    boxRealise e (d + 2) (L1f E X) = L1box e E d (boxRealise e (d + 2) X) := by
  rw [L1f, LinearMap.smul_apply, map_smul, boxRealise_n0 he hbdd hsupp X hX]
  rw [L1box]
  rfl

/-- The degree of `L₀ X` for `X` of degree `d+2`. -/
lemma support_deg_L0f (E : Work.BoseB7.Q3Env Mode) {d : ℕ} {X : RealFock m}
    (hX : ∀ α ∈ X.support, α.sum (fun _ k => k) = d + 2) :
    ∀ α ∈ (L0f E X).support, α.sum (fun _ k => k) = d + 2 := by
  have hn : ∀ α ∈ (n0 X).support, α.sum (fun _ k => k) = d + 2 := by
    rw [n0, LinearMap.comp_apply, cre_eq_creOf_evec0, ann_eq_annOf_evec0]
    have h1 : ∀ β ∈ (annOf m (evec0 m) X).support, β.sum (fun _ k => k) = d + 1 :=
      annOf_support_degree (n := d + 2) (evec0 m) X hX
    exact creOf_support_degree (evec0 m) _ h1
  rw [L0f]
  exact support_deg_sub_smul hn hX

/-- The degree of `L₁ X` for `X` of degree `d+2`. -/
lemma support_deg_L1f (E : Work.BoseB7.Q3Env Mode) {d : ℕ} {X : RealFock m}
    (hX : ∀ α ∈ X.support, α.sum (fun _ k => k) = d + 2) :
    ∀ α ∈ (L1f E X).support, α.sum (fun _ k => k) = d + 2 := by
  have hn : ∀ α ∈ (n0 X).support, α.sum (fun _ k => k) = d + 2 := by
    rw [n0, LinearMap.comp_apply, cre_eq_creOf_evec0, ann_eq_annOf_evec0]
    have h1 : ∀ β ∈ (annOf m (evec0 m) X).support, β.sum (fun _ k => k) = d + 1 :=
      annOf_support_degree (n := d + 2) (evec0 m) X hX
    exact creOf_support_degree (evec0 m) _ h1
  rw [L1f, LinearMap.smul_apply]
  exact support_deg_smul hn

end RowChi

end Work.BoseBoxFock
