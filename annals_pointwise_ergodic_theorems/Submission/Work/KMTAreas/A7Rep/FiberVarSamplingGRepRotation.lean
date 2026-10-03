/-
# The window/phase-rotation identity for the twisted fibre at an arbitrary residue

This is the `A7Rep`-side companion of `Work.KMTAreas.A7Hi.rotationIdentity`: the exact algebraic
reduction of the target `Work.KMTAreas.A7.FiberVarSamplingGRep` (and of the tree's crux
`Work.KMTAreas.A7Hi.FiberOpCutZeroVarBound`) to the **per-window constant-phase rotation bound**.

## The objects

For a finite set `A` of arithmetic frequencies, a bump `m : ℝ → ℂ` and an input `v : ℤ → ℂ`:

* `winModRep α v = e(-α·)·v` is the **window modulation** `M_α` (written with the circle character
  `fourier (T := 1) (-x) α`, so that no representative of the class `α : Circle` is chosen);
* `winConvRep m v = ∑'_j (cw m j)·v(· - j)` is the **bump convolution** `T_m`, the convolution on
  `ℤ` whose multiplier is the periodization of `m`;
* the fibre at the residue `n₀` is `fiberOpPSet P A m n₀ v`, the convolution with the kernel
  `j ↦ D_A(P(n₀) - j)·cw m j`, where `D_A(y) = ∑_{α ∈ A} e(α y)`.

## The identity (proved here, unconditionally given summability)

`fiberOpPSet P A m n₀ v x = ∑_{α ∈ A} e(α·P(n₀)) · winModRep α (winConvRep m (winModRep (-α) v)) x`.

This is *pure algebra* (a `Finset`/`tsum` interchange and the character identity
`e((n₀-j)α) = e(n₀α)·e(-jα)`); it holds with no band hypothesis and no bound on the frequencies.
It is the general-`n₀` form of `Work.KMTAreas.A7Hi.fiberOp_zero_apply_eq_windowSum` (which is the
`n₀ = 0` case, and lives in a file whose axioms are those of the still-open crux).

## Why it matters

For an input `v` whose spectrum lies in the *plateau* of the `A`-windows (the range hypothesis
`v = fiberOpSet A m' 0 v` of the tree's crux `Work.KMTAreas.A7Hi.FiberOpCutZeroVarBound`, with a
wider bump `m'` equal to `1` on `supp m`), the family `winModRep α (winConvRep m (winModRep (-α) v))`
is the `α`-window envelope of `v`, so the identity says that the fibre at the residue `n₀` is the
**phased window synthesis**

  `fiberOpPSet P A m n₀ v = ∑_{α ∈ A} e(P(n₀)α)·M_α h_α`,   `h_α = T_m (M_{-α} v)`,

i.e. it inserts the *constant* phase `e(P(n₀)α)` into the `α`-th window.  The target
`Work.KMTAreas.A7.FiberVarSamplingGRep` is therefore exactly the statement that the map

  `(h_α)_{α ∈ A} ↦ ∑_{α ∈ A} e(Mα)·M_α h_α`

is bounded on `ℓᵖ(ℤ; Vʳ)` *uniformly in the level `|A|` and in the phase `M`*: the per-window
constant-phase rotation bound of `Work.KMTAreas.A7Hi.rotationIdentity` /
`Work.KMTAreas.A7Hi.FiberOpCutZeroVarBound`.  Two ingredients of any proof of it *are* in the tree:

* the exact `ℓ²` orthogonality of the residue average,
  `Work.KMTAreas.A7.arithChar_orthogonality`
  (`∑_{n₀<q} ‖∑_{α∈A} e(α n₀)·c α‖² = q·∑_{α∈A}‖c α‖²` whenever `q • α = 0` for `α ∈ A`), which
  shows that averaging over the residues `M = P(n₀)` is an exact orthogonalisation;
* the submultiplicativity of the variational norm
  (`Work.KMTAreas.A7.variationalNorm_mul_le`, `variationalNorm_const_le`), which makes every
  *pointwise* modulation `M_c` an exact isometry of `ℓᵖ(ℤ; Vʳ)`.

What is *not* in the tree is the `Vʳ`-valued (non-Hilbert-valued) form of the rotation bound: the
`ℓ²` orthogonality above is blind to the variation in the *level* index.  See the session note
`NOTES_A7Rep_FiberVarSamplingGRep_SESSION3.md` for the identifications, the two known routes and
the obstructions recorded there.

## Contents of this file (all sorry-free)

1. the definitions `winModRep` (`M_α`), `winConvRep` (`T_m`);
2. the character algebra (`norm_fourier_rep`, `fourier_apply_neg_rep`, `fourier_mul_rep`,
   `fourier_neg_mul_rep`, `fourier_add_point_rep`);
3. the summability transport `summable_cw_mul_winMod`;
4. the single-window identity `tsum_fourier_neg_mul_eq_winModRep`;
5. the **window/rotation identity** `fiberOpSet_apply_eq_windowRotation` (arbitrary residue `n₀`)
   and its `P`-twisted / exact-height forms `fiberOpPSet_apply_eq_windowRotation`,
   `fiberOpP_apply_eq_windowRotation`;
6. the modulation calculus (`winModRep_comp`, `winModRep_neg_cancel`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.FiberGeneral

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7Rep

open MeasureTheory Finset
open scoped BigOperators ENNReal NNReal
open Work.Analysis.IonescuWainger

noncomputable section

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## 1. The window modulation and the bump convolution -/

/-- **The window modulation** `M_α v = e(-α·)·v`, realised through the circle character so that no
representative of `α : Circle` is chosen. -/
noncomputable def winModRep (α : Circ) (v : ℤ → ℂ) : ℤ → ℂ :=
  fun x => fourier (T := 1) (-x) α * v x

/-- **The bump convolution** `T_m v = ∑'_j (cw m j)·v(· - j)`: the convolution on `ℤ` whose
multiplier is the periodization `∑_j (cw m j) e(j·)` of the bump `m`. -/
noncomputable def winConvRep (m : ℝ → ℂ) (v : ℤ → ℂ) : ℤ → ℂ :=
  fun x => ∑' j : ℤ, Work.KMTAreas.A7.cw m j * v (x - j)

/-! ## 2. The character algebra -/

/-- The circle character has modulus one. -/
lemma norm_fourier_rep (n : ℤ) (α : Circ) : ‖fourier (T := 1) n α‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

/-- `fourier` at a negated *point*: `e(n·(-α)) = e((-n)·α)`. -/
lemma fourier_apply_neg_rep (n : ℤ) (α : Circ) :
    fourier (T := 1) n (-α) = fourier (T := 1) (-n) α := by
  simp only [fourier_apply, smul_neg, neg_smul]

/-- `e(n₀α)·e(-jα) = e((n₀-j)α)`. -/
lemma fourier_mul_rep (n₀ j : ℤ) (α : Circ) :
    fourier (T := 1) n₀ α * fourier (T := 1) (-j) α = fourier (T := 1) (n₀ - j) α := by
  have h := fourier_add (T := 1) (m := n₀) (n := -j) (x := α)
  rw [sub_eq_add_neg]
  exact h.symm

/-- `e(-xα)·e((x-j)α) = e(-jα)`: the character identity behind the window decomposition (the
`j`-dependence of the cross terms is the *difference* of the two frequencies). -/
lemma fourier_neg_mul_rep (x j : ℤ) (α : Circ) :
    fourier (T := 1) (-x) α * fourier (T := 1) (x - j) α = fourier (T := 1) (-j) α := by
  rw [← fourier_add]
  congr 1
  ring

/-! ## 3. The summability transport through a window modulation -/

/-- Summability of `j ↦ (cw m j)·v(x-j)` transfers to the window modulation `M_{-α} v`: the
modulation has unit modulus, so the norm of the summand is unchanged. -/
lemma summable_cw_mul_winMod (m : ℝ → ℂ) (α : Circ) (v : ℤ → ℂ) (x : ℤ)
    (hsumm : Summable (fun j : ℤ => Work.KMTAreas.A7.cw m j * v (x - j))) :
    Summable (fun j : ℤ => Work.KMTAreas.A7.cw m j
        * (fourier (T := 1) (-(x - j)) (-α) * v (x - j))) := by
  refine Summable.of_norm_bounded hsumm.norm (fun j => ?_)
  have h1 : ‖fourier (T := 1) (-(x - j)) (-α) * v (x - j)‖ = ‖v (x - j)‖ := by
    rw [norm_mul, norm_fourier_rep, one_mul]
  rw [norm_mul, h1, norm_mul]

/-! ## 4. The inner identity: `∑'_j e(-jα)·(cw m j)·v(x-j) = M_α T_m M_{-α} v` -/

/-- **The single-window identity.**  For every frequency `α`, bump `m`, input `v` and point `x`,
provided the family `j ↦ (cw m j)·v(x-j)` is summable,

  `∑'_j e(-jα)·(cw m j)·v(x-j) = winModRep α (winConvRep m (winModRep (-α) v)) x`.

This is the `α`-th summand of the window decomposition: `M_α T_m M_{-α}` is the `m`-cut of the
`α`-window of `v`. -/
theorem tsum_fourier_neg_mul_eq_winModRep (m : ℝ → ℂ) (α : Circ) (v : ℤ → ℂ) (x : ℤ)
    (hsumm : Summable (fun j : ℤ => Work.KMTAreas.A7.cw m j * v (x - j))) :
    (∑' j : ℤ, fourier (T := 1) (-j) α * (Work.KMTAreas.A7.cw m j * v (x - j)))
      = winModRep α (winConvRep m (winModRep (-α) v)) x := by
  have hR : winModRep α (winConvRep m (winModRep (-α) v)) x
      = ∑' j : ℤ, fourier (T := 1) (-x) α
          * (Work.KMTAreas.A7.cw m j * (fourier (T := 1) (-(x - j)) (-α) * v (x - j))) := by
    simp only [winModRep, winConvRep]
    rw [tsum_mul_left]
  rw [hR]
  refine tsum_congr (fun j => ?_)
  have hchar : fourier (T := 1) (-x) α * fourier (T := 1) (x - j) α
      = fourier (T := 1) (-j) α := fourier_neg_mul_rep x j α
  rw [fourier_apply_neg_rep]
  rw [← hchar]
  ring

/-! ## 5. The rotation identity for the fibre at an arbitrary residue -/

/-- **The window/phase-rotation identity (arbitrary finite frequency set and residue `n₀`).**

For every finite set `A` of circle frequencies, bump `m`, residue `n₀`, input `v` and point `x`,
provided `j ↦ (cw m j)·v(x-j)` is summable,

  `fiberOpSet A m n₀ v x = ∑_{α ∈ A} e(n₀α)·winModRep α (winConvRep m (winModRep (-α) v)) x`.

This is the general-`n₀` form of `fiberOpSet`'s `n₀ = 0` window decomposition
(`Work.KMTAreas.A7Hi.fiberOp_zero_apply_eq_windowSum`); the factor `e(n₀α)` is the *constant phase*
inserted in the `α`-th window, i.e. the rotation. -/
theorem fiberOpSet_apply_eq_windowRotation (A : Finset Circ) (m : ℝ → ℂ) (n₀ : ℤ)
    (v : ℤ → ℂ) (x : ℤ)
    (hsumm : Summable (fun j : ℤ => Work.KMTAreas.A7.cw m j * v (x - j))) :
    Work.KMTAreas.A7.fiberOpSet A m n₀ v x
      = ∑ α ∈ A, fourier (T := 1) n₀ α
          * winModRep α (winConvRep m (winModRep (-α) v)) x := by
  have hper : ∀ α : Circ, Summable (fun j : ℤ =>
      fourier (T := 1) (n₀ - j) α * (Work.KMTAreas.A7.cw m j * v (x - j))) := by
    intro α
    refine Summable.of_norm_bounded hsumm.norm (fun j => ?_)
    have h1 : ‖fourier (T := 1) (n₀ - j) α‖ = 1 := norm_fourier_rep (n₀ - j) α
    rw [norm_mul, h1, one_mul]
  have hLHS : (∑' j : ℤ, Work.KMTAreas.A7.arithCharSet A (n₀ - j)
        * Work.KMTAreas.A7.cw m j * v (x - j))
      = ∑' j : ℤ, ∑ α ∈ A, fourier (T := 1) (n₀ - j) α
          * (Work.KMTAreas.A7.cw m j * v (x - j)) := by
    refine tsum_congr (fun j => ?_)
    rw [Work.KMTAreas.A7.arithCharSet, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun α _ => by ring)
  rw [Work.KMTAreas.A7.fiberOpSet, hLHS,
    Summable.tsum_finsetSum (s := A) (fun α _ => hper α)]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [show (∑' j : ℤ, fourier (T := 1) (n₀ - j) α
        * (Work.KMTAreas.A7.cw m j * v (x - j)))
      = ∑' j : ℤ, fourier (T := 1) n₀ α
          * (fourier (T := 1) (-j) α * (Work.KMTAreas.A7.cw m j * v (x - j))) from by
    refine tsum_congr (fun j => ?_)
    rw [← fourier_mul_rep]
    ring]
  rw [tsum_mul_left]
  rw [tsum_fourier_neg_mul_eq_winModRep m α v x hsumm]

/-! ## 6. The twisted fibre at an arbitrary residue (the target's object) -/

/-- **The window/phase-rotation identity for the `P`-twisted fibre** `fiberOpPSet`: the twisted
fibre inserts the constant phase `e(P(n₀)α)` in the `α`-th window. -/
theorem fiberOpPSet_apply_eq_windowRotation (P : Polynomial ℤ) (A : Finset Circ) (m : ℝ → ℂ)
    (n₀ : ℤ) (v : ℤ → ℂ) (x : ℤ)
    (hsumm : Summable (fun j : ℤ => Work.KMTAreas.A7.cw m j * v (x - j))) :
    Work.KMTAreas.A7.fiberOpPSet P A m n₀ v x
      = ∑ α ∈ A, fourier (T := 1) (P.eval n₀) α
          * winModRep α (winConvRep m (winModRep (-α) v)) x := by
  have hper : ∀ α : Circ, Summable (fun j : ℤ =>
      fourier (T := 1) (P.eval n₀ - j) α * (Work.KMTAreas.A7.cw m j * v (x - j))) := by
    intro α
    refine Summable.of_norm_bounded hsumm.norm (fun j => ?_)
    have h1 : ‖fourier (T := 1) (P.eval n₀ - j) α‖ = 1 := norm_fourier_rep (P.eval n₀ - j) α
    rw [norm_mul, h1, one_mul]
  have hLHS : (∑' j : ℤ, Work.KMTAreas.A7.arithCharSet A (P.eval n₀ - j)
        * Work.KMTAreas.A7.cw m j * v (x - j))
      = ∑' j : ℤ, ∑ α ∈ A, fourier (T := 1) (P.eval n₀ - j) α
          * (Work.KMTAreas.A7.cw m j * v (x - j)) := by
    refine tsum_congr (fun j => ?_)
    rw [Work.KMTAreas.A7.arithCharSet, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun α _ => by ring)
  rw [Work.KMTAreas.A7.fiberOpPSet, hLHS,
    Summable.tsum_finsetSum (s := A) (fun α _ => hper α)]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [show (∑' j : ℤ, fourier (T := 1) (P.eval n₀ - j) α
        * (Work.KMTAreas.A7.cw m j * v (x - j)))
      = ∑' j : ℤ, fourier (T := 1) (P.eval n₀) α
          * (fourier (T := 1) (-j) α * (Work.KMTAreas.A7.cw m j * v (x - j))) from by
    refine tsum_congr (fun j => ?_)
    rw [← fourier_mul_rep]
    ring]
  rw [tsum_mul_left]
  rw [tsum_fourier_neg_mul_eq_winModRep m α v x hsumm]

/-- **The rotation identity in the exact form the target uses**: for the twisted, exact-height
fibre `fiberOpP ρ P l₂ m n₀` of `Work.KMTAreas.A7.FiberVarSamplingGRep`,

  `fiberOpP ρ P l₂ m n₀ v x = ∑_{α ∈ (ℚ/ℤ)_{l₂}} e(P(n₀)α)·M_α T_m M_{-α} v x`. -/
theorem fiberOpP_apply_eq_windowRotation (ρ : ℝ) (P : Polynomial ℤ) (l : ℕ) (m : ℝ → ℂ)
    (n₀ : ℤ) (v : ℤ → ℂ) (x : ℤ)
    (hsumm : Summable (fun j : ℤ => Work.KMTAreas.A7.cw m j * v (x - j))) :
    Work.KMTAreas.A7.fiberOpP ρ P l m n₀ v x
      = ∑ α ∈ iwArithFreqsNew ρ l,
          fourier (T := 1) (P.eval n₀) α
            * winModRep α (winConvRep m (winModRep (-α) v)) x := by
  rw [Work.KMTAreas.A7.fiberOpP_eq_fiberOpPSet_iwArithFreqsNew]
  exact fiberOpPSet_apply_eq_windowRotation P (iwArithFreqsNew ρ l) m n₀ v x hsumm

end

/-! ## 7. The modulation is a representation of the circle, and its inverse -/

/-- `fourier n` is additive in the *point*: it is a character of the circle. -/
lemma fourier_add_point_rep (n : ℤ) (α β : Work.Analysis.IonescuWainger.Circle) :
    fourier (T := 1) n (α + β) = fourier (T := 1) n α * fourier (T := 1) n β := by
  rw [fourier_apply, fourier_apply, fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- `M_α` is a representation: `M_α ∘ M_β = M_{α+β}`. -/
lemma winModRep_comp (α β : Work.Analysis.IonescuWainger.Circle) (v : ℤ → ℂ) :
    winModRep α (winModRep β v) = winModRep (α + β) v := by
  funext x
  simp only [winModRep]
  rw [fourier_add_point_rep]
  ring

/-- `M_α ∘ M_{-α} = id`: the window modulation is invertible (it is unitary). -/
lemma winModRep_neg_cancel (α : Work.Analysis.IonescuWainger.Circle) (v : ℤ → ℂ) :
    winModRep α (winModRep (-α) v) = v := by
  rw [winModRep_comp, add_neg_cancel]
  funext x
  simp only [winModRep]
  rw [show fourier (T := 1) (-x) (0 : Work.Analysis.IonescuWainger.Circle) = 1 from by
    simp [fourier_apply]]
  ring

end Work.KMTAreas.A7Rep
