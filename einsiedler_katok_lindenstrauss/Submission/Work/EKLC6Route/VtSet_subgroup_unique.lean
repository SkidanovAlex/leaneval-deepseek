import Mathlib
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLC6Core.contraction_rate_uminus
import Submission.Work.EKLC6Core.mem_uminus_of_entry_form

/-!
# `VtSet t` is a subgroup, and `Uminus t · VtSet t` is a direct product

Let `t : Fin 3 → ℝ` and let

`VtSet t = {g ∈ SL₃(ℝ) | g i j = 0 whenever t i < t j}`

be the "parabolic" part `G⁰G⁺(t)` of the frozen chart data
(`Submission/Work/EKLC6Route/Defs.lean`), and let

`Uminus t = ⨆ {U_ij | t i < t j}`

be the stable horospherical subgroup (`Submission/Work/EKLC6Core/Basic.lean`).

This file proves (statement `VtSet_subgroup_unique`, the group-theoretic half of
`L1 — BIGCELL` of `Submission/Work/EKLComp/C6GEOM_ROUTE_LEAD.md` §3.1):

* `VtSet t` is closed under multiplication and inversion and contains `1`;
* the multiplication map `Uminus t × VtSet t → SL₃(ℝ)` is injective, i.e. the
  factorisation of an element of the "big cell" as `u * k` with `u ∈ Uminus t`,
  `k ∈ VtSet t` is unique.

Both statements are `3 × 3` matrix computations, organised through two structural
facts:

* `Matrix.SpecialLinearGroup.coe_inv` is *by definition* the adjugate, so
  `g⁻¹ ∈ VtSet t` reduces to `adjugate g ∈ VtSet t`, which is the explicit
  `Matrix.adjugate_fin_three` formula: for `t i < t j` the `(i,j)` entry of the
  adjugate is the `2 × 2` minor `A i j * A k k - A i k * A k j` (`k` the third index),
  the first factor is `0`, and of the two remaining factors one vanishes according to
  the position of `t k`;
* an element of `Uminus t` is "unitriangular for the order of `t`": it has `1` on the
  diagonal and `0` at the positions `t i ≥ t j`, `i ≠ j`. The set of such matrices
  (`VtAux.upper t`) is a subgroup of `SL₃(ℝ)` — multiplication is the usual
  `(1+N)(1+M) = 1 + (N + M + NM)` argument for strictly block-triangular `N`, `M`, and
  inversion is again the adjugate computation, with the roles of the two patterns
  exchanged — and it contains every one-parameter root group `U_ij`, `t i < t j`.

Intersecting the two patterns (`t i < t j` gives zeros from `VtSet`, `t j ≤ t i` gives
zeros from `Uminus t ≤ VtAux.upper t`, and the diagonal is `1` in both cases), an
element of `Uminus t ∩ VtSet t` must be `1`; this gives uniqueness of the
factorisation, since `u k = u' k'` gives `u⁻¹ u' = k k'⁻¹`.

All the auxiliary lemmas live in the namespace `Work.EKLC6Route.VtAux`, so that this
file can be imported alongside any other development of the big-cell decomposition.
-/

noncomputable section
namespace Work.EKLC6Route

open Work.EKLContract Work.EKLC6Core

namespace VtAux

/-! ## The "unitriangular for the order of `t`" subgroup -/

/-- The carrier of the subgroup of unitriangular matrices for the order induced by `t`:
the `(i,j)` entry equals `1` when `t i ≥ t j` (so in particular `1` on the diagonal and
`0` off the diagonal at the positions `t i ≥ t j`). -/
def upperCarrier (t : Fin 3 → ℝ) : Set SL3 :=
  {g | ∀ i j : Fin 3, t i ≥ t j → toMat g i j = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j}

/-- Matrices vanishing at the positions `t i ≥ t j` are closed under addition. -/
theorem strictAdd {t : Fin 3 → ℝ} {X Y : Matrix (Fin 3) (Fin 3) ℝ}
    (hX : ∀ i j, t i ≥ t j → X i j = 0) (hY : ∀ i j, t i ≥ t j → Y i j = 0) :
    ∀ i j, t i ≥ t j → (X + Y) i j = 0 := by
  intro i j hij
  rw [Matrix.add_apply, hX i j hij, hY i j hij, add_zero]

/-- Matrices vanishing at the positions `t i ≥ t j` are closed under multiplication
(this is the triangularity of the order induced by `t`). -/
theorem strictMul {t : Fin 3 → ℝ} {X Y : Matrix (Fin 3) (Fin 3) ℝ}
    (hX : ∀ i j, t i ≥ t j → X i j = 0) (hY : ∀ i j, t i ≥ t j → Y i j = 0) :
    ∀ i j, t i ≥ t j → (X * Y) i j = 0 := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases le_or_gt (t k) (t i) with hle | hlt
  · rw [hX i k hle, zero_mul]
  · rw [hY k j (le_of_lt (lt_of_le_of_lt hij hlt)), mul_zero]

/-- `upperCarrier t` is closed under multiplication: subtracting `1` from both factors,
`(1+N)(1+M) - 1 = N + M + NM`, and all three summands vanish at the positions
`t i ≥ t j`. -/
theorem upperCarrier.mul {t : Fin 3 → ℝ} {g h : SL3}
    (hg : g ∈ upperCarrier t) (hh : h ∈ upperCarrier t) : g * h ∈ upperCarrier t := by
  have hg' : ∀ i j, t i ≥ t j → (toMat g - 1) i j = 0 := by
    intro i j hij
    rw [Matrix.sub_apply, hg i j hij, sub_self]
  have hh' : ∀ i j, t i ≥ t j → (toMat h - 1) i j = 0 := by
    intro i j hij
    rw [Matrix.sub_apply, hh i j hij, sub_self]
  have key : toMat (g * h) =
      1 + ((toMat g - 1) + (toMat h - 1) + (toMat g - 1) * (toMat h - 1)) := by
    rw [toMat_mul]
    noncomm_ring
  intro i j hij
  rw [key, Matrix.add_apply,
    strictAdd (strictAdd hg' hh') (strictMul hg' hh') i j hij, add_zero]

/-- The adjugate of a matrix in the `upperCarrier t` pattern is again in that pattern:
the `(i,j)` entry of the adjugate is a `2 × 2` minor whose determinant vanishes because
of the position of the third index. -/
theorem adjugate_one_of_pattern {t : Fin 3 → ℝ} {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ∀ i j, t i ≥ t j → A i j = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) :
    ∀ i j, t i ≥ t j → A.adjugate i j = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := by
  intro i j hij
  rw [Matrix.adjugate_fin_three]
  fin_cases i <;> fin_cases j <;> simp_all
  · rcases lt_or_ge (t 1) (t 2) with h | h
    · right; exact hA 2 1 (le_of_lt h)
    · left; exact hA 1 2 h
  · rcases lt_or_ge (t 0) (t 2) with h | h
    · right; exact hA 2 1 (le_of_lt (lt_of_le_of_lt hij h))
    · left; exact hA 0 2 h
  · rcases lt_or_ge (t 0) (t 1) with h | h
    · right; exact hA 1 2 (le_of_lt (lt_of_le_of_lt hij h))
    · left; exact hA 0 1 h
  · rcases lt_or_ge (t 1) (t 2) with h | h
    · right; exact hA 2 0 (le_of_lt (lt_of_le_of_lt hij h))
    · left; exact hA 1 2 h
  · rcases lt_or_ge (t 0) (t 2) with h | h
    · right; exact hA 2 0 (le_of_lt h)
    · left; exact hA 0 2 h
  · rcases lt_or_ge (t 1) (t 0) with h | h
    · left; exact hA 0 2 (le_of_lt (lt_of_le_of_lt hij h))
    · right; exact hA 1 0 h
  · rcases lt_or_ge (t 2) (t 1) with h | h
    · left; exact hA 1 0 (le_of_lt (lt_of_le_of_lt hij h))
    · right; exact hA 2 1 h
  · rcases lt_or_ge (t 2) (t 0) with h | h
    · left; exact hA 0 1 (le_of_lt (lt_of_le_of_lt hij h))
    · right; exact hA 2 0 h
  · rcases lt_or_ge (t 0) (t 1) with h | h
    · right; exact hA 1 0 (le_of_lt h)
    · left; exact hA 0 1 h

theorem upperCarrier.one (t : Fin 3 → ℝ) : (1 : SL3) ∈ upperCarrier t := by
  intro i j _
  rw [toMat_one]

/-- `upperCarrier t` is closed under inversion (via `coe_inv`, which is the adjugate). -/
theorem upperCarrier.inv {t : Fin 3 → ℝ} {g : SL3} (hg : g ∈ upperCarrier t) :
    g⁻¹ ∈ upperCarrier t := by
  intro i j hij
  exact adjugate_one_of_pattern hg i j hij

/-- The group of unitriangular matrices for the order induced by `t`. -/
def upper (t : Fin 3 → ℝ) : Subgroup SL3 where
  carrier := upperCarrier t
  mul_mem' := upperCarrier.mul
  one_mem' := upperCarrier.one t
  inv_mem' := upperCarrier.inv

/-- Every transvection `u_ij(s)` with `t i < t j` is unitriangular for the order of `t`. -/
theorem uij_mem_upper {t : Fin 3 → ℝ} {i j : Fin 3} (hij : i ≠ j) (hlt : t i < t j)
    (s : ℝ) : uij hij s ∈ upper t := by
  intro m n hmn
  have hc : ¬ (i = m ∧ j = n) := by
    rintro ⟨h1, h2⟩
    rw [← h1, ← h2] at hmn
    exact (not_lt_of_ge hmn) hlt
  rw [Work.EKLContract.Lemmas.horoUij_toMat hij s, Matrix.add_apply, Matrix.single_apply,
    if_neg hc, add_zero]

/-- The stable horospherical subgroup `Uminus t` consists of unitriangular matrices for
the order of `t`. -/
theorem Uminus_le_upper (t : Fin 3 → ℝ) : Uminus t ≤ upper t := by
  rw [Uminus]
  refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hlt => ?_
  intro g hg
  obtain ⟨s, hs⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff hij g).mp hg
  rw [← hs]
  exact uij_mem_upper hij hlt s

/-! ## `VtSet t` is a subgroup -/

/-- `VtSet t` is closed under multiplication: in the `(i,j)` entry with `t i < t j` of a
product, every term `g i k * h k j` vanishes, either because `g` vanishes at `(i,k)`
(when `t k ≤ t i`) or because `h` vanishes at `(k,j)` (when `t i < t k`). -/
theorem VtSet_mul {t : Fin 3 → ℝ} {g h : SL3} (hg : g ∈ VtSet t) (hh : h ∈ VtSet t) :
    g * h ∈ VtSet t := by
  have hg' : ∀ i j, t i < t j → toMat g i j = 0 := fun i j hij => hg i j hij
  have hh' : ∀ i j, t i < t j → toMat h i j = 0 := fun i j hij => hh i j hij
  intro i j hij
  change toMat (g * h) i j = 0
  rw [toMat_mul, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge (t k) (t j) with hlt | hge
  · rw [hh' k j hlt, mul_zero]
  · rw [hg' i k (lt_of_lt_of_le hij hge), zero_mul]

/-- The adjugate of a matrix vanishing at the positions `t i < t j` also vanishes there:
for `t i < t j` the `(i,j)` entry of the adjugate is the `2 × 2` minor
`A i j * A k k - A i k * A k j` (`k` the third index), `A i j = 0`, and of the two
remaining factors one vanishes according to the position of `t k`. -/
theorem adjugate_zero_of_pattern {t : Fin 3 → ℝ} {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ∀ i j, t i < t j → A i j = 0) : ∀ i j, t i < t j → A.adjugate i j = 0 := by
  intro i j hij
  rw [Matrix.adjugate_fin_three]
  fin_cases i <;> fin_cases j <;> simp_all
  · rcases lt_or_ge (t 0) (t 2) with h | h
    · left; exact hA 0 2 h
    · right; exact hA 2 1 (lt_of_le_of_lt h hij)
  · rcases lt_or_ge (t 0) (t 1) with h | h
    · left; exact hA 0 1 h
    · right; exact hA 1 2 (lt_of_le_of_lt h hij)
  · rcases lt_or_ge (t 1) (t 2) with h | h
    · left; exact hA 1 2 h
    · right; exact hA 2 0 (lt_of_le_of_lt h hij)
  · rcases lt_or_ge (t 1) (t 0) with h | h
    · right; exact hA 1 0 h
    · left; exact hA 0 2 (lt_of_le_of_lt h hij)
  · rcases lt_or_ge (t 2) (t 1) with h | h
    · right; exact hA 2 1 h
    · left; exact hA 1 0 (lt_of_le_of_lt h hij)
  · rcases lt_or_ge (t 2) (t 0) with h | h
    · right; exact hA 2 0 h
    · left; exact hA 0 1 (lt_of_le_of_lt h hij)

/-- `VtSet t` is closed under inversion: `coe_inv` identifies the inverse matrix with the
adjugate, and `adjugate_zero_of_pattern` applies. -/
theorem VtSet_inv {t : Fin 3 → ℝ} {g : SL3} (hg : g ∈ VtSet t) : g⁻¹ ∈ VtSet t := by
  have hg' : ∀ i j, t i < t j → toMat g i j = 0 := fun i j hij => hg i j hij
  intro i j hij
  change toMat (g⁻¹) i j = 0
  exact adjugate_zero_of_pattern hg' i j hij

/-- `1 ∈ VtSet t` (`VtSet t` is the parabolic part of a flag). -/
theorem VtSet_one (t : Fin 3 → ℝ) : (1 : SL3) ∈ VtSet t := by
  intro i j hij
  change toMat (1 : SL3) i j = 0
  have hne : i ≠ j := fun h => by rw [h] at hij; exact lt_irrefl _ hij
  rw [toMat_one, Matrix.one_apply, if_neg hne]

/-! ## The factorisation `Uminus t · VtSet t` is unique -/

/-- `Uminus t ∩ VtSet t = {1}`: an element of `Uminus t` is unitriangular for the order
of `t`, so it has `1` on the diagonal and `0` off the diagonal at the positions
`t i ≥ t j`; an element of `VtSet t` has `0` at the positions `t i < t j`. Together the
`(i,j)` entry with `i ≠ j` is `0` in both cases. -/
theorem eq_one_of_mem_Uminus_and_VtSet (t : Fin 3 → ℝ) {u : SL3}
    (hu : u ∈ Uminus t) (hk : u ∈ VtSet t) : u = 1 := by
  have hk' : ∀ i j, t i < t j → toMat u i j = 0 := fun i j hij => hk i j hij
  have hupper : u ∈ upper t := Uminus_le_upper t hu
  refine ext_toMat ?_
  rw [toMat_one]
  ext i j
  by_cases hij : i = j
  · rw [hij, hupper j j le_rfl, Matrix.one_apply_eq]
  · rcases lt_or_ge (t i) (t j) with h | h
    · rw [hk' i j h, Matrix.one_apply_ne hij]
    · rw [hupper i j h, Matrix.one_apply_ne hij]

end VtAux

/-- **`VtSet t` is a subgroup of `SL₃(ℝ)` and `Uminus t · VtSet t` is a direct product**
(the group-theoretic part of `L1 — BIGCELL`, `C6GEOM_ROUTE_LEAD.md` §3.1). -/
theorem VtSet_subgroup_unique (t : Fin 3 → ℝ) :
    (∀ g h : Work.EKLContract.SL3, g ∈ Work.EKLC6Route.VtSet t → h ∈ Work.EKLC6Route.VtSet t →
        g * h ∈ Work.EKLC6Route.VtSet t) ∧
    (∀ g : Work.EKLContract.SL3, g ∈ Work.EKLC6Route.VtSet t → g⁻¹ ∈ Work.EKLC6Route.VtSet t) ∧
    (1 : Work.EKLContract.SL3) ∈ Work.EKLC6Route.VtSet t ∧
    (∀ u u' k k' : Work.EKLContract.SL3, u ∈ Work.EKLC6Core.Uminus t → u' ∈ Work.EKLC6Core.Uminus t →
      k ∈ Work.EKLC6Route.VtSet t → k' ∈ Work.EKLC6Route.VtSet t →
      u * k = u' * k' → u = u' ∧ k = k') := by
  refine ⟨fun g h hg hh => VtAux.VtSet_mul hg hh, fun g hg => VtAux.VtSet_inv hg,
    VtAux.VtSet_one t, ?_⟩
  intro u u' k k' hu hu' hk hk' h
  -- `u⁻¹ * u' = k * k'⁻¹` lies in `Uminus t ∩ VtSet t`, hence is `1`
  have h2 : u⁻¹ * u' * k' = k := by
    calc u⁻¹ * u' * k' = u⁻¹ * (u' * k') := by group
      _ = u⁻¹ * (u * k) := by rw [h]
      _ = k := by group
  have hm : u⁻¹ * u' = k * k'⁻¹ := by
    rw [← h2]
    group
  have hmU : u⁻¹ * u' ∈ Uminus t := (Uminus t).mul_mem ((Uminus t).inv_mem hu) hu'
  have hmV : k * k'⁻¹ ∈ VtSet t := VtAux.VtSet_mul hk (VtAux.VtSet_inv hk')
  have h1 : u⁻¹ * u' = 1 :=
    VtAux.eq_one_of_mem_Uminus_and_VtSet t hmU (by rw [hm]; exact hmV)
  have h1' : k * k'⁻¹ = 1 := by rw [← hm]; exact h1
  exact ⟨inv_mul_eq_one.mp h1, mul_inv_eq_one.mp h1'⟩

end Work.EKLC6Route
