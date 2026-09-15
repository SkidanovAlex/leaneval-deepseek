import Mathlib
import Submission.Commons.Combinatorics.Additive.Gowers.gvn_general
import Submission.Commons.Combinatorics.Additive.AP.sum_weighted_coordinates
import Submission.Commons.Combinatorics.Additive.AP.sum_of_coordinates
import Submission.Commons.Combinatorics.Additive.AP.sum_of_coords
import Submission.Commons.Combinatorics.Additive.AP.sum_phiZ_cover

open scoped BigOperators

/-!
# The weighted generalised von Neumann theorem over `ZMod p`

This file proves `Commons.Combinatorics.Additive.Gowers.gvn_weighted`, the weighted
(relative) generalised von Neumann inequality of Green--Tao (2008, section 5): for a prime `p`,
`3 <= k <= p`, functions `f i : ZMod p -> R` dominated by a strictly positive weight `nu`, the
`k`-term arithmetic-progression sum of `f` is controlled by the `(k-1)`-dimensional weighted
cube sum of `f 0` and the `nu`-cube averages `Pm i`.

The proof is the iterated weighted Cauchy--Schwarz argument of Green--Tao, carried out for an
abstract finite stage `X` (so that it is reusable) and then specialised to `X = ZMod p` with
the Green--Tao reparametrisation `phi i y = sum y - i * sum y/(j+1)`.
-/

namespace GVNW

open GVNgen

open Commons.Combinatorics.Additive.AP (sum_phiZ_cover sum_of_coords)

/-! ## Splitting products over `Fin n` -/

/-- Splitting a product over `Fin n` at the first index (for `n ≥ 1`). -/
lemma prod_fin_zero {M : Type*} [CommMonoid M] {n : ℕ} (hn : 1 ≤ n) (g : Fin n → M) :
    (∏ j : Fin n, g j) = g ⟨0, hn⟩ * ∏ j : Fin (n-1), g ⟨j.val+1, by omega⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Fin.prod_univ_succ]
  congr 1

/-- Splitting a product over `Fin n` at the last index (for `n ≥ 1`). -/
lemma prod_fin_last {M : Type*} [CommMonoid M] {n : ℕ} (hn : 1 ≤ n) (g : Fin n → M) :
    (∏ j : Fin n, g j) = (∏ j : Fin (n-1), g ⟨j.val, by omega⟩) * g ⟨n-1, by omega⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Fin.prod_univ_castSucc]
  congr 1


/-! ## The `Bool`-cube `cons` reindexing -/

@[simp] lemma boolKEquiv_apply {k m : ℕ} (hm : m + 2 ≤ k)
    (p : Bool × (Fin (k-1-(m+1)) → Bool)) :
    boolKEquiv k m hm p = boolK hm p.1 p.2 := rfl

/-! ## Elementary `ZMod p` reindexings -/

section ZModHelpers

variable {p : ℕ} [Fact p.Prime]

/-- The translation step in a cube average: replacing `y'` by `h + v`. -/
lemma cube_shift {n : ℕ} (F : (Fin n → ZMod p) → ℝ) (v : Fin n → ZMod p) :
    (∑ y' : Fin n → ZMod p, F y')
      = ∑ h : Fin n → ZMod p, F (h + v) := by
  exact (Equiv.sum_comp (Equiv.addRight (G := Fin n → ZMod p) v) F).symm

/-- The single-factor reduction of the `Fin 1` product appearing at stage `0`. -/
lemma prod_fin_one_phiZ {k : ℕ} (hk : 1 ≤ k) (f : Fin k → ZMod p → ℝ)
    (u : Fin (k-1) → ZMod p) :
    (∏ i : Fin 1, f ⟨i.val, by omega⟩ (phiZ (p:=p) k ⟨i.val, by omega⟩ u))
      = f (⟨0, by omega⟩ : Fin k) (∑ j, u j) := by
  rw [Fintype.prod_unique]
  have h0 : ((default : Fin 1) : ℕ) = 0 := rfl
  have hidx : (⟨(default : Fin 1).val, by omega⟩ : Fin k) = (⟨0, by omega⟩ : Fin k) := Fin.ext h0
  rw [hidx]
  congr 1
  simp only [phiZ_apply, Fin.val_zero, Nat.cast_zero, zero_mul, sub_zero]

/-- The cardinality of `Fin n → ZMod p`. -/
lemma card_fun_zmod (n : ℕ) : (Fintype.card (Fin n → ZMod p) : ℝ) = (p : ℝ)^n := by
  rw [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow]


end ZModHelpers

/-! ## The weighted Green--Tao recursion for an abstract finite stage -/

section Weighted

variable {X : Type*} [Fintype X] [Nonempty X]

/-- The weighted stage-`m` integrand of Green–Tao §5: over the `(k-1-m)`-dimensional cube,
the functions `f_0,…,f_m` at full strength and the remaining indices as `√ν`. -/
noncomputable def Twn (X : Type*) [Fintype X] (k : ℕ)
    (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ) (ν : X → ℝ)
    (m : ℕ) (hm : m + 1 ≤ k) (u : Fin m → X) (v y' : Fin (k-1-m) → X) : ℝ :=
  ∏ ω : Fin (k-1-m) → Bool,
    (∏ i : Fin (m+1), f ⟨i.val, by omega⟩ (φ ⟨i.val, by omega⟩
        (app k m hm u (fun j => if ω j then y' j else v j))))
    * ∏ i : Fin (k-1-m), Real.sqrt (ν (φ ⟨m+1+i.val, by omega⟩
        (app k m hm u (fun j => if ω j then y' j else v j))))

/-- The weighted stage-`m` average. -/
noncomputable def Jw (X : Type*) [Fintype X] (k : ℕ)
    (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ) (ν : X → ℝ)
    (m : ℕ) (hm : m + 1 ≤ k) : ℝ :=
  av (fun u : Fin m → X => av (fun v : Fin (k-1-m) → X =>
    av (fun y' : Fin (k-1-m) → X => Twn X k φ f ν m hm u v y')))

/-- The "half" weight at the transition `m+1 → m`: over the `(k-2-m)`-dimensional cube, the
functions `f_0,…,f_m` at full strength and `√ν` on the indices `m+1,…,k-1`.  Its two copies
(for the two values of the peeled coordinate) multiply to the stage-`m` integrand. -/
noncomputable def Htw (X : Type*) [Fintype X] (k : ℕ)
    (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ) (ν : X → ℝ)
    (m : ℕ) (hm : m + 2 ≤ k) (u : Fin m → X) (z : X) (v y' : Fin (k-1-(m+1)) → X) : ℝ :=
  ∏ ω : Fin (k-1-(m+1)) → Bool,
    (∏ i : Fin (m+1), f ⟨i.val, by omega⟩ (φ ⟨i.val, by omega⟩
        (app k (m+1) (by omega) (Fin.snoc u z) (fun j => if ω j then y' j else v j))))
    * ∏ j : Fin (k-1-m), Real.sqrt (ν (φ ⟨m+1+j.val, by omega⟩
        (app k (m+1) (by omega) (Fin.snoc u z) (fun j => if ω j then y' j else v j))))

/-- The product of `f_{m+1}` over the stage-`(m+1)` cube. -/
noncomputable def GGw (X : Type*) [Fintype X] (k : ℕ)
    (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ)
    (m : ℕ) (hm : m + 2 ≤ k) (u : Fin (m+1) → X) (v y' : Fin (k-1-(m+1)) → X) : ℝ :=
  ∏ ω : Fin (k-1-(m+1)) → Bool, f ⟨m+1, by omega⟩ (φ ⟨m+1, by omega⟩
    (app k (m+1) (by omega) u (fun j => if ω j then y' j else v j)))

/-- The product of `√ν(φ_{m+1})` over the stage-`(m+1)` cube. -/
noncomputable def Ww (X : Type*) [Fintype X] (k : ℕ)
    (φ : Fin k → (Fin (k-1) → X) → X) (ν : X → ℝ)
    (m : ℕ) (hm : m + 2 ≤ k) (u : Fin (m+1) → X) (v y' : Fin (k-1-(m+1)) → X) : ℝ :=
  ∏ ω : Fin (k-1-(m+1)) → Bool, Real.sqrt (ν (φ ⟨m+1, by omega⟩
    (app k (m+1) (by omega) u (fun j => if ω j then y' j else v j))))

/-- `GGw` does not depend on the peeled coordinate. -/
lemma GGw_congr {k : ℕ} (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ)
    (hφ : ∀ (m : ℕ) (hm : m + 2 ≤ k) (u : Fin m → X) (z z' : X)
        (w : Fin (k-1-(m+1)) → X),
      φ ⟨m+1, by omega⟩ (app k (m+1) (by omega) (Fin.snoc u z) w)
        = φ ⟨m+1, by omega⟩ (app k (m+1) (by omega) (Fin.snoc u z') w))
    (m : ℕ) (hm : m + 2 ≤ k) (u : Fin m → X) (z z' : X)
    (v y' : Fin (k-1-(m+1)) → X) :
    GGw X k φ f m hm (Fin.snoc u z) v y' = GGw X k φ f m hm (Fin.snoc u z') v y' := by
  rw [GGw, GGw]
  apply Finset.prod_congr rfl
  intro ω _
  rw [hφ m hm u z z' (fun j => if ω j then y' j else v j)]

/-- `Ww` does not depend on the peeled coordinate. -/
lemma Ww_congr {k : ℕ} (φ : Fin k → (Fin (k-1) → X) → X) (ν : X → ℝ)
    (hφ : ∀ (m : ℕ) (hm : m + 2 ≤ k) (u : Fin m → X) (z z' : X)
        (w : Fin (k-1-(m+1)) → X),
      φ ⟨m+1, by omega⟩ (app k (m+1) (by omega) (Fin.snoc u z) w)
        = φ ⟨m+1, by omega⟩ (app k (m+1) (by omega) (Fin.snoc u z') w))
    (m : ℕ) (hm : m + 2 ≤ k) (u : Fin m → X) (z z' : X)
    (v y' : Fin (k-1-(m+1)) → X) :
    Ww X k φ ν m hm (Fin.snoc u z) v y' = Ww X k φ ν m hm (Fin.snoc u z') v y' := by
  rw [Ww, Ww]
  apply Finset.prod_congr rfl
  intro ω _
  rw [hφ m hm u z z' (fun j => if ω j then y' j else v j)]

/-- The square expansion of the weighted integrand: the two copies of the peeled coordinate
multiply to the stage-`m` integrand. -/
lemma Twn_expand {k : ℕ} (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ) (ν : X → ℝ)
    (m : ℕ) (hm : m + 2 ≤ k) (u : Fin m → X) (z z' : X)
    (v y' : Fin (k-1-(m+1)) → X) :
    Twn X k φ f ν m (by omega) u (consK hm z v) (consK hm z' y')
      = Htw X k φ f ν m hm u z v y' * Htw X k φ f ν m hm u z' v y' := by
  rw [Twn, Htw, Htw]
  rw [← Fintype.prod_equiv (boolKEquiv k m hm)
      (fun p : Bool × (Fin (k-1-(m+1)) → Bool) =>
        (∏ i : Fin (m+1), f ⟨i.val, by omega⟩ (φ ⟨i.val, by omega⟩
            (app k (m+1) (by omega) (Fin.snoc u (if p.1 then z' else z))
              (fun j => if p.2 j then y' j else v j))))
        * (∏ j : Fin (k-1-m), Real.sqrt (ν (φ ⟨m+1+j.val, by omega⟩
            (app k (m+1) (by omega) (Fin.snoc u (if p.1 then z' else z))
              (fun j => if p.2 j then y' j else v j))))))
      (fun ω'' : Fin (k-1-m) → Bool =>
        (∏ i : Fin (m+1), f ⟨i.val, by omega⟩ (φ ⟨i.val, by omega⟩
            (app k m (by omega) u (fun j => if ω'' j then (consK hm z' y') j else (consK hm z v) j))))
        * (∏ j : Fin (k-1-m), Real.sqrt (ν (φ ⟨m+1+j.val, by omega⟩
            (app k m (by omega) u (fun j => if ω'' j then (consK hm z' y') j else (consK hm z v) j))))))
      (fun p => by
        simp only [boolKEquiv_apply]
        rw [app_cons_fun (k := k) (m := m) hm u z z' v y' p.1 p.2]
        rfl)]
  rw [Fintype.prod_prod_type, Fintype.prod_bool]
  simp only [reduceIte, Bool.false_eq_true, eq_self_iff_true, if_true, if_false]
  rw [mul_comm]

/-
  TODO (next session): the two remaining lemmas of the weighted recursion.

  `Twn_split`:  `Twn(m+1)(Fin.snoc u z, v, y')`
                `= GGw(Fin.snoc u z,v,y') * (Ww(Fin.snoc u z,v,y'))⁻¹ * Htw(u,z,v,y')`
  is the weighted analogue of `Tfin_split`; it follows from `prod_fin_last` (on the `Fin (m+2)`
  product of the `f_i`) together with `prod_fin_zero` (splitting the `√ν` product over
  `Fin (k-1-m)` at the index `0`), and the pointwise identity `wsplit` below.

  CAUTION with the index arithmetic: `(k-1-m) - 1` and `k - 1 - (m+1)` are definitionally
  equal, but `m + 1 + (j.val + 1)` and `m + 2 + j.val` are NOT definitionally equal as values of
  `Fin`; it is easiest to keep every `√ν` index written as `m + 1 + i.val` (with `i : Fin (k-1-m)`)
  and to state the splitting lemma with the tail product expressed through a separate function
  `S'` (see `wsplit` below), proving the compatibility `∀ j, S' j = S ⟨j.val+1, _⟩` with
  `Fin.ext (by ...)`.

  `wsplit` (proved in the next session, then used inside `Twn_split`):
-/
private lemma wsplit {m k : ℕ} (hm : m + 2 ≤ k) (F1 : Fin (m+1) → ℝ) (F2 : ℝ)
    (S : Fin (k-1-m) → ℝ) (S' : Fin ((k-1-m)-1) → ℝ)
    (hS : S ⟨0, by omega⟩ ≠ 0)
    (hS' : ∀ j : Fin ((k-1-m)-1), S' j = S ⟨j.val + 1, by omega⟩) :
    (∏ i : Fin (m+1), F1 i) * F2 * (∏ j, S' j)
      = ((∏ i : Fin (m+1), F1 i) * (∏ j : Fin (k-1-m), S j))
          * (F2 * (S ⟨0, by omega⟩)⁻¹) := by
  have hcongr : (∏ j : Fin ((k-1-m)-1), S' j)
      = ∏ j : Fin ((k-1-m)-1), S ⟨j.val + 1, by omega⟩ :=
    Finset.prod_congr rfl (fun j _ => hS' j)
  rw [hcongr, prod_fin_zero (n := k-1-m) (by omega) S]
  field_simp

/-- Splitting the weighted stage-`(m+1)` integrand into the peeled factor, the inverse `√ν`
weight and the half-weight `Htw`. -/
lemma Twn_split {k : ℕ} (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ) (ν : X → ℝ)
    (hνpos : ∀ x, 0 < ν x)
    (m : ℕ) (hm : m + 2 ≤ k) (u : Fin m → X) (z : X) (v y' : Fin (k-1-(m+1)) → X) :
    Twn X k φ f ν (m+1) (by omega) (Fin.snoc u z) v y'
      = GGw X k φ f m hm (Fin.snoc u z) v y'
        * (Ww X k φ ν m hm (Fin.snoc u z) v y')⁻¹
        * Htw X k φ f ν m hm u z v y' := by
  rw [Twn, GGw, Ww, Htw]
  rw [show (∏ ω : Fin (k-1-(m+1)) → Bool,
        (∏ i : Fin (m+2), f ⟨i.val, by omega⟩ (φ ⟨i.val, by omega⟩
            (app k (m+1) (by omega) (Fin.snoc u z) (fun j => if ω j then y' j else v j))))
        * (∏ j : Fin (k-1-(m+1)), Real.sqrt (ν (φ ⟨m+2+j.val, by omega⟩
            (app k (m+1) (by omega) (Fin.snoc u z) (fun j => if ω j then y' j else v j))))))
      = ∏ ω : Fin (k-1-(m+1)) → Bool,
        ((∏ i : Fin (m+1), f ⟨i.val, by omega⟩ (φ ⟨i.val, by omega⟩
            (app k (m+1) (by omega) (Fin.snoc u z) (fun j => if ω j then y' j else v j))))
        * (∏ j : Fin (k-1-m), Real.sqrt (ν (φ ⟨m+1+j.val, by omega⟩
            (app k (m+1) (by omega) (Fin.snoc u z) (fun j => if ω j then y' j else v j)))))
        * (f ⟨m+1, by omega⟩ (φ ⟨m+1, by omega⟩
              (app k (m+1) (by omega) (Fin.snoc u z) (fun j => if ω j then y' j else v j)))
            * (Real.sqrt (ν (φ ⟨m+1, by omega⟩
              (app k (m+1) (by omega) (Fin.snoc u z) (fun j => if ω j then y' j else v j)))))⁻¹))
      from by
    apply Finset.prod_congr rfl
    intro ω _
    rw [prod_fin_last (n := m+2) (by omega)
      (fun i => f ⟨i.val, by omega⟩ (φ ⟨i.val, by omega⟩
        (app k (m+1) (by omega) (Fin.snoc u z) (fun j => if ω j then y' j else v j))))]
    refine wsplit hm
      (fun i => f ⟨i.val, by omega⟩ (φ ⟨i.val, by omega⟩
        (app k (m+1) (by omega) (Fin.snoc u z) (fun j => if ω j then y' j else v j))))
      (f ⟨m+1, by omega⟩ (φ ⟨m+1, by omega⟩
        (app k (m+1) (by omega) (Fin.snoc u z) (fun j => if ω j then y' j else v j))))
      (fun j : Fin (k-1-m) => Real.sqrt (ν (φ ⟨m+1+j.val, by omega⟩
        (app k (m+1) (by omega) (Fin.snoc u z) (fun j => if ω j then y' j else v j)))))
      (fun j : Fin ((k-1-m)-1) => Real.sqrt (ν (φ ⟨m+2+j.val, by omega⟩
        (app k (m+1) (by omega) (Fin.snoc u z) (fun j => if ω j then y' j else v j)))))
      (Real.sqrt_ne_zero'.mpr (hνpos _)) (fun j => by
        congr 1
        congr 1
        congr 1
        apply Fin.ext
        simp only [Fin.val_mk]
        omega)]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib]
  ring

end Weighted

section WeightedRecursion

variable {X : Type*} [Fintype X] [Nonempty X]

/-- The `z`-independent peeled factor of the weighted recursion. -/
noncomputable def Ghat (X : Type*) [Fintype X] (k : ℕ)
    (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ) (ν : X → ℝ)
    (m : ℕ) (hm : m + 2 ≤ k) (z0 : X) (u : Fin m → X) (v y' : Fin (k-1-(m+1)) → X) : ℝ :=
  GGw X k φ f m hm (Fin.snoc u z0) v y' * (Ww X k φ ν m hm (Fin.snoc u z0) v y')⁻¹

/-- `Ghat` is independent of the reference point. -/
lemma Ghat_congr {k : ℕ} (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ) (ν : X → ℝ)
    (hφ : ∀ (m : ℕ) (hm : m + 2 ≤ k) (u : Fin m → X) (z z' : X)
        (w : Fin (k-1-(m+1)) → X),
      φ ⟨m+1, by omega⟩ (app k (m+1) (by omega) (Fin.snoc u z) w)
        = φ ⟨m+1, by omega⟩ (app k (m+1) (by omega) (Fin.snoc u z') w))
    (m : ℕ) (hm : m + 2 ≤ k) (z z' : X) (u : Fin m → X) (v y' : Fin (k-1-(m+1)) → X) :
    Ghat X k φ f ν m hm z u v y' = Ghat X k φ f ν m hm z' u v y' := by
  rw [Ghat, Ghat, GGw_congr φ f hφ m hm u z z' v y', Ww_congr φ ν hφ m hm u z z' v y']

/-- The weighted stage-`(m+1)` integrand as a product of `Ghat` and `Htw`. -/
lemma Twn_split' {k : ℕ} (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ) (ν : X → ℝ)
    (hφ : ∀ (m : ℕ) (hm : m + 2 ≤ k) (u : Fin m → X) (z z' : X)
        (w : Fin (k-1-(m+1)) → X),
      φ ⟨m+1, by omega⟩ (app k (m+1) (by omega) (Fin.snoc u z) w)
        = φ ⟨m+1, by omega⟩ (app k (m+1) (by omega) (Fin.snoc u z') w))
    (hνpos : ∀ x, 0 < ν x)
    (m : ℕ) (hm : m + 2 ≤ k) (u : Fin m → X) (z z0 : X) (v y' : Fin (k-1-(m+1)) → X) :
    Twn X k φ f ν (m+1) (by omega) (Fin.snoc u z) v y'
      = Ghat X k φ f ν m hm z0 u v y' * Htw X k φ f ν m hm u z v y' := by
  rw [Twn_split φ f ν hνpos m hm u z v y']
  rw [show GGw X k φ f m hm (Fin.snoc u z) v y' * (Ww X k φ ν m hm (Fin.snoc u z) v y')⁻¹
      = Ghat X k φ f ν m hm z0 u v y' from by
    rw [Ghat, GGw_congr φ f hφ m hm u z z0 v y', Ww_congr φ ν hφ m hm u z z0 v y']]

/-- Splitting a product indexed by `X × U × W` into the `U`- and `(X × W)`-averages. -/
private def splitEquiv (U W : Type*) : (X × U) × W ≃ U × (X × W) where
  toFun q := (q.1.2, (q.1.1, q.2))
  invFun q := ((q.2.1, q.1), q.2.2)
  left_inv q := by obtain ⟨⟨a, b⟩, c⟩ := q; rfl
  right_inv q := by obtain ⟨a, ⟨b, c⟩⟩ := q; rfl


/-- The pointwise bound behind the weighted recursion: the square of the peeled factor is
dominated by the product of the `ν`-weights over the cube. -/
lemma Ghat_sq_le {k : ℕ} (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ) (ν : X → ℝ)
    (hf : ∀ i x, |f i x| ≤ ν x) (hνpos : ∀ x, 0 < ν x)
    (m : ℕ) (hm : m + 2 ≤ k) (z0 : X) (u : Fin m → X) (v y' : Fin (k-1-(m+1)) → X) :
    (Ghat X k φ f ν m hm z0 u v y')^2
      ≤ ∏ ω : Fin (k-1-(m+1)) → Bool, ν (φ ⟨m+1, by omega⟩
          (app k (m+1) (by omega) (Fin.snoc u z0) (fun j => if ω j then y' j else v j))) := by
  have hpt : ∀ ω : Fin (k-1-(m+1)) → Bool,
      f ⟨m+1, by omega⟩ (φ ⟨m+1, by omega⟩
          (app k (m+1) (by omega) (Fin.snoc u z0) (fun j => if ω j then y' j else v j))) ^ 2
        * (ν (φ ⟨m+1, by omega⟩
          (app k (m+1) (by omega) (Fin.snoc u z0) (fun j => if ω j then y' j else v j))))⁻¹
      ≤ ν (φ ⟨m+1, by omega⟩
          (app k (m+1) (by omega) (Fin.snoc u z0) (fun j => if ω j then y' j else v j))) := by
    intro ω
    set x : X := φ ⟨m+1, by omega⟩
      (app k (m+1) (by omega) (Fin.snoc u z0) (fun j => if ω j then y' j else v j)) with hx
    have h1 : f ⟨m+1, by omega⟩ x ^ 2 ≤ ν x ^ 2 := by
      have := abs_le.mp (hf ⟨m+1, by omega⟩ x)
      nlinarith [this.1, this.2]
    calc f ⟨m+1, by omega⟩ x ^ 2 * (ν x)⁻¹
        ≤ ν x ^ 2 * (ν x)⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr (le_of_lt (hνpos x)))
      _ = ν x := by field_simp
  rw [Ghat, mul_pow, GGw, Ww, inv_pow]
  rw [show ((∏ x : Fin (k-1-(m+1)) → Bool, Real.sqrt (ν (φ ⟨m+1, by omega⟩
        (app k (m+1) (by omega) (Fin.snoc u z0) (fun j => if x j then y' j else v j))))) ^ 2)
      = ∏ x : Fin (k-1-(m+1)) → Bool, ν (φ ⟨m+1, by omega⟩
        (app k (m+1) (by omega) (Fin.snoc u z0) (fun j => if x j then y' j else v j))) from by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro x _
    exact Real.sq_sqrt (le_of_lt (hνpos _))]
  rw [← Finset.prod_pow, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro ω _
    exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (le_of_lt (hνpos _)))
  · intro ω _
    exact hpt ω





/-- Reindexing `(Fin (m+1) → X) × (V × V)` as `(Fin m → X) × (X × (V × V))`. -/
private def reindexEquiv (k m : ℕ) (hm : m + 2 ≤ k) :
    ((Fin (m+1) → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X))) ≃
      ((Fin m → X) × (X × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)))) where
  toFun s := (((snocEquiv m X).symm s.1).2, (((snocEquiv m X).symm s.1).1, s.2))
  invFun t := (snocEquiv m X (t.2.1, t.1), t.2.2)
  left_inv s := by
    obtain ⟨u, q⟩ := s
    simp [snocEquiv]
  right_inv t := by
    obtain ⟨u', zq⟩ := t
    simp [snocEquiv]


/-- The weighted stage-`(m+1)` average, reindexed as an average over
`u × (z × (v, y'))`. -/
lemma Jw_reindex {k : ℕ} (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ) (ν : X → ℝ)
    (hφ : ∀ (m : ℕ) (hm : m + 2 ≤ k) (u : Fin m → X) (z z' : X)
        (w : Fin (k-1-(m+1)) → X),
      φ ⟨m+1, by omega⟩ (app k (m+1) (by omega) (Fin.snoc u z) w)
        = φ ⟨m+1, by omega⟩ (app k (m+1) (by omega) (Fin.snoc u z') w))
    (hνpos : ∀ x, 0 < ν x) (m : ℕ) (hm : m + 2 ≤ k) (z0 : X) :
    Jw X k φ f ν (m+1) (by omega)
      = av (fun t : (Fin m → X) × (X × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X))) =>
          Ghat X k φ f ν m hm z0 t.1 t.2.2.1 t.2.2.2
            * Htw X k φ f ν m hm t.1 t.2.1 t.2.2.1 t.2.2.2) := by
  rw [Jw]
  rw [show (fun u : Fin (m+1) → X => av (fun v : Fin (k-1-(m+1)) → X =>
        av (fun y' : Fin (k-1-(m+1)) → X =>
          Twn X k φ f ν (m+1) (by omega) u v y')))
      = fun u : Fin (m+1) → X =>
          av (fun q : (Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X) =>
            Twn X k φ f ν (m+1) (by omega) u q.1 q.2) from by
    funext u
    exact av_prod (g := fun v y' => Twn X k φ f ν (m+1) (by omega) u v y')]
  rw [av_prod (g := fun (u : Fin (m+1) → X)
      (q : (Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
    Twn X k φ f ν (m+1) (by omega) u q.1 q.2)]
  rw [show (av (fun s : (Fin (m+1) → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
        Twn X k φ f ν (m+1) (by omega) s.1 s.2.1 s.2.2))
      = av (fun t : (Fin m → X) × (X × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X))) =>
          Twn X k φ f ν (m+1) (by omega) (Fin.snoc t.1 t.2.1) t.2.2.1 t.2.2.2) from by
    rw [← av_comp (reindexEquiv (X := X) k m hm)
      (fun t : (Fin m → X) × (X × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X))) =>
        Twn X k φ f ν (m+1) (by omega) (Fin.snoc t.1 t.2.1) t.2.2.1 t.2.2.2)]
    apply av_congr
    intro s
    obtain ⟨u, q⟩ := s
    simp only [reindexEquiv, Equiv.coe_fn_mk, snocEquiv, Equiv.coe_fn_symm_mk]
    rw [Fin.snoc_init_self]]
  rw [show (av (fun t : (Fin m → X) × (X × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X))) =>
        Twn X k φ f ν (m+1) (by omega) (Fin.snoc t.1 t.2.1) t.2.2.1 t.2.2.2))
      = av (fun t : (Fin m → X) × (X × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X))) =>
          Ghat X k φ f ν m hm z0 t.1 t.2.2.1 t.2.2.2
            * Htw X k φ f ν m hm t.1 t.2.1 t.2.2.1 t.2.2.2) from by
    apply av_congr
    intro t
    exact Twn_split' φ f ν hφ hνpos m hm t.1 t.2.1 z0 t.2.2.1 t.2.2.2]


/-- The change of variables `(z, z', v, y') ↦ (consK z v, consK z' y')`. -/
private def csEquiv (k m : ℕ) (hm : m + 2 ≤ k) :
    ((X × X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X))) ≃
      ((Fin (k-1-m) → X) × (Fin (k-1-m) → X)) where
  toFun s := (consK hm s.1.1 s.2.1, consK hm s.1.2 s.2.2)
  invFun t := ((t.1 ⟨0, by omega⟩, t.2 ⟨0, by omega⟩),
    (fun j => t.1 ⟨j.val + 1, by omega⟩, fun j => t.2 ⟨j.val + 1, by omega⟩))
  left_inv s := by
    obtain ⟨⟨z, z'⟩, v, y'⟩ := s
    refine Prod.ext ?_ ?_
    · refine Prod.ext ?_ ?_
      · exact (consK_zero hm z v).symm
      · exact (consK_zero hm z' y').symm
    · refine Prod.ext ?_ ?_
      · funext j; exact consK_succ hm z v j
      · funext j; exact consK_succ hm z' y' j
  right_inv t := by
    obtain ⟨v, y⟩ := t
    refine Prod.ext ?_ ?_
    · funext j
      rcases eq_or_ne j.val 0 with hj | hj
      · have hj0 : j = (⟨0, by omega⟩ : Fin (k-1-m)) := Fin.ext hj
        rw [hj0]
        exact consK_apply_zero (k := k) (m := m) hm (v ⟨0, by omega⟩)
          (fun i => v ⟨i.val + 1, by omega⟩) ⟨0, by omega⟩ rfl
      · have hjn : j = (⟨j.val - 1 + 1, by omega⟩ : Fin (k-1-m)) :=
          Fin.ext (by simp only [Fin.val_mk]; omega)
        rw [hjn]
        exact consK_succ (k := k) (m := m) hm (v ⟨0, by omega⟩)
          (fun i => v ⟨i.val + 1, by omega⟩) ⟨j.val - 1, by omega⟩
    · funext j
      rcases eq_or_ne j.val 0 with hj | hj
      · have hj0 : j = (⟨0, by omega⟩ : Fin (k-1-m)) := Fin.ext hj
        rw [hj0]
        exact consK_apply_zero (k := k) (m := m) hm (y ⟨0, by omega⟩)
          (fun i => y ⟨i.val + 1, by omega⟩) ⟨0, by omega⟩ rfl
      · have hjn : j = (⟨j.val - 1 + 1, by omega⟩ : Fin (k-1-m)) :=
          Fin.ext (by simp only [Fin.val_mk]; omega)
        rw [hjn]
        exact consK_succ (k := k) (m := m) hm (y ⟨0, by omega⟩)
          (fun i => y ⟨i.val + 1, by omega⟩) ⟨j.val - 1, by omega⟩

/-- The second bookkeeping identity of the weighted recursion: the square of the `z`-average of
`Htw`, averaged over `(u, v, y')`, is the stage-`m` weighted quantity. -/
lemma Jw_Hsq {k : ℕ} (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ) (ν : X → ℝ)
    (m : ℕ) (hm : m + 2 ≤ k) :
    (av (fun s : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
        (av (fun z : X => Htw X k φ f ν m hm s.1 z s.2.1 s.2.2))^2))
      = Jw X k φ f ν m (by omega) := by
  rw [show (fun s : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
        (av (fun z : X => Htw X k φ f ν m hm s.1 z s.2.1 s.2.2))^2)
      = fun s : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
          av (fun p : X × X => Htw X k φ f ν m hm s.1 p.1 s.2.1 s.2.2
            * Htw X k φ f ν m hm s.1 p.2 s.2.1 s.2.2) from by
    funext s
    rw [av_sq]]
  rw [show (fun s : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
        av (fun p : X × X => Htw X k φ f ν m hm s.1 p.1 s.2.1 s.2.2
          * Htw X k φ f ν m hm s.1 p.2 s.2.1 s.2.2))
      = fun s : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
          av (fun p : X × X => Twn X k φ f ν m (by omega) s.1
            (consK hm p.1 s.2.1) (consK hm p.2 s.2.2)) from by
    funext s
    apply av_congr
    intro p
    exact (Twn_expand φ f ν m hm s.1 p.1 p.2 s.2.1 s.2.2).symm]
  rw [av_prod (g := fun (s : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)))
      (p : X × X) => Twn X k φ f ν m (by omega) s.1 (consK hm p.1 s.2.1) (consK hm p.2 s.2.2))]
  rw [show (av (fun t : ((Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X))) × (X × X) =>
        Twn X k φ f ν m (by omega) t.1.1 (consK hm t.2.1 t.1.2.1) (consK hm t.2.2 t.1.2.2)))
      = av (fun w : (Fin m → X) × ((Fin (k-1-m) → X) × (Fin (k-1-m) → X)) =>
          Twn X k φ f ν m (by omega) w.1 w.2.1 w.2.2) from by
    rw [← av_comp
      ((Equiv.prodAssoc (Fin m → X) ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) (X × X)).trans
        ((Equiv.prodCongr (Equiv.refl (Fin m → X))
          (Equiv.prodComm (α := (Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) (β := X × X))).trans
          (Equiv.prodCongr (Equiv.refl (Fin m → X)) (csEquiv (X := X) k m hm))))
      (fun w : (Fin m → X) × ((Fin (k-1-m) → X) × (Fin (k-1-m) → X)) =>
        Twn X k φ f ν m (by omega) w.1 w.2.1 w.2.2)]
    apply av_congr
    intro t
    obtain ⟨s, p⟩ := t
    simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, csEquiv, Prod.mk.injEq,
      Prod.map, Function.comp_apply]
    rfl ]
  rw [Jw]
  rw [show (fun u : Fin m → X => av (fun v : Fin (k-1-m) → X =>
        av (fun y' : Fin (k-1-m) → X => Twn X k φ f ν m (by omega) u v y')))
      = fun u : Fin m → X => av (fun s : (Fin (k-1-m) → X) × (Fin (k-1-m) → X) =>
          Twn X k φ f ν m (by omega) u s.1 s.2) from by
    funext u
    exact av_prod (g := fun v y' => Twn X k φ f ν m (by omega) u v y')]
  rw [av_prod (g := fun (u : Fin m → X) (s : (Fin (k-1-m) → X) × (Fin (k-1-m) → X)) =>
    Twn X k φ f ν m (by omega) u s.1 s.2)]


/-- Green–Tao's weighted Cauchy–Schwarz recursion `(J_d)² ≤ P_d J_{d+1}`. -/
lemma Jw_sq_le {k : ℕ} (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ) (ν : X → ℝ)
    (hf : ∀ i x, |f i x| ≤ ν x) (hνpos : ∀ x, 0 < ν x)
    (hφ : ∀ (m : ℕ) (hm : m + 2 ≤ k) (u : Fin m → X) (z z' : X)
        (w : Fin (k-1-(m+1)) → X),
      φ ⟨m+1, by omega⟩ (app k (m+1) (by omega) (Fin.snoc u z) w)
        = φ ⟨m+1, by omega⟩ (app k (m+1) (by omega) (Fin.snoc u z') w))
    (m : ℕ) (hm : m + 2 ≤ k) :
    (Jw X k φ f ν (m+1) (by omega))^2
      ≤ (av (fun r : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
            ∏ ω : Fin (k-1-(m+1)) → Bool, ν (φ ⟨m+1, by omega⟩
              (app k (m+1) (by omega) (Fin.snoc r.1 (Classical.arbitrary X))
                (fun j => if ω j then r.2.2 j else r.2.1 j)))))
        * Jw X k φ f ν m (by omega) := by
  set z0 : X := Classical.arbitrary X with hz0
  rw [Jw_reindex φ f ν hφ hνpos m hm z0]
  rw [show (av (fun t : (Fin m → X) × (X × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X))) =>
        Ghat X k φ f ν m hm z0 t.1 t.2.2.1 t.2.2.2 * Htw X k φ f ν m hm t.1 t.2.1 t.2.2.1 t.2.2.2))
      = av (fun s : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
          Ghat X k φ f ν m hm z0 s.1 s.2.1 s.2.2
            * av (fun z : X => Htw X k φ f ν m hm s.1 z s.2.1 s.2.2)) from by
    rw [← av_prod (g := fun (u : Fin m → X)
        (p : X × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X))) =>
      Ghat X k φ f ν m hm z0 u p.2.1 p.2.2 * Htw X k φ f ν m hm u p.1 p.2.1 p.2.2)]
    rw [show (fun u : Fin m → X => av (fun p : X × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
          Ghat X k φ f ν m hm z0 u p.2.1 p.2.2 * Htw X k φ f ν m hm u p.1 p.2.1 p.2.2))
        = fun u : Fin m → X => av (fun z : X =>
            av (fun q : (Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X) =>
              Ghat X k φ f ν m hm z0 u q.1 q.2 * Htw X k φ f ν m hm u z q.1 q.2)) from by
      funext u
      rw [← av_prod (g := fun (z : X)
          (q : (Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
        Ghat X k φ f ν m hm z0 u q.1 q.2 * Htw X k φ f ν m hm u z q.1 q.2)]]
    rw [show (fun u : Fin m → X => av (fun z : X =>
          av (fun q : (Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X) =>
            Ghat X k φ f ν m hm z0 u q.1 q.2 * Htw X k φ f ν m hm u z q.1 q.2)))
        = fun u : Fin m → X => av (fun q : (Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X) =>
            av (fun z : X => Ghat X k φ f ν m hm z0 u q.1 q.2 * Htw X k φ f ν m hm u z q.1 q.2))
        from by
      funext u
      exact av_swap (F := fun (z : X)
        (q : (Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
        Ghat X k φ f ν m hm z0 u q.1 q.2 * Htw X k φ f ν m hm u z q.1 q.2)]
    rw [show (fun u : Fin m → X => av (fun q : (Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X) =>
          av (fun z : X => Ghat X k φ f ν m hm z0 u q.1 q.2 * Htw X k φ f ν m hm u z q.1 q.2)))
        = fun u : Fin m → X => av (fun q : (Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X) =>
            Ghat X k φ f ν m hm z0 u q.1 q.2
              * av (fun z : X => Htw X k φ f ν m hm u z q.1 q.2)) from by
      funext u
      apply av_congr
      intro q
      rw [show (fun z : X => Ghat X k φ f ν m hm z0 u q.1 q.2 * Htw X k φ f ν m hm u z q.1 q.2)
          = fun z : X => Htw X k φ f ν m hm u z q.1 q.2 * Ghat X k φ f ν m hm z0 u q.1 q.2
            from by funext z; ring]
      rw [av_mul_const, mul_comm]]
    rw [← av_prod (g := fun (u : Fin m → X)
        (q : (Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
      Ghat X k φ f ν m hm z0 u q.1 q.2 * av (fun z : X => Htw X k φ f ν m hm u z q.1 q.2))]]
  have hcs := av_mul_sq_le
    (fun s : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
      Ghat X k φ f ν m hm z0 s.1 s.2.1 s.2.2)
    (fun s : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
      av (fun z : X => Htw X k φ f ν m hm s.1 z s.2.1 s.2.2))
  have hG : (av (fun s : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
        (Ghat X k φ f ν m hm z0 s.1 s.2.1 s.2.2)^2))
      ≤ (av (fun s : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
          ∏ ω : Fin (k-1-(m+1)) → Bool, ν (φ ⟨m+1, by omega⟩
            (app k (m+1) (by omega) (Fin.snoc s.1 z0)
              (fun j => if ω j then s.2.2 j else s.2.1 j))))) :=
    av_le (fun s => Ghat_sq_le φ f ν hf hνpos m hm z0 s.1 s.2.1 s.2.2)
  have hH : (av (fun s : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
        (av (fun z : X => Htw X k φ f ν m hm s.1 z s.2.1 s.2.2))^2))
      = Jw X k φ f ν m (by omega) := Jw_Hsq φ f ν m hm
  have hnn : 0 ≤ (av (fun s : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
      (av (fun z : X => Htw X k φ f ν m hm s.1 z s.2.1 s.2.2))^2)) :=
    av_nonneg _ (fun s => sq_nonneg _)
  calc (av (fun s : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
        Ghat X k φ f ν m hm z0 s.1 s.2.1 s.2.2
          * av (fun z : X => Htw X k φ f ν m hm s.1 z s.2.1 s.2.2)))^2
      ≤ (av (fun s : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
          (Ghat X k φ f ν m hm z0 s.1 s.2.1 s.2.2)^2))
        * (av (fun s : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
          (av (fun z : X => Htw X k φ f ν m hm s.1 z s.2.1 s.2.2))^2)) := hcs
    _ ≤ (av (fun s : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
          ∏ ω : Fin (k-1-(m+1)) → Bool, ν (φ ⟨m+1, by omega⟩
            (app k (m+1) (by omega) (Fin.snoc s.1 z0)
              (fun j => if ω j then s.2.2 j else s.2.1 j)))))
        * (av (fun s : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
          (av (fun z : X => Htw X k φ f ν m hm s.1 z s.2.1 s.2.2))^2)) :=
        mul_le_mul_of_nonneg_right hG hnn
    _ = (av (fun s : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
          ∏ ω : Fin (k-1-(m+1)) → Bool, ν (φ ⟨m+1, by omega⟩
            (app k (m+1) (by omega) (Fin.snoc s.1 z0)
              (fun j => if ω j then s.2.2 j else s.2.1 j)))))
        * Jw X k φ f ν m (by omega) := by rw [hH]


/-- The `P`-weight of the weighted recursion at stage `m` (junk value `0` if the stage is out
of range). -/
noncomputable def Pm (X : Type*) [Fintype X] [Nonempty X] (k : ℕ)
    (φ : Fin k → (Fin (k-1) → X) → X) (ν : X → ℝ) (m : ℕ) : ℝ :=
  if h : m + 1 < k then
    av (fun r : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
      ∏ ω : Fin (k-1-(m+1)) → Bool, ν (φ ⟨m+1, h⟩
        (app k (m+1) (by omega) (Fin.snoc r.1 (Classical.arbitrary X))
          (fun j => if ω j then r.2.2 j else r.2.1 j))))
  else 0

/-- The `P`-weight at a stage in range. -/
lemma Pm_eq {k : ℕ} (φ : Fin k → (Fin (k-1) → X) → X) (ν : X → ℝ)
    (m : ℕ) (hm : m + 2 ≤ k) :
    Pm X k φ ν m
      = av (fun r : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
          ∏ ω : Fin (k-1-(m+1)) → Bool, ν (φ ⟨m+1, by omega⟩
            (app k (m+1) (by omega) (Fin.snoc r.1 (Classical.arbitrary X))
              (fun j => if ω j then r.2.2 j else r.2.1 j)))) := by
  rw [Pm, dif_pos (by omega)]

/-- The `P`-weights are nonnegative. -/
lemma Pm_nonneg {k : ℕ} (φ : Fin k → (Fin (k-1) → X) → X) (ν : X → ℝ)
    (hνpos : ∀ x, 0 < ν x) (m : ℕ) : 0 ≤ Pm X k φ ν m := by
  rw [Pm]
  split
  · apply av_nonneg
    intro r
    exact Finset.prod_nonneg (fun ω _ => le_of_lt (hνpos _))
  · exact le_refl 0

/-- The weighted Cauchy–Schwarz recursion, in `Pm`-form. -/
lemma Jw_sq_le' {k : ℕ} (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ) (ν : X → ℝ)
    (hf : ∀ i x, |f i x| ≤ ν x) (hνpos : ∀ x, 0 < ν x)
    (hφ : ∀ (m : ℕ) (hm : m + 2 ≤ k) (u : Fin m → X) (z z' : X)
        (w : Fin (k-1-(m+1)) → X),
      φ ⟨m+1, by omega⟩ (app k (m+1) (by omega) (Fin.snoc u z) w)
        = φ ⟨m+1, by omega⟩ (app k (m+1) (by omega) (Fin.snoc u z') w))
    (m : ℕ) (hm : m + 2 ≤ k) :
    (Jw X k φ f ν (m+1) (by omega))^2 ≤ Pm X k φ ν m * Jw X k φ f ν m (by omega) := by
  rw [Pm_eq φ ν m hm]
  exact Jw_sq_le φ f ν hf hνpos hφ m hm

/-- Iterating the weighted Cauchy–Schwarz recursion: the `2^m`-th power of the stage-`m`
quantity is bounded by the stage-`0` quantity times the accumulated `P`-weights. -/
lemma Jw_pow_le {k : ℕ} (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ) (ν : X → ℝ)
    (hf : ∀ i x, |f i x| ≤ ν x) (hνpos : ∀ x, 0 < ν x)
    (hφ : ∀ (m : ℕ) (hm : m + 2 ≤ k) (u : Fin m → X) (z z' : X)
        (w : Fin (k-1-(m+1)) → X),
      φ ⟨m+1, by omega⟩ (app k (m+1) (by omega) (Fin.snoc u z) w)
        = φ ⟨m+1, by omega⟩ (app k (m+1) (by omega) (Fin.snoc u z') w))
    (hk : 1 ≤ k) :
    ∀ (m : ℕ) (hm : m + 1 ≤ k),
      (Jw X k φ f ν m hm)^(2^m)
        ≤ Jw X k φ f ν 0 (by omega) * ∏ i ∈ Finset.range m, (Pm X k φ ν i)^(2^i) := by
  intro m
  induction m with
  | zero =>
    intro hm
    rw [show (2:ℕ)^0 = 1 from rfl, pow_one, Finset.range_zero, Finset.prod_empty, mul_one]
  | succ n ih =>
    intro hm
    have hn : n + 1 ≤ k := by omega
    have hstep : (Jw X k φ f ν (n+1) (by omega))^2
        ≤ Pm X k φ ν n * Jw X k φ f ν n (by omega) :=
      Jw_sq_le' φ f ν hf hνpos hφ n (by omega)
    have hP : 0 ≤ Pm X k φ ν n := Pm_nonneg φ ν hνpos n
    rw [pow_succ', pow_mul]
    refine le_trans (pow_le_pow_left₀ (sq_nonneg _) hstep (2^n)) ?_
    rw [mul_pow]
    refine le_trans (mul_le_mul_of_nonneg_left (ih hn) (pow_nonneg hP _)) ?_
    rw [Finset.prod_range_succ]
    exact le_of_eq (by ring)


/-- At the last stage (`m = k-1`) the weighted quantity is the average of the product of all
the `f_i` over the `φ_i` (the cube and the `√ν`-product are empty). -/
lemma Jw_last {k : ℕ} (hk : 1 ≤ k) (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ)
    (ν : X → ℝ) (hm : k - 1 + 1 ≤ k) :
    Jw X k φ f ν (k-1) hm = av (fun u : Fin (k-1) → X => ∏ i : Fin k, f i (φ i u)) := by
  have happ : ∀ (u : Fin (k-1) → X) (w : Fin (k-1-(k-1)) → X),
      app k (k-1) hm u w = fun j : Fin (k-1) => u ⟨j.val, j.isLt⟩ := by
    intro u w
    funext j
    rw [app_apply, dif_pos j.isLt]
  rw [Jw]
  apply av_congr
  intro u
  -- the `v`- and `y'`-averages are over the one-point types `Fin 0 → X`
  have hE : IsEmpty (Fin (k-1-(k-1))) := by
    rw [show k-1-(k-1) = 0 from Nat.sub_self _]
    infer_instance
  have hT : ∀ (v y' : Fin (k-1-(k-1)) → X),
      Twn X k φ f ν (k-1) hm u v y'
        = ∏ ω : Fin (k-1-(k-1)) → Bool, ∏ i : Fin (k-1+1),
            f ⟨i.val, by omega⟩ (φ ⟨i.val, by omega⟩ (fun j : Fin (k-1) => u ⟨j.val, j.isLt⟩)) := by
    intro v y'
    simp only [Twn]
    apply Finset.prod_congr rfl
    intro ω _
    rw [Finset.prod_eq_one (fun i _ => (hE.false i).elim), mul_one]
    apply Finset.prod_congr rfl
    intro i _
    rw [happ u (fun j => if ω j then y' j else v j)]
  rw [show (fun v : Fin (k-1-(k-1)) → X => av (fun y' : Fin (k-1-(k-1)) → X =>
        Twn X k φ f ν (k-1) hm u v y'))
      = (fun _ : Fin (k-1-(k-1)) → X =>
          ∏ ω : Fin (k-1-(k-1)) → Bool, ∏ i : Fin (k-1+1),
            f ⟨i.val, by omega⟩ (φ ⟨i.val, by omega⟩ (fun j : Fin (k-1) => u ⟨j.val, j.isLt⟩)))
      from by
    funext v
    rw [av_congr (fun y' => hT v y')]
    exact av_const _]
  rw [av_const]
  -- collapse the empty cube product and reindex `Fin (k-1+1)` as `Fin k`
  haveI : Unique (Fin (k-1-(k-1)) → Bool) :=
    ⟨⟨fun i => (hE.false i).elim⟩, fun a => funext (fun i => (hE.false i).elim)⟩
  rw [Fintype.prod_unique]
  refine Fintype.prod_equiv (finCongr (Nat.sub_add_cancel hk)) _ _ (fun i => ?_)
  have he : finCongr (Nat.sub_add_cancel hk) i = (⟨i.val, by omega⟩ : Fin k) :=
    Fin.ext (by simp [finCongr])
  rw [he]




/-- At stage `0` the weighted quantity is the average of the weighted cube of `f_0`. -/
lemma Jw_zero {k : ℕ} (hk : 1 ≤ k) (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ)
    (ν : X → ℝ) (hm : 0 + 1 ≤ k) :
    Jw X k φ f ν 0 hm
      = av (fun v : Fin (k-1-0) → X => av (fun y' : Fin (k-1-0) → X =>
          ∏ ω : Fin (k-1-0) → Bool,
            (∏ i : Fin (0+1), f ⟨i.val, by omega⟩ (φ ⟨i.val, by omega⟩
                (fun j => if ω j then y' j else v j)))
              * ∏ i : Fin (k-1-0), Real.sqrt (ν (φ ⟨0+1+i.val, by omega⟩
                  (fun j => if ω j then y' j else v j))))) := by
  have happ : ∀ (u : Fin 0 → X) (w : Fin (k-1-0) → X), app k 0 hm u w = w := by
    intro u w
    funext j
    rw [app_apply, dif_neg (by omega : ¬ j.val < 0)]
    congr 1
  have hT : ∀ (u : Fin 0 → X) (v y' : Fin (k-1-0) → X),
      Twn X k φ f ν 0 hm u v y'
        = ∏ ω : Fin (k-1-0) → Bool,
            (∏ i : Fin (0+1), f ⟨i.val, by omega⟩ (φ ⟨i.val, by omega⟩
                (fun j => if ω j then y' j else v j)))
            * ∏ i : Fin (k-1-0), Real.sqrt (ν (φ ⟨0+1+i.val, by omega⟩
                (fun j => if ω j then y' j else v j))) := by
    intro u v y'
    simp only [Twn]
    apply Finset.prod_congr rfl
    intro ω _
    rw [show (∏ i : Fin (0+1), f ⟨i.val, by omega⟩ (φ ⟨i.val, by omega⟩
          (app k 0 hm u (fun j => if ω j then y' j else v j))))
        = ∏ i : Fin (0+1), f ⟨i.val, by omega⟩ (φ ⟨i.val, by omega⟩
          (fun j => if ω j then y' j else v j)) from by
      apply Finset.prod_congr rfl
      intro i _
      rw [happ u (fun j => if ω j then y' j else v j)]
      rfl]
    rw [show (∏ i : Fin (k-1-0), Real.sqrt (ν (φ ⟨0+1+i.val, by omega⟩
          (app k 0 hm u (fun j => if ω j then y' j else v j)))))
        = ∏ i : Fin (k-1-0), Real.sqrt (ν (φ ⟨0+1+i.val, by omega⟩
          (fun j => if ω j then y' j else v j))) from by
      apply Finset.prod_congr rfl
      intro i _
      rw [happ u (fun j => if ω j then y' j else v j)]
      rfl]
  rw [Jw]
  rw [show (fun u : Fin 0 → X => av (fun v : Fin (k-1-0) → X =>
        av (fun y' : Fin (k-1-0) → X => Twn X k φ f ν 0 hm u v y')))
      = (fun _ : Fin 0 → X => av (fun v : Fin (k-1-0) → X =>
          av (fun y' : Fin (k-1-0) → X => Twn X k φ f ν 0 hm
            (fun _ => Classical.arbitrary X) v y'))) from by
    funext u
    rfl]
  rw [av_const]
  rw [show Twn X k φ f ν 0 hm (fun _ => Classical.arbitrary X)
      = fun v y' => ∏ ω : Fin (k-1-0) → Bool,
          (∏ i : Fin (0+1), f ⟨i.val, by omega⟩ (φ ⟨i.val, by omega⟩
              (fun j => if ω j then y' j else v j)))
            * ∏ i : Fin (k-1-0), Real.sqrt (ν (φ ⟨0+1+i.val, by omega⟩
                (fun j => if ω j then y' j else v j))) from by
    funext v y'
    exact hT _ v y']

end WeightedRecursion

/-! ## Specialisation to `ZMod p` -/

section ZModSpecial

variable {p : ℕ} [Fact p.Prime]

/-- The `k`-term arithmetic-progression sum over `ZMod p`. -/
noncomputable def apsumZ (k : ℕ) (f : Fin k → ZMod p → ℝ) : ℝ :=
  ∑ r : ZMod p, ∑ x : ZMod p, ∏ i : Fin k, f i (x + (i : ZMod p) * r)

/-- `σ_ω(h) = ∑_j ω_j h_j`. -/
noncomputable def wsig {n : ℕ} (ω : Fin n → Bool) (h : Fin n → ZMod p) : ZMod p :=
  ∑ j, if ω j then h j else 0

/-- `τ_ω(h) = ∑_j ω_j h_j/(j+1)`. -/
noncomputable def wtau {n : ℕ} (ω : Fin n → Bool) (h : Fin n → ZMod p) : ZMod p :=
  ∑ j, (if ω j then h j else 0) / ((j : ZMod p) + 1)

/-- The sum of the coordinates of the cube vertex `v + ω·h`. -/
lemma sum_vertex {n : ℕ} (v h : Fin n → ZMod p) (ω : Fin n → Bool) :
    (∑ j, (if ω j then h j + v j else v j)) = (∑ j, v j) + wsig ω h := by
  rw [wsig, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : ω j <;> simp_all [add_comm]

/-- The `(j+1)`-weighted sum of the coordinates of the cube vertex `v + ω·h`. -/
lemma sum_div_vertex {n : ℕ} (v h : Fin n → ZMod p) (ω : Fin n → Bool) :
    (∑ j, (if ω j then h j + v j else v j) / ((j : ZMod p) + 1))
      = (∑ j, v j / ((j : ZMod p) + 1)) + wtau ω h := by
  rw [wtau, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : ω j <;> simp_all [add_div, add_comm]

/-- The Green–Tao reparametrisation evaluated at a cube vertex. -/
lemma phiZ_vertex {k : ℕ} (v h : Fin (k-1) → ZMod p) (ω : Fin (k-1) → Bool) (i : Fin k) :
    phiZ (p:=p) k i (fun j => if ω j then h j + v j else v j)
      = ((∑ t, v t) + wsig ω h)
        - (i : ZMod p) * ((∑ t, v t / ((t : ZMod p) + 1)) + wtau ω h) := by
  rw [phiZ_apply, sum_vertex v h ω, sum_div_vertex v h ω]

/-- The `ω`-th vertex weight of the weighted cube: `f_0` at the vertex and half-weights `√ν` at
the reparametrised points `φ_i` of the vertex, `1 ≤ i ≤ k-1`. -/
noncomputable def wvtx (k : ℕ) (g : ZMod p → ℝ) (ν : ZMod p → ℝ) (x s : ZMod p)
    (h : Fin (k-1) → ZMod p) (ω : Fin (k-1) → Bool) : ℝ :=
  g (x + wsig ω h) * ∏ i : Fin (k-1), Real.sqrt (ν (x + wsig ω h
    - ((1 + i.val : ℕ) : ZMod p) * (s + wtau ω h)))

/-- The weighted `(k-1)`-dimensional cube sum (the `J_{k-1}` of Green–Tao). -/
noncomputable def wcubeZ (k : ℕ) (g : ZMod p → ℝ) (ν : ZMod p → ℝ) : ℝ :=
  ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, ∑ s : ZMod p,
    ∏ ω : Fin (k-1) → Bool, wvtx k g ν x s h ω

/-- The stage-`0` weighted integrand in the cube coordinates `(v, y')`. -/
noncomputable def wint0 (k : ℕ) (g : ZMod p → ℝ) (ν : ZMod p → ℝ)
    (v y' : Fin (k-1) → ZMod p) : ℝ :=
  ∏ ω : Fin (k-1) → Bool,
    (g (∑ j, (if ω j then y' j else v j))
      * ∏ i : Fin (k-1), Real.sqrt (ν (phiZ (p:=p) k ⟨1+i.val, by have := i.isLt; omega⟩
          (fun j => if ω j then y' j else v j))))

/-! ### Step A: the last stage is the `k`-term AP sum -/

lemma Jw_last_zmod {k : ℕ} (hk : 3 ≤ k) (hkp : k ≤ p) (f : Fin k → ZMod p → ℝ)
    (ν : ZMod p → ℝ) :
    Jw (ZMod p) k (phiZ (p:=p) k) f ν (k-1) (by omega)
      = ((p:ℝ)^2)⁻¹ * apsumZ k f := by
  have hpne : (p:ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hcard : (Fintype.card (Fin (k-1) → ZMod p) : ℝ) = (p : ℝ)^(k-1) :=
    card_fun_zmod (p:=p) (k-1)
  have hsum : (∑ u : Fin (k-1) → ZMod p, ∏ i : Fin k, f i (phiZ (p:=p) k i u))
      = (p : ℝ)^(k-3) * apsumZ k f := by
    have hcov := sum_phiZ_cover (p:=p) hk hkp
      (fun a b => ∏ i : Fin k, f i (a - (i : ZMod p) * b))
    have hL : (∑ u : Fin (k-1) → ZMod p, ∏ i : Fin k, f i (phiZ (p:=p) k i u))
        = (∑ u : Fin (k-1) → ZMod p, ∏ i : Fin k, f i ((∑ t, u t)
            - (i : ZMod p) * (∑ t, u t / ((t : ZMod p) + 1)))) := by
      apply Finset.sum_congr rfl; intro u _
      apply Finset.prod_congr rfl; intro i _
      rw [phiZ_apply]
    have h1 : (∑ q : ZMod p × ZMod p, ∏ i : Fin k, f i (q.1 - (i : ZMod p) * q.2))
        = (∑ q : ZMod p × ZMod p, ∏ i : Fin k, f i (q.1 + (i : ZMod p) * q.2)) := by
      calc (∑ q : ZMod p × ZMod p, ∏ i : Fin k, f i (q.1 - (i : ZMod p) * q.2))
          = (∑ q : ZMod p × ZMod p, ∏ i : Fin k, f i
              ((Equiv.prodCongr (Equiv.refl (ZMod p)) (Equiv.neg (ZMod p)) q).1
                + (i : ZMod p) * (Equiv.prodCongr (Equiv.refl (ZMod p))
                    (Equiv.neg (ZMod p)) q).2)) := by
            apply Finset.sum_congr rfl; intro q _
            obtain ⟨a, b⟩ := q
            apply Finset.prod_congr rfl; intro i _
            have hfst : (Equiv.prodCongr (Equiv.refl (ZMod p)) (Equiv.neg (ZMod p)) (a,b)).1 = a :=
              rfl
            have hsnd : (Equiv.prodCongr (Equiv.refl (ZMod p)) (Equiv.neg (ZMod p)) (a,b)).2
                = -b := rfl
            rw [hfst, hsnd]
            congr 1
            ring
        _ = (∑ q : ZMod p × ZMod p, ∏ i : Fin k, f i (q.1 + (i : ZMod p) * q.2)) :=
            Equiv.sum_comp (Equiv.prodCongr (Equiv.refl (ZMod p)) (Equiv.neg (ZMod p)))
              (fun q : ZMod p × ZMod p => ∏ i : Fin k, f i (q.1 + (i : ZMod p) * q.2))
    have h2 : (∑ q : ZMod p × ZMod p, ∏ i : Fin k, f i (q.1 + (i : ZMod p) * q.2))
        = (∑ r : ZMod p, ∑ x : ZMod p, ∏ i : Fin k, f i (x + (i : ZMod p) * r)) := by
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_comm]
    rw [hL, hcov]
    congr 1
    rw [apsumZ]
    exact h1.trans h2
  rw [Jw_last (k := k) (by omega) (phiZ (p:=p) k) f ν (by omega)]
  unfold av
  rw [hcard, hsum]
  have hc1 : ((p:ℝ)^(k-1))⁻¹ * (p:ℝ)^(k-3) = ((p:ℝ)^2)⁻¹ := by
    have hsplit : (p:ℝ)^(k-1) = (p:ℝ)^2 * (p:ℝ)^(k-3) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit, mul_inv, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hpne), mul_one]
  rw [← mul_assoc, hc1]

/-! ### Step B: stage `0` is the weighted cube sum -/

/-- The stage-`0` quantity, written with the integrand `wint0` in the cube coordinates. -/
lemma Jw_zero_wint {k : ℕ} (hk : 1 ≤ k) (f : Fin k → ZMod p → ℝ) (ν : ZMod p → ℝ) :
    Jw (ZMod p) k (phiZ (p:=p) k) f ν 0 (by omega)
      = av (fun v : Fin (k-1) → ZMod p => av (fun y' : Fin (k-1) → ZMod p =>
          wint0 k (f ⟨0, by omega⟩) ν v y')) := by
  rw [Jw_zero (X := ZMod p) (k := k) hk (phiZ (p:=p) k) f ν (by omega)]
  apply av_congr; intro v
  apply av_congr; intro y'
  rw [wint0]
  apply Finset.prod_congr rfl; intro ω _
  rw [prod_fin_one_phiZ (p:=p) hk f (fun j => if ω j then y' j else v j)]
  rfl

/-- The weighted integrand at a translated cube vertex, in terms of the two linear forms
`x = ∑ v`, `s = ∑ v/(j+1)`. -/
lemma wint0_shift {k : ℕ} (g : ZMod p → ℝ) (ν : ZMod p → ℝ)
    (v h : Fin (k-1) → ZMod p) :
    wint0 k g ν v (h + v)
      = ∏ ω : Fin (k-1) → Bool,
          wvtx k g ν (∑ t, v t) (∑ t, v t / ((t : ZMod p) + 1)) h ω := by
  rw [wint0]
  simp only [Pi.add_apply, wvtx]
  apply Finset.prod_congr rfl; intro ω _
  congr 1
  · exact congrArg g (sum_vertex v h ω)
  · apply Finset.prod_congr rfl; intro i _
    congr 1
    congr 1
    exact phiZ_vertex v h ω ⟨1+i.val, by have := i.isLt; omega⟩

/-- The sum over the cube variables of the stage-`0` integrand is the weighted cube sum. -/
lemma wint0_sum {k : ℕ} (hk : 3 ≤ k) (hkp : k ≤ p) (g : ZMod p → ℝ) (ν : ZMod p → ℝ) :
    (∑ v : Fin (k-1) → ZMod p, ∑ y' : Fin (k-1) → ZMod p, wint0 k g ν v y')
      = (p:ℝ)^(k-3) * wcubeZ k g ν := by
  have hstep1 : (∑ v : Fin (k-1) → ZMod p, ∑ y' : Fin (k-1) → ZMod p, wint0 k g ν v y')
      = (∑ v : Fin (k-1) → ZMod p, ∑ h : Fin (k-1) → ZMod p, wint0 k g ν v (h + v)) := by
    apply Finset.sum_congr rfl; intro v _
    exact cube_shift (p:=p) (fun y' : Fin (k-1) → ZMod p => wint0 k g ν v y') v
  have hstep2 : (∑ v : Fin (k-1) → ZMod p, ∑ h : Fin (k-1) → ZMod p, wint0 k g ν v (h + v))
      = (∑ h : Fin (k-1) → ZMod p, ∑ v : Fin (k-1) → ZMod p,
          ∏ ω : Fin (k-1) → Bool,
            wvtx k g ν (∑ t, v t) (∑ t, v t / ((t : ZMod p) + 1)) h ω) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro h _
    apply Finset.sum_congr rfl; intro v _
    exact wint0_shift g ν v h
  have hstep3 : (∑ h : Fin (k-1) → ZMod p, ∑ v : Fin (k-1) → ZMod p,
        ∏ ω : Fin (k-1) → Bool,
          wvtx k g ν (∑ t, v t) (∑ t, v t / ((t : ZMod p) + 1)) h ω)
      = (p:ℝ)^(k-3) * (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, ∑ s : ZMod p,
          ∏ ω : Fin (k-1) → Bool, wvtx k g ν x s h ω) := by
    rw [show (∑ h : Fin (k-1) → ZMod p, ∑ v : Fin (k-1) → ZMod p,
          ∏ ω : Fin (k-1) → Bool,
            wvtx k g ν (∑ t, v t) (∑ t, v t / ((t : ZMod p) + 1)) h ω)
        = (∑ h : Fin (k-1) → ZMod p,
            (p:ℝ)^(k-3) * ∑ q : ZMod p × ZMod p,
              ∏ ω : Fin (k-1) → Bool, wvtx k g ν q.1 q.2 h ω) from by
      apply Finset.sum_congr rfl; intro h _
      exact sum_phiZ_cover (p:=p) hk hkp (fun x s => ∏ ω, wvtx k g ν x s h ω)]
    rw [← Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl; intro h _
    rw [Fintype.sum_prod_type]
  rw [hstep1, hstep2, hstep3, wcubeZ]

/-- The arithmetic of the stage-`0` endpoint. -/
private lemma arith_zero {k : ℕ} (hk : 3 ≤ k) {W : ℝ} (hpne : (p:ℝ) ≠ 0) :
    ((p:ℝ)^(k-1) * (p:ℝ)^(k-1))⁻¹ * ((p:ℝ)^(k-3) * W) = ((p:ℝ)^(k+1))⁻¹ * W := by
  have hkey : (p:ℝ)^(k-1) * (p:ℝ)^(k-1) = (p:ℝ)^(k-3) * (p:ℝ)^(k+1) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have h1 : (p:ℝ)^(k-3) ≠ 0 := pow_ne_zero _ hpne
  have h2 : (p:ℝ)^(k+1) ≠ 0 := pow_ne_zero _ hpne
  rw [hkey, mul_inv]
  field_simp

/-- **Stage `0` endpoint**: the stage-`0` weighted quantity is `p^{-(k+1)}` times the weighted
`(k-1)`-dimensional cube sum. -/
lemma Jw_zero_zmod {k : ℕ} (hk : 3 ≤ k) (hkp : k ≤ p) (f : Fin k → ZMod p → ℝ)
    (ν : ZMod p → ℝ) :
    Jw (ZMod p) k (phiZ (p:=p) k) f ν 0 (by omega)
      = ((p:ℝ)^(k+1))⁻¹ * wcubeZ k (f ⟨0, by omega⟩) ν := by
  have hk1 : 1 ≤ k := by omega
  have hpne : (p:ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hcard : (Fintype.card ((Fin (k-1) → ZMod p) × (Fin (k-1) → ZMod p)) : ℝ)
      = (p:ℝ)^(k-1) * (p:ℝ)^(k-1) := by
    rw [Fintype.card_prod, Nat.cast_mul, card_fun_zmod (p:=p) (k-1)]
  rw [Jw_zero_wint (p:=p) hk1 f ν, av_prod, av, Fintype.sum_prod_type, hcard]
  rw [wint0_sum (p:=p) hk hkp]
  exact arith_zero (p:=p) (k:=k) hk (W := wcubeZ k (f ⟨0, by omega⟩) ν) hpne

/-! ### Step C: the weighted generalised von Neumann theorem over `ZMod p` -/

/-- The exponent arithmetic for the stage-`(k-1)` endpoint. -/
private lemma pow_two_sub {k : ℕ} {A : ℝ} (hA : 0 ≤ A^(2^(k-1))) :
    A^(2^(k-1)) = |A|^(2^(k-1)) := by
  rw [← abs_pow, abs_of_nonneg hA]

/-- **The weighted (relative) generalised von Neumann theorem over `ZMod p`**
(Green–Tao 2008, Proposition 5.1, with `ν` an arbitrary positive weight and `|f i| ≤ ν`):
the `k`-term arithmetic-progression sum of `f` is controlled by the weighted
`(k-1)`-dimensional cube sum of `f 0` and the `ν`-cube averages `Pm i`. -/
theorem gvn_weighted_zmod {k : ℕ} (hk : 3 ≤ k) (hkp : k ≤ p) (f : Fin k → ZMod p → ℝ)
    (ν : ZMod p → ℝ) (hν : ∀ x, 0 < ν x) (hf : ∀ i x, |f i x| ≤ ν x) :
    |apsumZ k f| ^ (2^(k-1))
      ≤ (p : ℝ)^(2^k - k - 1) * wcubeZ k (f ⟨0, by omega⟩) ν
        * ∏ i ∈ Finset.range (k-1), (Pm (ZMod p) k (phiZ (p:=p) k) ν i)^(2^i) := by
  have hk1 : 1 ≤ k := by omega
  have hp : (0:ℝ) < p := by exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hpne : (p:ℝ) ≠ 0 := ne_of_gt hp
  set A : ℝ := apsumZ k f with hAdef
  set W : ℝ := wcubeZ k (f ⟨0, by omega⟩) ν with hWdef
  set P : ℝ := ∏ i ∈ Finset.range (k-1), (Pm (ZMod p) k (phiZ (p:=p) k) ν i)^(2^i) with hPdef
  have hφ : ∀ (m : ℕ) (hm : m + 2 ≤ k) (u : Fin m → ZMod p) (z z' : ZMod p)
      (w : Fin (k-1-(m+1)) → ZMod p),
      phiZ (p:=p) k ⟨m+1, by omega⟩ (app k (m+1) (by omega) (Fin.snoc u z) w)
        = phiZ (p:=p) k ⟨m+1, by omega⟩ (app k (m+1) (by omega) (Fin.snoc u z') w) :=
    fun m hm u z z' w => phiZ_app_cons (p:=p) hkp m hm u z z' w
  have hrec := Jw_pow_le (X := ZMod p) (k := k) (phiZ (p:=p) k) f ν hf hν hφ hk1 (k-1) (by omega)
  rw [Jw_last_zmod (p:=p) hk hkp f ν, Jw_zero_zmod (p:=p) hk hkp f ν] at hrec
  -- `hrec : (p^{-2} A)^{2^{k-1}} ≤ (p^{-(k+1)} W) P`
  have hA0 : 0 ≤ A^(2^(k-1)) := by
    obtain ⟨m, hm⟩ : ∃ m, 2^(k-1) = 2 * m :=
      ⟨2^(k-2), by rw [← pow_succ' 2 (k-2)]; congr 1; omega⟩
    rw [hm, pow_mul]
    exact pow_nonneg (sq_nonneg A) m
  have hL : (((p:ℝ)^2)⁻¹ * A)^(2^(k-1)) = ((p:ℝ)^(2^k))⁻¹ * |A|^(2^(k-1)) := by
    rw [mul_pow, inv_pow, ← pow_mul, pow_two_sub hA0,
      show 2 * 2^(k-1) = 2^k from by rw [← pow_succ' 2 (k-1), Nat.sub_add_cancel hk1]]
  rw [hL] at hrec
  have hp2 : (0:ℝ) < (p:ℝ)^(2^k) := pow_pos hp _
  have hmain : |A|^(2^(k-1))
      ≤ (p:ℝ)^(2^k) * ((((p:ℝ)^(k+1))⁻¹ * W) * P) := by
    have h := mul_le_mul_of_nonneg_left hrec (le_of_lt hp2)
    rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hp2), one_mul] at h
  have hle : k + 1 ≤ 2^k := by
    have hlt := Nat.lt_two_pow_self (n := k)
    omega
  have hrw : (p:ℝ)^(2^k) * ((((p:ℝ)^(k+1))⁻¹ * W) * P) = ((p:ℝ)^(2^k - (k+1)) * W) * P := by
    rw [show (p:ℝ)^(2^k) * ((((p:ℝ)^(k+1))⁻¹ * W) * P)
        = ((p:ℝ)^(2^k) * ((p:ℝ)^(k+1))⁻¹ * W) * P from by ring]
    rw [show (p:ℝ)^(2^k) * ((p:ℝ)^(k+1))⁻¹ = (p:ℝ)^(2^k - (k+1)) from by
      rw [pow_sub₀ (p:ℝ) hpne hle]]
  rw [hrw] at hmain
  rw [show 2^k - (k+1) = 2^k - k - 1 from by omega] at hmain
  exact hmain

/-! ### Consistency check: the constant weight `ν ≡ 1` recovers the unweighted theorem -/

/-- The weighted cube at constant weight `1` is `p` times the usual `(k-1)`-cube sum. -/
lemma wcubeZ_const (k : ℕ) (g : ZMod p → ℝ) :
    wcubeZ k g (fun _ => 1)
      = (p:ℝ) * ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
          ∏ ω : Fin (k-1) → Bool, g (x + wsig ω h) := by
  rw [wcubeZ]
  rw [show (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, ∑ s : ZMod p,
        ∏ ω : Fin (k-1) → Bool, wvtx k g (fun _ => 1) x s h ω)
      = (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
          (p:ℝ) * ∏ ω : Fin (k-1) → Bool, g (x + wsig ω h)) from by
    apply Finset.sum_congr rfl; intro h _
    apply Finset.sum_congr rfl; intro x _
    rw [show (∑ s : ZMod p, ∏ ω : Fin (k-1) → Bool, wvtx k g (fun _ => 1) x s h ω)
        = ∑ _s : ZMod p, ∏ ω : Fin (k-1) → Bool, g (x + wsig ω h) from by
      apply Finset.sum_congr rfl; intro s _
      apply Finset.prod_congr rfl; intro ω _
      simp only [wvtx, Real.sqrt_one, Finset.prod_const_one, mul_one]]
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]]
  rw [show (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
        (p:ℝ) * ∏ ω : Fin (k-1) → Bool, g (x + wsig ω h))
      = (p:ℝ) * ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
          ∏ ω : Fin (k-1) → Bool, g (x + wsig ω h) from by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro h _
    rw [Finset.mul_sum]]

/-- The `ν`-cube averages at constant weight `1` are all `1`. -/
lemma Pm_const {k : ℕ} (m : ℕ) (hm : m + 1 < k) :
    Pm (ZMod p) k (phiZ (p:=p) k) (fun _ => (1:ℝ)) m = 1 := by
  rw [Pm, dif_pos hm]
  rw [show (fun r : (Fin m → ZMod p) × ((Fin (k-1-(m+1)) → ZMod p) ×
        (Fin (k-1-(m+1)) → ZMod p)) =>
      ∏ ω : Fin (k-1-(m+1)) → Bool, (1:ℝ)) = fun _ => 1 from by
    funext r; simp]
  exact av_const 1

/-- **Consistency check**: at constant weight `ν ≡ 1` the weighted generalised von Neumann
theorem is the unweighted one of Green–Tao §5 (and matches the commons theorem
`Commons.Combinatorics.Additive.Gowers.gvn_general`). -/
theorem gvn_general_zmod_of_weighted {k : ℕ} (hk : 3 ≤ k) (hkp : k ≤ p)
    (f : Fin k → ZMod p → ℝ) (hf : ∀ i x, |f i x| ≤ 1) :
    |apsumZ k f| ^ (2^(k-1))
      ≤ (p:ℝ)^(2^k - k) * (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
          ∏ ω : Fin (k-1) → Bool, f (⟨0, by omega⟩ : Fin k)
            (x + ∑ j : Fin (k-1), (if ω j then h j else 0))) := by
  have hp : (0:ℝ) < p := by exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hle : k + 1 ≤ 2^k := by
    have hlt := Nat.lt_two_pow_self (n := k)
    omega
  have hmain := gvn_weighted_zmod (p:=p) hk hkp f (fun _ => (1:ℝ))
    (fun _ => by norm_num) (fun i x => by simpa using hf i x)
  rw [wcubeZ_const (p:=p) k (f ⟨0, by omega⟩)] at hmain
  have hP : (∏ i ∈ Finset.range (k-1),
      (Pm (ZMod p) k (phiZ (p:=p) k) (fun _ => (1:ℝ)) i)^(2^i)) = 1 := by
    apply Finset.prod_eq_one; intro i hi
    rw [Pm_const (p:=p) i (by rw [Finset.mem_range] at hi; omega), one_pow]
  rw [hP, mul_one] at hmain
  have hkey : (p:ℝ)^(2^k - k - 1) * ((p:ℝ) * (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
        ∏ ω : Fin (k-1) → Bool, f ⟨0, by omega⟩ (x + wsig ω h)))
      = (p:ℝ)^(2^k - k) * (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
        ∏ ω : Fin (k-1) → Bool, f ⟨0, by omega⟩ (x + wsig ω h)) := by
    rw [← mul_assoc]
    congr 1
    rw [← pow_succ, show 2^k - k - 1 + 1 = 2^k - k from by omega]
  rw [hkey] at hmain
  convert hmain using 2
  apply Finset.sum_congr rfl; intro h _
  apply Finset.sum_congr rfl; intro x _
  apply Finset.prod_congr rfl; intro ω _
  rfl


end ZModSpecial

end GVNW

/-! ## The theorem in the requested form -/

namespace Commons.Combinatorics.Additive.Gowers

open scoped BigOperators

open GVNW GVNgen

theorem gvn_weighted (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 3 ≤ k) (hkp : k ≤ p)
    (f : Fin k → ZMod p → ℝ) (ν : ZMod p → ℝ) (hν : ∀ x, 0 < ν x)
    (hf : ∀ i x, |f i x| ≤ ν x) :
    |∑ r : ZMod p, ∑ x : ZMod p, ∏ i : Fin k, f i (x + ((i:ℕ):ZMod p) * r)| ^ (2^(k-1))
      ≤ (p:ℝ)^(2^k - k - 1)
        * (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, ∑ s : ZMod p,
            ∏ ω : Fin (k-1) → Bool,
              (f ⟨0, by omega⟩ (x + ∑ j : Fin (k-1), (if ω j then h j else 0))
                * ∏ i : Fin (k-1), Real.sqrt (ν ((x + ∑ j : Fin (k-1), (if ω j then h j else 0))
                    - ((1 + i.val : ℕ) : ZMod p) * (s + ∑ j : Fin (k-1),
                        (if ω j then h j else 0) / (((j:ℕ):ZMod p) + 1))))))
        * ∏ i ∈ (Finset.range (k-1)).attach,
            (GVNgen.av (fun r : (Fin i.val → ZMod p) ×
                ((Fin (k-1-(i.val+1)) → ZMod p) × (Fin (k-1-(i.val+1)) → ZMod p)) =>
                ∏ ω : Fin (k-1-(i.val+1)) → Bool,
                  ν (GVNgen.phiZ k ⟨i.val+1, by have h := Finset.mem_range.mp i.property; omega⟩
                    (GVNgen.app k (i.val+1) (by have h := Finset.mem_range.mp i.property; omega)
                      (Fin.snoc r.1 (Classical.arbitrary (ZMod p)))
                      (fun j => if ω j then r.2.2 j else r.2.1 j)))))^(2^i.val) := by
  have h := GVNW.gvn_weighted_zmod (p:=p) hk hkp f ν hν hf
  simp only [GVNW.apsumZ, GVNW.wcubeZ, GVNW.wvtx, GVNW.wsig, GVNW.wtau] at h
  have hprod : (∏ i ∈ Finset.range (k-1),
        (Pm (ZMod p) k (phiZ (p:=p) k) ν i)^(2^i))
      = ∏ i ∈ (Finset.range (k-1)).attach,
          (GVNgen.av (fun r : (Fin i.val → ZMod p) ×
              ((Fin (k-1-(i.val+1)) → ZMod p) × (Fin (k-1-(i.val+1)) → ZMod p)) =>
              ∏ ω : Fin (k-1-(i.val+1)) → Bool,
                ν (GVNgen.phiZ k ⟨i.val+1, by have h := Finset.mem_range.mp i.property; omega⟩
                  (GVNgen.app k (i.val+1)
                    (by have h := Finset.mem_range.mp i.property; omega)
                    (Fin.snoc r.1 (Classical.arbitrary (ZMod p)))
                    (fun j => if ω j then r.2.2 j else r.2.1 j)))))^(2^i.val) := by
    refine (Finset.prod_attach (Finset.range (k-1))
      (fun n => (Pm (ZMod p) k (phiZ (p:=p) k) ν n)^(2^n))).symm.trans ?_
    apply Finset.prod_congr rfl; intro i _
    congr 1
    exact Pm_eq (X := ZMod p) (phiZ (p:=p) k) ν i.val
      (by have h := Finset.mem_range.mp i.property; omega)
  rw [hprod] at h
  exact h

end Commons.Combinatorics.Additive.Gowers
