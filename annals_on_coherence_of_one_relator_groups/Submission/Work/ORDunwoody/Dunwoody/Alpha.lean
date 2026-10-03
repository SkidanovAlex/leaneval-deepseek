/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The counting cochain `phi τ` on the 1-skeleton of `Λ''`

`DESIGN_N13.md` §9 records the architecture of the acyclicity proof of the Dunwoody dual graph
`dualGraph` (`Dunwoody/TrackWall.lean`).  The side function of a track `τ` is the "crossing
parity" of a path with `τ`, which is the integral of a fixed `ZMod 2`-valued **cochain** on the
edges of the 1-skeleton `graph` of `Λ''`:

    phi τ v w = 1   if `{v,w}` joins a pattern point `m` of `τ` to the *target* end `m.tgt` of
                    its cell, and `0` otherwise (in particular on the plain, collapsed edges).

The cochain is symmetric (`phi_comm`), so its integral over a walk

    alpha τ [v₀, …, vₙ] = Σ_{i<n} phi τ vᵢ vᵢ₊₁

is additive over concatenations of walks and *unchanged* by the insertion or deletion of a
backtrack.  The two computations the construction uses are

* `phi τ (src m) (mid m) = 0` and `phi τ (mid m) (tgt m) = [m ∈ τ]`: traversing the cell of `m`
  contributes `[m ∈ τ]` in either direction, so `alpha τ` of the boundary walk of a face is the
  number of visits of that face lying in `τ` (even, by `even_visits_of_track`);
* consequently `alpha τ` changes by exactly `1` across the two halves of the cell of a pattern
  point `m ∈ τ`, and not at all for `m ∉ τ` — which is `side_ne` and `side_other` of the wall
  system on the tracks.

Nothing in this file uses the simple connectivity of `Λ''`: that enters only through
`alpha τ (closed walk) = 0` (`DESIGN_N13.md` §9.2).
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.TrackWall

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

namespace Work.ORDunwoody.Dunwoody

open Work.ORDunwoody.Cayley
open scoped Sym2

-- `BaseV D` and `Track D` carry no decidable equality (in particular `G` has none), so the
-- classical decidability of the propositions in the cochain is used locally.
attribute [local instance] Classical.propDecidable

variable {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}
variable {D : GeoData T t₀ P}

/-! ## The endpoints of a cell are distinct -/

/-- A generator edge of length `0` is the constant edge, so a non-zero length forces the generator
to be non-trivial in `G`. -/
theorem genE_ne_one_of_L_ne_zero {x : Fin P.n × Bool} (h : D.L x ≠ 0) :
    CayV.genE P x ≠ 1 := by
  intro hg
  have h0 : D.geo x (Fin.last (D.L x)) = D.geo x 0 := by
    rw [D.geo_last, hg, one_smul, D.geo_zero]
  have h1 : D.L x = 0 := by
    have := congrArg Fin.val (D.geo_inj x h0)
    simpa using this
  exact h h1

theorem genE_true_ne_one_of_L_ne_zero {j : Fin P.n} (h : D.L (j, true) ≠ 0) :
    CayV.genE P (j, true) ≠ 1 :=
  genE_ne_one_of_L_ne_zero h

/-- The position of an interior index: an interior point of the generator edge. -/
theorem pos_of_pos_of_lt (c : G) (j : Fin P.n) {i : ℕ} (h0 : 0 < i) (hi : i < D.L (j, true)) :
    pos D c j i = (c, Sum.inr ⟨j, ⟨i - 1, by omega⟩⟩) := by
  conv_lhs => rw [show i = i - 1 + 1 from (Nat.succ_pred_eq_of_pos h0).symm]
  rw [pos_succ_of_lt D c j (i := i - 1) (by omega)]

/-- The position of the last index: the far end of the generator edge. -/
theorem pos_of_eq_L (c : G) (j : Fin P.n) {i : ℕ} (h0 : 0 < i) (hi : i = D.L (j, true)) :
    pos D c j i = (c * CayV.genE P (j, true), Sum.inl ()) := by
  subst hi
  conv_lhs => rw [show D.L (j, true) = D.L (j, true) - 1 + 1 from
    (Nat.succ_pred_eq_of_pos (by omega)).symm]
  rw [pos_succ_of_not_lt D c j (i := D.L (j, true) - 1) (by omega)]

/-- The shape of the position at a successor index. -/
theorem pos_succ_shape (c : G) (j : Fin P.n) (i : ℕ) :
    pos D c j (i + 1) = if h : i + 1 < D.L (j, true) then (c, Sum.inr ⟨j, ⟨i, by omega⟩⟩)
      else (c * CayV.genE P (j, true), Sum.inl ()) := rfl

/-- The index of an old vertex that is an interior point of a generator edge. -/
def innerVal? : BaseV₀ D → Option ℕ
  | Sum.inl _ => none
  | Sum.inr p => some (p.2 : ℕ)

@[simp] theorem innerVal?_inl (u : Unit) : innerVal? (D := D) (Sum.inl u) = none := rfl

@[simp] theorem innerVal?_inr (p : Sigma fun j : Fin P.n => Fin (D.L (j, true) - 1)) :
    innerVal? (D := D) (Sum.inr p) = some (p.2 : ℕ) := rfl

/-- A cell (a sub-edge of a positive generator edge) has distinct endpoints. -/
theorem pos_ne_succ (c : G) (j : Fin P.n) {k : ℕ} (hk : k < D.L (j, true)) :
    pos D c j k ≠ pos D c j (k + 1) := by
  rcases k with _ | k'
  · -- the source is the base point `(c, ∗)`
    rw [pos_zero D c j, pos_succ_shape (D := D) c j 0]
    by_cases h : 0 + 1 < D.L (j, true)
    · rw [dif_pos h]
      intro hc
      exact Sum.inl_ne_inr (Prod.mk.inj hc).2
    · rw [dif_neg h]
      intro hc
      have h1 : c = c * CayV.genE P (j, true) := congrArg Prod.fst hc
      have h2 : CayV.genE P (j, true) = 1 := by
        have := congrArg (fun z => c⁻¹ * z) h1
        simpa [mul_assoc] using this.symm
      exact genE_true_ne_one_of_L_ne_zero (ne_of_gt hk) h2
  · -- the source is an interior point
    have hk' : k' + 1 < D.L (j, true) := hk
    rw [pos_succ_shape (D := D) c j k', pos_succ_shape (D := D) c j (k' + 1)]
    by_cases h' : k' + 1 + 1 < D.L (j, true)
    · rw [dif_pos hk', dif_pos h']
      intro hc
      have h5 : k' = k' + 1 := by
        have hsum := (Prod.mk.inj hc).2
        simpa [innerVal?] using congrArg innerVal? hsum
      exact absurd h5.symm (Nat.succ_ne_self k')
    · rw [dif_pos hk', dif_neg h']
      intro hc
      exact Sum.inr_ne_inl (Prod.mk.inj hc).2

/-- **The two ends of the cell of a pattern point are distinct** (so a pattern point always
separates its two adjacent half-cells). -/
theorem MidV.src_ne_tgt (m : MidV D) : MidV.src m ≠ MidV.tgt m := by
  obtain ⟨c, ⟨j, k⟩⟩ := m
  exact pos_ne_succ (D := D) c j k.isLt

/-! ## The cochain -/

/-- **The counting cochain of a track.**  On the two edges of the 1-skeleton joining a pattern
point `m` to the target end `m.tgt` of its cell it takes the value `1` when `m` lies in the track
`τ` (and `0` otherwise); on every other edge of the 1-skeleton it is `0`. -/
noncomputable def phi (τ : Track D) : Vertex D → Vertex D → ZMod 2
  | Sum.inl u, Sum.inr m => if u = MidV.tgt m then (if trackOf m = τ then 1 else 0) else 0
  | Sum.inr m, Sum.inl u => if u = MidV.tgt m then (if trackOf m = τ then 1 else 0) else 0
  | _, _ => 0

@[simp] theorem phi_old_old (τ : Track D) (u u' : BaseV D) :
    phi τ (Sum.inl u) (Sum.inl u') = 0 := rfl

@[simp] theorem phi_mid_mid (τ : Track D) (m m' : MidV D) :
    phi τ (Sum.inr m) (Sum.inr m') = 0 := rfl

/-- The cochain is symmetric: reversing a step does not change its contribution. -/
theorem phi_comm (τ : Track D) (v w : Vertex D) : phi τ v w = phi τ w v := by
  cases v with
  | inl u => cases w with
    | inl u' => simp
    | inr m => simp [phi]
  | inr m => cases w with
    | inl u => simp [phi]
    | inr m' => simp

/-- The source half of a cell carries no value. -/
theorem phi_src_mid (τ : Track D) (m : MidV D) :
    phi τ (Sum.inl (MidV.src m)) (Sum.inr m) = 0 := by
  have hne : MidV.src m ≠ MidV.tgt m := MidV.src_ne_tgt m
  simp only [phi]
  rw [if_neg (fun h => hne h)]

/-- The mid-to-source half of a cell carries no value. -/
theorem phi_mid_src (τ : Track D) (m : MidV D) :
    phi τ (Sum.inr m) (Sum.inl (MidV.src m)) = 0 := by
  have hne : MidV.src m ≠ MidV.tgt m := MidV.src_ne_tgt m
  simp only [phi]
  rw [if_neg (fun h => hne h)]

/-- The target half of a cell carries the value `1` exactly when the pattern point lies in the
track. -/
theorem phi_mid_tgt (τ : Track D) (m : MidV D) :
    phi τ (Sum.inr m) (Sum.inl (MidV.tgt m)) = if trackOf m = τ then 1 else 0 := by
  simp [phi]

theorem phi_tgt_mid (τ : Track D) (m : MidV D) :
    phi τ (Sum.inl (MidV.tgt m)) (Sum.inr m) = if trackOf m = τ then 1 else 0 := by
  simp [phi]

/-! ## The integral over a walk -/

/-- **The integral of `phi τ` over a walk**: the sum of the values of the cochain on the
successive pairs of vertices of the list. -/
noncomputable def alpha (τ : Track D) : List (Vertex D) → ZMod 2
  | [] => 0
  | [_] => 0
  | v :: w :: rest => phi τ v w + alpha τ (w :: rest)

@[simp] theorem alpha_nil (τ : Track D) : alpha τ ([] : List (Vertex D)) = 0 := rfl

@[simp] theorem alpha_singleton (τ : Track D) (v : Vertex D) : alpha τ [v] = 0 := rfl

@[simp] theorem alpha_cons_cons (τ : Track D) (v w : Vertex D) (rest : List (Vertex D)) :
    alpha τ (v :: w :: rest) = phi τ v w + alpha τ (w :: rest) := rfl

theorem alpha_pair (τ : Track D) (v w : Vertex D) : alpha τ [v, w] = phi τ v w := by
  simp

/-- **A traversal of the cell of `m` contributes `[m ∈ τ]`.** -/
theorem alpha_cell (τ : Track D) (m : MidV D) (rest : List (Vertex D)) :
    alpha τ (Sum.inl (MidV.src m) :: Sum.inr m :: Sum.inl (MidV.tgt m) :: rest) =
      (if trackOf m = τ then 1 else 0) + alpha τ (Sum.inl (MidV.tgt m) :: rest) := by
  rw [alpha_cons_cons, alpha_cons_cons, phi_src_mid, phi_mid_tgt, zero_add]

/-- **A traversal of the cell of `m` in the reverse direction contributes `[m ∈ τ]` as well.** -/
theorem alpha_cell_rev (τ : Track D) (m : MidV D) (rest : List (Vertex D)) :
    alpha τ (Sum.inl (MidV.tgt m) :: Sum.inr m :: Sum.inl (MidV.src m) :: rest) =
      (if trackOf m = τ then 1 else 0) + alpha τ (Sum.inl (MidV.src m) :: rest) := by
  rw [alpha_cons_cons, alpha_cons_cons, phi_tgt_mid, phi_mid_src, zero_add]

end Work.ORDunwoody.Dunwoody
