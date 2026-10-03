/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The potential `psi τ` of the counting cochain `phi τ`

`Dunwoody/Alpha.lean` defines the `ZMod 2`-valued counting cochain `phi τ` on the edges of the
1-skeleton `graph` of `Λ''`, and `Dunwoody/AlphaPotential.lean` defines the function
`sigma τ : G → ZMod 2` on the group with the crossing equation

    sigma τ (a * genE P (j,true)) = sigma τ a + A τ a [(j,true)]        (`sigma_genE`)

on the Cayley graph of `G` with respect to the positive generators.

This file builds the **potential** of the cochain on the vertices of `Λ''`, i.e. the `S τ`/`ψ τ` of
`DESIGN_N13.md` §10.3:

* `midInd τ m` is the indicator of the pattern point `m` lying in the track `τ`, as an element of
  `ZMod 2` (the value of `phi τ` on the target half of the cell of `m`, `phi_mid_tgt_apply`);
* `partSum τ c j n` is the sum, over the cells `k < n` of the generator edge `(j,true)` based at
  `c`, of `midInd τ` of the pattern point of that cell;
* `sideV τ : BaseV D → ZMod 2` is `sigma τ` at a base point and
  `sigma τ c + partSum τ c j (i+1)` at the `i`-th interior point of the generator edge `(j,true)`
  based at `c`;
* `psi τ : Vertex D → ZMod 2` couples the old vertices with the pattern points by
  `psi τ (inr m) := sideV τ (MidV.src m)`.

The engine of the whole acyclicity proof is the **potential equation**

    phi τ v w = psi τ v + psi τ w          for every edge {v,w} of `graph`     (`psi_spec_adj`)

which turns `alpha τ` of any walk into a telescoping sum: hence `alpha τ` of any *closed* walk in
`graph` is `0` (`alpha_closedWalk`), which makes the counting side function of a track well
defined.  The potential equation reduces, through `sideV_pos_succ`, to the two computations

* `sideV_cell`:  `sideV τ (MidV.src m) + sideV τ (MidV.tgt m) = midInd τ m` for every pattern
  point `m` — the two halves of the cell of `m` differ exactly when `m ∈ τ`;
* `sideV_plain`: `sideV τ (a, ∗) = sideV τ ((a * genE P (j,true), ∗))` for a collapsed generator
  (`L (j,true) = 0`), whose plain edge contributes nothing.

Finally `arcIndex_sideV` computes `sideV τ` on the old vertices of the boundary walk of a face in
terms of `midSum` of the visits: an old vertex of arc index `k` has value
`sigma τ c + midSum τ (faceVisits D c w) k`.  This is the input of the `RegionRel`-invariance of
`sideV τ` (`Dunwoody/RegionAlpha.lean`).

Nothing here uses the simple connectivity of `Λ''`.
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.AlphaPotential
import Submission.Work.ORDunwoody.Dunwoody.ArcPref
import Submission.Work.ORDunwoody.faceAux_eq_faceSteps
import Submission.Work.ORDunwoody.faceVisits_eq_faceAux
import Submission.Work.ORDunwoody.even_visits_defs

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

namespace Work.ORDunwoody.Dunwoody

open Work.ORDunwoody.Cayley

-- `Track D` and `MidV D` carry no decidable equality (in particular `G` has none), so the
-- classical decidability of the propositions appearing in the definitions is used locally.
attribute [local instance] Classical.propDecidable

variable {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}
variable {D : GeoData T t₀ P}

/-! ## Elementary arithmetic in `ZMod 2` -/

theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := CharTwo.add_self_eq_zero x

/-- `a + (a + t) = t` in `ZMod 2`. -/
theorem zmod2_add_add (a t : ZMod 2) : a + (a + t) = t := by
  rw [← add_assoc, zmod2_add_self a, zero_add]

/-- `(a + b) + (b + c) = a + c` in `ZMod 2`. -/
theorem zmod2_add_add_add (a b c : ZMod 2) : (a + b) + (b + c) = a + c := by
  rw [add_assoc, ← add_assoc b b c, zmod2_add_self b, zero_add]

/-- If `a + b = c` in `ZMod 2` then `a = b + c`. -/
theorem zmod2_eq_add_of_add_eq {a b c : ZMod 2} (h : a + b = c) : a = b + c := by
  rw [← h, add_comm a b, ← add_assoc, zmod2_add_self, zero_add]

/-! ## The indicator of a pattern point lying in a track -/

/-- **The indicator of `m ∈ τ`**, as an element of `ZMod 2`: the value of the cochain `phi τ` on
the *target half* of the cell of the pattern point `m` (`phi_mid_tgt`). -/
noncomputable def midInd (τ : Track D) (m : MidV D) : ZMod 2 :=
  if trackOf m = τ then 1 else 0

@[simp] theorem midInd_eq_ite (τ : Track D) (m : MidV D) :
    midInd τ m = if trackOf m = τ then 1 else 0 := rfl

/-- The cochain on the target half of the cell of `m` is the indicator `midInd τ m`. -/
theorem phi_mid_tgt_apply (τ : Track D) (m : MidV D) :
    phi τ (Sum.inr m) (Sum.inl (MidV.tgt m)) = midInd τ m :=
  phi_mid_tgt τ m

/-- The cochain on the target half of the cell of `m`, in the reverse direction. -/
theorem phi_tgt_mid_apply (τ : Track D) (m : MidV D) :
    phi τ (Sum.inl (MidV.tgt m)) (Sum.inr m) = midInd τ m :=
  phi_tgt_mid τ m

/-! ## The partial sums along a generator edge -/

/-- **The number of cells of `τ` among the first `n` cells of the generator edge `(j,true)` based
at `c`**, as an element of `ZMod 2`.  Cells beyond the end of the edge contribute `0`. -/
noncomputable def partSum (τ : Track D) (c : G) (j : Fin P.n) (n : ℕ) : ZMod 2 :=
  ∑ k ∈ Finset.range n, (if h : k < D.L (j, true) then
    midInd τ (⟨c, ⟨j, ⟨k, h⟩⟩⟩ : MidV D) else 0)

@[simp] theorem partSum_zero (τ : Track D) (c : G) (j : Fin P.n) : partSum τ c j 0 = 0 := by
  simp [partSum]

/-- The recursion of `partSum`: one further cell changes the sum by the contribution of that
cell. -/
theorem partSum_succ (τ : Track D) (c : G) (j : Fin P.n) (n : ℕ) :
    partSum τ c j (n + 1) = partSum τ c j n +
      (if h : n < D.L (j, true) then midInd τ (⟨c, ⟨j, ⟨n, h⟩⟩⟩ : MidV D) else 0) := by
  simp only [partSum, Finset.sum_range_succ]

/-! ## The sum of a function on `Fin n` computed on `finRange n` -/

theorem list_sum_finRange {n : ℕ} (f : Fin n → ZMod 2) :
    ((List.finRange n).map f).sum = ∑ i : Fin n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.finRange_succ, List.map_cons, List.sum_cons, Fin.sum_univ_succ, List.map_map]
      rw [show (f ∘ Fin.succ) = (fun i : Fin n => f i.succ) from rfl, ih]

/-! ## The contribution of the traversal of a cell -/

/-- The pattern point of a cell has the cell's source as its source end. -/
theorem mid_src_eq (e : Cell D) : MidV.src e.mid = e.src := rfl

/-- The pattern point of a cell has the cell's target as its target end. -/
theorem mid_tgt_eq (e : Cell D) : MidV.tgt e.mid = e.tgt := rfl

/-- The contribution of the forward traversal of a cell is the indicator of its pattern point. -/
theorem stepHit_fwd_cell (τ : Track D) (e : Cell D) :
    stepHit τ (DStep.fwd e) = midInd τ e.mid := by
  rw [stepHit_fwd, ← mid_tgt_eq e, phi_mid_tgt_apply]

/-- The contribution of the backward traversal of a cell is the same indicator. -/
theorem stepHit_bwd_cell (τ : Track D) (e : Cell D) :
    stepHit τ (DStep.bwd e) = midInd τ e.mid := by
  rw [stepHit_bwd, ← mid_tgt_eq e, phi_tgt_mid_apply]

/-- `A` of a single positive generator is the partial sum to the far end of its edge. -/
theorem A_single (τ : Track D) (a : G) (j : Fin P.n) :
    A τ a [(j, true)] = partSum τ a j (D.L (j, true)) := by
  unfold A
  rw [faceSteps_true, faceSteps_nil, List.append_nil]
  unfold posSteps
  by_cases h : D.L (j, true) = 0
  · rw [dif_pos h, h]
    simp [partSum]
  · rw [dif_neg h, List.map_map, list_sum_finRange, partSum, Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [dif_pos hk, dif_pos hk, Function.comp_apply, stepHit_fwd_cell]
    rfl

/-! ## The side function on the old vertices -/

/-- **The side function on the old vertices of `Λ''`**: `sigma τ` at a base point, and
`sigma τ c + partSum τ c j (i+1)` at the `i`-th interior point of the generator edge
`(j,true)` based at `c`. -/
noncomputable def sideV (τ : Track D) : BaseV D → ZMod 2
  | (c, Sum.inl ()) => sigma τ c
  | (c, Sum.inr ⟨j, i⟩) => sigma τ c + partSum τ c j (i.1 + 1)

@[simp] theorem sideV_base_eq (τ : Track D) (c : G) :
    sideV τ ((c, Sum.inl ()) : BaseV D) = sigma τ c := rfl

@[simp] theorem sideV_inner_eq (τ : Track D) (c : G) (j : Fin P.n) (i : InnerIdx D j) :
    sideV τ ((c, Sum.inr ⟨j, i⟩) : BaseV D) = sigma τ c + partSum τ c j (i.1 + 1) := rfl

/-- **The step computation of `sideV`**: traversing the `n`-th cell of a generator edge changes
`sideV` by the indicator of that cell's pattern point. -/
theorem sideV_pos_succ (τ : Track D) (c : G) (j : Fin P.n) (n : ℕ) (h : n < D.L (j, true)) :
    sideV τ (pos D c j (n + 1)) =
      sideV τ (pos D c j n) + midInd τ (⟨c, ⟨j, ⟨n, h⟩⟩⟩ : MidV D) := by
  rcases n with _ | n'
  · rw [pos_zero, sideV_base_eq]
    by_cases h1 : 0 + 1 < D.L (j, true)
    · rw [pos_succ_of_lt D c j (i := 0) h1, sideV_inner_eq, partSum_succ, partSum_zero,
        zero_add]
      congr 1
      rw [dif_pos h]
    · rw [pos_succ_of_not_lt D c j (i := 0) h1, sideV_base_eq, sigma_genE, A_single,
        congrArg (partSum τ c j) (show D.L (j, true) = 0 + 1 from by omega),
        partSum_succ, partSum_zero, zero_add]
      congr 1
      rw [dif_pos h]
  · rw [pos_succ_of_lt D c j (i := n') h, sideV_inner_eq]
    by_cases h2 : n' + 1 + 1 < D.L (j, true)
    · rw [pos_succ_of_lt D c j (i := n' + 1) h2, sideV_inner_eq, partSum_succ, ← add_assoc]
      congr 1
      rw [dif_pos h]
    · rw [pos_succ_of_not_lt D c j (i := n' + 1) h2, sideV_base_eq, sigma_genE, A_single,
        congrArg (partSum τ c j) (show D.L (j, true) = n' + 1 + 1 from by omega),
        partSum_succ, ← add_assoc]
      congr 1
      rw [dif_pos h]

/-- **The two halves of a cell differ exactly when the cell's pattern point lies in the track.** -/
theorem sideV_cell (τ : Track D) (m : MidV D) :
    sideV τ (MidV.src m) + sideV τ (MidV.tgt m) = midInd τ m := by
  obtain ⟨c, ⟨j, k⟩⟩ := m
  have hk : (k : ℕ) < D.L (j, true) := k.isLt
  have h := sideV_pos_succ τ c j (k : ℕ) hk
  have hsrc : MidV.src (⟨c, ⟨j, k⟩⟩ : MidV D) = pos D c j (k : ℕ) := rfl
  have htgt : MidV.tgt (⟨c, ⟨j, k⟩⟩ : MidV D) = pos D c j ((k : ℕ) + 1) := rfl
  rw [hsrc, htgt, h]
  exact zmod2_add_add (sideV τ (pos D c j (k : ℕ))) (midInd τ (⟨c, ⟨j, k⟩⟩ : MidV D))

/-- **A collapsed generator edge does not change the side function.** -/
theorem sideV_plain (τ : Track D) (a : G) (j : Fin P.n) (h : D.L (j, true) = 0) :
    sideV τ ((a, Sum.inl ()) : BaseV D) =
      sideV τ ((a * CayV.genE P (j, true), Sum.inl ()) : BaseV D) := by
  rw [sideV_base_eq, sideV_base_eq, sigma_genE, A_single, h, partSum_zero, add_zero]

/-! ## The potential on the vertices of the 1-skeleton -/

/-- **The potential of the counting cochain**: the side function on the old vertices, coupled with
the pattern points by `psi τ (inr m) = sideV τ (MidV.src m)`. -/
noncomputable def psi (τ : Track D) : Vertex D → ZMod 2
  | Sum.inl u => sideV τ u
  | Sum.inr m => sideV τ (MidV.src m)

@[simp] theorem psi_inl_eq (τ : Track D) (u : BaseV D) :
    psi τ (Sum.inl u) = sideV τ u := rfl

@[simp] theorem psi_inr_eq (τ : Track D) (m : MidV D) :
    psi τ (Sum.inr m) = sideV τ (MidV.src m) := rfl

/-- **The potential equation for an elementary step of the 1-skeleton.** -/
theorem psi_spec_step (τ : Track D) {v w : Vertex D} (h : StepRel v w) :
    phi τ v w = psi τ v + psi τ w := by
  rcases h with ⟨e, h1 | h1⟩ | ⟨a, j, hL, h1, h2⟩
  · rw [h1.1, h1.2, ← mid_src_eq e, phi_src_mid, psi_inl_eq, psi_inr_eq]
    exact (zmod2_add_self (sideV τ (MidV.src e.mid))).symm
  · rw [h1.1, h1.2, ← mid_tgt_eq e, phi_mid_tgt, psi_inr_eq, psi_inl_eq]
    exact (sideV_cell τ e.mid).symm
  · rw [h1, h2, phi_old_old, psi_inl_eq, psi_inl_eq, ← sideV_plain τ a j hL]
    exact (zmod2_add_self (sideV τ (a, Sum.inl ()))).symm

/-- **The potential equation for an edge of the 1-skeleton.** -/
theorem psi_spec_adj (τ : Track D) {v w : Vertex D} (h : (graph (D := D)).Adj v w) :
    phi τ v w = psi τ v + psi τ w := by
  obtain ⟨-, hstep⟩ := (graph_adj_iff (D := D) (v := v) (w := w)).1 h
  rcases hstep with hs | hs
  · exact psi_spec_step τ hs
  · rw [phi_comm, psi_spec_step τ hs, add_comm]

/-! ## The telescoping of `alpha τ` -/

/-- `alpha τ` of a list is the sum of `phi τ` over its successive pairs. -/
theorem alpha_eq_zip_sum (τ : Track D) :
    ∀ l : List (Vertex D),
      alpha τ l = ((l.zip l.tail).map (fun p : Vertex D × Vertex D => phi τ p.1 p.2)).sum
  | [] => rfl
  | [_] => rfl
  | v :: w :: rest => by
      rw [alpha_cons_cons, alpha_eq_zip_sum τ (w :: rest)]
      simp only [List.tail_cons, List.zip_cons_cons, List.map_cons, List.sum_cons]

/-- The telescoping identity: the sum of `psi p.1 + psi p.2` over the successive pairs of a list
is `psi` at the two ends. -/
theorem sum_zip_telescope (ψ : Vertex D → ZMod 2) (d : Vertex D) :
    ∀ l : List (Vertex D),
      ((l.zip l.tail).map (fun p : Vertex D × Vertex D => ψ p.1 + ψ p.2)).sum =
        ψ (l.headD d) + ψ (l.getLastD d)
  | [] => by simp [List.headD, List.getLastD, zmod2_add_self]
  | [_] => by simp [List.headD, List.getLastD, zmod2_add_self]
  | v :: w :: rest => by
      rw [List.tail_cons, List.zip_cons_cons, List.map_cons, List.sum_cons]
      have hzip : ((w :: rest).zip rest) = ((w :: rest).zip (w :: rest).tail) := rfl
      rw [hzip]
      rw [sum_zip_telescope ψ d (w :: rest)]
      simp only [List.headD_cons, List.getLastD_cons]
      exact zmod2_add_add_add (ψ v) (ψ w) (ψ (rest.getLastD w))

/-- **`alpha τ` of a walk of the 1-skeleton is the difference of the potential at its ends.** -/
theorem alpha_chain (τ : Track D) (d : Vertex D) {l : List (Vertex D)}
    (hchain : ∀ p ∈ l.zip l.tail, (graph (D := D)).Adj p.1 p.2) :
    alpha τ l = psi τ (l.headD d) + psi τ (l.getLastD d) := by
  rw [alpha_eq_zip_sum τ l]
  have h1 : (l.zip l.tail).map (fun p : Vertex D × Vertex D => phi τ p.1 p.2) =
      (l.zip l.tail).map (fun p : Vertex D × Vertex D => psi τ p.1 + psi τ p.2) :=
    List.map_congr_left (fun p hp => psi_spec_adj τ (hchain p hp))
  rw [h1]
  exact sum_zip_telescope (psi τ) d l

/-- `(ys ++ [a]).getLastD d = a`: the default is irrelevant. -/
theorem getLastD_append_singleton {α : Type u} (ys : List α) (a d : α) :
    (ys ++ [a]).getLastD d = a := by
  induction ys generalizing d with
  | nil => rfl
  | cons y ys ih => rw [List.cons_append, List.getLastD_cons]; exact ih y

/-- If `l.getLast? = some a` then `l.getLastD d = a`. -/
theorem getLastD_eq_of_getLast?_eq_some {α : Type u} {l : List α} {a d : α}
    (h : l.getLast? = some a) : l.getLastD d = a := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp h
  exact getLastD_append_singleton ys a d

/-- **`alpha τ` of a closed walk of the 1-skeleton vanishes.**  This is (W1) of
`DESIGN_N13.md` §10.3. -/
theorem alpha_closedWalk (τ : Track D) {l : List (Vertex D)}
    (hchain : ∀ p ∈ l.zip l.tail, (graph (D := D)).Adj p.1 p.2)
    (hclosed : l.head? = l.getLast?) : alpha τ l = 0 := by
  cases l with
  | nil => simp
  | cons v t =>
      have hlast : (v :: t).getLast? = some v := by
        rw [← hclosed, List.head?_cons]
      rw [alpha_chain τ v hchain, List.headD_cons,
        getLastD_eq_of_getLast?_eq_some hlast, zmod2_add_self]

/-! ## The steps of a face walk and their side values -/

/-- The number of pattern points visited by a directed step. -/
def nVisits : DStep D → ℕ
  | .fwd _ => 1
  | .bwd _ => 1
  | .skip _ _ => 0

/-- `sideV` is unchanged by a collapsed generator edge, read in either direction. -/
theorem sideV_plain' (τ : Track D) (b : G) (j : Fin P.n) (h : D.L (j, true) = 0) :
    sideV τ ((b * (CayV.genE P (j, true))⁻¹, Sum.inl ()) : BaseV D) =
      sideV τ ((b, Sum.inl ()) : BaseV D) := by
  have h' := sideV_plain τ (b * (CayV.genE P (j, true))⁻¹) j h
  rw [show (b * (CayV.genE P (j, true))⁻¹) * CayV.genE P (j, true) = b from by group] at h'
  exact h'

/-- `posSteps` satisfies the step equation of `sideV`. -/
theorem posSteps_step (τ : Track D) (a : G) (j : Fin P.n) :
    ∀ s ∈ posSteps D a j, sideV τ (DStep.tgt s) = sideV τ (DStep.src s) + stepHit τ s := by
  unfold posSteps
  by_cases h : D.L (j, true) = 0
  · rw [dif_pos h]
    intro s hs
    rw [List.mem_singleton] at hs
    subst hs
    rw [DStep.tgt_skip, DStep.src_skip, stepHit_skip, add_zero]
    exact (sideV_plain τ a j h).symm
  · rw [dif_neg h]
    intro s hs
    rw [List.mem_map] at hs
    obtain ⟨k, -, rfl⟩ := hs
    rw [DStep.tgt_fwd, DStep.src_fwd, stepHit_fwd_cell]
    exact sideV_pos_succ τ a j (k : ℕ) k.isLt

/-- `negSteps` satisfies the step equation of `sideV`. -/
theorem negSteps_step (τ : Track D) (a : G) (j : Fin P.n) :
    ∀ s ∈ negSteps D a j, sideV τ (DStep.tgt s) = sideV τ (DStep.src s) + stepHit τ s := by
  unfold negSteps
  by_cases h : D.L (j, true) = 0
  · rw [dif_pos h]
    intro s hs
    rw [List.mem_singleton] at hs
    subst hs
    rw [DStep.tgt_skip, DStep.src_skip, stepHit_skip, add_zero]
    exact sideV_plain' τ a j h
  · rw [dif_neg h]
    intro s hs
    rw [List.mem_map] at hs
    obtain ⟨k, -, rfl⟩ := hs
    rw [DStep.tgt_bwd, DStep.src_bwd, stepHit_bwd_cell]
    exact zmod2_eq_add_of_add_eq (sideV_cell τ (⟨_, j, k⟩ : Cell D).mid)

/-- `faceSteps` satisfies the step equation of `sideV`. -/
theorem faceSteps_step (τ : Track D) (c : G) (w : List (Fin P.n × Bool)) :
    ∀ s ∈ faceSteps D c w, sideV τ (DStep.tgt s) = sideV τ (DStep.src s) + stepHit τ s := by
  induction w generalizing c with
  | nil => simp
  | cons x w ih =>
      obtain ⟨j, b⟩ := x
      cases b with
      | true =>
          rw [faceSteps_true]
          intro s hs
          rw [List.mem_append] at hs
          rcases hs with hs | hs
          · exact posSteps_step τ c j s hs
          · exact ih (c * CayV.genE P (j, true)) s hs
      | false =>
          rw [faceSteps_false]
          intro s hs
          rw [List.mem_append] at hs
          rcases hs with hs | hs
          · exact negSteps_step τ c j s hs
          · exact ih (c * (CayV.genE P (j, true))⁻¹) s hs

/-- The steps of a face walk form a chain, and the walk starts at the base point. -/
theorem faceSteps_chain (D : GeoData T t₀ P) (c : G) (w : List (Fin P.n × Bool)) :
    (faceSteps D c w).IsChain (fun s s' => DStep.tgt s = DStep.src s') ∧
    (∀ s, (faceSteps D c w).head? = some s → DStep.src s = (c, Sum.inl ())) := by
  induction w generalizing c with
  | nil => exact ⟨List.isChain_nil, by simp⟩
  | cons x w ih =>
      obtain ⟨j, b⟩ := x
      cases b with
      | true =>
          obtain ⟨hch, hhd⟩ := ih (c * CayV.genE P (j, true))
          obtain ⟨Aha, Alg, Ach, Ane⟩ := posSteps_facts (D := D) c j
          refine ⟨?_, ?_⟩
          · rw [faceSteps_true, List.isChain_append]
            exact ⟨Ach, hch, fun x' hx' y' hy' => by rw [Alg x' hx', hhd y' hy']⟩
          · intro s hs
            rw [faceSteps_true, List.head?_append_of_ne_nil _ Ane] at hs
            exact Aha s hs
      | false =>
          obtain ⟨hch, hhd⟩ := ih (c * (CayV.genE P (j, true))⁻¹)
          obtain ⟨Aha, Alg, Ach, Ane⟩ := negSteps_facts (D := D) c j
          refine ⟨?_, ?_⟩
          · rw [faceSteps_false, List.isChain_append]
            exact ⟨Ach, hch, fun x' hx' y' hy' => by rw [Alg x' hx', hhd y' hy']⟩
          · intro s hs
            rw [faceSteps_false, List.head?_append_of_ne_nil _ Ane] at hs
            exact Aha s hs

/-- The visits of the steps of a face walk are the visits of the face. -/
theorem filterMap_mid?_faceSteps (c : G) (w : List (Fin P.n × Bool)) :
    (faceSteps D c w).filterMap DStep.mid? = faceVisits D c w := by
  rw [faceVisits_eq_faceAux, faceAux_eq_faceSteps]

/-! ## The accumulated side value and arc index along a face walk -/

/-- The data accumulated along a list of directed steps: for every step, the target old vertex,
its arc index (the number of pattern points seen so far) and the current value of `sideV`. -/
noncomputable def stepData (τ : Track D) :
    List (DStep D) → ℕ → ZMod 2 → List (BaseV D × ℕ × ZMod 2)
  | [], _, _ => []
  | DStep.fwd e :: rest, k, d =>
      (e.tgt, k + 1, d + stepHit τ (DStep.fwd e)) ::
        stepData τ rest (k + 1) (d + stepHit τ (DStep.fwd e))
  | DStep.bwd e :: rest, k, d =>
      (e.src, k + 1, d + stepHit τ (DStep.bwd e)) ::
        stepData τ rest (k + 1) (d + stepHit τ (DStep.bwd e))
  | DStep.skip u w :: rest, k, d =>
      (w, k, d) :: stepData τ rest k d

@[simp] theorem stepData_nil (τ : Track D) (k : ℕ) (d : ZMod 2) : stepData τ [] k d = [] := rfl

@[simp] theorem stepData_fwd_eq (τ : Track D) (e : Cell D) (rest : List (DStep D)) (k : ℕ)
    (d : ZMod 2) :
    stepData τ (DStep.fwd e :: rest) k d =
      (e.tgt, k + 1, d + stepHit τ (DStep.fwd e)) ::
        stepData τ rest (k + 1) (d + stepHit τ (DStep.fwd e)) := rfl

@[simp] theorem stepData_bwd_eq (τ : Track D) (e : Cell D) (rest : List (DStep D)) (k : ℕ)
    (d : ZMod 2) :
    stepData τ (DStep.bwd e :: rest) k d =
      (e.src, k + 1, d + stepHit τ (DStep.bwd e)) ::
        stepData τ rest (k + 1) (d + stepHit τ (DStep.bwd e)) := rfl

@[simp] theorem stepData_skip_eq (τ : Track D) (u w : BaseV D) (rest : List (DStep D)) (k : ℕ)
    (d : ZMod 2) :
    stepData τ (DStep.skip u w :: rest) k d = (w, k, d) :: stepData τ rest k d := rfl

theorem stepData_cons (τ : Track D) (s : DStep D) (rest : List (DStep D)) (k : ℕ) (d : ZMod 2) :
    stepData τ (s :: rest) k d =
      (DStep.tgt s, k + nVisits s, d + stepHit τ s) ::
        stepData τ rest (k + nVisits s) (d + stepHit τ s) := by
  cases s with
  | fwd e => rfl
  | bwd e => rfl
  | skip u w => rw [stepData_skip_eq]; simp [nVisits]

@[simp] theorem filterMap_mid?_fwd (e : Cell D) (rest : List (DStep D)) :
    (DStep.fwd e :: rest).filterMap DStep.mid? = e.mid :: rest.filterMap DStep.mid? := by
  simp [List.filterMap_cons]

@[simp] theorem filterMap_mid?_bwd (e : Cell D) (rest : List (DStep D)) :
    (DStep.bwd e :: rest).filterMap DStep.mid? = e.mid :: rest.filterMap DStep.mid? := by
  simp [List.filterMap_cons]

@[simp] theorem filterMap_mid?_skip (u w : BaseV D) (rest : List (DStep D)) :
    (DStep.skip u w :: rest).filterMap DStep.mid? = rest.filterMap DStep.mid? := by
  simp [List.filterMap_cons]

/-- `arcIndexAux` over the vertex lists of the steps of a walk. -/
theorem arcIndexAux_flatMap_cons (s : DStep D) (rest : List (DStep D)) (k : ℕ) :
    arcIndexAux ((s :: rest).flatMap DStep.verts) k =
      (DStep.tgt s, k + nVisits s) :: arcIndexAux (rest.flatMap DStep.verts)
        (k + nVisits s) := by
  cases s with
  | fwd e =>
      rw [List.flatMap_cons]
      simp only [DStep.verts_fwd, DStep.tgt_fwd, nVisits, List.cons_append, List.nil_append,
        arcIndexAux_inr, arcIndexAux_inl]
  | bwd e =>
      rw [List.flatMap_cons]
      simp only [DStep.verts_bwd, DStep.tgt_bwd, nVisits, List.cons_append, List.nil_append,
        arcIndexAux_inr, arcIndexAux_inl]
  | skip u w =>
      rw [List.flatMap_cons]
      simp only [DStep.verts_skip, DStep.tgt_skip, nVisits, List.singleton_append, Nat.add_zero,
        arcIndexAux_inl]

/-- The values recorded by `stepData` are the values of the side function. -/
theorem stepData_sideV (τ : Track D) (ss : List (DStep D)) (k : ℕ) (d : ZMod 2)
    (hchain : ss.IsChain (fun s s' => DStep.tgt s = DStep.src s'))
    (hhead : ∀ s, ss.head? = some s → d = sideV τ (DStep.src s))
    (hstep : ∀ s ∈ ss, sideV τ (DStep.tgt s) = sideV τ (DStep.src s) + stepHit τ s)
    (u : BaseV D) (j : ℕ) (a : ZMod 2) (hmem : (u, j, a) ∈ stepData τ ss k d) :
    sideV τ u = a := by
  induction ss generalizing k d with
  | nil => simp at hmem
  | cons s rest ih =>
      rw [stepData_cons, List.mem_cons, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
      · rw [hhead s (by simp)]
        exact hstep s (by simp)
      · refine ih (k + nVisits s) (d + stepHit τ s) ?_ ?_ ?_ hmem
        · exact (List.isChain_cons.mp hchain).2
        · intro s' hs'
          have h1 := (List.isChain_cons.mp hchain).1 s' hs'
          have h2 := hhead s (by simp)
          have h3 := hstep s (by simp)
          rw [← h1, h3, ← h2]
        · intro s' hs'
          exact hstep s' (List.mem_cons_of_mem _ hs')

/-- The arc indices recorded by `stepData` are the arc indices of the vertex list. -/
theorem stepData_arcIndex (τ : Track D) (ss : List (DStep D)) (k : ℕ) (d : ZMod 2) :
    arcIndexAux (ss.flatMap DStep.verts) k =
      (stepData τ ss k d).map (fun p : BaseV D × ℕ × ZMod 2 => (p.1, p.2.1)) := by
  induction ss generalizing k d with
  | nil => rfl
  | cons s rest ih =>
      rw [stepData_cons, arcIndexAux_flatMap_cons, List.map_cons]
      show (DStep.tgt s, k + nVisits s) :: arcIndexAux (rest.flatMap DStep.verts)
          (k + nVisits s) =
        (DStep.tgt s, k + nVisits s) ::
          (stepData τ rest (k + nVisits s) (d + stepHit τ s)).map
            (fun p : BaseV D × ℕ × ZMod 2 => (p.1, p.2.1))
      rw [ih (k + nVisits s) (d + stepHit τ s)]

/-! ## `midSum` of the visits of a face walk -/

theorem midSum_eq (τ : Track D) (vs : List (MidV D)) (k : ℕ) :
    midSum τ vs k = ((vs.take k).map (midInd τ)).sum := rfl

theorem midSum_succ_cons (τ : Track D) (v : MidV D) (vs : List (MidV D)) (k : ℕ) :
    midSum τ (v :: vs) (k + 1) = midInd τ v + midSum τ vs k := by
  rw [midSum_eq, midSum_eq, List.take_succ_cons, List.map_cons, List.sum_cons]

theorem midSum_drop_head (τ : Track D) (vs : List (MidV D)) (k : ℕ) (m : MidV D)
    (vs' : List (MidV D)) (h : vs.drop k = m :: vs') :
    midSum τ vs (k + 1) = midSum τ vs k + midInd τ m := by
  induction vs generalizing k with
  | nil => simp at h
  | cons v vs ih =>
      rcases k with _ | k
      · simp only [List.drop_zero, List.cons.injEq] at h
        obtain ⟨rfl, -⟩ := h
        rw [midSum_succ_cons]
        simp
      · rw [midSum_succ_cons, midSum_succ_cons, ih k h, add_assoc]

/-- The accumulated visit sum after a step. -/
theorem midSum_step (τ : Track D) {vs : List (MidV D)} {k : ℕ} {s : DStep D}
    {rest : List (DStep D)} (hvs : vs.drop k = (s :: rest).filterMap DStep.mid?) :
    midSum τ vs (k + nVisits s) = midSum τ vs k + stepHit τ s := by
  cases s with
  | fwd e =>
      rw [filterMap_mid?_fwd] at hvs
      show midSum τ vs (k + 1) = midSum τ vs k + stepHit τ (DStep.fwd e)
      rw [midSum_drop_head τ vs k e.mid _ hvs, stepHit_fwd_cell]
  | bwd e =>
      rw [filterMap_mid?_bwd] at hvs
      show midSum τ vs (k + 1) = midSum τ vs k + stepHit τ (DStep.bwd e)
      rw [midSum_drop_head τ vs k e.mid _ hvs, stepHit_bwd_cell]
  | skip u w =>
      rw [filterMap_mid?_skip] at hvs
      show midSum τ vs k = midSum τ vs k + stepHit τ (DStep.skip u w)
      rw [stepHit_skip, add_zero]

/-- The visits remaining after a step. -/
theorem drop_step {vs : List (MidV D)} {k : ℕ} {s : DStep D} {rest : List (DStep D)}
    (hvs : vs.drop k = (s :: rest).filterMap DStep.mid?) :
    vs.drop (k + nVisits s) = rest.filterMap DStep.mid? := by
  cases s with
  | fwd e =>
      rw [filterMap_mid?_fwd] at hvs
      show vs.drop (k + 1) = rest.filterMap DStep.mid?
      rw [← List.drop_drop (i := 1) (j := k) (l := vs), hvs]
      simp
  | bwd e =>
      rw [filterMap_mid?_bwd] at hvs
      show vs.drop (k + 1) = rest.filterMap DStep.mid?
      rw [← List.drop_drop (i := 1) (j := k) (l := vs), hvs]
      simp
  | skip u w =>
      rw [filterMap_mid?_skip] at hvs
      exact hvs

/-- The values recorded by `stepData` are `sigma τ c` plus `midSum` of the visits. -/
theorem stepData_midSum (τ : Track D) (ss : List (DStep D)) (k : ℕ) (d : ZMod 2)
    (vs : List (MidV D)) (c : G)
    (hvs : vs.drop k = ss.filterMap DStep.mid?)
    (hd : d = sigma τ c + midSum τ vs k)
    (u : BaseV D) (j : ℕ) (a : ZMod 2) (hmem : (u, j, a) ∈ stepData τ ss k d) :
    a = sigma τ c + midSum τ vs j := by
  induction ss generalizing k d vs with
  | nil => simp at hmem
  | cons s rest ih =>
      rw [stepData_cons, List.mem_cons, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
      · rw [hd, midSum_step τ hvs, add_assoc]
      · have hd' : d + stepHit τ s = sigma τ c + midSum τ vs (k + nVisits s) := by
          rw [hd, midSum_step τ hvs, add_assoc]
        exact ih (k + nVisits s) (d + stepHit τ s) vs (drop_step hvs) hd' hmem

/-- **The value of the side function at an old vertex of a face walk, in terms of its arc
index**: an old vertex with `k` pattern points before it has value
`sigma τ c + midSum τ (faceVisits D c w) k`. -/
theorem arcIndex_sideV (τ : Track D) (c : G) (w : List (Fin P.n × Bool))
    {u : BaseV D} {j : ℕ} (hmem : (u, j) ∈ arcIndex (faceWalk D c w)) :
    sideV τ u = sigma τ c + midSum τ (faceVisits D c w) j := by
  rw [arcIndex, faceWalk_eq, arcIndexAux_inl, List.mem_cons, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | hmem
  · rw [sideV_base_eq, midSum_zero, add_zero]
  · rw [faceAux_eq_flatMap_verts, stepData_arcIndex] at hmem
    obtain ⟨⟨u', j', a'⟩, hp, hpj⟩ := List.mem_map.mp hmem
    simp only [Prod.mk.injEq] at hpj
    obtain ⟨rfl, rfl⟩ := hpj
    refine (stepData_sideV τ (faceSteps D c w) 0 (sigma τ c) ?_ ?_ ?_ u' j' a' hp).trans
      (stepData_midSum τ (faceSteps D c w) 0 (sigma τ c) (faceVisits D c w) c ?_ ?_
        u' j' a' hp)
    · exact (faceSteps_chain (D := D) c w).1
    · intro s hs
      rw [(faceSteps_chain (D := D) c w).2 s hs]
      rfl
    · exact faceSteps_step τ c w
    · rw [List.drop_zero, filterMap_mid?_faceSteps]
    · rw [midSum_zero, add_zero]

end Work.ORDunwoody.Dunwoody
