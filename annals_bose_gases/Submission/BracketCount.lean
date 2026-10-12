import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Submission.BoxLocalize
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Cell occupation counts and the all-particle localization identity

The bracket lower bound on `boxEnergy` needs a *finite* object expressing "how
many particles sit in each cell".  For a general (not necessarily symmetric)
wavefunction this is resolved by **tensor localization**, not by any symmetry
assumption: the identity

    Σ_a ∏_{i} χ_{a_i}(x_i)² = 1        (sum over assignments a : Fin N → cells)

decomposes a state `Ψ` into pieces `Ψ_a := (∏_i χ_{a_i}(x_i))·Ψ`, and each piece
has a *deterministic* assignment `a` with occupation numbers
`n_j(a) := #{i | a_i = j}` satisfying `Σ_j n_j(a) = N`.  No bosonic symmetry of
`Ψ` is needed: the assignment is a property of the localized piece, not an
observable of `Ψ`.

This module defines that finite object (using the cell cutoffs `cellCut` of
`Submission.CellGrid` and the concrete profile `rhoProfile` of
`Submission.Profile`) and proves:

  * `Assign m N` — the type of assignments (each of the `N` particles to a cell);
  * `cellCount` — the occupation number of a cell under an assignment, with
    `cellCount_sum`: `Σ_j n_j(a) = N` (the cell data sums to `N`);
  * `cellAssignCut` — the tensor cutoff of an assignment, with
    `cellAssignCut_pu`: the tensor partition of unity on `box N (m·ℓ)`;
  * `ims_tensor_identity` — the all-particle IMS identity (localizing *all*
    `N` particles at once), whose error density is
    `Ψ²·Σ_i Σ_c Σ_k (∂ₖχ_c(xᵢ))²`;
  * `tensorLocalize_kinetic_le` — the all-particle localization bound:
    localizing all particles into the `m³` cells costs at most
    `N·(6A²/ℓ²)·∫Ψ²`.

This is the finite skeleton on which the bracket lower bound
`⟪Ψ,𝓗Ψ⟫ ≥ Σ_a Σ_j eNeu (n_j(a)) ℓ ·‖piece‖² − error` (via Neumann cell
energies) will be built.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

local notation "⟪" f ", " g "⟫_["N "," L"]" => ∫ x in box N L, f x * g x

/-- An assignment of the `N` particles to the cells of the `m`-grid. -/
abbrev Assign (m N : ℕ) := Fin N → CellIdx m

/-- The occupation number of the cell `j` under the assignment `a`: the number
of particles assigned to `j`. -/
def cellCount {m N : ℕ} (a : Assign m N) (j : CellIdx m) : ℕ :=
  (Finset.univ.filter (fun i : Fin N => a i = j)).card

/-- The occupation numbers are nonnegative (trivial) and each is at most `N`. -/
lemma cellCount_le {m N : ℕ} (a : Assign m N) (j : CellIdx m) :
    cellCount a j ≤ N := by
  unfold cellCount
  have hsub : (Finset.univ.filter (fun i : Fin N => a i = j)) ⊆ Finset.univ :=
    Finset.filter_subset _ _
  have hle := Finset.card_le_card hsub
  simpa using hle

/-- **The occupation numbers sum to the particle number**: `Σ_j n_j(a) = N`. -/
lemma cellCount_sum {m N : ℕ} (a : Assign m N) :
    (∑ j : CellIdx m, cellCount a j) = N := by
  classical
  have hcc : ∀ j : CellIdx m, cellCount a j =
      (∑ i : Fin N, if a i = j then (1 : ℕ) else 0) := by
    intro j
    unfold cellCount
    rw [Finset.card_filter]
  calc
    (∑ j : CellIdx m, cellCount a j)
        = ∑ j : CellIdx m, (∑ i : Fin N, if a i = j then (1 : ℕ) else 0) := by
          exact Finset.sum_congr rfl (fun j hj => hcc j)
    _ = ∑ i : Fin N, (∑ j : CellIdx m, if a i = j then (1 : ℕ) else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ i : Fin N, 1 := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          simpa using (Fintype.sum_ite_eq (a i) (fun _ : CellIdx m => (1 : ℕ)))
    _ = N := by
          simp

/-- The tensor cutoff of an assignment: `χ_a(x) := ∏_i χ_{a_i}(x_i)`. -/
noncomputable def cellAssignCut (ℓ : ℝ) (m N : ℕ) (a : Assign m N) (x : X N) : ℝ :=
  ∏ i : Fin N, cellCut ℓ m (a i) (x i)

/-- The square of a finite product of reals is the product of the squares. -/
lemma sq_prod_eq_prod_sq {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∏ i, f i) ^ 2 = ∏ i, (f i) ^ 2 := by
  rw [pow_two]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [pow_two]

/-- The tensor partition of unity on the box: `Σ_a χ_a(x)² = 1` for
`x ∈ box N (m·ℓ)`. -/
lemma cellAssignCut_pu {ℓ : ℝ} (hℓ : 0 < ℓ) (m N : ℕ) {x : X N}
    (hx : x ∈ box N ((m : ℝ) * ℓ)) :
    (∑ a : Assign m N, (cellAssignCut ℓ m N a x) ^ 2) = 1 := by
  classical
  have hpi : ∀ i : Fin N, (∑ c : CellIdx m, (cellCut ℓ m c (x i)) ^ 2) = 1 := by
    intro i
    apply cellCut_pu hℓ m
    intro k
    exact hx i k
  have hsq : ∀ a : Assign m N, (cellAssignCut ℓ m N a x) ^ 2 =
      ∏ i : Fin N, (cellCut ℓ m (a i) (x i)) ^ 2 := by
    intro a
    unfold cellAssignCut
    exact sq_prod_eq_prod_sq (fun i : Fin N => cellCut ℓ m (a i) (x i))
  calc
    (∑ a : Assign m N, (cellAssignCut ℓ m N a x) ^ 2)
        = ∑ a : Assign m N, ∏ i : Fin N, (cellCut ℓ m (a i) (x i)) ^ 2 := by
          exact Finset.sum_congr rfl (fun a ha => hsq a)
    _ = ∏ i : Fin N, ∑ c : CellIdx m, (cellCut ℓ m c (x i)) ^ 2 := by
          rw [← Fintype.prod_sum (ι := Fin N) (κ := fun _ : Fin N => CellIdx m)
            (f := fun i : Fin N => fun c : CellIdx m => (cellCut ℓ m c (x i)) ^ 2)]
    _ = 1 := by
          simp [hpi]

lemma prod_all_eq_mul_erase {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (i : ι) :
    (∏ j : ι, f j) = f i * (Finset.univ.erase i).prod f := by
  rw [← Finset.prod_erase_mul (s := Finset.univ) f (a := i) (by simp)]
  rw [mul_comm]

lemma cellAssignCut_eq {ℓ : ℝ} (m N : ℕ) (a : Assign m N) (i : Fin N) (y : X N) :
    cellAssignCut ℓ m N a y =
      cellCut ℓ m (a i) (y i) * (Finset.univ.erase i).prod (fun j => cellCut ℓ m (a j) (y j)) := by
  unfold cellAssignCut
  rw [prod_all_eq_mul_erase (fun j : Fin N => cellCut ℓ m (a j) (y j)) i]

/-- Sum over assignments of a product that at index i equals q, elsewhere p. -/
lemma assign_sum_fiber' {ι C : Type*} [Fintype ι] [DecidableEq ι] [Fintype C] [DecidableEq C]
    (i : ι) (q : C → ℝ) (p : ι → C → ℝ) :
    (∑ a : ι → C, q (a i) * (Finset.univ.erase i).prod (fun j => p j (a j))) =
      (∑ c : C, q c) * (Finset.univ.erase i).prod (fun j => ∑ c : C, p j c) := by
  classical
  calc
    (∑ a : ι → C, q (a i) * (Finset.univ.erase i).prod (fun j => p j (a j)))
        = ∑ a : ι → C, (∏ j : ι, (if j = i then q (a j) else p j (a j))) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [prod_all_eq_mul_erase (fun j : ι => if j = i then q (a j) else p j (a j)) i]
          congr 1
          · simp
          · apply Finset.prod_congr rfl
            intro j hj
            have hji : j ≠ i := (Finset.mem_erase.mp hj).1
            simp [hji]
    _ = ∏ j : ι, ∑ c : C, (if j = i then q c else p j c) := by
          rw [Fintype.prod_sum]
    _ = (∑ c : C, q c) * (Finset.univ.erase i).prod (fun j => ∑ c : C, p j c) := by
          rw [prod_all_eq_mul_erase (fun j : ι => ∑ c : C, (if j = i then q c else p j c)) i]
          congr 1
          · simp
          · apply Finset.prod_congr rfl
            intro j hj
            have hji : j ≠ i := (Finset.mem_erase.mp hj).1
            simp [hji]

-- ContDiff of the assignment cutoff as a function of y
lemma cellAssignCut_contDiff (ℓ : ℝ) (m N : ℕ) (a : Assign m N) :
    ContDiff ℝ ∞ (fun y : X N => cellAssignCut ℓ m N a y) := by
  have hper : ∀ j : Fin N, ContDiff ℝ ∞ (fun y : X N => cellCut ℓ m (a j) (y j)) := by
    intro j
    have hpi : ContDiff ℝ ∞ (fun y : X N => y j) := by
      simpa using (contDiff_apply ℝ (EuclideanSpace ℝ (Fin 3)) (n := ∞) (ι := Fin N) j)
    exact (cellCut_contDiff ℓ m (a j)).comp hpi
  -- hmm: contDiff_prod gives ContDiff (fun y => ∏ i ∈ t, f i y) over the finset t
  unfold cellAssignCut
  -- rewrite the type-level product to a membership product over univ
  have h := contDiff_prod (𝕜 := ℝ) (n := ∞) (t := Finset.univ)
    (f := fun j : Fin N => fun y : X N => cellCut ℓ m (a j) (y j)) (by intro j hj; exact hper j)
  simpa using h


-- the direction kcDir N i k moves only coordinate i
lemma kcDir_eq_update (N : ℕ) (i : Fin N) (k : Fin 3) :
    kcDir N i k = Function.update (0 : X N) i (kcStdBasis k) := by
  rfl

lemma kcDir_apply_ne {N : ℕ} (i : Fin N) (k : Fin 3) {j : Fin N} (hji : j ≠ i) :
    (kcDir N i k) j = 0 := by
  rw [kcDir_eq_update, Function.update_of_ne hji (kcStdBasis k) (0 : X N)]
  simp

lemma kcDir_apply_eq {N : ℕ} (i : Fin N) (k : Fin 3) :
    (kcDir N i k) i = kcStdBasis k := by
  rw [kcDir_eq_update]
  simp

-- constancy of a product over particles other than i along the i-direction
lemma erase_prod_const_along {N m : ℕ} {ℓ : ℝ} (a : Assign m N) (i : Fin N) (k : Fin 3) (x : X N) :
    (fun t : ℝ => (Finset.univ.erase i).prod (fun j => cellCut ℓ m (a j) ((x + t • kcDir N i k) j))) =
      fun _ : ℝ => (Finset.univ.erase i).prod (fun j => cellCut ℓ m (a j) (x j)) := by
  funext t
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  congr 1
  -- (x + t • kcDir N i k) j = x j
  simp [kcDir_apply_ne i k (j := j) hji]

-- derivative along the i-direction of a product over the other particles is zero
lemma erase_prod_fderiv_zero {N m : ℕ} {ℓ : ℝ} (a : Assign m N) (i : Fin N) (k : Fin 3) (x : X N) :
    fderiv ℝ (fun y : X N => (Finset.univ.erase i).prod (fun j => cellCut ℓ m (a j) (y j))) x
      (kcDir N i k) = 0 := by
  have hΦ : ContDiff ℝ ∞ (fun y : X N =>
      (Finset.univ.erase i).prod (fun j => cellCut ℓ m (a j) (y j))) := by
    have hper : ∀ j : Fin N, ContDiff ℝ ∞ (fun y : X N => cellCut ℓ m (a j) (y j)) := by
      intro j
      have hpi : ContDiff ℝ ∞ (fun y : X N => y j) := by
        simpa using (contDiff_apply ℝ (EuclideanSpace ℝ (Fin 3)) (n := ∞) (ι := Fin N) j)
      exact (cellCut_contDiff ℓ m (a j)).comp hpi
    have h := contDiff_prod (𝕜 := ℝ) (n := ∞) (t := Finset.univ.erase i)
      (f := fun j : Fin N => fun y : X N => cellCut ℓ m (a j) (y j)) (by intro j hj; exact hper j)
    simpa using h
  have hdiff : DifferentiableAt ℝ (fun y : X N =>
      (Finset.univ.erase i).prod (fun j => cellCut ℓ m (a j) (y j))) x := by
    exact hΦ.differentiable (by norm_num : (∞ : ℕ∞ω) ≠ 0) x
  calc
    fderiv ℝ (fun y : X N => (Finset.univ.erase i).prod (fun j => cellCut ℓ m (a j) (y j))) x
        (kcDir N i k)
        = lineDeriv ℝ (fun y : X N => (Finset.univ.erase i).prod (fun j => cellCut ℓ m (a j) (y j)))
            x (kcDir N i k) := by
          exact (DifferentiableAt.lineDeriv_eq_fderiv hdiff).symm
    _ = deriv (fun t : ℝ => (Finset.univ.erase i).prod
          (fun j => cellCut ℓ m (a j) ((x + t • kcDir N i k) j))) 0 := by
          rfl
    _ = deriv (fun _ : ℝ => (Finset.univ.erase i).prod
          (fun j => cellCut ℓ m (a j) (x j))) 0 := by
          rw [erase_prod_const_along a i k x]
    _ = 0 := by
          simp

-- derivative of a piece: localising factor w.r.t. particle i sees only the i-th factor
lemma piece_deriv {N m : ℕ} {ℓ : ℝ} (a : Assign m N) (i : Fin N) (k : Fin 3)
    {f : X N → ℝ} (hf : ContDiff ℝ ∞ f) (x : X N) :
    fderiv ℝ (fun y : X N => cellAssignCut ℓ m N a y * f y) x (kcDir N i k) =
      (Finset.univ.erase i).prod (fun j => cellCut ℓ m (a j) (x j)) *
        fderiv ℝ (fun y : X N => cellCut ℓ m (a i) (y i) * f y) x (kcDir N i k) := by
  let Φ : X N → ℝ := fun y => (Finset.univ.erase i).prod (fun j => cellCut ℓ m (a j) (y j))
  let Q : X N → ℝ := fun y => cellCut ℓ m (a i) (y i) * f y
  let v : X N := kcDir N i k
  have hfun : (fun y : X N => cellAssignCut ℓ m N a y * f y) = fun y : X N => Φ y * Q y := by
    funext y
    dsimp [Φ, Q]
    rw [cellAssignCut_eq]
    ring
  have hΦc : ContDiff ℝ ∞ Φ := by
    dsimp [Φ]
    have hper : ∀ j : Fin N, ContDiff ℝ ∞ (fun y : X N => cellCut ℓ m (a j) (y j)) := by
      intro j
      have hpi : ContDiff ℝ ∞ (fun y : X N => y j) := by
        simpa using (contDiff_apply ℝ (EuclideanSpace ℝ (Fin 3)) (n := ∞) (ι := Fin N) j)
      exact (cellCut_contDiff ℓ m (a j)).comp hpi
    have h := contDiff_prod (𝕜 := ℝ) (n := ∞) (t := Finset.univ.erase i)
      (f := fun j : Fin N => fun y : X N => cellCut ℓ m (a j) (y j)) (by intro j hj; exact hper j)
    simpa using h
  have hQc : ContDiff ℝ ∞ Q := by
    dsimp [Q]
    have hpi : ContDiff ℝ ∞ (fun y : X N => y i) := by
      simpa using (contDiff_apply ℝ (EuclideanSpace ℝ (Fin 3)) (n := ∞) (ι := Fin N) i)
    exact (cellCut_contDiff ℓ m (a i)).comp hpi |>.mul hf
  have hdiffΦ : DifferentiableAt ℝ Φ x := hΦc.differentiable (by norm_num : (∞ : ℕ∞ω) ≠ 0) x
  have hdiffQ : DifferentiableAt ℝ Q x := hQc.differentiable (by norm_num : (∞ : ℕ∞ω) ≠ 0) x
  have hΦ0 : fderiv ℝ Φ x v = 0 := by
    dsimp [Φ, v]
    exact erase_prod_fderiv_zero a i k x
  calc
    fderiv ℝ (fun y : X N => cellAssignCut ℓ m N a y * f y) x v
        = fderiv ℝ (fun y : X N => Φ y * Q y) x v := by rw [hfun]
    _ = Φ x * fderiv ℝ Q x v + Q x * fderiv ℝ Φ x v := by
          have hm := fderiv_mul hdiffΦ hdiffQ
          change (fderiv ℝ (Φ * Q) x) v = Φ x * fderiv ℝ Q x v + Q x * fderiv ℝ Φ x v
          rw [hm]
          simp [mul_add, add_mul]
    _ = Φ x * fderiv ℝ Q x v := by rw [hΦ0]; ring
    _ = (Finset.univ.erase i).prod (fun j => cellCut ℓ m (a j) (x j)) *
          fderiv ℝ (fun y : X N => cellCut ℓ m (a i) (y i) * f y) x (kcDir N i k) := by
          dsimp [Φ, Q, v]

lemma finset_prod_sq {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (s.prod f) ^ 2 = s.prod (fun j => (f j) ^ 2) := by
  rw [pow_two, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  rw [pow_two]

lemma cellCut_pu_particle {ℓ : ℝ} (hℓ : 0 < ℓ) (m N : ℕ) {x : X N}
    (hx : x ∈ box N ((m : ℝ) * ℓ)) (j : Fin N) :
    (∑ c : CellIdx m, (cellCut ℓ m c (x j)) ^ 2) = 1 := by
  apply cellCut_pu hℓ m
  intro k
  exact ⟨(hx j k).1, (hx j k).2⟩

/-- The sum over all assignments of the localised kinetic of particle `i`
collapses to the single-cell sum: the other particles' factors form a
partition of unity.  Pointwise version. -/
lemma tensor_collapse_pointwise {N m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) (k : Fin 3)
    {f : X N → ℝ} (hf : ContDiff ℝ ∞ f) {x : X N}
    (hx : x ∈ box N ((m : ℝ) * ℓ)) :
    (∑ a : Assign m N, (fderiv ℝ (fun y : X N => cellAssignCut ℓ m N a y * f y) x (kcDir N i k)) ^ 2) =
      ∑ c : CellIdx m, (fderiv ℝ (fun y : X N => cellCut ℓ m c (y i) * f y) x (kcDir N i k)) ^ 2 := by
  classical
  let D : CellIdx m → ℝ := fun c => (fderiv ℝ (fun y : X N => cellCut ℓ m c (y i) * f y) x (kcDir N i k)) ^ 2
  calc
    (∑ a : Assign m N, (fderiv ℝ (fun y : X N => cellAssignCut ℓ m N a y * f y) x (kcDir N i k)) ^ 2)
        = ∑ a : Assign m N, D (a i) * (Finset.univ.erase i).prod
            (fun j => (cellCut ℓ m (a j) (x j)) ^ 2) := by
          apply Finset.sum_congr rfl
          intro a ha
          dsimp [D]
          rw [piece_deriv a i k hf x]
          have hmul (P fd : ℝ) : (P * fd) ^ 2 = fd ^ 2 * P ^ 2 := by ring
          rw [hmul]
          rw [finset_prod_sq (s := Finset.univ.erase i) (fun j => cellCut ℓ m (a j) (x j))]
    _ = (∑ c : CellIdx m, D c) * (Finset.univ.erase i).prod
          (fun j => ∑ c : CellIdx m, (cellCut ℓ m c (x j)) ^ 2) := by
          exact assign_sum_fiber' (ι := Fin N) (C := CellIdx m) i D
            (fun j => fun c : CellIdx m => (cellCut ℓ m c (x j)) ^ 2)
    _ = ∑ c : CellIdx m, D c := by
          have hpu : (Finset.univ.erase i).prod
              (fun j => ∑ c : CellIdx m, (cellCut ℓ m c (x j)) ^ 2) = 1 := by
            apply Finset.prod_eq_one
            intro j hj
            exact cellCut_pu_particle hℓ m N (x := x) hx j
          rw [hpu]
          ring
    _ = ∑ c : CellIdx m, (fderiv ℝ (fun y : X N => cellCut ℓ m c (y i) * f y) x (kcDir N i k)) ^ 2 := by
          dsimp [D]

/-- A continuous function is integrable on the compact box `box N L` when `L > 0`. -/
lemma cont_integrableOn_box {N : ℕ} {L : ℝ} (hL : 0 < L) {g : X N → ℝ} (hg : Continuous g) :
    IntegrableOn g (box N L) volume := by
  exact hg.continuousOn.integrableOn_compact (box_compact hL)

/-- Interchanging a finite sum over indices and the integral, when the summed
functions are pointwise equal on the box. -/
lemma sum_integral_eq {N : ℕ} {L : ℝ} (hL : 0 < L) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : ι → X N → ℝ) (F : κ → X N → ℝ)
    (hGcont : ∀ a : ι, Continuous (G a)) (hFcont : ∀ c : κ, Continuous (F c))
    (hpt : ∀ x : X N, x ∈ box N L → (∑ a : ι, G a x) = ∑ c : κ, F c x) :
    (∑ a : ι, ∫ x in box N L, G a x) = ∑ c : κ, ∫ x in box N L, F c x := by
  have hI_G : ∀ a : ι, IntegrableOn (G a) (box N L) volume := fun a =>
    cont_integrableOn_box hL (hGcont a)
  have hI_F : ∀ c : κ, IntegrableOn (F c) (box N L) volume := fun c =>
    cont_integrableOn_box hL (hFcont c)
  have hSG : Continuous (fun x : X N => ∑ a : ι, G a x) := by
    refine continuous_finsetSum (s := Finset.univ) (f := fun a : ι => G a) ?_
    intro a ha
    exact hGcont a
  have hSF : Continuous (fun x : X N => ∑ c : κ, F c x) := by
    refine continuous_finsetSum (s := Finset.univ) (f := fun c : κ => F c) ?_
    intro c hc
    exact hFcont c
  have hI_SG : IntegrableOn (fun x : X N => ∑ a : ι, G a x) (box N L) volume :=
    cont_integrableOn_box hL hSG
  have hI_SF : IntegrableOn (fun x : X N => ∑ c : κ, F c x) (box N L) volume :=
    cont_integrableOn_box hL hSF
  have hpt_ae : (fun x : X N => ∑ a : ι, G a x) =ᵐ[volume.restrict (box N L)]
      fun x : X N => ∑ c : κ, F c x := by
    refine (ae_restrict_mem (box_measurable N L)).mono ?_
    intro x hx
    exact hpt x hx
  calc
    (∑ a : ι, ∫ x in box N L, G a x)
        = ∫ x in box N L, (∑ a : ι, G a x) := by
          rw [integral_finsetSum (s := Finset.univ) (μ := volume.restrict (box N L))
            (f := fun a : ι => G a) (fun a ha => hI_G a)]
    _ = ∫ x in box N L, (∑ c : κ, F c x) := by
          exact MeasureTheory.integral_congr_ae (μ := volume.restrict (box N L)) hpt_ae
    _ = ∑ c : κ, ∫ x in box N L, F c x := by
          rw [integral_finsetSum (s := Finset.univ) (μ := volume.restrict (box N L))
            (f := fun c : κ => F c) (fun c hc => hI_F c)]

/-- The assignment-sum of the localised kinetic of particle `i` collapses to
the single-cell sum, integrated over the box. -/
lemma tensor_collapse_integral {N m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (hL : 0 < (m : ℝ) * ℓ)
    (i : Fin N) (k : Fin 3) (Ψ : CInfty0Box N ((m : ℝ) * ℓ)) :
    (∑ a : Assign m N, ∫ x in box N ((m : ℝ) * ℓ),
        (fderiv ℝ (fun y : X N => cellAssignCut ℓ m N a y * (Ψ : X N → ℝ) y) x (kcDir N i k)) ^ 2) =
      ∑ c : CellIdx m, ∫ x in box N ((m : ℝ) * ℓ),
        (fderiv ℝ (fun y : X N => cellCut ℓ m c (y i) * (Ψ : X N → ℝ) y) x (kcDir N i k)) ^ 2 := by
  let G : Assign m N → X N → ℝ := fun a x =>
    (fderiv ℝ (fun y : X N => cellAssignCut ℓ m N a y * (Ψ : X N → ℝ) y) x (kcDir N i k)) ^ 2
  let F : CellIdx m → X N → ℝ := fun c x =>
    (fderiv ℝ (fun y : X N => cellCut ℓ m c (y i) * (Ψ : X N → ℝ) y) x (kcDir N i k)) ^ 2
  have hGcont : ∀ a : Assign m N, Continuous (G a) := by
    intro a
    dsimp [G]
    have hφ : ContDiff ℝ ∞ (fun y : X N => cellAssignCut ℓ m N a y * (Ψ : X N → ℝ) y) := by
      exact (cellAssignCut_contDiff ℓ m N a).mul (psi_contDiff Ψ)
    exact (firstDir_contDiff hφ (kcDir N i k)).continuous.pow 2
  have hFcont : ∀ c : CellIdx m, Continuous (F c) := by
    intro c
    dsimp [F]
    have hφ : ContDiff ℝ ∞ (fun y : X N => cellCut ℓ m c (y i) * (Ψ : X N → ℝ) y) := by
      have hpi : ContDiff ℝ ∞ (fun y : X N => y i) := by
        simpa using (contDiff_apply ℝ (EuclideanSpace ℝ (Fin 3)) (n := ∞) (ι := Fin N) i)
      exact ((cellCut_contDiff ℓ m c).comp hpi).mul (psi_contDiff Ψ)
    exact (firstDir_contDiff hφ (kcDir N i k)).continuous.pow 2
  have hpt : ∀ x : X N, x ∈ box N ((m : ℝ) * ℓ) →
      (∑ a : Assign m N, G a x) = ∑ c : CellIdx m, F c x := by
    intro x hx
    dsimp [G, F]
    exact tensor_collapse_pointwise (N := N) (m := m) (ℓ := ℓ) hℓ i k (psi_contDiff Ψ) hx
  simpa [G, F] using
    (sum_integral_eq (N := N) (L := (m : ℝ) * ℓ) hL (ι := Assign m N) (κ := CellIdx m) G F hGcont hFcont hpt)

/-- The single-cell localization error, summed over cells and integrated, is an
integral of the collapsed error density. -/
lemma err_reshape {N m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (hL : 0 < (m : ℝ) * ℓ) (i : Fin N)
    (Ψ : CInfty0Box N ((m : ℝ) * ℓ)) :
    (∑ c : CellIdx m, ∫ x in box N ((m : ℝ) * ℓ), (((Ψ : X N → ℝ) x) ^ 2) *
        (∑ k : Fin 3, (fderiv ℝ (cellCut ℓ m c) (x i) (kcStdBasis k)) ^ 2)) =
      ∫ x in box N ((m : ℝ) * ℓ), (((Ψ : X N → ℝ) x) ^ 2) *
        (∑ k : Fin 3, ∑ c : CellIdx m, (fderiv ℝ (cellCut ℓ m c) (x i) (kcStdBasis k)) ^ 2) := by
  let G : CellIdx m → X N → ℝ := fun c x => (((Ψ : X N → ℝ) x) ^ 2) *
      ∑ k : Fin 3, (fderiv ℝ (cellCut ℓ m c) (x i) (kcStdBasis k)) ^ 2
  let F : Unit → X N → ℝ := fun _ x => (((Ψ : X N → ℝ) x) ^ 2) *
      (∑ k : Fin 3, ∑ c : CellIdx m, (fderiv ℝ (cellCut ℓ m c) (x i) (kcStdBasis k)) ^ 2)
  have hf : ContDiff ℝ ∞ (Ψ : X N → ℝ) := psi_contDiff Ψ
  have hBz : ∀ c : CellIdx m, ∀ k : Fin 3, Continuous (fun x : X N =>
      fderiv ℝ (cellCut ℓ m c) (x i) (kcStdBasis k)) := by
    intro c k
    have hfdj : ContDiff ℝ ∞ (fderiv ℝ (cellCut ℓ m c)) :=
      ContDiff.fderiv_right (m := ∞) (cellCut_contDiff ℓ m c) (by simp)
    have heval : ContDiff ℝ ∞ (fun (L : ℝ³ →L[ℝ] ℝ) => L (kcStdBasis k)) := by
      exact ((ContinuousLinearMap.apply (𝕜 := ℝ) (Fₗ := ℝ) (kcStdBasis k) : (ℝ³ →L[ℝ] ℝ) →L[ℝ] ℝ).contDiff)
    have hz : ContDiff ℝ ∞ (fun z : ℝ³ => fderiv ℝ (cellCut ℓ m c) z (kcStdBasis k)) := by
      simpa [Function.comp_def] using heval.comp hfdj
    have hpi : Continuous (fun x : X N => x i) := continuous_apply i
    exact hz.continuous.comp hpi
  have hBcont : ∀ c : CellIdx m, Continuous (fun x : X N =>
      ∑ k : Fin 3, (fderiv ℝ (cellCut ℓ m c) (x i) (kcStdBasis k)) ^ 2) := by
    intro c
    refine continuous_finsetSum (s := Finset.univ)
      (f := fun (k : Fin 3) (x : X N) => (fderiv ℝ (cellCut ℓ m c) (x i) (kcStdBasis k)) ^ 2) ?_
    intro k hk
    exact (hBz c k).pow 2
  have hGcont : ∀ c : CellIdx m, Continuous (G c) := by
    intro c
    dsimp [G]
    exact (hf.continuous.pow 2).mul (hBcont c)
  have hFcont : ∀ u : Unit, Continuous (F u) := by
    intro u
    dsimp [F]
    refine (hf.continuous.pow 2).mul ?_
    refine continuous_finsetSum (s := Finset.univ)
      (f := fun (k : Fin 3) (x : X N) => ∑ c : CellIdx m, (fderiv ℝ (cellCut ℓ m c) (x i) (kcStdBasis k)) ^ 2) ?_
    intro k hk
    refine continuous_finsetSum (s := Finset.univ)
      (f := fun (c : CellIdx m) (x : X N) => (fderiv ℝ (cellCut ℓ m c) (x i) (kcStdBasis k)) ^ 2) ?_
    intro c hc
    exact (hBz c k).pow 2
  have hpt : ∀ x : X N, x ∈ box N ((m : ℝ) * ℓ) →
      (∑ c : CellIdx m, G c x) = ∑ u : Unit, F u x := by
    intro x hx
    simp [F]
    calc
      (∑ c : CellIdx m, (((Ψ : X N → ℝ) x) ^ 2) *
          ∑ k : Fin 3, (fderiv ℝ (cellCut ℓ m c) (x i) (kcStdBasis k)) ^ 2)
          = (((Ψ : X N → ℝ) x) ^ 2) * (∑ c : CellIdx m,
              ∑ k : Fin 3, (fderiv ℝ (cellCut ℓ m c) (x i) (kcStdBasis k)) ^ 2) := by
            rw [← Finset.mul_sum]
      _ = (((Ψ : X N → ℝ) x) ^ 2) * (∑ k : Fin 3,
              ∑ c : CellIdx m, (fderiv ℝ (cellCut ℓ m c) (x i) (kcStdBasis k)) ^ 2) := by
            congr 1
            rw [Finset.sum_comm]
  simpa [G, F] using
    (sum_integral_eq (N := N) (L := (m : ℝ) * ℓ) hL (ι := CellIdx m) (κ := Unit) G F hGcont hFcont hpt)

lemma box0_eq_singleton (N : ℕ) : box N 0 = ({0} : Set (X N)) := by
  ext x
  constructor
  · intro hx
    funext i
    ext k
    have hik := hx i k
    exact (le_antisymm hik.2 hik.1)
  · intro hx i k
    have hik : x i k = 0 := by
      rw [hx]
      simp
    simp [hik]

lemma interior_box0_empty {N : ℕ} (hN : 1 ≤ N) : interior (box N 0) = (∅ : Set (X N)) := by
  rw [box0_eq_singleton]
  haveI : Nontrivial (X N) := by
    let i : Fin N := ⟨0, hN⟩
    let v : X N := Function.update (0 : X N) i (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
    refine ⟨⟨0, v, ?_⟩⟩
    intro hv
    have h := congrFun hv i
    simp [v] at h
    have h' := congrArg (fun w : ℝ³ => w (0 : Fin 3)) h
    norm_num at h'
  have hI : NeBot (𝓝[≠] (0 : X N)) := Real.punctured_nhds_module_neBot (0 : X N)
  exact interior_singleton (0 : X N)

lemma zero_box_no_state {N : ℕ} (hN : 1 ≤ N) (Ψ : CInfty0Box N 0) : False := by
  have hs : tsupport (Ψ : X N → ℝ) ⊆ interior (box N 0) := Ψ.support
  have hint : interior (box N 0) = (∅ : Set (X N)) := interior_box0_empty hN
  have hts : tsupport (Ψ : X N → ℝ) = (∅ : Set (X N)) := by
    rw [hint] at hs
    simpa using hs
  have hsupp0 : Function.support (Ψ : X N → ℝ) = ∅ := by
    have hsub : Function.support (Ψ : X N → ℝ) ⊆ tsupport (Ψ : X N → ℝ) :=
      subset_closure
    rw [hts] at hsub
    simpa using hsub
  have hzero : (Ψ : X N → ℝ) = 0 := by
    funext x
    by_contra hx
    have : x ∈ Function.support (Ψ : X N → ℝ) := by
      rw [Function.mem_support]
      exact hx
    simpa [hsupp0] using this
  exact Ψ.nezero hzero


/-- All-particle tensor IMS identity (auxiliary: assumes `0 < (m:ℝ)*ℓ`). -/
lemma ims_tensor_identity_aux {N m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (hL : 0 < (m : ℝ) * ℓ)
    (Ψ : CInfty0Box N ((m : ℝ) * ℓ)) :
    (∑ a : Assign m N, ∑ i : Fin N, ∑ k : Fin 3, ∫ x in box N ((m : ℝ) * ℓ),
        (fderiv ℝ (fun y : X N => cellAssignCut ℓ m N a y * (Ψ : X N → ℝ) y) x (kcDir N i k)) ^ 2) =
      (∑ i : Fin N, ∑ k : Fin 3, ∫ x in box N ((m : ℝ) * ℓ),
        (fderiv ℝ (Ψ : X N → ℝ) x (kcDir N i k)) ^ 2) +
        (∑ i : Fin N, ∫ x in box N ((m : ℝ) * ℓ),
          (((Ψ : X N → ℝ) x) ^ 2) *
            (∑ k : Fin 3, ∑ c : CellIdx m,
              (fderiv ℝ (cellCut ℓ m c) (x i) (kcStdBasis k)) ^ 2)) := by
  classical
  have hE : ∀ (i : Fin N) (k : Fin 3),
      (∑ a : Assign m N, ∫ x in box N ((m : ℝ) * ℓ),
        (fderiv ℝ (fun y : X N => cellAssignCut ℓ m N a y * (Ψ : X N → ℝ) y) x (kcDir N i k)) ^ 2) =
      (∑ c : CellIdx m, ∫ x in box N ((m : ℝ) * ℓ),
        (fderiv ℝ (fun y : X N => cellCut ℓ m c (y i) * (Ψ : X N → ℝ) y) x (kcDir N i k)) ^ 2) := by
    intro i k
    exact tensor_collapse_integral (N := N) (m := m) (ℓ := ℓ) hℓ hL i k Ψ
  have hχ : ∀ c : CellIdx m, ContDiff ℝ ∞ (cellCut ℓ m c) := fun c => cellCut_contDiff ℓ m c
  have hpu : ∀ y : ℝ³, y ∈ cubeOp ((m : ℝ) * ℓ) →
      (∑ c : CellIdx m, (cellCut ℓ m c y) ^ 2) = 1 := by
    intro y hy
    exact cellCut_pu hℓ m (fun k => by
      have hyk : y k ∈ Set.Ioo 0 ((m : ℝ) * ℓ) := hy k
      exact ⟨le_of_lt hyk.1, le_of_lt hyk.2⟩)
  have hbi : ∀ i : Fin N,
      (∑ c : CellIdx m, ∑ k : Fin 3, ∫ x in box N ((m : ℝ) * ℓ),
        (fderiv ℝ (fun y : X N => cellCut ℓ m c (y i) * (Ψ : X N → ℝ) y) x (kcDir N i k)) ^ 2) =
        (∑ k : Fin 3, ∫ x in box N ((m : ℝ) * ℓ),
          (fderiv ℝ (Ψ : X N → ℝ) x (kcDir N i k)) ^ 2) +
        (∑ c : CellIdx m, ∫ x in box N ((m : ℝ) * ℓ),
          (((Ψ : X N → ℝ) x) ^ 2) *
            (∑ k : Fin 3, (fderiv ℝ (cellCut ℓ m c) (x i) (kcStdBasis k)) ^ 2)) := by
    intro i
    exact ims_box_identity (N := N) (ι := CellIdx m) (L := (m : ℝ) * ℓ) hL i Ψ
      (fun c : CellIdx m => cellCut ℓ m c) hχ hpu
  have herr : ∀ i : Fin N,
      (∑ c : CellIdx m, ∫ x in box N ((m : ℝ) * ℓ), (((Ψ : X N → ℝ) x) ^ 2) *
          (∑ k : Fin 3, (fderiv ℝ (cellCut ℓ m c) (x i) (kcStdBasis k)) ^ 2)) =
        ∫ x in box N ((m : ℝ) * ℓ), (((Ψ : X N → ℝ) x) ^ 2) *
          (∑ k : Fin 3, ∑ c : CellIdx m, (fderiv ℝ (cellCut ℓ m c) (x i) (kcStdBasis k)) ^ 2) := by
    intro i
    exact err_reshape (N := N) (m := m) (ℓ := ℓ) hℓ hL i Ψ
  calc
    (∑ a : Assign m N, ∑ i : Fin N, ∑ k : Fin 3, ∫ x in box N ((m : ℝ) * ℓ),
        (fderiv ℝ (fun y : X N => cellAssignCut ℓ m N a y * (Ψ : X N → ℝ) y) x (kcDir N i k)) ^ 2)
        = (∑ i : Fin N, ∑ k : Fin 3, ∑ a : Assign m N, ∫ x in box N ((m : ℝ) * ℓ),
            (fderiv ℝ (fun y : X N => cellAssignCut ℓ m N a y * (Ψ : X N → ℝ) y) x (kcDir N i k)) ^ 2) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_comm]
    _ = (∑ i : Fin N, ∑ k : Fin 3, ∑ c : CellIdx m, ∫ x in box N ((m : ℝ) * ℓ),
          (fderiv ℝ (fun y : X N => cellCut ℓ m c (y i) * (Ψ : X N → ℝ) y) x (kcDir N i k)) ^ 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro k hk
          exact hE i k
    _ = (∑ i : Fin N, ∑ c : CellIdx m, ∑ k : Fin 3, ∫ x in box N ((m : ℝ) * ℓ),
          (fderiv ℝ (fun y : X N => cellCut ℓ m c (y i) * (Ψ : X N → ℝ) y) x (kcDir N i k)) ^ 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_comm]
    _ = (∑ i : Fin N, ((∑ k : Fin 3, ∫ x in box N ((m : ℝ) * ℓ),
          (fderiv ℝ (Ψ : X N → ℝ) x (kcDir N i k)) ^ 2) +
          (∑ c : CellIdx m, ∫ x in box N ((m : ℝ) * ℓ), (((Ψ : X N → ℝ) x) ^ 2) *
            (∑ k : Fin 3, (fderiv ℝ (cellCut ℓ m c) (x i) (kcStdBasis k)) ^ 2)))) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hbi i
    _ = (∑ i : Fin N, ∑ k : Fin 3, ∫ x in box N ((m : ℝ) * ℓ),
          (fderiv ℝ (Ψ : X N → ℝ) x (kcDir N i k)) ^ 2) +
        (∑ i : Fin N, ∑ c : CellIdx m, ∫ x in box N ((m : ℝ) * ℓ), (((Ψ : X N → ℝ) x) ^ 2) *
            (∑ k : Fin 3, (fderiv ℝ (cellCut ℓ m c) (x i) (kcStdBasis k)) ^ 2)) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ i : Fin N, ∑ k : Fin 3, ∫ x in box N ((m : ℝ) * ℓ),
          (fderiv ℝ (Ψ : X N → ℝ) x (kcDir N i k)) ^ 2) +
        (∑ i : Fin N, ∫ x in box N ((m : ℝ) * ℓ), (((Ψ : X N → ℝ) x) ^ 2) *
            (∑ k : Fin 3, ∑ c : CellIdx m, (fderiv ℝ (cellCut ℓ m c) (x i) (kcStdBasis k)) ^ 2)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          exact herr i


/-- All-particle IMS identity (the exact identity with the explicit
localization error on the right). -/
lemma ims_tensor_identity {N m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (Ψ : CInfty0Box N ((m : ℝ) * ℓ)) :
    (∑ a : Assign m N, ∑ i : Fin N, ∑ k : Fin 3, ∫ x in box N ((m : ℝ) * ℓ),
        (fderiv ℝ (fun y : X N => cellAssignCut ℓ m N a y * (Ψ : X N → ℝ) y) x (kcDir N i k)) ^ 2) =
      (∑ i : Fin N, ∑ k : Fin 3, ∫ x in box N ((m : ℝ) * ℓ),
        (fderiv ℝ (Ψ : X N → ℝ) x (kcDir N i k)) ^ 2) +
        (∑ i : Fin N, ∫ x in box N ((m : ℝ) * ℓ),
          (((Ψ : X N → ℝ) x) ^ 2) *
            (∑ k : Fin 3, ∑ c : CellIdx m,
              (fderiv ℝ (cellCut ℓ m c) (x i) (kcStdBasis k)) ^ 2)) := by
  classical
  by_cases hL : 0 < (m : ℝ) * ℓ
  · exact ims_tensor_identity_aux (N := N) (m := m) (ℓ := ℓ) hℓ hL Ψ
  · have hle : (m : ℝ) * ℓ ≤ 0 := le_of_not_gt hL
    have hmR : (m : ℝ) ≤ 0 := by
      nlinarith [hle, hℓ]
    have hmR0 : (m : ℝ) = 0 := le_antisymm hmR (Nat.cast_nonneg m)
    have hm0 : m = 0 := by exact_mod_cast hmR0
    subst m
    by_cases hN : N = 0
    · subst hN
      simp
    · have hNpos : 1 ≤ N := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hN)
      exfalso
      have Ψ0 : CInfty0Box N 0 := by simpa using Ψ
      exact zero_box_no_state hNpos Ψ0


/-- **The all-particle localization bound**: localizing all `N` particles into
the `m³` cells costs at most `N·(6A²/ℓ²)·∫Ψ²`. -/
lemma tensorLocalize_kinetic_le {N m : ℕ} {ℓ A : ℝ} (hm : 1 ≤ m) (hℓ : 0 < ℓ)
    (hA0 : 0 ≤ A) (hA : ∀ t : ℝ, |deriv rhoProfile t| ≤ A)
    (Ψ : CInfty0Box N ((m : ℝ) * ℓ)) :
    (∑ i : Fin N, ∑ k : Fin 3, ∫ x in box N ((m : ℝ) * ℓ),
        (fderiv ℝ (Ψ : X N → ℝ) x (kcDir N i k)) ^ 2) ≤
      (∑ a : Assign m N, ∑ i : Fin N, ∑ k : Fin 3, ∫ x in box N ((m : ℝ) * ℓ),
        (fderiv ℝ (fun y : X N => cellAssignCut ℓ m N a y * (Ψ : X N → ℝ) y) x
          (kcDir N i k)) ^ 2) +
        (N : ℝ) * (6 * A ^ 2 / ℓ ^ 2) * (∫ x in box N ((m : ℝ) * ℓ),
          ((Ψ : X N → ℝ) x) ^ 2) := by
  classical
  have hmain := ims_tensor_identity hℓ Ψ
  have herr0 : 0 ≤ (∑ i : Fin N, ∫ x in box N ((m : ℝ) * ℓ),
      (((Ψ : X N → ℝ) x) ^ 2) *
        (∑ k : Fin 3, ∑ c : CellIdx m, (fderiv ℝ (cellCut ℓ m c) (x i) (kcStdBasis k)) ^ 2)) := by
    apply Finset.sum_nonneg
    intro i hi
    apply integral_nonneg
    intro x
    exact mul_nonneg (sq_nonneg ((Ψ : X N → ℝ) x))
      (Finset.sum_nonneg (fun k hk =>
        Finset.sum_nonneg (fun c hc => sq_nonneg _)))
  have hC0 : 0 ≤ (6 * A ^ 2 / ℓ ^ 2) := by positivity
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hInt0 : 0 ≤ ∫ x in box N ((m : ℝ) * ℓ), (((Ψ : X N → ℝ) x) ^ 2) := by
    apply integral_nonneg
    intro x
    exact sq_nonneg _
  have hcost0 : 0 ≤ (N : ℝ) * (6 * A ^ 2 / ℓ ^ 2) *
      (∫ x in box N ((m : ℝ) * ℓ), (((Ψ : X N → ℝ) x) ^ 2)) := by
    exact mul_nonneg (mul_nonneg hN0 hC0) hInt0
  nlinarith [hmain, herr0, hcost0]


end BoseGases

end Submission
