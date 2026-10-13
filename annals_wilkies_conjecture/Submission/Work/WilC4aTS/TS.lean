/-
  Area `WilC4aTS`: Tarski--Seidenberg (semialgebraic projection) in the vocabulary of the frozen
  area `E`, and the hole `C4a_TS1` of area C4a.

  ## What this file is

  This is the *standalone* lemma file for the projection theorem, published for area E4 (whose CAD
  needs it) and used here for the C4a hole.  Nothing in it is a new axiom or a re-proof of
  Tarski--Seidenberg: the projection is
  `Work.WilLibTS.TS.SignElimination.polynomialSignSet_projection_finite` (the port of the upstream
  `OAI/Analysis/SymmetricDomains` development by the subproject `WilLibTS`), and this file is the
  *bridge* between that theorem and the frozen vocabulary `WilkiesDesign.E.SA`.

  ## Main results (all in namespace `Work.WilC4aTS`)

  Dictionary (`PolynomialSignSet` is abbreviated `PSS`, see `Submission.Work.WilC4aTS.PSS`):
  * `pss_of_forall_eq`, `pss_of_forall_pos` : finite conjunctions of equations / inequalities;
  * `pss_of_basic`, `pss_of_sad`, `pss_of_sa` : every `E.Basic` / `SAd` / `E.SA` set is a `PSS`;
  * `exists_sad_of_pss`, `exists_sa_of_pss` : conversely.

  Projection (the mathematical content):
  * `pss_projection_principle` : the imported Tarski--Seidenberg theorem, restated in this area;
  * `pss_proj_append`, `pss_proj_append_right`, `pss_projLast` : a projection of a `PSS` is a `PSS`;
  * `sa_projLast` : **Tarski--Seidenberg for one projection over `E.SA`** (the content of `C4a_TS1`);
  * `sa_projAppend`, `sa_projFirst`, `sa_projSnd` : the finite-coordinate projections,
    and `sad_projLast` / `sad_projAppend` at the level of the DNF vocabulary `SAd`.

  Boolean algebra at the level of the frozen `E.SA`: `sa_univ`, `sa_empty`, `sa_union`, `sa_inter`,
  `sa_compl`.

  The hole: `C4a_TS1_proved : WilkiesDesign.CG.C4a.TS1`, and its assembly from the single
  projection principle, `C4a_TS1_proved_of_projection`.
-/
import Submission.Work.WilC4aTS.SA
import Submission.Work.WilC4aTS.PSS
import Submission.Work.Wilkies.CG.C4a.Spec
import Submission.Work.WilLibTS.TS.PolynomialSignSetProjection2

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical
namespace Work.WilC4aTS
open WilkiesDesign WilkiesDesign.E
open MvPolynomial
open Set
open Work.WilLibTS.TS (PolynomialSignSet)

/-! ## 1. The dictionary `E.SA ↔ PolynomialSignSet` -/

/-- A finite conjunction of equations is a `PolynomialSignSet`. -/
theorem pss_of_forall_eq {m : ℕ} (L : List (Poly m)) :
    PSS {x : Fin m → ℝ | ∀ f ∈ L, MvPolynomial.eval x f = 0} := by
  induction L with
  | nil =>
      have h : {x : Fin m → ℝ | ∀ f ∈ ([] : List (Poly m)), MvPolynomial.eval x f = 0}
          = Set.univ := by ext x; simp
      rw [h]; exact pss_univ
  | cons f L ih =>
      have h : {x : Fin m → ℝ | ∀ f' ∈ (f :: L), MvPolynomial.eval x f' = 0}
          = {x : Fin m → ℝ | MvPolynomial.eval x f = 0}
            ∩ {x : Fin m → ℝ | ∀ f' ∈ L, MvPolynomial.eval x f' = 0} := by
        ext x; simp
      rw [h]
      exact pss_inter (PolynomialSignSet.zero f) ih

/-- A finite conjunction of strict inequalities is a `PolynomialSignSet`. -/
theorem pss_of_forall_pos {m : ℕ} (L : List (Poly m)) :
    PSS {x : Fin m → ℝ | ∀ g ∈ L, 0 < MvPolynomial.eval x g} := by
  induction L with
  | nil =>
      have h : {x : Fin m → ℝ | ∀ g ∈ ([] : List (Poly m)), 0 < MvPolynomial.eval x g}
          = Set.univ := by ext x; simp
      rw [h]; exact pss_univ
  | cons g L ih =>
      have h : {x : Fin m → ℝ | ∀ g' ∈ (g :: L), 0 < MvPolynomial.eval x g'}
          = {x : Fin m → ℝ | 0 < MvPolynomial.eval x g}
            ∩ {x : Fin m → ℝ | ∀ g' ∈ L, 0 < MvPolynomial.eval x g'} := by
        ext x; simp
      rw [h]
      exact pss_inter (PolynomialSignSet.positive g) ih

/-- Every basic semialgebraic set is a `PolynomialSignSet`. -/
theorem pss_of_basic {m : ℕ} (B : BasicD m) : PSS B.set := by
  have h : B.set = {x : Fin m → ℝ | ∀ f ∈ B.eqs, MvPolynomial.eval x f = 0}
      ∩ {x : Fin m → ℝ | ∀ g ∈ B.pos, 0 < MvPolynomial.eval x g} := rfl
  rw [h]
  exact pss_inter (pss_of_forall_eq B.eqs) (pss_of_forall_pos B.pos)

/-- Every `SAd` (semialgebraic set in DNF over `Poly m`) is a `PolynomialSignSet`. -/
theorem pss_of_sad {m : ℕ} (Y : SAd m) : PSS Y.set := by
  obtain ⟨L⟩ := Y
  show PSS {x : Fin m → ℝ | ∃ B ∈ L, B.Holds x}
  induction L with
  | nil =>
      have h : {x : Fin m → ℝ | ∃ B ∈ ([] : List (BasicD m)), B.Holds x} = ∅ := by
        ext x; simp
      rw [h]; exact pss_empty
  | cons B rest ih =>
      have h : {x : Fin m → ℝ | ∃ B' ∈ (B :: rest), B'.Holds x}
          = B.set ∪ {x : Fin m → ℝ | ∃ B' ∈ rest, B'.Holds x} := by
        ext x
        simp only [BasicD.set, Set.mem_union, List.mem_cons]
        constructor
        · rintro ⟨B', rfl | hB', hx⟩
          · exact Or.inl hx
          · exact Or.inr ⟨B', hB', hx⟩
        · rintro (hx | ⟨B', hB', hx⟩)
          · exact ⟨B, Or.inl rfl, hx⟩
          · exact ⟨B', Or.inr hB', hx⟩
      rw [h]
      exact pss_union (pss_of_basic B) ih

/-- Every set of the frozen vocabulary `E.SA` is a `PolynomialSignSet`. -/
theorem pss_of_sa {m : ℕ} (X : SA m) : PSS X.set := by
  rw [← SAd.set_ofSA X]
  exact pss_of_sad (SAd.ofSA X)

/-- Every `PolynomialSignSet` in DNF form is an `SAd`. -/
theorem exists_sad_of_pss {m : ℕ} {S : Set (Fin m → ℝ)} (hS : PSS S) :
    ∃ Y : SAd m, Y.set = S := by
  induction hS with
  | zero p => exact ⟨⟨[BEq p]⟩, by ext x; simp [SAd.set, BEq_holds]⟩
  | positive p => exact ⟨⟨[BPos p]⟩, by ext x; simp [SAd.set, BPos_holds]⟩
  | compl _ ih => obtain ⟨Y, hY⟩ := ih; exact ⟨Y.compl, by simp [SAd.compl_set, hY]⟩
  | union _ _ ihS ihT =>
      obtain ⟨Y, hY⟩ := ihS
      obtain ⟨Z, hZ⟩ := ihT
      exact ⟨Y.union Z, by simp [SAd.union_set, hY, hZ]⟩

/-- Every `PolynomialSignSet` is a set of the frozen vocabulary `E.SA`. -/
theorem exists_sa_of_pss {m : ℕ} {S : Set (Fin m → ℝ)} (hS : PSS S) :
    ∃ Y : SA m, Y.set = S := by
  obtain ⟨Y, hY⟩ := exists_sad_of_pss hS
  exact ⟨Y.toSA, by rw [SAd.set_toSA, hY]⟩

/-! ## 2. Boolean algebra at the level of the frozen `E.SA` -/

theorem sa_empty (m : ℕ) : ∃ Y : SA m, Y.set = ∅ :=
  ⟨(SAd.empty m).toSA, by rw [SAd.set_toSA, SAd.empty_set]⟩

theorem sa_univ (m : ℕ) : ∃ Y : SA m, Y.set = Set.univ :=
  ⟨(SAd.univ m).toSA, by rw [SAd.set_toSA, SAd.univ_set]⟩

theorem sa_union {m : ℕ} (X Y : SA m) : ∃ Z : SA m, Z.set = X.set ∪ Y.set :=
  ⟨((SAd.ofSA X).union (SAd.ofSA Y)).toSA, by
    rw [SAd.set_toSA, SAd.union_set, SAd.set_ofSA, SAd.set_ofSA]⟩

theorem sa_inter {m : ℕ} (X Y : SA m) : ∃ Z : SA m, Z.set = X.set ∩ Y.set :=
  ⟨((SAd.ofSA X).inter (SAd.ofSA Y)).toSA, by
    rw [SAd.set_toSA, SAd.inter_set, SAd.set_ofSA, SAd.set_ofSA]⟩

theorem sa_compl {m : ℕ} (X : SA m) : ∃ Z : SA m, Z.set = X.setᶜ :=
  ⟨(SAd.ofSA X).compl.toSA, by rw [SAd.set_toSA, SAd.compl_set, SAd.set_ofSA]⟩

/-! ## 3. Projection

The upstream theorem is stated for `PolynomialSignSet` over a product `X × (κ → ℝ)`, with the
coordinate map `Sum.elim (c z.1) z.2`.  We instantiate it to `κ = Fin q` and identify
`Fin p ⊕ Fin q` with `Fin (p + q)` through `finSumFinEquiv`, so that the coordinate map becomes
`xc ↦ Fin.append x y`.  The only combinatorial input needed is `append_eq_elim` below. -/

/-- **Tarski--Seidenberg (general form)**, in the vocabulary of this area: the projection of a
`PolynomialSignSet` along finitely many coordinates is a `PolynomialSignSet`.  This is a verbatim
restatement of the imported `Work.WilLibTS.TS.SignElimination.polynomialSignSet_projection_finite`,
so that callers of this area need not name the `WilLibTS` namespace. -/
theorem pss_projection_principle {X ι κ : Type*} [Finite κ] (c : X → ι → ℝ)
    (A : Set (X × (κ → ℝ)))
    (hA : PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2) A) :
    PolynomialSignSet c {x | ∃ y : κ → ℝ, (x, y) ∈ A} :=
  Work.WilLibTS.TS.SignElimination.polynomialSignSet_projection_finite hA

/-- Appending two tuples is `Sum.elim` along the equivalence `Fin p ⊕ Fin q ≃ Fin (p + q)`. -/
theorem append_eq_elim {p q : ℕ} {α : Type*} (u : Fin p → α) (v : Fin q → α) :
    (Fin.append u v : Fin (p + q) → α) = fun i => Sum.elim u v (finSumFinEquiv.symm i) := by
  funext i
  rcases h : finSumFinEquiv.symm i with a | b
  · have hi : i = Fin.castAdd q a := by
      rw [← finSumFinEquiv_apply_left (m := p) (n := q) a, ← h, Equiv.apply_symm_apply]
    rw [hi, Fin.append_left, Sum.elim_inl]
  · have hi : i = Fin.natAdd p b := by
      rw [← finSumFinEquiv_apply_right (m := p) (n := q) b, ← h, Equiv.apply_symm_apply]
    rw [hi, Fin.append_right, Sum.elim_inr]

/-- `Sum.elim` commutes with `Equiv.sumComm`. -/
theorem sum_elim_sumComm {α β : Type*} {γ : Sort*} (u : α → γ) (v : β → γ) (s : α ⊕ β) :
    Sum.elim v u (Equiv.sumComm α β s) = Sum.elim u v s := by
  rcases s with a | b <;> rfl

/-- **Tarski--Seidenberg, finite-coordinate projection (existential form).**
The projection of a `PolynomialSignSet` along the last `q` coordinates is a `PolynomialSignSet`. -/
theorem pss_proj_append {p q : ℕ} {S : Set (Fin (p + q) → ℝ)} (hS : PSS S) :
    PSS {x : Fin p → ℝ | ∃ y : Fin q → ℝ, Fin.append x y ∈ S} := by
  have hA : PolynomialSignSet
      (fun z : (Fin p → ℝ) × (Fin q → ℝ) => Sum.elim (id z.1) z.2)
      {z : (Fin p → ℝ) × (Fin q → ℝ) | Fin.append z.1 z.2 ∈ S} :=
    hS.coordinate_preimage (fun z : (Fin p → ℝ) × (Fin q → ℝ) => Fin.append z.1 z.2)
      finSumFinEquiv.symm
      (by intro z i; exact congrFun (append_eq_elim z.1 z.2) i)
  exact pss_projection_principle (c := (id : (Fin p → ℝ) → Fin p → ℝ)) _ hA

/-- The dual form: projecting onto the last `q` coordinates. -/
theorem pss_proj_append_right {p q : ℕ} {S : Set (Fin (p + q) → ℝ)} (hS : PSS S) :
    PSS {y : Fin q → ℝ | ∃ x : Fin p → ℝ, Fin.append x y ∈ S} := by
  have hA : PolynomialSignSet
      (fun z : (Fin q → ℝ) × (Fin p → ℝ) => Sum.elim (id z.1) z.2)
      {z : (Fin q → ℝ) × (Fin p → ℝ) | Fin.append z.2 z.1 ∈ S} :=
    hS.coordinate_preimage (fun z : (Fin q → ℝ) × (Fin p → ℝ) => Fin.append z.2 z.1)
      (fun i => Equiv.sumComm (Fin p) (Fin q) (finSumFinEquiv.symm i))
      (by
        intro z i
        rw [append_eq_elim z.2 z.1]
        exact (sum_elim_sumComm z.2 z.1 (finSumFinEquiv.symm i)).symm)
  exact pss_projection_principle (c := (id : (Fin q → ℝ) → Fin q → ℝ)) _ hA

/-- Reassembling a tuple from its first `p` and last `q` coordinates. -/
theorem append_first_snd {p q : ℕ} (z : Fin (p + q) → ℝ) :
    Fin.append (projFirst p q z) (projSnd p q z) = z := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simp [projFirst]
  · simp [projSnd]

/-- Appending a one-tuple is `Fin.snoc` (a restatement of Mathlib's `Fin.append_right_eq_snoc`). -/
theorem snoc_eq_append_one {n : ℕ} {α : Type*} (x : Fin n → α) (y : Fin 1 → α) :
    Fin.snoc x (y 0) = Fin.append x y :=
  (Fin.append_right_eq_snoc x y).symm

/-- **Tarski--Seidenberg, one projection.**  The projection of a `PolynomialSignSet` along the
last coordinate is a `PolynomialSignSet`. -/
theorem pss_projLast {m : ℕ} {S : Set (Fin (m + 1) → ℝ)} (hS : PSS S) : PSS (projLast S) := by
  have h : projLast S = {x : Fin m → ℝ | ∃ y : Fin 1 → ℝ, Fin.append x y ∈ S} := by
    ext x
    show (∃ t : ℝ, Fin.snoc x t ∈ S) ↔ ∃ y : Fin 1 → ℝ, Fin.append x y ∈ S
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨fun _ : Fin 1 => t,
        by simpa [snoc_eq_append_one x (fun _ : Fin 1 => t)] using ht⟩
    · rintro ⟨y, hy⟩
      exact ⟨y 0, by simpa [snoc_eq_append_one x y] using hy⟩
  rw [h]
  exact pss_proj_append hS

/-- **Tarski--Seidenberg for one projection over `E.SA`** (the semialgebraic sets of area E, in
DNF).  This is the content of the hole `C4a_TS1`, published for the CAD of area E4. -/
theorem sa_projLast {m : ℕ} (X : SA (m + 1)) : ∃ Y : SA m, Y.set = projLast X.set :=
  exists_sa_of_pss (pss_projLast (pss_of_sa X))

/-- Projection along the last `q` coordinates of a set of `E.SA`. -/
theorem sa_projAppend {p q : ℕ} (X : SA (p + q)) :
    ∃ Y : SA p, Y.set = {x : Fin p → ℝ | ∃ y : Fin q → ℝ, Fin.append x y ∈ X.set} :=
  exists_sa_of_pss (pss_proj_append (pss_of_sa X))

/-- The `projLast` projection at the level of the DNF vocabulary `SAd`. -/
theorem sad_projLast {m : ℕ} (X : SAd (m + 1)) : ∃ Y : SAd m, Y.set = projLast X.set :=
  exists_sad_of_pss (pss_projLast (pss_of_sad X))

/-- The finite-coordinate projection at the level of the DNF vocabulary `SAd`. -/
theorem sad_projAppend {p q : ℕ} (X : SAd (p + q)) :
    ∃ Y : SAd p, Y.set = {x : Fin p → ℝ | ∃ y : Fin q → ℝ, Fin.append x y ∈ X.set} :=
  exists_sad_of_pss (pss_proj_append (pss_of_sad X))

/-- Projection to the first `p` coordinates, in the image form of `E.projFirst`. -/
theorem sa_projFirst {p q : ℕ} (X : SA (p + q)) :
    ∃ Y : SA p, Y.set = projFirst p q '' X.set := by
  obtain ⟨Y, hY⟩ := sa_projAppend X
  refine ⟨Y, ?_⟩
  rw [hY]
  ext x
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨Fin.append x y, hy, funext fun i => Fin.append_left x y i⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨projSnd p q z, ?_⟩
    rwa [append_first_snd z]

/-- Projection to the last `q` coordinates, in the image form of `E.projSnd`. -/
theorem sa_projSnd {p q : ℕ} (X : SA (p + q)) :
    ∃ Y : SA q, Y.set = projSnd p q '' X.set := by
  obtain ⟨Y, hY⟩ := exists_sa_of_pss (pss_proj_append_right (pss_of_sa X))
  refine ⟨Y, ?_⟩
  rw [hY]
  ext y
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨Fin.append x y, hx, funext fun j => Fin.append_right x y j⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨projFirst p q z, ?_⟩
    rwa [append_first_snd z]

/-! ## 4. The hole `C4a_TS1` -/

/-- **Tarski--Seidenberg for one projection over `E.SA`**, assembled from the single projection
principle for `projLast` (the only external input).  This split keeps the arithmetic of the bridge
-- the dictionary of §1 and the `SAd`/`SA` round trip -- separate from the projection theorem. -/
theorem C4a_TS1_proved_of_projection
    (hTS : ∀ {m : ℕ} {S : Set (Fin (m + 1) → ℝ)}, PSS S → PSS (projLast S)) :
    WilkiesDesign.CG.C4a.TS1 := by
  intro m X
  obtain ⟨Y, hY⟩ := exists_sa_of_pss (hTS (pss_of_sa X))
  exact ⟨Y, hY⟩

/-- **The hole `C4a_TS1` of area C4a**: Tarski--Seidenberg for one projection, over the frozen
semialgebraic vocabulary `E.SA`.  Proved from the imported projection theorem (port `WilLibTS`),
via `C4a_TS1_proved_of_projection` and `pss_projLast`. -/
theorem C4a_TS1_proved : WilkiesDesign.CG.C4a.TS1 :=
  C4a_TS1_proved_of_projection fun hS => pss_projLast hS

end Work.WilC4aTS
