/-
  WilE6 (area E6): fibrewise closure and frontier of EA sets (Gabrielov 1998).

  This file: the foundational vocabulary of the E6 development.

  * `hvec c z`            : the chain values `exp (ℓ_j z)` at the point `z`.
  * `graphPt c z`         : the point `(z, hvec c z)` of `ℝ^{k+r}`.
  * `toCombined Q`        : the same polynomial viewed in the variables `Fin (k+r)`,
                            so that `eaEval c Q z = eval (graphPt c z) (toCombined Q)`.
  * `saPoly`, `saBasic`, `basicPullback`, `saPullback` : the pullback of a semialgebraic
                            description in the `(z,h)`-space to a `SemiPf` description in `z`.
                            This is the "substitution `h := E(y)`" step of the E6 design.
-/
import Submission.Work.Wilkies.E.Spec

set_option autoImplicit false
noncomputable section
open Classical Topology
namespace Work.WilE6
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

variable {k r : ℕ}

/-! ## §1. The graph of the chain -/

/-- The chain values at `z`: `hvec c z j = exp (ℓ_j z)`. -/
def hvec (c : EAChain k r) (z : Fin k → ℝ) : Fin r → ℝ := fun j => Real.exp (c.ell j z)

/-- The point `(z, h(z))` of `ℝ^{k+r}`. -/
def graphPt (c : EAChain k r) (z : Fin k → ℝ) : Fin (k + r) → ℝ := Fin.append z (hvec c z)

/-- The variable map `Fin k ⊕ Fin r → Fin (k+r)` (coordinates first, then chain values). -/
def sumToFin (k r : ℕ) : Fin k ⊕ Fin r → Fin (k + r)
  | Sum.inl i => Fin.castAdd r i
  | Sum.inr j => Fin.natAdd k j

/-- The inverse variable map `Fin (k+r) → Fin k ⊕ Fin r`. -/
def finToSum (k r : ℕ) : Fin (k + r) → Fin k ⊕ Fin r := Fin.addCases Sum.inl Sum.inr

@[simp] theorem sumToFin_inl (i : Fin k) : sumToFin k r (Sum.inl i) = Fin.castAdd r i := rfl
@[simp] theorem sumToFin_inr (j : Fin r) : sumToFin k r (Sum.inr j) = Fin.natAdd k j := rfl
@[simp] theorem finToSum_castAdd (i : Fin k) : finToSum k r (Fin.castAdd r i) = Sum.inl i :=
  Fin.addCases_left i
@[simp] theorem finToSum_natAdd (j : Fin r) : finToSum k r (Fin.natAdd k j) = Sum.inr j :=
  Fin.addCases_right j
@[simp] theorem graphPt_castAdd (c : EAChain k r) (z : Fin k → ℝ) (i : Fin k) :
    graphPt c z (Fin.castAdd r i) = z i := by simp only [graphPt, Fin.append_left]
@[simp] theorem graphPt_natAdd (c : EAChain k r) (z : Fin k → ℝ) (j : Fin r) :
    graphPt c z (Fin.natAdd k j) = hvec c z j := by simp only [graphPt, Fin.append_right]

/-- The chain-value vector is a polynomial expression: each chain value is the exponential of
an affine function. -/
theorem hvec_exp (c : EAChain k r) (z : Fin k → ℝ) (j : Fin r) :
    hvec c z j = Real.exp (∑ i, c.a j i * z i + c.b j) := rfl

theorem graphPt_eq_elim (c : EAChain k r) (z : Fin k → ℝ) (y : Fin (k + r)) :
    graphPt c z y = Sum.elim z (hvec c z) (finToSum k r y) := by
  induction y using Fin.addCases with
  | left i => simp only [finToSum_castAdd, Sum.elim_inl, graphPt_castAdd]
  | right j => simp only [finToSum_natAdd, Sum.elim_inr, graphPt_natAdd]

theorem graphPt_comp_sumToFin (c : EAChain k r) (z : Fin k → ℝ) :
    graphPt c z ∘ sumToFin k r = Sum.elim z (hvec c z) := by
  funext y
  rcases y with i | j
  · simp only [Function.comp_apply, sumToFin_inl, Sum.elim_inl, graphPt_castAdd]
  · simp only [Function.comp_apply, sumToFin_inr, Sum.elim_inr, graphPt_natAdd]

theorem elim_comp_finToSum (c : EAChain k r) (z : Fin k → ℝ) :
    Sum.elim z (hvec c z) ∘ finToSum k r = graphPt c z := by
  funext y
  induction y using Fin.addCases with
  | left i => simp only [Function.comp_apply, finToSum_castAdd, Sum.elim_inl, graphPt_castAdd]
  | right j => simp only [Function.comp_apply, finToSum_natAdd, Sum.elim_inr, graphPt_natAdd]

/-- The same EA polynomial, viewed as a polynomial on the `(z,h)`-space. -/
def toCombined (Q : EAPoly k r) : MvPolynomial (Fin (k + r)) ℝ :=
  MvPolynomial.rename (sumToFin k r) Q

/-- The pullback of a polynomial in the `(z,h)`-space to an EA polynomial in `z`. -/
def eaOfCombined (Q : MvPolynomial (Fin (k + r)) ℝ) : EAPoly k r :=
  MvPolynomial.rename (finToSum k r) Q

@[simp] theorem toCombined_C (a : ℝ) :
    toCombined (k := k) (r := r) (MvPolynomial.C a) = MvPolynomial.C a :=
  MvPolynomial.rename_C (sumToFin k r) a

@[simp] theorem toCombined_X_inl (i : Fin k) :
    toCombined (k := k) (r := r) (MvPolynomial.X (Sum.inl i)) =
      MvPolynomial.X (Fin.castAdd r i) := by
  simp only [toCombined, sumToFin_inl, MvPolynomial.rename_X]

@[simp] theorem toCombined_X_inr (j : Fin r) :
    toCombined (k := k) (r := r) (MvPolynomial.X (Sum.inr j)) =
      MvPolynomial.X (Fin.natAdd k j) := by
  simp only [toCombined, sumToFin_inr, MvPolynomial.rename_X]

theorem toCombined_add (P Q : EAPoly k r) : toCombined (P + Q) = toCombined P + toCombined Q :=
  map_add _ _ _

theorem toCombined_mul (P Q : EAPoly k r) : toCombined (P * Q) = toCombined P * toCombined Q :=
  map_mul _ _ _

theorem toCombined_pow (P : EAPoly k r) (n : ℕ) : toCombined (P ^ n) = toCombined P ^ n :=
  map_pow _ _ _

theorem toCombined_sum {ι : Type*} (s : Finset ι) (f : ι → EAPoly k r) :
    toCombined (∑ i ∈ s, f i) = ∑ i ∈ s, toCombined (f i) :=
  map_sum _ _ _

theorem toCombined_prod {ι : Type*} (s : Finset ι) (f : ι → EAPoly k r) :
    toCombined (∏ i ∈ s, f i) = ∏ i ∈ s, toCombined (f i) :=
  map_prod _ _ _

theorem totalDegree_toCombined (Q : EAPoly k r) :
    (toCombined Q).totalDegree ≤ Q.totalDegree :=
  MvPolynomial.totalDegree_rename_le _ _

/-- The evaluation of an EA polynomial at `z` is the evaluation of the corresponding
polynomial at `(z, h(z))`. -/
theorem eaEval_eq_eval_graphPt (c : EAChain k r) (Q : EAPoly k r) (z : Fin k → ℝ) :
    eaEval c Q z = MvPolynomial.eval (graphPt c z) (toCombined Q) := by
  rw [toCombined, MvPolynomial.eval_rename, graphPt_comp_sumToFin]
  rfl

theorem eval_eaOfCombined (c : EAChain k r) (Q : MvPolynomial (Fin (k + r)) ℝ)
    (z : Fin k → ℝ) :
    MvPolynomial.eval (Sum.elim z (hvec c z)) (eaOfCombined (k := k) (r := r) Q) =
      MvPolynomial.eval (graphPt c z) Q := by
  rw [eaOfCombined, MvPolynomial.eval_rename, elim_comp_finToSum]

/-- The `SA`-sets live over the empty chain, so `eaEval` over `EAChain.nil` is polynomial
evaluation. -/
theorem eaEval_nil (m : ℕ) (Q : EAPoly m 0) (w : Fin m → ℝ) :
    eaEval (EAChain.nil m) Q w =
      MvPolynomial.eval (Sum.elim w (fun j : Fin 0 => j.elim0)) Q := by
  have h : (Sum.elim w (fun j : Fin 0 => Real.exp ((EAChain.nil m).ell j w))) =
      Sum.elim w (fun j : Fin 0 => j.elim0) := by
    funext i
    rcases i with i | j
    · rfl
    · exact j.elim0
  rw [eaEval, h]

/-! ## §2. Semialgebraic descriptions in the `(z,h)`-space -/

/-- `Fin m ⊕ Fin 0 ≃ Fin m`. -/
def sumFin0Equiv (m : ℕ) : Fin m ⊕ Fin 0 ≃ Fin m where
  toFun s := match s with
    | Sum.inl i => i
    | Sum.inr j => j.elim0
  invFun i := Sum.inl i
  left_inv := by
    rintro (i | j)
    · rfl
    · exact j.elim0
  right_inv := by intro i; rfl

@[simp] theorem sumFin0Equiv_inl (m : ℕ) (i : Fin m) : sumFin0Equiv m (Sum.inl i) = i := rfl
@[simp] theorem sumFin0Equiv_symm_apply (m : ℕ) (i : Fin m) :
    (sumFin0Equiv m).symm i = Sum.inl i := rfl

/-- The identification of the `SA m`-polynomial ring `MvPolynomial (Fin m ⊕ Fin 0) ℝ` with
`MvPolynomial (Fin m) ℝ`. -/
def saPolyAlgEquiv (m : ℕ) : MvPolynomial (Fin m) ℝ ≃ₐ[ℝ] EAPoly m 0 :=
  MvPolynomial.renameEquiv ℝ (sumFin0Equiv m).symm

/-- View a polynomial in `m` variables as an `SA m`-polynomial. -/
def saPoly (m : ℕ) (P : MvPolynomial (Fin m) ℝ) : EAPoly m 0 := saPolyAlgEquiv m P

theorem saPoly_eq_rename (m : ℕ) (P : MvPolynomial (Fin m) ℝ) :
    saPoly m P = MvPolynomial.rename (sumFin0Equiv m).symm P := rfl

@[simp] theorem saPoly_C (m : ℕ) (a : ℝ) : saPoly m (MvPolynomial.C a) = MvPolynomial.C a :=
  MvPolynomial.rename_C _ _

@[simp] theorem saPoly_X (m : ℕ) (i : Fin m) :
    saPoly m (MvPolynomial.X i) = MvPolynomial.X (Sum.inl i) := by
  simp only [saPoly_eq_rename, sumFin0Equiv_symm_apply, MvPolynomial.rename_X]

theorem saPoly_add (m : ℕ) (P Q : MvPolynomial (Fin m) ℝ) :
    saPoly m (P + Q) = saPoly m P + saPoly m Q := map_add _ _ _

theorem saPoly_mul (m : ℕ) (P Q : MvPolynomial (Fin m) ℝ) :
    saPoly m (P * Q) = saPoly m P * saPoly m Q := map_mul _ _ _

theorem saPoly_pow (m : ℕ) (P : MvPolynomial (Fin m) ℝ) (n : ℕ) :
    saPoly m (P ^ n) = saPoly m P ^ n := map_pow _ _ _

theorem saPoly_sum {ι : Type*} (m : ℕ) (s : Finset ι) (f : ι → MvPolynomial (Fin m) ℝ) :
    saPoly m (∑ i ∈ s, f i) = ∑ i ∈ s, saPoly m (f i) := map_sum _ _ _

theorem saPoly_prod {ι : Type*} (m : ℕ) (s : Finset ι) (f : ι → MvPolynomial (Fin m) ℝ) :
    saPoly m (∏ i ∈ s, f i) = ∏ i ∈ s, saPoly m (f i) := map_prod _ _ _

/-- Evaluation of `saPoly`. -/
theorem eval_saPoly (m : ℕ) (P : MvPolynomial (Fin m) ℝ) (x : Fin m → ℝ) :
    MvPolynomial.eval (Sum.elim x (fun i : Fin 0 => i.elim0)) (saPoly m P) =
      MvPolynomial.eval x P := by
  rw [saPoly_eq_rename, MvPolynomial.eval_rename]
  rfl

/-- The degree of a polynomial in `m` variables, matching `atomDeg`. -/
def degP {σ : Type*} (P : MvPolynomial σ ℝ) : ℕ := P.totalDegree + 1

theorem totalDegree_saPoly (m : ℕ) (P : MvPolynomial (Fin m) ℝ) :
    (saPoly m P).totalDegree = P.totalDegree := by
  have h1 : (saPoly m P).totalDegree ≤ P.totalDegree := by
    rw [saPoly_eq_rename]
    exact MvPolynomial.totalDegree_rename_le _ _
  have h2 : P.totalDegree ≤ (saPoly m P).totalDegree := by
    have h := MvPolynomial.totalDegree_rename_le (⇑(sumFin0Equiv m)) (saPoly m P)
    have hkey : MvPolynomial.rename (⇑(sumFin0Equiv m)) (saPoly m P) = P := by
      rw [saPoly_eq_rename, MvPolynomial.rename_rename, Equiv.self_comp_symm,
        MvPolynomial.rename_id_apply]
    rwa [hkey] at h
  exact le_antisymm h1 h2

theorem atomDeg_saPoly (m : ℕ) (P : MvPolynomial (Fin m) ℝ) :
    atomDeg (saPoly m P) = degP P := by
  simp only [atomDeg, degP, totalDegree_saPoly]

/-- Turn a semialgebraic basic set in `m` variables (in `MvPolynomial (Fin m) ℝ`) into the
`SA m` basic set. -/
def saBasic (m : ℕ) (eqs pos : List (MvPolynomial (Fin m) ℝ)) : Basic m 0 :=
  ⟨eqs.map (saPoly m), pos.map (saPoly m)⟩

theorem map_atomDeg_saPoly (m : ℕ) (L : List (MvPolynomial (Fin m) ℝ)) :
    (L.map (atomDeg ∘ saPoly m)) = L.map degP := by
  induction L with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, ih, Function.comp_apply, atomDeg_saPoly]

theorem saBasic_deg (m : ℕ) (eqs pos : List (MvPolynomial (Fin m) ℝ)) :
    (saBasic m eqs pos).deg = (eqs.map degP).sum + (pos.map degP).sum := by
  simp only [saBasic, Basic.deg, List.map_append, List.sum_append, List.map_map]
  rw [map_atomDeg_saPoly m eqs, map_atomDeg_saPoly m pos]

/-- The pullback of an `SA (k+r)`-polynomial to an EA polynomial in `z`. -/
def eaOfSa (Q : EAPoly (k + r) 0) : EAPoly k r :=
  MvPolynomial.rename (fun i : Fin (k + r) ⊕ Fin 0 => finToSum k r (sumFin0Equiv (k + r) i)) Q

theorem atomDeg_eaOfSa (Q : EAPoly (k + r) 0) :
    atomDeg (eaOfSa (k := k) (r := r) Q) ≤ atomDeg Q := by
  simp only [atomDeg]
  exact Nat.add_le_add_right (MvPolynomial.totalDegree_rename_le _ Q) 1

theorem eval_eaOfSa (c : EAChain k r) (Q : EAPoly (k + r) 0) (z : Fin k → ℝ) :
    MvPolynomial.eval (Sum.elim z (hvec c z)) (eaOfSa (k := k) (r := r) Q) =
      MvPolynomial.eval (Sum.elim (graphPt c z) (fun i : Fin 0 => i.elim0)) Q := by
  rw [eaOfSa, MvPolynomial.eval_rename]
  have hfun : (Sum.elim z (hvec c z)) ∘
      (fun i : Fin (k + r) ⊕ Fin 0 => finToSum k r (sumFin0Equiv (k + r) i)) =
      Sum.elim (graphPt c z) (fun i : Fin 0 => i.elim0) := by
    funext i
    match i with
    | Sum.inl y =>
        simp only [Function.comp_apply, sumFin0Equiv_inl, Sum.elim_inl]
        exact (graphPt_eq_elim c z y).symm
    | Sum.inr j => simp only [Function.comp_apply, Sum.elim_inr]; exact j.elim0
  rw [hfun]

/-- Pull a basic set of the `(z,h)`-space back to a basic set in `z`. -/
def basicPullback (B : Basic (k + r) 0) : Basic k r :=
  ⟨B.eqs.map (eaOfSa (k := k) (r := r)), B.pos.map (eaOfSa (k := k) (r := r))⟩

/-- The `SemiPf` set obtained from a semialgebraic description in the `(z,h)`-space by
substituting the chain functions. -/
def saPullback (c : EAChain k r) (X : SA (k + r)) : SemiPf k where
  r := r
  c := c
  basics := X.basics.map basicPullback

@[simp] theorem saPullback_fmt (c : EAChain k r) (X : SA (k + r)) :
    (saPullback c X).fmt = k + r := rfl

theorem saPullback_basics (c : EAChain k r) (X : SA (k + r)) :
    (saPullback c X).basics = X.basics.map basicPullback := rfl

theorem basicPullback_deg_le (B : Basic (k + r) 0) :
    (basicPullback (k := k) (r := r) B).deg ≤ B.deg := by
  simp only [basicPullback, Basic.deg, List.map_append, List.sum_append, List.map_map]
  exact add_le_add (List.sum_le_sum fun Q _ => atomDeg_eaOfSa Q)
    (List.sum_le_sum fun Q _ => atomDeg_eaOfSa Q)

/-- The `deg` of the pullback is bounded by the `deg` of the semialgebraic description. -/
theorem saPullback_deg_le (c : EAChain k r) (X : SA (k + r)) :
    (saPullback c X).deg ≤ X.deg := by
  have hsum : ∀ L : List (Basic (k + r) 0),
      (List.map (Basic.deg (k := k) (r := r))
        (List.map (basicPullback (k := k) (r := r)) L)).sum ≤
        (List.map (Basic.deg (k := (k + r)) (r := 0)) L).sum := by
    intro L
    rw [List.map_map]
    exact List.sum_le_sum fun B _ => basicPullback_deg_le B
  show (List.map (Basic.deg (k := k) (r := r)) (saPullback c X).basics).sum ≤
    (List.map (Basic.deg (k := (k + r)) (r := 0)) X.basics).sum
  rw [saPullback_basics]
  exact hsum X.basics

/-- A basic set of the `(z,h)`-space, evaluated at `(z,h(z))`, is the pullback basic set
evaluated at `z`. -/
theorem basicPullback_holds (c : EAChain k r) (B : Basic (k + r) 0) (z : Fin k → ℝ) :
    (basicPullback (k := k) (r := r) B).holds c z ↔
      B.holds (EAChain.nil (k + r)) (graphPt c z) := by
  constructor
  · rintro ⟨heq, hpos⟩
    refine ⟨?_, ?_⟩
    · intro Q hQ
      have hmem : eaOfSa (k := k) (r := r) Q ∈
          (basicPullback (k := k) (r := r) B).eqs := List.mem_map.mpr ⟨Q, hQ, rfl⟩
      rw [eaEval_nil, ← eval_eaOfSa (c := c) Q z]
      exact heq _ hmem
    · intro Q hQ
      have hmem : eaOfSa (k := k) (r := r) Q ∈
          (basicPullback (k := k) (r := r) B).pos := List.mem_map.mpr ⟨Q, hQ, rfl⟩
      rw [eaEval_nil, ← eval_eaOfSa (c := c) Q z]
      exact hpos _ hmem
  · rintro ⟨heq, hpos⟩
    simp only [eaEval_nil] at heq hpos
    refine ⟨?_, ?_⟩
    · intro Q hQ
      obtain ⟨Q₀, hQ₀, rfl⟩ := List.mem_map.mp hQ
      change MvPolynomial.eval (Sum.elim z (hvec c z)) (eaOfSa (k := k) (r := r) Q₀) = 0
      rw [eval_eaOfSa]
      exact heq Q₀ hQ₀
    · intro Q hQ
      obtain ⟨Q₀, hQ₀, rfl⟩ := List.mem_map.mp hQ
      change 0 < MvPolynomial.eval (Sum.elim z (hvec c z)) (eaOfSa (k := k) (r := r) Q₀)
      rw [eval_eaOfSa]
      exact hpos Q₀ hQ₀

/-- Membership in the pullback: this is the "substitution `h := E(y)`" step. -/
theorem mem_saPullback_iff (c : EAChain k r) (X : SA (k + r)) (z : Fin k → ℝ) :
    z ∈ (saPullback c X).set ↔ z ∈ cubeC k ∧ graphPt c z ∈ X.set := by
  constructor
  · rintro ⟨hzcube, B, hB, hBolds⟩
    rw [saPullback_basics] at hB
    obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.mp hB
    exact ⟨hzcube, B₀, hB₀, (basicPullback_holds c B₀ z).mp hBolds⟩
  · rintro ⟨hzcube, B₀, hB₀, hBolds⟩
    exact ⟨hzcube, basicPullback B₀, List.mem_map.mpr ⟨B₀, hB₀, rfl⟩,
      (basicPullback_holds c B₀ z).mpr hBolds⟩

end Work.WilE6
