/-
  WilE8 / Box — the semi-Pfaffian presentation of the box-zero sets `boxZero M P`.

  `boxZero M P = {z : ℝ^N | (∀ i, |z i| ≤ M) ∧ expPolyEval P z = 0}` is the zero set of the
  exp-polynomial `P` inside the box `[-M,M]^N`.  We want to present it as a `StarR`-set, i.e.
  as `psiV ⁻¹' Z` for a `*`-set `Z ⊆ ℝ^N`, with format and degree independent of `M`.

  The presentation is built on the *compactifying* map `psi (x) = x/√(1+x²)`, which is a
  bijection `ℝ → (-1,1)`:  since `psiV` always lands in the closed cube, a `StarR`-set is the
  `psiV`-preimage of a union of projections of connected components of semi-Pfaffian sets
  living in the cube.

  The semi-Pfaffian set we use has `3N` coordinates, split into three blocks
  `(t, s, u) ∈ cubeC (N + (N + N))`:

  * `t` (the first `N` coordinates) carries `psi (z i)`;
  * `s` (the next `N` coordinates) carries `z i / M`;
  * `u` (the last `N` coordinates) is a slack variable witnessing `t i * s i ≥ 0`.

  The basic set imposes

  * `t i ^ 2 * (1 + M ^ 2 * s i ^ 2) = M ^ 2 * s i ^ 2` — the algebraic characterisation of
    `t i = ± psi (M * s i)`;
  * `t i * s i = u i ^ 2` — which selects the correct sign, i.e. `t i = psi (M * s i)`;
  * `P (M * s, exp (M * s)) = 0` — the pullback of the equation along `z = M * s`.

  The chain of the semi-Pfaffian set is `exp (M * s i)`, so that the format is `4N` and the
  degree is bounded by `8N + deg P + 1`, both independent of `M`; this is where the
  uniformity of the exponential chain in the coefficients (frozen design, `boxZero`) is used.
-/
import Mathlib
import Submission.Work.WilE8.Basic
import Submission.Work.WilE10.Psi

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilE8.Box

open WilkiesDesign WilkiesDesign.E

/-! ## Coordinates -/

/-- The `t`-block coordinate: the first `N` coordinates of `Fin (N + (N + N))`. -/
def tCoord (N : ℕ) (i : Fin N) : Fin (N + (N + N)) := Fin.castAdd (N + N) i

/-- The `s`-block coordinate: coordinates `N … 2N-1` of `Fin (N + (N + N))`. -/
def sCoord (N : ℕ) (j : Fin N) : Fin (N + (N + N)) := ⟨N + j.1, by have := j.2; omega⟩

/-- The `u`-block coordinate: the last `N` coordinates of `Fin (N + (N + N))`. -/
def uCoord (N : ℕ) (j : Fin N) : Fin (N + (N + N)) := ⟨N + N + j.1, by have := j.2; omega⟩

lemma tCoord_inj (N : ℕ) : Function.Injective (tCoord N) := by
  intro i j h
  have h' : ((tCoord N i : Fin (N + (N + N))) : ℕ) = ((tCoord N j : Fin (N + (N + N))) : ℕ) :=
    congrArg Fin.val h
  simp only [tCoord, Fin.val_castAdd] at h'
  exact Fin.ext h'

/-! ## The exponential chain `exp (M * s i)` -/

/-- The coefficients of the exp-affine chain `ell j x = M * x (sCoord j)`. -/
def chainCoeff (N : ℕ) (M : ℝ) (j : Fin N) (i : Fin (N + (N + N))) : ℝ :=
  if i = sCoord N j then M else 0

/-- The chain of `N` exponential functions `exp (M * s j)`. -/
def chainC (N : ℕ) (M : ℝ) : EAChain (N + (N + N)) N :=
  ⟨chainCoeff N M, fun _ => 0⟩

lemma ell_chainC (N : ℕ) (M : ℝ) (j : Fin N) (x : Fin (N + (N + N)) → ℝ) :
    (chainC N M).ell j x = M * x (sCoord N j) := by
  simp only [EAChain.ell, chainC, chainCoeff, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' _ _ (fun i => M * x i)]
  simp

/-! ## The defining polynomials -/

/-- `t² (1 + (M s)²) = (M s)²`: `t = ± psi (M s)`. -/
def psiEqPoly (N : ℕ) (M : ℝ) (i : Fin N) : EAPoly (N + (N + N)) N :=
  (MvPolynomial.X (Sum.inl (tCoord N i))) ^ 2 *
      (1 + MvPolynomial.C (M ^ 2) * (MvPolynomial.X (Sum.inl (sCoord N i))) ^ 2) -
    MvPolynomial.C (M ^ 2) * (MvPolynomial.X (Sum.inl (sCoord N i))) ^ 2

/-- `t s = u²`: the sign condition selecting `t = psi (M s)`. -/
def signPoly (N : ℕ) (i : Fin N) : EAPoly (N + (N + N)) N :=
  MvPolynomial.X (Sum.inl (tCoord N i)) * MvPolynomial.X (Sum.inl (sCoord N i)) -
    (MvPolynomial.X (Sum.inl (uCoord N i))) ^ 2

/-- The pullback of `P` along `z ↦ M * s`: variable `Sum.inl i ↦ M * s i`,
variable `Sum.inr i ↦ exp (M * s i)` (the chain variable `i`). -/
def substP (N : ℕ) (M : ℝ) (P : MvPolynomial (Fin N ⊕ Fin N) ℝ) : EAPoly (N + (N + N)) N :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun v => match v with
      | Sum.inl i => MvPolynomial.C M * MvPolynomial.X (Sum.inl (sCoord N i))
      | Sum.inr i => MvPolynomial.X (Sum.inr i)) P

/-- The single basic set (equations only) of the presentation. -/
def boxBasic (N : ℕ) (M : ℝ) (P : MvPolynomial (Fin N ⊕ Fin N) ℝ) : Basic (N + (N + N)) N :=
  ⟨((List.finRange N).map (fun i => psiEqPoly N M i)) ++
   ((List.finRange N).map (fun i => signPoly N i)) ++
   [substP N M P], []⟩

/-- The semi-Pfaffian set presenting `boxZero M P` in the `psi`-coordinates. -/
def boxSemiPf (N : ℕ) (M : ℝ) (P : MvPolynomial (Fin N ⊕ Fin N) ℝ) : SemiPf (N + (N + N)) :=
  ⟨N, chainC N M, [boxBasic N M P]⟩

/-! ## Evaluation of the defining polynomials -/

/-- Substitution commutes with evaluation. -/
lemma eval_eval₂Hom {ι κ : Type*} (d : κ → ℝ) (q : ι → MvPolynomial κ ℝ)
    (p : MvPolynomial ι ℝ) :
    MvPolynomial.eval d (MvPolynomial.eval₂Hom MvPolynomial.C q p) =
      MvPolynomial.eval (fun i => MvPolynomial.eval d (q i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => simp only [map_add, hp, hr]
  | mul_X p i hp => simp only [map_mul, MvPolynomial.eval₂Hom_X', MvPolynomial.eval_X, hp]

lemma eaEval_psiEqPoly (N : ℕ) (M : ℝ) (i : Fin N) (x : Fin (N + (N + N)) → ℝ) :
    eaEval (chainC N M) (psiEqPoly N M i) x =
      x (tCoord N i) ^ 2 * (1 + M ^ 2 * x (sCoord N i) ^ 2) - M ^ 2 * x (sCoord N i) ^ 2 := by
  simp only [eaEval, psiEqPoly, map_sub, map_mul, map_pow, map_add, map_one,
    MvPolynomial.eval_X, MvPolynomial.eval_C, Sum.elim_inl]

lemma eaEval_signPoly (N : ℕ) (M : ℝ) (i : Fin N) (x : Fin (N + (N + N)) → ℝ) :
    eaEval (chainC N M) (signPoly N i) x =
      x (tCoord N i) * x (sCoord N i) - x (uCoord N i) ^ 2 := by
  simp only [eaEval, signPoly, map_sub, map_mul, map_pow, MvPolynomial.eval_X, Sum.elim_inl]

/-- Evaluating the pullback of `P` under the chain `exp (M s)` gives the exp-polynomial `P`
evaluated at `M • s`. -/
lemma eaEval_substP (N : ℕ) (M : ℝ) (P : MvPolynomial (Fin N ⊕ Fin N) ℝ)
    (x : Fin (N + (N + N)) → ℝ) :
    eaEval (chainC N M) (substP N M P) x = expPolyEval P (fun i => M * x (sCoord N i)) := by
  have hd : (fun i => MvPolynomial.eval (Sum.elim x (fun j => Real.exp ((chainC N M).ell j x)))
        (match i with
         | Sum.inl i => MvPolynomial.C M * MvPolynomial.X (Sum.inl (sCoord N i))
         | Sum.inr i => MvPolynomial.X (Sum.inr i)))
      = Sum.elim (fun i => M * x (sCoord N i)) (fun i => Real.exp (M * x (sCoord N i))) := by
    funext v
    rcases v with i | j
    · simp
    · simp only [MvPolynomial.eval_X, Sum.elim_inr]
      rw [ell_chainC]
  rw [eaEval, substP, eval_eval₂Hom, expPolyEval, hd]

/-! ## Degree bounds -/

/-- Substitution of variables by polynomials of total degree `≤ 1` does not increase the total
degree. -/
lemma totalDegree_eval₂Hom_le {σ τ : Type*} (φ : σ → MvPolynomial τ ℝ)
    (hφ : ∀ v, (φ v).totalDegree ≤ 1) (P : MvPolynomial σ ℝ) :
    (MvPolynomial.eval₂Hom MvPolynomial.C φ P).totalDegree ≤ P.totalDegree := by
  have hsum : MvPolynomial.eval₂Hom MvPolynomial.C φ P
      = ∑ m ∈ P.support, MvPolynomial.C (P.coeff m) * (m.prod fun i k => φ i ^ k) := by
    conv_lhs => rw [MvPolynomial.as_sum P]
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.eval₂Hom_monomial]
  rw [hsum]
  refine MvPolynomial.totalDegree_finsetSum_le fun m hm => ?_
  have hprod : (m.prod fun i k => φ i ^ k).totalDegree
      ≤ ∑ i ∈ m.support, m i * (φ i).totalDegree := by
    rw [Finsupp.prod]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact (MvPolynomial.totalDegree_pow (φ i) (m i)).trans (le_of_eq (by ring))
  calc (MvPolynomial.C (P.coeff m) * (m.prod fun i k => φ i ^ k)).totalDegree
      ≤ (MvPolynomial.C (P.coeff m)).totalDegree + (m.prod fun i k => φ i ^ k).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + ∑ i ∈ m.support, m i * (φ i).totalDegree := by
        rw [MvPolynomial.totalDegree_C]; exact add_le_add le_rfl hprod
    _ ≤ ∑ i ∈ m.support, m i := by
        rw [Nat.zero_add]
        exact Finset.sum_le_sum fun i _ => by
          calc m i * (φ i).totalDegree ≤ m i * 1 := Nat.mul_le_mul_left _ (hφ i)
            _ = m i := Nat.mul_one _
    _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hm

lemma totalDegree_X2 (N : ℕ) (a : Fin (N + (N + N))) :
    (MvPolynomial.X (Sum.inl a) ^ 2 : EAPoly (N + (N + N)) N).totalDegree ≤ 2 :=
  le_of_eq (MvPolynomial.totalDegree_X_pow _ 2)

lemma totalDegree_psiEqPoly (N : ℕ) (M : ℝ) (i : Fin N) :
    (psiEqPoly N M i).totalDegree ≤ 4 := by
  have hB : (1 + MvPolynomial.C (M ^ 2) *
      (MvPolynomial.X (Sum.inl (sCoord N i)) : EAPoly (N + (N+N)) N) ^ 2).totalDegree ≤ 2 := by
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le (by simp) ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, Nat.zero_add]
    exact totalDegree_X2 N _
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
  · calc (MvPolynomial.X (Sum.inl (tCoord N i)) ^ 2 *
        (1 + MvPolynomial.C (M ^ 2) *
          (MvPolynomial.X (Sum.inl (sCoord N i)) : EAPoly (N + (N+N)) N) ^ 2)).totalDegree
      ≤ (MvPolynomial.X (Sum.inl (tCoord N i)) ^ 2 : EAPoly (N+(N+N)) N).totalDegree +
        (1 + MvPolynomial.C (M ^ 2) *
          (MvPolynomial.X (Sum.inl (sCoord N i)) : EAPoly (N + (N+N)) N) ^ 2).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 2 + 2 := add_le_add (totalDegree_X2 N _) hB
      _ ≤ 4 := by norm_num
  · calc (MvPolynomial.C (M ^ 2) *
        (MvPolynomial.X (Sum.inl (sCoord N i)) : EAPoly (N + (N+N)) N) ^ 2).totalDegree
      ≤ (MvPolynomial.C (M ^ 2) : EAPoly (N+(N+N)) N).totalDegree +
        (MvPolynomial.X (Sum.inl (sCoord N i)) ^ 2 : EAPoly (N+(N+N)) N).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 0 + 2 := add_le_add (le_of_eq (MvPolynomial.totalDegree_C _)) (totalDegree_X2 N _)
      _ ≤ 4 := by norm_num

lemma totalDegree_signPoly (N : ℕ) (i : Fin N) : (signPoly N i).totalDegree ≤ 2 := by
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
  · calc (MvPolynomial.X (Sum.inl (tCoord N i)) *
        (MvPolynomial.X (Sum.inl (sCoord N i)) : EAPoly (N+(N+N)) N)).totalDegree
      ≤ (MvPolynomial.X (Sum.inl (tCoord N i)) : EAPoly (N+(N+N)) N).totalDegree +
        (MvPolynomial.X (Sum.inl (sCoord N i)) : EAPoly (N+(N+N)) N).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 1 + 1 := add_le_add (le_of_eq (MvPolynomial.totalDegree_X _))
          (le_of_eq (MvPolynomial.totalDegree_X _))
      _ ≤ 2 := by norm_num
  · calc ((MvPolynomial.X (Sum.inl (uCoord N i)) : EAPoly (N+(N+N)) N) ^ 2).totalDegree
      ≤ 2 := totalDegree_X2 N _

lemma totalDegree_substP (N : ℕ) (M : ℝ) (P : MvPolynomial (Fin N ⊕ Fin N) ℝ) :
    (substP N M P).totalDegree ≤ P.totalDegree := by
  unfold substP
  refine totalDegree_eval₂Hom_le _ (fun v => ?_) P
  rcases v with i | j
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, Nat.zero_add]
    exact le_of_eq (MvPolynomial.totalDegree_X _)
  · exact le_of_eq (MvPolynomial.totalDegree_X _)

/-! ## Membership in the equations -/

lemma mem_boxBasic_psiEq (N : ℕ) (M : ℝ) (P : MvPolynomial (Fin N ⊕ Fin N) ℝ) (i : Fin N) :
    psiEqPoly N M i ∈ (boxBasic N M P).eqs := by
  have h1 : psiEqPoly N M i ∈ (List.finRange N).map (fun i => psiEqPoly N M i) :=
    List.mem_map_of_mem (f := fun i => psiEqPoly N M i) (List.mem_finRange i)
  simp only [boxBasic]
  exact List.mem_append_left _ (List.mem_append_left _ h1)

/-- Membership in the equations of `boxBasic`: only the atoms are used, and any atom in the
`psi`-list or the `sign`-list can be picked by its index. -/
lemma mem_boxBasic_sign (N : ℕ) (M : ℝ) (P : MvPolynomial (Fin N ⊕ Fin N) ℝ) (i : Fin N) :
    signPoly N i ∈ (boxBasic N M P).eqs := by
  have h1 : signPoly N i ∈ (List.finRange N).map (fun i => signPoly N i) :=
    List.mem_map_of_mem (f := fun i => signPoly N i) (List.mem_finRange i)
  simp only [boxBasic]
  exact List.mem_append_left _ (List.mem_append_right _ h1)

lemma mem_boxBasic_substP (N : ℕ) (M : ℝ) (P : MvPolynomial (Fin N ⊕ Fin N) ℝ) :
    substP N M P ∈ (boxBasic N M P).eqs := by
  simp only [boxBasic]
  exact List.mem_append_right _ (List.mem_singleton_self _)

/-! ## The degree of the presentation -/

/-- The degree of the basic set of the presentation is bounded by `8N + deg P + 1`,
independently of `M`. -/
lemma boxBasic_deg_le (N : ℕ) (M : ℝ) (d : ℕ) (P : MvPolynomial (Fin N ⊕ Fin N) ℝ)
    (hd : P.totalDegree ≤ d) : (boxBasic N M P).deg ≤ 8 * N + d + 1 := by
  have h1 : ((((List.finRange N).map (fun i => psiEqPoly N M i)).map atomDeg).sum) ≤ N * 5 := by
    have h := List.sum_le_length_nsmul
      (((List.finRange N).map (fun i => psiEqPoly N M i)).map atomDeg) 5 (by
        intro x hx
        rw [List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        rw [List.mem_map] at hy
        obtain ⟨i, -, rfl⟩ := hy
        exact Nat.succ_le_succ (totalDegree_psiEqPoly N M i))
    simpa using h
  have h2 : ((((List.finRange N).map (fun i => signPoly N i)).map atomDeg).sum) ≤ N * 3 := by
    have h := List.sum_le_length_nsmul
      (((List.finRange N).map (fun i => signPoly N i)).map atomDeg) 3 (by
        intro x hx
        rw [List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        rw [List.mem_map] at hy
        obtain ⟨i, -, rfl⟩ := hy
        exact Nat.succ_le_succ (totalDegree_signPoly N i))
    simpa using h
  have h3 : atomDeg (substP N M P) ≤ d + 1 :=
    Nat.succ_le_succ ((totalDegree_substP N M P).trans hd)
  simp only [boxBasic, Basic.deg, List.append_nil, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

/-- The degree of the semi-Pfaffian set of the presentation, same bound. -/
lemma boxSemiPf_deg_le (N : ℕ) (M : ℝ) (d : ℕ) (P : MvPolynomial (Fin N ⊕ Fin N) ℝ)
    (hd : P.totalDegree ≤ d) : (boxSemiPf N M P).deg ≤ 8 * N + d + 1 := by
  have h := boxBasic_deg_le N M d P hd
  simpa [boxSemiPf, SemiPf.deg] using h

/-- The format of the presentation is `4N`. -/
lemma boxSemiPf_fmt (N : ℕ) (M : ℝ) (P : MvPolynomial (Fin N ⊕ Fin N) ℝ) :
    (boxSemiPf N M P).fmt = (N + (N + N)) + N := rfl

/-! ## Membership characterisation -/

/-- The set of the presentation, written out (no structure projections, so that all the
arities and formats are syntactically visible). -/
def boxSet (N : ℕ) (M : ℝ) (P : MvPolynomial (Fin N ⊕ Fin N) ℝ) :
    Set (Fin (N + (N + N)) → ℝ) :=
  {x | x ∈ cubeC (N + (N + N)) ∧ (boxBasic N M P).holds (chainC N M) x}

lemma boxSemiPf_set (N : ℕ) (M : ℝ) (P : MvPolynomial (Fin N ⊕ Fin N) ℝ) :
    (boxSemiPf N M P).set = boxSet N M P := by
  ext x
  constructor
  · intro hx
    obtain ⟨hcube, B, hB, hholds⟩ := hx
    obtain rfl : B = boxBasic N M P := List.mem_singleton.mp hB
    exact ⟨hcube, hholds⟩
  · rintro ⟨hcube, hholds⟩
    exact ⟨hcube, boxBasic N M P, List.mem_singleton_self _, hholds⟩

/-- A point of `boxSet N M P` is characterised by the cube condition and the three families of
equations. -/
lemma mem_boxSet_iff {N : ℕ} {M : ℝ} {P : MvPolynomial (Fin N ⊕ Fin N) ℝ}
    {x : Fin (N + (N + N)) → ℝ} :
    x ∈ boxSet N M P ↔
      x ∈ cubeC (N + (N + N)) ∧
      (∀ i, x (tCoord N i) ^ 2 * (1 + M ^ 2 * x (sCoord N i) ^ 2) =
        M ^ 2 * x (sCoord N i) ^ 2) ∧
      (∀ i, x (tCoord N i) * x (sCoord N i) = x (uCoord N i) ^ 2) ∧
      expPolyEval P (fun i => M * x (sCoord N i)) = 0 := by
  constructor
  · rintro ⟨hcube, hholds⟩
    refine ⟨hcube, fun i => ?_, fun i => ?_, ?_⟩
    · have h := hholds.1 (psiEqPoly N M i) (mem_boxBasic_psiEq N M P i)
      rw [eaEval_psiEqPoly] at h
      exact sub_eq_zero.mp h
    · have h := hholds.1 (signPoly N i) (mem_boxBasic_sign N M P i)
      rw [eaEval_signPoly] at h
      exact sub_eq_zero.mp h
    · have h := hholds.1 (substP N M P) (mem_boxBasic_substP N M P)
      rwa [eaEval_substP] at h
  · rintro ⟨hcube, h1, h2, h3⟩
    refine ⟨hcube, fun f hf => ?_, fun g hg => ?_⟩
    · simp only [boxBasic] at hf
      rcases List.mem_append.mp hf with hf | hf
      · rcases List.mem_append.mp hf with hf | hf
        · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hf
          rw [eaEval_psiEqPoly, h1 i, sub_self]
        · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hf
          rw [eaEval_signPoly, h2 i, sub_self]
      · obtain rfl := List.mem_singleton.mp hf
        rw [eaEval_substP, h3]
    · simp only [boxBasic] at hg
      exact absurd hg (by simp)

/-- Membership in the presentation, in coordinates. -/
lemma mem_boxSemiPf_iff {N : ℕ} {M : ℝ} {P : MvPolynomial (Fin N ⊕ Fin N) ℝ}
    {x : Fin (N + (N + N)) → ℝ} :
    x ∈ (boxSemiPf N M P).set ↔
      x ∈ cubeC (N + (N + N)) ∧
      (∀ i, x (tCoord N i) ^ 2 * (1 + M ^ 2 * x (sCoord N i) ^ 2) =
        M ^ 2 * x (sCoord N i) ^ 2) ∧
      (∀ i, x (tCoord N i) * x (sCoord N i) = x (uCoord N i) ^ 2) ∧
      expPolyEval P (fun i => M * x (sCoord N i)) = 0 := by
  rw [boxSemiPf_set, mem_boxSet_iff]

/-! ## Auxiliary facts about `psi` -/

/-- `psi` and the identity have the same sign. -/
lemma psi_mul_self_nonneg (x : ℝ) : 0 ≤ psi x * x := by
  have h : psi x * x = x ^ 2 / Real.sqrt (1 + x ^ 2) := by
    rw [psi]; field_simp
  rw [h]
  positivity

end Work.WilE8.Box
