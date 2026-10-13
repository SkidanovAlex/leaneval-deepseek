/-
  WilE10 — `E10_rexp_to_subpf`: definitions.

  Given an rexp-polynomial `P` in `N = n + m` variables we build a semi-Pfaffian set `W` in
  `ℝ^(n+rd)` whose projection to the first `n` coordinates, pulled back along `psiV`, is exactly
  `{x | ∃ y, rexpPolyEval P (Fin.append x y) = 0}`.

  The ambient coordinates of `W` are, in blocks:
  * `uᵢ` (`i : Fin n`): the compactified coordinates, which are the projected ones;
  * `tᵢ` (`i : Fin (n+m)`): the value of the `i`-th argument, in the "small" branch `|tᵢ| ≤ 1`;
  * `sᵢ`: the reciprocal of the value, in the "large" branch `|tᵢ| > 1`;
  * `qᵢ`: a tag witnessing `tᵢ² + qᵢ² = 1` (i.e. `|tᵢ| ≤ 1`) in the small branch;
  * `wᵢ` (`i : Fin n`): a tag witnessing the sign condition `uᵢ·tᵢ ≥ 0` in the small branch.

  The chain is `exp (tⱼ)`.
-/
import Submission.Work.WilE10.Branch

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE10

open WilkiesDesign WilkiesDesign.E

/-! ## The index types -/

/-- The auxiliary coordinates. -/
abbrev Aux (n m : ℕ) : Type := Fin (n + m) ⊕ (Fin (n + m) ⊕ (Fin (n + m) ⊕ Fin n))

/-- The ambient coordinates: the `n` compactified ones, then the auxiliary block. -/
abbrev Idx (n m : ℕ) : Type := Fin n ⊕ Aux n m

/-- Number of auxiliary coordinates. -/
abbrev rd (n m : ℕ) : ℕ := (n + m) + ((n + m) + ((n + m) + n))

/-- Number of ambient coordinates. -/
abbrev Kdim (n m : ℕ) : ℕ := n + rd n m

/-- Flattening of the auxiliary block. -/
def eB (n m : ℕ) : Aux n m ≃ Fin (rd n m) :=
  (Equiv.sumCongr (Equiv.refl (Fin (n + m)))
      ((Equiv.sumCongr (Equiv.refl (Fin (n + m)))
          (finSumFinEquiv : Fin (n + m) ⊕ Fin n ≃ Fin ((n + m) + n))).trans
        (finSumFinEquiv : Fin (n + m) ⊕ Fin ((n + m) + n) ≃ Fin ((n + m) + ((n + m) + n))))).trans
    (finSumFinEquiv :
      Fin (n + m) ⊕ Fin ((n + m) + ((n + m) + n)) ≃ Fin ((n + m) + ((n + m) + ((n + m) + n))))

/-- Flattening of the ambient index type; the first `n` coordinates are the compactified ones. -/
def eA (n m : ℕ) : Idx n m ≃ Fin (Kdim n m) :=
  (Equiv.sumCongr (Equiv.refl (Fin n)) (eB n m)).trans
    (finSumFinEquiv : Fin n ⊕ Fin (rd n m) ≃ Fin (n + rd n m))

/-- The block-`u` index. -/
def uIdx (n m : ℕ) : Fin n → Idx n m := fun i => Sum.inl i
/-- The block-`t` index. -/
def tIdx (n m : ℕ) : Fin (n + m) → Idx n m := fun i => Sum.inr (Sum.inl i)
/-- The block-`s` index. -/
def sIdx (n m : ℕ) : Fin (n + m) → Idx n m := fun i => Sum.inr (Sum.inr (Sum.inl i))
/-- The block-`q` index. -/
def qIdx (n m : ℕ) : Fin (n + m) → Idx n m :=
  fun i => Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))
/-- The block-`w` index. -/
def wIdx (n m : ℕ) : Fin n → Idx n m := fun i => Sum.inr (Sum.inr (Sum.inr (Sum.inr i)))

theorem eA_uIdx (n m : ℕ) (i : Fin n) : eA n m (uIdx n m i) = Fin.castAdd (rd n m) i := by
  simp only [eA, uIdx, Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.refl_apply, Sum.map_inl,
    finSumFinEquiv_apply_left]

/-- The ambient index of the `i`-th `u`-coordinate. -/
def uu (n m : ℕ) : Fin n → Fin (Kdim n m) := fun i => eA n m (uIdx n m i)
/-- The ambient index of the `i`-th `t`-coordinate. -/
def ut (n m : ℕ) : Fin (n + m) → Fin (Kdim n m) := fun i => eA n m (tIdx n m i)
/-- The ambient index of the `i`-th `s`-coordinate. -/
def us (n m : ℕ) : Fin (n + m) → Fin (Kdim n m) := fun i => eA n m (sIdx n m i)
/-- The ambient index of the `i`-th `q`-coordinate. -/
def uq (n m : ℕ) : Fin (n + m) → Fin (Kdim n m) := fun i => eA n m (qIdx n m i)
/-- The ambient index of the `i`-th `w`-coordinate. -/
def uw (n m : ℕ) : Fin n → Fin (Kdim n m) := fun i => eA n m (wIdx n m i)

theorem uu_eq (n m : ℕ) (i : Fin n) : uu n m i = Fin.castAdd (rd n m) i := eA_uIdx n m i

/-! ## The chain `exp (tⱼ)` -/

def chain (n m : ℕ) : EAChain (Kdim n m) (n + m) :=
  ⟨fun j k => if k = ut n m j then 1 else 0, fun _ => 0⟩

theorem ell_chain (n m : ℕ) (j : Fin (n + m)) (p : Fin (Kdim n m) → ℝ) :
    (chain n m).ell j p = p (ut n m j) := by
  simp only [EAChain.ell, chain]
  rw [Finset.sum_congr rfl (fun k _ => by rw [ite_mul, one_mul, zero_mul]), Finset.sum_ite_eq']
  simp

/-! ## The atoms -/

/-- The variable `X (Sum.inl k)`. -/
abbrev Xa (n m : ℕ) (k : Fin (Kdim n m)) : EAPoly (Kdim n m) (n + m) :=
  MvPolynomial.X (Sum.inl k)

/-- The "small" tag: `tᵢ² + qᵢ² = 1`, i.e. `|tᵢ| ≤ 1`. -/
def tagEq (n m : ℕ) (i : Fin (n + m)) : EAPoly (Kdim n m) (n + m) :=
  Xa n m (ut n m i) ^ 2 + Xa n m (uq n m i) ^ 2 - 1

/-- The `ψ`-relation in the small branch: `uᵢ²(1 + tᵢ²) = tᵢ²`. -/
def relA (n m : ℕ) (i : Fin n) : EAPoly (Kdim n m) (n + m) :=
  Xa n m (uu n m i) ^ 2 * (1 + Xa n m (ut n m (Fin.castAdd m i)) ^ 2) -
    Xa n m (ut n m (Fin.castAdd m i)) ^ 2

/-- The sign condition in the small branch, expressed with the tag `wᵢ`: `uᵢ·tᵢ = wᵢ²`. -/
def relB (n m : ℕ) (i : Fin n) : EAPoly (Kdim n m) (n + m) :=
  Xa n m (uu n m i) * Xa n m (ut n m (Fin.castAdd m i)) - Xa n m (uw n m i) ^ 2

/-- The `ψ`-relation in the large branch: `uᵢ²(1 + sᵢ²) = 1`, i.e. `uᵢ = psi (1/sᵢ)`. -/
def relC (n m : ℕ) (i : Fin n) : EAPoly (Kdim n m) (n + m) :=
  Xa n m (uu n m i) ^ 2 * (1 + Xa n m (us n m (Fin.castAdd m i)) ^ 2) - 1

/-- The strict inequality `|sᵢ| < 1` (large branch). -/
def posS (n m : ℕ) (i : Fin (n + m)) : EAPoly (Kdim n m) (n + m) :=
  1 - Xa n m (us n m i) ^ 2

/-- The sign condition `uᵢ·sᵢ > 0` in the large branch. -/
def posSign (n m : ℕ) (i : Fin n) : EAPoly (Kdim n m) (n + m) :=
  Xa n m (uu n m i) * Xa n m (us n m (Fin.castAdd m i))

/-- `sᵢ ≠ 0`, expressed as `sᵢ² > 0`: the reciprocal `1/sᵢ` (the value of the coordinate) must
be defined in the large branch. -/
def sNZ (n m : ℕ) (i : Fin (n + m)) : EAPoly (Kdim n m) (n + m) :=
  Xa n m (us n m i) ^ 2

/-! ## The basics, one per branch pattern -/

/-- A degree bound for `P`: the largest total degree of a monomial in its support. This is the
`D` of `branchPoly`: the identity `branchPoly_eval` needs `m (Sum.inl i) ≤ D` for every monomial
`m` of `P`. -/
def degb {n m : ℕ} (P : MvPolynomial (Fin (n + m) ⊕ Fin (n + m)) ℝ) : ℕ :=
  P.support.sup (fun t => t.sum fun _ e => e)

theorem le_degb {n m : ℕ} (P : MvPolynomial (Fin (n + m) ⊕ Fin (n + m)) ℝ)
    {mm : (Fin (n + m) ⊕ Fin (n + m)) →₀ ℕ} (hm : mm ∈ P.support) (i : Fin (n + m)) :
    mm (Sum.inl i) ≤ degb P := by
  by_cases h : mm (Sum.inl i) = 0
  · rw [h]; exact Nat.zero_le _
  · have hs : Sum.inl i ∈ mm.support := Finsupp.mem_support_iff.mpr h
    have h1 : mm (Sum.inl i) ≤ mm.sum (fun _ e => e) := by
      rw [Finsupp.sum]
      exact Finset.single_le_sum (fun j _ => Nat.zero_le _) hs
    exact le_trans h1 (Finset.le_sup (f := fun t => t.sum fun _ e => e) hm)

def eqsOf (n m : ℕ) (P : MvPolynomial (Fin (n + m) ⊕ Fin (n + m)) ℝ) (ε : Fin (n + m) → Bool) :
    List (EAPoly (Kdim n m) (n + m)) :=
  (branchPoly (degb P) ε (ut n m) (us n m) id P) ::
    (((List.finRange (n + m)).flatMap (fun i => if ε i then [tagEq n m i] else [])) ++
     ((List.finRange n).flatMap (fun i =>
        if ε (Fin.castAdd m i) then [relA n m i, relB n m i] else [relC n m i])))

def posOf (n m : ℕ) (ε : Fin (n + m) → Bool) : List (EAPoly (Kdim n m) (n + m)) :=
  ((List.finRange (n + m)).flatMap (fun i => if ε i then [] else [posS n m i, sNZ n m i])) ++
    ((List.finRange n).flatMap (fun i => if ε (Fin.castAdd m i) then [] else [posSign n m i]))

def basicOf (n m : ℕ) (P : MvPolynomial (Fin (n + m) ⊕ Fin (n + m)) ℝ)
    (ε : Fin (n + m) → Bool) : Basic (Kdim n m) (n + m) :=
  ⟨eqsOf n m P ε, posOf n m ε⟩

/-- The list of all branch patterns. -/
def patternList (n m : ℕ) : List (Fin (n + m) → Bool) :=
  (Finset.univ : Finset (Fin (n + m) → Bool)).toList

theorem mem_patternList (n m : ℕ) (ε : Fin (n + m) → Bool) : ε ∈ patternList n m :=
  Finset.mem_toList.mpr (Finset.mem_univ ε)

/-- The semi-Pfaffian set of the branch construction. -/
def W (n m : ℕ) (P : MvPolynomial (Fin (n + m) ⊕ Fin (n + m)) ℝ) : SemiPf (Kdim n m) :=
  ⟨n + m, chain n m, (patternList n m).map (basicOf n m P)⟩

theorem mem_W_basics (n m : ℕ) (P : MvPolynomial (Fin (n + m) ⊕ Fin (n + m)) ℝ)
    (ε : Fin (n + m) → Bool) : basicOf n m P ε ∈ (W n m P).basics :=
  List.mem_map_of_mem (mem_patternList n m ε)

/-! ## The point of the forward direction -/

/-- The auxiliary point attached to `(x, y)`: on each coordinate `i` of `z = Fin.append x y` we
take the value `zᵢ` (`t`) or its reciprocal (`s`), together with the tags. -/
def mkPoint (n m : ℕ) (x : Fin n → ℝ) (ε : Fin (n + m) → Bool) (z : Fin (n + m) → ℝ) :
    Idx n m → ℝ
  | Sum.inl i => psi (x i)
  | Sum.inr (Sum.inl i) => if ε i then z i else 0
  | Sum.inr (Sum.inr (Sum.inl i)) => if ε i then 0 else (z i)⁻¹
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl i))) => if ε i then Real.sqrt (1 - z i ^ 2) else 0
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr i))) =>
      if ε (Fin.castAdd m i) then Real.sqrt (psi (x i) * x i) else 0

/-- The same point, in the frozen `Fin (Kdim)` indexing. -/
def mkPt (n m : ℕ) (x : Fin n → ℝ) (ε : Fin (n + m) → Bool) (z : Fin (n + m) → ℝ) :
    Fin (Kdim n m) → ℝ :=
  fun k => mkPoint n m x ε z ((eA n m).symm k)

theorem mkPt_uu (n m : ℕ) (x : Fin n → ℝ) (ε : Fin (n + m) → Bool) (z : Fin (n + m) → ℝ)
    (i : Fin n) : mkPt n m x ε z (uu n m i) = psi (x i) := by
  simp only [mkPt, uu, uIdx, Equiv.symm_apply_apply, mkPoint]

theorem mkPt_ut (n m : ℕ) (x : Fin n → ℝ) (ε : Fin (n + m) → Bool) (z : Fin (n + m) → ℝ)
    (i : Fin (n + m)) :
    mkPt n m x ε z (ut n m i) = (if ε i then z i else 0) := by
  simp only [mkPt, ut, tIdx, Equiv.symm_apply_apply, mkPoint]

theorem mkPt_us (n m : ℕ) (x : Fin n → ℝ) (ε : Fin (n + m) → Bool) (z : Fin (n + m) → ℝ)
    (i : Fin (n + m)) :
    mkPt n m x ε z (us n m i) = (if ε i then 0 else (z i)⁻¹) := by
  simp only [mkPt, us, sIdx, Equiv.symm_apply_apply, mkPoint]

theorem mkPt_uq (n m : ℕ) (x : Fin n → ℝ) (ε : Fin (n + m) → Bool) (z : Fin (n + m) → ℝ)
    (i : Fin (n + m)) :
    mkPt n m x ε z (uq n m i) = (if ε i then Real.sqrt (1 - z i ^ 2) else 0) := by
  simp only [mkPt, uq, qIdx, Equiv.symm_apply_apply, mkPoint]

theorem mkPt_uw (n m : ℕ) (x : Fin n → ℝ) (ε : Fin (n + m) → Bool) (z : Fin (n + m) → ℝ)
    (i : Fin n) :
    mkPt n m x ε z (uw n m i) =
      (if ε (Fin.castAdd m i) then Real.sqrt (psi (x i) * x i) else 0) := by
  simp only [mkPt, uw, wIdx, Equiv.symm_apply_apply, mkPoint]

/-! ## Projection and `Fin.append` -/

theorem projFirst_append {n m : ℕ} (x : Fin n → ℝ) (v : Fin m → ℝ) :
    projFirst n m (Fin.append x v) = x := by
  funext i
  rw [projFirst, Fin.append_left]

theorem append_of_projFirst {n m : ℕ} (w : Fin (n + m) → ℝ) :
    Fin.append (projFirst n m w) (fun j => w (Fin.natAdd n j)) = w := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · rw [Fin.append_left, projFirst]
  · rw [Fin.append_right]

theorem mem_projFirst_iff {n m : ℕ} (X : Set (Fin (n + m) → ℝ)) (x : Fin n → ℝ) :
    x ∈ projFirst n m '' X ↔ ∃ v : Fin m → ℝ, Fin.append x v ∈ X := by
  constructor
  · rintro ⟨w, hw, hwx⟩
    refine ⟨fun j => w (Fin.natAdd n j), ?_⟩
    rw [← hwx, append_of_projFirst w]
    exact hw
  · rintro ⟨v, hv⟩
    exact ⟨Fin.append x v, hv, projFirst_append x v⟩

theorem append_mkPt (n m : ℕ) (x : Fin n → ℝ) (ε : Fin (n + m) → Bool)
    (z : Fin (n + m) → ℝ) :
    Fin.append (psiV x) (fun j => mkPt n m x ε z (Fin.natAdd n j)) = mkPt n m x ε z := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · rw [Fin.append_left]
    show psi (x i) = mkPt n m x ε z (Fin.castAdd (rd n m) i)
    rw [← uu_eq n m i]
    exact (mkPt_uu n m x ε z i).symm
  · rw [Fin.append_right]

end Work.WilE10
