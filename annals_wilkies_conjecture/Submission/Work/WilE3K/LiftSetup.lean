/-
  annals_wilkies_conjecture, AREA E3K: setup for the arctan lift of a `SepChainLocal` system.

  Given a separable chain `S : SepChainLocal n r` all of whose chain functions are either
  `Real.exp` (`R = X`) or `Real.tan` (`R = 1 + X²`), we split the chain indices into the
  `tan`-type and the remaining (`exp`-type) ones, and build the lifted `ETData` on

      `Fin (rt + n)`  =  `Fin rt` (the lifted `tan` coordinates) `⊕ Fin n` (the original variables),

  with `rt` arctan graph equations `arctan t_p - (ℓ_{j_p}(x) - k_p π) = 0` and `re = r - rt`
  exp chains.  This file fixes the vocabulary; the evaluation/Jacobian identities are proved on
  top of it.
-/
import Submission.Work.WilE3K.ET
import Submission.Work.WilE3.Sep
import Submission.Work.WilE3.Defs
import Mathlib

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilE3K
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

variable {n r : ℕ}

namespace Lift

/-! ## §1. Splitting the chain indices into `tan`-type and `exp`-type -/

/-- The set of `tan`-type chain indices. -/
def tanSet (S : Work.WilE3.SepChainLocal n r) : Finset (Fin r) :=
  Finset.univ.filter (fun j => S.phi j = Real.tan)

/-- The complementary set of chain indices (the `exp`-type ones, under the chain-type
hypothesis). -/
def expSet (S : Work.WilE3.SepChainLocal n r) : Finset (Fin r) :=
  Finset.univ.filter (fun j => ¬ (S.phi j = Real.tan))

/-- The number of `tan`-type chains. -/
def rt (S : Work.WilE3.SepChainLocal n r) : ℕ := (tanSet S).card

/-- The number of `exp`-type chains. -/
def re (S : Work.WilE3.SepChainLocal n r) : ℕ := (expSet S).card

theorem mem_tanSet {S : Work.WilE3.SepChainLocal n r} {j : Fin r} :
    j ∈ tanSet S ↔ S.phi j = Real.tan := by simp [tanSet]

theorem mem_expSet {S : Work.WilE3.SepChainLocal n r} {j : Fin r} :
    j ∈ expSet S ↔ ¬ (S.phi j = Real.tan) := by simp [expSet]

theorem tanSet_disjoint (S : Work.WilE3.SepChainLocal n r) : Disjoint (tanSet S) (expSet S) := by
  rw [Finset.disjoint_left]
  intro j hj1 hj2
  rw [mem_tanSet] at hj1
  rw [mem_expSet] at hj2
  exact hj2 hj1

theorem tanSet_union (S : Work.WilE3.SepChainLocal n r) :
    tanSet S ∪ expSet S = Finset.univ := by
  ext j
  simp only [Finset.mem_union, mem_tanSet, mem_expSet, Finset.mem_univ, iff_true]
  exact Classical.em _

theorem rt_add_re (S : Work.WilE3.SepChainLocal n r) : rt S + re S = r := by
  have h := Finset.card_union_of_disjoint (tanSet_disjoint S)
  rw [tanSet_union, Finset.card_univ, Fintype.card_fin] at h
  rw [rt, re]; omega

/-- The order isomorphism enumerating the `tan`-type indices. -/
def tanI (S : Work.WilE3.SepChainLocal n r) : ↥(tanSet S) ≃ Fin (rt S) :=
  Finset.equivFin _

/-- The order isomorphism enumerating the `exp`-type indices. -/
def expI (S : Work.WilE3.SepChainLocal n r) : ↥(expSet S) ≃ Fin (re S) :=
  Finset.equivFin _

/-- The `p`-th `tan`-type chain index. -/
def tanIdx (S : Work.WilE3.SepChainLocal n r) (p : Fin (rt S)) : Fin r :=
  ((tanI S).symm p).1

/-- The `q`-th `exp`-type chain index. -/
def expIdx (S : Work.WilE3.SepChainLocal n r) (q : Fin (re S)) : Fin r :=
  ((expI S).symm q).1

theorem tanIdx_mem (S : Work.WilE3.SepChainLocal n r) (p : Fin (rt S)) :
    tanIdx S p ∈ tanSet S := ((tanI S).symm p).2

theorem expIdx_mem (S : Work.WilE3.SepChainLocal n r) (q : Fin (re S)) :
    expIdx S q ∈ expSet S := ((expI S).symm q).2

theorem phi_tanIdx (S : Work.WilE3.SepChainLocal n r) (p : Fin (rt S)) :
    S.phi (tanIdx S p) = Real.tan := mem_tanSet.mp (tanIdx_mem S p)

theorem not_phi_tan_expIdx (S : Work.WilE3.SepChainLocal n r) (q : Fin (re S)) :
    ¬ (S.phi (expIdx S q) = Real.tan) := mem_expSet.mp (expIdx_mem S q)

/-- The chain-type hypothesis of `SepKhovanskiiET`: every chain function is `exp` or `tan`. -/
def IsET (S : Work.WilE3.SepChainLocal n r) : Prop :=
  ∀ j, (S.phi j = Real.exp ∧ S.R j = MvPolynomial.X 0) ∨
    (S.phi j = Real.tan ∧ S.R j = 1 + MvPolynomial.X 0 ^ 2)

theorem exp_ne_tan : (Real.exp : ℝ → ℝ) ≠ Real.tan := by
  intro h
  have := congrFun h 0
  simp at this

theorem phi_expIdx (S : Work.WilE3.SepChainLocal n r) (htype : IsET S) (q : Fin (re S)) :
    S.phi (expIdx S q) = Real.exp := by
  rcases htype (expIdx S q) with ⟨he, _⟩ | ⟨ht, _⟩
  · exact he
  · exact absurd ht (not_phi_tan_expIdx S q)

theorem R_tanIdx (S : Work.WilE3.SepChainLocal n r) (htype : IsET S) (p : Fin (rt S)) :
    S.R (tanIdx S p) = 1 + MvPolynomial.X 0 ^ 2 := by
  rcases htype (tanIdx S p) with ⟨he, _⟩ | ⟨_, hR⟩
  · exact absurd (he.symm.trans (phi_tanIdx S p)) exp_ne_tan
  · exact hR

theorem R_expIdx (S : Work.WilE3.SepChainLocal n r) (htype : IsET S) (q : Fin (re S)) :
    S.R (expIdx S q) = MvPolynomial.X 0 := by
  rcases htype (expIdx S q) with ⟨_, hR⟩ | ⟨ht, _⟩
  · exact hR
  · exact absurd ht (not_phi_tan_expIdx S q)

theorem tanIdx_injective (S : Work.WilE3.SepChainLocal n r) : Function.Injective (tanIdx S) := by
  intro p p' h
  have h2 : (tanI S).symm p = (tanI S).symm p' := Subtype.ext h
  exact (tanI S).symm.injective h2

theorem expIdx_injective (S : Work.WilE3.SepChainLocal n r) : Function.Injective (expIdx S) := by
  intro p p' h
  have h2 : (expI S).symm p = (expI S).symm p' := Subtype.ext h
  exact (expI S).symm.injective h2

/-- The classification of a chain index as `tan`-type or `exp`-type. -/
def cls (S : Work.WilE3.SepChainLocal n r) (j : Fin r) : Fin (rt S) ⊕ Fin (re S) :=
  if h : S.phi j = Real.tan then Sum.inl ((tanI S) ⟨j, mem_tanSet.mpr h⟩)
  else Sum.inr ((expI S) ⟨j, mem_expSet.mpr h⟩)

theorem cls_tanIdx (S : Work.WilE3.SepChainLocal n r) (p : Fin (rt S)) :
    cls S (tanIdx S p) = Sum.inl p := by
  have h : S.phi (tanIdx S p) = Real.tan := phi_tanIdx S p
  unfold cls
  rw [dif_pos h]
  have : (⟨tanIdx S p, mem_tanSet.mpr h⟩ : ↥(tanSet S)) = (tanI S).symm p := Subtype.ext rfl
  rw [this, Equiv.apply_symm_apply]

theorem cls_expIdx (S : Work.WilE3.SepChainLocal n r) (q : Fin (re S)) :
    cls S (expIdx S q) = Sum.inr q := by
  have h : ¬ (S.phi (expIdx S q) = Real.tan) := not_phi_tan_expIdx S q
  unfold cls
  rw [dif_neg h]
  have : (⟨expIdx S q, mem_expSet.mpr h⟩ : ↥(expSet S)) = (expI S).symm q := Subtype.ext rfl
  rw [this, Equiv.apply_symm_apply]

theorem eq_tanIdx_of_cls_eq_inl (S : Work.WilE3.SepChainLocal n r) {j : Fin r}
    {p : Fin (rt S)} (h : cls S j = Sum.inl p) : j = tanIdx S p := by
  unfold cls at h
  split at h
  · rename_i hh
    rw [Sum.inl.injEq] at h
    have h2 : (⟨j, mem_tanSet.mpr hh⟩ : ↥(tanSet S)) = (tanI S).symm p := by
      rw [← h]
      exact (Equiv.symm_apply_apply (tanI S) _).symm
    have := congrArg Subtype.val h2
    simpa [tanIdx] using this
  · rename_i hh
    exact absurd h (by simp)

theorem eq_expIdx_of_cls_eq_inr (S : Work.WilE3.SepChainLocal n r) {j : Fin r}
    {q : Fin (re S)} (h : cls S j = Sum.inr q) : j = expIdx S q := by
  unfold cls at h
  split at h
  · rename_i hh
    exact absurd h (by simp)
  · rename_i hh
    rw [Sum.inr.injEq] at h
    have h2 : (⟨j, mem_expSet.mpr hh⟩ : ↥(expSet S)) = (expI S).symm q := by
      rw [← h]
      exact (Equiv.symm_apply_apply (expI S) _).symm
    have := congrArg Subtype.val h2
    simpa [expIdx] using this

/-! ## §2. The affine forms, the lift point and the lifted polynomials -/

/-- The affine form `ℓ_j x = ∑ i, a j i * x i + b j`. -/
def ell (S : Work.WilE3.SepChainLocal n r) (j : Fin r) (x : Fin n → ℝ) : ℝ :=
  ∑ i, S.a j i * x i + S.b j

theorem psi_eq_phi_ell (S : Work.WilE3.SepChainLocal n r) (j : Fin r) (x : Fin n → ℝ) :
    S.psi j x = S.phi j (ell S j x) := rfl

/-- The value of the lifted `p`-th `tan` coordinate: `t_p = tan (ℓ_{j_p} x)`. -/
def liftT (S : Work.WilE3.SepChainLocal n r) (x : Fin n → ℝ) (p : Fin (rt S)) : ℝ :=
  Real.tan (ell S (tanIdx S p) x)

/-- The lift point: the `p`-th `tan` coordinate is `t p` and the free coordinates are `x`. -/
def liftPt {N rt n re : ℕ} (E : ETData N rt n re) (t : Fin rt → ℝ) (x : Fin n → ℝ) :
    Fin (N + 1) → ℝ :=
  fun c => if h : (c : ℕ) < rt then t ⟨(c : ℕ), h⟩ else x (E.freeIndex c (not_lt.mp h))

theorem liftPt_tan {N rt n re : ℕ} (E : ETData N rt n re) (t : Fin rt → ℝ)
    (x : Fin n → ℝ) (p : Fin rt) : liftPt E t x (E.tanCoord p) = t p := by
  rw [liftPt, dif_pos (show ((E.tanCoord p : Fin (N + 1)) : ℕ) < rt from p.isLt)]
  simp

theorem liftPt_free {N rt n re : ℕ} (E : ETData N rt n re) (t : Fin rt → ℝ)
    (x : Fin n → ℝ) (a : Fin n) : liftPt E t x (E.freeCoord a) = x a := by
  rw [liftPt, dif_neg (show ¬ ((E.freeCoord a : Fin (N + 1)) : ℕ) < rt from
    not_lt.mpr (Nat.le_add_right rt a))]
  congr 1
  exact E.freeIndex_freeCoord a _

/-- The reindexing of the variables of `EAPoly n r` into `EAPoly (N+1) re`: the `Fin n` variables
become the free coordinates, the `tan`-type chain variables become the `tan` coordinates and the
`exp`-type chain variables become the chain variables. -/
def xi {N rt re n' r : ℕ} (hn : rt + n' = N + 1) (cls : Fin r → Fin rt ⊕ Fin re) :
    (Fin n' ⊕ Fin r) → (Fin (N + 1) ⊕ Fin re) :=
  Sum.elim (fun a => Sum.inl ⟨rt + a, by omega⟩)
    (fun j => Sum.elim (fun p : Fin rt => Sum.inl ⟨p, by omega⟩)
      (fun q : Fin re => Sum.inr q) (cls j))

theorem xi_inl {N rt re n' r : ℕ} (hn : rt + n' = N + 1)
    (cls : Fin r → Fin rt ⊕ Fin re) (a : Fin n') :
    xi hn cls (Sum.inl a) = Sum.inl ⟨rt + a, by omega⟩ := rfl

theorem xi_inr_inl {N rt re n' r : ℕ} (hn : rt + n' = N + 1)
    (cls : Fin r → Fin rt ⊕ Fin re) (j : Fin r) (p : Fin rt) (h : cls j = Sum.inl p) :
    xi hn cls (Sum.inr j) = Sum.inl ⟨p, by omega⟩ := by
  simp only [xi, Sum.elim_inr, h, Sum.elim_inl]

theorem xi_inr_inr {N rt re n' r : ℕ} (hn : rt + n' = N + 1)
    (cls : Fin r → Fin rt ⊕ Fin re) (j : Fin r) (q : Fin re) (h : cls j = Sum.inr q) :
    xi hn cls (Sum.inr j) = Sum.inr q := by
  simp only [xi, Sum.elim_inr, h, Sum.elim_inr]

theorem xi_inl_eq_freeCoord {N rt n re r : ℕ} (E : ETData N rt n re)
    (cls : Fin r → Fin rt ⊕ Fin re) (a : Fin n) :
    xi E.h cls (Sum.inl a) = Sum.inl (E.freeCoord a) := by
  rw [xi_inl]
  exact congrArg Sum.inl (Fin.ext rfl)

theorem xi_inr_inl_eq_tanCoord {N rt n re r : ℕ} (E : ETData N rt n re)
    (cls : Fin r → Fin rt ⊕ Fin re) (j : Fin r) (p : Fin rt) (h : cls j = Sum.inl p) :
    xi E.h cls (Sum.inr j) = Sum.inl (E.tanCoord p) := by
  rw [xi_inr_inl E.h cls j p h]
  exact congrArg Sum.inl (Fin.ext rfl)

/-- The lifted polynomial of the `i`-th equation. -/
def liftG {N rt re n' r : ℕ} (hn : rt + n' = N + 1) (cls : Fin r → Fin rt ⊕ Fin re)
    (f : Fin n' → EAPoly n' r) (i : Fin n') : EAPoly (N + 1) re :=
  MvPolynomial.rename (xi hn cls) (f i)

/-! ## §3. The lifted system -/

/-- The chain coefficients of the lifted system: the `exp`-type chains of `S`. -/
def liftCa (S : Work.WilE3.SepChainLocal n r) (q : Fin (re S)) : Fin n → ℝ :=
  fun i => S.a (expIdx S q) i

/-- The chain constants of the lifted system. -/
def liftCb (S : Work.WilE3.SepChainLocal n r) (q : Fin (re S)) : ℝ := S.b (expIdx S q)

/-- The linear parts of the arctan equations: the `tan`-type chains of `S`. -/
def liftLam (S : Work.WilE3.SepChainLocal n r) (p : Fin (rt S)) : Fin n → ℝ :=
  fun i => S.a (tanIdx S p) i

/-- The constants of the arctan equations, absorbing the branch shift `- k_p π`. -/
def liftMu (S : Work.WilE3.SepChainLocal n r) (k : Fin (rt S) → ℤ) (p : Fin (rt S)) : ℝ :=
  S.b (tanIdx S p) - (k p : ℝ) * Real.pi

/-- **The lifted system.** -/
def liftE (S : Work.WilE3.SepChainLocal n r) (hn : rt S + n = (rt S + n - 1) + 1)
    (cls : Fin r → Fin (rt S) ⊕ Fin (re S)) (f : Fin n → EAPoly n r) (k : Fin (rt S) → ℤ) :
    ETData (rt S + n - 1) (rt S) n (re S) :=
  { h := hn, ca := liftCa S, cb := liftCb S,
    G := fun i => liftG hn cls f i, lam := liftLam S, mu := liftMu S k }

@[simp] theorem liftE_h (S : Work.WilE3.SepChainLocal n r) (hn : rt S + n = (rt S + n - 1) + 1)
    (cls : Fin r → Fin (rt S) ⊕ Fin (re S)) (f : Fin n → EAPoly n r) (k : Fin (rt S) → ℤ) :
    (liftE S hn cls f k).h = hn := rfl

@[simp] theorem liftE_G (S : Work.WilE3.SepChainLocal n r) (hn : rt S + n = (rt S + n - 1) + 1)
    (cls : Fin r → Fin (rt S) ⊕ Fin (re S)) (f : Fin n → EAPoly n r) (k : Fin (rt S) → ℤ)
    (i : Fin n) : (liftE S hn cls f k).G i = liftG hn cls f i := rfl

@[simp] theorem liftE_lam (S : Work.WilE3.SepChainLocal n r) (hn : rt S + n = (rt S + n - 1) + 1)
    (cls : Fin r → Fin (rt S) ⊕ Fin (re S)) (f : Fin n → EAPoly n r) (k : Fin (rt S) → ℤ)
    (p : Fin (rt S)) : (liftE S hn cls f k).lam p = liftLam S p := rfl

@[simp] theorem liftE_mu (S : Work.WilE3.SepChainLocal n r) (hn : rt S + n = (rt S + n - 1) + 1)
    (cls : Fin r → Fin (rt S) ⊕ Fin (re S)) (f : Fin n → EAPoly n r) (k : Fin (rt S) → ℤ)
    (p : Fin (rt S)) : (liftE S hn cls f k).mu p = liftMu S k p := rfl

@[simp] theorem liftE_ca (S : Work.WilE3.SepChainLocal n r) (hn : rt S + n = (rt S + n - 1) + 1)
    (cls : Fin r → Fin (rt S) ⊕ Fin (re S)) (f : Fin n → EAPoly n r) (k : Fin (rt S) → ℤ)
    (q : Fin (re S)) : (liftE S hn cls f k).ca q = liftCa S q := rfl

@[simp] theorem liftE_cb (S : Work.WilE3.SepChainLocal n r) (hn : rt S + n = (rt S + n - 1) + 1)
    (cls : Fin r → Fin (rt S) ⊕ Fin (re S)) (f : Fin n → EAPoly n r) (k : Fin (rt S) → ℤ)
    (q : Fin (re S)) : (liftE S hn cls f k).cb q = liftCb S q := rfl

/-- The lifted system attached to `S`, `f` and the branch constants `k` (with the canonical
classification `cls S`). -/
def liftET (S : Work.WilE3.SepChainLocal n r) (hn : rt S + n = (rt S + n - 1) + 1)
    (f : Fin n → EAPoly n r) (k : Fin (rt S) → ℤ) :
    ETData (rt S + n - 1) (rt S) n (re S) :=
  liftE S hn (cls S) f k

@[simp] theorem liftET_G (S : Work.WilE3.SepChainLocal n r)
    (hn : rt S + n = (rt S + n - 1) + 1) (f : Fin n → EAPoly n r) (k : Fin (rt S) → ℤ)
    (i : Fin n) : (liftET S hn f k).G i = liftG hn (cls S) f i := rfl

/-- The lift of a point `x`: the `tan` coordinates are `tan (ℓ_{j_p} x)` and the free coordinates
are `x`. -/
def liftPoint (S : Work.WilE3.SepChainLocal n r)
    (E : ETData (rt S + n - 1) (rt S) n (re S)) (x : Fin n → ℝ) :
    Fin ((rt S + n - 1) + 1) → ℝ :=
  liftPt E (fun p => liftT S x p) x

theorem liftPoint_tan (S : Work.WilE3.SepChainLocal n r)
    (E : ETData (rt S + n - 1) (rt S) n (re S)) (x : Fin n → ℝ) (p : Fin (rt S)) :
    liftPoint S E x (E.tanCoord p) = liftT S x p := liftPt_tan E _ x p

theorem liftPoint_free (S : Work.WilE3.SepChainLocal n r)
    (E : ETData (rt S + n - 1) (rt S) n (re S)) (x : Fin n → ℝ) (a : Fin n) :
    liftPoint S E x (E.freeCoord a) = x a := liftPt_free E _ x a

end Lift

end Work.WilE3K
