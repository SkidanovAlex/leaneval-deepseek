/-
  WilE5 — area E5 (fibrewise weak stratification for restricted semi-Pfaffian sets).
  Companion of `Submission.Work.Wilkies.E.Spec` (frozen statements). This file: the
  foundational API (SemiPf/Stratum calculi, EAChain algebra, degree bookkeeping and the
  fibre ("y") coordinate conventions used by the stratification construction).

  Conventions (used in every file of this area):
  * `p` = number of base coordinates, `q` = number of fibre ("vertical") coordinates; the
    ambient index type is `Fin (p+q)`; the fibre coordinates are `Fin.natAdd p l`, `l : Fin q`.
  * `yDir p l` is that index, `InY` tests membership in the fibre range.
  * `detOp`, `opMono` are the frozen operators of `Spec` (GV's `∂_{h,ι,l}`); the fibrewise
    stratification uses them with `ι` and `l` taken in the fibre coordinates (see `Operators`).
-/
import Submission.Work.Wilkies.E.Spec
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit false
noncomputable section
open Classical Filter
open scoped Topology
namespace Work.WilE5
open WilkiesDesign WilkiesDesign.E

variable {p q r k n : ℕ}

/-! ## §1. Basic conditions -/

/-- Conjunction of two basic conditions over the same chain. -/
def conj {k r : ℕ} (B B' : Basic k r) : Basic k r :=
  ⟨B.eqs ++ B'.eqs, B.pos ++ B'.pos⟩

theorem conj_holds {k r : ℕ} (c : EAChain k r) (B B' : Basic k r) (x : Fin k → ℝ) :
    (conj B B').holds c x ↔ B.holds c x ∧ B'.holds c x := by
  simp only [Basic.holds, conj, List.mem_append]
  constructor
  · intro h
    exact ⟨⟨fun f hf => h.1 f (Or.inl hf), fun g hg => h.2 g (Or.inl hg)⟩,
      fun f hf => h.1 f (Or.inr hf), fun g hg => h.2 g (Or.inr hg)⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨fun f hf => hf.elim (h1 f) (h3 f), fun g hg => hg.elim (h2 g) (h4 g)⟩

theorem conj_deg {k r : ℕ} (B B' : Basic k r) :
    (conj B B').deg = B.deg + B'.deg := by
  simp only [Basic.deg, conj, List.map_append, List.sum_append]
  omega

/-- The basic condition "all the polynomials of `L` vanish". -/
def Basic.eqsOf {k r : ℕ} (L : List (EAPoly k r)) : Basic k r := ⟨L, []⟩

/-- The basic condition "all the polynomials of `L` are strictly positive". -/
def Basic.posOf {k r : ℕ} (L : List (EAPoly k r)) : Basic k r := ⟨[], L⟩

@[simp]
theorem Basic.holds_eqsOf {k r : ℕ} (c : EAChain k r) (L : List (EAPoly k r)) (x : Fin k → ℝ) :
    (Basic.eqsOf L).holds c x ↔ ∀ f ∈ L, eaEval c f x = 0 := by
  simp [Basic.holds, Basic.eqsOf]

@[simp]
theorem Basic.holds_posOf {k r : ℕ} (c : EAChain k r) (L : List (EAPoly k r)) (x : Fin k → ℝ) :
    (Basic.posOf L).holds c x ↔ ∀ f ∈ L, 0 < eaEval c f x := by
  simp [Basic.holds, Basic.posOf]

@[simp]
theorem Basic.deg_eqsOf {k r : ℕ} (L : List (EAPoly k r)) :
    (Basic.eqsOf L).deg = (L.map atomDeg).sum := by simp [Basic.deg, Basic.eqsOf]

@[simp]
theorem Basic.deg_posOf {k r : ℕ} (L : List (EAPoly k r)) :
    (Basic.posOf L).deg = (L.map atomDeg).sum := by simp [Basic.deg, Basic.posOf]

theorem Basic.deg_le_of_mem_eqs {k r : ℕ} (B : Basic k r) {f : EAPoly k r} (hf : f ∈ B.eqs) :
    atomDeg f ≤ B.deg := by
  have h1 : atomDeg f ≤ (B.eqs.map atomDeg).sum :=
    List.le_sum_of_mem (List.mem_map_of_mem hf)
  have h2 : (B.eqs.map atomDeg).sum ≤ ((B.eqs ++ B.pos).map atomDeg).sum := by
    rw [List.map_append, List.sum_append]; exact Nat.le_add_right _ _
  simpa [Basic.deg] using h1.trans h2

/-! ## §2. SemiPf calculus over a fixed chain -/

/-- The semi-Pfaffian set over the chain `c` with the given list of basic conditions. -/
def mkSemiPf {n r : ℕ} (c : EAChain n r) (L : List (Basic n r)) : SemiPf n := ⟨r, c, L⟩

@[simp]
theorem mkSemiPf_set {n r : ℕ} (c : EAChain n r) (L : List (Basic n r)) :
    (mkSemiPf c L).set = {x | x ∈ cubeC n ∧ ∃ B ∈ L, B.holds c x} := rfl

@[simp]
theorem mkSemiPf_deg {n r : ℕ} (c : EAChain n r) (L : List (Basic n r)) :
    (mkSemiPf c L).deg = (L.map Basic.deg).sum := rfl

@[simp]
theorem mkSemiPf_fmt {n r : ℕ} (c : EAChain n r) (L : List (Basic n r)) :
    (mkSemiPf c L).fmt = n + r := rfl

theorem mkSemiPf_set_eq_iUnion {n r : ℕ} (c : EAChain n r) (L : List (Basic n r)) :
    (mkSemiPf c L).set = cubeC n ∩ ⋃ B ∈ L, {x | B.holds c x} := by
  ext x
  simp [Set.mem_iUnion, Set.mem_inter_iff]

theorem mkSemiPf_set_mono {n r : ℕ} {c : EAChain n r} {L L' : List (Basic n r)}
    (h : ∀ B ∈ L, B ∈ L') : (mkSemiPf c L).set ⊆ (mkSemiPf c L').set := by
  rintro x ⟨hc, B, hB, hh⟩
  exact ⟨hc, B, h B hB, hh⟩

theorem mkSemiPf_deg_le {n r : ℕ} (c : EAChain n r) {L : List (Basic n r)} {D : ℕ}
    (h : ∀ B ∈ L, B.deg ≤ D) : (mkSemiPf c L).deg ≤ L.length * D := by
  rw [mkSemiPf_deg]
  have : (L.map Basic.deg).sum ≤ (L.map Basic.deg).length • D := by
    refine List.sum_le_length_nsmul _ _ ?_
    intro x hx
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hx
    exact h B hB
  simpa [List.length_map, nsmul_eq_mul] using this

theorem semiPf_set_subset_cube {n : ℕ} (X : SemiPf n) : X.set ⊆ cubeC n := fun _ hx => hx.1

@[simp]
theorem semiPf_mem_set {n : ℕ} (X : SemiPf n) (x : Fin n → ℝ) :
    x ∈ X.set ↔ x ∈ cubeC n ∧ ∃ B ∈ X.basics, B.holds X.c x := Iff.rfl

theorem semiPf_fmt_le_iff {n : ℕ} (X : SemiPf n) (F : ℕ) : X.fmt ≤ F ↔ n + X.r ≤ F := Iff.rfl

/-- Add one basic condition to every disjunct of `X`. -/
def semiPfAnd {n : ℕ} (X : SemiPf n) (B : Basic n X.r) : SemiPf n :=
  ⟨X.r, X.c, X.basics.map (fun A => conj A B)⟩

/-- Conjunction with a fixed condition, at the level of lists of disjuncts. -/
theorem exists_conj_iff {n r : ℕ} (c : EAChain n r) (L : List (Basic n r)) (B : Basic n r)
    (x : Fin n → ℝ) :
    (∃ A ∈ L.map (fun A => conj A B), A.holds c x) ↔
      (∃ A ∈ L, A.holds c x) ∧ B.holds c x := by
  constructor
  · rintro ⟨A, hA, hh⟩
    obtain ⟨A', hA', rfl⟩ := List.mem_map.mp hA
    exact ⟨⟨A', hA', ((conj_holds c A' B x).mp hh).1⟩, ((conj_holds c A' B x).mp hh).2⟩
  · rintro ⟨⟨A, hA, h1⟩, h2⟩
    exact ⟨conj A B, List.mem_map_of_mem (f := fun A => conj A B) hA,
      (conj_holds c A B x).mpr ⟨h1, h2⟩⟩


theorem semiPfAnd_r {n : ℕ} (X : SemiPf n) (B : Basic n X.r) : (semiPfAnd X B).r = X.r := rfl

theorem semiPfAnd_c {n : ℕ} (X : SemiPf n) (B : Basic n X.r) : (semiPfAnd X B).c = X.c := rfl

theorem semiPfAnd_set {n : ℕ} (X : SemiPf n) (B : Basic n X.r) :
    (semiPfAnd X B).set = X.set ∩ {x | B.holds X.c x} := by
  ext x
  simp only [semiPf_mem_set, semiPfAnd, Set.mem_inter_iff, Set.mem_setOf_eq, and_assoc]
  exact and_congr_right fun _ => exists_conj_iff X.c X.basics B x

theorem semiPfAnd_set_subset {n : ℕ} (X : SemiPf n) (B : Basic n X.r) :
    (semiPfAnd X B).set ⊆ X.set := by
  rw [semiPfAnd_set]; exact Set.inter_subset_left

theorem semiPfAnd_deg {n : ℕ} (X : SemiPf n) (B : Basic n X.r) :
    (semiPfAnd X B).deg = X.deg + X.basics.length * B.deg := by
  unfold SemiPf.deg semiPfAnd
  induction X.basics with
  | nil => simp
  | cons A L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, conj_deg]
    rw [ih]; ring

theorem semiPfAnd_fmt {n : ℕ} (X : SemiPf n) (B : Basic n X.r) : (semiPfAnd X B).fmt = X.fmt := rfl

/-! ## §2b. `eaEval` as a ring homomorphism -/

/-- `eaEval c · x` as a ring homomorphism (it is `MvPolynomial.eval` at the point
`Sum.elim x (fun j => exp (ℓ_j x))`). -/
def eaEvalHom {k r : ℕ} (c : EAChain k r) (x : Fin k → ℝ) : EAPoly k r →+* ℝ :=
  MvPolynomial.eval (Sum.elim x fun j => Real.exp (c.ell j x))

theorem eaEval_eq_hom {k r : ℕ} (c : EAChain k r) (x : Fin k → ℝ) (Q : EAPoly k r) :
    eaEval c Q x = eaEvalHom c x Q := rfl

theorem eaEval_add {k r : ℕ} (c : EAChain k r) (Q Q' : EAPoly k r) (x : Fin k → ℝ) :
    eaEval c (Q + Q') x = eaEval c Q x + eaEval c Q' x := by simp [eaEval]

theorem eaEval_mul {k r : ℕ} (c : EAChain k r) (Q Q' : EAPoly k r) (x : Fin k → ℝ) :
    eaEval c (Q * Q') x = eaEval c Q x * eaEval c Q' x := by simp [eaEval]

theorem eaEval_neg {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) (x : Fin k → ℝ) :
    eaEval c (-Q) x = -eaEval c Q x := by simp [eaEval]

theorem eaEval_one {k r : ℕ} (c : EAChain k r) (x : Fin k → ℝ) : eaEval c 1 x = 1 := by
  simp [eaEval]

theorem eaEval_C {k r : ℕ} (c : EAChain k r) (a : ℝ) (x : Fin k → ℝ) :
    eaEval c (MvPolynomial.C a) x = a := by simp [eaEval]

theorem eaEval_X_inl {k r : ℕ} (c : EAChain k r) (i : Fin k) (x : Fin k → ℝ) :
    eaEval c (MvPolynomial.X (Sum.inl i)) x = x i := by simp [eaEval, MvPolynomial.eval_X]

theorem eaEval_X_inr {k r : ℕ} (c : EAChain k r) (j : Fin r) (x : Fin k → ℝ) :
    eaEval c (MvPolynomial.X (Sum.inr j)) x = Real.exp (c.ell j x) := by
  simp [eaEval, MvPolynomial.eval_X]

/-- `eaEval` commutes with determinants: the algebraic content of `detOp`. -/
theorem eaEval_matrix_det {m : Type*} [Fintype m] [DecidableEq m]
    {k r : ℕ} (c : EAChain k r) (M : Matrix m m (EAPoly k r)) (x : Fin k → ℝ) :
    eaEval c M.det x = (M.map fun Q => eaEval c Q x).det := by
  rw [show eaEval c M.det x = eaEvalHom c x M.det from rfl, RingHom.map_det]
  rfl

theorem eaEval_detOp {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r)
    (ι : Fin j → Fin k) (l : Fin k) (f : EAPoly k r) (x : Fin k → ℝ) :
    eaEval c (detOp c h ι l f) x =
      (Matrix.of fun (a b : Fin (j + 1)) =>
        eaEval c (eaD c (Fin.lastCases l ι b) (Fin.lastCases f h a)) x).det := by
  unfold detOp
  rw [eaEval_matrix_det]
  rfl

/-! ## §3. The fibre ("y") coordinates -/

/-- The ambient index of the `l`-th fibre coordinate. -/
def yDir (p : ℕ) (l : Fin q) : Fin (p + q) := Fin.natAdd p l

theorem yDir_injective (p : ℕ) : Function.Injective (yDir p : Fin q → Fin (p + q)) :=
  fun _ _ h => Fin.natAdd_injective q p h

/-- `i` is a fibre coordinate. -/
def InY {p q : ℕ} (i : Fin (p + q)) : Prop := ∃ l : Fin q, i = yDir p l

theorem inY_yDir {p q : ℕ} (l : Fin q) : InY (p := p) (yDir p l) := ⟨l, rfl⟩

/-! ## §4. Degree bookkeeping for `eaD` -/

theorem totalDegree_pderiv_le {k r : ℕ} (i : Fin k ⊕ Fin r) (Q : EAPoly k r) :
    (MvPolynomial.pderiv i Q).totalDegree ≤ Q.totalDegree := by
  classical
  conv_lhs => rw [MvPolynomial.totalDegree_eq]
  refine Finset.sup_le fun m hm => ?_
  rw [Finsupp.card_toMultiset]
  have hm' : Q.coeff (m + Finsupp.single i 1) * ((m i : ℕ) + 1) ≠ 0 := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_pderiv] at hm
    exact hm
  have hcoeff : Q.coeff (m + Finsupp.single i 1) ≠ 0 := fun h => hm' (by rw [h, zero_mul])
  have hmem : m + Finsupp.single i 1 ∈ Q.support := by
    simpa [MvPolynomial.mem_support_iff] using hcoeff
  have h1 : m.sum (fun _ e => e) ≤ MvPolynomial.totalDegree Q := by
    have hle := MvPolynomial.le_totalDegree hmem
    have h2 : (m + Finsupp.single i 1).sum (fun _ e => e) = m.sum (fun _ e => e) + 1 := by
      rw [Finsupp.sum_add_index (by intro a; simp) (by intro a b c; simp),
        Finsupp.sum_single_index]
      simp
    rw [h2] at hle
    omega
  exact h1

theorem totalDegree_eaD_le {k r : ℕ} (c : EAChain k r) (i : Fin k) (Q : EAPoly k r) :
    (eaD c i Q).totalDegree ≤ Q.totalDegree + 1 := by
  have h1 : (MvPolynomial.pderiv (Sum.inl i) Q).totalDegree ≤ Q.totalDegree :=
    totalDegree_pderiv_le _ _
  have hsum : (∑ j : Fin r, MvPolynomial.C (c.a j i) * MvPolynomial.X (Sum.inr j) *
      MvPolynomial.pderiv (Sum.inr j) Q).totalDegree ≤ Q.totalDegree + 1 := by
    refine MvPolynomial.totalDegree_finsetSum_le (s := Finset.univ)
      (f := fun j : Fin r => (MvPolynomial.C (c.a j i) * MvPolynomial.X (Sum.inr j) : EAPoly k r) *
        MvPolynomial.pderiv (Sum.inr j) Q) ?_
    intro j _
    have h2 := totalDegree_pderiv_le (Sum.inr j) Q
    have h3 : ((MvPolynomial.C (c.a j i) * MvPolynomial.X (Sum.inr j) : EAPoly k r)).totalDegree ≤ 1 := by
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
    have h4 := MvPolynomial.totalDegree_mul
      ((MvPolynomial.C (c.a j i) * MvPolynomial.X (Sum.inr j) : EAPoly k r))
      (MvPolynomial.pderiv (Sum.inr j) Q)
    omega
  have h5 := MvPolynomial.totalDegree_add (MvPolynomial.pderiv (Sum.inl i) Q)
    (∑ j : Fin r, (MvPolynomial.C (c.a j i) * MvPolynomial.X (Sum.inr j) : EAPoly k r) *
      MvPolynomial.pderiv (Sum.inr j) Q)
  simp only [eaD]
  omega

theorem atomDeg_eaD_le {k r : ℕ} (c : EAChain k r) (i : Fin k) (Q : EAPoly k r) :
    atomDeg (eaD c i Q) ≤ atomDeg Q + 1 := by
  have := totalDegree_eaD_le c i Q
  simp only [atomDeg]; omega

theorem atomDeg_pos {k r : ℕ} (Q : EAPoly k r) : 0 < atomDeg Q := Nat.succ_pos _

/-! ## §5. `Stratum` API -/

/-- The trivial stratum: one `SemiPf` piece with no equations. -/
def trivStratum {p q : ℕ} (X : SemiPf (p + q)) : Stratum p q := ⟨X, 0, fun i => i.elim0⟩

@[simp]
theorem trivStratum_X {p q : ℕ} (X : SemiPf (p + q)) : (trivStratum X).X = X := rfl

theorem Stratum.good_eqs {p q : ℕ} {S : Stratum p q} (h : S.Good) {z : Fin (p + q) → ℝ}
    (hz : z ∈ S.X.set) (a : Fin S.j) : eaEval S.X.c (S.h a) z = 0 :=
  (h z hz).1 a

theorem Stratum.good_rank {p q : ℕ} {S : Stratum p q} (h : S.Good) {z : Fin (p + q) → ℝ}
    (hz : z ∈ S.X.set) :
    (Matrix.of fun (a : Fin S.j) (l : Fin q) =>
      eaEval S.X.c (eaD S.X.c (yDir p l) (S.h a)) z).rank = S.j :=
  (h z hz).2.1

theorem Stratum.good_local {p q : ℕ} {S : Stratum p q} (h : S.Good) {z : Fin (p + q) → ℝ}
    (hz : z ∈ S.X.set) :
    ∀ᶠ z' in 𝓝 z, projFirst p q z' = projFirst p q z →
      (∀ a, eaEval S.X.c (S.h a) z' = 0) → z' ∈ S.X.set :=
  (h z hz).2.2

theorem Stratum.deg_eq {p q : ℕ} (S : Stratum p q) :
    S.deg = S.X.deg + ∑ a, atomDeg (S.h a) := rfl

end Work.WilE5

end
