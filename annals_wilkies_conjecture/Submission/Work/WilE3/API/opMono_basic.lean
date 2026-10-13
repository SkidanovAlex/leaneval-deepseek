import Mathlib
import Submission.Work.WilE3.Defs

namespace Work.WilE3.API

set_option autoImplicit false
open Classical Topology
open WilkiesDesign.E

noncomputable section

/-! ## Helper layer: `opMono` is `ℝ`-linear in its last argument.

`opMono c h ι m f` is the ordered iterate `∂_{h,ι,k-1}^{m (k-1)} ⋯ ∂_{h,ι,0}^{m 0} f` of the
first-order operators `detOp c h ι l`.  Each `detOp c h ι l` is a *linear* operator in `f`: it is
the determinant of a matrix whose rows are the `h`-derivatives together with one row
`b ↦ eaD c (lastCases l ι b) f` depending linearly on `f`, and the determinant is multilinear in
its rows.  Hence every iterate, and therefore the whole ordered fold, is additive and
`ℝ`-homogeneous in `f`. -/

/-- The matrix of `detOp c h ι l f : (∂_{ι 1} h_a, …, ∂_{ι j} h_a, ∂_l f)`: its last row is
`b ↦ eaD c (Fin.lastCases l ι b) f` and its other rows only involve `h`. -/
private def detM {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (l : Fin k) (f : EAPoly k r) : Matrix (Fin (j + 1)) (Fin (j + 1)) (EAPoly k r) :=
  Matrix.of fun (a b : Fin (j + 1)) => eaD c (Fin.lastCases l ι b) (Fin.lastCases f h a)

/-- `detOp` is the determinant of `detM`. -/
private lemma detOp_eq_detM {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r)
    (ι : Fin j → Fin k) (l : Fin k) (f : EAPoly k r) : detOp c h ι l f = (detM c h ι l f).det :=
  rfl

/-- `eaD c i` is additive. -/
private lemma eaD_add {k r : ℕ} (c : EAChain k r) (i : Fin k) (f f' : EAPoly k r) :
    eaD c i (f + f') = eaD c i f + eaD c i f' := by
  simp only [eaD, map_add, Finset.sum_add_distrib, mul_add]
  abel

/-- `eaD c i` is `ℝ`-homogeneous. -/
private lemma eaD_smul {k r : ℕ} (c : EAChain k r) (i : Fin k) (a : ℝ) (f : EAPoly k r) :
    eaD c i (a • f) = a • eaD c i f := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]
  simp only [eaD, MvPolynomial.pderiv_C_mul, mul_assoc]
  rw [mul_add, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun x _ => by ring)

/-- Replacing the last row of `detM c h ι l f` by the row of `g` recovers `detM c h ι l g`: only
the last row of `detM` depends on the polynomial argument. -/
private lemma detM_updateRow {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r)
    (ι : Fin j → Fin k) (l : Fin k) (f g : EAPoly k r) :
    detM c h ι l f = Matrix.updateRow (detM c h ι l g) (Fin.last j)
      (fun b => eaD c (Fin.lastCases l ι b) f) := by
  funext a b
  rw [Matrix.updateRow_apply]
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl
  · simp [detM, Fin.castSucc_ne_last]
  · simp [detM]

/-- `detOp c h ι l` is additive in its last argument. -/
private lemma detOp_add {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r)
    (ι : Fin j → Fin k) (l : Fin k) (f f' : EAPoly k r) :
    detOp c h ι l (f + f') = detOp c h ι l f + detOp c h ι l f' := by
  have hrow : (fun b : Fin (j + 1) => eaD c (Fin.lastCases l ι b) (f + f'))
      = (fun b => eaD c (Fin.lastCases l ι b) f) + (fun b => eaD c (Fin.lastCases l ι b) f') := by
    funext b
    change eaD c (Fin.lastCases l ι b) (f + f')
      = eaD c (Fin.lastCases l ι b) f + eaD c (Fin.lastCases l ι b) f'
    exact eaD_add (k := k) (r := r) c _ f f'
  rw [detOp_eq_detM, detOp_eq_detM, detOp_eq_detM]
  rw [detM_updateRow c h ι l (f + f') (f + f'), hrow, Matrix.det_updateRow_add,
    ← detM_updateRow c h ι l f (f + f'), ← detM_updateRow c h ι l f' (f + f')]

/-- `detOp c h ι l` is `ℝ`-homogeneous in its last argument. -/
private lemma detOp_smul {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r)
    (ι : Fin j → Fin k) (l : Fin k) (a : ℝ) (f : EAPoly k r) :
    detOp c h ι l (a • f) = a • detOp c h ι l f := by
  have hrow : (fun b : Fin (j + 1) => eaD c (Fin.lastCases l ι b) (a • f))
      = (MvPolynomial.C a : EAPoly k r) • (fun b => eaD c (Fin.lastCases l ι b) f) := by
    funext b
    change eaD c (Fin.lastCases l ι b) (a • f)
      = MvPolynomial.C a * eaD c (Fin.lastCases l ι b) f
    rw [eaD_smul (k := k) (r := r) c _ a f, MvPolynomial.smul_eq_C_mul]
  rw [detOp_eq_detM, detOp_eq_detM, detM_updateRow c h ι l (a • f) (a • f), hrow,
    Matrix.det_updateRow_smul, ← detM_updateRow c h ι l f (a • f), ← MvPolynomial.smul_eq_C_mul]

/-! ## Helper layer: additivity and homogeneity of an ordered iterate / fold.

These are purely combinatorial and hold over any additive monoid `α` with any family of
additive (resp. homogeneous) self-maps. -/

/-- Iterates of an additive map are additive. -/
private lemma iterate_add {α : Type*} [AddMonoid α] (g : α → α)
    (hg : ∀ a b : α, g (a + b) = g a + g b) (n : ℕ) :
    ∀ a b : α, (g^[n]) (a + b) = (g^[n]) a + (g^[n]) b := by
  induction n with
  | zero => intro a b; simp
  | succ n ih =>
      intro a b
      rw [Function.iterate_succ_apply', ih a b, Function.iterate_succ_apply' g n a,
        Function.iterate_succ_apply' g n b]
      exact hg _ _

/-- Iterates of a homogeneous map are homogeneous. -/
private lemma iterate_smul {α : Type*} {M : Type*} [Monoid M] [AddCommMonoid α]
    [DistribMulAction M α] (g : α → α) (hg : ∀ (a : M) (x : α), g (a • x) = a • g x) (n : ℕ) :
    ∀ (a : M) (x : α), (g^[n]) (a • x) = a • (g^[n]) x := by
  induction n with
  | zero => intro a x; simp
  | succ n ih =>
      intro a x
      rw [Function.iterate_succ_apply' g n (a • x), ih a x,
        Function.iterate_succ_apply' g n x]
      exact hg a _

/-- A right fold of identity maps is the identity. -/
private lemma foldr_id {ι α : Type*} (l : List ι) (x : α) :
    l.foldr (fun _ acc => acc) x = x := by
  induction l with
  | nil => rfl
  | cons i t ih => simpa only [List.foldr_cons] using ih

/-- A right fold of additive maps is additive. -/
private lemma foldr_add {ι α : Type*} [AddMonoid α] (l : List ι) (g : ι → α → α)
    (m : ι → ℕ) (hg : ∀ i, ∀ a b : α, g i (a + b) = g i a + g i b) (a b : α) :
    l.foldr (fun i acc => (g i)^[m i] acc) (a + b) =
      l.foldr (fun i acc => (g i)^[m i] acc) a + l.foldr (fun i acc => (g i)^[m i] acc) b := by
  induction l with
  | nil => simp
  | cons i t ih =>
      simp only [List.foldr_cons]
      rw [ih, iterate_add (g i) (hg i) (m i)]

/-- A right fold of homogeneous maps is homogeneous. -/
private lemma foldr_smul {ι α M : Type*} [Monoid M] [AddCommMonoid α] [DistribMulAction M α]
    (l : List ι) (g : ι → α → α) (m : ι → ℕ)
    (hg : ∀ i (a : M) (x : α), g i (a • x) = a • g i x) (a : M) (x : α) :
    l.foldr (fun i acc => (g i)^[m i] acc) (a • x) =
      a • l.foldr (fun i acc => (g i)^[m i] acc) x := by
  induction l with
  | nil => rfl
  | cons i t ih =>
      simp only [List.foldr_cons]
      rw [ih, iterate_smul (g i) (hg i) (m i)]

/-! ## The target. -/

theorem opMono_basic {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r)
    (ι : Fin j → Fin k) (m : Fin k → ℕ) :
    (∀ f : EAPoly k r, opMono c h ι (0 : Fin k → ℕ) f = f) ∧
    (∀ f f' : EAPoly k r, opMono c h ι m (f + f') = opMono c h ι m f + opMono c h ι m f') ∧
    (∀ (a : ℝ) (f : EAPoly k r), opMono c h ι m (a • f) = a • opMono c h ι m f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro f
    rw [opMono]
    simp only [Pi.zero_apply, Function.iterate_zero_apply]
    exact foldr_id _ f
  · intro f f'
    rw [opMono]
    exact foldr_add (List.finRange k) (fun l => detOp c h ι l) m
      (fun l => detOp_add c h ι l) f f'
  · intro a f
    rw [opMono]
    exact foldr_smul (List.finRange k) (fun l => detOp c h ι l) m
      (fun l => detOp_smul c h ι l) a f

end

end Work.WilE3.API
