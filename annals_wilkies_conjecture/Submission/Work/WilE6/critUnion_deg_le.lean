import Mathlib
import Submission.Work.WilE6.Setup
import Submission.Work.WilE6.critSA_deg_le
import Submission.Work.WilE6.eaTaylor_poly_shifted
import Submission.Work.WilE6.Main

/-!
### Degree bound for `critUnionOf`

`critUnionOf K X` is the `SA`-set obtained by taking, for every basic set `B` of `X` and every
attained sup-norm index `j : Fin (k+1)` (`k = p + q`), the criterion piece
`critSA hp κ (Pof X.c B κ) (Gsof X.c B κ)` at the uniform cut-off `κ = kappa K X.deg p`.

This file proves that the total degree of that `SA`-set is bounded by a polynomial in `X.deg`
(and in the fixed format bound `F`), i.e. there is a `Q : Polynomial ℕ` (depending only on `K`
and `F`) with

`(critUnionOf K X).deg ≤ Q.eval X.deg`

whenever `X.fmt ≤ F` and `X.basics.length ≤ X.deg`.

The books (writing `D = X.deg`, `k = p + q ≤ F`, `p ≤ k ≤ F`, `κ = kappa K D p`):

* each `critBasic` piece has `deg ≤ 3k + 8 + 2p(κ²+2) + 2(P.totalDegree + κ² + 2)
  + Σ_G G.totalDegree + |Gs|(κ+1)` (this is `critSA_deg_le`);
* `P.totalDegree ≤ 2 D + κ²` and `Σ_G G.totalDegree + |Gs|(κ+1) ≤ 2 D (κ+1)`;
* there are `X.basics.length ≤ D` basic sets, each contributing `k + 1 ≤ F + 1` pieces;
* `κ ≤ K.eval (3D + 2F + 1) + 1`, a polynomial in `D` because `p ≤ F`.

So `Q = C(F+1) * X * uPoly` where `uPoly` is the polynomial expression
`(3F+8) + 2F(κ(D)²+2) + 2(2D + 2κ(D)² + 2) + 2D(κ(D)+1)`, `κ(D) = K.eval (3D+2F+1) + 1`.
-/

set_option autoImplicit false
noncomputable section
open Classical Topology
namespace Work.WilE6
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

variable {k r p q : ℕ}

/-! ## §1. Generic list/degree helpers -/

/-- The sum of a flattened list is the sum of the sums. -/
theorem cud_sum_flatMap {α : Type*} (l : List α) (f : α → List ℕ) :
    (l.flatMap f).sum = (l.map (fun a => (f a).sum)).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, ih]

/-- The degree of the union of the `SA`-pieces indexed by a list is the sum of the degrees. -/
theorem cud_SA_deg_flatMap {m : ℕ} {α : Type*} (l : List α) (g : α → SA m) :
    (⟨l.flatMap (fun a => (g a).basics)⟩ : SA m).deg = (l.map (fun a => (g a).deg)).sum := by
  rw [SA.deg]
  show ((l.flatMap fun a => (g a).basics).map Basic.deg).sum = _
  rw [List.map_flatMap]
  induction l with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, ih, SA.deg]

/-! ## §2. Per-basic-set degree bounds -/

/-- The total degree of the Taylor polynomial of the merged equation. -/
theorem cud_Pof_totalDegree_le (c : EAChain k r) (B : Basic k r) (κ : ℕ) :
    (Pof c B κ).totalDegree ≤ 2 * B.deg + κ ^ 2 := by
  rw [Pof]
  exact (eaTaylorPoly_totalDegree_le c (mergeEq B) (κ ^ 2)).trans
    (Nat.add_le_add_right (totalDegree_mergeEq_le B) _)

/-- A basic set of `X` has degree at most the degree of `X`. -/
theorem cud_deg_le_semiPf_deg {k : ℕ} {X : SemiPf k} {B : Basic k X.r}
    (hB : B ∈ X.basics) : B.deg ≤ X.deg := by
  rw [SemiPf.deg]
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨B, hB, rfl⟩)

/-- The positivity atoms contribute at most `2 * B.deg * (κ+1)` to the degree of a piece. -/
theorem cud_Gsof_bound (c : EAChain k r) (B : Basic k r) (κ : ℕ) :
    ((Gsof c B κ).map (fun G => G.totalDegree)).sum + (Gsof c B κ).length * (κ + 1)
      ≤ 2 * B.deg * (κ + 1) := by
  have hlen : (Gsof c B κ).length = B.pos.length := by rw [Gsof]; exact List.length_map _
  have h1 : ((Gsof c B κ).map (fun G => G.totalDegree)).sum
      ≤ (B.pos.map (fun g => g.totalDegree)).sum + B.pos.length * κ := by
    rw [Gsof, List.map_map]
    calc (B.pos.map ((fun G => G.totalDegree) ∘ fun g => eaTaylorPoly c g κ)).sum
        ≤ (B.pos.map (fun g => g.totalDegree + κ)).sum :=
          List.sum_le_sum (fun g _ => eaTaylorPoly_totalDegree_le c g κ)
      _ = (B.pos.map (fun g => g.totalDegree)).sum + (B.pos.map (fun _ => κ)).sum :=
          List.sum_map_add
      _ = (B.pos.map (fun g => g.totalDegree)).sum + B.pos.length * κ := by
          rw [sum_map_const]
  refine le_trans (add_le_add h1 le_rfl) ?_
  rw [hlen]
  have hA : (B.pos.map (fun g => g.totalDegree)).sum ≤ (B.pos.map atomDeg).sum :=
    List.sum_le_sum (fun (g : EAPoly k r) _ => Nat.le_succ g.totalDegree)
  have hL : B.pos.length ≤ (B.pos.map atomDeg).sum := by
    have h := List.sum_le_sum (l := B.pos) (f := fun _ : EAPoly k r => 1) (g := atomDeg)
      (fun (g : EAPoly k r) _ => Nat.le_add_left 1 g.totalDegree)
    rw [sum_map_const, Nat.mul_one] at h
    exact h
  have hPd : (B.pos.map atomDeg).sum ≤ B.deg := by
    rw [Basic.deg, List.map_append, List.sum_append]
    exact Nat.le_add_left _ _
  calc (B.pos.map (fun g => g.totalDegree)).sum + B.pos.length * κ + B.pos.length * (κ + 1)
      ≤ (B.pos.map atomDeg).sum + (B.pos.map atomDeg).sum * κ
          + (B.pos.map atomDeg).sum * (κ + 1) := by
        refine add_le_add (add_le_add hA (Nat.mul_le_mul_right _ hL)) (Nat.mul_le_mul_right _ hL)
    _ = 2 * (B.pos.map atomDeg).sum * (κ + 1) := by ring
    _ ≤ 2 * B.deg * (κ + 1) := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hPd)

/-! ## §3. The degree bound for `critUnion`, with `κ` explicit -/

theorem cud_critUnion_deg_aux {k p : ℕ} (hp : p ≤ k) (κ : ℕ) (hκ : 1 ≤ κ) (X : SemiPf k) :
    (critUnion (p := p) hp κ X).deg ≤
      X.basics.length * (k + 1) *
        (3*k + 8 + 2*p*(κ^2 + 2) + 2*(2*X.deg + 2*κ^2 + 2) + 2*X.deg*(κ + 1)) := by
  set U : ℕ := 3*k + 8 + 2*p*(κ^2 + 2) + 2*(2*X.deg + 2*κ^2 + 2) + 2*X.deg*(κ + 1) with hU
  have hdeg : (critUnion (p := p) hp κ X).deg
      = (X.basics.map (fun B => (critSA (p := p) hp κ (Pof X.c B κ) (Gsof X.c B κ)).deg)).sum := by
    rw [show critUnion (p := p) hp κ X = (⟨X.basics.flatMap (fun B =>
        (critSA (p := p) hp κ (Pof X.c B κ) (Gsof X.c B κ)).basics)⟩ : SA _) from rfl]
    exact cud_SA_deg_flatMap _ _
  rw [hdeg]
  have hstep : ∀ B ∈ X.basics,
      (critSA (p := p) hp κ (Pof X.c B κ) (Gsof X.c B κ)).deg ≤ (k + 1) * U := by
    intro B hB
    have hcrit := critSA_deg_le (p := p) hp κ hκ (Pof X.c B κ) (Gsof X.c B κ)
    have hP := cud_Pof_totalDegree_le X.c B κ
    have hGs := cud_Gsof_bound X.c B κ
    have hBd := cud_deg_le_semiPf_deg (X := X) hB
    have hBd2 : 2 * B.deg ≤ 2 * X.deg := Nat.mul_le_mul_left 2 hBd
    have h2 : ((Gsof X.c B κ).map (fun G => G.totalDegree)).sum
        + (Gsof X.c B κ).length * (κ + 1) ≤ 2 * X.deg * (κ + 1) :=
      hGs.trans (Nat.mul_le_mul_right _ hBd2)
    refine hcrit.trans (Nat.mul_le_mul_left _ ?_)
    rw [hU]
    omega
  calc (X.basics.map (fun B => (critSA (p := p) hp κ (Pof X.c B κ) (Gsof X.c B κ)).deg)).sum
      ≤ (X.basics.map (fun _ => (k + 1) * U)).sum := List.sum_le_sum hstep
    _ = X.basics.length * ((k + 1) * U) := by rw [sum_map_const]
    _ = X.basics.length * (k + 1) * U := by ring
    _ = X.basics.length * (k + 1) *
        (3*k + 8 + 2*p*(κ^2 + 2) + 2*(2*X.deg + 2*κ^2 + 2) + 2*X.deg*(κ + 1)) := by rw [hU]

/-! ## §4. The polynomial `Q` -/

/-- `D ↦ K.eval (3D + 2F + 1) + 1`, as a polynomial in `D`. -/
def cud_kappaPoly (K : Polynomial ℕ) (F : ℕ) : Polynomial ℕ :=
  K.comp (Polynomial.C 3 * Polynomial.X + Polynomial.C (2 * F + 1)) + Polynomial.C 1

theorem cud_kappaPoly_eval (K : Polynomial ℕ) (F D : ℕ) :
    (cud_kappaPoly K F).eval D = K.eval (3 * D + 2 * F + 1) + 1 := by
  simp only [cud_kappaPoly, Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Nat.add_assoc]

/-- The uniform per-piece degree bound, as a polynomial in `D`,
with `κ(D) = K.eval (3D + 2F + 1) + 1`. -/
def cud_uPoly (K : Polynomial ℕ) (F : ℕ) : Polynomial ℕ :=
  Polynomial.C (3 * F + 8) + Polynomial.C (2 * F) * (cud_kappaPoly K F ^ 2 + Polynomial.C 2)
    + Polynomial.C 2 * (Polynomial.C 2 * Polynomial.X + Polynomial.C 2 * cud_kappaPoly K F ^ 2
      + Polynomial.C 2)
    + Polynomial.C 2 * Polynomial.X * (cud_kappaPoly K F + Polynomial.C 1)

/-- `(F+1) * D * (uniform per-piece bound)`, as a polynomial in `D`. -/
def cud_boundPoly (K : Polynomial ℕ) (F : ℕ) : Polynomial ℕ :=
  Polynomial.C (F + 1) * Polynomial.X * cud_uPoly K F

theorem cud_boundPoly_eval (K : Polynomial ℕ) (F D : ℕ) :
    (cud_boundPoly K F).eval D = (F + 1) * D *
      ((3 * F + 8) + 2 * F * ((K.eval (3 * D + 2 * F + 1) + 1) ^ 2 + 2)
        + 2 * (2 * D + 2 * (K.eval (3 * D + 2 * F + 1) + 1) ^ 2 + 2)
        + 2 * D * ((K.eval (3 * D + 2 * F + 1) + 1) + 1)) := by
  simp only [cud_boundPoly, cud_uPoly, cud_kappaPoly, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_comp, Nat.add_assoc]

/-! ## §5. The main lemma -/

theorem critUnion_deg_le (K : Polynomial ℕ) (F : ℕ) : ∃ Q : Polynomial ℕ, ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)), X.fmt ≤ F → X.basics.length ≤ X.deg → (Work.WilE6.critUnionOf K X).deg ≤ Q.eval X.deg := by
  refine ⟨cud_boundPoly K F, fun p q X hfmt hlen => ?_⟩
  have hkF : p + q ≤ F := by
    have h := hfmt; rw [SemiPf.fmt] at h; omega
  have hpF : p ≤ F := by omega
  have hk1F : p + q + 1 ≤ F + 1 := Nat.succ_le_succ hkF
  set κ : ℕ := kappa K X.deg p with hκD
  set κP : ℕ := (cud_kappaPoly K F).eval X.deg with hκP
  have hκ1 : 1 ≤ κ := by rw [hκD, kappa]; omega
  have hκκ : κ ≤ κP := by
    rw [hκD, hκP, kappa, cud_kappaPoly_eval]
    exact Nat.add_le_add_right (polynomial_eval_mono K (by omega)) 1
  have haux : (critUnionOf K X).deg ≤
      X.basics.length * (p + q + 1) *
        (3*(p+q) + 8 + 2*p*(κ^2 + 2) + 2*(2*X.deg + 2*κ^2 + 2) + 2*X.deg*(κ + 1)) := by
    rw [show critUnionOf K X = critUnion (p := p) (by omega : p ≤ p + q) κ X from rfl]
    exact cud_critUnion_deg_aux (by omega : p ≤ p + q) κ hκ1 X
  have hinner : 3*(p+q) + 8 + 2*p*(κ^2 + 2) + 2*(2*X.deg + 2*κ^2 + 2) + 2*X.deg*(κ + 1)
      ≤ (3*F + 8) + 2*F*(κP^2 + 2) + 2*(2*X.deg + 2*κP^2 + 2) + 2*X.deg*(κP + 1) := by
    have hA : 3*(p+q) + 8 ≤ 3*F + 8 := add_le_add (Nat.mul_le_mul_left 3 hkF) le_rfl
    have hB : 2*p*(κ^2+2) ≤ 2*F*(κP^2+2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hpF)
        (Nat.add_le_add_right (Nat.pow_le_pow_left hκκ 2) 2)
    have hC : 2*(2*X.deg + 2*κ^2 + 2) ≤ 2*(2*X.deg + 2*κP^2 + 2) :=
      Nat.mul_le_mul_left 2 (add_le_add (add_le_add le_rfl
        (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hκκ 2))) le_rfl)
    have hE : 2*X.deg*(κ+1) ≤ 2*X.deg*(κP+1) :=
      Nat.mul_le_mul_left (2*X.deg) (add_le_add hκκ le_rfl)
    exact add_le_add (add_le_add (add_le_add hA hB) hC) hE
  have hprod : X.basics.length * (p + q + 1) ≤ X.deg * (F + 1) := Nat.mul_le_mul hlen hk1F
  have hchain : X.basics.length * (p+q+1) *
        (3*(p+q) + 8 + 2*p*(κ^2 + 2) + 2*(2*X.deg + 2*κ^2 + 2) + 2*X.deg*(κ + 1))
      ≤ X.deg * (F + 1) *
        ((3*F + 8) + 2*F*(κP^2 + 2) + 2*(2*X.deg + 2*κP^2 + 2) + 2*X.deg*(κP + 1)) :=
    (Nat.mul_le_mul_left _ hinner).trans (Nat.mul_le_mul_right _ hprod)
  refine haux.trans (hchain.trans ?_)
  rw [hκP, cud_kappaPoly_eval, cud_boundPoly_eval]
  apply le_of_eq
  ring_nf

end Work.WilE6
