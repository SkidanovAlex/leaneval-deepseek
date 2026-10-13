/-
  The *uniform* (single-polynomial) degree bound for the boundary-compatible Lagrange stratum
  `Work.WilE9G.Assembly.lagStratumAE`.

  For a fixed format bound `F` there is one polynomial `b` such that for **every** ambient
  stratum `S` of format `≤ F` (and every weight `Φ` and direction `c`) the degree of the
  boundary-compatible Lagrange stratum is bounded by `b` evaluated at
  `S.deg + atomDeg Φ + #(S.X.basics)`.  The point is that the number of disjuncts of the
  Lagrange stratum equals the number of basics of `S`, so the count `#basics` -- rather than
  a fixed constant `K` -- may enter the *argument* of `b`, where it is absorbed by the
  quadratic growth of `b`.

  The mathematical content is the degree bookkeeping of the construction: every equation of
  `lagStratumAE` is either one of the `1 + (m + S.j + 1)` Lagrange equations `lagEqs` (degree
  `≤ S.deg + atomDeg Φ + 2`), the square of the Jacobian determinant (degree `≤
  (1 + (m + S.j + 1)) (S.deg + atomDeg Φ + 2)`), or a padded atom of a basic of `S` (padding
  never raises the atom degree).  Since `S.j ≤ n + (1+m) ≤ F` and `1 + m ≤ F`, the size of the
  multiplier block is `≤ 2F + 1`, and every quantity involved is linear in
  `x = S.deg + atomDeg Φ + #basics`; the product `#basics · (linear in x)` is quadratic, so
  one polynomial `b` of degree `2` can carry all the constants.

  The two degree bounds for `lagEqs` and `lagDet` are proved in the sibling modules
  `Assembly.lagEqs_totalDegree_le` and `Assembly.lagDet_totalDegree_le`.
-/
import Mathlib
import Submission.Work.WilE9G.Assembly.Defs
import Submission.Work.WilE9G.Lagrange.lagStratum_deg
import Submission.Work.WilE9G.Assembly.lagEqs_totalDegree_le
import Submission.Work.WilE9G.Assembly.lagDet_totalDegree_le

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE9G.Assembly
open WilkiesDesign WilkiesDesign.E Work.WilE9G Work.WilE9G.Lagrange

/-! ## Elementary list/atom bookkeeping -/

/-- `List.sum` of a constant function on `Fin k` is at most `k * B`. -/
private lemma ofFn_sum_le {k : ℕ} (g : Fin k → ℕ) (B : ℕ) (h : ∀ i, g i ≤ B) :
    (List.ofFn g).sum ≤ k * B := by
  rw [List.sum_ofFn]
  have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin k)) g B (fun i _ => h i)
  rwa [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this

/-- The sum of the atom degrees of a family of polynomials with `totalDegree ≤ B` is at most
`k * (B + 1)`. -/
private lemma ofFn_atomDeg_sum_le {k N r : ℕ} (f : Fin k → EAPoly N r) (B : ℕ)
    (h : ∀ i, (f i).totalDegree ≤ B) : ((List.ofFn f).map atomDeg).sum ≤ k * (B + 1) := by
  rw [List.map_ofFn]
  exact ofFn_sum_le _ _ (fun i => Nat.add_le_add_right (h i) 1)

/-- `List.ofFn` followed by `atomDeg` and `List.sum` is the corresponding `Finset.sum`. -/
private lemma listSum_ofFn_map {k N r : ℕ} (f : Fin k → EAPoly N r) :
    ((List.ofFn f).map atomDeg).sum = ∑ i : Fin k, atomDeg (f i) := by
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

/-! ## The uniform numerical bound -/

/-- For every format bound `F` there is a polynomial `b` dominating the quadratic expression
`x * ((2F+1)(x+3) + 2(2F+1)(x+2) + 1) + x + (2F+1)(x+3)` for all `x`. -/
private theorem poly_bound (F : ℕ) : ∃ b : Polynomial ℕ, ∀ x : ℕ,
    x * ((2*F+1)*(x+3) + (2*((2*F+1)*(x+2)) + 1)) + x + (2*F+1)*(x+3) ≤ b.eval x := by
  refine ⟨(Polynomial.C (8*(2*F+1)+2) * (Polynomial.X*Polynomial.X + Polynomial.X + 1)
    : Polynomial ℕ), ?_⟩
  intro x
  have hbx : ((Polynomial.C (8*(2*F+1)+2)
        * (Polynomial.X*Polynomial.X + Polynomial.X + 1) : Polynomial ℕ)).eval x
      = (8*(2*F+1)+2)*(x*x+x+1) := by
    simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  rw [hbx]
  nlinarith [Nat.zero_le x]

/-! ## The bookkeeping bound for the set of the Lagrange stratum -/

/-- **The degree of the set of `lagStratumAE`.**  Each disjunct of `lagStratumAE` consists of
the `1 + (m + S.j + 1)` Lagrange equations, the squared determinant and the padded atoms of one
basic of `S`.  Since padding does not raise the atom degree and `List.map` preserves the number
of basics, the total degree is at most `#basics · (Σ atomDeg(lagEqs) + atomDeg(det²)) + S.X.deg`. -/
theorem lagStratumAE_Xdeg_le_aux {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ) :
    (lagStratumAE S Phi c).X.deg ≤
      S.X.basics.length *
        (((List.ofFn (lagEqs S Phi c)).map atomDeg).sum
          + atomDeg (lagDet S Phi c * lagDet S Phi c)) + S.X.deg := by
  have hpt : ∀ B ∈ S.X.basics,
      Basic.deg ⟨List.ofFn (lagEqs S Phi c) ++ B.eqs.map (Work.WilE7.EAPoly.pad
          (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega)),
        [lagDet S Phi c * lagDet S Phi c] ++ B.pos.map (Work.WilE7.EAPoly.pad
          (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega))⟩
      ≤ Basic.deg B + (((List.ofFn (lagEqs S Phi c)).map atomDeg).sum
          + atomDeg (lagDet S Phi c * lagDet S Phi c)) := by
    intro B _
    have h1 : ((B.eqs.map (Work.WilE7.EAPoly.pad
          (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega))).map atomDeg).sum
        ≤ (B.eqs.map atomDeg).sum := by
      rw [List.map_map]
      exact Work.WilE7.list_sum_map_le B.eqs _ _ (fun Q _ => Work.WilE7.atomDeg_pad_le _ Q)
    have h2 : ((B.pos.map (Work.WilE7.EAPoly.pad
          (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega))).map atomDeg).sum
        ≤ (B.pos.map atomDeg).sum := by
      rw [List.map_map]
      exact Work.WilE7.list_sum_map_le B.pos _ _ (fun Q _ => Work.WilE7.atomDeg_pad_le _ Q)
    simp only [Basic.deg, List.map_append, List.sum_append, List.singleton_append,
      List.map_cons, List.sum_cons]
    omega
  have hmain := Work.WilE7.list_sum_map_le S.X.basics
    (fun B => Basic.deg ⟨List.ofFn (lagEqs S Phi c) ++ B.eqs.map (Work.WilE7.EAPoly.pad
          (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega)),
        [lagDet S Phi c * lagDet S Phi c] ++ B.pos.map (Work.WilE7.EAPoly.pad
          (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega))⟩)
    (fun B => Basic.deg B + (((List.ofFn (lagEqs S Phi c)).map atomDeg).sum
        + atomDeg (lagDet S Phi c * lagDet S Phi c))) hpt
  have hL : (S.X.basics.map (fun B => Basic.deg ⟨List.ofFn (lagEqs S Phi c)
        ++ B.eqs.map (Work.WilE7.EAPoly.pad
            (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega)),
        [lagDet S Phi c * lagDet S Phi c] ++ B.pos.map (Work.WilE7.EAPoly.pad
            (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega))⟩)).sum
      = (lagStratumAE S Phi c).X.deg := by
    simp only [lagStratumAE, SemiPf.deg, List.map_map]
    rfl
  have hR : (S.X.basics.map (fun B => Basic.deg B + (((List.ofFn (lagEqs S Phi c)).map atomDeg).sum
        + atomDeg (lagDet S Phi c * lagDet S Phi c)))).sum
      = S.X.deg + S.X.basics.length * (((List.ofFn (lagEqs S Phi c)).map atomDeg).sum
          + atomDeg (lagDet S Phi c * lagDet S Phi c)) := by
    rw [List.sum_map_add, List.map_const', List.sum_replicate, nsmul_eq_mul]
    rfl
  calc (lagStratumAE S Phi c).X.deg
      = _ := hL.symm
    _ ≤ _ := hmain
    _ = _ := hR
    _ = _ := Nat.add_comm _ _

/-! ## The target -/

theorem lagStratumAE_deg_uniform (F : ℕ) :
    ∃ b : Polynomial ℕ, ∀ (n m : ℕ) (S : Work.WilE9G.AmbStratum (n + (1 + m)))
      (Phi : WilkiesDesign.E.EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ),
      S.j ≤ n + (1 + m) → S.X.fmt ≤ F →
      (Work.WilE9G.Assembly.lagStratumAE S Phi c).X.deg ≤
        b.eval (S.deg + WilkiesDesign.E.atomDeg Phi + S.X.basics.length) ∧
      (Work.WilE9G.Assembly.lagStratumAE S Phi c).deg ≤
        b.eval (S.deg + WilkiesDesign.E.atomDeg Phi + S.X.basics.length) := by
  obtain ⟨b, hb⟩ := poly_bound F
  refine ⟨b, ?_⟩
  intro n m S Phi c hj hf
  -- the format bound controls the size of the multiplier block
  have hF1 : n + (1 + m) ≤ F := by
    have h := hf; simp only [SemiPf.fmt] at h; omega
  have hmF : 1 + m ≤ F := by omega
  have hjF : S.j ≤ F := by omega
  have hcard : 1 + (m + S.j + 1) ≤ 2*F+1 := by omega
  -- the abbreviations
  set x : ℕ := S.deg + atomDeg Phi + S.X.basics.length with hx
  set D : ℕ := S.deg + atomDeg Phi with hD
  set K : ℕ := S.X.basics.length with hK
  set E1 : ℕ := ((List.ofFn (lagEqs S Phi c)).map atomDeg).sum with hE1
  set E2 : ℕ := atomDeg (lagDet S Phi c * lagDet S Phi c) with hE2
  have hXdegle : S.X.deg ≤ S.deg := by
    rw [AmbStratum.deg]; exact Nat.le_add_right _ _
  have hDx : D ≤ x := by rw [hx]; exact Nat.le_add_right D K
  have hKx : K ≤ x := by rw [hx]; exact Nat.le_add_left K D
  have hXd : S.X.deg ≤ x := by rw [hx, hD, hK]; omega
  -- degrees of the two "fixed" families of atoms
  have hE1le : E1 ≤ (2*F+1)*(D+3) := by
    rw [hE1, hD]
    exact (ofFn_atomDeg_sum_le (lagEqs S Phi c) (S.deg + atomDeg Phi + 2)
      (fun a => lagEqs_totalDegree_le S Phi c a)).trans (Nat.mul_le_mul_right _ hcard)
  have hE2le : E2 ≤ 2*((2*F+1)*(D+2)) + 1 := by
    rw [hE2, hD]
    have h0 := lagDet_totalDegree_le S Phi c
    have hle : (lagDet S Phi c).totalDegree ≤ (2*F+1)*((S.deg + atomDeg Phi) + 2) :=
      h0.trans (Nat.mul_le_mul_right _ hcard)
    have hmul : (lagDet S Phi c * lagDet S Phi c).totalDegree
        ≤ 2*((2*F+1)*((S.deg + atomDeg Phi) + 2)) := by
      rw [two_mul]
      exact (MvPolynomial.totalDegree_mul _ _).trans (add_le_add hle hle)
    simp only [atomDeg] at hmul ⊢
    omega
  -- the degree of the set
  have hX : (lagStratumAE S Phi c).X.deg ≤ K*(E1+E2) + S.X.deg := by
    rw [hK, hE1, hE2]
    exact lagStratumAE_Xdeg_le_aux S Phi c
  have hEE : E1 + E2 ≤ (2*F+1)*(x+3) + (2*((2*F+1)*(x+2)) + 1) := by
    have a1 : E1 ≤ (2*F+1)*(x+3) := hE1le.trans (Nat.mul_le_mul_left _ (by omega))
    have a2 : E2 ≤ 2*((2*F+1)*(x+2)) + 1 :=
      hE2le.trans (Nat.add_le_add_right
        (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left (2*F+1) (by omega : D+2 ≤ x+2))) 1)
    exact Nat.add_le_add a1 a2
  have hE1x : E1 ≤ (2*F+1)*(x+3) := hE1le.trans (Nat.mul_le_mul_left _ (by omega))
  have hS : K*(E1+E2) + S.X.deg + E1 ≤
      x*((2*F+1)*(x+3) + (2*((2*F+1)*(x+2)) + 1)) + x + (2*F+1)*(x+3) := by
    have h1 : K*(E1+E2) ≤ x*((2*F+1)*(x+3) + (2*((2*F+1)*(x+2)) + 1)) :=
      Nat.mul_le_mul hKx hEE
    have h2 : K*(E1+E2) + S.X.deg
        ≤ x*((2*F+1)*(x+3) + (2*((2*F+1)*(x+2)) + 1)) + x := Nat.add_le_add h1 hXd
    exact Nat.add_le_add h2 hE1x
  have hZ1 : (lagStratumAE S Phi c).X.deg ≤ b.eval x :=
    hX.trans ((Nat.le_add_right _ _).trans (hS.trans (hb x)))
  -- the degree of the stratum (set plus its own equations, which are the `lagEqs`)
  have hdegE : (lagStratumAE S Phi c).deg = (lagStratumAE S Phi c).X.deg + E1 := by
    have h1 : (lagStratumAE S Phi c).deg
        = (lagStratumAE S Phi c).X.deg
          + ∑ a : Fin (1 + (m + S.j + 1)), atomDeg (lagEqs S Phi c a) := by
      simp only [Work.WilE9.Sharp.EffStratum.deg, lagStratumAE_h]
      rfl
    rw [h1, hE1, listSum_ofFn_map]
  have hZ2 : (lagStratumAE S Phi c).deg ≤ b.eval x := by
    rw [hdegE]
    exact (Nat.add_le_add_right hX E1).trans (hS.trans (hb x))
  exact ⟨hZ1, hZ2⟩

end Work.WilE9G.Assembly
