import Mathlib
import Submission.Work.Stems.Collar.WangThetaCupMixed
import Submission.Work.StemsB.Rat.WangThetaCupLow
import Submission.Work.Stems.Collar.wangTheta_cup_three

namespace Work.Stems.Collar

open Work.StemsB.Rat
open Work.StemsB

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 25600000
set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {E : Type} [TopologicalSpace E]

/-! ## Degree bookkeeping for the powers of the fibre class -/

/-- `b ≤ (b-1)(k+2)`. -/
private lemma b_le (b k : ℕ) (hb : 2 ≤ b) : b ≤ (b - 1) * (k + 2) := by
  have h2 : (b - 1) * 2 = (b - 1) + (b - 1) := by ring
  have h1 : (b - 1) * 2 ≤ (b - 1) * (k + 2) :=
    Nat.mul_le_mul_left (b - 1) (by omega : 2 ≤ k + 2)
  omega

/-- `x^{k+2}` lives in degree `(b-1)(k+2)`, which is `n + b` for `n = (b-1)(k+2) - b`. -/
private lemma powArg (b k : ℕ) (hb : 2 ≤ b) :
    (b - 1) * (k + 2) = ((b - 1) * (k + 2) - b) + b := by
  refine (Nat.sub_add_cancel ?_).symm
  exact b_le b k hb

/-- The result of `θ` on `x^{k+2}` lives in degree `(b-1)(k+1)`. -/
private lemma powRes (b k : ℕ) (hb : 2 ≤ b) :
    ((b - 1) * (k + 2) - b) + 1 = (b - 1) * (k + 1) := by
  have hA : 0 < (b - 1) * (k + 1) := Nat.mul_pos (by omega) (by omega)
  rw [show (b - 1) * (k + 2) = (b - 1) * (k + 1) + (b - 1) from Nat.mul_succ (b - 1) (k + 1)]
  omega

/-- The degree equality of the recursion step of `wangPow`. -/
private lemma powStep (b k : ℕ) : (b - 1) + (b - 1) * (k + 1) = (b - 1) * (k + 2) := by
  rw [show (b - 1) * (k + 2) = (b - 1) * (k + 1) + (b - 1) from Nat.mul_succ (b - 1) (k + 1)]
  omega

/-- The degree equality of the base case of `wangPow`. -/
private lemma powZero (b : ℕ) : (b - 1) = (b - 1) * (0 + 1) := by
  rw [Nat.mul_one]

/-- The degree equality of the low case of the transgression. -/
private lemma lowU (b : ℕ) (hb : 2 ≤ b) : (b - 2) + 1 = (b - 1) + 0 := by omega

/-- The degree equality of the low case of the transgression (argument). -/
private lemma lowV (b : ℕ) (hb : 2 ≤ b) : (b - 1) + (b - 1) = (b - 2) + b := by omega

/-- The degree equalities of the mixed multiplicativity formula. -/
private lemma mixH1 (b m : ℕ) (hb : 2 ≤ b) : (m + b - 1) + 1 = (b - 1) + (m + 1) := by omega
private lemma mixH2 (b m : ℕ) (hb : 2 ≤ b) : (b - 1) + (m + b) = (m + b - 1) + b := by omega
private lemma mixH3 (b m : ℕ) (hb : 2 ≤ b) : (m + b) + 0 = (b - 1) + (m + 1) := by omega

/-! ## `transT` bookkeeping -/

/-- `wangTheta` is insensitive to the spelling of its degree index. -/
private lemma wangTheta_index {b : ℕ} (hb : 2 ≤ b) (p : C(E, SphModel b))
    (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b))
    {n n' : ℕ} (h : n = n') (z : Work.Thom.Coh ℚ (n + b) ↥(p ⁻¹' {OnePoint.infty})) :
    transT ↥(p ⁻¹' {OnePoint.infty}) (congrArg (fun t => t + 1) h)
        (wangTheta b hb p d_G hT_G hT_O n z)
      = wangTheta b hb p d_G hT_G hT_O n'
          (transT ↥(p ⁻¹' {OnePoint.infty}) (congrArg (fun t => t + b) h) z) := by
  cases h
  rw [transT_self, transT_self]

/-- `transT` is proof-irrelevant in the degree equality (as an equality of maps). -/
private lemma transT_congr_fun {Y : Type} [TopologicalSpace Y] {k l : ℕ} (h h' : k = l) :
    transT Y h = transT Y h' :=
  LinearMap.ext fun v => transT_congr h h' v

/-- `transT` composes (as linear maps). -/
private lemma transT_comp_fun {Y : Type} [TopologicalSpace Y] {k l j : ℕ} (h : k = l)
    (h' : l = j) : (transT Y h').comp (transT Y h) = transT Y (h.trans h') :=
  LinearMap.ext fun v => transT_comp h h' v

/-- `transT` along a self-equality, as linear maps. -/
private lemma transT_self_fun {Y : Type} [TopologicalSpace Y] {k : ℕ} (h : k = k) :
    transT Y h = LinearMap.id :=
  LinearMap.ext fun v => transT_self h v

/-- The cup product is compatible with a degree transport in its second variable. -/
private lemma cupT_transT_right {Y : Type} [TopologicalSpace Y] (p : ℕ) {q q' : ℕ} (h : q = q')
    (x : Work.Thom.Coh ℚ p Y) (y : Work.Thom.Coh ℚ q Y) :
    cupT Y p q' x (transT Y h y)
      = transT Y (congrArg (fun t => p + t) h) (cupT Y p q x y) := by
  cases h
  rw [transT_self, transT_self]

/-- The cup product is compatible with a degree transport in its first variable. -/
private lemma cupT_transT_left {Y : Type} [TopologicalSpace Y] {p p' : ℕ} (h : p = p') (q : ℕ)
    (x : Work.Thom.Coh ℚ p Y) (y : Work.Thom.Coh ℚ q Y) :
    cupT Y p' q (transT Y h x) y
      = transT Y (congrArg (fun t => t + q) h) (cupT Y p q x y) := by
  cases h
  rw [transT_self, transT_self]

/-- Associativity of the cup product, in the `transT` spelling. -/
private lemma cupT_assoc' {Y : Type} [TopologicalSpace Y] (n m k : ℕ)
    (x : Work.Thom.Coh ℚ n Y) (y : Work.Thom.Coh ℚ m Y) (z : Work.Thom.Coh ℚ k Y) :
    transT Y (Nat.add_assoc n m k) (cupT Y (n + m) k (cupT Y n m x y) z)
      = cupT Y n (m + k) x (cupT Y m k y z) :=
  (transT_cast _ _).trans
    (Work.Cohomology.cupH'_assoc ℚ (TopCat.toSSet.obj (TopCat.of Y)) n m k x y z)

/-- `a • x + x = (a+1) • x`. -/
private lemma smul_add_self {V : Type} [AddCommMonoid V] [Module ℚ V] (a : ℚ) (x : V) :
    a • x + x = (a + 1) • x := by
  nth_rewrite 2 [← one_smul ℚ x]
  rw [← add_smul]

/-- The cup product is `ℚ`-linear in its second variable. -/
private lemma cupT_smul_right {Y : Type} [TopologicalSpace Y] (p q : ℕ) (a : ℚ)
    (u : Work.Thom.Coh ℚ p Y) (v : Work.Thom.Coh ℚ q Y) :
    cupT Y p q u (a • v) = a • cupT Y p q u v :=
  map_smul (cupT Y p q u) a v

/-! ## The recursion steps of `wangPow` -/

/-- The recursive definition of `wangPow`, with the degree equality named. -/
private lemma wangPow_succ_eq (b : ℕ) (hb : 2 ≤ b) (p : C(E, SphModel b))
    (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b))
    (x : Work.Thom.Coh ℚ (b - 1) ↥(p ⁻¹' {OnePoint.infty})) (k : ℕ) :
    wangPow b hb E p d_G hT_G hT_O x (k + 1)
      = transT ↥(p ⁻¹' {OnePoint.infty}) (powStep b k)
          (cupT ↥(p ⁻¹' {OnePoint.infty}) (b - 1) ((b - 1) * (k + 1)) x
            (wangPow b hb E p d_G hT_G hT_O x k)) :=
  transT_congr _ (powStep b k) _

/-- The base case of `wangPow`, with the degree equality named. -/
private lemma wangPow_zero_eq (b : ℕ) (hb : 2 ≤ b) (p : C(E, SphModel b))
    (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b))
    (x : Work.Thom.Coh ℚ (b - 1) ↥(p ⁻¹' {OnePoint.infty})) :
    wangPow b hb E p d_G hT_G hT_O x 0
      = transT ↥(p ⁻¹' {OnePoint.infty}) (powZero b) x :=
  transT_congr _ (powZero b) _

/-! ## The power formula for the Wang transgression -/

theorem wangTheta_pow (b : ℕ) (hb : 2 ≤ b) (hbodd : Odd b) (E : Type) [TopologicalSpace E]
    (p : C(E, Work.StemsB.SphModel b)) (d_G : ↥(Work.StemsB.sphLoopBig b))
    (hT_G : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopBig b) d_G)
    (hT_O : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopOuter b) (Work.StemsB.dOuter b)) :
    ∀ (k : ℕ) (x : Work.Thom.Coh ℚ (b - 1) ↥(p ⁻¹' {OnePoint.infty})),
    Work.StemsB.Rat.transT ↥(p ⁻¹' {OnePoint.infty})
        (by
          have hA : 0 < (b - 1) * (k + 1) := Nat.mul_pos (by omega) (by omega)
          rw [show (b - 1) * (k + 2) = (b - 1) * (k + 1) + (b - 1) from
            Nat.mul_succ (b - 1) (k + 1)]
          omega : ((b - 1) * (k + 2) - b) + 1 = (b - 1) * (k + 1))
        (Work.StemsB.Rat.wangTheta b hb p d_G hT_G hT_O ((b - 1) * (k + 2) - b)
          (Work.StemsB.Rat.transT ↥(p ⁻¹' {OnePoint.infty})
            (by
              refine (Nat.sub_add_cancel ?_).symm
              have h1 : (b - 1) * 2 ≤ (b - 1) * (k + 2) :=
                Nat.mul_le_mul_left (b - 1) (by omega : 2 ≤ k + 2)
              omega : (b - 1) * (k + 2) = ((b - 1) * (k + 2) - b) + b)
            (Work.Stems.Collar.wangPow b hb E p d_G hT_G hT_O x (k + 1))))
      = (k + 2 : ℚ) •
          Work.StemsB.Rat.cupT ↥(p ⁻¹' {OnePoint.infty}) ((b - 1) * (k + 1)) 0
            (Work.Stems.Collar.wangPow b hb E p d_G hT_G hT_O x k)
            (Work.StemsB.Rat.wangThetaLow b hb E p d_G hT_G hT_O x) := by
  have main : ∀ (k : ℕ) (x : Work.Thom.Coh ℚ (b - 1) ↥(p ⁻¹' {OnePoint.infty})),
      transT ↥(p ⁻¹' {OnePoint.infty}) (powRes b k hb)
        (wangTheta b hb p d_G hT_G hT_O ((b - 1) * (k + 2) - b)
          (transT ↥(p ⁻¹' {OnePoint.infty}) (powArg b k hb)
            (wangPow b hb E p d_G hT_G hT_O x (k + 1))))
      = (k + 2 : ℚ) • cupT ↥(p ⁻¹' {OnePoint.infty}) ((b - 1) * (k + 1)) 0
          (wangPow b hb E p d_G hT_G hT_O x k)
          (wangThetaLow b hb E p d_G hT_G hT_O x) := by
    intro k
    induction k with
    | zero =>
      intro x
      -- the low-degree lemma, in our transports
      have hlow : transT (↥(p ⁻¹' {OnePoint.infty})) (lowU b hb)
            (wangTheta b hb p d_G hT_G hT_O (b - 2)
              (transT (↥(p ⁻¹' {OnePoint.infty})) (lowV b hb) (cupT (↥(p ⁻¹' {OnePoint.infty})) (b - 1) (b - 1) x x)))
          = (2 : ℚ) • cupT (↥(p ⁻¹' {OnePoint.infty})) (b - 1) 0 x (wangThetaLow b hb E p d_G hT_G hT_O x) := by
        have h := wangTheta_cup_low b hb E p d_G hT_G hT_O x
        rw [coeff_odd b hbodd] at h
        convert h using 2 <;> rfl
      -- the LHS, in the low form
      have hL : transT (↥(p ⁻¹' {OnePoint.infty})) (powRes b 0 hb)
            (wangTheta b hb p d_G hT_G hT_O ((b - 1) * (0 + 2) - b)
              (transT (↥(p ⁻¹' {OnePoint.infty})) (powArg b 0 hb) (wangPow b hb E p d_G hT_G hT_O x 1)))
          = transT (↥(p ⁻¹' {OnePoint.infty})) (powZero b) (transT (↥(p ⁻¹' {OnePoint.infty})) (lowU b hb)
              (wangTheta b hb p d_G hT_G hT_O (b - 2)
                (transT (↥(p ⁻¹' {OnePoint.infty})) (lowV b hb) (cupT (↥(p ⁻¹' {OnePoint.infty})) (b - 1) (b - 1) x x)))) := by
        rw [wangPow_succ_eq b hb p d_G hT_G hT_O x 0]
        rw [transT_comp]
        rw [wangPow_zero_eq b hb p d_G hT_G hT_O x]
        rw [cupT_transT_right]
        rw [transT_comp]
        -- reindex `θ`
        have hbase : (b - 1) * (0 + 2) - b = b - 2 := by omega
        have hd : ((b - 1) * (0 + 2) - b) + 1 = (b - 2) + 1 := congrArg (fun t => t + 1) hbase
        have hb' : ((b - 1) * (0 + 2) - b) + b = (b - 2) + b := congrArg (fun t => t + b) hbase
        have hidx := wangTheta_index hb p d_G hT_G hT_O hbase
          (transT (↥(p ⁻¹' {OnePoint.infty})) ((congrArg (fun t => (b - 1) + t) (powZero b)).trans
            ((powStep b 0).trans (powArg b 0 hb))) (cupT (↥(p ⁻¹' {OnePoint.infty})) (b - 1) (b - 1) x x))
        have hθ : wangTheta b hb p d_G hT_G hT_O ((b - 1) * (0 + 2) - b)
              (transT (↥(p ⁻¹' {OnePoint.infty})) ((congrArg (fun t => (b - 1) + t) (powZero b)).trans
                ((powStep b 0).trans (powArg b 0 hb))) (cupT (↥(p ⁻¹' {OnePoint.infty})) (b - 1) (b - 1) x x))
            = transT (↥(p ⁻¹' {OnePoint.infty})) hd.symm
                (wangTheta b hb p d_G hT_G hT_O (b - 2)
                  (transT (↥(p ⁻¹' {OnePoint.infty})) hb'
                    (transT (↥(p ⁻¹' {OnePoint.infty})) ((congrArg (fun t => (b - 1) + t) (powZero b)).trans
                      ((powStep b 0).trans (powArg b 0 hb))) (cupT (↥(p ⁻¹' {OnePoint.infty})) (b - 1) (b - 1) x x)))) :=
          (transT_round hd _).trans (congrArg (transT (↥(p ⁻¹' {OnePoint.infty})) hd.symm) hidx)
        rw [hθ]
        rw [transT_comp]
        have harg0 : transT (↥(p ⁻¹' {OnePoint.infty})) hb'
              (transT (↥(p ⁻¹' {OnePoint.infty})) ((congrArg (fun t => (b - 1) + t) (powZero b)).trans
                ((powStep b 0).trans (powArg b 0 hb))) (cupT (↥(p ⁻¹' {OnePoint.infty})) (b - 1) (b - 1) x x))
            = transT (↥(p ⁻¹' {OnePoint.infty})) (lowV b hb) (cupT (↥(p ⁻¹' {OnePoint.infty})) (b - 1) (b - 1) x x) := by
          rw [transT_comp]
        rw [harg0]
        rw [transT_congr_fun (hd.symm.trans (powRes b 0 hb)) ((lowU b hb).trans (powZero b))]
        rw [← transT_comp (lowU b hb) (powZero b) _]
        rfl
      -- the RHS, in the low form
      have hR : (↑(0 : ℕ) + 2 : ℚ) • cupT (↥(p ⁻¹' {OnePoint.infty})) ((b - 1) * (0 + 1)) 0
            (wangPow b hb E p d_G hT_G hT_O x 0)
            (wangThetaLow b hb E p d_G hT_G hT_O x)
          = transT (↥(p ⁻¹' {OnePoint.infty})) (powZero b) ((2 : ℚ) • cupT (↥(p ⁻¹' {OnePoint.infty})) (b - 1) 0 x
              (wangThetaLow b hb E p d_G hT_G hT_O x)) := by
        rw [wangPow_zero_eq b hb p d_G hT_G hT_O x]
        rw [cupT_transT_left]
        rw [show (↑(0 : ℕ) + 2 : ℚ) = 2 by norm_num]
        rw [transT_congr (congrArg (fun t => t + 0) (powZero b)) (powZero b) _]
        rw [← map_smul]
        rfl
      rw [hL, hR]
      exact congrArg (transT (↥(p ⁻¹' {OnePoint.infty})) (powZero b)) hlow
    | succ k ih =>
      intro x
      -- the parity of the two coefficients of the mixed formula
      have hC1 : ((-1 : ℚ) ^ (b - 1)) = 1 := by
        obtain ⟨j, _⟩ := hbodd
        exact Even.neg_one_pow ⟨j, by omega⟩
      have hC2 : ((-1 : ℚ) ^ ((b - 1) * (((b - 1) * (k + 2) - b) + b)
            + (((b - 1) * (k + 2) - b) + b))) = 1 := by
        have hsub : ((b - 1) * (k + 2) - b) + b = (b - 1) * (k + 2) :=
          Nat.sub_add_cancel (b_le b k hb)
        have hev : Even ((b - 1) * (k + 2)) := by
          obtain ⟨j, _⟩ := hbodd
          rw [show b - 1 = 2 * j from by omega]
          exact ⟨j * (k + 2), by ring⟩
        rw [hsub]
        exact Even.neg_one_pow ((hev.mul_left (b - 1)).add hev)
      -- the mixed formula
      have hmix := wangTheta_cup_mixed b hb E p d_G hT_G hT_O ((b - 1) * (k + 2) - b) x
        (transT (↥(p ⁻¹' {OnePoint.infty})) (powArg b k hb) (wangPow b hb E p d_G hT_G hT_O x (k + 1)))
      rw [hC1, hC2, one_smul, one_smul] at hmix
      -- the index change
      have h3 : (b - 1) * (k + 3) = (b - 1) * (k + 2) + (b - 1) := by
        rw [show k + 3 = (k + 2) + 1 from rfl, Nat.mul_succ]
      have hD : (b - 1) * (k + 3) - b = ((b - 1) * (k + 2) - b) + b - 1 := by
        have hb2 := b_le b k hb
        omega
      have hd : ((b - 1) * (k + 3) - b) + 1 = (((b - 1) * (k + 2) - b) + b - 1) + 1 :=
        congrArg (fun t => t + 1) hD
      have hb' : ((b - 1) * (k + 3) - b) + b = (((b - 1) * (k + 2) - b) + b - 1) + b :=
        congrArg (fun t => t + b) hD
      have hK : (b - 1) + (((b - 1) * (k + 2) - b) + 1) = (b - 1) * (k + 2) + 0 := by
        have hb2 := b_le b k hb
        omega
      -- unfold the power `x^{k+3}`
      rw [wangPow_succ_eq b hb p d_G hT_G hT_O x (k + 1)]
      rw [transT_comp]
      set Z := transT (↥(p ⁻¹' {OnePoint.infty})) ((powStep b (k + 1)).trans (powArg b (k + 1) hb))
          (cupT (↥(p ⁻¹' {OnePoint.infty})) (b - 1) ((b - 1) * (k + 2)) x
            (wangPow b hb E p d_G hT_G hT_O x (k + 1))) with hZ
      -- reindex `θ`
      have hidx := wangTheta_index hb p d_G hT_G hT_O hD Z
      have hθ : wangTheta b hb p d_G hT_G hT_O ((b - 1) * (k + 3) - b) Z
            = transT (↥(p ⁻¹' {OnePoint.infty})) hd.symm
                (wangTheta b hb p d_G hT_G hT_O (((b - 1) * (k + 2) - b) + b - 1)
                  (transT (↥(p ⁻¹' {OnePoint.infty})) hb' Z)) :=
        (transT_round hd _).trans (congrArg (transT (↥(p ⁻¹' {OnePoint.infty})) hd.symm) hidx)
      rw [hθ]
      rw [transT_comp]
      -- the argument comparison
      have harg : transT (↥(p ⁻¹' {OnePoint.infty})) hb' Z
          = transT (↥(p ⁻¹' {OnePoint.infty})) (mixH2 b ((b - 1) * (k + 2) - b) hb)
              (cupT (↥(p ⁻¹' {OnePoint.infty})) (b - 1) (((b - 1) * (k + 2) - b) + b) x
                (transT (↥(p ⁻¹' {OnePoint.infty})) (powArg b k hb) (wangPow b hb E p d_G hT_G hT_O x (k + 1)))) := by
        rw [hZ]
        rw [transT_comp]
        rw [cupT_transT_right]
        rw [transT_comp]
      rw [harg]
      -- insert the transport `hK` and apply the mixed formula
      rw [transT_congr_fun (hd.symm.trans (powRes b (k + 1) hb))
        ((mixH1 b ((b - 1) * (k + 2) - b) hb).trans hK)]
      refine (transT_comp (mixH1 b ((b - 1) * (k + 2) - b) hb) hK _).symm.trans ?_
      rw [hmix]
      -- the two terms
      let Wk := cupT (↥(p ⁻¹' {OnePoint.infty})) ((b - 1) * (k + 1)) 0 (wangPow b hb E p d_G hT_G hT_O x k)
        (wangThetaLow b hb E p d_G hT_G hT_O x)
      let Wk1 := cupT (↥(p ⁻¹' {OnePoint.infty})) ((b - 1) * (k + 2)) 0 (wangPow b hb E p d_G hT_G hT_O x (k + 1))
        (wangThetaLow b hb E p d_G hT_G hT_O x)
      have hθy : wangTheta b hb p d_G hT_G hT_O ((b - 1) * (k + 2) - b)
            (transT (↥(p ⁻¹' {OnePoint.infty})) (powArg b k hb) (wangPow b hb E p d_G hT_G hT_O x (k + 1)))
          = transT (↥(p ⁻¹' {OnePoint.infty})) ((powRes b k hb).symm) ((k + 2 : ℚ) • Wk) :=
        (transT_round (powRes b k hb) _).trans
          (congrArg (transT (↥(p ⁻¹' {OnePoint.infty})) ((powRes b k hb).symm)) (ih x))
      have hXk : cupT (↥(p ⁻¹' {OnePoint.infty})) (b - 1) ((b - 1) * (k + 1)) x (wangPow b hb E p d_G hT_G hT_O x k)
          = transT (↥(p ⁻¹' {OnePoint.infty})) ((powStep b k).symm) (wangPow b hb E p d_G hT_G hT_O x (k + 1)) :=
        (transT_round (powStep b k) _).trans
          (congrArg (transT (↥(p ⁻¹' {OnePoint.infty})) ((powStep b k).symm))
            (wangPow_succ_eq b hb p d_G hT_G hT_O x k).symm)
      have assocH : ((b - 1) + ((b - 1) * (k + 1))) + 0 = (b - 1) + ((b - 1) * (k + 1)) := by
        omega
      have hassoc : cupT (↥(p ⁻¹' {OnePoint.infty})) (b - 1) ((b - 1) * (k + 1)) x Wk
          = transT (↥(p ⁻¹' {OnePoint.infty})) assocH
              (cupT (↥(p ⁻¹' {OnePoint.infty})) ((b - 1) + ((b - 1) * (k + 1))) 0
                (cupT (↥(p ⁻¹' {OnePoint.infty})) (b - 1) ((b - 1) * (k + 1)) x
                  (wangPow b hb E p d_G hT_G hT_O x k))
                (wangThetaLow b hb E p d_G hT_G hT_O x)) := by
        have h := (cupT_assoc' (b - 1) ((b - 1) * (k + 1)) 0 x
          (wangPow b hb E p d_G hT_G hT_O x k)
          (wangThetaLow b hb E p d_G hT_G hT_O x)).symm
        rw [transT_congr_fun (Nat.add_assoc (b - 1) ((b - 1) * (k + 1)) 0) assocH] at h
        exact h
      rw [hθy]
      rw [show transT (↥(p ⁻¹' {OnePoint.infty})) ((powRes b k hb).symm) ((k + 2 : ℚ) • Wk)
            = (k + 2 : ℚ) • transT (↥(p ⁻¹' {OnePoint.infty})) ((powRes b k hb).symm) Wk from map_smul _ _ _]
      rw [cupT_smul_right]
      rw [cupT_transT_right]
      rw [hassoc]
      rw [hXk]
      rw [cupT_transT_left]
      rw [cupT_transT_left]
      rw [map_add]
      rw [map_smul]
      repeat rw [transT_comp]
      rw [transT_self]
      rw [smul_add_self]
      rw [show (↑k + 2 + 1 : ℚ) = (↑(k + 1) + 2 : ℚ) by push_cast; ring]
  intro k x
  convert main k x using 2 <;> rfl

end

end Work.Stems.Collar
