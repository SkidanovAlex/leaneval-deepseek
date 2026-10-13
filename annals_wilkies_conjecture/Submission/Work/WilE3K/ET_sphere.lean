/-
  annals_wilkies_conjecture, AREA E3K (`Submission.Work.WilE3K`): the *sphere step* of the
  arctan-elimination induction (K3).

  `ET_sphere` is the geometric half of one elimination step of `Elim.lean`.  Given a lifted
  system `E : ETData N (rt+1) n re` and a finite set `s` of nondegenerate zeros of `E`, it
  produces

  * the system `E₁ = E.sphereData c` obtained from `E` by adjoining one free coordinate (the last
    one) and the sphere equation `∑_k z_k² = c` as the last polynomial equation (`sphereData`),
    with `c = 1 + ∑_{z ∈ s} ‖z‖² > ‖z‖²` for every `z ∈ s`, and
  * the finite set `t` of the two points of that sphere over each `z ∈ s`,
    `Fin.snoc z (±√(c - ‖z‖²))`;

  and then

  * `E₁.psiMap` is a proper map: one of its components is the sphere equation, hence coercive;
  * every `z' ∈ t` is a nondegenerate zero of `E₁` (the Jacobian of `E₁` at the lift is block
    upper triangular, with diagonal block `E.jac z` and bottom right entry `2·z'_last ≠ 0`);
  * the degree grows by the two of the sphere equation (`atomDeg` counts `totalDegree + 1`);
  * `2 * s.card ≤ t.card`, the two lifts of a point being distinct.

  This is the exact analogue, for the `ETData` vocabulary, of `Work.WilE2.kho_sphere`.
-/
import Mathlib
import Submission.Work.WilE3K.ET
import Submission.Work.WilE3K.Elim
import Submission.Work.WilE3K.sum_atomDeg_sphereData_le
import Submission.Work.WilE3K.two_mul_card_le_card_sphereLift
import Submission.Work.WilE3K.sphereData_jac_last_last
import Submission.Work.WilE3K.sphereData_jac_lastCol
import Submission.Work.WilE2.det_ne_zero_of_lastCol_zero
import Submission.Work.WilE2.isProperMap_of_sq_sum_component

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilE3K
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

namespace ETSphere

variable {N rt n re : ℕ}

/-! ## §1. The sphere constant and the two lifts of a point -/

/-- `c = 1 + ∑_{z ∈ s} ‖z‖²`: the squared radius of the sphere.  It is chosen so that every
`z ∈ s` lies strictly inside it. -/
def sphC (s : Finset (Fin (N + 1) → ℝ)) : ℝ := 1 + ∑ z ∈ s, ∑ k : Fin (N + 1), (z k) ^ 2

/-- The last coordinate of the lift of `z` to the sphere `∑_k z_k² = c`. -/
def sphW (c : ℝ) (z : Fin (N + 1) → ℝ) : ℝ := Real.sqrt (c - ∑ k : Fin (N + 1), (z k) ^ 2)

/-- The lift of `z` to the sphere, with last coordinate `+√(c - ‖z‖²)`. -/
def sphPt (c : ℝ) (z : Fin (N + 1) → ℝ) : Fin ((N + 1) + 1) → ℝ := Fin.snoc z (sphW c z)

/-- The lift of `z` to the sphere, with last coordinate `-√(c - ‖z‖²)`. -/
def sphPt' (c : ℝ) (z : Fin (N + 1) → ℝ) : Fin ((N + 1) + 1) → ℝ := Fin.snoc z (-(sphW c z))

/-- The two lifts of the points of `s`. -/
def sphT (s : Finset (Fin (N + 1) → ℝ)) (c : ℝ) : Finset (Fin ((N + 1) + 1) → ℝ) :=
  s.biUnion (fun z => {sphPt c z, sphPt' c z})

/-- Every point of `s` lies strictly inside the sphere of squared radius `sphC s`. -/
theorem sphC_gt (s : Finset (Fin (N + 1) → ℝ)) {z : Fin (N + 1) → ℝ} (hz : z ∈ s) :
    (∑ k : Fin (N + 1), (z k) ^ 2) < sphC s := by
  have hle : (∑ k : Fin (N + 1), (z k) ^ 2) ≤ ∑ y ∈ s, ∑ k : Fin (N + 1), (y k) ^ 2 :=
    Finset.single_le_sum (s := s) (f := fun y => ∑ k : Fin (N + 1), (y k) ^ 2)
      (fun y _ => Finset.sum_nonneg fun k _ => sq_nonneg _) hz
  rw [sphC]
  linarith

/-- The last coordinate of the lift of a point of `s` does not vanish, so the two lifts of that
point are distinct. -/
theorem sphW_ne_zero (s : Finset (Fin (N + 1) → ℝ)) {z : Fin (N + 1) → ℝ} (hz : z ∈ s) :
    sphW (sphC s) z ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.mpr (by linarith [sphC_gt s hz]))

/-- The defining property of the last coordinate of the lift. -/
theorem sphW_sq (s : Finset (Fin (N + 1) → ℝ)) {z : Fin (N + 1) → ℝ} (hz : z ∈ s) :
    (sphW (sphC s) z) ^ 2 = sphC s - ∑ k : Fin (N + 1), (z k) ^ 2 :=
  Real.sq_sqrt (le_of_lt (by linarith [sphC_gt s hz]))

/-! ## §2. Coordinate bookkeeping for `sphereData` -/

/-- The `tan` coordinates of the sphere step are the old ones (the new coordinate is free). -/
theorem sphereData_tanCoord (E : ETData N (rt + 1) n re) (c : ℝ) (j : Fin (rt + 1)) :
    (E.sphereData c).tanCoord j = Fin.castSucc (E.tanCoord j) :=
  Fin.ext rfl

/-- The free coordinates of the sphere step are the old ones on the first `n` indices. -/
theorem sphereData_freeCoord_castSucc (E : ETData N (rt + 1) n re) (c : ℝ) (i : Fin n) :
    (E.sphereData c).freeCoord (Fin.castSucc i) = Fin.castSucc (E.freeCoord i) :=
  Fin.ext rfl

/-- The last free coordinate of the sphere step is the new coordinate. -/
theorem sphereData_freeCoord_last (E : ETData N (rt + 1) n re) (c : ℝ) :
    (E.sphereData c).freeCoord (Fin.last n) = Fin.last (N + 1) := by
  refine Fin.ext ?_
  show (rt + 1) + n = N + 1
  have h := E.h
  omega

/-- No variable of the extended ambient space maps to the last coordinate of `sphereData`. -/
theorem castAdd_ne_last (i : Fin (N + 1)) : Fin.castAdd 1 i ≠ Fin.last (N + 1) := by
  intro h
  have h' : (i : ℕ) = N + 1 := by
    have := congrArg Fin.val h
    simpa using this
  omega

/-- The last coordinate of `sphereData` is not a `tan` coordinate. -/
theorem not_last_lt (n : ℕ) : ¬ ((Fin.last n : Fin (n + 1)) : ℕ) < n := by
  rw [Fin.val_last]
  exact Nat.lt_irrefl n

/-- Unfolding of the chain coefficients of `sphereData`. -/
theorem sphereData_ca_apply (E : ETData N (rt + 1) n re) (c : ℝ) (j : Fin re)
    (i' : Fin (n + 1)) :
    (E.sphereData c).ca j i' = if h : (i' : ℕ) < n then E.ca j ⟨(i' : ℕ), h⟩ else 0 := rfl

/-- Unfolding of the arctan coefficients of `sphereData`. -/
theorem sphereData_lam_apply (E : ETData N (rt + 1) n re) (c : ℝ) (j : Fin (rt + 1))
    (i' : Fin (n + 1)) :
    (E.sphereData c).lam j i' = if h : (i' : ℕ) < n then E.lam j ⟨(i' : ℕ), h⟩ else 0 := rfl

/-- Unfolding of the equations of `sphereData`. -/
theorem sphereData_G_apply (E : ETData N (rt + 1) n re) (c : ℝ) (i' : Fin (n + 1)) :
    (E.sphereData c).G i' =
      if h : (i' : ℕ) < n then ETData.embedP (E.G ⟨(i' : ℕ), h⟩) else ETData.spherePoly c := rfl

theorem sphereData_ca_castSucc (E : ETData N (rt + 1) n re) (c : ℝ) (j : Fin re) (i : Fin n) :
    (E.sphereData c).ca j (Fin.castSucc i) = E.ca j i := by
  rw [sphereData_ca_apply, dif_pos (by simpa using i.isLt)]
  have h : (⟨(↑(Fin.castSucc i) : ℕ), i.isLt⟩ : Fin n) = i := Fin.ext (by simp)
  rw [h]

theorem sphereData_ca_last (E : ETData N (rt + 1) n re) (c : ℝ) (j : Fin re) :
    (E.sphereData c).ca j (Fin.last n) = 0 := by
  rw [sphereData_ca_apply, dif_neg (not_last_lt n)]

theorem sphereData_lam_castSucc (E : ETData N (rt + 1) n re) (c : ℝ) (j : Fin (rt + 1))
    (i : Fin n) :
    (E.sphereData c).lam j (Fin.castSucc i) = E.lam j i := by
  rw [sphereData_lam_apply, dif_pos (by simpa using i.isLt)]
  have h : (⟨(↑(Fin.castSucc i) : ℕ), i.isLt⟩ : Fin n) = i := Fin.ext (by simp)
  rw [h]

theorem sphereData_lam_last (E : ETData N (rt + 1) n re) (c : ℝ) (j : Fin (rt + 1)) :
    (E.sphereData c).lam j (Fin.last n) = 0 := by
  rw [sphereData_lam_apply, dif_neg (not_last_lt n)]

theorem sphereData_G_castSucc (E : ETData N (rt + 1) n re) (c : ℝ) (i : Fin n) :
    (E.sphereData c).G (Fin.castSucc i) = ETData.embedP (E.G i) := by
  rw [sphereData_G_apply, dif_pos (by simpa using i.isLt)]
  have h : (⟨(↑(Fin.castSucc i) : ℕ), i.isLt⟩ : Fin n) = i := Fin.ext (by simp)
  rw [h]

theorem sphereData_G_last (E : ETData N (rt + 1) n re) (c : ℝ) :
    (E.sphereData c).G (Fin.last n) = ETData.spherePoly c := by
  rw [sphereData_G_apply, dif_neg (not_last_lt n)]

/-- The free index of the new coordinate is the last free index. -/
theorem sphereData_freeIndex_last (E : ETData N (rt + 1) n re) (c : ℝ)
    (h : rt + 1 ≤ ((Fin.last (N + 1) : Fin ((N + 1) + 1)) : ℕ)) :
    (E.sphereData c).freeIndex (Fin.last (N + 1)) h = Fin.last n := by
  refine Fin.ext ?_
  show (N + 1) - (rt + 1) = n
  have h1 := E.h
  omega

/-! ## §3. Evaluation along the sphere step -/

/-- The chain of the sphere step agrees with the chain of `E` on the old coordinates. -/
theorem sphereData_ellChain (E : ETData N (rt + 1) n re) (c : ℝ) (j : Fin re)
    (z : Fin ((N + 1) + 1) → ℝ) :
    (E.sphereData c).ellChain j z = E.ellChain j (Fin.init z) := by
  show (∑ i' : Fin (n + 1), (E.sphereData c).ca j i' * z ((E.sphereData c).freeCoord i'))
      + E.cb j
    = (∑ i : Fin n, E.ca j i * (Fin.init z) (E.freeCoord i)) + E.cb j
  congr 1
  rw [Fin.sum_univ_castSucc, sphereData_ca_last, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sphereData_ca_castSucc, sphereData_freeCoord_castSucc]
  rfl

/-- Evaluating an embedded polynomial along the sphere step is evaluating along `E`. -/
theorem sphereData_evalPoly_embedP (E : ETData N (rt + 1) n re) (c : ℝ)
    (Q : EAPoly (N + 1) re) (z : Fin ((N + 1) + 1) → ℝ) :
    (E.sphereData c).evalPoly (ETData.embedP Q) z = E.evalPoly Q (Fin.init z) := by
  have hcomp : (Sum.elim z (fun j => Real.exp ((E.sphereData c).ellChain j z))) ∘
      (Sum.map (Fin.castAdd 1) id) =
      Sum.elim (Fin.init z) (fun j => Real.exp (E.ellChain j (Fin.init z))) := by
    funext x
    rcases x with i | j
    · rfl
    · simp only [Function.comp_apply, Sum.map_inr, id_eq, Sum.elim_inr]
      rw [sphereData_ellChain]
  show MvPolynomial.eval (Sum.elim z (fun j => Real.exp ((E.sphereData c).ellChain j z)))
      (MvPolynomial.rename (Sum.map (Fin.castAdd 1) id) Q)
    = MvPolynomial.eval (Sum.elim (Fin.init z) (fun j => Real.exp (E.ellChain j (Fin.init z)))) Q
  rw [MvPolynomial.eval_rename, hcomp]

/-- The arctan linear forms of the sphere step agree with those of `E`. -/
theorem sphereData_lin (E : ETData N (rt + 1) n re) (c : ℝ) (j : Fin (rt + 1))
    (z : Fin ((N + 1) + 1) → ℝ) :
    (E.sphereData c).lin j z = E.lin j (Fin.init z) := by
  show (∑ i' : Fin (n + 1), (E.sphereData c).lam j i' * z ((E.sphereData c).freeCoord i'))
      + E.mu j
    = (∑ i : Fin n, E.lam j i * (Fin.init z) (E.freeCoord i)) + E.mu j
  congr 1
  rw [Fin.sum_univ_castSucc, sphereData_lam_last, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sphereData_lam_castSucc, sphereData_freeCoord_castSucc]
  rfl

/-- The arctan equations of the sphere step agree with those of `E`. -/
theorem sphereData_tanFun (E : ETData N (rt + 1) n re) (c : ℝ) (j : Fin (rt + 1))
    (z : Fin ((N + 1) + 1) → ℝ) :
    (E.sphereData c).tanFun j z = E.tanFun j (Fin.init z) := by
  show Real.arctan (z ((E.sphereData c).tanCoord j)) - (E.sphereData c).lin j z
    = Real.arctan ((Fin.init z) (E.tanCoord j)) - E.lin j (Fin.init z)
  rw [sphereData_lin, sphereData_tanCoord]
  simp only [Fin.init]

/-- The polynomial equations of the sphere step agree with those of `E`. -/
theorem sphereData_evP_castSucc (E : ETData N (rt + 1) n re) (c : ℝ) (i : Fin n)
    (z : Fin ((N + 1) + 1) → ℝ) :
    (E.sphereData c).evP (Fin.castSucc i) z = E.evP i (Fin.init z) := by
  show (E.sphereData c).evalPoly ((E.sphereData c).G (Fin.castSucc i)) z
    = E.evalPoly (E.G i) (Fin.init z)
  rw [sphereData_G_castSucc]
  exact sphereData_evalPoly_embedP E c (E.G i) z

/-- The evaluation of the sphere polynomial along the chain of the sphere step. -/
theorem evalPoly_spherePoly (E : ETData N (rt + 1) n re) (c : ℝ)
    (z : Fin ((N + 1) + 1) → ℝ) :
    (E.sphereData c).evalPoly (ETData.spherePoly c) z
      = (∑ k : Fin ((N + 1) + 1), (z k) ^ 2) - c := by
  show MvPolynomial.eval (Sum.elim z (fun j => Real.exp ((E.sphereData c).ellChain j z)))
      ((∑ k : Fin ((N + 1) + 1), MvPolynomial.X (Sum.inl k) ^ 2) - MvPolynomial.C c)
    = (∑ k : Fin ((N + 1) + 1), (z k) ^ 2) - c
  rw [map_sub, map_sum, MvPolynomial.eval_C]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by
    rw [MvPolynomial.eval_pow, MvPolynomial.eval_X, Sum.elim_inl]

/-- The sphere equation is the last free equation of the sphere step. -/
theorem sphereData_evP_last (E : ETData N (rt + 1) n re) (c : ℝ)
    (z : Fin ((N + 1) + 1) → ℝ) :
    (E.sphereData c).evP (Fin.last n) z = (∑ k : Fin ((N + 1) + 1), (z k) ^ 2) - c := by
  show (E.sphereData c).evalPoly ((E.sphereData c).G (Fin.last n)) z
    = (∑ k : Fin ((N + 1) + 1), (z k) ^ 2) - c
  rw [sphereData_G_last]
  exact evalPoly_spherePoly E c z

/-! ## §4. Continuity -/

theorem continuous_ellChain (E : ETData N rt n re) (j : Fin re) :
    Continuous (E.ellChain j) := by
  show Continuous (fun z : Fin (N + 1) → ℝ =>
    (∑ i : Fin n, E.ca j i * z (E.freeCoord i)) + E.cb j)
  continuity

theorem continuous_lin (E : ETData N rt n re) (j : Fin rt) : Continuous (E.lin j) := by
  show Continuous (fun z : Fin (N + 1) → ℝ =>
    (∑ i : Fin n, E.lam j i * z (E.freeCoord i)) + E.mu j)
  continuity

theorem continuous_tanFun (E : ETData N rt n re) (j : Fin rt) : Continuous (E.tanFun j) := by
  show Continuous (fun z : Fin (N + 1) → ℝ =>
    Real.arctan (z (E.tanCoord j)) - E.lin j z)
  exact (Real.continuous_arctan.comp (continuous_apply (E.tanCoord j))).sub
    (continuous_lin E j)

theorem continuous_evalPoly (E : ETData N rt n re) (P : EAPoly (N + 1) re) :
    Continuous (E.evalPoly P) := by
  show Continuous (fun z : Fin (N + 1) → ℝ =>
    MvPolynomial.eval (Sum.elim z (fun j => Real.exp (E.ellChain j z))) P)
  have h : Continuous (fun z : Fin (N + 1) → ℝ =>
      Sum.elim z (fun j => Real.exp (E.ellChain j z))) := by
    rw [continuous_pi_iff]
    intro x
    rcases x with i | j
    · exact continuous_apply i
    · exact Real.continuous_exp.comp (continuous_ellChain E j)
  exact (MvPolynomial.continuous_eval P).comp h

theorem continuous_map (E : ETData N rt n re) : Continuous E.map := by
  rw [continuous_pi_iff]
  intro r
  by_cases hr : (r : ℕ) < rt
  · have hfun : (fun z => E.map z r) = E.tanFun (E.tanIndex r hr) := by
      funext z
      rw [ETData.map, dif_pos hr]
    rw [hfun]
    exact continuous_tanFun E _
  · have hfun : (fun z => E.map z r) = E.evP (E.freeIndex r (not_lt.mp hr)) := by
      funext z
      rw [ETData.map, dif_neg hr]
    rw [hfun]
    show Continuous (fun z : Fin (N + 1) → ℝ =>
      (E.evalPoly (E.G (E.freeIndex r (not_lt.mp hr)))) z)
    exact continuous_evalPoly E _

theorem continuous_psiMap (E : ETData N (rt + 1) n re) : Continuous E.psiMap := by
  rw [continuous_pi_iff]
  intro i
  have hfun : (fun z => E.psiMap z i) = fun z => E.map z (Fin.succAbove E.lastRow i) := rfl
  rw [hfun]
  exact (continuous_apply (Fin.succAbove E.lastRow i)).comp (continuous_map E)

/-! ## §5. The sphere equation is a component of `psiMap` -/

/-- The last component of `psiMap` is the sphere equation, which is coercive. -/
theorem sphereData_psiMap_last (E : ETData N (rt + 1) n re) (c : ℝ)
    (w : Fin ((N + 1) + 1) → ℝ) :
    (E.sphereData c).psiMap w (Fin.last N) = (∑ k : Fin ((N + 1) + 1), (w k) ^ 2) - c := by
  have hle : (rt : ℕ) ≤ N := by have h := E.h; omega
  have hsucc :
      (⟨rt, by have h := E.h; omega⟩ : Fin ((N + 1) + 1)) ≤ Fin.castSucc (Fin.last N) := by
    simp only [Fin.le_iff_val_le_val, Fin.val_castSucc, Fin.val_last]
    exact hle
  show (E.sphereData c).map w (Fin.succAbove (E.sphereData c).lastRow (Fin.last N))
    = (∑ k : Fin ((N + 1) + 1), (w k) ^ 2) - c
  rw [show (E.sphereData c).lastRow
      = (⟨rt, by have h := E.h; omega⟩ : Fin ((N + 1) + 1)) from rfl,
    Fin.succAbove_of_le_castSucc _ _ hsucc, Fin.succ_last]
  rw [← sphereData_freeCoord_last E c, ETData.map_free]
  exact sphereData_evP_last E c w

/-! ## §6. Coordinate bookkeeping: the general-index forms -/

theorem sphereData_ca_of_lt (E : ETData N (rt + 1) n re) (c : ℝ) (j : Fin re)
    (i' : Fin (n + 1)) (h : (i' : ℕ) < n) :
    (E.sphereData c).ca j i' = E.ca j ⟨(i' : ℕ), h⟩ := by
  rw [sphereData_ca_apply, dif_pos h]

theorem sphereData_lam_of_lt (E : ETData N (rt + 1) n re) (c : ℝ) (j : Fin (rt + 1))
    (i' : Fin (n + 1)) (h : (i' : ℕ) < n) :
    (E.sphereData c).lam j i' = E.lam j ⟨(i' : ℕ), h⟩ := by
  rw [sphereData_lam_apply, dif_pos h]

theorem sphereData_G_of_lt (E : ETData N (rt + 1) n re) (c : ℝ) (i' : Fin (n + 1))
    (h : (i' : ℕ) < n) :
    (E.sphereData c).G i' = ETData.embedP (E.G ⟨(i' : ℕ), h⟩) := by
  rw [sphereData_G_apply, dif_pos h]

/-! ## §7. The Jacobian of the sphere step -/

/-- The reindexing `Sum.map (Fin.castAdd 1) id` is injective. -/
theorem castAdd_injective' : Function.Injective (Fin.castAdd 1 : Fin (N + 1) → Fin ((N + 1) + 1)) := by
  intro a b h
  exact Fin.ext (by simpa using congrArg Fin.val h)

theorem sumMap_castAdd_injective :
    Function.Injective (Sum.map (Fin.castAdd 1) id :
      Fin (N + 1) ⊕ Fin re → Fin ((N + 1) + 1) ⊕ Fin re) :=
  Sum.map_injective.mpr ⟨castAdd_injective', Function.injective_id⟩

theorem pderiv_inl_embedP (j : Fin (N + 1)) (Q : EAPoly (N + 1) re) :
    MvPolynomial.pderiv (Sum.inl (Fin.castSucc j)) (ETData.embedP Q)
      = ETData.embedP (MvPolynomial.pderiv (Sum.inl j) Q) := by
  have h := MvPolynomial.pderiv_rename (sumMap_castAdd_injective (N := N) (re := re))
    (Sum.inl j) Q
  rw [show (Sum.map (Fin.castAdd 1) id (Sum.inl j) : Fin ((N + 1) + 1) ⊕ Fin re)
      = Sum.inl (Fin.castSucc j) from by
    rw [Sum.map_inl]
    exact congrArg Sum.inl (Fin.ext rfl)] at h
  simpa only [ETData.embedP] using h

theorem pderiv_inr_embedP (k : Fin re) (Q : EAPoly (N + 1) re) :
    MvPolynomial.pderiv (Sum.inr k) (ETData.embedP Q)
      = ETData.embedP (MvPolynomial.pderiv (Sum.inr k) Q) := by
  have h := MvPolynomial.pderiv_rename (sumMap_castAdd_injective (N := N) (re := re))
    (Sum.inr k) Q
  simpa only [ETData.embedP, Sum.map_inr, id_eq] using h

/-- The symbolic derivative of the sphere step in an old coordinate direction. -/
theorem sphereData_dcoef_castSucc (E : ETData N (rt + 1) n re) (c : ℝ) (i : Fin (N + 1))
    (k : Fin re) :
    (E.sphereData c).dcoef (Fin.castSucc i) k = E.dcoef i k := by
  unfold ETData.dcoef
  by_cases hi : rt + 1 ≤ (i : ℕ)
  · rw [dif_pos (by simpa using hi), dif_pos hi]
    have hlt :
        (((E.sphereData c).freeIndex (Fin.castSucc i) (by simpa using hi) : Fin (n + 1)) : ℕ) < n := by
      simp only [ETData.freeIndex, Fin.val_castSucc]
      have h1 := E.h
      have h2 := i.isLt
      omega
    rw [sphereData_ca_of_lt E c k _ hlt]
    exact congrArg (E.ca k) (Fin.ext rfl)
  · rw [dif_neg (by simpa using hi), dif_neg hi]

/-- The symbolic derivative of an embedded polynomial along the sphere step. -/
theorem sphereData_dPoly_embedP (E : ETData N (rt + 1) n re) (c : ℝ) (j : Fin (N + 1))
    (Q : EAPoly (N + 1) re) :
    (E.sphereData c).dPoly (Fin.castSucc j) (ETData.embedP Q)
      = ETData.embedP (E.dPoly j Q) := by
  have hsum : (∑ k : Fin re, MvPolynomial.C ((E.sphereData c).dcoef (Fin.castSucc j) k) *
        MvPolynomial.X (Sum.inr k) * MvPolynomial.pderiv (Sum.inr k) (ETData.embedP Q))
      = MvPolynomial.rename (Sum.map (Fin.castAdd 1) id)
          (∑ k : Fin re, MvPolynomial.C (E.dcoef j k) * MvPolynomial.X (Sum.inr k) *
            MvPolynomial.pderiv (Sum.inr k) Q) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sphereData_dcoef_castSucc E c j k, pderiv_inr_embedP (N := N) (re := re) k Q]
    simp only [ETData.embedP, map_mul, MvPolynomial.rename_C, MvPolynomial.rename_X,
      Sum.map_inr, id_eq]
  unfold ETData.dPoly
  rw [hsum, pderiv_inl_embedP (N := N) (re := re) j Q]
  simp only [ETData.embedP, map_add]

/-- **One entry of the Jacobian of the sphere step.**  The top left `(N+1) × (N+1)` block of the
Jacobian of `E.sphereData c` is the Jacobian of `E`. -/
theorem sphereData_jac_entry (E : ETData N (rt + 1) n re) (c : ℝ)
    (z : Fin ((N + 1) + 1) → ℝ) (i j : Fin (N + 1)) :
    (E.sphereData c).jac z (Fin.castSucc i) (Fin.castSucc j) = E.jac (Fin.init z) i j := by
  unfold ETData.jac
  simp only [Matrix.of_apply]
  by_cases hi : (i : ℕ) < rt + 1
  · have hrow : ((Fin.castSucc i : Fin ((N + 1) + 1)) : ℕ) < rt + 1 := by simpa using hi
    by_cases hj : (j : ℕ) < rt + 1
    · -- arctan row, arctan column
      simp only [dif_pos hrow, dif_pos hi]
      rw [show (E.sphereData c).tanIndex (Fin.castSucc i) hrow = E.tanIndex i hi
        from Fin.ext rfl]
      conv_lhs => rw [show Fin.castSucc j
        = (E.sphereData c).tanCoord (⟨j, hj⟩ : Fin (rt + 1)) from Fin.ext rfl]
      conv_rhs => rw [show j = E.tanCoord (⟨j, hj⟩ : Fin (rt + 1)) from Fin.ext rfl]
      simp only [ETData.dTanFun_tan]
      simp only [sphereData_tanCoord, Fin.init]
    · -- arctan row, free column
      have hj1 : (j : ℕ) - (rt + 1) < n := by
        have h1 := E.h
        have h2 := j.isLt
        omega
      simp only [dif_pos hrow, dif_pos hi]
      rw [show (E.sphereData c).tanIndex (Fin.castSucc i) hrow = E.tanIndex i hi
        from Fin.ext rfl]
      conv_lhs => rw [show Fin.castSucc j
          = (E.sphereData c).freeCoord (⟨(j : ℕ) - (rt + 1), by omega⟩ : Fin (n + 1))
        from Fin.ext (by simp only [Fin.val_castSucc, ETData.freeCoord_val]; omega)]
      conv_rhs => rw [show j = E.freeCoord (⟨(j : ℕ) - (rt + 1), hj1⟩ : Fin n)
        from Fin.ext (by simp only [ETData.freeCoord_val]; omega)]
      simp only [ETData.dTanFun_free]
      congr 1
      rw [sphereData_lam_apply, dif_pos hj1]
  · -- polynomial row: the column is a coordinate index, no case distinction
    have hrow : ¬ ((Fin.castSucc i : Fin ((N + 1) + 1)) : ℕ) < rt + 1 := by simpa using hi
    simp only [dif_neg hrow, dif_neg hi]
    have hlt :
        (((E.sphereData c).freeIndex (Fin.castSucc i) (by simpa using hi) : Fin (n + 1)) : ℕ) < n := by
      simp only [ETData.freeIndex, Fin.val_castSucc]
      have h1 := E.h
      have h2 := i.isLt
      omega
    rw [sphereData_G_of_lt E c _ hlt]
    rw [sphereData_dPoly_embedP E c j]
    rw [sphereData_evalPoly_embedP E c]
    rfl

/-- **The Jacobian of the sphere step, with the new coordinate removed.** -/
theorem sphereData_jac_submatrix' (E : ETData N (rt + 1) n re) (c : ℝ)
    (z : Fin ((N + 1) + 1) → ℝ) :
    ((E.sphereData c).jac z).submatrix Fin.castSucc Fin.castSucc = E.jac (Fin.init z) := by
  ext i j
  exact sphereData_jac_entry E c z i j

/-! ## §8. The points of the sphere over a nondegenerate zero are nondegenerate -/

/-- A point of the sphere over a nondegenerate zero of `E`, with nonvanishing last coordinate, is
a nondegenerate zero of the sphere step. -/
theorem sphereData_nondegen_snoc (E : ETData N (rt + 1) n re) (c : ℝ)
    {z : Fin (N + 1) → ℝ} {w : ℝ} (hz : E.Nondegen z)
    (hw : w ^ 2 = c - ∑ k : Fin (N + 1), (z k) ^ 2) (hw0 : w ≠ 0) :
    (E.sphereData c).Nondegen (Fin.snoc z w) := by
  have hsum : (∑ k : Fin ((N + 1) + 1), ((Fin.snoc z w : Fin ((N + 1) + 1) → ℝ) k) ^ 2)
      = (∑ k : Fin (N + 1), (z k) ^ 2) + w ^ 2 := by
    rw [Fin.sum_univ_castSucc]
    simp [Fin.snoc_castSucc, Fin.snoc_last]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [sphereData_evP_last, hsum, hw]
      ring
    · rw [sphereData_evP_castSucc, Fin.init_snoc]
      exact hz.1 i
  · intro j
    rw [sphereData_tanFun, Fin.init_snoc]
    exact hz.2.1 j
  · -- the Jacobian is block upper triangular, with diagonal blocks `E.jac z` and `2 * w`
    have h0 : ∀ i : Fin (N + 1),
        (E.sphereData c).jac (Fin.snoc z w) (Fin.castSucc i) (Fin.last (N + 1)) = 0 :=
      sphereData_jac_lastCol E c (Fin.snoc z w)
    have hA : (((E.sphereData c).jac (Fin.snoc z w)).submatrix Fin.castSucc Fin.castSucc).det
        ≠ 0 := by
      rw [sphereData_jac_submatrix' E c (Fin.snoc z w), Fin.init_snoc]
      exact hz.2.2
    have hc : (E.sphereData c).jac (Fin.snoc z w) (Fin.last (N + 1)) (Fin.last (N + 1)) ≠ 0 := by
      rw [sphereData_jac_last_last, Fin.snoc_last]
      exact mul_ne_zero (by norm_num) hw0
    exact Work.WilE2.det_ne_zero_of_lastCol_zero ((E.sphereData c).jac (Fin.snoc z w)) h0 hA hc

end ETSphere

open ETSphere

theorem ET_sphere {N rt n re : ℕ} (E : Work.WilE3K.ETData N (rt + 1) n re)
    (s : Finset (Fin (N + 1) → ℝ)) (hs : ∀ z ∈ s, E.Nondegen z) :
    ∃ (E₁ : Work.WilE3K.ETData (N + 1) (rt + 1) (n + 1) re)
      (t : Finset (Fin ((N + 1) + 1) → ℝ)),
      IsProperMap E₁.psiMap ∧ (∀ z ∈ t, E₁.Nondegen z) ∧
      (∑ i, WilkiesDesign.E.atomDeg (E₁.G i)) ≤ (∑ i, WilkiesDesign.E.atomDeg (E.G i)) + 3 ∧
      2 * s.card ≤ t.card := by
  refine ⟨E.sphereData (sphC s), sphT s (sphC s), ?_, ?_, ?_, ?_⟩
  · -- properness: the last component of `psiMap` is the coercive sphere equation
    refine Work.WilE2.isProperMap_of_sq_sum_component (sphC s)
      (E.sphereData (sphC s)).psiMap (ETSphere.continuous_psiMap _) (Fin.last N) ?_
    intro w
    exact ETSphere.sphereData_psiMap_last E (sphC s) w
  · -- nondegeneracy of the two lifts of every point of `s`
    intro z hz
    rw [sphT, Finset.mem_biUnion] at hz
    obtain ⟨z₀, hz₀, hzm⟩ := hz
    rw [Finset.mem_insert, Finset.mem_singleton] at hzm
    rcases hzm with rfl | rfl
    · exact ETSphere.sphereData_nondegen_snoc E (sphC s) (hs z₀ hz₀)
        (sphW_sq s hz₀) (sphW_ne_zero s hz₀)
    · refine ETSphere.sphereData_nondegen_snoc E (sphC s) (hs z₀ hz₀) ?_
        (neg_ne_zero.mpr (sphW_ne_zero s hz₀))
      rw [neg_sq]
      exact sphW_sq s hz₀
  · -- degree: the sphere equation contributes two total degree, hence three `atomDeg`
    exact sum_atomDeg_sphereData_le E (sphC s)
  · -- cardinality: two distinct lifts per point
    exact two_mul_card_le_card_sphereLift s (sphC s) (fun z hz => sphC_gt s hz)

end Work.WilE3K
