import Submission.Work.WilE10.SubPfRexp.Defs
import Submission.Work.WilC0.Bridge
import Submission.Work.WilE10.SubPfRexp.constrPoly_iff
import Submission.Work.WilE10.SubPfRexp.reexpEval_subst
import Submission.Work.WilE10.SubPfRexp.elim_coordIdx
import Submission.Work.WilE10.SubPfRexp.cube_bound

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical

namespace Work.WilE10.SubPfRexp

open WilkiesDesign WilkiesDesign.E
open Work.WilC0 (rexpEval RExPoly RExpExistI)

variable {n m r : ℕ}

/-! ## Elementary facts about `psi` -/

theorem psi_sq_mul (t : ℝ) : psi t ^ 2 * (1 + t ^ 2) = t ^ 2 := by
  rw [Work.WilE10.psi_sq]
  field_simp

theorem psi_mul_nonneg (t : ℝ) : 0 ≤ psi t * t := by
  have h : psi t * t = t ^ 2 / Real.sqrt (1 + t ^ 2) := by rw [psi]; field_simp
  rw [h]; positivity

/-! ## Projection bookkeeping -/

theorem projFirst_append (x : Fin n → ℝ) (v : Fin m → ℝ) :
    projFirst n m (Fin.append x v) = x := by
  funext i
  rw [projFirst, Fin.append_left]

theorem mem_projFirst_iff (X : Set (Fin (n + m) → ℝ)) (x : Fin n → ℝ) :
    x ∈ projFirst n m '' X ↔ ∃ v : Fin m → ℝ, Fin.append x v ∈ X := by
  constructor
  · rintro ⟨w, hw, hwx⟩
    refine ⟨fun j => w (Fin.natAdd n j), ?_⟩
    have hfin : Fin.append x (fun j => w (Fin.natAdd n j)) = w := by
      funext k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · rw [Fin.append_left, ← hwx, projFirst]
      · rw [Fin.append_right]
    rw [hfin]
    exact hw
  · rintro ⟨v, hv⟩
    exact ⟨Fin.append x v, hv, projFirst_append x v⟩

/-! ## The set attached to one branch -/

/-- **The core equivalence.** The branch set (with `L := Lbound c`) is exactly the set of `x` such
that some `Fin.append (psiV x) w` lies in the branch's part of the cube. -/
theorem branchSet_eq (c : EAChain (n + m) r) (B : Basic (n + m) r) :
    branchSet c (fun j => Lbound c j) B =
      {x : Fin n → ℝ | ∃ w : Fin m → ℝ,
        Fin.append (psiV x) w ∈ cubeC (n + m) ∧ B.holds c (Fin.append (psiV x) w)} := by
  ext x
  constructor
  · -- LHS → RHS: extract the witnesses and the psi-graph relations.
    rintro ⟨y, hy⟩
    let p : Fin n ⊕ Wit n m r B.pos.length → ℝ := Sum.elim x y
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := (constrPoly_iff c (fun j => Lbound c j) B p).mp hy
    have hxinl : ∀ a : Fin n, p (Sum.inl a) = x a := fun a => rfl
    have huv : ∀ a : Fin n, p (Sum.inr (Wit.uIdx a)) = psi (x a) := by
      intro a
      refine (Work.WilE10.Basic.psi_eq_iff_sq_and_exists_sq (z := p (Sum.inr (Wit.uIdx a)))
        (t := x a)).mpr ⟨?_, ⟨p (Sum.inr (Wit.vIdx a)), ?_⟩⟩
      · have h := h1 a
        rw [hxinl a] at h
        exact sub_eq_zero.mp h
      · have h := h2 a
        rw [hxinl a] at h
        exact sub_eq_zero.mp h
    let w : Fin m → ℝ := fun b => p (Sum.inr (Wit.wIdx b))
    have hwle : ∀ b : Fin m, |w b| ≤ 1 := by
      intro b
      refine (Work.WilE10.Basic.abs_le_one_iff_exists_sq).mpr
        ⟨p (Sum.inr (Wit.qqIdx b)), ?_⟩
      have h := h3 b
      linarith
    have hcoord : ∀ i : Fin (n + m),
        p (coordIdx (P := B.pos.length) i) = Fin.append (psiV x) w i :=
      fun i => elim_coordIdx x y (psiV x) w (fun a => huv a) (fun b => rfl) i
    have hcube : Fin.append (psiV x) w ∈ cubeC (n + m) := by
      intro i
      refine Fin.addCases (fun a => ?_) (fun b => ?_) i
      · rw [Fin.append_left]
        exact Work.WilE10.psi_abs_le_one (x a)
      · rw [Fin.append_right]
        exact hwle b
    have ht : ∀ j : Fin r, WilkiesDesign.rexp (p (Sum.inr (Wit.tIdx j))) ^ (Lbound c j)
        = Real.exp (c.ell j (Fin.append (psiV x) w)) := by
      intro j
      have hell : c.ell j (fun i => p (coordIdx (P := B.pos.length) i))
          = c.ell j (Fin.append (psiV x) w) := by
        congr 1
        funext i
        exact hcoord i
      have hLt : (Lbound c j : ℝ) * p (Sum.inr (Wit.tIdx j))
          = c.ell j (Fin.append (psiV x) w) := by
        have h := h4 j
        rw [hell] at h
        exact sub_eq_zero.mp h
      have habs : |p (Sum.inr (Wit.tIdx j))| ≤ 1 := by
        refine (Work.WilE10.Basic.abs_le_one_iff_exists_sq).mpr
          ⟨p (Sum.inr (Wit.sIdx j)), ?_⟩
        have h := h5 j
        linarith
      rw [Work.WilE10.rexp_eq_exp habs, ← Real.exp_nat_mul, hLt]
    have hholds : B.holds c (Fin.append (psiV x) w) := by
      refine ⟨?_, ?_⟩
      · intro f hf
        obtain ⟨k, hk⟩ := List.mem_iff_get.mp hf
        rw [← hk]
        have h := h6 k
        rw [reexpEval_subst c (fun j => Lbound c j) (B.eqs.get k) p
          (Fin.append (psiV x) w) hcoord ht] at h
        exact h
      · intro g hg
        obtain ⟨l, hl⟩ := List.mem_iff_get.mp hg
        rw [← hl]
        have h := h7 l
        rw [reexpEval_subst c (fun j => Lbound c j) (B.pos.get l) p
          (Fin.append (psiV x) w) hcoord ht] at h
        exact (Work.WilE10.Basic.pos_iff_exists_mul_sq_eq_one).mpr
          ⟨p (Sum.inr (Wit.pwIdx l)), sub_eq_zero.mp h⟩
    exact ⟨w, hcube, hholds⟩
  · -- RHS → LHS: build the witnesses.
    rintro ⟨w, hcube, hholds⟩
    let z : Fin (n + m) → ℝ := Fin.append (psiV x) w
    let u : Fin n → ℝ := psiV x
    let vv : Fin n → ℝ := fun a => Real.sqrt (psi (x a) * x a)
    let qq : Fin m → ℝ := fun b => Real.sqrt (1 - (w b) ^ 2)
    let t : Fin r → ℝ := fun j => c.ell j z / (Lbound c j : ℝ)
    let s : Fin r → ℝ := fun j => Real.sqrt (1 - t j ^ 2)
    let pw : Fin B.pos.length → ℝ :=
      fun l => Real.sqrt (1 / eaEval c (B.pos.get l) z)
    let y : Wit n m r B.pos.length → ℝ :=
      Sum.elim u (Sum.elim vv (Sum.elim w (Sum.elim qq (Sum.elim t (Sum.elim s pw)))))
    let p : Fin n ⊕ Wit n m r B.pos.length → ℝ := Sum.elim x y
    have hx : ∀ a : Fin n, p (Sum.inl a) = x a := fun a => rfl
    have hpu : ∀ a : Fin n, p (Sum.inr (Wit.uIdx a)) = psi (x a) := fun a => rfl
    have hpv : ∀ a : Fin n, p (Sum.inr (Wit.vIdx a)) = Real.sqrt (psi (x a) * x a) := fun a => rfl
    have hpw : ∀ b : Fin m, p (Sum.inr (Wit.wIdx b)) = w b := fun b => rfl
    have hpqq : ∀ b : Fin m, p (Sum.inr (Wit.qqIdx b)) = Real.sqrt (1 - (w b) ^ 2) := fun b => rfl
    have hpt : ∀ j : Fin r, p (Sum.inr (Wit.tIdx j)) = c.ell j z / (Lbound c j : ℝ) := fun _ => rfl
    have hps : ∀ j : Fin r,
        p (Sum.inr (Wit.sIdx j)) = Real.sqrt (1 - t j ^ 2) := fun _ => rfl
    have hppw : ∀ l : Fin B.pos.length,
        p (Sum.inr (Wit.pwIdx l)) = Real.sqrt (1 / eaEval c (B.pos.get l) z) := fun _ => rfl
    have hcoord : ∀ i : Fin (n + m),
        p (coordIdx (P := B.pos.length) i) = z i :=
      fun i => elim_coordIdx x y (psiV x) w (fun a => rfl) (fun b => rfl) i
    have hb1 : ∀ a : Fin m, (w a) ^ 2 ≤ 1 := by
      intro a
      have h := hcube (Fin.natAdd n a)
      rw [Fin.append_right] at h
      exact (sq_le_one_iff_abs_le_one (w a)).mpr h
    have ht : ∀ j : Fin r, WilkiesDesign.rexp (p (Sum.inr (Wit.tIdx j))) ^ (Lbound c j)
        = Real.exp (c.ell j z) := by
      intro j
      rw [hpt j]
      exact (Work.WilE10.Basic.exp_eq_rexp_pow (Lbound c j) (c.ell j z)
        (cube_bound c j hcube).1).symm
    refine ⟨y, (constrPoly_iff c (fun j => Lbound c j) B p).mpr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro a
      rw [hpu a, hx a, psi_sq_mul]
      ring
    · intro a
      rw [hpu a, hx a, hpv a, Real.sq_sqrt (psi_mul_nonneg (x a))]
      ring
    · intro b
      rw [hpw b, hpqq b, Real.sq_sqrt (by linarith [hb1 b])]
      ring
    · intro j
      have hz : c.ell j (fun i => p (coordIdx (P := B.pos.length) i)) = c.ell j z := by
        congr 1
        funext i
        exact hcoord i
      rw [hpt j, hz, (cube_bound c j hcube).2.2]
      ring
    · intro j
      have hle : (c.ell j z / (Lbound c j : ℝ)) ^ 2 ≤ 1 :=
        (sq_le_one_iff_abs_le_one _).mpr (cube_bound c j hcube).2.1
      have hsq : Real.sqrt (1 - t j ^ 2) ^ 2 = 1 - t j ^ 2 := by
        refine Real.sq_sqrt ?_
        show (0 : ℝ) ≤ 1 - t j ^ 2
        have ht' : t j = c.ell j z / (Lbound c j : ℝ) := rfl
        rw [ht']
        linarith
      rw [hpt j, hps j, hsq]
      ring
    · intro k
      rw [reexpEval_subst c (fun j => Lbound c j) (B.eqs.get k) p z hcoord ht]
      exact hholds.1 (B.eqs.get k) (List.get_mem _ k)
    · intro l
      have he : 0 < eaEval c (B.pos.get l) z := hholds.2 (B.pos.get l) (List.get_mem _ l)
      rw [reexpEval_subst c (fun j => Lbound c j) (B.pos.get l) p z hcoord ht, hppw l,
        Real.sq_sqrt (by positivity), one_div, mul_inv_cancel₀ (ne_of_gt he)]
      ring

/-! ## The main theorem -/

theorem subpf_to_rexp_core (n : ℕ) (Z : Set (Fin n → ℝ)) (h : WilkiesDesign.E.SubPf n Z) :
    WilkiesDesign.RExpExist (WilkiesDesign.E.psiV ⁻¹' Z) := by
  obtain ⟨m, X, rfl⟩ := h
  refine (Work.WilC0.rexExistI_iff_rexExist _).mp ?_
  have hXset : X.set = ⋃ i : Fin X.basics.length,
      {z : Fin (n + m) → ℝ | z ∈ cubeC (n + m) ∧ (X.basics.get i).holds X.c z} := by
    ext z
    simp only [SemiPf.set, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hz, B, hB, hBh⟩
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hB
      exact ⟨i, hz, by rw [hi]; exact hBh⟩
    · rintro ⟨i, hz, hh⟩
      exact ⟨hz, X.basics.get i, List.get_mem _ i, hh⟩
  have hmain : psiV ⁻¹' (projFirst n m '' X.set) = ⋃ i : Fin X.basics.length,
      branchSet X.c (fun j => Lbound X.c j) (X.basics.get i) := by
    have hunion : (⋃ i : Fin X.basics.length,
        branchSet X.c (fun j => Lbound X.c j) (X.basics.get i)) =
        ⋃ i : Fin X.basics.length, {x : Fin n → ℝ | ∃ w : Fin m → ℝ,
          Fin.append (psiV x) w ∈ cubeC (n + m) ∧
            (X.basics.get i).holds X.c (Fin.append (psiV x) w)} :=
      Set.iUnion_congr (fun i => branchSet_eq X.c (X.basics.get i))
    rw [hunion]
    ext x
    rw [Set.mem_preimage, mem_projFirst_iff, hXset]
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨w, i, hw⟩
      exact ⟨i, w, hw⟩
    · rintro ⟨i, w, hw⟩
      exact ⟨w, i, hw⟩
  rw [hmain]
  refine RExpExistI.iUnion_fin X.basics.length
    (fun i => branchSet X.c (fun j => Lbound X.c j) (X.basics.get i)) (fun i => ?_)
  exact RExpExistI.existsBlock
    (RExpExistI.rexPoly (constrPoly X.c (fun j => Lbound X.c j) (X.basics.get i)))

end Work.WilE10.SubPfRexp
