import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Defs
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.dthIter_coef_mul_eqOn
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.dzIter_sum_coef_eqOn
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.dthIter_congr_eqOn
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.dzIter_congr_eqOn
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `JetCalc/Expand` — the jet expansion of a differential combination

This module assembles the primitive jet-calculus lemmas proved in the sibling modules
(`dthIter_coef_mul_eqOn`, `dzIter_sum_coef_eqOn`, `dthIter_Dz_eqOn`, and the two
congruence lemmas) into the two identities used by the slot-convergence theorem:

* `mixed_coef_mul_pt`: the mixed jet of `c(θ)·X` is the angular Leibniz sum of `c`
  against the mixed jets of `X` (`coefJetS c j i 0 X`);
* `mixed_combo_pt`: for `j + i ≤ 2`, the mixed jet of the combination
  `a(θ)·X + b(θ)·D_zX + c(θ)·∂_θX` is `EJet a b c j i X`.

Also here: the two elementary quadrant facts (`sin_two_pos_quad`, `cos_pos_quad`),
the `z`-independence of the angular coefficients (`dthIter_const_z`), the `D_z`-shift
`mixed_Dz_shift`, and the congruence of `mixed` on the open quadrant.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT.Slots.JetCalc

/-- `sin(2θ)` is positive on the open quadrant. -/
theorem sin_two_pos_quad {z θ : ℝ} (h : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [h.2.1]) (by linarith [h.2.2, Real.pi_pos])

/-- `cos θ` is positive on the open quadrant. -/
theorem cos_pos_quad {z θ : ℝ} (h : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [h.2.1, Real.pi_pos], by linarith [h.2.2, Real.pi_pos]⟩

/-! ## Congruence and the `z`-independence of the angular coefficients -/

/-- Congruence of `mixed` under equality on the open quadrant. -/
theorem mixed_congr_eqOn {F G : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry F) (Function.uncurry G) Work.FTS.EllipticEst.Q0) (j i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.mixed j i F))
      (Function.uncurry (Work.Spaces.mixed j i G)) Work.FTS.EllipticEst.Q0 :=
  dzIter_congr_eqOn (dthIter_congr_eqOn h i) j

/-- The iterated angular operator applied to a `θ`-only function does not depend on `z`. -/
theorem dthIter_const_z (k : ℕ) (c : ℝ → ℝ) (z z' : ℝ) :
    Work.Spaces.DthIter k (fun _ (θ' : ℝ) => c θ') z
      = Work.Spaces.DthIter k (fun _ (θ' : ℝ) => c θ') z' := by
  induction k generalizing z z' with
  | zero => rfl
  | succ k ih =>
      funext θ
      show Real.sin (2 * θ)
            * deriv (fun θ' => Work.Spaces.DthIter k (fun _ (θ'' : ℝ) => c θ'') z θ') θ
        = Real.sin (2 * θ)
            * deriv (fun θ' => Work.Spaces.DthIter k (fun _ (θ'' : ℝ) => c θ'') z' θ') θ
      rw [ih z z']

/-- Pointwise form of `dthIter_const_z`. -/
theorem dthIter_const_z_pt (k : ℕ) (c : ℝ → ℝ) (z z' θ : ℝ) :
    Work.Spaces.DthIter k (fun _ (θ' : ℝ) => c θ') z θ
      = Work.Spaces.DthIter k (fun _ (θ' : ℝ) => c θ') z' θ :=
  congrFun (dthIter_const_z k c z z') θ

/-! ## Congruence of `D_θ` and Clairaut for the iterates

The child module `JetCalc/dthIter_Dz_eqOn` carries the same commutation identity; as it is not
needed by anything else here, the identity is reproved below in a form self-contained in this
module (so that the slot theorem does not depend on it). -/

/-- `D_θ` is congruent under equality on the open quadrant. -/
theorem Dth_congr_eqOn {F G : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry F) (Function.uncurry G) Work.FTS.EllipticEst.Q0) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth F)) (Function.uncurry (Work.Spaces.Dth G))
      Work.FTS.EllipticEst.Q0 := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  show Real.sin (2 * θ) * Work.Spaces.pth F z θ = Real.sin (2 * θ) * Work.Spaces.pth G z θ
  rw [Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 h hp]

/-- Clairaut for the iterates at finite order: `D_θ^i(D_zX) = D_z(D_θ^iX)` on the open
quadrant, for `X` of class `C^{i+1}`. -/
theorem dthIter_Dz_eqOn_alt : ∀ (i : ℕ) (X : ℝ → ℝ → ℝ),
    ContDiffOn ℝ (i + 1) (Function.uncurry X) Work.FTS.EllipticEst.Q0 →
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz X)))
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i X)))
      Work.FTS.EllipticEst.Q0 := by
  intro i
  induction i with
  | zero => intro X hX; exact fun _ _ => rfl
  | succ i ih =>
      intro X hX p hp
      obtain ⟨z, θ⟩ := p
      have hXi : ContDiffOn ℝ (i + 1) (Function.uncurry X) Work.FTS.EllipticEst.Q0 :=
        hX.of_le (Nat.cast_le.mpr (Nat.le_succ (i + 1)))
      have hih : Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz X)))
          (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i X)))
          Work.FTS.EllipticEst.Q0 := ih X hXi
      have hDthC : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.DthIter i X))
          Work.FTS.EllipticEst.Q0 :=
        Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_DthIter_le
          (n := Nat.succ i + 1) Work.FTS.EllipticEst.isOpen_Q0 i 2 le_rfl hX
      have hstep : Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.Dz X)) z θ
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DthIter i X)) z θ := by
        show Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DthIter i (Work.Spaces.Dz X)) z θ
            = Real.sin (2 * θ)
                * Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DthIter i X)) z θ
        rw [Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hih hp]
      have hcl : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i X)) z θ
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DthIter i X)) z θ :=
        Work.Spaces.Dz_Dth_comm
          (hDthC.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp))
      show Work.Spaces.DthIter (i + 1) (Work.Spaces.Dz X) z θ
          = Work.Spaces.Dz (Work.Spaces.DthIter (i + 1) X) z θ
      rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ, hstep, hcl]

/-! ## The `D_z`-shift of a mixed jet -/

/-- A `D_z` inside a mixed jet shifts the radial order by one. -/
theorem mixed_Dz_shift {j i : ℕ} {Y : ℝ → ℝ → ℝ}
    (hY : ContDiffOn ℝ (j + i + 1) (Function.uncurry Y) Work.FTS.EllipticEst.Q0) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.mixed j i (Work.Spaces.Dz Y) z θ
        = Work.Spaces.mixed (j + 1) i Y z θ := by
  intro z θ hp
  have h1 : ContDiffOn ℝ (i + 1) (Function.uncurry Y) Work.FTS.EllipticEst.Q0 :=
    hY.of_le (Nat.cast_le.mpr (by omega : i + 1 ≤ j + i + 1))
  have hcomm : Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz Y)))
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i Y))) Work.FTS.EllipticEst.Q0 :=
    dthIter_Dz_eqOn_alt i Y h1
  have h2 := dzIter_congr_eqOn hcomm j hp
  have hDz1 : Work.Spaces.Dz (Work.Spaces.DthIter i Y)
      = Work.Spaces.DzIter 1 (Work.Spaces.DthIter i Y) := by
    rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz Y)) z θ
      = Work.Spaces.DzIter (j + 1) (Work.Spaces.DthIter i Y) z θ
  rw [show Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz Y)) z θ
      = Work.Spaces.DzIter j (Work.Spaces.Dz (Work.Spaces.DthIter i Y)) z θ from h2, hDz1]
  exact congrFun (congrFun (Work.Spaces.DzIter_add_right j 1
    (Work.Spaces.DthIter i Y)).symm z) θ

/-! ## The expansion of a coefficient times a function -/

/-- **The coefficient expansion.**  For a `θ`-dependent coefficient `c` and a function `X`
which is `C^{i+j}` on the open quadrant, the mixed jet `D_z^jD_θ^i(c·X)` is the angular
Leibniz sum of the coefficient against the mixed jets of `X`. -/
theorem mixed_coef_mul_pt {j i : ℕ} {c : ℝ → ℝ} {X : ℝ → ℝ → ℝ}
    (hX : ContDiffOn ℝ (i + j) (Function.uncurry X) Work.FTS.EllipticEst.Q0)
    (hc : ContDiffOn ℝ i (fun p : ℝ × ℝ => c p.2) Work.FTS.EllipticEst.Q0) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.mixed j i (fun z θ => c θ * X z θ) z θ = coefJetS c j i 0 X z θ := by
  intro z θ hp
  have hXi : ContDiffOn ℝ i (Function.uncurry X) Work.FTS.EllipticEst.Q0 :=
    hX.of_le (Nat.cast_le.mpr (by omega : i ≤ i + j))
  have h1 : Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (fun z θ => c θ * X z θ)))
      (Function.uncurry (fun z θ => ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) *
        (Work.Spaces.DthIter k (fun _ (θ' : ℝ) => c θ') z θ
          * Work.Spaces.DthIter (i - k) X z θ)))
      Work.FTS.EllipticEst.Q0 := dthIter_coef_mul_eqOn hXi hc
  have hsumEq : Set.EqOn
      (Function.uncurry (fun z θ => ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) *
        (Work.Spaces.DthIter k (fun _ (θ' : ℝ) => c θ') z θ
          * Work.Spaces.DthIter (i - k) X z θ)))
      (Function.uncurry (fun z θ => ∑ k ∈ Finset.range (i + 1),
        ((i.choose k : ℝ) * Work.Spaces.DthIter k (fun _ (θ' : ℝ) => c θ') z θ)
          * Work.Spaces.DthIter (i - k) X z θ))
      Work.FTS.EllipticEst.Q0 := by
    intro p hp'
    simp only [Function.uncurry]
    exact Finset.sum_congr rfl (fun k hk => by ring)
  have hkey := h1.trans hsumEq
  have h2 := dzIter_congr_eqOn hkey j hp
  have hbridge : Set.EqOn
      (Function.uncurry (fun z θ => ∑ k ∈ Finset.range (i + 1),
        ((i.choose k : ℝ) * Work.Spaces.DthIter k (fun _ (θ' : ℝ) => c θ') z θ)
          * Work.Spaces.DthIter (i - k) X z θ))
      (Function.uncurry (fun z' θ' => ∑ k ∈ Finset.range (i + 1),
        ((i.choose k : ℝ) * Work.Spaces.DthIter k (fun _ (θ'' : ℝ) => c θ'') z θ')
          * Work.Spaces.DthIter (i - k) X z' θ'))
      Work.FTS.EllipticEst.Q0 := by
    intro p hp'
    simp only [Function.uncurry]
    exact Finset.sum_congr rfl (fun k hk => by rw [dthIter_const_z_pt k c p.1 z p.2])
  have h2b := dzIter_congr_eqOn hbridge j hp
  have hF : ∀ k ∈ Finset.range (i + 1),
      ContDiffOn ℝ j (Function.uncurry (Work.Spaces.DthIter (i - k) X))
        Work.FTS.EllipticEst.Q0 :=
    fun k hk => Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_DthIter_le
      Work.FTS.EllipticEst.isOpen_Q0 (i - k) j (Nat.add_le_add_right (Nat.sub_le i k) j) hX
  have h3 := dzIter_sum_coef_eqOn (s := Finset.range (i + 1))
    (c := fun k (θ' : ℝ) => (i.choose k : ℝ) * Work.Spaces.DthIter k (fun _ (θ'' : ℝ) => c θ'') z θ')
    (F := fun k => Work.Spaces.DthIter (i - k) X) j hF hp
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => c θ * X z θ)) z θ
      = coefJetS c j i 0 X z θ
  rw [show Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => c θ * X z θ)) z θ
      = Work.Spaces.DzIter j (fun z θ => ∑ k ∈ Finset.range (i + 1),
          ((i.choose k : ℝ) * Work.Spaces.DthIter k (fun _ (θ' : ℝ) => c θ') z θ)
            * Work.Spaces.DthIter (i - k) X z θ) z θ from h2]
  rw [show Work.Spaces.DzIter j (fun z θ => ∑ k ∈ Finset.range (i + 1),
          ((i.choose k : ℝ) * Work.Spaces.DthIter k (fun _ (θ' : ℝ) => c θ') z θ)
            * Work.Spaces.DthIter (i - k) X z θ) z θ
      = Work.Spaces.DzIter j (fun z' θ' => ∑ k ∈ Finset.range (i + 1),
          ((i.choose k : ℝ) * Work.Spaces.DthIter k (fun _ (θ'' : ℝ) => c θ'') z θ')
            * Work.Spaces.DthIter (i - k) X z' θ') z θ from h2b]
  rw [show Work.Spaces.DzIter j (fun z' θ' => ∑ k ∈ Finset.range (i + 1),
          ((i.choose k : ℝ) * Work.Spaces.DthIter k (fun _ (θ'' : ℝ) => c θ'') z θ')
            * Work.Spaces.DthIter (i - k) X z' θ') z θ
      = ∑ k ∈ Finset.range (i + 1),
          ((i.choose k : ℝ) * Work.Spaces.DthIter k (fun _ (θ'' : ℝ) => c θ'') z θ)
            * Work.Spaces.DzIter j (Work.Spaces.DthIter (i - k) X) z θ from h3]
  rw [coefJetS]
  simp only [Nat.add_zero]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [show Work.Spaces.DzIter j (Work.Spaces.DthIter (i - k) X) z θ
      = Work.Spaces.mixed j (i - k) X z θ from rfl]
  ring

/-! ## The master expansion of the combination -/

/-- **The combinatorial identity.**  For `j + i ≤ 2`, the mixed jet of
`a(θ)·X + b(θ)·D_zX + c(θ)·∂_θX` is the jet functional `EJet`. -/
theorem mixed_combo_pt {j i : ℕ} (hji : j + i ≤ 2) {a b c : ℝ → ℝ} {X : ℝ → ℝ → ℝ}
    (hX : ContDiffOn ℝ 3 (Function.uncurry X) Work.FTS.EllipticEst.Q0)
    (ha : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => a p.2) Work.FTS.EllipticEst.Q0)
    (hb : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => b p.2) Work.FTS.EllipticEst.Q0)
    (hc : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => c p.2) Work.FTS.EllipticEst.Q0) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.mixed j i (combo a b c X) z θ = EJet a b c j i X z θ := by
  intro z θ hp
  have hji3 : j + i ≤ 3 := by omega
  have hij : i + j ≤ 3 := by omega
  have hT1 : ContDiffOn ℝ (i + j) (fun p : ℝ × ℝ => a p.2 * X p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
    have h1 : ContDiffOn ℝ (i + j) (fun p : ℝ × ℝ => a p.2) Work.FTS.EllipticEst.Q0 :=
      ha.of_le (Nat.cast_le.mpr (by omega : i + j ≤ 2))
    have h2 : ContDiffOn ℝ (i + j) (fun p : ℝ × ℝ => X p.1 p.2) Work.FTS.EllipticEst.Q0 :=
      hX.of_le (Nat.cast_le.mpr hij)
    exact h1.mul h2
  have hDzX : ContDiffOn ℝ (i + j) (fun p : ℝ × ℝ => Work.Spaces.Dz X p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_Dz_of_succ
      Work.FTS.EllipticEst.isOpen_Q0 (n := 2) hX).of_le (Nat.cast_le.mpr (by omega : i + j ≤ 2))
  have hT2 : ContDiffOn ℝ (i + j) (fun p : ℝ × ℝ => b p.2 * Work.Spaces.Dz X p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
    have h1 : ContDiffOn ℝ (i + j) (fun p : ℝ × ℝ => b p.2) Work.FTS.EllipticEst.Q0 :=
      hb.of_le (Nat.cast_le.mpr (by omega : i + j ≤ 2))
    exact h1.mul hDzX
  have hpthX : ContDiffOn ℝ (i + j) (fun p : ℝ × ℝ => Work.Spaces.pth X p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_pth_of_succ
      Work.FTS.EllipticEst.isOpen_Q0 (n := 2) hX).of_le (Nat.cast_le.mpr (by omega : i + j ≤ 2))
  have hT3 : ContDiffOn ℝ (i + j) (fun p : ℝ × ℝ => c p.2 * Work.Spaces.pth X p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
    have h1 : ContDiffOn ℝ (i + j) (fun p : ℝ × ℝ => c p.2) Work.FTS.EllipticEst.Q0 :=
      hc.of_le (Nat.cast_le.mpr (by omega : i + j ≤ 2))
    exact h1.mul hpthX
  have hT12 : ContDiffOn ℝ (i + j)
      (fun p : ℝ × ℝ => a p.2 * X p.1 p.2 + b p.2 * Work.Spaces.Dz X p.1 p.2)
      Work.FTS.EllipticEst.Q0 := hT1.add hT2
  -- additivity of `mixed` over the two sums
  have hadd1 : Work.Spaces.mixed j i
      (fun z θ => a θ * X z θ + b θ * Work.Spaces.Dz X z θ + c θ * Work.Spaces.pth X z θ) z θ
      = Work.Spaces.mixed j i (fun z θ => a θ * X z θ + b θ * Work.Spaces.Dz X z θ) z θ
        + Work.Spaces.mixed j i (fun z θ => c θ * Work.Spaces.pth X z θ) z θ :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn Work.FTS.EllipticEst.isOpen_Q0
      hT12 hT3 i j le_rfl (z, θ) hp
  have hadd2 : Work.Spaces.mixed j i (fun z θ => a θ * X z θ + b θ * Work.Spaces.Dz X z θ) z θ
      = Work.Spaces.mixed j i (fun z θ => a θ * X z θ) z θ
        + Work.Spaces.mixed j i (fun z θ => b θ * Work.Spaces.Dz X z θ) z θ :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn Work.FTS.EllipticEst.isOpen_Q0
      hT1 hT2 i j le_rfl (z, θ) hp
  -- the three expansions
  have hXi : ContDiffOn ℝ (i + j) (Function.uncurry X) Work.FTS.EllipticEst.Q0 :=
    hX.of_le (Nat.cast_le.mpr hij)
  have eT1 : Work.Spaces.mixed j i (fun z θ => a θ * X z θ) z θ = coefJetS a j i 0 X z θ :=
    mixed_coef_mul_pt hXi (ha.of_le (Nat.cast_le.mpr (by omega : i ≤ 2))) z θ hp
  have eT2 : Work.Spaces.mixed j i (fun z θ => b θ * Work.Spaces.Dz X z θ) z θ
      = coefJetS b (j + 1) i 0 X z θ := by
    have hbase : Work.Spaces.mixed j i (fun z θ => b θ * Work.Spaces.Dz X z θ) z θ
        = coefJetS b j i 0 (Work.Spaces.Dz X) z θ :=
      mixed_coef_mul_pt hDzX (hb.of_le (Nat.cast_le.mpr (by omega : i ≤ 2))) z θ hp
    rw [hbase, coefJetS, coefJetS]
    simp only [Nat.add_zero]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hY : ContDiffOn ℝ (j + (i - k) + 1) (Function.uncurry X) Work.FTS.EllipticEst.Q0 :=
      hX.of_le (Nat.cast_le.mpr (by omega : j + (i - k) + 1 ≤ 3))
    rw [mixed_Dz_shift (j := j) (i := i - k) (Y := X) hY z θ hp]
  have hcd : ContDiffOn ℝ i (fun p : ℝ × ℝ => c p.2 / Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 := by
    have h1 : ContDiffOn ℝ i (fun p : ℝ × ℝ => c p.2) Work.FTS.EllipticEst.Q0 :=
      hc.of_le (Nat.cast_le.mpr (by omega : i ≤ 2))
    have h2 : ContDiffOn ℝ i (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    show ContDiffOn ℝ i ((fun p : ℝ × ℝ => c p.2) / (fun p : ℝ × ℝ => Real.sin (2 * p.2)))
      Work.FTS.EllipticEst.Q0
    exact h1.div h2 (fun p hp' => ne_of_gt (sin_two_pos_quad hp'))
  have eT3 : Work.Spaces.mixed j i (fun z θ => c θ * Work.Spaces.pth X z θ) z θ
      = coefJetS (fun θ => c θ / Real.sin (2 * θ)) j i 1 X z θ := by
    have hcong : Set.EqOn (Function.uncurry (fun z θ => c θ * Work.Spaces.pth X z θ))
        (Function.uncurry (fun z θ => (c θ / Real.sin (2 * θ)) * Work.Spaces.Dth X z θ))
        Work.FTS.EllipticEst.Q0 := by
      intro p hp'
      obtain ⟨z', θ'⟩ := p
      have hs : Real.sin (2 * θ') ≠ 0 := ne_of_gt (sin_two_pos_quad hp')
      simp only [Function.uncurry, Work.Spaces.Dth, Work.Spaces.pth]
      field_simp
    have hstep := mixed_congr_eqOn hcong j i hp
    have hDthX : ContDiffOn ℝ (i + j) (Function.uncurry (Work.Spaces.Dth X))
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_Dth_of_succ
        Work.FTS.EllipticEst.isOpen_Q0 (n := 2) hX).of_le (Nat.cast_le.mpr (by omega : i + j ≤ 2))
    have hbase : Work.Spaces.mixed j i
        (fun z θ => (c θ / Real.sin (2 * θ)) * Work.Spaces.Dth X z θ) z θ
        = coefJetS (fun θ => c θ / Real.sin (2 * θ)) j i 0 (Work.Spaces.Dth X) z θ :=
      mixed_coef_mul_pt hDthX hcd z θ hp
    rw [show Work.Spaces.mixed j i (fun z θ => c θ * Work.Spaces.pth X z θ) z θ
        = Work.Spaces.mixed j i
            (fun z θ => c θ / Real.sin (2 * θ) * Work.Spaces.Dth X z θ) z θ from hstep,
      hbase, coefJetS, coefJetS]
    simp only [Nat.add_zero]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hDth1 : Work.Spaces.Dth X = Work.Spaces.DthIter 1 X := by
      rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
    rw [hDth1]
    show (i.choose k : ℝ) * (Work.Spaces.DthIter k (fun _ (θ'' : ℝ) => c θ'' / Real.sin (2 * θ'')) z θ
          * Work.Spaces.DzIter j (Work.Spaces.DthIter (i - k) (Work.Spaces.DthIter 1 X)) z θ)
        = (i.choose k : ℝ) * (Work.Spaces.DthIter k (fun _ (θ'' : ℝ) => c θ'' / Real.sin (2 * θ'')) z θ
          * Work.Spaces.DzIter j (Work.Spaces.DthIter (i - k + 1) X) z θ)
    rw [Work.Spaces.DthIter_add_right (i - k) 1 X]
  show Work.Spaces.mixed j i
      (fun z θ => a θ * X z θ + b θ * Work.Spaces.Dz X z θ + c θ * Work.Spaces.pth X z θ) z θ
    = EJet a b c j i X z θ
  rw [hadd1, hadd2, eT1, eT2, eT3, EJet]

/-- `tan` is `C²` on the open quadrant. -/
theorem contDiffOn_tan_quad : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.tan p.2)
    Work.FTS.EllipticEst.Q0 := by
  have hsin : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.sin p.2) Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_sin.comp contDiff_snd).contDiffOn
  have hcos : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.cos p.2) Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_cos.comp contDiff_snd).contDiffOn
  have h3 : ContDiffOn ℝ 2 ((fun p : ℝ × ℝ => Real.sin p.2) / (fun p : ℝ × ℝ => Real.cos p.2))
      Work.FTS.EllipticEst.Q0 :=
    hsin.div hcos (fun p hp' => ne_of_gt (cos_pos_quad hp'))
  convert h3 using 1
  funext p
  rw [Pi.div_apply, Real.tan_eq_sin_div_cos]

end Work.FTS_RegExport.RXT.Slots.JetCalc
