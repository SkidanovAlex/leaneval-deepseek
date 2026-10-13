import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_RegExport.RXT.SysAux.pertSlot_lip_approx
import Submission.Work.FTS_RegExport.RXT.Slots.v2_velPert
import Submission.Work.FTS_RegExport.RXT.velVanish2Aux
import Submission.Work.FTS_RegExport.RXT.Sys.GdotCore
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.Spaces.DzDthIterCommOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT0.SJC

open scoped Real Topology
open Set Filter
open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Regularity (pExp)
set_option autoImplicit false
variable {α Ce C₀ : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}

/-! ## Joint (in `τ`) Lipschitz approximation of the order-`≤ 2` jets of the three slots

`RXT.SysAux.pertSlot_lip_approx` gives the `τ`-Lipschitz modulus of the three slots
`Rop Φ̃`, `Vop Φ̃`, `Uop Φ̃ / sin 2θ` themselves.  Here we upgrade it to every mixed jet
`D_z^j D_θ^i`, `j + i ≤ 2`: the difference of the two `τ`-slices telescopes into the
difference slice `Δ = slice τ - slice τ'`, whose slot is controlled by the pair
`EllPkgGo` (`HkNorm α 4 (slot Δ) ≤ Ce · Xn α Δ`) together with the *trace-free weighted*
`ℋ⁴ → L^∞` trade-off `v2_hkMem_pointwise_min`
(`|mixed j i Q z θ| ≤ Ct · min z 1 · HkNorm α 4 Q`). -/

/-- `D_θ`-iterates only see the values on the open quadrant. -/
private theorem DthIter_congr_Q0_pt {u v : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → u z θ = v z θ) (i : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DthIter i u z θ = Work.Spaces.DthIter i v z θ := by
  induction i with
  | zero => intro z θ hz h1 h2; exact h z θ hz h1 h2
  | succ n ih =>
      intro z θ hz h1 h2
      have hEq : Set.EqOn (Function.uncurry (Work.Spaces.DthIter n u))
          (Function.uncurry (Work.Spaces.DthIter n v)) Work.FTS.EllipticEst.Q0 := by
        intro p hp
        obtain ⟨hz', h1', h2'⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
        exact ih p.1 p.2 hz' h1' h2'
      have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
        Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, h1, h2⟩
      have hpth : Work.Spaces.pth (Work.Spaces.DthIter n u) z θ
          = Work.Spaces.pth (Work.Spaces.DthIter n v) z θ :=
        Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEq hp
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth]
      rw [hpth]

/-- `mixed` only sees the values on the open quadrant. -/
private theorem mixed_congr_Q0_pt {u v : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → u z θ = v z θ) (j i : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed j i u z θ = Work.Spaces.mixed j i v z θ :=
  fun z θ hz h1 h2 =>
    Work.FTS.EllipticEst.SmoothOpen.DzIter_congr
      (F := Work.Spaces.DthIter i u) (G := Work.Spaces.DthIter i v)
      (DthIter_congr_Q0_pt h i) j z θ hz h1 h2

theorem slotJetLipschitzApprox
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    {gn : ℕ → Fam} {L S : ℝ} (hS : 0 < S)
    (hCl : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) S,
      Work.FTS.ClassC.ClassC (pExp α) (slice (gn n) τ))
    (hLip : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S,
      Work.FTS.Nonlin.Xn (pExp α) (slice (gn n) τ - slice (gn n) τ') ≤ L * |τ - τ'|) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S,
      ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (|Work.Spaces.mixed j i (Work.Construction.Rop (pExp α)
            (Work.Construction.PhiTil (pExp α) (slice (gn n) τ) (E (slice (gn n) τ)))) z θ
          - Work.Spaces.mixed j i (Work.Construction.Rop (pExp α)
            (Work.Construction.PhiTil (pExp α) (slice (gn n) τ') (E (slice (gn n) τ')))) z θ|
        ≤ K * |τ - τ'|) ∧
      (|Work.Spaces.mixed j i (Work.Construction.Vop
            (Work.Construction.PhiTil (pExp α) (slice (gn n) τ) (E (slice (gn n) τ)))) z θ
          - Work.Spaces.mixed j i (Work.Construction.Vop
            (Work.Construction.PhiTil (pExp α) (slice (gn n) τ') (E (slice (gn n) τ')))) z θ|
        ≤ K * |τ - τ'|) ∧
      (|Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop (pExp α)
            (Work.Construction.PhiTil (pExp α) (slice (gn n) τ) (E (slice (gn n) τ))) z θ
            / Real.sin (2 * θ)) z θ
          - Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop (pExp α)
            (Work.Construction.PhiTil (pExp α) (slice (gn n) τ') (E (slice (gn n) τ'))) z θ
            / Real.sin (2 * θ)) z θ| ≤ K * |τ - τ'|) := by
  have hαG : 0 < pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  obtain ⟨Ct, hCt0, hCt⟩ := Work.FTS_RegExport.RXT.v2_hkMem_pointwise_min hαG hαG1
  refine ⟨Ct * max Ce 0 * max L 0,
    mul_nonneg (mul_nonneg hCt0 (le_max_right _ _)) (le_max_right _ _), ?_⟩
  intro n τ hτ τ' hτ' j i hji z θ hz hθ hθ2
  have hCu : Work.FTS.ClassC.ClassC (pExp α) (slice (gn n) τ) := hCl n τ hτ
  have hCv : Work.FTS.ClassC.ClassC (pExp α) (slice (gn n) τ') := hCl n τ' hτ'
  set Δ : Fn := fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ with hΔ
  have hCΔ : Work.FTS.ClassC.ClassC (pExp α) Δ :=
    Work.FTS.StrongEps.EComparison.classC_sub hCu hCv
  set Xu : Fn := Work.Construction.PhiTil (pExp α)
    (slice (gn n) τ) (E (slice (gn n) τ)) with hXu
  set Xv : Fn := Work.Construction.PhiTil (pExp α)
    (slice (gn n) τ') (E (slice (gn n) τ')) with hXv
  set Xd : Fn := Work.Construction.PhiTil (pExp α) Δ (E Δ) with hXd
  obtain ⟨hGo, _hK6⟩ := hEll Δ hCΔ
  obtain ⟨hGu, _⟩ := hEll (slice (gn n) τ) hCu
  obtain ⟨hGv, _⟩ := hEll (slice (gn n) τ') hCv
  have hSXd : Work.FTS.EllipticEst.SmoothOpen Xd :=
    Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hαG hGo
  have hSXv : Work.FTS.EllipticEst.SmoothOpen Xv :=
    Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hαG hGv
  have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn (pExp α) Δ :=
    Work.Spaces.HkNorm_nonneg _ _ _
  have hXnΔ : Work.FTS.Nonlin.Xn (pExp α) Δ ≤ max L 0 * |τ - τ'| := by
    refine le_trans (hLip n τ hτ τ' hτ') ?_
    exact mul_le_mul_of_nonneg_right (le_max_left L 0) (abs_nonneg _)
  -- ## the pointwise telescoping of the residues
  have hpot : ∀ z' θ' : ℝ, 0 < z' → Xu z' θ' = Xd z' θ' + Xv z' θ' := by
    intro z' θ' hz'
    have hL : Work.Construction.L12 Δ z'
        = Work.Construction.L12 (slice (gn n) τ) z'
          - Work.Construction.L12 (slice (gn n) τ') z' :=
      Work.FTS.StrongEps.EComparison.L12_sub_HkMem hCu.reg hCv.reg
        (Work.FTS.ClassC.classC_hkMem_four hCu) (Work.FTS.ClassC.classC_hkMem_four hCv)
        z' hz'.le
    have hE' : E Δ z' θ'
        = E (slice (gn n) τ) z' θ'
          - E (slice (gn n) τ') z' θ' := by
      have h2 : E Δ = E (slice (gn n) τ)
          - E (slice (gn n) τ') := by
        rw [hΔ]
        exact map_sub E _ _
      exact congrFun (congrFun h2 z') θ'
    rw [hXu, hXd, hXv]
    unfold Work.Construction.PhiTil Work.Construction.Theta
    rw [hL, hE']
    ring
  -- ## the pointwise additivity of the three slots on `Q0`
  have hR_id : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Work.Construction.Rop (pExp α) Xu z' θ'
        = Work.Construction.Rop (pExp α) Xd z' θ'
          + Work.Construction.Rop (pExp α) Xv z' θ' := by
    intro z' θ' hz' h1 h2
    calc Work.Construction.Rop (pExp α) Xu z' θ'
        = Work.Construction.Rop (pExp α) (fun z θ => Xd z θ + Xv z θ) z' θ' :=
          Work.FTS.GalFields.RHS.Sharp.Rop_congr_Q0
            (f := Xu) (g := fun z θ => Xd z θ + Xv z θ)
            (fun z θ hz'' _ _ => hpot z θ hz'') z' θ' hz' h1 h2
      _ = Work.Construction.Rop (pExp α) Xd z' θ'
            + Work.Construction.Rop (pExp α) Xv z' θ' :=
          Work.FTS.GalFields.RHS.Sharp.Rop_add_Q0 hSXd hSXv z' θ' hz' h1 h2
  have hV_id : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Work.Construction.Vop Xu z' θ'
        = Work.Construction.Vop Xd z' θ' + Work.Construction.Vop Xv z' θ' := by
    intro z' θ' hz' h1 h2
    calc Work.Construction.Vop Xu z' θ'
        = Work.Construction.Vop (fun z θ => Xd z θ + Xv z θ) z' θ' :=
          Work.FTS.GalFields.RHS.Sharp.Vop_congr_Q0
            (f := Xu) (g := fun z θ => Xd z θ + Xv z θ)
            (fun z θ hz'' _ _ => hpot z θ hz'') z' θ' hz' h1 h2
      _ = Work.Construction.Vop Xd z' θ' + Work.Construction.Vop Xv z' θ' :=
          Work.FTS.GalFields.RHS.Sharp.Vop_add_Q0 hSXd hSXv z' θ' hz' h1 h2
  have hU_id : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Work.Construction.Uop (pExp α) Xu z' θ' / Real.sin (2 * θ')
        = Work.Construction.Uop (pExp α) Xd z' θ' / Real.sin (2 * θ')
          + Work.Construction.Uop (pExp α) Xv z' θ' / Real.sin (2 * θ') := by
    intro z' θ' hz' h1 h2
    have hc : Work.Construction.Uop (pExp α) Xu z' θ'
        = Work.Construction.Uop (pExp α) (fun z θ => Xd z θ + Xv z θ) z' θ' :=
      Work.FTS.GalFields.RHS.Sharp.Uop_congr_Q0
        (f := Xu) (g := fun z θ => Xd z θ + Xv z θ)
        (fun z θ hz'' _ _ => hpot z θ hz'') z' θ' hz' h1 h2
    have ha := Work.FTS.GalFields.RHS.Sharp.Uop_add_Q0 (α := pExp α) hSXd hSXv z' θ' hz' h1 h2
    rw [hc, ha]
    ring
  -- ## the abstract slot bound: the trade-off bound on the difference slot
  have hji' : i + j ≤ 2 := by omega
  have key : ∀ (Sl : Fn → Fn) (P Q : Fn),
      Work.FTS.EllipticEst.SmoothOpen (Sl Q) → Work.FTS.EllipticEst.SmoothOpen (Sl P) →
      (∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
        Sl Xu z' θ' = Sl Q z' θ' + Sl P z' θ') →
      ContDiffOn ℝ 4 (Function.uncurry (Sl Q)) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem (pExp α) 4 (Sl Q) →
      Work.Spaces.HkNorm (pExp α) 4 (Sl Q) ≤ max Ce 0 * Work.FTS.Nonlin.Xn (pExp α) Δ →
      |Work.Spaces.mixed j i (Sl Xu) z θ - Work.Spaces.mixed j i (Sl P) z θ|
        ≤ Ct * max Ce 0 * max L 0 * |τ - τ'| := by
    intro Sl P Q hSQ hSP hsum hcd hmem hnorm
    have hsplit : Work.Spaces.mixed j i (Sl Xu) z θ
        = Work.Spaces.mixed j i (Sl Q) z θ + Work.Spaces.mixed j i (Sl P) z θ := by
      rw [mixed_congr_Q0_pt (u := Sl Xu) (v := fun z θ => Sl Q z θ + Sl P z θ)
        (fun z θ hz' h1 h2 => hsum z θ hz' h1 h2) j i z θ hz hθ hθ2]
      exact Work.FTS.EllipticEst.SmoothOpen.mixed_add hSQ hSP j i z θ hz hθ hθ2
    have hpt := hCt (Sl Q) hcd hmem j i hji' z θ hz hθ hθ2
    have hN0 : 0 ≤ Work.Spaces.HkNorm (pExp α) 4 (Sl Q) :=
      Work.Spaces.HkNorm_nonneg _ _ _
    have hstep : Ct * min z 1 * Work.Spaces.HkNorm (pExp α) 4 (Sl Q)
        ≤ Ct * (max Ce 0 * (max L 0 * |τ - τ'|)) := by
      have h1 : Ct * min z 1 ≤ Ct * 1 :=
        mul_le_mul_of_nonneg_left (min_le_right z 1) hCt0
      calc Ct * min z 1 * Work.Spaces.HkNorm (pExp α) 4 (Sl Q)
          ≤ (Ct * 1) * Work.Spaces.HkNorm (pExp α) 4 (Sl Q) :=
            mul_le_mul_of_nonneg_right h1 hN0
        _ ≤ Ct * (max Ce 0 * Work.FTS.Nonlin.Xn (pExp α) Δ) := by
            rw [mul_one]
            exact mul_le_mul_of_nonneg_left hnorm hCt0
        _ ≤ Ct * (max Ce 0 * (max L 0 * |τ - τ'|)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hXnΔ (le_max_right Ce 0)) hCt0
    calc |Work.Spaces.mixed j i (Sl Xu) z θ - Work.Spaces.mixed j i (Sl P) z θ|
        = |Work.Spaces.mixed j i (Sl Q) z θ| := by rw [hsplit, add_sub_cancel_right]
      _ ≤ Ct * min z 1 * Work.Spaces.HkNorm (pExp α) 4 (Sl Q) := hpt
      _ ≤ Ct * (max Ce 0 * (max L 0 * |τ - τ'|)) := hstep
      _ = Ct * max Ce 0 * max L 0 * |τ - τ'| := by ring
  -- ## the bound of the three difference slots
  have hRb : |Work.Spaces.mixed j i (Work.Construction.Rop (pExp α) Xu) z θ
      - Work.Spaces.mixed j i (Work.Construction.Rop (pExp α) Xv) z θ|
      ≤ Ct * max Ce 0 * max L 0 * |τ - τ'| :=
    key (Work.Construction.Rop (pExp α)) Xv Xd hGo.R.1.1 hGv.R.1.1 hR_id
      (hGo.R.1.1.forall 4) hGo.R.1.2
      (le_trans hGo.R.2 (mul_le_mul_of_nonneg_right (le_max_left Ce 0) hXn0))
  have hVb : |Work.Spaces.mixed j i (Work.Construction.Vop Xu) z θ
      - Work.Spaces.mixed j i (Work.Construction.Vop Xv) z θ|
      ≤ Ct * max Ce 0 * max L 0 * |τ - τ'| :=
    key Work.Construction.Vop Xv Xd hGo.V.1.1 hGv.V.1.1 hV_id
      (hGo.V.1.1.forall 4) hGo.V.1.2
      (le_trans hGo.V.2 (mul_le_mul_of_nonneg_right (le_max_left Ce 0) hXn0))
  have hUb : |Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop (pExp α) Xu z θ
        / Real.sin (2 * θ)) z θ
      - Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop (pExp α) Xv z θ
        / Real.sin (2 * θ)) z θ|
      ≤ Ct * max Ce 0 * max L 0 * |τ - τ'| :=
    key (fun X => fun z θ => Work.Construction.Uop (pExp α) X z θ / Real.sin (2 * θ))
      Xv Xd
      (by simpa only [Work.Construction.s2] using hGo.U.1.1)
      (by simpa only [Work.Construction.s2] using hGv.U.1.1)
      hU_id
      (hGo.U.1.1.forall 4) hGo.U.1.2
      (le_trans hGo.U.2 (mul_le_mul_of_nonneg_right (le_max_left Ce 0) hXn0))
  refine ⟨?_, ?_, ?_⟩
  · calc |Work.Spaces.mixed j i (Work.Construction.Rop (pExp α)
          (Work.Construction.PhiTil (pExp α) (slice (gn n) τ) (E (slice (gn n) τ)))) z θ
        - Work.Spaces.mixed j i (Work.Construction.Rop (pExp α)
          (Work.Construction.PhiTil (pExp α) (slice (gn n) τ') (E (slice (gn n) τ')))) z θ|
        = |Work.Spaces.mixed j i (Work.Construction.Rop (pExp α) Xu) z θ
            - Work.Spaces.mixed j i (Work.Construction.Rop (pExp α) Xv) z θ| := by
          rw [hXu, hXv]
      _ ≤ Ct * max Ce 0 * max L 0 * |τ - τ'| := hRb
  · calc |Work.Spaces.mixed j i (Work.Construction.Vop
          (Work.Construction.PhiTil (pExp α) (slice (gn n) τ) (E (slice (gn n) τ)))) z θ
        - Work.Spaces.mixed j i (Work.Construction.Vop
          (Work.Construction.PhiTil (pExp α) (slice (gn n) τ') (E (slice (gn n) τ')))) z θ|
        = |Work.Spaces.mixed j i (Work.Construction.Vop Xu) z θ
            - Work.Spaces.mixed j i (Work.Construction.Vop Xv) z θ| := by
          rw [hXu, hXv]
      _ ≤ Ct * max Ce 0 * max L 0 * |τ - τ'| := hVb
  · calc |Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop (pExp α)
          (Work.Construction.PhiTil (pExp α) (slice (gn n) τ) (E (slice (gn n) τ))) z θ
          / Real.sin (2 * θ)) z θ
        - Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop (pExp α)
          (Work.Construction.PhiTil (pExp α) (slice (gn n) τ') (E (slice (gn n) τ'))) z θ
          / Real.sin (2 * θ)) z θ|
        = |Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop (pExp α) Xu z θ
            / Real.sin (2 * θ)) z θ
          - Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop (pExp α) Xv z θ
            / Real.sin (2 * θ)) z θ| := by
          rw [hXu, hXv]
      _ ≤ Ct * max Ce 0 * max L 0 * |τ - τ'| := hUb

end Work.FTS_RegExport.RXT0.SJC
