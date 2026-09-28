import Mathlib
import Submission.Work.Serre.CellStep.Geom
import Submission.Work.Serre.cellImgQuarterSphereHomeo
import Submission.Work.RatHurewicz.ExcisionSetup
import Submission.Work.Serre.compressRel_slabV
import Submission.Work.Serre.SPC.OneCellX

set_option synthInstance.maxHeartbeats 400000


/-!
# The compression property of the shell pair of an attached cell

For the cell step of the Serre computation one needs the compression property
(`Work.RatHurewicz.CompressRel`) of the pair

  `(χᵢ({ρ < ‖x‖ < R}), χᵢ({ρ < ‖x‖ < R}) ∩ χᵢ({‖x‖ = 1/4}))`

inside the `i`-th attached cell of `attachCells n Γ ι f`, in **every** dimension `d`
(the statement carries no bound on `d`).

The pair is a homotopy-theoretic sphere pair: the open shell `{ρ < ‖x‖ < R}` deformation retracts
radially onto the concentric sphere `{‖x‖ = 1/4}` (because `ρ < 1/4 < R`), and the characteristic
map `χᵢ` is a homeomorphism on the open model cell.  So the compression property follows from the
model case `Work.Serre.CellShellCompress.compressRel_cellShellSet` (an explicit radial strong
deformation retraction, `Work.Serre.compressRel_of_deformation`) transported along the
homeomorphism of pairs given by the characteristic map
(`Work.Serre.compressRel_of_homeo`).
-/

open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

open Work.RatHurewicz

/-! ## The radial deformation of the model shell -/

namespace CellShellCompress

variable {n : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type} {ρ R : ℝ}

/-- The radius-`1/4` sphere of the model cell lies in the open model cell. -/
theorem quarterSet_subset_cellInner (n : ℕ) : quarterSet n ⊆ cellInner n := by
  intro z hz
  rw [cellInner]
  show ‖(z : CellVec n)‖ < 1
  rw [show ‖(z : CellVec n)‖ = 1 / 4 from hz]
  norm_num

/-- The radial parameter of the deformation of the model shell: at time `t` the radius `‖x‖` is
interpolated towards `1/4`, so that the point moves radially to the sphere of radius `1/4`. -/
def shellLam (x : ↥(cellShellSet n ρ R)) (t : unitInterval) : ℝ :=
  ((1 - (t : ℝ)) * ‖((x : cellDisk n) : CellVec n)‖ + (t : ℝ) * (1 / 4))
    / ‖((x : cellDisk n) : CellVec n)‖

/-- Points of the shell have positive norm. -/
theorem norm_pos_of_mem_shell (hρ : 0 < ρ) (x : ↥(cellShellSet n ρ R)) :
    0 < ‖((x : cellDisk n) : CellVec n)‖ := by
  have h := (mem_cellShellSet.mp x.2).1
  linarith

theorem shellLam_nonneg (hρ : 0 < ρ) (x : ↥(cellShellSet n ρ R)) (t : unitInterval) :
    0 ≤ shellLam x t := by
  have h := norm_pos_of_mem_shell hρ x
  rw [shellLam]
  apply div_nonneg
  · have h1 : 0 ≤ (1 - (t : ℝ)) * ‖((x : cellDisk n) : CellVec n)‖ :=
      mul_nonneg (by linarith [t.2.2]) (le_of_lt h)
    have h2 : 0 ≤ (t : ℝ) * (1 / 4) := mul_nonneg t.2.1 (by norm_num)
    linarith
  · exact le_of_lt h

theorem shellLam_mul (hρ : 0 < ρ) (x : ↥(cellShellSet n ρ R)) (t : unitInterval) :
    shellLam x t * ‖((x : cellDisk n) : CellVec n)‖
      = (1 - (t : ℝ)) * ‖((x : cellDisk n) : CellVec n)‖ + (t : ℝ) * (1 / 4) := by
  rw [shellLam]
  exact div_mul_cancel₀ _ (ne_of_gt (norm_pos_of_mem_shell hρ x))

theorem shellLam_zero (hρ : 0 < ρ) (x : ↥(cellShellSet n ρ R)) : shellLam x 0 = 1 := by
  have h := ne_of_gt (norm_pos_of_mem_shell hρ x)
  simp [shellLam, h]

theorem shellLam_one (hρ : 0 < ρ) (x : ↥(cellShellSet n ρ R)) :
    shellLam x 1 = (1 / 4) / ‖((x : cellDisk n) : CellVec n)‖ := by
  rw [shellLam]
  norm_num

theorem shellLam_eq_one_of_mem (hρ : 0 < ρ) (x : ↥(cellShellSet n ρ R))
    (hx : (x : cellDisk n) ∈ quarterSet n) (t : unitInterval) : shellLam x t = 1 := by
  have hN : ‖((x : cellDisk n) : CellVec n)‖ = 1 / 4 := hx
  rw [shellLam, hN]
  field_simp
  ring

/-- The norm of the deformed point. -/
theorem norm_shellLam_smul (hρ : 0 < ρ) (x : ↥(cellShellSet n ρ R)) (t : unitInterval) :
    ‖shellLam x t • ((x : cellDisk n) : CellVec n)‖
      = (1 - (t : ℝ)) * ‖((x : cellDisk n) : CellVec n)‖ + (t : ℝ) * (1 / 4) := by
  rw [norm_smul, Real.norm_of_nonneg (shellLam_nonneg hρ x t), shellLam_mul hρ x t]

/-- The deformed point stays in the closed model cell. -/
theorem shellPt_mem_ball (hρ : 0 < ρ) (hR1 : R ≤ 1) (x : ↥(cellShellSet n ρ R))
    (t : unitInterval) :
    shellLam x t • ((x : cellDisk n) : CellVec n) ∈ Metric.closedBall (0 : CellVec n) 1 := by
  have hN1 : ‖((x : cellDisk n) : CellVec n)‖ ≤ 1 :=
    le_trans (le_of_lt (mem_cellShellSet.mp x.2).2) hR1
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_shellLam_smul hρ x t]
  have h1 : (1 - (t : ℝ)) * ‖((x : cellDisk n) : CellVec n)‖ ≤ (1 - (t : ℝ)) * 1 :=
    mul_le_mul_of_nonneg_left hN1 (by linarith [t.2.2])
  have h2 : (t : ℝ) * (1 / 4) ≤ (t : ℝ) * 1 :=
    mul_le_mul_of_nonneg_left (by norm_num) t.2.1
  linarith

/-- The deformed point stays in the model shell. -/
theorem shellLam_smul_mem_shell (hρ : 0 < ρ) (hρ4 : ρ < 1 / 4) (h4R : 1 / 4 < R)
    (x : ↥(cellShellSet n ρ R)) (t : unitInterval) :
    ρ < ‖shellLam x t • ((x : cellDisk n) : CellVec n)‖ ∧
      ‖shellLam x t • ((x : cellDisk n) : CellVec n)‖ < R := by
  have hN := norm_pos_of_mem_shell hρ x
  have hxl := (mem_cellShellSet.mp x.2).1
  have hxr := (mem_cellShellSet.mp x.2).2
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  rw [norm_shellLam_smul hρ x t]
  constructor
  · rcases eq_or_lt_of_le ht1 with h | h
    · rw [h]
      norm_num
      exact hρ4
    · have hA : (1 - (t : ℝ)) * ρ < (1 - (t : ℝ)) * ‖((x : cellDisk n) : CellVec n)‖ :=
        mul_lt_mul_of_pos_left hxl (by linarith)
      have hB : (t : ℝ) * ρ ≤ (t : ℝ) * (1 / 4) :=
        mul_le_mul_of_nonneg_left (le_of_lt hρ4) ht0
      nlinarith [hA, hB]
  · rcases eq_or_lt_of_le ht0 with h | h
    · rw [← h]
      norm_num
      exact hxr
    · have hA : (1 - (t : ℝ)) * ‖((x : cellDisk n) : CellVec n)‖ ≤ (1 - (t : ℝ)) * R :=
        mul_le_mul_of_nonneg_left (le_of_lt hxr) (by linarith [ht1])
      have hB : (t : ℝ) * (1 / 4) < (t : ℝ) * R := mul_lt_mul_of_pos_left h4R h
      nlinarith [hA, hB]

/-- The deformed point of the shell, as an element of the closed model cell. -/
def shellPt (hρ : 0 < ρ) (hR1 : R ≤ 1) (x : ↥(cellShellSet n ρ R)) (t : unitInterval) :
    cellDisk n :=
  ⟨shellLam x t • ((x : cellDisk n) : CellVec n), shellPt_mem_ball hρ hR1 x t⟩

/-- The deformed point of the shell remains in the shell. -/
theorem shellPt_mem (hρ : 0 < ρ) (hR1 : R ≤ 1) (hρ4 : ρ < 1 / 4) (h4R : 1 / 4 < R)
    (x : ↥(cellShellSet n ρ R)) (t : unitInterval) :
    shellPt hρ hR1 x t ∈ cellShellSet n ρ R :=
  shellLam_smul_mem_shell hρ hρ4 h4R x t

theorem shellPt_zero (hρ : 0 < ρ) (hR1 : R ≤ 1) (x : ↥(cellShellSet n ρ R)) :
    shellPt hρ hR1 x 0 = (x : cellDisk n) := by
  refine Subtype.ext ?_
  show shellLam x 0 • ((x : cellDisk n) : CellVec n) = ((x : cellDisk n) : CellVec n)
  rw [shellLam_zero hρ x, one_smul]

theorem shellPt_one_mem (hρ : 0 < ρ) (hR1 : R ≤ 1) (x : ↥(cellShellSet n ρ R)) :
    (shellPt hρ hR1 x 1 : cellDisk n) ∈ quarterSet n := by
  change ‖shellLam x 1 • ((x : cellDisk n) : CellVec n)‖ = 1 / 4
  rw [norm_smul, Real.norm_of_nonneg (shellLam_nonneg hρ x 1), shellLam_one hρ x,
    div_mul_cancel₀ _ (ne_of_gt (norm_pos_of_mem_shell hρ x))]

theorem shellPt_fixed (hρ : 0 < ρ) (hR1 : R ≤ 1) (x : ↥(cellShellSet n ρ R))
    (hx : (x : cellDisk n) ∈ quarterSet n) (t : unitInterval) :
    shellPt hρ hR1 x t = (x : cellDisk n) := by
  refine Subtype.ext ?_
  show shellLam x t • ((x : cellDisk n) : CellVec n) = ((x : cellDisk n) : CellVec n)
  rw [shellLam_eq_one_of_mem hρ x hx t, one_smul]

theorem continuous_shellLam (hρ : 0 < ρ) :
    Continuous fun z : ↥(cellShellSet n ρ R) × unitInterval => shellLam z.1 z.2 := by
  have hv : Continuous fun z : ↥(cellShellSet n ρ R) × unitInterval =>
      ((z.1 : cellDisk n) : CellVec n) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)
  have hn : Continuous fun z : ↥(cellShellSet n ρ R) × unitInterval =>
      ‖((z.1 : cellDisk n) : CellVec n)‖ := continuous_norm.comp hv
  have hnum : Continuous fun z : ↥(cellShellSet n ρ R) × unitInterval =>
      (1 - (z.2 : ℝ)) * ‖((z.1 : cellDisk n) : CellVec n)‖ + (z.2 : ℝ) * (1 / 4) :=
    ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul hn).add
      ((continuous_subtype_val.comp continuous_snd).mul continuous_const)
  exact (Continuous.div₀ hnum hn (fun z => ne_of_gt (norm_pos_of_mem_shell hρ z.1)))

theorem continuous_shellPt (hρ : 0 < ρ) (hR1 : R ≤ 1) :
    Continuous fun z : ↥(cellShellSet n ρ R) × unitInterval => shellPt hρ hR1 z.1 z.2 := by
  have hv : Continuous fun z : ↥(cellShellSet n ρ R) × unitInterval =>
      ((z.1 : cellDisk n) : CellVec n) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)
  have hprod : Continuous fun z : ↥(cellShellSet n ρ R) × unitInterval =>
      shellLam z.1 z.2 • ((z.1 : cellDisk n) : CellVec n) :=
    (continuous_shellLam hρ).smul hv
  exact Continuous.subtype_mk hprod _

/-- The radial strong deformation retraction of the model shell onto the sphere of radius `1/4`. -/
def shellHom (hρ : 0 < ρ) (hR1 : R ≤ 1) (hρ4 : ρ < 1 / 4) (h4R : 1 / 4 < R) :
    C(↥(cellShellSet n ρ R) × unitInterval, ↥(cellShellSet n ρ R)) where
  toFun z := ⟨shellPt hρ hR1 z.1 z.2, shellPt_mem hρ hR1 hρ4 h4R z.1 z.2⟩
  continuous_toFun := Continuous.subtype_mk (continuous_shellPt hρ hR1) _

/-- **The model shell compresses onto the sphere of radius `1/4`, in every dimension.** -/
theorem compressRel_cellShellSet (hρ : 0 < ρ) (hρ4 : ρ < 1 / 4) (h4R : 1 / 4 < R)
    (hR1 : R ≤ 1) (d : ℕ) :
    CompressRel ↥(cellShellSet n ρ R)
      {x : ↥(cellShellSet n ρ R) | (x : cellDisk n) ∈ quarterSet n} d :=
  compressRel_of_deformation (shellHom hρ hR1 hρ4 h4R)
    (fun x => Subtype.ext (shellPt_zero hρ hR1 x))
    (fun x => shellPt_one_mem hρ hR1 x)
    (fun x hx t => Subtype.ext (shellPt_fixed hρ hR1 x hx t)) d

/-! ## The characteristic map is a homeomorphism of the shell pair -/

/-- **The characteristic map of the `i`-th cell restricts to a homeomorphism of the model shell
onto its image**, with the pointwise description `e x = cellMap i x`. -/
theorem exists_shellImgHomeo (f : ι → C(cellSphere n, Γ)) (i : ι)
    (hS : cellShellSet n ρ R ⊆ cellInner n) :
    ∃ e : ↥(cellShellSet n ρ R) ≃ₜ ↥(cellImg f i (cellShellSet n ρ R)),
      ∀ x, (e x : attachCells n Γ ι f) = cellMap n Γ ι f i (x : cellDisk n) := by
  classical
  have himg : cellImg f i (cellShellSet n ρ R) ⊆ cellInterior n Γ ι f i :=
    fun z ⟨x, hx, hxz⟩ => ⟨x, hS hx, hxz⟩
  obtain ⟨sec, hsec⟩ := cellInterior_section (f := f) i
  have hmem : ∀ z : ↥(cellImg f i (cellShellSet n ρ R)),
      ((sec ⟨z.1, himg z.2⟩ : ↥(cellInner n)) : cellDisk n) ∈ cellShellSet n ρ R := by
    intro z
    obtain ⟨x, hxS, hxz⟩ := z.2
    have h2 : cellMap n Γ ι f i ((sec ⟨z.1, himg z.2⟩ : ↥(cellInner n)) : cellDisk n)
        = cellMap n Γ ι f i ((⟨x, hS hxS⟩ : ↥(cellInner n)) : cellDisk n) := by
      rw [hsec ⟨z.1, himg z.2⟩]
      exact hxz.symm
    have h3 := cellMap_injective_cellInner (f := f) i h2
    exact (congrArg (fun w : ↥(cellInner n) => ((w : cellDisk n))) h3) ▸ hxS
  refine ⟨{ toFun := fun x => ⟨cellMap n Γ ι f i (x : cellDisk n), ⟨(x : cellDisk n), x.2, rfl⟩⟩
            invFun := fun z =>
              ⟨((sec ⟨z.1, himg z.2⟩ : ↥(cellInner n)) : cellDisk n), hmem z⟩
            left_inv := ?_
            right_inv := ?_
            continuous_toFun := Continuous.subtype_mk
              ((cellMap n Γ ι f i).continuous.comp continuous_subtype_val) _
            continuous_invFun := Continuous.subtype_mk
              ((continuous_subtype_val.comp sec.continuous).comp
                (Continuous.subtype_mk continuous_subtype_val _)) _ }, ?_⟩
  · intro x
    apply Subtype.ext
    have h2 : cellMap n Γ ι f i
          ((sec ⟨cellMap n Γ ι f i (x : cellDisk n),
              himg ⟨(x : cellDisk n), x.2, rfl⟩⟩ : ↥(cellInner n)) : cellDisk n)
        = cellMap n Γ ι f i ((⟨(x : cellDisk n), hS x.2⟩ : ↥(cellInner n)) : cellDisk n) := by
      rw [hsec]
    exact congrArg (fun w : ↥(cellInner n) => ((w : cellDisk n)))
      (cellMap_injective_cellInner (f := f) i h2)
  · intro z
    apply Subtype.ext
    exact hsec ⟨z.1, himg z.2⟩
  · intro x
    rfl

end CellShellCompress

/-! ## The target -/

theorem compressRel_cellShellImg (n : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Γ)) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hR1 : R ≤ 1) (hρ4 : ρ < 1 / 4) (h4R : 1 / 4 < R) (i : ι) (d : ℕ) :
    Work.RatHurewicz.CompressRel ↥(Work.Serre.cellImg (Γ := Γ) (ι := ι) f i
        (Work.Serre.cellShellSet n ρ R))
      {x | (x : Work.RatHurewicz.attachCells n Γ ι f) ∈
        Work.Serre.cellImg (Γ := Γ) (ι := ι) f i (Work.Serre.quarterSet n)} d := by
  classical
  have hS : cellShellSet n ρ R ⊆ cellInner n := cellShellSet_subset_cellInner hR1
  obtain ⟨e, he⟩ := CellShellCompress.exists_shellImgHomeo (ρ := ρ) (R := R) (f := f) i hS
  have he' : ∀ y : ↥(cellImg f i (cellShellSet n ρ R)),
      (y : attachCells n Γ ι f)
        = cellMap n Γ ι f i ((e.symm y : ↥(cellShellSet n ρ R)) : cellDisk n) := by
    intro y
    have h := he (e.symm y)
    rwa [e.apply_symm_apply] at h
  refine compressRel_of_homeo e.symm
    (A := {x : ↥(cellImg f i (cellShellSet n ρ R)) |
      (x : attachCells n Γ ι f) ∈ cellImg f i (quarterSet n)})
    (A' := {x : ↥(cellShellSet n ρ R) | (x : cellDisk n) ∈ quarterSet n}) ?_ d
    (CellShellCompress.compressRel_cellShellSet (n := n) (ρ := ρ) (R := R) hρ hρ4 h4R hR1 d)
  intro y
  have hy := he' y
  show (y : attachCells n Γ ι f) ∈ cellImg f i (quarterSet n) ↔
    ((e.symm y : ↥(cellShellSet n ρ R)) : cellDisk n) ∈ quarterSet n
  rw [hy]
  constructor
  · intro hq
    obtain ⟨z, hz, hzy⟩ := (mem_cellImg f).mp hq
    have hzi : z ∈ cellInner n := CellShellCompress.quarterSet_subset_cellInner n hz
    have hyi : ((e.symm y : ↥(cellShellSet n ρ R)) : cellDisk n) ∈ cellInner n :=
      hS (e.symm y).2
    have hzy' : cellMap n Γ ι f i ((⟨z, hzi⟩ : ↥(cellInner n)) : cellDisk n)
        = cellMap n Γ ι f i
            ((⟨((e.symm y : ↥(cellShellSet n ρ R)) : cellDisk n), hyi⟩ :
              ↥(cellInner n)) : cellDisk n) := hzy
    have h3 := cellMap_injective_cellInner (f := f) i hzy'
    have h4 : z = ((e.symm y : ↥(cellShellSet n ρ R)) : cellDisk n) :=
      congrArg (fun w : ↥(cellInner n) => ((w : cellDisk n))) h3
    exact h4 ▸ hz
  · intro hq
    exact (mem_cellImg f).mpr ⟨((e.symm y : ↥(cellShellSet n ρ R)) : cellDisk n), hq, rfl⟩

end

end Work.Serre
