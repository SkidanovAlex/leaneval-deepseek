import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongEps.EpsZero.Nstar_zero_classC
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Filter Set

namespace Work.FTS_EllLimOK

set_option autoImplicit false

open Work.FTS.Galerkin (Fn)

/-! ## 0. Abstract linear algebra -/

theorem exists_section_extend {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (C : Submodule K V) (G : Submodule K (V × W))
    (E : V →ₗ[K] W) (hC : ∀ v ∈ C, (v, E v) ∈ G) :
    ∃ E' : V →ₗ[K] W, (∀ v ∈ C, E' v = E v) ∧
      ∀ v ∈ G.map (LinearMap.fst K V W), (v, E' v) ∈ G := by
  set L : Submodule K V := G.map (LinearMap.fst K V W) with hL
  -- the projection `G → L` and a linear right inverse
  let pr : G →ₗ[K] L := ((LinearMap.fst K V W).comp G.subtype).codRestrict L
    (fun x => ⟨x, x.2, rfl⟩)
  have hπ : LinearMap.range pr = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨v, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨s₀, hs₀⟩ := LinearMap.exists_rightInverse_of_surjective pr hπ
  have hs₀v : ∀ v : L, ((s₀ v : G) : V × W).1 = (v : V) := by
    intro v
    have := congrArg Subtype.val (LinearMap.congr_fun hs₀ v)
    exact this
  -- the fibre over `0`
  let F : Submodule K W := G.comap (LinearMap.inr K V W)
  let C' : Submodule K L := C.comap L.subtype
  let d : L →ₗ[K] W := (LinearMap.snd K V W).comp (G.subtype.comp s₀) - E.comp L.subtype
  have hdF : ∀ c : C', d (C'.subtype c) ∈ F := by
    intro c
    show (0, d c) ∈ G
    have h1 : ((s₀ c : G) : V × W) ∈ G := (s₀ c).2
    have h2 : (((c : L) : V), E ((c : L) : V)) ∈ G := hC _ c.2
    have h3 := G.sub_mem h1 h2
    have hfst := hs₀v (c : L)
    convert h3 using 1
    ext
    · simp [hfst]
    · simp [d]
  let δ : C' →ₗ[K] F := (d.comp C'.subtype).codRestrict F hdF
  obtain ⟨δ', hδ'⟩ := LinearMap.exists_extend δ
  let E₁ : L →ₗ[K] W :=
    (LinearMap.snd K V W).comp (G.subtype.comp s₀) - F.subtype.comp δ'
  obtain ⟨E', hE'⟩ := LinearMap.exists_extend E₁
  have hE'v : ∀ v : L, E' v = E₁ v := fun v => LinearMap.congr_fun hE' v
  refine ⟨E', ?_, ?_⟩
  · intro v hv
    have hvL : v ∈ L := Submodule.mem_map.mpr ⟨(v, E v), hC v hv, rfl⟩
    have := hE'v ⟨v, hvL⟩
    have hδc : (δ' ⟨v, hvL⟩ : W) = d ⟨v, hvL⟩ := by
      have := congrArg Subtype.val (LinearMap.congr_fun hδ' (⟨⟨v, hvL⟩, hv⟩ : C'))
      exact this
    simp only [E₁, LinearMap.sub_apply, LinearMap.comp_apply] at this
    rw [this]
    simp only [Submodule.subtype_apply] at hδc ⊢
    rw [hδc]
    simp [d]
  · intro v hv
    have := hE'v ⟨v, hv⟩
    rw [this]
    have h1 : ((s₀ ⟨v, hv⟩ : G) : V × W) ∈ G := (s₀ ⟨v, hv⟩).2
    have h2 : ((0 : V), ((δ' ⟨v, hv⟩ : F) : W)) ∈ G := (δ' ⟨v, hv⟩).2
    have h3 := G.sub_mem h1 h2
    have hfst := hs₀v ⟨v, hv⟩
    convert h3 using 1
    ext
    · simp [hfst]
    · simp [E₁]

/-! ## 1. Elementary facts -/

theorem contDiffOn_of_smoothOpen {g : Fn} (h : Work.FTS.EllipticEst.SmoothOpen g) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry g) Work.Construction.Qd :=
  (Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp h n

theorem mixed_add_Qd {n : ℕ} {f h : Fn}
    (hf : ContDiffOn ℝ n (Function.uncurry f) Work.Construction.Qd)
    (hh : ContDiffOn ℝ n (Function.uncurry h) Work.Construction.Qd)
    {j i : ℕ} (hji : j + i ≤ n) {z θ : ℝ} (hz : (z, θ) ∈ Work.Construction.Qd) :
    Work.Spaces.mixed j i (f + h) z θ = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i h z θ :=
  Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn isOpen_Qd hf hh i j
    (by omega) (z, θ) hz

theorem isBslSolPos_smul' {α c : ℝ} {F Ψ : Fn}
    (h : Work.FTS.StrongGlobal.IsBslSolPos α F Ψ) :
    Work.FTS.StrongGlobal.IsBslSolPos α (c • F) (c • Ψ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun z hz θ hθ hθ2 => ?_, fun z hz => ?_, fun z hz => ?_, fun θ hθ => ?_⟩
  · rw [Work.FTS.EllipticEst.LevelOneFts.CF.bslOp_smul, h1 z hz θ hθ hθ2]; rfl
  · show c * Ψ z 0 = 0
    rw [h2 z hz, mul_zero]
  · show c * Ψ z (π / 2) = 0
    rw [h3 z hz, mul_zero]
  · have := (h4 θ hθ).const_mul c
    simpa using this

theorem isBslSolPos_zero (α : ℝ) : Work.FTS.StrongGlobal.IsBslSolPos α (0 : Fn) (0 : Fn) :=
  Work.FTS.StrongGlobal.IsBslSol.toPos (Work.FTS.EllipticEst.IsBslSol_zero α)

/-! ## 2. Interleaving -/

def ilv {X : Type*} (a b : ℕ → X) : ℕ → X := fun n => if n % 2 = 0 then a (n / 2) else b (n / 2)

theorem ilv_even {X : Type*} (a b : ℕ → X) (n : ℕ) : ilv a b (2 * n) = a n := by
  simp [ilv]

theorem ilv_odd {X : Type*} (a b : ℕ → X) (n : ℕ) : ilv a b (2 * n + 1) = b n := by
  unfold ilv
  rw [if_neg (show ¬ (2 * n + 1) % 2 = 0 by omega)]
  congr 1
  omega

theorem tendsto_ilv {X : Type*} {l : Filter X} {a b : ℕ → X}
    (ha : Tendsto a atTop l) (hb : Tendsto b atTop l) : Tendsto (ilv a b) atTop l := by
  rw [tendsto_atTop'] at ha hb ⊢
  intro s hs
  obtain ⟨N1, h1⟩ := ha s hs
  obtain ⟨N2, h2⟩ := hb s hs
  refine ⟨2 * (N1 + N2), fun n hn => ?_⟩
  unfold ilv
  split_ifs
  · exact h1 _ (by omega)
  · exact h2 _ (by omega)

theorem tendsto_two_mul : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
  tendsto_atTop_atTop.mpr fun b => ⟨b, fun n hn => by omega⟩

theorem tendsto_two_mul_add_one : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
  tendsto_atTop_atTop.mpr fun b => ⟨b, fun n hn => by omega⟩

theorem limSeq4_ilv {α : ℝ} {fn hn : ℕ → Fn} {f : Fn} (hf : LimSeq4 α fn f)
    (hh : LimSeq4 α hn f) : LimSeq4 α (ilv fn hn) f := by
  obtain ⟨B1, hB1⟩ := hf.bound
  obtain ⟨B2, hB2⟩ := hh.bound
  refine ⟨fun n => ?_, ⟨max B1 B2, fun n => ?_⟩, hf.c4, fun j i hji z θ hz => ?_⟩
  · unfold ilv; split_ifs
    · exact hf.classC _
    · exact hh.classC _
  · unfold ilv; split_ifs
    · exact le_trans (hB1 _) (le_max_left _ _)
    · exact le_trans (hB2 _) (le_max_right _ _)
  · have heq : (fun n => Work.Spaces.mixed j i (ilv fn hn n) z θ)
        = ilv (fun n => Work.Spaces.mixed j i (fn n) z θ)
            (fun n => Work.Spaces.mixed j i (hn n) z θ) := by
      funext n; unfold ilv; split_ifs <;> rfl
    rw [heq]
    exact tendsto_ilv (hf.conv j i hji z θ hz) (hh.conv j i hji z θ hz)


/-! ## 3. `LimSeq4` is linear -/

theorem limSeq4_const {α : ℝ} {g : Fn} (hg : Work.FTS.ClassC.ClassC α g) :
    LimSeq4 α (fun _ => g) g :=
  ⟨fun _ => hg, ⟨_, fun _ => le_rfl⟩, contDiffOn_of_smoothOpen hg.reg 4,
    fun _ _ _ _ _ _ => tendsto_const_nhds⟩

theorem limSeq4_add {α : ℝ} {fn hn : ℕ → Fn} {f h : Fn} (hf : LimSeq4 α fn f)
    (hh : LimSeq4 α hn h) : LimSeq4 α (fun n => fn n + hn n) (f + h) := by
  obtain ⟨B1, hB1⟩ := hf.bound
  obtain ⟨B2, hB2⟩ := hh.bound
  refine ⟨fun n => Work.FTS.ClassC.classC_add (hf.classC n) (hh.classC n),
    ⟨Real.sqrt 2 * (B1 + B2), fun n => ?_⟩, hf.c4.add hh.c4, fun j i hji z θ hz => ?_⟩
  · have hfs := (hf.classC n).reg
    have hhs := (hh.classC n).reg
    have hm1 := Work.FTS.IPGen.HkMem_mono_le hfs 6 (by norm_num) (hf.classC n).mem
    have hm2 := Work.FTS.IPGen.HkMem_mono_le hhs 6 (by norm_num) (hh.classC n).mem
    have := Work.FTS.EllipticEst.HkNorm_add_le α 6
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hfs)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hhs) hm1 hm2
    calc Work.FTS.StrongGlobal.Xn6 α (fn n + hn n)
        = Work.Spaces.HkNorm α 6 (fun z θ => fn n z θ + hn n z θ) := rfl
      _ ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 6 (fn n) + Work.Spaces.HkNorm α 6 (hn n)) := this
      _ ≤ Real.sqrt 2 * (B1 + B2) :=
          mul_le_mul_of_nonneg_left (add_le_add (hB1 n) (hB2 n)) (Real.sqrt_nonneg 2)
  · have hseq : (fun n => Work.Spaces.mixed j i (fn n + hn n) z θ)
        = fun n => Work.Spaces.mixed j i (fn n) z θ + Work.Spaces.mixed j i (hn n) z θ := by
      funext n
      exact mixed_add_Qd (contDiffOn_of_smoothOpen (hf.classC n).reg 4)
        (contDiffOn_of_smoothOpen (hh.classC n).reg 4) hji hz
    rw [hseq, mixed_add_Qd hf.c4 hh.c4 hji hz]
    exact (hf.conv j i hji z θ hz).add (hh.conv j i hji z θ hz)

theorem limSeq4_smul {α : ℝ} (c : ℝ) {fn : ℕ → Fn} {f : Fn} (hf : LimSeq4 α fn f) :
    LimSeq4 α (fun n => c • fn n) (c • f) := by
  obtain ⟨B, hB⟩ := hf.bound
  refine ⟨fun n => Work.FTS.ClassC.classC_smul c (hf.classC n), ⟨|c| * B, fun n => ?_⟩,
    hf.c4.const_smul c, fun j i hji z θ hz => ?_⟩
  · show Work.Spaces.HkNorm α 6 (c • fn n) ≤ |c| * B
    rw [Work.FTS.EllipticEst.HkNorm_smul]
    exact mul_le_mul_of_nonneg_left (hB n) (abs_nonneg c)
  · simp only [Work.FTS.EllipticEst.mixed_smul, Pi.smul_apply, smul_eq_mul]
    exact (hf.conv j i hji z θ hz).const_mul c

/-! ## 4. The construction -/


/-- The class `C` as a submodule. -/
def classCSub (α : ℝ) : Submodule ℝ Fn where
  carrier := {g | Work.FTS.ClassC.ClassC α g}
  zero_mem' := Work.FTS.ClassC.classC_zero α
  add_mem' := fun ha hb => Work.FTS.ClassC.classC_add ha hb
  smul_mem' := fun c _ hg => Work.FTS.ClassC.classC_smul c hg




end Work.FTS_EllLimOK
