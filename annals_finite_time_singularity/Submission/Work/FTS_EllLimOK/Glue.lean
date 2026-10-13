/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.Glue` — the ruling's proved reduction `ExistsEllSolC ∧ EllClosed → ExistsEllSolCLim`

This is the lead's `cbc/fts_ellim_3a_files/EllLimGlue.lean` (ruling of 2026-10-10), installed in
this area with the namespace set to `Work.FTS_EllLimOK` and with
`EllLimOK4` replaced by the area's `EllLimOK` — the *same* definition as
`Work.FTS.StrongEps.EllLimOK` (`Main.Lead_EllLimOK_iff`), kept local so that the area's own
modules do not pay for the heavy `StrongEps` import.  The lemma `ellLimOK4_of_ellLimOK` of the
original is dropped (it related the old and the new form of the statement; the old form no longer
exists).

## Contents

* `exists_section_extend` — the abstract linear algebra: a linear map that is a *section* of a
  submodule `G ≤ V × W` over a class submodule `C` can be adjusted off `C` so as to be a section
  over all of `G`'s first projection.
* the elementary facts `contDiffOn_of_smoothOpen`, `mixed_add_Qd`, `isBslSolPos_smul'`,
  `isBslSolPos_zero`;
* the interleaving machinery (`ilv`) and **`jconv_transfer`**: under `ClosedE`, the jet limit of
  `E` along a `LimSeq4` does not depend on the sequence — this is what makes the graph of `E`
  below a well-defined submodule;
* **`limSeq4_add`**, **`limSeq4_smul`** (and `limSeq4_const`): `LimSeq4` is a linear class, using
  `HkNorm_add_le`, `HkNorm_smul` and `mixed_add_of_contDiffOn`;
* `graphG`, `classCSub` and **`exists_ellLimOK_of_closed`**: any linear `E` with the law, `C²` on
  the class `C` and the closure `ClosedE` can be modified *off the class* into an operator
  satisfying (1a);
* **`existsEllSolCLim_of`** — `ExistsEllSolC` (the delivered elliptic layer) plus the closure
  obligation `EllClosed` give one operator carrying both the packages and (1a);
* **`core1_1a_of_existsEllSolCLim`** — the same at the profile exponent `pExp α`, i.e. Final's
  core fields (1) and (1a) from one `E`.
-/
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_EllLimOK.Defs
import Submission.Work.FTS.ClassC.A1
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.ScaleAPI
import Submission.Work.FTS.EllipticEst.LevelOneFts.CF.bslOp_smul
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.H2.PhiStarE5.Locality
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS.Regularity.Defs

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

/-- **The jet limit does not depend on the sequence**: under `ClosedE`, if the jets of `E (fn n)`
converge to those of `Ψ` along one `LimSeq4` to `f`, they do so along every `LimSeq4` to `f`. -/
theorem jconv_transfer {α : ℝ} {E : Fn → Fn} (hcl : ClosedE α E) {fn hn : ℕ → Fn} {f Ψ : Fn}
    (hf : LimSeq4 α fn f) (hh : LimSeq4 α hn f) (hΨ : JConv (fun n => E (fn n)) Ψ) :
    JConv (fun n => E (hn n)) Ψ := by
  obtain ⟨Ψ', -, -, hΨ'⟩ := hcl _ f (limSeq4_ilv hf hh)
  intro j i hji z θ hz
  have hlim := hΨ' j i hji z θ hz
  have hev : Tendsto (fun n => Work.Spaces.mixed j i (E (fn n)) z θ) atTop
      (𝓝 (Work.Spaces.mixed j i Ψ' z θ)) :=
    Tendsto.congr (fun n => by simp only [Function.comp, ilv_even]) (hlim.comp tendsto_two_mul)
  have hod : Tendsto (fun n => Work.Spaces.mixed j i (E (hn n)) z θ) atTop
      (𝓝 (Work.Spaces.mixed j i Ψ' z θ)) :=
    Tendsto.congr (fun n => by simp only [Function.comp, ilv_odd])
      (hlim.comp tendsto_two_mul_add_one)
  rw [tendsto_nhds_unique (hΨ j i hji z θ hz) hev]
  exact hod

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

/-- The graph submodule: pairs `(f, Ψ)` where `Ψ` is a `C²` solution for `f` and the jet limit of
`E` along some (hence every) `LimSeq4` to `f`. -/
def graphG (α : ℝ) (E : Fn →ₗ[ℝ] Fn)
    (hsm : ∀ g, Work.FTS.ClassC.ClassC α g →
      ContDiffOn ℝ 2 (Function.uncurry (E g)) Work.Construction.Qd) :
    Submodule ℝ (Fn × Fn) where
  carrier := {p | (∃ fn : ℕ → Fn, LimSeq4 α fn p.1 ∧ JConv (fun n => E (fn n)) p.2) ∧
    Work.FTS.StrongGlobal.IsBslSolPos α p.1 p.2 ∧
    ContDiffOn ℝ 2 (Function.uncurry p.2) Work.Construction.Qd}
  zero_mem' := by
    refine ⟨⟨fun _ => 0, limSeq4_const (Work.FTS.ClassC.classC_zero α), ?_⟩,
      isBslSolPos_zero α, contDiffOn_const⟩
    intro j i _ z θ _
    simp only [map_zero]
    exact tendsto_const_nhds
  add_mem' := by
    rintro ⟨f, Ψ⟩ ⟨h, Φ⟩ ⟨⟨fn, hfn, hJf⟩, hlf, hsf⟩ ⟨⟨hn, hhn, hJh⟩, hlh, hsh⟩
    refine ⟨⟨fun n => fn n + hn n, limSeq4_add hfn hhn, ?_⟩,
      IsBslSolPos_add hlf hlh hsf hsh, hsf.add hsh⟩
    intro j i hji z θ hz
    have hseq : (fun n => Work.Spaces.mixed j i (E (fn n + hn n)) z θ)
        = fun n => Work.Spaces.mixed j i (E (fn n)) z θ
            + Work.Spaces.mixed j i (E (hn n)) z θ := by
      funext n
      rw [map_add]
      exact mixed_add_Qd (hsm _ (hfn.classC n)) (hsm _ (hhn.classC n)) hji hz
    show Tendsto (fun n => Work.Spaces.mixed j i (E (fn n + hn n)) z θ) atTop
      (𝓝 (Work.Spaces.mixed j i (Ψ + Φ) z θ))
    rw [hseq, mixed_add_Qd hsf hsh hji hz]
    exact (hJf j i hji z θ hz).add (hJh j i hji z θ hz)
  smul_mem' := by
    rintro c ⟨f, Ψ⟩ ⟨⟨fn, hfn, hJf⟩, hlf, hsf⟩
    refine ⟨⟨fun n => c • fn n, limSeq4_smul c hfn, ?_⟩, isBslSolPos_smul' hlf,
      hsf.const_smul c⟩
    intro j i hji z θ hz
    show Tendsto (fun n => Work.Spaces.mixed j i (E (c • fn n)) z θ) atTop
      (𝓝 (Work.Spaces.mixed j i (c • Ψ) z θ))
    simp only [map_smul, Work.FTS.EllipticEst.mixed_smul, Pi.smul_apply, smul_eq_mul]
    exact (hJf j i hji z θ hz).const_mul c

/-- The class `C` as a submodule. -/
def classCSub (α : ℝ) : Submodule ℝ Fn where
  carrier := {g | Work.FTS.ClassC.ClassC α g}
  zero_mem' := Work.FTS.ClassC.classC_zero α
  add_mem' := fun ha hb => Work.FTS.ClassC.classC_add ha hb
  smul_mem' := fun c _ hg => Work.FTS.ClassC.classC_smul c hg

/-- **The glue (PROVED)**: a linear `E` that solves the law and is `C²` on the class `C`, and is
closed, can be modified *off the class `C`* into an operator satisfying (1a). -/
theorem exists_ellLimOK_of_closed {α : ℝ} (E : Fn →ₗ[ℝ] Fn)
    (hsol : ∀ g, Work.FTS.ClassC.ClassC α g → Work.FTS.StrongGlobal.IsBslSolPos α g (E g))
    (hsm : ∀ g, Work.FTS.ClassC.ClassC α g →
      ContDiffOn ℝ 2 (Function.uncurry (E g)) Work.Construction.Qd)
    (hcl : ClosedE α E) :
    ∃ E' : Fn →ₗ[ℝ] Fn, (∀ g, Work.FTS.ClassC.ClassC α g → E' g = E g) ∧ EllLimOK α E' := by
  have hC : ∀ g ∈ classCSub α, (g, E g) ∈ graphG α E hsm := by
    intro g hg
    exact ⟨⟨fun _ => g, limSeq4_const hg, fun _ _ _ _ _ _ => tendsto_const_nhds⟩, hsol g hg,
      hsm g hg⟩
  obtain ⟨E', hE'C, hE'G⟩ := exists_section_extend (classCSub α) (graphG α E hsm) E hC
  refine ⟨E', fun g hg => hE'C g hg, ?_⟩
  intro fn f B h1 h2 h4 h3
  have hL : LimSeq4 α fn f := ⟨h1, ⟨B, h2⟩, h4, h3⟩
  obtain ⟨Ψ, hl, hs, hJ⟩ := hcl fn f hL
  have hfL : f ∈ (graphG α E hsm).map (LinearMap.fst ℝ Fn Fn) :=
    Submodule.mem_map.mpr ⟨(f, Ψ), ⟨⟨fn, hL, hJ⟩, hl, hs⟩, rfl⟩
  obtain ⟨⟨kn, hkn, hJk⟩, hlaw, -⟩ := hE'G f hfL
  refine ⟨hlaw, fun j i hji z θ hz => ?_⟩
  have := jconv_transfer hcl hkn hL hJk j i hji z θ hz
  refine Tendsto.congr (fun n => ?_) this
  simp only [hE'C (fn n) (h1 n)]

/-- **`ExistsEllSolCLim` from the delivered `ExistsEllSolC` and the closure obligation.** -/
theorem existsEllSolCLim_of (hE : Work.FTS.ClassC.ExistsEllSolC)
    (hcl : ∀ α Ce : ℝ, 0 < α → EllClosed α Ce) : ExistsEllSolCLim := by
  obtain ⟨Ce, hCe, α₀, hα₀, h⟩ := hE
  refine ⟨Ce, hCe, α₀, hα₀, fun α hα hαle => ?_⟩
  obtain ⟨E, hEp⟩ := h α hα hαle
  obtain ⟨E', hE'C, hok⟩ := exists_ellLimOK_of_closed E (fun g hg => (hEp g hg).2.sol)
    (fun g hg => contDiffOn_of_smoothOpen (hEp g hg).2.smooth 2) (hcl α Ce hα E hEp)
  exact ⟨E', fun g hg => by rw [hE'C g hg]; exact hEp g hg, hok⟩

/-- **Final core (1) ∧ (1a) from `ExistsEllSolCLim`**, at the profile exponent. -/
theorem core1_1a_of_existsEllSolCLim (h : ExistsEllSolCLim) :
    ∃ Ce : ℝ, 0 < Ce ∧ ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α →
      Work.FTS.Regularity.pExp α ≤ α₀ → ∃ E : Fn →ₗ[ℝ] Fn,
      (∀ g, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) g →
        Work.FTS.VocabO.EllPkgGo (Work.FTS.Regularity.pExp α) Ce g (E g) ∧
          Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce g (E g)) ∧
      EllLimOK (Work.FTS.Regularity.pExp α) E := by
  obtain ⟨Ce, hCe, α₀, hα₀, hh⟩ := h
  exact ⟨Ce, hCe, α₀, hα₀, fun α hα hle => hh _ (Work.FTS.Regularity.pExp_pos hα) hle⟩

end Work.FTS_EllLimOK
