/-
# `IsDeTurckNonlin` for the chart nonlinearity `chartNonlin bg`

The flat analytic core of the DeTurck trick (`Submission.Work.Diff.STE.Flat.TorusShortTimeExistence`)
applies to a nonlinearity `Φ : (Fin n → ℝ) × Jet n → MatC n` of *DeTurck shape*
(`Work.Diff.STE.Flat.IsDeTurckNonlin Φ`), i.e. one for which there is an `N` with

* `Φ (x, (A, L, B)) = secOpFlat A B + N (x, (A, L))` whenever `reMat A` is invertible,
* `N` is `C^∞` on `{det (reMat A) ≠ 0}` and `1`-periodic in `x`,
* and `Φ` itself is `C^∞` on the same set.

This file discharges that obligation for the chart nonlinearity

`chartNonlin bg (x, (A, L, B)) = secOpFlat A B + ↑(pN (bg x) (∂bg x) (∂²bg x) (reMat A) (∂A))`

of `Submission/Work/Diff/STE/Man/Defs.lean`, which packages the coordinate DeTurck operator
`pPhi` for the background metric with chart matrix `bg`.

The lower-order part is `chartNonlinN bg` by construction, so the decomposition and the
periodicity conditions are immediate; the mathematical content is the smoothness of

* `bgJet bg x = (bg x, linMatOf (∂bg x), bilMatOf (∂²bg x))` in `x` — this is where the
  hypotheses `hbg` (`C^∞`) and `hdet` (the background Gram matrix is invertible everywhere)
  are used: `pPhi` involves the **inverse** of the background Gram matrix, which is `C^∞`
  exactly where the determinant is nonzero;
* the composite with the jet-level operator `pPhi`, which is `C^∞` on the set where the
  foreground Gram matrix is invertible (that is the content of the already proven
  `Work.Diff.STE.deTurck.contDiffOn_pPhi`);
* the scalar principal part `secOpFlat A B`, `C^∞` in `(A, B)` where `A` is invertible.

The only structural work is that `linMatOf`/`bilMatOf` (the continuous linear maps with
prescribed values on the canonical basis `bB`) are `C^∞` functions of their coefficient
families, which is proved by exhibiting them as continuous linear maps.
-/
import Mathlib
import Submission.Work.Diff.STE.Man.Defs
import Submission.Work.Diff.STE.deTurck.contDiffOn_pPhi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators
open Set

namespace Work.Diff.STE.Man

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

noncomputable section

/-! ## 1. `linMatOf` and `bilMatOf` are smooth in their coefficient families

`linMatOf L` is the continuous linear map `E →L[ℝ] F` with `linMatOf L (bB c) = L c`.  As a
function of the family `L` it is continuous linear (it is the composite of the linear equivalence
`LinearMap.toContinuousLinearMap` with `bB.constr`), hence `C^∞`; `bilMatOf` is the same
construction applied twice, `bilMatOf B = linMatOf (fun c => linMatOf (B c))`. -/

/-- `linMatOf` is continuous linear in its coefficient family. -/
private noncomputable def linMatOfLM {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    (Fin (dim E) → F) →ₗ[ℝ] (E →L[ℝ] F) :=
  (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (F' := F)).toLinearMap.comp
    (((Work.Diff.EXT.bB (E := E)).constr ℝ).toLinearMap)

/-- `linMatOf` as a continuous linear map. -/
private noncomputable def linMatOfCLM {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] : (Fin (dim E) → F) →L[ℝ] (E →L[ℝ] F) :=
  LinearMap.toContinuousLinearMap (𝕜 := ℝ) (F' := E →L[ℝ] F) (linMatOfLM (E := E) (F := F))

/-- **Smoothness of `linMatOf` in the coefficients.** -/
lemma contDiff_linMatOf {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] :
    ContDiff ℝ (⊤ : ℕ∞) (fun L : Fin (dim E) → F => linMatOf (E := E) L) := by
  have h := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := (⊤ : ℕ∞))
    (linMatOfCLM (E := E) (F := F))
  exact h

/-- **Smoothness of `bilMatOf` in the coefficients.** -/
lemma contDiff_bilMatOf {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun B : Fin (dim E) → Fin (dim E) → F => bilMatOf (E := E) B) := by
  have h : (fun B : Fin (dim E) → Fin (dim E) → F => bilMatOf (E := E) B)
      = fun B => linMatOf (E := E) (F := E →L[ℝ] F) (fun c => linMatOf (E := E) (B c)) := rfl
  rw [h]
  refine contDiff_linMatOf (F := E →L[ℝ] F) |>.comp ?_
  refine contDiff_pi.mpr (fun c => ?_)
  exact contDiff_linMatOf.comp (by fun_prop)

/-! ## 2. The background jet family `bgJet` -/

/-- **The background jet family**: the value, the first jet and the second jet of the background
chart matrix `bg`, packaged as the triple of jets on which the coordinate DeTurck operator
`Work.Diff.STE.DeTurck.pPhi` is evaluated. -/
noncomputable def bgJet (bg : (Fin (dim E) → ℝ) → Work.Diff.EXT.MatE (E := E))
    (x : Fin (dim E) → ℝ) :
    Work.Diff.EXT.MatE (E := E) × Work.Diff.STE.DeTurck.LinMat E ×
      Work.Diff.STE.DeTurck.BilMat E :=
  (bg x, linMatOf (fun c => dpd (E := E) c bg x),
    bilMatOf (fun c d => dpd (E := E) c (dpd (E := E) d bg) x))

@[simp] lemma bgJet_fst (bg : (Fin (dim E) → ℝ) → Work.Diff.EXT.MatE (E := E))
    (x : Fin (dim E) → ℝ) : (bgJet bg x).1 = bg x := rfl

@[simp] lemma bgJet_snd_fst (bg : (Fin (dim E) → ℝ) → Work.Diff.EXT.MatE (E := E))
    (x : Fin (dim E) → ℝ) :
    (bgJet bg x).2.1 = linMatOf (E := E) (fun c => dpd (E := E) c bg x) := rfl

@[simp] lemma bgJet_snd_snd (bg : (Fin (dim E) → ℝ) → Work.Diff.EXT.MatE (E := E))
    (x : Fin (dim E) → ℝ) :
    (bgJet bg x).2.2 = bilMatOf (E := E) (fun c d => dpd (E := E) c (dpd (E := E) d bg) x) :=
  rfl

/-- A coordinate partial derivative of a `C^∞` family is `C^∞`. -/
lemma contDiff_dpd {β : Type*} [NormedAddCommGroup β] [NormedSpace ℝ β]
    {f : (Fin (dim E) → ℝ) → β} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : Fin (dim E)) :
    ContDiff ℝ (⊤ : ℕ∞) (dpd (E := E) c f) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  exact h1.clm_apply contDiff_const

/-- **The background jet family of a `C^∞` chart matrix is `C^∞`.** -/
lemma contDiff_bgJet {bg : (Fin (dim E) → ℝ) → Work.Diff.EXT.MatE (E := E)}
    (hbg : ContDiff ℝ (⊤ : ℕ∞) bg) : ContDiff ℝ (⊤ : ℕ∞) (bgJet bg) := by
  have hL : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => linMatOf (E := E) (fun c => dpd (E := E) c bg x)) :=
    contDiff_linMatOf.comp (contDiff_pi.mpr (fun c => contDiff_dpd hbg c))
  have hB : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => bilMatOf (E := E) (fun c d => dpd (E := E) c (dpd (E := E) d bg) x)) :=
    contDiff_bilMatOf.comp (contDiff_pi.mpr (fun c => contDiff_pi.mpr (fun d =>
      contDiff_dpd (contDiff_dpd hbg d) c)))
  exact hbg.prodMk (hL.prodMk hB)

/-- The coordinate partial derivative of a `1`-periodic differentiable family is `1`-periodic. -/
lemma periodicIn_dpd_of_differentiable (i c : Fin (dim E)) {β : Type*}
    [NormedAddCommGroup β] [NormedSpace ℝ β] {f : (Fin (dim E) → ℝ) → β}
    (hf : Differentiable ℝ f) (hper : Work.Diff.STE.PeriodicIn i f) :
    Work.Diff.STE.PeriodicIn i (dpd (E := E) c f) := by
  intro x
  have hφ : fderiv ℝ (fun y : Fin (dim E) → ℝ => y + Pi.single i 1) x
      = ContinuousLinearMap.id ℝ (Fin (dim E) → ℝ) := by simp
  have hcomp : fderiv ℝ (fun y : Fin (dim E) → ℝ => f (y + Pi.single i 1)) x
      = fderiv ℝ f x := by
    rw [show (fun y : Fin (dim E) → ℝ => f (y + Pi.single i 1)) = f from funext hper]
  have h2 : fderiv ℝ (fun y : Fin (dim E) → ℝ => f (y + Pi.single i 1)) x
      = (fderiv ℝ f (x + Pi.single i 1)).comp
          (fderiv ℝ (fun y : Fin (dim E) → ℝ => y + Pi.single i 1) x) :=
    fderiv_comp x (hf.differentiableAt) (by fun_prop)
  rw [hcomp, hφ, ContinuousLinearMap.comp_id] at h2
  simp only [dpd]
  rw [← h2]

/-- **The background jet family of a `1`-periodic chart matrix is `1`-periodic.** -/
lemma periodic_bgJet {bg : (Fin (dim E) → ℝ) → Work.Diff.EXT.MatE (E := E)}
    (hbg : ContDiff ℝ (⊤ : ℕ∞) bg) (hper : Work.Diff.STE.Periodic1 bg) :
    Work.Diff.STE.Periodic1 (bgJet bg) := by
  intro i x
  simp only [bgJet]
  have h1 : bg (x + Pi.single i 1) = bg x := hper i x
  have h2 : (fun c => dpd (E := E) c bg (x + Pi.single i 1)) = (fun c => dpd (E := E) c bg x) :=
    funext (fun c => periodicIn_dpd_of_differentiable i c (hbg.differentiable (by simp)) (hper i) x)
  have h3 : (fun c d => dpd (E := E) c (dpd (E := E) d bg) (x + Pi.single i 1))
      = (fun c d => dpd (E := E) c (dpd (E := E) d bg) x) := by
    funext c d
    exact periodicIn_dpd_of_differentiable i c
      ((contDiff_dpd hbg d).differentiable (by simp))
      (periodicIn_dpd_of_differentiable i d (hbg.differentiable (by simp)) (hper i)) x
  rw [h1, h2, h3]

/-! ## 3. The jet-level nonlinearity and its smoothness -/

/-- A triple of background jets `(Aba, Lba, Bba)`. -/
abbrev MatTriple (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    Type _ :=
  Work.Diff.EXT.MatE (E := E) × Work.Diff.STE.DeTurck.LinMat E × Work.Diff.STE.DeTurck.BilMat E

/-- A pair of triples of jets: the background jets and the jets of the unknown. -/
abbrev JetPair (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    Type _ := MatTriple E × MatTriple E

/-- The real part of a complex matrix, as a real matrix over the canonical index type (so that the
target of the map is the normed space `Fin n → Fin n → ℝ` rather than the type synonym `Matrix`). -/
noncomputable def reMatFun (A : Flat.MatC (dim E)) : Work.Diff.EXT.MatE (E := E) :=
  fun i j => (A i j).re

@[simp] lemma reMatFun_apply (A : Flat.MatC (dim E)) (i j : Fin (dim E)) :
    reMatFun (E := E) A i j = (A i j).re := rfl

/-- `reMatFun` is `Flat.reMat`, seen as a matrix. -/
lemma matrix_of_reMatFun (A : Flat.MatC (dim E)) :
    Matrix.of (reMatFun (E := E) A) = Flat.reMat A := rfl

/-- The real part of a complex matrix is `C^∞` in the matrix. -/
lemma contDiff_reMatFun : ContDiff ℝ (⊤ : ℕ∞) (reMatFun (E := E)) := by
  rw [contDiff_pi]; intro i
  rw [contDiff_pi]; intro j
  exact Complex.reCLM.contDiff.comp (by fun_prop)

/-- The entrywise complexification of a real matrix, as a map. -/
lemma contDiff_ofRealMat : ContDiff ℝ (⊤ : ℕ∞) (ofRealMat (E := E)) := by
  rw [contDiff_pi]; intro i
  rw [contDiff_pi]; intro j
  exact Complex.ofRealCLM.contDiff.comp (by fun_prop)

/-- The coordinate DeTurck operator on a pair of jets, as an entrywise complexified matrix. -/
noncomputable def pPhiArrowC (q : JetPair E) : Flat.MatC (dim E) :=
  ofRealMat (Work.Diff.STE.DeTurck.pPhi q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.2.1 q.2.2.2)

/-- **`pPhi` is `C^∞` where both Gram matrices are invertible** (entrywise complexified). -/
lemma contDiffOn_pPhiArrowC :
    ContDiffOn ℝ (⊤ : ℕ∞) (pPhiArrowC (E := E))
      {q : JetPair E | (Matrix.of q.1.1).det ≠ 0 ∧ (Matrix.of q.2.1).det ≠ 0} :=
  contDiff_ofRealMat.comp_contDiffOn (Work.Diff.STE.deTurck.contDiffOn_pPhi (E := E))

/-- The unpacking of a background triple and a value/first jet pair into the pair of `2`-jets on
which `pPhi` is evaluated.  The second jet of the unknown is set to `0`, since `pN = pPhi (·, ·, 0)`
is the lower-order part. -/
noncomputable def unpackRed
    (z : MatTriple E × (Flat.MatC (dim E) × (Fin (dim E) → Flat.MatC (dim E)))) :
    JetPair E :=
  (z.1, (reMatFun (E := E) z.2.1, linMatOf (E := E) (fun c => reMatFun (E := E) (z.2.2 c)),
    (0 : Work.Diff.STE.DeTurck.BilMat E)))

/-- The lower-order part of the chart nonlinearity at the jet level, as a function of the
background jets `J` and the value `A` and first jet `L` of the unknown. -/
noncomputable def pNcore (J : MatTriple E) (A : Flat.MatC (dim E))
    (L : Fin (dim E) → Flat.MatC (dim E)) : Flat.MatC (dim E) :=
  pPhiArrowC (E := E) (unpackRed (E := E) (J, (A, L)))

lemma contDiff_unpackRed : ContDiff ℝ (⊤ : ℕ∞) (unpackRed (E := E)) := by
  have h2 : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : MatTriple E × (Flat.MatC (dim E) × (Fin (dim E) → Flat.MatC (dim E))) =>
        reMatFun (E := E) z.2.1) :=
    contDiff_reMatFun.comp (by fun_prop)
  have h3 : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : MatTriple E × (Flat.MatC (dim E) × (Fin (dim E) → Flat.MatC (dim E))) =>
        linMatOf (E := E) (fun c => reMatFun (E := E) (z.2.2 c))) :=
    contDiff_linMatOf.comp (contDiff_pi.mpr (fun c => contDiff_reMatFun.comp (by fun_prop)))
  exact (by fun_prop : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : MatTriple E × (Flat.MatC (dim E) × (Fin (dim E) → Flat.MatC (dim E))) => z.1)).prodMk
    (h2.prodMk (h3.prodMk contDiff_const))

/-- **Smoothness of the lower-order chart nonlinearity** on the set where the foreground Gram
matrix is invertible, holding the background triple fixed. -/
lemma contDiffOn_pNcoreRed :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : MatTriple E × (Flat.MatC (dim E) × (Fin (dim E) → Flat.MatC (dim E))) =>
        pNcore (E := E) z.1 z.2.1 z.2.2)
      ({J : MatTriple E | (Matrix.of J.1).det ≠ 0} ×ˢ
        {w : Flat.MatC (dim E) × (Fin (dim E) → Flat.MatC (dim E)) |
          (Flat.reMat w.1).det ≠ 0}) := by
  have hunpack : ContDiffOn ℝ (⊤ : ℕ∞) (unpackRed (E := E))
      ({J : MatTriple E | (Matrix.of J.1).det ≠ 0} ×ˢ
        {w : Flat.MatC (dim E) × (Fin (dim E) → Flat.MatC (dim E)) |
          (Flat.reMat w.1).det ≠ 0}) := (contDiff_unpackRed (E := E)).contDiffOn
  have h := (contDiffOn_pPhiArrowC (E := E)).comp hunpack ?_
  · exact h
  · rintro ⟨J, w⟩ ⟨hJ, hw⟩
    exact ⟨hJ, hw⟩

/-- **Smoothness of the lower-order chart nonlinearity** on the set where the foreground Gram
matrix is invertible, for the *full* spatial jet as second argument. -/
lemma contDiffOn_pNcoreFull :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : MatTriple E × Flat.Jet (dim E) => pNcore (E := E) z.1 z.2.1 z.2.2.1)
      ({J : MatTriple E | (Matrix.of J.1).det ≠ 0} ×ˢ
        {w : Flat.Jet (dim E) | (Flat.reMat w.1).det ≠ 0}) := by
  have hproj : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : MatTriple E × Flat.Jet (dim E) => (z.1, (z.2.1, z.2.2.1))) := by fun_prop
  have hprojOn : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : MatTriple E × Flat.Jet (dim E) => (z.1, (z.2.1, z.2.2.1)))
      ({J : MatTriple E | (Matrix.of J.1).det ≠ 0} ×ˢ
        {w : Flat.Jet (dim E) | (Flat.reMat w.1).det ≠ 0}) := hproj.contDiffOn
  have h := (contDiffOn_pNcoreRed (E := E)).comp hprojOn ?_
  · exact h
  · rintro ⟨J, w⟩ ⟨hJ, hw⟩
    exact ⟨hJ, hw⟩

/-- The lower-order part of the chart nonlinearity, as a function of the background jet family. -/
noncomputable def pNred (G : (Fin (dim E) → ℝ) → MatTriple E) :
    (Fin (dim E) → ℝ) × (Flat.MatC (dim E) × (Fin (dim E) → Flat.MatC (dim E))) →
      Flat.MatC (dim E) :=
  fun p => pNcore (E := E) (G p.1) p.2.1 p.2.2

/-- The lower-order part of the chart nonlinearity, for a full spatial jet. -/
noncomputable def pNfull (G : (Fin (dim E) → ℝ) → MatTriple E) :
    (Fin (dim E) → ℝ) × Flat.Jet (dim E) → Flat.MatC (dim E) :=
  fun p => pNcore (E := E) (G p.1) p.2.1 p.2.2.1

/-- **Smoothness of the lower-order chart nonlinearity** for a smooth background jet family whose
Gram matrix is everywhere invertible (value/first-jet version). -/
lemma contDiffOn_pNred {G : (Fin (dim E) → ℝ) → MatTriple E}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGdet : ∀ x, (Matrix.of (G x).1).det ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (pNred (E := E) G)
      (univ ×ˢ {w : Flat.MatC (dim E) × (Fin (dim E) → Flat.MatC (dim E)) |
        (Flat.reMat w.1).det ≠ 0}) := by
  have hinner : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (Fin (dim E) → ℝ) × (Flat.MatC (dim E) × (Fin (dim E) → Flat.MatC (dim E))) =>
        (G p.1, p.2)) :=
    (hG.comp (by fun_prop)).prodMk (by fun_prop)
  have hinnerOn : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Fin (dim E) → ℝ) × (Flat.MatC (dim E) × (Fin (dim E) → Flat.MatC (dim E))) =>
        (G p.1, p.2))
      (univ ×ˢ {w : Flat.MatC (dim E) × (Fin (dim E) → Flat.MatC (dim E)) |
        (Flat.reMat w.1).det ≠ 0}) := hinner.contDiffOn
  have h := (contDiffOn_pNcoreRed (E := E)).comp hinnerOn ?_
  · exact h
  · rintro ⟨x, w⟩ ⟨-, hw⟩
    exact ⟨hGdet x, hw⟩

/-- **Smoothness of the lower-order chart nonlinearity** for a smooth background jet family whose
Gram matrix is everywhere invertible (full-jet version). -/
lemma contDiffOn_pNfull {G : (Fin (dim E) → ℝ) → MatTriple E}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGdet : ∀ x, (Matrix.of (G x).1).det ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (pNfull (E := E) G)
      (univ ×ˢ {w : Flat.Jet (dim E) | (Flat.reMat w.1).det ≠ 0}) := by
  have hinner : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (Fin (dim E) → ℝ) × Flat.Jet (dim E) => (G p.1, p.2)) :=
    (hG.comp (by fun_prop)).prodMk (by fun_prop)
  have hinnerOn : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Fin (dim E) → ℝ) × Flat.Jet (dim E) => (G p.1, p.2))
      (univ ×ˢ {w : Flat.Jet (dim E) | (Flat.reMat w.1).det ≠ 0}) := hinner.contDiffOn
  have h := (contDiffOn_pNcoreFull (E := E)).comp hinnerOn ?_
  · exact h
  · rintro ⟨x, w⟩ ⟨-, hw⟩
    exact ⟨hGdet x, hw⟩

/-- Periodicity of the lower-order chart nonlinearity in the background family. -/
lemma periodic_pNcore {G : (Fin (dim E) → ℝ) → MatTriple E} (hG : Work.Diff.STE.Periodic1 G)
    (A : Flat.MatC (dim E)) (L : Fin (dim E) → Flat.MatC (dim E)) :
    Work.Diff.STE.Periodic1 (fun x => pNcore (E := E) (G x) A L) := by
  intro i x
  show pNcore (E := E) (G (x + Pi.single i 1)) A L = pNcore (E := E) (G x) A L
  rw [hG i x]

/-- Periodicity of the lower-order chart nonlinearity in `x`, at a fixed value/first-jet pair. -/
lemma periodic_pNred {G : (Fin (dim E) → ℝ) → MatTriple E} (hG : Work.Diff.STE.Periodic1 G)
    (w : Flat.MatC (dim E) × (Fin (dim E) → Flat.MatC (dim E))) :
    Work.Diff.STE.Periodic1 (fun x : Fin (dim E) → ℝ => pNred (E := E) G (x, w)) := by
  intro i x
  show pNcore (E := E) (G (x + Pi.single i 1)) w.1 w.2
      = pNcore (E := E) (G x) w.1 w.2
  rw [hG i x]

/-! ## 4. The scalar principal part `secOpFlat` -/

/-- The entries of the inverse of an invertible real matrix depend `C^∞`-ly on the matrix. -/
lemma contDiffOn_matrixInv_entry {n : ℕ} (c d : Fin n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun B : Fin n → Fin n → ℝ => ((Matrix.of B)⁻¹) c d)
      {B : Fin n → Fin n → ℝ | (Matrix.of B).det ≠ 0} := by
  intro B hB
  exact (contDiffAt_pi.mp (contDiffAt_pi.mp
    (Work.Diff.EXT.contDiffAt_matrix_inv_pi (M := B) hB) c) d).contDiffWithinAt

/-- The entries of the inverse of the real part of a complex matrix depend `C^∞`-ly on the matrix,
where the matrix is invertible. -/
lemma contDiffOn_reMatInv_entry (c d : Fin (dim E)) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun A : Flat.MatC (dim E) => (((Matrix.of (reMatFun (E := E) A))⁻¹) c d : ℂ))
      {A : Flat.MatC (dim E) | (Matrix.of (reMatFun (E := E) A)).det ≠ 0} := by
  intro A hA
  have hB : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun B : Fin (dim E) → Fin (dim E) → ℝ => ((Matrix.of B)⁻¹) c d) (reMatFun (E := E) A) :=
    contDiffAt_pi.mp (contDiffAt_pi.mp
      (Work.Diff.EXT.contDiffAt_matrix_inv_pi (M := reMatFun (E := E) A) hA) c) d
  have hC : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun A : Flat.MatC (dim E) => ((Matrix.of (reMatFun (E := E) A))⁻¹) c d) A :=
    hB.comp A contDiff_reMatFun.contDiffAt
  have hD : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun A : Flat.MatC (dim E) => (((Matrix.of (reMatFun (E := E) A))⁻¹) c d : ℂ)) A :=
    Complex.ofRealCLM.contDiff.comp_contDiffAt A hC
  exact hD.contDiffWithinAt

/-- **Smoothness of the scalar principal part `secOpFlat`** where the coefficient matrix is
invertible. -/
lemma contDiffOn_secOpFlat :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Fin (dim E) → ℝ) × Flat.Jet (dim E) => Flat.secOpFlat p.2.1 p.2.2.2)
      (univ ×ˢ {w : Flat.Jet (dim E) | (Flat.reMat w.1).det ≠ 0}) := by
  rw [contDiffOn_pi]; intro i
  rw [contDiffOn_pi]; intro j
  simp only [Flat.secOpFlat]
  refine ContDiffOn.sum (fun c _ => ContDiffOn.sum (fun d _ => ?_))
  refine ContDiffOn.mul ?_ ?_
  · exact (contDiffOn_reMatInv_entry (E := E) c d).comp (by fun_prop) (fun p hp => hp.2)
  · fun_prop

/-! ## 5. The chart nonlinearity is of DeTurck shape -/

/-- The defining decomposition of `chartNonlin` in terms of the jet-level lower-order part. -/
lemma chartNonlin_eq_secOpFlat_add_pNfull
    (bg : (Fin (dim E) → ℝ) → Work.Diff.EXT.MatE (E := E)) :
    chartNonlin (E := E) bg
      = fun p : (Fin (dim E) → ℝ) × Flat.Jet (dim E) =>
          Flat.secOpFlat p.2.1 p.2.2.2 + pNfull (E := E) (bgJet bg) p := rfl

/-- `chartNonlinN` is the lower-order part of `chartNonlin`, as a function of the background jet
family. -/
lemma chartNonlinN_eq_pNred (bg : (Fin (dim E) → ℝ) → Work.Diff.EXT.MatE (E := E)) :
    chartNonlinN (E := E) bg = pNred (E := E) (bgJet bg) := rfl

/-! ## 6. The target -/

theorem isDeTurckNonlin_chartNonlin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    (bg : (Fin (Work.Diff.STE.Man.dim E) → ℝ) → Work.Diff.EXT.MatE (E := E))
    (hbg : ContDiff ℝ (⊤ : ℕ∞) bg)
    (hper : Work.Diff.STE.Periodic1 bg)
    (hdet : ∀ x : Fin (Work.Diff.STE.Man.dim E) → ℝ, (Matrix.of (bg x)).det ≠ 0) :
    Work.Diff.STE.Flat.IsDeTurckNonlin (Work.Diff.STE.Man.chartNonlin (E := E) bg) := by
  have hG : ContDiff ℝ (⊤ : ℕ∞) (bgJet bg) := contDiff_bgJet hbg
  have hGdet : ∀ x, (Matrix.of (bgJet bg x).1).det ≠ 0 := fun x => hdet x
  refine ⟨?_, chartNonlinN (E := E) bg, ?_, ?_, ?_⟩
  · rw [chartNonlin_eq_secOpFlat_add_pNfull]
    exact (contDiffOn_secOpFlat (E := E)).add (contDiffOn_pNfull (E := E) hG hGdet)
  · rw [chartNonlinN_eq_pNred]
    exact contDiffOn_pNred (E := E) hG hGdet
  · intro x A L B _hA
    exact chartNonlin_eq_secOpFlat_add (E := E) bg x A L B
  · intro w
    rw [chartNonlinN_eq_pNred]
    exact periodic_pNred (E := E) (periodic_bgJet hbg hper) w

end

end Work.Diff.STE.Man
