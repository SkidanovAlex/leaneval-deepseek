/-
  WilE9G / Lagrange — **the differential of the system `degenH`**.

  `degenH S Phi : ℝ^{(n+1+m) + (j+1) + (1+m)} → ℝ^{j + (1 + (1+m))}` is the system whose zero
  set is the Lagrange locus of the genericity step (the `j` equations `h_a` of `S`, the
  normalisation `degenLam`, and the `1+m` rearranged Lagrange equations `degenPsi`).  This file
  computes its differential at a point `p`: the rows of `degenDCLM S Phi p` are

  * `rowH a` (`a : Fin S.j`): `∑_l ∂_l h_a(z) · vz_l` — the equations of `S` depend on the
    `z`-coordinates only;
  * `rowLam`: `∑_a 2 ν_a · vν_a` — the normalisation depends on `(ν,ν₀)` only;
  * `rowPsi l` (`l : Fin (1+m)`): the `z`-derivatives of `ψ_l` plus the `ν`-derivatives plus the
    diagonal `ν₀ Φ` in the `c`-direction.

  The three block computations are `hasFDerivAt_rowH`, `hasFDerivAt_rowLam` and
  `hasFDerivAt_rowPsi`; the assembly is `hasFDerivAt_degenH`.
-/
import Mathlib
import Submission.Work.WilE9G.Lagrange.DegenSetup
import Submission.Work.WilE9G.Amb
import Submission.Work.WilE5.Strat.flatConormalTools

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE9G.Lagrange
open WilkiesDesign WilkiesDesign.E Work.WilE9G

variable {n m : ℕ}

/-! ## 1. The coordinate indices of the `(z, (ν,ν₀), c)`-space -/

/-- The `z`-coordinate of `p` as an index of the ambient space. -/
def zIdx {j : ℕ} (i : Fin (n + (1 + m))) : Fin (degenDim n m j) :=
  ⟨i.val, by simp only [degenDim]; omega⟩

/-- The `(ν,ν₀)`-coordinate of `p` as an index of the ambient space. -/
def nuIdx {j : ℕ} (a : Fin (j + 1)) : Fin (degenDim n m j) :=
  ⟨n + (1 + m) + a.val, by simp only [degenDim]; omega⟩

/-- The `c`-coordinate of `p` as an index of the ambient space. -/
def cIdx {j : ℕ} (l : Fin (1 + m)) : Fin (degenDim n m j) :=
  ⟨n + (1 + m) + (j + 1) + l.val, by simp only [degenDim]; omega⟩

@[simp] theorem degenZ_eq_apply {j : ℕ} (p : Fin (degenDim n m j) → ℝ)
    (i : Fin (n + (1 + m))) : degenZ p i = p (zIdx (m := m) (j := j) i) := rfl

@[simp] theorem degenNu_eq_apply {j : ℕ} (p : Fin (degenDim n m j) → ℝ) (a : Fin (j + 1)) :
    degenNu p a = p (nuIdx (m := m) a) := rfl

@[simp] theorem degenC_eq_apply {j : ℕ} (p : Fin (degenDim n m j) → ℝ) (l : Fin (1 + m)) :
    degenC p l = p (cIdx (m := m) (j := j) l) := rfl

@[simp] theorem degenPt_zIdx {j : ℕ} (z : Fin (n + (1 + m)) → ℝ) (nu : Fin (j + 1) → ℝ)
    (c : Fin (1 + m) → ℝ) (i : Fin (n + (1 + m))) :
    degenPt z nu c (zIdx (m := m) (j := j) i) = z i := by
  have h := congrFun (degenZ_degenPt (n := n) (m := m) z nu c) i
  rwa [degenZ_eq_apply] at h

@[simp] theorem degenPt_nuIdx {j : ℕ} (z : Fin (n + (1 + m)) → ℝ) (nu : Fin (j + 1) → ℝ)
    (c : Fin (1 + m) → ℝ) (a : Fin (j + 1)) :
    degenPt z nu c (nuIdx (m := m) a) = nu a := by
  have h := congrFun (degenNu_degenPt (n := n) (m := m) z nu c) a
  rwa [degenNu_eq_apply] at h

@[simp] theorem degenPt_cIdx {j : ℕ} (z : Fin (n + (1 + m)) → ℝ) (nu : Fin (j + 1) → ℝ)
    (c : Fin (1 + m) → ℝ) (l : Fin (1 + m)) :
    degenPt z nu c (cIdx (m := m) (j := j) l) = c l := by
  have h := congrFun (degenC_degenPt (n := n) (m := m) z nu c) l
  rwa [degenC_eq_apply] at h

/-! ## 2. The coordinate maps as continuous linear maps -/

/-- The map `p ↦ degenZ p` as a continuous linear map. -/
def ZCLM {j : ℕ} : (Fin (degenDim n m j) → ℝ) →L[ℝ] (Fin (n + (1 + m)) → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (zIdx (m := m) (j := j) i)

@[simp] theorem ZCLM_apply {j : ℕ} (p : Fin (degenDim n m j) → ℝ) :
    ZCLM (n := n) (m := m) (j := j) p = degenZ p := rfl

theorem hasFDerivAt_degenZ {j : ℕ} (p : Fin (degenDim n m j) → ℝ) :
    HasFDerivAt (fun p' : Fin (degenDim n m j) → ℝ => degenZ p')
      (ZCLM (n := n) (m := m) (j := j)) p := by
  have h : (fun p' : Fin (degenDim n m j) → ℝ => degenZ p')
      = (ZCLM (n := n) (m := m) (j := j) : (Fin (degenDim n m j) → ℝ) → Fin (n + (1 + m)) → ℝ) :=
    funext fun p' => ZCLM_apply p'
  rw [h]
  exact (ZCLM (n := n) (m := m) (j := j)).hasFDerivAt

/-- The composition of a `pi`-combination of projections on the `z`-space with `ZCLM`. -/
theorem sum_proj_comp_ZCLM {j : ℕ} (cs : Fin (n + (1 + m)) → ℝ) :
    ((∑ l : Fin (n + (1 + m)), cs l • ContinuousLinearMap.proj l) :
        (Fin (n + (1 + m)) → ℝ) →L[ℝ] ℝ) ∘SL (ZCLM (n := n) (m := m) (j := j))
      = ∑ l : Fin (n + (1 + m)), cs l • ContinuousLinearMap.proj (zIdx (m := m) (j := j) l) := by
  ext p
  simp only [ContinuousLinearMap.comp_apply, sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply, ZCLM_apply,
    degenZ_eq_apply, smul_eq_mul]

/-! ## 3. The rows of the differential -/

/-- The row of the differential of `eaEval S.X.c Q ∘ degenZ` at `p`. -/
def eaDRow (S : AmbStratum (n + (1 + m))) (Q : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) : (Fin (degenDim n m S.j) → ℝ) →L[ℝ] ℝ :=
  ∑ l : Fin (n + (1 + m)), eaEval S.X.c (eaD S.X.c l Q) (degenZ p) •
    ContinuousLinearMap.proj (zIdx (m := m) (j := S.j) l)

/-- `eaEval S.X.c Q ∘ degenZ` has the `eaDRow` of `Q` as its differential. -/
theorem hasFDerivAt_eaDRow (S : AmbStratum (n + (1 + m))) (Q : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) :
    HasFDerivAt (fun p' : Fin (degenDim n m S.j) → ℝ => eaEval S.X.c Q (degenZ p'))
      (eaDRow S Q p) p := by
  have hZ := hasFDerivAt_degenZ (n := n) (m := m) (j := S.j) p
  have hE : HasFDerivAt (fun z : Fin (n + (1 + m)) → ℝ => eaEval S.X.c Q z)
      (∑ l : Fin (n + (1 + m)),
        eaEval S.X.c (eaD S.X.c l Q) (degenZ p) • ContinuousLinearMap.proj l) (degenZ p) :=
    Work.WilE5.Calc.hasFDerivAt_eaEval S.X.c Q (degenZ p)
  have hcomp := hE.comp p hZ
  rw [eaDRow, ← sum_proj_comp_ZCLM (n := n) (m := m) (j := S.j)
    (fun l => eaEval S.X.c (eaD S.X.c l Q) (degenZ p))]
  exact hcomp

/-- The row of the differential of the `l`-th rearranged Lagrange equation. -/
def rowPsi (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) (l : Fin (1 + m)) : (Fin (degenDim n m S.j) → ℝ) →L[ℝ] ℝ :=
  (eaEval S.X.c Phi (degenZ p) * degenC p l
      + eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) Phi) (degenZ p))
      • ContinuousLinearMap.proj (nuIdx (m := m) (Fin.last S.j))
    + degenNu p (Fin.last S.j) •
        (degenC p l • eaDRow S Phi p
          + eaEval S.X.c Phi (degenZ p) • ContinuousLinearMap.proj (cIdx (m := m) (j := S.j) l)
          + eaDRow S (eaD S.X.c (Fin.natAdd n l) Phi) p)
    - ∑ a : Fin S.j,
        (eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) (degenZ p) •
            ContinuousLinearMap.proj (nuIdx (m := m) (Fin.castAdd 1 a))
          + degenNu p (Fin.castAdd 1 a) • eaDRow S (eaD S.X.c (Fin.natAdd n l) (S.h a)) p)

/-- The row of the differential of the normalisation. -/
def rowLam (S : AmbStratum (n + (1 + m))) (p : Fin (degenDim n m S.j) → ℝ) :
    (Fin (degenDim n m S.j) → ℝ) →L[ℝ] ℝ :=
  ∑ a : Fin (S.j + 1), (2 * degenNu p a) • ContinuousLinearMap.proj (nuIdx (m := m) a)

/-! ## 3b. Evaluating the rows -/

theorem eaDRow_apply (S : AmbStratum (n + (1 + m))) (Q : EAPoly (n + (1 + m)) S.X.r)
    (p v : Fin (degenDim n m S.j) → ℝ) :
    eaDRow S Q p v = ∑ l : Fin (n + (1 + m)),
      eaEval S.X.c (eaD S.X.c l Q) (degenZ p) * degenZ v l := by
  simp only [eaDRow, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    degenZ_eq_apply]

theorem rowLam_apply (S : AmbStratum (n + (1 + m))) (p v : Fin (degenDim n m S.j) → ℝ) :
    rowLam S p v = ∑ a : Fin (S.j + 1), (2 * degenNu p a) * degenNu v a := by
  simp only [rowLam, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    degenNu_eq_apply]

/-- `eaDRow` vanishes on directions with no `z`-component. -/
theorem eaDRow_degenPt_zero (S : AmbStratum (n + (1 + m))) (Q : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) (vc : Fin (1 + m) → ℝ) :
    eaDRow S Q p (degenPt (0 : Fin (n + (1 + m)) → ℝ) (0 : Fin (S.j + 1) → ℝ) vc) = 0 := by
  rw [eaDRow_apply]
  simp only [degenZ_eq_apply, degenPt_zIdx, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

/-- The `l`-th Lagrange row evaluated on a direction with only `c`-coordinates: only the diagonal
`ν₀ Φ` term survives. -/
theorem rowPsi_apply_degenPt (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (p : Fin (degenDim n m S.j) → ℝ) (l : Fin (1 + m))
    (vc : Fin (1 + m) → ℝ) :
    rowPsi S Phi p l (degenPt (0 : Fin (n + (1 + m)) → ℝ) (0 : Fin (S.j + 1) → ℝ) vc)
      = degenNu p (Fin.last S.j) * eaEval S.X.c Phi (degenZ p) * vc l := by
  simp only [rowPsi, add_apply, sub_apply, sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, eaDRow_degenPt_zero, degenPt_zIdx,
    degenPt_nuIdx, degenPt_cIdx, Pi.zero_apply, mul_zero, zero_mul,
    smul_eq_mul]
  simp
  ring

/-! ## 4. Row indices and the assembled differential -/

/-- The index of the row of the equation `h_a`. -/
def hRow {j : ℕ} (a : Fin j) : Fin (j + (1 + (1 + m))) := Fin.castAdd (1 + (1 + m)) a

/-- The index of the row of the normalisation. -/
def lamRow (j : ℕ) : Fin (j + (1 + (1 + m))) :=
  Fin.natAdd j (Fin.castAdd (1 + m) (0 : Fin 1))

/-- The index of the row of the `l`-th Lagrange equation. -/
def psiRow {j : ℕ} (l : Fin (1 + m)) : Fin (j + (1 + (1 + m))) :=
  Fin.natAdd j (Fin.natAdd 1 l)

@[simp] theorem hRow_val {j : ℕ} (a : Fin j) : (hRow (m := m) a).val = a.val := rfl
@[simp] theorem lamRow_val (j : ℕ) : (lamRow (m := m) j).val = j := by
  simp [lamRow]
@[simp] theorem psiRow_val {j : ℕ} (l : Fin (1 + m)) : (psiRow (m := m) (j := j) l).val
    = j + (1 + l.val) := by
  simp [psiRow]

theorem degenH_apply_hRow (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) (a : Fin S.j) :
    degenH S Phi p (hRow (m := m) a) = eaEval S.X.c (S.h a) (degenZ p) := by
  simp only [degenH, hRow, Fin.append_left]

theorem degenH_apply_lamRow (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) :
    degenH S Phi p (lamRow (m := m) S.j) = degenLam S p := by
  simp only [degenH, lamRow, Fin.append_right, Fin.append_left]

theorem degenH_apply_psiRow (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) (l : Fin (1 + m)) :
    degenH S Phi p (psiRow (m := m) l) = degenPsi S Phi p l := by
  simp only [degenH, psiRow, Fin.append_right]

/-- The row function of the differential of `degenH`. -/
def degenRow (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) :
    Fin (S.j + (1 + (1 + m))) → ((Fin (degenDim n m S.j) → ℝ) →L[ℝ] ℝ) :=
  fun r => Fin.addCases (fun a => eaDRow S (S.h a) p)
    (fun s => Fin.addCases (fun _ : Fin 1 => rowLam S p) (fun l => rowPsi S Phi p l) s) r

theorem degenRow_hRow (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) (a : Fin S.j) :
    degenRow S Phi p (hRow (m := m) a) = eaDRow S (S.h a) p := by
  simp only [degenRow, hRow, Fin.addCases_left]

theorem degenRow_lamRow (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) :
    degenRow S Phi p (lamRow (m := m) S.j) = rowLam S p := by
  simp only [degenRow, lamRow, Fin.addCases_right, Fin.addCases_left]

theorem degenRow_psiRow (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) (l : Fin (1 + m)) :
    degenRow S Phi p (psiRow (m := m) l) = rowPsi S Phi p l := by
  simp only [degenRow, psiRow, Fin.addCases_right]

/-- The differential of `degenH` at `p`. -/
def degenDCLM (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) :
    (Fin (degenDim n m S.j) → ℝ) →L[ℝ] (Fin (S.j + (1 + (1 + m))) → ℝ) :=
  ContinuousLinearMap.pi (degenRow S Phi p)

@[simp] theorem degenDCLM_apply (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (p : Fin (degenDim n m S.j) → ℝ)
    (v : Fin (degenDim n m S.j) → ℝ) (r : Fin (S.j + (1 + (1 + m)))) :
    degenDCLM S Phi p v r = degenRow S Phi p r v := rfl

end Work.WilE9G.Lagrange
