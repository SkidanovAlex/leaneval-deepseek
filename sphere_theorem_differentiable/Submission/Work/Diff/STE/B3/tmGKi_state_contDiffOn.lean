import Mathlib
import Submission.Work.Diff.STE.B3.transport_tame_defs
import Submission.Work.Diff.STE.B3.tmNom_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Matrix BigOperators ContDiff
open Filter

namespace Work.Diff.STE.B3

set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## Toolbox

The proof of `tmGKi_state_contDiffOn` splits into two independent pieces, proved here as private
lemmas (so that they do not collide with the sibling modules
`Submission/Work/Diff/STE/B3/tmInv_contDiff_entry.lean` and
`Submission/Work/Diff/STE/B3/tmGK_entry_contDiffOn.lean`, which state the same two facts):

* `tmInv_entry_contDiff` — the clamped matrix inverse `tmInv a b ha hab` is a globally `C^∞`
  function of its matrix argument;
* `tmGK_entry_contDiffOn_aux` — the nominal coordinate chart matrix `tmGK z V` is `C^∞` in the state
  variables on the set where `flatToE (D.x₀ j) z` lies in the chart target and `det (Ff z) ≠ 0`.

The target is then the composition of the first with the second (`ContDiff.comp_contDiffOn`). -/

/-- Entrywise form of the definition of the clamped matrix inverse: the bump of the determinant
times the inverse (written with the unconditional Cramer formula `A⁻¹ = (det A)⁻¹ • A.adjugate`)
plus `(1 - bump) • 1`. -/
private lemma tmInv_apply_aux {n : ℕ} (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    tmInv a b ha hab A i j
      = tmClampBump (n := n) a b ha hab A.det * Ring.inverse A.det * A.adjugate i j
        + (1 - tmClampBump (n := n) a b ha hab A.det) * (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
  simp only [tmInv, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.inv_def]
  ring

/-- The determinant of a matrix family whose entries are `C^∞` at a point is `C^∞` there. -/
private lemma contDiffAt_det_of_entries {n : ℕ} {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] {X : W → Matrix (Fin n) (Fin n) ℝ} {w₀ : W}
    (hX : ∀ i j, ContDiffAt ℝ ∞ (fun w => X w i j) w₀) :
    ContDiffAt ℝ ∞ (fun w => (X w).det) w₀ := by
  have hfun : (fun w : W => (X w).det)
      = fun w => ∑ σ : Equiv.Perm (Fin n), (↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ k, X w (σ k) k := by
    funext w; rw [Matrix.det_apply']
  rw [hfun]
  refine ContDiffAt.sum (fun σ _ => contDiffAt_const.mul ?_)
  exact contDiffAt_prod (t := Finset.univ) (f := fun k w => X w (σ k) k) (fun k _ => hX (σ k) k)

/-- Replacing one row of a matrix family by a constant row preserves local smoothness. -/
private lemma contDiffAt_updateRow_of_entries {n : ℕ} {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] {X : W → Matrix (Fin n) (Fin n) ℝ} {w₀ : W}
    (hX : ∀ i j, ContDiffAt ℝ ∞ (fun w => X w i j) w₀) (q : Fin n) (bb : Fin n → ℝ) :
    ∀ k l, ContDiffAt ℝ ∞ (fun w => (X w).updateRow q bb k l) w₀ := by
  intro k l
  have h2 : (fun w : W => (X w).updateRow q bb k l)
      = fun w => if k = q then bb l else X w k l := by
    funext w; rw [Matrix.updateRow_apply]
  rw [h2]
  by_cases hk : k = q
  · simp only [hk, ite_true]; exact contDiffAt_const
  · simp only [hk, ite_false]; exact hX k l

/-- The adjugate of a matrix family whose entries are `C^∞` at a point is `C^∞` there. -/
private lemma contDiffAt_adjugate_of_entries {n : ℕ} {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] {X : W → Matrix (Fin n) (Fin n) ℝ} {w₀ : W}
    (hX : ∀ i j, ContDiffAt ℝ ∞ (fun w => X w i j) w₀) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun w => (X w).adjugate i j) w₀ := by
  classical
  have hrw : (fun w : W => (X w).adjugate i j)
      = fun w => ((X w).updateRow j (Pi.single i 1)).det := by
    funext w; rw [Matrix.adjugate_apply]
  rw [hrw]
  exact contDiffAt_det_of_entries (contDiffAt_updateRow_of_entries hX j (Pi.single i 1))

/-- **The clamped matrix inverse is a globally `C^∞` function of the matrix entries.**

The bump `tmClampBump a b ha hab` is supported in the ball of radius `b/2` about `(a+b)/2`, hence
vanishes on the ball of radius `a/2` about `0` (as `0 < a`).  So the *junk-free* identity

`tmInv a b ha hab A i j = F (A.det) * (A.det)⁻¹ * A.adjugate i j + (1 - F (A.det)) * 1 i j`

exhibits `tmInv` as a sum of products of smooth functions: `F`, `det` and the adjugate entries are
smooth, and the singular factor `(A.det)⁻¹` is always multiplied by `F (A.det)`, which vanishes
identically near every matrix with `det A = 0`. -/
private lemma tmInv_entry_contDiff {n : ℕ} (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (i j : Fin n) :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
      (fun A : Fin n → Fin n → ℝ => tmInv a b ha hab (Matrix.of A) i j) := by
  classical
  have hbump : ContDiff ℝ ∞ (tmClampBump (n := n) a b ha hab) :=
    ContDiffBump.contDiff (f := (⟨(b - a) / 2, b / 2, by linarith, by linarith⟩ :
      ContDiffBump ((a + b) / 2))) (n := ⊤)
  rw [contDiff_iff_contDiffAt]
  intro A
  have hdetcd : ContDiffAt ℝ ∞ (fun A' : Fin n → Fin n → ℝ => (Matrix.of A').det) A :=
    contDiffAt_det_of_entries (fun p r => by
      simpa only [Matrix.of_apply] using
        (show ContDiffAt ℝ ∞ (fun A' : Fin n → Fin n → ℝ => A' p r) A from by fun_prop))
  have hadj : ContDiffAt ℝ ∞ (fun A' : Fin n → Fin n → ℝ => (Matrix.of A').adjugate i j) A :=
    contDiffAt_adjugate_of_entries (fun p r => by
      simpa only [Matrix.of_apply] using
        (show ContDiffAt ℝ ∞ (fun A' : Fin n → Fin n → ℝ => A' p r) A from by fun_prop)) i j
  by_cases hdet : (Matrix.of A).det = 0
  · -- near a singular matrix the bump vanishes, so `tmInv` is locally the identity matrix
    have hopen : IsOpen {t : ℝ | b / 2 < dist t ((a + b) / 2)} :=
      isOpen_lt continuous_const (continuous_id.dist continuous_const)
    have hmem : (0 : ℝ) ∈ {t : ℝ | b / 2 < dist t ((a + b) / 2)} := by
      show (b / 2 : ℝ) < dist (0 : ℝ) ((a + b) / 2)
      rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (by linarith)]
      linarith
    have hcont : ContinuousAt (fun A' : Fin n → Fin n → ℝ => (Matrix.of A').det) A :=
      hdetcd.continuousAt
    have hev1 : ∀ᶠ A' in nhds A, b / 2 < dist ((Matrix.of A').det) ((a + b) / 2) :=
      hcont.eventually (hopen.mem_nhds (by simpa [hdet] using hmem))
    have hbump0 : ∀ᶠ A' in nhds A,
        tmClampBump (n := n) a b ha hab ((Matrix.of A').det) = 0 := by
      filter_upwards [hev1] with A' hA'
      have h := ContDiffBump.zero_of_le_dist
        (f := (⟨(b - a) / 2, b / 2, by linarith, by linarith⟩ :
          ContDiffBump ((a + b) / 2))) (le_of_lt hA')
      simpa only [tmClampBump] using h
    refine (contDiffAt_const (c := (1 : Matrix (Fin n) (Fin n) ℝ) i j)).congr_of_eventuallyEq ?_
    filter_upwards [hbump0] with A' h0
    rw [tmInv_apply_aux, h0]
    simp
  · -- near a non-singular matrix every factor is smooth
    have hbump' : ContDiffAt ℝ ∞
        (fun A' : Fin n → Fin n → ℝ => tmClampBump (n := n) a b ha hab ((Matrix.of A').det)) A :=
      hbump.contDiffAt.comp A hdetcd
    have hinv : ContDiffAt ℝ ∞
        (fun A' : Fin n → Fin n → ℝ => Ring.inverse ((Matrix.of A').det)) A := by
      have h1 : ContDiffAt ℝ ∞ (fun A' : Fin n → Fin n → ℝ => ((Matrix.of A').det)⁻¹) A :=
        hdetcd.inv hdet
      refine h1.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
      funext A'
      exact congrFun Ring.inverse_eq_inv' ((Matrix.of A').det)
    have hsum : ContDiffAt ℝ ∞
        (fun A' : Fin n → Fin n → ℝ =>
          tmClampBump (n := n) a b ha hab ((Matrix.of A').det)
              * Ring.inverse ((Matrix.of A').det) * (Matrix.of A').adjugate i j
            + (1 - tmClampBump (n := n) a b ha hab ((Matrix.of A').det))
              * (1 : Matrix (Fin n) (Fin n) ℝ) i j) A :=
      ((hbump'.mul hinv).mul hadj).add
        (((contDiffAt_const (c := (1 : ℝ))).sub hbump').mul contDiffAt_const)
    exact hsum.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq
      (funext fun A' => tmInv_apply_aux a b ha hab (Matrix.of A') i j))

/-- **`tmGK` is `C^∞` in the state variables.**  Its entry is
`∑ b, ∑ a, Finvf z i a * V a b * Finvf z k b`; the entries of `Finvf` are smooth at `z` as soon as
`flatToE (D.x₀ j) z` lies in the chart target (smoothness of `Ff`) and `det (Ff z) ≠ 0`
(`tmNom_inv_entry_ContDiffAt`), while `V` only enters polynomially. -/
private lemma tmGK_entry_contDiffOn_aux (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (j : ι₀) (i k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
      (fun w : (Fin (Module.finrank ℝ E) → ℝ) ×
          (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) =>
        Work.Diff.STE.B3.tmGK (I := I) (M := M) D j w.1 w.2 i k)
      {w : (Fin (Module.finrank ℝ E) → ℝ) ×
          (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) |
        Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈ (extChartAt I (D.x₀ j)).target ∧
        (Matrix.of (Work.Diff.STE.B3.Ff (I := I) (M := M) D j w.1)).det ≠ 0} := by
  intro w hw
  obtain ⟨htgt, hdet⟩ := hw
  have hfinv : ∀ p r : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞ (fun w' : (Fin (Module.finrank ℝ E) → ℝ) ×
          (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) =>
        Finvf (I := I) (M := M) D j w'.1 p r) w := by
    intro p r
    exact (tmNom_inv_entry_ContDiffAt
      (X := fun y : Fin (Module.finrank ℝ E) → ℝ => Matrix.of (Ff (I := I) (M := M) D j y))
      (fun a b => Ff_contDiffAt (I := I) (M := M) D j a b htgt) hdet p r).comp w contDiffAt_fst
  have hV : ∀ p r : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞ (fun w' : (Fin (Module.finrank ℝ E) → ℝ) ×
          (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) => w'.2 p r) w := by
    intro p r
    fun_prop
  have hentry : ∀ w' : (Fin (Module.finrank ℝ E) → ℝ) ×
      (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ),
      Work.Diff.STE.B3.tmGK (I := I) (M := M) D j w'.1 w'.2 i k
        = ∑ b, ∑ a, Finvf (I := I) (M := M) D j w'.1 i a * w'.2 a b
            * Finvf (I := I) (M := M) D j w'.1 k b := by
    intro w'
    simp only [Work.Diff.STE.B3.tmGK, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul,
      Matrix.of_apply]
  have hsum : ContDiffAt ℝ ∞
      (fun w' : (Fin (Module.finrank ℝ E) → ℝ) ×
          (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) =>
        ∑ b, ∑ a, Finvf (I := I) (M := M) D j w'.1 i a * w'.2 a b
            * Finvf (I := I) (M := M) D j w'.1 k b) w := by
    refine ContDiffAt.sum (fun b _ => ContDiffAt.sum (fun a _ => ?_))
    exact ((hfinv i a).mul (hV a b)).mul (hfinv k b)
  exact (hsum.congr_of_eventuallyEq
    (Filter.EventuallyEq.of_eq (funext fun w' => hentry w'))).contDiffWithinAt

/-- **Smoothness of the clamped inverse of the nominal coordinate chart matrix, in the state
variables.**

`Work.Diff.STE.B3.tmGKi a b ha hab z V = tmInv a b ha hab (tmGK z V)` with
`tmGK z V = Finvf z * V * Finvf zᵀ` (`Submission/Work/Diff/STE/B3/transport_tame_defs.lean`), where
`Finvf z = (Ff z)⁻¹` entrywise (`Submission/Work/Diff/STE/B3/TransportDefs.lean`) and `tmInv` is the
*smooth clamped* matrix inverse (bump of the determinant times the inverse plus `(1 - bump) • 1`).
The domain is exactly the set on which the `z`-dependence is smooth: `flatToE (D.x₀ j) z` in the
chart target (for `Ff` and for the chart data of `g₀`) and `det (Ff z) ≠ 0` (for `Finvf`).  Nothing
is imposed on the matrix variable `V`, because `tmInv` is smooth in its matrix argument *everywhere*:
its clamp vanishes on a neighbourhood of `{det = 0}`, so the `A⁻¹` factor is only ever evaluated
where `det ≠ 0`.

INGREDIENTS (all proved, in the workspace): `Work.Diff.STE.B3.Ff_contDiffAt` and
`Work.Diff.STE.B3.tmNom_inv_entry_ContDiffAt` / `tmNom_det_ContDiffAt` /
`tmNom_adjugate_ContDiffAt` (`Submission/Work/Diff/STE/B3/tmNom_aux.lean`) for `Finvf`; smoothness of
`tmInv` in the matrix entries (a fresh but mechanical piece: `det`, `adjugate` are polynomial, the
bump is a `ContDiffBump`, and the product `bump(det) • A⁻¹` is smooth everywhere because the bump
vanishes near `det = 0`; use `A⁻¹ = (det A)⁻¹ • A.adjugate` and the local argument of
`contDiff_mul_of_tsupport_subset` in `Submission/Work/Diff/STE/B3/transport_exists_A.lean`); matrix
multiplication and entry extraction are smooth.

The two pieces are proved above as the private lemmas `tmInv_entry_contDiff` (the clamped inverse is
smooth in its matrix argument, by a case split on `det A = 0`) and `tmGK_entry_contDiffOn_aux`
(smoothness of `tmGK` in the state variables); the theorem itself is their composition. -/
theorem tmGKi_state_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (p q : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
      (fun w : (Fin (Module.finrank ℝ E) → ℝ) ×
          (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) =>
        (Work.Diff.STE.B3.tmGKi (I := I) (M := M) D j a b ha hab w.1 w.2) p q)
      {w : (Fin (Module.finrank ℝ E) → ℝ) ×
          (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) |
        Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈ (extChartAt I (D.x₀ j)).target ∧
        (Matrix.of (Work.Diff.STE.B3.Ff (I := I) (M := M) D j w.1)).det ≠ 0} := by
  classical
  set s : Set ((Fin (Module.finrank ℝ E) → ℝ) ×
      (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)) :=
    {w : (Fin (Module.finrank ℝ E) → ℝ) ×
          (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) |
        Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈ (extChartAt I (D.x₀ j)).target ∧
        (Matrix.of (Work.Diff.STE.B3.Ff (I := I) (M := M) D j w.1)).det ≠ 0} with hs
  have hGK : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
      (fun w : (Fin (Module.finrank ℝ E) → ℝ) ×
          (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) =>
        (fun i k => Work.Diff.STE.B3.tmGK (I := I) (M := M) D j w.1 w.2 i k)) s := by
    refine contDiffOn_pi' (fun i => contDiffOn_pi' (fun k => ?_))
    exact tmGK_entry_contDiffOn_aux (I := I) (M := M) D j i k
  have hcomp := (tmInv_entry_contDiff (n := Module.finrank ℝ E) a b ha hab p q).comp_contDiffOn hGK
  refine hcomp.congr (fun w hw => ?_)
  simp only [Function.comp_apply, Work.Diff.STE.B3.tmGKi]
  congr 1

end Work.Diff.STE.B3
