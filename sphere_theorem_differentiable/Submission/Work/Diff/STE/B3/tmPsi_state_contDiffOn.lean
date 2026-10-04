import Mathlib
import Submission.Work.Diff.STE.B3.transport_tame_defs
import Submission.Work.Diff.STE.B3.tmNom_aux
import Submission.Work.Diff.STE.B3.transport_Mf_second
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.B3.densGood
import Submission.Work.Diff.STE.B3.transport_Rres_contDiffOn
import Submission.Work.Diff.STE.deTurck.contDiffOn_pPhi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

noncomputable section

/-- The state space of `tmPsi`: a flat coordinate `z`, the orthonormal-frame chart matrix `V` and
its first jet `W`. -/
abbrev St (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (Fin (Module.finrank ℝ E) → ℝ) ×
    (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) ×
    (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)

/-- The set on which the smoothness of `tmPsi` is asserted in the statement. -/
abbrev Sset (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) : Set (St E) :=
  {w | Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈ (extChartAt I (D.x₀ j)).target ∧
       (Matrix.of (Ff (I := I) (M := M) D j w.1)).det ≠ 0 ∧ (Matrix.of w.2.1).det ≠ 0}

/-! ## Part A: generic calculus helpers -/

/-- A partial derivative of a `C^∞` function of the flat coordinate is `C^∞`. -/
lemma contDiffAt_pdR {d : ℕ} {F : (Fin d → ℝ) → ℝ} {z : Fin d → ℝ}
    (hF : ContDiffAt ℝ ∞ F z) (c : Fin d) :
    ContDiffAt ℝ ∞ (Work.Diff.STE.pdR c F) z := by
  have hfd : ContDiffAt ℝ ∞ (fderiv ℝ F) z := hF.fderiv_right (m := ∞) (by simp)
  have h := (ContinuousLinearMap.contDiff
      (ContinuousLinearMap.apply ℝ ℝ (Pi.single c (1 : ℝ)))).contDiffAt.comp z hfd
  refine h.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
  funext y
  exact (ContinuousLinearMap.apply_apply (Pi.single c (1 : ℝ)) (fderiv ℝ F y)).symm

/-- Composing a smooth function with a continuous linear map. -/
lemma contDiffAt_clm_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (L : F →L[ℝ] G) {f : X → F} {x : X}
    (hf : ContDiffAt ℝ ∞ f x) : ContDiffAt ℝ ∞ (fun y => L (f y)) x :=
  L.contDiff.contDiffAt.comp x hf

/-- Composing a smoothly-varying function with a continuous linear map, within a set. -/
lemma contDiffWithinAt_clm_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (L : F →L[ℝ] G) {f : X → F}
    {s : Set X} {x : X}
    (hf : ContDiffWithinAt ℝ ∞ f s x) : ContDiffWithinAt ℝ ∞ (fun y => L (f y)) s x :=
  ((L.contDiff.contDiffAt).contDiffWithinAt (s := Set.univ)).comp x hf
    (fun _ _ => Set.mem_univ _)

/-- The determinant of a matrix family with smooth entries is smooth. -/
lemma contDiffAt_det_of_entries {n : ℕ} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {X : Y → Matrix (Fin n) (Fin n) ℝ} {y : Y}
    (hX : ∀ i j, ContDiffAt ℝ ∞ (fun y' => X y' i j) y) :
    ContDiffAt ℝ ∞ (fun y' => (X y').det) y := by
  have hfun : (fun y' : Y => (X y').det)
      = fun y' => ∑ σ : Equiv.Perm (Fin n), (↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ k, X y' (σ k) k := by
    funext y'; rw [Matrix.det_apply']
  rw [hfun]
  refine ContDiffAt.sum (fun σ _ => contDiffAt_const.mul ?_)
  exact contDiffAt_prod (t := Finset.univ) (f := fun k y' => X y' (σ k) k) (fun k _ => hX (σ k) k)

lemma contDiffAt_updateRow_of_entries {n : ℕ} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {X : Y → Matrix (Fin n) (Fin n) ℝ} {y : Y}
    (hX : ∀ i j, ContDiffAt ℝ ∞ (fun y' => X y' i j) y) (q : Fin n) (b : Fin n → ℝ) :
    ∀ k l, ContDiffAt ℝ ∞ (fun y' => (X y').updateRow q b k l) y := by
  intro k l
  have h2 : (fun y' : Y => (X y').updateRow q b k l)
      = fun y' => if k = q then b l else X y' k l := by
    funext y'; rw [Matrix.updateRow_apply]
  rw [h2]
  by_cases hk : k = q
  · simp only [hk, ite_true]; exact contDiffAt_const
  · simp only [hk, ite_false]; exact hX k l

/-- The adjugate of a matrix family with smooth entries is smooth. -/
lemma contDiffAt_adjugate_of_entries {n : ℕ} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {X : Y → Matrix (Fin n) (Fin n) ℝ} {y : Y}
    (hX : ∀ i j, ContDiffAt ℝ ∞ (fun y' => X y' i j) y) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun y' => (X y').adjugate i j) y := by
  classical
  have hrw : (fun y' : Y => (X y').adjugate i j)
      = fun y' => ((X y').updateRow j (Pi.single i 1)).det := by
    funext y'; rw [Matrix.adjugate_apply]
  rw [hrw]
  exact contDiffAt_det_of_entries (contDiffAt_updateRow_of_entries hX j (Pi.single i 1))

/-- The entries of the inverse of a matrix family with smooth entries are smooth, away from the
degenerate matrices (Cramer's rule). -/
lemma contDiffAt_invEntry_of_entries {n : ℕ} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {X : Y → Matrix (Fin n) (Fin n) ℝ} {y : Y}
    (hX : ∀ i j, ContDiffAt ℝ ∞ (fun y' => X y' i j) y) (hdet : (X y).det ≠ 0)
    (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun y' => ((X y')⁻¹) i j) y := by
  have hd : ContDiffAt ℝ ∞ (fun y' => (X y').det) y := contDiffAt_det_of_entries hX
  have hdi : ContDiffAt ℝ ∞ (fun y' : Y => Ring.inverse ((X y').det)) y := by
    have h1 : ContDiffAt ℝ ∞ (fun y' : Y => ((X y').det)⁻¹) y := hd.inv hdet
    refine h1.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
    funext y'
    exact congrFun Ring.inverse_eq_inv' ((X y').det)
  have hmul := hdi.mul (contDiffAt_adjugate_of_entries hX i j)
  refine hmul.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
  funext y'
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]

lemma contDiff_tmClampBump (n : ℕ) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ContDiff ℝ ∞ (tmClampBump (n := n) a b ha hab) :=
  (⟨(b - a) / 2, b / 2, by linarith, by linarith⟩ : ContDiffBump ((a + b) / 2)).contDiff (n := ⊤)

/-- The clamp of `tmInv` is supported away from `0`. -/
lemma tsupport_tmClampBump_subset (n : ℕ) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    tsupport (tmClampBump (n := n) a b ha hab) ⊆ {t : ℝ | t ≠ 0} := by
  have hbump : tmClampBump (n := n) a b ha hab
      = ⇑(⟨(b - a) / 2, b / 2, by linarith, by linarith⟩ : ContDiffBump ((a + b) / 2)) := rfl
  intro t ht
  rw [hbump, ContDiffBump.tsupport_eq] at ht
  simp only [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs] at ht
  intro h0
  rw [h0, zero_sub, abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ (a + b) / 2)] at ht
  linarith

/-- The entries of `tmInv` applied to a matrix family with smooth entries are smooth, with **no**
nondegeneracy hypothesis: the clamping bump kills the inverse near the degenerate locus. -/
lemma contDiffAt_tmInv {n : ℕ} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    {X : Y → Matrix (Fin n) (Fin n) ℝ} {y : Y}
    (hX : ∀ i j, ContDiffAt ℝ ∞ (fun y' => X y' i j) y) (p q : Fin n) :
    ContDiffAt ℝ ∞ (fun y' => tmInv a b ha hab (X y') p q) y := by
  classical
  have hBsm : ContDiff ℝ ∞ (tmClampBump (n := n) a b ha hab) := contDiff_tmClampBump n a b ha hab
  have hzero : (0 : ℝ) ∉ tsupport (tmClampBump (n := n) a b ha hab) :=
    fun h => (tsupport_tmClampBump_subset n a b ha hab h) rfl
  have hdet : ContDiffAt ℝ ∞ (fun y' => (X y').det) y := contDiffAt_det_of_entries hX
  have hBdet : ContDiffAt ℝ ∞ (fun y' => tmClampBump (n := n) a b ha hab ((X y').det)) y :=
    hBsm.contDiffAt.comp y hdet
  have hterm2 : ContDiffAt ℝ ∞
      (fun y' => (1 - tmClampBump (n := n) a b ha hab ((X y').det))
        * (1 : Matrix (Fin n) (Fin n) ℝ) p q) y :=
    (contDiffAt_const.sub hBdet).mul contDiffAt_const
  have hterm1 : ContDiffAt ℝ ∞
      (fun y' => tmClampBump (n := n) a b ha hab ((X y').det) * ((X y')⁻¹) p q) y := by
    by_cases hbz : (X y).det ∈ tsupport (tmClampBump (n := n) a b ha hab)
    · have hdetne : (X y).det ≠ 0 := tsupport_tmClampBump_subset n a b ha hab hbz
      exact hBdet.mul (contDiffAt_invEntry_of_entries hX hdetne p q)
    · have hev : ∀ᶠ y' in 𝓝 y, tmClampBump (n := n) a b ha hab ((X y').det) = 0 := by
        have h1 : ∀ᶠ y' in 𝓝 y, (X y').det ∉ tsupport (tmClampBump (n := n) a b ha hab) :=
          hdet.continuousAt.preimage_mem_nhds ((isClosed_tsupport _).isOpen_compl.mem_nhds hbz)
        filter_upwards [h1] with y' hy'
        exact image_eq_zero_of_notMem_tsupport hy'
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hev] with y' hy'
      rw [hy', zero_mul]
  have hmain : ContDiffAt ℝ ∞
      (fun y' => tmClampBump (n := n) a b ha hab ((X y').det) * ((X y')⁻¹) p q
        + (1 - tmClampBump (n := n) a b ha hab ((X y').det))
          * (1 : Matrix (Fin n) (Fin n) ℝ) p q) y :=
    hterm1.add hterm2
  refine hmain.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
  funext y'
  simp only [tmInv, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

/-! ## Part B: the atoms, as functions of the state -/

lemma contDiffAt_fst_state {w : St E} :
    ContDiffAt ℝ ∞ (fun w' : St E => w'.1) w := contDiffAt_fst

/-- Smoothness on the state of a partial derivative of a function of the flat coordinate. -/
lemma contDiffAt_pdR_state {F : (Fin (Module.finrank ℝ E) → ℝ) → ℝ} {w : St E}
    (hF : ContDiffAt ℝ ∞ F w.1) (c : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ ∞ (fun w' : St E => Work.Diff.STE.pdR c F w'.1) w :=
  (contDiffAt_pdR hF c).comp w (contDiffAt_fst_state (E := E))

lemma contDiffAt_Ff_z (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target)
    (a i : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ ∞ (fun y => Ff (I := I) (M := M) D j y a i) z :=
  Ff_contDiffAt (I := I) (M := M) D j a i hz

lemma contDiffAt_Finvf_z (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target)
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0)
    (i a : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ ∞ (fun y => Finvf (I := I) (M := M) D j y i a) z :=
  tmNom_inv_entry_ContDiffAt (X := fun y : Fin (Module.finrank ℝ E) → ℝ =>
      Matrix.of (Ff (I := I) (M := M) D j y))
    (fun p q => Ff_contDiffAt (I := I) (M := M) D j p q hz) hdet i a

lemma contDiffAt_wf_z (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target) :
    ContDiffAt ℝ ∞ (wf (I := I) (M := M) D j) z := by
  have h1 : ContDiffAt ℝ ∞ (D.psi j) z := (D.psi_contDiff j).contDiffAt
  have h2 : ContDiffAt ℝ ∞ (fun z => Real.sqrt (D.dens j z)) z :=
    D.sqrt_dens_contDiffAt j (densGood D j) hz
  exact h1.mul h2

lemma contDiffAt_Ff_state (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {w : St E} (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈
      (extChartAt I (D.x₀ j)).target) (a i : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ ∞ (fun w' : St E => Ff (I := I) (M := M) D j w'.1 a i) w :=
  (contDiffAt_Ff_z (I := I) (M := M) D j hz a i).comp w (contDiffAt_fst_state (E := E))

lemma contDiffAt_Finvf_state (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {w : St E} (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈
      (extChartAt I (D.x₀ j)).target)
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j w.1)).det ≠ 0)
    (i a : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ ∞ (fun w' : St E => Finvf (I := I) (M := M) D j w'.1 i a) w :=
  (contDiffAt_Finvf_z (I := I) (M := M) D j hz hdet i a).comp w (contDiffAt_fst_state (E := E))

lemma contDiffAt_wf_state (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {w : St E} (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈
      (extChartAt I (D.x₀ j)).target) :
    ContDiffAt ℝ ∞ (fun w' : St E => wf (I := I) (M := M) D j w'.1) w :=
  (contDiffAt_wf_z (I := I) (M := M) D j hz).comp w (contDiffAt_fst_state (E := E))

lemma contDiffAt_pdR_wf_state (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {w : St E} (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈
      (extChartAt I (D.x₀ j)).target) (c : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ ∞
      (fun w' : St E => Work.Diff.STE.pdR c (wf (I := I) (M := M) D j) w'.1) w :=
  contDiffAt_pdR_state (contDiffAt_wf_z (I := I) (M := M) D j hz) c

lemma contDiffAt_pdR_pdR_wf_state (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {w : St E} (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈
      (extChartAt I (D.x₀ j)).target) (c d : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ ∞
      (fun w' : St E =>
        Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (wf (I := I) (M := M) D j)) w'.1) w :=
  contDiffAt_pdR_state (contDiffAt_pdR (contDiffAt_wf_z (I := I) (M := M) D j hz) d) c

lemma contDiffAt_pdR_Ff_state (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {w : St E} (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈
      (extChartAt I (D.x₀ j)).target)
    (a i : Fin (Module.finrank ℝ E)) (c : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ ∞
      (fun w' : St E =>
        Work.Diff.STE.pdR c (fun y => Ff (I := I) (M := M) D j y a i) w'.1) w :=
  contDiffAt_pdR_state (contDiffAt_Ff_z (I := I) (M := M) D j hz a i) c

lemma contDiffAt_pdR_pdR_Ff_state (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {w : St E} (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈
      (extChartAt I (D.x₀ j)).target)
    (a i : Fin (Module.finrank ℝ E)) (c d : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ ∞
      (fun w' : St E =>
        Work.Diff.STE.pdR c (Work.Diff.STE.pdR d
          (fun y => Ff (I := I) (M := M) D j y a i)) w'.1) w :=
  contDiffAt_pdR_state (contDiffAt_pdR (contDiffAt_Ff_z (I := I) (M := M) D j hz a i) d) c

lemma contDiffAt_tmDFin_state (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {w : St E} (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈
      (extChartAt I (D.x₀ j)).target)
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j w.1)).det ≠ 0)
    (c i a : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ ∞ (fun w' : St E => tmDFin (I := I) (M := M) D j w'.1 c i a) w := by
  have h := contDiffAt_pdR_state (contDiffAt_Finvf_z (I := I) (M := M) D j hz hdet i a) c
  simpa only [tmDFin] using h

lemma contDiffAt_state_V (p q : Fin (Module.finrank ℝ E)) {w : St E} :
    ContDiffAt ℝ ∞ (fun w' : St E => w'.2.1 p q) w := by
  have h1 : ContDiffAt ℝ ∞ (fun w' : St E => w'.2.1) w := contDiffAt_snd.fst
  have h2 : ContDiffAt ℝ ∞ (fun w' : St E => w'.2.1 p) w :=
    contDiffAt_clm_comp (ContinuousLinearMap.proj p) h1
  exact contDiffAt_clm_comp (ContinuousLinearMap.proj q) h2

lemma contDiffAt_state_W (p q r : Fin (Module.finrank ℝ E)) {w : St E} :
    ContDiffAt ℝ ∞ (fun w' : St E => w'.2.2 p q r) w := by
  have h1 : ContDiffAt ℝ ∞ (fun w' : St E => w'.2.2) w := contDiffAt_snd.snd
  have h2 : ContDiffAt ℝ ∞ (fun w' : St E => w'.2.2 p) w :=
    contDiffAt_clm_comp (ContinuousLinearMap.proj p) h1
  have h3 : ContDiffAt ℝ ∞ (fun w' : St E => w'.2.2 p q) w :=
    contDiffAt_clm_comp (ContinuousLinearMap.proj q) h2
  exact contDiffAt_clm_comp (ContinuousLinearMap.proj r) h3

variable (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)

lemma contDiffAt_tmGK_state {w : St E}
    (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈ (extChartAt I (D.x₀ j)).target)
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j w.1)).det ≠ 0)
    (i k : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ ∞ (fun w' : St E => tmGK (I := I) (M := M) D j w'.1 w'.2.1 i k) w := by
  have hF : ∀ i a : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞ (fun w' : St E => Finvf (I := I) (M := M) D j w'.1 i a) w :=
    fun i a => contDiffAt_Finvf_state (I := I) (M := M) D j hz hdet i a
  have hV : ∀ a b : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞ (fun w' : St E => w'.2.1 a b) w :=
    fun a b => contDiffAt_state_V a b
  simp only [tmGK, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  refine ContDiffAt.sum (fun a _ => ?_)
  refine ContDiffAt.mul ?_ ?_
  · refine ContDiffAt.sum (fun b _ => ?_)
    exact (hF i b).mul (hV b a)
  · exact hF k a

lemma contDiffAt_tmGKi_state (a b : ℝ) (ha : 0 < a) (hab : a < b) {w : St E}
    (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈ (extChartAt I (D.x₀ j)).target)
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j w.1)).det ≠ 0)
    (p q : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ ∞
      (fun w' : St E => tmGKi (I := I) (M := M) D j a b ha hab w'.1 w'.2.1 p q) w := by
  have hGK : ∀ i k : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞ (fun w' : St E => tmGK (I := I) (M := M) D j w'.1 w'.2.1 i k) w :=
    fun i k => contDiffAt_tmGK_state D j hz hdet i k
  exact contDiffAt_tmInv (Y := St E) a b ha hab
    (X := fun w' : St E => tmGK (I := I) (M := M) D j w'.1 w'.2.1) hGK p q

lemma contDiffAt_tmDGK_state {w : St E}
    (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈ (extChartAt I (D.x₀ j)).target)
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j w.1)).det ≠ 0)
    (c i k : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ ∞
      (fun w' : St E => tmDGK (I := I) (M := M) D j w'.1 w'.2.1 w'.2.2 c i k) w := by
  have hF : ∀ i a : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞ (fun w' : St E => Finvf (I := I) (M := M) D j w'.1 i a) w :=
    fun i a => contDiffAt_Finvf_state (I := I) (M := M) D j hz hdet i a
  have hV : ∀ a b : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞ (fun w' : St E => w'.2.1 a b) w :=
    fun a b => contDiffAt_state_V a b
  have hW : ∀ a b r : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞ (fun w' : St E => w'.2.2 a b r) w :=
    fun a b r => contDiffAt_state_W a b r
  have hDF : ∀ c i a : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞ (fun w' : St E => tmDFin (I := I) (M := M) D j w'.1 c i a) w :=
    fun c i a => contDiffAt_tmDFin_state (I := I) (M := M) D j hz hdet c i a
  simp only [tmDGK]
  refine ContDiffAt.sum (fun a _ => ContDiffAt.sum (fun b _ => ?_))
  refine ContDiffAt.add (ContDiffAt.add ?_ ?_) ?_
  · exact ((hDF c i a).mul (hV a b)).mul (hF k b)
  · exact ((hF i a).mul (hW a b c)).mul (hF k b)
  · exact ((hF i a).mul (hV a b)).mul (hDF c k b)

lemma contDiffAt_tmDGKclm_state {w : St E}
    (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈ (extChartAt I (D.x₀ j)).target)
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j w.1)).det ≠ 0) :
    ContDiffAt ℝ ∞
      (fun w' : St E => tmDGKclm (I := I) (M := M) D j w'.1 w'.2.1 w'.2.2) w := by
  have hD : ∀ c i k : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞
        (fun w' : St E => tmDGK (I := I) (M := M) D j w'.1 w'.2.1 w'.2.2 c i k) w :=
    fun c i k => contDiffAt_tmDGK_state D j hz hdet c i k
  simp only [tmDGKclm]
  refine ContDiffAt.sum (fun c _ => ?_)
  refine contDiffAt_clm_comp
    (L := ContinuousLinearMap.smulRightL ℝ E (Work.Diff.EXT.MatE (E := E))
      ((Work.Diff.EXT.bB (E := E)).coord c).toContinuousLinearMap)
    (f := fun w' : St E => (fun i k : Fin (Module.finrank ℝ E) =>
      tmDGK (I := I) (M := M) D j w'.1 w'.2.1 w'.2.2 c i k)) ?_
  rw [contDiffAt_pi]
  intro i
  rw [contDiffAt_pi]
  intro k
  exact hD c i k

lemma contDiffAt_tmEight_state {w : St E}
    (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈ (extChartAt I (D.x₀ j)).target)
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j w.1)).det ≠ 0)
    (c d a b : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ ∞
      (fun w' : St E => tmEight (I := I) (M := M) D j w'.1 w'.2.1 w'.2.2 c d a b) w := by
  have hF : ∀ a i : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞ (fun w' : St E => Ff (I := I) (M := M) D j w'.1 a i) w :=
    fun a i => contDiffAt_Ff_state (I := I) (M := M) D j hz a i
  have hDF : ∀ c a i : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞
        (fun w' : St E => Work.Diff.STE.pdR c
          (fun y => Ff (I := I) (M := M) D j y a i) w'.1) w :=
    fun c a i => contDiffAt_pdR_Ff_state (I := I) (M := M) D j hz a i c
  have hDDF : ∀ c d a i : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞
        (fun w' : St E => Work.Diff.STE.pdR c (Work.Diff.STE.pdR d
          (fun y => Ff (I := I) (M := M) D j y a i)) w'.1) w :=
    fun c d a i => contDiffAt_pdR_pdR_Ff_state (I := I) (M := M) D j hz a i c d
  have hGK : ∀ i k : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞ (fun w' : St E => tmGK (I := I) (M := M) D j w'.1 w'.2.1 i k) w :=
    fun i k => contDiffAt_tmGK_state D j hz hdet i k
  have hDGK : ∀ c i k : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞
        (fun w' : St E => tmDGK (I := I) (M := M) D j w'.1 w'.2.1 w'.2.2 c i k) w :=
    fun c i k => contDiffAt_tmDGK_state D j hz hdet c i k
  simp only [tmEight]
  refine ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun k _ => ?_))
  refine ContDiffAt.add (ContDiffAt.add (ContDiffAt.add (ContDiffAt.add (ContDiffAt.add
    (ContDiffAt.add (ContDiffAt.add ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · exact ((hDDF c d a i).mul (hGK i k)).mul (hF b k)
  · exact ((hDF c a i).mul (hDGK d i k)).mul (hF b k)
  · exact ((hDF c a i).mul (hGK i k)).mul (hDF d b k)
  · exact ((hDF d a i).mul (hDGK c i k)).mul (hF b k)
  · exact ((hDF d a i).mul (hGK i k)).mul (hDF c b k)
  · exact ((hF a i).mul (hDGK c i k)).mul (hDF d b k)
  · exact ((hF a i).mul (hDGK d i k)).mul (hDF c b k)
  · exact ((hF a i).mul (hGK i k)).mul (hDDF c d b k)

/-- **The determinant of `tmGK z V` is nonvanishing** whenever `det (Ff z) ≠ 0` and `det V ≠ 0`:
this is the nondegeneracy that `pN` needs for its unclamped inverse. -/
lemma det_tmGK_ne_zero {z : Fin (Module.finrank ℝ E) → ℝ}
    {V : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ}
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0)
    (hV : (Matrix.of V).det ≠ 0) :
    (Matrix.of (tmGK (I := I) (M := M) D j z V)).det ≠ 0 := by
  have h1 : (Matrix.of (Finvf (I := I) (M := M) D j z)).det ≠ 0 := by
    rw [Finvf_eq_inv (I := I) (M := M) D j z, Matrix.det_nonsing_inv,
      congrFun Ring.inverse_eq_inv']
    exact inv_ne_zero hdet
  have hkey : (Matrix.of (tmGK (I := I) (M := M) D j z V)).det
      = (Matrix.of (Finvf (I := I) (M := M) D j z) * Matrix.of V
          * (Matrix.of (Finvf (I := I) (M := M) D j z))ᵀ).det := rfl
  rw [hkey, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  exact mul_ne_zero (mul_ne_zero h1 hV) h1

/-- The chart `2`-jet of the background metric `g₀` along the flat coordinate, as a function of the
state. -/
lemma contDiffAt_gJet_state {w : St E}
    (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈ (extChartAt I (D.x₀ j)).target) :
    ContDiffAt ℝ ∞ (fun w' : St E =>
      Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
        (yf (I := I) (M := M) D j w'.1)) w := by
  have hjet : ContDiffOn ℝ ∞
      (fun y : E => Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j) y)
      (extChartAt I (D.x₀ j)).target :=
    Work.Diff.STE.D.psi.contDiffOn_chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
      (fun y hy => (Work.Diff.EXT.kz_contDiffAt_chartMatFun
        (I := I) g₀ (D.x₀ j) hy).contDiffWithinAt)
  have h1 : ContDiffAt ℝ ∞ (fun w' : St E =>
      Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
        (Work.Diff.STE.flatToE (I := I) (D.x₀ j) w'.1)) w :=
    ContDiffAt.comp (x := w) (f := fun w' : St E => Work.Diff.STE.flatToE (I := I) (D.x₀ j) w'.1)
      (hjet.contDiffAt ((isOpen_extChartAt_target (I := I) (D.x₀ j)).mem_nhds hz))
      (((Work.Diff.STE.contDiff_flatToE (I := I) (x₀ := D.x₀ j)).comp
        contDiff_fst).contDiffAt)
  simpa only [yf] using h1

/-- The nominal coordinate-frame chart matrix, viewed as a matrix (i.e. as an element of the
function space `MatE`), so that `C^∞`-statements about it do not have to unfold `Matrix`. -/
def tmGKm (z : Fin (Module.finrank ℝ E) → ℝ)
    (V : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) :
    Work.Diff.EXT.MatE (E := E) :=
  tmGK (I := I) (M := M) D j z V

/-- The pair of `2`-jets fed into the jet-level DeTurck operator `pPhi`, as a function of the
state. -/
def pNMap (w : St E) : Work.Diff.STE.deTurck.JetPair E :=
  (((Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
        (yf (I := I) (M := M) D j w.1)).1,
    (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
        (yf (I := I) (M := M) D j w.1)).2.1,
    (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
        (yf (I := I) (M := M) D j w.1)).2.2),
   (tmGK (I := I) (M := M) D j w.1 w.2.1,
    tmDGKclm (I := I) (M := M) D j w.1 w.2.1 w.2.2, 0))

lemma contDiffAt_pNMap_state {w : St E}
    (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈ (extChartAt I (D.x₀ j)).target)
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j w.1)).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun w' : St E => pNMap (I := I) (M := M) (g₀ := g₀) D j w') w := by
  have hjet := contDiffAt_gJet_state (I := I) (M := M) (g₀ := g₀) D j hz
  have hA : ∀ i k : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞ (fun w' : St E => tmGK (I := I) (M := M) D j w'.1 w'.2.1 i k) w :=
    fun i k => contDiffAt_tmGK_state D j hz hdet i k
  have hA' : ContDiffAt ℝ ∞ (fun w' : St E => tmGKm (I := I) (M := M) D j w'.1 w'.2.1) w := by
    rw [contDiffAt_pi]
    intro i
    rw [contDiffAt_pi]
    intro k
    exact hA i k
  have hL := contDiffAt_tmDGKclm_state D j hz hdet
  have h2 : ContDiffAt ℝ ∞ (fun w' : St E =>
      (tmGKm (I := I) (M := M) D j w'.1 w'.2.1,
        tmDGKclm (I := I) (M := M) D j w'.1 w'.2.1 w'.2.2,
        (0 : E →L[ℝ] E →L[ℝ] Work.Diff.EXT.MatE (E := E)))) w :=
    ContDiffAt.prodMk hA' (ContDiffAt.prodMk hL contDiffAt_const)
  exact ContDiffAt.prodMk
    (ContDiffAt.prodMk hjet.fst (ContDiffAt.prodMk hjet.snd.fst hjet.snd.snd)) h2

lemma mapsTo_pNMap_state :
    MapsTo (fun w' : St E => pNMap (I := I) (M := M) (g₀ := g₀) D j w')
      (Sset (I := I) (M := M) D j) (Work.Diff.STE.deTurck.pPhiDom E) := by
  intro y hy
  obtain ⟨hy1, hy2, hy3⟩ := hy
  refine ⟨?_, ?_⟩
  · have hpd : (Matrix.of (Work.Diff.EXT.gmat (I := I) g₀ (D.x₀ j)
        ((extChartAt I (D.x₀ j)).symm (yf (I := I) (M := M) D j y.1)))).PosDef :=
      Work.Diff.STE.deTurck.posDef_gmat (I := I) g₀ (D.x₀ j)
        (Work.Diff.STE.D.psi.symm_target_mem_chart_source (I := I) hy1)
    have hne : (Matrix.of (Work.Diff.EXT.gmat (I := I) g₀ (D.x₀ j)
        ((extChartAt I (D.x₀ j)).symm (yf (I := I) (M := M) D j y.1)))).det ≠ 0 :=
      ne_of_gt hpd.det_pos
    simpa only [pNMap, Work.Diff.STE.D.psi.chartJetOf_fst_inner] using hne
  · have h := det_tmGK_ne_zero (I := I) (M := M) D j hy2 hy3
    simpa only [pNMap] using h

/-- **The `pN`-term of `tmPsi` is `C^∞` in the state.** -/
lemma contDiffWithinAt_pN_state (i k : Fin (Module.finrank ℝ E)) {w : St E}
    (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈ (extChartAt I (D.x₀ j)).target)
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j w.1)).det ≠ 0)
    (hV : (Matrix.of w.2.1).det ≠ 0) :
    ContDiffWithinAt ℝ ∞ (fun w' : St E =>
      Work.Diff.STE.DeTurck.pN
        (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
          (yf (I := I) (M := M) D j w'.1)).1
        (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
          (yf (I := I) (M := M) D j w'.1)).2.1
        (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
          (yf (I := I) (M := M) D j w'.1)).2.2
        (Matrix.of (tmGK (I := I) (M := M) D j w'.1 w'.2.1))
        (tmDGKclm (I := I) (M := M) D j w'.1 w'.2.1 w'.2.2) i k)
      (Sset (I := I) (M := M) D j) w := by
  have hG : ContDiffWithinAt ℝ ∞ (fun w' : St E => pNMap (I := I) (M := M) (g₀ := g₀) D j w')
      (Sset (I := I) (M := M) D j) w :=
    (contDiffAt_pNMap_state (I := I) (M := M) (g₀ := g₀) D j hz hdet).contDiffWithinAt
  have hmem := mapsTo_pNMap_state (I := I) (M := M) (g₀ := g₀) D j
  have hwS : w ∈ Sset (I := I) (M := M) D j := ⟨hz, hdet, hV⟩
  have hcomp := ContDiffWithinAt.comp (x := w)
    ((Work.Diff.STE.deTurck.contDiffOn_pPhi (E := E)).contDiffWithinAt (hmem hwS)) hG hmem
  have h1 : ContDiffWithinAt ℝ ∞ (fun w' : St E =>
      Work.Diff.STE.DeTurck.pN
        (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
          (yf (I := I) (M := M) D j w'.1)).1
        (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
          (yf (I := I) (M := M) D j w'.1)).2.1
        (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
          (yf (I := I) (M := M) D j w'.1)).2.2
        (Matrix.of (tmGK (I := I) (M := M) D j w'.1 w'.2.1))
        (tmDGKclm (I := I) (M := M) D j w'.1 w'.2.1 w'.2.2))
      (Sset (I := I) (M := M) D j) w :=
    hcomp.congr (fun y hy => by unfold Work.Diff.STE.DeTurck.pN pNMap; rfl)
      (by unfold Work.Diff.STE.DeTurck.pN pNMap; rfl)
  exact contDiffWithinAt_clm_comp
    ((ContinuousLinearMap.proj k : (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj i : Work.Diff.EXT.MatE (E := E) →L[ℝ]
        (Fin (Module.finrank ℝ E) → ℝ))) h1

/-- **The assembly**: `tmPsi` is `C^∞` in the state at every point of the statement's domain. -/
lemma contDiffWithinAt_tmPsi_state (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (a' b' : Fin (Module.finrank ℝ E)) {w : St E}
    (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈ (extChartAt I (D.x₀ j)).target)
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j w.1)).det ≠ 0)
    (hV : (Matrix.of w.2.1).det ≠ 0) :
    ContDiffWithinAt ℝ ∞
      (fun w' : St E => tmPsi (I := I) (M := M) D j a b ha hab w'.1 w'.2.1 w'.2.2 a' b')
      (Sset (I := I) (M := M) D j) w := by
  have hS1 : ContDiffWithinAt ℝ ∞ (fun w' : St E =>
      ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
        tmGKi (I := I) (M := M) D j a b ha hab w'.1 w'.2.1 c d
          * (Work.Diff.STE.pdR c (wf (I := I) (M := M) D j) w'.1 * w'.2.2 a' b' d
              + Work.Diff.STE.pdR d (wf (I := I) (M := M) D j) w'.1 * w'.2.2 a' b' c
              + Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (wf (I := I) (M := M) D j)) w'.1
                * w'.2.1 a' b'))
      (Sset (I := I) (M := M) D j) w := by
    refine ContDiffWithinAt.sum (fun c _ => ContDiffWithinAt.sum (fun d _ => ?_))
    refine ContDiffWithinAt.mul ?_ ?_
    · exact (contDiffAt_tmGKi_state D j a b ha hab hz hdet c d).contDiffWithinAt
    · refine ContDiffWithinAt.add (ContDiffWithinAt.add (ContDiffWithinAt.mul ?_ ?_)
        (ContDiffWithinAt.mul ?_ ?_)) (ContDiffWithinAt.mul ?_ ?_)
      · exact (contDiffAt_pdR_wf_state D j hz c).contDiffWithinAt
      · exact (contDiffAt_state_W a' b' d).contDiffWithinAt
      · exact (contDiffAt_pdR_wf_state D j hz d).contDiffWithinAt
      · exact (contDiffAt_state_W a' b' c).contDiffWithinAt
      · exact (contDiffAt_pdR_pdR_wf_state D j hz c d).contDiffWithinAt
      · exact (contDiffAt_state_V a' b').contDiffWithinAt
  have hS2 : ContDiffWithinAt ℝ ∞ (fun w' : St E =>
      wf (I := I) (M := M) D j w'.1
        * (∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
            tmGKi (I := I) (M := M) D j a b ha hab w'.1 w'.2.1 c d
              * tmEight (I := I) (M := M) D j w'.1 w'.2.1 w'.2.2 c d a' b'))
      (Sset (I := I) (M := M) D j) w := by
    refine ContDiffWithinAt.mul ?_ ?_
    · exact (contDiffAt_wf_state D j hz).contDiffWithinAt
    · refine ContDiffWithinAt.sum (fun c _ => ContDiffWithinAt.sum (fun d _ => ?_))
      exact ((contDiffAt_tmGKi_state D j a b ha hab hz hdet c d).contDiffWithinAt).mul
        ((contDiffAt_tmEight_state D j hz hdet c d a' b').contDiffWithinAt)
  have hS3 : ContDiffWithinAt ℝ ∞ (fun w' : St E =>
      wf (I := I) (M := M) D j w'.1
        * (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            Ff (I := I) (M := M) D j w'.1 a' i * Ff (I := I) (M := M) D j w'.1 b' k
              * (Work.Diff.STE.DeTurck.pN
                  (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
                    (yf (I := I) (M := M) D j w'.1)).1
                  (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
                    (yf (I := I) (M := M) D j w'.1)).2.1
                  (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
                    (yf (I := I) (M := M) D j w'.1)).2.2
                  (Matrix.of (tmGK (I := I) (M := M) D j w'.1 w'.2.1))
                  (tmDGKclm (I := I) (M := M) D j w'.1 w'.2.1 w'.2.2) i k)))
      (Sset (I := I) (M := M) D j) w := by
    refine ContDiffWithinAt.mul ?_ ?_
    · exact (contDiffAt_wf_state D j hz).contDiffWithinAt
    · refine ContDiffWithinAt.sum (fun i _ => ContDiffWithinAt.sum (fun k _ => ?_))
      refine ContDiffWithinAt.mul (ContDiffWithinAt.mul ?_ ?_) ?_
      · exact (contDiffAt_Ff_state (I := I) (M := M) D j hz a' i).contDiffWithinAt
      · exact (contDiffAt_Ff_state (I := I) (M := M) D j hz b' k).contDiffWithinAt
      · exact contDiffWithinAt_pN_state D j i k hz hdet hV
  refine (((hS1.neg).sub hS2).add hS3).congr (fun y hy => ?_) ?_
  · simp only [tmPsi]
  · simp only [tmPsi]

/-- **Smoothness of the residual `tmPsi` in the state variables.**

`Work.Diff.STE.B3.tmPsi a b ha hab z V W a' b'` is the residual of the transport identity
(`Submission/Work/Diff/STE/B3/transport_tame_defs.lean`); this states that it is `C^∞` as a function
of `(z, V, W)` on the set where `flatToE (D.x₀ j) z` lies in the chart target (for `Ff`, for the
chart data of `g₀` and for `wf`) and `det (Ff z) ≠ 0` (for `Finvf`), and where the state matrix `V` is
invertible.

The last conjunct `(Matrix.of w.2.1).det ≠ 0` is *necessary*: the third summand of `tmPsi` feeds
`Matrix.of (tmGK z V)` into `Work.Diff.STE.DeTurck.pN`, and `pN` contains the **unclamped** inverse
(`jInv A = (Matrix.of A)⁻¹`), while `det (tmGK z V) = det (Finvf z)² * det V`.  So at a state with
`det V = 0` (and `wf z ≠ 0`) `tmPsi` is unbounded in every neighbourhood.  The principal parts of
`tmPsi` use the *clamped* `tmGKi` and are smooth in `V` with no condition (see
`Work.Diff.STE.B3.tmGKi_state_contDiffOn`).

INGREDIENTS (all proved, in the workspace): `Work.Diff.STE.B3.Ff_contDiffAt`,
`Work.Diff.STE.B3.tmNom_Finvf_ContDiffAt`, `tmNom_det_ContDiffAt`,
`tmNom_adjugate_ContDiffAt`, `tmNom_inv_entry_ContDiffAt`,
`tmNom_pdR_Gf_eq_tmDGK` (`Submission/Work/Diff/STE/B3/tmNom_aux.lean`) for `Ff`, `Finvf` and their
partials; `Work.Diff.STE.D.psi.contDiffOn_chartJetOf` and
`Work.Diff.EXT.kz_contDiffAt_chartMatFun` for the chart data of `g₀` and `h`;
`Work.Diff.STE.B3.wf`/`D.psi_contDiff`/`D.sqrt_dens_contDiffAt` for `wf`; smoothness of `tmInv` in
the matrix variable (as in `Work.Diff.STE.B3.tmGKi_state_contDiffOn`); smoothness of `pN` on the
locus where both Gram matrices are invertible (`Work.Diff.STE.deTurck.contDiffOn_pPhi`,
cf. `Submission/Work/Diff/STE/B3/transport_Rres_contDiffOn.lean` which proves the same kind of
statement for `Rres`).  Everything is a finite sum/product of smooth pieces, so `fun_prop` plus the
quoted inputs should close it. -/
theorem tmPsi_state_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (a' b' : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
      (fun w : (Fin (Module.finrank ℝ E) → ℝ) ×
          (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) ×
          (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
            Fin (Module.finrank ℝ E) → ℝ) =>
        Work.Diff.STE.B3.tmPsi (I := I) (M := M) D j a b ha hab w.1 w.2.1 w.2.2 a' b')
      {w : (Fin (Module.finrank ℝ E) → ℝ) ×
          (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) ×
          (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
            Fin (Module.finrank ℝ E) → ℝ) |
        Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈ (extChartAt I (D.x₀ j)).target ∧
        (Matrix.of (Work.Diff.STE.B3.Ff (I := I) (M := M) D j w.1)).det ≠ 0 ∧
        (Matrix.of w.2.1).det ≠ 0} := by
  intro w hw
  obtain ⟨hz, hdet, hdetV⟩ := hw
  exact contDiffWithinAt_tmPsi_state D j a b ha hab a' b' hz hdet hdetV

end

end Work.Diff.STE.B3
