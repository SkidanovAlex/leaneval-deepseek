import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.TowerDefs
import Submission.Work.Diff.STE.contDiff_seriesFun
import Submission.Work.Diff.STE.CSq_comp_le
import Submission.Work.Diff.STE.fourierCoeff_pdVec
import Submission.Work.Diff.STE.summable_wt_zpow
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Preparation for the flat limit step: the jet region, jets of Fourier series, and the level-one
identification

This module collects the elementary facts used by `Work.Diff.STE.flat.limit_solves`:

* the open set `goodJ` of jets with invertible value part (the region on which a DeTurck-shaped
  nonlinearity is smooth), and its basic properties;
* smoothness/periodicity of `x ↦ seriesFunM c x`, of its coordinate derivatives `pdM`, and of the
  spatial `2`-jet `x ↦ jetM (seriesFunM c) x`, from the moment summability of `c`;
* periodicity of a DeTurck-shaped `Φ` in the space variable, on the good region;
* Fourier inversion for `Φ (·, jetM (seriesFunM c) ·)`, giving the **level-one identification**
  `seriesFunM (dd Φ cinf 1 t) x = Φ (x, jetM (seriesFunM (cinf t)) x)`.
-/

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat
open scoped BigOperators Topology

noncomputable section

variable {n : ℕ}

/-! ## The good region of jets -/

/-- The set of jets whose value part has invertible real part: the region on which a
DeTurck-shaped nonlinearity is `C^∞`. -/
def goodJ (n : ℕ) : Set (Jet n) := {w | (reMat w.1).det ≠ 0}

lemma continuous_reMat : Continuous (fun w : Jet n => reMat w.1) := by
  refine continuous_pi (fun i => continuous_pi (fun j => ?_))
  exact Complex.continuous_re.comp
    ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst))

lemma continuous_reMat_det : Continuous (fun w : Jet n => (reMat w.1).det) :=
  continuous_reMat.matrix_det

lemma isOpen_goodJ : IsOpen (goodJ n) := by
  rw [show goodJ n = (fun w : Jet n => (reMat w.1).det) ⁻¹' ({0}ᶜ : Set ℝ) from rfl]
  exact continuous_reMat_det.isOpen_preimage _ isOpen_compl_singleton

/-! ## Jets of a Fourier series -/

lemma contDiff_seriesFunM_of_mom {c : (Fin n → ℤ) → MatC n}
    (hm : ∀ i j : Fin n, ∀ N : ℕ, Summable (fun k : Fin n → ℤ => (wt k) ^ N * ‖c k i j‖)) :
    ContDiff ℝ (⊤ : ℕ∞) (seriesFunM c) := by
  refine contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j => ?_))
  have h := Work.Diff.STE.contDiff_seriesFun (c := fun k : Fin n → ℤ => c k i j) (hm i j)
  simpa only [seriesFunM_apply] using h

lemma periodic_seriesFunM (c : (Fin n → ℤ) → MatC n) : Periodic1 (seriesFunM c) := by
  intro i x
  funext a b
  exact Work.Diff.STE.periodic_seriesFun (fun k : Fin n → ℤ => c k a b) i x

lemma contDiff_pdM {f : Torus n} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (d : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (pdM d f) := by
  refine contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j => ?_))
  have hfi : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => f x i j) :=
    (contDiff_pi.mp (contDiff_pi.mp hf i)) j
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (fun x : Fin n → ℝ => f x i j)) :=
    hfi.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have h2 : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Fin n → ℝ => (fderiv ℝ (fun x : Fin n → ℝ => f x i j) x) (Pi.single d 1)) :=
    h1.clm_apply contDiff_const
  simpa only [pdM, Work.Diff.STE.pd] using h2

lemma periodic_pdM {f : Torus n} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : Periodic1 f) (d : Fin n) :
    Periodic1 (pdM d f) := by
  intro i x
  funext a b
  have hfi : Differentiable ℝ (fun y : Fin n → ℝ => f y a b) :=
    ((contDiff_pi.mp (contDiff_pi.mp hf a)) b).differentiable (by simp)
  have hperi : PeriodicIn i (fun y : Fin n → ℝ => f y a b) :=
    fun y => congrFun (congrFun (hper i y) a) b
  exact Work.Diff.STE.periodicIn_pd_of_differentiable i d hfi hperi x

lemma contDiff_jetM_of_mom {c : (Fin n → ℤ) → MatC n}
    (hm : ∀ i j : Fin n, ∀ N : ℕ, Summable (fun k : Fin n → ℤ => (wt k) ^ N * ‖c k i j‖)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => jetM (seriesFunM c) x) := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) (seriesFunM c) := contDiff_seriesFunM_of_mom hm
  have h1 : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Fin n → ℝ => fun a : Fin n => pdM a (seriesFunM c) x) :=
    contDiff_pi.mpr (fun a => contDiff_pdM hf a)
  have h2 : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Fin n → ℝ => fun a : Fin n => fun b : Fin n => pdM a (pdM b (seriesFunM c)) x) :=
    contDiff_pi.mpr (fun a => contDiff_pi.mpr (fun b => contDiff_pdM (contDiff_pdM hf b) a))
  exact hf.prodMk (h1.prodMk h2)

lemma periodic_jetM {f : Torus n} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : Periodic1 f) :
    Periodic1 (fun x : Fin n → ℝ => jetM f x) := by
  intro i x
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact hper i x
  · funext a
    exact ((periodic_pdM hf hper a) i) x
  · funext a b
    exact ((periodic_pdM (contDiff_pdM hf b) (periodic_pdM hf hper b) a) i) x

/-! ## Periodicity of a DeTurck-shaped nonlinearity -/

/-- A DeTurck-shaped nonlinearity is `1`-periodic in the space variable on the good region. -/
lemma phi_periodic {Φ : (Fin n → ℝ) × Jet n → MatC n} (hshape : IsDeTurckNonlin Φ)
    {x : Fin n → ℝ} {w : Jet n} (i : Fin n) (hw : w ∈ goodJ n) :
    Φ (x + Pi.single i 1, w) = Φ (x, w) := by
  obtain ⟨-, N, -, hdec, hNper⟩ := hshape
  rw [hdec x w.1 w.2.1 w.2.2 hw, hdec (x + Pi.single i 1) w.1 w.2.1 w.2.2 hw]
  have hN' : N (x + Pi.single i 1, w.1, w.2.1) = N (x, w.1, w.2.1) := by
    simpa only [] using hNper (w.1, w.2.1) i x
  rw [hN']

/-! ## The composition with the jet of a Fourier series -/

lemma contDiff_phi_jet {Φ : (Fin n → ℝ) × Jet n → MatC n} (hshape : IsDeTurckNonlin Φ)
    {c : (Fin n → ℤ) → MatC n}
    (hm : ∀ i j : Fin n, ∀ N : ℕ, Summable (fun k : Fin n → ℤ => (wt k) ^ N * ‖c k i j‖))
    (hpd : ∀ x : Fin n → ℝ, (reMat (seriesFunM c x)).det ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => Φ (x, jetM (seriesFunM c) x)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hjx : jetM (seriesFunM c) x ∈ goodJ n := hpd x
  have hs : (Set.univ ×ˢ goodJ n) ∈ 𝓝 (x, jetM (seriesFunM c) x) :=
    (isOpen_univ.prod isOpen_goodJ).mem_nhds ⟨trivial, hjx⟩
  have hΦ : ContDiffAt ℝ (⊤ : ℕ∞) Φ (x, jetM (seriesFunM c) x) := hshape.1.contDiffAt hs
  refine ContDiffAt.comp x hΦ ?_
  exact (contDiff_id.prodMk (contDiff_jetM_of_mom hm)).contDiffAt

lemma periodic_phi_jet {Φ : (Fin n → ℝ) × Jet n → MatC n} (hshape : IsDeTurckNonlin Φ)
    {c : (Fin n → ℤ) → MatC n}
    (hm : ∀ i j : Fin n, ∀ N : ℕ, Summable (fun k : Fin n → ℤ => (wt k) ^ N * ‖c k i j‖))
    (hper : Periodic1 (seriesFunM c))
    (hpd : ∀ x : Fin n → ℝ, (reMat (seriesFunM c x)).det ≠ 0) :
    Periodic1 (fun x : Fin n → ℝ => Φ (x, jetM (seriesFunM c) x)) := by
  have hjet : Periodic1 (fun x : Fin n → ℝ => jetM (seriesFunM c) x) :=
    periodic_jetM (contDiff_seriesFunM_of_mom hm) hper
  intro i x
  have h1 : jetM (seriesFunM c) (x + Pi.single i 1) = jetM (seriesFunM c) x := hjet i x
  show Φ (x + Pi.single i 1, jetM (seriesFunM c) (x + Pi.single i 1))
      = Φ (x, jetM (seriesFunM c) x)
  rw [h1]
  exact phi_periodic hshape i (hpd x)

/-! ## Fourier inversion for matrix-valued functions -/

lemma seriesFunM_fourierCoeffM {F : Torus n} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hper : Periodic1 F) : ∀ x : Fin n → ℝ, seriesFunM (fourierCoeffM F) x = F x := by
  intro x
  funext a b
  exact Work.Diff.STE.flat.seriesFun_fourierCoeff (fun y : Fin n → ℝ => F y a b)
    ((contDiff_pi.mp (contDiff_pi.mp hF a)) b) (fun i y => congrFun (congrFun (hper i y) a) b) x

/-! ## The level-one identification -/

lemma dd_one_eq (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (cinf : ℝ → (Fin n → ℤ) → MatC n) (t : ℝ) :
    dd Φ cinf 1 t = fourierCoeffM (fun x : Fin n → ℝ => Φ (x, jetM (seriesFunM (cinf t)) x)) := by
  funext k a b
  rw [dd_succ]
  show fourierCoeffM (fun x : Fin n → ℝ => Φ (x, jetM (seriesFunM (cinf t)) x)) k a b
      = fourierCoeffM (fun x : Fin n → ℝ => Φ (x, jetM (seriesFunM (cinf t)) x)) k a b
  rfl

lemma dd_one_apply (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (cinf : ℝ → (Fin n → ℤ) → MatC n) (t : ℝ) (k : Fin n → ℤ) (a b : Fin n) :
    dd Φ cinf 1 t k a b = Work.Diff.STE.fourierCoeff
      (fun x : Fin n → ℝ => Φ (x, jetM (seriesFunM (cinf t)) x) a b) k := by
  rw [dd_one_eq]
  rfl

/-- **The level-one identification**: the first time derivative of the limit solution, as a
Fourier series, is the nonlinearity evaluated at the spatial jet of the solution. -/
lemma seriesFunM_dd_one (Φ : (Fin n → ℝ) × Jet n → MatC n) (hshape : IsDeTurckNonlin Φ)
    {cinf : ℝ → (Fin n → ℤ) → MatC n} {t : ℝ}
    (hm : ∀ i j : Fin n, ∀ N : ℕ, Summable (fun k : Fin n → ℤ => (wt k) ^ N * ‖cinf t k i j‖))
    (hper : Periodic1 (seriesFunM (cinf t)))
    (hpd : ∀ x : Fin n → ℝ, (reMat (seriesFunM (cinf t) x)).det ≠ 0) :
    ∀ x : Fin n → ℝ, seriesFunM (dd Φ cinf 1 t) x = Φ (x, jetM (seriesFunM (cinf t)) x) := by
  rw [dd_one_eq]
  exact seriesFunM_fourierCoeffM (contDiff_phi_jet hshape hm hpd)
    (periodic_phi_jet hshape hm hper hpd)

end

end Work.Diff.STE.flat
