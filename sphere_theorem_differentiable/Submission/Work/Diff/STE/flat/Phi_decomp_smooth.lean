import Mathlib
import Submission.Work.Diff.STE.flat.level_defs
import Submission.Work.Diff.STE.flat.level_aux
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.flat.det_ne_zero_of_quadForm_le
import Submission.Work.Diff.STE.commutator_pd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

open scoped BigOperators
open Work.Diff.STE.Flat

/-! ## Private helpers: the smoothness and periodicity of the flat jet of a Fourier series

Every estimate below is an immediate consequence of the two facts proved elsewhere in the
workspace, namely that a rapidly decaying Fourier series is `C^∞` (`contDiff_seriesFun`) and that
`∂ᵢ` preserves `1`-periodicity (`periodicIn_pd_of_differentiable`). -/

/-- The coordinate partial derivative of a smooth function `(Fin n → ℝ) → ℂ` is smooth.  (`pd d` is
`fderiv ℝ · (Pi.single d 1)`, and `fderiv` lowers the level by one while `⊤ : ℕ∞` is fixed by
`n ↦ n - 1`.) -/
private lemma pd_contDiff_top {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (d : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.pd d f) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) :=
    hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have h2 : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Fin n → ℝ => (fderiv ℝ f x) (Pi.single d 1)) := h1.clm_apply contDiff_const
  rw [show Work.Diff.STE.pd d f
      = (fun x : Fin n → ℝ => (fderiv ℝ f x) (Pi.single d 1)) from rfl]
  exact h2

/-- A matrix-valued Fourier series with rapidly decaying coefficients is smooth. -/
private lemma seriesFunM_contDiff {n : ℕ} (c : (Fin n → ℤ) → MatC n)
    (hmom : ∀ (i j : Fin n) (M : ℕ),
      Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ M * ‖c k i j‖)) :
    ContDiff ℝ (⊤ : ℕ∞) (seriesFunM c) := by
  refine contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j => ?_))
  have h := Work.Diff.STE.contDiff_seriesFun (c := fun k : Fin n → ℤ => c k i j)
    (fun M => hmom i j M)
  simpa only [Flat.seriesFunM_apply] using h

/-- The Fourier series of a coefficient family is `1`-periodic. -/
private lemma periodic_seriesFunM {n : ℕ} (c : (Fin n → ℤ) → MatC n) :
    Periodic1 (seriesFunM c) := by
  intro k x
  funext i j
  simpa only [Flat.seriesFunM_apply] using
    (periodic1_seriesFun (fun m : Fin n → ℤ => c m i j) k x : _)

/-- Entrywise form of the periodicity of `seriesFunM`. -/
private lemma periodic_seriesFunM_apply {n : ℕ} (c : (Fin n → ℤ) → MatC n) (i j : Fin n) :
    Periodic1 (fun x : Fin n → ℝ => seriesFunM c x i j) :=
  fun k x => congrFun (congrFun (periodic_seriesFunM c k x) i) j

/-- `pd` preserves `1`-periodicity of a smooth function. -/
private lemma periodic_pd_of_contDiff {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : Periodic1 f) (a : Fin n) :
    Periodic1 (Work.Diff.STE.pd a f) :=
  fun k => Work.Diff.STE.periodicIn_pd_of_differentiable k a (hf.differentiable (by simp))
    (hper k)

/-- The smoothness of the spatial jet `x ↦ (seriesFunM c x, ∂ seriesFunM c x, ∂² seriesFunM c x)`. -/
private lemma jetM_contDiff {n : ℕ} (c : (Fin n → ℤ) → MatC n)
    (hmom : ∀ (i j : Fin n) (M : ℕ),
      Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ M * ‖c k i j‖)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => jetM (seriesFunM c) x) := by
  have hval : ∀ i j : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x => seriesFunM c x i j) :=
    fun i j => (contDiff_pi.mp (contDiff_pi.mp (seriesFunM_contDiff c hmom) i)) j
  have h0 : ContDiff ℝ (⊤ : ℕ∞) (fun x => seriesFunM c x) := seriesFunM_contDiff c hmom
  have h1 : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => fun c' : Fin n => pdM c' (seriesFunM c) x) :=
    contDiff_pi.mpr (fun c' => contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j =>
      pd_contDiff_top (hval i j) c')))
  have h2 : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => fun c' d : Fin n => pdM c' (pdM d (seriesFunM c)) x) :=
    contDiff_pi.mpr (fun c' => contDiff_pi.mpr (fun d => contDiff_pi.mpr (fun i =>
      contDiff_pi.mpr (fun j => pd_contDiff_top (pd_contDiff_top (hval i j) d) c'))))
  have h3 : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => (seriesFunM c x, (fun c' : Fin n => pdM c' (seriesFunM c) x,
        fun c' d : Fin n => pdM c' (pdM d (seriesFunM c)) x))) := h0.prodMk (h1.prodMk h2)
  simpa only [jetM] using h3

/-- The smoothness of the value-and-first-jet map `x ↦ (seriesFunM c x, ∂ seriesFunM c x)`. -/
private lemma jetP_contDiff {n : ℕ} (c : (Fin n → ℤ) → MatC n)
    (hmom : ∀ (i j : Fin n) (M : ℕ),
      Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ M * ‖c k i j‖)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => jetP c x) := by
  have hval : ∀ i j : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x => seriesFunM c x i j) :=
    fun i j => (contDiff_pi.mp (contDiff_pi.mp (seriesFunM_contDiff c hmom) i)) j
  have h0 : ContDiff ℝ (⊤ : ℕ∞) (fun x => seriesFunM c x) := seriesFunM_contDiff c hmom
  have h1 : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => fun a : Fin n => fun i j : Fin n =>
        Work.Diff.STE.pd a (fun y => seriesFunM c y i j) x) :=
    contDiff_pi.mpr (fun a => contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j =>
      pd_contDiff_top (hval i j) a)))
  have h3 : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => (seriesFunM c x,
        fun a i j : Fin n => Work.Diff.STE.pd a (fun y => seriesFunM c y i j) x)) :=
    h0.prodMk h1
  simpa only [jetP] using h3

/-- The symmetrised inverse metric of a periodic Fourier series is periodic. -/
private lemma periodic_symInvC {n : ℕ} (c : (Fin n → ℤ) → MatC n) (a b : Fin n) :
    Periodic1 (symInvC c a b) := by
  intro k x
  simp only [symInvC_apply, symInvR_apply]
  rw [periodic_seriesFunM c k x]

/-- `jetP` is periodic. -/
private lemma periodic_jetP {n : ℕ} (c : (Fin n → ℤ) → MatC n)
    (hval : ∀ i j : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x => seriesFunM c x i j)) :
    Periodic1 (jetP c) := by
  intro k x
  rw [show jetP c (x + Pi.single k 1)
        = (seriesFunM c (x + Pi.single k 1),
            fun a i j : Fin n => Work.Diff.STE.pd a (fun y => seriesFunM c y i j)
              (x + Pi.single k 1)) from rfl]
  rw [show jetP c x
        = (seriesFunM c x,
            fun a i j : Fin n => Work.Diff.STE.pd a (fun y => seriesFunM c y i j) x) from rfl]
  rw [Prod.mk.injEq]
  constructor
  · exact periodic_seriesFunM c k x
  · funext a i j
    exact periodic_pd_of_contDiff (hval i j) (periodic_seriesFunM_apply c i j) a k x

theorem Phi_decomp_smooth {n : ℕ}
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (N : (Fin n → ℝ) × (Work.Diff.STE.Flat.MatC n × (Fin n → Work.Diff.STE.Flat.MatC n))
      → Work.Diff.STE.Flat.MatC n)
    (hdec : ∀ (x : Fin n → ℝ) (A : Work.Diff.STE.Flat.MatC n)
        (L : Fin n → Work.Diff.STE.Flat.MatC n)
        (B : Fin n → Fin n → Work.Diff.STE.Flat.MatC n),
        (Work.Diff.STE.Flat.reMat A).det ≠ 0 →
          Φ (x, (A, L, B)) = Work.Diff.STE.Flat.secOpFlat A B + N (x, (A, L)))
    (hNsm : ContDiffOn ℝ (⊤ : ℕ∞) N (Set.univ ×ˢ
        {w : Work.Diff.STE.Flat.MatC n × (Fin n → Work.Diff.STE.Flat.MatC n)
          | (Work.Diff.STE.Flat.reMat w.1).det ≠ 0}))
    (hNper : ∀ w : Work.Diff.STE.Flat.MatC n × (Fin n → Work.Diff.STE.Flat.MatC n),
        Work.Diff.STE.Periodic1 (fun x : Fin n → ℝ => N (x, w)))
    (hΦsm : ContDiffOn ℝ (⊤ : ℕ∞) Φ (Set.univ ×ˢ
        {w : Work.Diff.STE.Flat.Jet n | (Work.Diff.STE.Flat.reMat w.1).det ≠ 0}))
    {c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n} {lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
      lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
        Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) i j * v i * v j)
    (hmom : ∀ (i j : Fin n) (M : ℕ),
      Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ M * ‖c k i j‖)) :
    (∀ (x : Fin n → ℝ) (i j : Fin n),
        Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM c) x) i j
          = (∑ a, ∑ b, Work.Diff.STE.flat.symInvC c a b x
              * Work.Diff.STE.pd a (Work.Diff.STE.pd b
                  (fun y => Work.Diff.STE.Flat.seriesFunM c y i j)) x)
            + N (x, Work.Diff.STE.flat.jetP c x) i j) ∧
    (∀ (i j : Fin n), ContDiff ℝ (⊤ : ℕ∞)
        (fun x => Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM c) x) i j)) ∧
    (∀ (i j : Fin n), Work.Diff.STE.Periodic1
        (fun x => Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM c) x) i j)) := by
  classical
  have hdet : ∀ x : Fin n → ℝ, (reMat (seriesFunM c x)).det ≠ 0 :=
    fun x => det_ne_zero_of_quadForm_le _ hlam (hell x)
  have hval : ∀ i j : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x => seriesFunM c x i j) :=
    fun i j => (contDiff_pi.mp (contDiff_pi.mp (seriesFunM_contDiff c hmom) i)) j
  -- the pointwise decomposition
  have hP1 : ∀ (x : Fin n → ℝ) (i j : Fin n),
      Φ (x, jetM (seriesFunM c) x) i j
        = (∑ a, ∑ b, symInvC c a b x
            * Work.Diff.STE.pd a (Work.Diff.STE.pd b (fun y => seriesFunM c y i j)) x)
          + N (x, jetP c x) i j := by
    intro x i j
    have hBu : ∀ a b : Fin n,
        pdM a (pdM b (seriesFunM c)) x = pdM b (pdM a (seriesFunM c)) x := by
      intro a b
      funext p q
      simp only [pdM]
      exact Work.Diff.STE.cm_pd_comm_at ((hval p q).of_le (by simp)).contDiffAt a b
    have hsec : secOpFlat (seriesFunM c x)
        (fun a b => pdM a (pdM b (seriesFunM c)) x) i j
        = ∑ a, ∑ b, symInvC c a b x
            * Work.Diff.STE.pd a (Work.Diff.STE.pd b (fun y => seriesFunM c y i j)) x := by
      rw [secOpFlat_eq_symInvR c _ hBu x i j]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      simp only [symInvC_apply, symInvR_apply, pdM]
    rw [show jetM (seriesFunM c) x
          = (seriesFunM c x, (fun a => pdM a (seriesFunM c) x,
              fun a b => pdM a (pdM b (seriesFunM c)) x)) from rfl]
    rw [hdec x (seriesFunM c x) (fun a => pdM a (seriesFunM c) x)
          (fun a b => pdM a (pdM b (seriesFunM c)) x) (hdet x)]
    simp only [Pi.add_apply]
    rw [hsec]
    rw [show jetP c x = (seriesFunM c x, fun a => pdM a (seriesFunM c) x) from rfl]
  refine ⟨hP1, ?_, ?_⟩
  · -- smoothness
    intro i j
    have hf : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Fin n → ℝ => (x, jetM (seriesFunM c) x)) :=
      (contDiff_id : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => x)).prodMk
        (jetM_contDiff c hmom)
    have hmem : ∀ x : Fin n → ℝ, (x, jetM (seriesFunM c) x)
        ∈ Set.univ ×ˢ {w : Jet n | (reMat w.1).det ≠ 0} := by
      intro x
      exact ⟨Set.mem_univ x, hdet x⟩
    have hcomp := hΦsm.comp_contDiff hf hmem
    exact contDiff_pi.mp (contDiff_pi.mp hcomp i) j
  · -- periodicity
    intro i j
    intro k x
    change Φ (x + Pi.single k 1, jetM (seriesFunM c) (x + Pi.single k 1)) i j
      = Φ (x, jetM (seriesFunM c) x) i j
    have hsumper : (∑ a, ∑ b, symInvC c a b (x + Pi.single k 1)
          * Work.Diff.STE.pd a (Work.Diff.STE.pd b (fun y => seriesFunM c y i j))
              (x + Pi.single k 1))
        = (∑ a, ∑ b, symInvC c a b x
          * Work.Diff.STE.pd a (Work.Diff.STE.pd b (fun y => seriesFunM c y i j)) x) := by
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [periodic_symInvC c a b k x,
        periodic_pd_of_contDiff (pd_contDiff_top (hval i j) b)
          (periodic_pd_of_contDiff (hval i j) (periodic_seriesFunM_apply c i j) b) a k x]
    have hNj : N (x + Pi.single k 1, jetP c (x + Pi.single k 1)) i j
        = N (x, jetP c x) i j := by
      rw [periodic_jetP c hval k x]
      exact congrFun (congrFun (hNper (jetP c x) k x) i) j
    rw [hP1 (x + Pi.single k 1) i j, hP1 x i j, hsumper, hNj]

end Work.Diff.STE.flat
