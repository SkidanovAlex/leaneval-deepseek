import Mathlib
import Submission.Work.WilE9G.Lagrange.DegenSetup
import Submission.Work.WilE9G.Lagrange.Stratum
import Submission.Work.WilE9G.Lagrange.degen_kernel_defs
import Submission.Work.WilE9G.Lagrange.dgCoef_single_eq_lagJacTrue
import Submission.Work.WilE5.Strat.flatConormalTools

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE9G.Lagrange
open WilkiesDesign WilkiesDesign.E Work.WilE9G

variable {n m : ℕ}

/-! ## Auxiliary lemmas

`degenF S` is the projection to the `(x, c)`-coordinates; `emb` is the embedding of the reduced
variables `(yt, ν)`.  The lemmas below compute `degenF` on `emb`, invert `fderiv degenF`, and
identify `dgH` on `emb` with `lagJacTrue` acting by `mulVec`. -/

/-- `degenF` vanishes on the image of `emb`. -/
theorem degenF_emb_zero (S : AmbStratum (n + (1 + m)))
    (u : Fin ((1 + m) + (S.j + 1)) → ℝ) : degenF S (emb n m u) = 0 := by
  funext k
  revert k
  refine Fin.addCases ?_ ?_
  · intro i
    simp only [degenF, Fin.append_left, projBase, degenZ_apply_k, Pi.zero_apply]
    exact emb_apply_of_lt u _ (by rw [degenZK_val, Fin.val_castLE]; exact i.isLt)
  · intro l
    simp only [degenF, Fin.append_right, degenC_apply_k, Pi.zero_apply]
    exact emb_apply_of_ge u _ (by rw [degenCK_val]; omega)

/-- A vector killed by `fderiv degenF` is supported on the reduced coordinates. -/
theorem eq_emb_of_fderiv_degenF_eq_zero (S : AmbStratum (n + (1 + m)))
    (p : Fin (degenDim n m S.j) → ℝ) (v : Fin (degenDim n m S.j) → ℝ)
    (h : fderiv ℝ (degenF S) p v = 0) :
    v = emb n m (fun col => v (degenColK n m (j := S.j) col)) := by
  rw [fderiv_degenF, dgF_eq_degenF] at h
  refine eq_emb_of_supported v ?_ ?_
  · intro i
    have hc := congrFun h (Fin.castAdd (1 + m) i)
    rwa [degenF, Fin.append_left, projBase, degenZ_apply_k, Pi.zero_apply] at hc
  · intro l
    have hc := congrFun h (Fin.natAdd n l)
    rwa [degenF, Fin.append_right, degenC_apply_k, Pi.zero_apply] at hc

/-- Linearity of `dgCoef ·` on the image of `emb`. -/
theorem dgCoef_emb (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) (r : Fin (S.j + (1 + (1 + m))))
    (u : Fin ((1 + m) + (S.j + 1)) → ℝ) :
    dgCoef S Phi p r (emb n m u)
      = ∑ col : Fin ((1 + m) + (S.j + 1)),
          dgCoef S Phi p r (Pi.single (degenColK n m (j := S.j) col) 1) * u col := by
  rw [emb, map_sum]
  refine Finset.sum_congr rfl (fun col _ => ?_)
  rw [map_smul, smul_eq_mul, mul_comm]

/-- The entry comparison of `dgH ∘ emb` with `lagJacTrue · mulVec`. -/
theorem dgH_emb_apply_mulVec (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (p : Fin (degenDim n m S.j) → ℝ)
    (u : Fin ((1 + m) + (S.j + 1)) → ℝ) (r : Fin ((1 + m) + (S.j + 1))) :
    dgH S Phi p (emb n m u) (degenRowInv m (j := S.j) r)
      = (lagJacTrue S Phi (degenC p) (degenZ p)
          (fun a => degenNu p (Fin.castAdd 1 a))
          (degenNu p (Fin.last S.j))).mulVec u r := by
  have hentry : ∀ col : Fin ((1 + m) + (S.j + 1)),
      dgCoef S Phi p (degenRowInv m (j := S.j) r)
          (Pi.single (degenColK n m (j := S.j) col) 1)
        = (lagJacTrue S Phi (degenC p) (degenZ p)
            (fun a => degenNu p (Fin.castAdd 1 a))
            (degenNu p (Fin.last S.j))) r col := by
    intro col
    exact congrFun (congrFun (dgCoef_single_eq_lagJacTrue S Phi p) r) col
  rw [dgH_apply, dgCoef_emb, Matrix.mulVec_apply_eq_sum]
  refine Finset.sum_congr rfl (fun col _ => ?_)
  rw [hentry col]

/-- `dgH` vanishes on the image of `emb` exactly when `lagJacTrue` kills `u`. -/
theorem dgH_emb_eq_zero_iff (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (p : Fin (degenDim n m S.j) → ℝ)
    (u : Fin ((1 + m) + (S.j + 1)) → ℝ) :
    dgH S Phi p (emb n m u) = 0
      ↔ (lagJacTrue S Phi (degenC p) (degenZ p)
          (fun a => degenNu p (Fin.castAdd 1 a))
          (degenNu p (Fin.last S.j))).mulVec u = 0 := by
  constructor
  · intro h
    funext r
    have hc := congrFun h (degenRowInv m (j := S.j) r)
    rw [dgH_emb_apply_mulVec S Phi p u r, Pi.zero_apply] at hc
    exact hc
  · intro h
    funext r'
    obtain ⟨r, rfl⟩ := degenRowInv_surjective (m := m) (j := S.j) r'
    rw [dgH_emb_apply_mulVec S Phi p u r]
    exact congrFun h r

/-- A square real matrix is nonsingular iff `mulVec` is injective. -/
theorem det_ne_zero_iff_mulVec {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) :
    M.det ≠ 0 ↔ ∀ u, M.mulVec u = 0 → u = 0 := by
  constructor
  · intro h u hu
    by_contra hne
    exact h (Matrix.exists_mulVec_eq_zero_iff.mp ⟨u, hne, hu⟩)
  · intro h hdet
    obtain ⟨u, hne, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    exact hne (h u hu)

/-! ## The main statement -/

theorem degen_kernel_iff {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (Phi : WilkiesDesign.E.EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (Work.WilE9G.Lagrange.degenDim n m S.j) → ℝ) :
    (∀ v : Fin (Work.WilE9G.Lagrange.degenDim n m S.j) → ℝ,
        fderiv ℝ (Work.WilE9G.Lagrange.degenH S Phi) p v = 0 →
        fderiv ℝ (Work.WilE9G.Lagrange.degenF S) p v = 0 → v = 0)
      ↔ (Work.WilE9G.Lagrange.lagJacTrue S Phi (Work.WilE9G.Lagrange.degenC p)
            (Work.WilE9G.Lagrange.degenZ p)
            (fun a => Work.WilE9G.Lagrange.degenNu p (Fin.castAdd 1 a))
            (Work.WilE9G.Lagrange.degenNu p (Fin.last S.j))).det ≠ 0 := by
  constructor
  · intro h
    rw [det_ne_zero_iff_mulVec]
    intro u hu
    have hv : emb n m u = 0 := by
      apply h
      · rw [fderiv_degenH]
        exact (dgH_emb_eq_zero_iff S Phi p u).mpr hu
      · rw [fderiv_degenF, dgF_eq_degenF]
        exact degenF_emb_zero S u
    funext col
    have hc := congrFun hv (degenColK n m (j := S.j) col)
    rwa [emb_apply_colK u col, Pi.zero_apply] at hc
  · intro hne v hv0 hF0
    have hker : ∀ u : Fin ((1 + m) + (S.j + 1)) → ℝ,
        (lagJacTrue S Phi (degenC p) (degenZ p)
          (fun a => degenNu p (Fin.castAdd 1 a))
          (degenNu p (Fin.last S.j))).mulVec u = 0 → u = 0 :=
      (det_ne_zero_iff_mulVec _).mp hne
    set u : Fin ((1 + m) + (S.j + 1)) → ℝ :=
      fun col => v (degenColK n m (j := S.j) col) with hu
    have hv' : v = emb n m u := by
      rw [hu]
      exact eq_emb_of_fderiv_degenF_eq_zero S p v hF0
    have hvH : fderiv ℝ (degenH S Phi) p (emb n m u) = 0 := by
      rw [← hv']
      exact hv0
    rw [fderiv_degenH] at hvH
    have hu0 : u = 0 := hker u ((dgH_emb_eq_zero_iff S Phi p u).mp hvH)
    rw [hv', hu0]
    exact emb_zero

end Work.WilE9G.Lagrange
