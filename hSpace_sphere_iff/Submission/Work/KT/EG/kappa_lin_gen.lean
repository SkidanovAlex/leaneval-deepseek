import Mathlib
import Submission.Work.KT.EG.kappaRedDefs
import Submission.Work.KT.EG.kappa_abs
import Submission.Work.KT.EG.kappa_lin_defs
import Submission.Work.KT.Fund.spectral_split_out
import Submission.Work.KT.Fund.kappa_mul
import Submission.Work.KT.Fund.kappa_const
import Submission.Work.KT.Fund.kappa_homotopic
import Submission.Work.KT.Fund.kappa_one
import Submission.Work.KT.Fund.isUnit_matrix_forall
import Submission.Work.KT.Fund.kl_defs
import Submission.Work.KT.Fund.kl_alg
import Submission.Work.KT.Fund.kl_v_cls
import Submission.Work.KT.Fund.kl_w_cls
import Submission.Work.KT.Fund.klV_unit
import Submission.Work.KT.Fund.klW_unit
import Submission.Work.KT.EG.KLG.linBig_defs
import Submission.Work.KT.EG.KLG.exists_t0_unit
import Submission.Work.KT.EG.KLG.isUnit_mobius_family
import Submission.Work.KT.EG.KLG.kappa_bott_gen
import Submission.Work.KT.EG.KLG.cls_one_sum
import Submission.Work.KT.EG.KLG.isUnit_linBig
import Submission.Work.KT.EG.KLG.linBig_slices

namespace Work.KT.EG

open Matrix

noncomputable section

set_option linter.unusedSectionVars false


/-! ## Elementary `K₀` bookkeeping -/

/-- The left unit law of a product with the defining property of the `K₀`-product. -/
lemma one_left_gen {A : Type} [Ring A] (hcomm : ∀ x y : A, x * y = y * x)
    {μ : Work.KT.K0 A →+ Work.KT.K0 A →+ Work.KT.K0 A} (hμ : Work.KT.IsK0Mul μ)
    (x : Work.KT.K0 A) : μ (Work.KT.cls (Work.KT.Mat.one A 1)) x = x := by
  obtain ⟨μ0, hμ0, -, -, hunit0⟩ := Work.KT.k0_basic.1 A hcomm
  rw [IsK0Mul.eq hcomm hμ hμ0, hunit0 x]

/-- `cls (Mat.one C(X × S²,ℂ) n) = fst*(cls ⟨n,1-E⟩) + fst*(cls ⟨n,E⟩)`. -/
lemma cls_one_fst (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] {n : ℕ}
    (E : Matrix (Fin n) (Fin n) C(X, ℂ)) (hE : E * E = E) :
    Work.KT.cls (Work.KT.Mat.one C(X × S2, ℂ) n)
      = fstStar X (Work.KT.cls (⟨n, 1 - E⟩ : Work.KT.Mat C(X, ℂ)))
        + fstStar X (Work.KT.cls (⟨n, E⟩ : Work.KT.Mat C(X, ℂ))) := by
  have h := congrArg (fstStar X) (KLG.cls_one_sum X n E hE)
  rw [map_add] at h
  rw [fstStar_cls_one X n] at h
  exact h

lemma pullMat_mul {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Work.KT.Fund.pullMat X (M * N)
      = Work.KT.Fund.pullMat X M * Work.KT.Fund.pullMat X N :=
  Work.KT.Fund.klP_mul X M N

lemma pullMat_one' {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] {n : ℕ} :
    Work.KT.Fund.pullMat X (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) = 1 :=
  Work.KT.Fund.klP_one X

/-! ## Pointwise evaluation of a linear clutching function -/

lemma eval_pullMat {Y : Type} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) C(Y, ℂ)) (q : Y × Sph ℂ) :
    (Work.KT.Fund.pullMat Y M).map (fun f => f q) = M.map (fun f => f q.1) := by
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply, Work.KT.Fund.pullMat_apply]

/-- Pointwise evaluation of `z • pullMat a + pullMat b`. -/
lemma eval_lin {Y : Type} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] {n : ℕ}
    (a b : Matrix (Fin n) (Fin n) C(Y, ℂ)) (q : Y × Sph ℂ) :
    ((((Work.KT.zUnit Y : C(Y × Sph ℂ, ℂ)) • Work.KT.Fund.pullMat Y a)
        + Work.KT.Fund.pullMat Y b).map (fun f => f q))
      = ((q.2 : ℂ)) • (a.map (fun f => f q.1)) + b.map (fun f => f q.1) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Work.KT.zUnit_apply,
    Work.KT.Fund.pullMat_apply, ContinuousMap.add_apply, ContinuousMap.mul_apply, smul_eq_mul]

/-- The pointwise invertibility of a linear clutching unit. -/
lemma unit_pointwise {Y : Type} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] {n : ℕ}
    (a b : Matrix (Fin n) (Fin n) C(Y, ℂ))
    (u : (Matrix (Fin n) (Fin n) C(Y × Sph ℂ, ℂ))ˣ)
    (hu : (u : Matrix (Fin n) (Fin n) C(Y × Sph ℂ, ℂ))
      = (Work.KT.zUnit Y : C(Y × Sph ℂ, ℂ)) • Work.KT.Fund.pullMat Y a
        + Work.KT.Fund.pullMat Y b)
    (x : Y) (z : ℂ) (hz : ‖z‖ = 1) :
    IsUnit (z • (a.map (fun f => f x)) + b.map (fun f => f x)) := by
  obtain ⟨v, hv⟩ : ∃ v : Sph ℂ, (v : ℂ) = z :=
    ⟨⟨z, by rwa [Metric.mem_sphere, dist_eq_norm, sub_zero]⟩, rfl⟩
  have hunit : IsUnit (u : Matrix (Fin n) (Fin n) C(Y × Sph ℂ, ℂ)) := u.isUnit
  rw [Work.KT.Fund.isUnit_matrix_forall (X := Y × Sph ℂ) n] at hunit
  have hq := hunit (x, v)
  have hq' : ((u : Matrix (Fin n) (Fin n) C(Y × Sph ℂ, ℂ)).map (fun f => f (x, v)))
      = z • (a.map (fun f => f x)) + b.map (fun f => f x) := by
    rw [hu]
    simpa only [hv] using eval_lin a b (x, v)
  rwa [hq'] at hq

/-! ## `bottZ` versus `gammaHopf` -/

/-- `bottZ X = gammaHopf X - [1]`, from the Bott formula applied at `E = 1`. -/
lemma bottZ_eq (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    bottZ X = gammaHopf X - Work.KT.cls (Work.KT.Mat.one C(X × S2, ℂ) 1) := by
  have hz0 : Work.KT.cls (⟨1, (0 : Matrix (Fin 1) (Fin 1) C(X, ℂ))⟩ : Work.KT.Mat C(X, ℂ)) = 0 := by
    have h := KLG.cls_one_sum X 1 (1 : Matrix (Fin 1) (Fin 1) C(X, ℂ)) (by simp)
    rw [sub_self] at h
    have h2 : Work.KT.cls (⟨1, (0 : Matrix (Fin 1) (Fin 1) C(X, ℂ))⟩ : Work.KT.Mat C(X, ℂ))
        + Work.KT.cls (Work.KT.Mat.one C(X, ℂ) 1)
        = 0 + Work.KT.cls (Work.KT.Mat.one C(X, ℂ) 1) := by
      rw [zero_add]
      exact h.symm
    exact add_right_cancel h2
  have hone : Work.KT.Fund.pullMat X (1 : Matrix (Fin 1) (Fin 1) C(X, ℂ)) = 1 := by
    ext i j p
    fin_cases i; fin_cases j
    simp [Work.KT.Fund.pullMat_apply, Matrix.one_apply]
  have hz : (Work.KT.Fund.zUnitMat X : Matrix (Fin 1) (Fin 1) C(X × Sph ℂ, ℂ))
      = Work.KT.Fund.pullMat X (1 - (1 : Matrix (Fin 1) (Fin 1) C(X, ℂ)))
        + (Work.KT.zUnit X : C(X × Sph ℂ, ℂ))
          • Work.KT.Fund.pullMat X (1 : Matrix (Fin 1) (Fin 1) C(X, ℂ)) := by
    rw [sub_self, hone]
    ext i j p
    fin_cases i; fin_cases j
    simp [Work.KT.Fund.zUnitMat, Matrix.smul_apply, Matrix.one_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply, Matrix.add_apply, Matrix.zero_apply]
  obtain ⟨μ0, hμ0, -, -, -⟩ := Work.KT.k0_basic.1 (C(X × S2, ℂ)) (fun x y => mul_comm x y)
  have hkb := KLG.kappa_bott_gen X 1 1 (by simp) (Work.KT.Fund.zUnitMat X) hz μ0 hμ0
  rw [sub_self] at hkb
  rw [hz0, map_zero, zero_add] at hkb
  rw [show Work.KT.cls (⟨1, (1 : Matrix (Fin 1) (Fin 1) C(X, ℂ))⟩ : Work.KT.Mat C(X, ℂ))
      = Work.KT.cls (Work.KT.Mat.one C(X, ℂ) 1) from rfl] at hkb
  rw [fstStar_cls_one X 1] at hkb
  rw [one_left_gen (A := C(X × S2, ℂ)) (fun x y => mul_comm x y) hμ0] at hkb
  rw [bottZ, redK, hkb]

/-- **The `a = 1` case**: for a unit `w` over the circle with `↑w = z • 1 + pullMat b`, the reduced
clutched class is a `K(X,ℂ)`-multiple of `bottZ`. -/
lemma redK_one_lin (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] {n : ℕ}
    (b : Matrix (Fin n) (Fin n) C(X, ℂ))
    (w : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (hw : (w : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = (Work.KT.zUnit X : C(X × Sph ℂ, ℂ)) • (1 : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
        + Work.KT.Fund.pullMat X b)
    (μ : Work.KT.K0 C(X × S2, ℂ) →+ Work.KT.K0 C(X × S2, ℂ) →+ Work.KT.K0 C(X × S2, ℂ))
    (hμ : Work.KT.IsK0Mul μ) :
    ∃ b' : Work.KT.K0 C(X, ℂ),
      redK X n w = μ (fstStar X b') (bottZ X) := by
  have hb : ∀ (x : X) (z : ℂ), ‖z‖ = 1 →
      IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ) + b.map (fun f => f x)) := by
    intro x z hz
    have hone : Work.KT.Fund.pullMat X (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) = 1 := by
      ext i j p
      by_cases hij : i = j <;> simp [Work.KT.Fund.pullMat_apply, Matrix.one_apply, hij]
    have hw' : (w : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
        = (Work.KT.zUnit X : C(X × Sph ℂ, ℂ))
            • Work.KT.Fund.pullMat X (1 : Matrix (Fin n) (Fin n) C(X, ℂ))
          + Work.KT.Fund.pullMat X b := by
      rw [hone]; exact hw
    have h := unit_pointwise (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) b w hw' x z hz
    rwa [Matrix.map_one _ (by simp) (by simp)] at h
  obtain ⟨E, hE, hc, hins, hout, -⟩ := Work.KT.Fund.spectral_split_out X n b hb
  have hv : IsUnit (Work.KT.Fund.klV X n b E) := (Work.KT.Fund.klV_unit X n b E hE hc hins).1
  have hv0 : IsUnit (Work.KT.Fund.klV0 X n E) := (Work.KT.Fund.klV_unit X n b E hE hc hins).2
  have hwk : IsUnit (Work.KT.Fund.klW X n b E) := Work.KT.Fund.klW_unit X n b E hE hc hout
  let v : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ := hv.unit
  let v0 : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ := hv0.unit
  let wk : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ := hwk.unit
  have hvc : (v : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) = Work.KT.Fund.klV X n b E :=
    IsUnit.unit_spec hv
  have hv0c : (v0 : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) = Work.KT.Fund.klV0 X n E :=
    IsUnit.unit_spec hv0
  have hwkc : (wk : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) = Work.KT.Fund.klW X n b E :=
    IsUnit.unit_spec hwk
  have hkappa_v : Work.KT.Fund.kappa X n v = Work.KT.Fund.kappa X n v0 :=
    Work.KT.Fund.kl_v_cls X n b E hE hc hins v hvc v0 hv0c
  have hkappa_wk : Work.KT.Fund.kappa X n wk
      = Work.KT.cls (Work.KT.Mat.one C(X × S2, ℂ) n) :=
    Work.KT.Fund.kl_w_cls X n b E hE hc hout wk hwkc
  have hcomm : (v : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
        * (wk : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = (wk : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
        * (v : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
    rw [hvc, hwkc]
    exact Work.KT.Fund.kl_factor_comm X b E hE hc
  have huw : w = v * wk := by
    refine Units.ext ?_
    rw [Units.val_mul, hvc, hwkc, Work.KT.Fund.kl_factor X b E hE hc, hw]
    unfold Work.KT.Fund.klz Work.KT.Fund.klP
    rfl
  have hkappa_w : Work.KT.Fund.kappa X n w = Work.KT.Fund.kappa X n v0 := by
    have hkm := Work.KT.Fund.kappa_mul X n v wk hcomm
    calc Work.KT.Fund.kappa X n w = Work.KT.Fund.kappa X n (v * wk) := by rw [huw]
      _ = Work.KT.Fund.kappa X n v + Work.KT.Fund.kappa X n wk
            - Work.KT.cls (Work.KT.Mat.one C(X × S2, ℂ) n) := hkm
      _ = Work.KT.Fund.kappa X n v0 := by rw [hkappa_v, hkappa_wk]; abel
  have hv0val : (v0 : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = Work.KT.Fund.pullMat X (1 - E) + (Work.KT.zUnit X : C(X × Sph ℂ, ℂ))
          • Work.KT.Fund.pullMat X E := by
    rw [hv0c]
    show Work.KT.Fund.klz X • Work.KT.Fund.klP X E + (1 - Work.KT.Fund.klP X E)
      = Work.KT.Fund.pullMat X (1 - E) + (Work.KT.zUnit X : C(X × Sph ℂ, ℂ))
          • Work.KT.Fund.pullMat X E
    have hsub : (1 : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) - Work.KT.Fund.klP X E
        = Work.KT.Fund.klP X (1 - E) := by
      rw [← Work.KT.Fund.klP_one (X := X) (n := n)]
      exact (Work.KT.Fund.klP_sub X (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) E).symm
    rw [hsub, add_comm]
    unfold Work.KT.Fund.klz Work.KT.Fund.klP
    rfl
  have hkb := KLG.kappa_bott_gen X n E hE v0 hv0val μ hμ
  refine ⟨Work.KT.cls (⟨n, E⟩ : Work.KT.Mat C(X, ℂ)), ?_⟩
  unfold redK
  rw [hkappa_w, hkb, cls_one_fst X E hE]
  have hsub : μ (fstStar X (Work.KT.cls (⟨n, E⟩ : Work.KT.Mat C(X, ℂ)))) (gammaHopf X)
      - fstStar X (Work.KT.cls (⟨n, E⟩ : Work.KT.Mat C(X, ℂ)))
      = μ (fstStar X (Work.KT.cls (⟨n, E⟩ : Work.KT.Mat C(X, ℂ))))
          (gammaHopf X - Work.KT.cls (Work.KT.Mat.one C(X × S2, ℂ) 1)) := by
    rw [map_sub]
    congr 1
    exact (IsK0Mul.one_right (fun a b : C(X × S2, ℂ) => mul_comm a b) hμ _).symm
  have habel : fstStar X (Work.KT.cls (⟨n, 1 - E⟩ : Work.KT.Mat C(X, ℂ)))
        + μ (fstStar X (Work.KT.cls (⟨n, E⟩ : Work.KT.Mat C(X, ℂ)))) (gammaHopf X)
        - (fstStar X (Work.KT.cls (⟨n, 1 - E⟩ : Work.KT.Mat C(X, ℂ)))
          + fstStar X (Work.KT.cls (⟨n, E⟩ : Work.KT.Mat C(X, ℂ))))
      = μ (fstStar X (Work.KT.cls (⟨n, E⟩ : Work.KT.Mat C(X, ℂ)))) (gammaHopf X)
        - fstStar X (Work.KT.cls (⟨n, E⟩ : Work.KT.Mat C(X, ℂ))) := by abel
  rw [habel, hsub, bottZ_eq X]

/-- **The general linear clutching function is a Bott multiple.** For matrices `a`, `b` over
`C(X, ℂ)` and a unit `u` whose values are `z • pullMat a + pullMat b` (a *linear* clutching
function), the reduced clutched class is a `K(X, ℂ)`-multiple of `bottZ = κ(z) - [1]`:
`redK X n u = μ (fstStar X b') (bottZ X)` for some `b'`. -/
theorem kappa_lin_gen (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (n : ℕ)
    (a b : Matrix (Fin n) (Fin n) C(X, ℂ))
    (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (hu : (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = (Work.KT.zUnit X : C(X × Sph ℂ, ℂ)) • Work.KT.Fund.pullMat X a
        + Work.KT.Fund.pullMat X b)
    (μ : Work.KT.K0 C(X × S2, ℂ) →+ Work.KT.K0 C(X × S2, ℂ) →+ Work.KT.K0 C(X × S2, ℂ))
    (hμ : Work.KT.IsK0Mul μ) :
    ∃ b' : Work.KT.K0 C(X, ℂ),
      Work.KT.EG.redK X n u = μ (Work.KT.EG.fstStar X b') (Work.KT.EG.bottZ X) := by
  have hub : ∀ (x : X) (z : ℂ), ‖z‖ = 1 →
      IsUnit (z • (a.map (fun f => f x)) + b.map (fun f => f x)) :=
    fun x z hz => unit_pointwise a b u hu x z hz
  have hab : IsUnit (a + b) := by
    rw [Work.KT.Fund.isUnit_matrix_forall (X := X) n]
    intro x
    have h := hub x 1 (by norm_num)
    have h1 : (a + b).map (fun f => f x)
        = (1 : ℂ) • (a.map (fun f => f x)) + b.map (fun f => f x) := by
      rw [Matrix.map_add _ (fun p q => rfl) _ _, one_smul]
    rw [h1]; exact h
  obtain ⟨t₀, ht0, ht1, hc⟩ := KLG.exists_t0_unit X n a b hab
  have hBig : IsUnit (KLG.linBig X a b t₀) := KLG.isUnit_linBig X a b t₀ ht0 ht1 hub
  let H : (Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))ˣ := hBig.unit
  have hH : (H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))
      = KLG.linBig X a b t₀ := IsUnit.unit_spec hBig
  have hslice := KLG.linBig_slices X a b t₀
  have h1unit : IsUnit ((Work.KT.zUnit X : C(X × Sph ℂ, ℂ))
      • Work.KT.Fund.pullMat X (a + t₀ • b) + Work.KT.Fund.pullMat X (t₀ • a + b)) := by
    have hmap : IsUnit ((KLG.linBig X a b t₀).map
        (fun f => f.comp (Work.KT.Fund.incl1 X))) :=
      Work.KT.Fund.isUnit_map_comp (Work.KT.Fund.incl1 X) hBig
    rwa [hslice.2] at hmap
  let u₁ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ := h1unit.unit
  have hu₁ : (u₁ : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = (Work.KT.zUnit X : C(X × Sph ℂ, ℂ)) • Work.KT.Fund.pullMat X (a + t₀ • b)
        + Work.KT.Fund.pullMat X (t₀ • a + b) := IsUnit.unit_spec h1unit
  have hs0 : ((H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ)).map
      (fun f => f.comp (Work.KT.Fund.incl0 X))) = (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
    rw [hH, hslice.1, ← hu]
  have hs1 : ((H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ)).map
      (fun f => f.comp (Work.KT.Fund.incl1 X))) = (u₁ : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
    rw [hH, hslice.2, ← hu₁]
  have hκ : Work.KT.Fund.kappa X n u = Work.KT.Fund.kappa X n u₁ :=
    Work.KT.Fund.kappa_homotopic X n u u₁ H hs0 hs1
  obtain ⟨c, hcval⟩ := hc
  have hcval' : (c : Matrix (Fin n) (Fin n) C(X, ℂ)) = a + t₀ • b := hcval
  let cM : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ :=
    Units.map (Work.KT.Fund.KC.pullHomM X n) (c⁻¹)
  have hcM : (cM : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = Work.KT.Fund.pullMat X (↑(c⁻¹) : Matrix (Fin n) (Fin n) C(X, ℂ)) := by
    change Work.KT.Fund.KC.pullHomM X n (↑(c⁻¹) : Matrix (Fin n) (Fin n) C(X, ℂ))
      = Work.KT.Fund.pullMat X (↑(c⁻¹) : Matrix (Fin n) (Fin n) C(X, ℂ))
    rw [Work.KT.Fund.KC.pullMat_eq_pullHomM]
  let w₂ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ := cM * u₁
  have hw₂ : (w₂ : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = (Work.KT.zUnit X : C(X × Sph ℂ, ℂ)) • (1 : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
        + Work.KT.Fund.pullMat X
            ((↑(c⁻¹) : Matrix (Fin n) (Fin n) C(X, ℂ)) * (t₀ • a + b)) := by
    rw [show w₂ = cM * u₁ from rfl, Units.val_mul, hcM, hu₁, mul_add, mul_smul_comm,
      ← pullMat_mul, ← hcval', Units.inv_mul, pullMat_one', ← pullMat_mul]
  have hu₁' : (u₁ : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = Work.KT.Fund.pullMat X (c : Matrix (Fin n) (Fin n) C(X, ℂ))
        * (w₂ : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
    rw [hw₂, hu₁, mul_add, mul_smul_comm, mul_one, ← pullMat_mul, ← mul_assoc,
      Units.mul_inv, one_mul, ← hcval']
  have hκabs : Work.KT.Fund.kappa X n u₁ = Work.KT.Fund.kappa X n w₂ :=
    Work.KT.EG.kappa_abs X n c w₂ u₁ hu₁'
  have hred : Work.KT.EG.redK X n u = Work.KT.EG.redK X n w₂ := by
    unfold Work.KT.EG.redK
    rw [hκ.trans hκabs]
  obtain ⟨b', hb'⟩ := redK_one_lin X
    ((↑(c⁻¹) : Matrix (Fin n) (Fin n) C(X, ℂ)) * (t₀ • a + b)) w₂ hw₂ μ hμ
  exact ⟨b', hred.trans hb'⟩

end

end Work.KT.EG
