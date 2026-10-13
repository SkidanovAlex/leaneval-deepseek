import Mathlib
import Submission.Work.WilE2.KhoGood
import Submission.Work.WilE2.KhoCount
import Submission.Work.WilE2.RolleDetAnalytic
import Submission.Work.WilE2.KhovB
import Submission.Work.WilE2.KhovB_mono
import Submission.Work.WilE2.Jac
import Submission.Work.WilE2.RegSol
import Submission.Work.WilE2.exists_pos_lt_abs_of_isCompact
import Submission.Work.WilE2.exists_delta_lt_abs_avoid_null
import Submission.Work.WilE2.sum_totalDegree_liftedSystem_shift_le

set_option maxHeartbeats 1000000
set_option autoImplicit false

noncomputable section
open Classical
namespace Work.WilE2

open WilkiesDesign WilkiesDesign.E WilkiesConjecture

variable {n s : ℕ}

/-! ## My own helper lemmas -/

/-- The affine exponent `S.ell j` is smooth. -/
private theorem contDiff_ell_aux {n r : ℕ} (S : ESys n r) (j : Fin r) (N : WithTop ℕ∞) :
    ContDiff ℝ N (S.ell j) := by
  rw [show S.ell j = fun x : Fin n → ℝ => (∑ i, S.a j i * x i) + S.b j from by
    funext x; rw [ESys.ell]]
  exact (ContDiff.sum (fun i _ => contDiff_const.mul (contDiff_apply ℝ ℝ i))).add contDiff_const

/-- The evaluation of an EA polynomial along the chain is smooth in the coordinates. -/
private theorem contDiff_ev_gen {n r : ℕ} (S : ESys n r) (P : EPoly n r) (N : WithTop ℕ∞) :
    ContDiff ℝ N (S.ev P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [show S.ev (MvPolynomial.C c) = fun _ : Fin n → ℝ => c from by funext x; simp [ESys.ev]]
      exact contDiff_const
  | add P Q hP hQ =>
      rw [show S.ev (P + Q) = S.ev P + S.ev Q from by funext x; simp [ESys.ev, map_add]]
      exact hP.add hQ
  | mul_X P s hP =>
      rw [show S.ev (P * MvPolynomial.X s) = S.ev P * S.ev (MvPolynomial.X s) from by
        funext x; simp [ESys.ev, map_mul]]
      refine hP.mul ?_
      rcases s with j | j
      · rw [show S.ev (MvPolynomial.X (Sum.inl j)) = fun x : Fin n → ℝ => x j from by
          funext x; simp [ESys.ev]]
        exact contDiff_apply ℝ ℝ j
      · rw [show S.ev (MvPolynomial.X (Sum.inr j)) = S.psi j from by
          funext x; simp [ESys.ev, ESys.psi]]
        exact (Real.contDiff_exp (n := N)).comp (contDiff_ell_aux S j N)

private theorem KhovB_mono_degree : ∀ (r n D D' : ℕ), D ≤ D' → KhovB r n D ≤ KhovB r n D'
  | 0, n, D, D', h => Nat.pow_le_pow_left h n
  | r + 1, n, D, D', h =>
      KhovB_mono_degree r (n + 2) (2 * D + n + 6) (2 * D' + n + 6) (by omega)

private theorem toMatrix_fderiv_eq {m : ℕ} (Φ : (Fin m → ℝ) → (Fin m → ℝ)) (z : Fin m → ℝ) :
    (LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin m))) (fderiv ℝ Φ z).toLinearMap
      = Matrix.of fun i j => fderiv ℝ Φ z (Pi.single j 1) i := by
  ext i j
  rw [LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply]
  rfl

private theorem det_fderiv_eq {m : ℕ} (Φ : (Fin m → ℝ) → (Fin m → ℝ)) (z : Fin m → ℝ) :
    (fderiv ℝ Φ z).det = (Matrix.of fun i j => fderiv ℝ Φ z (Pi.single j 1) i).det := by
  rw [show (fderiv ℝ Φ z).det = LinearMap.det (fderiv ℝ Φ z).toLinearMap from rfl,
    ← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin m)) (fderiv ℝ Φ z).toLinearMap,
    toMatrix_fderiv_eq]

private theorem crossField_sub_const {m : ℕ} (G : (Fin (m + 1) → ℝ) → (Fin m → ℝ)) (y : Fin m → ℝ)
    (z : Fin (m + 1) → ℝ) :
    crossField (fun w => G w - y) z = crossField G z := by
  have htm : ∀ v : Fin (m + 1) → ℝ, tangMatrix (fun w => G w - y) z v = tangMatrix G z v := by
    intro v
    ext i j
    rw [tangMatrix, tangMatrix, Matrix.of_apply, Matrix.of_apply]
    split_ifs with h
    · rw [show (fun w : Fin (m + 1) → ℝ => (G w - y) ⟨(j : ℕ), h⟩)
            = (fun w => G w ⟨(j : ℕ), h⟩ - y ⟨(j : ℕ), h⟩) from by
          funext w; exact Pi.sub_apply (G w) y _]
      rw [fderiv_sub_const]
    · rfl
  funext i
  simp only [crossField]
  rw [htm]

private abbrev khoV (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) (y : Fin n → ℝ) :
    (Fin (n + 1) → ℝ) → (Fin n → ℝ) :=
  fun z => liftSystem S F z - y

private theorem khoV_eq_zero_iff (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) (y : Fin n → ℝ)
    (z : Fin (n + 1) → ℝ) : khoV S F y z = 0 ↔ liftSystem S F z = y :=
  sub_eq_zero

private theorem khoV_crossField (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) (y : Fin n → ℝ)
    (z : Fin (n + 1) → ℝ) :
    crossField (khoV S F y) z = crossField (liftSystem S F) z :=
  crossField_sub_const (liftSystem S F) y z

private theorem khoV_fderiv (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) (y : Fin n → ℝ)
    (a : Fin n) (z : Fin (n + 1) → ℝ) :
    fderiv ℝ (fun w => khoV S F y w a) z = fderiv ℝ (fun w => liftSystem S F w a) z :=
  fderiv_sub_const (y a)

private theorem snoc_lastPsi_eq_self {n s : ℕ} (S : ESys n (s + 1)) (z : Fin (n + 1) → ℝ)
    (hz : rolleg S z = 0) : Fin.snoc (Fin.init z) (S.lastPsi (Fin.init z)) = z := by
  have hz' : z (Fin.last n) = S.lastPsi (Fin.init z) := by
    have h : S.lastPsi (Fin.init z) - z (Fin.last n) = 0 := hz
    linarith
  rw [← hz', Fin.snoc_init_self]

private theorem graph_eval_liftP {n s : ℕ} (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) (i : Fin n)
    (z : Fin (n + 1) → ℝ) (hz : rolleg S z = 0) :
    (S.liftChain).ev (liftP (F i)) z = S.ev (F i) (Fin.init z) := by
  have h := ESys.ev_liftP_lastPsi S (F i) (Fin.init z)
  rw [snoc_lastPsi_eq_self S z hz] at h
  exact h

private theorem rolleDetFun_eq_crossField_of_graph {n s : ℕ} (S : ESys n (s + 1))
    (F : Fin n → EPoly n (s + 1)) (z : Fin (n + 1) → ℝ) (hz : rolleg S z = 0) :
    rolleDetFun S F z = fderiv ℝ (rolleg S) z (crossField (liftSystem S F) z) := by
  have h := ev_rolleDet_eq_crossField S F (Fin.init z)
  rw [snoc_lastPsi_eq_self S z hz] at h
  exact h

private theorem rolleMap_apply_liftedSystem {n s : ℕ} (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
    (z : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    rolleMap S F z i = (S.liftChain).ev (S.liftedSystem F i) z := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [ESys.liftedSystem_last, rolleMap_apply_last]
    rfl
  · rw [ESys.liftedSystem_castSucc, rolleMap_apply_castSucc]
    rfl

private theorem contDiff_liftSystem_aux {n s : ℕ} (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) :
    ContDiff ℝ 2 (liftSystem S F) :=
  contDiff_pi.mpr (fun i => contDiff_ev_gen (S.liftChain) (liftP (F i)) 2)

private theorem contDiff_rolleg_aux {n s : ℕ} (S : ESys n (s + 1)) : ContDiff ℝ 1 (rolleg S) := by
  rw [rolleg_eq_ravel]
  refine ContDiff.sub ?_ ?_
  · rw [show ((S.ravel).psi (Fin.last s) : (Fin (n + 1) → ℝ) → ℝ)
          = (S.ravel).ev (MvPolynomial.X (Sum.inr (Fin.last s))) from by
        funext z; rw [ESys.ev_X_inr]]
    exact contDiff_ev_gen (S.ravel) (MvPolynomial.X (Sum.inr (Fin.last s))) 1
  · exact contDiff_apply ℝ ℝ (Fin.last n)

private theorem continuous_rolleDetFun_aux {n s : ℕ} (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) :
    Continuous (rolleDetFun S F) :=
  (contDiff_ev_gen (S.liftChain) (S.rolleDet F) 1).continuous

private theorem det_fderiv_rolleMap_aux {n s : ℕ} (S : ESys n (s + 1))
    (F : Fin n → EPoly n (s + 1)) (z : Fin (n + 1) → ℝ) :
    (fderiv ℝ (rolleMap S F) z).det =
      (Matrix.of fun i j => (S.liftChain).ev ((S.liftChain).d j (S.liftedSystem F i)) z).det := by
  have hfun : rolleMap S F = fun z i => (S.liftChain).ev (S.liftedSystem F i) z := by
    funext z i
    rw [rolleMap_apply_liftedSystem]
  rw [hfun, det_fderiv_eq (fun z i => (S.liftChain).ev (S.liftedSystem F i) z) z]
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  rw [fderiv_system_apply (S.liftChain) (S.liftedSystem F) z]

private theorem nondegen_shift_aux {n s : ℕ} (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
    (c : Fin (n + 1) → ℝ) (z : Fin (n + 1) → ℝ)
    (hev : ∀ i, (S.liftChain).ev (S.liftedSystem F i) z = c i)
    (hdet : (Matrix.of fun i j => (S.liftChain).ev ((S.liftChain).d j (S.liftedSystem F i)) z).det
      ≠ 0) :
    (S.liftChain).Nondegen (fun i => S.liftedSystem F i + MvPolynomial.C (-(c i))) z := by
  constructor
  · intro i
    have h1 : (S.liftChain).ev (S.liftedSystem F i + MvPolynomial.C (-(c i))) z
        = (S.liftChain).ev (S.liftedSystem F i) z + (-(c i)) := by
      rw [ESys.ev_add, ESys.ev_C]
      rfl
    rw [h1, hev i, add_neg_cancel]
  · rw [show (Matrix.of fun i j => (S.liftChain).ev
          ((S.liftChain).d j (S.liftedSystem F i + MvPolynomial.C (-(c i)))) z)
        = (Matrix.of fun i j => (S.liftChain).ev ((S.liftChain).d j (S.liftedSystem F i)) z) from by
      ext i j
      simp only [Matrix.of_apply]
      rw [ESys.d_add, ESys.d_C, add_zero]]
    exact hdet

/-! ## The main theorem -/

theorem kho_proper {n s : ℕ} (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
    (T : Finset (Fin n → ℝ))
    (hproper : IsProperMap (liftSystem S F)) (hT : ∀ x ∈ T, S.Nondegen F x)
    (ih : ∀ (n' : ℕ) (S' : ESys n' s) (F' : Fin n' → EPoly n' s) (T' : Finset (Fin n' → ℝ)),
      (∀ x ∈ T', S'.Nondegen F' x) → T'.card ≤ KhovB s n' (∑ i, (F' i).totalDegree))
    (y : Fin n → ℝ) (hgood : KhoGood S F T y) :
    T.card ≤ KhovB s (n + 1) (2 * (∑ i, (F i).totalDegree) + n + 1) := by
  classical
  obtain ⟨hSub, hReg, hSlice, hρ, hρpos, hydist, hift⟩ := hgood
  obtain ⟨t, htcard, htmem⟩ := hift y hydist
  have htV : ∀ z ∈ t, liftSystem S F z = y := by
    intro z hz
    funext i
    have h2 := congrFun (htmem z hz) (Fin.castSucc i)
    rw [graphMap_apply_castSucc, Fin.snoc_castSucc] at h2
    exact h2
  have htg : ∀ z ∈ t, rolleg S z = 0 := by
    intro z hz
    have h2 := congrFun (htmem z hz) (Fin.last n)
    rw [graphMap_apply_last, Fin.snoc_last] at h2
    exact h2
  have htroot : ∀ z ∈ t, khoV S F y z = 0 ∧ rolleg S z = 0 := by
    intro z hz
    refine ⟨?_, htg z hz⟩
    rw [khoV_eq_zero_iff]
    exact htV z hz
  have hC : IsCompact {z : Fin (n + 1) → ℝ | khoV S F y z = 0} := by
    have h1 : {z : Fin (n + 1) → ℝ | khoV S F y z = 0} = {z | liftSystem S F z = y} := by
      ext z
      exact khoV_eq_zero_iff S F y z
    rw [h1]
    exact hproper.isCompact_preimage isCompact_singleton
  have hV2 : ContDiff ℝ 2 (khoV S F y) :=
    contDiff_liftSystem_aux S F |>.sub contDiff_const
  have hV1 : ContDiff ℝ 1 (khoV S F y) :=
    (contDiff_pi.mpr (fun i => contDiff_ev_gen (S.liftChain) (liftP (F i)) 1)).sub contDiff_const
  have hg1 : ContDiff ℝ 1 (rolleg S) := contDiff_rolleg_aux S
  have hψc : Continuous (rolleDetFun S F) := continuous_rolleDetFun_aux S F
  have hgrad : ∀ z, khoV S F y z = 0 →
      LinearIndependent ℝ (fun a => fderiv ℝ (fun w => khoV S F y w a) z) := by
    intro z hz
    have hzy : liftSystem S F z = y := (khoV_eq_zero_iff S F y z).mp hz
    have hfe : (fun a => fderiv ℝ (fun w => khoV S F y w a) z)
        = (fun a => fderiv ℝ (fun w => liftSystem S F w a) z) := by
      funext a
      exact khoV_fderiv S F y a z
    rw [hfe]
    exact hSub z hzy
  have hψ : ∀ z, khoV S F y z = 0 → rolleg S z = 0 →
      rolleDetFun S F z = fderiv ℝ (rolleg S) z (crossField (khoV S F y) z) := by
    intro z _ hzg
    rw [rolleDetFun_eq_crossField_of_graph S F z hzg, khoV_crossField]
  have hnd : ∀ z, khoV S F y z = 0 → rolleg S z = 0 → rolleDetFun S F z ≠ 0 := by
    intro z hzV hzg
    have hzy : liftSystem S F z = y := (khoV_eq_zero_iff S F y z).mp hzV
    have hroot : (fun i => S.ev (F i) (Fin.init z)) = y := by
      funext i
      rw [← graph_eval_liftP S F i z hzg]
      exact congrFun hzy i
    have hJ : (Matrix.of fun i j => S.ev (S.d j (F i)) (Fin.init z)).det ≠ 0 := hReg _ hroot
    intro h0
    apply hJ
    have hzsnoc := snoc_lastPsi_eq_self S z hzg
    have h2 : (S.liftChain).ev (S.rolleDet F) z
        = (S.liftChain).ev (S.rolleDet F)
            (Fin.snoc (Fin.init z) (S.lastPsi (Fin.init z))) := by rw [hzsnoc]
    rw [det_lift_eq S F (Fin.init z), ← h2]
    rw [show (S.liftChain).ev (S.rolleDet F) z = rolleDetFun S F z from rfl, h0, neg_zero]
  have hKnull : MeasureTheory.volume
      {t : ℝ | Fin.snoc y t ∈ rolleMap S F '' {z | (fderiv ℝ (rolleMap S F) z).det = 0}} = 0 :=
    hSlice
  obtain ⟨δ, hδpos, hδK, hδlt⟩ :=
    exists_delta_lt_abs_avoid_null (khoV S F y) (rolleg S) (rolleDetFun S F) hV1 hg1 hψc hC hnd
      _ hKnull
  have hnd' : ∀ z, khoV S F y z = 0 → rolleg S z = 0 →
      fderiv ℝ (rolleg S) z (crossField (khoV S F y) z) ≠ 0 := by
    intro z hzV hzg
    rw [← hψ z hzV hzg]
    exact hnd z hzV hzg
  obtain ⟨t₁, ht₁, ht₁card⟩ :=
    rolle_count_elimination (khoV S F y) (rolleg S) (rolleDetFun S F) hV2 hg1 hψc hC hgrad hψ hnd'
      δ hδpos hδlt t htroot
  let c : Fin (n + 1) → ℝ := Fin.snoc y δ
  let F' : Fin (n + 1) → EPoly (n + 1) s :=
    fun i => S.liftedSystem F i + MvPolynomial.C (-(c i))
  have hnondeg : ∀ z ∈ t₁, (S.liftChain).Nondegen F' z := by
    intro z hz
    obtain ⟨hzV, hzψ⟩ := ht₁ z hz
    have hzy : liftSystem S F z = y := (khoV_eq_zero_iff S F y z).mp hzV
    have hrm : rolleMap S F z = Fin.snoc y δ := by
      funext i
      rw [rolleMap_apply_liftedSystem S F z i]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last, ESys.liftedSystem_last]
        exact hzψ
      · rw [Fin.snoc_castSucc, ESys.liftedSystem_castSucc]
        exact congrFun hzy j
    have hdet : (fderiv ℝ (rolleMap S F) z).det ≠ 0 := by
      intro h0
      exact hδK ⟨z, h0, hrm⟩
    have hdet' : (Matrix.of fun i j =>
        (S.liftChain).ev ((S.liftChain).d j (S.liftedSystem F i)) z).det ≠ 0 := by
      rw [← det_fderiv_rolleMap_aux S F z]
      exact hdet
    exact nondegen_shift_aux S F c z
      (fun i => by
        have h2 := congrFun hrm i
        rwa [rolleMap_apply_liftedSystem S F z i] at h2) hdet'
  have hdeg : (∑ i, (F' i).totalDegree) ≤ 2 * (∑ i : Fin n, (F i).totalDegree) + n + 1 :=
    sum_totalDegree_liftedSystem_shift_le S F c
  calc T.card = t.card := htcard.symm
    _ ≤ t₁.card := ht₁card
    _ ≤ KhovB s (n + 1) (∑ i, (F' i).totalDegree) := ih (n + 1) (S.liftChain) F' t₁ hnondeg
    _ ≤ KhovB s (n + 1) (2 * (∑ i : Fin n, (F i).totalDegree) + n + 1) :=
        KhovB_mono_degree s (n + 1) (∑ i, (F' i).totalDegree)
          (2 * (∑ i : Fin n, (F i).totalDegree) + n + 1) hdeg

end Work.WilE2
