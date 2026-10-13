/-
  Work.WilE2 — area E2.  Existence of a *good* value for the Khovanskii–Rolle elimination.

  `KhoGood S F T y` bundles the four genericity properties of the value `y` at which the
  counting of the proper case runs (`KhoGood.lean`).  This module produces such a `y` from

  * the non-degeneracy of the finitely many roots `T` of the system at the value `0`
    (this is what makes the crossings of the graph `N = {g = 0}` transversal, so that the
    inverse function theorem moves them onto every nearby level `{G = y'}`);
  * the properness of the lifted map `G = liftSystem S F`; and
  * the density of the regular values of `G` (the Sard input, `regular_values_dense`).

  The three "bad" subsets of `ℝⁿ` are shown to be small:

  * `{y | ¬ KhoRegValue S F y} = F '' {x | det (fderiv F x) = 0}` is the *critical value set*
    of the square system map `F` — Lebesgue-null by Sard in the square case (`sard_square`);
  * `{y | ¬ KhoSliceNull S F y}` is, by Fubini, the set of `y` whose slice of the critical
    value set of `rolleMap` is non-null — null by `sard_square` + `slice_null_ae`;
  * `{y | ¬ KhoSubmersion S F y} = G '' (crossField G)⁻¹' {0}` is *closed*: the critical set of
    `G` (where the cross product of the gradients vanishes) is closed, and `G` is proper, hence
    a closed map.

  The regular values of `G` are therefore open as well as dense, and avoiding the two null bad
  sets inside a ball of regular values (below the radius supplied by the inverse function
  theorem) gives the required `y`.
-/
import Mathlib
import Submission.Work.WilE2.KhoGood
import Submission.Work.WilE2.RegSol
import Submission.Work.WilE2.RolleDetAnalytic
import Submission.Work.WilE2.Genericity
import Submission.Work.WilE2.slice_null_ae
import Submission.Work.WilE2.avoid_null
import Submission.Work.WilE2.sard_square
import Submission.Work.WilE2.ift_perturbation
import Submission.Work.WilE2.tangentField_exists
import Submission.Work.WilE2.linearIndependent_tangGrad
import Submission.Work.WilE2.hasFDerivAt_rolleMap
import Submission.Work.WilE2.khoReg_bad_null
import Submission.Work.WilE2.khoSlice_bad_null
import Submission.Work.WilE2.khoSubm_bad_closed

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical MeasureTheory
namespace Work.WilE2

open WilkiesDesign WilkiesDesign.E WilkiesConjecture

variable {n s : ℕ}

/-! ## §1. Smoothness of the graph map -/

/-- A vector of `ℝⁿ`, completed by `0` in the extra coordinate, has the same norm:
the extra coordinate does not increase the supremum norm. -/
theorem kge_norm_snoc_zero_le (y : Fin n → ℝ) :
    ‖(Fin.snoc y (0 : ℝ) : Fin (n + 1) → ℝ)‖ ≤ ‖y‖ := by
  refine (pi_norm_le_iff_of_nonempty (f := (Fin.snoc y (0 : ℝ) : Fin (n + 1) → ℝ))).mpr
    (fun i => ?_)
  rcases Fin.eq_castSucc_or_eq_last i with ⟨a, rfl⟩ | rfl
  · rw [Fin.snoc_castSucc]
    exact norm_le_pi_norm y a
  · rw [Fin.snoc_last, norm_zero]
    exact norm_nonneg y

/-! ### Local smoothness of the evaluated chain

The evaluation `S.ev P` of an EA polynomial is `C^N` for every order `N` (a polynomial
expression in the coordinates and the smooth chain functions).  The induction is reproduced
here, in the two instances needed below, so that this module rests only on proved material.
The delicate point is that the codomain `ℝ` carries two propositionally equal but not
definitionally equal `NormedSpace ℝ ℝ` instances; the goal is therefore always rewritten into
the same syntactic shape before a smoothness lemma is applied. -/

/-- The affine exponent `S.ell j` is smooth. -/
theorem kge_contDiff_ell (S : ESys n s) (j : Fin s) (N : WithTop ℕ∞) :
    ContDiff ℝ N (S.ell j) := by
  have h : S.ell j = fun x : Fin n → ℝ => S.ellGrad j x + S.b j := by
    funext x
    rw [ESys.ellGrad_apply, ESys.ell]
  rw [h]
  exact (S.ellGrad j).contDiff.add (contDiff_const (c := S.b j))

/-- The chain functions `S.psi j = exp ∘ S.ell j` are smooth. -/
theorem kge_contDiff_psi (S : ESys n s) (j : Fin s) (N : WithTop ℕ∞) :
    ContDiff ℝ N (fun x : Fin n → ℝ => S.psi j x) := by
  rw [show (fun x : Fin n → ℝ => S.psi j x)
      = (fun x : Fin n → ℝ => Real.exp (S.ell j x)) from rfl]
  exact (kge_contDiff_ell S j N).exp

/-- The `n + s` generators of the evaluation are smooth. -/
theorem kge_contDiff_ev_X (S : ESys n s) (t : Fin n ⊕ Fin s) (N : WithTop ℕ∞) :
    ContDiff ℝ N (S.ev (MvPolynomial.X t)) := by
  rcases t with j | j
  · have h : S.ev (MvPolynomial.X (Sum.inl j)) = fun x : Fin n → ℝ => x j := by
      funext x; simp [ESys.ev]
    rw [h]
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).contDiff
  · have h : S.ev (MvPolynomial.X (Sum.inr j)) = fun x : Fin n → ℝ => S.psi j x := by
      funext x; simp [ESys.ev, ESys.psi]
    rw [h]
    exact kge_contDiff_psi S j N

/-- The evaluated EA polynomial `S.ev P` is smooth. -/
theorem kge_contDiff_ev (S : ESys n s) (P : EPoly n s) (N : WithTop ℕ∞) :
    ContDiff ℝ N (S.ev P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      have h : S.ev (MvPolynomial.C c) = fun _ : Fin n → ℝ => c := by
        funext x; simp [ESys.ev]
      rw [h]
      exact contDiff_const
  | add P Q hP hQ =>
      have h : S.ev (P + Q) = S.ev P + S.ev Q := by
        funext x; simp [ESys.ev, map_add]
      rw [h]
      exact hP.add hQ
  | mul_X P t hP =>
      have h : S.ev (P * MvPolynomial.X t) = S.ev P * S.ev (MvPolynomial.X t) := by
        funext x; simp [ESys.ev, map_mul]
      rw [h]
      exact hP.mul (kge_contDiff_ev_X S t N)

/-- The components of `graphMap` are the functions `liftFun`. -/
theorem kge_graphMap_apply_liftFun (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
    (z : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    graphMap S F z j = liftFun S F j z := by
  rcases Fin.eq_castSucc_or_eq_last j with ⟨a, rfl⟩ | rfl
  · rw [graphMap_apply_castSucc, liftFun_of_lt S F (Fin.castSucc a) a.isLt]
    simp only [liftSystem]
    rw [show (⟨↑(Fin.castSucc a), a.isLt⟩ : Fin n) = a from Fin.ext (by simp)]
  · rw [graphMap_apply_last, liftFun_of_not_lt S F (Fin.last n) (by simp)]

/-- The graph map of the lift is `C¹`. -/
theorem kge_contDiff_graphMap (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) :
    ContDiff ℝ 1 (graphMap S F) := by
  rw [contDiff_pi]
  intro j
  rcases Fin.eq_castSucc_or_eq_last j with ⟨a, rfl⟩ | rfl
  · have h : (fun z : Fin (n + 1) → ℝ => graphMap S F z (Fin.castSucc a))
        = (S.liftChain).ev (liftP (F a)) := by
      funext z
      rw [graphMap_apply_castSucc]
      simp only [liftSystem]
    rw [h]
    exact kge_contDiff_ev (S.liftChain) (liftP (F a)) 1
  · have h : (fun z : Fin (n + 1) → ℝ => graphMap S F z (Fin.last n)) = rolleg S := by
      funext z
      rw [graphMap_apply_last]
    rw [h, rolleg_eq_ravel]
    refine ContDiff.sub ?_ ?_
    · exact kge_contDiff_psi (S.ravel) (Fin.last s) 1
    · exact (ContinuousLinearMap.proj (Fin.last n) : (Fin (n + 1) → ℝ) →L[ℝ] ℝ).contDiff


/-! ## §2. The IFT data at the transversal crossings -/

/-- `graphMap` is differentiable, with the componentwise derivative. -/
theorem kge_hasFDerivAt_graphMap (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
    (z : Fin (n + 1) → ℝ) :
    HasFDerivAt (graphMap S F)
      (ContinuousLinearMap.pi fun j : Fin (n + 1) => fderiv ℝ (liftFun S F j) z) z := by
  refine hasFDerivAt_pi.mpr fun j => ?_
  rcases Fin.eq_castSucc_or_eq_last j with ⟨a, rfl⟩ | rfl
  · have hfun : (fun w : Fin (n + 1) → ℝ => graphMap S F w (Fin.castSucc a))
        = (S.liftChain).ev (liftP (F a)) := by
      funext w
      rw [graphMap_apply_castSucc]
      simp only [liftSystem]
    have hfd : fderiv ℝ (liftFun S F (Fin.castSucc a)) z
        = (S.liftChain).grad (liftP (F a)) z := by
      rw [liftFun_of_lt S F (Fin.castSucc a) a.isLt]
      rw [show (⟨↑(Fin.castSucc a), a.isLt⟩ : Fin n) = a from Fin.ext (by simp)]
      exact (ev_hasFDerivAt (S.liftChain) (liftP (F a)) z).fderiv
    rw [hfun, hfd]
    exact ev_hasFDerivAt (S.liftChain) (liftP (F a)) z
  · have hfun : (fun w : Fin (n + 1) → ℝ => graphMap S F w (Fin.last n)) = rolleg S := by
      funext w
      rw [graphMap_apply_last]
    have hfd : fderiv ℝ (liftFun S F (Fin.last n)) z = fderiv ℝ (rolleg S) z := by
      rw [liftFun_of_not_lt S F (Fin.last n) (by simp)]
    have hdiff : HasFDerivAt (rolleg S)
        ((S.ravel).psi (Fin.last s) z • (S.ravel).ellGrad (Fin.last s) -
          (ContinuousLinearMap.proj (Fin.last n) : (Fin (n + 1) → ℝ) →L[ℝ] ℝ)) z := by
      have h1 : HasFDerivAt (fun w : Fin (n + 1) → ℝ => (S.ravel).psi (Fin.last s) w)
          ((S.ravel).psi (Fin.last s) z • (S.ravel).ellGrad (Fin.last s)) z :=
        ESys.hasFDerivAt_psi S.ravel (Fin.last s) z
      have h2 : HasFDerivAt (fun w : Fin (n + 1) → ℝ => w (Fin.last n))
          (ContinuousLinearMap.proj (Fin.last n) : (Fin (n + 1) → ℝ) →L[ℝ] ℝ) z :=
        ContinuousLinearMap.hasFDerivAt
          (ContinuousLinearMap.proj (Fin.last n) : (Fin (n + 1) → ℝ) →L[ℝ] ℝ) (x := z)
      rw [rolleg_eq_ravel S]
      exact h1.sub h2
    rw [hfun, hfd]
    exact hdiff.differentiableAt.hasFDerivAt

/-- **The determinant of the differential of the graph map is the analytic Rolle determinant.**
The componentwise derivative identifies `det (fderiv (graphMap))` with the determinant of the
transpose of the matrix `[∇g_1, …, ∇g_n, ∇g]` of the paper, hence with the Rolle determinant. -/
theorem kge_fderiv_graphMap_det (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
    (z : Fin (n + 1) → ℝ) :
    (fderiv ℝ (graphMap S F) z).det =
      (Matrix.of fun (i j : Fin (n + 1)) =>
        fderiv ℝ (liftFun S F j) z (Pi.single i (1 : ℝ))).det := by
  have hfd : fderiv ℝ (graphMap S F) z
      = ContinuousLinearMap.pi (fun j : Fin (n + 1) => fderiv ℝ (liftFun S F j) z) :=
    (kge_hasFDerivAt_graphMap S F z).fderiv
  have hmat : LinearMap.toMatrix'
        (ContinuousLinearMap.pi (fun j : Fin (n + 1) => fderiv ℝ (liftFun S F j) z)).toLinearMap
      = (Matrix.of fun (i j : Fin (n + 1)) =>
          fderiv ℝ (liftFun S F j) z (Pi.single i (1 : ℝ))).transpose := by
    ext i j
    rw [LinearMap.toMatrix'_apply, Matrix.transpose_apply, Matrix.of_apply]
    change (ContinuousLinearMap.pi fun j : Fin (n + 1) => fderiv ℝ (liftFun S F j) z)
        (Pi.single j (1 : ℝ)) i = (fderiv ℝ (liftFun S F i) z) (Pi.single j (1 : ℝ))
    rw [ContinuousLinearMap.pi_apply]
  rw [hfd, ContinuousLinearMap.det, ← LinearMap.det_toMatrix', hmat, Matrix.det_transpose]

/-- On the graph `N = {g = 0}`, the lifted system reproduces the old one, so every
non-degenerate root of the old system is a zero of the graph map. -/
theorem kge_graphMap_at_lastPsi (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) (x : Fin n → ℝ)
    (hx : S.Nondegen F x) : graphMap S F (Fin.snoc x (S.lastPsi x)) = 0 := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨a, rfl⟩ | rfl
  · rw [graphMap_apply_castSucc]
    show (S.liftChain).ev (liftP (F a)) (Fin.snoc x (S.lastPsi x)) = 0
    rw [ESys.ev_liftP_lastPsi]
    exact hx.1 a
  · rw [graphMap_apply_last]
    simp [rolleg, Fin.init_snoc, Fin.snoc_last]

/-- At a non-degenerate root of the old system, the graph map is a local diffeomorphism: its
Jacobian determinant does not vanish there (paper's Claim `regular-solutions`). -/
theorem kge_det_fderiv_graphMap_ne_zero (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
    (x : Fin n → ℝ) (hx : S.Nondegen F x) :
    (fderiv ℝ (graphMap S F) (Fin.snoc x (S.lastPsi x))).det ≠ 0 := by
  rw [kge_fderiv_graphMap_det S F (Fin.snoc x (S.lastPsi x))]
  intro h
  have hsym := hx.2
  rw [det_lift_analytic S F x] at hsym
  exact hsym (by rw [h, neg_zero])


/-- The map `x ↦ (x, ψₛ(x))` exhibiting the (transversal) crossings is injective. -/
theorem kge_snoc_lastPsi_injective (S : ESys n (s + 1)) :
    Function.Injective (fun x : Fin n → ℝ => (Fin.snoc x (S.lastPsi x) : Fin (n + 1) → ℝ)) := by
  intro x y h
  have := congrArg Fin.init h
  simpa [Fin.init_snoc] using this

/-! ## §3. The generic value -/

theorem kho_good_exists {n s : ℕ} (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
    (T : Finset (Fin n → ℝ)) (hT : ∀ x ∈ T, S.Nondegen F x)
    (hproper : IsProperMap (liftSystem S F))
    (hsard : ∀ (y₀ : Fin n → ℝ) (ε : ℝ), 0 < ε → ∃ y : Fin n → ℝ, dist y y₀ < ε ∧
      KhoSubmersion S F y) :
    ∃ y : Fin n → ℝ, KhoGood S F T y := by
  classical
  -- The finitely many transversal crossings of the graph `N = {g = 0}`.
  have hcard : (T.image (fun x : Fin n → ℝ => (Fin.snoc x (S.lastPsi x) : Fin (n + 1) → ℝ))).card = T.card := by
    rw [Finset.card_image_of_injOn]
    intro x _ y _ hxy
    exact kge_snoc_lastPsi_injective S hxy
  have hzero : ∀ z ∈ T.image (fun x : Fin n → ℝ => (Fin.snoc x (S.lastPsi x) : Fin (n + 1) → ℝ)),
      graphMap S F z = 0 := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact kge_graphMap_at_lastPsi S F x (hT x hx)
  have hnd : ∀ z ∈ T.image (fun x : Fin n → ℝ => (Fin.snoc x (S.lastPsi x) : Fin (n + 1) → ℝ)),
      (fderiv ℝ (graphMap S F) z).det ≠ 0 := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact kge_det_fderiv_graphMap_ne_zero S F x (hT x hx)
  -- The inverse function theorem: every value close to `0` has `T.card` preimages.
  obtain ⟨ρ₀, hρ₀pos, hρ₀⟩ :=
    ift_perturbation (graphMap S F) (kge_contDiff_graphMap S F)
      (T.image (fun x : Fin n → ℝ => (Fin.snoc x (S.lastPsi x) : Fin (n + 1) → ℝ))) hzero hnd
  -- The values at which the two Sard-type conditions fail form a null set.
  have hBreg : volume {y : Fin n → ℝ | ¬ KhoRegValue S F y} = 0 := khoReg_bad_null S F
  have hBslice : volume {y : Fin n → ℝ | ¬ KhoSliceNull S F y} = 0 :=
    khoSlice_bad_null S F fun z => (hasFDerivAt_rolleMap S F z).differentiableAt.hasFDerivAt
  have hunion : volume ({y : Fin n → ℝ | ¬ KhoRegValue S F y} ∪
      {y : Fin n → ℝ | ¬ KhoSliceNull S F y}) = 0 := measure_union_null hBreg hBslice
  -- The non-regular values of the lifted map form a closed set (properness), so the regular
  -- values are open.
  have hG2 : ContDiff ℝ 2 (liftSystem S F) := by
    rw [contDiff_pi]
    intro i
    exact kge_contDiff_ev (S.liftChain) (liftP (F i)) 2
  have hcont : Continuous (crossField (liftSystem S F)) :=
    (contDiff_crossField (liftSystem S F) hG2).continuous
  have hclosed : IsClosed {y : Fin n → ℝ | ¬ KhoSubmersion S F y} :=
    khoSubm_bad_closed S F hproper hcont
  have hopen : IsOpen {y : Fin n → ℝ | ¬ KhoSubmersion S F y}ᶜ := hclosed.isOpen_compl
  -- A regular value near `0`, and a ball of regular values inside `B(0, ρ₀)`.
  obtain ⟨y₁, hy₁d, hy₁⟩ := hsard 0 (ρ₀ / 2) (by linarith)
  have hy₁B : y₁ ∉ ({y : Fin n → ℝ | ¬ KhoSubmersion S F y} : Set (Fin n → ℝ)) :=
    fun h => h hy₁
  obtain ⟨δ, hδpos, hδball⟩ := Metric.isOpen_iff.mp hopen y₁ hy₁B
  have hgap : 0 < ρ₀ - dist y₁ 0 := by
    have := dist_nonneg (x := y₁) (y := 0)
    linarith
  obtain ⟨y, hyd, hybad⟩ := avoid_null hunion y₁ (lt_min hδpos hgap)
  have hyB : y ∉ ({y : Fin n → ℝ | ¬ KhoSubmersion S F y} : Set (Fin n → ℝ)) := by
    refine hδball (Metric.ball_subset_ball (min_le_left _ _) (Metric.mem_ball.mpr hyd))
  have hdist0 : dist y 0 < ρ₀ := by
    have h1 : dist y 0 ≤ dist y y₁ + dist y₁ 0 := dist_triangle y y₁ 0
    have h2 : min δ (ρ₀ - dist y₁ 0) ≤ ρ₀ - dist y₁ 0 := min_le_right _ _
    linarith
  refine ⟨y, not_not.mp hyB, not_not.mp (fun h => hybad (Or.inl h)),
    not_not.mp (fun h => hybad (Or.inr h)), ?_⟩
  refine ⟨ρ₀, hρ₀pos, hdist0, fun y' hy' => ?_⟩
  have hy'' : dist (Fin.snoc y' (0 : ℝ) : Fin (n + 1) → ℝ) 0 < ρ₀ := by
    have h1 : dist (Fin.snoc y' (0 : ℝ) : Fin (n + 1) → ℝ) 0 ≤ dist y' 0 := by
      rw [dist_zero_right, dist_zero_right]
      exact kge_norm_snoc_zero_le y'
    linarith
  obtain ⟨t, htcard, htz⟩ := hρ₀ (Fin.snoc y' (0 : ℝ) : Fin (n + 1) → ℝ) hy''
  exact ⟨t, by rw [htcard, hcard], htz⟩

end Work.WilE2
