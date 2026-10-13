import Mathlib
import Submission.Work.WilE2.Ebc.Defs
import Submission.Work.WilE2.Ebc.Poly
import Submission.Work.WilE2.Ebc.SlopeDefs

namespace Work.WilE2.Cb

/-- If the continuous linear functionals `D i` have trivial common kernel, then the matrix of
their coefficients in the standard basis is nonsingular. -/
private theorem det_ne_zero_of_forall_ker' {n : ℕ}
    (D : Fin n → ((Fin n → ℝ) →L[ℝ] ℝ))
    (h : ∀ v : Fin n → ℝ, (∀ i, D i v = 0) → v = 0) :
    (Matrix.of fun i j => D i (Pi.single j 1)).det ≠ 0 := by
  set T : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun v i => D i v
      map_add' := by intro v w; funext i; simp
      map_smul' := by intro c v; funext i; simp } with hT
  have hTapp : ∀ (v : Fin n → ℝ) (i : Fin n), T v i = D i v := fun v i => rfl
  have hker : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    apply h v
    intro i
    have h1 : T v i = 0 := by
      have h2 := congrFun hv i
      simpa using h2
    rwa [hTapp v i] at h1
  have hdet : LinearMap.det T ≠ 0 := by
    intro hd
    have h1 := (LinearMap.det_eq_zero_iff_ker_ne_bot (f := T)).mp hd
    rw [hker] at h1
    exact h1 rfl
  have hM : (Matrix.of fun i j => D i (Pi.single j 1))
      = LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin n)) T := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    simp [Pi.basisFun_apply, Pi.basisFun_repr, hTapp]
  rw [hM, LinearMap.det_toMatrix]
  exact hdet

/-- `tubeF ch g ε ρ` is the function `y ↦ eaEval ch (tubePoly g ε ρ) y`. -/
private theorem tubeF_eq_fun {k r : ℕ} (ch : WilkiesDesign.E.EAChain k r)
    (g : Finset (WilkiesDesign.E.EAPoly k r)) (ε ρ : ℝ) :
    Work.WilE2.tubeF ch g ε ρ
      = (fun z : Fin k → ℝ =>
          WilkiesDesign.E.eaEval ch (Work.WilE2.tubePoly g ε ρ) z) := by
  funext z
  rw [Work.WilE2.tubeF_apply]

/-- The `i₀`-th component of the critical system is the tube function itself. -/
private theorem critPoly_eval_fun_self {k r : ℕ} (ch : WilkiesDesign.E.EAChain k r)
    (g : Finset (WilkiesDesign.E.EAPoly k r)) (ε ρ : ℝ) (i₀ : Fin k) (sl : Fin k → ℝ) :
    (fun y : Fin k → ℝ =>
        WilkiesDesign.E.eaEval ch (Work.WilE2.critPoly ch g ε ρ i₀ sl i₀) y)
      = Work.WilE2.tubeF ch g ε ρ := by
  funext y
  rw [Work.WilE2.eaEval_critPoly_self, Work.WilE2.tubeF_apply]

/-- The other components of the critical system are the slope differences. -/
private theorem critPoly_eval_fun_other {k r : ℕ} (ch : WilkiesDesign.E.EAChain k r)
    (g : Finset (WilkiesDesign.E.EAPoly k r)) (ε ρ : ℝ) (i₀ : Fin k) (sl : Fin k → ℝ)
    (i : Fin k) (hi : i ≠ i₀) :
    (fun y : Fin k → ℝ =>
        WilkiesDesign.E.eaEval ch (Work.WilE2.critPoly ch g ε ρ i₀ sl i) y)
      = (fun w : Fin k → ℝ =>
          Work.WilE2.Ebc.pderiv (Work.WilE2.tubeF ch g ε ρ) i w
            - sl i * Work.WilE2.Ebc.pderiv (Work.WilE2.tubeF ch g ε ρ) i₀ w) := by
  funext y
  rw [Work.WilE2.eaEval_critPoly_other ch g ε ρ i₀ sl y hi]
  simp only [Work.WilE2.Ebc.pderiv_apply, tubeF_eq_fun ch g ε ρ]

theorem good_card_le {k r : ℕ} {F : ℕ} (q : Polynomial ℕ)
    (hq : ∀ (k' r' : ℕ) (c : WilkiesDesign.E.EAChain k' r') (f : Fin k' → WilkiesDesign.E.EAPoly k' r')
        (s : Finset (Fin k' → ℝ)), k' + r' ≤ F →
      (∀ x ∈ s, (∀ i, WilkiesDesign.E.eaEval c (f i) x = 0) ∧
        (Matrix.of fun i j => WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c j (f i)) x).det ≠ 0) →
      s.card ≤ q.eval (∑ i, WilkiesDesign.E.atomDeg (f i)))
    (hkr : k + r ≤ F) (ch : WilkiesDesign.E.EAChain k r) (g : Finset (WilkiesDesign.E.EAPoly k r))
    (ε ρ : ℝ) (i₀ : Fin k) (sl : Fin k → ℝ)
    (hsl : ∀ z : Fin k → ℝ, Work.WilE2.tubeF ch g ε ρ z = 0 →
      (∀ j : Fin k, j ≠ i₀ → Work.WilE2.Ebc.pderiv (Work.WilE2.tubeF ch g ε ρ) j z
        = sl j * Work.WilE2.Ebc.pderiv (Work.WilE2.tubeF ch g ε ρ) i₀ z) →
      Work.WilE2.Ebc.pderiv (Work.WilE2.tubeF ch g ε ρ) i₀ z ≠ 0 →
      ∀ v : Fin k → ℝ, v ≠ 0 → fderiv ℝ (Work.WilE2.tubeF ch g ε ρ) z v = 0 →
        ∃ j : Fin k, j ≠ i₀ ∧
          fderiv ℝ (fun w => Work.WilE2.Ebc.pderiv (Work.WilE2.tubeF ch g ε ρ) j w
            - sl j * Work.WilE2.Ebc.pderiv (Work.WilE2.tubeF ch g ε ρ) i₀ w) z v ≠ 0) :
    ∀ t : Finset (Fin k → ℝ),
      (↑t : Set (Fin k → ℝ)) ⊆ {z | Work.WilE2.tubeF ch g ε ρ z = 0 ∧
        (∀ j : Fin k, j ≠ i₀ → Work.WilE2.Ebc.pderiv (Work.WilE2.tubeF ch g ε ρ) j z
          = sl j * Work.WilE2.Ebc.pderiv (Work.WilE2.tubeF ch g ε ρ) i₀ z) ∧
        Work.WilE2.Ebc.pderiv (Work.WilE2.tubeF ch g ε ρ) i₀ z ≠ 0} →
      t.card ≤ q.eval ((Work.WilE2.ebcDegPoly F).eval (∑ f ∈ g, WilkiesDesign.E.atomDeg f)) := by
  intro t ht
  -- Vanishing of the critical system at every point of `t`, from the assumptions on `t`.
  have hvanish : ∀ x ∈ t, ∀ i : Fin k,
      WilkiesDesign.E.eaEval ch (Work.WilE2.critPoly ch g ε ρ i₀ sl i) x = 0 := by
    intro x hx i
    obtain ⟨h0, hslope, _hne⟩ := ht hx
    exact ((Work.WilE2.eaEval_critPoly_iff ch g ε ρ i₀ sl x).mpr
      ⟨by rw [← Work.WilE2.tubeF_apply]; exact h0, fun j hj => by
        simpa only [Work.WilE2.Ebc.pderiv_apply, tubeF_eq_fun ch g ε ρ] using hslope j hj⟩) i
  -- Non-degeneracy of the Jacobian of the critical system, from `hsl`.
  have hdet : ∀ x ∈ t,
      (Matrix.of fun i j =>
        WilkiesDesign.E.eaEval ch (WilkiesDesign.E.eaD ch j
          (Work.WilE2.critPoly ch g ε ρ i₀ sl i)) x).det ≠ 0 := by
    intro x hx
    obtain ⟨h0, hslope, hne⟩ := ht hx
    have hmat : (Matrix.of fun i j => WilkiesDesign.E.eaEval ch
          (WilkiesDesign.E.eaD ch j (Work.WilE2.critPoly ch g ε ρ i₀ sl i)) x)
        = (Matrix.of fun i j =>
            (fderiv ℝ (fun y => WilkiesDesign.E.eaEval ch
              (Work.WilE2.critPoly ch g ε ρ i₀ sl i) y) x) (Pi.single j 1)) := by
      ext i j
      simp only [Matrix.of_apply]
      exact Work.WilE2.eaEval_eaD_critPoly ch g ε ρ i₀ sl x i j
    rw [hmat]
    refine det_ne_zero_of_forall_ker'
      (fun i => fderiv ℝ (fun y => WilkiesDesign.E.eaEval ch
        (Work.WilE2.critPoly ch g ε ρ i₀ sl i) y) x) ?_
    intro v hv
    by_contra hv0
    have hfd : fderiv ℝ (Work.WilE2.tubeF ch g ε ρ) x v = 0 := by
      have h1 := hv i₀
      rwa [critPoly_eval_fun_self ch g ε ρ i₀ sl] at h1
    obtain ⟨j, hj, hjd⟩ := hsl x h0 hslope hne v hv0 hfd
    have hjv := hv j
    rw [critPoly_eval_fun_other ch g ε ρ i₀ sl j hj] at hjv
    exact hjd hjv
  -- Apply the Khovanskii hypothesis to the critical system.
  have hbound := hq k r ch (fun i => Work.WilE2.critPoly ch g ε ρ i₀ sl i) t hkr
    (fun x hx => ⟨hvanish x hx, hdet x hx⟩)
  -- Bound the atom degrees of the critical system by the degree polynomial.
  refine le_trans hbound ?_
  exact Work.WilE2.eval_mono_nat q
    (Work.WilE2.sum_atomDeg_critPoly_le ch g ε ρ i₀ sl (by omega))

end Work.WilE2.Cb
