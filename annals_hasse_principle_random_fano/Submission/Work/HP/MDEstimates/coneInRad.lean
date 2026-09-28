import Mathlib
import Submission.Work.HP.MDEstimates.QuadAuxDefs
import Submission.Work.HP.MDEstimates.polarQuadFacts
import Submission.Work.HP.MDEstimates.radSupPair

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

noncomputable section
open MvPolynomial

namespace Work.HP.MDEstimates

/-! ## Linear polynomials

`linPoly a = ∑ aᵢ Xᵢ` is the linear form with coefficient vector `a`. -/

/-- The linear polynomial `∑ᵢ aᵢ Xᵢ`. -/
def linPoly (a : Fin 5 → ℚ) : MvPolynomial (Fin 5) ℚ :=
  ∑ i, MvPolynomial.C (a i) * MvPolynomial.X i

lemma linPoly_eval (a : Fin 5 → ℚ) (z : Fin 5 → ℚ) :
    (linPoly a).eval z = ∑ i, a i * z i := by
  simp [linPoly]

lemma linPoly_isHomogeneous (a : Fin 5 → ℚ) : (linPoly a).IsHomogeneous 1 := by
  rw [linPoly]
  exact MvPolynomial.IsHomogeneous.sum Finset.univ
    (fun i => MvPolynomial.C (a i) * MvPolynomial.X i) 1
    (fun i _ => MvPolynomial.isHomogeneous_C_mul_X _ _)

lemma linPoly_eval_div (a : Fin 5 → ℚ) (c : ℚ) (z : Fin 5 → ℚ) :
    (linPoly (fun i => a i / c)).eval z = (∑ i, a i * z i) / c := by
  rw [linPoly_eval, Finset.sum_div]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma linPoly_eval_two_sub_div (A B : Fin 5 → ℚ) (c : ℚ) (z : Fin 5 → ℚ) :
    (linPoly (fun i => 2 * A i - B i / c)).eval z
      = 2 * (∑ i, A i * z i) - (∑ i, B i * z i) / c := by
  rw [linPoly_eval]
  rw [show (∑ i, (2 * A i - B i / c) * z i)
        = ∑ i, ((2 * A i) * z i - (B i / c) * z i) from
      Finset.sum_congr rfl (fun i _ => by ring)]
  rw [Finset.sum_sub_distrib]
  rw [show (∑ i, (2 * A i) * z i) = 2 * ∑ i, A i * z i from by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)]
  rw [show (∑ i, (B i / c) * z i) = ∑ i, (B i * z i) / c from
        Finset.sum_congr rfl (fun i _ => by ring)]
  rw [Finset.sum_div]

/-- A linear functional on `Fin 5 → ℚ` is determined by its values on the standard basis. -/
lemma linMap_pi_expand (f : (Fin 5 → ℚ) →ₗ[ℚ] ℚ) (z : Fin 5 → ℚ) :
    f z = ∑ i, f (Pi.single i (1:ℚ)) * z i := by
  have hz : z = ∑ i, Pi.single i (z i) := (Finset.univ_sum_single z).symm
  conv_lhs => rw [hz]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show Pi.single i (z i) = z i • (Pi.single i (1:ℚ) : Fin 5 → ℚ) from ?_]
  · rw [map_smul, smul_eq_mul, mul_comm]
  · simpa using Pi.single_smul (f := fun _ : Fin 5 => ℚ) i (z i) (1:ℚ)

/-! ## Polar helper lemmas -/

private lemma polQ_add_right (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2)
    (x y z : Fin 5 → ℚ) : polQ Q x (y + z) = polQ Q x y + polQ Q x z := by
  have hA := polarQuadFacts Q hQ
  calc polQ Q x (y + z) = polQ Q (y + z) x := hA.2.2.1 x (y + z)
    _ = polQ Q y x + polQ Q z x := hA.1 y z x
    _ = polQ Q x y + polQ Q x z := by rw [hA.2.2.1 y x, hA.2.2.1 z x]

private lemma polQ_smul_right (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2)
    (c : ℚ) (x y : Fin 5 → ℚ) : polQ Q x (c • y) = c * polQ Q x y := by
  have hA := polarQuadFacts Q hQ
  calc polQ Q x (c • y) = polQ Q (c • y) x := hA.2.2.1 x (c • y)
    _ = c * polQ Q y x := hA.2.1 c y x
    _ = c * polQ Q x y := by rw [hA.2.2.1 y x]

private lemma polQ_self_expand (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2)
    (x y : Fin 5 → ℚ) :
    polQ Q (x + y) (x + y) = polQ Q x x + polQ Q y y + 2 * polQ Q x y := by
  have hA := polarQuadFacts Q hQ
  rw [hA.1 x y (x + y), polQ_add_right Q hQ x x y, polQ_add_right Q hQ y x y,
    hA.2.2.1 y x]
  ring

private lemma polQ_smul_smul (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2)
    (s t : ℚ) (x y : Fin 5 → ℚ) : polQ Q (s • x) (t • y) = s * t * polQ Q x y := by
  rw [polarQuadFacts Q hQ |>.2.1 s x (t • y), polQ_smul_right Q hQ t x y]
  ring

private lemma polQ_smul_self (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2)
    (s : ℚ) (x : Fin 5 → ℚ) : polQ Q (s • x) (s • x) = s^2 * polQ Q x x := by
  rw [polQ_smul_smul Q hQ s s x x]; ring

/-! ## The key evaluation identity -/

theorem quadIsoFactorEval (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2)
    (R₀ : Submodule ℚ (Fin 5 → ℚ)) (hR₀ : ∀ v : Fin 5 → ℚ, v ∈ R₀ ↔ v ∈ radQ Q)
    (hdim : 3 ≤ Module.finrank ℚ R₀)
    {v w : Fin 5 → ℚ} (hv : MvPolynomial.eval v Q = 0) (hvw : polQ Q v w ≠ 0) :
    ∀ z : Fin 5 → ℚ, MvPolynomial.eval z Q =
      (polQ Q v z / polQ Q v w) * (2 * polQ Q w z - (polQ Q w w / polQ Q v w) * polQ Q v z) := by
  intro z
  have hA := polarQuadFacts Q hQ
  obtain ⟨p_add, p_smul, p_comm, p_self, p_evalsmul, p_evaladd⟩ := hA
  obtain ⟨htop, -⟩ := radSupPair Q hQ R₀ hR₀ hdim hv hvw
  have hz : z ∈ R₀ ⊔ Submodule.span ℚ ({v, w} : Set (Fin 5 → ℚ)) := by rw [htop]; trivial
  rw [Submodule.mem_sup] at hz
  obtain ⟨r, hr, u, hu, rfl⟩ := hz
  have hrrad : r ∈ radQ Q := (hR₀ r).mp hr
  have hr0 : ∀ y, polQ Q r y = 0 := hrrad
  have hrQ : MvPolynomial.eval r Q = 0 := by rw [← p_self r]; exact hr0 r
  have hv0 : polQ Q v v = 0 := by rw [p_self v]; exact hv
  have hevalru : MvPolynomial.eval (r + u) Q = MvPolynomial.eval u Q := by
    rw [p_evaladd r u, ← p_self r, hr0 u, hr0 r]; ring
  have hbv : polQ Q v (r + u) = polQ Q v u := by
    rw [polQ_add_right Q hQ, p_comm v r, hr0 v, zero_add]
  have hbw : polQ Q w (r + u) = polQ Q w u := by
    rw [polQ_add_right Q hQ, p_comm w r, hr0 w, zero_add]
  rw [hevalru, hbv, hbw]
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hu
  rw [← hab]
  have hpuu : polQ Q (a • v + b • w) (a • v + b • w)
      = 2 * (a * b) * polQ Q v w + b ^ 2 * polQ Q w w := by
    rw [polQ_self_expand Q hQ, polQ_smul_self Q hQ, polQ_smul_self Q hQ,
      polQ_smul_smul Q hQ, hv0]
    ring
  have hpv : polQ Q v (a • v + b • w) = b * polQ Q v w := by
    rw [polQ_add_right Q hQ, polQ_smul_right Q hQ, polQ_smul_right Q hQ, hv0]
    ring
  have hpw : polQ Q w (a • v + b • w) = a * polQ Q v w + b * polQ Q w w := by
    rw [polQ_add_right Q hQ, polQ_smul_right Q hQ, polQ_smul_right Q hQ, p_comm w v]
  rw [← p_self (a • v + b • w), hpuu, hpv, hpw]
  field_simp
  ring

/-! ## The main theorem -/

theorem coneInRad (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2)
    (hnolf : ∀ ℓ : MvPolynomial (Fin 5) ℚ, ℓ.IsHomogeneous 1 → ℓ ∣ Q → False)
    (R₀ : Submodule ℚ (Fin 5 → ℚ)) (hR₀ : ∀ v : Fin 5 → ℚ, v ∈ R₀ ↔ v ∈ radQ Q)
    (hdim : 3 ≤ Module.finrank ℚ R₀) : coneQ Q ⊆ radQ Q := by
  intro v hv
  by_contra hvr
  simp only [radQ, Set.mem_ofPred_eq, not_forall] at hvr
  obtain ⟨w, hvw⟩ := hvr
  have hA := polarQuadFacts Q hQ
  obtain ⟨p_add, p_smul, p_comm, p_self, p_evalsmul, p_evaladd⟩ := hA
  set c := polQ Q v w with hc
  set d := polQ Q w w with hd
  have hcne : c ≠ 0 := hvw
  -- the two linear maps z ↦ polQ Q v z and z ↦ polQ Q w z
  let φv : (Fin 5 → ℚ) →ₗ[ℚ] ℚ :=
    { toFun := fun y => polQ Q v y
      map_add' := fun a b => by rw [p_comm v (a + b), p_add, ← p_comm v a, ← p_comm v b]
      map_smul' := fun t a => by
        rw [p_comm v (t • a), p_smul, ← p_comm v a]; simp [smul_eq_mul] }
  let φw : (Fin 5 → ℚ) →ₗ[ℚ] ℚ :=
    { toFun := fun y => polQ Q w y
      map_add' := fun a b => by rw [p_comm w (a + b), p_add, ← p_comm w a, ← p_comm w b]
      map_smul' := fun t a => by
        rw [p_comm w (t • a), p_smul, ← p_comm w a]; simp [smul_eq_mul] }
  have hφv : ∀ z, (∑ i, polQ Q v (Pi.single i (1:ℚ)) * z i) = polQ Q v z :=
    fun z => by simpa [φv] using (linMap_pi_expand φv z).symm
  have hφw : ∀ z, (∑ i, polQ Q w (Pi.single i (1:ℚ)) * z i) = polQ Q w z :=
    fun z => by simpa [φw] using (linMap_pi_expand φw z).symm
  -- the two linear forms
  let ℓ : MvPolynomial (Fin 5) ℚ := linPoly (fun i => polQ Q v (Pi.single i (1:ℚ)) / c)
  let m : MvPolynomial (Fin 5) ℚ :=
    linPoly (fun i => 2 * polQ Q w (Pi.single i (1:ℚ)) - (d * polQ Q v (Pi.single i (1:ℚ))) / c)
  have hℓeval : ∀ z, ℓ.eval z = polQ Q v z / c := by
    intro z
    simp only [ℓ]
    rw [linPoly_eval_div, hφv z]
  have hmeval : ∀ z, m.eval z = 2 * polQ Q w z - (d / c) * polQ Q v z := by
    intro z
    simp only [m]
    rw [linPoly_eval_two_sub_div, hφw z]
    have hdsum : (∑ i, (d * polQ Q v (Pi.single i (1:ℚ))) * z i) = d * polQ Q v z := by
      rw [show (∑ i, (d * polQ Q v (Pi.single i (1:ℚ))) * z i)
            = d * ∑ i, polQ Q v (Pi.single i (1:ℚ)) * z i from by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)]
      rw [hφv z]
    rw [hdsum]
    rw [show d * polQ Q v z / c = (d / c) * polQ Q v z from by ring]
  have hfac := quadIsoFactorEval Q hQ R₀ hR₀ hdim hv hvw
  have hpolyeq : ℓ * m = Q := by
    apply MvPolynomial.funext
    intro z
    rw [MvPolynomial.eval_mul, hℓeval z, hmeval z]
    rw [show polQ Q w w = d from hd.symm, show polQ Q v w = c from hc.symm] at hfac
    exact (hfac z).symm
  exact hnolf ℓ (linPoly_isHomogeneous _) ⟨m, hpolyeq.symm⟩

end Work.HP.MDEstimates
