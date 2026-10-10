import Mathlib
import Submission.Work.MotT.T4Setup
import Submission.Work.MotT.AM2_descent
import Submission.Work.MotT.T4Extend
import Submission.Work.MotT.coeffAut_conj_trans
import Submission.Work.MotC2.transAlgEquiv_injective
import Submission.Work.MotC2.Negation
import Submission.Work.MotC2.negAlgEquiv_mul_transAlgEquiv
import Submission.Work.MotT.c2_over_ML2
import Submission.Work.MotT.T4_compare
import Submission.Work.MotT.sigma_pow_trans_ratio
import Submission.Work.MotT.transAlgEquiv_neg_ratio
import Submission.Work.MotT.coeffAut_neg_comm
import Submission.Work.MotT.twistPointK_coords
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.MotT

open WeierstrassCurve WeierstrassCurve.Affine

/-! ## §0 The delegated inputs (imported; see the header) -/






/-! ## §1 The two branches of the LAM arithmetic -/

noncomputable section

variable {K : Type} [Field K]

/-- `restrictScalars K` is multiplicative. -/
theorem T4_res_mul {R S M : Type*} [Field R] [Field S] [Field M] [Algebra R S] [Algebra R M]
    [Algebra S M] [IsScalarTower R S M]
    (e₁ e₂ : M ≃ₐ[S] M) :
    (e₁ * e₂).restrictScalars R = e₁.restrictScalars R * e₂.restrictScalars R :=
  map_mul (AlgEquiv.restrictScalarsHom (R := R) (S := S) (A := M)) e₁ e₂

/-- Powers commute with `restrictScalars`. -/
theorem T4_res_pow {R S M : Type*} [Field R] [Field S] [Field M] [Algebra R S] [Algebra R M]
    [Algebra S M] [IsScalarTower R S M] (e : M ≃ₐ[S] M) (m : ℕ) :
    (e ^ m).restrictScalars R = (e.restrictScalars R) ^ m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ, pow_succ, T4_res_mul, ih]

/-- The `K`-linear automorphism `AM2_sigmaK` is the restriction of scalars of `AM2_sigma`, so their
powers agree on the nose. -/
theorem T4_sigmaK_pow_apply (D : Work.MotV.KleinData K) (hD : D.Good) (h₁ h₂ : K)
    (hk : ringChar K ≠ 5) (m : ℕ) :
    ∀ x : ML2 D h₁ h₂ hk,
      ((AM2_sigmaK D hD h₁ h₂ hk) ^ m) x = ((AM2_sigma D hD h₁ h₂ hk) ^ m) x := by
  induction m with
  | zero => intro x; rfl
  | succ m ih =>
    intro x
    rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, AM2_sigmaK_apply]
    exact ih _

/-- **The diagonal action is multiplicative in the point.**  If `τ_A` acts on every Klein ratio
`κᵢ/κ₀` by multiplication by `(algebraMap c)^i` and `τ_B` by `(algebraMap d)^i`, then `τ_{A+B}` acts
by `(algebraMap (c*d))^i`. -/
theorem T4_ratio_add (D : Work.MotV.KleinData K) (h₁ h₂ : K) (hk : ringChar K ≠ 5)
    [instDec : DecidableEq ↥(KummerField2 K h₁ h₂ hk)]
    [instEll : (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)).IsElliptic]
    (A B : (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)).toAffine.Point)
    (c d : ↥(KummerField2 K h₁ h₂ hk))
    (hA : ∀ i : Fin 5,
      Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A
          (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
            Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) =
        (algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk) c) ^ (i : ℕ) *
          (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
            Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0))
    (hB : ∀ i : Fin 5,
      Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) B
          (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
            Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) =
        (algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk) d) ^ (i : ℕ) *
          (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
            Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0)) :
    ∀ i : Fin 5,
      Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) (A + B)
          (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
            Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) =
        (algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk) (c * d)) ^ (i : ℕ) *
          (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
            Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) := by
  intro i
  have hcomm : Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A
        ((algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk) d) ^ (i : ℕ)) =
      (algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk) d) ^ (i : ℕ) := by
    rw [← map_pow]
    exact (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A).commutes _
  calc Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) (A + B)
          (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
            Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0)
      = Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A
          (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) B
            (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
              Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0)) := by
        rw [← AlgEquiv.mul_apply, ← Work.MotC2.transAlgEquiv_add]
    _ = Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A
          ((algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk) d) ^ (i : ℕ) *
            (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
              Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0)) := by
        rw [hB i]
    _ = (algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk) d) ^ (i : ℕ) *
          Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A
            (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
              Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) := by
        rw [map_mul, hcomm]
    _ = (algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk) d) ^ (i : ℕ) *
          ((algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk) c) ^ (i : ℕ) *
            (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
              Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0)) := by
        rw [hA i]
    _ = (algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk) (c * d)) ^ (i : ℕ) *
          (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
            Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) := by
        rw [map_mul, mul_pow]
        refl_ring1


/-- **The `ε = 0` branch of the LAM arithmetic**: if the extension `Θ` of `θ` to `L(E)` is a pure
translation `τ_Q`, then the twist `C_{h₁/h₂}` has a `K`-point. -/
theorem T4_eps0 (D : Work.MotV.KleinData K) (hD : D.Good) (h₁ h₂ : K) (h₁0 : h₁ ≠ 0)
    (h₂0 : h₂ ≠ 0) (hk : ringChar K ≠ 5)
    [instDec : DecidableEq ↥(KummerField2 K h₁ h₂ hk)]
    [instEll : (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)).IsElliptic]
    (θ : twistFieldTK D h₁ ≃ₐ[K] twistFieldTK D h₂)
    (Θ : ML2 D h₁ h₂ hk ≃ₐ[↥(KummerField2 K h₁ h₂ hk)] ML2 D h₁ h₂ hk)
    (hΘ : ∀ x : ↥(AM21 D h₁ h₂ hk),
      (Θ (x : ML2 D h₁ h₂ hk) : ML2 D h₁ h₂ hk) =
        ((thetaL D hk θ x : ↥(AM22 D h₁ h₂ hk)) : ML2 D h₁ h₂ hk))
    (Q : (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)).toAffine.Point)
    (hQ : Θ = Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) Q) :
    ∃ y : Fin 5 → K, y ≠ 0 ∧
      ∀ k, Work.MotV.kleinTw D.a D.b (h₁ * h₂ ^ (-1 : ℤ)) y k = 0 := by
  have hw : (wL1 K h₁ h₂ hk / wL2 K h₁ h₂ hk) ^ 5 =
      algebraMap K ↥(KummerField2 K h₁ h₂ hk) (h₁ / h₂) := by
    rw [div_pow, wL1_pow_five, wL2_pow_five, ← map_div₀]
  have hQ' : ∀ σ : ↥(KummerField2 K h₁ h₂ hk) ≃ₐ[K] ↥(KummerField2 K h₁ h₂ hk),
      ∃ A : (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)).toAffine.Point,
        WeierstrassCurve.Affine.Point.map (W' := D.E) (S := K)
            (F := ↥(KummerField2 K h₁ h₂ hk)) (K := ↥(KummerField2 K h₁ h₂ hk))
            σ.toAlgHom Q = Q + A ∧
        ∀ i : Fin 5,
          Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A
              (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
                Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) =
            (algebraMap ↥(KummerField2 K h₁ h₂ hk)
                (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))
                (σ (wL1 K h₁ h₂ hk / wL2 K h₁ h₂ hk) /
                  (wL1 K h₁ h₂ hk / wL2 K h₁ h₂ hk))) ^ (i : ℕ) *
              (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
                Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) := by
    intro σ
    obtain ⟨A₁, hA₁, hr₁⟩ := sigma_pow_trans_ratio D hD h₁ h₂ hk
      (AM2_mK D hD h₁ h₂ hk h₁ h₁0 (wL1 K h₁ h₂ hk) (wL1_pow_five K h₁ h₂ hk) σ)
    obtain ⟨A₂, hA₂, hr₂⟩ := sigma_pow_trans_ratio D hD h₁ h₂ hk
      (AM2_mK D hD h₁ h₂ hk h₂ h₂0 (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk) σ)
    refine ⟨A₁ - A₂, ?_, ?_⟩
    · -- the point relation
      have hcmpE : Θ.restrictScalars K *
            AM2_rhoFun D hD h₁ h₂ hk h₁ h₁0 (wL1 K h₁ h₂ hk) (wL1_pow_five K h₁ h₂ hk) σ =
          AM2_rhoFun D hD h₁ h₂ hk h₂ h₂0 (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk) σ *
            Θ.restrictScalars K := by
        ext x
        rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
        exact T4_compare D hD h₁ h₂ h₁0 h₂0 hk θ Θ hΘ σ x
      have hσ₁ : (AM2_sigmaK D hD h₁ h₂ hk) ^
            (AM2_mK D hD h₁ h₂ hk h₁ h₁0 (wL1 K h₁ h₂ hk) (wL1_pow_five K h₁ h₂ hk) σ) =
          (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
            A₁).restrictScalars K := by
        have h2 : ((AM2_sigma D hD h₁ h₂ hk) ^
              (AM2_mK D hD h₁ h₂ hk h₁ h₁0 (wL1 K h₁ h₂ hk) (wL1_pow_five K h₁ h₂ hk)
                σ)).restrictScalars K =
            (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
              A₁).restrictScalars K := by
          rw [hA₁]
        rw [T4_res_pow] at h2
        exact h2
      have hσ₂ : (AM2_sigmaK D hD h₁ h₂ hk) ^
            (AM2_mK D hD h₁ h₂ hk h₂ h₂0 (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk) σ) =
          (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
            A₂).restrictScalars K := by
        have h2 : ((AM2_sigma D hD h₁ h₂ hk) ^
              (AM2_mK D hD h₁ h₂ hk h₂ h₂0 (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk)
                σ)).restrictScalars K =
            (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
              A₂).restrictScalars K := by
          rw [hA₂]
        rw [T4_res_pow] at h2
        exact h2
      have hγτ : AM2_coeffAut D hD h₁ h₂ hk σ * Θ.restrictScalars K =
          (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
              (WeierstrassCurve.Affine.Point.map (W' := D.E) (S := K)
                (F := ↥(KummerField2 K h₁ h₂ hk)) (K := ↥(KummerField2 K h₁ h₂ hk))
                σ.toAlgHom Q)).restrictScalars K *
            AM2_coeffAut D hD h₁ h₂ hk σ := by
        ext x
        rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hQ]
        exact coeffAut_conj_trans D hD h₁ h₂ hk σ Q x
      have hL : Θ.restrictScalars K *
            AM2_rhoFun D hD h₁ h₂ hk h₁ h₁0 (wL1 K h₁ h₂ hk) (wL1_pow_five K h₁ h₂ hk) σ =
          (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
              (Q + A₁)).restrictScalars K * AM2_coeffAut D hD h₁ h₂ hk σ := by
        rw [AM2_rhoFun, hσ₁, ← mul_assoc, hQ, ← T4_res_mul (R := K) (S := ↥(KummerField2 K h₁ h₂ hk)) (M := ML2 D h₁ h₂ hk),
          Work.MotC2.transAlgEquiv_add]
      have hR : AM2_rhoFun D hD h₁ h₂ hk h₂ h₂0 (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk) σ *
            Θ.restrictScalars K =
          (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
              (A₂ + WeierstrassCurve.Affine.Point.map (W' := D.E) (S := K)
                (F := ↥(KummerField2 K h₁ h₂ hk)) (K := ↥(KummerField2 K h₁ h₂ hk))
                σ.toAlgHom Q)).restrictScalars K * AM2_coeffAut D hD h₁ h₂ hk σ := by
        rw [AM2_rhoFun, mul_assoc, hσ₂, hγτ, ← mul_assoc, ← T4_res_mul (R := K) (S := ↥(KummerField2 K h₁ h₂ hk)) (M := ML2 D h₁ h₂ hk),
          Work.MotC2.transAlgEquiv_add]
      rw [hL, hR] at hcmpE
      have hpt := mul_right_cancel hcmpE
      have hτeq : Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
            (Q + A₁) =
          Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
            (A₂ + WeierstrassCurve.Affine.Point.map (W' := D.E) (S := K)
              (F := ↥(KummerField2 K h₁ h₂ hk)) (K := ↥(KummerField2 K h₁ h₂ hk))
              σ.toAlgHom Q) := by
        ext x
        exact AlgEquiv.congr_fun hpt x
      have hfin := Work.MotC2.transAlgEquiv_injective
        (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) hτeq
      calc WeierstrassCurve.Affine.Point.map (W' := D.E) (S := K)
              (F := ↥(KummerField2 K h₁ h₂ hk)) (K := ↥(KummerField2 K h₁ h₂ hk))
              σ.toAlgHom Q
          = (WeierstrassCurve.Affine.Point.map (W' := D.E) (S := K)
              (F := ↥(KummerField2 K h₁ h₂ hk)) (K := ↥(KummerField2 K h₁ h₂ hk))
              σ.toAlgHom Q + A₂) - A₂ := by abel
        _ = (Q + A₁) - A₂ := by rw [hfin, add_comm]
        _ = Q + (A₁ - A₂) := by abel
    · -- the diagonal action
      have hpos : ∀ (m : ℕ) (i : Fin 5),
          (algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk)
              ((zL2 K h₁ h₂ hk) ^ m)) ^ (i : ℕ) =
            (algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk) (zL2 K h₁ h₂ hk)) ^
              ((i : ℕ) * m) := by
        intro m i
        rw [map_pow, ← pow_mul, Nat.mul_comm m (i : ℕ)]
      have hA₁'all : ∀ i : Fin 5,
          Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A₁
            (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
              Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) =
          (algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk)
              ((zL2 K h₁ h₂ hk) ^ (AM2_mK D hD h₁ h₂ hk h₁ h₁0
                (wL1 K h₁ h₂ hk) (wL1_pow_five K h₁ h₂ hk) σ))) ^ (i : ℕ) *
            (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
              Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) := by
        intro i
        rw [hr₁ i, hpos]
      have hA₂'all : ∀ i : Fin 5,
          Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A₂
            (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
              Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) =
          (algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk)
              ((zL2 K h₁ h₂ hk) ^ (AM2_mK D hD h₁ h₂ hk h₂ h₂0
                (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk) σ))) ^ (i : ℕ) *
            (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
              Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) := by
        intro i
        rw [hr₂ i, hpos]
      have hA₂neg : ∀ i : Fin 5,
          Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) (-A₂)
            (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
              Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) =
          (algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk)
              (((zL2 K h₁ h₂ hk) ^ (AM2_mK D hD h₁ h₂ hk h₂ h₂0
                (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk) σ)))⁻¹) ^ (i : ℕ) *
            (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
              Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) := by
        intro i
        have h := transAlgEquiv_neg_ratio D h₁ h₂ hk A₂
          ((zL2 K h₁ h₂ hk) ^ (AM2_mK D hD h₁ h₂ hk h₂ h₂0
            (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk) σ)) hA₂'all i
        rw [h, map_inv₀, inv_pow]
      have hsum := T4_ratio_add D h₁ h₂ hk A₁ (-A₂)
        ((zL2 K h₁ h₂ hk) ^ (AM2_mK D hD h₁ h₂ hk h₁ h₁0
          (wL1 K h₁ h₂ hk) (wL1_pow_five K h₁ h₂ hk) σ))
        (((zL2 K h₁ h₂ hk) ^ (AM2_mK D hD h₁ h₂ hk h₂ h₂0
          (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk) σ))⁻¹) hA₁'all hA₂neg
      have hσw : σ (wL1 K h₁ h₂ hk / wL2 K h₁ h₂ hk) / (wL1 K h₁ h₂ hk / wL2 K h₁ h₂ hk) =
          (zL2 K h₁ h₂ hk) ^ (AM2_mK D hD h₁ h₂ hk h₁ h₁0
              (wL1 K h₁ h₂ hk) (wL1_pow_five K h₁ h₂ hk) σ) /
            (zL2 K h₁ h₂ hk) ^ (AM2_mK D hD h₁ h₂ hk h₂ h₂0
              (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk) σ) := by
        have e1 : (zL2 K h₁ h₂ hk) ^ (AM2_mK D hD h₁ h₂ hk h₁ h₁0
              (wL1 K h₁ h₂ hk) (wL1_pow_five K h₁ h₂ hk) σ) =
            σ (wL1 K h₁ h₂ hk) / wL1 K h₁ h₂ hk := by
          rw [AM2_zL_pow_mK D hD h₁ h₂ hk h₁ h₁0 (wL1 K h₁ h₂ hk)
            (wL1_pow_five K h₁ h₂ hk) σ, AM2_cK]
        have e2 : (zL2 K h₁ h₂ hk) ^ (AM2_mK D hD h₁ h₂ hk h₂ h₂0
              (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk) σ) =
            σ (wL2 K h₁ h₂ hk) / wL2 K h₁ h₂ hk := by
          rw [AM2_zL_pow_mK D hD h₁ h₂ hk h₂ h₂0 (wL2 K h₁ h₂ hk)
            (wL2_pow_five K h₁ h₂ hk) σ, AM2_cK]
        rw [e1, e2, map_div₀]
        simp only [div_eq_mul_inv, mul_inv_rev]
        refl_ring1
      have hcw2 : algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk)
            ((zL2 K h₁ h₂ hk) ^ (AM2_mK D hD h₁ h₂ hk h₁ h₁0
                (wL1 K h₁ h₂ hk) (wL1_pow_five K h₁ h₂ hk) σ) *
              (((zL2 K h₁ h₂ hk) ^ (AM2_mK D hD h₁ h₂ hk h₂ h₂0
                (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk) σ)))⁻¹) =
          algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk)
            (σ (wL1 K h₁ h₂ hk / wL2 K h₁ h₂ hk) /
              (wL1 K h₁ h₂ hk / wL2 K h₁ h₂ hk)) := by
        rw [hσw, map_mul, map_inv₀, map_div₀, div_eq_mul_inv]
      intro i
      rw [sub_eq_add_neg, hsum i, hcw2]
  obtain ⟨y, hy, hyeq⟩ := twistPointK_coords D hD h₁ h₂ hk (h := h₁ / h₂)
    (div_ne_zero h₁0 h₂0) (wL1 K h₁ h₂ hk / wL2 K h₁ h₂ hk) hw Q hQ'
  exact ⟨y, hy, fun k => by
    rw [show h₁ * h₂ ^ (-1 : ℤ) = h₁ / h₂ by rw [zpow_neg_one, div_eq_mul_inv]]
    exact hyeq k⟩

/-- **The `ε = 1` branch of the LAM arithmetic**: if the extension `Θ` of `θ` to `L(E)` is
`τ_Q ∘ [-1]`, then the twist `C_{h₁h₂}` has a `K`-point. -/
theorem T4_eps1 (D : Work.MotV.KleinData K) (hD : D.Good) (h₁ h₂ : K) (h₁0 : h₁ ≠ 0)
    (h₂0 : h₂ ≠ 0) (hk : ringChar K ≠ 5)
    [instDec : DecidableEq ↥(KummerField2 K h₁ h₂ hk)]
    [instEll : (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)).IsElliptic]
    (θ : twistFieldTK D h₁ ≃ₐ[K] twistFieldTK D h₂)
    (Θ : ML2 D h₁ h₂ hk ≃ₐ[↥(KummerField2 K h₁ h₂ hk)] ML2 D h₁ h₂ hk)
    (hΘ : ∀ x : ↥(AM21 D h₁ h₂ hk),
      (Θ (x : ML2 D h₁ h₂ hk) : ML2 D h₁ h₂ hk) =
        ((thetaL D hk θ x : ↥(AM22 D h₁ h₂ hk)) : ML2 D h₁ h₂ hk))
    (Q : (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)).toAffine.Point)
    (hQ : Θ = Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) Q *
      Work.MotC2.negAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))) :
    ∃ y : Fin 5 → K, y ≠ 0 ∧
      ∀ k, Work.MotV.kleinTw D.a D.b (h₁ * h₂ ^ (1 : ℤ)) y k = 0 := by
  have hw : (wL1 K h₁ h₂ hk * wL2 K h₁ h₂ hk) ^ 5 =
      algebraMap K ↥(KummerField2 K h₁ h₂ hk) (h₁ * h₂) := by
    rw [mul_pow, wL1_pow_five, wL2_pow_five, ← map_mul]
  have hQ' : ∀ σ : ↥(KummerField2 K h₁ h₂ hk) ≃ₐ[K] ↥(KummerField2 K h₁ h₂ hk),
      ∃ A : (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)).toAffine.Point,
        WeierstrassCurve.Affine.Point.map (W' := D.E) (S := K)
            (F := ↥(KummerField2 K h₁ h₂ hk)) (K := ↥(KummerField2 K h₁ h₂ hk))
            σ.toAlgHom (-Q) = (-Q) + A ∧
        ∀ i : Fin 5,
          Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A
              (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
                Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) =
            (algebraMap ↥(KummerField2 K h₁ h₂ hk)
                (Work.MotC2.Func (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)))
                (σ (wL1 K h₁ h₂ hk * wL2 K h₁ h₂ hk) /
                  (wL1 K h₁ h₂ hk * wL2 K h₁ h₂ hk))) ^ (i : ℕ) *
              (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
                Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) := by
    intro σ
    obtain ⟨A₁, hA₁, hr₁⟩ := sigma_pow_trans_ratio D hD h₁ h₂ hk
      (AM2_mK D hD h₁ h₂ hk h₁ h₁0 (wL1 K h₁ h₂ hk) (wL1_pow_five K h₁ h₂ hk) σ)
    obtain ⟨A₂, hA₂, hr₂⟩ := sigma_pow_trans_ratio D hD h₁ h₂ hk
      (AM2_mK D hD h₁ h₂ hk h₂ h₂0 (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk) σ)
    refine ⟨A₁ + A₂, ?_, ?_⟩
    · -- the point relation
      have hcmpE : Θ.restrictScalars K *
            AM2_rhoFun D hD h₁ h₂ hk h₁ h₁0 (wL1 K h₁ h₂ hk) (wL1_pow_five K h₁ h₂ hk) σ =
          AM2_rhoFun D hD h₁ h₂ hk h₂ h₂0 (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk) σ *
            Θ.restrictScalars K := by
        ext x
        rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
        exact T4_compare D hD h₁ h₂ h₁0 h₂0 hk θ Θ hΘ σ x
      have hσ₁ : (AM2_sigmaK D hD h₁ h₂ hk) ^
            (AM2_mK D hD h₁ h₂ hk h₁ h₁0 (wL1 K h₁ h₂ hk) (wL1_pow_five K h₁ h₂ hk) σ) =
          (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
            A₁).restrictScalars K := by
        have h2 : ((AM2_sigma D hD h₁ h₂ hk) ^
              (AM2_mK D hD h₁ h₂ hk h₁ h₁0 (wL1 K h₁ h₂ hk) (wL1_pow_five K h₁ h₂ hk)
                σ)).restrictScalars K =
            (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
              A₁).restrictScalars K := by
          rw [hA₁]
        rw [T4_res_pow] at h2
        exact h2
      have hσ₂ : (AM2_sigmaK D hD h₁ h₂ hk) ^
            (AM2_mK D hD h₁ h₂ hk h₂ h₂0 (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk) σ) =
          (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
            A₂).restrictScalars K := by
        have h2 : ((AM2_sigma D hD h₁ h₂ hk) ^
              (AM2_mK D hD h₁ h₂ hk h₂ h₂0 (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk)
                σ)).restrictScalars K =
            (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
              A₂).restrictScalars K := by
          rw [hA₂]
        rw [T4_res_pow] at h2
        exact h2
      have hnτ : (Work.MotC2.negAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))).restrictScalars K *
            (AM2_sigmaK D hD h₁ h₂ hk) ^
              (AM2_mK D hD h₁ h₂ hk h₁ h₁0 (wL1 K h₁ h₂ hk) (wL1_pow_five K h₁ h₂ hk) σ) =
          (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
            (-A₁)).restrictScalars K *
            (Work.MotC2.negAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))).restrictScalars K := by
        rw [hσ₁, ← T4_res_mul (R := K) (S := ↥(KummerField2 K h₁ h₂ hk))
          (M := ML2 D h₁ h₂ hk)]
        exact congrArg (fun e : ML2 D h₁ h₂ hk ≃ₐ[↥(KummerField2 K h₁ h₂ hk)]
          ML2 D h₁ h₂ hk => e.restrictScalars K)
          (Work.MotC2.negAlgEquiv_mul_transAlgEquiv
            (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A₁)
      have hnτ_pt : ∀ y : ML2 D h₁ h₂ hk,
          (Work.MotC2.negAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))).restrictScalars K
              (((AM2_sigmaK D hD h₁ h₂ hk) ^
                (AM2_mK D hD h₁ h₂ hk h₁ h₁0 (wL1 K h₁ h₂ hk) (wL1_pow_five K h₁ h₂ hk)
                  σ)) y) =
            (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
              (-A₁)).restrictScalars K
              ((Work.MotC2.negAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))).restrictScalars K y) := by
        intro y
        simp only [← AlgEquiv.mul_apply]
        rw [hnτ]
      have hγn : AM2_coeffAut D hD h₁ h₂ hk σ *
            (Work.MotC2.negAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))).restrictScalars K =
          (Work.MotC2.negAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))).restrictScalars K *
            AM2_coeffAut D hD h₁ h₂ hk σ := by
        ext x
        rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
        exact coeffAut_neg_comm D hD h₁ h₂ hk σ x
      have hγn_pt : ∀ y : ML2 D h₁ h₂ hk,
          (Work.MotC2.negAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))).restrictScalars K
              (AM2_coeffAut D hD h₁ h₂ hk σ y) =
            AM2_coeffAut D hD h₁ h₂ hk σ
              ((Work.MotC2.negAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))).restrictScalars K y) := by
        intro y
        simp only [← AlgEquiv.mul_apply]
        rw [hγn]
      have hγτ_pt : ∀ y : ML2 D h₁ h₂ hk,
          AM2_coeffAut D hD h₁ h₂ hk σ
              ((Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
                Q).restrictScalars K y) =
            (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
              (WeierstrassCurve.Affine.Point.map (W' := D.E) (S := K)
                (F := ↥(KummerField2 K h₁ h₂ hk)) (K := ↥(KummerField2 K h₁ h₂ hk))
                σ.toAlgHom Q)).restrictScalars K
              (AM2_coeffAut D hD h₁ h₂ hk σ y) := by
        intro y
        exact coeffAut_conj_trans D hD h₁ h₂ hk σ Q y
      have hL : Θ.restrictScalars K *
            AM2_rhoFun D hD h₁ h₂ hk h₁ h₁0 (wL1 K h₁ h₂ hk) (wL1_pow_five K h₁ h₂ hk) σ =
          (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
              (Q - A₁)).restrictScalars K *
            (AM2_coeffAut D hD h₁ h₂ hk σ *
              (Work.MotC2.negAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))).restrictScalars K) := by
        refine AlgEquiv.ext fun x => ?_
        calc (Θ.restrictScalars K *
              AM2_rhoFun D hD h₁ h₂ hk h₁ h₁0 (wL1 K h₁ h₂ hk) (wL1_pow_five K h₁ h₂ hk) σ) x
            = (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) Q).restrictScalars K
                ((Work.MotC2.negAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))).restrictScalars K
                  (((AM2_sigmaK D hD h₁ h₂ hk) ^
                    (AM2_mK D hD h₁ h₂ hk h₁ h₁0 (wL1 K h₁ h₂ hk) (wL1_pow_five K h₁ h₂ hk)
                      σ)) (AM2_coeffAut D hD h₁ h₂ hk σ x))) := by
              rw [AM2_rhoFun, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hQ,
                T4_res_mul (R := K) (S := ↥(KummerField2 K h₁ h₂ hk)) (M := ML2 D h₁ h₂ hk),
                AlgEquiv.mul_apply]
          _ = (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) Q).restrictScalars K
                ((Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
                  (-A₁)).restrictScalars K
                  ((Work.MotC2.negAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))).restrictScalars K
                    (AM2_coeffAut D hD h₁ h₂ hk σ x))) := by
              rw [hnτ_pt]
          _ = (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
                (Q - A₁)).restrictScalars K
                ((Work.MotC2.negAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))).restrictScalars K
                  (AM2_coeffAut D hD h₁ h₂ hk σ x)) := by
              conv_lhs => rw [← AlgEquiv.mul_apply,
                ← T4_res_mul (R := K) (S := ↥(KummerField2 K h₁ h₂ hk)) (M := ML2 D h₁ h₂ hk),
                ← Work.MotC2.transAlgEquiv_add]
              rw [sub_eq_add_neg]
          _ = (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
                (Q - A₁)).restrictScalars K
                (AM2_coeffAut D hD h₁ h₂ hk σ
                  ((Work.MotC2.negAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))).restrictScalars K
                    x)) := by
              rw [hγn_pt]
          _ = ((Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
                (Q - A₁)).restrictScalars K *
                (AM2_coeffAut D hD h₁ h₂ hk σ *
                  (Work.MotC2.negAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))).restrictScalars K)) x := by
              rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
      have hR : AM2_rhoFun D hD h₁ h₂ hk h₂ h₂0 (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk) σ *
            Θ.restrictScalars K =
          (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
              (A₂ + WeierstrassCurve.Affine.Point.map (W' := D.E) (S := K)
                (F := ↥(KummerField2 K h₁ h₂ hk)) (K := ↥(KummerField2 K h₁ h₂ hk))
                σ.toAlgHom Q)).restrictScalars K *
            (AM2_coeffAut D hD h₁ h₂ hk σ *
              (Work.MotC2.negAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))).restrictScalars K) := by
        refine AlgEquiv.ext fun x => ?_
        calc (AM2_rhoFun D hD h₁ h₂ hk h₂ h₂0 (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk) σ *
              Θ.restrictScalars K) x
            = ((AM2_sigmaK D hD h₁ h₂ hk) ^
                (AM2_mK D hD h₁ h₂ hk h₂ h₂0 (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk) σ))
                ((AM2_coeffAut D hD h₁ h₂ hk σ
                  ((Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
                    Q).restrictScalars K
                    ((Work.MotC2.negAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))).restrictScalars K
                      x)))) := by
              rw [AM2_rhoFun, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hQ,
                T4_res_mul (R := K) (S := ↥(KummerField2 K h₁ h₂ hk)) (M := ML2 D h₁ h₂ hk),
                AlgEquiv.mul_apply]
          _ = ((AM2_sigmaK D hD h₁ h₂ hk) ^
                (AM2_mK D hD h₁ h₂ hk h₂ h₂0 (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk) σ))
                ((Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
                    (WeierstrassCurve.Affine.Point.map (W' := D.E) (S := K)
                      (F := ↥(KummerField2 K h₁ h₂ hk)) (K := ↥(KummerField2 K h₁ h₂ hk))
                      σ.toAlgHom Q)).restrictScalars K
                  (AM2_coeffAut D hD h₁ h₂ hk σ
                    ((Work.MotC2.negAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))).restrictScalars K
                      x))) := by
              rw [hγτ_pt]
          _ = (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
                (A₂ + WeierstrassCurve.Affine.Point.map (W' := D.E) (S := K)
                  (F := ↥(KummerField2 K h₁ h₂ hk)) (K := ↥(KummerField2 K h₁ h₂ hk))
                  σ.toAlgHom Q)).restrictScalars K
                (AM2_coeffAut D hD h₁ h₂ hk σ
                  ((Work.MotC2.negAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))).restrictScalars K
                    x)) := by
              conv_lhs => rw [hσ₂, ← AlgEquiv.mul_apply,
                ← T4_res_mul (R := K) (S := ↥(KummerField2 K h₁ h₂ hk)) (M := ML2 D h₁ h₂ hk),
                ← Work.MotC2.transAlgEquiv_add]
          _ = ((Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
                (A₂ + WeierstrassCurve.Affine.Point.map (W' := D.E) (S := K)
                  (F := ↥(KummerField2 K h₁ h₂ hk)) (K := ↥(KummerField2 K h₁ h₂ hk))
                  σ.toAlgHom Q)).restrictScalars K *
                (AM2_coeffAut D hD h₁ h₂ hk σ *
                  (Work.MotC2.negAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))).restrictScalars K)) x := by
              rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
      rw [hL, hR] at hcmpE
      have hpt := mul_right_cancel hcmpE
      have hτeq : Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
            (Q - A₁) =
          Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
            (A₂ + WeierstrassCurve.Affine.Point.map (W' := D.E) (S := K)
              (F := ↥(KummerField2 K h₁ h₂ hk)) (K := ↥(KummerField2 K h₁ h₂ hk))
              σ.toAlgHom Q) := by
        ext x
        exact AlgEquiv.congr_fun hpt x
      have hfin : Q - A₁ = A₂ + WeierstrassCurve.Affine.Point.map (W' := D.E) (S := K)
          (F := ↥(KummerField2 K h₁ h₂ hk)) (K := ↥(KummerField2 K h₁ h₂ hk))
          σ.toAlgHom Q :=
        Work.MotC2.transAlgEquiv_injective
          (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) hτeq
      have h2 : WeierstrassCurve.Affine.Point.map (W' := D.E) (S := K)
          (F := ↥(KummerField2 K h₁ h₂ hk)) (K := ↥(KummerField2 K h₁ h₂ hk))
          σ.toAlgHom Q = (Q - A₁) - A₂ :=
        eq_sub_iff_add_eq.mpr (by rw [hfin, add_comm])
      calc WeierstrassCurve.Affine.Point.map (W' := D.E) (S := K)
              (F := ↥(KummerField2 K h₁ h₂ hk)) (K := ↥(KummerField2 K h₁ h₂ hk))
              σ.toAlgHom (-Q)
          = -(WeierstrassCurve.Affine.Point.map (W' := D.E) (S := K)
              (F := ↥(KummerField2 K h₁ h₂ hk)) (K := ↥(KummerField2 K h₁ h₂ hk))
              σ.toAlgHom Q) := by rw [map_neg]
        _ = -((Q - A₁) - A₂) := by rw [h2]
        _ = -Q + (A₁ + A₂) := by abel
    · -- the diagonal action
      have hpos : ∀ (m : ℕ) (i : Fin 5),
          (algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk)
              ((zL2 K h₁ h₂ hk) ^ m)) ^ (i : ℕ) =
            (algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk) (zL2 K h₁ h₂ hk)) ^
              ((i : ℕ) * m) := by
        intro m i
        rw [map_pow, ← pow_mul, Nat.mul_comm m (i : ℕ)]
      have hA₁'all : ∀ i : Fin 5,
          Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A₁
            (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
              Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) =
          (algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk)
              ((zL2 K h₁ h₂ hk) ^ (AM2_mK D hD h₁ h₂ hk h₁ h₁0
                (wL1 K h₁ h₂ hk) (wL1_pow_five K h₁ h₂ hk) σ))) ^ (i : ℕ) *
            (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
              Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) := by
        intro i
        rw [hr₁ i, hpos]
      have hA₂'all : ∀ i : Fin 5,
          Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A₂
            (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
              Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) =
          (algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk)
              ((zL2 K h₁ h₂ hk) ^ (AM2_mK D hD h₁ h₂ hk h₂ h₂0
                (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk) σ))) ^ (i : ℕ) *
            (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
              Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) := by
        intro i
        rw [hr₂ i, hpos]
      have hsum := T4_ratio_add D h₁ h₂ hk A₁ A₂
        ((zL2 K h₁ h₂ hk) ^ (AM2_mK D hD h₁ h₂ hk h₁ h₁0
          (wL1 K h₁ h₂ hk) (wL1_pow_five K h₁ h₂ hk) σ))
        ((zL2 K h₁ h₂ hk) ^ (AM2_mK D hD h₁ h₂ hk h₂ h₂0
          (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk) σ)) hA₁'all hA₂'all
      have hσw : σ (wL1 K h₁ h₂ hk * wL2 K h₁ h₂ hk) / (wL1 K h₁ h₂ hk * wL2 K h₁ h₂ hk) =
          (zL2 K h₁ h₂ hk) ^ (AM2_mK D hD h₁ h₂ hk h₁ h₁0
              (wL1 K h₁ h₂ hk) (wL1_pow_five K h₁ h₂ hk) σ) *
            (zL2 K h₁ h₂ hk) ^ (AM2_mK D hD h₁ h₂ hk h₂ h₂0
              (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk) σ) := by
        have e1 : (zL2 K h₁ h₂ hk) ^ (AM2_mK D hD h₁ h₂ hk h₁ h₁0
              (wL1 K h₁ h₂ hk) (wL1_pow_five K h₁ h₂ hk) σ) =
            σ (wL1 K h₁ h₂ hk) / wL1 K h₁ h₂ hk := by
          rw [AM2_zL_pow_mK D hD h₁ h₂ hk h₁ h₁0 (wL1 K h₁ h₂ hk)
            (wL1_pow_five K h₁ h₂ hk) σ, AM2_cK]
        have e2 : (zL2 K h₁ h₂ hk) ^ (AM2_mK D hD h₁ h₂ hk h₂ h₂0
              (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk) σ) =
            σ (wL2 K h₁ h₂ hk) / wL2 K h₁ h₂ hk := by
          rw [AM2_zL_pow_mK D hD h₁ h₂ hk h₂ h₂0 (wL2 K h₁ h₂ hk)
            (wL2_pow_five K h₁ h₂ hk) σ, AM2_cK]
        rw [map_mul, e1, e2]
        simp only [div_eq_mul_inv, mul_inv_rev]
        refl_ring1
      have hcw3 : algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk)
            ((zL2 K h₁ h₂ hk) ^ (AM2_mK D hD h₁ h₂ hk h₁ h₁0
                (wL1 K h₁ h₂ hk) (wL1_pow_five K h₁ h₂ hk) σ) *
              (zL2 K h₁ h₂ hk) ^ (AM2_mK D hD h₁ h₂ hk h₂ h₂0
                (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk) σ)) =
          algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk)
            (σ (wL1 K h₁ h₂ hk * wL2 K h₁ h₂ hk) /
              (wL1 K h₁ h₂ hk * wL2 K h₁ h₂ hk)) := by
        rw [hσw]
      intro i
      rw [hsum i, hcw3]
  obtain ⟨y, hy, hyeq⟩ := twistPointK_coords D hD h₁ h₂ hk (h := h₁ * h₂)
    (mul_ne_zero h₁0 h₂0) (wL1 K h₁ h₂ hk * wL2 K h₁ h₂ hk) hw (-Q) hQ'
  exact ⟨y, hy, fun k => by
    rw [show h₁ * h₂ ^ (1 : ℤ) = h₁ * h₂ by rw [zpow_one]]
    exact hyeq k⟩

/-- **T4, the LAM arithmetic.**  A `K`-isomorphism `θ : F_{h₁} ≃ₐ[K] F_{h₂}` of the two T-twist
fields forces a `K`-point of the twisted Klein curve `C_{h₁·h₂^{ε}}` for `ε = ±1`. -/
theorem T4_main {K : Type} [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (h₁ h₂ : K) (h₁0 : h₁ ≠ 0) (h₂0 : h₂ ≠ 0) (hk : ringChar K ≠ 5)
    (θ : twistFieldTK D h₁ ≃ₐ[K] twistFieldTK D h₂) :
    ∃ ε : ℤˣ, ∃ y : Fin 5 → K, y ≠ 0 ∧
      ∀ k, Work.MotV.kleinTw D.a D.b (h₁ * h₂ ^ (ε : ℤ)) y k = 0 := by
  letI : DecidableEq ↥(KummerField2 K h₁ h₂ hk) := Classical.decEq _
  haveI hEll : (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)).IsElliptic := by
    haveI hE := hD.elliptic
    show (D.E.map (algebraMap K ↥(KummerField2 K h₁ h₂ hk))).IsElliptic
    infer_instance
  obtain ⟨Θ, hΘ⟩ := exists_algEquiv_ML2 D hD h₁0 h₂0 hk θ
  obtain ⟨Q, ε, hQ⟩ := c2_over_ML2 D hD h₁ h₂ hk Θ
  fin_cases ε
  · have hQ0 : Θ = Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) Q := by
      simpa using hQ
    obtain ⟨y, hy, hyeq⟩ := T4_eps0 D hD h₁ h₂ h₁0 h₂0 hk θ Θ hΘ Q hQ0
    refine ⟨-1, y, hy, fun k => ?_⟩
    have : ((-1 : ℤˣ) : ℤ) = -1 := rfl
    rw [this]
    exact hyeq k
  · have hQ1 : Θ = Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) Q *
        Work.MotC2.negAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) := by
      simpa using hQ
    obtain ⟨y, hy, hyeq⟩ := T4_eps1 D hD h₁ h₂ h₁0 h₂0 hk θ Θ hΘ Q hQ1
    refine ⟨1, y, hy, fun k => ?_⟩
    have : ((1 : ℤˣ) : ℤ) = 1 := rfl
    rw [this]
    exact hyeq k

end

end Work.MotT
