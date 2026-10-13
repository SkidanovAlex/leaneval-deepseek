import Mathlib
import Submission.Work.WilE3.Taylor.CaseII.Defs

/-!
  annals_wilkies_conjecture, AREA E3 / Taylor / CaseII: the analytic data of `sphSys_det_ne`.
  Definitions only; statements about them are proved in the companion modules.
-/

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open WilkiesDesign.E

namespace Work.WilE3.Taylor.CaseII

variable {k r : ℕ}

/-- `∂ᵢ Φ` evaluated at `x`. -/
def Wq (c : EAChain k r) (Φ : EAPoly k r) (i : Fin k) (x : Fin k → ℝ) : ℝ :=
  eaEval c (eaD c i Φ) x

/-- `∂ᵢ(∑ ∂ₗ Φ^2)` evaluated at `x`, i.e. `∂ᵢ G`. -/
def dGq (c : EAChain k r) (Φ : EAPoly k r) (i : Fin k) (x : Fin k → ℝ) : ℝ :=
  eaEval c (eaD c i (sqGrad c Φ)) x

/-- The squared gradient norm `G = ∑ ∂ₗ Φ^2` evaluated at `x`. -/
def Gq (c : EAChain k r) (Φ : EAPoly k r) (x : Fin k → ℝ) : ℝ :=
  eaEval c (sqGrad c Φ) x

/-- The `i`-th coordinate of `x - y`. -/
def Tq (y : Fin k → ℝ) (i : Fin k) (x : Fin k → ℝ) : ℝ := x i - y i

/-- `mu = ∂ᵢ₀ Φ * (x j₀ - y j₀) - ∂ⱼ₀ Φ * (x i₀ - y i₀)`. -/
def muq (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (i₀ j₀ : Fin k)
    (x : Fin k → ℝ) : ℝ :=
  Wq c Φ i₀ x * Tq y j₀ x - Wq c Φ j₀ x * Tq y i₀ x

/-- The square of the distance to `y` (the sphere function without its level). -/
def Sq (y : Fin k → ℝ) (x : Fin k → ℝ) : ℝ :=
  ∑ i : Fin k, (Tq y i x) ^ 2

/-- The open set `{mu ≠ 0}` on which every division below is legitimate. -/
def Uset (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (i₀ j₀ : Fin k) :
    Set (Fin k → ℝ) :=
  {x | muq c Φ y i₀ j₀ x ≠ 0}

/-- The `x`-dependent part of the radial shear form: `shA_l = P_l / (G * mu)`. -/
def shA (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (i₀ j₀ l : Fin k) :
    (Fin k → ℝ) → ℝ :=
  fun x =>
    (dGq c Φ i₀ x * (Wq c Φ j₀ x * Tq y l x - Wq c Φ l x * Tq y j₀ x)
      - dGq c Φ j₀ x * (Wq c Φ i₀ x * Tq y l x - Wq c Φ l x * Tq y i₀ x)
      + dGq c Φ l x * muq c Φ y i₀ j₀ x) / (Gq c Φ x * muq c Φ y i₀ j₀ x)

/-- The coefficient of `v i₀` in the radial shear form. -/
def shB1 (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (i₀ j₀ l : Fin k) :
    (Fin k → ℝ) → ℝ :=
  fun x => (Wq c Φ j₀ x * Tq y l x - Wq c Φ l x * Tq y j₀ x) / muq c Φ y i₀ j₀ x

/-- The coefficient of `v j₀` in the radial shear form. -/
def shB2 (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (i₀ j₀ l : Fin k) :
    (Fin k → ℝ) → ℝ :=
  fun x => -((Wq c Φ i₀ x * Tq y l x - Wq c Φ l x * Tq y i₀ x) / muq c Φ y i₀ j₀ x)

/-- The radial shear form `shA_l + v_l + shB1_l v i₀ + shB2_l v j₀` of the `l`-th row. -/
def shfun (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (i₀ j₀ l : Fin k)
    (v : Fin k → ℝ) : (Fin k → ℝ) → ℝ :=
  fun x => shA c Φ y i₀ j₀ l x + v l + shB1 c Φ y i₀ j₀ l x * v i₀
    + shB2 c Φ y i₀ j₀ l x * v j₀

/-- The `x`-dependent part of the master system. -/
def Amas (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (i₀ j₀ : Fin k) :
    (Fin k → ℝ) → (Fin k → ℝ) :=
  fun x i => if i = i₀ then eaEval c Φ x else if i = j₀ then Sq y x
    else shA c Φ y i₀ j₀ i x

/-- The parameter direction of the master system. -/
def bmas (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (i₀ j₀ : Fin k) :
    (Fin k → ℝ) → (Fin 2 → ℝ) →L[ℝ] (Fin k → ℝ) :=
  fun x => ContinuousLinearMap.pi fun i : Fin k =>
    if i = i₀ ∨ i = j₀ then 0
    else shB1 c Φ y i₀ j₀ i x • (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin 2 => ℝ) 0)
      + shB2 c Φ y i₀ j₀ i x • (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin 2 => ℝ) 1)

/-- The shear parameters as a point of `Fin 2 → ℝ`. -/
def shearParam (v : Fin k → ℝ) (i₀ j₀ : Fin k) : Fin 2 → ℝ :=
  fun t => if t = 0 then v i₀ else v j₀

/-- The master map of the boundary system. -/
def MasterFun (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (i₀ j₀ : Fin k)
    (v : Fin k → ℝ) : (Fin k → ℝ) → (Fin k → ℝ) :=
  fun x => Amas c Φ y i₀ j₀ x + bmas c Φ y i₀ j₀ x (shearParam v i₀ j₀)

/-! ## The parametrization of the boundary system -/

/-- The target coordinates of the shear system, as a function of `((v, δ2), c)`:
`κ i₀ = c`, `κ j₀ = δ2` and `κ l = -v l` for `l` not in `{i₀, j₀}`. -/
def kappaLV (k : ℕ) (i₀ j₀ : Fin k) (hij : i₀ ≠ j₀) :
    ((Fin k → ℝ) × ℝ) × ℝ →ₗ[ℝ] (Fin k → ℝ) where
  toFun p := fun i => if i = i₀ then p.2 else if i = j₀ then p.1.2 else -(p.1.1 i)
  map_add' p q := by
    funext i
    by_cases h₁ : i = i₀
    · simp [h₁]
    · by_cases h₂ : i = j₀
      · simp [h₁, h₂, Ne.symm hij]
      · simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, if_neg h₁, if_neg h₂, neg_add] <;>
          ring
  map_smul' r p := by
    funext i
    by_cases h₁ : i = i₀
    · simp [h₁]
    · by_cases h₂ : i = j₀
      · simp [h₁, h₂, Ne.symm hij]
      · simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply,
          if_neg h₁, if_neg h₂, mul_neg] <;>
          ring

/-- The shear parameters `(v i₀, v j₀)`. -/
def thetaLV (k : ℕ) (i₀ j₀ : Fin k) :
    ((Fin k → ℝ) × ℝ) × ℝ →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun p := fun t => if t = 0 then p.1.1 i₀ else p.1.1 j₀
  map_add' p q := by
    funext t
    by_cases h : t = 0 <;> simp [h]
  map_smul' r p := by
    funext t
    by_cases h : t = 0 <;> simp [h]

/-- The inverse parametrization. -/
def TparamInv (k : ℕ) (i₀ j₀ : Fin k) (q : (Fin k → ℝ) × (Fin 2 → ℝ)) :
    ((Fin k → ℝ) × ℝ) × ℝ :=
  (((fun i => if i = i₀ then q.2 0 else if i = j₀ then q.2 1 else -(q.1 i)), q.1 j₀), q.1 i₀)

/-- The parametrization equivalence of the boundary system. -/
def TparamLV (k : ℕ) (i₀ j₀ : Fin k) (hij : i₀ ≠ j₀) :
    (((Fin k → ℝ) × ℝ) × ℝ) ≃ₗ[ℝ]
      ((Fin k → ℝ) × (Fin 2 → ℝ)) where
  toFun p := (kappaLV k i₀ j₀ hij p, thetaLV k i₀ j₀ p)
  invFun := TparamInv k i₀ j₀
  map_add' p q := by
    refine Prod.ext ?_ ?_
    · exact (kappaLV k i₀ j₀ hij).map_add p q
    · exact (thetaLV k i₀ j₀).map_add p q
  map_smul' r p := by
    refine Prod.ext ?_ ?_
    · exact (kappaLV k i₀ j₀ hij).map_smul r p
    · exact (thetaLV k i₀ j₀).map_smul r p
  left_inv p := by
    refine Prod.ext ?_ ?_
    · refine Prod.ext ?_ ?_
      · funext i
        by_cases h₁ : i = i₀
        · rw [h₁]; simp [TparamInv, kappaLV, thetaLV]
        · by_cases h₂ : i = j₀
          · rw [h₂]; simp [TparamInv, kappaLV, thetaLV, Ne.symm hij]
          · simp [TparamInv, kappaLV, thetaLV, h₁, h₂, neg_neg]
      · simp [TparamInv, kappaLV, thetaLV, Ne.symm hij]
    · simp [TparamInv, kappaLV, thetaLV]
  right_inv q := by
    refine Prod.ext ?_ ?_
    · funext i
      by_cases h₁ : i = i₀
      · rw [h₁]; simp [TparamInv, kappaLV, thetaLV]
      · by_cases h₂ : i = j₀
        · rw [h₂]; simp [TparamInv, kappaLV, thetaLV, Ne.symm hij]
        · simp [TparamInv, kappaLV, thetaLV, h₁, h₂, neg_neg]
    · funext t
      by_cases h : t = 0
      · rw [h]; simp [TparamInv, kappaLV, thetaLV]
      · have ht : t = 1 := by fin_cases t <;> simp_all
        rw [ht]; simp [TparamInv, kappaLV, thetaLV, Ne.symm hij]

end Work.WilE3.Taylor.CaseII
