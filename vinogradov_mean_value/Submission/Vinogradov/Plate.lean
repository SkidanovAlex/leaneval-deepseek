/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.AffinePush
import Submission.Vinogradov.Nikolskii

/-!
# Plates of the moment curve (GLYZ, arXiv:1912.09798)

This module starts the formalisation of the *bilinear "short proof"* of ℓ²
decoupling for the moment curve (Guo–Li–Yung–Zorin-Kranich, arXiv:1912.09798),
the route recommended in `ROADMAP.lean` (session 28) as the replacement for
BDG's §§6–8 (which need the multilinear Kakeya/BCCT input and contain the
refuted §5/§7 same-weight Corollary).

## The objects

For `k ≥ 1`, `i ≥ 0` and `t ∈ ℝ` we let `γ^{(i)}(t)` be the `i`-th derivative of
the moment curve `γ(t) = (t, t², …, tᵏ)`; in coordinates

    `(γ^{(i)}(t))_j = (j+1)^{↓i} · t^{j+1-i}`     (falling factorial, `= 0` if `i > j+1`),

which is `gammaDeriv`.  The **plate** `𝒰_J` of a dyadic interval `J` centred at `c`
of length `δ` is the parallelepiped of dimensions `δ¹ × … × δᵏ` centred at `γ(c)`
with sides parallel to `γ^{(1)}(c), …, γ^{(k)}(c)`:

    `plate k δ c = {γ(c) + Σ_i u_i γ^{(i)}(c) | |u_i| ≤ δ^i}`,

and the **polar plate** `𝒰_J^o` is the parallelepiped of dimensions
`δ^{-1} × … × δ^{-k}`

    `polarPlate k δ c = {x | |⟪x, γ^{(i)}(c)⟫| ≤ δ^{-i}, 1 ≤ i ≤ k}`.

## The affine rescaling identity

The algebraic heart of GLYZK §2 is the *affine rigidity* of the moment curve
`momPhase_affine` (`Rescaling.lean`): for `A = affVec k ρ t₀`,

    `⟪A x, γ(t)⟫ = ⟪x, γ(ρ t + t₀)⟫ - ⟪x, γ(t₀)⟫`,

i.e. `A` is the adjoint of the affine map `A_I` of GLYZK which sends `γ(t)` to
`γ(ρ t + t₀)`.  Writing `affVecDual k ρ t₀` for the *transpose* of `A` (the map
GLYZ call `A_I`, without the translation), the identity above is equivalent to
the pair

    `affVecDual k ρ t₀ (γ(t)) = γ(ρ t + t₀) - γ(t₀)`,
    `affVecDual k ρ t₀ (γ^{(i)}(t)) = ρ^i · γ^{(i)}(ρ t + t₀)`   (`i ≥ 1`),

proved below (`affVecDual_gammaVec`, `affVecDual_gammaDeriv`).  These give the
exact set identities

    `affMap k ρ t₀ '' plate k δ c = plate k (ρδ) (ρc + t₀)`,
    `affVecDual k ρ t₀ ⁻¹' polarPlate k (δ/ρ) ((c-a)/ρ) = polarPlate k δ c`,

which are the form in which GLYZK's affine rescaling Lemma 2.2 is used.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Interval Topology RealInnerProductSpace
open LeanEval.NumberTheory.VinogradovMeanValue

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Vinogradov

/-! ## 1. The derivatives of the moment curve -/

/-- The `i`-th derivative of the moment curve at `t`: its `j`-th coordinate is
`(j+1)^{↓i} · t^{j+1-i}` (a falling factorial; `0` when `i > j+1`). -/
noncomputable def gammaDeriv (k : ℕ) (i : ℕ) (t : ℝ) : E k :=
  (WithLp.equiv 2 (Fin k → ℝ)).symm
    (fun j => ((j.val + 1).descFactorial i : ℝ) * t ^ (j.val + 1 - i))

/-- Defining equation of `gammaDeriv`. -/
lemma gammaDeriv_apply (k i : ℕ) (t : ℝ) (j : Fin k) :
    gammaDeriv k i t j = ((j.val + 1).descFactorial i : ℝ) * t ^ (j.val + 1 - i) := rfl

/-- The `0`-th derivative is the moment curve itself. -/
lemma gammaDeriv_zero (k : ℕ) (t : ℝ) : gammaDeriv k 0 t = gammaVec k t := by
  ext j
  rw [gammaDeriv_apply, gammaVec_apply, Nat.descFactorial_zero, Nat.cast_one, tsub_zero, one_mul]

/-- The first derivative of the moment curve, explicitly. -/
lemma gammaDeriv_one_apply (k : ℕ) (t : ℝ) (j : Fin k) :
    gammaDeriv k 1 t j = ((j.val + 1 : ℕ) : ℝ) * t ^ j.val := by
  rw [gammaDeriv_apply, Nat.descFactorial_one, Nat.succ_sub_one]

/-! ## 2. The transpose of the affine map: GLYZ's `A_I` -/

/-- **GLYZ's affine map `A_I`, linear part only.**  `affVecDual k ρ t₀` is the
transpose of `affVec k ρ t₀`; together with the translation `γ(t₀)` it is the
map of GLYZK §2 that sends `γ(t)` to `γ(ρ t + t₀)`
(`affVecDual_gammaVec`), and its derivatives
(`affVecDual_gammaDeriv`). -/
noncomputable def affVecDual (k : ℕ) (ρ t₀ : ℝ) (x : E k) : E k :=
  (WithLp.equiv 2 (Fin k → ℝ)).symm
    (fun l => ∑ j : Fin k, x j * ((l.val + 1).choose (j.val + 1) : ℝ)
      * ρ ^ (j.val + 1) * t₀ ^ (l.val - j.val))

/-- Defining equation of `affVecDual`. -/
lemma affVecDual_apply (k : ℕ) (ρ t₀ : ℝ) (x : E k) (l : Fin k) :
    affVecDual k ρ t₀ x l = ∑ j : Fin k, x j
      * ((l.val + 1).choose (j.val + 1) : ℝ) * ρ ^ (j.val + 1)
      * t₀ ^ (l.val - j.val) := rfl

/-- `affVecDual k ρ t₀` as a linear map. -/
noncomputable def affVecDualLin (k : ℕ) (ρ t₀ : ℝ) : E k →ₗ[ℝ] E k where
  toFun := affVecDual k ρ t₀
  map_add' := by
    intro x y
    ext l
    simp only [PiLp.add_apply, affVecDual_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  map_smul' := by
    intro c x
    ext l
    simp only [RingHom.id_apply, PiLp.smul_apply, smul_eq_mul, affVecDual_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring

/-- Defining equation of `affVecDualLin`. -/
lemma affVecDualLin_apply (k : ℕ) (ρ t₀ : ℝ) (x : E k) :
    affVecDualLin k ρ t₀ x = affVecDual k ρ t₀ x := rfl

/-- **`affVecDual` is the transpose of `affVec`.** -/
lemma inner_affVec_affVecDual (k : ℕ) (ρ t₀ : ℝ) (x y : E k) :
    ⟪affVecDual k ρ t₀ x, y⟫ = ⟪x, affVec k ρ t₀ y⟫ := by
  rw [inner_coord, inner_coord]
  simp only [affVecDual_apply, affVec_apply, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-! ## 4. The affine image of a plate -/

/-- The subtraction form of `momPhase_affine`. -/
lemma momPhase_affine_sub (k : ℕ) (x : E k) (ρ t₀ t : ℝ) :
    momPhase k (affVec k ρ t₀ x) t = momPhase k x (ρ * t + t₀) - momPhase k x t₀ := by
  rw [momPhase_affine]
  ring

/-- **The transpose of the affine map sends the moment curve to the affine image
of the moment curve**: `affVecDual k ρ t₀ (γ(t)) = γ(ρ t + t₀) - γ(t₀)`. -/
lemma affVecDual_gammaVec (k : ℕ) (ρ t₀ t : ℝ) :
    affVecDual k ρ t₀ (gammaVec k t) = gammaVec k (ρ * t + t₀) - gammaVec k t₀ := by
  have h : ∀ x : E k, ⟪affVecDual k ρ t₀ (gammaVec k t), x⟫
      = ⟪gammaVec k (ρ * t + t₀) - gammaVec k t₀, x⟫ := by
    intro x
    rw [inner_affVec_affVecDual, real_inner_comm, inner_gamma, momPhase_affine_sub, inner_sub_left]
    have h1 : (⟪gammaVec k (ρ * t + t₀), x⟫ : ℝ) = momPhase k x (ρ * t + t₀) := by
      rw [real_inner_comm, inner_gamma]
    have h2 : (⟪gammaVec k t₀, x⟫ : ℝ) = momPhase k x t₀ := by rw [real_inner_comm, inner_gamma]
    rw [h1, h2]
  have hz : ∀ y : E k,
      ⟪affVecDual k ρ t₀ (gammaVec k t) - (gammaVec k (ρ * t + t₀) - gammaVec k t₀), y⟫ = 0 := by
    intro y
    rw [inner_sub_left, h y, sub_self]
  have hself : ⟪affVecDual k ρ t₀ (gammaVec k t) - (gammaVec k (ρ * t + t₀) - gammaVec k t₀),
      affVecDual k ρ t₀ (gammaVec k t) - (gammaVec k (ρ * t + t₀) - gammaVec k t₀)⟫ = 0 := by
    rw [real_inner_comm]
    exact hz _
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hself)


/-! ## 3. The affine rescaling identities -/

/-- Coordinate-wise derivative of `gammaDeriv`, in scalar pairing form. -/
lemma hasDerivAt_gammaDeriv_inner (k i : ℕ) (y : E k) (u : ℝ) :
    HasDerivAt (fun v : ℝ => ⟪y, gammaDeriv k i v⟫) ⟪y, gammaDeriv k (i + 1) u⟫ u := by
  have hcoord : ∀ j : Fin k, HasDerivAt
      (fun v : ℝ => y j * (((j.val + 1).descFactorial i : ℕ) : ℝ) * v ^ (j.val + 1 - i))
      (y j * (((j.val + 1).descFactorial (i + 1) : ℕ) : ℝ)
        * u ^ (j.val + 1 - (i + 1))) u := by
    intro j
    have h1 : HasDerivAt (fun v : ℝ => v ^ (j.val + 1 - i))
        (((j.val + 1 - i : ℕ) : ℝ) * u ^ (j.val + 1 - i - 1)) u := hasDerivAt_pow _ _
    have h2 := h1.const_mul (y j * (((j.val + 1).descFactorial i : ℕ) : ℝ))
    refine h2.congr_deriv ?_
    rw [Nat.descFactorial_succ]
    push_cast
    rw [show j.val + 1 - i - 1 = j.val - i by omega]
    ring
  have hsum : HasDerivAt
      (fun v : ℝ => ∑ j : Fin k,
        y j * (((j.val + 1).descFactorial i : ℕ) : ℝ) * v ^ (j.val + 1 - i))
      (∑ j : Fin k, y j * (((j.val + 1).descFactorial (i + 1) : ℕ) : ℝ)
        * u ^ (j.val + 1 - (i + 1))) u := by
    have := HasDerivAt.fun_sum (u := Finset.univ)
      (A := fun j v => y j * (((j.val + 1).descFactorial i : ℕ) : ℝ) * v ^ (j.val + 1 - i))
      (A' := fun j => y j * (((j.val + 1).descFactorial (i + 1) : ℕ) : ℝ)
        * u ^ (j.val + 1 - (i + 1)))
      (fun j _ => hcoord j)
    simpa using this
  convert hsum using 1
  · funext v
    rw [inner_coord]
    exact Finset.sum_congr rfl fun j _ => by rw [gammaDeriv_apply]; ring
  · rw [inner_coord]
    exact Finset.sum_congr rfl fun j _ => by rw [gammaDeriv_apply]; ring

/-- Chain-rule form of `hasDerivAt_gammaDeriv_inner`. -/
lemma hasDerivAt_gammaDeriv_inner_comp (k i : ℕ) (y : E k) (ρ t₀ u : ℝ) :
    HasDerivAt (fun v : ℝ => ⟪y, gammaDeriv k i (ρ * v + t₀)⟫)
      (ρ * ⟪y, gammaDeriv k (i + 1) (ρ * u + t₀)⟫) u := by
  have h1 := hasDerivAt_gammaDeriv_inner k i y (ρ * u + t₀)
  have h2 : HasDerivAt (fun v : ℝ => ρ * v + t₀) ρ u := by
    simpa using ((hasDerivAt_id u).const_mul ρ).add_const t₀
  simpa [Function.comp_def, smul_eq_mul, mul_comm] using h1.comp u h2

/-- The pairing form of the transpose identity. -/
lemma inner_affVecDual_gammaDeriv (k i : ℕ) (y : E k) (ρ t₀ v : ℝ) :
    ⟪y, affVecDual k ρ t₀ (gammaDeriv k i v)⟫ = ⟪affVec k ρ t₀ y, gammaDeriv k i v⟫ := by
  rw [real_inner_comm, inner_affVec_affVecDual]
  exact real_inner_comm _ _

/-- The derivative of the difference `affVecDual k ρ t₀ (γ^{(i)}(v)) − ρ^i γ^{(i)}(ρv+t₀)`,
in scalar pairing form. -/
lemma hasDerivAt_diff_gammaDeriv_inner (k i : ℕ) (y : E k) (ρ t₀ u : ℝ) :
    HasDerivAt (fun v : ℝ =>
        ⟪y, affVecDual k ρ t₀ (gammaDeriv k i v) - ρ ^ i • gammaDeriv k i (ρ * v + t₀)⟫)
      ⟪y, affVecDual k ρ t₀ (gammaDeriv k (i + 1) u)
        - ρ ^ (i + 1) • gammaDeriv k (i + 1) (ρ * u + t₀)⟫ u := by
  have hL : HasDerivAt (fun v : ℝ => ⟪y, affVecDual k ρ t₀ (gammaDeriv k i v)⟫)
      ⟪y, affVecDual k ρ t₀ (gammaDeriv k (i + 1) u)⟫ u := by
    simpa only [inner_affVecDual_gammaDeriv] using
      hasDerivAt_gammaDeriv_inner k i (affVec k ρ t₀ y) u
  have hR : HasDerivAt (fun v : ℝ => ⟪y, ρ ^ i • gammaDeriv k i (ρ * v + t₀)⟫)
      ⟪y, ρ ^ (i + 1) • gammaDeriv k (i + 1) (ρ * u + t₀)⟫ u := by
    have h1 : HasDerivAt (fun v : ℝ => ρ ^ i * ⟪y, gammaDeriv k i (ρ * v + t₀)⟫)
        (ρ ^ i * (ρ * ⟪y, gammaDeriv k (i + 1) (ρ * u + t₀)⟫)) u :=
      (hasDerivAt_gammaDeriv_inner_comp k i y ρ t₀ u).const_mul (ρ ^ i)
    convert h1 using 1
    · funext v
      rw [real_inner_smul_right]
    · rw [real_inner_smul_right]
      ring
  have hsub := hL.sub hR
  have hfun : ((fun v : ℝ => ⟪y, affVecDual k ρ t₀ (gammaDeriv k i v)⟫)
      - fun v : ℝ => ⟪y, ρ ^ i • gammaDeriv k i (ρ * v + t₀)⟫)
      = fun v : ℝ => ⟪y, affVecDual k ρ t₀ (gammaDeriv k i v)
          - ρ ^ i • gammaDeriv k i (ρ * v + t₀)⟫ := by
    funext v
    rw [Pi.sub_apply, inner_sub_right]
  have hder : (⟪y, affVecDual k ρ t₀ (gammaDeriv k (i + 1) u)⟫
      - ⟪y, ρ ^ (i + 1) • gammaDeriv k (i + 1) (ρ * u + t₀)⟫)
      = ⟪y, affVecDual k ρ t₀ (gammaDeriv k (i + 1) u)
          - ρ ^ (i + 1) • gammaDeriv k (i + 1) (ρ * u + t₀)⟫ := by
    rw [inner_sub_right]
  rw [hfun, hder] at hsub
  exact hsub

/-- **The affine rescaling identity for the derivatives of the moment curve.**
For `i ≥ 1`, the transpose `affVecDual k ρ t₀` of the affine map `affVec k ρ t₀`
sends `γ^{(i)}(t)` to `ρ^i · γ^{(i)}(ρ t + t₀)`. -/
theorem affVecDual_gammaDeriv (k : ℕ) (ρ t₀ : ℝ) :
    ∀ i : ℕ, ∀ t : ℝ, affVecDual k ρ t₀ (gammaDeriv k (i + 1) t)
      = ρ ^ (i + 1) • gammaDeriv k (i + 1) (ρ * t + t₀) := by
  intro i
  induction i with
  | zero =>
    intro t
    set V : E k := affVecDual k ρ t₀ (gammaDeriv k 1 t)
      - ρ ^ 1 • gammaDeriv k 1 (ρ * t + t₀) with hV
    have hz : ∀ y : E k, ⟪y, V⟫ = 0 := by
      intro y
      have h1 : HasDerivAt
          (fun v : ℝ => ⟪y, affVecDual k ρ t₀ (gammaVec k v) - gammaVec k (ρ * v + t₀)⟫)
          (⟪y, affVecDual k ρ t₀ (gammaDeriv k 1 t)
            - ρ ^ 1 • gammaDeriv k 1 (ρ * t + t₀)⟫) t := by
        simpa [gammaDeriv_zero, one_smul] using
          hasDerivAt_diff_gammaDeriv_inner k 0 y ρ t₀ t
      have h2 : HasDerivAt
          (fun v : ℝ => ⟪y, affVecDual k ρ t₀ (gammaVec k v) - gammaVec k (ρ * v + t₀)⟫) 0 t := by
        have hzero : (fun v : ℝ =>
            ⟪y, affVecDual k ρ t₀ (gammaVec k v) - gammaVec k (ρ * v + t₀)⟫)
            = fun _ => (-⟪y, gammaVec k t₀⟫) := by
          funext v
          rw [affVecDual_gammaVec]
          simp
        rw [hzero]
        exact hasDerivAt_const t _
      simpa [hV] using h1.unique h2
    have hself : ⟪V, V⟫ = 0 := by
      rw [real_inner_comm]
      exact hz V
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hself)
  | succ i ih =>
    intro t
    set V : E k := affVecDual k ρ t₀ (gammaDeriv k (i + 2) t)
      - ρ ^ (i + 2) • gammaDeriv k (i + 2) (ρ * t + t₀) with hV
    have hz : ∀ y : E k, ⟪y, V⟫ = 0 := by
      intro y
      have h1 := hasDerivAt_diff_gammaDeriv_inner k (i + 1) y ρ t₀ t
      have hzero : (fun v : ℝ =>
          ⟪y, affVecDual k ρ t₀ (gammaDeriv k (i + 1) v)
            - ρ ^ (i + 1) • gammaDeriv k (i + 1) (ρ * v + t₀)⟫) = fun _ => (0 : ℝ) := by
        funext v
        rw [ih v]
        simp
      have h2 : HasDerivAt (fun v : ℝ =>
          ⟪y, affVecDual k ρ t₀ (gammaDeriv k (i + 1) v)
            - ρ ^ (i + 1) • gammaDeriv k (i + 1) (ρ * v + t₀)⟫) 0 t := by
        rw [hzero]
        exact hasDerivAt_const t 0
      simpa [hV] using h1.unique h2
    have hself : ⟪V, V⟫ = 0 := by
      rw [real_inner_comm]
      exact hz V
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hself)



/-! ## 5. Plates and polar plates -/

/-- GLYZ's affine map `A_I`: `x ↦ γ(t₀) + affVecDual k ρ t₀ x`. -/
noncomputable def affMap (k : ℕ) (ρ t₀ : ℝ) (x : E k) : E k :=
  gammaVec k t₀ + affVecDual k ρ t₀ x

/-- Defining equation of `affMap`. -/
lemma affMap_apply (k : ℕ) (ρ t₀ : ℝ) (x : E k) :
    affMap k ρ t₀ x = gammaVec k t₀ + affVecDual k ρ t₀ x := rfl

/-- The cube of side parameters of a plate: `|y_i| ≤ (i+1)!`. -/
def plateBox (k : ℕ) : Set (E k) := {y | ∀ i : Fin k, |y i| ≤ ((i.val + 1).factorial : ℝ)}

/-- **The plate** `𝒰_J`: the parallelepiped of dimensions `δ¹ × δ² × ⋯ × δᵏ`
centred at `γ(t)`, with sides parallel to `γ^{(1)}(t), …, γ^{(k)}(t)`. -/
noncomputable def plate (k : ℕ) (δ : ℝ) (t : ℝ) : Set (E k) :=
  affMap k δ t '' plateBox k

/-- **The polar plate** `𝒰_J^o`: the parallelepiped of dimensions
`δ^{-1} × δ^{-2} × ⋯ × δ^{-k}` polar to `𝒰_J`. -/
def polarPlate (k : ℕ) (δ : ℝ) (t : ℝ) : Set (E k) :=
  {x | ∀ i : Fin k, |⟪x, gammaDeriv k (i.val + 1) t⟫| ≤ (δ ^ (i.val + 1))⁻¹}

/-- Membership in the polar plate, unfolded. -/
lemma mem_polarPlate_iff (k : ℕ) (δ : ℝ) (t : ℝ) (x : E k) :
    x ∈ polarPlate k δ t ↔ ∀ i : Fin k,
      |⟪x, gammaDeriv k (i.val + 1) t⟫| ≤ (δ ^ (i.val + 1))⁻¹ := Iff.rfl

/-- The `i`-th derivative of the moment curve at `0` is a multiple of the
`i`-th standard basis vector: `γ^{(i+1)}(0) = (i+1)! · e_i`. -/
lemma gammaDeriv_at_zero (k : ℕ) (i : Fin k) :
    gammaDeriv k (i.val + 1) 0 = ((i.val + 1).factorial : ℝ) • PiLp.single 2 i 1 := by
  ext l
  rw [gammaDeriv_apply, PiLp.smul_apply, smul_eq_mul, PiLp.single_apply]
  by_cases h : l = i
  · subst h
    rw [if_pos rfl, mul_one, Nat.descFactorial_self, tsub_self, pow_zero, mul_one]
  · rw [if_neg h, mul_zero]
    rcases lt_trichotomy (l.val + 1) (i.val + 1) with hlt | heq | hgt
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hlt, Nat.cast_zero, zero_mul]
    · exact absurd (Fin.ext (by omega)) h
    · have h0 : (0 : ℝ) ^ (l.val + 1 - (i.val + 1)) = 0 :=
        pow_eq_zero_iff'.mpr ⟨rfl, by omega⟩
      rw [h0, mul_zero]

/-- The action of `affVecDual` on a scalar multiple. -/
lemma affVecDual_smul (k : ℕ) (ρ t₀ : ℝ) (a : ℝ) (x : E k) :
    affVecDual k ρ t₀ (a • x) = a • affVecDual k ρ t₀ x :=
  (affVecDualLin k ρ t₀).map_smul a x

/-- The action of `affVecDual` on a finite sum. -/
lemma affVecDual_sum (k : ℕ) (ρ t₀ : ℝ) {ι : Type*} (s : Finset ι) (f : ι → E k) :
    affVecDual k ρ t₀ (∑ i ∈ s, f i) = ∑ i ∈ s, affVecDual k ρ t₀ (f i) :=
  map_sum (affVecDualLin k ρ t₀) f s

/-- The action of `affVecDual` on the standard basis. -/
lemma affVecDual_single (k : ℕ) (δ : ℝ) (t : ℝ) (i : Fin k) :
    affVecDual k δ t (PiLp.single 2 i 1)
      = (((i.val + 1).factorial : ℝ))⁻¹
        • (δ ^ (i.val + 1) • gammaDeriv k (i.val + 1) t) := by
  have h : affVecDual k δ t (gammaDeriv k (i.val + 1) 0)
      = δ ^ (i.val + 1) • gammaDeriv k (i.val + 1) t := by
    rw [affVecDual_gammaDeriv, mul_zero, zero_add]
  rw [gammaDeriv_at_zero, affVecDual_smul] at h
  rw [← h, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)), one_smul]

/-- The action of `affVecDualLin` on the standard basis. -/
lemma affVecDualLin_single (k : ℕ) (δ : ℝ) (t : ℝ) (i : Fin k) :
    affVecDualLin k δ t (PiLp.single 2 i 1)
      = (((i.val + 1).factorial : ℝ))⁻¹
        • (δ ^ (i.val + 1) • gammaDeriv k (i.val + 1) t) :=
  affVecDual_single k δ t i

/-- **Composition of the linear parts**: `A_ρt₀ ∘ A_δc = A_{ρδ, ρc+t₀}`. -/
lemma affVecDual_comp (k : ℕ) (ρ t₀ δ c : ℝ) (y : E k) :
    affVecDual k ρ t₀ (affVecDual k δ c y) = affVecDual k (ρ * δ) (ρ * c + t₀) y := by
  have hy : y = ∑ i : Fin k, (PiLp.basisFun 2 ℝ (Fin k)).repr y i • PiLp.single 2 i 1 := by
    conv_lhs => rw [← Module.Basis.sum_repr (PiLp.basisFun 2 ℝ (Fin k)) y]
    exact Finset.sum_congr rfl fun i _ => by rw [PiLp.basisFun_apply]
  conv_lhs => rw [hy]
  conv_rhs => rw [hy]
  rw [affVecDual_sum, affVecDual_sum, affVecDual_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [affVecDual_smul, affVecDual_single, affVecDual_gammaDeriv, smul_smul, mul_pow]
  ring_nf

/-- Composition of the linear parts, as a linear-map identity. -/
lemma affVecDualLin_comp (k : ℕ) (ρ t₀ δ c : ℝ) :
    (affVecDualLin k ρ t₀).comp (affVecDualLin k δ c)
      = affVecDualLin k (ρ * δ) (ρ * c + t₀) := by
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.comp_apply]
  exact affVecDual_comp k ρ t₀ δ c y


/-- The action of `affVecDual` on a sum. -/
lemma affVecDual_add (k : ℕ) (ρ t₀ : ℝ) (x y : E k) :
    affVecDual k ρ t₀ (x + y) = affVecDual k ρ t₀ x + affVecDual k ρ t₀ y :=
  (affVecDualLin k ρ t₀).map_add x y

/-- **The affine maps compose**: `A_ρt₀ ∘ A_δc = A_{ρδ, ρc + t₀}`. -/
lemma affMap_affMap (k : ℕ) (ρ t₀ δ c : ℝ) (y : E k) :
    affMap k ρ t₀ (affMap k δ c y) = affMap k (ρ * δ) (ρ * c + t₀) y := by
  rw [affMap_apply, affMap_apply, affMap_apply, affVecDual_add, affVecDual_gammaVec,
    affVecDual_comp]
  abel

/-- **The affine rescaling of the plate**: `A_ρt₀(𝒰_J) = 𝒰_{A_I(J)}`. -/
lemma affMap_image_plate (k : ℕ) (ρ t₀ δ c : ℝ) :
    affMap k ρ t₀ '' plate k δ c = plate k (ρ * δ) (ρ * c + t₀) := by
  rw [plate, plate, ← Set.image_comp]
  congr 1
  funext y
  rw [Function.comp_apply]
  exact affMap_affMap k ρ t₀ δ c y

/-- **The moment curve lies in its own plate**: `γ(t) ∈ 𝒰_{[c-δ,c+δ]}`. -/
lemma gammaVec_mem_plate (k : ℕ) {δ : ℝ} (hδ : 0 < δ) {c t : ℝ} (ht : |t - c| ≤ δ) :
    gammaVec k t ∈ plate k δ c := by
  refine ⟨gammaVec k ((t - c) / δ), ?_, ?_⟩
  · intro i
    rw [gammaVec_apply, abs_pow]
    calc |(t - c) / δ| ^ (i.val + 1) ≤ 1 ^ (i.val + 1) := by
          refine pow_le_pow_left₀ (abs_nonneg _) ?_ _
          rw [abs_div, abs_of_pos hδ]
          exact (div_le_one hδ).mpr ht
      _ = 1 := one_pow _
      _ ≤ ((i.val + 1).factorial : ℝ) := by
          exact_mod_cast Nat.factorial_pos (i.val + 1)
  · rw [affMap_apply, affVecDual_gammaVec, mul_div_cancel₀ (t - c) (ne_of_gt hδ), sub_add_cancel]
    abel

/-- **The pairing identity for `affVec` and the derivatives of the curve**:
`⟪A x, γ^{(i)}(v)⟫ = ρ^i ⟪x, γ^{(i)}(ρv + t₀)⟫`. -/
lemma inner_affVec_gammaDeriv (k : ℕ) (ρ t₀ : ℝ) (y : E k) (i : ℕ) (v : ℝ) :
    ⟪affVec k ρ t₀ y, gammaDeriv k (i + 1) v⟫
      = ρ ^ (i + 1) * ⟪y, gammaDeriv k (i + 1) (ρ * v + t₀)⟫ := by
  rw [← inner_affVecDual_gammaDeriv, affVecDual_gammaDeriv, real_inner_smul_right]

/-- **The polar plate rescales**: `A_I(𝒰^o_{J_I}) ⊆ 𝒰^o_J`. -/
lemma affVec_image_polarPlate (k : ℕ) {κ : ℝ} (hκ : 0 < κ) (a : ℝ) {δ : ℝ} {c : ℝ} :
    affVec k κ a '' polarPlate k δ c ⊆ polarPlate k (δ / κ) ((c - a) / κ) := by
  rintro _ ⟨y, hy, rfl⟩
  intro i
  have hdiv : 0 < κ := hκ
  rw [inner_affVec_gammaDeriv, mul_div_cancel₀ (c - a) (ne_of_gt hκ), sub_add_cancel, abs_mul,
    abs_of_nonneg (pow_nonneg hκ.le _)]
  have h1 : |⟪y, gammaDeriv k (i.val + 1) c⟫| ≤ (δ ^ (i.val + 1))⁻¹ := hy i
  have h2 : (0 : ℝ) ≤ κ ^ (i.val + 1) := pow_nonneg hκ.le _
  have h3 : κ ^ (i.val + 1) * (δ ^ (i.val + 1))⁻¹ = ((δ / κ) ^ (i.val + 1))⁻¹ := by
    rw [div_pow, inv_div, div_eq_mul_inv]
  calc κ ^ (i.val + 1) * |⟪y, gammaDeriv k (i.val + 1) c⟫|
      ≤ κ ^ (i.val + 1) * (δ ^ (i.val + 1))⁻¹ :=
        mul_le_mul_of_nonneg_left h1 h2
    _ = ((δ / κ) ^ (i.val + 1))⁻¹ := h3


/-- **The plate in curve coordinates.**  The linear part of `affMap` expands in
the basis of derivatives of the curve: `A_δt y = Σ_i (y_i/(i+1)!) δ^{i+1} γ^{(i+1)}(t)`. -/
lemma affVecDual_eq_sum_gammaDeriv (k : ℕ) (δ : ℝ) (t : ℝ) (y : E k) :
    affVecDual k δ t y
      = ∑ i : Fin k, (y i * (((i.val + 1).factorial : ℝ))⁻¹)
          • (δ ^ (i.val + 1) • gammaDeriv k (i.val + 1) t) := by
  have hy : y = ∑ i : Fin k, y i • PiLp.single 2 i 1 := by
    conv_lhs => rw [← Module.Basis.sum_repr (PiLp.basisFun 2 ℝ (Fin k)) y]
    exact Finset.sum_congr rfl fun i _ => by
      rw [PiLp.basisFun_repr, PiLp.basisFun_apply]
  conv_lhs => rw [hy]
  rw [affVecDual_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [affVecDual_smul, affVecDual_single, smul_smul]

/-- **The plate is adapted to the polar plate.**  For `x ∈ 𝒰_J` and `z ∈ 𝒰_J^o`,
`|⟪x − γ(c), z⟫| ≤ k`. -/
lemma abs_inner_sub_gammaVec_le_of_mem_plate (k : ℕ) {δ : ℝ} (hδ : 0 < δ) {t : ℝ}
    {x z : E k} (hx : x ∈ plate k δ t) (hz : z ∈ polarPlate k δ t) :
    |⟪x - gammaVec k t, z⟫| ≤ (k : ℝ) := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [affMap_apply, add_sub_cancel_left, affVecDual_eq_sum_gammaDeriv]
  have hsum : ⟪∑ i : Fin k, (y i * (((i.val + 1).factorial : ℝ))⁻¹)
        • (δ ^ (i.val + 1) • gammaDeriv k (i.val + 1) t), z⟫
      = ∑ i : Fin k, (y i * (((i.val + 1).factorial : ℝ))⁻¹)
        * (δ ^ (i.val + 1) * ⟪gammaDeriv k (i.val + 1) t, z⟫) := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_left, real_inner_smul_left]
  rw [hsum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ i : Fin k, |(y i * (((i.val + 1).factorial : ℝ))⁻¹)
      * (δ ^ (i.val + 1) * ⟪gammaDeriv k (i.val + 1) t, z⟫)| ≤ 1 := by
    intro i
    have hfact : (0 : ℝ) < ((i.val + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos (i.val + 1)
    have hδi : (0 : ℝ) < δ ^ (i.val + 1) := pow_pos hδ _
    have hz' : |⟪gammaDeriv k (i.val + 1) t, z⟫| ≤ (δ ^ (i.val + 1))⁻¹ := by
      rw [real_inner_comm]
      exact hz i
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hδi, abs_of_pos (inv_pos.mpr hfact)]
    calc |y i| * (((i.val + 1).factorial : ℝ))⁻¹
          * (δ ^ (i.val + 1) * |⟪gammaDeriv k (i.val + 1) t, z⟫|)
        ≤ ((i.val + 1).factorial : ℝ) * (((i.val + 1).factorial : ℝ))⁻¹
          * (δ ^ (i.val + 1) * (δ ^ (i.val + 1))⁻¹) := by
          have h8 : (0 : ℝ) ≤ δ ^ (i.val + 1) * (δ ^ (i.val + 1))⁻¹ := by positivity
          have h9 : (0 : ℝ) ≤ (((i.val + 1).factorial : ℝ))⁻¹ * δ ^ (i.val + 1) := by positivity
          have h10 : (0 : ℝ) ≤ ((i.val + 1).factorial : ℝ) := hfact.le
          calc |y i| * (((i.val + 1).factorial : ℝ))⁻¹
                * (δ ^ (i.val + 1) * |⟪gammaDeriv k (i.val + 1) t, z⟫|)
              = (|y i| * (((i.val + 1).factorial : ℝ))⁻¹ * δ ^ (i.val + 1))
                * |⟪gammaDeriv k (i.val + 1) t, z⟫| := by ring
            _ ≤ (((i.val + 1).factorial : ℝ) * (((i.val + 1).factorial : ℝ))⁻¹
                * δ ^ (i.val + 1)) * (δ ^ (i.val + 1))⁻¹ := by
                refine mul_le_mul ?_ hz' (abs_nonneg _) ?_
                · refine mul_le_mul_of_nonneg_right ?_ hδi.le
                  exact mul_le_mul_of_nonneg_right (hy i) (inv_nonneg.mpr hfact.le)
                · positivity
            _ = ((i.val + 1).factorial : ℝ) * (((i.val + 1).factorial : ℝ))⁻¹
                * (δ ^ (i.val + 1) * (δ ^ (i.val + 1))⁻¹) := by ring
      _ = 1 := by
          rw [mul_inv_cancel₀ (ne_of_gt hfact), mul_inv_cancel₀ (ne_of_gt hδi), mul_one]
  calc ∑ i : Fin k, |(y i * (((i.val + 1).factorial : ℝ))⁻¹)
        * (δ ^ (i.val + 1) * ⟪gammaDeriv k (i.val + 1) t, z⟫)|
      ≤ ∑ _i : Fin k, (1 : ℝ) := Finset.sum_le_sum fun i _ => hterm i
    _ = (k : ℝ) := by simp


/-- `A_{1,0}` is the identity. -/
lemma affVecDual_one_zero (k : ℕ) (y : E k) : affVecDual k 1 0 y = y := by
  ext l
  rw [affVecDual_apply, Finset.sum_eq_single l]
  · rw [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, one_pow]
    ring
  · intro j _ hj
    rcases lt_trichotomy j.val l.val with hlt | heq | hgt
    · have h0 : (0 : ℝ) ^ (l.val - j.val) = 0 := pow_eq_zero_iff'.mpr ⟨rfl, by omega⟩
      rw [h0, mul_zero]
    · exact absurd (Fin.ext heq) hj
    · have h0 : (l.val + 1).choose (j.val + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [h0, Nat.cast_zero]
      ring
  · intro hl
    exact absurd (Finset.mem_univ l) hl

/-- `A_{ρ⁻¹,−t₀/ρ}` is a left inverse of `A_{ρ,t₀}` (for `ρ ≠ 0`). -/
lemma affVecDual_comp_inv (k : ℕ) {ρ : ℝ} (hρ : ρ ≠ 0) (t₀ : ℝ) (y : E k) :
    affVecDual k ρ⁻¹ (-t₀ / ρ) (affVecDual k ρ t₀ y) = y := by
  rw [affVecDual_comp]
  have h1 : ρ⁻¹ * ρ = 1 := inv_mul_cancel₀ hρ
  have h2 : ρ⁻¹ * t₀ + -t₀ / ρ = 0 := by
    field_simp
    ring
  rw [h1, h2, affVecDual_one_zero]

/-- `A_{ρ,t₀}` is a left inverse of `A_{ρ⁻¹,−t₀/ρ}` (for `ρ ≠ 0`). -/
lemma affVecDual_inv_comp (k : ℕ) {ρ : ℝ} (hρ : ρ ≠ 0) (t₀ : ℝ) (y : E k) :
    affVecDual k ρ t₀ (affVecDual k ρ⁻¹ (-t₀ / ρ) y) = y := by
  have h := affVecDual_comp k ρ t₀ ρ⁻¹ (-t₀ / ρ) y
  have h1 : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ
  have h2 : ρ * (-t₀ / ρ) + t₀ = 0 := by
    field_simp
    ring
  rw [h1, h2, affVecDual_one_zero] at h
  exact h

/-- **`A_I` is a bijection.** -/
lemma affVecDual_bijective (k : ℕ) {ρ : ℝ} (hρ : ρ ≠ 0) (t₀ : ℝ) :
    Function.Bijective (affVecDual k ρ t₀) :=
  ⟨fun _ _ h => by
      have := congrArg (affVecDual k ρ⁻¹ (-t₀ / ρ)) h
      rwa [affVecDual_comp_inv k hρ, affVecDual_comp_inv k hρ] at this,
    fun y => ⟨affVecDual k ρ⁻¹ (-t₀ / ρ) y, affVecDual_inv_comp k hρ t₀ y⟩⟩

/-- **The inverse image of a plate.**  `A_I^{-1}(𝒰_J) = 𝒰_{J_I}`. -/
lemma affMap_preimage_plate (k : ℕ) {ρ : ℝ} (hρ : ρ ≠ 0) (t₀ δ c : ℝ) :
    affMap k ρ t₀ ⁻¹' (plate k (ρ * δ) (ρ * c + t₀)) = plate k δ c := by
  have hinj : Function.Injective (affMap k ρ t₀) := by
    intro x y h
    have h' : affVecDual k ρ t₀ x = affVecDual k ρ t₀ y := by
      simpa [affMap_apply] using h
    exact (affVecDual_bijective k hρ t₀).1 h'
  rw [← affMap_image_plate, Set.preimage_image_eq _ hinj]

/-- **The affine maps compose invertibly**: `A_{ρ⁻¹,−t₀/ρ} ∘ A_{ρ,t₀} = id`. -/
lemma affMap_self_inv (k : ℕ) {ρ : ℝ} (hρ : ρ ≠ 0) (t₀ : ℝ) (x : E k) :
    affMap k ρ⁻¹ (-t₀ / ρ) (affMap k ρ t₀ x) = x := by
  rw [affMap_apply, affMap_apply, affVecDual_add, affVecDual_gammaVec, affVecDual_comp_inv k hρ]
  have h2 : ρ⁻¹ * t₀ + -t₀ / ρ = 0 := by
    field_simp
    ring
  have hγ0 : gammaVec k (0 : ℝ) = (0 : E k) := by
    ext j
    rw [gammaVec_apply, zero_pow (Nat.succ_ne_zero _)]
    rfl
  rw [h2, hγ0]
  abel

end Submission.Vinogradov
