/-
  Work.WilE2 — localising an EA zero set to an axis-parallel box.

  `axBox a b = ∏ᵢ [aᵢ, bᵢ]` is the elementary piece of the cube topology: the traces
  `X ∩ box x δ` of a small cube around a point `x` of `X = cubeC k ∩ Zset c g` are exactly the
  neighbourhoods of `x` in `X` whose component count the argument counts.  The affine map
  `boxMap a b z i = (aᵢ+bᵢ)/2 + ((bᵢ-aᵢ)/2) zᵢ` carries the cube onto `axBox a b`, and
  `boxChain`/`boxSub` reparametrise the chain and the polynomials so that

      `eaEval (boxChain c a b) (boxSub a b Q) z = eaEval c Q (boxMap a b z)`   (`eaEval_boxSub`)

  i.e. the zero set of the reparametrised family on the cube is the pullback of the zero set of
  the original family on the box (`boxMap_image_Zset`).  Consequently the component bound
  `VarietyBound` for the cube applies to *every* box, with the same format `k + r` and the same
  polynomial bound; this is what makes `X` locally connected.

  The reparametrisation is the diagonal affine one: `boxChain` scales the `i`-th chain
  coefficient `a_{j i}` by the half-width of the `i`-th interval and shifts the constant term to
  `ℓ_j (center)`, so that `(boxChain c a b).ell j z = c.ell j (boxMap a b z)`
  (`boxChain_ell`) — the exponentials of the reparametrised chain are exactly the exponentials of
  `c` at `boxMap a b z`; and `boxSub` substitutes `xᵢ ↦ (aᵢ+bᵢ)/2 + ((bᵢ-aᵢ)/2) xᵢ` in the
  polynomial variables, leaving the `Eⱼ = exp(ℓ_j)` variables alone.
-/
import Mathlib
import Submission.Work.WilE2.VcbDefs
import Submission.Work.WilE5.Basic

set_option autoImplicit false
noncomputable section

namespace Work.WilE2

open Classical Set
open WilkiesDesign WilkiesDesign.E

variable {k r : ℕ}

/-- The axis-parallel closed box `∏ᵢ [aᵢ, bᵢ]`. -/
def axBox (a b : Fin k → ℝ) : Set (Fin k → ℝ) := {z | ∀ i, a i ≤ z i ∧ z i ≤ b i}

/-- The midpoints of the sides of the box. -/
def boxCenter (a b : Fin k → ℝ) : Fin k → ℝ := fun i => (a i + b i) / 2

/-- The half-widths of the sides of the box. -/
def boxHalf (a b : Fin k → ℝ) : Fin k → ℝ := fun i => (b i - a i) / 2

/-- The diagonal affine map of the cube onto the box. -/
def boxMap (a b : Fin k → ℝ) : (Fin k → ℝ) → (Fin k → ℝ) :=
  fun z i => boxCenter a b i + boxHalf a b i * z i

/-- The chain reparametrised by the box: its exponentials at `z` are the exponentials of `c` at
`boxMap a b z`. -/
def boxChain (c : EAChain k r) (a b : Fin k → ℝ) : EAChain k r where
  a := fun j i => boxHalf a b i * c.a j i
  b := fun j => c.ell j (boxCenter a b)

/-- Substitution of the affine map into the EA polynomials: `xᵢ ↦ (aᵢ+bᵢ)/2 + ((bᵢ-aᵢ)/2) xᵢ`. -/
def boxSub (a b : Fin k → ℝ) : EAPoly k r →ₐ[ℝ] EAPoly k r :=
  MvPolynomial.aeval (Sum.elim
    (fun i => MvPolynomial.C (boxCenter a b i) + MvPolynomial.C (boxHalf a b i)
      * MvPolynomial.X (Sum.inl i))
    (fun j => MvPolynomial.X (Sum.inr j)))

/-- The exponentials of the reparametrised chain are the exponentials of `c` at `boxMap a b z`. -/
theorem boxChain_ell (c : EAChain k r) (a b : Fin k → ℝ) (j : Fin r) (z : Fin k → ℝ) :
    (boxChain c a b).ell j z = c.ell j (boxMap a b z) := by
  have hsum : (∑ i, c.a j i * ((a i + b i) / 2 + (b i - a i) / 2 * z i))
      = (∑ i, c.a j i * ((a i + b i) / 2)) + (∑ i, (b i - a i) / 2 * c.a j i * z i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [EAChain.ell, boxChain, boxCenter, boxHalf, boxMap]
  rw [hsum]
  ring

/-- `boxSub` leaves the `Eⱼ = exp(ℓ_j)` variables alone. -/
theorem boxSub_X_inr (a b : Fin k → ℝ) (j : Fin r) :
    boxSub (k := k) (r := r) a b (MvPolynomial.X (Sum.inr j)) = MvPolynomial.X (Sum.inr j) := by
  simp [boxSub]

/-- `boxSub` acts on the `xᵢ` by the affine map. -/
theorem boxSub_X_inl (a b : Fin k → ℝ) (i : Fin k) :
    boxSub (k := k) (r := r) a b (MvPolynomial.X (Sum.inl i))
      = MvPolynomial.C (boxCenter a b i) + MvPolynomial.C (boxHalf a b i)
          * MvPolynomial.X (Sum.inl i) := by
  simp [boxSub]

/-- `boxSub` fixes the constants. -/
theorem boxSub_C (a b : Fin k → ℝ) (t : ℝ) :
    boxSub (k := k) (r := r) a b (MvPolynomial.C t) = MvPolynomial.C t := by
  simp [boxSub]

/-- **The reparametrisation identity.**  Evaluating the substituted polynomial in the
reparametrised chain at `z` is evaluating the original polynomial in the original chain at
`boxMap a b z`. -/
theorem eaEval_boxSub (c : EAChain k r) (a b : Fin k → ℝ) (Q : EAPoly k r) (z : Fin k → ℝ) :
    eaEval (boxChain c a b) (boxSub a b Q) z = eaEval c Q (boxMap a b z) := by
  change MvPolynomial.aeval (Sum.elim z fun j => Real.exp ((boxChain c a b).ell j z)) (boxSub a b Q)
    = MvPolynomial.aeval (Sum.elim (boxMap a b z) fun j => Real.exp (c.ell j (boxMap a b z))) Q
  rw [show (boxSub (k := k) (r := r) a b : EAPoly k r →ₐ[ℝ] EAPoly k r)
      = MvPolynomial.aeval (Sum.elim
          (fun i => MvPolynomial.C (boxCenter a b i) + MvPolynomial.C (boxHalf a b i)
            * MvPolynomial.X (Sum.inl i))
          (fun j => MvPolynomial.X (Sum.inr j))) from rfl]
  rw [MvPolynomial.comp_aeval_apply]
  rw [show (fun s : Fin k ⊕ Fin r =>
        MvPolynomial.aeval (Sum.elim z fun j => Real.exp ((boxChain c a b).ell j z))
          (Sum.elim
            (fun i => MvPolynomial.C (boxCenter a b i) + MvPolynomial.C (boxHalf a b i)
              * MvPolynomial.X (Sum.inl i))
            (fun j => MvPolynomial.X (Sum.inr j)) s))
      = Sum.elim (boxMap a b z) (fun j => Real.exp (c.ell j (boxMap a b z))) from by
    funext s
    rcases s with i | j
    · simp only [Sum.elim_inl, map_add, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
        Algebra.algebraMap_self_apply, boxMap]
    · simp only [Sum.elim_inr, MvPolynomial.aeval_X, boxChain_ell]]

/-- The affine bijection of the cube onto the box (a diagonal affine map), as a homeomorphism. -/
noncomputable def boxHomeo (a b : Fin k → ℝ) (hab : ∀ i, a i < b i) :
    (Fin k → ℝ) ≃ₜ (Fin k → ℝ) where
  toFun := boxMap a b
  invFun := fun w i => (w i - boxCenter a b i) / boxHalf a b i
  left_inv := by
    intro z
    funext i
    have hne : boxHalf a b i ≠ 0 := by
      simp only [boxHalf]; linarith [hab i]
    simp only [boxMap]
    field_simp
    ring
  right_inv := by
    intro w
    funext i
    have hne : boxHalf a b i ≠ 0 := by
      simp only [boxHalf]; linarith [hab i]
    simp only [boxMap]
    field_simp
    ring
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact Continuous.add continuous_const
      (Continuous.mul continuous_const (continuous_apply i))
  continuous_invFun := by
    apply continuous_pi
    intro i
    exact Continuous.div_const (Continuous.sub (continuous_apply i) continuous_const) _

/-- `boxHomeo` acts by `boxMap`. -/
theorem boxHomeo_apply (a b : Fin k → ℝ) (hab : ∀ i, a i < b i) (z : Fin k → ℝ) :
    boxHomeo a b hab z = boxMap a b z := rfl

/-- The image of the cube under `boxMap` is the box. -/
theorem boxMap_image_cubeC {a b : Fin k → ℝ} (hab : ∀ i, a i < b i) :
    boxMap a b '' cubeC k = axBox a b := by
  have hb : ∀ i, boxHalf a b i = (b i - a i) / 2 := fun i => rfl
  have hc : ∀ i, boxCenter a b i = (a i + b i) / 2 := fun i => rfl
  have hpos : ∀ i, 0 < boxHalf a b i := by
    intro i; rw [hb i]; linarith [hab i]
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    intro i
    have h1 : |z i| ≤ 1 := hz i
    have hz1 : -1 ≤ z i := (abs_le.mp h1).1
    have hz2 : z i ≤ 1 := (abs_le.mp h1).2
    have hup : boxHalf a b i * z i ≤ boxHalf a b i := by nlinarith [hpos i, hz2]
    have hlo : -(boxHalf a b i) ≤ boxHalf a b i * z i := by nlinarith [hpos i, hz1]
    have hup' : (b i - a i) / 2 * z i ≤ (b i - a i) / 2 := by rw [← hb i]; exact hup
    have hlo' : -((b i - a i) / 2) ≤ (b i - a i) / 2 * z i := by rw [← hb i]; exact hlo
    constructor
    · simp only [boxMap]; rw [hc i, hb i]; linarith
    · simp only [boxMap]; rw [hc i, hb i]; linarith
  · intro hw
    refine ⟨fun i => (w i - boxCenter a b i) / boxHalf a b i, ?_, ?_⟩
    · intro i
      rw [abs_le]
      have hw' := hw i
      constructor
      · rw [le_div_iff₀ (hpos i)]
        rw [hc i, hb i] at *
        linarith [hw'.1]
      · rw [div_le_iff₀ (hpos i)]
        rw [hc i, hb i] at *
        linarith [hw'.2]
    · funext i
      have hne : boxHalf a b i ≠ 0 := ne_of_gt (hpos i)
      simp only [boxMap]
      field_simp
      ring

end Work.WilE2
