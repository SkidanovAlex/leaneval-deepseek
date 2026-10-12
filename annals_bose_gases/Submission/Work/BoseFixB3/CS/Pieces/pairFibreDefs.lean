import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.CS.Pieces.ppMass_le_q4mass_cnPlus_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.pairFibreDefs`

The two-body **fibre** of an `n`-body function over a distinguished pair of slots, together
with the projection-transfer lemmas that make the `n = 2` congruence-step bound
(`Pieces.ppMass_le_q4mass_cnPlus_two`) applicable to it.

For `x : X n` and distinct slots `i j : Fin n`, the fibre of `Φ : X n → ℝ` is

  `pairFibre x i j Φ u = Φ (Function.update (Function.update x i (u 0)) j (u 1))`,  `u : X 2`,

i.e. slots `0, 1` of the fibre sit in the `n`-body slots `i, j`, and all other slots keep the
background values `x`.

The key point (`aP_zero_pairFibre` / `aQ_one_pairFibre` and their siblings) is that the box
projections `P_k`, `Q_k` (`k = 0, 1`) of the fibre are the `n`-body projections `P_i, P_j`,
`Q_i, Q_j` evaluated at `pairUpd x i j u`: the two transfer identities are pure
`Function.update` algebra (the projections integrate over a single slot), with **no**
continuity or integrability input.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB3.CS.Pieces

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false

/-- The configuration of `X n` obtained from the background `x` by overwriting slots `i` and
`j` with the two values of `u : X 2`. -/
def pairUpd {n : ℕ} (x : Submission.BoseGases.X n) (i j : Fin n) (u : Submission.BoseGases.X 2) :
    Submission.BoseGases.X n :=
  Function.update (Function.update x i (u 0)) j (u 1)

/-- The two-body fibre of `Φ` at the ordered pair `(i,j)` over the background `x`. -/
def pairFibre {n : ℕ} (x : Submission.BoseGases.X n) (i j : Fin n)
    (Φ : Submission.BoseGases.X n → ℝ) : Submission.BoseGases.X 2 → ℝ :=
  fun u => Φ (pairUpd x i j u)

/-- The fibre variable is the background with slots `i, j` overwritten — definitional form of
`pairFibre`. -/
lemma pairFibre_eq {n : ℕ} (x : Submission.BoseGases.X n) (i j : Fin n)
    (Φ : Submission.BoseGases.X n → ℝ) :
    pairFibre x i j Φ = fun u : Submission.BoseGases.X 2 => Φ (pairUpd x i j u) := rfl

lemma pairUpd_apply_zero {n : ℕ} {x : Submission.BoseGases.X n} {i j : Fin n} (hij : i ≠ j)
    (u : Submission.BoseGases.X 2) : pairUpd x i j u i = u 0 := by
  show Function.update (Function.update x i (u 0)) j (u 1) i = u 0
  rw [Function.update_comm (a := i) (b := j) hij (u 0) (u 1) x]
  exact Function.update_self i (u 0) (Function.update x j (u 1))

lemma pairUpd_apply_one {n : ℕ} {x : Submission.BoseGases.X n} {i j : Fin n}
    (u : Submission.BoseGases.X 2) : pairUpd x i j u j = u 1 := by
  show Function.update (Function.update x i (u 0)) j (u 1) j = u 1
  exact Function.update_self j (u 1) (Function.update x i (u 0))

/-- The fibre identity at the `0`-th slot: overwriting slot `i` of `pairUpd x i j u` is the same
as first inserting `y` into slot `0` of `u`. -/
lemma pairUpd_update_zero {n : ℕ} {x : Submission.BoseGases.X n} {i j : Fin n} (hij : i ≠ j)
    (u : Submission.BoseGases.X 2) (y : E3) :
    pairUpd x i j (Function.update u 0 y) = Function.update (pairUpd x i j u) i y := by
  have h0 : (Function.update u (0 : Fin 2) y) 0 = y := Function.update_self 0 y u
  have h1 : (Function.update u (0 : Fin 2) y) 1 = u 1 :=
    Function.update_of_ne (a := (1 : Fin 2)) (a' := (0 : Fin 2)) (by decide) y u
  have hL : pairUpd x i j (Function.update u 0 y)
      = Function.update (Function.update x j (u 1)) i y := by
    show Function.update (Function.update x i ((Function.update u 0 y) 0)) j
        ((Function.update u 0 y) 1) = Function.update (Function.update x j (u 1)) i y
    rw [h0, h1]
    exact Function.update_comm (a := i) (b := j) hij y (u 1) x
  have hR : Function.update (pairUpd x i j u) i y
      = Function.update (Function.update x j (u 1)) i y := by
    show Function.update (Function.update (Function.update x i (u 0)) j (u 1)) i y
        = Function.update (Function.update x j (u 1)) i y
    rw [Function.update_comm (a := i) (b := j) hij (u 0) (u 1) x, Function.update_idem]
  rw [hL, hR]

/-- The fibre identity at the `1`-st slot. -/
lemma pairUpd_update_one {n : ℕ} {x : Submission.BoseGases.X n} {i j : Fin n} (_hij : i ≠ j)
    (u : Submission.BoseGases.X 2) (y : E3) :
    pairUpd x i j (Function.update u 1 y) = Function.update (pairUpd x i j u) j y := by
  have h0 : (Function.update u (1 : Fin 2) y) 0 = u 0 :=
    Function.update_of_ne (a := (0 : Fin 2)) (a' := (1 : Fin 2)) (by decide) y u
  have h1 : (Function.update u (1 : Fin 2) y) 1 = y := Function.update_self 1 y u
  show Function.update (Function.update x i ((Function.update u 1 y) 0)) j
      ((Function.update u 1 y) 1)
      = Function.update (Function.update (Function.update x i (u 0)) j (u 1)) j y
  rw [h0, h1, Function.update_idem]

/-- `u ↦ pairUpd x i j u` is continuous. -/
lemma pairUpd_continuous {n : ℕ} (x : Submission.BoseGases.X n) (i j : Fin n) :
    Continuous (pairUpd x i j) := by
  unfold pairUpd
  exact (Continuous.update (continuous_const : Continuous fun _ : Submission.BoseGases.X 2 => x)
    i (continuous_apply 0)).update j (continuous_apply 1)

/-- A fibre of a continuous function is continuous. -/
lemma pairFibre_continuous {n : ℕ} {x : Submission.BoseGases.X n} {i j : Fin n}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) :
    Continuous (pairFibre x i j Φ) :=
  hΦ.comp (pairUpd_continuous x i j)

/-! ## Transfer of the box projections -/

/-- **Slot-`0` transfer of `P`.** -/
lemma aP_zero_pairFibre {n : ℕ} {ℓ : ℝ} {i j : Fin n} (hij : i ≠ j)
    (Ψ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n)
    (u : Submission.BoseGases.X 2) :
    Submission.BoseGases.aP ℓ 0 (pairFibre x i j Ψ) u
      = Submission.BoseGases.aP ℓ i Ψ (pairUpd x i j u) := by
  show Submission.BoseGases.aP ℓ 0 (fun u' => Ψ (pairUpd x i j u')) u
      = Submission.BoseGases.aP ℓ i Ψ (pairUpd x i j u)
  unfold Submission.BoseGases.aP
  congr 1
  refine integral_congr_ae ?_
  filter_upwards with y
  show Ψ (pairUpd x i j (Function.update u 0 y)) = Ψ (Function.update (pairUpd x i j u) i y)
  rw [pairUpd_update_zero hij]

/-- **Slot-`1` transfer of `P`.** -/
lemma aP_one_pairFibre {n : ℕ} {ℓ : ℝ} {i j : Fin n} (hij : i ≠ j)
    (Ψ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n)
    (u : Submission.BoseGases.X 2) :
    Submission.BoseGases.aP ℓ 1 (pairFibre x i j Ψ) u
      = Submission.BoseGases.aP ℓ j Ψ (pairUpd x i j u) := by
  show Submission.BoseGases.aP ℓ 1 (fun u' => Ψ (pairUpd x i j u')) u
      = Submission.BoseGases.aP ℓ j Ψ (pairUpd x i j u)
  unfold Submission.BoseGases.aP
  congr 1
  refine integral_congr_ae ?_
  filter_upwards with y
  show Ψ (pairUpd x i j (Function.update u 1 y)) = Ψ (Function.update (pairUpd x i j u) j y)
  rw [pairUpd_update_one hij]

/-- **Slot-`0` transfer of `Q`.** -/
lemma aQ_zero_pairFibre {n : ℕ} {ℓ : ℝ} {i j : Fin n} (hij : i ≠ j)
    (Ψ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n)
    (u : Submission.BoseGases.X 2) :
    Submission.BoseGases.aQ ℓ 0 (pairFibre x i j Ψ) u
      = Submission.BoseGases.aQ ℓ i Ψ (pairUpd x i j u) := by
  have h := aP_zero_pairFibre (ℓ := ℓ) hij Ψ x u
  rw [show Submission.BoseGases.aQ ℓ 0 (pairFibre x i j Ψ) u
        = (pairFibre x i j Ψ) u - Submission.BoseGases.aP ℓ 0 (pairFibre x i j Ψ) u from rfl,
      show Submission.BoseGases.aQ ℓ i Ψ (pairUpd x i j u)
        = Ψ (pairUpd x i j u) - Submission.BoseGases.aP ℓ i Ψ (pairUpd x i j u) from rfl, h]
  rfl

/-- **Slot-`1` transfer of `Q`.** -/
lemma aQ_one_pairFibre {n : ℕ} {ℓ : ℝ} {i j : Fin n} (hij : i ≠ j)
    (Ψ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n)
    (u : Submission.BoseGases.X 2) :
    Submission.BoseGases.aQ ℓ 1 (pairFibre x i j Ψ) u
      = Submission.BoseGases.aQ ℓ j Ψ (pairUpd x i j u) := by
  have h := aP_one_pairFibre (ℓ := ℓ) hij Ψ x u
  rw [show Submission.BoseGases.aQ ℓ 1 (pairFibre x i j Ψ) u
        = (pairFibre x i j Ψ) u - Submission.BoseGases.aP ℓ 1 (pairFibre x i j Ψ) u from rfl,
      show Submission.BoseGases.aQ ℓ j Ψ (pairUpd x i j u)
        = Ψ (pairUpd x i j u) - Submission.BoseGases.aP ℓ j Ψ (pairUpd x i j u) from rfl, h]
  rfl

/-! ## Transfer of the `4Q`-bracket -/

/-- **The `(0,1)` `4Q`-bracket of the fibre** is the `(i,j)` `4Q`-bracket of `Φ` at
`pairUpd x i j u`. -/
lemma q4B_pairFibre_zero_one {n : ℕ} {ℓ : ℝ} {i j : Fin n} (hij : i ≠ j)
    (om : E3 → E3 → ℝ) (Φ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n)
    (u : Submission.BoseGases.X 2) :
    Submission.BoseGases.q4B ℓ om (pairFibre x i j Φ) (0, 1) u
      = Submission.BoseGases.q4B ℓ om Φ (i, j) (pairUpd x i j u) := by
  have hQ0 : Submission.BoseGases.aQ ℓ 0 (pairFibre x i j Φ)
      = fun u' => Submission.BoseGases.aQ ℓ i Φ (pairUpd x i j u') :=
    funext (fun u' => aQ_zero_pairFibre hij Φ x u')
  have hP0 : Submission.BoseGases.aP ℓ 0 (pairFibre x i j Φ)
      = fun u' => Submission.BoseGases.aP ℓ i Φ (pairUpd x i j u') :=
    funext (fun u' => aP_zero_pairFibre hij Φ x u')
  have h1 : Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aQ ℓ 0 (pairFibre x i j Φ)) u
      = Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aQ ℓ i Φ) (pairUpd x i j u) := by
    rw [hQ0]; exact aQ_one_pairFibre hij (Submission.BoseGases.aQ ℓ i Φ) x u
  have h2 : Submission.BoseGases.aP ℓ 1 (Submission.BoseGases.aP ℓ 0 (pairFibre x i j Φ)) u
      = Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) (pairUpd x i j u) := by
    rw [hP0]; exact aP_one_pairFibre hij (Submission.BoseGases.aP ℓ i Φ) x u
  have h3 : Submission.BoseGases.aP ℓ 1 (Submission.BoseGases.aQ ℓ 0 (pairFibre x i j Φ)) u
      = Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) (pairUpd x i j u) := by
    rw [hQ0]; exact aP_one_pairFibre hij (Submission.BoseGases.aQ ℓ i Φ) x u
  have h4 : Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aP ℓ 0 (pairFibre x i j Φ)) u
      = Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Φ) (pairUpd x i j u) := by
    rw [hP0]; exact aQ_one_pairFibre hij (Submission.BoseGases.aP ℓ i Φ) x u
  have hom : om (u 0) (u 1) = om (pairUpd x i j u i) (pairUpd x i j u j) := by
    rw [pairUpd_apply_zero hij, pairUpd_apply_one]
  simp only [Submission.BoseGases.q4B, h1, h2, h3, h4, hom]

/-- **The `(1,0)` `4Q`-bracket of the fibre** is the `(j,i)` `4Q`-bracket of `Φ` at
`pairUpd x i j u`. -/
lemma q4B_pairFibre_one_zero {n : ℕ} {ℓ : ℝ} {i j : Fin n} (hij : i ≠ j)
    (om : E3 → E3 → ℝ) (Φ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n)
    (u : Submission.BoseGases.X 2) :
    Submission.BoseGases.q4B ℓ om (pairFibre x i j Φ) (1, 0) u
      = Submission.BoseGases.q4B ℓ om Φ (j, i) (pairUpd x i j u) := by
  have hQ0 : Submission.BoseGases.aQ ℓ 0 (pairFibre x i j Φ)
      = fun u' => Submission.BoseGases.aQ ℓ i Φ (pairUpd x i j u') :=
    funext (fun u' => aQ_zero_pairFibre hij Φ x u')
  have hQ1 : Submission.BoseGases.aQ ℓ 1 (pairFibre x i j Φ)
      = fun u' => Submission.BoseGases.aQ ℓ j Φ (pairUpd x i j u') :=
    funext (fun u' => aQ_one_pairFibre hij Φ x u')
  have hP0 : Submission.BoseGases.aP ℓ 0 (pairFibre x i j Φ)
      = fun u' => Submission.BoseGases.aP ℓ i Φ (pairUpd x i j u') :=
    funext (fun u' => aP_zero_pairFibre hij Φ x u')
  have hP1 : Submission.BoseGases.aP ℓ 1 (pairFibre x i j Φ)
      = fun u' => Submission.BoseGases.aP ℓ j Φ (pairUpd x i j u') :=
    funext (fun u' => aP_one_pairFibre hij Φ x u')
  have h1 : Submission.BoseGases.aQ ℓ 0 (Submission.BoseGases.aQ ℓ 1 (pairFibre x i j Φ)) u
      = Submission.BoseGases.aQ ℓ i (Submission.BoseGases.aQ ℓ j Φ) (pairUpd x i j u) := by
    rw [hQ1]; exact aQ_zero_pairFibre hij (Submission.BoseGases.aQ ℓ j Φ) x u
  have h2 : Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aP ℓ 1 (pairFibre x i j Φ)) u
      = Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) (pairUpd x i j u) := by
    rw [hP1]; exact aP_zero_pairFibre hij (Submission.BoseGases.aP ℓ j Φ) x u
  have h3 : Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aQ ℓ 1 (pairFibre x i j Φ)) u
      = Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Φ) (pairUpd x i j u) := by
    rw [hQ1]; exact aP_zero_pairFibre hij (Submission.BoseGases.aQ ℓ j Φ) x u
  have h4 : Submission.BoseGases.aQ ℓ 0 (Submission.BoseGases.aP ℓ 1 (pairFibre x i j Φ)) u
      = Submission.BoseGases.aQ ℓ i (Submission.BoseGases.aP ℓ j Φ) (pairUpd x i j u) := by
    rw [hP1]; exact aQ_zero_pairFibre hij (Submission.BoseGases.aP ℓ j Φ) x u
  have hom : om (u 1) (u 0) = om (pairUpd x i j u j) (pairUpd x i j u i) := by
    rw [pairUpd_apply_zero hij, pairUpd_apply_one]
  simp only [Submission.BoseGases.q4B, h1, h2, h3, h4, hom]

/-- The double projection of the fibre is constant in the fibre variable, with value the
`n`-body double projection at the background `x`. -/
lemma aP_aP_pairFibre_const {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) (x : Submission.BoseGases.X n)
    (u : Submission.BoseGases.X 2) :
    Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aP ℓ 1 (pairFibre x i j Φ)) u
      = Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x := by
  have hP1 : Submission.BoseGases.aP ℓ 1 (pairFibre x i j Φ)
      = fun u' => Submission.BoseGases.aP ℓ j Φ (pairUpd x i j u') :=
    funext (fun u' => aP_one_pairFibre hij Φ x u')
  rw [hP1]
  rw [show Submission.BoseGases.aP ℓ 0 (fun u' => Submission.BoseGases.aP ℓ j Φ (pairUpd x i j u')) u
        = Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) (pairUpd x i j u) from
      aP_zero_pairFibre hij (Submission.BoseGases.aP ℓ j Φ) x u]
  have hup : pairUpd x i j u = Function.update (Function.update x j (u 1)) i (u 0) := by
    show Function.update (Function.update x i (u 0)) j (u 1) = _
    exact Function.update_comm (a := i) (b := j) hij (u 0) (u 1) x
  rw [hup]
  refine (Submission.BoseGases.aP_pair_const_in_i (ℓ := ℓ) (i := i) (j := j) hℓ hij
    (Φ := Φ) hΦc (Function.update x j (u 1)) (u 0)).trans ?_
  exact Submission.BoseGases.aP_pair_const_in_j (ℓ := ℓ) (i := i) (j := j) hℓ hij (Φ := Φ) hΦc x (u 1)

end Work.BoseFixB3.CS.Pieces
