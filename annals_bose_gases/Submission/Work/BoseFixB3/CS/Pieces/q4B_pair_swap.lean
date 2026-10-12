import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB3.CS.Pieces.aP_eq_zero_of_nonpos
import Submission.Work.BoseFixB3.CS.Pieces.pairFibreDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.q4B_pair_swap`

The `4Q`-bracket `q4B ℓ om Φ p` of the corpus (`Submission.PotWords`, FS `eq:DefQ4`)
is **symmetric in the ordered pair** `p = (p.1, p.2)`, for every symmetric kernel
`om` and every continuous state `Φ`:

  `q4B ℓ (omC ω) Ψ (j, i) c = q4B ℓ (omC ω) Ψ (i, j) c`   (`i ≠ j`).

## Why it is true

Recall (FS `eq:DefQ4`, corpus `Submission.BoseGases.q4B`)

  `q4B ℓ om Ψ p x = Q_{p.2}Q_{p.1}Ψ x + om (x p.1) (x p.2)
        · (P_{p.2}P_{p.1}Ψ x + P_{p.2}Q_{p.1}Ψ x + Q_{p.2}P_{p.1}Ψ x)`,

where `P_k = aP ℓ k` is the mean over the centred cube in slot `k` and `Q_k = 1 − P_k`.
For `0 < ℓ` the projection algebra of `Submission.PotWords` / `Submission.Q0Sector`
gives, with `A := P_iΨ c`, `B := P_jΨ c`, `AB := P_iP_jΨ c`,

* `Q_iQ_jΨ c = Q_jQ_iΨ c`                                 (`aQ_comm`);
* `P_iP_jΨ c + P_iQ_jΨ c + Q_iP_jΨ c = AB + (A − AB) + (B − AB) = A + B − AB`
  and likewise, using `aP_comm` / `aP_aQ_comm`, the same for the transposed pair
  `P_jP_iΨ c + P_jQ_iΨ c + Q_jP_iΨ c`;

together with `om (c i) (c j) = om (c j) (c i)` from the symmetry hypothesis.

For `ℓ ≤ 0` the centred cube `acube ℓ` is contained in `{0}`, a null set, so `P_k ≡ 0`
and `Q_k ≡ 1`; both sides of the identity collapse to `Ψ c`.
-/

open MeasureTheory

namespace Work.BoseFixB3.CS.Pieces

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-! ## The degenerate box `ℓ ≤ 0`

The one-slot mean projection vanishes identically when the cube is a null set; that
is the general lemma `Work.BoseFixB3.CS.Pieces.aP_eq_zero_of_nonpos` (proved in the
sibling module of the same name, imported above). -/

/-- For a non-positive side length the whole `4Q`-bracket is just `Ψ`. -/
private lemma q4B_eq_self_of_nonpos {n : ℕ} {ℓ : ℝ} (hℓ : ℓ ≤ 0)
    (om : E3 → E3 → ℝ) {Ψ : Submission.BoseGases.X n → ℝ} (c : Submission.BoseGases.X n)
    (p : Fin n × Fin n) : Submission.BoseGases.q4B ℓ om Ψ p c = Ψ c := by
  have hPall : ∀ (k : Fin n) (Φ : Submission.BoseGases.X n → ℝ)
      (x : Submission.BoseGases.X n), Submission.BoseGases.aP ℓ k Φ x = 0 :=
    fun k Φ x => aP_eq_zero_of_nonpos hℓ k Φ x
  unfold Submission.BoseGases.q4B
  simp only [Submission.BoseGases.aQ, hPall]
  ring

/-! ## The main identity -/

theorem q4B_pair_swap {ℓ : ℝ} {ω : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hω : ∀ x y : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.omC ω x y = Submission.BoseGases.omC ω y x)
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) {Ψ : Submission.BoseGases.X n → ℝ} (hΨc : Continuous Ψ)
    (c : Submission.BoseGases.X n) :
    Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC ω) Ψ (j, i) c
      = Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC ω) Ψ (i, j) c := by
  by_cases hℓ : 0 < ℓ
  · -- Non-degenerate box: the projection algebra of the corpus.
    have hQQ : Submission.BoseGases.aQ ℓ i (Submission.BoseGases.aQ ℓ j Ψ) c
        = Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aQ ℓ i Ψ) c :=
      Submission.BoseGases.aQ_comm hℓ hij hΨc c
    have hPQ : Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Ψ) c
        = Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Ψ) c :=
      Submission.BoseGases.aP_aQ_comm hℓ hij hΨc c
    have hQP : Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Ψ) c
        = Submission.BoseGases.aQ ℓ i (Submission.BoseGases.aP ℓ j Ψ) c :=
      Submission.BoseGases.aP_aQ_comm hℓ hij.symm hΨc c
    have hPPij : Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Ψ) c
        = Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Ψ) c :=
      (Submission.BoseGases.aP_comm hℓ i j hΨc c).symm
    have hL : Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Ψ) c
          + Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Ψ) c
          + Submission.BoseGases.aQ ℓ i (Submission.BoseGases.aP ℓ j Ψ) c
        = Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Ψ) c
          + Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Ψ) c
          + Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Ψ) c := by
      rw [hPQ, hQP, hPPij]
      simp only [Submission.BoseGases.aQ]
      ring
    unfold Submission.BoseGases.q4B
    rw [hQQ, hω (c i) (c j), hL]
  · -- Degenerate box: both sides are `Ψ c`.
    have hℓ' : ℓ ≤ 0 := not_lt.mp hℓ
    rw [q4B_eq_self_of_nonpos hℓ' (Submission.BoseGases.omC ω) c (j, i),
      q4B_eq_self_of_nonpos hℓ' (Submission.BoseGases.omC ω) c (i, j)]

end Work.BoseFixB3.CS.Pieces
