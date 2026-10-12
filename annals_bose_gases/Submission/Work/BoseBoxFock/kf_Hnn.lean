import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseBoxFock.KafzHonest
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.kf_Hnn` — the `n₊`-type row `(c₁ n₀ − c₂) Σ_k a_k†a_k` of the dictionary

This is row 10 (`Hnn`) of the dictionary table of
`Submission/Work/BoseBoxFock/KafzHonest.lean`: for superposed modes `φ k` with
`φ k 0 = 0` (no condensate component) and the `c`-number substitution
`n₀ ↦ c₁ n₀ − c₂` (FS `eq:subst-z`'s `|z|² − 1`), the transport under the
⟨condensate | excited⟩ split `Work.BoseB4.split` of

    `(c₁ n₀ − c₂) ∘ (Σ_k a_k† a_k)`

is the anti-normal family

    `c₁ • (monoOp 1 1 B − monoOp 0 0 B) − c₂ • monoOp 0 0 B`,
    `B = Σ_k (creOfE (φ k)) ∘ (annOfE (φ k))`.

## Proof

Two rows of the dictionary, applied at `x`:

* the (`0,0`) **number row** `split_weighted_number` with all weights `1`
  (`kf_Hnn_number_row`): `split (W x) = (monoOp 0 0 B) (split x)` for
  `W = Σ_k a_k† a_k`;
* the (`1,1`)/(`0,0`) **`n₀ ∘ W` sandwich** `split_n0_spectator`: for any spectator
  word `W` transporting to `lift B`, `split (n₀ (W x)) = (monoOp 1 1 B − monoOp 0 0 B) (split x)`.

The assembly is the linearity of `split` (`map_sub`, `map_smul`) plus the applied
form of the operator identities (`LinearMap.sub_apply`, `LinearMap.smul_apply`,
`Module.End.one_apply`).  The final identity is purely definitional — as in
`Work.BoseBoxFock.kf_contact_mu` the `ℝ`-scalar `c • ·` of the module structure
coming with the `ℂ`-module on `FockCore (cfock _)` and the scalar `(c : ℂ) • ·`
agree (`Complex.coe_smul` at the definitional level) — so it is closed by `rfl`;
unfolding it costs more than the default heartbeat budget (the same `set_option`
is used by the sibling rows `split_L0_rows`, `kf_contact_mu`, `KafzDict`).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

variable {m : ℕ} [NeZero m]

/-- **The number-type row with all weights `1`.**  The `split` of the superposed number
operator `Σ_k a_k†a_k` is the (`0,0`) row with spectator word
`Σ_k creOfE (φ k) ∘ annOfE (φ k)` (the specialisation of `split_weighted_number`
to the constant weight `1`). -/
lemma kf_Hnn_number_row {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (s : Finset Mode) (φ : Mode → Fin m → ℝ) (hφ : ∀ k ∈ s, φ k 0 = 0) (x : RealFock m) :
    split ((∑ k ∈ s, (creOf m (φ k)) ∘ₗ (annOf m (φ k))) x)
      = (monoOp 0 0 (∑ k ∈ s, (1 : ℂ) • ((creOfE (φ k)) ∘ₗ (annOfE (φ k))))) (split x) := by
  have h := split_weighted_number (m := m) (Mode := Mode) s (fun _ => (1 : ℝ)) φ hφ x
  simpa only [one_smul, Complex.ofReal_one] using h

theorem kf_Hnn {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (s : Finset Mode) (φ : Mode → Fin m → ℝ) (hφ : ∀ k ∈ s, φ k 0 = 0)
    (c1 c2 : ℝ) (x : Work.BoseB4.RealFock m) :
    Work.BoseB4.split (((c1 • Work.BoseBoxFock.n0 - c2 • (1 : Work.BoseB4.RealFock m →ₗ[ℝ] Work.BoseB4.RealFock m)).comp
        (∑ k ∈ s, (Work.BoseB4.creOf m (φ k)) ∘ₗ (Work.BoseB4.annOf m (φ k)))) x)
      = ((c1 : ℂ) • (Work.BoseB4.monoOp 1 1 (∑ k ∈ s, (1 : ℂ) • ((Work.BoseBoxFock.creOfE (φ k)) ∘ₗ (Work.BoseBoxFock.annOfE (φ k))))
            - Work.BoseB4.monoOp 0 0 (∑ k ∈ s, (1 : ℂ) • ((Work.BoseBoxFock.creOfE (φ k)) ∘ₗ (Work.BoseBoxFock.annOfE (φ k)))))
          - (c2 : ℂ) • Work.BoseB4.monoOp 0 0 (∑ k ∈ s, (1 : ℂ) • ((Work.BoseBoxFock.creOfE (φ k)) ∘ₗ (Work.BoseBoxFock.annOfE (φ k))))) (Work.BoseB4.split x) := by
  set W : RealFock m →ₗ[ℝ] RealFock m :=
    ∑ k ∈ s, (creOf m (φ k)) ∘ₗ (annOf m (φ k)) with hWdef
  set B : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
    ∑ k ∈ s, (1 : ℂ) • ((creOfE (φ k)) ∘ₗ (annOfE (φ k))) with hBdef
  -- the (`0,0`) number row: `W` transports to `monoOp 0 0 B`
  have hW : ∀ y : RealFock m, split (W y) = (monoOp 0 0 B) (split y) := by
    intro y
    rw [hWdef, hBdef]
    exact kf_Hnn_number_row (m := m) s φ hφ y
  -- the same row in the `lift B` form requested by the sandwich lemma
  have hWl : ∀ y : RealFock m, split (W y) = lift B (split y) :=
    fun y => by rw [hW y, monoOp_zero_zero B]
  -- the applied `(c₁ n₀ − c₂)` on the spectator word
  have h1 : ((c1 • n0 - c2 • (1 : RealFock m →ₗ[ℝ] RealFock m)).comp W) x
      = c1 • (n0 (W x)) - c2 • (W x) := by
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply]
  rw [h1, map_sub, map_smul, map_smul]
  rw [show n0 (W x) = ((cre m 0) ∘ₗ ((ann m 0) ∘ₗ W)) x from rfl]
  -- the (`1,1`)/(`0,0`) sandwich `n₀ ∘ W`, and the number row for the `c₂`-term
  rw [split_n0_spectator B W hWl x, hW x]
  -- the rest is definitional (`LinearMap.sub_apply`, `LinearMap.smul_apply`,
  -- `(r : ℝ) • v = (r : ℂ) • v` on this `ℂ`-module)
  rfl

end Work.BoseBoxFock
