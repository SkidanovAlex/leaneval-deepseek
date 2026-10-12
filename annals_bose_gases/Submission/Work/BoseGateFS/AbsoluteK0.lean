import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseGateFS.HonestInhab
import Submission.Work.BoseGateFS.HonestRowsAssemble
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.AbsoluteK0` — `HonestRows` at **one absolute** `K₀`

The τ-free bundle `KinkFS` is produced at *some* `K₁ > 0` (at the honest model it
is the constant of FS's `L¹` row `|Ŵ₁| ≤ 16πa`, `KinkFSHonest.lean`), while the
§11/§12 rows carry their own constants.  `KinkFS.mono` enlarges the bundle to any
larger constant, so all rows can be assembled at the single

`K₀ = max (max K₁ 1) (max Cα Cint) …`,

the "one ABSOLUTE `K₀`" of the design: the caller chooses `K₀` once and states
every row at it.  The helpers below make that choice mechanical: each K₀-carrying
row is monotone in its constant because its right-hand side is
`K₀ · (nonnegative factor)`.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseGateFS

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode}

/-- `E.lille ≥ 0` at a positive chemical potential. -/
lemma lille_nonneg (hv : FSParamsView E) : 0 ≤ E.lille := by
  show 0 ≤ Work.BoseB7.lille E.mu E.aScat E.KH
  rw [Work.BoseB7.lille]
  exact mul_nonneg (mul_nonneg (Work.BoseGateFS.mu_pos_of_view hv).le
    (pow_nonneg hv.a_pos.le 3)) (sq_nonneg _)

/-- **Constant relaxation for the K₀-carrying rows**: an estimate
`x ≤ C·y` with `C ≤ K₀` and `y ≥ 0` is an estimate at `K₀`. -/
lemma le_mul_mono_of_nonneg {x C K y : ℝ} (h : x ≤ C * y) (hCK : C ≤ K) (hy : 0 ≤ y) :
    x ≤ K * y :=
  le_trans h (mul_le_mul_of_nonneg_right hCK hy)

/-- `η_H(E) ≥ 0`; every K₀-carrying row with `η` on the right is monotone in `K₀`. -/
lemma eta_nonneg {E : Q3Env Mode} (hv : FSParamsView E) : 0 ≤ eta E := by
  rw [Work.BoseB7A.eta]
  exact Real.rpow_nonneg
    (mul_nonneg (Real.rpow_nonneg (le_trans zero_le_one hv.one_le_Kl) _)
      (lille_nonneg hv)) _

/-- **`HonestRows` at one absolute `K₀`.**  The τ-free bundle is obtained at some
`K₁ ≤ K₀` (so by `KinkFS.mono` it is available at `K₀`), and every §11/§12 row is
supplied *at* `K₀`; the caller picks `K₀` above all the existential constants
(each row is monotone in its constant by `le_mul_mono_of_nonneg`, with the
nonnegative factors `η_H`, `ρ a K_H⁻¹`, `lille·(K_H a)·‖·‖`, `(K_ℓK_L)^{-M}`, …). -/
def honestRows_absolute {K₀ : ℝ}
    (hex : ∃ K₁ : ℝ, K₁ ≤ K₀ ∧ Nonempty (KinkFS K₁ F T E))
    (hv : FSParamsView E)
    (hτ : ∀ ρ : ℝ, AdmRho E ρ → ∀ q : Mode, F.PHq E.KH E.aScat q →
      ‖F.kmom q‖ ^ 2 / 2 + 3 * ρ * K₀ * E.aScat ≤ E.tau q)
    (hW1low : ∀ k : Mode, ‖F.kmom k‖ ≤ 1 / (4 * E.KH * E.aScat) → 0 ≤ E.W1 k)
    (hbox : ∀ i j : Mode, F.ccrK i j
      = Work.BoseK15.corpusBox.hatChiSq (E.ell • (F.kmom i - F.kmom j))
        - Work.BoseK15.corpusBox.hatChi (E.ell • F.kmom i)
          * Work.BoseK15.corpusBox.hatChi (E.ell • F.kmom j))
    (hα : ∀ ρ : ℝ, AdmRho E ρ → ∀ p q : Mode, F.PHq E.KH E.aScat p → F.PHq E.KH E.aScat q →
      |(KzEnvAt E ρ).alpha p - (KzEnvAt E ρ).alpha q|
        ≤ K₀ * E.lille * (E.KH * E.aScat) * ‖F.kmom p - F.kmom q‖)
    (hint : ∀ ρ : ℝ, AdmRho E ρ →
      |ρ * E.W1omega0 - E.ell ^ (-(3 : ℝ)) *
          ∑ k ∈ F.PHset E, E.W1 k * (KzEnvAt E ρ).alpha k|
        ≤ K₀ * ρ * E.aScat * E.KH⁻¹)
    (hq2 : ∀ ρ : ℝ, AdmRho E ρ → ∀ Ψ : F.H,
      2 * ρ * E.W1omega0 * F.qw Ψ (T.Gop E)
        ≤ F.qw Ψ (F.Q2ex (KzEnvAt E ρ)) + (E.b / 400) * F.qw Ψ (T.gapOpT (KzEnvAt E ρ))
          + (1 / 2) * F.qw Ψ (F.dNumOpR (KzEnvAt E ρ)
              (fun k => rHi F E k ∧ ¬ F.PHq E.KH E.aScat k)))
    (hhatChi_small : ∀ q : Mode, F.PHq E.KH E.aScat q → |E.hatChi q| ≤ K₀ * eta E)
    (hccrX_small : ∀ s q : Mode, E.fL s ≠ 0 → F.PHq E.KH E.aScat q →
      |T.ccrX s q| ≤ K₀ * eta E)
    (hsum : ∑ s ∈ excited Mode, |E.hatChiSq s| ≤ K₀)
    (htail : ∑ s ∈ excited Mode, |E.hatChiSq s| * (1 - E.fL s)
      ≤ K₀ * (E.Kl * E.KL) ^ (-(E.intM : ℝ)))
    (hform_upper : ∀ (S : Finset Mode) (c : Mode → ℝ) (w : Mode → F.H),
      (∑ s ∈ S, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (w s') (w s))
        ≤ K₀ * ∑ s ∈ S, c s ^ 2 * F.bp (w s) (w s))
    (hcount : (((excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ)
      ≤ K₀ * (E.Kl * E.KL) ^ 3)
    (hsumW1sq : E.ell ^ (-(3 : ℝ)) *
        ∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat), E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2
      ≤ K₀ * E.aScat) :
    Nonempty (HonestRows K₀ F T E) := by
  obtain ⟨K₁, hK₁, ⟨hK⟩⟩ := hex
  exact ⟨honestRows_of_rows (hK.mono hK₁) hv hτ hW1low hbox hα hint hq2 hhatChi_small
    hccrX_small hsum htail hform_upper hcount hsumW1sq⟩

end Work.BoseGateFS
