import Mathlib
import Submission.Work.KT.PsiC.Setup
import Submission.Work.KT.PsiC.ReindexAux
import Submission.Work.KT.PsiC.CycProj
import Submission.Work.KT.PsiC.FramePerm
import Submission.Work.KT.PsiC.FramePerm2
import Submission.Work.KT.PsiC.FramePerm3

/-!
# `Work.KT.PsiC.BFrame` — the common frame for the `ψ²ψ³ = ψ³ψ²` comparison

All the objects live on the index type `IB n = (I2 n × I2 n) × I2 n` (six tensor positions grouped
into three pairs).  The relevant position permutations:

* `sg0`,`sg1`,`sg2` — the three pair swaps;  `sB = sg0*sg1*sg2` (in `Setup`);
* `cB` — the cycle of the three pairs (in `Setup`), so that `τ = cB`;
* `uB`,`vB` — the transport of `c1A`,`c2A`, with `cB = uB * vB`;
* `gamB = τ⁻¹ * sB`, the six-cycle with `gamB^2 = τ` and `gamB^3 = sB`;
* `invB` — a position permutation inverting `gamB` (`invB * gamB * invB = gamB⁻¹`).

The projectors:  `Edel d0 d1 d2 = Π_j h_{d_j}(σ_j)`, `Eeps ε = Edel ε ε ε`,
`Deps ε = h_ε(sB) - Eeps ε`.

The two sides of the comparison are

`ψ²ψ³ = Σ_{ε,λ} εχ(λ) [ P · Q_{λ²}(τ) · h_ε(sB) ]`   (with `Q` the cyclic projector)
`ψ³ψ² = Σ_{ε,λ} εχ(λ) [ P · Eeps ε · Q_λ(τ) ]`

and each differs from `Σ_{ε,λ} εχ(λ) [P · cycProj gamB (λε)]` by a sum of "rest" terms that cancels.
-/

namespace Work.KT.PsiC

open Matrix
open Work.KT.Psi

noncomputable section

variable {A : Type} [Ring A] [Algebra ℂ A]

/-- `Π_j h_{d_j}(σ_j)`: the joint `d`-eigenspace projector of the three pair swaps. -/
def Edel (d0 d1 d2 : ℂ) (n : ℕ) : Matrix (IB n) (IB n) A :=
  halfProj d0 (sg0 n) * halfProj d1 (sg1 n) * halfProj d2 (sg2 n)

/-- The `ε`-joint projector `Π_j h_ε(σ_j)`. -/
def Eeps (ε : ℂ) (n : ℕ) : Matrix (IB n) (IB n) A := Edel ε ε ε n

/-- The "mixed" projector `h_ε(sB) - E_ε`; `h_ε(sB) = E_ε + D_ε`. -/
def Deps (ε : ℂ) (n : ℕ) : Matrix (IB n) (IB n) A := halfProj ε (sB n) - Eeps ε n

/-- The transport of `c1A` to frame B (a `3`-cycle on the first elements of the pairs). -/
def uB (n : ℕ) : Equiv.Perm (IB n) := (Phi n).symm.trans ((c1A n).trans (Phi n))

/-- The transport of `c2A` to frame B (a `3`-cycle on the second elements of the pairs). -/
def vB (n : ℕ) : Equiv.Perm (IB n) := (Phi n).symm.trans ((c2A n).trans (Phi n))

/-- The six-cycle `γ = τ⁻¹ sB`, with `γ² = τ` and `γ³ = sB`. -/
def gamB (n : ℕ) : Equiv.Perm (IB n) := (cB n)⁻¹ * sB n

/-- The position permutation `(a,b),(c,d),(e,f) ↦ (e,f),(c,d),(a,b)` inverting `gamB`. -/
def invB (n : ℕ) : Equiv.Perm (IB n) where
  toFun x := ((x.2, x.1.2), x.1.1)
  invFun x := ((x.2, x.1.2), x.1.1)
  left_inv := by rintro ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨e, f⟩⟩; rfl
  right_inv := by rintro ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨e, f⟩⟩; rfl

/-- The `μ`-spectral projector of the six-cycle `gamB`: `(1/6) Σ_{k<6} μ⁻ᵏ γᵏ`.  This (and not
`cycProj`, which is the three-term projector of a `3`-cycle) is the genuine eigenspace projector. -/
def cycProj6 (n : ℕ) (mu : ℂ) : Matrix (IB n) (IB n) A :=
  algebraMap ℂ A ((1 : ℂ) / 6) •
    (∑ k ∈ Finset.range 6, algebraMap ℂ A (mu⁻¹ ^ k) • ((gamB n).permMatrix A) ^ k)

/-- The "leading" class `[P · cycProj6 γ μ]` of the six-cycle frame. -/
def Tcls (p : Mat A) (mu : ℂ) : K0 A :=
  clsM (IB p.1) (PB p * cycProj6 (A := A) p.1 mu)

/-- The off-diagonal part of the `λ²`-spectral projector of `cB = uB * vB`. -/
def Q2m (p : Mat A) (lam : ℂ) : Matrix (IB p.1) (IB p.1) A :=
  cycProj (uB p.1) (lam * omega) * cycProj (vB p.1) (lam * omega ^ 2) +
    cycProj (uB p.1) (lam * omega ^ 2) * cycProj (vB p.1) (lam * omega)

/-- The corresponding "rest" class of the `ψ²ψ³` side. -/
def Q2cls (p : Mat A) (eps lam : ℂ) : K0 A :=
  clsM (IB p.1) (PB p * Q2m p lam * halfProj eps (sB p.1))

/-- The "rest" class of the `ψ³ψ²` side. -/
def Dcls (p : Mat A) (eps : ℂ) : K0 A :=
  clsM (IB p.1) (PB p * Edel eps (-eps) (-eps) p.1)

end

end Work.KT.PsiC
